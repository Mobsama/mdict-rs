use adler::adler32_slice;
use byteorder::{BigEndian, ByteOrder, LittleEndian, ReadBytesExt, WriteBytesExt};
use encoding_rs::{Encoding, GB18030, UTF_16BE, UTF_16LE, UTF_8};
use hex;
use memchr::memmem;
use regex::Regex;
use ripemd128::{Digest, Ripemd128};
use rust_lzo::LZOContext;
use rust_salsa20::{Key::Key32, Salsa20};
use std::cmp::Ordering;
use std::fs::{self, File, read_dir};
use std::io::{self, prelude::*, BufReader, BufWriter, Cursor, Error, ErrorKind, Read, Result, SeekFrom};
use std::path::PathBuf;
use std::str::FromStr;
use std::thread::{self, JoinHandle};
use std::collections::HashMap;
use xxhash_rust::xxh64::xxh64;

enum MDictVersion {
    V1,
    V2,
    V3,
}

impl MDictVersion {
    fn key_block_attrs_size(&self) -> u8 {
        match self {
            MDictVersion::V1 => 4 * 4,
            MDictVersion::V2 => 5 * 8,
            MDictVersion::V3 => 5 * 8,
        }
    }

    fn read_number<T: ReadBytesExt>(&self, cursor: &mut T) -> Result<u64> {
        Ok(match self {
            MDictVersion::V1 => cursor.read_u32::<BigEndian>()? as u64,
            _ => cursor.read_u64::<BigEndian>()?,
        })
    }

    fn number_width(&self) -> u8 {
        match self {
            MDictVersion::V1 => 4,
            _ => 8,
        }
    }
}

impl FromStr for MDictVersion {
    type Err = io::Error;

    fn from_str(s: &str) -> Result<Self> {
        let version = s
            .parse::<f64>()
            .map_err(|err| io::Error::new(ErrorKind::InvalidData, err.to_string()))?;
        let version = if version < 2.0 {
            MDictVersion::V1
        } else if version >= 3.0 {
            MDictVersion::V3
        } else {
            MDictVersion::V2
        };
        Ok(version)
    }
}

struct MDictHeader {
    encoding: &'static Encoding,
    version: MDictVersion,
    key_block_offset: u64,
    encrypt: i32,
    encrypted_key: Option<Vec<u8>>,
    stylesheet: HashMap<String, (String, String)>,
}

impl MDictHeader {
    fn new(fpath: &PathBuf, mode: &MDictMode, passcode: String) -> Result<Self> {
        let mut f = BufReader::new(File::open(fpath)?);
        let header_bytes_size = f.read_u32::<BigEndian>()?;
        let mut header_bytes = vec![0; header_bytes_size as usize];
        f.read_exact(&mut header_bytes)?;
        let adler32 = f.read_u32::<LittleEndian>()?;
        let calculated_adler32 = adler32_slice(&header_bytes);
        assert_eq!(adler32, calculated_adler32 & 0xffffffff);
        let key_block_offset = f
            .seek(SeekFrom::Current(0))
            .expect("Failed to get file offset");

        let head_text = if header_bytes[header_bytes.len() - 2..] == [0x00, 0x00] {
            match decode_string(&UTF_16LE, &header_bytes[..header_bytes.len() - 2]) {
                Ok(str) => str,
                Err(_) => {
                    decode_string(&UTF_16BE, &header_bytes[..header_bytes.len() - 2]).unwrap()
                }
            }
        } else {
            decode_string(&UTF_8, &header_bytes[..header_bytes.len() - 1])?
        };

        let header_attrs = parse_header(head_text);

        let version: MDictVersion = header_attrs
            .get("GeneratedByEngineVersion")
            .unwrap()
            .parse()
            .unwrap();
        let encoding = match mode {
            MDictMode::MDX {
                encoding,
                substyle: _,
            } => encoding,
            MDictMode::MDD => "UTF-16LE",
        };
        let encoding = if let MDictVersion::V3 = version {
            UTF_8
        } else if encoding.is_empty()
            && header_attrs
                .get("Encoding")
                .is_some_and(|encoding| encoding == "GBK" || encoding == "GB2312")
        {
            GB18030
        } else if encoding.is_empty() {
            UTF_8
        } else {
            Encoding::for_label(encoding.as_bytes()).unwrap()
        };

        let encrypt_str = header_attrs.get("Encrypted").map_or("", |v| v);
        let encrypt = if encrypt_str.is_empty() || encrypt_str == "No" {
            0
        } else if encrypt_str == "Yes" {
            1
        } else {
            encrypt_str.parse::<i32>().unwrap()
        };

        let encrypted_key = if !passcode.is_empty() {
            let mut split = passcode.split(',');
            let regcode = split.next().unwrap();
            let regcode = hex::decode(regcode).unwrap();
            let userid = split.next().unwrap();
            let userid = encode_string(&UTF_8, userid)?;
            Some(decrypt_regcode_by_userid(regcode, userid))
        } else if matches!(version, MDictVersion::V3) && header_attrs.contains_key("UUID") {
            let uuid = header_attrs.get("UUID").unwrap();
            let mid = (uuid.len() + 1) / 2;
            let mut hasher = Vec::new();
            let hasher1 = xxh64(uuid[..mid].as_bytes(), 0).to_le_bytes();
            let hasher2 = xxh64(uuid[mid..].as_bytes(), 0).to_le_bytes();
            hasher.extend(hasher1);
            hasher.extend(hasher2);
            Some(hasher)
        } else {
            None
        };

        let mut stylesheet: HashMap<String, (String, String)> = HashMap::new();
        if header_attrs.contains_key("StyleSheet") {
            let stylesheet_str = header_attrs.get("StyleSheet").unwrap();
            if !stylesheet_str.trim().is_empty() {
                let lines: Vec<&str> = stylesheet_str.split("\n").collect();
                for (i, _) in lines.iter().enumerate().step_by(3) {
                    stylesheet.insert(
                        lines.get(i).unwrap().to_string(),
                        (
                            lines.get(i + 1).unwrap().to_string(),
                            lines.get(i + 2).unwrap().to_string(),
                        ),
                    );
                }
            }
        }

        let header = MDictHeader {
            encoding,
            version,
            key_block_offset,
            encrypt,
            encrypted_key,
            stylesheet,
        };
        Ok(header)
    }
}

enum MDictMode {
    MDX { encoding: String, substyle: bool },
    MDD,
}

impl MDictMode {
    fn treat_record_data(&self, header: &MDictHeader, data: Vec<u8>) -> Result<Vec<u8>> {
        let res = match self {
            MDictMode::MDD => data,
            MDictMode::MDX {
                encoding: _,
                substyle,
            } => {
                let mut data = {
                    let str = decode_string(&header.encoding, &data)?;
                    str.trim_start_matches('\x00')
                        .trim_end_matches('\x00')
                        .to_string()
                };
                if *substyle && !header.stylesheet.is_empty() {
                    data = self.substitute_stylesheet(&header, &data);
                }
                encode_string(&UTF_8, &data).unwrap()
            }
        };
        Ok(res)
    }

    fn substitute_stylesheet(&self, header: &MDictHeader, txt: &str) -> String {
        let regex = Regex::new(r"`\d+`").unwrap();
        let txt_list: Vec<&str> = regex.split(txt).collect();
        let txt_tag: Vec<&str> = regex.find_iter(txt).map(|m| m.as_str()).collect();

        let mut txt_styled = String::from(txt_list[0]);

        for (j, p) in txt_list[1..].iter().enumerate() {
            let style = &header.stylesheet[&txt_tag[j][1..txt_tag[j].len() - 1]];
            if !p.is_empty() && p.ends_with('\n') {
                txt_styled += &style.0;
                txt_styled += &p.trim_end();
                txt_styled += &style.1;
                txt_styled += "\r\n";
            } else {
                txt_styled += &style.0;
                txt_styled += p;
                txt_styled += &style.1;
            }
        }
        txt_styled
    }
}

struct MDictFile {
    pub fpath: PathBuf,
    index: MDictIndex,
    mode: MDictMode,
    header: MDictHeader,
}

impl MDictFile {
    pub fn new(fpath: PathBuf, mode: MDictMode, passcode: String) -> Self {
        let header = MDictHeader::new(&fpath, &mode, passcode).unwrap();
        let index = MDictIndex::load(&fpath);
        MDictFile {
            fpath,
            index,
            mode,
            header,
        }
    }

    fn load_index(&mut self) {
        if self.index.entries_nums == 0 {
            let (
                record_index_offset,
                record_block_offset,
                key_id_list,
                mut key_list,
                key_block_list,
            ) = self.read_keys();
            let record_block_list = self.read_records(
                record_index_offset,
                record_block_offset,
                key_id_list,
                &mut key_list,
            );
            self.index
                .create_index_file(key_list, key_block_list, record_block_list)
                .unwrap();
        }
    }

    fn read_keys(
        &mut self,
    ) -> (
        u64,
        u64,
        Vec<u64>,
        Vec<(String, MDictBlockItem, MDictBlockItem)>,
        Vec<MDictBlockInfo>,
    ) {
        if matches!(self.header.version, MDictVersion::V3) {
            self.read_keys_v3().unwrap()
        } else if self.header.encrypt & 0x01 == 0x01 && self.header.encrypted_key.is_none() {
            self.read_keys_brutal().unwrap()
        } else {
            self.read_keys_v1v2().unwrap()
        }
    }

    fn read_keys_v1v2(
        &mut self,
    ) -> Result<(
        u64,
        u64,
        Vec<u64>,
        Vec<(String, MDictBlockItem, MDictBlockItem)>,
        Vec<MDictBlockInfo>,
    )> {
        let mut f = BufReader::new(File::open(&self.fpath)?);
        f.seek(SeekFrom::Start(self.header.key_block_offset))?;

        let mut block = vec![0; self.header.version.key_block_attrs_size() as usize];

        f.read_exact(&mut block)?;

        if self.header.encrypt & 0x01 == 0x01 {
            block = salsa_decrypt(block, &self.header.encrypted_key.clone().unwrap());
        }

        if !matches!(self.header.version, MDictVersion::V1) {
            let adler32 = f.read_u32::<BigEndian>()?;
            let calculated_adler32 = adler32_slice(&block);
            assert_eq!(adler32, calculated_adler32 & 0xffffffff);
        }

        let mut cursor = Cursor::new(block);
        let num_key_blocks = self.header.version.read_number(&mut cursor)?;
        let _num_entries = self.header.version.read_number(&mut cursor)?;
        let _key_block_info_decomp_size = if let MDictVersion::V2 = self.header.version {
            self.header.version.read_number(&mut cursor)?
        } else {
            0
        };
        let key_block_info_size = self.header.version.read_number(&mut cursor)?;

        let mut key_block_info = vec![0; key_block_info_size as usize];
        f.read_exact(&mut key_block_info)?;
        let key_block_info_list = self.decode_key_block_info(key_block_info)?;
        assert_eq!(num_key_blocks, key_block_info_list.len() as u64);

        let (key_id_list, key_list, key_block_list) =
            self.decode_key_block(&mut f, key_block_info_list)?;
        let record_block_offset = f.stream_position()?;
        Ok((
            0,
            record_block_offset,
            key_id_list,
            key_list,
            key_block_list,
        ))
    }

    fn decode_key_block_info(
        &self,
        mut key_block_info_compressed: Vec<u8>,
    ) -> Result<Vec<(u64, u64)>> {
        let key_block_info = if !matches!(self.header.version, MDictVersion::V1) {
            assert_eq!(&key_block_info_compressed[..4], &[0x02, 0x00, 0x00, 0x00]);
            if self.header.encrypt & 0x02 == 0x02 {
                let mut key = Vec::from(&key_block_info_compressed[4..8]);
                key.extend(&0x3695u32.to_le_bytes());
                let mut hasher = Ripemd128::new();
                hasher.input(key);
                let result = hasher.result();
                let key = result.as_slice();
                let fast_decrypt = fast_decrypt(&key_block_info_compressed[8..], key);
                key_block_info_compressed = key_block_info_compressed[..8].to_vec();
                key_block_info_compressed.extend(fast_decrypt);
            }
            let mut decoder = flate2::read::ZlibDecoder::new(&key_block_info_compressed[8..]);
            let mut key_block_info = Vec::new();
            decoder.read_to_end(&mut key_block_info).unwrap();

            let adler32 = BigEndian::read_u32(&key_block_info_compressed[4..8]);
            let calculated_adler32 = adler32_slice(&key_block_info);
            assert_eq!(adler32, calculated_adler32 & 0xffffffff);
            key_block_info
        } else {
            key_block_info_compressed
        };
        let mut key_block_info_list = Vec::new();
        let mut cursor = Cursor::new(key_block_info);
        let mut _num_entries: u64 = 0;

        let skip_text_head_and_tail = |cursor: &mut Cursor<Vec<u8>>| {
            let read_text_number = |cursor: &mut Cursor<Vec<u8>>| {
                if let MDictVersion::V1 = self.header.version {
                    cursor.read_u8().unwrap() as u64
                } else {
                    cursor.read_u16::<BigEndian>().unwrap() as u64
                }
            };
            let text_term: u64 = if let MDictVersion::V1 = self.header.version {
                0
            } else {
                1
            };
            let text_head_size = read_text_number(cursor);
            if self.header.encoding != UTF_16LE && self.header.encoding != UTF_16BE {
                cursor.set_position(cursor.position() + text_head_size + text_term);
            } else {
                cursor.set_position(cursor.position() + (text_head_size + text_term) * 2);
            }
            let text_tail_size = read_text_number(cursor);
            if self.header.encoding != UTF_16LE && self.header.encoding != UTF_16BE {
                cursor.set_position(cursor.position() + text_tail_size + text_term);
            } else {
                cursor.set_position(cursor.position() + (text_tail_size + text_term) * 2);
            }
        };

        while cursor.position() < cursor.get_ref().len() as u64 {
            _num_entries += self.header.version.read_number(&mut cursor).unwrap();
            skip_text_head_and_tail(&mut cursor);
            let key_block_compressed_size = self.header.version.read_number(&mut cursor).unwrap();
            let key_block_decompressed_size = self.header.version.read_number(&mut cursor).unwrap();
            key_block_info_list.push((key_block_compressed_size, key_block_decompressed_size));
        }

        Ok(key_block_info_list)
    }

    fn decode_key_block(
        &mut self,
        file: &mut BufReader<File>,
        key_block_info_list: Vec<(u64, u64)>,
    ) -> Result<(
        Vec<u64>,
        Vec<(String, MDictBlockItem, MDictBlockItem)>,
        Vec<MDictBlockInfo>,
    )> {
        let mut key_id_list = Vec::new();
        let mut key_list = Vec::new();
        let mut key_block_list = Vec::with_capacity(key_block_info_list.len());
        for (compressed_size, decompressed_size) in key_block_info_list {
            let block_start = file.stream_position().unwrap();
            let mut key_block_compressed = vec![0; compressed_size as usize];
            file.read_exact(&mut key_block_compressed)?;
            let key_block =
                decode_block(&self.header, key_block_compressed, decompressed_size).unwrap();
            let (id_list, keys) = self.split_key_block(key_block_list.len() as u64, key_block);
            key_id_list.extend(id_list);
            key_list.extend(keys);
            key_block_list.push(MDictBlockInfo::new(
                block_start,
                compressed_size,
                decompressed_size,
            ));
        }
        Ok((key_id_list, key_list, key_block_list))
    }

    fn split_key_block(
        &mut self,
        current_block: u64,
        key_block: Vec<u8>,
    ) -> (Vec<u64>, Vec<(String, MDictBlockItem, MDictBlockItem)>) {
        let mut key_start_index = 0;
        let mut key_id_list = Vec::new();
        let mut key_list = Vec::new();
        while key_start_index < key_block.len() {
            let key_id = if let MDictVersion::V1 = self.header.version {
                BigEndian::read_u32(&key_block[key_start_index..key_start_index + 4]) as u64
            } else {
                BigEndian::read_u64(&key_block[key_start_index..key_start_index + 8])
            };
            let delimiter: Vec<u8> =
                if self.header.encoding == UTF_16LE || self.header.encoding == UTF_16BE {
                    Vec::from([0x00, 0x00])
                } else {
                    Vec::from([0x00])
                };
            let mut i = key_start_index + self.header.version.number_width() as usize;
            let mut key_end_index = 0;
            while i < key_block.len() {
                if key_block[i..i + delimiter.len()] == delimiter {
                    key_end_index = i;
                    break;
                }
                i += delimiter.len();
            }
            let block_item_start =
                key_start_index as u64 + self.header.version.number_width() as u64;
            let key_text = decode_string(
                &self.header.encoding,
                &key_block[block_item_start as usize..key_end_index],
            )
            .unwrap();
            key_id_list.push(key_id);
            let block_item = MDictBlockItem::new(
                current_block,
                block_item_start,
                key_end_index as u64 - block_item_start,
            );
            key_list.push((key_text, block_item, MDictBlockItem::default()));
            key_start_index = key_end_index + delimiter.len();
        }
        (key_id_list, key_list)
    }

    fn read_keys_brutal(
        &mut self,
    ) -> Result<(
        u64,
        u64,
        Vec<u64>,
        Vec<(String, MDictBlockItem, MDictBlockItem)>,
        Vec<MDictBlockInfo>,
    )> {
        let mut f = BufReader::new(File::open(&self.fpath)?);
        f.seek(SeekFrom::Start(self.header.key_block_offset))?;

        let (mut block, key_block_type) = if let MDictVersion::V1 = self.header.version {
            let num_bytes: usize = 8 * 5 + 4;
            (vec![0; num_bytes], vec![0x02, 0x00, 0x00, 0x00])
        } else {
            let num_bytes: usize = 4 * 4;
            (vec![0; num_bytes], vec![0x01, 0x00, 0x00, 0x00])
        };
        f.read_exact(&mut block)?;
        let mut key_block_info = vec![0; 8];
        f.read_exact(&mut key_block_info)?;

        if !matches!(self.header.version, MDictVersion::V1) {
            assert_eq!(key_block_info[..4], key_block_type)
        }
        loop {
            let fpos = f.stream_position()?;
            let mut buffer = [0; 1024];
            let nread = f.read(&mut buffer)?;
            let index = memmem::find(&buffer[..nread], &key_block_type);
            if index.is_some() {
                key_block_info.extend_from_slice(&buffer[..index.unwrap()]);
                f.seek(SeekFrom::Start(fpos + index.unwrap() as u64))?;
                break;
            } else {
                key_block_info.extend(buffer);
            }
        }
        let key_block_info_list = self.decode_key_block_info(key_block_info)?;

        let (key_id_list, key_list, key_block_list) =
            self.decode_key_block(&mut f, key_block_info_list)?;
        let record_block_offset = f.stream_position()?;

        Ok((
            0,
            record_block_offset,
            key_id_list,
            key_list,
            key_block_list,
        ))
    }

    fn read_keys_v3(
        &mut self,
    ) -> Result<(
        u64,
        u64,
        Vec<u64>,
        Vec<(String, MDictBlockItem, MDictBlockItem)>,
        Vec<MDictBlockInfo>,
    )> {
        let mut f = BufReader::new(File::open(&self.fpath)?);
        f.seek(SeekFrom::Start(self.header.key_block_offset))?;
        let mut key_data_offset = 0;
        let mut record_index_offset = 0;
        let mut record_block_offset = 0;
        loop {
            let block_type = f.read_i32::<BigEndian>()?;
            let block_size = self.header.version.read_number(&mut f)?;
            let block_offset = f.stream_position()?;
            match block_type {
                0x01000000 => record_block_offset = block_offset,
                0x02000000 => record_index_offset = block_offset,
                0x03000000 => key_data_offset = block_offset,
                0x04000000 => (), //_key_index_offset
                _ => {
                    return Err(Error::new(
                        ErrorKind::InvalidData,
                        format!("Unknown block type {}", block_type),
                    ))
                }
            }
            f.seek(SeekFrom::Current(block_size as i64))?;
            if f.read_i32::<BigEndian>().is_ok_and(|x| x > 0) {
                f.seek(SeekFrom::Current(-4))?;
            } else {
                break;
            }
        }

        f.seek(SeekFrom::Start(key_data_offset))?;
        let number = f.read_u64::<BigEndian>()?;
        let _total_size = self.header.version.read_number(&mut f)?;
        let mut key_id_list = Vec::new();
        let mut key_list = Vec::new();
        let mut key_block_list = Vec::with_capacity(number as usize);
        for _i in 0..number {
            let block_start = f.stream_position()?;
            let decompressed_size = f.read_u64::<BigEndian>()?;
            let compressed_size = f.read_u64::<BigEndian>()?;

            let mut key_block_compressed = vec![0; compressed_size as usize];
            f.read_exact(&mut key_block_compressed)?;
            let key_block =
                decode_block(&self.header, key_block_compressed, decompressed_size).unwrap();
            let (id_list, keys) = self.split_key_block(key_block_list.len() as u64, key_block);
            key_id_list.extend(id_list);
            key_list.extend(keys);
            key_block_list.push(MDictBlockInfo::new(
                block_start,
                compressed_size,
                decompressed_size,
            ));
        }

        Ok((
            record_index_offset,
            record_block_offset,
            key_id_list,
            key_list,
            key_block_list,
        ))
    }

    fn read_records(
        &mut self,
        record_index_offset: u64,
        record_block_offset: u64,
        key_id_list: Vec<u64>,
        key_list: &mut Vec<(String, MDictBlockItem, MDictBlockItem)>,
    ) -> Vec<MDictBlockInfo> {
        if let MDictVersion::V3 = self.header.version {
            self.read_records_v3(
                record_index_offset,
                record_block_offset,
                key_id_list,
                key_list,
            )
            .unwrap()
        } else {
            self.read_records_v1v2(record_block_offset, key_id_list, key_list)
                .unwrap()
        }
    }

    fn read_records_v1v2(
        &mut self,
        record_block_offset: u64,
        key_id_list: Vec<u64>,
        key_list: &mut Vec<(String, MDictBlockItem, MDictBlockItem)>,
    ) -> Result<Vec<MDictBlockInfo>> {
        let mut f = BufReader::new(File::open(&self.fpath)?);
        f.seek(SeekFrom::Start(record_block_offset))?;

        let num_record_blocks = self.header.version.read_number(&mut f).unwrap();
        let num_entries = self.header.version.read_number(&mut f).unwrap();
        assert_eq!(num_entries, key_list.len() as u64);
        let record_block_info_size = self.header.version.read_number(&mut f).unwrap();
        let record_block_size = self.header.version.read_number(&mut f).unwrap();

        let mut record_block_info_list = Vec::with_capacity(num_record_blocks as usize);
        let mut size_counter: u64 = 0;
        for _ in 0..num_record_blocks {
            let compressed_size = self.header.version.read_number(&mut f).unwrap();
            let decompressed_size = self.header.version.read_number(&mut f).unwrap();
            record_block_info_list.push((compressed_size, decompressed_size));
            size_counter += self.header.version.number_width() as u64 * 2;
        }
        assert_eq!(size_counter, record_block_info_size);

        let mut i: usize = 0;
        let mut offset: u64 = 0;
        let mut size_counter: u64 = 0;
        let mut record_block_list = Vec::with_capacity(record_block_info_list.len());

        for (compressed_size, decompressed_size) in record_block_info_list {
            let block_start = f.stream_position()?;
            let mut block = vec![0; compressed_size as usize];
            f.read_exact(&mut block)?;
            while i < key_id_list.len() {
                let record_start = key_id_list.get(i).unwrap();
                if record_start - offset >= decompressed_size {
                    break;
                }
                let record_end = if i < key_id_list.len() - 1 {
                    *key_id_list.get(i + 1).unwrap()
                } else {
                    decompressed_size + offset
                };

                let record_start_offset = record_start - offset;
                let block = key_list.get_mut(i).unwrap();
                block.2 = MDictBlockItem::new(
                    record_block_list.len() as u64,
                    record_start_offset,
                    record_end - offset - record_start_offset,
                );
                i += 1;
            }
            record_block_list.push(MDictBlockInfo::new(
                block_start,
                compressed_size,
                decompressed_size,
            ));
            offset += decompressed_size;
            size_counter += compressed_size;
        }
        assert_eq!(size_counter, record_block_size);
        Ok(record_block_list)
    }

    fn read_records_v3(
        &mut self,
        record_index_offset: u64,
        record_block_offset: u64,
        key_id_list: Vec<u64>,
        key_list: &mut Vec<(String, MDictBlockItem, MDictBlockItem)>,
    ) -> Result<Vec<MDictBlockInfo>> {
        let record_index = self.read_record_index(record_index_offset)?;

        let mut f = BufReader::new(File::open(&self.fpath)?);
        f.seek(SeekFrom::Start(record_block_offset))?;

        let mut offset = 0;
        let mut i = 0;

        let num_record_blocks = f.read_u64::<BigEndian>()?;
        let _num_bytes = self.header.version.read_number(&mut f)?;
        let mut record_block_list = Vec::with_capacity(num_record_blocks as usize);
        for j in 0..num_record_blocks {
            let decompressed_size = f.read_u64::<BigEndian>()?;
            let mut compressed_size = f.read_u64::<BigEndian>()?;

            let recode = record_index.get(j as usize).unwrap();
            if (compressed_size + 8, decompressed_size) != *recode {
                compressed_size = recode.0 - 8;

                f.seek(SeekFrom::Current(compressed_size as i64))?;
                continue;
            }

            let block_start = f.stream_position()?;
            let mut block = vec![0; compressed_size as usize];
            f.read_exact(&mut block)?;

            while i < key_id_list.len() {
                let record_start = key_id_list.get(i).unwrap();
                if record_start - offset >= decompressed_size {
                    break;
                }
                let record_end = if i < key_id_list.len() - 1 {
                    *key_id_list.get(i + 1).unwrap()
                } else {
                    decompressed_size + offset
                };
                i += 1;

                let record_start_offset = record_start - offset;
                let block = key_list.get_mut(i).unwrap();
                block.2 = MDictBlockItem::new(
                    record_block_list.len() as u64,
                    record_start_offset,
                    record_end - offset - record_start_offset,
                );
            }
            offset += decompressed_size;
            record_block_list.push(MDictBlockInfo::new(
                block_start,
                compressed_size,
                decompressed_size,
            ));
        }
        Ok(record_block_list)
    }

    fn read_record_index(&self, record_index_offset: u64) -> Result<Vec<(u64, u64)>> {
        let mut f = BufReader::new(File::open(&self.fpath)?);
        f.seek(SeekFrom::Start(record_index_offset))?;
        let num_record_blocks = f.read_u64::<BigEndian>()?;
        let _num_bytes = self.header.version.read_number(&mut f)?;
        let mut record_index = Vec::new();
        for _ in 0..num_record_blocks {
            let decompressed_size = f.read_u64::<BigEndian>()?;
            let compressed_size = f.read_u64::<BigEndian>()?;
            let mut block = vec![0; compressed_size as usize];
            f.read_exact(&mut block)?;
            let record_block = decode_block(&self.header, block, decompressed_size)?;
            if record_block.len() % 16 != 0 {
                return Err(Error::new(
                    ErrorKind::InvalidData,
                    format!("record index block has invalid size {}", record_block.len()),
                ));
            }
            let mut j = 0;
            while j < record_block.len() {
                let block_size = BigEndian::read_u64(&record_block[j..j + 8]);
                let decompressed_size = BigEndian::read_u64(&record_block[j + 8..j + 16]);
                record_index.push((block_size, decompressed_size));
                j += 16;
            }
        }
        Ok(record_index)
    }

    fn get_key(&self, position: u64) -> Result<String> {
        if position >= self.index.entries_nums {
            return Err(Error::new(
                ErrorKind::InvalidData,
                "Exceeding the maximum number of words",
            ));
        }
        let mut index_file = BufReader::new(File::open(&self.index.fpath)?);
        let block_item = self.index.read_key_block_item(&mut index_file, position)?;
        let block_info = self
            .index
            .read_key_block_info(&mut index_file, block_item.block_index)?;
        let mut dict_file = BufReader::new(File::open(&self.fpath)?);
        let blcok = Self::read_block(&mut dict_file, &self.header, block_info, block_item);
        let key = decode_string(&self.header.encoding, &blcok)?;
        Ok(key)
    }

    fn get_record(&self, position: u64) -> Result<Vec<u8>> {
        if position >= self.index.entries_nums {
            return Err(Error::new(
                ErrorKind::InvalidData,
                "Exceeding the maximum number of words",
            ));
        }
        let mut index_file = BufReader::new(File::open(&self.index.fpath)?);
        let block_item = self
            .index
            .read_record_block_item(&mut index_file, position)?;
        let block_info = self
            .index
            .read_record_block_info(&mut index_file, block_item.block_index)?;
        let mut dict_file = BufReader::new(File::open(&self.fpath)?);
        let blcok = Self::read_block(&mut dict_file, &self.header, block_info, block_item);
        let record = self.mode.treat_record_data(&self.header, blcok)?;
        Ok(record)
    }

    fn read_block(
        file: &mut BufReader<File>,
        header: &MDictHeader,
        block_info: MDictBlockInfo,
        block_item: MDictBlockItem,
    ) -> Vec<u8> {
        file.seek(SeekFrom::Start(block_info.offset)).unwrap();
        let mut block = vec![0; block_info.compressed_size as usize];
        file.read_exact(&mut block).unwrap();
        let block = decode_block(header, block, block_info.decompressed_size).unwrap();
        block[block_item.start_offset as usize
            ..(block_item.start_offset + block_item.item_size) as usize]
            .to_vec()
    }

    pub fn binary_search(&self, target: String) -> Option<(u64, String, Vec<u8>)> {
        let mut low = 0;
        let mut high = self.index.entries_nums;
        while low < high {
            let mid = (low + high) / 2;
            let key = if let MDictMode::MDD = self.mode {
                let key = self.get_key(mid).unwrap();
                let key = if key.starts_with("\\") && !target.starts_with("\\") {
                    key[1..].to_string()
                } else {
                    key
                };
                key
            } else {
                self.get_key(mid).unwrap()
            };
            let ordering = key.to_lowercase().cmp(&target.to_lowercase());
            match ordering {
                Ordering::Equal => return Some((mid, key, self.get_record(mid).unwrap())),
                Ordering::Less => low = mid + 1,
                Ordering::Greater => high = mid,
            }
        }
        None
    }

    pub fn binary_search_exclude_record(&self, target: String) -> Option<(u64, String)> {
        let mut low = 0;
        let mut high = self.index.entries_nums;
        while low < high {
            let mid = (low + high) / 2;
            let key = self.get_key(mid).unwrap();
            let ordering = key.to_lowercase().cmp(&target.to_lowercase());
            match ordering {
                Ordering::Equal => return Some((mid, key)),
                Ordering::Less => low = mid + 1,
                Ordering::Greater => high = mid,
            }
        }
        None
    }
}

fn decode_string(encoder: &'static Encoding, data: &[u8]) -> Result<String> {
    let (cow, _encoding, had_errors) = encoder.decode(data);
    if had_errors {
        Err(io::Error::new(
            ErrorKind::InvalidData,
            "decode string error",
        ))
    } else {
        Ok(cow.into_owned())
    }
}

fn encode_string(encoder: &'static Encoding, data: &str) -> Result<Vec<u8>> {
    let (cow, _encoding, had_errors) = encoder.encode(data);
    if had_errors {
        Err(io::Error::new(
            ErrorKind::InvalidData,
            "encode string error",
        ))
    } else {
        Ok(cow.into_owned())
    }
}

fn parse_header(header: String) -> HashMap<String, String> {
    let mut tagdict = HashMap::new();
    let regex = Regex::new(r#"(\w+)="(.*?)""#).unwrap();
    for capture in regex.captures_iter(&header) {
        let key = capture.get(1).unwrap().as_str().to_owned();
        let value =
            html_escape::decode_html_entities(capture.get(2).unwrap().as_str()).into_owned();
        tagdict.insert(key, value);
    }
    tagdict
}

fn salsa_decrypt(mut ciphertext: Vec<u8>, encrypt_key: &[u8]) -> Vec<u8> {
    let key: [u8; 32] = encrypt_key.try_into().unwrap();
    let key = Key32(key);
    let nonce = [0x0; 8];
    let mut salsa = Salsa20::new(key, nonce, 8);
    salsa.encrypt(&mut ciphertext);
    ciphertext
}

fn decrypt_regcode_by_userid(regcode: Vec<u8>, userid: Vec<u8>) -> Vec<u8> {
    let mut hasher = Ripemd128::new();
    hasher.input(userid);
    let result = hasher.result();
    let userid_digest = result.as_slice();
    salsa_decrypt(regcode, userid_digest)
}

fn fast_decrypt(data: &[u8], key: &[u8]) -> Vec<u8> {
    let mut decrypted_data: Vec<u8> = data.to_vec();
    let mut previous: u8 = 0x36;

    for (i, &byte) in data.iter().enumerate() {
        let t: u8 = (byte >> 4 | byte << 4) & 0xff;
        let key_byte: u8 = key[i % key.len()];
        let t = t ^ previous ^ (i as u8) ^ key_byte;
        previous = byte;
        decrypted_data[i] = t;
    }
    decrypted_data
}

fn decode_block(header: &MDictHeader, block: Vec<u8>, decompressed_size: u64) -> Result<Vec<u8>> {
    let info = LittleEndian::read_u32(&block[..4]);
    let compression_method = info & 0xf;
    let encryption_method = (info >> 4) & 0xf;
    let encryption_size = (info >> 8) & 0xff;

    let adler32 = BigEndian::read_u32(&block[4..8]);
    let encrypted_key = header.encrypted_key.to_owned().unwrap_or({
        let mut hasher = Ripemd128::new();
        hasher.input(block[4..8].to_vec());
        let result = hasher.result();
        result.as_slice().to_vec()
    });
    let data = block[8..].to_vec();
    let decrypted_block = match encryption_method {
        0 => data,
        1 => {
            let mut fast_decrypt = fast_decrypt(&data[..encryption_size as usize], &encrypted_key);
            fast_decrypt.extend_from_slice(&data[encryption_size as usize..]);
            fast_decrypt
        }
        2 => {
            let mut salsa_decrypt =
                salsa_decrypt(data[..encryption_size as usize].to_vec(), &encrypted_key);
            salsa_decrypt.extend_from_slice(&data[encryption_size as usize..]);
            salsa_decrypt
        }
        _ => {
            return Err(io::Error::new(
                ErrorKind::InvalidData,
                format!("encryption method {} not supported", encryption_method),
            ))
        }
    };

    if matches!(header.version, MDictVersion::V3) {
        assert_eq!(adler32, adler32_slice(&decrypted_block) & 0xffffffff);
    }

    let decompressed_block = match compression_method {
        0 => decrypted_block,
        1 => {
            let mut header: Vec<u8> = Vec::new();
            header.push(0xf0);
            header.extend(&decompressed_size.to_le_bytes());
            header.extend(&decrypted_block);
            let mut lzo_decrypted: Vec<u8> = vec![0; decompressed_size as usize];
            LZOContext::decompress_to_slice(&header, &mut lzo_decrypted);
            lzo_decrypted
        }
        2 => {
            let mut decoder = flate2::read::ZlibDecoder::new(&decrypted_block[..]);
            let mut decompressed_block = Vec::new();
            decoder.read_to_end(&mut decompressed_block).unwrap();
            decompressed_block
        }
        _ => {
            return Err(io::Error::new(
                ErrorKind::InvalidData,
                format!("compression method {} not supported", compression_method),
            ))
        }
    };

    if !matches!(header.version, MDictVersion::V3) {
        assert_eq!(adler32, adler32_slice(&decompressed_block) & 0xffffffff);
    }
    Ok(decompressed_block)
}

struct MDictIndex {
    fpath: PathBuf,
    entries_nums: u64,
    key_block_nums: u64,
    record_block_nums: u64,
}

impl MDictIndex {
    const INDEX_VERSION: u8 = 1;

    fn new(fpath: PathBuf, entries_nums: u64, key_block_nums: u64, record_block_nums: u64) -> Self {
        MDictIndex {
            fpath,
            entries_nums,
            key_block_nums,
            record_block_nums,
        }
    }

    fn default(fpath: PathBuf) -> Self {
        Self::new(fpath, 0, 0, 0)
    }

    fn load(dict_file_path: &PathBuf) -> Self {
        let mut fpath = dict_file_path.clone();
        fpath.set_extension("");
        fpath.pop();
        fpath.push("index");

        if !fpath.exists() {
            fs::create_dir(&fpath).unwrap();
        }

        let mut extension = dict_file_path.extension().unwrap().to_owned();
        extension.push(".index");

        fpath.push(dict_file_path.file_name().unwrap());
        fpath.set_extension(extension);

        if fpath.exists() {
            let mut file = BufReader::new(File::open(&fpath).unwrap());
            let version = file.read_u8();
            if version.is_ok_and(|v| v == Self::INDEX_VERSION) {
                let entries_nums = file.read_u64::<BigEndian>().unwrap();
                let key_block_nums = file.read_u64::<BigEndian>().unwrap();
                let record_block_nums = file.read_u64::<BigEndian>().unwrap();
                return MDictIndex::new(fpath, entries_nums, key_block_nums, record_block_nums);
            } else {
                fs::remove_file(&fpath).unwrap();
            }
        }

        MDictIndex::default(fpath)
    }

    fn create_index_file(
        &mut self,
        mut key_list: Vec<(String, MDictBlockItem, MDictBlockItem)>,
        key_block_list: Vec<MDictBlockInfo>,
        record_block_list: Vec<MDictBlockInfo>,
    ) -> Result<()> {
        key_list.sort_by(|a, b| a.0.cmp(&b.0));

        let mut file = BufWriter::new(File::create(self.fpath.clone()).unwrap());
        file.write_u8(Self::INDEX_VERSION)?;

        self.entries_nums = key_list.len() as u64;
        self.key_block_nums = key_block_list.len() as u64;
        self.record_block_nums = record_block_list.len() as u64;

        file.write_u64::<BigEndian>(self.entries_nums)?;
        file.write_u64::<BigEndian>(self.key_block_nums)?;
        file.write_u64::<BigEndian>(self.record_block_nums)?;
        for info in key_block_list {
            file.write_u64::<BigEndian>(info.offset)?;
            file.write_u64::<BigEndian>(info.compressed_size)?;
            file.write_u64::<BigEndian>(info.decompressed_size)?;
        }
        for info in record_block_list {
            file.write_u64::<BigEndian>(info.offset)?;
            file.write_u64::<BigEndian>(info.compressed_size)?;
            file.write_u64::<BigEndian>(info.decompressed_size)?;
        }
        for (_, key_block_item, record_block_item) in key_list {
            file.write_u64::<BigEndian>(key_block_item.block_index)?;
            file.write_u64::<BigEndian>(key_block_item.start_offset)?;
            file.write_u64::<BigEndian>(key_block_item.item_size)?;
            file.write_u64::<BigEndian>(record_block_item.block_index)?;
            file.write_u64::<BigEndian>(record_block_item.start_offset)?;
            file.write_u64::<BigEndian>(record_block_item.item_size)?;
        }

        Ok(())
    }

    fn read_key_block_info(
        &self,
        file: &mut BufReader<File>,
        position: u64,
    ) -> Result<MDictBlockInfo> {
        if position >= self.key_block_nums {
            return Err(Error::new(
                ErrorKind::InvalidData,
                "Exceeding the maximum number of key blocks",
            ));
        }
        let offset = 1 + 3 * 8 + position * MDictBlockInfo::size();
        file.seek(SeekFrom::Start(offset))?;
        let offset = file.read_u64::<BigEndian>()?;
        let compressed_size = file.read_u64::<BigEndian>()?;
        let decompressed_size = file.read_u64::<BigEndian>()?;
        Ok(MDictBlockInfo::new(
            offset,
            compressed_size,
            decompressed_size,
        ))
    }

    fn read_key_block_item(
        &self,
        file: &mut BufReader<File>,
        position: u64,
    ) -> Result<MDictBlockItem> {
        if position >= self.entries_nums {
            return Err(Error::new(
                ErrorKind::InvalidData,
                "Exceeding the maximum number of words",
            ));
        }
        let offset = 1
            + 3 * 8
            + (self.key_block_nums + self.record_block_nums) * MDictBlockInfo::size()
            + position * MDictBlockItem::size() * 2;
        file.seek(SeekFrom::Start(offset))?;

        let block_index = file.read_u64::<BigEndian>()?;
        let start_offset = file.read_u64::<BigEndian>()?;
        let item_size = file.read_u64::<BigEndian>()?;
        Ok(MDictBlockItem::new(block_index, start_offset, item_size))
    }

    fn read_record_block_info(
        &self,
        file: &mut BufReader<File>,
        position: u64,
    ) -> Result<MDictBlockInfo> {
        if position >= self.record_block_nums {
            return Err(Error::new(
                ErrorKind::InvalidData,
                "Exceeding the maximum number of record blocks",
            ));
        }
        let offset = 1
            + 3 * 8
            + self.key_block_nums * MDictBlockInfo::size()
            + position * MDictBlockInfo::size();
        file.seek(SeekFrom::Start(offset))?;
        let offset = file.read_u64::<BigEndian>()?;
        let compressed_size = file.read_u64::<BigEndian>()?;
        let decompressed_size = file.read_u64::<BigEndian>()?;
        Ok(MDictBlockInfo::new(
            offset,
            compressed_size,
            decompressed_size,
        ))
    }

    fn read_record_block_item(
        &self,
        file: &mut BufReader<File>,
        position: u64,
    ) -> Result<MDictBlockItem> {
        if position >= self.entries_nums {
            return Err(Error::new(
                ErrorKind::InvalidData,
                "Exceeding the maximum number of records",
            ));
        }
        let offset = 1
            + 3 * 8
            + (self.key_block_nums + self.record_block_nums) * MDictBlockInfo::size()
            + position * MDictBlockItem::size() * 2
            + MDictBlockItem::size();
        file.seek(SeekFrom::Start(offset))?;

        let block_index = file.read_u64::<BigEndian>()?;
        let start_offset = file.read_u64::<BigEndian>()?;
        let item_size = file.read_u64::<BigEndian>()?;
        Ok(MDictBlockItem::new(block_index, start_offset, item_size))
    }
}

struct MDictBlockInfo {
    offset: u64,
    compressed_size: u64,
    decompressed_size: u64,
}

impl MDictBlockInfo {
    fn new(offset: u64, compressed_size: u64, decompressed_size: u64) -> Self {
        MDictBlockInfo {
            offset,
            compressed_size,
            decompressed_size,
        }
    }

    fn size() -> u64 {
        3 * 8
    }
}

struct MDictBlockItem {
    block_index: u64,
    start_offset: u64,
    item_size: u64,
}

impl MDictBlockItem {
    fn new(block_index: u64, start_offset: u64, item_size: u64) -> Self {
        MDictBlockItem {
            block_index,
            start_offset,
            item_size,
        }
    }
    fn default() -> Self {
        MDictBlockItem {
            block_index: 0,
            start_offset: 0,
            item_size: 0,
        }
    }

    fn size() -> u64 {
        3 * 8
    }
}

pub struct MDict {
    mdx: MDictFile,
    mdds: Vec<MDictFile>,
}

impl MDict {
    pub fn new(path: String, encoding: String, substyle: bool, passcode: String) -> Result<Self> {
        let mut mdx_paths = Vec::new();
        let files = read_dir(path)?;
        for entry in files {
            let entry = entry.unwrap();
            let path = entry.path();
            if path.is_file() {
                if path.extension().is_some_and(|p| p == "mdx") {
                    mdx_paths.push(path)
                }
            }
        }
        if mdx_paths.is_empty() || mdx_paths.len() > 1 {
            return Err(Error::new(
                ErrorKind::InvalidData,
                String::from("No mdx file exists or there are multiple mdx files"),
            ));
        }

        let mut mdx = MDictFile::new(
            mdx_paths.get(0).unwrap().clone(),
            MDictMode::MDX { encoding, substyle },
            passcode.clone(),
        );
        let mut mdd_paths = Vec::new();
        loop {
            let mut path = mdx.fpath.clone();
            path.set_extension("");

            if !mdd_paths.is_empty() {
                path.set_extension(format!("{}.mdd", mdd_paths.len()));
            } else {
                path.set_extension("mdd");
            }

            if path.exists() {
                mdd_paths.push(path);
            } else {
                break;
            }
        }

        let mdd_handle: Vec<JoinHandle<MDictFile>> = mdd_paths
            .iter()
            .map(|path| MDictFile::new(path.to_owned(), MDictMode::MDD, passcode.clone()))
            .map(|mut mdd| {
                thread::spawn(move || {
                    mdd.load_index();
                    mdd
                })
            })
            .collect();

        mdx.load_index();

        let mut mdds = Vec::new();
        for handle in mdd_handle {
            mdds.push(handle.join().unwrap());
        }
        Ok(MDict { mdx, mdds })
    }

    pub fn binary_search(&self, target: String) -> Option<(u64, String, String)> {
        let res = self.mdx.binary_search(target);
        match res {
            Some((position, key, value)) => {
                let mut record = decode_string(&UTF_8, &value).unwrap();
                if record.starts_with("@@@LINK=") {
                    let link = record.replace("@@@LINK=", "");
                    record = self.binary_search(link.trim().to_owned()).unwrap().2;
                }
                Some((position, key, record))
            }
            None => None,
        }
    }

    pub fn read_resourse(&self, record: &str) -> Vec<(String, Vec<u8>)> {
        let mut resourse = Vec::new();
        let src: Regex = Regex::new(r#"src="([^"]*)""#).unwrap();
        for capture in src.captures_iter(&record) {
            if let Some(src_value) = capture.get(1) {
                match self.read_resourse_in_mdds(src_value.as_str()) {
                    Some(value) => resourse.push(value),
                    None => (),
                }
            }
        }

        let href = Regex::new(r#"href="([^"]*)""#).unwrap();
        for capture in href.captures_iter(&record) {
            if let Some(href_value) = capture.get(1) {
                if href_value.as_str().starts_with("entry://") {
                    continue;
                }
                match self.read_resourse_in_mdds(href_value.as_str()) {
                    Some(value) => resourse.push(value),
                    None => (),
                }
            }
        }
        resourse
    }

    fn read_resourse_in_mdds(&self, resource_name: &str) -> Option<(String, Vec<u8>)> {
        for mdd in &self.mdds {
            match mdd.binary_search(resource_name.trim().to_owned()) {
                None => (),
                Some((_, key, value)) => return Some((key, value)),
            }
        }
        None
    }

    pub fn prefix_search(&self, target: String, max_size: usize) -> Option<Vec<String>> {
        let res = self.mdx.binary_search_exclude_record(target);
        match res {
            None => None,
            Some((mut position, key)) => {
                let mut vec = Vec::new();
                vec.push(key);
                loop {
                    if vec.len() >= max_size {
                        break;
                    }
                    position += 1;
                    let next = self.mdx.get_key(position);
                    match next {
                        Ok(next) => {
                            if next.starts_with(vec.get(0).unwrap()) {
                                vec.push(next)
                            } else {
                                break;
                            }
                        }
                        Err(_) => break,
                    }
                }
                Some(vec)
            }
        }
    }
}
