# mdict-rs

Rust code version of projett [mdict-analysis](https://bitbucket.org/xwang/mdict-analysis/).

Support V1V2V3.

The index file is created when the dictionary file is loaded for the first time to assist with binary search.

## Example
```Rust
let mdict = mdict_rs::MDict::new(path, encoding, false, passcode).unwrap();
//binary search words.
let (index, key, record) = mdict.binary_search(String::from("hello")).unwrap();
//get resource in record.
//filename:data
//multi-level filename
let resourse: Vec<String, Vec<u8>> mdict.read_resourse(&record);
```

## Acknowledge

[mdict-analysis](https://bitbucket.org/xwang/mdict-analysis/) by Xiaoqiang Wang
[mdict_rs](https://github.com/12101111/mdict_rs/) by 韩朴宇