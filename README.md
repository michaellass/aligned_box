# aligned_box: Allocate aligned heap memory in Rust.

[![CI](https://github.com/michaellass/aligned_box/actions/workflows/ci.yml/badge.svg)](https://github.com/michaellass/aligned_box/actions/workflows/ci.yml)
[![license](https://img.shields.io/github/license/michaellass/aligned_box.svg)](https://github.com/michaellass/aligned_box/blob/master/LICENSE)
[![crates.io](https://img.shields.io/crates/v/aligned_box.svg)](https://crates.io/crates/aligned_box)
[![docs.rs](https://docs.rs/aligned_box/badge.svg)](https://docs.rs/aligned_box)

This crate provides a wrapper around the `Box` type, which allows allocating heap memory with user-specified alignment.

## Examples
Place value 17 of type `i32` on the heap, aligned to 64 bytes:
```rust
use aligned_box::AlignedBox;
let b = AlignedBox::<i32>::new(64, 17);
```

Allocate memory for 1024 values of type `f32` on the heap, aligned to 128 bytes. Values are initialized by their default value:
```rust
use aligned_box::AlignedBox;
let b = AlignedBox::<[f32]>::slice_from_default(128, 1024);
```

Allocate memory for 1024 values of type `f32` on the heap, aligned to 128 bytes. All values are initialized with PI:
```rust
use aligned_box::AlignedBox;
let b = AlignedBox::<[f32]>::slice_from_value(128, 1024, std::f32::consts::PI);
```
