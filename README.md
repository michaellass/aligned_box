# aligned_box: Allocate aligned heap memory in Rust.

[![build](https://travis-ci.com/michaellass/aligned_box.svg?branch=master)](https://travis-ci.com/michaellass/aligned_box)
[![license](https://img.shields.io/github/license/michaellass/aligned_box.svg)](https://github.com/michaellass/aligned_box/blob/master/LICENSE)
[![crates.io](https://img.shields.io/crates/v/aligned_box.svg)](https://crates.io/crates/aligned_box)

aligned_box provides traits and implementations for the allocation of aligned heap memory. It adds new constructors to
`std::boxed::Box` in order to do aligned allocations.

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
