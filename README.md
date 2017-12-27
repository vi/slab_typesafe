# slab_typesafe
A type-safe wrapper from Rust's "slab" data structure

Prevents using [slab](https://crates.io/crates/slab) with obviously wrong keys:

```rust
#[macro_use] 
extern crate slab_typesafe;

declare_slab_token!(StringHandle1);
declare_slab_token!(StringHandle2);

let mut slab1 : Slab<StringHandle1, _> = Slab::new();
let mut slab2 : Slab<StringHandle2, _> = Slab::new();

let hello = slab1.insert("hello");
let world = slab2.insert("world");

slab1[world]; // the type `Slab<StringHandle1, _>` cannot be indexed by `StringHandle2`
slab2.remove(hello); // expected struct `StringHandle2`, found struct `StringHandle1`
```rust
