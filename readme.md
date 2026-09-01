# ![Inplace Containers](https://img.shields.io/badge/InplaceContainers-Stack%20Allocated-blue) Inplace Containers

[![Crates.io](https://img.shields.io/crates/v/inplace_containers.svg)](https://crates.io/crates/inplace_containers) [![Docs.rs](https://img.shields.io/docsrs/inplace_containers)](https://docs.rs/inplace_containers) [![License](https://img.shields.io/crates/l/inplace_containers)](LICENSE)

**Zero-allocation, stack-allocated container types for Rust**. `inplace_containers` provides `InplaceVector` and `InplaceString` — high-performance alternatives to `Vec` and `String` when heap allocation is undesirable.

---

## Features

- Fully stack-allocated, fixed-capacity containers.
- No heap allocations.
- API familiar to Rust’s standard library (`Vec`, `String`).
- Iterators, `IntoIterator`, and `Extend` support.
- Clone, Debug, PartialEq, Hash, Ord, and conversions implemented.
- UTF-8 correctness for `InplaceString`.
- Niche-optimized layout keeps `Option<InplaceString<N>>` the same size as `InplaceString<N>` and `Option<InplaceVector<T, N>>` the same size as `InplaceVector<T, N>`.
- Compile-time construction and capacity checks with the `inplace_vec!` and `inplace_string!` macros.
- `ToInplaceOwned` support for fixed-size arrays and wrappers that dereference to arrays.
- `no_std` support when default features are disabled.
- Optional `nightly` feature enables unstable Pattern-gated APIs (requires nightly Rust).

---

## `no_std`

The default features are `all` and `std`. To use the containers without the standard library, disable default features and select the containers you need:

```toml
[dependencies]
inplace_containers = { version = "0.4.1", default-features = false, features = ["all"] }
```

The `std` feature enables integrations that require the standard library, such as `std::io::Write`, `String` conversions, C string conversions, and `std::error::Error` implementations.

---

## Nightly

To enable unstable Pattern-gated APIs, build with nightly and the `nightly` feature:

```toml
[dependencies]
inplace_containers = { version = "0.4.1", features = ["nightly"] }
```

```sh
cargo +nightly build
```

---

## Containers

### `InplaceVector<T, N>`

A fixed-capacity vector that stores `N` elements of type `T` inline.

```rust
use inplace_containers::inplace_vec;

// The macro encodes the fixed capacity in the type without heap allocation.
let mut vec = inplace_vec![5;];
vec.push(1);
vec.push(2);
vec.extend_from_slice(&[3, 4, 5]);

assert_eq!(vec.len(), 5);
assert!(vec.is_full());

let last = vec.pop();
assert_eq!(last, Some(5));
```

Const construction is supported for literal vectors:

```rust
use inplace_containers::inplace_vec;

const VALUES: inplace_containers::InplaceVector<i32, 3> = inplace_vec![1, 2, 3];
assert_eq!(VALUES, &[1, 2, 3]);
```

**Key methods reference:**

| Method | Signature | Description |
|--------|----------|-------------|
| `new` | `fn new() -> Self` | Creates an empty vector |
| `len` | `fn len(&self) -> usize` | Returns current length |
| `is_empty` | `fn is_empty(&self) -> bool` | Checks if vector is empty |
| `is_full` | `fn is_full(&self) -> bool` | Checks if vector reached capacity |
| `CAPACITY` | `const CAPACITY: usize` | Compile-time fixed capacity |
| `capacity` | `fn capacity(&self) -> usize` | Returns fixed capacity |
| `remaining_capacity` | `fn remaining_capacity(&self) -> usize` | Returns remaining capacity |
| `push` | `fn push(&mut self, value: T)` | Adds element, panics if full |
| `try_push` | `fn try_push(&mut self, value: T) -> Result<(), InplaceError>` | Adds element safely |
| `pop` | `fn pop(&mut self) -> Option<T>` | Removes last element |
| `insert` | `fn insert(&mut self, idx: usize, value: T)` | Inserts at index |
| `remove` | `fn remove(&mut self, idx: usize) -> T` | Removes element at index |
| `swap_remove` | `fn swap_remove(&mut self, idx: usize) -> T` | Removes element, replaces with last |
| `extend_from_slice` | `fn extend_from_slice(&mut self, slice: &[T])` | Appends elements from slice |
| `truncate` | `fn truncate(&mut self, new_len: usize)` | Shortens vector |
| `clear` | `fn clear(&mut self)` | Removes all elements |
| `split_off` | `fn split_off(&mut self, at: usize) -> Self` | Splits vector at index |
| `drain` | `fn drain<R>(&mut self, range: R) -> InplaceVector<T, N>` | Extracts range |

Fixed-size arrays can be cloned into an `InplaceVector`. The trait is also available through wrappers that dereference to an array:

```rust
use inplace_containers::prelude::*;

let values = [1, 2, 3];
let vector = values.to_inplace_owned();
assert_eq!(vector, &[1, 2, 3]);
```

---

### `InplaceString<N>`

A fixed-capacity, stack-allocated string type.

```rust
use inplace_containers::inplace_string;

// The macro creates an empty inline string with room for ten UTF-8 bytes.
let mut s = inplace_string![10;];
s.push_str("hello");
s.push(' ');
s.push_str("rust");

assert_eq!(s.len(), 10);
assert_eq!(s.as_str(), "hello rust");
```

Const construction is supported for string literals:

```rust
use inplace_containers::{inplace_string, InplaceString};

const VALUE: InplaceString<5> = inplace_string!("hello");
assert_eq!(VALUE, "hello");
```

**Key methods reference:**

| Method | Signature | Description |
|--------|----------|-------------|
| `new` | `fn new() -> Self` | Creates an empty string |
| `len` | `fn len(&self) -> usize` | Returns length in bytes |
| `is_empty` | `fn is_empty(&self) -> bool` | Checks if empty |
| `CAPACITY` | `const CAPACITY: usize` | Compile-time fixed capacity in bytes |
| `capacity` | `fn capacity(&self) -> usize` | Returns fixed capacity |
| `remaining_capacity` | `fn remaining_capacity(&self) -> usize` | Returns remaining capacity |
| `push` | `fn push(&mut self, ch: char)` | Appends a char, panics if full |
| `try_push` | `fn try_push(&mut self, ch: char) -> Result<(), InplaceError>` | Safe char push |
| `push_str` | `fn push_str(&mut self, s: &str)` | Appends string, panics if full |
| `try_push_str` | `fn try_push_str(&mut self, s: &str) -> Result<(), InplaceError>` | Safe string push |
| `insert` | `fn insert(&mut self, idx: usize, ch: char)` | Inserts char at index |
| `insert_str` | `fn insert_str(&mut self, idx: usize, s: &str)` | Inserts string at index |
| `remove` | `fn remove(&mut self, idx: usize) -> char` | Removes char at index |
| `drain` | `fn drain<R>(&mut self, range: R) -> StringDrain<'_, N>` | Removes a byte range on char boundaries and yields the removed chars |
| `pop` | `fn pop(&mut self) -> Option<char>` | Removes last char |
| `clear` | `fn clear(&mut self)` | Clears the string |
| `truncate` | `fn truncate(&mut self, new_len: usize)` | Shortens string to new_len |
| `split_off` | `fn split_off(&mut self, at: usize) -> Self` | Splits string at index |
| `into_bytes` | `fn into_bytes(self) -> InplaceVector<u8, N>` | Converts to byte vector |
| `as_bytes` | `fn as_bytes(&self) -> &[u8]` | Returns byte slice |
| `as_mut_bytes` | `unsafe fn as_mut_bytes(&mut self) -> &mut [u8]` | Mutable byte slice |

---

### Bounded formatting

`BoundedDisplay::to_inplace_string()` formats values directly into an `InplaceString<20>`. It is implemented for integer types through `isize`, as well as `bool` and `char`:

```rust
use inplace_containers::BoundedDisplay;

let value = isize::MIN;
let string = value.to_inplace_string();
assert_eq!(string.as_str(), value.to_string());
```

---

### Macros

- `inplace_string![CAP; "literal"]` - creates an `InplaceString` with explicit capacity.
- `inplace_string![CAP;]` - creates an empty `InplaceString` with explicit capacity.

- `inplace_vec![...]` – stack-allocated vector creation with optional compile-time capacity checking.
- `inplace_string!("...")` – creates an `InplaceString` from a literal, including in const contexts.

```rust
use inplace_containers::{inplace_vec, inplace_string};

// Explicit compile-time capacity, with fewer initial elements than slots.
let vec = inplace_vec![4; 1, 2, 3];
// Capacity inferred directly from the literal length.
let s = inplace_string!("hello");
// Explicit capacity when the inline buffer should be larger than the literal.
let s2 = inplace_string![10; "hello"];
// Empty string with capacity chosen up front.
let s3 = inplace_string![10;];
```

---

## Safety Notes

- `unsafe` is used internally for performance.
- Methods like `unchecked_push`, `unchecked_insert`, and `set_len` bypass checks.
- Safe `InplaceString` constructors and mutation methods preserve UTF-8; `unsafe` methods require the caller to maintain capacity and UTF-8 invariants.

---

## License

MIT OR Apache-2.0

