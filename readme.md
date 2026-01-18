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
- Compile-time capacity checks with `inplace_vec!` macro.

---

## Containers

### `InplaceVector<T, N>`

A fixed-capacity vector that stores `N` elements of type `T` inline.

```rust
use inplace_containers::InplaceVector;

let mut vec = InplaceVector::<i32, 5>::new();
vec.push(1);
vec.push(2);
vec.extend_from_slice(&[3, 4, 5]);

assert_eq!(vec.len(), 5);
assert!(vec.is_full());

let last = vec.pop();
assert_eq!(last, Some(5));
```

**Key methods reference:**

| Method | Signature | Description |
|--------|----------|-------------|
| `new` | `fn new() -> Self` | Creates an empty vector |
| `len` | `fn len(&self) -> usize` | Returns current length |
| `is_empty` | `fn is_empty(&self) -> bool` | Checks if vector is empty |
| `is_full` | `fn is_full(&self) -> bool` | Checks if vector reached capacity |
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

---

### `InplaceString<N>`

A fixed-capacity, stack-allocated string type.

```rust
use inplace_containers::InplaceString;

let mut s: InplaceString<10> = InplaceString::new();
s.push_str("hello");
s.push(' ');
s.push_str("rust");

assert_eq!(s.len(), 10);
assert_eq!(s.as_str(), "hello rust");
```

**Key methods reference:**

| Method | Signature | Description |
|--------|----------|-------------|
| `new` | `fn new() -> Self` | Creates an empty string |
| `len` | `fn len(&self) -> usize` | Returns length in bytes |
| `is_empty` | `fn is_empty(&self) -> bool` | Checks if empty |
| `capacity` | `fn capacity(&self) -> usize` | Returns fixed capacity |
| `remaining_capacity` | `fn remaining_capacity(&self) -> usize` | Returns remaining capacity |
| `push` | `fn push(&mut self, ch: char)` | Appends a char, panics if full |
| `try_push` | `fn try_push(&mut self, ch: char) -> Result<(), InplaceError>` | Safe char push |
| `push_str` | `fn push_str(&mut self, s: &str)` | Appends string, panics if full |
| `try_push_str` | `fn try_push_str(&mut self, s: &str) -> Result<(), InplaceError>` | Safe string push |
| `insert` | `fn insert(&mut self, idx: usize, ch: char)` | Inserts char at index |
| `insert_str` | `fn insert_str(&mut self, idx: usize, s: &str)` | Inserts string at index |
| `remove` | `fn remove(&mut self, idx: usize) -> char` | Removes char at index |
| `pop` | `fn pop(&mut self) -> Option<char>` | Removes last char |
| `clear` | `fn clear(&mut self)` | Clears the string |
| `truncate` | `fn truncate(&mut self, new_len: usize)` | Shortens string to new_len |
| `split_off` | `fn split_off(&mut self, at: usize) -> Self` | Splits string at index |
| `into_bytes` | `fn into_bytes(self) -> InplaceVector<u8, N>` | Converts to byte vector |
| `as_bytes` | `fn as_bytes(&self) -> &[u8]` | Returns byte slice |
| `as_mut_bytes` | `unsafe fn as_mut_bytes(&mut self) -> &mut [u8]` | Mutable byte slice |

---

### Macros

- `inplace_vec![...]` – stack-allocated vector creation with optional compile-time capacity checking.
- `inplace_string!("...")` – creates an `InplaceString` from a literal.

```rust
use inplace_containers::{inplace_vec, inplace_string};

let vec = inplace_vec![4; 1, 2, 3];
let s = inplace_string!("hello");
```

---

## Safety Notes

- `unsafe` is used internally for performance.
- Methods like `unchecked_push`, `unchecked_insert`, and `set_len` bypass checks.
- Always ensure capacity is not exceeded to avoid undefined behavior.
- `InplaceString` UTF-8 safety is only guaranteed for literals or checked strings.

---

## License

MIT OR Apache-2.0

