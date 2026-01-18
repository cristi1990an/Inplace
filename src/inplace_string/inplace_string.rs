mod details {

    /// UTF-8 continuation byte tag: `10xxxxxx`    
    const TAG_CONT: u8 = 0b1000_0000;
    /// UTF-8 2-byte leading tag: `110xxxxx`
    const TAG_TWO_B: u8 = 0b1100_0000;
    /// UTF-8 3-byte leading tag: `1110xxxx`
    const TAG_THREE_B: u8 = 0b1110_0000;
    /// UTF-8 4-byte leading tag: `11110xxx`
    const TAG_FOUR_B: u8 = 0b1111_0000;
    /// Maximum scalar value representable in 1 UTF-8 byte.
    const MAX_ONE_B: u32 = 0x80;
    /// Maximum scalar value representable in 2 UTF-8 bytes.
    const MAX_TWO_B: u32 = 0x800;
    /// Maximum scalar value representable in 3 UTF-8 bytes.
    const MAX_THREE_B: u32 = 0x10000;

    /// Returns the number of bytes required to encode a Unicode scalar value
    /// in UTF-8.
    ///
    /// This function assumes `code` is a valid Unicode scalar value.
    const fn len_utf8(code: u32) -> usize {
        match code {
            ..MAX_ONE_B => 1,
            ..MAX_TWO_B => 2,
            ..MAX_THREE_B => 3,
            _ => 4,
        }
    }

    /// Encodes a Unicode scalar value into UTF-8 at the given destination
    /// pointer **without performing any validation**.
    ///
    /// # Safety
    ///
    /// - `code` must be a valid Unicode scalar value.
    /// - `dst` must point to at least `len_utf8(code)` writable bytes.
    /// - No bounds or aliasing checks are performed.
    pub(crate) const unsafe fn encode_utf8_raw_unchecked(code: u32, dst: *mut u8) {
        let len = len_utf8(code);
        unsafe {
            if len == 1 {
                *dst = code as u8;
                return;
            }

            let last1 = (code & 0x3F) as u8 | TAG_CONT;
            let last2 = (code >> 6 & 0x3F) as u8 | TAG_CONT;
            let last3 = (code >> 12 & 0x3F) as u8 | TAG_CONT;
            let last4 = (code >> 18 & 0x3F) as u8 | TAG_FOUR_B;

            if len == 2 {
                *dst = last2 | TAG_TWO_B;
                *dst.add(1) = last1;
                return;
            }

            if len == 3 {
                *dst = last3 | TAG_THREE_B;
                *dst.add(1) = last2;
                *dst.add(2) = last1;
                return;
            }

            *dst = last4;
            *dst.add(1) = last3;
            *dst.add(2) = last2;
            *dst.add(3) = last1;
        }
    }
}

use core::fmt;
use core::{
    fmt::{Debug, Write},
    hash::Hash,
    num::NonZeroUsize,
    ops::{Add, AddAssign, Deref, DerefMut, RangeBounds},
    ptr,
    str::FromStr,
};

use crate::InplaceVector;

/// A fixed-capacity, UTF-8 encoded string stored inline.
///
/// `InplaceString<N>` stores up to `N` bytes of UTF-8 data without heap
/// allocation. Always implements the Copy trait. All operations preserve UTF-8 validity.
///
/// The length is stored using a `NonZeroUsize` to enable niche optimization,
/// making `Option<InplaceString<N>>` the same size as `InplaceString<N>`.
#[derive(Clone, Copy)]
pub struct InplaceString<const N: usize> {
    data: [u8; N],
    size: NonZeroUsize,
}

#[derive(Debug)]
pub struct InplaceError {
    current_size: usize,
    capacity: usize,
    required_capacity: usize,
}

impl std::fmt::Display for InplaceError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "InplaceString growt should not exceed capacity.
                Capacity: {} Size: {} Len of string to push: {}",
            self.capacity, self.current_size, self.required_capacity
        )
    }
}

impl std::error::Error for InplaceError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        None
    }
}

#[derive(Debug)]
pub enum InplaceUtf8Error {
    Utf8Error(std::str::Utf8Error),
    InplaceError(InplaceError),
}

impl std::error::Error for InplaceUtf8Error {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        None
    }
}

impl std::fmt::Display for InplaceUtf8Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            InplaceUtf8Error::Utf8Error(utf8_error) => write!(f, "{}", utf8_error),
            InplaceUtf8Error::InplaceError(inplace_error) => write!(f, "{}", inplace_error),
        }
    }
}

impl<const N: usize> InplaceString<N> {
    /// Creates a new empty `InplaceString`.
    ///
    /// Capacity is fixed at `N`.
    pub const fn new() -> Self {
        InplaceString {
            data: [const { 0 }; N],
            size: unsafe { NonZeroUsize::new_unchecked(1) },
        }
    }

    /// Returns the string as a `&str`.
    ///
    /// This is always safe because all mutations preserve UTF-8 validity.
    pub fn as_str(&self) -> &str {
        unsafe { str::from_utf8_unchecked(self.data.get_unchecked(..self.len())) }
    }

    /// Returns the string as a mutable `&mut str`.
    pub fn as_mut_str(&mut self) -> &mut str {
        let len = self.len();
        unsafe { str::from_utf8_unchecked_mut(self.data.get_unchecked_mut(..len)) }
    }

    /// Returns the underlying bytes of the string.
    pub fn as_bytes(&self) -> &[u8] {
        &self.data[..self.len()]
    }

    /// Returns the fixed capacity of this string.
    pub const fn capacity(&self) -> usize {
        N
    }

    /// Returns remaining unused capacity.
    pub const fn remaining_capacity(&self) -> usize {
        N - self.len()
    }

    /// Returns `true` if the string is at full capacity.
    pub const fn is_full(&self) -> bool {
        self.remaining_capacity() == 0
    }

    /// Appends a character without checking capacity.
    ///
    /// # Safety
    ///
    /// - `ch.len_utf8()` must be <= `remaining_capacity()`
    /// - Violating this causes out-of-bounds writes and UB.
    pub unsafe fn unchecked_push(&mut self, ch: char) {
        let len = self.len();
        let ch_len = ch.len_utf8();
        debug_assert!(ch_len <= self.remaining_capacity());
        unsafe {
            details::encode_utf8_raw_unchecked(ch as u32, self.data.as_mut_ptr().add(self.len()));
            self.set_len(len + ch_len);
        }
    }

    /// Attempts to append a character, returning an error if capacity is exceeded.
    pub fn try_push(&mut self, ch: char) -> Result<(), InplaceError> {
        let ch_len = ch.len_utf8();
        if self.remaining_capacity() < ch_len {
            return Err(InplaceError {
                current_size: self.len(),
                capacity: N,
                required_capacity: ch_len,
            });
        }

        unsafe { self.unchecked_push(ch) };
        Ok(())
    }

    /// Appends a character, panicking if capacity is exceeded.
    pub fn push(&mut self, ch: char) {
        self.try_push(ch).unwrap();
    }

    /// Appends the slice into the string without checking that capacity is not exceeded.
    /// This is a low-level operation that can be used to optimize multiple unchecked_push_str calls when
    /// the final size is known by the user to not exceed the total capacity.
    ///
    /// # Safety
    ///
    /// - string.len should not be greater than remaining_capacity
    /// - undefined behavior otherwise.
    ///
    pub unsafe fn unchecked_push_str(&mut self, string: &str) {
        let string_len = string.len();
        debug_assert!(string_len <= self.remaining_capacity());
        unsafe {
            std::ptr::copy(
                string.as_ptr(),
                self.data.as_mut_ptr().add(self.len()),
                string_len,
            );
            self.set_len(self.len() + string_len);
        }
    }

    pub fn try_push_str(&mut self, string: &str) -> Result<(), InplaceError> {
        let string_len = string.len();
        if self.remaining_capacity() < string_len {
            return Err(InplaceError {
                current_size: self.len(),
                capacity: N,
                required_capacity: string_len,
            });
        }
        unsafe {
            self.unchecked_push_str(string);
        }

        Ok(())
    }

    pub fn push_str(&mut self, string: &str) {
        self.try_push_str(string).unwrap();
    }

    /// Inserts a new char into the string without checking that capacity is not exceeded.
    /// This is a low-level operation that can be used to optimize multiple insert calls when
    /// the final size is known by the user to not exceed the total capacity.
    ///
    /// # Safety
    ///
    /// - ch.len_utf8() should not be greater than remaining_capacity()
    /// - undefined behavior otherwise.
    ///
    pub unsafe fn unchecked_insert(&mut self, idx: usize, ch: char) {
        assert!(self.is_char_boundary(idx));
        debug_assert!(ch.len_utf8() <= self.remaining_capacity());

        let len = self.len();
        let ch_len = ch.len_utf8();

        let base = self.data.as_mut_ptr();
        unsafe {
            ptr::copy(base.add(idx), base.add(idx + ch_len), len - idx);
            details::encode_utf8_raw_unchecked(ch as u32, self.data.as_mut_ptr().add(idx));
            self.set_len(len + ch_len);
        }
    }

    pub fn try_insert(&mut self, idx: usize, ch: char) -> Result<(), InplaceError> {
        let ch_len = ch.len_utf8();
        if self.remaining_capacity() < ch_len {
            return Err(InplaceError {
                current_size: self.len(),
                capacity: N,
                required_capacity: ch_len,
            });
        }

        unsafe { self.unchecked_insert(idx, ch) };
        Ok(())
    }

    /// Inserts the slice into the string without checking that capacity is not exceeded.
    /// This is a low-level operation that can be used to optimize multiple insert calls when
    /// the final size is known by the user to not exceed the total capacity.
    ///
    /// # Safety
    ///
    /// - string.len should not be greater than remaining_capacity
    /// - undefined behavior otherwise.
    ///
    pub unsafe fn unchecked_insert_str(&mut self, idx: usize, string: &str) {
        assert!(self.is_char_boundary(idx));
        assert!(string.len() <= self.remaining_capacity());

        let len = self.len();
        let amt = string.len();

        self.unchecked_push_str(string);
        self.as_mut_bytes()[idx..len + amt].rotate_right(amt);
    }

    pub fn try_insert_str(&mut self, idx: usize, string: &str) -> Result<(), InplaceError> {
        let amt = string.len();

        if amt > self.remaining_capacity() {
            return Err(InplaceError {
                current_size: self.len(),
                capacity: N,
                required_capacity: amt,
            });
        }

        unsafe { self.unchecked_insert_str(idx, string) };

        Ok(())
    }

    pub fn insert_str(&mut self, idx: usize, string: &str) {
        self.try_insert_str(idx, string).unwrap();
    }

    pub fn insert(&mut self, idx: usize, ch: char) {
        self.try_insert(idx, ch).unwrap();
    }

    pub fn extend_from_within<R>(&mut self, src: R)
    where
        R: RangeBounds<usize>,
    {
        let len = self.len();

        // resolve start bound
        let start = match src.start_bound() {
            std::ops::Bound::Included(&i) => i,
            std::ops::Bound::Excluded(&i) => i + 1,
            std::ops::Bound::Unbounded => 0,
        };

        // resolve end bound
        let end = match src.end_bound() {
            std::ops::Bound::Included(&i) => i + 1,
            std::ops::Bound::Excluded(&i) => i,
            std::ops::Bound::Unbounded => len,
        };

        assert!(start <= end, "range start > end");
        assert!(end <= len, "range end out of bounds");

        assert!(self.is_char_boundary(start));
        assert!(self.is_char_boundary(end));

        let count = end - start;
        let new_len = len.checked_add(count).expect("overflow");

        assert!(new_len <= N, "InplaceString capacity exceeded");

        unsafe {
            let ptr = self.as_mut_ptr();

            ptr::copy(ptr.add(start), ptr.add(len), count);
            self.set_len(new_len);
        }
    }

    /// Forces the length of the string to new_len.
    /// This is a low-level operation that maintains none of the normal invariants of the type.
    ///
    /// # Safety
    ///
    /// - new_len must be less than or equal to capacity().
    /// - the elements at old_len..new_len must represent a valid UTF8 sequence.
    ///
    pub unsafe fn set_len(&mut self, new_len: usize) {
        debug_assert!(new_len <= N);
        self.size = NonZeroUsize::new_unchecked(new_len.add(1));
    }

    /// Returns the current length in bytes.
    pub const fn len(&self) -> usize {
        unsafe { self.size.get().unchecked_sub(1) }
    }

    /// Returns `true` if the string is empty.
    pub const fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub fn clear(&mut self) {
        unsafe { self.set_len(0) };
    }

    pub fn pop(&mut self) -> Option<char> {
        let ch = self.chars().next_back()?;
        let newlen = self.len() - ch.len_utf8();
        unsafe {
            self.set_len(newlen);
        }
        Some(ch)
    }

    pub fn truncate(&mut self, new_len: usize) {
        if new_len < self.len() {
            assert!(self.is_char_boundary(new_len));
            unsafe { self.set_len(new_len) };
        }
    }

    pub fn split_off(&mut self, at: usize) -> Self {
        let (_, split) = self.as_bytes().split_at(at);
        assert!(self.is_char_boundary(at));
        let result = unsafe { Self::from_utf8_unchecked(split) };
        unsafe {
            self.set_len(at);
        }

        result
    }

    pub fn from_utf8(v: &[u8]) -> Result<Self, InplaceUtf8Error> {
        match str::from_utf8(v) {
            Ok(str) => Self::try_from(str).map_err(InplaceUtf8Error::InplaceError),
            Err(err) => Err(InplaceUtf8Error::Utf8Error(err)),
        }
    }

    /// Converts a slice of bytes to a string slice without checking that the string contains valid UTF-8.
    ///
    /// This is an alias to str::from_utf8_unchecked.
    ///
    /// See the safe version, from_utf8, for more information.
    ///
    /// # Panics
    /// Panics if bytes.len() > N
    ///
    /// # Safety
    /// The bytes passed in must be valid UTF-8.
    ///
    pub unsafe fn from_utf8_unchecked(bytes: &[u8]) -> Self {
        if bytes.len() > N {
            panic!(
                "Length of array passed to from_utf8_unchecked would exceed InplaceString capacity"
            );
        }

        debug_assert!(str::from_utf8(bytes).is_ok());

        let mut result = Self::new();
        unsafe {
            std::ptr::copy_nonoverlapping(bytes.as_ptr(), result.data.as_mut_ptr(), bytes.len());
            result.set_len(bytes.len());
        }
        result
    }

    pub fn from_utf8_lossy(v: &[u8]) -> Self {
        let mut iter = v.utf8_chunks();

        let first_valid = if let Some(chunk) = iter.next() {
            let valid = chunk.valid();
            if chunk.invalid().is_empty() {
                debug_assert_eq!(valid.len(), v.len());
                return unsafe { Self::from_utf8_unchecked(valid.as_bytes()) };
            }
            valid
        } else {
            return Self::new();
        };

        const REPLACEMENT: &str = "\u{FFFD}";

        let mut res = Self::new();
        res.push_str(first_valid);
        res.push_str(REPLACEMENT);

        for chunk in iter {
            res.push_str(chunk.valid());
            if !chunk.invalid().is_empty() {
                res.push_str(REPLACEMENT);
            }
        }

        res
    }

    pub fn into_bytes(self) -> InplaceVector<u8, N> {
        let mut result = InplaceVector::new();

        unsafe {
            std::ptr::copy_nonoverlapping(self.as_ptr(), result.as_mut_ptr(), self.len());
            result.set_len(self.len());
        }

        result
    }

    /// Returns a mutable reference to the contents of this InplaceString.
    ///
    /// # Safety
    /// This function is unsafe because the returned &mut [u8] allows writing bytes which are not valid UTF-8.
    /// If this constraint is violated, using the original InplaceString after dropping the
    /// &mut [u8] may violate memory safety.
    pub unsafe fn as_mut_bytes(&mut self) -> &mut [u8] {
        let len = self.len();
        &mut self.data[..len]
    }

    pub fn remove(&mut self, idx: usize) -> char {
        let ch = match self[idx..].chars().next() {
            Some(ch) => ch,
            None => panic!("cannot remove a char from the end of a string"),
        };

        let next = idx + ch.len_utf8();
        let len = self.len();
        unsafe {
            std::ptr::copy(
                self.as_ptr().add(next),
                self.as_mut_ptr().add(idx),
                len - next,
            );
            self.set_len(len - (next - idx));
        }

        ch
    }
}

impl<const N: usize> Deref for InplaceString<N> {
    type Target = str;

    fn deref(&self) -> &Self::Target {
        self.as_str()
    }
}

impl<const N: usize> DerefMut for InplaceString<N> {
    fn deref_mut(&mut self) -> &mut str {
        self.as_mut_str()
    }
}

impl<const N: usize> TryFrom<&str> for InplaceString<N> {
    type Error = InplaceError;

    fn try_from(value: &str) -> Result<Self, Self::Error> {
        let str_len = value.len();
        if N < str_len {
            return Err(InplaceError {
                current_size: 0,
                capacity: N,
                required_capacity: str_len,
            });
        }

        let mut result = Self::new();
        unsafe { result.unchecked_push_str(value) };
        Ok(result)
    }
}

impl<const N: usize> TryFrom<&mut str> for InplaceString<N> {
    type Error = InplaceError;

    fn try_from(value: &mut str) -> Result<Self, Self::Error> {
        (value as &str).try_into()
    }
}

impl<const N: usize> TryFrom<String> for InplaceString<N> {
    type Error = InplaceError;

    fn try_from(value: String) -> Result<Self, Self::Error> {
        value.as_str().try_into()
    }
}

impl<const N: usize> TryFrom<char> for InplaceString<N> {
    type Error = InplaceError;

    fn try_from(value: char) -> Result<Self, Self::Error> {
        let ch_len = value.len_utf8();
        if N < ch_len {
            return Err(InplaceError {
                current_size: 0,
                capacity: N,
                required_capacity: ch_len,
            });
        }

        let mut result = Self::new();
        unsafe { result.unchecked_push(value) };
        Ok(result)
    }
}

impl<const N: usize> TryFrom<InplaceVector<u8, N>> for InplaceString<N> {
    type Error = std::str::Utf8Error;

    fn try_from(value: InplaceVector<u8, N>) -> Result<Self, Self::Error> {
        let str = std::str::from_utf8(&value)?;

        let mut result = InplaceString::new();

        unsafe {
            std::ptr::copy_nonoverlapping(str.as_ptr(), result.as_mut_ptr(), str.len());
            result.set_len(str.len());
        };

        Ok(result)
    }
}

impl<'a, const N: usize> FromIterator<&'a char> for InplaceString<N> {
    fn from_iter<T: IntoIterator<Item = &'a char>>(iter: T) -> Self {
        let mut result = Self::new();
        for ch in iter {
            result.try_push(*ch).expect("capacity exceeded");
        }
        result
    }
}

impl<const N: usize> FromStr for InplaceString<N> {
    type Err = InplaceError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Self::try_from(s)
    }
}

impl<const N: usize> Hash for InplaceString<N> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.as_str().hash(state);
    }
}

impl<const N: usize> PartialOrd for InplaceString<N> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl<const N: usize> Ord for InplaceString<N> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.as_str().cmp(other)
    }
}

impl<const N: usize> Write for InplaceString<N> {
    fn write_str(&mut self, s: &str) -> std::fmt::Result {
        self.try_push_str(s).map_err(|_| std::fmt::Error)?;
        Ok(())
    }
}

impl<const N: usize, I> std::ops::Index<I> for InplaceString<N>
where
    I: std::slice::SliceIndex<str>,
{
    type Output = I::Output;

    fn index(&self, index: I) -> &Self::Output {
        self.as_str().index(index)
    }
}

impl<const N: usize, I> std::ops::IndexMut<I> for InplaceString<N>
where
    I: std::slice::SliceIndex<str>,
{
    fn index_mut(&mut self, index: I) -> &mut Self::Output {
        self.as_mut_str().index_mut(index)
    }
}

impl<const N: usize> TryFrom<&[u8]> for InplaceString<N> {
    type Error = InplaceUtf8Error;

    fn try_from(value: &[u8]) -> Result<Self, Self::Error> {
        Self::from_utf8(value)
    }
}

impl<const N: usize> AsRef<[u8]> for InplaceString<N> {
    fn as_ref(&self) -> &[u8] {
        self.as_bytes()
    }
}

impl<const N: usize> AsRef<str> for InplaceString<N> {
    fn as_ref(&self) -> &str {
        self.as_str()
    }
}

impl<const N: usize> std::borrow::Borrow<str> for InplaceString<N> {
    fn borrow(&self) -> &str {
        self
    }
}

impl<const N: usize> std::borrow::BorrowMut<str> for InplaceString<N> {
    fn borrow_mut(&mut self) -> &mut str {
        self.as_mut_str()
    }
}

impl<const N: usize> Default for InplaceString<N> {
    fn default() -> Self {
        Self::new()
    }
}

// impl<const Lhs: usize, const Rhs: usize> Add<InplaceString<Lhs>> for InplaceString<Rhs>
// {
//     type Output = InplaceString<{Lhs + Rhs}>;

//     fn add(self, rhs: InplaceString<Lhs>) -> Self::Output {
//         todo!()
//     }
// }

impl<const N: usize> Add<&str> for InplaceString<N> {
    type Output = InplaceString<N>;

    fn add(mut self, rhs: &str) -> Self::Output {
        self.push_str(rhs);
        self
    }
}

impl<const N: usize> AddAssign<&str> for InplaceString<N> {
    fn add_assign(&mut self, rhs: &str) {
        self.push_str(rhs);
    }
}

impl<const N: usize> AsMut<str> for InplaceString<N> {
    fn as_mut(&mut self) -> &mut str {
        self.as_mut_str()
    }
}

impl<const N: usize> Debug for InplaceString<N> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct(concat!("InplaceString<", stringify!(N), ">"))
            .field("string", &self.as_str())
            .field("size", &self.len())
            .finish()
    }
}

impl<const N: usize> std::fmt::Display for InplaceString<N> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        fmt::Display::fmt(&**self, f)
    }
}

impl<const N: usize> PartialEq for InplaceString<N> {
    fn eq(&self, other: &Self) -> bool {
        self.as_str() == other.as_str()
    }
}

impl<const N: usize> PartialEq<InplaceString<N>> for &str {
    fn eq(&self, other: &InplaceString<N>) -> bool {
        *self == other.as_str()
    }
}

impl<const N: usize> PartialEq<&str> for InplaceString<N> {
    fn eq(&self, other: &&str) -> bool {
        self.as_str() == *other
    }
}

impl<const N: usize> Extend<char> for InplaceString<N> {
    fn extend<T: IntoIterator<Item = char>>(&mut self, iter: T) {
        for ch in iter {
            self.push(ch);
        }
    }
}

impl<'a, const N: usize> Extend<&'a str> for InplaceString<N> {
    fn extend<T: IntoIterator<Item = &'a str>>(&mut self, iter: T) {
        for string in iter {
            self.push_str(string);
        }
    }
}

impl<const N: usize> Eq for InplaceString<N> {}

/// A helper trait for formatting values into a bounded `InplaceString`.
///
/// Implemented only for basic types guaranteed that their string formatted size will not exceed 20 bytes.
pub trait BoundedDisplay: core::fmt::Display {
    /// Formats `self` into an `InplaceString<20>`. Should never panic.
    ///
    fn to_inplace_string(&self) -> InplaceString<20> {
        let mut result = InplaceString::<20>::new();
        use core::fmt::Write;
        write!(&mut result, "{}", self).expect("This shouldn't fail :)");
        result
    }
}

impl BoundedDisplay for u8 {}

impl BoundedDisplay for i8 {}

impl BoundedDisplay for i16 {}

impl BoundedDisplay for u16 {}

impl BoundedDisplay for u32 {}

impl BoundedDisplay for i32 {}

impl BoundedDisplay for u64 {}

impl BoundedDisplay for i64 {}

impl BoundedDisplay for usize {}

impl BoundedDisplay for bool {}

impl BoundedDisplay for char {}

#[cfg(test)]
mod tests {
    use super::*;

    const CAP: usize = 16;

    #[test]
    fn test_u8_bounded_display() {
        let value: u8 = 255;
        let s = value.to_inplace_string();
        assert_eq!(s.as_str(), "255");
        assert!(value.to_string().len() <= 20);
    }

    #[test]
    fn test_i8_bounded_display() {
        let value: i8 = -128;
        let s = value.to_inplace_string();
        assert_eq!(s.as_str(), "-128");
        assert!(value.to_string().len() <= 20);
    }

    #[test]
    fn test_u32_bounded_display() {
        let value: u32 = 4_294_967_295;
        let s = value.to_inplace_string();
        assert_eq!(s.as_str(), "4294967295");
        assert!(value.to_string().len() <= 20);
    }

    #[test]
    fn test_i32_bounded_display() {
        let value: i32 = -2_147_483_648;
        let s = value.to_inplace_string();
        assert_eq!(s.as_str(), "-2147483648");
        assert!(value.to_string().len() <= 20);
    }

    #[test]
    fn test_u64_bounded_display() {
        let value: u64 = 18_446_744_073_709_551_615;
        let s = value.to_inplace_string();
        assert_eq!(s.as_str(), "18446744073709551615");
        assert!(value.to_string().len() <= 20);
    }

    #[test]
    fn test_i64_bounded_display() {
        let value: i64 = -9_223_372_036_854_775_808;
        let s = value.to_inplace_string();
        assert_eq!(s.as_str(), "-9223372036854775808");
        assert!(value.to_string().len() <= 20);
    }

    #[test]
    fn test_usize_bounded_display() {
        let value: usize = 123456789;
        let s = value.to_inplace_string();
        assert_eq!(s.as_str(), "123456789");
        assert!(value.to_string().len() <= 20);
    }

    #[test]
    fn test_bool_bounded_display() {
        let t = true.to_inplace_string();
        let f = false.to_inplace_string();
        assert_eq!(t.as_str(), "true");
        assert_eq!(f.as_str(), "false");
        assert!(t.to_string().len() <= 20);
        assert!(f.to_string().len() <= 20);
    }

    #[test]
    fn test_char_bounded_display() {
        let ch = 'β';
        let s = ch.to_inplace_string();
        assert_eq!(s.as_str(), "β");
        assert!(ch.to_string().len() <= 20);
    }

    #[test]
    fn test_new_and_basic_properties() {
        let s: InplaceString<CAP> = InplaceString::new();
        assert_eq!(s.len(), 0);
        assert!(s.is_empty());
        assert_eq!(s.capacity(), CAP);
        assert_eq!(s.remaining_capacity(), CAP);
        assert!(!s.is_full());
    }

    #[test]
    fn test_push_and_try_push() {
        let mut s: InplaceString<CAP> = InplaceString::new();
        s.push('a');
        assert_eq!(s.as_str(), "a");

        s.try_push('β').unwrap();
        assert_eq!(s.as_str(), "aβ");

        let mut s: InplaceString<1> = InplaceString::new();
        let err = s.try_push('β').unwrap_err();
        assert_eq!(err.current_size, 0);
        assert_eq!(err.required_capacity, 2);
    }

    #[test]
    fn test_push_str_and_try_push_str() {
        let mut s: InplaceString<CAP> = InplaceString::new();
        s.push_str("hello");
        assert_eq!(s.as_str(), "hello");

        s.try_push_str(" world").unwrap();
        assert_eq!(s.as_str(), "hello world");

        let mut s: InplaceString<5> = InplaceString::new();
        let err = s.try_push_str("toolong").unwrap_err();
        assert_eq!(err.required_capacity, 7);
    }

    #[test]
    fn test_insert_and_insert_str() {
        let mut s: InplaceString<CAP> = InplaceString::new();
        s.push_str("ac");
        s.insert(1, 'b');
        assert_eq!(s, "abc");

        s.insert_str(1, "XYZ");
        assert_eq!(s, "aXYZbc");
    }

    #[test]
    fn test_unchecked_push_and_insert() {
        let mut s: InplaceString<CAP> = InplaceString::new();
        unsafe {
            s.unchecked_push('α');
            s.unchecked_push('β');
            s.unchecked_insert(2, 'γ');
        }
        assert_eq!(s.as_str(), "αγβ");
    }

    #[test]
    fn test_pop_and_remove() {
        let mut s: InplaceString<CAP> = InplaceString::new();
        s.push_str("aβγ");
        let ch = s.pop().unwrap();
        assert_eq!(ch, 'γ');
        assert_eq!(s.as_str(), "aβ");

        let removed = s.remove(1);
        assert_eq!(removed, 'β');
        assert_eq!(s.as_str(), "a");
    }

    #[test]
    fn test_clear_and_is_empty() {
        let mut s: InplaceString<CAP> = InplaceString::new();
        s.push_str("test");
        assert!(!s.is_empty());
        s.clear();
        assert!(s.is_empty());
        assert_eq!(s.len(), 0);
    }

    #[test]
    fn test_from_utf8() {
        let bytes = "hello β".as_bytes();
        let s: InplaceString<CAP> = InplaceString::from_utf8(bytes).unwrap();
        assert_eq!(s.as_str(), "hello β");

        let invalid_bytes = &[0xFF, 0xFF];
        let err = InplaceString::<CAP>::from_utf8(invalid_bytes).unwrap_err();
        match err {
            InplaceUtf8Error::Utf8Error(_) => {}
            _ => panic!("Expected Utf8Error"),
        }
    }

    #[test]
    fn test_from_utf8_unchecked() {
        let bytes = "αβγ".as_bytes();
        let s = unsafe { InplaceString::<CAP>::from_utf8_unchecked(bytes) };
        assert_eq!(s.as_str(), "αβγ");
    }

    #[test]
    fn test_try_from_various() {
        let s: InplaceString<CAP> = "hello".try_into().unwrap();
        assert_eq!(s, "hello");

        let ch: InplaceString<CAP> = 'β'.try_into().unwrap();
        assert_eq!(ch, "β");

        let string: String = "world".into();
        let s2: InplaceString<CAP> = string.try_into().unwrap();
        assert_eq!(s2, "world");
    }

    #[test]
    fn test_into_bytes() {
        let s: InplaceString<CAP> = "hello β".try_into().unwrap();
        let v = s.into_bytes();
        assert_eq!(v.as_slice(), "hello β".as_bytes());
    }

    #[test]
    fn test_extend() {
        let mut s: InplaceString<CAP> = InplaceString::new();
        s.extend(['a', 'β', 'γ']);
        assert_eq!(s.as_str(), "aβγ");

        s.extend(["X", "Y"]);
        assert_eq!(s.as_str(), "aβγXY");
    }

    #[test]
    fn test_deref_and_index() {
        let s: InplaceString<CAP> = "hello".try_into().unwrap();
        assert_eq!(&*s, "hello");
        assert_eq!(&s[1..4], "ell");
    }

    #[test]
    fn test_debug_display_hash() {
        let s: InplaceString<CAP> = "hash_test".try_into().unwrap();
        let debug = format!("{:?}", s);
        assert!(debug.contains("hash_test"));
        let display = format!("{}", s);
        assert_eq!(display, "hash_test");

        use std::collections::hash_map::DefaultHasher;
        let mut hasher = DefaultHasher::new();
        s.hash(&mut hasher);
    }

    #[test]
    fn test_partial_eq_and_ord() {
        let s1: InplaceString<CAP> = "abc".try_into().unwrap();
        let s2: InplaceString<CAP> = "abc".try_into().unwrap();
        let s3: InplaceString<CAP> = "xyz".try_into().unwrap();

        assert_eq!(s1, s2);
        assert!(s1 < s3);

        let r: &str = "abc";
        assert_eq!(&r, &s1);
        assert_eq!(s1, r);
    }

    #[test]
    fn test_add_and_add_assign() {
        let s1: InplaceString<CAP> = "foo".try_into().unwrap();
        dbg!(s1);
        let s2 = s1 + "bar";
        assert_eq!(s2.as_str(), "foobar");
        dbg!(s2);
        let mut s3: InplaceString<CAP> = "foo".try_into().unwrap();
        s3 += "bar";
        assert_eq!(s3.as_str(), "foobar");
        dbg!(s3);
    }

    #[test]
    fn test_transmute() {
        let mut s = InplaceString::<CAP>::from_str("hello").unwrap();

        unsafe {
            let vec = s.as_mut_bytes();
            assert_eq!(&[104, 101, 108, 108, 111][..], &vec[..]);

            vec.reverse();
        }
        assert_eq!(s, "olleh");
    }

    #[test]
    fn test_extend_from_within() {
        let mut string = String::from("abcde");

        string.extend_from_within(2..);
        assert_eq!(string, "abcdecde");

        string.extend_from_within(..2);
        assert_eq!(string, "abcdecdeab");

        string.extend_from_within(4..8);
        assert_eq!(string, "abcdecdeabecde");
    }

    #[test]
    #[should_panic]
    fn test_extend_from_within_out_of_bounds() {
        let mut s: InplaceString<CAP> = "abc".try_into().unwrap();
        s.extend_from_within(0..10); // panic: end out of bounds
    }

    #[test]
    #[should_panic]
    fn test_unchecked_push_overflow() {
        let mut s: InplaceString<1> = InplaceString::new();
        s.push('β'); // would exceed capacity
    }
}
