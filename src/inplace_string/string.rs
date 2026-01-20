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
            MAX_ONE_B..MAX_TWO_B => 2,
            MAX_TWO_B..MAX_THREE_B => 3,
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
    iter::FusedIterator,
    marker::PhantomData,
    num::NonZeroUsize,
    ops::{Add, AddAssign, Deref, DerefMut, RangeBounds},
    ptr,
    str::FromStr,
};

use crate::InplaceVector;

/// A fixed-capacity, UTF-8 encoded string stored inline.
///
/// `InplaceString<N>` stores up to `N` bytes of UTF-8 data without heap
/// allocation. This type is `Copy`. Safe operations preserve UTF-8 validity.
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
    current_len: usize,
    capacity: usize,
    required_len: usize,
}

impl std::fmt::Display for InplaceError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "InplaceString capacity exceeded. Capacity: {} Len: {} Required len: {}",
            self.capacity, self.current_len, self.required_len
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
    ///
    /// # Examples
    ///
    /// ```
    /// use inplace_containers::InplaceString;
    ///
    /// let s: InplaceString<8> = InplaceString::new();
    /// assert!(s.is_empty());
    /// assert_eq!(s.capacity(), 8);
    /// ```
    pub const fn new() -> Self {
        InplaceString {
            data: [const { 0 }; N],
            size: unsafe { NonZeroUsize::new_unchecked(1) },
        }
    }

    /// Returns the string as a `&str`.
    ///
    /// This is always safe because all mutations preserve UTF-8 validity.
    ///
    /// # Examples
    ///
    /// ```
    /// use inplace_containers::InplaceString;
    ///
    /// let s: InplaceString<8> = "hi".try_into().unwrap();
    /// assert_eq!(s, "hi");
    /// ```
    pub fn as_str(&self) -> &str {
        unsafe { str::from_utf8_unchecked(self.data.get_unchecked(..self.len())) }
    }

    /// Returns the string as a mutable `&mut str`.
    ///
    /// # Examples
    ///
    /// ```
    /// use inplace_containers::InplaceString;
    ///
    /// let mut s: InplaceString<8> = "hi".try_into().unwrap();
    /// s.as_mut_str().make_ascii_uppercase();
    /// assert_eq!(s, "HI");
    /// ```
    pub fn as_mut_str(&mut self) -> &mut str {
        let len = self.len();
        unsafe { str::from_utf8_unchecked_mut(self.data.get_unchecked_mut(..len)) }
    }

    /// Returns the underlying bytes of the string.
    ///
    /// # Examples
    ///
    /// ```
    /// use inplace_containers::InplaceString;
    ///
    /// let s: InplaceString<8> = "hi".try_into().unwrap();
    /// assert_eq!(s.as_bytes(), &[104, 105]);
    /// ```
    pub fn as_bytes(&self) -> &[u8] {
        &self.data[..self.len()]
    }

    /// Returns the fixed capacity of this string.
    ///
    /// # Examples
    ///
    /// ```
    /// use inplace_containers::InplaceString;
    ///
    /// let s: InplaceString<4> = InplaceString::new();
    /// assert_eq!(s.capacity(), 4);
    /// ```
    pub const fn capacity(&self) -> usize {
        N
    }

    /// Returns remaining unused capacity.
    ///
    /// # Examples
    ///
    /// ```
    /// use inplace_containers::InplaceString;
    ///
    /// let mut s: InplaceString<4> = InplaceString::new();
    /// s.push_str("hi");
    /// assert_eq!(s.remaining_capacity(), 2);
    /// ```
    pub const fn remaining_capacity(&self) -> usize {
        N - self.len()
    }

    /// Returns `true` if the string is at full capacity.
    ///
    /// # Examples
    ///
    /// ```
    /// use inplace_containers::InplaceString;
    ///
    /// let mut s: InplaceString<2> = InplaceString::new();
    /// assert!(!s.is_full());
    /// s.push_str("hi");
    /// assert!(s.is_full());
    /// ```
    pub const fn is_full(&self) -> bool {
        self.remaining_capacity() == 0
    }

    /// Appends a character without checking capacity.
    ///
    /// # Safety
    ///
    /// - `ch.len_utf8()` must be <= `remaining_capacity()`
    /// - Violating this causes out-of-bounds writes and UB.
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use inplace_containers::InplaceString;
    ///
    /// let mut s: InplaceString<2> = InplaceString::new();
    /// unsafe {
    ///     s.unchecked_push('a');
    /// }
    /// assert_eq!(s, "a");
    /// ```
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
    ///
    /// # Examples
    ///
    /// ```
    /// use inplace_containers::InplaceString;
    ///
    /// let mut s: InplaceString<1> = InplaceString::new();
    /// assert!(s.try_push('a').is_ok());
    /// assert!(s.try_push('b').is_err());
    /// ```
    pub fn try_push(&mut self, ch: char) -> Result<(), InplaceError> {
        let ch_len = ch.len_utf8();
        if self.remaining_capacity() < ch_len {
            return Err(InplaceError {
                current_len: self.len(),
                capacity: N,
                required_len: self.len() + ch_len,
            });
        }

        unsafe { self.unchecked_push(ch) };
        Ok(())
    }

    /// Appends a character, panicking if capacity is exceeded.
    ///
    /// # Panics
    ///
    /// Panics if the character would exceed capacity.
    ///
    /// # Examples
    ///
    /// ```
    /// use inplace_containers::InplaceString;
    ///
    /// let mut s: InplaceString<2> = InplaceString::new();
    /// s.push('a');
    /// assert_eq!(s, "a");
    /// ```
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
    /// # Examples
    ///
    /// ```no_run
    /// use inplace_containers::InplaceString;
    ///
    /// let mut s: InplaceString<4> = InplaceString::new();
    /// unsafe {
    ///     s.unchecked_push_str("hi");
    /// }
    /// assert_eq!(s, "hi");
    /// ```
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

    /// Attempts to append the string slice, returning an error if capacity is exceeded.
    ///
    /// # Examples
    ///
    /// ```
    /// use inplace_containers::InplaceString;
    ///
    /// let mut s: InplaceString<3> = InplaceString::new();
    /// assert!(s.try_push_str("hi").is_ok());
    /// assert!(s.try_push_str("too").is_err());
    /// ```
    pub fn try_push_str(&mut self, string: &str) -> Result<(), InplaceError> {
        let string_len = string.len();
        if self.remaining_capacity() < string_len {
            return Err(InplaceError {
                current_len: self.len(),
                capacity: N,
                required_len: self.len() + string_len,
            });
        }
        unsafe {
            self.unchecked_push_str(string);
        }

        Ok(())
    }

    /// Appends the string slice, panicking if capacity is exceeded.
    ///
    /// # Panics
    ///
    /// Panics if the string slice would exceed capacity.
    ///
    /// # Examples
    ///
    /// ```
    /// use inplace_containers::InplaceString;
    ///
    /// let mut s: InplaceString<4> = InplaceString::new();
    /// s.push_str("hi");
    /// assert_eq!(s, "hi");
    /// ```
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
    /// - utf8 validity is still checked
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use inplace_containers::InplaceString;
    ///
    /// let mut s: InplaceString<4> = "ac".try_into().unwrap();
    /// unsafe {
    ///     s.unchecked_insert(1, 'b');
    /// }
    /// assert_eq!(s, "abc");
    /// ```
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

    /// Inserts the slice into the string without checking that capacity is not exceeded.
    /// This is a low-level operation that can be used to optimize multiple insert calls when
    /// the final size is known by the user to not exceed the total capacity.
    ///
    /// # Safety
    ///
    /// - string.len should not be greater than remaining_capacity
    /// - undefined behavior otherwise.
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use inplace_containers::InplaceString;
    ///
    /// let mut s: InplaceString<6> = "ab".try_into().unwrap();
    /// unsafe {
    ///     s.unchecked_insert_str(1, "CD");
    /// }
    /// assert_eq!(s, "aCDb");
    /// ```
    ///
    pub unsafe fn unchecked_insert_str(&mut self, idx: usize, string: &str) {
        assert!(self.is_char_boundary(idx));
        assert!(string.len() <= self.remaining_capacity());

        let len = self.len();
        let amt = string.len();

        self.unchecked_push_str(string);
        self.as_mut_bytes()[idx..len + amt].rotate_right(amt);
    }

    /// Inserts a string slice at `idx`, panicking if capacity is exceeded.
    ///
    /// # Panics
    ///
    /// Panics if `idx` is out of bounds, not on a char boundary, or if capacity is exceeded.
    ///
    /// # Examples
    ///
    /// ```
    /// use inplace_containers::InplaceString;
    ///
    /// let mut s: InplaceString<6> = "ab".try_into().unwrap();
    /// s.insert_str(1, "CD");
    /// assert_eq!(s, "aCDb");
    /// ```
    pub fn insert_str(&mut self, idx: usize, string: &str) {
        let len = self.len();
        if idx > len {
            panic!("insert_str index (is {idx}) should be <= len (is {len})");
        }
        if !self.is_char_boundary(idx) {
            panic!("insert_str index (is {idx}) is not on a char boundary");
        }
        let amt = string.len();

        if amt > self.remaining_capacity() {
            panic!("InplaceString insert_str should not exceed capacity");
        }

        unsafe { self.unchecked_insert_str(idx, string) };
    }

    /// Inserts a character at `idx`, panicking if capacity is exceeded.
    ///
    /// # Panics
    ///
    /// Panics if `idx` is out of bounds, not on a char boundary, or if capacity is exceeded.
    ///
    /// # Examples
    ///
    /// ```
    /// use inplace_containers::InplaceString;
    ///
    /// let mut s: InplaceString<4> = "ac".try_into().unwrap();
    /// s.insert(1, 'b');
    /// assert_eq!(s, "abc");
    /// ```
    pub fn insert(&mut self, idx: usize, ch: char) {
        let len = self.len();
        if idx > len {
            panic!("insert index (is {idx}) should be <= len (is {len})");
        }
        if !self.is_char_boundary(idx) {
            panic!("insert index (is {idx}) is not on a char boundary");
        }

        let ch_len = ch.len_utf8();
        if self.remaining_capacity() < ch_len {
            panic!("InplaceString insert should not exceed capacity");
        }

        unsafe { self.unchecked_insert(idx, ch) };
    }

    /// Appends a slice of this string to itself.
    ///
    /// # Panics
    ///
    /// Panics if the range is out of bounds, not on char boundaries, or exceeds capacity.
    ///
    /// # Examples
    ///
    /// ```
    /// use inplace_containers::InplaceString;
    ///
    /// let mut s: InplaceString<10> = "abcd".try_into().unwrap();
    /// s.extend_from_within(0..2);
    /// assert_eq!(s, "abcdab");
    /// ```
    pub fn extend_from_within<R>(&mut self, src: R)
    where
        R: RangeBounds<usize>,
    {
        let len = self.len();

        let start = match src.start_bound() {
            std::ops::Bound::Included(&i) => i,
            std::ops::Bound::Excluded(&i) => i + 1,
            std::ops::Bound::Unbounded => 0,
        };

        let end = match src.end_bound() {
            std::ops::Bound::Included(&i) => i + 1,
            std::ops::Bound::Excluded(&i) => i,
            std::ops::Bound::Unbounded => len,
        };

        if start > end || end > len {
            panic!("extend_from_within range out of bounds");
        }
        if !self.is_char_boundary(start) || !self.is_char_boundary(end) {
            panic!("extend_from_within range is not on char boundaries");
        }

        let count = end - start;
        let new_len = len.checked_add(count).expect("overflow");

        if new_len > N {
            panic!("extend_from_within would exceed capacity");
        }

        unsafe {
            let ptr = self.data.as_mut_ptr();
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
    /// # Examples
    ///
    /// ```no_run
    /// use inplace_containers::InplaceString;
    ///
    /// let mut s: InplaceString<4> = InplaceString::new();
    /// unsafe {
    ///     s.unchecked_push_str("hi");
    ///     s.set_len(1);
    /// }
    /// assert_eq!(s, "h");
    /// ```
    ///
    pub unsafe fn set_len(&mut self, new_len: usize) {
        debug_assert!(new_len <= N);
        self.size = NonZeroUsize::new_unchecked(new_len.add(1));
    }

    /// Returns the current length in bytes.
    ///
    /// # Examples
    ///
    /// ```
    /// use inplace_containers::InplaceString;
    ///
    /// let mut s: InplaceString<4> = InplaceString::new();
    /// s.push_str("hi");
    /// assert_eq!(s.len(), 2);
    /// ```
    pub const fn len(&self) -> usize {
        unsafe { self.size.get().unchecked_sub(1) }
    }

    /// Returns `true` if the string is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use inplace_containers::InplaceString;
    ///
    /// let mut s: InplaceString<4> = InplaceString::new();
    /// assert!(s.is_empty());
    /// s.push('a');
    /// assert!(!s.is_empty());
    /// ```
    pub const fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Clears the string, removing all characters.
    ///
    /// # Examples
    ///
    /// ```
    /// use inplace_containers::InplaceString;
    ///
    /// let mut s: InplaceString<4> = "hi".try_into().unwrap();
    /// s.clear();
    /// assert!(s.is_empty());
    /// ```
    pub fn clear(&mut self) {
        unsafe { self.set_len(0) };
    }

    /// Removes the last character and returns it, or `None` if empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use inplace_containers::InplaceString;
    ///
    /// let mut s: InplaceString<4> = "hi".try_into().unwrap();
    /// assert_eq!(s.pop(), Some('i'));
    /// assert_eq!(s, "h");
    /// ```
    pub fn pop(&mut self) -> Option<char> {
        let ch = self.chars().next_back()?;
        let newlen = self.len() - ch.len_utf8();
        unsafe {
            self.set_len(newlen);
        }
        Some(ch)
    }

    /// Shortens this string to `new_len`.
    ///
    /// If `new_len` is greater than the current length, this has no effect.
    ///
    /// # Panics
    ///
    /// Panics if `new_len` is not on a char boundary.
    ///
    /// # Examples
    ///
    /// ```
    /// use inplace_containers::InplaceString;
    ///
    /// let mut s: InplaceString<4> = "abcd".try_into().unwrap();
    /// s.truncate(2);
    /// assert_eq!(s, "ab");
    /// ```
    pub fn truncate(&mut self, new_len: usize) {
        if new_len < self.len() {
            if !self.is_char_boundary(new_len) {
                panic!("truncate index (is {new_len}) is not on a char boundary");
            }
            unsafe { self.set_len(new_len) };
        }
    }

    /// Splits the string into two at the given byte index.
    ///
    /// Returns a new string containing `[at, len)`, leaving `self` with `[0, at)`.
    ///
    /// # Panics
    ///
    /// Panics if `at` is out of bounds or not on a char boundary.
    ///
    /// # Examples
    ///
    /// ```
    /// use inplace_containers::InplaceString;
    ///
    /// let mut s: InplaceString<8> = "hello".try_into().unwrap();
    /// let tail = s.split_off(2);
    /// assert_eq!(s, "he");
    /// assert_eq!(tail, "llo");
    /// ```
    pub fn split_off(&mut self, at: usize) -> Self {
        let len = self.len();
        if at > len {
            panic!("split_off index (is {at}) should be <= len (is {len})");
        }
        if !self.is_char_boundary(at) {
            panic!("split_off index (is {at}) is not on a char boundary");
        }

        let (_, split) = self.as_bytes().split_at(at);
        let result = unsafe { Self::from_utf8_unchecked(split).unwrap() };
        unsafe {
            self.set_len(at);
        }

        result
    }

    /// Replaces the specified range with characters from the iterator.
    ///
    /// Returns an iterator over the removed characters.
    ///
    /// # Panics
    ///
    /// Panics if the range is out of bounds, not on char boundaries, or exceeds capacity.
    ///
    /// # Examples
    ///
    /// ```
    /// use inplace_containers::InplaceString;
    ///
    /// let mut s: InplaceString<8> = "abcd".try_into().unwrap();
    /// let removed: String = s.splice(1..3, ['X', 'Y']).collect();
    /// assert_eq!(removed, "bc");
    /// assert_eq!(s, "aXYd");
    /// ```
    pub fn splice<R, I>(&mut self, range: R, replace_with: I) -> StringSplice<N>
    where
        R: RangeBounds<usize>,
        I: IntoIterator<Item = char>,
    {
        use std::ops::Bound::*;

        let len = self.len();
        let start = match range.start_bound() {
            Included(&i) => i,
            Excluded(&i) => i + 1,
            Unbounded => 0,
        };
        let end = match range.end_bound() {
            Included(&i) => i + 1,
            Excluded(&i) => i,
            Unbounded => len,
        };

        if start > end || end > len {
            panic!("splice range out of bounds");
        }
        if !self.is_char_boundary(start) || !self.is_char_boundary(end) {
            panic!("splice range is not on char boundaries");
        }

        let removed_len = end - start;
        let mut replacement = InplaceString::<N>::new();
        for ch in replace_with {
            if replacement.remaining_capacity() < ch.len_utf8() {
                panic!("splice would exceed capacity");
            }
            unsafe { replacement.unchecked_push(ch) };
        }

        let repl_len = replacement.len();
        let new_len = len - removed_len + repl_len;
        if new_len > N {
            panic!("splice would exceed capacity");
        }

        let removed = unsafe {
            let bytes = &self.as_bytes()[start..end];
            Self::from_utf8_unchecked(bytes).unwrap()
        };

        unsafe {
            let base = self.data.as_mut_ptr();
            let tail_len = len - end;
            if repl_len != removed_len {
                ptr::copy(base.add(end), base.add(start + repl_len), tail_len);
            }
            ptr::copy_nonoverlapping(replacement.as_bytes().as_ptr(), base.add(start), repl_len);
            self.set_len(new_len);
        }

        StringSplice {
            inner: removed,
            index: 0,
        }
    }

    /// Converts a byte slice to `InplaceString` if it is valid UTF-8.
    ///
    /// # Errors
    ///
    /// Returns `Err` if the bytes are not valid UTF-8 or exceed capacity.
    ///
    /// # Examples
    ///
    /// ```
    /// use inplace_containers::InplaceString;
    ///
    /// let bytes = b"hi";
    /// let s: InplaceString<4> = InplaceString::from_utf8(bytes).unwrap();
    /// assert_eq!(s, "hi");
    /// ```
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
    /// # Safety
    /// The bytes passed in must be valid UTF-8.
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use inplace_containers::InplaceString;
    ///
    /// let bytes = b"hi";
    /// let s: InplaceString<4> = unsafe { InplaceString::from_utf8_unchecked(bytes).unwrap() };
    /// assert_eq!(s, "hi");
    /// ```
    ///
    pub unsafe fn from_utf8_unchecked(bytes: &[u8]) -> Result<Self, InplaceError> {
        if bytes.len() > N {
            return Err(InplaceError {
                current_len: 0,
                capacity: N,
                required_len: bytes.len(),
            });
        }

        debug_assert!(str::from_utf8(bytes).is_ok());

        let mut result = Self::new();
        unsafe {
            std::ptr::copy_nonoverlapping(bytes.as_ptr(), result.data.as_mut_ptr(), bytes.len());
            result.set_len(bytes.len());
        }
        Ok(result)
    }

    /// Converts a byte slice to a string, replacing invalid sequences with the replacement char.
    ///
    /// # Errors
    ///
    /// Returns `Err(InplaceError)` if the resulting string would exceed capacity.
    ///
    /// # Examples
    ///
    /// ```
    /// use inplace_containers::InplaceString;
    ///
    /// let bytes = b"hi";
    /// let s: InplaceString<4> = InplaceString::from_utf8_lossy(bytes).unwrap();
    /// assert_eq!(s, "hi");
    /// ```
    pub fn from_utf8_lossy(v: &[u8]) -> Result<Self, InplaceError> {
        let mut iter = v.utf8_chunks();

        let first_valid = if let Some(chunk) = iter.next() {
            let valid = chunk.valid();
            if chunk.invalid().is_empty() {
                debug_assert_eq!(valid.len(), v.len());
                return unsafe { Self::from_utf8_unchecked(valid.as_bytes()) };
            }
            valid
        } else {
            return Ok(Self::new());
        };

        const REPLACEMENT: &str = "\u{FFFD}";

        let mut res = Self::new();
        res.try_push_str(first_valid)?;
        res.try_push_str(REPLACEMENT)?;

        for chunk in iter {
            res.try_push_str(chunk.valid())?;
            if !chunk.invalid().is_empty() {
                res.try_push_str(REPLACEMENT)?;
            }
        }

        Ok(res)
    }

    /// Converts the string into its underlying byte vector.
    ///
    /// # Examples
    ///
    /// ```
    /// use inplace_containers::InplaceString;
    ///
    /// let s: InplaceString<4> = "hi".try_into().unwrap();
    /// let v = s.into_bytes();
    /// assert_eq!(v, &b"hi"[..]);
    /// ```
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
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use inplace_containers::InplaceString;
    ///
    /// let mut s: InplaceString<4> = "hi".try_into().unwrap();
    /// unsafe {
    ///     let bytes = s.as_mut_bytes();
    ///     bytes[0] = b'H';
    /// }
    /// assert_eq!(s, "Hi");
    /// ```
    pub unsafe fn as_mut_bytes(&mut self) -> &mut [u8] {
        let len = self.len();
        &mut self.data[..len]
    }

    /// Removes and returns the character at `idx`.
    ///
    /// # Panics
    ///
    /// Panics if `idx` is out of bounds or not on a char boundary.
    ///
    /// # Examples
    ///
    /// ```
    /// use inplace_containers::InplaceString;
    ///
    /// let mut s: InplaceString<4> = "abc".try_into().unwrap();
    /// assert_eq!(s.remove(1), 'b');
    /// assert_eq!(s, "ac");
    /// ```
    pub fn remove(&mut self, idx: usize) -> char {
        let len = self.len();
        if idx >= len {
            panic!("remove index (is {idx}) should be < len (is {len})");
        }
        if !self.is_char_boundary(idx) {
            panic!("remove index (is {idx}) is not on a char boundary");
        }
        let ch = self[idx..].chars().next().expect("valid char boundary");

        let next = idx + ch.len_utf8();
        unsafe {
            let base = self.data.as_mut_ptr();
            std::ptr::copy(base.add(next), base.add(idx), len - next);
            self.set_len(len - (next - idx));
        }

        ch
    }

    /// Creates an iterator that removes characters matching a predicate.
    ///
    /// Characters for which the predicate returns `true` are removed and yielded.
    ///
    /// # Examples
    ///
    /// ```
    /// use inplace_containers::InplaceString;
    ///
    /// let mut s: InplaceString<8> = "abcd".try_into().unwrap();
    /// let removed: String = s.extract_if(|ch| ch == 'b' || ch == 'd').collect();
    /// assert_eq!(removed, "bd");
    /// assert_eq!(s, "ac");
    /// ```
    pub fn extract_if<F>(&mut self, predicate: F) -> StringExtractIf<'_, N, F>
    where
        F: FnMut(char) -> bool,
    {
        let len = self.len();
        StringExtractIf {
            string: self as *mut InplaceString<N>,
            pred: predicate,
            read: 0,
            write: 0,
            len,
            finished: false,
            _marker: PhantomData,
        }
    }

    /// Retains only the characters specified by the predicate.
    ///
    /// # Examples
    ///
    /// ```
    /// use inplace_containers::InplaceString;
    ///
    /// let mut s: InplaceString<8> = "abcd".try_into().unwrap();
    /// s.retain(|ch| ch != 'b');
    /// assert_eq!(s, "acd");
    /// ```
    pub fn retain<F>(&mut self, mut f: F)
    where
        F: FnMut(char) -> bool,
    {
        let filtered = self.chars().filter(|ch| f(*ch));
        let mut tmp = Self::new();
        for ch in filtered {
            unsafe { tmp.unchecked_push(ch) };
        }
        *self = tmp;
    }
}

/// Iterator returned by `InplaceString::splice`.
pub struct StringSplice<const N: usize> {
    inner: InplaceString<N>,
    index: usize,
}

/// Iterator returned by `InplaceString::extract_if`.
pub struct StringExtractIf<'a, const N: usize, F>
where
    F: FnMut(char) -> bool,
{
    string: *mut InplaceString<N>,
    pred: F,
    read: usize,
    write: usize,
    len: usize,
    finished: bool,
    _marker: core::marker::PhantomData<&'a mut InplaceString<N>>,
}

impl<const N: usize> Iterator for StringSplice<N> {
    type Item = char;

    fn next(&mut self) -> Option<Self::Item> {
        if self.index >= self.inner.len() {
            return None;
        }
        let s = &self.inner.as_str()[self.index..];
        let ch = s.chars().next()?;
        self.index += ch.len_utf8();
        Some(ch)
    }
}

impl<const N: usize> FusedIterator for StringSplice<N> {}

impl<'a, const N: usize, F> StringExtractIf<'a, N, F>
where
    F: FnMut(char) -> bool,
{
    fn finish(&mut self) {
        if self.finished {
            return;
        }
        unsafe {
            let string = &mut *self.string;
            string.set_len(self.write);
        }
        self.finished = true;
    }
}

impl<'a, const N: usize, F> Iterator for StringExtractIf<'a, N, F>
where
    F: FnMut(char) -> bool,
{
    type Item = char;

    fn next(&mut self) -> Option<Self::Item> {
        unsafe {
            let base = (*self.string).as_mut_ptr();
            while self.read < self.len {
                let read = self.read;
                let remaining = self.len - read;
                let bytes = std::slice::from_raw_parts(base.add(read), remaining);
                let s = std::str::from_utf8_unchecked(bytes);
                let ch = s.chars().next().expect("valid UTF-8");
                let ch_len = ch.len_utf8();
                self.read += ch_len;

                if (self.pred)(ch) {
                    return Some(ch);
                }

                if self.write != read {
                    ptr::copy(base.add(read), base.add(self.write), ch_len);
                }
                self.write += ch_len;
            }
            self.finish();
            None
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (0, None)
    }
}

impl<'a, const N: usize, F> FusedIterator for StringExtractIf<'a, N, F> where F: FnMut(char) -> bool {}

impl<'a, const N: usize, F> Drop for StringExtractIf<'a, N, F>
where
    F: FnMut(char) -> bool,
{
    fn drop(&mut self) {
        if self.finished {
            return;
        }
        unsafe {
            let base = (*self.string).as_mut_ptr();
            while self.read < self.len {
                let read = self.read;
                let remaining = self.len - read;
                let bytes = std::slice::from_raw_parts(base.add(read), remaining);
                let s = std::str::from_utf8_unchecked(bytes);
                let ch = s.chars().next().expect("valid UTF-8");
                let ch_len = ch.len_utf8();
                self.read += ch_len;

                if (self.pred)(ch) {
                    continue;
                }

                if self.write != read {
                    ptr::copy(base.add(read), base.add(self.write), ch_len);
                }
                self.write += ch_len;
            }
        }
        self.finish();
    }
}

impl<const N: usize> Deref for InplaceString<N> {
    type Target = str;

    /// Dereferences to a `str`.
    ///
    /// # Examples
    ///
    /// ```
    /// use inplace_containers::InplaceString;
    ///
    /// let s: InplaceString<8> = "hi".try_into().unwrap();
    /// assert_eq!(&*s, "hi");
    /// ```
    fn deref(&self) -> &Self::Target {
        self.as_str()
    }
}

impl<const N: usize> DerefMut for InplaceString<N> {
    /// Mutably dereferences to a `str`.
    ///
    /// # Examples
    ///
    /// ```
    /// use inplace_containers::InplaceString;
    ///
    /// let mut s: InplaceString<8> = "hi".try_into().unwrap();
    /// s.make_ascii_uppercase();
    /// assert_eq!(s, "HI");
    /// ```
    fn deref_mut(&mut self) -> &mut str {
        self.as_mut_str()
    }
}

impl<const N: usize> TryFrom<&str> for InplaceString<N> {
    type Error = InplaceError;

    /// Attempts to create an `InplaceString` from a `&str`.
    ///
    /// # Errors
    ///
    /// Returns `Err(InplaceError)` if the string exceeds capacity.
    ///
    /// # Examples
    ///
    /// ```
    /// use inplace_containers::InplaceString;
    ///
    /// let s: InplaceString<4> = InplaceString::try_from("hi").unwrap();
    /// assert_eq!(s, "hi");
    /// ```
    fn try_from(value: &str) -> Result<Self, Self::Error> {
        let str_len = value.len();
        if N < str_len {
            return Err(InplaceError {
                current_len: 0,
                capacity: N,
                required_len: str_len,
            });
        }

        let mut result = Self::new();
        unsafe { result.unchecked_push_str(value) };
        Ok(result)
    }
}

impl<const N: usize> TryFrom<&mut str> for InplaceString<N> {
    type Error = InplaceError;

    /// Attempts to create an `InplaceString` from a mutable `str`.
    ///
    /// # Errors
    ///
    /// Returns `Err(InplaceError)` if the string exceeds capacity.
    ///
    /// # Examples
    ///
    /// ```
    /// use inplace_containers::InplaceString;
    ///
    /// let mut s = String::from("hi");
    /// let inplace: InplaceString<4> = InplaceString::try_from(s.as_mut_str()).unwrap();
    /// assert_eq!(inplace, "hi");
    /// ```
    fn try_from(value: &mut str) -> Result<Self, Self::Error> {
        (value as &str).try_into()
    }
}

impl<const N: usize> TryFrom<String> for InplaceString<N> {
    type Error = InplaceError;

    /// Attempts to create an `InplaceString` from a `String`.
    ///
    /// # Errors
    ///
    /// Returns `Err(InplaceError)` if the string exceeds capacity.
    ///
    /// # Examples
    ///
    /// ```
    /// use inplace_containers::InplaceString;
    ///
    /// let s = String::from("hi");
    /// let inplace: InplaceString<4> = InplaceString::try_from(s).unwrap();
    /// assert_eq!(inplace, "hi");
    /// ```
    fn try_from(value: String) -> Result<Self, Self::Error> {
        value.as_str().try_into()
    }
}

impl<const N: usize> TryFrom<char> for InplaceString<N> {
    type Error = InplaceError;

    /// Attempts to create an `InplaceString` from a single character.
    ///
    /// # Errors
    ///
    /// Returns `Err(InplaceError)` if the character exceeds capacity.
    ///
    /// # Examples
    ///
    /// ```
    /// use inplace_containers::InplaceString;
    ///
    /// let s: InplaceString<2> = InplaceString::try_from('a').unwrap();
    /// assert_eq!(s, "a");
    /// ```
    fn try_from(value: char) -> Result<Self, Self::Error> {
        let ch_len = value.len_utf8();
        if N < ch_len {
            return Err(InplaceError {
                current_len: 0,
                capacity: N,
                required_len: ch_len,
            });
        }

        let mut result = Self::new();
        unsafe { result.unchecked_push(value) };
        Ok(result)
    }
}

impl<const N: usize> TryFrom<InplaceVector<u8, N>> for InplaceString<N> {
    type Error = std::str::Utf8Error;

    /// Attempts to create an `InplaceString` from an `InplaceVector` of bytes.
    ///
    /// # Errors
    ///
    /// Returns `Err(Utf8Error)` if the bytes are not valid UTF-8.
    ///
    /// # Examples
    ///
    /// ```
    /// use inplace_containers::{InplaceString, InplaceVector};
    ///
    /// let mut v: InplaceVector<u8, 4> = InplaceVector::new();
    /// v.push(b'h');
    /// v.push(b'i');
    /// let s: InplaceString<4> = InplaceString::try_from(v).unwrap();
    /// assert_eq!(s, "hi");
    /// ```
    fn try_from(value: InplaceVector<u8, N>) -> Result<Self, Self::Error> {
        let str = std::str::from_utf8(&value)?;

        let mut result = InplaceString::new();

        unsafe {
            std::ptr::copy_nonoverlapping(str.as_ptr(), result.data.as_mut_ptr(), str.len());
            result.set_len(str.len());
        };

        Ok(result)
    }
}

impl<const N: usize> TryFrom<&std::ffi::CStr> for InplaceString<N> {
    type Error = InplaceUtf8Error;

    /// Attempts to create an `InplaceString` from a C string.
    ///
    /// # Errors
    ///
    /// Returns `Err` if the bytes are invalid UTF-8 or exceed capacity.
    ///
    /// # Examples
    ///
    /// ```
    /// use inplace_containers::InplaceString;
    /// use std::ffi::CStr;
    ///
    /// let cstr = CStr::from_bytes_with_nul(b"hi\0").unwrap();
    /// let s: InplaceString<4> = InplaceString::try_from(cstr).unwrap();
    /// assert_eq!(s, "hi");
    /// ```
    fn try_from(value: &std::ffi::CStr) -> Result<Self, Self::Error> {
        value.to_bytes().try_into()
    }
}

impl<const N: usize> TryFrom<std::ffi::CString> for InplaceString<N> {
    type Error = InplaceUtf8Error;

    /// Attempts to create an `InplaceString` from a `CString`.
    ///
    /// # Errors
    ///
    /// Returns `Err` if the bytes are invalid UTF-8 or exceed capacity.
    ///
    /// # Examples
    ///
    /// ```
    /// use inplace_containers::InplaceString;
    /// use std::ffi::CString;
    ///
    /// let cstr = CString::new("hi").unwrap();
    /// let s: InplaceString<4> = InplaceString::try_from(cstr).unwrap();
    /// assert_eq!(s, "hi");
    /// ```
    fn try_from(value: std::ffi::CString) -> Result<Self, Self::Error> {
        value.as_c_str().try_into()
    }
}

impl<'a, const N: usize> FromIterator<&'a char> for InplaceString<N> {
    /// Creates an `InplaceString` from an iterator of `&char`.
    ///
    /// # Panics
    ///
    /// Panics if the iterator yields more bytes than capacity.
    ///
    /// # Examples
    ///
    /// ```
    /// use inplace_containers::InplaceString;
    ///
    /// let chars = ['a', 'b'];
    /// let s: InplaceString<4> = chars.iter().collect();
    /// assert_eq!(s, "ab");
    /// ```
    fn from_iter<T: IntoIterator<Item = &'a char>>(iter: T) -> Self {
        let mut result = Self::new();
        for ch in iter {
            result.try_push(*ch).expect("capacity exceeded");
        }
        result
    }
}

impl<const N: usize> FromIterator<char> for InplaceString<N> {
    /// Creates an `InplaceString` from an iterator of `char`.
    ///
    /// # Panics
    ///
    /// Panics if the iterator yields more bytes than capacity.
    ///
    /// # Examples
    ///
    /// ```
    /// use inplace_containers::InplaceString;
    ///
    /// let s: InplaceString<4> = ['a', 'b'].into_iter().collect();
    /// assert_eq!(s, "ab");
    /// ```
    fn from_iter<T: IntoIterator<Item = char>>(iter: T) -> Self {
        let mut result = Self::new();
        for ch in iter {
            result.try_push(ch).expect("capacity exceeded");
        }
        result
    }
}

impl<'a, const N: usize> FromIterator<&'a str> for InplaceString<N> {
    /// Creates an `InplaceString` from an iterator of `&str`.
    ///
    /// # Panics
    ///
    /// Panics if the iterator yields more bytes than capacity.
    ///
    /// # Examples
    ///
    /// ```
    /// use inplace_containers::InplaceString;
    ///
    /// let parts = ["he", "llo"];
    /// let s: InplaceString<8> = parts.into_iter().collect();
    /// assert_eq!(s, "hello");
    /// ```
    fn from_iter<T: IntoIterator<Item = &'a str>>(iter: T) -> Self {
        let mut result = Self::new();
        for s in iter {
            result.try_push_str(s).expect("capacity exceeded");
        }
        result
    }
}

impl<const N: usize> FromStr for InplaceString<N> {
    type Err = InplaceError;

    /// Parses a string slice into an `InplaceString`.
    ///
    /// # Errors
    ///
    /// Returns `Err(InplaceError)` if the string exceeds capacity.
    ///
    /// # Examples
    ///
    /// ```
    /// use inplace_containers::InplaceString;
    /// use std::str::FromStr;
    ///
    /// let s = InplaceString::<4>::from_str("hi").unwrap();
    /// assert_eq!(s, "hi");
    /// ```
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Self::try_from(s)
    }
}

impl<const N: usize> From<InplaceString<N>> for String {
    /// Converts an `InplaceString` into a `String`.
    ///
    /// # Examples
    ///
    /// ```
    /// use inplace_containers::InplaceString;
    ///
    /// let s: InplaceString<4> = "hi".try_into().unwrap();
    /// let std = String::from(s);
    /// assert_eq!(std, "hi");
    /// ```
    fn from(value: InplaceString<N>) -> Self {
        Self::from(value.as_str())
    }
}

impl<const N: usize> Hash for InplaceString<N> {
    /// Hashes the string contents.
    ///
    /// # Examples
    ///
    /// ```
    /// use inplace_containers::InplaceString;
    /// use std::collections::hash_map::DefaultHasher;
    /// use std::hash::{Hash, Hasher};
    ///
    /// let s: InplaceString<4> = "hi".try_into().unwrap();
    /// let mut hasher = DefaultHasher::new();
    /// s.hash(&mut hasher);
    /// ```
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.as_str().hash(state);
    }
}

impl<const N: usize> PartialOrd for InplaceString<N> {
    /// Compares two strings lexicographically.
    ///
    /// # Examples
    ///
    /// ```
    /// use inplace_containers::InplaceString;
    ///
    /// let a: InplaceString<4> = "a".try_into().unwrap();
    /// let b: InplaceString<4> = "b".try_into().unwrap();
    /// assert!(a < b);
    /// ```
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl<const N: usize> Ord for InplaceString<N> {
    /// Compares two strings lexicographically.
    ///
    /// # Examples
    ///
    /// ```
    /// use inplace_containers::InplaceString;
    ///
    /// let a: InplaceString<4> = "a".try_into().unwrap();
    /// let b: InplaceString<4> = "b".try_into().unwrap();
    /// assert!(a.cmp(&b).is_lt());
    /// ```
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.as_str().cmp(other)
    }
}

impl<const N: usize> Write for InplaceString<N> {
    /// Writes a string slice into this `InplaceString`.
    ///
    /// # Errors
    ///
    /// Returns `fmt::Error` if the string would exceed capacity.
    ///
    /// # Examples
    ///
    /// ```
    /// use inplace_containers::InplaceString;
    /// use core::fmt::Write;
    ///
    /// let mut s: InplaceString<8> = InplaceString::new();
    /// write!(&mut s, "hi").unwrap();
    /// assert_eq!(s, "hi");
    /// ```
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

    /// Indexes into the string.
    ///
    /// # Panics
    ///
    /// Panics if the index is out of bounds or not on a char boundary.
    ///
    /// # Examples
    ///
    /// ```
    /// use inplace_containers::InplaceString;
    ///
    /// let s: InplaceString<8> = "hello".try_into().unwrap();
    /// assert_eq!(&s[1..3], "el");
    /// ```
    fn index(&self, index: I) -> &Self::Output {
        self.as_str().index(index)
    }
}

impl<const N: usize, I> std::ops::IndexMut<I> for InplaceString<N>
where
    I: std::slice::SliceIndex<str>,
{
    /// Mutably indexes into the string.
    ///
    /// # Panics
    ///
    /// Panics if the index is out of bounds or not on a char boundary.
    ///
    /// # Examples
    ///
    /// ```
    /// use inplace_containers::InplaceString;
    ///
    /// let mut s: InplaceString<8> = "hello".try_into().unwrap();
    /// s[0..1].make_ascii_uppercase();
    /// assert_eq!(s, "Hello");
    /// ```
    fn index_mut(&mut self, index: I) -> &mut Self::Output {
        self.as_mut_str().index_mut(index)
    }
}

impl<const N: usize> TryFrom<&[u8]> for InplaceString<N> {
    type Error = InplaceUtf8Error;

    /// Attempts to create an `InplaceString` from a byte slice.
    ///
    /// # Errors
    ///
    /// Returns `Err` if the bytes are invalid UTF-8 or exceed capacity.
    ///
    /// # Examples
    ///
    /// ```
    /// use inplace_containers::InplaceString;
    ///
    /// let s: InplaceString<4> = InplaceString::try_from(&b"hi"[..]).unwrap();
    /// assert_eq!(s, "hi");
    /// ```
    fn try_from(value: &[u8]) -> Result<Self, Self::Error> {
        Self::from_utf8(value)
    }
}

impl<const N: usize> AsRef<[u8]> for InplaceString<N> {
    /// Returns a byte slice of this string.
    ///
    /// # Examples
    ///
    /// ```
    /// use inplace_containers::InplaceString;
    ///
    /// let s: InplaceString<4> = "hi".try_into().unwrap();
    /// let bytes: &[u8] = s.as_ref();
    /// assert_eq!(bytes, b"hi");
    /// ```
    fn as_ref(&self) -> &[u8] {
        self.as_bytes()
    }
}

impl<const N: usize> AsRef<str> for InplaceString<N> {
    /// Returns a `&str` view of this string.
    ///
    /// # Examples
    ///
    /// ```
    /// use inplace_containers::InplaceString;
    ///
    /// let s: InplaceString<4> = "hi".try_into().unwrap();
    /// let view: &str = s.as_ref();
    /// assert_eq!(view, "hi");
    /// ```
    fn as_ref(&self) -> &str {
        self.as_str()
    }
}

impl<const N: usize> std::borrow::Borrow<str> for InplaceString<N> {
    /// Borrows the string as a `str`.
    ///
    /// # Examples
    ///
    /// ```
    /// use inplace_containers::InplaceString;
    /// use std::borrow::Borrow;
    ///
    /// let s: InplaceString<4> = "hi".try_into().unwrap();
    /// let view: &str = s.borrow();
    /// assert_eq!(view, "hi");
    /// ```
    fn borrow(&self) -> &str {
        self
    }
}

impl<const N: usize> std::borrow::BorrowMut<str> for InplaceString<N> {
    /// Mutably borrows the string as a `str`.
    ///
    /// # Examples
    ///
    /// ```
    /// use inplace_containers::InplaceString;
    /// use std::borrow::BorrowMut;
    ///
    /// let mut s: InplaceString<4> = "hi".try_into().unwrap();
    /// let view: &mut str = s.borrow_mut();
    /// view.make_ascii_uppercase();
    /// assert_eq!(s, "HI");
    /// ```
    fn borrow_mut(&mut self) -> &mut str {
        self.as_mut_str()
    }
}

impl<const N: usize> Default for InplaceString<N> {
    /// Creates an empty string.
    ///
    /// # Examples
    ///
    /// ```
    /// use inplace_containers::InplaceString;
    ///
    /// let s: InplaceString<4> = InplaceString::default();
    /// assert!(s.is_empty());
    /// ```
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

    /// Appends a `&str` to this string, returning the result.
    ///
    /// # Panics
    ///
    /// Panics if the result would exceed capacity.
    ///
    /// # Examples
    ///
    /// ```
    /// use inplace_containers::InplaceString;
    ///
    /// let s: InplaceString<6> = "hi".try_into().unwrap();
    /// let s = s + "yo";
    /// assert_eq!(s, "hiyo");
    /// ```
    fn add(mut self, rhs: &str) -> Self::Output {
        self.push_str(rhs);
        self
    }
}

impl<const N: usize> AddAssign<&str> for InplaceString<N> {
    /// Appends a `&str` to this string in place.
    ///
    /// # Panics
    ///
    /// Panics if the result would exceed capacity.
    ///
    /// # Examples
    ///
    /// ```
    /// use inplace_containers::InplaceString;
    ///
    /// let mut s: InplaceString<6> = "hi".try_into().unwrap();
    /// s += "yo";
    /// assert_eq!(s, "hiyo");
    /// ```
    fn add_assign(&mut self, rhs: &str) {
        self.push_str(rhs);
    }
}

impl<const N: usize> AsMut<str> for InplaceString<N> {
    /// Returns a mutable `str` view of this string.
    ///
    /// # Examples
    ///
    /// ```
    /// use inplace_containers::InplaceString;
    ///
    /// let mut s: InplaceString<4> = "hi".try_into().unwrap();
    /// let view: &mut str = s.as_mut();
    /// view.make_ascii_uppercase();
    /// assert_eq!(s, "HI");
    /// ```
    fn as_mut(&mut self) -> &mut str {
        self.as_mut_str()
    }
}

impl<const N: usize> Debug for InplaceString<N> {
    /// Formats the string using the debug formatter.
    ///
    /// # Examples
    ///
    /// ```
    /// use inplace_containers::InplaceString;
    ///
    /// let s: InplaceString<4> = "hi".try_into().unwrap();
    /// let out = format!("{:?}", s);
    /// assert!(out.contains("hi"));
    /// ```
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct(concat!("InplaceString<", stringify!(N), ">"))
            .field("string", &self.as_str())
            .field("size", &self.len())
            .finish()
    }
}

impl<const N: usize> std::fmt::Display for InplaceString<N> {
    /// Formats the string using the display formatter.
    ///
    /// # Examples
    ///
    /// ```
    /// use inplace_containers::InplaceString;
    ///
    /// let s: InplaceString<4> = "hi".try_into().unwrap();
    /// assert_eq!(format!("{}", s), "hi");
    /// ```
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        fmt::Display::fmt(&**self, f)
    }
}

impl<const N: usize> PartialEq for InplaceString<N> {
    /// Checks equality with another `InplaceString`.
    ///
    /// # Examples
    ///
    /// ```
    /// use inplace_containers::InplaceString;
    ///
    /// let a: InplaceString<4> = "hi".try_into().unwrap();
    /// let b: InplaceString<4> = "hi".try_into().unwrap();
    /// assert_eq!(a, b);
    /// ```
    fn eq(&self, other: &Self) -> bool {
        self.as_str() == other.as_str()
    }
}

impl<const N: usize> PartialEq<InplaceString<N>> for &str {
    /// Checks equality between a `&str` and an `InplaceString`.
    ///
    /// # Examples
    ///
    /// ```
    /// use inplace_containers::InplaceString;
    ///
    /// let s: InplaceString<4> = "hi".try_into().unwrap();
    /// assert_eq!("hi", s);
    /// ```
    fn eq(&self, other: &InplaceString<N>) -> bool {
        *self == other.as_str()
    }
}

impl<const N: usize> PartialEq<&str> for InplaceString<N> {
    /// Checks equality between an `InplaceString` and a `&str`.
    ///
    /// # Examples
    ///
    /// ```
    /// use inplace_containers::InplaceString;
    ///
    /// let s: InplaceString<4> = "hi".try_into().unwrap();
    /// assert_eq!(s, "hi");
    /// ```
    fn eq(&self, other: &&str) -> bool {
        self.as_str() == *other
    }
}

impl<const N: usize> Extend<char> for InplaceString<N> {
    /// Extends the string with characters from an iterator.
    ///
    /// # Panics
    ///
    /// Panics if the result would exceed capacity.
    ///
    /// # Examples
    ///
    /// ```
    /// use inplace_containers::InplaceString;
    ///
    /// let mut s: InplaceString<4> = InplaceString::new();
    /// s.extend(['a', 'b']);
    /// assert_eq!(s, "ab");
    /// ```
    fn extend<T: IntoIterator<Item = char>>(&mut self, iter: T) {
        for ch in iter {
            self.push(ch);
        }
    }
}

impl<'a, const N: usize> Extend<&'a str> for InplaceString<N> {
    /// Extends the string with string slices from an iterator.
    ///
    /// # Panics
    ///
    /// Panics if the result would exceed capacity.
    ///
    /// # Examples
    ///
    /// ```
    /// use inplace_containers::InplaceString;
    ///
    /// let mut s: InplaceString<8> = InplaceString::new();
    /// s.extend(["he", "llo"]);
    /// assert_eq!(s, "hello");
    /// ```
    fn extend<T: IntoIterator<Item = &'a str>>(&mut self, iter: T) {
        for string in iter {
            self.push_str(string);
        }
    }
}

impl<const N: usize> Extend<String> for InplaceString<N> {
    /// Extends the string with owned strings from an iterator.
    ///
    /// # Panics
    ///
    /// Panics if the result would exceed capacity.
    ///
    /// # Examples
    ///
    /// ```
    /// use inplace_containers::InplaceString;
    ///
    /// let mut s: InplaceString<8> = InplaceString::new();
    /// s.extend([String::from("he"), String::from("llo")]);
    /// assert_eq!(s, "hello");
    /// ```
    fn extend<T: IntoIterator<Item = String>>(&mut self, iter: T) {
        for string in iter {
            self.push_str(string.as_str());
        }
    }
}

impl<const N: usize> Eq for InplaceString<N> {}

/// A helper trait for formatting values into a bounded `InplaceString`.
///
/// Implemented only for basic types guaranteed that their string formatted size will not exceed 20 bytes.
#[allow(dead_code)]
pub trait BoundedDisplay: core::fmt::Display {
    /// Formats `self` into an `InplaceString<20>`. Should never panic.
    ///
    /// # Examples
    ///
    /// ```
    /// use inplace_containers::BoundedDisplay;
    ///
    /// let s = 42u32.to_inplace_string();
    /// assert_eq!(s, "42");
    /// ```
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
        assert_eq!(s, "255");
        assert!(value.to_string().len() <= 20);
    }

    #[test]
    fn test_i8_bounded_display() {
        let value: i8 = -128;
        let s = value.to_inplace_string();
        assert_eq!(s, "-128");
        assert!(value.to_string().len() <= 20);
    }

    #[test]
    fn test_u32_bounded_display() {
        let value: u32 = 4_294_967_295;
        let s = value.to_inplace_string();
        assert_eq!(s, "4294967295");
        assert!(value.to_string().len() <= 20);
    }

    #[test]
    fn test_i32_bounded_display() {
        let value: i32 = -2_147_483_648;
        let s = value.to_inplace_string();
        assert_eq!(s, "-2147483648");
        assert!(value.to_string().len() <= 20);
    }

    #[test]
    fn test_u64_bounded_display() {
        let value: u64 = 18_446_744_073_709_551_615;
        let s = value.to_inplace_string();
        assert_eq!(s, "18446744073709551615");
        assert!(value.to_string().len() <= 20);
    }

    #[test]
    fn test_i64_bounded_display() {
        let value: i64 = -9_223_372_036_854_775_808;
        let s = value.to_inplace_string();
        assert_eq!(s, "-9223372036854775808");
        assert!(value.to_string().len() <= 20);
    }

    #[test]
    fn test_usize_bounded_display() {
        let value: usize = 123456789;
        let s = value.to_inplace_string();
        assert_eq!(s, "123456789");
        assert!(value.to_string().len() <= 20);
    }

    #[test]
    fn test_bool_bounded_display() {
        let t = true.to_inplace_string();
        let f = false.to_inplace_string();
        assert_eq!(t, "true");
        assert_eq!(f, "false");
        assert!(t.to_string().len() <= 20);
        assert!(f.to_string().len() <= 20);
    }

    #[test]
    fn test_char_bounded_display() {
        let ch = 'β';
        let s = ch.to_inplace_string();
        assert_eq!(s, "β");
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
        assert_eq!(s, "a");

        s.try_push('β').unwrap();
        assert_eq!(s, "aβ");

        let mut s: InplaceString<1> = InplaceString::new();
        let err = s.try_push('β').unwrap_err();
        assert_eq!(err.current_len, 0);
        assert_eq!(err.required_len, 2);
    }

    #[test]
    fn test_push_str_and_try_push_str() {
        let mut s: InplaceString<CAP> = InplaceString::new();
        s.push_str("hello");
        assert_eq!(s, "hello");

        s.try_push_str(" world").unwrap();
        assert_eq!(s, "hello world");

        let mut s: InplaceString<5> = InplaceString::new();
        let err = s.try_push_str("toolong").unwrap_err();
        assert_eq!(err.required_len, 7);
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
    fn test_splice_and_extract_if() {
        let mut s: InplaceString<CAP> = "abcd".try_into().unwrap();
        let removed: String = s.splice(1..3, ['X', 'Y']).collect();
        assert_eq!(removed, "bc");
        assert_eq!(s, "aXYd");

        let removed2: String = s.extract_if(|ch| ch == 'X').collect();
        assert_eq!(removed2, "X");
        assert_eq!(s, "aYd");
    }
    #[test]
    fn test_truncate_and_split_off() {
        let mut s: InplaceString<CAP> = "abcd".try_into().unwrap();
        s.truncate(2);
        assert_eq!(s, "ab");
        let tail = s.split_off(1);
        assert_eq!(s, "a");
        assert_eq!(tail, "b");
    }

    #[test]
    #[should_panic]
    fn test_truncate_non_boundary_panics() {
        let mut s: InplaceString<CAP> = "aIı".try_into().unwrap();
        s.truncate(3);
    }
    #[test]
    #[should_panic]
    fn test_splice_capacity_error() {
        let mut s: InplaceString<4> = "ab".try_into().unwrap();
        s.splice(0..0, ['x', 'y', 'z']);
    }

    #[test]
    fn test_unchecked_push_and_insert() {
        let mut s: InplaceString<CAP> = InplaceString::new();
        unsafe {
            s.unchecked_push('β');
            s.unchecked_push('γ');
            s.unchecked_insert(2, 'δ');
        }
        assert_eq!(s, "βδγ");
    }

    #[test]
    fn test_pop_and_remove() {
        let mut s: InplaceString<CAP> = InplaceString::new();
        s.push_str("aβγ");
        let ch = s.pop().unwrap();
        assert_eq!(ch, 'γ');
        assert_eq!(s, "aβ");

        let removed = s.remove(1);
        assert_eq!(removed, 'β');
        assert_eq!(s, "a");
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
        assert_eq!(s, "hello β");

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
        let s = unsafe { InplaceString::<CAP>::from_utf8_unchecked(bytes).unwrap() };
        assert_eq!(s, "αβγ");
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
        assert_eq!(v, "hello β".as_bytes());
    }

    #[test]
    fn test_extend() {
        let mut s: InplaceString<CAP> = InplaceString::new();
        s.extend(['a', 'β', 'γ']);
        assert_eq!(s, "aβγ");

        s.extend(["X", "Y"]);
        assert_eq!(s, "aβγXY");
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
        assert_eq!(s1, "abc");
        assert_eq!("abc", s1);
    }

    #[test]
    fn test_add_and_add_assign() {
        let s1: InplaceString<CAP> = "foo".try_into().unwrap();
        dbg!(s1);
        let s2 = s1 + "bar";
        assert_eq!(s2, "foobar");
        dbg!(s2);
        let mut s3: InplaceString<CAP> = "foo".try_into().unwrap();
        s3 += "bar";
        assert_eq!(s3, "foobar");
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
        let mut string: InplaceString<CAP> = "abcde".try_into().unwrap();

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
