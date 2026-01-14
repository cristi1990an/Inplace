mod details {

    const TAG_CONT: u8 = 0b1000_0000;
    const TAG_TWO_B: u8 = 0b1100_0000;
    const TAG_THREE_B: u8 = 0b1110_0000;
    const TAG_FOUR_B: u8 = 0b1111_0000;
    const MAX_ONE_B: u32 = 0x80;
    const MAX_TWO_B: u32 = 0x800;
    const MAX_THREE_B: u32 = 0x10000;

    const fn len_utf8(code: u32) -> usize {
        match code {
            ..MAX_ONE_B => 1,
            ..MAX_TWO_B => 2,
            ..MAX_THREE_B => 3,
            _ => 4,
        }
    }

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
use std::{
    fmt::Debug,
    hash::Hash,
    ops::{Deref, DerefMut},
    ptr,
    str::FromStr,
};

#[derive(Clone, Copy)]
pub struct InplaceString<const N: usize> {
    data: [u8; N],
    size: usize,
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
    pub const fn new() -> Self {
        InplaceString {
            data: [const { 0 }; N],
            size: 0,
        }
    }

    pub fn as_str(&self) -> &str {
        unsafe { str::from_utf8_unchecked(self.data.get_unchecked(..self.size)) }
    }

    pub fn as_mut_str(&mut self) -> &mut str {
        unsafe { str::from_utf8_unchecked_mut(self.data.get_unchecked_mut(..self.size)) }
    }

    pub const fn as_bytes(&self) -> &[u8] {
        &self.data
    }

    pub const fn capacity(&self) -> usize {
        N
    }

    pub const fn remaining_capacity(&self) -> usize {
        N - self.size
    }

    pub const fn is_full(&self) -> bool {
        self.remaining_capacity() == 0
    }

    /// Pushes a new char into the string without checking that capacity is not exceeded.
    /// This is a low-level operation that can be used to optimize multiple push calls when 
    /// the final size is known by the user to not exceed the total capacity.
    ///
    /// # Safety
    ///
    /// - ch.len_utf8() should not be greater than remaining_capacity()
    /// - undefined behavior otherwise.
    ///
    pub unsafe fn unchecked_push(&mut self, ch: char) {
        let len = self.len();
        let ch_len = ch.len_utf8();
        unsafe {
            details::encode_utf8_raw_unchecked(ch as u32, self.as_mut_ptr().add(self.len()));
            self.set_len(len + ch_len);
        }
    }

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
        unsafe {
            ptr::copy(
                string.as_ptr(),
                self.as_mut_ptr().add(self.size),
                string_len,
            );
            self.set_len(self.size + string_len);
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

        let len = self.len();
        let ch_len = ch.len_utf8();

        unsafe {
            ptr::copy(
                self.as_ptr().add(idx),
                self.as_mut_ptr().add(idx + ch_len),
                len - idx,
            );
            details::encode_utf8_raw_unchecked(ch as u32, self.as_mut_ptr().add(idx));
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

        let len = self.len();
        let amt = string.len();

        unsafe {
            ptr::copy(
                self.as_ptr().add(idx),
                self.as_mut_ptr().add(idx + amt),
                len - idx,
            );
            ptr::copy_nonoverlapping(string.as_ptr(), self.as_mut_ptr().add(idx), amt);
            self.set_len(len + amt);
        }
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

    /// Forces the length of the string to new_len.
    /// This is a low-level operation that maintains none of the normal invariants of the type.
    ///
    /// # Safety
    ///
    /// - new_len must be less than or equal to capacity().
    /// - the elements at old_len..new_len must represent a valid UTF8 sequence.
    ///
    pub unsafe fn set_len(&mut self, new_len: usize) {
        self.size = new_len;
    }

    pub const fn len(&self) -> usize {
        self.size
    }

    pub const fn is_empty(&self) -> bool {
        self.size == 0
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

    pub fn from_utf8(v: &[u8]) -> Result<Self, InplaceUtf8Error> {
        match str::from_utf8(v) {
            Ok(str) => Self::try_from(str).map_err(InplaceUtf8Error::InplaceError),
            Err(err) => Err(InplaceUtf8Error::Utf8Error(err)),
        }
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
        value.try_into()
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

impl<'a, const N: usize> FromIterator<&'a char> for InplaceString<N> {
    fn from_iter<T: IntoIterator<Item = &'a char>>(iter: T) -> Self {
        let mut result = Self::new();
        for ch in iter {
            result.push(*ch);
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

impl<const N: usize> Debug for InplaceString<N> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct(&format!("InplaceString<{N}>"))
            .field("string", &self.as_str())
            .field("size", &self.size)
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
