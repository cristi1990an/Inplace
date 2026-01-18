use core::fmt;
use core::{
    fmt::Debug,
    hash::Hash,
    iter::FusedIterator,
    mem::MaybeUninit,
    num::NonZeroUsize,
    ops::{Add, Deref, DerefMut, Index, IndexMut, RangeBounds},
    ptr,
    slice::SliceIndex,
};

pub struct InplaceVector<T, const N: usize> {
    data: [MaybeUninit<T>; N],
    size: NonZeroUsize,
}

impl<T, const N: usize> InplaceVector<T, N> {
    pub const fn new() -> Self {
        InplaceVector {
            data: [const { MaybeUninit::uninit() }; N],
            size: unsafe { NonZeroUsize::new_unchecked(1) },
        }
    }

    /// Forces the length of the vector to new_len.
    /// This is a low-level operation that maintains none of the normal invariants of the type.
    ///
    /// # Safety
    ///
    /// - new_len must be less than or equal to capacity().
    /// - the elements at old_len..new_len must be initialized.
    ///
    pub unsafe fn set_len(&mut self, new_len: usize) {
        debug_assert!(new_len <= N);
        self.size = NonZeroUsize::new_unchecked(new_len.add(1));
    }

    pub fn spare_capacity_mut(&mut self) -> &mut [MaybeUninit<T>] {
        let len = self.capacity() - self.len();
        let ptr = unsafe { self.data.as_mut_ptr().add(self.len()) };
        unsafe { std::slice::from_raw_parts_mut(ptr, len) }
    }

    pub const fn len(&self) -> usize {
        unsafe { self.size.get().unchecked_sub(1) }
    }

    pub const fn capacity(&self) -> usize {
        N
    }

    pub const fn remaining_capacity(&self) -> usize {
        N - self.len()
    }

    pub const fn is_full(&self) -> bool {
        self.remaining_capacity() == 0
    }

    pub const fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub const fn as_ptr(&self) -> *const T {
        self.data.as_ptr() as *const T
    }

    pub const fn as_mut_ptr(&mut self) -> *mut T {
        self.data.as_mut_ptr() as *mut T
    }

    pub const fn as_slice(&self) -> &[T] {
        let len = self.len();
        let ptr = self.as_ptr();
        unsafe { std::slice::from_raw_parts(ptr, len) }
    }

    pub const fn as_mut_slice(&mut self) -> &mut [T] {
        let len = self.len();
        let ptr = self.as_mut_ptr();
        unsafe { std::slice::from_raw_parts_mut(ptr, len) }
    }

    /// Pushes a new value into the vector without checking that capacity is not exceeded.
    /// This is a low-level operation that can be used to optimize multiple push calls when
    /// the final size is known by the user to not exceed the total capacity.
    /// /// Return a reference to the newly added element.
    ///
    /// # Safety
    ///
    /// - len should be less than capacity.
    /// - undefined behavior otherwise.
    ///
    pub unsafe fn unchecked_push(&mut self, value: T) -> &T {
        debug_assert!(!self.is_full());
        let uninit_tail = self.spare_capacity_mut().get_unchecked_mut(0);
        uninit_tail.write(value);
        self.set_len(self.len() + 1);
        self.get_unchecked(self.len() - 1)
    }

    /// Appends an element to the back of the vector and returns a reference to it.
    ///
    /// # Panics
    /// Panics if the new size exceeds the vector's capacity (is_full == true).
    ///
    pub fn push(&mut self, value: T) -> &T {
        if self.is_full() {
            panic!("InplaceVector push should not exceed capacity");
        }

        unsafe { self.unchecked_push(value) }
    }

    /// Pushes a new value into the vector only if capacity allows it (is_full == false).
    /// Returns a Result with value Ok with a reference to the new element added at the end of the vector
    /// or value Err containing the value that was not inserted.
    ///
    pub fn push_within_capacity(&mut self, value: T) -> Result<&T, T> {
        if self.is_full() {
            Err(value)
        } else {
            unsafe { Ok(self.unchecked_push(value)) }
        }
    }

    /// Pushes a new value into the vector without checking that capacity is not exceeded.
    /// This is a low-level operation that can be used to optimize multiple push calls when
    /// the final size is known by the user to not exceed the total capacity.
    /// Return a mutable reference to the newly added element.
    ///
    /// # Safety
    ///
    /// - len should be less than capacity.
    /// - undefined behavior otherwise.
    ///
    pub unsafe fn unchecked_push_mut(&mut self, value: T) -> &mut T {
        debug_assert!(!self.is_full());
        let uninit_tail = self.spare_capacity_mut().get_unchecked_mut(0);
        uninit_tail.write(value);
        let new_len = self.len() + 1;
        self.set_len(new_len);
        self.get_unchecked_mut(new_len)
    }

    /// Appends an element to the back of the vector and returns a mutable reference to it.
    ///
    /// # Panics
    ///
    /// Panics if the new size exceeds the vector's capacity (is_full == true).
    ///
    pub fn push_mut(&mut self, value: T) -> &mut T {
        if self.is_full() {
            panic!("InplaceVector push should not exceed capacity");
        }

        unsafe { self.unchecked_push_mut(value) }
    }

    /// Pushes a new value into the vector only if capacity allows it (is_full == false).
    /// Returns a Result with value Ok with a mutable reference to the new element added at the end of the vector
    /// or value Err containing the value that was not inserted.
    ///
    pub fn push_within_capacity_mut(&mut self, value: T) -> Result<&mut T, T> {
        if self.is_full() {
            Err(value)
        } else {
            unsafe { Ok(self.unchecked_push_mut(value)) }
        }
    }

    /// Clones and appends all elements in a slice to the vector, returning a slice to the newly added elements,
    ///
    /// Iterates over the slice other, clones each element, and then appends it to this vector. The other slice is traversed in-order.
    ///
    /// # Panics
    ///
    /// Panics if the len of the slice would exceed the vector's remaining_capacity
    ///
    pub fn extend_from_slice(&mut self, other: &[T]) -> &[T]
    where
        T: Clone,
    {
        let old_len = self.len();
        if other.len() > self.remaining_capacity() {
            panic!("InplaceVector extend_from_slice should not exceed capacity");
        }

        for elem in other.iter().cloned() {
            unsafe { self.unchecked_push(elem) };
        }

        unsafe { self.get_unchecked(old_len..self.len()) }
    }

    /// Clones and appends all elements in a slice to the vector, returning a slice to the newly added elements,
    ///
    /// Iterates over the slice other, clones each element, and then appends it to this vector. The other slice is traversed in-order.
    ///
    /// # Panics
    ///
    /// Panics if the len of the slice would exceed the vector's remaining_capacity
    ///
    pub fn extend_from_slice_mut(&mut self, other: &[T]) -> &mut [T]
    where
        T: Clone,
    {
        let old_len = self.len();
        if other.len() > self.remaining_capacity() {
            panic!("InplaceVector extend_from_slice should not exceed capacity");
        }

        for elem in other.iter().cloned() {
            unsafe { self.unchecked_push(elem) };
        }

        let new_len = self.len();
        unsafe { self.get_unchecked_mut(old_len..new_len) }
    }

    pub fn extend_from_slice_within_capacity<'a>(&mut self, other: &'a [T]) -> Result<(), &'a [T]>
    where
        T: Clone,
    {
        let (to_clone, remaining) = other.split_at(self.remaining_capacity());
        for elem in to_clone.iter().cloned() {
            unsafe { self.unchecked_push(elem) };
        }

        if remaining.is_empty() {
            Ok(())
        } else {
            Err(remaining)
        }
    }

    pub fn extend_from_within<R>(&mut self, src: R)
    where
        R: RangeBounds<usize>,
        T: Clone,
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

        assert!(
            start <= end && end <= len,
            "range out of bounds: {}..{} for len {}",
            start,
            end,
            len
        );

        let count = end - start;

        if len + count > N {
            panic!(
                "extend_from_within would exceed capacity: {} + {} > {}",
                len, count, N
            );
        }

        for i in start..end {
            let elem = self[i].clone();
            unsafe {
                self.unchecked_push(elem);
            }
        }
    }

    pub fn append(&mut self, other: &mut InplaceVector<T, N>) {
        let count = other.len();
        if count == 0 {
            return;
        }

        let self_len = self.len();
        let remaining = self.remaining_capacity();
        if count > remaining {
            panic!("InplaceVector append should not exceed capacity");
        }

        unsafe {
            ptr::copy_nonoverlapping(
                other.as_ptr().add(0),
                self.as_mut_ptr().add(self_len),
                count,
            );
            other.set_len(0);
            self.set_len(self_len + count);
        }
    }

    pub fn clone_from_slice(&mut self, src: &[T])
    where
        T: Clone,
    {
        assert!(
            self.len() == src.len(),
            "destination and source slices have different lengths"
        );
        for (dest, source) in self.iter_mut().zip(src) {
            dest.clone_from(source);
        }
    }

    pub fn copy_from_slice(&mut self, src: &[T])
    where
        T: Copy,
    {
        assert!(
            self.len() == src.len(),
            "destination and source slices have different lengths"
        );
        unsafe {
            ptr::copy_nonoverlapping(src.as_ptr(), self.as_mut_ptr(), self.len());
        }
    }

    /// Pops the last value from the vector without checking that the vector is not empty.
    /// This is a low-level operation that can be used to optimize a pop call when
    /// the user knows for sure that the vector is not empty.
    ///
    /// # Safety
    ///
    /// - vector should not be empty.
    /// - undefined behavior otherwise.
    ///
    pub unsafe fn unchecked_pop(&mut self) -> T {
        debug_assert!(!self.is_empty());
        let index = self.len().unchecked_sub(1);
        let last_uninit = self.data.get_unchecked_mut(index);
        let last = last_uninit.assume_init_read();
        self.set_len(self.len() - 1);
        last
    }

    pub fn pop(&mut self) -> Option<T> {
        if self.is_empty() {
            None
        } else {
            Some(unsafe { self.unchecked_pop() })
        }
    }

    pub fn pop_if<Pred>(&mut self, predicate: Pred) -> Option<T>
    where
        Pred: FnOnce(&mut T) -> bool,
    {
        if let Some(last) = self.as_mut_slice().last_mut() {
            if predicate(last) {
                return Some(unsafe { self.unchecked_pop() });
            }
        }
        None
    }

    pub fn clear(&mut self) {
        while self.pop().is_some() {}
    }

    pub fn truncate(&mut self, new_len: usize) {
        if new_len < self.len() {
            while new_len != self.len() {
                unsafe {
                    self.unchecked_pop();
                }
            }
        }
    }

    pub fn resize_with<F>(&mut self, new_len: usize, mut f: F)
    where
        F: FnMut() -> T,
    {
        if new_len > self.capacity() {
            panic!("InplaceVector should not be resized above capacity");
        }

        if new_len > self.len() {
            while new_len != self.len() {
                unsafe {
                    self.unchecked_push(f());
                }
            }
        } else {
            self.truncate(new_len);
        }
    }

    pub fn resize(&mut self, new_len: usize, value: T)
    where
        T: Clone,
    {
        if new_len > self.capacity() {
            panic!("InplaceVector should not be resized above capacity");
        }

        if new_len > self.len() {
            while new_len != self.len() {
                unsafe {
                    self.unchecked_push(value.clone());
                }
            }
        } else {
            self.truncate(new_len);
        }
    }

    pub fn insert(&mut self, index: usize, element: T) -> &mut T {
        let len = self.len();
        if index > len {
            panic!("insertion index (is {index}) should be <= len (is {len})");
        }
        if self.is_full() {
            panic!("insert call should not exceed capacity");
        }

        unsafe { self.unchecked_push(element) };

        let slice = &mut self.as_mut_slice()[index..];
        slice.rotate_right(1);

        unsafe { self.get_unchecked_mut(index) }
    }

    pub fn split_off(&mut self, at: usize) -> Self {
        if at > self.len() {
            panic!(
                "'at' split index (is {at}) should be <= len (is {})",
                self.len()
            );
        }

        let other_len = self.len() - at;
        let mut other = Self::new();
        unsafe {
            self.set_len(at);
            other.set_len(other_len);
            ptr::copy_nonoverlapping(self.as_ptr().add(at), other.as_mut_ptr(), other_len);
        }
        other
    }

    pub fn try_remove(&mut self, index: usize) -> Option<T> {
        let len = self.len();
        if index >= len {
            return None;
        }
        unsafe {
            let ret;
            {
                let ptr = self.as_mut_ptr().add(index);
                ret = ptr::read(ptr);
                ptr::copy(ptr.add(1), ptr, len - index - 1);
            }
            self.set_len(len - 1);
            Some(ret)
        }
    }

    pub fn remove(&mut self, index: usize) -> T {
        match self.try_remove(index) {
            Some(value) => value,
            None => {
                let len = self.len();
                panic!("removal index (is {index}) should be < len (is {len})");
            }
        }
    }

    pub fn swap_remove(&mut self, index: usize) -> T {
        let len = self.len();
        if index >= len {
            panic!("removal index (is {index}) should be < len (is {len})");
        }

        unsafe {
            let value = ptr::read(self.as_ptr().add(index));
            let base_ptr = self.as_mut_ptr();
            ptr::copy(base_ptr.add(len - 1), base_ptr.add(index), 1);
            self.set_len(len - 1);
            value
        }
    }

    pub fn drain<R>(&mut self, range: R) -> Self
    where
        R: RangeBounds<usize>,
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
            panic!("drain range out of bounds");
        }

        let count = end - start;

        let mut drained = Self::new();

        unsafe {
            ptr::copy_nonoverlapping(self.as_ptr().add(start), drained.as_mut_ptr(), count);
            drained.set_len(count);

            let tail = len - end;
            if tail > 0 {
                let base = self.as_mut_ptr();
                ptr::copy(base.add(end), base.add(start), tail);
            }

            self.set_len(len - count);
        }

        drained
    }

    pub fn dedup_by<F>(&mut self, mut same_bucket: F)
    where
        F: FnMut(&mut T, &mut T) -> bool,
    {
        let len = self.len();
        if len <= 1 {
            return;
        }

        unsafe {
            let ptr = self.as_mut_ptr();
            let mut write = 1;

            for read in 1..len {
                let prev = ptr.add(write - 1);
                let curr = ptr.add(read);

                if same_bucket(&mut *prev, &mut *curr) {
                    ptr::drop_in_place(curr);
                } else {
                    if write != read {
                        ptr::copy_nonoverlapping(curr, ptr.add(write), 1);
                    }
                    write += 1;
                }
            }

            self.set_len(write);
        }
    }

    pub fn dedup(&mut self)
    where
        T: PartialEq,
    {
        self.dedup_by(|a, b| a == b);
    }

    pub fn dedup_by_key<F, K>(&mut self, mut key: F)
    where
        F: FnMut(&mut T) -> K,
        K: PartialEq,
    {
        self.dedup_by(|a, b| key(a) == key(b));
    }

    pub fn retain<F>(&mut self, mut f: F)
    where
        F: FnMut(&T) -> bool,
    {
        self.retain_mut(|elem| f(elem));
    }

    pub fn retain_mut<F>(&mut self, mut f: F)
    where
        F: FnMut(&mut T) -> bool,
    {
        let mut keep = 0;
        for i in 0..self.len() {
            if f(&mut self[i]) {
                if keep != i {
                    self.swap(keep, i);
                }
                keep += 1;
            }
        }
        self.truncate(keep);
    }

}

impl<T, const N: usize> FromIterator<T> for InplaceVector<T, N> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let mut result = Self::new();
        result.extend(iter);
        result
    }
}

impl<T, const N: usize> Extend<T> for InplaceVector<T, N> {
    fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        let it = iter.into_iter();
        match it.size_hint() {
            (lowerbound, _) if lowerbound > self.remaining_capacity() => {
                panic!("Can't extend {lowerbound} elements into InplaceVector<_, {N}>")
            }

            (_, Some(upperbound)) if upperbound <= self.remaining_capacity() => {
                for elem in it {
                    unsafe { self.unchecked_push(elem) };
                }
            }
            _ => {
                for elem in it {
                    self.push(elem);
                }
            }
        };
    }
}

impl<const N: usize> std::io::Write for InplaceVector<u8, N> {
    fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
        let old_len = self.len();
        let min = self.remaining_capacity().min(buf.len());
        unsafe {
            std::ptr::copy_nonoverlapping(buf.as_ptr(), self.as_mut_ptr().add(old_len), min);
            self.set_len(old_len + min);
        }

        Ok(min)
    }

    fn flush(&mut self) -> std::io::Result<()> {
        Ok(())
    }
}

impl<T, const N: usize> Drop for InplaceVector<T, N> {
    fn drop(&mut self) {
        self.clear();
    }
}

impl<T, const N: usize> IntoIterator for InplaceVector<T, N> {
    type Item = T;

    type IntoIter = IntoIter<T, N>;

    fn into_iter(self) -> Self::IntoIter {
        let len = self.len();
        let data = unsafe { std::ptr::read(&self.data) };
        std::mem::forget(self);
        IntoIter {
            data,
            begin: 0,
            end: len,
        }
    }
}

impl<'a, T, const N: usize> IntoIterator for &'a InplaceVector<T, N> {
    type Item = &'a T;

    type IntoIter = std::slice::Iter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.as_slice().iter()
    }
}

impl<'a, T, const N: usize> IntoIterator for &'a mut InplaceVector<T, N> {
    type Item = &'a mut T;

    type IntoIter = std::slice::IterMut<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.as_mut_slice().iter_mut()
    }
}

impl<T: Clone, const N: usize> Clone for InplaceVector<T, N> {
    fn clone(&self) -> Self {
        let mut result = Self::new();

        for value in self.as_slice() {
            unsafe { result.unchecked_push(value.clone()) };
        }

        result
    }
}

impl<T: Clone, const N: usize> Default for InplaceVector<T, N> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T, const N: usize> Deref for InplaceVector<T, N> {
    type Target = [T];

    fn deref(&self) -> &Self::Target {
        self.as_slice()
    }
}

impl<T, const N: usize> DerefMut for InplaceVector<T, N> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.as_mut_slice()
    }
}

impl<T, I, const N: usize> Index<I> for InplaceVector<T, N>
where
    I: SliceIndex<[T]>,
{
    type Output = <I as SliceIndex<[T]>>::Output;

    fn index(&self, index: I) -> &Self::Output {
        Index::index(self.as_slice(), index)
    }
}

impl<T, I, const N: usize> IndexMut<I> for InplaceVector<T, N>
where
    I: SliceIndex<[T]>,
{
    fn index_mut(&mut self, index: I) -> &mut <InplaceVector<T, N> as Index<I>>::Output {
        IndexMut::index_mut(self.as_mut_slice(), index)
    }
}

impl<T, const N: usize> PartialEq for InplaceVector<T, N>
where
    T: PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        self.as_slice() == other.as_slice()
    }
}

impl<T, U, const N: usize, const M: usize> PartialEq<&[U; M]> for InplaceVector<T, N>
where
    T: PartialEq<U>,
{
    fn eq(&self, other: &&[U; M]) -> bool {
        self.as_slice().eq(*other)
    }
}

impl<T, U, const N: usize, const M: usize> PartialEq<&mut [U; M]> for InplaceVector<T, N>
where
    T: PartialEq<U>,
{
    fn eq(&self, other: &&mut [U; M]) -> bool {
        self.as_slice().eq(*other)
    }
}

impl<T, U, const N: usize> PartialEq<&[U]> for InplaceVector<T, N>
where
    T: PartialEq<U>,
{
    fn eq(&self, other: &&[U]) -> bool {
        self.as_slice().eq(*other)
    }
}

impl<T, U, const N: usize> PartialEq<&mut [U]> for InplaceVector<T, N>
where
    T: PartialEq<U>,
{
    fn eq(&self, other: &&mut [U]) -> bool {
        self.as_slice().eq(*other)
    }
}

impl<T, const N: usize> Eq for InplaceVector<T, N> where T: Eq {}

impl<T, const N: usize> PartialOrd for InplaceVector<T, N>
where
    T: PartialOrd,
{
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        self.as_slice().partial_cmp(other.as_slice())
    }
}

impl<T, const N: usize> Hash for InplaceVector<T, N>
where
    T: Hash,
{
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.as_slice().hash(state);
    }
}

impl<T: fmt::Debug, const N: usize> Debug for InplaceVector<T, N> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        fmt::Debug::fmt(&**self, f)
    }
}

impl<T, const N: usize> AsMut<InplaceVector<T, N>> for InplaceVector<T, N> {
    fn as_mut(&mut self) -> &mut InplaceVector<T, N> {
        self
    }
}

impl<T, const N: usize> AsMut<[T]> for InplaceVector<T, N> {
    fn as_mut(&mut self) -> &mut [T] {
        self
    }
}

impl<T, const N: usize> From<[T; N]> for InplaceVector<T, N> {
    fn from(value: [T; N]) -> Self {
        let mut result = Self::new();
        unsafe {
            result.set_len(N);
            ptr::copy_nonoverlapping(value.as_ptr(), result.as_mut_ptr(), N);
            std::mem::forget(value);
        };
        result
    }
}

impl<'a, T: Clone, const N: usize> TryFrom<&'a [T]> for InplaceVector<T, N> {
    type Error = &'a [T];

    fn try_from(slice: &'a [T]) -> Result<Self, Self::Error> {
        let count = slice.len();
        if count > N {
            return Err(slice);
        }

        let mut result = InplaceVector::new();

        unsafe {
            result.set_len(count);
            ptr::copy_nonoverlapping(slice.as_ptr(), result.as_mut_ptr(), count);
        };

        Ok(result)
    }
}

impl<T, const N: usize> TryFrom<InplaceVector<T, N>> for [T; N] {
    type Error = InplaceVector<T, N>;

    fn try_from(mut vec: InplaceVector<T, N>) -> Result<[T; N], InplaceVector<T, N>> {
        if vec.len() != N {
            return Err(vec);
        }

        let array = unsafe {
            vec.set_len(0);
            ptr::read(vec.as_ptr() as *const [T; N])
        };
        Ok(array)
    }
}

pub struct IntoIter<T, const N: usize> {
    data: [MaybeUninit<T>; N],
    begin: usize,
    end: usize,
}

impl<T, const N: usize> IntoIter<T, N> {
    fn as_ptr(&self) -> *const T {
        unsafe { (self.data.as_ptr() as *const T).add(self.begin) }
    }

    fn as_mut_ptr(&mut self) -> *mut T {
        unsafe { (self.data.as_mut_ptr() as *mut T).add(self.begin) }
    }

    const fn len(&self) -> usize {
        self.end - self.begin
    }

    const fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub fn as_slice(&self) -> &[T] {
        let ptr = self.as_ptr();
        unsafe { std::slice::from_raw_parts(ptr, self.len()) }
    }

    pub fn as_mut_slice(&mut self) -> &mut [T] {
        let ptr = self.as_mut_ptr();
        unsafe { std::slice::from_raw_parts_mut(ptr, self.len()) }
    }

    unsafe fn unchecked_next(&mut self) -> T {
        let next_uninit = self.data.get_unchecked(self.begin);
        self.begin += 1;
        next_uninit.assume_init_read()
    }

    unsafe fn unchecked_back(&mut self) -> T {
        let back_uninit = self.data.get_unchecked(self.end - 1);
        self.end -= 1;
        back_uninit.assume_init_read()
    }

    unsafe fn unchecked_push(&mut self, value: T) {
        let back_uninit = self.data.get_unchecked_mut(self.end);
        self.end += 1;
        back_uninit.write(value);
    }
}

impl<T, const N: usize> Iterator for IntoIter<T, N> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        if self.is_empty() {
            None
        } else {
            Some(unsafe { self.unchecked_next() })
        }
    }
}

impl<T, const N: usize> DoubleEndedIterator for IntoIter<T, N> {
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.is_empty() {
            None
        } else {
            Some(unsafe { self.unchecked_back() })
        }
    }
}

impl<T, const N: usize> FusedIterator for IntoIter<T, N> {}

impl<T, const N: usize> Drop for IntoIter<T, N> {
    fn drop(&mut self) {
        while self.next_back().is_some() {}
    }
}

impl<T, const N: usize> Default for IntoIter<T, N> {
    fn default() -> Self {
        Self {
            data: [const { MaybeUninit::uninit() }; N],
            begin: 0,
            end: 0,
        }
    }
}

impl<T: Clone, const N: usize> Clone for IntoIter<T, N> {
    fn clone(&self) -> Self {
        let mut result = Self::default();
        unsafe {
            std::ptr::copy_nonoverlapping(
                self.as_ptr().add(self.begin),
                result.as_mut_ptr(),
                self.len(),
            );
            result.end = self.len()
        }
        result
    }
}

impl<T, const N: usize> AsRef<[T]> for IntoIter<T, N> {
    fn as_ref(&self) -> &[T] {
        self.as_slice()
    }
}

#[cfg(test)]
mod tests {
    use crate::inplace_vec;
    use core::cell::Cell;

    use super::*;

    #[test]
    fn test_iter_clone() {
        let vec = inplace_vec![
            "1".to_owned(),
            "2".to_owned(),
            "3".to_owned(),
            "4".to_owned(),
            "5".to_owned()
        ];

        let mut iter = vec.into_iter();
        iter.next();

        let clone = iter;

        assert!(clone.eq(["2", "3", "4", "5"]));
    }
    #[test]
    fn test_macro() {
        let deduced_size = inplace_vec![
            "1".to_owned(),
            "2".to_owned(),
            "3".to_owned(),
            "4".to_owned(),
            "5".to_owned()
        ];

        assert_eq!(deduced_size.capacity(), 5);
        assert!(deduced_size.iter().eq(&["1", "2", "3", "4", "5"]));

        let specific_size = inplace_vec![
            8;
            "1".to_owned(),
            "2".to_owned(),
            "3".to_owned(),
            "4".to_owned(),
            "5".to_owned()
        ];

        assert_eq!(specific_size.capacity(), 8);
        assert!(specific_size.iter().eq(&["1", "2", "3", "4", "5"]));

        let one_element_vec = inplace_vec![42];

        assert_eq!(one_element_vec.capacity(), 1);
        assert!(one_element_vec.iter().eq(&[42]));

        let mut capacity_spec = inplace_vec!(5;);
        capacity_spec.push(42); // for deduction

        assert_eq!(capacity_spec.first(), Some(42).as_ref());
        assert_eq!(capacity_spec.capacity(), 5);
    }

    #[test]
    fn basic_push_pop_and_len_capacity() {
        let mut v = InplaceVector::<i32, 4>::new();
        assert_eq!(v.len(), 0);
        assert_eq!(v.capacity(), 4);
        v.push(1);
        v.push(2);
        assert_eq!(v.len(), 2);
        assert_eq!(v.pop(), Some(2));
        assert_eq!(v.pop(), Some(1));
        assert_eq!(v.pop(), None);
        assert!(v.is_empty());
    }

    #[test]
    #[should_panic]
    fn push_panics_when_full() {
        let mut v = InplaceVector::<i32, 2>::new();
        v.push(10);
        v.push(20);
        v.push(30);
    }

    #[test]
    fn push_within_capacity_behavior() {
        let mut v = InplaceVector::<i32, 2>::new();
        assert!(v.push_within_capacity(5).is_ok());
        assert!(v.push_within_capacity(6).is_ok());
        assert!(v.push_within_capacity(7).is_err());
        assert_eq!(v.as_slice(), &[5, 6]);
    }

    #[test]
    fn as_slice_and_mut_slice_and_index() {
        let mut v = InplaceVector::<i32, 4>::new();
        v.push(7);
        v.push(8);
        assert_eq!(v.as_slice(), &[7, 8]);
        v.as_mut_slice()[1] = 42;
        assert_eq!(v[1], 42);
    }

    #[test]
    fn iter_and_iter_mut() {
        let mut v = InplaceVector::<i32, 4>::new();
        v.push(0);
        v.push(1);
        v.push(2);

        let collected: Vec<_> = v.iter().copied().collect();
        assert_eq!(collected, vec![0, 1, 2]);

        for x in v.iter_mut() {
            *x += 10;
        }
        assert_eq!(v.as_slice(), &[10, 11, 12]);
    }

    #[test]
    fn append_moves_and_empties_other() {
        let mut a = InplaceVector::<String, 6>::new();
        a.push("1".into());
        a.push("2".into());

        let mut b = InplaceVector::<String, 6>::new();
        b.push("3".into());
        b.push("4".into());
        b.push("5".into());

        a.append(&mut b);
        assert_eq!(a.as_slice(), &["1", "2", "3", "4", "5"]);
        assert_eq!(b.len(), 0);
    }

    #[test]
    fn split_off_edges_and_middle() {
        let mut v = InplaceVector::<i32, 8>::new();
        for i in 0..6 {
            v.push(i);
        }

        let o1 = v.split_off(2);
        assert_eq!(v.as_slice(), &[0, 1]);
        assert_eq!(o1.as_slice(), &[2, 3, 4, 5]);

        let mut v2 = InplaceVector::<i32, 4>::new();
        for i in 0..4 {
            v2.push(i);
        }
        let o2 = v2.split_off(0);
        assert_eq!(v2.as_slice(), &[]);
        assert_eq!(o2.as_slice(), &[0, 1, 2, 3]);

        let mut v3 = InplaceVector::<i32, 4>::new();
        for i in 0..3 {
            v3.push(i);
        }
        let o3 = v3.split_off(3);
        assert_eq!(v3.as_slice(), &[0, 1, 2]);
        assert_eq!(o3.as_slice(), &[]);
    }

    #[test]
    fn insert_remove_swap_remove() {
        let mut v = InplaceVector::<i32, 6>::new();
        v.push(1);
        v.push(3);
        v.push(4);

        v.insert(1, 2);
        assert_eq!(v.as_slice(), &[1, 2, 3, 4]);

        let removed = v.remove(2);
        assert_eq!(removed, 3);
        assert_eq!(v.as_slice(), &[1, 2, 4]);

        v.push(9);
        let swapped = v.swap_remove(1);
        assert_eq!(swapped, 2);
        assert_eq!(v.len(), 3);
        assert_eq!(v.as_slice()[1], 9);
    }

    #[test]
    fn retain_and_retain_mut() {
        let mut v = InplaceVector::<i32, 8>::new();
        for i in 0..8 {
            v.push(i);
        }
        v.retain(|&x| x % 2 == 0);
        assert_eq!(v.as_slice(), &[0, 2, 4, 6]);

        let mut v2 = InplaceVector::<i32, 8>::new();
        for i in 0..8 {
            v2.push(i);
        }
        v2.retain_mut(|x| {
            *x += 1;
            (*x) % 2 == 0
        });
        assert_eq!(v2.as_slice(), &[2, 4, 6, 8], "sanity");
        assert_eq!(v2.len(), 4);
    }

    #[test]
    fn clone_from_slice_and_copy_from_slice() {
        let mut v = InplaceVector::<String, 3>::new();
        v.push("a".to_string());
        v.push("b".to_string());
        v.push("c".to_string());

        let src = ["x".to_string(), "y".to_string(), "z".to_string()];
        v.clone_from_slice(&src);
        assert_eq!(
            v.as_slice(),
            &["x".to_string(), "y".to_string(), "z".to_string()]
        );

        let mut c = InplaceVector::<u32, 3>::new();
        c.push(1);
        c.push(2);
        c.push(3);

        let src2 = [9u32, 8u32, 7u32];
        c.copy_from_slice(&src2);
        assert_eq!(c.as_slice(), &[9, 8, 7]);
    }

    #[test]
    fn from_array_and_try_from_slice() {
        let arr = [1u8, 2u8, 3u8, 4u8];
        let v: InplaceVector<u8, 4> = InplaceVector::from(arr);
        assert_eq!(v.as_slice(), &[1, 2, 3, 4]);

        let s = [10u16, 20u16];
        let try_v = InplaceVector::<u16, 4>::try_from(&s[..]);
        assert!(try_v.is_ok());
        let v2 = try_v.unwrap();
        assert_eq!(v2.as_slice(), &[10, 20]);
        let big: &[u16] = &[1, 2, 3, 4, 5];
        assert!(InplaceVector::<u16, 4>::try_from(big).is_err());
    }

    #[test]
    fn try_from_into_array_success_and_failure() {
        let mut v = InplaceVector::<i32, 3>::new();
        v.push(1);
        v.push(2);
        v.push(3);

        let arr_res: Result<[i32; 3], _> = <[i32; 3]>::try_from(v);
        assert!(arr_res.is_ok());
        assert_eq!(arr_res.unwrap(), [1, 2, 3]);

        let mut v2 = InplaceVector::<i32, 3>::new();
        v2.push(4);
        let conv: Result<[i32; 3], _> = <[i32; 3]>::try_from(v2);
        assert!(conv.is_err());
    }

    #[test]
    fn into_iter_consumes_and_double_ended() {
        let mut v = InplaceVector::<i32, 5>::new();
        for i in 0..4 {
            v.push(i);
        }
        let mut into = v.into_iter();
        assert_eq!(into.next(), Some(0));
        assert_eq!(into.next_back(), Some(3));
        assert_eq!(into.next(), Some(1));
        assert_eq!(into.next_back(), Some(2));
        assert_eq!(into.next(), None);
    }

    #[test]
    fn spare_capacity_and_set_len_manual_init() {
        let mut v = InplaceVector::<i32, 6>::new();
        v.push(1);
        v.push(2);

        let spare = v.spare_capacity_mut();
        assert_eq!(spare.len(), 4);
        spare[0].write(10);
        spare[1].write(20);

        unsafe {
            v.set_len(4);
        }
        assert_eq!(v, &[1, 2, 10, 20]);
    }

    #[test]
    fn resize_and_resize_with_and_truncate_clear() {
        let mut v = InplaceVector::<i32, 6>::new();
        v.push(1);
        v.push(2);

        v.resize(5, 7);
        assert_eq!(v, &[1, 2, 7, 7, 7]);

        v.resize_with(3, || 9);
        assert_eq!(v, &[1, 2, 7]);

        v.truncate(1);
        assert_eq!(v, &[1]);

        v.clear();
        assert_eq!(v.len(), 0);
    }

    #[test]
    fn pop_if_checks_last_elem() {
        let mut v = InplaceVector::<i32, 4>::new();
        v.push(5);
        v.push(10);

        let p = v.pop_if(|x| *x == 10);
        assert_eq!(p, Some(10));
        assert_eq!(v.as_slice(), &[5]);

        let p2 = v.pop_if(|x| *x == 100);
        assert_eq!(p2, None);
    }

    #[test]
    fn default_and_clone_and_debug() {
        let mut v = InplaceVector::<i32, 4>::default();
        v.push(3);
        let c = v.clone();
        assert_eq!(c.as_slice(), &[3]);
        assert_eq!(format!("{:?}", c), "[3]");
    }

    #[test]
    fn drop_behavior_managed_by_set_len() {
        let counter = Cell::new(0);
        struct DC<'a>(&'a Cell<u32>);
        impl<'a> Drop for DC<'a> {
            fn drop(&mut self) {
                self.0.set(self.0.get() + 1);
            }
        }

        {
            let mut v = InplaceVector::<DC, 4>::new();
            v.push(DC(&counter));
            v.push(DC(&counter));

            unsafe {
                v.set_len(1);
            }
        }
        assert!(counter.get() <= 2);
    }

    #[test]
    #[should_panic(expected = "insertion index")]
    fn insert_out_of_bounds_panics() {
        let mut v = InplaceVector::<i32, 3>::new();
        v.push(1);
        v.insert(2, 5); // len is 1, index 2 is invalid
    }

    #[test]
    #[should_panic(expected = "insert call should not exceed capacity")]
    fn insert_when_full_panics() {
        let mut v = InplaceVector::<i32, 2>::new();
        v.push(1);
        v.push(2);
        v.insert(1, 3);
    }

    #[test]
    #[should_panic(expected = "removal index")]
    fn remove_out_of_bounds_panics() {
        let mut v = InplaceVector::<i32, 2>::new();
        v.push(1);
        v.remove(1);
    }

    #[test]
    #[should_panic(expected = "removal index")]
    fn swap_remove_out_of_bounds_panics() {
        let mut v = InplaceVector::<i32, 2>::new();
        v.push(1);
        v.swap_remove(1);
    }

    #[test]
    #[should_panic(expected = "range out of bounds")]
    fn drain_out_of_bounds_panics() {
        let mut v = InplaceVector::<i32, 3>::new();
        v.push(1);
        v.push(2);
        v.drain(0..4);
    }

    #[test]
    fn drain_removes_correct_range() {
        let mut v = InplaceVector::<i32, 5>::new();
        for i in 0..5 { v.push(i); }
        let drained = v.drain(1..4);
        assert_eq!(drained.as_slice(), &[1, 2, 3]);
        assert_eq!(v.as_slice(), &[0, 4]);
    }

    #[test]
    fn split_off_at_len_and_zero() {
        let mut v = InplaceVector::<i32, 3>::new();
        v.push(1);
        v.push(2);
        let tail = v.split_off(2);
        assert_eq!(tail.as_slice(), &[]);
        assert_eq!(v.as_slice(), &[1, 2]);

        let mut v2 = InplaceVector::<i32, 3>::new();
        v2.push(1);
        let head = v2.split_off(0);
        assert_eq!(head.as_slice(), &[1]);
        assert_eq!(v2.as_slice(), &[]);
    }

    #[test]
    #[should_panic]
    fn extend_from_slice_panics_when_too_big() {
        let mut v = InplaceVector::<i32, 2>::new();
        let slice = [1, 2, 3];
        v.extend_from_slice(&slice);
    }

    #[test]
    fn try_from_slice_failure_and_success() {
        let arr = [1, 2, 3, 4];
        assert!(InplaceVector::<i32, 3>::try_from(&arr[..]).is_err());
        let arr2 = [1, 2];
        let v = InplaceVector::<i32, 3>::try_from(&arr2[..]).unwrap();
        assert_eq!(v.as_slice(), &[1, 2]);
    }

    #[test]
    #[should_panic]
    fn resize_panics_when_exceeds_capacity() {
        let mut v = InplaceVector::<i32, 2>::new();
        v.resize(3, 1);
    }

    #[test]
    #[should_panic]
    fn resize_with_panics_when_exceeds_capacity() {
        let mut v = InplaceVector::<i32, 2>::new();
        v.resize_with(3, || 1);
    }

    #[test]
    fn dedup_variants() {
        let mut v = InplaceVector::<i32, 5>::new();
        v.push(1); v.push(1); v.push(2); v.push(2); v.push(3);
        v.dedup();
        assert_eq!(v.as_slice(), &[1, 2, 3]);

        let mut v2 = InplaceVector::<i32, 10>::new();
        v2.push(1); v2.push(1); v2.push(2); v2.push(2); v2.push(4); v2.push(3); v2.push(5); v2.push(7);
        v2.dedup_by(|a, b| *a % 2 == *b % 2);
        assert_eq!(v2.as_slice(), &[1, 2, 3]);
    }

    #[test]
    fn dedup_by_key_example() {
        let mut v = InplaceVector::<i32, 5>::new();
        v.push(1); v.push(3); v.push(2); v.push(4); v.dedup_by_key(|x| *x % 2);
        assert_eq!(v.as_slice(), &[1, 2]);
    }

    #[test]
    #[should_panic]
    fn append_panics_when_overflow() {
        let mut a = InplaceVector::<i32, 2>::new();
        a.push(1);

        let mut b = InplaceVector::<i32, 2>::new();
        b.push(2); b.push(3);

        a.append(&mut b)
    }

    #[test]
    fn into_iter_clone_and_double_ended() {
        let mut v = InplaceVector::<i32, 3>::new();
        v.push(10); v.push(20);
        let mut iter = v.clone().into_iter();
        assert_eq!(iter.next(), Some(10));
        assert_eq!(iter.next_back(), Some(20));
        assert_eq!(iter.next(), None);

        let mut iter2 = v.into_iter();
        let mut clone = iter2.clone();
        assert_eq!(clone.as_slice(), &[10, 20]);
    }

    #[test]
    fn write_trait_behavior() {
        let mut v = InplaceVector::<u8, 4>::new();
        let buf = [1, 2, 3, 4, 5];
        let written = std::io::Write::write(&mut v, &buf).unwrap();
        assert_eq!(written, 4);
        assert_eq!(v.as_slice(), &[1, 2, 3, 4]);
    }
}
