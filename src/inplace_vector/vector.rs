use core::fmt;
use core::{
    fmt::Debug,
    hash::Hash,
    iter::{ExactSizeIterator, FusedIterator},
    marker::PhantomData,
    mem::MaybeUninit,
    num::NonZeroUsize,
    ops::{Add, Deref, DerefMut, Index, IndexMut, RangeBounds},
    ptr,
    slice::SliceIndex,
};

/// A fixed-capacity vector stored inline.
///
/// `InplaceVector<T, N>` stores up to `N` elements without heap allocation.
///
/// # Examples
///
/// ```
/// use inplace_containers::InplaceVector;
///
/// let mut v: InplaceVector<i32, 4> = InplaceVector::new();
/// v.push(1);
/// v.push(2);
/// assert_eq!(v, &[1, 2]);
/// ```
pub struct InplaceVector<T, const N: usize> {
    data: [MaybeUninit<T>; N],
    size: NonZeroUsize,
}

/// Errors returned by fallible `InplaceVector` conversions.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum InplaceVectorError {
    /// The source length did not match the expected length.
    LengthMismatch {
        expected_len: usize,
        actual_len: usize,
    },
}

impl<T, const N: usize> InplaceVector<T, N> {
    /// Creates a new empty `InplaceVector`.
    ///
    /// The capacity is fixed at `N`.
    ///
    /// # Examples
    ///
    /// ```
    /// use inplace_containers::InplaceVector;
    ///
    /// let v: InplaceVector<i32, 4> = InplaceVector::new();
    /// assert_eq!(v.len(), 0);
    /// assert_eq!(v.capacity(), 4);
    /// ```
    #[must_use]
    #[inline]
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
    /// # Examples
    ///
    /// ```no_run
    /// use inplace_containers::InplaceVector;
    ///
    /// let mut v: InplaceVector<i32, 2> = InplaceVector::new();
    /// let spare = v.spare_capacity_mut();
    /// spare[0].write(10);
    /// unsafe {
    ///     v.set_len(1);
    /// }
    /// assert_eq!(v, &[10]);
    /// ```
    ///
    #[inline]
    pub unsafe fn set_len(&mut self, new_len: usize) {
        debug_assert!(new_len <= N);
        self.size = NonZeroUsize::new_unchecked(new_len.add(1));
    }

    /// Returns the remaining spare capacity as a slice of `MaybeUninit<T>`.
    ///
    /// # Examples
    ///
    /// ```
    /// use inplace_containers::InplaceVector;
    ///
    /// let mut v: InplaceVector<i32, 3> = InplaceVector::new();
    /// v.push(1);
    /// let spare = v.spare_capacity_mut();
    /// assert_eq!(spare.len(), 2);
    /// spare[0].write(2);
    /// unsafe {
    ///     v.set_len(2);
    /// }
    /// assert_eq!(v, &[1, 2]);
    /// ```
    #[must_use]
    #[inline]
    pub fn spare_capacity_mut(&mut self) -> &mut [MaybeUninit<T>] {
        let len = self.capacity() - self.len();
        let ptr = unsafe { self.data.as_mut_ptr().add(self.len()) };
        unsafe { std::slice::from_raw_parts_mut(ptr, len) }
    }

    /// Returns the number of elements in the vector.
    ///
    /// # Examples
    ///
    /// ```
    /// use inplace_containers::InplaceVector;
    ///
    /// let mut v: InplaceVector<i32, 4> = InplaceVector::new();
    /// assert_eq!(v.len(), 0);
    /// v.push(1);
    /// assert_eq!(v.len(), 1);
    /// ```
    #[must_use]
    #[inline]
    pub const fn len(&self) -> usize {
        unsafe { self.size.get().unchecked_sub(1) }
    }

    /// Returns the total capacity of the vector.
    ///
    /// # Examples
    ///
    /// ```
    /// use inplace_containers::InplaceVector;
    ///
    /// let v: InplaceVector<i32, 4> = InplaceVector::new();
    /// assert_eq!(v.capacity(), 4);
    /// ```
    #[must_use]
    #[inline]
    pub const fn capacity(&self) -> usize {
        N
    }

    /// Returns how many more elements the vector can hold.
    ///
    /// # Examples
    ///
    /// ```
    /// use inplace_containers::InplaceVector;
    ///
    /// let mut v: InplaceVector<i32, 3> = InplaceVector::new();
    /// v.push(1);
    /// assert_eq!(v.remaining_capacity(), 2);
    /// ```
    #[must_use]
    #[inline]
    pub const fn remaining_capacity(&self) -> usize {
        N - self.len()
    }

    /// Returns `true` if the vector has no remaining capacity.
    ///
    /// # Examples
    ///
    /// ```
    /// use inplace_containers::InplaceVector;
    ///
    /// let mut v: InplaceVector<i32, 1> = InplaceVector::new();
    /// assert!(!v.is_full());
    /// v.push(1);
    /// assert!(v.is_full());
    /// ```
    #[must_use]
    #[inline]
    pub const fn is_full(&self) -> bool {
        self.remaining_capacity() == 0
    }

    /// Returns `true` if the vector contains no elements.
    ///
    /// # Examples
    ///
    /// ```
    /// use inplace_containers::InplaceVector;
    ///
    /// let mut v: InplaceVector<i32, 2> = InplaceVector::new();
    /// assert!(v.is_empty());
    /// v.push(1);
    /// assert!(!v.is_empty());
    /// ```
    #[must_use]
    #[inline]
    pub const fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Returns a raw pointer to the vector's buffer.
    ///
    /// # Examples
    ///
    /// ```
    /// use inplace_containers::InplaceVector;
    ///
    /// let mut v: InplaceVector<i32, 2> = InplaceVector::new();
    /// v.push(10);
    /// let ptr = v.as_ptr();
    /// unsafe {
    ///     assert_eq!(*ptr, 10);
    /// }
    /// ```
    #[must_use]
    #[inline]
    pub const fn as_ptr(&self) -> *const T {
        self.data.as_ptr() as *const T
    }

    /// Returns a mutable raw pointer to the vector's buffer.
    ///
    /// # Examples
    ///
    /// ```
    /// use inplace_containers::InplaceVector;
    ///
    /// let mut v: InplaceVector<i32, 2> = InplaceVector::new();
    /// v.push(1);
    /// let ptr = v.as_mut_ptr();
    /// unsafe {
    ///     *ptr = 5;
    /// }
    /// assert_eq!(v, &[5]);
    /// ```
    #[must_use]
    #[inline]
    pub const fn as_mut_ptr(&mut self) -> *mut T {
        self.data.as_mut_ptr() as *mut T
    }

    /// Returns a shared slice of all initialized elements.
    ///
    /// # Examples
    ///
    /// ```
    /// use inplace_containers::InplaceVector;
    ///
    /// let mut v: InplaceVector<i32, 3> = InplaceVector::new();
    /// v.push(1);
    /// v.push(2);
    /// assert_eq!(v, &[1, 2]);
    /// ```
    #[must_use]
    #[inline]
    pub const fn as_slice(&self) -> &[T] {
        let len = self.len();
        let ptr = self.as_ptr();
        unsafe { std::slice::from_raw_parts(ptr, len) }
    }

    /// Returns a mutable slice of all initialized elements.
    ///
    /// # Examples
    ///
    /// ```
    /// use inplace_containers::InplaceVector;
    ///
    /// let mut v: InplaceVector<i32, 3> = InplaceVector::new();
    /// v.push(1);
    /// v.push(2);
    /// v.as_mut_slice()[1] = 7;
    /// assert_eq!(v, &[1, 7]);
    /// ```
    #[must_use]
    #[inline]
    pub const fn as_mut_slice(&mut self) -> &mut [T] {
        let len = self.len();
        let ptr = self.as_mut_ptr();
        unsafe { std::slice::from_raw_parts_mut(ptr, len) }
    }

    /// Pushes a new value into the vector without checking that capacity is not exceeded.
    ///
    /// This is a low-level operation that can be used to optimize multiple push calls when
    /// the final size is known by the user to not exceed the total capacity.
    /// Returns a reference to the newly added element.
    ///
    /// # Safety
    ///
    /// - len should be less than capacity.
    /// - undefined behavior otherwise.
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use inplace_containers::InplaceVector;
    ///
    /// let mut v: InplaceVector<i32, 2> = InplaceVector::new();
    /// unsafe {
    ///     v.unchecked_push(1);
    ///     v.unchecked_push(2);
    /// }
    /// assert_eq!(v, &[1, 2]);
    /// ```
    ///
    #[inline]
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
    /// # Examples
    ///
    /// ```
    /// use inplace_containers::InplaceVector;
    ///
    /// let mut v: InplaceVector<i32, 2> = InplaceVector::new();
    /// let r = v.push(10);
    /// assert_eq!(*r, 10);
    /// assert_eq!(v, &[10]);
    /// ```
    ///
    #[inline]
    pub fn push(&mut self, value: T) -> &T {
        match self.push_within_capacity(value) {
            Ok(value) => value,
            Err(_) => panic!("InplaceVector push should not exceed capacity"),
        }
    }

    /// Pushes a new value only if capacity allows it.
    ///
    /// Returns `Ok(&T)` with a reference to the newly added element, or `Err(value)` if full.
    ///
    /// # Examples
    ///
    /// ```
    /// use inplace_containers::InplaceVector;
    ///
    /// let mut v: InplaceVector<i32, 1> = InplaceVector::new();
    /// assert!(v.push_within_capacity(1).is_ok());
    /// assert!(v.push_within_capacity(2).is_err());
    /// assert_eq!(v, &[1]);
    /// ```
    ///
    #[inline]
    pub fn push_within_capacity(&mut self, value: T) -> Result<&T, T> {
        if self.is_full() {
            Err(value)
        } else {
            unsafe { Ok(self.unchecked_push(value)) }
        }
    }

    /// Pushes a new value into the vector without checking that capacity is not exceeded.
    ///
    /// This is a low-level operation that can be used to optimize multiple push calls when
    /// the final size is known by the user to not exceed the total capacity.
    /// Returns a mutable reference to the newly added element.
    ///
    /// # Safety
    ///
    /// - len should be less than capacity.
    /// - undefined behavior otherwise.
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use inplace_containers::InplaceVector;
    ///
    /// let mut v: InplaceVector<i32, 2> = InplaceVector::new();
    /// unsafe {
    ///     v.unchecked_push_mut(1);
    /// }
    /// assert_eq!(v, &[1]);
    /// ```
    ///
    #[inline]
    pub unsafe fn unchecked_push_mut(&mut self, value: T) -> &mut T {
        debug_assert!(!self.is_full());
        let uninit_tail = self.spare_capacity_mut().get_unchecked_mut(0);
        uninit_tail.write(value);
        let new_len = self.len() + 1;
        self.set_len(new_len);
        self.get_unchecked_mut(new_len - 1)
    }

    /// Appends an element to the back of the vector and returns a mutable reference to it.
    ///
    /// # Panics
    ///
    /// Panics if the new size exceeds the vector's capacity (is_full == true).
    ///
    /// # Examples
    ///
    /// ```
    /// use inplace_containers::InplaceVector;
    ///
    /// let mut v: InplaceVector<i32, 2> = InplaceVector::new();
    /// let r = v.push_mut(10);
    /// *r = 7;
    /// assert_eq!(v, &[7]);
    /// ```
    ///
    #[inline]
    pub fn push_mut(&mut self, value: T) -> &mut T {
        match self.push_within_capacity_mut(value) {
            Ok(value) => value,
            Err(_) => panic!("InplaceVector push should not exceed capacity"),
        }
    }

    /// Pushes a new value only if capacity allows it.
    ///
    /// Returns `Ok(&mut T)` with a mutable reference to the newly added element, or `Err(value)` if full.
    ///
    /// # Examples
    ///
    /// ```
    /// use inplace_containers::InplaceVector;
    ///
    /// let mut v: InplaceVector<i32, 1> = InplaceVector::new();
    /// assert!(v.push_within_capacity_mut(1).is_ok());
    /// assert!(v.push_within_capacity_mut(2).is_err());
    /// assert_eq!(v, &[1]);
    /// ```
    ///
    #[inline]
    pub fn push_within_capacity_mut(&mut self, value: T) -> Result<&mut T, T> {
        if self.is_full() {
            Err(value)
        } else {
            unsafe { Ok(self.unchecked_push_mut(value)) }
        }
    }

    /// Tries to clone and append all elements in a slice to the vector.
    ///
    /// Returns a slice to the newly added elements on success.
    ///
    /// Returns `None` if the slice would exceed remaining capacity.
    ///
    /// # Examples
    ///
    /// ```
    /// use inplace_containers::InplaceVector;
    ///
    /// let mut v: InplaceVector<i32, 2> = InplaceVector::new();
    /// assert!(v.try_extend_from_slice(&[1, 2]).is_some());
    /// assert!(v.try_extend_from_slice(&[3]).is_none());
    /// ```
    #[inline]
    pub fn try_extend_from_slice(&mut self, other: &[T]) -> Option<&[T]>
    where
        T: Clone,
    {
        let old_len = self.len();
        if other.len() > self.remaining_capacity() {
            return None;
        }

        for elem in other.iter().cloned() {
            unsafe { self.unchecked_push(elem) };
        }

        Some(unsafe { self.get_unchecked(old_len..self.len()) })
    }

    /// Clones and appends all elements in a slice to the vector.
    ///
    /// Returns a slice to the newly added elements. The other slice is traversed in order.
    ///
    /// # Panics
    ///
    /// Panics if the len of the slice would exceed the vector's remaining_capacity
    ///
    /// # Examples
    ///
    /// ```
    /// use inplace_containers::InplaceVector;
    ///
    /// let mut v: InplaceVector<i32, 4> = InplaceVector::new();
    /// let added = v.extend_from_slice(&[1, 2]);
    /// assert_eq!(added, &[1, 2]);
    /// assert_eq!(v, &[1, 2]);
    /// ```
    ///
    #[inline]
    pub fn extend_from_slice(&mut self, other: &[T]) -> &[T]
    where
        T: Clone,
    {
        if let Some(slice) = self.try_extend_from_slice(other) {
            slice
        } else {
            panic!("InplaceVector extend_from_slice should not exceed capacity");
        }
    }

    /// Tries to clone and append all elements in a slice to the vector.
    ///
    /// Returns a mutable slice to the newly added elements on success.
    ///
    /// Returns `None` if the slice would exceed remaining capacity.
    ///
    /// # Examples
    ///
    /// ```
    /// use inplace_containers::InplaceVector;
    ///
    /// let mut v: InplaceVector<i32, 2> = InplaceVector::new();
    /// assert!(v.try_extend_from_slice_mut(&[1]).is_some());
    /// assert!(v.try_extend_from_slice_mut(&[2, 3]).is_none());
    /// ```
    #[inline]
    pub fn try_extend_from_slice_mut(&mut self, other: &[T]) -> Option<&mut [T]>
    where
        T: Clone,
    {
        let old_len = self.len();
        if other.len() > self.remaining_capacity() {
            return None;
        }

        for elem in other.iter().cloned() {
            unsafe { self.unchecked_push(elem) };
        }

        let new_len = self.len();
        Some(unsafe { self.get_unchecked_mut(old_len..new_len) })
    }

    /// Clones and appends all elements in a slice to the vector.
    ///
    /// Returns a mutable slice to the newly added elements. The other slice is traversed in order.
    ///
    /// # Panics
    ///
    /// Panics if the len of the slice would exceed the vector's remaining_capacity
    ///
    /// # Examples
    ///
    /// ```
    /// use inplace_containers::InplaceVector;
    ///
    /// let mut v: InplaceVector<i32, 4> = InplaceVector::new();
    /// let added = v.extend_from_slice_mut(&[1, 2]);
    /// added[0] = 10;
    /// assert_eq!(v, &[10, 2]);
    /// ```
    ///
    #[inline]
    pub fn extend_from_slice_mut(&mut self, other: &[T]) -> &mut [T]
    where
        T: Clone,
    {
        if let Some(slice) = self.try_extend_from_slice_mut(other) {
            slice
        } else {
            panic!("InplaceVector extend_from_slice should not exceed capacity");
        }
    }

    /// Clones and appends as many elements as possible from a slice.
    ///
    /// Returns `Ok(())` if all elements fit, or `Err(remaining)` with the tail that did not fit.
    ///
    /// This function never panics; it returns the remaining slice when capacity is insufficient.
    ///
    /// # Examples
    ///
    /// ```
    /// use inplace_containers::InplaceVector;
    ///
    /// let mut v: InplaceVector<i32, 2> = InplaceVector::new();
    /// let res = v.extend_from_slice_within_capacity(&[1, 2, 3]);
    /// assert!(res.is_err());
    /// assert_eq!(v, &[1, 2]);
    /// ```
    #[inline]
    pub fn extend_from_slice_within_capacity<'a>(&mut self, other: &'a [T]) -> Result<(), &'a [T]>
    where
        T: Clone,
    {
        let take = self.remaining_capacity().min(other.len());
        let (to_clone, remaining) = other.split_at(take);
        for elem in to_clone.iter().cloned() {
            unsafe { self.unchecked_push(elem) };
        }

        if remaining.is_empty() {
            Ok(())
        } else {
            Err(remaining)
        }
    }

    /// Clones elements from a range within the vector and appends them to the end.
    ///
    /// # Panics
    ///
    /// Panics if the range is out of bounds or would exceed capacity.
    ///
    /// # Examples
    ///
    /// ```
    /// use inplace_containers::InplaceVector;
    ///
    /// let mut v: InplaceVector<i32, 5> = InplaceVector::new();
    /// v.push(1);
    /// v.push(2);
    /// v.push(3);
    /// v.extend_from_within(0..2);
    /// assert_eq!(v, &[1, 2, 3, 1, 2]);
    /// ```
    #[inline]
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

    /// Tries to move all elements from `other` into `self`, leaving `other` empty.
    ///
    /// Returns a mutable slice to the appended elements, or `None` if `other.len()` exceeds
    /// remaining capacity.
    ///
    /// # Examples
    ///
    /// ```
    /// use inplace_containers::InplaceVector;
    ///
    /// let mut a: InplaceVector<i32, 4> = InplaceVector::new();
    /// a.push(1);
    /// let mut b: InplaceVector<i32, 4> = InplaceVector::new();
    /// b.push(2);
    /// assert!(a.try_append(&mut b).is_some());
    /// assert_eq!(a, &[1, 2]);
    /// assert!(b.is_empty());
    /// ```
    #[inline]
    pub fn try_append(&mut self, other: &mut InplaceVector<T, N>) -> Option<&mut [T]> {
        let count = other.len();
        let self_len = self.len();
        if count == 0 {
            return Some(&mut self.as_mut_slice()[self_len..self_len]);
        }
        if count > self.remaining_capacity() {
            return None;
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

        Some(&mut self.as_mut_slice()[self_len..self_len + count])
    }

    /// Moves all elements from `other` into `self`, leaving `other` empty.
    ///
    /// # Panics
    ///
    /// Panics if `other.len()` exceeds remaining capacity.
    ///
    /// # Examples
    ///
    /// ```
    /// use inplace_containers::InplaceVector;
    ///
    /// let mut a: InplaceVector<i32, 4> = InplaceVector::new();
    /// a.push(1);
    /// let mut b: InplaceVector<i32, 4> = InplaceVector::new();
    /// b.push(2);
    /// a.append(&mut b);
    /// assert_eq!(a, &[1, 2]);
    /// assert!(b.is_empty());
    /// ```
    #[inline]
    pub fn append(&mut self, other: &mut InplaceVector<T, N>) {
        if self.try_append(other).is_none() {
            panic!("InplaceVector append should not exceed capacity");
        }
    }

    /// Clones elements from a slice into this vector.
    ///
    /// # Panics
    ///
    /// Panics if the source length does not match `self.len()`.
    ///
    /// # Examples
    ///
    /// ```
    /// use inplace_containers::InplaceVector;
    ///
    /// let mut v: InplaceVector<String, 3> = InplaceVector::new();
    /// v.push("a".to_string());
    /// v.push("b".to_string());
    /// v.push("c".to_string());
    /// v.clone_from_slice(&["x".to_string(), "y".to_string(), "z".to_string()]);
    /// assert_eq!(v, &["x", "y", "z"]);
    /// ```
    #[inline]
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

    /// Copies elements from a slice into this vector.
    ///
    /// # Panics
    ///
    /// Panics if the source length does not match `self.len()`.
    ///
    /// # Examples
    ///
    /// ```
    /// use inplace_containers::InplaceVector;
    ///
    /// let mut v: InplaceVector<u32, 3> = InplaceVector::new();
    /// v.push(1);
    /// v.push(2);
    /// v.push(3);
    /// v.copy_from_slice(&[9, 8, 7]);
    /// assert_eq!(v, &[9, 8, 7]);
    /// ```
    #[inline]
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
    /// # Examples
    ///
    /// ```no_run
    /// use inplace_containers::InplaceVector;
    ///
    /// let mut v: InplaceVector<i32, 2> = InplaceVector::new();
    /// v.push(1);
    /// unsafe {
    ///     assert_eq!(v.unchecked_pop(), 1);
    /// }
    /// assert!(v.is_empty());
    /// ```
    ///
    #[inline]
    pub unsafe fn unchecked_pop(&mut self) -> T {
        debug_assert!(!self.is_empty());
        let index = self.len().unchecked_sub(1);
        let last_uninit = self.data.get_unchecked_mut(index);
        let last = last_uninit.assume_init_read();
        self.set_len(self.len() - 1);
        last
    }

    /// Removes the last element and returns it, or `None` if empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use inplace_containers::InplaceVector;
    ///
    /// let mut v: InplaceVector<i32, 2> = InplaceVector::new();
    /// assert_eq!(v.pop(), None);
    /// v.push(1);
    /// assert_eq!(v.pop(), Some(1));
    /// ```
    #[inline]
    pub fn pop(&mut self) -> Option<T> {
        if self.is_empty() {
            None
        } else {
            Some(unsafe { self.unchecked_pop() })
        }
    }

    /// Removes the last element if the predicate returns `true`.
    ///
    /// # Examples
    ///
    /// ```
    /// use inplace_containers::InplaceVector;
    ///
    /// let mut v: InplaceVector<i32, 2> = InplaceVector::new();
    /// v.push(1);
    /// v.push(2);
    /// assert_eq!(v.pop_if(|x| *x == 2), Some(2));
    /// assert_eq!(v.pop_if(|x| *x == 2), None);
    /// ```
    #[inline]
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

    /// Clears the vector, removing all elements.
    ///
    /// # Examples
    ///
    /// ```
    /// use inplace_containers::InplaceVector;
    ///
    /// let mut v: InplaceVector<i32, 2> = InplaceVector::new();
    /// v.push(1);
    /// v.clear();
    /// assert!(v.is_empty());
    /// ```
    #[inline]
    pub fn clear(&mut self) {
        while self.pop().is_some() {}
    }

    /// Shortens the vector to the specified length.
    ///
    /// If `new_len` is greater than the current length, this has no effect.
    ///
    /// # Examples
    ///
    /// ```
    /// use inplace_containers::InplaceVector;
    ///
    /// let mut v: InplaceVector<i32, 4> = InplaceVector::new();
    /// v.push(1);
    /// v.push(2);
    /// v.push(3);
    /// v.truncate(2);
    /// assert_eq!(v, &[1, 2]);
    /// ```
    #[inline]
    pub fn truncate(&mut self, new_len: usize) {
        if new_len < self.len() {
            while new_len != self.len() {
                unsafe {
                    self.unchecked_pop();
                }
            }
        }
    }

    /// Resizes the vector, filling new entries with values from `f`.
    ///
    /// # Panics
    ///
    /// Panics if `new_len` exceeds capacity.
    ///
    /// # Examples
    ///
    /// ```
    /// use inplace_containers::InplaceVector;
    ///
    /// let mut v: InplaceVector<i32, 4> = InplaceVector::new();
    /// v.push(1);
    /// v.resize_with(3, || 5);
    /// assert_eq!(v, &[1, 5, 5]);
    /// ```
    #[inline]
    pub fn resize_with<F>(&mut self, new_len: usize, f: F)
    where
        F: FnMut() -> T,
    {
        if new_len > self.capacity() {
            panic!("InplaceVector should not be resized above capacity");
        }

        let mut f = f;
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

    /// Resizes the vector, cloning `value` to fill new entries.
    ///
    /// # Panics
    ///
    /// Panics if `new_len` exceeds capacity.
    ///
    /// # Examples
    ///
    /// ```
    /// use inplace_containers::InplaceVector;
    ///
    /// let mut v: InplaceVector<i32, 4> = InplaceVector::new();
    /// v.resize(3, 7);
    /// assert_eq!(v, &[7, 7, 7]);
    /// ```
    #[inline]
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

    /// Tries to insert an element at position `index`, shifting subsequent elements to the right.
    ///
    /// Returns a mutable reference to the inserted element on success, or `None` if the vector is full.
    ///
    /// # Panics
    ///
    /// Panics if `index > len`.
    ///
    /// # Examples
    ///
    /// ```
    /// use inplace_containers::InplaceVector;
    ///
    /// let mut v: InplaceVector<i32, 2> = InplaceVector::new();
    /// v.push(1);
    /// assert!(v.try_insert(1, 2).is_some());
    /// assert!(v.try_insert(0, 3).is_none());
    /// ```
    #[inline]
    pub fn try_insert(&mut self, index: usize, element: T) -> Option<&mut T> {
        let len = self.len();
        if index > len {
            panic!("insertion index (is {index}) should be <= len (is {len})");
        }
        if self.is_full() {
            return None;
        }

        unsafe { self.unchecked_push(element) };

        let slice = &mut self.as_mut_slice()[index..];
        slice.rotate_right(1);

        Some(unsafe { self.get_unchecked_mut(index) })
    }

    /// Inserts an element at position `index`, shifting subsequent elements to the right.
    ///
    /// # Panics
    ///
    /// Panics if `index > len` or if the vector is full.
    ///
    /// # Examples
    ///
    /// ```
    /// use inplace_containers::InplaceVector;
    ///
    /// let mut v: InplaceVector<i32, 4> = InplaceVector::new();
    /// v.push(1);
    /// v.push(3);
    /// v.insert(1, 2);
    /// assert_eq!(v, &[1, 2, 3]);
    /// ```
    #[inline]
    pub fn insert(&mut self, index: usize, element: T) -> &mut T {
        match self.try_insert(index, element) {
            Some(value) => value,
            None => panic!("insert call should not exceed capacity"),
        }
    }

    /// Splits the vector into two at the given index.
    ///
    /// Returns a new vector containing elements in `[at, len)`, and leaves
    /// `self` containing `[0, at)`.
    ///
    /// # Panics
    ///
    /// Panics if `at > len`.
    ///
    /// # Examples
    ///
    /// ```
    /// use inplace_containers::InplaceVector;
    ///
    /// let mut v: InplaceVector<i32, 4> = InplaceVector::new();
    /// v.push(1);
    /// v.push(2);
    /// v.push(3);
    /// let tail = v.split_off(1);
    /// assert_eq!(v, &[1]);
    /// assert_eq!(tail, &[2, 3]);
    /// ```
    #[must_use]
    #[inline]
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

    /// Removes and returns the element at `index`.
    ///
    /// # Panics
    ///
    /// Panics if `index` is out of bounds.
    ///
    /// # Examples
    ///
    /// ```
    /// use inplace_containers::InplaceVector;
    ///
    /// let mut v: InplaceVector<i32, 3> = InplaceVector::new();
    /// v.push(1);
    /// v.push(2);
    /// assert_eq!(v.remove(0), 1);
    /// assert_eq!(v, &[2]);
    /// ```
    #[inline]
    pub fn remove(&mut self, index: usize) -> T {
        let len = self.len();
        if index >= len {
            panic!("removal index (is {index}) should be < len (is {len})");
        }
        unsafe {
            let ret;
            {
                let ptr = self.as_mut_ptr().add(index);
                ret = ptr::read(ptr);
                ptr::copy(ptr.add(1), ptr, len - index - 1);
            }
            self.set_len(len - 1);
            ret
        }
    }

    /// Removes and returns the element at `index` by swapping with the last element.
    ///
    /// This does not preserve ordering.
    ///
    /// # Panics
    ///
    /// Panics if `index` is out of bounds.
    ///
    /// # Examples
    ///
    /// ```
    /// use inplace_containers::InplaceVector;
    ///
    /// let mut v: InplaceVector<i32, 3> = InplaceVector::new();
    /// v.push(1);
    /// v.push(2);
    /// v.push(3);
    /// let removed = v.swap_remove(0);
    /// assert_eq!(removed, 1);
    /// assert_eq!(v.len(), 2);
    /// ```
    #[inline]
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

    /// Removes the specified range and returns it as an iterator.
    ///
    /// The elements are removed even if the iterator is not fully consumed.
    ///
    /// # Panics
    ///
    /// Panics if the range is out of bounds.
    ///
    /// # Examples
    ///
    /// ```
    /// use inplace_containers::InplaceVector;
    ///
    /// let mut v: InplaceVector<i32, 5> = InplaceVector::new();
    /// v.push(1);
    /// v.push(2);
    /// v.push(3);
    /// v.push(4);
    /// let drained: Vec<_> = v.drain(1..3).collect();
    /// assert_eq!(drained, vec![2, 3]);
    /// assert_eq!(v, &[1, 4]);
    /// ```
    #[inline]
    pub fn drain<R>(&mut self, range: R) -> Drain<'_, T, N>
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

        let tail_len = len - end;

        unsafe {
            self.set_len(start);
        }

        Drain {
            vec: self as *mut InplaceVector<T, N>,
            start,
            cur: start,
            end,
            tail_start: end,
            tail_len,
            _marker: PhantomData,
        }
    }

    /// Replaces the specified range with elements from the iterator.
    ///
    /// Returns an iterator over the removed elements.
    ///
    /// # Panics
    ///
    /// Panics if the range is out of bounds or if the new length exceeds capacity.
    ///
    /// # Examples
    ///
    /// ```
    /// use inplace_containers::InplaceVector;
    ///
    /// let mut v: InplaceVector<i32, 4> = InplaceVector::new();
    /// v.push(1);
    /// v.push(2);
    /// v.push(3);
    /// let removed: Vec<_> = v.splice(1..2, [9, 8]).collect();
    /// assert_eq!(removed, vec![2]);
    /// assert_eq!(v, &[1, 9, 8, 3]);
    /// ```
    #[inline]
    pub fn splice<R, I>(&mut self, range: R, replace_with: I) -> Splice<T, N>
    where
        R: RangeBounds<usize>,
        I: IntoIterator<Item = T>,
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

        let removed_len = end - start;

        let mut replacement = InplaceVector::<T, N>::new();
        for item in replace_with {
            if replacement.is_full() {
                panic!("splice would exceed capacity");
            }
            unsafe { replacement.unchecked_push(item) };
        }

        let repl_len = replacement.len();
        let new_len = len - removed_len + repl_len;
        if new_len > N {
            panic!("splice would exceed capacity");
        }

        let mut removed = InplaceVector::<T, N>::new();

        unsafe {
            let base = self.as_mut_ptr();
            for index in start..end {
                removed.unchecked_push(ptr::read(base.add(index)));
            }

            let tail_len = len - end;
            if repl_len != removed_len {
                ptr::copy(base.add(end), base.add(start + repl_len), tail_len);
            }

            for (offset, value) in replacement.into_iter().enumerate() {
                ptr::write(base.add(start + offset), value);
            }

            self.set_len(new_len);
        }

        Splice {
            iter: removed.into_iter(),
        }
    }

    /// Removes consecutive elements that satisfy the given equivalence relation.
    ///
    /// # Examples
    ///
    /// ```
    /// use inplace_containers::InplaceVector;
    ///
    /// let mut v: InplaceVector<i32, 6> = InplaceVector::new();
    /// v.push(1);
    /// v.push(1);
    /// v.push(2);
    /// v.push(2);
    /// v.dedup_by(|a, b| a == b);
    /// assert_eq!(v, &[1, 2]);
    /// ```
    #[inline]
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

    /// Removes consecutive duplicate elements.
    ///
    /// # Examples
    ///
    /// ```
    /// use inplace_containers::InplaceVector;
    ///
    /// let mut v: InplaceVector<i32, 5> = InplaceVector::new();
    /// v.push(1);
    /// v.push(1);
    /// v.push(2);
    /// v.push(2);
    /// v.dedup();
    /// assert_eq!(v, &[1, 2]);
    /// ```
    #[inline]
    pub fn dedup(&mut self)
    where
        T: PartialEq,
    {
        self.dedup_by(|a, b| a == b);
    }

    /// Removes consecutive elements that map to the same key.
    ///
    /// # Examples
    ///
    /// ```
    /// use inplace_containers::InplaceVector;
    ///
    /// let mut v: InplaceVector<i32, 5> = InplaceVector::new();
    /// v.push(1);
    /// v.push(3);
    /// v.push(2);
    /// v.push(4);
    /// v.dedup_by_key(|x| *x % 2);
    /// assert_eq!(v, &[1, 2]);
    /// ```
    #[inline]
    pub fn dedup_by_key<F, K>(&mut self, mut key: F)
    where
        F: FnMut(&mut T) -> K,
        K: PartialEq,
    {
        self.dedup_by(|a, b| key(a) == key(b));
    }

    /// Creates an iterator that removes elements matching a predicate.
    ///
    /// Elements for which the predicate returns `true` are removed and yielded.
    ///
    /// # Examples
    ///
    /// ```
    /// use inplace_containers::InplaceVector;
    ///
    /// let mut v: InplaceVector<i32, 4> = InplaceVector::new();
    /// v.push(1);
    /// v.push(2);
    /// v.push(3);
    /// let removed: Vec<_> = v.extract_if(|x| *x % 2 == 1).collect();
    /// assert_eq!(removed, vec![1, 3]);
    /// assert_eq!(v, &[2]);
    /// ```
    #[inline]
    pub fn extract_if<F>(&mut self, predicate: F) -> ExtractIf<'_, T, N, F>
    where
        F: FnMut(&mut T) -> bool,
    {
        let len = self.len();
        ExtractIf {
            vec: self as *mut InplaceVector<T, N>,
            pred: predicate,
            read: 0,
            write: 0,
            len,
            finished: false,
            _marker: PhantomData,
        }
    }

    /// Retains only the elements specified by the predicate.
    ///
    /// # Examples
    ///
    /// ```
    /// use inplace_containers::InplaceVector;
    ///
    /// let mut v: InplaceVector<i32, 6> = InplaceVector::new();
    /// v.push(1);
    /// v.push(2);
    /// v.push(3);
    /// v.retain(|x| *x % 2 == 1);
    /// assert_eq!(v, &[1, 3]);
    /// ```
    #[inline]
    pub fn retain<F>(&mut self, mut f: F)
    where
        F: FnMut(&T) -> bool,
    {
        self.retain_mut(|elem| f(elem));
    }

    /// Retains only the elements specified by the predicate, allowing mutation.
    ///
    /// # Examples
    ///
    /// ```
    /// use inplace_containers::InplaceVector;
    ///
    /// let mut v: InplaceVector<i32, 4> = InplaceVector::new();
    /// v.push(1);
    /// v.push(2);
    /// v.retain_mut(|x| {
    ///     *x *= 2;
    ///     *x > 2
    /// });
    /// assert_eq!(v, &[4]);
    /// ```
    #[inline]
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
    /// Creates an `InplaceVector` from an iterator.
    ///
    /// # Panics
    ///
    /// Panics if the iterator yields more than `N` elements.
    ///
    /// # Examples
    ///
    /// ```
    /// use inplace_containers::InplaceVector;
    ///
    /// let v: InplaceVector<i32, 3> = [1, 2].into_iter().collect();
    /// assert_eq!(v, &[1, 2]);
    /// ```
    #[inline]
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let mut result = Self::new();
        result.extend(iter);
        result
    }
}

impl<T, const N: usize> Extend<T> for InplaceVector<T, N> {
    /// Extends the vector with the contents of the iterator.
    ///
    /// # Panics
    ///
    /// Panics if the iterator yields more than the remaining capacity.
    ///
    /// # Examples
    ///
    /// ```
    /// use inplace_containers::InplaceVector;
    ///
    /// let mut v: InplaceVector<i32, 3> = InplaceVector::new();
    /// v.extend([1, 2]);
    /// assert_eq!(v, &[1, 2]);
    /// ```
    #[inline]
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

impl<'a, T: Clone, const N: usize> Extend<&'a T> for InplaceVector<T, N> {
    /// Extends the vector by cloning elements from the iterator.
    ///
    /// # Panics
    ///
    /// Panics if the iterator yields more than the remaining capacity.
    ///
    /// # Examples
    ///
    /// ```
    /// use inplace_containers::InplaceVector;
    ///
    /// let src = [1, 2];
    /// let mut v: InplaceVector<i32, 3> = InplaceVector::new();
    /// v.extend(src.iter());
    /// assert_eq!(v, &[1, 2]);
    /// ```
    #[inline]
    fn extend<I: IntoIterator<Item = &'a T>>(&mut self, iter: I) {
        let it = iter.into_iter();
        match it.size_hint() {
            (lowerbound, _) if lowerbound > self.remaining_capacity() => {
                panic!("Can't extend {lowerbound} elements into InplaceVector<_, {N}>")
            }

            (_, Some(upperbound)) if upperbound <= self.remaining_capacity() => {
                for elem in it {
                    unsafe { self.unchecked_push(elem.clone()) };
                }
            }
            _ => {
                for elem in it {
                    self.push(elem.clone());
                }
            }
        };
    }
}

impl<const N: usize> std::io::Write for InplaceVector<u8, N> {
    /// Writes bytes into the vector, returning how many were written.
    ///
    /// This writes up to the remaining capacity.
    ///
    /// # Examples
    ///
    /// ```
    /// use inplace_containers::InplaceVector;
    /// use std::io::Write;
    ///
    /// let mut v: InplaceVector<u8, 3> = InplaceVector::new();
    /// let written = v.write(&[1, 2, 3, 4]).unwrap();
    /// assert_eq!(written, 3);
    /// assert_eq!(v, &[1, 2, 3]);
    /// ```
    #[inline]
    fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
        let old_len = self.len();
        let min = self.remaining_capacity().min(buf.len());
        unsafe {
            std::ptr::copy_nonoverlapping(buf.as_ptr(), self.as_mut_ptr().add(old_len), min);
            self.set_len(old_len + min);
        }

        Ok(min)
    }

    /// This type does not buffer, so `flush` is a no-op.
    ///
    /// # Examples
    ///
    /// ```
    /// use inplace_containers::InplaceVector;
    /// use std::io::Write;
    ///
    /// let mut v: InplaceVector<u8, 2> = InplaceVector::new();
    /// v.write(&[1, 2]).unwrap();
    /// v.flush().unwrap();
    /// ```
    #[inline]
    fn flush(&mut self) -> std::io::Result<()> {
        Ok(())
    }
}

impl<T, const N: usize> Drop for InplaceVector<T, N> {
    #[inline]
    fn drop(&mut self) {
        self.clear();
    }
}

impl<T, const N: usize> IntoIterator for InplaceVector<T, N> {
    type Item = T;

    type IntoIter = IntoIter<T, N>;

    /// Creates an iterator that consumes the vector.
    ///
    /// # Examples
    ///
    /// ```
    /// use inplace_containers::InplaceVector;
    ///
    /// let mut v: InplaceVector<i32, 2> = InplaceVector::new();
    /// v.push(1);
    /// v.push(2);
    /// let mut iter = v.into_iter();
    /// assert_eq!(iter.next(), Some(1));
    /// assert_eq!(iter.next(), Some(2));
    /// assert_eq!(iter.next(), None);
    /// ```
    #[inline]
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

    /// Creates an iterator over shared references.
    ///
    /// # Examples
    ///
    /// ```
    /// use inplace_containers::InplaceVector;
    ///
    /// let mut v: InplaceVector<i32, 2> = InplaceVector::new();
    /// v.push(1);
    /// v.push(2);
    /// let mut iter = (&v).into_iter();
    /// assert_eq!(iter.next(), Some(&1));
    /// ```
    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.as_slice().iter()
    }
}

impl<'a, T, const N: usize> IntoIterator for &'a mut InplaceVector<T, N> {
    type Item = &'a mut T;

    type IntoIter = std::slice::IterMut<'a, T>;

    /// Creates an iterator over mutable references.
    ///
    /// # Examples
    ///
    /// ```
    /// use inplace_containers::InplaceVector;
    ///
    /// let mut v: InplaceVector<i32, 2> = InplaceVector::new();
    /// v.push(1);
    /// v.push(2);
    /// for x in &mut v {
    ///     *x *= 2;
    /// }
    /// assert_eq!(v, &[2, 4]);
    /// ```
    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.as_mut_slice().iter_mut()
    }
}

impl<T: Clone, const N: usize> Clone for InplaceVector<T, N> {
    /// Clones the vector and its elements.
    ///
    /// # Examples
    ///
    /// ```
    /// use inplace_containers::InplaceVector;
    ///
    /// let mut v: InplaceVector<i32, 2> = InplaceVector::new();
    /// v.push(1);
    /// let c = v.clone();
    /// assert_eq!(c, &[1]);
    /// ```
    #[inline]
    fn clone(&self) -> Self {
        let mut result = Self::new();

        for value in self.as_slice() {
            unsafe { result.unchecked_push(value.clone()) };
        }

        result
    }
}

impl<T: Clone, const N: usize> Default for InplaceVector<T, N> {
    /// Creates an empty vector.
    ///
    /// # Examples
    ///
    /// ```
    /// use inplace_containers::InplaceVector;
    ///
    /// let v: InplaceVector<i32, 2> = InplaceVector::default();
    /// assert!(v.is_empty());
    /// ```
    #[inline]
    fn default() -> Self {
        Self::new()
    }
}

impl<T, const N: usize> Deref for InplaceVector<T, N> {
    type Target = [T];

    /// Dereferences to a slice of elements.
    ///
    /// # Examples
    ///
    /// ```
    /// use inplace_containers::InplaceVector;
    ///
    /// let mut v: InplaceVector<i32, 2> = InplaceVector::new();
    /// v.push(1);
    /// assert_eq!(&*v, &[1]);
    /// ```
    #[inline]
    fn deref(&self) -> &Self::Target {
        self.as_slice()
    }
}

impl<T, const N: usize> DerefMut for InplaceVector<T, N> {
    /// Mutably dereferences to a slice of elements.
    ///
    /// # Examples
    ///
    /// ```
    /// use inplace_containers::InplaceVector;
    ///
    /// let mut v: InplaceVector<i32, 2> = InplaceVector::new();
    /// v.push(1);
    /// v[0] = 5;
    /// assert_eq!(v, &[5]);
    /// ```
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.as_mut_slice()
    }
}

impl<T, I, const N: usize> Index<I> for InplaceVector<T, N>
where
    I: SliceIndex<[T]>,
{
    type Output = <I as SliceIndex<[T]>>::Output;

    /// Indexes into the vector.
    ///
    /// # Examples
    ///
    /// ```
    /// use inplace_containers::InplaceVector;
    ///
    /// let mut v: InplaceVector<i32, 3> = InplaceVector::new();
    /// v.push(1);
    /// v.push(2);
    /// assert_eq!(v[1], 2);
    /// ```
    #[inline]
    fn index(&self, index: I) -> &Self::Output {
        Index::index(self.as_slice(), index)
    }
}

impl<T, I, const N: usize> IndexMut<I> for InplaceVector<T, N>
where
    I: SliceIndex<[T]>,
{
    /// Mutably indexes into the vector.
    ///
    /// # Examples
    ///
    /// ```
    /// use inplace_containers::InplaceVector;
    ///
    /// let mut v: InplaceVector<i32, 3> = InplaceVector::new();
    /// v.push(1);
    /// v.push(2);
    /// v[0] = 10;
    /// assert_eq!(v, &[10, 2]);
    /// ```
    #[inline]
    fn index_mut(&mut self, index: I) -> &mut <InplaceVector<T, N> as Index<I>>::Output {
        IndexMut::index_mut(self.as_mut_slice(), index)
    }
}

impl<T, const N: usize> PartialEq for InplaceVector<T, N>
where
    T: PartialEq,
{
    /// Checks equality with another `InplaceVector`.
    ///
    /// # Examples
    ///
    /// ```
    /// use inplace_containers::InplaceVector;
    ///
    /// let mut a: InplaceVector<i32, 2> = InplaceVector::new();
    /// a.push(1);
    /// let mut b: InplaceVector<i32, 2> = InplaceVector::new();
    /// b.push(1);
    /// assert_eq!(a, b);
    /// ```
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.as_slice() == other.as_slice()
    }
}

impl<T, U, const N: usize, const M: usize> PartialEq<&[U; M]> for InplaceVector<T, N>
where
    T: PartialEq<U>,
{
    /// Checks equality with a reference to an array.
    ///
    /// # Examples
    ///
    /// ```
    /// use inplace_containers::InplaceVector;
    ///
    /// let mut v: InplaceVector<i32, 3> = InplaceVector::new();
    /// v.push(1);
    /// v.push(2);
    /// assert_eq!(v, &[1, 2]);
    /// ```
    #[inline]
    fn eq(&self, other: &&[U; M]) -> bool {
        self.as_slice().eq(*other)
    }
}

impl<T, U, const N: usize, const M: usize> PartialEq<&mut [U; M]> for InplaceVector<T, N>
where
    T: PartialEq<U>,
{
    /// Checks equality with a mutable array reference.
    ///
    /// # Examples
    ///
    /// ```
    /// use inplace_containers::InplaceVector;
    ///
    /// let mut arr = [1, 2];
    /// let mut v: InplaceVector<i32, 3> = InplaceVector::new();
    /// v.push(1);
    /// v.push(2);
    /// assert_eq!(v, &mut arr);
    /// ```
    #[inline]
    fn eq(&self, other: &&mut [U; M]) -> bool {
        self.as_slice().eq(*other)
    }
}

impl<T, U, const N: usize> PartialEq<&[U]> for InplaceVector<T, N>
where
    T: PartialEq<U>,
{
    /// Checks equality with a slice reference.
    ///
    /// # Examples
    ///
    /// ```
    /// use inplace_containers::InplaceVector;
    ///
    /// let mut v: InplaceVector<i32, 3> = InplaceVector::new();
    /// v.push(1);
    /// v.push(2);
    /// let slice: &[i32] = &[1, 2];
    /// assert_eq!(v, slice);
    /// ```
    #[inline]
    fn eq(&self, other: &&[U]) -> bool {
        self.as_slice().eq(*other)
    }
}

impl<T, U, const N: usize> PartialEq<&mut [U]> for InplaceVector<T, N>
where
    T: PartialEq<U>,
{
    /// Checks equality with a mutable slice reference.
    ///
    /// # Examples
    ///
    /// ```
    /// use inplace_containers::InplaceVector;
    ///
    /// let mut slice = [1, 2];
    /// let mut v: InplaceVector<i32, 3> = InplaceVector::new();
    /// v.push(1);
    /// v.push(2);
    /// assert_eq!(v, &mut slice[..]);
    /// ```
    #[inline]
    fn eq(&self, other: &&mut [U]) -> bool {
        self.as_slice().eq(*other)
    }
}

impl<T, const N: usize> Eq for InplaceVector<T, N> where T: Eq {}

impl<T, const N: usize> PartialOrd for InplaceVector<T, N>
where
    T: PartialOrd,
{
    /// Compares two vectors lexicographically.
    ///
    /// # Examples
    ///
    /// ```
    /// use inplace_containers::InplaceVector;
    ///
    /// let mut a: InplaceVector<i32, 2> = InplaceVector::new();
    /// a.push(1);
    /// let mut b: InplaceVector<i32, 2> = InplaceVector::new();
    /// b.push(2);
    /// assert!(a < b);
    /// ```
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        self.as_slice().partial_cmp(other.as_slice())
    }
}

impl<T, const N: usize> Ord for InplaceVector<T, N>
where
    T: Ord,
{
    /// Compares two vectors lexicographically.
    ///
    /// # Examples
    ///
    /// ```
    /// use inplace_containers::InplaceVector;
    ///
    /// let mut a: InplaceVector<i32, 2> = InplaceVector::new();
    /// a.push(1);
    /// let mut b: InplaceVector<i32, 2> = InplaceVector::new();
    /// b.push(2);
    /// assert!(a.cmp(&b).is_lt());
    /// ```
    #[inline]
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.as_slice().cmp(other.as_slice())
    }
}

impl<T, const N: usize> Hash for InplaceVector<T, N>
where
    T: Hash,
{
    /// Hashes the contents of the vector.
    ///
    /// # Examples
    ///
    /// ```
    /// use inplace_containers::InplaceVector;
    /// use std::collections::hash_map::DefaultHasher;
    /// use std::hash::{Hash, Hasher};
    ///
    /// let mut v: InplaceVector<i32, 2> = InplaceVector::new();
    /// v.push(1);
    /// let mut hasher = DefaultHasher::new();
    /// v.hash(&mut hasher);
    /// ```
    #[inline]
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.as_slice().hash(state);
    }
}

impl<T: fmt::Debug, const N: usize> Debug for InplaceVector<T, N> {
    /// Formats the vector using the debug formatter.
    ///
    /// # Examples
    ///
    /// ```
    /// use inplace_containers::InplaceVector;
    ///
    /// let mut v: InplaceVector<i32, 2> = InplaceVector::new();
    /// v.push(1);
    /// assert_eq!(format!("{:?}", v), "[1]");
    /// ```
    #[inline]
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        fmt::Debug::fmt(&**self, f)
    }
}

impl<T, const N: usize> AsMut<InplaceVector<T, N>> for InplaceVector<T, N> {
    /// Converts to a mutable reference to `self`.
    ///
    /// # Examples
    ///
    /// ```
    /// use inplace_containers::InplaceVector;
    ///
    /// let mut v: InplaceVector<i32, 2> = InplaceVector::new();
    /// let r: &mut InplaceVector<i32, 2> = v.as_mut();
    /// r.push(1);
    /// assert_eq!(v, &[1]);
    /// ```
    #[inline]
    fn as_mut(&mut self) -> &mut InplaceVector<T, N> {
        self
    }
}

impl<T, const N: usize> AsRef<[T]> for InplaceVector<T, N> {
    /// Converts to a shared slice.
    ///
    /// # Examples
    ///
    /// ```
    /// use inplace_containers::InplaceVector;
    ///
    /// let mut v: InplaceVector<i32, 2> = InplaceVector::new();
    /// v.push(1);
    /// let s: &[i32] = v.as_ref();
    /// assert_eq!(s, &[1]);
    /// ```
    #[inline]
    fn as_ref(&self) -> &[T] {
        self
    }
}

impl<T, const N: usize> AsMut<[T]> for InplaceVector<T, N> {
    /// Converts to a mutable slice.
    ///
    /// # Examples
    ///
    /// ```
    /// use inplace_containers::InplaceVector;
    ///
    /// let mut v: InplaceVector<i32, 2> = InplaceVector::new();
    /// v.push(1);
    /// let s: &mut [i32] = v.as_mut();
    /// s[0] = 3;
    /// assert_eq!(v, &[3]);
    /// ```
    #[inline]
    fn as_mut(&mut self) -> &mut [T] {
        self
    }
}

impl<T, const N: usize> std::borrow::Borrow<[T]> for InplaceVector<T, N> {
    /// Borrows as a slice.
    ///
    /// # Examples
    ///
    /// ```
    /// use inplace_containers::InplaceVector;
    /// use std::borrow::Borrow;
    ///
    /// let mut v: InplaceVector<i32, 2> = InplaceVector::new();
    /// v.push(1);
    /// let s: &[i32] = v.borrow();
    /// assert_eq!(s, &[1]);
    /// ```
    #[inline]
    fn borrow(&self) -> &[T] {
        self
    }
}

impl<T, const N: usize> std::borrow::BorrowMut<[T]> for InplaceVector<T, N> {
    /// Mutably borrows as a slice.
    ///
    /// # Examples
    ///
    /// ```
    /// use inplace_containers::InplaceVector;
    /// use std::borrow::BorrowMut;
    ///
    /// let mut v: InplaceVector<i32, 2> = InplaceVector::new();
    /// v.push(1);
    /// let s: &mut [i32] = v.borrow_mut();
    /// s[0] = 3;
    /// assert_eq!(v, &[3]);
    /// ```
    #[inline]
    fn borrow_mut(&mut self) -> &mut [T] {
        self
    }
}

impl<T, const N: usize> From<[T; N]> for InplaceVector<T, N> {
    /// Converts an array into an `InplaceVector`.
    ///
    /// # Examples
    ///
    /// ```
    /// use inplace_containers::InplaceVector;
    ///
    /// let v: InplaceVector<i32, 3> = InplaceVector::from([1, 2, 3]);
    /// assert_eq!(v, &[1, 2, 3]);
    /// ```
    #[inline]
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

    /// Attempts to clone a slice into an `InplaceVector`.
    ///
    /// Returns `Err(slice)` if the slice length exceeds capacity.
    ///
    /// # Examples
    ///
    /// ```
    /// use inplace_containers::InplaceVector;
    ///
    /// let slice = [1, 2];
    /// let v: InplaceVector<i32, 3> = InplaceVector::try_from(&slice[..]).unwrap();
    /// assert_eq!(v, &[1, 2]);
    /// ```
    #[inline]
    fn try_from(slice: &'a [T]) -> Result<Self, Self::Error> {
        let count = slice.len();
        if count > N {
            return Err(slice);
        }

        let mut result = InplaceVector::new();

        for elem in slice {
            unsafe { result.unchecked_push(elem.clone()) };
        }

        Ok(result)
    }
}

impl<T, const N: usize> TryFrom<InplaceVector<T, N>> for [T; N] {
    type Error = InplaceVector<T, N>;

    /// Attempts to convert an `InplaceVector` into an array.
    ///
    /// Returns `Err(vec)` if the vector is not full.
    ///
    /// # Examples
    ///
    /// ```
    /// use inplace_containers::InplaceVector;
    ///
    /// let mut v: InplaceVector<i32, 2> = InplaceVector::new();
    /// v.push(1);
    /// v.push(2);
    /// let arr: [i32; 2] = <[i32; 2]>::try_from(v).unwrap();
    /// assert_eq!(arr, [1, 2]);
    /// ```
    #[inline]
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

impl<T: Clone, const N: usize> TryFrom<&InplaceVector<T, N>> for [T; N] {
    type Error = InplaceVectorError;

    /// Attempts to clone an `InplaceVector` into an array.
    ///
    /// # Errors
    ///
    /// Returns `Err` if the vector is not full.
    ///
    /// # Examples
    ///
    /// ```
    /// use inplace_containers::InplaceVector;
    ///
    /// let mut v: InplaceVector<i32, 2> = InplaceVector::new();
    /// v.push(1);
    /// v.push(2);
    /// let arr: [i32; 2] = <[i32; 2]>::try_from(&v).unwrap();
    /// assert_eq!(arr, [1, 2]);
    /// ```
    #[inline]
    fn try_from(vec: &InplaceVector<T, N>) -> Result<[T; N], InplaceVectorError> {
        if vec.len() != N {
            return Err(InplaceVectorError::LengthMismatch {
                expected_len: N,
                actual_len: vec.len(),
            });
        }

        let slice = vec.as_slice();
        Ok(std::array::from_fn(|i| slice[i].clone()))
    }
}

pub struct IntoIter<T, const N: usize> {
    data: [MaybeUninit<T>; N],
    begin: usize,
    end: usize,
}

/// Iterator returned by `InplaceVector::drain`.
pub struct Drain<'a, T, const N: usize> {
    vec: *mut InplaceVector<T, N>,
    start: usize,
    cur: usize,
    end: usize,
    tail_start: usize,
    tail_len: usize,
    _marker: PhantomData<&'a mut InplaceVector<T, N>>,
}

/// Iterator returned by `InplaceVector::extract_if`.
pub struct ExtractIf<'a, T, const N: usize, F>
where
    F: FnMut(&mut T) -> bool,
{
    vec: *mut InplaceVector<T, N>,
    pred: F,
    read: usize,
    write: usize,
    len: usize,
    finished: bool,
    _marker: PhantomData<&'a mut InplaceVector<T, N>>,
}

/// Iterator returned by `InplaceVector::splice`.
pub struct Splice<T, const N: usize> {
    iter: IntoIter<T, N>,
}

impl<'a, T, const N: usize> Drain<'a, T, N> {
    #[inline]
    fn as_ptr(&self) -> *const T {
        unsafe { (*self.vec).as_ptr() }
    }

    #[inline]
    fn as_mut_ptr(&mut self) -> *mut T {
        unsafe { (*self.vec).as_mut_ptr() }
    }

    #[inline]
    fn len(&self) -> usize {
        self.end - self.cur
    }
}

impl<'a, T, const N: usize> Iterator for Drain<'a, T, N> {
    type Item = T;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if self.len() == 0 {
            None
        } else {
            let index = self.cur;
            self.cur += 1;
            unsafe { Some(ptr::read(self.as_ptr().add(index))) }
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = self.len();
        (len, Some(len))
    }
}

impl<'a, T, const N: usize> DoubleEndedIterator for Drain<'a, T, N> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.len() == 0 {
            None
        } else {
            self.end -= 1;
            unsafe { Some(ptr::read(self.as_ptr().add(self.end))) }
        }
    }
}

impl<'a, T, const N: usize> ExactSizeIterator for Drain<'a, T, N> {}

impl<'a, T, const N: usize> FusedIterator for Drain<'a, T, N> {}

impl<'a, T, const N: usize> Drop for Drain<'a, T, N> {
    #[inline]
    fn drop(&mut self) {
        unsafe {
            for index in self.cur..self.end {
                ptr::drop_in_place(self.as_mut_ptr().add(index));
            }

            if self.tail_len > 0 {
                let base = self.as_mut_ptr();
                if self.start != self.tail_start {
                    ptr::copy(
                        base.add(self.tail_start),
                        base.add(self.start),
                        self.tail_len,
                    );
                }
            }

            let vec = &mut *self.vec;
            vec.set_len(self.start + self.tail_len);
        }
    }
}

impl<'a, T, const N: usize, F> ExtractIf<'a, T, N, F>
where
    F: FnMut(&mut T) -> bool,
{
    #[inline]
    fn finish(&mut self) {
        if self.finished {
            return;
        }
        unsafe {
            let vec = &mut *self.vec;
            vec.set_len(self.write);
        }
        self.finished = true;
    }
}

impl<'a, T, const N: usize, F> Iterator for ExtractIf<'a, T, N, F>
where
    F: FnMut(&mut T) -> bool,
{
    type Item = T;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        unsafe {
            let base = (*self.vec).as_mut_ptr();
            while self.read < self.len {
                let index = self.read;
                self.read += 1;
                let elem = base.add(index);
                if (self.pred)(&mut *elem) {
                    return Some(ptr::read(elem));
                }
                if self.write != index {
                    ptr::copy(elem, base.add(self.write), 1);
                }
                self.write += 1;
            }
            self.finish();
            None
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        (0, Some(self.len.saturating_sub(self.read)))
    }
}

impl<'a, T, const N: usize, F> FusedIterator for ExtractIf<'a, T, N, F> where
    F: FnMut(&mut T) -> bool
{
}

impl<'a, T, const N: usize, F> Drop for ExtractIf<'a, T, N, F>
where
    F: FnMut(&mut T) -> bool,
{
    #[inline]
    fn drop(&mut self) {
        if self.finished {
            return;
        }
        unsafe {
            let base = (*self.vec).as_mut_ptr();
            while self.read < self.len {
                let index = self.read;
                self.read += 1;
                let elem = base.add(index);
                if (self.pred)(&mut *elem) {
                    ptr::drop_in_place(elem);
                } else {
                    if self.write != index {
                        ptr::copy(elem, base.add(self.write), 1);
                    }
                    self.write += 1;
                }
            }
        }
        self.finish();
    }
}

impl<T, const N: usize> Iterator for Splice<T, N> {
    type Item = T;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next()
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

impl<T, const N: usize> DoubleEndedIterator for Splice<T, N> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        self.iter.next_back()
    }
}

impl<T, const N: usize> ExactSizeIterator for Splice<T, N> {}

impl<T, const N: usize> FusedIterator for Splice<T, N> {}

impl<T, const N: usize> IntoIter<T, N> {
    #[inline]
    fn as_ptr(&self) -> *const T {
        unsafe { (self.data.as_ptr() as *const T).add(self.begin) }
    }

    #[inline]
    fn as_mut_ptr(&mut self) -> *mut T {
        unsafe { (self.data.as_mut_ptr() as *mut T).add(self.begin) }
    }

    #[inline]
    const fn len(&self) -> usize {
        self.end - self.begin
    }

    #[inline]
    const fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Returns a slice of the remaining iterator elements.
    ///
    /// # Examples
    ///
    /// ```
    /// use inplace_containers::InplaceVector;
    ///
    /// let mut v: InplaceVector<i32, 3> = InplaceVector::new();
    /// v.push(1);
    /// v.push(2);
    /// let iter = v.into_iter();
    /// assert_eq!(iter.as_slice(), &[1, 2]);
    /// ```
    #[inline]
    pub fn as_slice(&self) -> &[T] {
        let ptr = self.as_ptr();
        unsafe { std::slice::from_raw_parts(ptr, self.len()) }
    }

    /// Returns a mutable slice of the remaining iterator elements.
    ///
    /// # Examples
    ///
    /// ```
    /// use inplace_containers::InplaceVector;
    ///
    /// let mut v: InplaceVector<i32, 3> = InplaceVector::new();
    /// v.push(1);
    /// v.push(2);
    /// let mut iter = v.into_iter();
    /// assert_eq!(iter.as_slice(), &[1, 2]);
    /// let slice = iter.as_mut_slice();
    /// slice[0] = 5;
    /// assert_eq!(iter.as_slice(), &[5, 2]);
    /// ```
    #[inline]
    pub fn as_mut_slice(&mut self) -> &mut [T] {
        let ptr = self.as_mut_ptr();
        unsafe { std::slice::from_raw_parts_mut(ptr, self.len()) }
    }

    #[inline]
    unsafe fn unchecked_next(&mut self) -> T {
        let next_uninit = self.data.get_unchecked(self.begin);
        self.begin += 1;
        next_uninit.assume_init_read()
    }

    #[inline]
    unsafe fn unchecked_back(&mut self) -> T {
        let back_uninit = self.data.get_unchecked(self.end - 1);
        self.end -= 1;
        back_uninit.assume_init_read()
    }

    #[inline]
    unsafe fn unchecked_push(&mut self, value: T) {
        let back_uninit = self.data.get_unchecked_mut(self.end);
        self.end += 1;
        back_uninit.write(value);
    }
}

impl<T, const N: usize> Iterator for IntoIter<T, N> {
    type Item = T;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if self.is_empty() {
            None
        } else {
            Some(unsafe { self.unchecked_next() })
        }
    }
}

impl<T, const N: usize> DoubleEndedIterator for IntoIter<T, N> {
    #[inline]
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
    #[inline]
    fn drop(&mut self) {
        while self.next_back().is_some() {}
    }
}

impl<T, const N: usize> Default for IntoIter<T, N> {
    #[inline]
    fn default() -> Self {
        Self {
            data: [const { MaybeUninit::uninit() }; N],
            begin: 0,
            end: 0,
        }
    }
}

impl<T: Clone, const N: usize> Clone for IntoIter<T, N> {
    #[inline]
    fn clone(&self) -> Self {
        let mut result = Self::default();
        for value in self.as_slice().iter().cloned() {
            unsafe {
                result.unchecked_push(value);
            }
        }
        result
    }
}

impl<T, const N: usize> AsRef<[T]> for IntoIter<T, N> {
    #[inline]
    fn as_ref(&self) -> &[T] {
        self.as_slice()
    }
}

#[cfg(test)]
mod tests {
    use crate::inplace_vec;
    use core::cell::Cell;
    use std::borrow::{Borrow, BorrowMut};
    use std::cmp::Ordering;
    use std::sync::atomic::{AtomicUsize, Ordering as AtomicOrdering};

    use super::*;

    #[test]
    #[inline]
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
    #[inline]
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
    #[inline]
    fn basic_push_pop_and_len_capacity() {
        let mut v = inplace_vec![4;];
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
    #[inline]
    fn push_panics_when_full() {
        let mut v = inplace_vec![2;];
        v.push(10);
        v.push(20);
        v.push(30);
    }

    #[test]
    #[inline]
    fn push_within_capacity_behavior() {
        let mut v = inplace_vec![2;];
        assert!(v.push_within_capacity(5).is_ok());
        assert!(v.push_within_capacity(6).is_ok());
        assert!(v.push_within_capacity(7).is_err());
        assert_eq!(v, &[5, 6]);
    }

    #[test]
    #[inline]
    fn push_mut_returns_last_element() {
        let mut v = inplace_vec![2;];
        let r = v.push_mut(1);
        *r = 5;
        assert_eq!(v, &[5]);

        let r2 = v.push_mut(2);
        *r2 = 7;
        assert_eq!(v, &[5, 7]);
    }

    #[test]
    #[inline]
    fn as_slice_and_mut_slice_and_index() {
        let mut v = inplace_vec![4;];
        v.push(7);
        v.push(8);
        assert_eq!(v, &[7, 8]);
        v.as_mut_slice()[1] = 42;
        assert_eq!(v[1], 42);
    }

    #[test]
    #[inline]
    fn iter_and_iter_mut() {
        let mut v = inplace_vec![4;];
        v.push(0);
        v.push(1);
        v.push(2);

        let collected: Vec<_> = v.iter().copied().collect();
        assert_eq!(collected, vec![0, 1, 2]);

        for x in v.iter_mut() {
            *x += 10;
        }
        assert_eq!(v, &[10, 11, 12]);
    }

    #[test]
    #[inline]
    fn append_moves_and_empties_other() {
        let mut a = inplace_vec![6;];
        a.push("1".to_string());
        a.push("2".to_string());

        let mut b = inplace_vec![6;];
        b.push("3".to_string());
        b.push("4".to_string());
        b.push("5".to_string());

        a.append(&mut b);
        assert_eq!(a, &["1", "2", "3", "4", "5"]);
        assert_eq!(b.len(), 0);
    }

    #[test]
    #[inline]
    fn split_off_edges_and_middle() {
        let mut v = inplace_vec![8;];
        for i in 0..6 {
            v.push(i);
        }

        let o1 = v.split_off(2);
        assert_eq!(v, &[0, 1]);
        assert_eq!(o1, &[2, 3, 4, 5]);

        let mut v2 = inplace_vec![4;];
        for i in 0..4 {
            v2.push(i);
        }
        let o2 = v2.split_off(0);
        assert_eq!(v2, &[]);
        assert_eq!(o2, &[0, 1, 2, 3]);

        let mut v3 = inplace_vec![4;];
        for i in 0..3 {
            v3.push(i);
        }
        let o3 = v3.split_off(3);
        assert_eq!(v3, &[0, 1, 2]);
        assert_eq!(o3, &[]);
    }

    #[test]
    #[inline]
    fn insert_remove_swap_remove() {
        let mut v = inplace_vec![6;];
        v.push(1);
        v.push(3);
        v.push(4);

        v.insert(1, 2);
        assert_eq!(v, &[1, 2, 3, 4]);

        let removed = v.remove(2);
        assert_eq!(removed, 3);
        assert_eq!(v, &[1, 2, 4]);

        v.push(9);
        let swapped = v.swap_remove(1);
        assert_eq!(swapped, 2);
        assert_eq!(v.len(), 3);
        assert_eq!(v[1], 9);
    }

    #[test]
    #[inline]
    fn insert_and_extract_if() {
        let mut v = inplace_vec![4;];
        v.push(1);
        v.insert(1, 2);

        let removed: Vec<_> = v.extract_if(|x| *x % 2 == 0).collect();
        assert_eq!(removed, vec![2]);
        assert_eq!(v, &[1]);
    }

    #[test]
    #[inline]
    fn try_insert_when_full_returns_none() {
        let mut v = inplace_vec![1;];
        v.push(1);
        assert!(v.try_insert(0, 2).is_none());
        assert_eq!(v, &[1]);
    }

    #[test]
    #[inline]
    fn try_capacity_error_paths() {
        let mut v = inplace_vec![3;];
        v.push(1);
        v.push(2);

        assert!(v.try_extend_from_slice(&[3, 4]).is_none());
        assert!(v.try_extend_from_slice_mut(&[3, 4]).is_none());

        assert_eq!(v, &[1, 2]);
    }

    #[test]
    #[inline]
    fn try_extend_and_append_success() {
        let mut v = inplace_vec![4;];
        let added = v
            .try_extend_from_slice(&[1, 2])
            .expect("extend should succeed");
        assert_eq!(added, &[1, 2]);

        let added_mut = v
            .try_extend_from_slice_mut(&[3])
            .expect("extend mut should succeed");
        added_mut[0] = 4;
        assert_eq!(v, &[1, 2, 4]);

        let mut a = inplace_vec![4;];
        a.push(10);
        let mut b = inplace_vec![4;];
        b.push(20);
        b.push(30);
        assert!(a.try_append(&mut b).is_some());
        assert_eq!(a, &[10, 20, 30]);
        assert!(b.is_empty());
    }

    #[test]
    #[inline]
    fn try_append_errors() {
        let mut a = inplace_vec![2;];
        a.push(1);

        let mut b = inplace_vec![2;];
        b.push(2);
        b.push(3);

        assert!(a.try_append(&mut b).is_none());
        assert_eq!(a, &[1]);
        assert_eq!(b, &[2, 3]);
    }

    #[test]
    #[inline]
    fn splice_replaces_range() {
        let mut v = inplace_vec![5;];
        v.push(1);
        v.push(2);
        v.push(3);
        v.push(4);

        let removed: Vec<_> = v.splice(1..3, [9, 8]).collect();
        assert_eq!(removed, vec![2, 3]);
        assert_eq!(v, &[1, 9, 8, 4]);
    }

    #[test]
    #[inline]
    fn retain_and_retain_mut() {
        let mut v = inplace_vec![8;];
        for i in 0..8 {
            v.push(i);
        }
        v.retain(|&x| x % 2 == 0);
        assert_eq!(v, &[0, 2, 4, 6]);

        let mut v2 = inplace_vec![8;];
        for i in 0..8 {
            v2.push(i);
        }
        v2.retain_mut(|x| {
            *x += 1;
            (*x) % 2 == 0
        });
        assert_eq!(v2, &[2, 4, 6, 8], "sanity");
        assert_eq!(v2.len(), 4);
    }

    #[test]
    #[inline]
    fn clone_from_slice_and_copy_from_slice() {
        let mut v = inplace_vec![3;];
        v.push("a".to_string());
        v.push("b".to_string());
        v.push("c".to_string());

        let src = ["x".to_string(), "y".to_string(), "z".to_string()];
        v.clone_from_slice(&src);
        assert_eq!(v, &["x".to_string(), "y".to_string(), "z".to_string()]);

        let mut c = inplace_vec![3;];
        c.push(1);
        c.push(2);
        c.push(3);

        let src2 = [9u32, 8u32, 7u32];
        c.copy_from_slice(&src2);
        assert_eq!(c, &[9, 8, 7]);
    }

    #[test]
    #[inline]
    fn from_array_and_try_from_slice() {
        let arr = [1u8, 2u8, 3u8, 4u8];
        let v: InplaceVector<u8, 4> = InplaceVector::from(arr);
        assert_eq!(v, &[1, 2, 3, 4]);

        let s = [10u16, 20u16];
        let try_v = InplaceVector::<u16, 4>::try_from(&s[..]);
        assert!(try_v.is_ok());
        let v2 = try_v.unwrap();
        assert_eq!(v2, &[10, 20]);
        let big: &[u16] = &[1, 2, 3, 4, 5];
        assert!(InplaceVector::<u16, 4>::try_from(big).is_err());
    }

    #[test]
    #[inline]
    fn try_from_into_array_success_and_failure() {
        let mut v = inplace_vec![3;];
        v.push(1);
        v.push(2);
        v.push(3);

        let arr_res: Result<[i32; 3], _> = <[i32; 3]>::try_from(v);
        assert!(arr_res.is_ok());
        assert_eq!(arr_res.unwrap(), [1, 2, 3]);

        let mut v2 = inplace_vec![3;];
        v2.push(4);
        let conv: Result<[i32; 3], _> = <[i32; 3]>::try_from(v2);
        assert!(conv.is_err());
    }

    #[test]
    #[inline]
    fn try_from_ref_into_array() {
        let mut v = inplace_vec![2;];
        v.push(1);
        v.push(2);

        let arr: [i32; 2] = <[i32; 2]>::try_from(&v).unwrap();
        assert_eq!(arr, [1, 2]);
    }

    #[test]
    #[inline]
    fn into_iter_consumes_and_double_ended() {
        let mut v = inplace_vec![5;];
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
    #[inline]
    fn spare_capacity_and_set_len_manual_init() {
        let mut v = inplace_vec![6;];
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
    #[inline]
    fn resize_and_resize_with_and_truncate_clear() {
        let mut v = inplace_vec![6;];
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
    #[inline]
    fn pop_if_checks_last_elem() {
        let mut v = inplace_vec![4;];
        v.push(5);
        v.push(10);

        let p = v.pop_if(|x| *x == 10);
        assert_eq!(p, Some(10));
        assert_eq!(v, &[5]);

        let p2 = v.pop_if(|x| *x == 100);
        assert_eq!(p2, None);
    }

    #[test]
    #[inline]
    fn default_and_clone_and_debug() {
        let mut v = InplaceVector::<i32, 4>::default();
        v.push(3);
        let c = v.clone();
        assert_eq!(c, &[3]);
        assert_eq!(format!("{:?}", c), "[3]");
    }

    #[test]
    #[inline]
    fn ord_and_borrow_traits() {
        let mut a = inplace_vec![4;];
        a.extend([1, 2].iter());
        let mut b = inplace_vec![4;];
        b.extend([1, 3].iter());
        assert_eq!(a.cmp(&b), Ordering::Less);

        let as_ref: &[i32] = a.as_ref();
        assert_eq!(as_ref, &[1, 2]);

        let borrowed: &[i32] = a.borrow();
        assert_eq!(borrowed, &[1, 2]);

        let mut c = inplace_vec![4;];
        c.extend([5, 6].iter());
        let borrowed_mut: &mut [i32] = c.borrow_mut();
        borrowed_mut[0] = 7;
        assert_eq!(c, &[7, 6]);
    }

    #[test]
    #[inline]
    fn drop_behavior_managed_by_set_len() {
        let counter = Cell::new(0);
        struct DC<'a>(&'a Cell<u32>);
        impl<'a> Drop for DC<'a> {
            #[inline]
            fn drop(&mut self) {
                self.0.set(self.0.get() + 1);
            }
        }

        {
            let mut v = inplace_vec![4;];
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
    #[inline]
    fn insert_out_of_bounds_panics() {
        let mut v = inplace_vec![3;];
        v.push(1);
        v.insert(2, 5); // len is 1, index 2 is invalid
    }

    #[test]
    #[should_panic(expected = "insert call should not exceed capacity")]
    #[inline]
    fn insert_when_full_panics() {
        let mut v = inplace_vec![2;];
        v.push(1);
        v.push(2);
        v.insert(1, 3);
    }

    #[test]
    #[should_panic(expected = "removal index")]
    #[inline]
    fn remove_out_of_bounds_panics() {
        let mut v = inplace_vec![2;];
        v.push(1);
        v.remove(1);
    }

    #[test]
    #[should_panic(expected = "removal index")]
    #[inline]
    fn swap_remove_out_of_bounds_panics() {
        let mut v = inplace_vec![2;];
        v.push(1);
        v.swap_remove(1);
    }

    #[test]
    #[should_panic(expected = "range out of bounds")]
    #[inline]
    fn drain_out_of_bounds_panics() {
        let mut v = inplace_vec![3;];
        v.push(1);
        v.push(2);
        v.drain(0..4);
    }

    #[test]
    #[inline]
    fn drain_removes_correct_range() {
        let mut v = inplace_vec![5;];
        for i in 0..5 {
            v.push(i);
        }
        let drained: Vec<_> = v.drain(1..4).collect();
        assert_eq!(drained, vec![1, 2, 3]);
        assert_eq!(v, &[0, 4]);
    }

    #[test]
    #[inline]
    fn split_off_at_len_and_zero() {
        let mut v = inplace_vec![3;];
        v.push(1);
        v.push(2);
        let tail = v.split_off(2);
        assert_eq!(tail, &[]);
        assert_eq!(v, &[1, 2]);

        let mut v2 = inplace_vec![3;];
        v2.push(1);
        let head = v2.split_off(0);
        assert_eq!(head, &[1]);
        assert_eq!(v2, &[]);
    }

    #[test]
    #[should_panic]
    #[inline]
    fn extend_from_slice_panics_when_too_big() {
        let mut v = inplace_vec![2;];
        let slice = [1, 2, 3];
        v.extend_from_slice(&slice);
    }

    #[test]
    #[inline]
    fn try_from_slice_failure_and_success() {
        let arr = [1, 2, 3, 4];
        assert!(InplaceVector::<i32, 3>::try_from(&arr[..]).is_err());
        let arr2 = [1, 2];
        let v = InplaceVector::<i32, 3>::try_from(&arr2[..]).unwrap();
        assert_eq!(v, &[1, 2]);
    }

    #[test]
    #[inline]
    fn try_from_slice_clones_elements() {
        #[derive(Debug)]
        struct Counted<'a>(&'a AtomicUsize);

        impl<'a> Clone for Counted<'a> {
            #[inline]
            fn clone(&self) -> Self {
                self.0.fetch_add(1, AtomicOrdering::Relaxed);
                Self(self.0)
            }
        }

        let counter = AtomicUsize::new(0);
        let arr = [Counted(&counter), Counted(&counter), Counted(&counter)];

        let v = InplaceVector::<Counted<'_>, 4>::try_from(&arr[..]).unwrap();
        assert_eq!(v.len(), 3);
        assert_eq!(counter.load(AtomicOrdering::Relaxed), 3);
    }

    #[test]
    #[inline]
    fn extend_from_slice_within_capacity_full_fit() {
        let mut v = inplace_vec![6;];
        let slice = [1, 2];
        let res = v.extend_from_slice_within_capacity(&slice);
        assert!(res.is_ok());
        assert_eq!(v, &[1, 2]);
    }

    #[test]
    #[should_panic]
    #[inline]
    fn resize_panics_when_exceeds_capacity() {
        let mut v = inplace_vec![2;];
        v.resize(3, 1);
    }

    #[test]
    #[should_panic]
    #[inline]
    fn resize_with_panics_when_exceeds_capacity() {
        let mut v = inplace_vec![2;];
        v.resize_with(3, || 1);
    }

    #[test]
    #[inline]
    fn dedup_variants() {
        let mut v = inplace_vec![5;];
        v.push(1);
        v.push(1);
        v.push(2);
        v.push(2);
        v.push(3);
        v.dedup();
        assert_eq!(v, &[1, 2, 3]);

        let mut v2 = inplace_vec![10;];
        v2.push(1);
        v2.push(1);
        v2.push(2);
        v2.push(2);
        v2.push(4);
        v2.push(3);
        v2.push(5);
        v2.push(7);
        v2.dedup_by(|a, b| *a % 2 == *b % 2);
        assert_eq!(v2, &[1, 2, 3]);
    }

    #[test]
    #[inline]
    fn dedup_by_key_example() {
        let mut v = inplace_vec![5;];
        v.push(1);
        v.push(3);
        v.push(2);
        v.push(4);
        v.dedup_by_key(|x| *x % 2);
        assert_eq!(v, &[1, 2]);
    }

    #[test]
    #[should_panic]
    #[inline]
    fn append_panics_when_overflow() {
        let mut a = inplace_vec![2;];
        a.push(1);

        let mut b = inplace_vec![2;];
        b.push(2);
        b.push(3);

        a.append(&mut b)
    }

    #[test]
    #[inline]
    fn into_iter_clone_and_double_ended() {
        let mut v = inplace_vec![3;];
        v.push(10);
        v.push(20);
        let mut iter = v.clone().into_iter();
        assert_eq!(iter.next(), Some(10));
        assert_eq!(iter.next_back(), Some(20));
        assert_eq!(iter.next(), None);

        let iter2 = v.into_iter();
        let clone = iter2.clone();
        assert_eq!(clone.as_slice(), &[10, 20]);
    }

    #[test]
    #[inline]
    fn write_trait_behavior() {
        let mut v = inplace_vec![4;];
        let buf = [1, 2, 3, 4, 5];
        let written = std::io::Write::write(&mut v, &buf).unwrap();
        assert_eq!(written, 4);
        assert_eq!(v, &[1, 2, 3, 4]);
    }
}
