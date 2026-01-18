/// Internal helper macro used by `inplace_vec!` to count the number of
/// comma-separated expressions at compile time.
///
/// This macro expands to a `usize` constant equal to the number of expressions
/// passed to it.
///
/// # Notes
/// - This macro is not intended to be used directly.
/// - It performs purely syntactic counting via macro expansion and does not
///   evaluate the expressions.
///
/// # Examples
/// ```
/// use inplace_containers::*;
/// const N: usize = __count!(1, 2, 3, 4);
/// assert_eq!(N, 4);
/// ```
#[macro_export]
macro_rules! __count {
    () => { 0usize };
    ($head:expr $(, $tail:expr)*) => {
        1usize + $crate::__count!($($tail),*)
    };
}

/// Creates an `InplaceVector` with optional compile-time capacity checking.
///
/// This macro provides a convenient and allocation-free way to construct an
/// `InplaceVector` from a list of elements or with an explicit capacity.
///
/// ## Forms
///
/// ### Empty vector
/// ```
/// use inplace_containers::*;
/// let v: InplaceVector<InplaceString<20>, 3> = inplace_vec![];
/// ```
///
/// ### Empty vector with explicit capacity
/// ```
/// use inplace_containers::*;
/// let mut v = inplace_vec![8;];
/// v.push(42);
/// ```
///
/// ### Vector from elements (capacity inferred)
/// ```
/// use inplace_containers::*;
/// let v = inplace_vec![1, 2, 3];
/// ```
///
/// ### Vector from elements with explicit capacity
/// ```
/// use inplace_containers::*;
/// let v = inplace_vec![8; 1, 2, 3];
/// ```
///
/// In the last form, the macro performs a **compile-time assertion** that the
/// provided capacity is at least the number of elements. If the assertion fails,
/// compilation will fail.
///
/// ## Safety
///
/// This macro internally uses `unsafe` code to efficiently move elements into
/// the backing storage without intermediate allocations. The implementation
/// ensures:
///
/// - No double-drop of elements
/// - Correct handling of non-`Copy` types
/// - No out-of-bounds writes
///
/// The macro is safe to use as long as `InplaceVector`’s invariants are upheld.
///
/// ## Panics
///
/// This macro does not panic at runtime. Capacity mismatches are detected at
/// compile time.
///
/// ## Examples
///
/// ```
/// use inplace_containers::*;
/// let v = inplace_vec![4; "a", "b", "c"];
/// assert_eq!(v.len(), 3);
/// ```
///
/// ```compile_fail
/// use inplace_containers::*;
/// let v = inplace_vec![2; 1, 2, 3]; // capacity too small
/// ```
#[macro_export]
macro_rules! inplace_vec {
    () => {
        InplaceVector::new()
    };

    ($cap:expr;) => {
        InplaceVector::<_, $cap>::new()
    };

    ($($elem:expr),+ $(,)?) => {{
        let array = [$($elem),*];
        InplaceVector::from(array)
    }};


    ($cap:expr; $($elem:expr),+ $(,)?) => {{
        const COUNT: usize = $crate::__count!($($elem),*);
        const _: () = assert!(
            $cap >= COUNT,
            concat!(
                "inplace_vec!: capacity ",
                stringify!($cap),
                " is smaller than the number of elements"
            )
        );

        let array = core::mem::ManuallyDrop::new([$($elem),*]);

        let mut v = InplaceVector::<_, $cap>::new();

        unsafe {
            // for deduction
            let mut _tmp = array.as_ptr();
            _tmp = v.as_ptr();

            core::ptr::copy_nonoverlapping(array.as_ptr(), v.as_mut_ptr(), COUNT);
            v.set_len(COUNT);
        };

        v
    }};

}
