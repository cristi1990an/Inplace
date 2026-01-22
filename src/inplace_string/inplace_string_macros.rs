/// Creates an [`crate::InplaceString`] with compile-time capacity checking.
///
/// This macro provides allocation-free construction from a string literal or
/// with an explicit capacity.
///
/// # Forms
///
/// ```rust
/// use inplace_containers::*;
/// let s = inplace_string!("hello");
/// ```
///
/// ```rust
/// use inplace_containers::*;
/// let s = inplace_string![10; "hello"];
/// ```
///
/// ```rust
/// use inplace_containers::*;
/// let s: InplaceString<10> = inplace_string![10;];
/// ```
///
/// # Guarantees
///
/// - For `inplace_string!("lit")`, `capacity() == $lit.len()`.
/// - For `inplace_string![CAP; "lit"]`, `capacity() == CAP`.
/// - For `inplace_string![CAP;]`, the string is empty with `capacity() == CAP`.
/// - No allocation is performed.
///
/// # Safety
///
/// This macro internally uses `unsafe` code and relies on the following facts:
///
/// - The input is a string literal and therefore valid UTF-8.
/// - The backing storage has enough capacity to hold the literal.
/// - `unchecked_push_str` is safe under these conditions.
///
/// As a result, the macro itself is **safe to use**.
///
/// # Examples
///
/// ```rust
/// use inplace_containers::*;
/// let s = inplace_string!("test");
/// assert_eq!(s.capacity(), 4);
/// assert_eq!(s.len(), 4);
/// assert_eq!(s, "test");
/// ```
///
/// ```rust
/// use inplace_containers::*;
/// let s = inplace_string![8; "hi"];
/// assert_eq!(s.capacity(), 8);
/// assert_eq!(s.len(), 2);
/// assert_eq!(s, "hi");
/// ```
///
/// # Notes
///
/// - Only string literals are supported for contents.
/// - Dynamic strings or `&str` values are intentionally rejected to preserve
///   compile-time capacity guarantees.
#[macro_export]
macro_rules! inplace_string {
    ($lit:literal) => {{
        const CAP: usize = $lit.len();
        let mut s = $crate::InplaceString::<CAP>::new();
        unsafe {
            s.unchecked_push_str($lit);
        }
        s
    }};
    ($cap:expr;) => {{
        $crate::InplaceString::<$cap>::new()
    }};
    ($cap:expr; $lit:literal) => {{
        const _: () = assert!(
            $cap >= $lit.len(),
            concat!(
                "inplace_string!: capacity ",
                stringify!($cap),
                " is smaller than the literal length"
            )
        );
        let mut s = $crate::InplaceString::<$cap>::new();
        unsafe {
            s.unchecked_push_str($lit);
        }
        s
    }};
}

#[test]
fn foo() {
    let string = inplace_string!("test");

    assert_eq!(string.capacity(), 4);
    assert_eq!(string.len(), 4);
    assert_eq!(string, "test");
}

#[test]
fn explicit_capacity_literal() {
    let string = inplace_string![10; "test"];

    assert_eq!(string.capacity(), 10);
    assert_eq!(string.len(), 4);
    assert_eq!(string, "test");
}

#[test]
fn explicit_capacity_empty() {
    let string: crate::InplaceString<10> = inplace_string![10;];

    assert_eq!(string.capacity(), 10);
    assert_eq!(string.len(), 0);
    assert_eq!(string, "");
}
