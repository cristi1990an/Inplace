use super::InplaceString;

/// Creates an [`InplaceString`] from a string literal with exact capacity.
///
/// This macro constructs an `InplaceString` whose capacity is **exactly equal**
/// to the length of the provided string literal. No heap allocation is performed,
/// and the contents are copied directly into the inline storage.
///
/// The capacity is determined at compile time using the literal’s length.
///
/// # Forms
///
/// ```
/// use inplace_containers::*;
/// let s = inplace_string!("hello");
/// ```
///
/// # Guarantees
///
/// - The resulting string has `capacity() == $lit.len()`.
/// - The resulting string has `len() == $lit.len()`.
/// - No allocation is performed.
/// - Construction happens entirely at compile time + stack.
///
/// # Safety
///
/// This macro internally uses `unsafe` code and relies on the following facts:
///
/// - The input is a string literal and therefore valid UTF-8.
/// - The backing storage has exactly enough capacity to hold the literal.
/// - `unchecked_push_str` is safe under these conditions.
///
/// As a result, the macro itself is **safe to use**.
///
/// # Examples
///
/// ```
/// use inplace_containers::*;
/// let s = inplace_string!("test");
/// assert_eq!(s.capacity(), 4);
/// assert_eq!(s.len(), 4);
/// assert_eq!(s, "test");
/// ```
///
/// # Notes
///
/// - Only string literals are supported.
/// - Dynamic strings or `&str` values are intentionally rejected to preserve
///   compile-time capacity guarantees.
#[macro_export]
macro_rules! inplace_string {
    ($lit:literal) => {{
        const CAP: usize = $lit.len();
        let mut s = InplaceString::<CAP>::new();
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
