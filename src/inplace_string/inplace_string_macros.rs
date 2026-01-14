use super::InplaceString;

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
    //let _ = inplace_string!("test");
}
