
#[macro_export]
macro_rules! __count {
    () => { 0usize };
    ($head:expr $(, $tail:expr)*) => {
        1usize + $crate::__count!($($tail),*)
    };
}

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
                "inplace_vec!: capacity (is ",
                stringify!($cap),
                ") smaller than element count (is ",
                stringify!(COUNT),
                ")"
            )
        );

        let array = [$($elem),*];

        let mut v = InplaceVector::<_, $cap>::new();

        unsafe {
            // for deduction
            let mut _tmp = array.as_ptr();
            _tmp = v.as_ptr();

            std::ptr::copy_nonoverlapping(array.as_ptr(), v.as_mut_ptr(), COUNT);
            v.set_len(COUNT);
            std::mem::forget(array);
        };

        v
    }};

}

