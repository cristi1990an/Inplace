#![cfg_attr(not(feature = "std"), no_std)]
#![cfg_attr(feature = "nightly", feature(pattern))]

#[cfg(test)]
extern crate std;

#[cfg(feature = "inplace_vector")]
mod inplace_vector;

#[cfg(feature = "inplace_vector")]
pub use inplace_vector::*;

/// Commonly used traits and container types.
pub mod prelude {
    #[cfg(feature = "inplace_vector")]
    pub use crate::{InplaceVector, ToInplaceOwned};

    #[cfg(feature = "inplace_string")]
    pub use crate::InplaceString;
}

#[cfg(feature = "inplace_string")]
mod inplace_string;

#[cfg(feature = "inplace_string")]
pub use inplace_string::*;
