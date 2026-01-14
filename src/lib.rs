#[cfg(feature = "inplace_vector")]
mod inplace_vector;

#[cfg(feature = "inplace_vector")]
pub use inplace_vector::*;

#[cfg(feature = "inplace_string")]
mod inplace_string;

#[cfg(feature = "inplace_string")]
pub use inplace_string::*;
