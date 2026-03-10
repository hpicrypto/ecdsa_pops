//! Implementations of proof-of-possesions (PoP) based on ECDSA signatures over P256.
//!
//! The signatures are assumed to be on random nonces and the one part of the signature
//! (x-coordinate of of the random point sampled by the signer) is known

#![deny(missing_docs)]
#![allow(non_snake_case)]

pub(crate) mod circuit;
pub mod errors;
mod pop_native;
mod relations;
pub(crate) mod roks;
pub mod utils;

pub use pop_native::*;
pub use relations::recdsa::*;
