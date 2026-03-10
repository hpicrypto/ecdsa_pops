//! Defintions for various relations used

/// rchsnorr EC equation verifies
pub(crate) mod rcshnorr;

/// dlog equality across different groups
pub(crate) mod rdleq;

/// knowledge of valid signature of m under committed public key
pub mod recdsa;

/// the knowledge of pedersen commitment opening
pub(crate) mod rpedersen;

#[cfg(test)]
pub(crate) mod tests;
