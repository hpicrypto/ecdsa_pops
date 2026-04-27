//! Defintions for various relations used

/// rchsnorr relation
pub(crate) mod rcshnorr;

/// rchsnorr relation with compact commitments
pub(crate) mod rcschnorr_compact;

/// dlog equality across different groups
pub(crate) mod rdleq;

/// knowledge of valid signature of m under committed public key
pub mod recdsa;

/// the knowledge of pedersen commitment opening
pub(crate) mod rpedersen;

/// point addition over p256 committed points
pub(crate) mod rpa;

/// scalar multiplication over p256 with committed base
pub(crate) mod rsm;

#[cfg(test)]
pub(crate) mod tests;
