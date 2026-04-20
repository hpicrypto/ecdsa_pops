//! Errors related to proving and verifying proofs.

// TODO: Better error handling

use bincode::Error;
use r1csipa::ProofError;
use thiserror::Error;

/// Represents an error
#[derive(Debug, Error)]
pub enum PopError {
    /// Circuit proof causes an error
    #[error("Circuit error")]
    CircuitError(#[from] ProofError),
    /// RoK error
    #[error("RoK error")]
    RoKError(String),
    /// Serde Serialization Error
    #[error("Serde Serialization error")]
    SerializationError(#[from] Error),
    /// Occurs when converting slices to arrays
    #[error("Invalid slice length")]
    SliceLength(#[from] std::array::TryFromSliceError),
    /// ECDSA Signature Error
    #[error("Bad ECDSA Signature")]
    ECDSASigError,
    /// Invalid Statement/Witness pair for relation
    #[error("Bad statement/witness")]
    InvalidStatementWitness(String),
    /// Try to access a witness that does not exist
    #[error("Missing witness")]
    MissingWitness(String),
    /// Try to access an array on a bad index
    #[error("Index out of bounds")]
    IndexOutOfBounds(String),
}
