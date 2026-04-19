extern crate alloc;
use alloc::vec::Vec;
use ark_std::vec;
use alloc::string::String;
use thiserror::Error;

#[derive(Debug, Error)]
pub enum ActError {
    #[error("Invalid scalar: not in field")]
    InvalidScalar,
    #[error("Invalid group element: not in subgroup")]
    InvalidSubgroup,
    #[error("Proof verification failed: {0}")]
    VerificationFailed(String),
    #[error("Serialization error: {0}")]
    SerializationError(#[from] ark_serialize::SerializationError),
    #[error("I/O error: {0}")]
    IoError(#[from] ark_std::io::Error),
    #[error("Bulletproofs error: {0}")]
    BulletproofsError(#[from] ark_bulletproofs::ProofError),
    #[error("Protocol error: {0}")]
    ProtocolError(String),
    #[error("Database error: {0}")]
    DatabaseError(String),
}

pub type Result<T> = core::result::Result<T, ActError>;
