extern crate alloc;
use alloc::string::String;
use core::fmt;

#[derive(Debug)]
pub enum ActError {
    InvalidScalar,
    InvalidSubgroup,
    VerificationFailed(String),
    SerializationError(ark_serialize::SerializationError),
    IoError(ark_std::io::Error),
    ProtocolError(String),
    DatabaseError(String),
}

pub type Result<T> = core::result::Result<T, ActError>;

impl fmt::Display for ActError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidScalar => write!(f, "Invalid scalar: not in field"),
            Self::InvalidSubgroup => write!(f, "Invalid group element: not in subgroup"),
            Self::VerificationFailed(msg) => write!(f, "Proof verification failed: {msg}"),
            Self::SerializationError(err) => write!(f, "Serialization error: {err}"),
            Self::IoError(err) => write!(f, "I/O error: {err}"),
            Self::ProtocolError(msg) => write!(f, "Protocol error: {msg}"),
            Self::DatabaseError(msg) => write!(f, "Database error: {msg}"),
        }
    }
}

impl From<ark_serialize::SerializationError> for ActError {
    fn from(value: ark_serialize::SerializationError) -> Self {
        Self::SerializationError(value)
    }
}

impl From<ark_std::io::Error> for ActError {
    fn from(value: ark_std::io::Error) -> Self {
        Self::IoError(value)
    }
}

#[cfg(feature = "server")]
impl From<redis::RedisError> for ActError {
    fn from(value: redis::RedisError) -> Self {
        Self::DatabaseError(value.to_string())
    }
}

