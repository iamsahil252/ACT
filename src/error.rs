extern crate alloc;
use alloc::string::String;
use core::fmt;

#[derive(Debug)]
pub enum ActError {
    InvalidScalar,
    InvalidSubgroup,
    VerificationFailed(String),
    SerializationError(String),
    IoError(String),
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
            Self::SerializationError(msg) => write!(f, "Serialization error: {msg}"),
            Self::IoError(msg) => write!(f, "I/O error: {msg}"),
            Self::ProtocolError(msg) => write!(f, "Protocol error: {msg}"),
            Self::DatabaseError(msg) => write!(f, "Database error: {msg}"),
        }
    }
}

impl From<core::convert::Infallible> for ActError {
    fn from(e: core::convert::Infallible) -> Self {
        match e {}
    }
}

#[cfg(feature = "server")]
impl From<redis::RedisError> for ActError {
    fn from(value: redis::RedisError) -> Self {
        Self::DatabaseError(value.to_string())
    }
}
