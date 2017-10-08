use core::{result, fmt};
use core::fmt::{Display, Formatter};
use error;

pub type Result<T> = result::Result<T, Error>;

#[derive(Debug)]
pub struct Error {
    reason: &'static str,
}

impl Error {
    pub fn new(reason: &'static str) -> Self {
        Error {
            reason: reason,
        }
    }
}

impl error::Error for Error {
    fn description(&self) -> &str {
        self.reason
    }

    fn cause(&self) -> Option<&error::Error> {
        None
    }
}

impl Display for Error {
    fn fmt(&self, f: &mut Formatter) -> result::Result<(), fmt::Error> {
        error::Error::description(self).fmt(f)
    }
}

#[cfg(feature = "std")]
impl From<::std::io::Error> for Error {
    fn from(_err: ::std::io::Error) -> Self {
        return ::io::Error { reason: "IO Error" };
    }
}
