//! A basic example of `woah` showing a simulated HTTP request.

// Compile with `cargo +nightly check --examples --features=nightly`
// Run with `cargo +nightly run --example basic --features=nightly`

use rand::prelude::*;
use std::fmt::{self, Display, Formatter};
use woah::prelude::*;

// Convenience type with `LocalError` and `FatalError` filled in.
type RequestResult<T> = Result<T, LocalError, FatalError>;

fn main() {
    match get_data() {
        Success(data) => println!("{}", data),
        LocalErr(e) => eprintln!("error: {}", e),
        FatalErr(e) => eprintln!("error: {}", e),
    }
}

/// Get data from an HTTP API.
fn get_data() -> RequestResult<String> {
    match do_http_request()? {
        Ok(data) => Success(data),
        Err(e) => {
            eprintln!("error: {}... retrying", e);
            get_data()
        }
    }
}

/// Make an HTTP request.
///
/// This is simulated with randomly returning either a time out
/// or a request failure.
fn do_http_request() -> RequestResult<String> {
    if random() {
        LocalErr(LocalError::RequestTimedOut)
    } else {
        FatalErr(FatalError::RequestFailed)
    }
}

/// Errors which can be handled.
#[derive(Debug)]
enum LocalError {
    /// A request timed out. Can be handled by retrying.
    RequestTimedOut,
}

/// Errors which can't be handled.
#[derive(Debug)]
enum FatalError {
    /// The request failed.
    RequestFailed,
}

impl Display for LocalError {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            LocalError::RequestTimedOut => write!(f, "request timed out"),
        }
    }
}

impl Display for FatalError {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            FatalError::RequestFailed => write!(f, "request failed"),
        }
    }
}
