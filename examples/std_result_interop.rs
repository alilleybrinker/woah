//! An example of `woah` interoperating smoothly with `std::result::Result`.

// Compile with `cargo +nightly check --examples --features=nightly`
// Run with `cargo +nightly run --example std_result_interop --features=nightly`

use std::fmt::{self, Display, Formatter};
use std::result::Result as StdResult;
use woah::prelude::*;

fn main() {
    let r1 = woah_to_std();
    let r2 = std_to_woah();

    eprintln!("error: {:?} (woah -> std)", r1);
    eprintln!("error: {:?} (std -> woah)", r2);
}

/// Returns a `woah::Result`.
fn returns_woah_result() -> Result<(), LocalError, FatalError> {
    FatalErr(FatalError::RequestFailed)
}

/// Returns a `std::result::Result`.
fn returns_std_result() -> StdResult<(), FatalError> {
    Err(FatalError::RequestFailed)
}

/// Converts a `woah::Result` to a `std::result::Result`.
fn woah_to_std() -> StdResult<(), FatalError> {
    let _ = returns_woah_result()?;
    Ok(())
}

/// Converts a `std::result::Result` to a `woah::Result`.
fn std_to_woah() -> Result<(), LocalError, FatalError> {
    let _ = returns_std_result()?;
    Success(())
}

/// Errors which can be handled.
#[derive(Debug)]
enum LocalError {
    #[allow(unused)]
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
