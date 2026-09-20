// SPDX-License-Identifier: MIT OR Apache-2.0

//! Covers the `Termination` impl, which is generic over the success type the
//! way std's impl for `std::result::Result` is.
//!
//! The `Result<!, L, F>` case lives in tests/nightly.rs, since the never type
//! needs the `nightly` feature.

#![cfg(feature = "std")]

use std::process::ExitCode;
use woah::prelude::*;

#[test]
fn any_terminating_success_type_works() {
    fn assert_termination<T: Termination>() {}

    assert_termination::<Result<(), &'static str, &'static str>>();
    assert_termination::<Result<ExitCode, &'static str, &'static str>>();
    assert_termination::<Result<Result<(), u32, u32>, &'static str, &'static str>>();
}

#[test]
fn success_delegates_to_the_inner_termination() {
    // `ExitCode` implements neither `PartialEq` nor `Eq`, so compare the debug
    // output instead. The point is that the success value's own `report` is
    // what comes back, rather than a blanket success.
    let result: Result<ExitCode, &str, &str> = Success(ExitCode::from(3));

    assert_eq!(
        format!("{:?}", result.report()),
        format!("{:?}", ExitCode::from(3))
    );
}

#[test]
fn errors_report_failure() {
    let local: Result<(), &str, &str> = LocalErr("a local error");
    let fatal: Result<(), &str, &str> = FatalErr("a fatal error");
    let failure = format!("{:?}", ExitCode::FAILURE);

    // Both error variants report failure, and print the error to stderr.
    assert_eq!(format!("{:?}", local.report()), failure);
    assert_eq!(format!("{:?}", fatal.report()), failure);
}

#[test]
fn unit_success_reports_success() {
    let result: Result<(), &str, &str> = Success(());

    assert_eq!(
        format!("{:?}", result.report()),
        format!("{:?}", ExitCode::SUCCESS)
    );
}
