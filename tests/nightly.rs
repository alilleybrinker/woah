// SPDX-License-Identifier: MIT OR Apache-2.0

//! Covers the trait impls behind the `nightly` feature: `Try`/`FromResidual`,
//! `FromIterator`, `Sum`, `Product` and `into_success`.
//!
//! The `?` tests are the important ones. A fatal error propagating while a
//! local error is handed back to the caller is the behavior the whole crate
//! exists to provide, and nothing else in the suite checks it.

#![cfg(feature = "nightly")]

use woah::prelude::*;

type R = Result<u32, &'static str, &'static str>;

fn success_source() -> R {
    Success(1)
}

fn local_source() -> R {
    LocalErr("a local error")
}

fn fatal_source() -> R {
    FatalErr("a fatal error")
}

#[test]
fn question_mark_propagates_a_fatal_error() {
    fn caller() -> R {
        let handled = fatal_source()?;
        Success(handled.unwrap_or(0))
    }

    assert_eq!(caller(), FatalErr("a fatal error"));
}

#[test]
fn question_mark_hands_back_a_local_error() {
    fn caller() -> R {
        // A local error arrives as `Err` rather than returning early, so it can
        // be handled here.
        match local_source()? {
            Ok(value) => Success(value),
            Err(_) => Success(99),
        }
    }

    assert_eq!(caller(), Success(99));
}

#[test]
fn question_mark_passes_a_success_through() {
    fn caller() -> R {
        let handled = success_source()?;
        Success(handled.unwrap_or(0) + 1)
    }

    assert_eq!(caller(), Success(2));
}

#[test]
fn question_mark_accepts_a_std_result() {
    fn std_source() -> StdResult<u32, &'static str> {
        Err("a fatal error")
    }

    // `?` on a `std::result::Result` inside a function returning a
    // `woah::Result` treats its error as the fatal one.
    fn caller() -> R {
        Success(std_source()? + 1)
    }

    assert_eq!(caller(), FatalErr("a fatal error"));
}

#[test]
fn collect_stops_at_the_first_error() {
    let all: Result<Vec<u32>, &str, &str> = vec![Success(1), Success(2)].into_iter().collect();
    assert_eq!(all, Success(vec![1, 2]));

    let local: Result<Vec<u32>, &str, &str> =
        vec![Success(1), LocalErr("a local error"), Success(3)]
            .into_iter()
            .collect();
    assert_eq!(local, LocalErr("a local error"));

    let fatal: Result<Vec<u32>, &str, &str> =
        vec![Success(1), FatalErr("a fatal error"), Success(3)]
            .into_iter()
            .collect();
    assert_eq!(fatal, FatalErr("a fatal error"));
}

#[test]
fn sum_and_product() {
    let sum: R = vec![Success(1), Success(2), Success(3)].into_iter().sum();
    assert_eq!(sum, Success(6));

    let sum_err: R = vec![Success(1), FatalErr("a fatal error")]
        .into_iter()
        .sum();
    assert_eq!(sum_err, FatalErr("a fatal error"));

    let product: R = vec![Success(2), Success(3)].into_iter().product();
    assert_eq!(product, Success(6));

    let product_err: R = vec![Success(2), LocalErr("a local error")]
        .into_iter()
        .product();
    assert_eq!(product_err, LocalErr("a local error"));
}

#[test]
fn into_success_on_uninhabited_errors() {
    let result: Result<u32, !, !> = Success(5);
    assert_eq!(result.into_success(), 5);
}

#[cfg(feature = "std")]
#[test]
fn termination_is_implemented() {
    fn assert_termination<T: std::process::Termination>() {}

    assert_termination::<Result<(), &'static str, &'static str>>();
    assert_termination::<Result<!, &'static str, &'static str>>();
}
