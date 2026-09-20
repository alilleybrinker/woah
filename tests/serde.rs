// SPDX-License-Identifier: MIT OR Apache-2.0

//! Checks that `woah::Result` survives a serde round trip, and pins down the
//! shape it serializes to.
//!
//! The wire format is whatever `Result<Result<T, L>, F>` serializes to, since
//! that is what the impls convert through. That is a compatibility promise, so
//! the shape is asserted explicitly rather than only round-tripped.

#![cfg(feature = "serde")]

use woah::prelude::*;

type R = Result<u32, String, String>;

#[test]
fn success_round_trips() {
    let value: R = Success(5);
    let json = serde_json::to_string(&value).unwrap();

    assert_eq!(json, r#"{"Ok":{"Ok":5}}"#);
    assert_eq!(serde_json::from_str::<R>(&json).unwrap(), value);
}

#[test]
fn local_err_round_trips() {
    let value: R = LocalErr(String::from("a local error"));
    let json = serde_json::to_string(&value).unwrap();

    assert_eq!(json, r#"{"Ok":{"Err":"a local error"}}"#);
    assert_eq!(serde_json::from_str::<R>(&json).unwrap(), value);
}

#[test]
fn fatal_err_round_trips() {
    let value: R = FatalErr(String::from("a fatal error"));
    let json = serde_json::to_string(&value).unwrap();

    assert_eq!(json, r#"{"Err":"a fatal error"}"#);
    assert_eq!(serde_json::from_str::<R>(&json).unwrap(), value);
}

#[test]
fn nested_results_round_trip() {
    let value: Result<Result<u32, String, String>, String, String> =
        Success(LocalErr(String::from("an inner local error")));
    let json = serde_json::to_string(&value).unwrap();

    assert_eq!(
        serde_json::from_str::<Result<Result<u32, String, String>, String, String>>(&json).unwrap(),
        value
    );
}
