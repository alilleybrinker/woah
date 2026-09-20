// SPDX-License-Identifier: MIT OR Apache-2.0

//! Covers the iterator types and the three `IntoIterator` impls, none of which
//! the doc-tests exercise beyond a single `next` call.

use woah::prelude::*;

type R = Result<u32, &'static str, &'static str>;

#[test]
fn iter_yields_only_success() {
    let success: R = Success(5);
    assert_eq!(success.iter().collect::<Vec<_>>(), vec![&5]);

    let local: R = LocalErr("a local error");
    assert_eq!(local.iter().count(), 0);

    let fatal: R = FatalErr("a fatal error");
    assert_eq!(fatal.iter().count(), 0);
}

#[test]
fn iter_size_hint_reports_exact_length() {
    let success: R = Success(5);
    assert_eq!(success.iter().size_hint(), (1, Some(1)));

    let fatal: R = FatalErr("a fatal error");
    assert_eq!(fatal.iter().size_hint(), (0, Some(0)));
}

#[test]
fn iter_is_fused_and_double_ended() {
    let success: R = Success(5);
    let mut iter = success.iter();

    assert_eq!(iter.next_back(), Some(&5));
    assert_eq!(iter.next(), None);
    // Fused: still `None` once exhausted.
    assert_eq!(iter.next(), None);
}

#[test]
fn iter_mut_writes_through() {
    let mut success: R = Success(5);

    for value in success.iter_mut() {
        *value += 1;
    }

    assert_eq!(success, Success(6));

    let mut fatal: R = FatalErr("a fatal error");
    assert_eq!(fatal.iter_mut().count(), 0);
}

#[test]
fn into_iter_reports_exact_length() {
    let success: R = Success(5);
    let iter = success.into_iter();

    assert_eq!(iter.size_hint(), (1, Some(1)));
    assert_eq!(iter.len(), 1);

    let fatal: R = FatalErr("a fatal error");
    let iter = fatal.into_iter();

    assert_eq!(iter.size_hint(), (0, Some(0)));
    assert_eq!(iter.len(), 0);
}

#[test]
fn into_iter_is_fused_and_double_ended() {
    let success: R = Success(5);
    let mut iter = success.into_iter();

    assert_eq!(iter.next_back(), Some(5));
    assert_eq!(iter.next(), None);
    // Fused: still `None` once exhausted.
    assert_eq!(iter.next(), None);
}

#[test]
fn iter_and_iter_mut_report_exact_length() {
    let mut success: R = Success(5);

    assert_eq!(success.iter().len(), 1);
    assert_eq!(success.iter_mut().len(), 1);

    let mut fatal: R = FatalErr("a fatal error");

    assert_eq!(fatal.iter().len(), 0);
    assert_eq!(fatal.iter_mut().len(), 0);
}

#[test]
fn into_iterator_by_value() {
    let success: R = Success(5);
    assert_eq!(success.into_iter().collect::<Vec<_>>(), vec![5]);

    let local: R = LocalErr("a local error");
    assert_eq!(local.into_iter().count(), 0);
}

#[test]
fn into_iterator_by_reference() {
    let success: R = Success(5);
    assert_eq!((&success).into_iter().collect::<Vec<_>>(), vec![&5]);

    // `for` loops over a reference go through the same impl.
    let mut seen = Vec::new();

    for value in &success {
        seen.push(*value);
    }

    assert_eq!(seen, vec![5]);
}

#[test]
fn into_iterator_by_mutable_reference() {
    let mut success: R = Success(5);

    for value in &mut success {
        *value *= 2;
    }

    assert_eq!(success, Success(10));
}
