// SPDX-License-Identifier: MIT OR Apache-2.0

//! Checks that the methods documented as `const fn` really are usable in const
//! contexts. Everything here is evaluated at compile time, so the test passing
//! is incidental -- it compiling is the point, and dropping a `const` from any
//! of these signatures breaks the build.

use woah::prelude::*;
use woah::{Iter, IterMut};

const SUCCESS: Result<u32, &str, &str> = Result::from_success(0);
const LOCAL: Result<u32, &str, &str> = Result::from_local_err("local");
const FATAL: Result<u32, &str, &str> = Result::from_fatal_error("fatal");

// Grouped into an array so the test compares values rather than asserting on
// constants, which clippy rightly points out proves nothing at runtime.
const PREDICATES: [bool; 6] = [
    SUCCESS.is_success(),
    SUCCESS.is_err(),
    LOCAL.is_err(),
    LOCAL.is_local_err(),
    FATAL.is_fatal_err(),
    FATAL.is_local_err(),
];

const AS_REF: Result<&u32, &&str, &&str> = SUCCESS.as_ref();
const ITER: Iter<'_, u32> = SUCCESS.iter();

// `as_mut` and `iter_mut` need a mutable place to borrow, which a `const` item
// is not, so they are exercised inside const blocks instead.
const AS_MUT: u32 = {
    let mut result: Result<u32, &str, &str> = Result::from_success(1);

    match result.as_mut() {
        Success(t) => *t,
        LocalErr(_) | FatalErr(_) => 0,
    }
};

// Nothing can be asked of the iterator here -- `Iterator::size_hint` is a trait
// method, so it is not const -- but building one at compile time is the point.
const ITER_MUT: () = {
    let mut result: Result<u32, &str, &str> = Result::from_success(2);
    let _: IterMut<'_, u32> = result.iter_mut();
};

#[test]
fn const_constructors() {
    assert_eq!(SUCCESS, Success(0));
    assert_eq!(LOCAL, LocalErr("local"));
    assert_eq!(FATAL, FatalErr("fatal"));
}

#[test]
fn const_predicates() {
    assert_eq!(PREDICATES, [true, false, true, true, true, false]);
}

#[test]
fn const_borrows() {
    assert_eq!(AS_REF, Success(&0));
    assert_eq!(AS_MUT, 1);
}

#[test]
fn const_iterators() {
    assert_eq!(ITER.size_hint(), (1, Some(1)));
    assert_eq!(ITER_MUT, ());
}
