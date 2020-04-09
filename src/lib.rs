#![doc(issue_tracker_base_url = "https://github.com/alilleybrinker/woe/issues/")]

// Turn on the try trait for the regular code and for documentation tests.
#![cfg_attr(feature="try_trait", feature(try_trait))]
#![cfg_attr(feature="try_trait", doc(test(attr(feature(try_trait)))))]
#![cfg_attr(feature="trusted_len", feature(trusted_len))]
#![cfg_attr(feature="never_type", feature(never_type))]
#![cfg_attr(feature="termination_trait", feature(termination_trait_lib))]
#![cfg_attr(feature="termination_trait", feature(process_exitcode_placeholder))]
// Turn on clippy lints.
#![deny(clippy::all)]
#![deny(clippy::pedantic)]
#![deny(clippy::cargo)]
#![warn(clippy::restriction)]
// TODO: Add all missing documentation so this lint passes.
// #![warn(missing_docs)]
// #![warn(missing_doc_code_examples)]
// #![warn(private_doc_tests)]
#![warn(missing_debug_implementations)]
#![warn(missing_copy_implementations)]

//!`woe` is a Rust crate which provides the following type:
//!
//! ```text
//! enum Result<T, L, F> {
//!     Ok(T),
//!     LocalErr(L),
//!     FatalErr(F),
//! }
//! ```
//!
//! This type differentiates between "local errors" which can be handled and "fatal errors" which can't, to
//! enable the error handling pattern described by Tyler Neely (@spacejam) in the blog post ["Error Handling
//! in a Correctness-Critical Rust Project"][post]. `woe::Result` is intended to be a more ergonomic
//! alternative to the `Result<Result<T, LocalError>, FatalError>` type proposed in the post.
//!
//! The important thing to note is that using the question mark operator on `woe::Result` causes
//! any `FatalError` to propagate up, while providing `Result<T, LocalError>` otherwise, to enable
//! the local code to handle any local errors without propagating them.
//!
//! # Features
//! 
//! `woe` can be used on stable or nightly. On nightly, enabling the `nightly` feature is recommended,
//! to get the full power of the `woe::Result` type, including:
//! 
//! * Being able to use it with the question mark operator,
//! * Being able to make it the return type of `fn main`,
//! * Gaining a number of useful additional methods, including `from_iter` (which enables easy conversion
//!   from `Vec<woe::Result<T, L, F>` into `woe::Result<Vec<T>, L, F>` via the `collect` method).
//! 
//! The following table is the full list of features. If you want to use `woe` without any dependencies,
//! you can disable the `either_methods` feature, which otherwise imports the `either` crate to add additional
//! methods.
//! 
//!| Feature Name         | Channels              | Depends On         | What It Does |
//!|:---------------------|:----------------------|:-------------------|:-------------|
//!| `default`            | Stable, Beta, Nightly | `either_methods`   | Enables default features (currently just `either_methods`). |
//!| `either_methods`     | Stable, Beta, Nightly | None               | Adds the `either` crate as a dependency and provides convenience methods for operating on `Either<LocalErr, FatalErr>`. |
//!| `nightly`            | Nightly               | `try_trait`, `trusted_len`, `never_type`, `termination_trait`, `product_trait`, `sum_trait`, `from_iterator_trait` | Enables all nightly-only features. __This feature is permanently unstable, and changes to the APIs enabled by this feature are never considered breaking changes.__ |
//!| `try_trait`          | Nightly               |                    | Enables the `Try` trait, so `woe::Result` can be used with the question mark operator. |
//!| `trusted_len`        | Nightly               |                    | Enables `woe::Result::{IntoIter, Iter, IterMut}` to implement the `TrustedLen` trait. |
//!| `never_type`         | Nightly               |                    | Enables the `into_ok` method if both the `LocalErr` and `FatalErr` variant types are `!` (the never type). |
//!| `termination_trait`  | Nightly               | `never_type`       | Enables `woe::Result` to be used as the return type for the `main` function. |
//!| `product_trait`      | Nightly               | `try_trait`        | Enables the `std::iter::Product` trait. |
//!| `sum_trait`          | Nightly               | `try_trait`        | Enables the `std::iter::Sum` trait. |
//!| `from_iterator_trait` | Nightly              | `try_trait`        | Enables the `FromIterator` trait, which also enables convenient `collect`ing of `Vec<woe::Result<T, L, F>>` into `woe::Result<Vec<T>, L, F>` |
//!
//! # Example on stable
//! 
//! ```
//! use woe::Result::{self, Ok, LocalErr, FatalErr};
//! use std::result::{Result as StdResult, Result::Ok as StdOk, Result::Err as StdErr};
//!
//! fn main() {
//!     match do_thing() {
//!         StdOk(num) => println!("Got a number: {}", num),
//!         StdResult::Err(fatal_err) => eprintln!("Fatal error: {:?}", fatal_err),
//!     }
//! }
//!
//! fn do_thing() -> StdResult<i64, FatalError> {
//!     let result = do_another_thing(5, 5)?;
//!
//!     // `result` has type `Result<i64, LocalError>`.
//!     match result {
//!         StdResult::Err(local_err) => {
//!             println!("Local error: {:?}", local_err);
//!             StdOk(i64::default())
//!         }
//!         StdOk(num) => StdOk(num),
//!     }
//! }
//!
//! fn do_another_thing(x: i64, y: i64) -> StdResult<StdResult<i64, LocalError>, FatalError> {
//!     if x > y {
//!         Ok(x)
//!     } else if x == y {
//!         // Make clear which error is the local error ...
//!         LocalErr(LocalError::SomeError)
//!     } else {
//!         // ... and which is the fatal error
//!         FatalErr(FatalError::CatastrophicError)
//!     }.into_result()
//! }
//!
//! #[derive(Debug)]
//! enum LocalError {
//!     SomeError,
//!     AnotherError,
//! }
//!
//! #[derive(Debug)]
//! enum FatalError {
//!     BigBadError,
//!     CatastrophicError,
//! }
//! ```
//! 
//! # Example using `--feature 'nightly'`
//!
//! ```ignore
//! # ignore this test until I figure out how to make doctests conditional on features.
//! use std::ops::Try;
//! use woe::Result::{self, Ok, LocalErr, FatalErr};
//! use std::result::{Result as StdResult, Result::Ok as StdOk, Result::Err as StdErr};
//!
//! fn main() {
//!     match do_thing() {
//!         StdOk(num) => println!("Got a number: {}", num),
//!         StdResult::Err(fatal_err) => eprintln!("Fatal error: {:?}", fatal_err),
//!     }
//! }
//!
//! fn do_thing() -> StdResult<i64, FatalError> {
//!     // `woe::Result` interoperates with `std::result::Result` without issue.
//!     let result = do_another_thing(5, 5)?;
//!
//!     // `result` has type `Result<i64, LocalError>`.
//!     match result {
//!         StdResult::Err(local_err) => {
//!             println!("Local error: {:?}", local_err);
//!             StdOk(i64::default())
//!         }
//!         StdOk(num) => StdOk(num),
//!     }
//! }
//!
//! fn do_another_thing(x: i64, y: i64) -> Result<i64, LocalError, FatalError> {
//!     // `woe::Result` works as expected using the `?` operator with itself.
//!     let result = do_third_thing(x, y)?;
//!     // `woe::Result::from_ok` takes in a `Result<T, L>` and returns a `woe::Result<T, L, F>`.
//!     Result::from_ok(result)
//! }
//!
//! fn do_third_thing(x: i64, y: i64) -> Result<i64, LocalError, FatalError> {
//!     if x > y {
//!         Ok(x)
//!     } else if x == y {
//!         LocalErr(LocalError::SomeError)
//!     } else {
//!         FatalErr(FatalError::CatastrophicError)
//!     }
//! }
//!
//! #[derive(Debug)]
//! enum LocalError {
//!     SomeError,
//!     AnotherError,
//! }
//!
//! #[derive(Debug)]
//! enum FatalError {
//!     BigBadError,
//!     CatastrophicError,
//! }
//! ```
//!
//! [post]: http://sled.rs/errors.html "Link to the blog post"

#[cfg(any(feature="from_iterator_trait", feature="product_trait", feature="sum_trait"))]
use crate::LoopState::{Break, Continue};
use crate::Result::{FatalErr, LocalErr, Ok};
use core::fmt::Debug;
use core::iter::{DoubleEndedIterator, FusedIterator, Iterator};
#[cfg(feature="from_iterator_trait")]
use core::iter::FromIterator;
#[cfg(feature="product_trait")]
use core::iter::Product;
#[cfg(feature="sum_trait")]
use core::iter::Sum;
#[cfg(feature="trusted_len")]
use core::iter::TrustedLen;
#[cfg(feature="try_trait")]
use core::ops::Try;
use core::ops::{Deref, DerefMut};
use core::result::{Result as StdResult, Result::Err as StdErr, Result::Ok as StdOk};
#[cfg(feature="either_methods")]
pub use either::Either;
#[cfg(feature="either_methods")]
use either::Either::{Left, Right};
#[cfg(feature="termination_trait")]
use std::process::{ExitCode, Termination};

/// A type representing success (`Ok`), a local error (`LocalErr`), or a fatal error (`FatalErr`).
#[derive(Copy, PartialEq, PartialOrd, Eq, Ord, Debug, Hash)]
pub enum Result<T, L, F> {
    Ok(T),
    LocalErr(L),
    FatalErr(F),
}

#[cfg(feature="try_trait")]
impl<T, L, F> Try for Result<T, L, F> {
    type Ok = StdResult<T, L>;
    type Error = F;

    fn into_result(self) -> StdResult<StdResult<T, L>, F> {
        match self {
            Ok(t) => StdOk(StdOk(t)),
            LocalErr(err) => StdOk(StdErr(err)),
            FatalErr(err) => StdErr(err),
        }
    }

    fn from_error(err: F) -> Self {
        FatalErr(err)
    }

    fn from_ok(ok: StdResult<T, L>) -> Self {
        match ok {
            StdOk(t) => Ok(t),
            StdErr(err) => LocalErr(err),
        }
    }
}

#[cfg(not(feature="try_trait"))]
impl<T, L, F> Result<T, L, F> {
    pub fn into_result(self) -> StdResult<StdResult<T, L>, F> {
        match self {
            Ok(t) => StdOk(StdOk(t)),
            LocalErr(err) => StdOk(StdErr(err)),
            FatalErr(err) => StdErr(err),
        }
    }

    pub fn from_error(err: F) -> Self {
        FatalErr(err)
    }

    pub fn from_ok(ok: StdResult<T, L>) -> Self {
        match ok {
            StdOk(t) => Ok(t),
            StdErr(err) => LocalErr(err),
        }
    }
}

impl<T: Default, L, F> Result<T, L, F> {
    pub fn into_result_default(self) -> StdResult<T, F> {
        match self {
            Ok(t) => StdOk(t),
            LocalErr(_) => StdOk(T::default()),
            FatalErr(err) => StdErr(err),
        }
    }
}

impl<T, L, F> Result<T, L, F> {
    pub fn is_ok(&self) -> bool {
        match self {
            Ok(_) => true,
            _ => false,
        }
    }

    pub fn is_err(&self) -> bool {
        !self.is_ok()
    }

    pub fn is_local_err(&self) -> bool {
        match self {
            LocalErr(_) => true,
            _ => false,
        }
    }

    pub fn is_fatal_err(&self) -> bool {
        match self {
            FatalErr(_) => true,
            _ => false,
        }
    }

    pub fn contains<U>(&self, x: &U) -> bool
    where
        U: PartialEq<T>,
    {
        match self {
            Ok(t) if *x == *t => true,
            _ => false,
        }
    }

    #[cfg(feature="either_methods")]
    pub fn contains_err<U, Y>(&self, e: Either<&U, &Y>) -> bool
    where
        U: PartialEq<L>,
        Y: PartialEq<F>,
    {
        match (self, e) {
            (LocalErr(err), Left(e)) if *e == *err => true,
            (FatalErr(err), Right(e)) if *e == *err => true,
            _ => false,
        }
    }

    pub fn contains_local_err<E>(&self, e: &E) -> bool
    where
        E: PartialEq<L>,
    {
        match self {
            LocalErr(err) if *e == *err => true,
            _ => false,
        }
    }

    pub fn contains_fatal_err<E>(&self, e: &E) -> bool
    where
        E: PartialEq<F>,
    {
        match self {
            FatalErr(err) if *e == *err => true,
            _ => false,
        }
    }

    pub fn ok(self) -> Option<T> {
        match self {
            Ok(t) => Some(t),
            _ => None,
        }
    }

    #[cfg(feature="either_methods")]
    pub fn err(self) -> Option<Either<L, F>> {
        match self {
            LocalErr(err) => Some(Left(err)),
            FatalErr(err) => Some(Right(err)),
            _ => None,
        }
    }

    pub fn local_err(self) -> Option<L> {
        match self {
            LocalErr(err) => Some(err),
            _ => None,
        }
    }

    pub fn fatal_err(self) -> Option<F> {
        match self {
            FatalErr(err) => Some(err),
            _ => None,
        }
    }

    pub fn as_ref(&self) -> Result<&T, &L, &F> {
        match self {
            Ok(t) => Ok(t),
            LocalErr(err) => LocalErr(err),
            FatalErr(err) => FatalErr(err),
        }
    }

    pub fn as_mut(&mut self) -> Result<&mut T, &mut L, &mut F> {
        match self {
            Ok(t) => Ok(t),
            LocalErr(err) => LocalErr(err),
            FatalErr(err) => FatalErr(err),
        }
    }

    pub fn map<U, S>(self, f: U) -> Result<S, L, F>
    where
        U: FnOnce(T) -> S,
    {
        match self {
            Ok(t) => Ok(f(t)),
            LocalErr(e) => LocalErr(e),
            FatalErr(e) => FatalErr(e),
        }
    }

    pub fn map_or<U, G>(self, default: U, f: G) -> U
    where
        G: FnOnce(T) -> U,
    {
        match self {
            Ok(t) => f(t),
            _ => default,
        }
    }

    pub fn map_or_else<U, LD, FD, G>(self, default_local: LD, default_fatal: FD, f: G) -> U
    where
        LD: FnOnce(L) -> U,
        FD: FnOnce(F) -> U,
        G: FnOnce(T) -> U,
    {
        match self {
            Ok(t) => f(t),
            LocalErr(err) => default_local(err),
            FatalErr(err) => default_fatal(err),
        }
    }

    #[cfg(feature="either_methods")]
    pub fn map_err<U, M, G>(self, f: U) -> Result<T, M, G>
    where
        U: FnOnce(Either<L, F>) -> Either<M, G>,
    {
        match self {
            Ok(t) => Ok(t),
            LocalErr(err) => match f(Left(err)) {
                Left(err) => LocalErr(err),
                Right(err) => FatalErr(err),
            },
            FatalErr(err) => match f(Right(err)) {
                Left(err) => LocalErr(err),
                Right(err) => FatalErr(err),
            },
        }
    }

    pub fn map_local_err<U, S>(self, f: U) -> Result<T, S, F>
    where
        U: FnOnce(L) -> S,
    {
        match self {
            Ok(t) => Ok(t),
            LocalErr(e) => LocalErr(f(e)),
            FatalErr(e) => FatalErr(e),
        }
    }

    pub fn map_fatal_err<U, S>(self, f: U) -> Result<T, L, S>
    where
        U: FnOnce(F) -> S,
    {
        match self {
            Ok(t) => Ok(t),
            LocalErr(e) => LocalErr(e),
            FatalErr(e) => FatalErr(f(e)),
        }
    }

    pub fn iter(&self) -> Iter<T> {
        let inner = match self {
            Ok(t) => Some(t),
            _ => None,
        };

        Iter { inner }
    }

    pub fn iter_mut(&mut self) -> IterMut<T> {
        let inner = match self {
            Ok(t) => Some(t),
            _ => None,
        };

        IterMut { inner }
    }

    pub fn and<U>(self, res: Result<U, L, F>) -> Result<U, L, F> {
        match self {
            Ok(_) => res,
            LocalErr(err) => LocalErr(err),
            FatalErr(err) => FatalErr(err),
        }
    }

    pub fn and_then<U, G>(self, op: G) -> Result<U, L, F>
    where
        G: FnOnce(T) -> Result<U, L, F>,
    {
        match self {
            Ok(t) => op(t),
            LocalErr(err) => LocalErr(err),
            FatalErr(err) => FatalErr(err),
        }
    }

    pub fn or<M, G>(
        self,
        res_local: Result<T, M, G>,
        res_fatal: Result<T, M, G>,
    ) -> Result<T, M, G> {
        match self {
            Ok(t) => Ok(t),
            LocalErr(_) => res_local,
            FatalErr(_) => res_fatal,
        }
    }

    pub fn or_local<M>(self, res: Result<T, M, F>) -> Result<T, M, F> {
        match self {
            Ok(t) => Ok(t),
            LocalErr(_) => res,
            FatalErr(err) => FatalErr(err),
        }
    }

    pub fn or_fatal<G>(self, res: Result<T, L, G>) -> Result<T, L, G> {
        match self {
            Ok(t) => Ok(t),
            LocalErr(err) => LocalErr(err),
            FatalErr(_) => res,
        }
    }

    pub fn or_else<O, P, M, G>(self, op_local: O, op_fatal: P) -> Result<T, M, G>
    where
        O: FnOnce(L) -> Result<T, M, G>,
        P: FnOnce(F) -> Result<T, M, G>,
    {
        match self {
            Ok(t) => Ok(t),
            LocalErr(err) => op_local(err),
            FatalErr(err) => op_fatal(err),
        }
    }

    pub fn or_else_local<O, M>(self, op: O) -> Result<T, M, F>
    where
        O: FnOnce(L) -> Result<T, M, F>,
    {
        match self {
            Ok(t) => Ok(t),
            LocalErr(err) => op(err),
            FatalErr(err) => FatalErr(err),
        }
    }

    pub fn or_else_fatal<O, G>(self, op: O) -> Result<T, L, G>
    where
        O: FnOnce(F) -> Result<T, L, G>,
    {
        match self {
            Ok(t) => Ok(t),
            LocalErr(err) => LocalErr(err),
            FatalErr(err) => op(err),
        }
    }

    pub fn unwrap_or(self, optb: T) -> T {
        match self {
            Ok(t) => t,
            _ => optb,
        }
    }

    pub fn unwrap_or_else<M, G>(self, local_op: M, fatal_op: G) -> T
    where
        M: FnOnce(L) -> T,
        G: FnOnce(F) -> T,
    {
        match self {
            Ok(t) => t,
            LocalErr(err) => local_op(err),
            FatalErr(err) => fatal_op(err),
        }
    }
}

impl<'a, T, L, F> Result<&'a T, L, F>
where
    T: Copy,
{
    pub fn copied(self) -> Result<T, L, F> {
        match self {
            Ok(t) => Ok(*t),
            LocalErr(err) => LocalErr(err),
            FatalErr(err) => FatalErr(err),
        }
    }
}

impl<'a, T, L, F> Result<&'a mut T, L, F>
where
    T: Copy,
{
    pub fn copied(self) -> Result<T, L, F> {
        match self {
            Ok(t) => Ok(*t),
            LocalErr(err) => LocalErr(err),
            FatalErr(err) => FatalErr(err),
        }
    }
}

impl<'a, T, L, F> Result<&'a T, L, F>
where
    T: Clone,
{
    pub fn cloned(self) -> Result<T, L, F> {
        match self {
            Ok(t) => Ok(t.clone()),
            LocalErr(err) => LocalErr(err),
            FatalErr(err) => FatalErr(err),
        }
    }
}

impl<'a, T, L, F> Result<&'a mut T, L, F>
where
    T: Clone,
{
    pub fn cloned(self) -> Result<T, L, F> {
        match self {
            Ok(t) => Ok(t.clone()),
            LocalErr(err) => LocalErr(err),
            FatalErr(err) => FatalErr(err),
        }
    }
}

impl<T, L, F> Result<T, L, F>
where
    L: Debug,
    F: Debug,
{
    pub fn unwrap(self) -> T {
        match self {
            Ok(t) => t,
            LocalErr(err) => panic!("{:?}", err),
            FatalErr(err) => panic!("{:?}", err),
        }
    }

    pub fn expect(self, msg: &str) -> T {
        match self {
            Ok(t) => t,
            LocalErr(_) => panic!("{}", msg),
            FatalErr(_) => panic!("{}", msg),
        }
    }
}

#[cfg(feature="either_methods")]
impl<T, L, F> Result<T, L, F>
where
    T: Debug,
    L: Debug,
    F: Debug,
{
    pub fn unwrap_err(self) -> Either<L, F> {
        match self {
            Ok(t) => panic!("{:?}", t),
            LocalErr(err) => Left(err),
            FatalErr(err) => Right(err),
        }
    }

    pub fn expect_err(self, msg: &str) -> Either<L, F> {
        match self {
            Ok(_) => panic!("{}", msg),
            LocalErr(err) => Left(err),
            FatalErr(err) => Right(err),
        }
    }
}

impl<T, L, F> Result<T, L, F>
where
    T: Debug,
    F: Debug,
{
    pub fn unwrap_local_err(self) -> L {
        match self {
            Ok(t) => panic!("{:?}", t),
            LocalErr(err) => err,
            FatalErr(err) => panic!("{:?}", err),
        }
    }

    pub fn expect_local_err(self, msg: &str) -> L {
        match self {
            Ok(_) => panic!("{}", msg),
            LocalErr(err) => err,
            FatalErr(_) => panic!("{}", msg),
        }
    }
}

impl<T, L, F> Result<T, L, F>
where
    T: Debug,
    L: Debug,
{
    pub fn unwrap_fatal_err(self) -> F {
        match self {
            Ok(t) => panic!("{:?}", t),
            LocalErr(err) => panic!("{:?}", err),
            FatalErr(err) => err,
        }
    }

    pub fn expect_fatal_err(self, msg: &str) -> F {
        match self {
            Ok(_) => panic!("{}", msg),
            LocalErr(_) => panic!("{}", msg),
            FatalErr(err) => err,
        }
    }
}

impl<T, L, F> Result<T, L, F>
where
    T: Default,
{
    pub fn unwrap_or_default(self) -> T {
        match self {
            Ok(t) => t,
            _ => T::default(),
        }
    }
}

#[cfg(feature="never_type")]
impl<T, L, F> Result<T, L, F>
where
    L: Into<!>,
    F: Into<!>,
{
    pub fn into_ok(self) -> T {
        match self {
            Ok(t) => t,
            LocalErr(err) => err.into(),
            FatalErr(err) => err.into(),
        }
    }
}

impl<T, L, F> Result<T, L, F>
where
    T: Deref,
{
    pub fn as_deref(&self) -> Result<&<T as Deref>::Target, &L, &F> {
        match self {
            Ok(t) => Ok(t.deref()),
            LocalErr(err) => LocalErr(err),
            FatalErr(err) => FatalErr(err),
        }
    }
}

impl<T, L, F> Result<T, L, F>
where
    L: Deref,
    F: Deref,
{
    pub fn as_deref_err(&self) -> Result<&T, &<L as Deref>::Target, &<F as Deref>::Target> {
        match self {
            Ok(t) => Ok(t),
            LocalErr(err) => LocalErr(err.deref()),
            FatalErr(err) => FatalErr(err.deref()),
        }
    }
}

impl<T, L, F> Result<T, L, F>
where
    L: Deref,
{
    pub fn as_deref_local_err(&self) -> Result<&T, &<L as Deref>::Target, &F> {
        match self {
            Ok(t) => Ok(t),
            LocalErr(err) => LocalErr(err.deref()),
            FatalErr(err) => FatalErr(err),
        }
    }
}

impl<T, L, F> Result<T, L, F>
where
    F: Deref,
{
    pub fn as_deref_fatal_err(&self) -> Result<&T, &L, &<F as Deref>::Target> {
        match self {
            Ok(t) => Ok(t),
            LocalErr(err) => LocalErr(err),
            FatalErr(err) => FatalErr(err.deref()),
        }
    }
}

impl<T, L, F> Result<T, L, F>
where
    T: DerefMut,
{
    pub fn as_deref_mut(&mut self) -> Result<&mut <T as Deref>::Target, &mut L, &mut F> {
        match self {
            Ok(t) => Ok(t.deref_mut()),
            LocalErr(err) => LocalErr(err),
            FatalErr(err) => FatalErr(err),
        }
    }
}

impl<T, L, F> Result<T, L, F>
where
    L: DerefMut,
    F: DerefMut,
{
    pub fn as_deref_mut_err(
        &mut self,
    ) -> Result<&mut T, &mut <L as Deref>::Target, &mut <F as Deref>::Target> {
        match self {
            Ok(t) => Ok(t),
            LocalErr(err) => LocalErr(err.deref_mut()),
            FatalErr(err) => FatalErr(err.deref_mut()),
        }
    }
}

impl<T, L, F> Result<T, L, F>
where
    L: DerefMut,
{
    pub fn as_deref_mut_local_err(&mut self) -> Result<&mut T, &mut <L as Deref>::Target, &mut F> {
        match self {
            Ok(t) => Ok(t),
            LocalErr(err) => LocalErr(err.deref_mut()),
            FatalErr(err) => FatalErr(err),
        }
    }
}

impl<T, L, F> Result<T, L, F>
where
    F: DerefMut,
{
    pub fn as_deref_mut_fatal_err(&mut self) -> Result<&mut T, &mut L, &mut <F as Deref>::Target> {
        match self {
            Ok(t) => Ok(t),
            LocalErr(err) => LocalErr(err),
            FatalErr(err) => FatalErr(err.deref_mut()),
        }
    }
}

impl<T, L, F> Result<Option<T>, L, F> {
    pub fn transpose(self) -> Option<Result<T, L, F>> {
        match self {
            Ok(Some(t)) => Some(Ok(t)),
            Ok(None) => None,
            LocalErr(err) => Some(LocalErr(err)),
            FatalErr(err) => Some(FatalErr(err)),
        }
    }
}

impl<T, L, F> Clone for Result<T, L, F>
where
    T: Clone,
    L: Clone,
    F: Clone,
{
    fn clone(&self) -> Result<T, L, F> {
        match self {
            Ok(t) => Ok(t.clone()),
            LocalErr(err) => LocalErr(err.clone()),
            FatalErr(err) => FatalErr(err.clone()),
        }
    }

    fn clone_from(&mut self, source: &Result<T, L, F>) {
        match (self, source) {
            (Ok(to), Ok(from)) => to.clone_from(from),
            (LocalErr(to), LocalErr(from)) => to.clone_from(from),
            (FatalErr(to), FatalErr(from)) => to.clone_from(from),
            (to, from) => *to = from.clone(),
        }
    }
}

#[cfg(feature="from_iterator_trait")]
impl<A, V, L, F> FromIterator<Result<A, L, F>> for Result<V, L, F>
where
    V: FromIterator<A>,
{
    fn from_iter<I>(iter: I) -> Result<V, L, F>
    where
        I: IntoIterator<Item = Result<A, L, F>>,
    {
        process_results(iter.into_iter(), |i| i.collect())
    }
}

impl<'a, T, L, F> IntoIterator for &'a mut Result<T, L, F> {
    type Item = &'a mut T;
    type IntoIter = IterMut<'a, T>;

    fn into_iter(self) -> IterMut<'a, T> {
        self.iter_mut()
    }
}

impl<'a, T, L, F> IntoIterator for &'a Result<T, L, F> {
    type Item = &'a T;
    type IntoIter = Iter<'a, T>;

    fn into_iter(self) -> Iter<'a, T> {
        self.iter()
    }
}

impl<T, L, F> IntoIterator for Result<T, L, F> {
    type Item = T;
    type IntoIter = IntoIter<T>;

    fn into_iter(self) -> IntoIter<T> {
        IntoIter { inner: self.ok() }
    }
}

#[cfg(feature="product_trait")]
impl<T, U, L, F> Product<Result<U, L, F>> for Result<T, L, F>
where
    T: Product<U>,
{
    fn product<I>(iter: I) -> Result<T, L, F>
    where
        I: Iterator<Item = Result<U, L, F>>,
    {
        process_results(iter, |i| i.product())
    }
}

#[cfg(feature="sum_trait")]
impl<T, U, L, F> Sum<Result<U, L, F>> for Result<T, L, F>
where
    T: Sum<U>,
{
    fn sum<I>(iter: I) -> Result<T, L, F>
    where
        I: Iterator<Item = Result<U, L, F>>,
    {
        process_results(iter, |i| i.sum())
    }
}

#[cfg(feature="termination_trait")]
impl<L, F> Termination for Result<(), L, F>
where
    L: Debug,
    F: Debug,
{
    fn report(self) -> i32 {
        match self {
            Ok(()) => ().report(),
            LocalErr(err) => LocalErr::<!, L, F>(err).report(),
            FatalErr(err) => FatalErr::<!, L, F>(err).report(),
        }
    }
}

#[cfg(feature="termination_trait")]
impl<L, F> Termination for Result<!, L, F>
where
    L: Debug,
    F: Debug,
{
    fn report(self) -> i32 {
        match self {
            LocalErr(err) => {
                eprintln!("Error: {:?}", err);
                ExitCode::FAILURE.report()
            }
            FatalErr(err) => {
                eprintln!("Error: {:?}", err);
                ExitCode::FAILURE.report()
            }
            Ok(t) => t,
        }
    }
}

/// An iterator over the value in an `Ok` variant of a `woe::Result`.
#[derive(Debug)]
pub struct IntoIter<T> {
    inner: Option<T>,
}

impl<T> Iterator for IntoIter<T> {
    type Item = T;

    #[inline]
    fn next(&mut self) -> Option<T> {
        self.inner.take()
    }
}

/// An iterator over a reference to the `Ok` variant of a `woe::Result`.
#[derive(Debug)]
pub struct Iter<'a, T: 'a> {
    inner: Option<&'a T>,
}

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = &'a T;

    #[inline]
    fn next(&mut self) -> Option<&'a T> {
        self.inner.take()
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let n = if self.inner.is_some() { 1 } else { 0 };
        (n, Some(n))
    }
}

impl<'a, T> DoubleEndedIterator for Iter<'a, T> {
    #[inline]
    fn next_back(&mut self) -> Option<&'a T> {
        self.inner.take()
    }
}

impl<'a, T> FusedIterator for Iter<'a, T> {}

#[cfg(feature="trusted_len")]
unsafe impl<'a, T> TrustedLen for Iter<'a, T> {}

/// An iterator over a mutable reference to the `Ok` variant of a `woe::Result`.
#[derive(Debug)]
pub struct IterMut<'a, T: 'a> {
    inner: Option<&'a mut T>,
}

impl<'a, T> Iterator for IterMut<'a, T> {
    type Item = &'a mut T;

    #[inline]
    fn next(&mut self) -> Option<&'a mut T> {
        self.inner.take()
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let n = if self.inner.is_some() { 1 } else { 0 };
        (n, Some(n))
    }
}

impl<'a, T> DoubleEndedIterator for IterMut<'a, T> {
    #[inline]
    fn next_back(&mut self) -> Option<&'a mut T> {
        self.inner.take()
    }
}

impl<'a, T> FusedIterator for IterMut<'a, T> {}

#[cfg(feature="trusted_len")]
unsafe impl<'a, T> TrustedLen for IterMut<'a, T> {}

#[cfg(any(feature="from_iterator_trait", feature="product_trait", feature="sum_trait"))]
pub(crate) struct ResultShunt<'a, I, L, F> {
    iter: I,
    error: &'a mut Result<(), L, F>,
}

#[cfg(any(feature="from_iterator_trait", feature="product_trait", feature="sum_trait"))]
pub(crate) fn process_results<I, T, L, F, G, U>(iter: I, mut f: G) -> Result<U, L, F>
where
    I: Iterator<Item = Result<T, L, F>>,
    for<'a> G: FnMut(ResultShunt<'a, I, L, F>) -> U,
{
    let mut error = Ok(());
    let shunt = ResultShunt {
        iter,
        error: &mut error,
    };
    let value = f(shunt);
    error.map(|()| value)
}

#[cfg(any(feature="from_iterator_trait", feature="product_trait", feature="sum_trait"))]
impl<I, T, L, F> Iterator for ResultShunt<'_, I, L, F>
where
    I: Iterator<Item = Result<T, L, F>>,
{
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        self.find(|_| true)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        if self.error.is_err() {
            (0, Some(0))
        } else {
            let (_, upper) = self.iter.size_hint();
            (0, upper)
        }
    }

    fn try_fold<B, G, R>(&mut self, init: B, mut f: G) -> R
    where
        G: FnMut(B, Self::Item) -> R,
        R: Try<Ok = B>,
    {
        let error = &mut *self.error;
        self.iter
            .try_fold(init, |acc, x| match x {
                Ok(x) => LoopState::from_try(f(acc, x)),
                LocalErr(e) => {
                    *error = LocalErr(e);
                    Break(Try::from_ok(acc))
                }
                FatalErr(e) => {
                    *error = FatalErr(e);
                    Break(Try::from_ok(acc))
                }
            })
            .into_try()
    }
}

#[cfg(any(feature="from_iterator_trait", feature="product_trait", feature="sum_trait"))]
#[derive(PartialEq)]
enum LoopState<C, B> {
    Continue(C),
    Break(B),
}

#[cfg(any(feature="from_iterator_trait", feature="product_trait", feature="sum_trait"))]
impl<C, B> Try for LoopState<C, B> {
    type Ok = C;
    type Error = B;

    #[inline]
    fn into_result(self) -> StdResult<Self::Ok, Self::Error> {
        match self {
            Continue(y) => StdOk(y),
            Break(x) => StdErr(x),
        }
    }

    #[inline]
    fn from_error(v: Self::Error) -> Self {
        Break(v)
    }

    #[inline]
    fn from_ok(v: Self::Ok) -> Self {
        Continue(v)
    }
}

#[cfg(any(feature="from_iterator_trait", feature="product_trait", feature="sum_trait"))]
impl<R: Try> LoopState<R::Ok, R> {
    #[inline]
    fn from_try(r: R) -> Self {
        match Try::into_result(r) {
            StdOk(v) => Continue(v),
            StdErr(v) => Break(Try::from_error(v)),
        }
    }

    #[inline]
    fn into_try(self) -> R {
        match self {
            Continue(v) => Try::from_ok(v),
            Break(v) => v,
        }
    }
}
