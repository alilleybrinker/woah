// SPDX-License-Identifier: MIT OR Apache-2.0

//! `woah` is a Rust crate which provides the following type:
//!
//! ```text
//! enum Result<T, L, F> {
//!     Success(T),
//!     LocalErr(L),
//!     FatalErr(F),
//! }
//! ```
//!
//! This type differentiates between "local errors" which can be handled and "fatal errors" which can't, to
//! enable the error handling pattern described by Tyler Neely (@spacejam) in the blog post ["Error Handling
//! in a Correctness-Critical Rust Project"][post]. `woah::Result` is intended to be a more ergonomic
//! alternative to the `Result<Result<T, LocalError>, FatalError>` type proposed in the post.
//!
//! The important thing to note is that using the question mark operator on `woah::Result` causes
//! any `FatalError` to propagate up, while providing `Result<T, LocalError>` otherwise, to enable
//! the local code to handle local errors without propagating them.
//!
//! [__For more details, read the `docs` module.__][docs]
//!
//! [post]: http://sled.rs/errors.html "Link to the blog post"
//! [docs]: docs/index.html "Link to the docs module"

#![doc(issue_tracker_base_url = "https://github.com/alilleybrinker/woah/issues/")]
#![cfg_attr(not(feature = "std"), no_std)]
// Turn on the `Try` trait for both code and documentation tests.
#![cfg_attr(feature = "nightly", feature(try_trait_v2))]
#![cfg_attr(feature = "nightly", feature(try_blocks))]
#![cfg_attr(feature = "nightly", feature(control_flow_enum))]
#![cfg_attr(feature = "nightly", feature(trusted_len))]
#![cfg_attr(feature = "nightly", feature(never_type))]
#![cfg_attr(feature = "nightly", doc(test(attr(feature(try_trait_v2)))))]
#![cfg_attr(feature = "nightly", doc(test(attr(feature(try_blocks)))))]
#![cfg_attr(feature = "nightly", doc(test(attr(feature(control_flow_enum)))))]
#![cfg_attr(feature = "nightly", doc(test(attr(feature(trusted_len)))))]
#![cfg_attr(feature = "nightly", doc(test(attr(feature(never_type)))))]
// Turn on clippy lints.
#![deny(clippy::all)]
#![deny(clippy::cargo)]
// Turn on useful warnings (make `deny` once all are resolved.)
//#![warn(missing_docs)]
//#![warn(missing_doc_code_examples)]
//#![warn(private_doc_tests)]
#![warn(missing_debug_implementations)]
#![warn(missing_copy_implementations)]

use crate::Result::{FatalErr, LocalErr, Success};
#[cfg(feature = "nightly")]
use core::convert::Infallible;
use core::convert::{From, Into};
use core::fmt::Debug;
#[cfg(feature = "nightly")]
use core::iter::FromIterator;
#[cfg(feature = "nightly")]
use core::iter::Product;
#[cfg(feature = "nightly")]
use core::iter::Sum;
#[cfg(feature = "nightly")]
use core::iter::TrustedLen;
use core::iter::{DoubleEndedIterator, FusedIterator, Iterator};
#[cfg(feature = "nightly")]
use core::ops::ControlFlow;
use core::ops::{Deref, DerefMut};
#[cfg(feature = "nightly")]
use core::ops::{FromResidual, Try};
use core::result::{Result as StdResult, Result::Err, Result::Ok};
#[cfg(feature = "either")]
use either::Either::{self, Left, Right};
#[cfg(feature = "serde")]
use serde::{Deserialize, Deserializer, Serialize, Serializer};
#[cfg(feature = "std")]
use std::process::{ExitCode, Termination};

pub mod prelude {
    //! A collection of re-exports to make `woah::Result` the standard result type.
    //!
    //! This keeps `std::result::Result` available as `StdResult`, and imports additional types and traits
    //! to make `woah::Result` fully-featured, based on feature flags.

    // Replace `std::result::Result` with `woah::Result`.
    //
    // This also imports the variant names for `woah::Result`, so they can be
    // referenced directly.
    pub use crate::{Result, Result::FatalErr, Result::LocalErr, Result::Success};
    pub use core::result::Result as StdResult;

    // Import the Try and FromResidual traits.
    #[cfg(feature = "nightly")]
    pub use core::ops::{FromResidual, Try};

    // Import the ControlFlow struct.
    #[cfg(feature = "nightly")]
    pub use core::ops::ControlFlow;

    // Import the Termination trait.
    #[cfg(feature = "std")]
    pub use std::process::Termination;

    // Import the FromIterator trait.
    #[cfg(feature = "nightly")]
    pub use core::iter::FromIterator;

    // Import the Product trait.
    #[cfg(feature = "nightly")]
    pub use core::iter::Product;

    // Import the Sum trait.
    #[cfg(feature = "nightly")]
    pub use core::iter::Sum;

    // Import the TrustedLen trait.
    #[cfg(feature = "nightly")]
    pub use core::iter::TrustedLen;
}

pub mod docs {
    //! Documentation, including crate features and examples.
    //!
    //! ## Why are the docs like this?
    //!
    //! Putting the docs in Rustdoc means they can be run as documentation tests. Breaking them up into modules
    //! helps keep them from getting too unwieldy, so people can still navigate the API itself with ease.
    //!
    //! `woah::Result` has a lot of methods, and the way they're grouped and presented by Rustdoc isn't always
    //! easy to navigate. To help, this page explains them in groups of similar methods.
    //!
    //! [is]: #see-if-the-result-is-a-particular-variant
    //! [contains]: #see-if-the-result-contains-a-value
    //! [get]: #get-an-option-if-a-variant-is-present
    //! [as_ref]: #reference-the-contained-value
    //! [as_deref]: #dereference-the-contained-value
    //! [map]: #map-over-the-contained-value
    //! [iter]: #iterate-over-the-contained-value
    //! [compose]: #compose-results
    //! [unwrap]: #unwrap-the-result
    //! [clone]: #copy-or-clone-the-contained-value
    //! [transpose]: #transpose-when-holding-an-option
    //! [convert]: #convert-to-and-from-a-stdresultresult
    //! [try]: #use-woahresult-with-the-question-mark-operator
    //! [main]: #use-woahresult-as-the-return-type-of-main
    //! [from_iter]: #build-a-woahresult-from-an-iterator
    //!
    //! ## Methods
    //!
    //! ### See if the `Result` is a particular variant
    //!
    //! These methods, the "is" methods, return a `bool` based on what variant is present.
    //!
    //! 1. [`is_success`](../../enum.Result.html#method.is_success)
    //! 2. [`is_err`](../../enum.Result.html#method.is_err)
    //! 3. [`is_local_err`](../../enum.Result.html#method.is_local_err)
    //! 4. [`is_fatal_err`](../../enum.Result.html#method.is_fatal_err)
    //!
    //! ### See if the `Result` contains a value
    //!
    //! These methods check if the `Result` contains a particular value.
    //!
    //! 1. [`contains`](../../enum.Result.html#method.contains)
    //! 2. [`contains_err`](../../enum.Result.html#method.contains_err)
    //! 3. [`contains_local_err`](../../enum.Result.html#method.contains_local_err)
    //! 4. [`contains_fatal_err`](../../enum.Result.html#method.contains_fatal_err)
    //!
    //! ### Get an `Option` if a variant is present
    //!
    //! These methods try to get the contained value out, returning an `Option` in case it's
    //! another variant.
    //!
    //! 1. [`success`](../../enum.Result.html#method.success)
    //! 2. [`err`](../../enum.Result.html#method.err)
    //! 3. [`local_err`](../../enum.Result.html#method.local_err)
    //! 4. [`fatal_err`](../../enum.Result.html#method.fatal_err)
    //!
    //! ### Reference the contained value
    //!
    //! Gets a reference (immutable or mutable) to the contained value.
    //!
    //! 1. [`as_ref`](../../enum.Result.html#method.as_ref)
    //! 2. [`as_mut`](../../enum.Result.html#method.as_mut)
    //!
    //! ### Dereference the contained value
    //!
    //! Dereferences the contained value if it implements `Deref`.
    //!
    //! 1. [`as_deref`](../../enum.Result.html#method.as_deref)
    //! 2. [`as_deref_err`](../../enum.Result.html#method.as_deref_err)
    //! 3. [`as_deref_local_err`](../../enum.Result.html#method.as_deref_local_err)
    //! 4. [`as_deref_fatal_err`](../../enum.Result.html#method.as_deref_fatal_err)
    //!
    //! Dereferences the contained value mutably if it implements `DerefMut`.
    //!
    //! 1. [`as_deref_mut`](../../enum.Result.html#method.as_deref_mut)
    //! 2. [`as_deref_mut_err`](../../enum.Result.html#method.as_deref_mut_err)
    //! 3. [`as_deref_mut_local_err`](../../enum.Result.html#method.as_deref_mut_local_err)
    //! 4. [`as_deref_mut_fatal_err`](../../enum.Result.html#method.as_deref_mut_fatal_err)
    //!
    //! ### Map over the contained value
    //!
    //! Applies some function to the contained value.
    //!
    //! 1. [`map`](../../enum.Result.html#method.map)
    //! 2. [`map_or`](../../enum.Result.html#method.map_or)
    //! 3. [`map_or_else`](../../enum.Result.html#method.map_or_else)
    //!
    //! Applies some function to the contained value, if it's a local or fatal error.
    //!
    //! 1. [`map_err`](../../enum.Result.html#method.map_err)
    //! 2. [`map_err_or`](../../enum.Result.html#method.map_err_or)
    //! 3. [`map_err_or_else`](../../enum.Result.html#method.map_err_or_else)
    //!
    //! Applies some function to the contained value, if it's a local error.
    //!
    //! 1. [`map_local_err`](../../enum.Result.html#method.map_local_err)
    //! 2. [`map_local_err_or`](../../enum.Result.html#method.map_local_err_or)
    //! 3. [`map_local_err_or_else`](../../enum.Result.html#method.map_local_err_or_else)
    //!
    //! Applies some function to the contained value, if it's a fatal error.
    //!
    //! 1. [`map_fatal_err`](../../enum.Result.html#method.map_fatal_err)
    //! 2. [`map_fatal_err_or`](../../enum.Result.html#method.map_fatal_err_or)
    //! 3. [`map_fatal_err_or_else`](../../enum.Result.html#method.map_fatal_err_or_else)
    //!
    //! ### Iterate over the contained value
    //!
    //! 1. [`iter`](../../enum.Result.html#method.iter)
    //! 2. [`iter_mut`](../../enum.Result.html#method.iter_mut)
    //! 3. [`into_iter`](../../enum.Result.html#impl-IntoIterator-2) (for `woah::Result`)
    //! 4. [`into_iter`](../../enum.Result.html#impl-IntoIterator-1) (for `&woah::Result`)
    //! 5. [`into_iter`](../../enum.Result.html#impl-IntoIterator) (for `&mut woah::Result`)
    //!
    //! ### Compose `Result`s
    //!
    //! 1. [`and`](../../enum.Result.html#method.and)
    //! 2. [`and_then`](../../enum.Result.html#method.and_then)
    //! 3. [`or`](../../enum.Result.html#method.or)
    //! 4. [`or_else`](../../enum.Result.html#method.or_else)
    //! 5. [`or_else_fatal`](../../enum.Result.html#method.or_else_fatal)
    //! 6. [`or_else_local`](../../enum.Result.html#method.or_else_local)
    //! 7. [`or_fatal`](../../enum.Result.html#method.or_fatal)
    //! 8. [`or_local`](../../enum.Result.html#method.or_local)
    //!
    //! ### Unwrap the `Result`
    //!
    //! 1. [`unwrap`](../../enum.Result.html#method.unwrap)
    //! 2. [`unwrap_err`](../../enum.Result.html#method.unwrap_err)
    //! 3. [`unwrap_fatal_err`](../../enum.Result.html#method.unwrap_fatal_err)
    //! 4. [`unwrap_local_err`](../../enum.Result.html#method.unwrap_local_err)
    //! 5. [`unwrap_or`](../../enum.Result.html#method.unwrap_or)
    //! 6. [`unwrap_or_default`](../../enum.Result.html#method.unwrap_or_default)
    //! 7. [`unwrap_or_else`](../../enum.Result.html#method.unwrap_or_else)
    //! 8. [`expect`](../../enum.Result.html#method.expect)
    //! 9. [`expect_err`](../../enum.Result.html#method.expect_err)
    //! 10. [`expect_fatal_err`](../../enum.Result.html#method.expect_fatal_err)
    //! 11. [`expect_local_err`](../../enum.Result.html#method.expect_local_err)
    //!
    //! ### Copy or clone the contained value
    //!
    //! 1. [`cloned`](../../enum.Result.html#method.cloned) (for `&woah::Result`)
    //! 2. [`cloned`](../../enum.Result.html#method.cloned-1) (for `&mut woah::Result`)
    //! 1. [`copied`](../../enum.Result.html#method.copied) (for `&woah::Result`)
    //! 2. [`copied`](../../enum.Result.html#method.copied-1) (for `&mut woah::Result`)
    //!
    //! ### Transpose when holding an `Option`
    //!
    //! 1. [`transpose`](../../enum.Result.html#method.transpose)
    //!
    //! ### Convert to and from a `std::result::Result`
    //!
    //! 1. [`into_result`](../../enum.Result.html#method.into_result)
    //! 1. [`into_result_default`](../../enum.Result.html#method.into_result_default)
    //!
    //! ### Use `woah::Result` with the question mark operator
    //!
    //! 1. [`Try` impl](../../enum.Result.html#impl-Try) (nightly-only, with `nightly` feature or `try_trait` feature)
    //!
    //! ### Use `woah::Result` as the return type of `main`
    //!
    //! 1. [`Termination` impl](../../enum.Result.html#impl-Termination) (nightly-only, with `nightly` feature, or `termination_trait` and `std` features)
    //!
    //! ### Build a `woah::Result` from an iterator
    //!
    //! 1. [`FromIterator` impl](../../enum.Result.html#impl-FromIterator%3CResult%3CA%2C%20L%2C%20F%3E%3E) (nightly-only, with `nightly` feature, or `from_iterator_trait` feature)
    //!
    //! ## Features
    //!
    //! `woah` can be used on stable or nightly. On nightly, enabling the `nightly` feature is recommended,
    //! to get the full power of the `woah::Result` type, including:
    //!
    //! * Being able to use it with the question mark operator,
    //! * Being able to make it the return type of `fn main`,
    //! * Gaining a number of useful additional methods, including `from_iter` (which enables easy conversion
    //!   from `Vec<woah::Result<T, L, F>` into `woah::Result<Vec<T>, L, F>` via the `collect` method).
    //!
    //! The following table is the full list of features. If you want to use `woah` without any dependencies,
    //! you can disable the `either` feature, which otherwise imports the `either` crate to add additional
    //! methods.
    //!
    //!| Feature Name  | Channels              | Depends On         | What It Does |
    //!|:--------------|:----------------------|:-------------------|:-------------|
    //!| `default`     | Stable, Beta, Nightly | `either`           | Enables default features (currently `either` and `std`). |
    //!| `nightly`     | Nightly               | None               | Enables all nightly-only features. __This feature is permanently unstable, and changes to the APIs enabled by this feature are never considered breaking changes.__ |
    //!| `serde`       | Stable, Beta, Nightly | None               | Implements `serde::Serialize` and `serde::Deserialize` for `woah::Result`. |
    //!| `std`         | Stable, Beta, Nightly | None               | Use the standard library. Turn off to make the crate `no_std` compatible. _Turning off the standard library eliminates the `Termination` trait and `ExitCode` type._ |
    //!| `either`      | Stable, Beta, Nightly | None               | Adds the `either` crate as a dependency and provides convenience methods for operating on `Either<LocalErr, FatalErr>`. |
    //!
    //!
    //! ## Examples
    //!
    //! Examples of using `woah` on both stable and nightly.
    //!
    //! ### Example on stable
    //!
    //!```
    //! use woah::prelude::*;
    //! use std::cmp::Ordering;
    //!
    //! match get_number() {
    //!     Ok(num) => println!("Got a number: {}", num),
    //!     StdResult::Err(fatal_err) => eprintln!("Fatal error: {:?}", fatal_err),
    //! }
    //!
    //! fn get_number() -> StdResult<i64, FatalError> {
    //!     // propagate any fatal error
    //!     let result: StdResult<i64, LocalError> = compare_numbers(5, 5)?;
    //!
    //!     // handle any local error
    //!     let num = result.unwrap_or_else(|local_err| {
    //!         println!("Local error: {:?}", local_err);
    //!         i64::default()
    //!     });
    //!
    //!     Ok(num)
    //! }
    //!
    //! fn compare_numbers(x: i64, y: i64) -> StdResult<StdResult<i64, LocalError>, FatalError> {
    //!     match x.cmp(&y) {
    //!         Ordering::Greater => Success(x),
    //!         Ordering::Equal => LocalErr(LocalError::SomeError),
    //!         Ordering::Less => FatalErr(FatalError::CatastrophicError),
    //!     }.into_result()
    //! }
    //!
    //! #[derive(Debug)]
    //! enum LocalError { SomeError, AnotherError }
    //!
    //! #[derive(Debug)]
    //! enum FatalError { BigBadError, CatastrophicError }
    //! ```
    //!
    //! ### Example on nightly
    //!
    //! This uses `--features nightly` to enable nightly-only features.
    //!
    //! ```
    //! use woah::prelude::*;
    //! use std::cmp::Ordering;
    //!
    //! # #[cfg(feature = "nightly")]
    //! # fn main() {
    //! match get_number() {
    //!     Ok(num) => println!("Got a number: {}", num),
    //!     StdResult::Err(fatal_err) => eprintln!("Fatal error: {:?}", fatal_err),
    //! }
    //! # }
    //! #
    //! # #[cfg(not(feature = "nightly"))]
    //! # fn main() {}
    //!
    //! # #[cfg(feature = "nightly")]
    //! fn get_number() -> StdResult<i64, FatalError> {
    //!     // propagate any fatal error
    //!     let result: StdResult<i64, LocalError> = compare_numbers(5, 10)?;
    //!
    //!     // handle any local error
    //!     let num = result.unwrap_or_else(|local_err| {
    //!         println!("Local error: {:?}", local_err);
    //!         i64::default()
    //!     });
    //!
    //!     Ok(num)
    //! }
    //!
    //! # #[cfg(feature = "nightly")]
    //! fn compare_numbers(x: i64, y: i64) -> Result<i64, LocalError, FatalError> {
    //!     match x.cmp(&y) {
    //!         Ordering::Greater => Success(x),
    //!         Ordering::Equal => LocalErr(LocalError::Equal),
    //!         Ordering::Less => FatalErr(FatalError::Less),
    //!     }
    //! }
    //!
    //! # #[cfg(feature = "nightly")]
    //! #[derive(Debug)]
    //! enum LocalError { Equal }
    //!
    //! # #[cfg(feature = "nightly")]
    //! #[derive(Debug)]
    //! enum FatalError { Less }
    //! ```
}

/// A type representing success (`Success`), a local error (`LocalErr`), or a fatal error (`FatalErr`).
///
/// See the [`woah`](index.html) top-level documentation for details.
#[derive(Copy, PartialEq, PartialOrd, Eq, Ord, Debug, Hash)]
#[must_use = "this `Result` may be a `LocalErr`, which should be handled, or a `FatalErr`, which should be propagated"]
pub enum Result<T, L, F> {
    /// Contains the success value.
    Success(T),
    /// Contains a local error value (which should be handled)
    LocalErr(L),
    /// Contains a fatal error value (which should be propagated)
    FatalErr(F),
}

#[cfg(feature = "nightly")]
impl<T, L, F> FromResidual for Result<T, L, F> {
    #[inline]
    fn from_residual(residual: StdResult<Infallible, F>) -> Self {
        Result::FatalErr(residual.unwrap_err())
    }
}

#[cfg(feature = "nightly")]
impl<T, L, F> Try for Result<T, L, F> {
    type Output = StdResult<T, L>;
    type Residual = StdResult<Infallible, F>;

    #[inline]
    fn from_output(output: StdResult<T, L>) -> Self {
        From::from(output)
    }

    #[inline]
    fn branch(self) -> ControlFlow<StdResult<Infallible, F>, StdResult<T, L>> {
        match self {
            Result::Success(t) => ControlFlow::Continue(Ok(t)),
            Result::LocalErr(l) => ControlFlow::Continue(Err(l)),
            Result::FatalErr(f) => ControlFlow::Break(Err(f)),
        }
    }
}

impl<T, L, F> Result<T, L, F> {
    /// Convert `woah::Result<T, L, F>` into a `Result<Result<T, L>, F>`, which is equivalent
    /// in `?` behavior.
    ///
    /// # Example
    ///
    /// ```
    /// use woah::prelude::*;
    ///
    /// let result: StdResult<StdResult<i64, &str>, &str> = LocalErr("a local error").into_result();
    /// assert_eq!(result, Ok(Err("a local error")));
    /// ```
    #[inline]
    pub fn into_result(self) -> StdResult<StdResult<T, L>, F> {
        self.into()
    }

    /// Construct either a [`Success`] or [`LocalErr`] variant based on a
    /// `Result`.
    ///
    /// [`Success`]: enum.Result.html#variant.Success
    /// [`LocalErr`]: enum.Result.html#variant.LocalErr
    ///
    /// # Example
    ///
    /// ```
    /// use woah::prelude::*;
    ///
    /// let result: Result<i64, &str, &str> = Result::from_result(Ok(0));
    /// assert_eq!(result, Success(0));
    /// ```
    #[inline]
    pub fn from_result(ok: StdResult<T, L>) -> Self {
        match ok {
            Ok(t) => Success(t),
            Err(err) => LocalErr(err),
        }
    }

    /// Construct the [`Success`] variant based on some success value.
    ///
    /// [`Success`]: enum.Result.html#variant.Success
    ///
    /// # Example
    ///
    /// ```
    /// use woah::prelude::*;
    ///
    /// let fatal_err: Result<i64, &str, &str> = Result::from_success(0);
    /// assert_eq!(fatal_err, Success(0));
    /// ```
    #[inline]
    pub fn from_success(val: T) -> Self {
        Success(val)
    }

    /// Construct the [`LocalErr`] variant based on some error.
    ///
    /// [`LocalErr`]: enum.Result.html#variant.LocalErr
    ///
    /// # Example
    ///
    /// ```
    /// use woah::prelude::*;
    ///
    /// let fatal_err: Result<i64, &str, &str> = Result::from_fatal_error("a fatal error");
    /// assert_eq!(fatal_err, FatalErr("a fatal error"));
    /// ```
    #[inline]
    pub fn from_local_err(err: L) -> Self {
        LocalErr(err)
    }

    /// Construct the [`FatalErr`] variant based on some error.
    ///
    /// [`FatalErr`]: enum.Result.html#variant.FatalErr
    ///
    /// # Example
    ///
    /// ```
    /// use woah::prelude::*;
    ///
    /// let fatal_err: Result<i64, &str, &str> = Result::from_fatal_error("a fatal error");
    /// assert_eq!(fatal_err, FatalErr("a fatal error"));
    /// ```
    #[inline]
    pub fn from_fatal_error(err: F) -> Self {
        FatalErr(err)
    }

    /// Returns `true` if the result is [`Success`].
    ///
    /// [`Success`]: enum.Result.html#variant.Success
    ///
    /// # Example
    ///
    /// ```
    /// use woah::prelude::*;
    ///
    /// let x: Result<i32, &str, &str> = Success(-3);
    /// assert_eq!(x.is_success(), true);
    ///
    /// let x: Result<i32, &str, &str> = LocalErr("Some error message");
    /// assert_eq!(x.is_success(), false);
    ///
    /// let x: Result<i32, &str, &str> = FatalErr("Another error message");
    /// assert_eq!(x.is_success(), false);
    /// ```
    #[must_use = "if you intended to assert that this is ok, consider `.unwrap()` instead"]
    #[inline]
    pub fn is_success(&self) -> bool {
        matches!(self, Success(_))
    }

    /// Returns `true` if the result is [`LocalErr`] or [`FatalErr`].
    ///
    /// [`LocalErr`]: enum.Result.html#variant.LocalErr
    /// [`FatalErr`]: enum.Result.html#variant.FatalErr
    ///
    /// # Example
    ///
    /// ```
    /// use woah::prelude::*;
    ///
    /// let x: Result<i32, &str, &str> = Success(-3);
    /// assert_eq!(x.is_err(), false);
    ///
    /// let x: Result<i32, &str, &str> = LocalErr("Some error message");
    /// assert_eq!(x.is_err(), true);
    ///
    /// let x: Result<i32, &str, &str> = FatalErr("Another error message");
    /// assert_eq!(x.is_err(), true);
    /// ```
    #[must_use = "if you intended to assert that this is err, consider `.unwrap_err()` instead"]
    #[inline]
    pub fn is_err(&self) -> bool {
        !self.is_success()
    }

    /// Returns `true` if the result is [`LocalErr`].
    ///
    /// [`LocalErr`]: enum.Result.html#variant.LocalErr
    ///
    /// # Example
    ///
    /// ```
    /// use woah::prelude::*;
    ///
    /// let x: Result<i32, &str, &str> = Success(-3);
    /// assert_eq!(x.is_local_err(), false);
    ///
    /// let x: Result<i32, &str, &str> = LocalErr("Some error message");
    /// assert_eq!(x.is_local_err(), true);
    ///
    /// let x: Result<i32, &str, &str> = FatalErr("Another error message");
    /// assert_eq!(x.is_local_err(), false);
    /// ```
    #[must_use = "if you intended to assert that this is local_err, consider `.unwrap_local_err()` instead"]
    #[inline]
    pub fn is_local_err(&self) -> bool {
        matches!(self, LocalErr(_))
    }

    /// Returns `true` if the result is [`FatalErr`].
    ///
    /// [`FatalErr`]: enum.Result.html#variant.FatalErr
    ///
    /// # Example
    ///
    /// ```
    /// use woah::prelude::*;
    ///
    /// let x: Result<i32, &str, &str> = Success(-3);
    /// assert_eq!(x.is_fatal_err(), false);
    ///
    /// let x: Result<i32, &str, &str> = LocalErr("Some error message");
    /// assert_eq!(x.is_fatal_err(), false);
    ///
    /// let x: Result<i32, &str, &str> = FatalErr("Another error message");
    /// assert_eq!(x.is_fatal_err(), true);
    /// ```
    #[must_use = "if you intended to assert that this is fatal_err, consider `.unwrap_fatal_err()` instead"]
    #[inline]
    pub fn is_fatal_err(&self) -> bool {
        matches!(self, FatalErr(_))
    }

    /// Returns `true` if the result is a [`Success`] value containing the given value.
    ///
    /// [`Success`]: enum.Result.html#variant.Success
    ///
    /// # Examples
    ///
    /// ```
    /// use woah::prelude::*;
    ///
    /// let x: Result<u32, &str, &str> = Success(2);
    /// assert_eq!(x.contains(&2), true);
    ///
    /// let x: Result<u32, &str, &str> = Success(3);
    /// assert_eq!(x.contains(&2), false);
    ///
    /// let x: Result<u32, &str, &str> = LocalErr("Some error message");
    /// assert_eq!(x.contains(&2), false);
    /// ```
    #[must_use]
    #[inline]
    pub fn contains<U>(&self, x: &U) -> bool
    where
        U: PartialEq<T>,
    {
        matches!(self, Success(t) if *x == *t)
    }

    /// Returns `true` if the result is a [`LocalErr`] or [`FatalErr`] value containing the given value.
    ///
    /// [`LocalErr`]: enum.Result.html#variant.LocalErr
    /// [`FatalErr`]: enum.Result.html#variant.FatalErr
    ///
    /// # Examples
    ///
    /// ```
    /// use woah::prelude::*;
    /// use either::Either;
    ///
    /// let x: Result<&str, u32, &str> = LocalErr(2);
    /// let check: Either<_, &&str> = Either::Left(&2);
    /// assert_eq!(x.contains_err(check), true);
    ///
    /// let x: Result<&str, &str, u32> = FatalErr(3);
    /// let check: Either<&&str, _> = Either::Right(&2);
    /// assert_eq!(x.contains_err(check), false);
    ///
    /// let x: Result<u32, &str, &str> = Success(0);
    /// let check: Either<&&str, &&str> = Either::Left(&"");
    /// assert_eq!(x.contains_err(check), false);
    /// ```
    #[cfg(feature = "either")]
    #[must_use]
    #[inline]
    pub fn contains_err<U, Y>(&self, e: Either<&U, &Y>) -> bool
    where
        U: PartialEq<L>,
        Y: PartialEq<F>,
    {
        matches!((self, e), (LocalErr(err), Left(e)) if *e == *err)
            || matches!((self, e), (FatalErr(err), Right(e)) if *e == *err)
    }

    /// Returns `true` if the result is a [`LocalErr`] value containing the given value.
    ///
    /// [`LocalErr`]: enum.Result.html#variant.LocalErr
    ///
    /// # Examples
    ///
    /// ```
    /// use woah::prelude::*;
    ///
    /// let x: Result<&str, u32, &str> = LocalErr(2);
    /// assert_eq!(x.contains_local_err(&2), true);
    ///
    /// let x: Result<&str, u32, &str> = LocalErr(3);
    /// assert_eq!(x.contains_local_err(&2), false);
    ///
    /// let x: Result<&str, u32, &str> = Success("Some error message");
    /// assert_eq!(x.contains_local_err(&2), false);
    /// ```
    #[must_use]
    #[inline]
    pub fn contains_local_err<E>(&self, e: &E) -> bool
    where
        E: PartialEq<L>,
    {
        matches!(self, LocalErr(err) if *e == *err)
    }

    /// Returns `true` if the result is a [`FatalErr`] value containing the given value.
    ///
    /// [`FatalErr`]: enum.Result.html#variant.FatalErr
    ///
    /// # Examples
    ///
    /// ```
    /// use woah::prelude::*;
    ///
    /// let x: Result<&str, &str, u32> = FatalErr(2);
    /// assert_eq!(x.contains_fatal_err(&2), true);
    ///
    /// let x: Result<&str, &str, u32> = FatalErr(3);
    /// assert_eq!(x.contains_fatal_err(&2), false);
    ///
    /// let x: Result<&str, &str, u32> = Success("Some error message");
    /// assert_eq!(x.contains_fatal_err(&2), false);
    /// ```
    #[must_use]
    #[inline]
    pub fn contains_fatal_err<E>(&self, e: &E) -> bool
    where
        E: PartialEq<F>,
    {
        matches!(self, FatalErr(err) if *e == *err)
    }

    /// Convert a [`Success`] variant to an `Option::Some`, otherwise to a `None`.
    ///
    /// [`Success`]: enum.Result.html#variant.Success
    ///
    /// # Example
    ///
    /// ```
    /// use woah::prelude::*;
    ///
    /// let x: Result<u32, &str, &str> = Success(2);
    /// assert_eq!(x.success(), Some(2));
    ///
    /// let x: Result<&str, u32, &str> = LocalErr(2);
    /// assert_eq!(x.success(), None);
    ///
    /// let x: Result<&str, &str, u32> = FatalErr(2);
    /// assert_eq!(x.success(), None);
    /// ```
    #[inline]
    pub fn success(self) -> Option<T> {
        match self {
            Success(t) => Some(t),
            _ => None,
        }
    }

    /// Convert a [`LocalErr`] or [`FatalErr`] variant to an `Option<Either<_, _>>`, otherwise to a `None`.
    ///
    /// [`LocalErr`]: enum.Result.html#variant.LocalErr
    /// [`FatalErr`]: enum.Result.html#variant.FatalErr
    ///
    /// # Example
    ///
    /// ```
    /// use woah::prelude::*;
    /// use either::Either::{self, Left, Right};
    ///
    /// let x: Result<u32, &str, &str> = Success(2);
    /// assert_eq!(x.err(), None);
    ///
    /// let x: Result<&str, u32, &str> = LocalErr(2);
    /// assert_eq!(x.err(), Some(Left(2)));
    ///
    /// let x: Result<&str, &str, u32> = FatalErr(2);
    /// assert_eq!(x.err(), Some(Right(2)));
    /// ```
    #[cfg(feature = "either")]
    #[inline]
    pub fn err(self) -> Option<Either<L, F>> {
        match self {
            LocalErr(err) => Some(Left(err)),
            FatalErr(err) => Some(Right(err)),
            _ => None,
        }
    }

    /// Convert a [`LocalErr`] variant to an `Option::Some`, otherwise to a `None`.
    ///
    /// [`LocalErr`]: enum.Result.html#variant.LocalErr
    ///
    /// # Example
    ///
    /// ```
    /// use woah::prelude::*;
    ///
    /// let x: Result<u32, &str, &str> = Success(2);
    /// assert_eq!(x.local_err(), None);
    ///
    /// let x: Result<&str, u32, &str> = LocalErr(2);
    /// assert_eq!(x.local_err(), Some(2));
    ///
    /// let x: Result<&str, &str, u32> = FatalErr(2);
    /// assert_eq!(x.local_err(), None);
    /// ```
    #[inline]
    pub fn local_err(self) -> Option<L> {
        match self {
            LocalErr(err) => Some(err),
            _ => None,
        }
    }

    /// Convert a [`FatalErr`] variant to an `Option::Some`, otherwise to a `None`.
    ///
    /// [`FatalErr`]: enum.Result.html#variant.FatalErr
    ///
    /// # Example
    ///
    /// ```
    /// use woah::prelude::*;
    ///
    /// let x: Result<u32, &str, &str> = Success(2);
    /// assert_eq!(x.fatal_err(), None);
    ///
    /// let x: Result<&str, u32, &str> = LocalErr(2);
    /// assert_eq!(x.fatal_err(), None);
    ///
    /// let x: Result<&str, &str, u32> = FatalErr(2);
    /// assert_eq!(x.fatal_err(), Some(2));
    /// ```
    #[inline]
    pub fn fatal_err(self) -> Option<F> {
        match self {
            FatalErr(err) => Some(err),
            _ => None,
        }
    }

    /// Get a reference to the contained value.
    ///
    /// # Example
    ///
    /// ```
    /// use woah::prelude::*;
    ///
    /// let x: Result<u32, u32, u32> = Success(0);
    /// assert_eq!(x.as_ref(), Success(&0));
    ///
    /// let x: Result<u32, u32, u32> = LocalErr(0);
    /// assert_eq!(x.as_ref(), LocalErr(&0));
    ///
    /// let x: Result<u32, u32, u32> = FatalErr(0);
    /// assert_eq!(x.as_ref(), FatalErr(&0));
    /// ```
    #[inline]
    pub fn as_ref(&self) -> Result<&T, &L, &F> {
        match self {
            Success(t) => Success(t),
            LocalErr(err) => LocalErr(err),
            FatalErr(err) => FatalErr(err),
        }
    }

    /// Get a mutable reference to the contained value.
    ///
    /// # Example
    ///
    /// ```
    /// use woah::prelude::*;
    ///
    /// let mut x: Result<u32, u32, u32> = Success(0);
    /// assert_eq!(x.as_mut(), Success(&mut 0));
    ///
    /// let mut x: Result<u32, u32, u32> = LocalErr(0);
    /// assert_eq!(x.as_mut(), LocalErr(&mut 0));
    ///
    /// let mut x: Result<u32, u32, u32> = FatalErr(0);
    /// assert_eq!(x.as_mut(), FatalErr(&mut 0));
    /// ```
    #[inline]
    pub fn as_mut(&mut self) -> Result<&mut T, &mut L, &mut F> {
        match self {
            Success(t) => Success(t),
            LocalErr(err) => LocalErr(err),
            FatalErr(err) => FatalErr(err),
        }
    }

    /// Apply a function to the contained value if it's a [`Success`].
    ///
    /// [`Success`]: enum.Result.html#variant.Success
    ///
    /// # Example
    ///
    /// ```
    /// use woah::prelude::*;
    ///
    /// let x: Result<u32, u32, u32> = Success(0);
    /// assert_eq!(x.map(|s| s + 1), Success(1));
    ///
    /// let x: Result<u32, u32, u32> = LocalErr(0);
    /// assert_eq!(x.map(|s| s + 1), LocalErr(0));
    ///
    /// let x: Result<u32, u32, u32> = FatalErr(0);
    /// assert_eq!(x.map(|s| s + 1), FatalErr(0));
    /// ```
    #[inline]
    pub fn map<U, S>(self, f: U) -> Result<S, L, F>
    where
        U: FnOnce(T) -> S,
    {
        match self {
            Success(t) => Success(f(t)),
            LocalErr(e) => LocalErr(e),
            FatalErr(e) => FatalErr(e),
        }
    }

    /// Apply a function to the contained value if it's a [`Success`].
    ///
    /// Otherwise return the provided value.
    ///
    /// [`Success`]: enum.Result.html#variant.Success
    ///
    /// # Example
    ///
    /// ```
    /// use woah::prelude::*;
    ///
    /// let x: Result<u32, u32, u32> = Success(0);
    /// assert_eq!(x.map_or(5, |s| s + 1), 1);
    ///
    /// let x: Result<u32, u32, u32> = LocalErr(0);
    /// assert_eq!(x.map_or(5, |s| s + 1), 5);
    ///
    /// let x: Result<u32, u32, u32> = FatalErr(0);
    /// assert_eq!(x.map_or(5, |s| s + 1), 5);
    /// ```
    #[inline]
    pub fn map_or<U, G>(self, default: U, f: G) -> U
    where
        G: FnOnce(T) -> U,
    {
        match self {
            Success(t) => f(t),
            _ => default,
        }
    }

    /// Apply a function to the contained value if it's a [`Success`].
    ///
    /// Otherwise run one of the provided default functions.
    ///
    /// [`Success`]: enum.Result.html#variant.Success
    ///
    /// # Example
    ///
    /// ```
    /// use woah::prelude::*;
    ///
    /// let x: Result<u32, u32, u32> = Success(0);
    /// assert_eq!(x.map_or_else(|l| l + 3, |f| f + 2, |s| s + 1), 1);
    ///
    /// let x: Result<u32, u32, u32> = LocalErr(0);
    /// assert_eq!(x.map_or_else(|l| l + 3, |f| f + 2, |s| s + 1), 3);
    ///
    /// let x: Result<u32, u32, u32> = FatalErr(0);
    /// assert_eq!(x.map_or_else(|l| l + 3, |f| f + 2, |s| s + 1), 2);
    /// ```
    #[inline]
    pub fn map_or_else<U, LD, FD, G>(self, default_local: LD, default_fatal: FD, f: G) -> U
    where
        LD: FnOnce(L) -> U,
        FD: FnOnce(F) -> U,
        G: FnOnce(T) -> U,
    {
        match self {
            Success(t) => f(t),
            LocalErr(err) => default_local(err),
            FatalErr(err) => default_fatal(err),
        }
    }

    /// Apply a function to the contained value if it's a [`LocalErr`] or [`FatalErr`].
    ///
    /// [`LocalErr`]: enum.Result.html#variant.LocalErr
    /// [`FatalErr`]: enum.Result.html#variant.FatalErr
    ///
    /// # Example
    ///
    /// ```
    /// use woah::prelude::*;
    /// use either::Either::{self, Left, Right};
    ///
    /// fn modify_error(err: Either<u32, u32>) -> Either<u32, u32> {
    ///     match err {
    ///         Left(l) => Left(l + 1),
    ///         Right(f) => Right(f + 1),
    ///     }
    /// }
    ///
    /// let x: Result<u32, u32, u32> = Success(0);
    /// assert_eq!(x.map_err(modify_error), Success(0));
    ///
    /// let x: Result<u32, u32, u32> = LocalErr(0);
    /// assert_eq!(x.map_err(modify_error), LocalErr(1));
    ///
    /// let x: Result<u32, u32, u32> = FatalErr(0);
    /// assert_eq!(x.map_err(modify_error), FatalErr(1));
    /// ```
    #[cfg(feature = "either")]
    #[inline]
    pub fn map_err<U, M, G>(self, f: U) -> Result<T, M, G>
    where
        U: FnOnce(Either<L, F>) -> Either<M, G>,
    {
        match self {
            Success(t) => Success(t),
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

    /// Apply a function to the contained value if it's a [`LocalErr`].
    ///
    /// [`LocalErr`]: enum.Result.html#variant.LocalErr
    ///
    /// # Example
    ///
    /// ```
    /// use woah::prelude::*;
    ///
    /// let x: Result<u32, u32, u32> = Success(0);
    /// assert_eq!(x.map_local_err(|l| l + 1), Success(0));
    ///
    /// let x: Result<u32, u32, u32> = LocalErr(0);
    /// assert_eq!(x.map_local_err(|l| l + 1), LocalErr(1));
    ///
    /// let x: Result<u32, u32, u32> = FatalErr(0);
    /// assert_eq!(x.map_local_err(|l| l + 1), FatalErr(0));
    /// ```
    #[inline]
    pub fn map_local_err<U, S>(self, f: U) -> Result<T, S, F>
    where
        U: FnOnce(L) -> S,
    {
        match self {
            Success(t) => Success(t),
            LocalErr(e) => LocalErr(f(e)),
            FatalErr(e) => FatalErr(e),
        }
    }

    /// Apply a function to the contained value if it's a [`FatalErr`].
    ///
    /// [`FatalErr`]: enum.Result.html#variant.FatalErr
    ///
    /// # Example
    ///
    /// ```
    /// use woah::prelude::*;
    ///
    /// let x: Result<u32, u32, u32> = Success(0);
    /// assert_eq!(x.map_fatal_err(|f| f + 1), Success(0));
    ///
    /// let x: Result<u32, u32, u32> = LocalErr(0);
    /// assert_eq!(x.map_fatal_err(|f| f + 1), LocalErr(0));
    ///
    /// let x: Result<u32, u32, u32> = FatalErr(0);
    /// assert_eq!(x.map_fatal_err(|f| f + 1), FatalErr(1));
    /// ```
    #[inline]
    pub fn map_fatal_err<U, S>(self, f: U) -> Result<T, L, S>
    where
        U: FnOnce(F) -> S,
    {
        match self {
            Success(t) => Success(t),
            LocalErr(e) => LocalErr(e),
            FatalErr(e) => FatalErr(f(e)),
        }
    }

    /// Get an iterator over the inner value in the `Result`, if it's a [`Success`].
    ///
    /// [`Success`]: enum.Result.html#variant.Success
    ///
    /// # Example
    ///
    /// ```
    /// use woah::prelude::*;
    ///
    /// let r: Result<u32, &str, &str> = Success(0);
    ///
    /// assert_eq!(r.iter().next(), Some(&0));
    /// ```
    #[inline]
    pub fn iter(&self) -> Iter<T> {
        let inner = match self {
            Success(t) => Some(t),
            _ => None,
        };

        Iter { inner }
    }

    /// Get a mutable iterator over the inner value in the `Result`, if it's a [`Success`].
    ///
    /// [`Success`]: enum.Result.html#variant.Success
    ///
    /// # Example
    ///
    /// ```
    /// use woah::prelude::*;
    ///
    /// let mut r: Result<u32, &str, &str> = Success(0);
    ///
    /// {
    ///     let next = r.iter_mut().next();
    ///
    ///     assert!(next.is_some());
    ///
    ///     *next.unwrap() = 5;
    /// }
    ///
    /// assert_eq!(r, Success(5));
    /// ```
    #[inline]
    pub fn iter_mut(&mut self) -> IterMut<T> {
        let inner = match self {
            Success(t) => Some(t),
            _ => None,
        };

        IterMut { inner }
    }

    /// If it's a [`Success`], replace it with `res`.
    ///
    /// [`Success`]: enum.Result.html#variant.Success
    ///
    /// # Example
    ///
    /// ```
    /// use woah::prelude::*;
    ///
    /// let r1: Result<u32, &str, &str> = Success(0);
    /// let r2: Result<u32, _, &str> = r1.and(LocalErr(""));
    /// assert_eq!(r2, LocalErr(""));
    /// ```
    #[inline]
    pub fn and<U>(self, res: Result<U, L, F>) -> Result<U, L, F> {
        match self {
            Success(_) => res,
            LocalErr(err) => LocalErr(err),
            FatalErr(err) => FatalErr(err),
        }
    }

    /// If it's a [`Success`], replace it with the result of `op`.
    ///
    /// [`Success`]: enum.Result.html#variant.Success
    ///
    /// # Example
    ///
    /// ```
    /// use woah::prelude::*;
    ///
    /// let r1: Result<u32, &str, &str> = Success(0);
    /// let r2: Result<u32, _, &str> = r1.and_then(|c| {
    ///     if c == 0 {
    ///         LocalErr("local")
    ///     } else {
    ///         FatalErr("fatal")
    ///     }
    /// });
    ///
    /// assert_eq!(r2, LocalErr("local"));
    /// ```
    #[inline]
    pub fn and_then<U, G>(self, op: G) -> Result<U, L, F>
    where
        G: FnOnce(T) -> Result<U, L, F>,
    {
        match self {
            Success(t) => op(t),
            LocalErr(err) => LocalErr(err),
            FatalErr(err) => FatalErr(err),
        }
    }

    /// If it's a [`LocalErr`] or [`FatalErr`], replace them with the appropriate value.
    ///
    /// [`LocalErr`]: enum.Result.html#variant.LocalErr
    /// [`FatalErr`]: enum.Result.html#variant.FatalErr
    ///
    /// # Example
    ///
    /// ```
    /// use woah::prelude::*;
    ///
    /// let l: Result<u32, u32, u32> = LocalErr(1);
    /// let f: Result<u32, u32, u32> = FatalErr(2);
    ///
    /// let r: Result<u32, u32, u32> = Success(0);
    /// assert_eq!(r.or(l, f), Success(0));
    ///
    /// let r: Result<u32, u32, u32> = LocalErr(0);
    /// assert_eq!(r.or(l, f), LocalErr(1));
    ///
    /// let r: Result<u32, u32, u32> = FatalErr(0);
    /// assert_eq!(r.or(l, f), FatalErr(2));
    /// ```
    #[inline]
    pub fn or<M, G>(
        self,
        res_local: Result<T, M, G>,
        res_fatal: Result<T, M, G>,
    ) -> Result<T, M, G> {
        match self {
            Success(t) => Success(t),
            LocalErr(_) => res_local,
            FatalErr(_) => res_fatal,
        }
    }

    /// If it's a [`LocalErr`], replace them with the given value.
    ///
    /// [`LocalErr`]: enum.Result.html#variant.LocalErr
    ///
    /// # Example
    ///
    /// ```
    /// use woah::prelude::*;
    ///
    /// let l: Result<u32, u32, u32> = LocalErr(1);
    ///
    /// let r: Result<u32, u32, u32> = Success(0);
    /// assert_eq!(r.or_local(l), Success(0));
    ///
    /// let r: Result<u32, u32, u32> = LocalErr(0);
    /// assert_eq!(r.or_local(l), LocalErr(1));
    ///
    /// let r: Result<u32, u32, u32> = FatalErr(0);
    /// assert_eq!(r.or_local(l), FatalErr(0));
    /// ```
    #[inline]
    pub fn or_local<M>(self, res: Result<T, M, F>) -> Result<T, M, F> {
        match self {
            Success(t) => Success(t),
            LocalErr(_) => res,
            FatalErr(err) => FatalErr(err),
        }
    }

    /// If it's a [`FatalErr`], replace them with the given value.
    ///
    /// [`FatalErr`]: enum.Result.html#variant.FatalErr
    ///
    /// # Example
    ///
    /// ```
    /// use woah::prelude::*;
    ///
    /// let f: Result<u32, u32, u32> = FatalErr(2);
    ///
    /// let r: Result<u32, u32, u32> = Success(0);
    /// assert_eq!(r.or_fatal(f), Success(0));
    ///
    /// let r: Result<u32, u32, u32> = LocalErr(0);
    /// assert_eq!(r.or_fatal(f), LocalErr(0));
    ///
    /// let r: Result<u32, u32, u32> = FatalErr(0);
    /// assert_eq!(r.or_fatal(f), FatalErr(2));
    /// ```
    #[inline]
    pub fn or_fatal<G>(self, res: Result<T, L, G>) -> Result<T, L, G> {
        match self {
            Success(t) => Success(t),
            LocalErr(err) => LocalErr(err),
            FatalErr(_) => res,
        }
    }

    /// If it's a [`LocalErr`] or [`FatalErr`], replace them with the appropriate function result.
    ///
    /// [`LocalErr`]: enum.Result.html#variant.LocalErr
    /// [`FatalErr`]: enum.Result.html#variant.FatalErr
    ///
    /// # Example
    ///
    /// ```
    /// use woah::prelude::*;
    ///
    /// let l = |l| LocalErr(l + 1);
    /// let f = |f| FatalErr(f + 2);
    ///
    /// let r: Result<u32, u32, u32> = Success(0);
    /// assert_eq!(r.or_else(l, f), Success(0));
    ///
    /// let r: Result<u32, u32, u32> = LocalErr(0);
    /// assert_eq!(r.or_else(l, f), LocalErr(1));
    ///
    /// let r: Result<u32, u32, u32> = FatalErr(0);
    /// assert_eq!(r.or_else(l, f), FatalErr(2));
    /// ```
    #[inline]
    pub fn or_else<O, P, M, G>(self, op_local: O, op_fatal: P) -> Result<T, M, G>
    where
        O: FnOnce(L) -> Result<T, M, G>,
        P: FnOnce(F) -> Result<T, M, G>,
    {
        match self {
            Success(t) => Success(t),
            LocalErr(err) => op_local(err),
            FatalErr(err) => op_fatal(err),
        }
    }

    /// If it's a [`LocalErr`], replace it with the appropriate function result.
    ///
    /// [`LocalErr`]: enum.Result.html#variant.LocalErr
    ///
    /// # Example
    ///
    /// ```
    /// use woah::prelude::*;
    ///
    /// let l = |l| LocalErr(l + 1);
    ///
    /// let r: Result<u32, u32, u32> = Success(0);
    /// assert_eq!(r.or_else_local(l), Success(0));
    ///
    /// let r: Result<u32, u32, u32> = LocalErr(0);
    /// assert_eq!(r.or_else_local(l), LocalErr(1));
    ///
    /// let r: Result<u32, u32, u32> = FatalErr(0);
    /// assert_eq!(r.or_else_local(l), FatalErr(0));
    /// ```
    #[inline]
    pub fn or_else_local<O, M>(self, op: O) -> Result<T, M, F>
    where
        O: FnOnce(L) -> Result<T, M, F>,
    {
        match self {
            Success(t) => Success(t),
            LocalErr(err) => op(err),
            FatalErr(err) => FatalErr(err),
        }
    }

    /// If it's a [`FatalErr`], replace it with the appropriate function result.
    ///
    /// [`FatalErr`]: enum.Result.html#variant.FatalErr
    ///
    /// # Example
    ///
    /// ```
    /// use woah::prelude::*;
    ///
    /// let f = |f| FatalErr(f + 2);
    ///
    /// let r: Result<u32, u32, u32> = Success(0);
    /// assert_eq!(r.or_else_fatal(f), Success(0));
    ///
    /// let r: Result<u32, u32, u32> = LocalErr(0);
    /// assert_eq!(r.or_else_fatal(f), LocalErr(0));
    ///
    /// let r: Result<u32, u32, u32> = FatalErr(0);
    /// assert_eq!(r.or_else_fatal(f), FatalErr(2));
    /// ```
    #[inline]
    pub fn or_else_fatal<O, G>(self, op: O) -> Result<T, L, G>
    where
        O: FnOnce(F) -> Result<T, L, G>,
    {
        match self {
            Success(t) => Success(t),
            LocalErr(err) => LocalErr(err),
            FatalErr(err) => op(err),
        }
    }

    /// Return inner value if it's a [`Success`], or `alt` otherwise.
    ///
    /// [`Success`]: enum.Result.html#variant.Success
    ///
    /// # Example
    ///
    /// ```
    /// use woah::prelude::*;
    ///
    /// let r: Result<u32, u32, u32> = Success(0);
    /// assert_eq!(r.unwrap_or(5), 0);
    ///
    /// let r: Result<u32, u32, u32> = LocalErr(0);
    /// assert_eq!(r.unwrap_or(5), 5);
    ///
    /// let r: Result<u32, u32, u32> = FatalErr(0);
    /// assert_eq!(r.unwrap_or(5), 5);
    /// ```
    #[inline]
    pub fn unwrap_or(self, alt: T) -> T {
        match self {
            Success(t) => t,
            _ => alt,
        }
    }

    /// Return inner value if it's a [`Success`], or the appropriate function otherwise.
    ///
    /// [`Success`]: enum.Result.html#variant.Success
    ///
    /// # Example
    ///
    /// ```
    /// use woah::prelude::*;
    ///
    /// let l = |_| 5;
    /// let f = |_| 10;
    ///
    /// let r: Result<u32, u32, u32> = Success(0);
    /// assert_eq!(r.unwrap_or_else(l, f), 0);
    ///
    /// let r: Result<u32, u32, u32> = LocalErr(0);
    /// assert_eq!(r.unwrap_or_else(l, f), 5);
    ///
    /// let r: Result<u32, u32, u32> = FatalErr(0);
    /// assert_eq!(r.unwrap_or_else(l, f), 10);
    /// ```
    #[inline]
    pub fn unwrap_or_else<M, G>(self, local_op: M, fatal_op: G) -> T
    where
        M: FnOnce(L) -> T,
        G: FnOnce(F) -> T,
    {
        match self {
            Success(t) => t,
            LocalErr(err) => local_op(err),
            FatalErr(err) => fatal_op(err),
        }
    }
}

impl<'a, T, L, F> Result<&'a T, L, F>
where
    T: Copy,
{
    /// Copy the value if it's a [`Success`].
    ///
    /// [`Success`]: enum.Result.html#variant.Success
    ///
    /// # Example
    ///
    /// ```
    /// use woah::prelude::*;
    ///
    /// let r: Result<&u32, (), ()> = Success(&0);
    /// assert_eq!(r.copied(), Success(0));
    /// ```
    #[inline]
    pub fn copied(self) -> Result<T, L, F> {
        match self {
            Success(t) => Success(*t),
            LocalErr(err) => LocalErr(err),
            FatalErr(err) => FatalErr(err),
        }
    }
}

impl<'a, T, L, F> Result<&'a mut T, L, F>
where
    T: Copy,
{
    /// Copy the value if it's a [`Success`].
    ///
    /// [`Success`]: enum.Result.html#variant.Success
    ///
    /// # Example
    ///
    /// ```
    /// use woah::prelude::*;
    ///
    /// let r: Result<&u32, (), ()> = Success(&0);
    /// assert_eq!(r.copied(), Success(0));
    /// ```
    #[inline]
    pub fn copied(self) -> Result<T, L, F> {
        match self {
            Success(t) => Success(*t),
            LocalErr(err) => LocalErr(err),
            FatalErr(err) => FatalErr(err),
        }
    }
}

impl<'a, T, L, F> Result<&'a T, L, F>
where
    T: Clone,
{
    /// Clone the value if it's a [`Success`].
    ///
    /// [`Success`]: enum.Result.html#variant.Success
    ///
    /// # Example
    ///
    /// ```
    /// use woah::prelude::*;
    ///
    /// let r: Result<&u32, (), ()> = Success(&0);
    /// assert_eq!(r.cloned(), Success(0));
    /// ```
    #[inline]
    pub fn cloned(self) -> Result<T, L, F> {
        match self {
            Success(t) => Success(t.clone()),
            LocalErr(err) => LocalErr(err),
            FatalErr(err) => FatalErr(err),
        }
    }
}

impl<'a, T, L, F> Result<&'a mut T, L, F>
where
    T: Clone,
{
    /// Clone the value if it's a [`Success`].
    ///
    /// [`Success`]: enum.Result.html#variant.Success
    ///
    /// # Example
    ///
    /// ```
    /// use woah::prelude::*;
    ///
    /// let r: Result<&u32, (), ()> = Success(&0);
    /// assert_eq!(r.cloned(), Success(0));
    /// ```
    #[inline]
    pub fn cloned(self) -> Result<T, L, F> {
        match self {
            Success(t) => Success(t.clone()),
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
    /// Get the value if it's a [`Success`], panic otherwise.
    ///
    /// [`Success`]: enum.Result.html#variant.Success
    ///
    /// # Example
    ///
    /// ```
    /// use woah::prelude::*;
    ///
    /// let r: Result<u32, (), ()> = Success(0);
    /// assert_eq!(r.unwrap(), 0);
    /// ```
    #[inline]
    pub fn unwrap(self) -> T {
        match self {
            Success(t) => t,
            LocalErr(err) => panic!("{:?}", err),
            FatalErr(err) => panic!("{:?}", err),
        }
    }

    /// Get the value if it's a [`Success`], panic with a `msg` otherwise.
    ///
    /// [`Success`]: enum.Result.html#variant.Success
    ///
    /// # Example
    ///
    /// ```
    /// use woah::prelude::*;
    ///
    /// let r: Result<u32, (), ()> = Success(0);
    /// assert_eq!(r.expect("should be success"), 0);
    /// ```
    #[inline]
    pub fn expect(self, msg: &str) -> T {
        match self {
            Success(t) => t,
            LocalErr(_) => panic!("{}", msg),
            FatalErr(_) => panic!("{}", msg),
        }
    }
}

#[cfg(feature = "either")]
impl<T, L, F> Result<T, L, F>
where
    T: Debug,
    L: Debug,
    F: Debug,
{
    #[inline]
    pub fn unwrap_err(self) -> Either<L, F> {
        match self {
            Success(t) => panic!("{:?}", t),
            LocalErr(err) => Left(err),
            FatalErr(err) => Right(err),
        }
    }

    #[inline]
    pub fn expect_err(self, msg: &str) -> Either<L, F> {
        match self {
            Success(_) => panic!("{}", msg),
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
    #[inline]
    pub fn unwrap_local_err(self) -> L {
        match self {
            Success(t) => panic!("{:?}", t),
            LocalErr(err) => err,
            FatalErr(err) => panic!("{:?}", err),
        }
    }

    #[inline]
    pub fn expect_local_err(self, msg: &str) -> L {
        match self {
            Success(_) => panic!("{}", msg),
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
    #[inline]
    pub fn unwrap_fatal_err(self) -> F {
        match self {
            Success(t) => panic!("{:?}", t),
            LocalErr(err) => panic!("{:?}", err),
            FatalErr(err) => err,
        }
    }

    #[inline]
    pub fn expect_fatal_err(self, msg: &str) -> F {
        match self {
            Success(_) => panic!("{}", msg),
            LocalErr(_) => panic!("{}", msg),
            FatalErr(err) => err,
        }
    }
}

impl<T, L, F> Result<T, L, F>
where
    T: Default,
{
    #[inline]
    pub fn unwrap_or_default(self) -> T {
        match self {
            Success(t) => t,
            _ => T::default(),
        }
    }

    #[inline]
    pub fn into_result_default(self) -> StdResult<T, F> {
        match self {
            Success(t) => Ok(t),
            LocalErr(_) => Ok(T::default()),
            FatalErr(err) => Err(err),
        }
    }
}

#[cfg(feature = "nightly")]
impl<T, L, F> Result<T, L, F>
where
    L: Into<!>,
    F: Into<!>,
{
    #[inline]
    pub fn into_success(self) -> T {
        match self {
            Success(t) => t,
            LocalErr(err) => err.into(),
            FatalErr(err) => err.into(),
        }
    }
}

impl<T, L, F> Result<T, L, F>
where
    T: Deref,
{
    #[inline]
    pub fn as_deref(&self) -> Result<&<T as Deref>::Target, &L, &F> {
        match self {
            Success(t) => Success(t.deref()),
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
    #[inline]
    pub fn as_deref_err(&self) -> Result<&T, &<L as Deref>::Target, &<F as Deref>::Target> {
        match self {
            Success(t) => Success(t),
            LocalErr(err) => LocalErr(err.deref()),
            FatalErr(err) => FatalErr(err.deref()),
        }
    }
}

impl<T, L, F> Result<T, L, F>
where
    L: Deref,
{
    #[inline]
    pub fn as_deref_local_err(&self) -> Result<&T, &<L as Deref>::Target, &F> {
        match self {
            Success(t) => Success(t),
            LocalErr(err) => LocalErr(err.deref()),
            FatalErr(err) => FatalErr(err),
        }
    }
}

impl<T, L, F> Result<T, L, F>
where
    F: Deref,
{
    #[inline]
    pub fn as_deref_fatal_err(&self) -> Result<&T, &L, &<F as Deref>::Target> {
        match self {
            Success(t) => Success(t),
            LocalErr(err) => LocalErr(err),
            FatalErr(err) => FatalErr(err.deref()),
        }
    }
}

impl<T, L, F> Result<T, L, F>
where
    T: DerefMut,
{
    #[inline]
    pub fn as_deref_mut(&mut self) -> Result<&mut <T as Deref>::Target, &mut L, &mut F> {
        match self {
            Success(t) => Success(t.deref_mut()),
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
    #[inline]
    pub fn as_deref_mut_err(
        &mut self,
    ) -> Result<&mut T, &mut <L as Deref>::Target, &mut <F as Deref>::Target> {
        match self {
            Success(t) => Success(t),
            LocalErr(err) => LocalErr(err.deref_mut()),
            FatalErr(err) => FatalErr(err.deref_mut()),
        }
    }
}

impl<T, L, F> Result<T, L, F>
where
    L: DerefMut,
{
    #[inline]
    pub fn as_deref_mut_local_err(&mut self) -> Result<&mut T, &mut <L as Deref>::Target, &mut F> {
        match self {
            Success(t) => Success(t),
            LocalErr(err) => LocalErr(err.deref_mut()),
            FatalErr(err) => FatalErr(err),
        }
    }
}

impl<T, L, F> Result<T, L, F>
where
    F: DerefMut,
{
    #[inline]
    pub fn as_deref_mut_fatal_err(&mut self) -> Result<&mut T, &mut L, &mut <F as Deref>::Target> {
        match self {
            Success(t) => Success(t),
            LocalErr(err) => LocalErr(err),
            FatalErr(err) => FatalErr(err.deref_mut()),
        }
    }
}

impl<T, L, F> Result<Option<T>, L, F> {
    #[inline]
    pub fn transpose(self) -> Option<Result<T, L, F>> {
        match self {
            Success(Some(t)) => Some(Success(t)),
            Success(None) => None,
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
    #[inline]
    fn clone(&self) -> Result<T, L, F> {
        match self {
            Success(t) => Success(t.clone()),
            LocalErr(err) => LocalErr(err.clone()),
            FatalErr(err) => FatalErr(err.clone()),
        }
    }

    #[inline]
    fn clone_from(&mut self, source: &Result<T, L, F>) {
        match (self, source) {
            (Success(to), Success(from)) => to.clone_from(from),
            (LocalErr(to), LocalErr(from)) => to.clone_from(from),
            (FatalErr(to), FatalErr(from)) => to.clone_from(from),
            (to, from) => *to = from.clone(),
        }
    }
}

#[cfg(feature = "nightly")]
impl<A, V, L, F> FromIterator<Result<A, L, F>> for Result<V, L, F>
where
    V: FromIterator<A>,
{
    #[inline]
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

    #[inline]
    fn into_iter(self) -> IterMut<'a, T> {
        self.iter_mut()
    }
}

impl<'a, T, L, F> IntoIterator for &'a Result<T, L, F> {
    type Item = &'a T;
    type IntoIter = Iter<'a, T>;

    #[inline]
    fn into_iter(self) -> Iter<'a, T> {
        self.iter()
    }
}

impl<T, L, F> IntoIterator for Result<T, L, F> {
    type Item = T;
    type IntoIter = IntoIter<T>;

    #[inline]
    fn into_iter(self) -> IntoIter<T> {
        IntoIter {
            inner: self.success(),
        }
    }
}

#[cfg(feature = "nightly")]
impl<T, U, L, F> Product<Result<U, L, F>> for Result<T, L, F>
where
    T: Product<U>,
{
    #[inline]
    fn product<I>(iter: I) -> Result<T, L, F>
    where
        I: Iterator<Item = Result<U, L, F>>,
    {
        process_results(iter, |i| i.product())
    }
}

#[cfg(feature = "nightly")]
impl<T, U, L, F> Sum<Result<U, L, F>> for Result<T, L, F>
where
    T: Sum<U>,
{
    #[inline]
    fn sum<I>(iter: I) -> Result<T, L, F>
    where
        I: Iterator<Item = Result<U, L, F>>,
    {
        process_results(iter, |i| i.sum())
    }
}

#[cfg(feature = "std")]
impl<L, F> Termination for Result<(), L, F>
where
    L: Debug,
    F: Debug,
{
    #[inline]
    fn report(self) -> ExitCode {
        match self {
            Success(()) => ().report(),
            LocalErr(err) => {
                eprintln!("Error: {:?}", err);
                ExitCode::FAILURE.report()
            }
            FatalErr(err) => {
                eprintln!("Error: {:?}", err);
                ExitCode::FAILURE.report()
            }
        }
    }
}

#[cfg(all(feature = "nightly", feature = "std"))]
impl<L, F> Termination for Result<!, L, F>
where
    L: Debug,
    F: Debug,
{
    #[inline]
    fn report(self) -> ExitCode {
        match self {
            LocalErr(err) => {
                eprintln!("Error: {:?}", err);
                ExitCode::FAILURE.report()
            }
            FatalErr(err) => {
                eprintln!("Error: {:?}", err);
                ExitCode::FAILURE.report()
            }
            Success(t) => t,
        }
    }
}

/// An iterator over the value in an `Success` variant of a `woah::Result`.
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

/// An iterator over a reference to the `Success` variant of a `woah::Result`.
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

#[cfg(feature = "nightly")]
unsafe impl<'a, T> TrustedLen for Iter<'a, T> {}

/// An iterator over a mutable reference to the `Success` variant of a `woah::Result`.
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

#[cfg(feature = "nightly")]
unsafe impl<'a, T> TrustedLen for IterMut<'a, T> {}

#[cfg(feature = "nightly")]
pub(crate) struct ResultShunt<'a, I, L, F> {
    iter: I,
    error: &'a mut Result<(), L, F>,
}

#[cfg(feature = "nightly")]
#[inline]
pub(crate) fn process_results<I, T, L, F, G, U>(iter: I, mut f: G) -> Result<U, L, F>
where
    I: Iterator<Item = Result<T, L, F>>,
    for<'a> G: FnMut(ResultShunt<'a, I, L, F>) -> U,
{
    let mut error = Success(());
    let shunt = ResultShunt {
        iter,
        error: &mut error,
    };
    let value = f(shunt);
    error.map(|()| value)
}

#[cfg(feature = "nightly")]
impl<I, T, L, F> Iterator for ResultShunt<'_, I, L, F>
where
    I: Iterator<Item = Result<T, L, F>>,
{
    type Item = T;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.find(|_| true)
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        if self.error.is_err() {
            (0, Some(0))
        } else {
            let (_, upper) = self.iter.size_hint();
            (0, upper)
        }
    }

    #[inline]
    fn try_fold<B, G, R>(&mut self, init: B, mut f: G) -> R
    where
        G: FnMut(B, Self::Item) -> R,
        R: Try<Output = B>,
    {
        let error = &mut *self.error;

        into_try(self.iter.try_fold(init, |acc, x| match x {
            Success(x) => from_try(f(acc, x)),
            LocalErr(l) => {
                *error = LocalErr(l);
                ControlFlow::Break(try { acc })
            }
            FatalErr(f) => {
                *error = FatalErr(f);
                ControlFlow::Break(try { acc })
            }
        }))
    }
}

/// Create a `ControlFlow` from any type implementing `Try`.
#[cfg(feature = "nightly")]
#[inline]
fn from_try<R: Try>(r: R) -> ControlFlow<R, R::Output> {
    match R::branch(r) {
        ControlFlow::Continue(v) => ControlFlow::Continue(v),
        ControlFlow::Break(v) => ControlFlow::Break(R::from_residual(v)),
    }
}

/// Convert a `ControlFlow` into any type implementing `Try`;
#[cfg(feature = "nightly")]
#[inline]
fn into_try<R: Try>(cf: ControlFlow<R, R::Output>) -> R {
    match cf {
        ControlFlow::Continue(v) => R::from_output(v),
        ControlFlow::Break(v) => v,
    }
}

impl<T, L, F> From<StdResult<T, L>> for Result<T, L, F> {
    fn from(result: StdResult<T, L>) -> Result<T, L, F> {
        match result {
            Ok(t) => Success(t),
            Err(l) => LocalErr(l),
        }
    }
}

impl<T, L, F> From<StdResult<StdResult<T, L>, F>> for Result<T, L, F> {
    fn from(result: StdResult<StdResult<T, L>, F>) -> Result<T, L, F> {
        match result {
            Ok(inner) => match inner {
                Ok(ok) => Success(ok),
                Err(err) => LocalErr(err),
            },
            Err(err) => FatalErr(err),
        }
    }
}

impl<T, L, F> From<Result<T, L, F>> for StdResult<StdResult<T, L>, F> {
    fn from(other: Result<T, L, F>) -> StdResult<StdResult<T, L>, F> {
        match other {
            Success(ok) => Ok(Ok(ok)),
            LocalErr(err) => Ok(Err(err)),
            FatalErr(err) => Err(err),
        }
    }
}

#[cfg(feature = "serde")]
impl<T, L, F> Serialize for Result<T, L, F>
where
    T: Serialize,
    L: Serialize,
    F: Serialize,
{
    fn serialize<S>(&self, serializer: S) -> StdResult<S::Ok, S::Error>
    where
        S: Serializer,
    {
        // Convert `woah::Result` into `StdResult<StdResult<&T, &L>, &F>` and serialize that.
        self.as_ref().into_result().serialize(serializer)
    }
}

#[cfg(feature = "serde")]
impl<'de, T, L, F> Deserialize<'de> for Result<T, L, F>
where
    T: Deserialize<'de>,
    L: Deserialize<'de>,
    F: Deserialize<'de>,
{
    fn deserialize<D>(deserializer: D) -> StdResult<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        // Deserialize a `std::result::Result`.
        let result: StdResult<StdResult<T, L>, F> = StdResult::deserialize(deserializer)?;
        // Convert to a `woah::Result`.
        let result: Result<T, L, F> = result.into();
        // Wrap it for the return.
        Ok(result)
    }
}
