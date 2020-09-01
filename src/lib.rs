//!`woah` is a Rust crate which provides the following type:
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
#![cfg_attr(feature = "try_trait", feature(try_trait))]
#![cfg_attr(feature = "try_trait", doc(test(attr(feature(try_trait)))))]
// Turn on the `TrustedLen` trait.
#![cfg_attr(feature = "trusted_len", feature(trusted_len))]
// Enable use of the never type (`!`) in generic code.
#![cfg_attr(feature = "never_type", feature(never_type))]
// Turn on the `Termination` trait.
#![cfg_attr(feature = "termination_trait", feature(termination_trait_lib))]
// Turn on the `ExitCode` type.
#![cfg_attr(feature = "termination_trait", feature(process_exitcode_placeholder))]
// Turn on clippy lints.
#![deny(clippy::all)]
#![deny(clippy::cargo)]
// Turn on useful warnings (make `deny` once all are resolved.)
//#![warn(missing_docs)]
//#![warn(missing_doc_code_examples)]
//#![warn(private_doc_tests)]
#![warn(missing_debug_implementations)]
#![warn(missing_copy_implementations)]

#[cfg(any(
    feature = "from_iterator_trait",
    feature = "product_trait",
    feature = "sum_trait"
))]
use crate::LoopState::{Break, Continue};
use crate::Result::{FatalErr, LocalErr, Ok};
use core::fmt::Debug;
#[cfg(feature = "from_iterator_trait")]
use core::iter::FromIterator;
#[cfg(feature = "product_trait")]
use core::iter::Product;
#[cfg(feature = "sum_trait")]
use core::iter::Sum;
#[cfg(feature = "trusted_len")]
use core::iter::TrustedLen;
use core::iter::{DoubleEndedIterator, FusedIterator, Iterator};
#[cfg(feature = "try_trait")]
use core::ops::Try;
use core::ops::{Deref, DerefMut};
use core::result::{Result as StdResult, Result::Err as StdErr, Result::Ok as StdOk};
#[cfg(feature = "either_methods")]
use either::Either::{self, Left, Right};
#[cfg(feature = "serde")]
use serde::{Deserialize, Deserializer, Serialize, Serializer};
use std::convert::{From, Into};
#[cfg(all(feature = "termination_trait", feature = "std"))]
use std::process::{ExitCode, Termination};

pub mod prelude {
    //! A collection of re-exports to make `woah::Result` the standard result type.
    //!
    //! This keeps `std::result::Result` available as `StdResult`, and imports additional types and traits
    //! to make `woah::Result` fully-featured, based on feature flags.

    // Replace `std::result::Result` with `woah::Result`.
    pub use crate::{Result, Result::FatalErr, Result::LocalErr, Result::Ok};
    pub use std::result::{Result as StdResult, Result::Err as StdErr, Result::Ok as StdOk};

    // Import the Try trait.
    #[cfg(feature = "try_trait")]
    pub use std::ops::Try;

    // Import the Termination trait.
    #[cfg(all(feature = "termination_trait", feature = "std"))]
    pub use std::process::Termination;

    // Import the FromIterator trait.
    #[cfg(feature = "from_iterator_trait")]
    pub use core::iter::FromIterator;

    // Import the Product trait.
    #[cfg(feature = "product_trait")]
    pub use core::iter::Product;

    // Import the Sum trait.
    #[cfg(feature = "sum_trait")]
    pub use core::iter::Sum;

    // Import the TrustedLen trait.
    #[cfg(feature = "trusted_len")]
    pub use core::iter::TrustedLen;
}

pub mod docs {
    //! Documentation, including crate features and examples.
    //!
    //! # Why are the docs like this?
    //!
    //! Putting the docs in Rustdoc means they can be run as documentation tests. Breaking them up into modules and
    //! submodules helps keep them from getting too unwieldy, so people can still navigate the API itself with ease.

    pub mod concept {
        //! Explanation of why `woah` exists.

        // TODO: Write the rest of this.
    }

    pub mod methods {
        //! An explanation of `woah::Result`'s methods.
        //!
        //! `woah::Result` has a lot of methods, and the way they're grouped and presented by Rustdoc isn't always
        //! easy to navigate. To help, this page explains them in groups of similar methods, and includes a Table
        //! of Contents to make it easy to find again in the future.
        //!
        //! # Table of Contents
        //!
        //! 1. [See if the `Result` is a particular variant][is]
        //! 2. [See if the `Result` contains a value][contains]
        //! 3. [Get an `Option` if a variant is present][get]
        //! 4. [Reference the contained value][as_ref]
        //! 5. [Dereference the contained value][as_deref]
        //! 6. [Map over the contained value][map]
        //! 7. [Iterate over the contained value][iter]
        //! 8. [Compose `Result`s][compose]
        //! 9. [Unwrap the `Result`][unwrap]
        //! 10. [Copy or clone the contained value][clone]
        //! 11. [Transpose when holding an `Option`][transpose]
        //! 12. [Convert to and from a `std::result::Result`][convert]
        //! 13. [Use `woah::Result` with the question mark operator][try]
        //! 14. [Use `woah::Result` as the return type of `main`][main]
        //! 15. [Build a `woah::Result` from an iterator][from_iter]
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
        //! # Methods
        //!
        //! ## See if the `Result` is a particular variant
        //!
        //! These methods, the "is" methods, return a `bool` based on what variant is present.
        //!
        //! 1. [`is_ok`](../../enum.Result.html#method.is_ok)
        //! 2. [`is_err`](../../enum.Result.html#method.is_err)
        //! 3. [`is_local_err`](../../enum.Result.html#method.is_local_err)
        //! 4. [`is_fatal_err`](../../enum.Result.html#method.is_fatal_err)
        //!
        //! ---
        //!
        //! ## See if the `Result` contains a value
        //!
        //! These methods check if the `Result` contains a particular value.
        //!
        //! 1. [`contains`](../../enum.Result.html#method.contains)
        //! 2. [`contains_err`](../../enum.Result.html#method.contains_err)
        //! 3. [`contains_local_err`](../../enum.Result.html#method.contains_local_err)
        //! 4. [`contains_fatal_err`](../../enum.Result.html#method.contains_fatal_err)
        //!
        //! ---
        //!
        //! ## Get an `Option` if a variant is present
        //!
        //! These methods try to get the contained value out, returning an `Option` in case it's
        //! another variant.
        //!
        //! 1. [`ok`](../../enum.Result.html#method.ok)
        //! 2. [`err`](../../enum.Result.html#method.err)
        //! 3. [`local_err`](../../enum.Result.html#method.local_err)
        //! 4. [`fatal_err`](../../enum.Result.html#method.fatal_err)
        //!
        //! ---
        //!
        //! ## Reference the contained value
        //!
        //! Gets a reference (immutable or mutable) to the contained value.
        //!
        //! 1. [`as_ref`](../../enum.Result.html#method.as_ref)
        //! 2. [`as_mut`](../../enum.Result.html#method.as_mut)
        //!
        //! ---
        //!
        //! ## Dereference the contained value
        //!
        //! Dereferences the contained value if it implements `Deref`.
        //!
        //! 1. [`as_deref`](../../enum.Result.html#method.as_deref)
        //! 2. [`as_deref_err`](../../enum.Result.html#method.as_deref_err)
        //! 3. [`as_deref_local_err`](../../enum.Result.html#method.as_deref_local_err)
        //! 4. [`as_deref_fatal_err`](../../enum.Result.html#method.as_deref_fatal_err)
        //!
        //!
        //! 1. [`as_deref_mut`](../../enum.Result.html#method.as_deref_mut)
        //! 2. [`as_deref_mut_err`](../../enum.Result.html#method.as_deref_mut_err)
        //! 3. [`as_deref_mut_local_err`](../../enum.Result.html#method.as_deref_mut_local_err)
        //! 4. [`as_deref_mut_fatal_err`](../../enum.Result.html#method.as_deref_mut_fatal_err)
        //!
        //! ---
        //!
        //! ## Map over the contained value
        //!
        //! Applies some function to the contained value.
        //!
        //! 1. [`map`](../../enum.Result.html#method.map)
        //! 2. [`map_or`](../../enum.Result.html#method.map_or)
        //! 3. [`map_or_else`](../../enum.Result.html#method.map_or_else)
        //!
        //!
        //! 1. [`map_err`](../../enum.Result.html#method.map_err)
        //! 2. [`map_err_or`](../../enum.Result.html#method.map_err_or)
        //! 3. [`map_err_or_else`](../../enum.Result.html#method.map_err_or_else)
        //!
        //!
        //! 1. [`map_local_err`](../../enum.Result.html#method.map_local_err)
        //! 2. [`map_local_err_or`](../../enum.Result.html#method.map_local_err_or)
        //! 3. [`map_local_err_or_else`](../../enum.Result.html#method.map_local_err_or_else)
        //!
        //!
        //! 1. [`map_fatal_err`](../../enum.Result.html#method.map_fatal_err)
        //! 2. [`map_fatal_err_or`](../../enum.Result.html#method.map_fatal_err_or)
        //! 3. [`map_fatal_err_or_else`](../../enum.Result.html#method.map_fatal_err_or_else)
        //!
        //! ---
        //!
        //! ## Iterate over the contained value
        //!
        //! ---
        //!
        //! ## Compose `Result`s
        //!
        //! ---
        //!
        //! ## Unwrap the `Result`
        //!
        //! ---
        //!
        //! ## Copy or clone the contained value
        //!
        //! ---
        //!
        //! ## Transpose when holding an `Option`
        //!
        //! ---
        //!
        //! ## Convert to and from a `std::result::Result`
        //!
        //! ---
        //!
        //! ## Use `woah::Result` with the question mark operator
        //!
        //! ---
        //!
        //! ## Use `woah::Result` as the return type of `main`
        //!
        //! ---
        //!
        //! ## Build a `woah::Result` from an iterator
        //!
        //!
        //! <style>
        //! hr { border: 0; background-color: transparent; height: 0; display: block; border-bottom: 1px solid transparent; margin: 3rem 0 0 0; }
        //! </style>
    }

    pub mod features {
        //! Features to configure based on stable vs. nightly, std vs. no_std, or a desire for no dependencies.
        //!
        //! # Features
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
        //! you can disable the `either_methods` feature, which otherwise imports the `either` crate to add additional
        //! methods.
        //!
        //!| Feature Name          | Channels              | Depends On         | What It Does |
        //!|:----------------------|:----------------------|:-------------------|:-------------|
        //!| `default`             | Stable, Beta, Nightly | `either_methods`   | Enables default features (currently just `either_methods`). |
        //!| `nightly`             | Nightly               | `try_trait`, `trusted_len`, `never_type`, `termination_trait`, `product_trait`, `sum_trait`, `from_iterator_trait` | Enables all nightly-only features. __This feature is permanently unstable, and changes to the APIs enabled by this feature are never considered breaking changes.__ |
        //!| `serde`               | Stable, Beta, Nightly |                    | Implements `serde::Serialize` and `serde::Deserialize` for `woah::Result`. |
        //!| `std`                 | Stable, Beta, Nightly | None               | Use the standard library. Turn off to make the crate `no_std` compatible. _Turning off the standard library conflicts with the `termination_trait` feature, so turning off `std` will automatically disable that feature._ |
        //!| `either_methods`      | Stable, Beta, Nightly | None               | Adds the `either` crate as a dependency and provides convenience methods for operating on `Either<LocalErr, FatalErr>`. |
        //!| `try_trait`           | Nightly               | None               | Enables the `Try` trait, so `woah::Result` can be used with the question mark operator. |
        //!| `trusted_len`         | Nightly               | None               | Enables `woah::Result::{IntoIter, Iter, IterMut}` to implement the `TrustedLen` trait. |
        //!| `never_type`          | Nightly               | None               | Enables the `into_ok` method if both the `LocalErr` and `FatalErr` variant types are `!` (the never type). |
        //!| `termination_trait`   | Nightly               | `never_type`       | Enables `woah::Result` to be used as the return type for the `main` function. _This requires the `std` feature to be turned on as well (which it is by default)._ |
        //!| `product_trait`       | Nightly               | `try_trait`        | Enables the `std::iter::Product` trait. |
        //!| `sum_trait`           | Nightly               | `try_trait`        | Enables the `std::iter::Sum` trait. |
        //!| `from_iterator_trait` | Nightly               | `try_trait`        | Enables the `FromIterator` trait, which also enables convenient `collect`ing of `Vec<woah::Result<T, L, F>>` into `woah::Result<Vec<T>, L, F>` |
    }

    pub mod examples {
        //! Examples of using `woah` on both stable and nightly.
        //!
        //! # Table of Contents
        //!
        //! 1. [Example on stable](#example-on-stable)
        //! 2. [Example on nightly](#example-on-nightly)
        //!
        //! # Example on stable
        //!
        //! ```
        //! use woah::prelude::*;
        //! use std::cmp::Ordering;
        //!
        //! match get_number() {
        //!     StdOk(num) => println!("Got a number: {}", num),
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
        //!     StdOk(num)
        //! }
        //!
        //! fn compare_numbers(x: i64, y: i64) -> StdResult<StdResult<i64, LocalError>, FatalError> {
        //!     match x.cmp(&y) {
        //!         Ordering::Greater => Ok(x),
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
        //! # Example on nightly
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
        //!     StdOk(num) => println!("Got a number: {}", num),
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
        //!     StdOk(num)
        //! }
        //!
        //! # #[cfg(feature = "nightly")]
        //! fn compare_numbers(x: i64, y: i64) -> Result<i64, LocalError, FatalError> {
        //!     match x.cmp(&y) {
        //!         Ordering::Greater => Ok(x),
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
}

/// A type representing success (`Ok`), a local error (`LocalErr`), or a fatal error (`FatalErr`).
///
/// See the [`woah`](index.html) top-level documentation for details.
#[derive(Copy, PartialEq, PartialOrd, Eq, Ord, Debug, Hash)]
#[must_use = "this `Result` may be a `LocalErr`, which should be handled, or a `FatalErr`, which should be propagated"]
pub enum Result<T, L, F> {
    /// Contains the success value.
    Ok(T),
    /// Contains a local error value (which should be handled)
    LocalErr(L),
    /// Contains a fatal error value (which should be propagated)
    FatalErr(F),
}

#[cfg(feature = "try_trait")]
impl<T, L, F> Try for Result<T, L, F> {
    type Ok = StdResult<T, L>;
    type Error = F;

    /// Convert `woah::Result<T, L, F>` into a `Result<Result<T, L>, F>`, which is equivalent
    /// in `?` behavior.
    ///
    /// # Example
    ///
    /// ```
    /// use woah::prelude::*;
    ///
    /// let result: StdResult<StdResult<i64, &str>, &str> = LocalErr("a local error").into_result();
    /// assert_eq!(result, StdOk(StdErr("a local error")));
    /// ```
    #[inline]
    fn into_result(self) -> StdResult<StdResult<T, L>, F> {
        self.into()
    }

    /// Construct the `FatalErr` variant based on some error.
    ///
    /// # Example
    ///
    /// ```
    /// use woah::prelude::*;
    ///
    /// let fatal_err: Result<i64, &str, &str> = Result::from_error("a fatal error");
    /// assert_eq!(fatal_err, FatalErr("a fatal error"));
    /// ```
    #[inline]
    fn from_error(err: F) -> Self {
        FatalErr(err)
    }

    /// Construct either an `Ok` or `LocalErr` variant based on a
    /// `Result`.
    ///
    /// # Example
    ///
    /// ```
    /// use woah::prelude::*;
    ///
    /// // Construct a `LocalErr` variant.
    /// let local_err: Result<i64, &str, &str> = Result::from_ok(StdErr("a local error"));
    /// assert_eq!(local_err, LocalErr("a local error"));
    ///
    /// // Construct an `Ok` variant.
    /// let ok: Result<i64, &str, &str> = Result::from_ok(StdOk(42));
    /// assert_eq!(ok, Ok(42));
    /// ```
    #[inline]
    fn from_ok(ok: StdResult<T, L>) -> Self {
        match ok {
            StdOk(t) => Ok(t),
            StdErr(err) => LocalErr(err),
        }
    }
}

#[cfg(not(feature = "try_trait"))]
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
    /// assert_eq!(result, StdOk(StdErr("a local error")));
    /// ```
    #[inline]
    pub fn into_result(self) -> StdResult<StdResult<T, L>, F> {
        self.into()
    }

    /// Construct the `FatalErr` variant based on some error.
    ///
    /// # Example
    ///
    /// ```
    /// use woah::prelude::*;
    ///
    /// let fatal_err: Result<i64, &str, &str> = Result::from_error("a fatal error");
    /// assert_eq!(fatal_err, FatalErr("a fatal error"));
    /// ```
    #[inline]
    pub fn from_error(err: F) -> Self {
        FatalErr(err)
    }

    /// Construct either an `Ok` or `LocalErr` variant based on a
    /// `Result`.
    ///
    /// # Example
    ///
    /// ```
    /// use woah::prelude::*;
    ///
    /// let result: StdResult<StdResult<i64, &str>, &str> = LocalErr("a local error").into_result();
    /// assert_eq!(result, StdOk(StdErr("a local error")));
    /// ```
    #[inline]
    pub fn from_ok(ok: StdResult<T, L>) -> Self {
        match ok {
            StdOk(t) => Ok(t),
            StdErr(err) => LocalErr(err),
        }
    }
}

impl<T, L, F> Result<T, L, F> {
    /// Returns `true` if the result is [`Ok`].
    ///
    /// [`Ok`]: enum.Result.html#variant.Ok
    ///
    /// # Example
    ///
    /// ```
    /// use woah::prelude::*;
    ///
    /// let x: Result<i32, &str, &str> = Ok(-3);
    /// assert_eq!(x.is_ok(), true);
    ///
    /// let x: Result<i32, &str, &str> = LocalErr("Some error message");
    /// assert_eq!(x.is_ok(), false);
    ///
    /// let x: Result<i32, &str, &str> = FatalErr("Another error message");
    /// assert_eq!(x.is_ok(), false);
    /// ```
    #[must_use = "if you intended to assert that this is ok, consider `.unwrap()` instead"]
    #[inline]
    pub fn is_ok(&self) -> bool {
        match self {
            Ok(_) => true,
            _ => false,
        }
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
    /// let x: Result<i32, &str, &str> = Ok(-3);
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
        !self.is_ok()
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
    /// let x: Result<i32, &str, &str> = Ok(-3);
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
        match self {
            LocalErr(_) => true,
            _ => false,
        }
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
    /// let x: Result<i32, &str, &str> = Ok(-3);
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
        match self {
            FatalErr(_) => true,
            _ => false,
        }
    }

    /// Returns `true` if the result is an [`Ok`] value containing the given value.
    ///
    /// [`Ok`]: enum.Result.html#variant.Ok
    ///
    /// # Examples
    ///
    /// ```
    /// use woah::prelude::*;
    ///
    /// let x: Result<u32, &str, &str> = Ok(2);
    /// assert_eq!(x.contains(&2), true);
    ///
    /// let x: Result<u32, &str, &str> = Ok(3);
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
        match self {
            Ok(t) if *x == *t => true,
            _ => false,
        }
    }

    #[cfg(feature = "either_methods")]
    #[must_use]
    #[inline]
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

    #[must_use]
    #[inline]
    pub fn contains_local_err<E>(&self, e: &E) -> bool
    where
        E: PartialEq<L>,
    {
        match self {
            LocalErr(err) if *e == *err => true,
            _ => false,
        }
    }

    #[must_use]
    #[inline]
    pub fn contains_fatal_err<E>(&self, e: &E) -> bool
    where
        E: PartialEq<F>,
    {
        match self {
            FatalErr(err) if *e == *err => true,
            _ => false,
        }
    }

    #[inline]
    pub fn ok(self) -> Option<T> {
        match self {
            Ok(t) => Some(t),
            _ => None,
        }
    }

    #[cfg(feature = "either_methods")]
    #[inline]
    pub fn err(self) -> Option<Either<L, F>> {
        match self {
            LocalErr(err) => Some(Left(err)),
            FatalErr(err) => Some(Right(err)),
            _ => None,
        }
    }

    #[inline]
    pub fn local_err(self) -> Option<L> {
        match self {
            LocalErr(err) => Some(err),
            _ => None,
        }
    }

    #[inline]
    pub fn fatal_err(self) -> Option<F> {
        match self {
            FatalErr(err) => Some(err),
            _ => None,
        }
    }

    #[inline]
    pub fn as_ref(&self) -> Result<&T, &L, &F> {
        match self {
            Ok(t) => Ok(t),
            LocalErr(err) => LocalErr(err),
            FatalErr(err) => FatalErr(err),
        }
    }

    #[inline]
    pub fn as_mut(&mut self) -> Result<&mut T, &mut L, &mut F> {
        match self {
            Ok(t) => Ok(t),
            LocalErr(err) => LocalErr(err),
            FatalErr(err) => FatalErr(err),
        }
    }

    #[inline]
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

    #[inline]
    pub fn map_or<U, G>(self, default: U, f: G) -> U
    where
        G: FnOnce(T) -> U,
    {
        match self {
            Ok(t) => f(t),
            _ => default,
        }
    }

    #[inline]
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

    #[cfg(feature = "either_methods")]
    #[inline]
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

    #[inline]
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

    #[inline]
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

    #[inline]
    pub fn iter(&self) -> Iter<T> {
        let inner = match self {
            Ok(t) => Some(t),
            _ => None,
        };

        Iter { inner }
    }

    #[inline]
    pub fn iter_mut(&mut self) -> IterMut<T> {
        let inner = match self {
            Ok(t) => Some(t),
            _ => None,
        };

        IterMut { inner }
    }

    #[inline]
    pub fn and<U>(self, res: Result<U, L, F>) -> Result<U, L, F> {
        match self {
            Ok(_) => res,
            LocalErr(err) => LocalErr(err),
            FatalErr(err) => FatalErr(err),
        }
    }

    #[inline]
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

    #[inline]
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

    #[inline]
    pub fn or_local<M>(self, res: Result<T, M, F>) -> Result<T, M, F> {
        match self {
            Ok(t) => Ok(t),
            LocalErr(_) => res,
            FatalErr(err) => FatalErr(err),
        }
    }

    #[inline]
    pub fn or_fatal<G>(self, res: Result<T, L, G>) -> Result<T, L, G> {
        match self {
            Ok(t) => Ok(t),
            LocalErr(err) => LocalErr(err),
            FatalErr(_) => res,
        }
    }

    #[inline]
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

    #[inline]
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

    #[inline]
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

    #[inline]
    pub fn unwrap_or(self, optb: T) -> T {
        match self {
            Ok(t) => t,
            _ => optb,
        }
    }

    #[inline]
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
    #[inline]
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
    #[inline]
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
    #[inline]
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
    #[inline]
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
    #[inline]
    pub fn unwrap(self) -> T {
        match self {
            Ok(t) => t,
            LocalErr(err) => panic!("{:?}", err),
            FatalErr(err) => panic!("{:?}", err),
        }
    }

    #[inline]
    pub fn expect(self, msg: &str) -> T {
        match self {
            Ok(t) => t,
            LocalErr(_) => panic!("{}", msg),
            FatalErr(_) => panic!("{}", msg),
        }
    }
}

#[cfg(feature = "either_methods")]
impl<T, L, F> Result<T, L, F>
where
    T: Debug,
    L: Debug,
    F: Debug,
{
    #[inline]
    pub fn unwrap_err(self) -> Either<L, F> {
        match self {
            Ok(t) => panic!("{:?}", t),
            LocalErr(err) => Left(err),
            FatalErr(err) => Right(err),
        }
    }

    #[inline]
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
    #[inline]
    pub fn unwrap_local_err(self) -> L {
        match self {
            Ok(t) => panic!("{:?}", t),
            LocalErr(err) => err,
            FatalErr(err) => panic!("{:?}", err),
        }
    }

    #[inline]
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
    #[inline]
    pub fn unwrap_fatal_err(self) -> F {
        match self {
            Ok(t) => panic!("{:?}", t),
            LocalErr(err) => panic!("{:?}", err),
            FatalErr(err) => err,
        }
    }

    #[inline]
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
    #[inline]
    pub fn unwrap_or_default(self) -> T {
        match self {
            Ok(t) => t,
            _ => T::default(),
        }
    }

    #[inline]
    pub fn into_result_default(self) -> StdResult<T, F> {
        match self {
            Ok(t) => StdOk(t),
            LocalErr(_) => StdOk(T::default()),
            FatalErr(err) => StdErr(err),
        }
    }
}

#[cfg(feature = "never_type")]
impl<T, L, F> Result<T, L, F>
where
    L: Into<!>,
    F: Into<!>,
{
    #[inline]
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
    #[inline]
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
    #[inline]
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
    #[inline]
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
    #[inline]
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
    #[inline]
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
    #[inline]
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
    #[inline]
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
    #[inline]
    pub fn as_deref_mut_fatal_err(&mut self) -> Result<&mut T, &mut L, &mut <F as Deref>::Target> {
        match self {
            Ok(t) => Ok(t),
            LocalErr(err) => LocalErr(err),
            FatalErr(err) => FatalErr(err.deref_mut()),
        }
    }
}

impl<T, L, F> Result<Option<T>, L, F> {
    #[inline]
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
    #[inline]
    fn clone(&self) -> Result<T, L, F> {
        match self {
            Ok(t) => Ok(t.clone()),
            LocalErr(err) => LocalErr(err.clone()),
            FatalErr(err) => FatalErr(err.clone()),
        }
    }

    #[inline]
    fn clone_from(&mut self, source: &Result<T, L, F>) {
        match (self, source) {
            (Ok(to), Ok(from)) => to.clone_from(from),
            (LocalErr(to), LocalErr(from)) => to.clone_from(from),
            (FatalErr(to), FatalErr(from)) => to.clone_from(from),
            (to, from) => *to = from.clone(),
        }
    }
}

#[cfg(feature = "from_iterator_trait")]
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
        IntoIter { inner: self.ok() }
    }
}

#[cfg(feature = "product_trait")]
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

#[cfg(feature = "sum_trait")]
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

#[cfg(all(feature = "termination_trait", feature = "std"))]
impl<L, F> Termination for Result<(), L, F>
where
    L: Debug,
    F: Debug,
{
    #[inline]
    fn report(self) -> i32 {
        match self {
            Ok(()) => ().report(),
            LocalErr(err) => LocalErr::<!, L, F>(err).report(),
            FatalErr(err) => FatalErr::<!, L, F>(err).report(),
        }
    }
}

#[cfg(all(feature = "termination_trait", feature = "std"))]
impl<L, F> Termination for Result<!, L, F>
where
    L: Debug,
    F: Debug,
{
    #[inline]
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

/// An iterator over the value in an `Ok` variant of a `woah::Result`.
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

/// An iterator over a reference to the `Ok` variant of a `woah::Result`.
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

#[cfg(feature = "trusted_len")]
unsafe impl<'a, T> TrustedLen for Iter<'a, T> {}

/// An iterator over a mutable reference to the `Ok` variant of a `woah::Result`.
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

#[cfg(feature = "trusted_len")]
unsafe impl<'a, T> TrustedLen for IterMut<'a, T> {}

#[cfg(any(
    feature = "from_iterator_trait",
    feature = "product_trait",
    feature = "sum_trait"
))]
pub(crate) struct ResultShunt<'a, I, L, F> {
    iter: I,
    error: &'a mut Result<(), L, F>,
}

#[cfg(any(
    feature = "from_iterator_trait",
    feature = "product_trait",
    feature = "sum_trait"
))]
#[inline]
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

#[cfg(any(
    feature = "from_iterator_trait",
    feature = "product_trait",
    feature = "sum_trait"
))]
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

#[cfg(any(
    feature = "from_iterator_trait",
    feature = "product_trait",
    feature = "sum_trait"
))]
#[derive(PartialEq)]
enum LoopState<C, B> {
    Continue(C),
    Break(B),
}

#[cfg(any(
    feature = "from_iterator_trait",
    feature = "product_trait",
    feature = "sum_trait"
))]
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

#[cfg(any(
    feature = "from_iterator_trait",
    feature = "product_trait",
    feature = "sum_trait"
))]
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

impl<T, L, F> From<StdResult<StdResult<T, L>, F>> for Result<T, L, F> {
    fn from(result: StdResult<StdResult<T, L>, F>) -> Result<T, L, F> {
        match result {
            StdOk(inner) => match inner {
                StdOk(ok) => Ok(ok),
                StdErr(err) => LocalErr(err),
            },
            StdErr(err) => FatalErr(err),
        }
    }
}

impl<T, L, F> Into<StdResult<StdResult<T, L>, F>> for Result<T, L, F> {
    fn into(self) -> StdResult<StdResult<T, L>, F> {
        match self {
            Ok(ok) => StdOk(StdOk(ok)),
            LocalErr(err) => StdOk(StdErr(err)),
            FatalErr(err) => StdErr(err),
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
        StdOk(result)
    }
}
