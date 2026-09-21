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
//! [docs]: crate::docs

#![doc(issue_tracker_base_url = "https://github.com/alilleybrinker/woah/issues/")]
#![cfg_attr(not(feature = "std"), no_std)]
// Turn on the `Try` trait for both code and documentation tests.
#![cfg_attr(feature = "nightly", feature(try_trait_v2))]
#![cfg_attr(feature = "nightly", feature(trusted_len))]
#![cfg_attr(feature = "nightly", doc(test(attr(feature(try_trait_v2)))))]
#![cfg_attr(feature = "nightly", doc(test(attr(feature(trusted_len)))))]
// Turn on clippy lints.
#![deny(clippy::all)]
#![deny(clippy::cargo)]
// Every public item is documented with an example, so this is a hard error.
#![deny(missing_docs)]
// These two are still off: `missing_doc_code_examples` is an unstable rustdoc
// lint, and both it and `private_doc_tests` now live behind a `rustdoc::`
// prefix, so the bare names would themselves warn.
//#![warn(rustdoc::missing_doc_code_examples)]
//#![warn(rustdoc::private_doc_tests)]
#![warn(missing_debug_implementations)]
#![warn(missing_copy_implementations)]

use crate::Result::{FatalErr, LocalErr, Success};
#[cfg(feature = "nightly")]
use core::convert::Infallible;
use core::convert::{From, Into};
use core::fmt::Debug;
use core::hint::unreachable_unchecked;
#[cfg(feature = "nightly")]
use core::iter::FromIterator;
#[cfg(feature = "nightly")]
use core::iter::Product;
#[cfg(feature = "nightly")]
use core::iter::Sum;
#[cfg(feature = "nightly")]
use core::iter::TrustedLen;
use core::iter::{DoubleEndedIterator, ExactSizeIterator, FusedIterator, Iterator};
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
    //! This shadows `std::result::Result`, keeping it available as `StdResult`, and imports the
    //! variant names so they can be written unqualified.
    //!
    //! It deliberately re-exports very little else. `?` needs no trait in scope, being desugared
    //! by the compiler, and `collect`, `sum` and `product` are `Iterator` methods, so `Try`,
    //! `FromResidual`, `FromIterator`, `Sum` and `Product` do not need importing to use any of
    //! them on a `woah::Result`. A prelude meant for glob import should not put names in scope
    //! that nothing here requires.

    // Replace `std::result::Result` with `woah::Result`.
    //
    // This also imports the variant names for `woah::Result`, so they can be
    // referenced directly.
    pub use crate::{Result, Result::FatalErr, Result::LocalErr, Result::Success};
    pub use core::result::Result as StdResult;

    // Unlike the traits above, this one is load-bearing: `fn main() -> woah::Result<..>` works
    // without it, but calling `report` directly does not.
    #[cfg(feature = "std")]
    pub use std::process::Termination;
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
    //! 1. [`is_success`](crate::Result::is_success)
    //! 2. [`is_err`](crate::Result::is_err)
    //! 3. [`is_local_err`](crate::Result::is_local_err)
    //! 4. [`is_fatal_err`](crate::Result::is_fatal_err)
    //!
    //! ### Get an `Option` if a variant is present
    //!
    //! These methods try to get the contained value out, returning an `Option` in case it's
    //! another variant.
    //!
    //! 1. [`success`](crate::Result::success)
    #![cfg_attr(feature = "either", doc = "2. [`err`](crate::Result::err)")]
    //! 3. [`local_err`](crate::Result::local_err)
    //! 4. [`fatal_err`](crate::Result::fatal_err)
    //!
    //! ### Reference the contained value
    //!
    //! Gets a reference (immutable or mutable) to the contained value.
    //!
    //! 1. [`as_ref`](crate::Result::as_ref)
    //! 2. [`as_mut`](crate::Result::as_mut)
    //!
    //! ### Dereference the contained value
    //!
    //! Dereferences the contained value if it implements `Deref`.
    //!
    //! 1. [`as_deref`](crate::Result::as_deref)
    //! 2. [`as_deref_err`](crate::Result::as_deref_err)
    //! 3. [`as_deref_local_err`](crate::Result::as_deref_local_err)
    //! 4. [`as_deref_fatal_err`](crate::Result::as_deref_fatal_err)
    //!
    //! Dereferences the contained value mutably if it implements `DerefMut`.
    //!
    //! 1. [`as_deref_mut`](crate::Result::as_deref_mut)
    //! 2. [`as_deref_mut_err`](crate::Result::as_deref_mut_err)
    //! 3. [`as_deref_mut_local_err`](crate::Result::as_deref_mut_local_err)
    //! 4. [`as_deref_mut_fatal_err`](crate::Result::as_deref_mut_fatal_err)
    //!
    //! ### Map over the contained value
    //!
    //! Applies some function to the contained value.
    //!
    //! 1. [`map`](crate::Result::map)
    //! 2. [`map_or`](crate::Result::map_or)
    //! 3. [`map_or_else`](crate::Result::map_or_else)
    //!
    //! Applies some function to the contained value, if it's a local or fatal error.
    //!
    #![cfg_attr(feature = "either", doc = "1. [`map_err`](crate::Result::map_err)")]
    #![cfg_attr(
        feature = "either",
        doc = "2. [`map_err_or`](crate::Result::map_err_or)"
    )]
    #![cfg_attr(
        feature = "either",
        doc = "3. [`map_err_or_else`](crate::Result::map_err_or_else)"
    )]
    //!
    //! Applies some function to the contained value, if it's a local error.
    //!
    //! 1. [`map_local_err`](crate::Result::map_local_err)
    //! 2. [`map_local_err_or_else`](crate::Result::map_local_err_or_else)
    //!
    //! Applies some function to the contained value, if it's a fatal error.
    //!
    //! 1. [`map_fatal_err`](crate::Result::map_fatal_err)
    //! 2. [`map_fatal_err_or_else`](crate::Result::map_fatal_err_or_else)
    //!
    //! ### Iterate over the contained value
    //!
    //! 1. [`iter`](crate::Result::iter)
    //! 2. [`iter_mut`](crate::Result::iter_mut)
    //! 3. [`into_iter`](crate::Result#method.into_iter-2) (for `woah::Result`)
    //! 4. [`into_iter`](crate::Result#method.into_iter-1) (for `&woah::Result`)
    //! 5. [`into_iter`](crate::Result#method.into_iter) (for `&mut woah::Result`)
    //!
    //! ### Compose `Result`s
    //!
    //! 1. [`and`](crate::Result::and)
    //! 2. [`and_then`](crate::Result::and_then)
    //! 3. [`or`](crate::Result::or)
    //! 4. [`or_else`](crate::Result::or_else)
    //! 5. [`or_else_fatal_err`](crate::Result::or_else_fatal_err)
    //! 6. [`or_else_local_err`](crate::Result::or_else_local_err)
    //! 7. [`or_fatal_err`](crate::Result::or_fatal_err)
    //! 8. [`or_local_err`](crate::Result::or_local_err)
    //!
    //! ### Unwrap the `Result`
    //!
    //! 1. [`unwrap`](crate::Result::unwrap)
    #![cfg_attr(
        feature = "either",
        doc = "2. [`unwrap_err`](crate::Result::unwrap_err)"
    )]
    //! 3. [`unwrap_fatal_err`](crate::Result::unwrap_fatal_err)
    //! 4. [`unwrap_local_err`](crate::Result::unwrap_local_err)
    //! 5. [`unwrap_or`](crate::Result::unwrap_or)
    //! 6. [`unwrap_or_default`](crate::Result::unwrap_or_default)
    //! 7. [`unwrap_or_else`](crate::Result::unwrap_or_else)
    //! 8. [`expect`](crate::Result::expect)
    #![cfg_attr(
        feature = "either",
        doc = "9. [`expect_err`](crate::Result::expect_err)"
    )]
    //! 10. [`expect_fatal_err`](crate::Result::expect_fatal_err)
    //! 11. [`expect_local_err`](crate::Result::expect_local_err)
    //!
    //! ### Copy or clone the contained value
    //!
    //! 1. [`cloned`](crate::Result::cloned) (for `&woah::Result`)
    //! 2. [`cloned`](crate::Result#method.cloned-1) (for `&mut woah::Result`)
    //! 1. [`copied`](crate::Result::copied) (for `&woah::Result`)
    //! 2. [`copied`](crate::Result#method.copied-1) (for `&mut woah::Result`)
    //!
    //! ### Transpose when holding an `Option`
    //!
    //! 1. [`transpose`](crate::Result::transpose)
    //!
    //! ### Convert to and from a `std::result::Result`
    //!
    //! The names say which `std::result::Result` is involved. `Result<T, L>` carries only the
    //! local error -- it is what `?` hands back -- and the nested `Result<Result<T, L>, F>` puts
    //! the fatal error outside and the local one inside. Note that `Result<T, F>`, carrying only
    //! the fatal error, is a third shape: [`into_merged_result`](crate::Result::into_merged_result)
    //! produces it, and nothing constructs a `woah::Result` from it.
    //!
    //! 1. [`from_local_result`](crate::Result::from_local_result)
    //! 1. [`from_nested_result`](crate::Result::from_nested_result)
    //! 1. [`into_nested_result`](crate::Result::into_nested_result)
    //! 1. [`into_merged_result`](crate::Result::into_merged_result)
    //!
    //! ### Use `woah::Result` with the question mark operator
    //!
    //! 1. [`Try` impl](crate::Result#trait-implementations) (nightly-only, with the `nightly` feature)
    //!
    //! ### Use `woah::Result` as the return type of `main`
    //!
    //! 1. [`Termination` impl](crate::Result#trait-implementations) (with the `std` feature, for
    //!    any success type that implements `Termination` itself, which includes `()` and, on
    //!    nightly, `!`)
    //!
    //! ### Build a `woah::Result` from an iterator
    //!
    //! 1. [`FromIterator` impl](crate::Result#trait-implementations) (nightly-only, with the `nightly` feature)
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
    //!| `nightly`     | Nightly 1.100+        | None               | Enables all nightly-only features. Requires Rust 1.100 or later, when the `!` type stabilized. __This feature is permanently unstable, and changes to the APIs enabled by this feature are never considered breaking changes.__ |
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
    //!     }.into_nested_result()
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
/// See the [`woah`](crate) top-level documentation for details.
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
    /// Convert into the nested `Result<Result<T, L>, F>`, which is equivalent in `?` behavior:
    /// the fatal error is the outer `Err`, and the local error the inner one.
    ///
    /// The inverse is [`from_nested_result`]. Note that it is *not* [`from_local_result`], which
    /// takes a `Result<T, L>` with no fatal channel at all; round-tripping through that pair
    /// nests one layer deeper each time.
    ///
    /// [`from_nested_result`]: crate::Result::from_nested_result
    /// [`from_local_result`]: crate::Result::from_local_result
    ///
    /// # Example
    ///
    /// ```
    /// use woah::prelude::*;
    ///
    /// let result: StdResult<StdResult<i64, &str>, &str> = LocalErr("a local error").into_nested_result();
    /// assert_eq!(result, Ok(Err("a local error")));
    /// ```
    #[inline]
    pub fn into_nested_result(self) -> StdResult<StdResult<T, L>, F> {
        self.into()
    }

    /// Construct a [`Success`] or a [`LocalErr`] from a `Result<T, L>` carrying the local error.
    ///
    /// This is the shape `?` hands back: `Try::Output` for `woah::Result` is `Result<T, L>`,
    /// because a fatal error breaks early and never reaches it. So this method re-wraps what `?`
    /// gave you, and carries no fatal error to put in a [`FatalErr`].
    ///
    /// For the nested `Result<Result<T, L>, F>` that [`into_nested_result`] produces, use
    /// [`from_nested_result`], which is its inverse and can produce all three variants.
    ///
    /// [`Success`]: crate::Result::Success
    /// [`LocalErr`]: crate::Result::LocalErr
    /// [`FatalErr`]: crate::Result::FatalErr
    /// [`into_nested_result`]: crate::Result::into_nested_result
    /// [`from_nested_result`]: crate::Result::from_nested_result
    ///
    /// # Example
    ///
    /// ```
    /// use woah::prelude::*;
    ///
    /// let result: Result<i64, &str, &str> = Result::from_local_result(Ok(0));
    /// assert_eq!(result, Success(0));
    /// ```
    #[inline]
    pub fn from_local_result(ok: StdResult<T, L>) -> Self {
        match ok {
            Ok(t) => Success(t),
            Err(err) => LocalErr(err),
        }
    }

    /// Construct any of the three variants from the nested `Result<Result<T, L>, F>`.
    ///
    /// This is the inverse of [`into_nested_result`]: the outer `Err` becomes a [`FatalErr`],
    /// the inner one a [`LocalErr`], and `Ok(Ok(_))` a [`Success`]. Unlike
    /// [`from_local_result`], which takes a `Result<T, L>` and so can only produce the first
    /// two variants, this can produce all three.
    ///
    /// [`Success`]: crate::Result::Success
    /// [`LocalErr`]: crate::Result::LocalErr
    /// [`FatalErr`]: crate::Result::FatalErr
    /// [`into_nested_result`]: crate::Result::into_nested_result
    /// [`from_local_result`]: crate::Result::from_local_result
    ///
    /// # Example
    ///
    /// ```
    /// use woah::prelude::*;
    ///
    /// let result: Result<i64, &str, &str> = Result::from_nested_result(Ok(Ok(0)));
    /// assert_eq!(result, Success(0));
    ///
    /// let result: Result<i64, &str, &str> = Result::from_nested_result(Ok(Err("local")));
    /// assert_eq!(result, LocalErr("local"));
    ///
    /// let result: Result<i64, &str, &str> = Result::from_nested_result(Err("fatal"));
    /// assert_eq!(result, FatalErr("fatal"));
    /// ```
    ///
    /// Round-tripping through [`into_nested_result`] gets the original back, which
    /// [`from_local_result`] cannot do:
    ///
    /// ```
    /// use woah::prelude::*;
    ///
    /// for result in [
    ///     Success(0),
    ///     LocalErr("a local error"),
    ///     FatalErr("a fatal error"),
    /// ] {
    ///     let result: Result<i64, &str, &str> = result;
    ///     assert_eq!(Result::from_nested_result(result.into_nested_result()), result);
    /// }
    /// ```
    #[inline]
    pub fn from_nested_result(nested: StdResult<StdResult<T, L>, F>) -> Self {
        // Delegates to the `From` impl so the two cannot drift apart.
        From::from(nested)
    }

    /// Construct the [`Success`] variant based on some success value.
    ///
    /// [`Success`]: crate::Result::Success
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
    pub const fn from_success(val: T) -> Self {
        Success(val)
    }

    /// Construct the [`LocalErr`] variant based on some error.
    ///
    /// [`LocalErr`]: crate::Result::LocalErr
    ///
    /// # Example
    ///
    /// ```
    /// use woah::prelude::*;
    ///
    /// let fatal_err: Result<i64, &str, &str> = Result::from_fatal_err("a fatal error");
    /// assert_eq!(fatal_err, FatalErr("a fatal error"));
    /// ```
    #[inline]
    pub const fn from_local_err(err: L) -> Self {
        LocalErr(err)
    }

    /// Construct the [`FatalErr`] variant based on some error.
    ///
    /// [`FatalErr`]: crate::Result::FatalErr
    ///
    /// # Example
    ///
    /// ```
    /// use woah::prelude::*;
    ///
    /// let fatal_err: Result<i64, &str, &str> = Result::from_fatal_err("a fatal error");
    /// assert_eq!(fatal_err, FatalErr("a fatal error"));
    /// ```
    #[inline]
    pub const fn from_fatal_err(err: F) -> Self {
        FatalErr(err)
    }

    /// Returns `true` if the result is [`Success`].
    ///
    /// [`Success`]: crate::Result::Success
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
    pub const fn is_success(&self) -> bool {
        matches!(self, Success(_))
    }

    /// Returns `true` if the result is [`LocalErr`] or [`FatalErr`].
    ///
    /// [`LocalErr`]: crate::Result::LocalErr
    /// [`FatalErr`]: crate::Result::FatalErr
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
    pub const fn is_err(&self) -> bool {
        !self.is_success()
    }

    /// Returns `true` if the result is [`LocalErr`].
    ///
    /// [`LocalErr`]: crate::Result::LocalErr
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
    pub const fn is_local_err(&self) -> bool {
        matches!(self, LocalErr(_))
    }

    /// Returns `true` if the result is [`FatalErr`].
    ///
    /// [`FatalErr`]: crate::Result::FatalErr
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
    pub const fn is_fatal_err(&self) -> bool {
        matches!(self, FatalErr(_))
    }

    /// Returns `true` if the result is a [`Success`] whose value matches a predicate.
    ///
    /// [`Success`]: crate::Result::Success
    ///
    /// # Example
    ///
    /// ```
    /// use woah::prelude::*;
    ///
    /// let x: Result<u32, &str, &str> = Success(2);
    /// assert_eq!(x.is_success_and(|t| t > 1), true);
    ///
    /// let x: Result<u32, &str, &str> = Success(0);
    /// assert_eq!(x.is_success_and(|t| t > 1), false);
    ///
    /// let x: Result<u32, &str, &str> = LocalErr("Some error message");
    /// assert_eq!(x.is_success_and(|t| t > 1), false);
    /// ```
    #[must_use]
    #[inline]
    pub fn is_success_and<G>(self, f: G) -> bool
    where
        G: FnOnce(T) -> bool,
    {
        match self {
            Success(t) => f(t),
            _ => false,
        }
    }

    /// Returns `true` if the result is a [`LocalErr`] or [`FatalErr`] whose value matches a
    /// predicate.
    ///
    /// [`LocalErr`]: crate::Result::LocalErr
    /// [`FatalErr`]: crate::Result::FatalErr
    ///
    /// # Example
    ///
    /// ```
    /// use woah::prelude::*;
    /// use either::Either::{self, Left, Right};
    ///
    /// fn is_big(err: Either<u32, u32>) -> bool {
    ///     match err {
    ///         Left(l) => l > 1,
    ///         Right(f) => f > 1,
    ///     }
    /// }
    ///
    /// let x: Result<&str, u32, u32> = LocalErr(2);
    /// assert_eq!(x.is_err_and(is_big), true);
    ///
    /// let x: Result<&str, u32, u32> = FatalErr(2);
    /// assert_eq!(x.is_err_and(is_big), true);
    ///
    /// let x: Result<&str, u32, u32> = FatalErr(0);
    /// assert_eq!(x.is_err_and(is_big), false);
    ///
    /// let x: Result<&str, u32, u32> = Success("all good");
    /// assert_eq!(x.is_err_and(is_big), false);
    /// ```
    #[cfg(feature = "either")]
    #[must_use]
    #[inline]
    pub fn is_err_and<G>(self, f: G) -> bool
    where
        G: FnOnce(Either<L, F>) -> bool,
    {
        match self {
            Success(_) => false,
            LocalErr(err) => f(Left(err)),
            FatalErr(err) => f(Right(err)),
        }
    }

    /// Returns `true` if the result is a [`LocalErr`] whose value matches a predicate.
    ///
    /// [`LocalErr`]: crate::Result::LocalErr
    ///
    /// # Example
    ///
    /// ```
    /// use woah::prelude::*;
    ///
    /// let x: Result<&str, u32, u32> = LocalErr(2);
    /// assert_eq!(x.is_local_err_and(|l| l > 1), true);
    ///
    /// let x: Result<&str, u32, u32> = LocalErr(0);
    /// assert_eq!(x.is_local_err_and(|l| l > 1), false);
    ///
    /// let x: Result<&str, u32, u32> = FatalErr(2);
    /// assert_eq!(x.is_local_err_and(|l| l > 1), false);
    /// ```
    #[must_use]
    #[inline]
    pub fn is_local_err_and<G>(self, f: G) -> bool
    where
        G: FnOnce(L) -> bool,
    {
        match self {
            LocalErr(err) => f(err),
            _ => false,
        }
    }

    /// Returns `true` if the result is a [`FatalErr`] whose value matches a predicate.
    ///
    /// [`FatalErr`]: crate::Result::FatalErr
    ///
    /// # Example
    ///
    /// ```
    /// use woah::prelude::*;
    ///
    /// let x: Result<&str, u32, u32> = FatalErr(2);
    /// assert_eq!(x.is_fatal_err_and(|f| f > 1), true);
    ///
    /// let x: Result<&str, u32, u32> = FatalErr(0);
    /// assert_eq!(x.is_fatal_err_and(|f| f > 1), false);
    ///
    /// let x: Result<&str, u32, u32> = LocalErr(2);
    /// assert_eq!(x.is_fatal_err_and(|f| f > 1), false);
    /// ```
    #[must_use]
    #[inline]
    pub fn is_fatal_err_and<G>(self, f: G) -> bool
    where
        G: FnOnce(F) -> bool,
    {
        match self {
            FatalErr(err) => f(err),
            _ => false,
        }
    }

    /// Convert a [`Success`] variant to an `Option::Some`, otherwise to a `None`.
    ///
    /// [`Success`]: crate::Result::Success
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
    /// [`LocalErr`]: crate::Result::LocalErr
    /// [`FatalErr`]: crate::Result::FatalErr
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
    /// [`LocalErr`]: crate::Result::LocalErr
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
    /// [`FatalErr`]: crate::Result::FatalErr
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
    pub const fn as_ref(&self) -> Result<&T, &L, &F> {
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
    pub const fn as_mut(&mut self) -> Result<&mut T, &mut L, &mut F> {
        match self {
            Success(t) => Success(t),
            LocalErr(err) => LocalErr(err),
            FatalErr(err) => FatalErr(err),
        }
    }

    /// Apply a function to the contained value if it's a [`Success`].
    ///
    /// [`Success`]: crate::Result::Success
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
    /// [`Success`]: crate::Result::Success
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
    /// [`Success`]: crate::Result::Success
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
    /// [`LocalErr`]: crate::Result::LocalErr
    /// [`FatalErr`]: crate::Result::FatalErr
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

    /// Apply a function to the contained value if it's a [`LocalErr`] or [`FatalErr`], or return
    /// a default.
    ///
    /// **The [`Success`] value is discarded.** The default stands in for it, so the success value
    /// never reaches the caller. Use [`map_err_or_else`] to map it instead of dropping it.
    ///
    /// [`Success`]: crate::Result::Success
    /// [`LocalErr`]: crate::Result::LocalErr
    /// [`FatalErr`]: crate::Result::FatalErr
    /// [`map_err_or_else`]: crate::Result::map_err_or_else
    ///
    /// # Example
    ///
    /// ```
    /// use woah::prelude::*;
    /// use either::Either::{self, Left, Right};
    ///
    /// fn size(err: Either<u32, u32>) -> u32 {
    ///     match err {
    ///         Left(l) => l + 1,
    ///         Right(f) => f + 2,
    ///     }
    /// }
    ///
    /// let x: Result<u32, u32, u32> = LocalErr(0);
    /// assert_eq!(x.map_err_or(5, size), 1);
    ///
    /// let x: Result<u32, u32, u32> = FatalErr(0);
    /// assert_eq!(x.map_err_or(5, size), 2);
    ///
    /// // The success value is discarded; only the default comes back.
    /// let x: Result<u32, u32, u32> = Success(0);
    /// assert_eq!(x.map_err_or(5, size), 5);
    /// ```
    #[cfg(feature = "either")]
    #[inline]
    pub fn map_err_or<U, G>(self, default: U, f: G) -> U
    where
        G: FnOnce(Either<L, F>) -> U,
    {
        match self {
            Success(_) => default,
            LocalErr(err) => f(Left(err)),
            FatalErr(err) => f(Right(err)),
        }
    }

    /// Apply a function to the contained value if it's a [`LocalErr`] or [`FatalErr`].
    ///
    /// Otherwise run the provided default function on the [`Success`] value. Unlike
    /// [`map_err_or`], nothing is discarded: every variant reaches a function.
    ///
    /// [`Success`]: crate::Result::Success
    /// [`LocalErr`]: crate::Result::LocalErr
    /// [`FatalErr`]: crate::Result::FatalErr
    /// [`map_err_or`]: crate::Result::map_err_or
    ///
    /// # Example
    ///
    /// ```
    /// use woah::prelude::*;
    /// use either::Either::{self, Left, Right};
    ///
    /// fn size(err: Either<u32, u32>) -> u32 {
    ///     match err {
    ///         Left(l) => l + 1,
    ///         Right(f) => f + 2,
    ///     }
    /// }
    ///
    /// let x: Result<u32, u32, u32> = LocalErr(0);
    /// assert_eq!(x.map_err_or_else(|s| s + 3, size), 1);
    ///
    /// let x: Result<u32, u32, u32> = FatalErr(0);
    /// assert_eq!(x.map_err_or_else(|s| s + 3, size), 2);
    ///
    /// let x: Result<u32, u32, u32> = Success(0);
    /// assert_eq!(x.map_err_or_else(|s| s + 3, size), 3);
    /// ```
    #[cfg(feature = "either")]
    #[inline]
    pub fn map_err_or_else<U, SD, G>(self, default_success: SD, f: G) -> U
    where
        SD: FnOnce(T) -> U,
        G: FnOnce(Either<L, F>) -> U,
    {
        match self {
            Success(t) => default_success(t),
            LocalErr(err) => f(Left(err)),
            FatalErr(err) => f(Right(err)),
        }
    }

    /// Apply a function to the contained value if it's a [`LocalErr`].
    ///
    /// [`LocalErr`]: crate::Result::LocalErr
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

    /// Apply a function to the contained value if it's a [`LocalErr`].
    ///
    /// Otherwise run one of the provided default functions. Nothing is discarded: the
    /// [`Success`] and [`FatalErr`] variants each get their own function, so a fatal error
    /// cannot be mistaken for a success.
    ///
    /// [`Success`]: crate::Result::Success
    /// [`LocalErr`]: crate::Result::LocalErr
    /// [`FatalErr`]: crate::Result::FatalErr
    ///
    /// # Example
    ///
    /// ```
    /// use woah::prelude::*;
    ///
    /// let x: Result<u32, u32, u32> = LocalErr(0);
    /// assert_eq!(x.map_local_err_or_else(|s| s + 2, |f| f + 3, |l| l + 1), 1);
    ///
    /// let x: Result<u32, u32, u32> = Success(0);
    /// assert_eq!(x.map_local_err_or_else(|s| s + 2, |f| f + 3, |l| l + 1), 2);
    ///
    /// let x: Result<u32, u32, u32> = FatalErr(0);
    /// assert_eq!(x.map_local_err_or_else(|s| s + 2, |f| f + 3, |l| l + 1), 3);
    /// ```
    #[inline]
    pub fn map_local_err_or_else<U, SD, FD, G>(
        self,
        default_success: SD,
        default_fatal: FD,
        f: G,
    ) -> U
    where
        SD: FnOnce(T) -> U,
        FD: FnOnce(F) -> U,
        G: FnOnce(L) -> U,
    {
        match self {
            Success(t) => default_success(t),
            LocalErr(err) => f(err),
            FatalErr(err) => default_fatal(err),
        }
    }

    /// Apply a function to the contained value if it's a [`FatalErr`].
    ///
    /// [`FatalErr`]: crate::Result::FatalErr
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

    /// Apply a function to the contained value if it's a [`FatalErr`].
    ///
    /// Otherwise run one of the provided default functions. Nothing is discarded: the
    /// [`Success`] and [`LocalErr`] variants each get their own function, so a local error
    /// cannot be mistaken for a success.
    ///
    /// [`Success`]: crate::Result::Success
    /// [`LocalErr`]: crate::Result::LocalErr
    /// [`FatalErr`]: crate::Result::FatalErr
    ///
    /// # Example
    ///
    /// ```
    /// use woah::prelude::*;
    ///
    /// let x: Result<u32, u32, u32> = FatalErr(0);
    /// assert_eq!(x.map_fatal_err_or_else(|s| s + 2, |l| l + 3, |f| f + 1), 1);
    ///
    /// let x: Result<u32, u32, u32> = Success(0);
    /// assert_eq!(x.map_fatal_err_or_else(|s| s + 2, |l| l + 3, |f| f + 1), 2);
    ///
    /// let x: Result<u32, u32, u32> = LocalErr(0);
    /// assert_eq!(x.map_fatal_err_or_else(|s| s + 2, |l| l + 3, |f| f + 1), 3);
    /// ```
    #[inline]
    pub fn map_fatal_err_or_else<U, SD, LD, G>(
        self,
        default_success: SD,
        default_local: LD,
        f: G,
    ) -> U
    where
        SD: FnOnce(T) -> U,
        LD: FnOnce(L) -> U,
        G: FnOnce(F) -> U,
    {
        match self {
            Success(t) => default_success(t),
            LocalErr(err) => default_local(err),
            FatalErr(err) => f(err),
        }
    }

    /// Apply a function to the contained value if it's a [`Success`], without modifying it.
    ///
    /// [`Success`]: crate::Result::Success
    ///
    /// # Example
    ///
    /// ```
    /// use woah::prelude::*;
    ///
    /// let mut seen = None;
    ///
    /// let x: Result<u32, u32, u32> = Success(0);
    /// assert_eq!(x.inspect(|t| seen = Some(*t)), Success(0));
    /// assert_eq!(seen, Some(0));
    ///
    /// let x: Result<u32, u32, u32> = LocalErr(1);
    /// assert_eq!(x.inspect(|t| seen = Some(*t)), LocalErr(1));
    /// assert_eq!(seen, Some(0));
    /// ```
    #[inline]
    pub fn inspect<G>(self, f: G) -> Self
    where
        G: FnOnce(&T),
    {
        if let Success(t) = &self {
            f(t);
        }

        self
    }

    /// Apply a function to the contained value if it's a [`LocalErr`] or [`FatalErr`], without
    /// modifying it.
    ///
    /// [`LocalErr`]: crate::Result::LocalErr
    /// [`FatalErr`]: crate::Result::FatalErr
    ///
    /// # Example
    ///
    /// ```
    /// use woah::prelude::*;
    /// use either::Either::{Left, Right};
    ///
    /// let mut seen = None;
    ///
    /// let x: Result<u32, u32, u32> = FatalErr(1);
    /// let x = x.inspect_err(|e| {
    ///     seen = Some(match e {
    ///         Left(l) => *l,
    ///         Right(f) => *f,
    ///     })
    /// });
    ///
    /// assert_eq!(x, FatalErr(1));
    /// assert_eq!(seen, Some(1));
    ///
    /// let x: Result<u32, u32, u32> = Success(0);
    /// assert_eq!(x.inspect_err(|_| seen = None), Success(0));
    /// assert_eq!(seen, Some(1));
    /// ```
    #[cfg(feature = "either")]
    #[inline]
    pub fn inspect_err<G>(self, f: G) -> Self
    where
        G: FnOnce(Either<&L, &F>),
    {
        match &self {
            Success(_) => {}
            LocalErr(err) => f(Left(err)),
            FatalErr(err) => f(Right(err)),
        }

        self
    }

    /// Apply a function to the contained value if it's a [`LocalErr`], without modifying it.
    ///
    /// [`LocalErr`]: crate::Result::LocalErr
    ///
    /// # Example
    ///
    /// ```
    /// use woah::prelude::*;
    ///
    /// let mut seen = None;
    ///
    /// let x: Result<u32, u32, u32> = LocalErr(0);
    /// assert_eq!(x.inspect_local_err(|l| seen = Some(*l)), LocalErr(0));
    /// assert_eq!(seen, Some(0));
    ///
    /// let x: Result<u32, u32, u32> = FatalErr(1);
    /// assert_eq!(x.inspect_local_err(|l| seen = Some(*l)), FatalErr(1));
    /// assert_eq!(seen, Some(0));
    /// ```
    #[inline]
    pub fn inspect_local_err<G>(self, f: G) -> Self
    where
        G: FnOnce(&L),
    {
        if let LocalErr(err) = &self {
            f(err);
        }

        self
    }

    /// Apply a function to the contained value if it's a [`FatalErr`], without modifying it.
    ///
    /// [`FatalErr`]: crate::Result::FatalErr
    ///
    /// # Example
    ///
    /// ```
    /// use woah::prelude::*;
    ///
    /// let mut seen = None;
    ///
    /// let x: Result<u32, u32, u32> = FatalErr(0);
    /// assert_eq!(x.inspect_fatal_err(|f| seen = Some(*f)), FatalErr(0));
    /// assert_eq!(seen, Some(0));
    ///
    /// let x: Result<u32, u32, u32> = LocalErr(1);
    /// assert_eq!(x.inspect_fatal_err(|f| seen = Some(*f)), LocalErr(1));
    /// assert_eq!(seen, Some(0));
    /// ```
    #[inline]
    pub fn inspect_fatal_err<G>(self, f: G) -> Self
    where
        G: FnOnce(&F),
    {
        if let FatalErr(err) = &self {
            f(err);
        }

        self
    }

    /// Get an iterator over the inner value in the `Result`, if it's a [`Success`].
    ///
    /// [`Success`]: crate::Result::Success
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
    pub const fn iter(&self) -> Iter<'_, T> {
        let inner = match self {
            Success(t) => Some(t),
            _ => None,
        };

        Iter { inner }
    }

    /// Get a mutable iterator over the inner value in the `Result`, if it's a [`Success`].
    ///
    /// [`Success`]: crate::Result::Success
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
    pub const fn iter_mut(&mut self) -> IterMut<'_, T> {
        let inner = match self {
            Success(t) => Some(t),
            _ => None,
        };

        IterMut { inner }
    }

    /// If it's a [`Success`], replace it with `res`.
    ///
    /// [`Success`]: crate::Result::Success
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
    /// [`Success`]: crate::Result::Success
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
    /// [`LocalErr`]: crate::Result::LocalErr
    /// [`FatalErr`]: crate::Result::FatalErr
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
    /// [`LocalErr`]: crate::Result::LocalErr
    ///
    /// # Example
    ///
    /// ```
    /// use woah::prelude::*;
    ///
    /// let l: Result<u32, u32, u32> = LocalErr(1);
    ///
    /// let r: Result<u32, u32, u32> = Success(0);
    /// assert_eq!(r.or_local_err(l), Success(0));
    ///
    /// let r: Result<u32, u32, u32> = LocalErr(0);
    /// assert_eq!(r.or_local_err(l), LocalErr(1));
    ///
    /// let r: Result<u32, u32, u32> = FatalErr(0);
    /// assert_eq!(r.or_local_err(l), FatalErr(0));
    /// ```
    #[inline]
    pub fn or_local_err<M>(self, res: Result<T, M, F>) -> Result<T, M, F> {
        match self {
            Success(t) => Success(t),
            LocalErr(_) => res,
            FatalErr(err) => FatalErr(err),
        }
    }

    /// If it's a [`FatalErr`], replace them with the given value.
    ///
    /// [`FatalErr`]: crate::Result::FatalErr
    ///
    /// # Example
    ///
    /// ```
    /// use woah::prelude::*;
    ///
    /// let f: Result<u32, u32, u32> = FatalErr(2);
    ///
    /// let r: Result<u32, u32, u32> = Success(0);
    /// assert_eq!(r.or_fatal_err(f), Success(0));
    ///
    /// let r: Result<u32, u32, u32> = LocalErr(0);
    /// assert_eq!(r.or_fatal_err(f), LocalErr(0));
    ///
    /// let r: Result<u32, u32, u32> = FatalErr(0);
    /// assert_eq!(r.or_fatal_err(f), FatalErr(2));
    /// ```
    #[inline]
    pub fn or_fatal_err<G>(self, res: Result<T, L, G>) -> Result<T, L, G> {
        match self {
            Success(t) => Success(t),
            LocalErr(err) => LocalErr(err),
            FatalErr(_) => res,
        }
    }

    /// If it's a [`LocalErr`] or [`FatalErr`], replace them with the appropriate function result.
    ///
    /// [`LocalErr`]: crate::Result::LocalErr
    /// [`FatalErr`]: crate::Result::FatalErr
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
    /// [`LocalErr`]: crate::Result::LocalErr
    ///
    /// # Example
    ///
    /// ```
    /// use woah::prelude::*;
    ///
    /// let l = |l| LocalErr(l + 1);
    ///
    /// let r: Result<u32, u32, u32> = Success(0);
    /// assert_eq!(r.or_else_local_err(l), Success(0));
    ///
    /// let r: Result<u32, u32, u32> = LocalErr(0);
    /// assert_eq!(r.or_else_local_err(l), LocalErr(1));
    ///
    /// let r: Result<u32, u32, u32> = FatalErr(0);
    /// assert_eq!(r.or_else_local_err(l), FatalErr(0));
    /// ```
    #[inline]
    pub fn or_else_local_err<O, M>(self, op: O) -> Result<T, M, F>
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
    /// [`FatalErr`]: crate::Result::FatalErr
    ///
    /// # Example
    ///
    /// ```
    /// use woah::prelude::*;
    ///
    /// let f = |f| FatalErr(f + 2);
    ///
    /// let r: Result<u32, u32, u32> = Success(0);
    /// assert_eq!(r.or_else_fatal_err(f), Success(0));
    ///
    /// let r: Result<u32, u32, u32> = LocalErr(0);
    /// assert_eq!(r.or_else_fatal_err(f), LocalErr(0));
    ///
    /// let r: Result<u32, u32, u32> = FatalErr(0);
    /// assert_eq!(r.or_else_fatal_err(f), FatalErr(2));
    /// ```
    #[inline]
    pub fn or_else_fatal_err<O, G>(self, op: O) -> Result<T, L, G>
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
    /// [`Success`]: crate::Result::Success
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
    /// [`Success`]: crate::Result::Success
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

impl<T, L, F> Result<&T, L, F>
where
    T: Copy,
{
    /// Copy the value if it's a [`Success`].
    ///
    /// [`Success`]: crate::Result::Success
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

impl<T, L, F> Result<&mut T, L, F>
where
    T: Copy,
{
    /// Copy the value if it's a [`Success`].
    ///
    /// [`Success`]: crate::Result::Success
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

impl<T, L, F> Result<&T, L, F>
where
    T: Clone,
{
    /// Clone the value if it's a [`Success`].
    ///
    /// [`Success`]: crate::Result::Success
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

impl<T, L, F> Result<&mut T, L, F>
where
    T: Clone,
{
    /// Clone the value if it's a [`Success`].
    ///
    /// [`Success`]: crate::Result::Success
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
    /// [`Success`]: crate::Result::Success
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
    /// [`Success`]: crate::Result::Success
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
    /// Get the error if it's a [`LocalErr`] or [`FatalErr`], panic otherwise.
    ///
    /// [`LocalErr`]: crate::Result::LocalErr
    /// [`FatalErr`]: crate::Result::FatalErr
    ///
    /// # Example
    ///
    /// ```
    /// use woah::prelude::*;
    /// use either::Either::{Left, Right};
    ///
    /// let r: Result<u32, u32, u32> = LocalErr(0);
    /// assert_eq!(r.unwrap_err(), Left(0));
    ///
    /// let r: Result<u32, u32, u32> = FatalErr(1);
    /// assert_eq!(r.unwrap_err(), Right(1));
    /// ```
    #[inline]
    pub fn unwrap_err(self) -> Either<L, F> {
        match self {
            Success(t) => panic!("{:?}", t),
            LocalErr(err) => Left(err),
            FatalErr(err) => Right(err),
        }
    }

    /// Get the error if it's a [`LocalErr`] or [`FatalErr`], panic with a `msg` otherwise.
    ///
    /// [`LocalErr`]: crate::Result::LocalErr
    /// [`FatalErr`]: crate::Result::FatalErr
    ///
    /// # Example
    ///
    /// ```
    /// use woah::prelude::*;
    /// use either::Either::Right;
    ///
    /// let r: Result<u32, u32, u32> = FatalErr(0);
    /// assert_eq!(r.expect_err("should be an error"), Right(0));
    /// ```
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
    /// Get the error if it's a [`LocalErr`], panic otherwise.
    ///
    /// This panics on a [`FatalErr`] as well as on a [`Success`].
    ///
    /// [`Success`]: crate::Result::Success
    /// [`LocalErr`]: crate::Result::LocalErr
    /// [`FatalErr`]: crate::Result::FatalErr
    ///
    /// # Example
    ///
    /// ```
    /// use woah::prelude::*;
    ///
    /// let r: Result<u32, u32, u32> = LocalErr(0);
    /// assert_eq!(r.unwrap_local_err(), 0);
    /// ```
    #[inline]
    pub fn unwrap_local_err(self) -> L {
        match self {
            Success(t) => panic!("{:?}", t),
            LocalErr(err) => err,
            FatalErr(err) => panic!("{:?}", err),
        }
    }

    /// Get the error if it's a [`LocalErr`], panic with a `msg` otherwise.
    ///
    /// This panics on a [`FatalErr`] as well as on a [`Success`].
    ///
    /// [`Success`]: crate::Result::Success
    /// [`LocalErr`]: crate::Result::LocalErr
    /// [`FatalErr`]: crate::Result::FatalErr
    ///
    /// # Example
    ///
    /// ```
    /// use woah::prelude::*;
    ///
    /// let r: Result<u32, u32, u32> = LocalErr(0);
    /// assert_eq!(r.expect_local_err("should be a local error"), 0);
    /// ```
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
    /// Get the error if it's a [`FatalErr`], panic otherwise.
    ///
    /// This panics on a [`LocalErr`] as well as on a [`Success`].
    ///
    /// [`Success`]: crate::Result::Success
    /// [`LocalErr`]: crate::Result::LocalErr
    /// [`FatalErr`]: crate::Result::FatalErr
    ///
    /// # Example
    ///
    /// ```
    /// use woah::prelude::*;
    ///
    /// let r: Result<u32, u32, u32> = FatalErr(0);
    /// assert_eq!(r.unwrap_fatal_err(), 0);
    /// ```
    #[inline]
    pub fn unwrap_fatal_err(self) -> F {
        match self {
            Success(t) => panic!("{:?}", t),
            LocalErr(err) => panic!("{:?}", err),
            FatalErr(err) => err,
        }
    }

    /// Get the error if it's a [`FatalErr`], panic with a `msg` otherwise.
    ///
    /// This panics on a [`LocalErr`] as well as on a [`Success`].
    ///
    /// [`Success`]: crate::Result::Success
    /// [`LocalErr`]: crate::Result::LocalErr
    /// [`FatalErr`]: crate::Result::FatalErr
    ///
    /// # Example
    ///
    /// ```
    /// use woah::prelude::*;
    ///
    /// let r: Result<u32, u32, u32> = FatalErr(0);
    /// assert_eq!(r.expect_fatal_err("should be a fatal error"), 0);
    /// ```
    #[inline]
    pub fn expect_fatal_err(self, msg: &str) -> F {
        match self {
            Success(_) => panic!("{}", msg),
            LocalErr(_) => panic!("{}", msg),
            FatalErr(err) => err,
        }
    }
}
impl<T, L, F> Result<T, L, F> {
    /// Return the contained [`Success`] value, without checking that the value is a [`Success`].
    ///
    /// [`Success`]: crate::Result::Success
    ///
    /// # Safety
    ///
    /// Calling this on a [`LocalErr`] or [`FatalErr`] is undefined behavior.
    ///
    /// [`LocalErr`]: crate::Result::LocalErr
    /// [`FatalErr`]: crate::Result::FatalErr
    ///
    /// # Example
    ///
    /// ```
    /// use woah::prelude::*;
    ///
    /// let x: Result<u32, &str, &str> = Success(0);
    /// assert_eq!(unsafe { x.unwrap_unchecked() }, 0);
    /// ```
    #[inline]
    pub unsafe fn unwrap_unchecked(self) -> T {
        match self {
            Success(t) => t,
            // SAFETY: the caller guarantees this is a `Success`.
            _ => unsafe { unreachable_unchecked() },
        }
    }

    /// Return the contained [`LocalErr`] or [`FatalErr`] value, without checking that the value
    /// is one of them.
    ///
    /// [`LocalErr`]: crate::Result::LocalErr
    /// [`FatalErr`]: crate::Result::FatalErr
    ///
    /// # Safety
    ///
    /// Calling this on a [`Success`] is undefined behavior.
    ///
    /// [`Success`]: crate::Result::Success
    ///
    /// # Example
    ///
    /// ```
    /// use woah::prelude::*;
    /// use either::Either::{Left, Right};
    ///
    /// let x: Result<&str, u32, u32> = LocalErr(0);
    /// assert_eq!(unsafe { x.unwrap_err_unchecked() }, Left(0));
    ///
    /// let x: Result<&str, u32, u32> = FatalErr(1);
    /// assert_eq!(unsafe { x.unwrap_err_unchecked() }, Right(1));
    /// ```
    #[cfg(feature = "either")]
    #[inline]
    pub unsafe fn unwrap_err_unchecked(self) -> Either<L, F> {
        match self {
            LocalErr(err) => Left(err),
            FatalErr(err) => Right(err),
            // SAFETY: the caller guarantees this is a `LocalErr` or a `FatalErr`.
            Success(_) => unsafe { unreachable_unchecked() },
        }
    }

    /// Return the contained [`LocalErr`] value, without checking that the value is a [`LocalErr`].
    ///
    /// [`LocalErr`]: crate::Result::LocalErr
    ///
    /// # Safety
    ///
    /// Calling this on a [`Success`] or [`FatalErr`] is undefined behavior.
    ///
    /// [`Success`]: crate::Result::Success
    /// [`FatalErr`]: crate::Result::FatalErr
    ///
    /// # Example
    ///
    /// ```
    /// use woah::prelude::*;
    ///
    /// let x: Result<&str, u32, u32> = LocalErr(0);
    /// assert_eq!(unsafe { x.unwrap_local_err_unchecked() }, 0);
    /// ```
    #[inline]
    pub unsafe fn unwrap_local_err_unchecked(self) -> L {
        match self {
            LocalErr(err) => err,
            // SAFETY: the caller guarantees this is a `LocalErr`.
            _ => unsafe { unreachable_unchecked() },
        }
    }

    /// Return the contained [`FatalErr`] value, without checking that the value is a [`FatalErr`].
    ///
    /// [`FatalErr`]: crate::Result::FatalErr
    ///
    /// # Safety
    ///
    /// Calling this on a [`Success`] or [`LocalErr`] is undefined behavior.
    ///
    /// [`Success`]: crate::Result::Success
    /// [`LocalErr`]: crate::Result::LocalErr
    ///
    /// # Example
    ///
    /// ```
    /// use woah::prelude::*;
    ///
    /// let x: Result<&str, u32, u32> = FatalErr(0);
    /// assert_eq!(unsafe { x.unwrap_fatal_err_unchecked() }, 0);
    /// ```
    #[inline]
    pub unsafe fn unwrap_fatal_err_unchecked(self) -> F {
        match self {
            FatalErr(err) => err,
            // SAFETY: the caller guarantees this is a `FatalErr`.
            _ => unsafe { unreachable_unchecked() },
        }
    }
}

impl<T, L, F> Result<T, L, F>
where
    T: Default,
{
    /// Get the value if it's a [`Success`], or `T`'s default value otherwise.
    ///
    /// [`Success`]: crate::Result::Success
    ///
    /// # Example
    ///
    /// ```
    /// use woah::prelude::*;
    ///
    /// let r: Result<u32, &str, &str> = Success(5);
    /// assert_eq!(r.unwrap_or_default(), 5);
    ///
    /// let r: Result<u32, &str, &str> = LocalErr("a local error");
    /// assert_eq!(r.unwrap_or_default(), 0);
    ///
    /// let r: Result<u32, &str, &str> = FatalErr("a fatal error");
    /// assert_eq!(r.unwrap_or_default(), 0);
    /// ```
    #[inline]
    pub fn unwrap_or_default(self) -> T {
        match self {
            Success(t) => t,
            _ => T::default(),
        }
    }
}

impl<T, L, F> Result<T, L, F>
where
    F: From<L>,
{
    /// Convert into a `Result<T, F>`, merging the two error channels into one.
    ///
    /// The [`LocalErr`] value is converted into the fatal error type, so both errors come back
    /// as a single `Err`. When the two error types are the same, as in
    /// `woah::Result<T, E, E>`, that conversion is the identity and this is simply a way to
    /// stop distinguishing the two.
    ///
    /// This is not [`flatten`], which removes a layer of nesting rather than collapsing the
    /// error channels. To handle the local error some other way, take the nested form from
    /// [`into_nested_result`] and map over it.
    ///
    /// [`LocalErr`]: crate::Result::LocalErr
    /// [`flatten`]: crate::Result::flatten
    /// [`into_nested_result`]: crate::Result::into_nested_result
    ///
    /// # Example
    ///
    /// With one error type in both channels there is nothing to convert:
    ///
    /// ```
    /// use woah::prelude::*;
    ///
    /// let r: Result<u32, &str, &str> = Success(5);
    /// assert_eq!(r.into_merged_result(), Ok(5));
    ///
    /// let r: Result<u32, &str, &str> = LocalErr("an error");
    /// assert_eq!(r.into_merged_result(), Err("an error"));
    ///
    /// let r: Result<u32, &str, &str> = FatalErr("an error");
    /// assert_eq!(r.into_merged_result(), Err("an error"));
    /// ```
    ///
    /// With two error types, the local one escalates through its `From` impl:
    ///
    /// ```
    /// use woah::prelude::*;
    ///
    /// #[derive(Debug, PartialEq)]
    /// struct Timeout;
    ///
    /// #[derive(Debug, PartialEq)]
    /// enum Fatal {
    ///     GaveUp,
    ///     Unreachable,
    /// }
    ///
    /// impl From<Timeout> for Fatal {
    ///     fn from(_: Timeout) -> Fatal {
    ///         Fatal::GaveUp
    ///     }
    /// }
    ///
    /// let r: Result<u32, Timeout, Fatal> = LocalErr(Timeout);
    /// assert_eq!(r.into_merged_result(), Err(Fatal::GaveUp));
    ///
    /// let r: Result<u32, Timeout, Fatal> = FatalErr(Fatal::Unreachable);
    /// assert_eq!(r.into_merged_result(), Err(Fatal::Unreachable));
    /// ```
    #[inline]
    pub fn into_merged_result(self) -> StdResult<T, F> {
        match self {
            Success(t) => Ok(t),
            LocalErr(err) => Err(F::from(err)),
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
    /// Get the value, which must be a [`Success`] because neither error type can be constructed.
    ///
    /// The bounds mean this is only callable when both error types convert into the never type,
    /// so the [`LocalErr`] and [`FatalErr`] variants cannot exist.
    ///
    /// [`Success`]: crate::Result::Success
    /// [`LocalErr`]: crate::Result::LocalErr
    /// [`FatalErr`]: crate::Result::FatalErr
    ///
    /// # Example
    ///
    /// ```
    /// use woah::prelude::*;
    ///
    /// let r: Result<u32, !, !> = Success(5);
    /// assert_eq!(r.into_success(), 5);
    /// ```
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
    /// Convert to a `Result` holding a reference to the dereferenced [`Success`] value.
    ///
    /// [`Success`]: crate::Result::Success
    ///
    /// # Example
    ///
    /// ```
    /// use woah::prelude::*;
    ///
    /// let r: Result<String, u32, u32> = Success(String::from("hello"));
    /// assert_eq!(r.as_deref(), Success("hello"));
    ///
    /// let r: Result<String, u32, u32> = LocalErr(0);
    /// assert_eq!(r.as_deref(), LocalErr(&0));
    /// ```
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
    /// Convert to a `Result` holding references to the dereferenced [`LocalErr`] and
    /// [`FatalErr`] values.
    ///
    /// [`LocalErr`]: crate::Result::LocalErr
    /// [`FatalErr`]: crate::Result::FatalErr
    ///
    /// # Example
    ///
    /// ```
    /// use woah::prelude::*;
    ///
    /// let r: Result<u32, String, String> = LocalErr(String::from("a local error"));
    /// assert_eq!(r.as_deref_err(), LocalErr("a local error"));
    ///
    /// let r: Result<u32, String, String> = FatalErr(String::from("a fatal error"));
    /// assert_eq!(r.as_deref_err(), FatalErr("a fatal error"));
    /// ```
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
    /// Convert to a `Result` holding a reference to the dereferenced [`LocalErr`] value.
    ///
    /// [`LocalErr`]: crate::Result::LocalErr
    ///
    /// # Example
    ///
    /// ```
    /// use woah::prelude::*;
    ///
    /// let r: Result<u32, String, u32> = LocalErr(String::from("a local error"));
    /// assert_eq!(r.as_deref_local_err(), LocalErr("a local error"));
    ///
    /// let r: Result<u32, String, u32> = FatalErr(0);
    /// assert_eq!(r.as_deref_local_err(), FatalErr(&0));
    /// ```
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
    /// Convert to a `Result` holding a reference to the dereferenced [`FatalErr`] value.
    ///
    /// [`FatalErr`]: crate::Result::FatalErr
    ///
    /// # Example
    ///
    /// ```
    /// use woah::prelude::*;
    ///
    /// let r: Result<u32, u32, String> = FatalErr(String::from("a fatal error"));
    /// assert_eq!(r.as_deref_fatal_err(), FatalErr("a fatal error"));
    ///
    /// let r: Result<u32, u32, String> = LocalErr(0);
    /// assert_eq!(r.as_deref_fatal_err(), LocalErr(&0));
    /// ```
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
    /// Convert to a `Result` holding a mutable reference to the dereferenced [`Success`] value.
    ///
    /// [`Success`]: crate::Result::Success
    ///
    /// # Example
    ///
    /// ```
    /// use woah::prelude::*;
    ///
    /// let mut r: Result<String, u32, u32> = Success(String::from("hello"));
    ///
    /// if let Success(s) = r.as_deref_mut() {
    ///     s.make_ascii_uppercase();
    /// }
    ///
    /// assert_eq!(r, Success(String::from("HELLO")));
    /// ```
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
    /// Convert to a `Result` holding mutable references to the dereferenced [`LocalErr`] and
    /// [`FatalErr`] values.
    ///
    /// [`LocalErr`]: crate::Result::LocalErr
    /// [`FatalErr`]: crate::Result::FatalErr
    ///
    /// # Example
    ///
    /// ```
    /// use woah::prelude::*;
    ///
    /// let mut r: Result<u32, String, String> = FatalErr(String::from("a fatal error"));
    ///
    /// if let FatalErr(e) = r.as_deref_mut_err() {
    ///     e.make_ascii_uppercase();
    /// }
    ///
    /// assert_eq!(r, FatalErr(String::from("A FATAL ERROR")));
    /// ```
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
    /// Convert to a `Result` holding a mutable reference to the dereferenced [`LocalErr`] value.
    ///
    /// [`LocalErr`]: crate::Result::LocalErr
    ///
    /// # Example
    ///
    /// ```
    /// use woah::prelude::*;
    ///
    /// let mut r: Result<u32, String, u32> = LocalErr(String::from("a local error"));
    ///
    /// if let LocalErr(e) = r.as_deref_mut_local_err() {
    ///     e.make_ascii_uppercase();
    /// }
    ///
    /// assert_eq!(r, LocalErr(String::from("A LOCAL ERROR")));
    /// ```
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
    /// Convert to a `Result` holding a mutable reference to the dereferenced [`FatalErr`] value.
    ///
    /// [`FatalErr`]: crate::Result::FatalErr
    ///
    /// # Example
    ///
    /// ```
    /// use woah::prelude::*;
    ///
    /// let mut r: Result<u32, u32, String> = FatalErr(String::from("a fatal error"));
    ///
    /// if let FatalErr(e) = r.as_deref_mut_fatal_err() {
    ///     e.make_ascii_uppercase();
    /// }
    ///
    /// assert_eq!(r, FatalErr(String::from("A FATAL ERROR")));
    /// ```
    #[inline]
    pub fn as_deref_mut_fatal_err(&mut self) -> Result<&mut T, &mut L, &mut <F as Deref>::Target> {
        match self {
            Success(t) => Success(t),
            LocalErr(err) => LocalErr(err),
            FatalErr(err) => FatalErr(err.deref_mut()),
        }
    }
}

impl<T, L, F> Result<Result<T, L, F>, L, F> {
    /// Flatten a `Result` nested inside the [`Success`] variant of another `Result`.
    ///
    /// This removes a layer of nesting. To collapse a single `Result`'s two error channels into
    /// one instead, see [`into_merged_result`].
    ///
    /// [`Success`]: crate::Result::Success
    /// [`into_merged_result`]: crate::Result::into_merged_result
    ///
    /// # Example
    ///
    /// ```
    /// use woah::prelude::*;
    ///
    /// let x: Result<Result<u32, u32, u32>, u32, u32> = Success(Success(0));
    /// assert_eq!(x.flatten(), Success(0));
    ///
    /// let x: Result<Result<u32, u32, u32>, u32, u32> = Success(LocalErr(1));
    /// assert_eq!(x.flatten(), LocalErr(1));
    ///
    /// let x: Result<Result<u32, u32, u32>, u32, u32> = Success(FatalErr(2));
    /// assert_eq!(x.flatten(), FatalErr(2));
    ///
    /// let x: Result<Result<u32, u32, u32>, u32, u32> = LocalErr(3);
    /// assert_eq!(x.flatten(), LocalErr(3));
    ///
    /// let x: Result<Result<u32, u32, u32>, u32, u32> = FatalErr(4);
    /// assert_eq!(x.flatten(), FatalErr(4));
    /// ```
    #[inline]
    pub fn flatten(self) -> Result<T, L, F> {
        match self {
            Success(inner) => inner,
            LocalErr(err) => LocalErr(err),
            FatalErr(err) => FatalErr(err),
        }
    }
}

impl<T, L, F> Result<Option<T>, L, F> {
    /// Transpose a `Result` of an `Option` into an `Option` of a `Result`.
    ///
    /// [`Success`]: crate::Result::Success
    ///
    /// # Example
    ///
    /// ```
    /// use woah::prelude::*;
    ///
    /// let r: Result<Option<u32>, &str, &str> = Success(Some(5));
    /// assert_eq!(r.transpose(), Some(Success(5)));
    ///
    /// let r: Result<Option<u32>, &str, &str> = Success(None);
    /// assert_eq!(r.transpose(), None);
    ///
    /// let r: Result<Option<u32>, &str, &str> = LocalErr("a local error");
    /// assert_eq!(r.transpose(), Some(LocalErr("a local error")));
    /// ```
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

// Generic over `T` the way std's `impl<T: Termination, E: Debug> Termination for
// Result<T, E>` is. This subsumes the two impls that used to be here, for
// `Result<(), L, F>` and `Result<!, L, F>`: both `()` and `!` implement
// `Termination`, so a blanket impl would have collided with them.
#[cfg(feature = "std")]
impl<T, L, F> Termination for Result<T, L, F>
where
    T: Termination,
    L: Debug,
    F: Debug,
{
    #[inline]
    fn report(self) -> ExitCode {
        match self {
            Success(t) => t.report(),
            LocalErr(err) => {
                eprintln!("Error: {:?}", err);
                ExitCode::FAILURE
            }
            FatalErr(err) => {
                eprintln!("Error: {:?}", err);
                ExitCode::FAILURE
            }
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

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let n = if self.inner.is_some() { 1 } else { 0 };
        (n, Some(n))
    }
}

impl<T> DoubleEndedIterator for IntoIter<T> {
    #[inline]
    fn next_back(&mut self) -> Option<T> {
        self.inner.take()
    }
}

impl<T> ExactSizeIterator for IntoIter<T> {}

impl<T> FusedIterator for IntoIter<T> {}

#[cfg(feature = "nightly")]
unsafe impl<T> TrustedLen for IntoIter<T> {}

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

impl<T> ExactSizeIterator for Iter<'_, T> {}

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

impl<T> ExactSizeIterator for IterMut<'_, T> {}

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
                ControlFlow::Break(R::from_output(acc))
            }
            FatalErr(f) => {
                *error = FatalErr(f);
                ControlFlow::Break(R::from_output(acc))
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
        self.as_ref().into_nested_result().serialize(serializer)
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
