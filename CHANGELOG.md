# Changelog

All notable changes to `woah` are documented here. This file starts at 0.5.0;
for earlier releases, see the commit history.

The format is based on [Keep a Changelog][keep-a-changelog], and `woah` follows
[Semantic Versioning][semver].

[keep-a-changelog]: https://keepachangelog.com/en/1.1.0/
[semver]: https://semver.org/spec/v2.0.0.html

## [0.5.0] - unreleased

### Added

- `inspect`, `inspect_err`, `inspect_local_err` and `inspect_fatal_err`, for
  looking at a contained value without consuming it.
- `is_success_and`, `is_err_and`, `is_local_err_and` and `is_fatal_err_and`,
  for testing a contained value against a predicate.
- `flatten`, collapsing a `Result` nested in another's `Success` variant.
- `from_nested_result`, constructing any of the three variants from the nested
  `Result<Result<T, L>, F>`. This is the inverse of `into_nested_result`, which
  previously existed only as a `From` impl with no named counterpart, so the
  named conversions could go one way but not back.
- `into_result_merged`, converting into a `std::result::Result<T, F>` by merging both
  error channels into one, escalating a `LocalErr` through `F: From<L>`. This is
  the transform #7 asked for, which `flatten` -- the direct analogue of std's
  method -- does not perform.
- `map_err_or`, `map_err_or_else`, `map_local_err_or_else` and
  `map_fatal_err_or_else`. These stand to `map_err`, `map_local_err` and
  `map_fatal_err` as `map_or` and `map_or_else` stand to `map`: they unwrap to
  a value rather than returning a `Result`. The `docs` module had listed these
  since 0.4.x, but they were never implemented.

  Two of the six it listed are deliberately *not* here.
  `map_local_err_or(default, f)` would have returned the default for a
  `FatalErr` as well as a `Success`, silently dropping a fatal error and making
  it indistinguishable from success; `map_fatal_err_or` did the same to a local
  error. In a crate whose premise is that fatal errors do not get swallowed,
  that is the wrong default shape for an API to have. The `_or_else` forms give
  every variant its own function and lose nothing.
- `unwrap_unchecked`, `unwrap_err_unchecked`, `unwrap_local_err_unchecked` and
  `unwrap_fatal_err_unchecked`. These are `unsafe`: calling one on a variant it
  does not name is undefined behavior.
- `ExactSizeIterator` for `IntoIter`, `Iter` and `IterMut`, and
  `DoubleEndedIterator`, `FusedIterator` and (with the `nightly` feature)
  `TrustedLen` for `IntoIter`, which previously implemented only `Iterator`
  while the other two iterators implemented all four.
- Integration tests for the serde impls, the iterator types and the
  `nightly`-gated trait impls, including the `?` behavior the crate exists to
  provide.
- This changelog.

### Changed

- **Breaking:** the two named conversions to and from `std::result::Result` say
  which shape they deal with. `into_result` is now `into_nested_result`, for the
  nested `Result<Result<T, L>, F>` it returns, and `from_result` is now
  `from_flat_result`, for the flat `Result<T, L>` it takes. The old names looked
  like inverses and were not: round-tripping them nests one layer deeper each
  time. The `From` impls, which are unambiguous because the types differ, are
  unchanged.
- **Breaking:** `or_local`, `or_fatal`, `or_else_local` and `or_else_fatal` are
  renamed `or_local_err`, `or_fatal_err`, `or_else_local_err` and
  `or_else_fatal_err`. They were the only four methods naming a variant without
  the `_err` suffix the other 28 use.
- **Breaking:** `from_fatal_error` is renamed `from_fatal_err`, so the
  constructors read `from_success` / `from_local_err` / `from_fatal_err`. Every
  other method in the crate spells this variant `fatal_err` -- 14 of them --
  and this was the lone exception.
- The `Termination` impl is now generic over the success type, as std's impl for
  `std::result::Result` is: any `T: Termination` works, rather than only `()`.
  This replaces the two previous impls, for `Result<(), L, F>` and
  `Result<!, L, F>`, which it subsumes -- both `()` and `!` implement
  `Termination`, so keeping them alongside a blanket impl would not have
  compiled. A `Success` now reports through its own value's `report`, so
  `fn main() -> woah::Result<ExitCode, L, F>` can set an exit code.
- **Breaking:** the minimum supported Rust version is now 1.98.0, up from
  1.61.0.
- **Breaking:** the crate is now on the 2024 edition.
- The `nightly` feature now requires a nightly toolchain from Rust 1.100 or
  later, since it no longer gates the never type behind `#![feature]`.
- `from_success`, `from_local_err`, `from_fatal_err`, `is_success`, `is_err`,
  `is_local_err`, `is_fatal_err`, `as_ref`, `as_mut`, `iter` and `iter_mut` are
  now `const fn`.
- The `rand` dev-dependency used by the examples moved from 0.8 to 0.10.
- The examples now declare `required-features = ["nightly"]`, so `cargo test`
  works on stable.

### Fixed

- Every link to the crate's own items is now an intra-doc link. The
  hand-written HTML paths had rotted: all 68 links on the `docs` module's page
  pointed one directory too high, and the trait-impl anchors no longer matched
  the ids rustdoc generates.
- The `docs` module pointed at three features that do not exist (`try_trait`,
  `termination_trait` and `from_iterator_trait`). It also described the
  `Termination` impl as
  nightly-only, when the impl for `Result<(), L, F>` works on stable with the
  `std` feature.
- `IntoIter::size_hint` reported `(0, None)` rather than an exact bound,
  because it did not override the default. `Iter` and `IterMut` always
  reported exactly.
- A stable `cargo build` is warning-free again: the crate no longer uses
  `try` blocks, whose syntax warned even with the surrounding code compiled
  out, and the elided-lifetime and `needless_lifetimes` findings are resolved.
- `cargo clippy` passes. It had been failing outright, since
  `#![deny(clippy::all)]` turned four `needless_lifetimes` findings into
  errors.
- The README's headline example now says that it needs the `nightly` feature,
  rather than leaving the caveat further down the page.
- `cargo doc --no-default-features` builds without warnings. The `docs`
  module's index linked `either`-gated methods unconditionally, so those links
  did not resolve with the feature off; they are now conditional on it, and CI
  builds the docs both ways.

### Removed

- **Breaking:** `contains`, `contains_err`, `contains_local_err` and
  `contains_fatal_err`. These mirrored `Result::contains`, which std never
  stabilized and has since removed outright -- it is not in std even on
  nightly -- on the grounds that `is_ok_and` subsumes it. The `is_*_and`
  family added in this release subsumes these the same way. Where the old
  methods borrowed and these consume, add `as_ref`:

  ```rust
  // was
  result.contains(&2);
  result.contains_local_err(&"boom");

  // now
  result.as_ref().is_success_and(|t| *t == 2);
  result.as_ref().is_local_err_and(|e| *e == "boom");
  ```

- The stale `control_flow_enum` and `never_type` feature gates, both of which
  named features that have since stabilized.

## Documentation

- Every public item is documented with an example, and `missing_docs` is now
  denied.

## Continuous integration

- Tests run across 1.98.0, stable and nightly, over each feature combination,
  rather than only `--all-features` on nightly.
- `cargo fmt --check`, `cargo clippy --all-features --all-targets -D warnings`
  and a warning-free `cargo doc` now gate changes.
