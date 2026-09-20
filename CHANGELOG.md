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
- `unwrap_unchecked`, `unwrap_err_unchecked`, `unwrap_local_err_unchecked` and
  `unwrap_fatal_err_unchecked`. These are `unsafe`: calling one on a variant it
  does not name is undefined behavior.
- Integration tests for the serde impls, the iterator types and the
  `nightly`-gated trait impls, including the `?` behavior the crate exists to
  provide.
- This changelog.

### Changed

- **Breaking:** the minimum supported Rust version is now 1.98.0, up from
  1.61.0.
- **Breaking:** the crate is now on the 2024 edition.
- The `nightly` feature now requires a nightly toolchain from Rust 1.100 or
  later, since it no longer gates the never type behind `#![feature]`.
- `from_success`, `from_local_err`, `from_fatal_error`, `is_success`, `is_err`,
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
- The `docs` module listed six methods that do not exist (`map_err_or`,
  `map_err_or_else`, `map_local_err_or`, `map_local_err_or_else`,
  `map_fatal_err_or` and `map_fatal_err_or_else`), and pointed at three
  features that do not exist (`try_trait`, `termination_trait` and
  `from_iterator_trait`). It also described the `Termination` impl as
  nightly-only, when the impl for `Result<(), L, F>` works on stable with the
  `std` feature.
- A stable `cargo build` is warning-free again: the crate no longer uses
  `try` blocks, whose syntax warned even with the surrounding code compiled
  out, and the elided-lifetime and `needless_lifetimes` findings are resolved.
- `cargo clippy` passes. It had been failing outright, since
  `#![deny(clippy::all)]` turned four `needless_lifetimes` findings into
  errors.
- The README's headline example now says that it needs the `nightly` feature,
  rather than leaving the caveat further down the page.

### Removed

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
