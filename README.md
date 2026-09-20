
# `woah`

![Crates.io](https://img.shields.io/crates/v/woah)
![Crates.io](https://img.shields.io/crates/l/woah)

__A `Result` that separates local errors you can handle from fatal errors you can't.__

Sometimes you want to be able to pass some errors upward without handling them, while
conveniently handling other kinds of errors at a local level. You might try to do
this with manual pattern-matching on a `Result`, or by constructing a
`Result<Result<T, LocalError>, FatalError>`. Instead, you can use `woah`!

## Example

This example uses the `?` operator on a `woah::Result`, which requires the
`nightly` feature on a nightly toolchain. On stable you convert to and from a
`std::result::Result` instead; see [Use](#use) below, the crate documentation,
or `examples/std_result_interop.rs`.

```rust
use woah::prelude::*;
use rand::random;

fn main() {
    match get_data() {
        Success(data) => println!("{}", data),
        LocalErr(e) => eprintln!("error: {:?}", e),
        FatalErr(e) => eprintln!("error: {:?}", e),
    }
}

/// Get data from an HTTP API.
fn get_data() -> Result<String, LocalError, FatalError> {
    match do_http_request()? {
        Ok(data) => Success(data),
        Err(e) => {
            eprintln!("error: {:?}... retrying", e);
            get_data()
        }
    }
}

/// Make an HTTP request.
///
/// This is simulated with randomly returning either a time out
/// or a request failure.
fn do_http_request() -> Result<String, LocalError, FatalError> {
    if random() {
        LocalErr(LocalError::RequestTimedOut)
    } else {
        FatalErr(FatalError::RequestFailed)
    }
}

/// Errors which can be handled.
#[derive(Debug)]
enum LocalError {
    RequestTimedOut,
}

/// Errors which can't be handled.
#[derive(Debug)]
enum FatalError {
    RequestFailed,
}
```

## Use

__`woah` can be used on stable Rust, but it's best when used on nightly.__

On nightly, with the `nightly` feature enabled, you get access to the `Try`
trait which allows use of the `?` operator to propagate fatal errors. On
stable, you have to convert to and from a `std::result::Result` to use
the `?` operator, which is less convenient.

## Features

| Feature Name | Default? | Purpose |
|:-------------|:--------|:---------|
| `nightly`    | No      | Lets you use the `?` operator with `woah::Result`, and adds some other convenience trait impls based on unstable APIs in `std`. Requires a nightly toolchain from Rust 1.100 or later. |
| `std`        | Yes     | Uses `std` for imports, adds the `Termination` and `ExitCode` APIs, and if `either` is turned on, turns on `std` for `either` as well. |
| `either`     | Yes     | Adds methods to `woah::Result` for working with `Either<LocalErr, FatalErr>` |
| `serde`      | No      | Implements `Serialize` and `Deserialize` for `woah::Result` |

## License

`woah` is dual-licensed MIT or Apache 2.0.


[post]: http://sled.rs/errors.html "Link to the blog post"
