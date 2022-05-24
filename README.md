
# `woah`

![Crates.io](https://img.shields.io/crates/v/woah)
![Crates.io](https://img.shields.io/crates/l/woah)

__A `Result` that separates local errors you can handle from fatal errors you can't.__

Sometimes you want to be able to pass some errors upward without handling them, while
conveniently handling other kinds of errors at a local level. You might try to do
this with manual pattern-matching a `Result`, or by constructing a
`Result<T, LocalError>, FatalError`. Instead, you can use `woah`!

## Example

```rust
use woah::prelude::*;
use rand::prelude::*;

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

## License

`woah` is dual-licensed MIT or Apache 2.0.


[post]: http://sled.rs/errors.html "Link to the blog post"
