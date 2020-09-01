
# `woah`

`woah` is a (currently nightly-only) Rust crate which provides the following type:

```rust
enum Result<T, L, F> {
    Ok(T),
    LocalErr(L),
    FatalErr(F),
}
```

This type differentiates between "local errors" which can be handled and "fatal errors" which can't, to
enable the error handling pattern described by Tyler Neely (@spacejam) in the blog post ["Error Handling
in a Correctness-Critical Rust Project"][post]. `woah::Result` is intended to be a more ergonomic
alternative to the `Result<Result<T, LocalError>, FatalError>` type proposed in the post.

The important thing to note is that using the question mark operator on `woah::Result` causes
any `FatalError` to propagate up, while providing `Result<T, LocalError>` otherwise, to enable
the local code to handle any local errors without propagating them.

## Example

```rust
use std::ops::Try;
use woah::Result::{self, Ok, LocalErr, FatalErr};
use std::result::Result as StdResult;

fn main() {
    match do_thing() {
        StdResult::Ok(num) => println!("Got a number: {}", num),
        StdResult::Err(fatal_err) => eprintln!("Fatal error: {:?}", fatal_err),
    }
}

fn do_thing() -> StdResult<i64, FatalError> {
    let result = do_another_thing(5, 5)?;

    match result {
        StdResult::Err(local_err) => {
            println!("Local error: {:?}", local_err);
            StdResult::Ok(i64::default())
        }
        StdResult::Ok(num) => StdResult::Ok(num),
    }
}

fn do_another_thing(x: i64, y: i64) -> Result<i64, LocalError, FatalError> {
    let result = do_third_thing(x, y)?;
    Result::from_ok(result)
}

fn do_third_thing(x: i64, y: i64) -> Result<i64, LocalError, FatalError> {
    if x > y {
        Ok(x)
    } else if x == y {
        LocalErr(LocalError::SomeError)
    } else {
        FatalErr(FatalError::CatastrophicError)
    }
}

#[derive(Debug)]
enum LocalError {
    SomeError,
    AnotherError,
}

#[derive(Debug)]
enum FatalError {
    BigBadError,
    CatastrophicError,
}
```


[post]: http://sled.rs/errors.html "Link to the blog post"
