
# `woe`

`woe` is a (currently nightly-only) Rust crate which provides the following type:

```rust
enum Result<T, L, F> {
    Ok(T),
    LocalErr(L),
    FatalErr(F),
}
```

This type differentiates between "local errors" which can be handled and "fatal errors" which can't, to
enable the error handling pattern described by Tyler Neely (@spacejam) in the blog post ["Error Handling
in a Correctness-Critical Rust Project"][post]. `woe::Result` is intended to be a more ergonomic
alternative to the `Result<Result<T, LocalError>, FatalError>` type proposed in the post.

## Example

```rust
fn do_third_thing(x: i64, y: i64) -> woe::Result<i64, LocalError, FatalError> {
    if x > y {
        woe::Result::Ok(x)
    } else if x == y {
        woe::Result::LocalErr(LocalError::SomeError)
    } else {
        woe::Result::FatalErr(FatalError::CatastrophicError)
    }
}

fn do_another_thing(x: i64, y: i64) -> woe::Result<i64, LocalError, FatalError> {
    let result = do_third_thing(x, y)?;

    woe::Result::from_ok(result)
}

fn do_thing() -> Result<i64, FatalError> {
    let result = do_another_thing(5, 5)?;

    match result {
        Err(local_err) => {
            println!("Local error: {:?}", local_err);

            Ok(i64::default())
        }
        Ok(num) => Ok(num),
    }
}

fn main() {
    match do_thing() {
        Ok(num) => println!("Got a number: {}", num),
        Err(fatal_err) => eprintln!("Fatal error: {:?}", fatal_err),
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
