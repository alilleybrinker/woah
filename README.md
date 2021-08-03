
# woah

`woah` is a Rust crate providing a "ternary `Result`" type that differentiates between
"local errors" which can be handled, and "fatal errors" which can't.

## Example

```rust
use std::ops::Try as _;

fn main() -> Result<(), FatalError> {
	let data = get_data_from_api()?;
	println!("Data: {}", data),
	Ok(())
}

fn get_data_from_api() -> Result<String, FatalError> {
	// If the error is fatal, return early!
	let result = request_url("https://some_website.whatever/api/get_data")?;

	match result {
		// If the error is recoverable, handle it.
		Err(RecoverableError::Redirected { new_url }) => request_url(new_url),
		Ok(num) => Ok(num),
	}
}

fn request_url(url: &str) -> woah::Result<String, RecoverableError, FatalError> {
	// ...
}

enum RecoverableError {
	Redirected { new_url: String },
}

#[derive(Debug)]
enum FatalError {
	CouldntConnect,
}
```


[post]: http://sled.rs/errors.html "Link to the blog post"
