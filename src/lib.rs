#![feature(try_trait)]

use std::ops::Try;
use std::result::Result as StdResult;

#[derive(Debug)]
pub enum Result<T, L, F> {
    Ok(T),
    LocalErr(L),
    FatalErr(F),
}

impl<T, L, F> Try for Result<T, L, F> {
    type Ok = StdResult<T, L>;
    type Error = F;

    fn into_result(self) -> StdResult<StdResult<T, L>, F> {
        match self {
            Result::Ok(t) => Ok(Ok(t)),
            Result::LocalErr(err) => Ok(Err(err)),
            Result::FatalErr(err) => Err(err),
        }
    }

    fn from_error(err: F) -> Self {
        Result::FatalErr(err)
    }

    fn from_ok(ok: StdResult<T, L>) -> Self {
        match ok {
            Ok(t) => Result::Ok(t),
            Err(err) => Result::LocalErr(err),
        }
    }
}

impl<T, L, F> Result<T, L, F> {
    pub fn is_ok(&self) -> bool {
        match self {
            Result::Ok(_) => true,
            _ => false,
        }
    }

    pub fn is_err(&self) -> bool {
        !self.is_ok()
    }

    pub fn is_local_err(&self) -> bool {
        match self {
            Result::LocalErr(_) => true,
            _ => false,
        }
    }

    pub fn is_fatal_err(&self) -> bool {
        match self {
            Result::FatalErr(_) => true,
            _ => false,
        }
    }

    pub fn contains<U>(&self, x: &U) -> bool where U: PartialEq<T> {
        match self {
            Result::Ok(t) if *x == *t => true,
            _ => false,
        }
    }

    pub fn contains_local_err<E>(&self, e: &E) -> bool where E: PartialEq<L> {
        match self {
            Result::LocalErr(err) if *e == *err => true,
            _ => false,
        }
    }

    pub fn contains_fatal_err<E>(&self, e: &E) -> bool where E: PartialEq<F> {
        match self {
            Result::FatalErr(err) if *e == *err => true,
            _ => false,
        }
    }

    pub fn ok(self) -> Option<T> {
        match self {
            Result::Ok(t) => Some(t),
            _ => None,
        }
    }

    pub fn local_err(self) -> Option<L> {
        match self {
            Result::LocalErr(err) => Some(err),
            _ => None,
        }
    }

    pub fn fatal_err(self) -> Option<F> {
        match self {
            Result::FatalErr(err) => Some(err),
            _ => None,
        }
    }

    pub fn as_ref(&self) -> Result<&T, &L, &F> {
        match self {
            Result::Ok(t) => Result::Ok(t),
            Result::LocalErr(err) => Result::LocalErr(err),
            Result::FatalErr(err) => Result::FatalErr(err),
        }
    }

    pub fn as_mut(&mut self) -> Result<&mut T, &mut L, &mut F> {
        match self {
            Result::Ok(t) => Result::Ok(t),
            Result::LocalErr(err) => Result::LocalErr(err),
            Result::FatalErr(err) => Result::FatalErr(err),
        }
    }

    pub fn map<U, S>(self, f: U) -> Result<S, L, F>
    where
        U: FnOnce(T) -> S
    {
        match self {
            Result::Ok(t) => Result::Ok(f(t)),
            Result::LocalErr(e) => Result::LocalErr(e),
            Result::FatalErr(e) => Result::FatalErr(e),
        }
    }

    pub fn map_or<U, G>(self, default: U, f: G) -> U
    where
        G: FnOnce(T) -> U
    {
        match self {
            Result::Ok(t) => f(t),
            _ => default,
        }
    }

    pub fn map_or_else<U, LD, FD, G>(self, default_local: LD, default_fatal: FD, f: G) -> U
    where
        LD: FnOnce(L) -> U,
        FD: FnOnce(F) -> U,
        G: FnOnce(T) -> U,
    {
        match self {
            Result::Ok(t) => f(t),
            Result::LocalErr(err) => default_local(err),
            Result::FatalErr(err) => default_fatal(err),
        }
    }
    
    pub fn map_local_err<U, S>(self, f: U) -> Result<T, S, F>
    where
        U: FnOnce(L) -> S
    {
        match self {
            Result::Ok(t) => Result::Ok(t),
            Result::LocalErr(e) => Result::LocalErr(f(e)),
            Result::FatalErr(e) => Result::FatalErr(e),
        }
    }
    
    pub fn map_fatal_err<U, S>(self, f: U) -> Result<T, L, S>
    where
        U: FnOnce(F) -> S
    {
        match self {
            Result::Ok(t) => Result::Ok(t),
            Result::LocalErr(e) => Result::LocalErr(e),
            Result::FatalErr(e) => Result::FatalErr(f(e)),
        }
    }
}

impl<T: Default, L, F> Result<T, L, F> {
    pub fn into_result_default(self) -> StdResult<T, F> {
        match self {
            Result::Ok(t) => Ok(t),
            Result::LocalErr(_) => Ok(T::default()),
            Result::FatalErr(err) => Err(err),
        }
    }
}

/*
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
*/
