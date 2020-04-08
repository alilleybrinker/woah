use std::result::Result as StdResult;
use std::iter::{Iterator, DoubleEndedIterator, FusedIterator};
use std::fmt::Debug;

#[cfg(feature="try_trait")]
use std::ops::Try;

#[cfg(feature="trusted_len")]
use std::iter::TrustedLen;

#[derive(Debug)]
pub enum Result<T, L, F> {
    Ok(T),
    LocalErr(L),
    FatalErr(F),
}

#[cfg(feature="try_trait")]
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

    pub fn iter(&self) -> Iter<T> {
        let inner = match self {
            Result::Ok(t) => Some(t),
            _ => None,
        };

        Iter { inner }
    }

    pub fn iter_mut(&mut self) -> IterMut<T> {
        let inner = match self {
            Result::Ok(t) => Some(t),
            _ => None,
        };

        IterMut { inner }
    }

    pub fn and<U>(self, res: Result<U, L, F>) -> Result<U, L, F> {
        match self {
            Result::Ok(_) => res,
            Result::LocalErr(err) => Result::LocalErr(err),
            Result::FatalErr(err) => Result::FatalErr(err),
        }
    }

    pub fn and_then<U, G>(self, op: G) -> Result<U, L, F>
    where
        G: FnOnce(T) -> Result<U, L, F>,
    {
        match self {
            Result::Ok(t) => op(t),
            Result::LocalErr(err) => Result::LocalErr(err),
            Result::FatalErr(err) => Result::FatalErr(err),
        }
    }

    pub fn or_local<M>(self, res: Result<T, M, F>) -> Result<T, M, F> {
        match self {
            Result::Ok(t) => Result::Ok(t),
            Result::LocalErr(_) => res,
            Result::FatalErr(err) => Result::FatalErr(err)
        }
    }

    pub fn or_fatal<G>(self, res: Result<T, L, G>) -> Result<T, L, G> {
        match self {
            Result::Ok(t) => Result::Ok(t),
            Result::LocalErr(err) => Result::LocalErr(err),
            Result::FatalErr(_) => res,
        }
    }

    pub fn or_else_local<O, M>(self, op: O) -> Result<T, M, F>
    where
        O: FnOnce(L) -> Result<T, M, F>,
    {
        match self {
            Result::Ok(t) => Result::Ok(t),
            Result::LocalErr(err) => op(err),
            Result::FatalErr(err) => Result::FatalErr(err),
        }
    }

    pub fn or_else_fatal<O, G>(self, op: O) -> Result<T, L, G>
    where
        O: FnOnce(F) -> Result<T, L, G>,
    {
        match self {
            Result::Ok(t) => Result::Ok(t),
            Result::LocalErr(err) => Result::LocalErr(err),
            Result::FatalErr(err) => op(err),
        }
    }

    pub fn unwrap_or(self, optb: T) -> T {
        match self {
            Result::Ok(t) => t,
            _ => optb,
        }
    }

    pub fn unwrap_or_else<M, G>(self, local_op: M, fatal_op: G) -> T
    where
        M: FnOnce(L) -> T,
        G: FnOnce(F) -> T,
    {
        match self {
            Result::Ok(t) => t,
            Result::LocalErr(err) => local_op(err),
            Result::FatalErr(err) => fatal_op(err),
        }
    }
}

impl<'a, T, L, F> Result<&'a T, L, F> where T: Copy {
    pub fn copied(self) -> Result<T, L, F> {
        match self {
            Result::Ok(t) => Result::Ok(*t),
            Result::LocalErr(err) => Result::LocalErr(err),
            Result::FatalErr(err) => Result::FatalErr(err),
        }
    }
}

impl<'a, T, L, F> Result<&'a mut T, L, F> where T: Copy {
    pub fn copied(self) -> Result<T, L, F> {
        match self {
            Result::Ok(t) => Result::Ok(*t),
            Result::LocalErr(err) => Result::LocalErr(err),
            Result::FatalErr(err) => Result::FatalErr(err),
        }
    }
}

impl<'a, T, L, F> Result<&'a T, L, F> where T: Clone {
    pub fn cloned(self) -> Result<T, L, F> {
        match self {
            Result::Ok(t) => Result::Ok(t.clone()),
            Result::LocalErr(err) => Result::LocalErr(err),
            Result::FatalErr(err) => Result::FatalErr(err),
        }
    }
}

impl<'a, T, L, F> Result<&'a mut T, L, F> where T: Clone {
    pub fn cloned(self) -> Result<T, L, F> {
        match self {
            Result::Ok(t) => Result::Ok(t.clone()),
            Result::LocalErr(err) => Result::LocalErr(err),
            Result::FatalErr(err) => Result::FatalErr(err),
        }
    }
}

impl<T, L, F> Result<T, L, F> where L: Debug, F: Debug {
    pub fn unwrap(self) -> T {
        match self {
            Result::Ok(t) => t,
            Result::LocalErr(err) => panic!("{:?}", err),
            Result::FatalErr(err) => panic!("{:?}", err),
        }
    }

    pub fn expect(self, msg: &str) -> T {
        match self {
            Result::Ok(t) => t,
            Result::LocalErr(_) => panic!("{}", msg),
            Result::FatalErr(_) => panic!("{}", msg),
        }
    }
}

impl<T, L, F> Result<T, L, F> where T: Debug, F: Debug {
    pub fn unwrap_local_err(self) -> L {
        match self {
            Result::Ok(t) => panic!("{:?}", t),
            Result::LocalErr(err) => err,
            Result::FatalErr(err) => panic!("{:?}", err),
        }
    }

    pub fn expect_local_err(self, msg: &str) -> L {
        match self {
            Result::Ok(_) => panic!("{}", msg),
            Result::LocalErr(err) => err,
            Result::FatalErr(_) => panic!("{}", msg),
        }
    }
}

impl<T, L, F> Result<T, L, F> where T: Debug, L: Debug {
    pub fn unwrap_fatal_err(self) -> F {
        match self {
            Result::Ok(t) => panic!("{:?}", t),
            Result::LocalErr(err) => panic!("{:?}", err),
            Result::FatalErr(err) => err,
        }
    }

    pub fn expect_fatal_err(self, msg: &str) -> F {
        match self {
            Result::Ok(_) => panic!("{}", msg),
            Result::LocalErr(_) => panic!("{}", msg),
            Result::FatalErr(err) => err, 
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
