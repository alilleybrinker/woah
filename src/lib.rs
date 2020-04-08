#![feature(try_trait)]

use std::fmt::Debug;
use std::iter::{DoubleEndedIterator, FromIterator, FusedIterator, Iterator, Product, Sum};
use std::ops::Try;
use std::ops::{Deref, DerefMut};
use std::result::Result as StdResult;

#[cfg(feature = "termination_trait_lib")]
use std::process::{ExitCode, Termination};

#[cfg(feature = "trusted_len")]
use std::iter::TrustedLen;

#[derive(Copy, PartialEq, PartialOrd, Eq, Ord, Debug, Hash)]
pub enum Result<T, L, F> {
    Ok(T),
    LocalErr(L),
    FatalErr(F),
}

#[cfg(feature = "try_trait")]
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

    pub fn contains<U>(&self, x: &U) -> bool
    where
        U: PartialEq<T>,
    {
        match self {
            Result::Ok(t) if *x == *t => true,
            _ => false,
        }
    }

    pub fn contains_local_err<E>(&self, e: &E) -> bool
    where
        E: PartialEq<L>,
    {
        match self {
            Result::LocalErr(err) if *e == *err => true,
            _ => false,
        }
    }

    pub fn contains_fatal_err<E>(&self, e: &E) -> bool
    where
        E: PartialEq<F>,
    {
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
        U: FnOnce(T) -> S,
    {
        match self {
            Result::Ok(t) => Result::Ok(f(t)),
            Result::LocalErr(e) => Result::LocalErr(e),
            Result::FatalErr(e) => Result::FatalErr(e),
        }
    }

    pub fn map_or<U, G>(self, default: U, f: G) -> U
    where
        G: FnOnce(T) -> U,
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
        U: FnOnce(L) -> S,
    {
        match self {
            Result::Ok(t) => Result::Ok(t),
            Result::LocalErr(e) => Result::LocalErr(f(e)),
            Result::FatalErr(e) => Result::FatalErr(e),
        }
    }

    pub fn map_fatal_err<U, S>(self, f: U) -> Result<T, L, S>
    where
        U: FnOnce(F) -> S,
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
            Result::FatalErr(err) => Result::FatalErr(err),
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

impl<'a, T, L, F> Result<&'a T, L, F>
where
    T: Copy,
{
    pub fn copied(self) -> Result<T, L, F> {
        match self {
            Result::Ok(t) => Result::Ok(*t),
            Result::LocalErr(err) => Result::LocalErr(err),
            Result::FatalErr(err) => Result::FatalErr(err),
        }
    }
}

impl<'a, T, L, F> Result<&'a mut T, L, F>
where
    T: Copy,
{
    pub fn copied(self) -> Result<T, L, F> {
        match self {
            Result::Ok(t) => Result::Ok(*t),
            Result::LocalErr(err) => Result::LocalErr(err),
            Result::FatalErr(err) => Result::FatalErr(err),
        }
    }
}

impl<'a, T, L, F> Result<&'a T, L, F>
where
    T: Clone,
{
    pub fn cloned(self) -> Result<T, L, F> {
        match self {
            Result::Ok(t) => Result::Ok(t.clone()),
            Result::LocalErr(err) => Result::LocalErr(err),
            Result::FatalErr(err) => Result::FatalErr(err),
        }
    }
}

impl<'a, T, L, F> Result<&'a mut T, L, F>
where
    T: Clone,
{
    pub fn cloned(self) -> Result<T, L, F> {
        match self {
            Result::Ok(t) => Result::Ok(t.clone()),
            Result::LocalErr(err) => Result::LocalErr(err),
            Result::FatalErr(err) => Result::FatalErr(err),
        }
    }
}

impl<T, L, F> Result<T, L, F>
where
    L: Debug,
    F: Debug,
{
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

impl<T, L, F> Result<T, L, F>
where
    T: Debug,
    F: Debug,
{
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

impl<T, L, F> Result<T, L, F>
where
    T: Debug,
    L: Debug,
{
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

impl<T, L, F> Result<T, L, F>
where
    T: Default,
{
    pub fn unwrap_or_default(self) -> T {
        match self {
            Result::Ok(t) => t,
            _ => T::default(),
        }
    }
}

#[cfg(feature = "never_type")]
impl<T, L, F> Result<T, L, F>
where
    L: Into<!>,
    F: Into<!>,
{
    pub fn into_ok(self) -> T {
        match self {
            Result::Ok(t) => t,
            Result::LocalErr(err) => err.into(),
            Result::FatalErr(err) => err.into(),
        }
    }
}

impl<T, L, F> Result<T, L, F>
where
    T: Deref,
{
    pub fn as_deref(&self) -> Result<&<T as Deref>::Target, &L, &F> {
        match self {
            Result::Ok(t) => Result::Ok(t.deref()),
            Result::LocalErr(err) => Result::LocalErr(err),
            Result::FatalErr(err) => Result::FatalErr(err),
        }
    }
}

impl<T, L, F> Result<T, L, F>
where
    L: Deref,
{
    pub fn as_deref_local_err(&self) -> Result<&T, &<L as Deref>::Target, &F> {
        match self {
            Result::Ok(t) => Result::Ok(t),
            Result::LocalErr(err) => Result::LocalErr(err.deref()),
            Result::FatalErr(err) => Result::FatalErr(err),
        }
    }
}

impl<T, L, F> Result<T, L, F>
where
    F: Deref,
{
    pub fn as_deref_fatal_err(&self) -> Result<&T, &L, &<F as Deref>::Target> {
        match self {
            Result::Ok(t) => Result::Ok(t),
            Result::LocalErr(err) => Result::LocalErr(err),
            Result::FatalErr(err) => Result::FatalErr(err.deref()),
        }
    }
}

impl<T, L, F> Result<T, L, F>
where
    T: DerefMut,
{
    pub fn as_deref_mut(&mut self) -> Result<&mut <T as Deref>::Target, &mut L, &mut F> {
        match self {
            Result::Ok(t) => Result::Ok(t.deref_mut()),
            Result::LocalErr(err) => Result::LocalErr(err),
            Result::FatalErr(err) => Result::FatalErr(err),
        }
    }
}

impl<T, L, F> Result<T, L, F>
where
    L: DerefMut,
{
    pub fn as_deref_mut_local_err(&mut self) -> Result<&mut T, &mut <L as Deref>::Target, &mut F> {
        match self {
            Result::Ok(t) => Result::Ok(t),
            Result::LocalErr(err) => Result::LocalErr(err.deref_mut()),
            Result::FatalErr(err) => Result::FatalErr(err),
        }
    }
}

impl<T, L, F> Result<T, L, F>
where
    F: DerefMut,
{
    pub fn as_deref_mut_fatal_err(&mut self) -> Result<&mut T, &mut L, &mut <F as Deref>::Target> {
        match self {
            Result::Ok(t) => Result::Ok(t),
            Result::LocalErr(err) => Result::LocalErr(err),
            Result::FatalErr(err) => Result::FatalErr(err.deref_mut()),
        }
    }
}

impl<T, L, F> Result<Option<T>, L, F> {
    pub fn transpose(self) -> Option<Result<T, L, F>> {
        match self {
            Result::Ok(Some(t)) => Some(Result::Ok(t)),
            Result::Ok(None) => None,
            Result::LocalErr(err) => Some(Result::LocalErr(err)),
            Result::FatalErr(err) => Some(Result::FatalErr(err)),
        }
    }
}

impl<T, L, F> Clone for Result<T, L, F>
where
    T: Clone,
    L: Clone,
    F: Clone,
{
    fn clone(&self) -> Result<T, L, F> {
        match self {
            Result::Ok(t) => Result::Ok(t.clone()),
            Result::LocalErr(err) => Result::LocalErr(err.clone()),
            Result::FatalErr(err) => Result::FatalErr(err.clone()),
        }
    }

    fn clone_from(&mut self, source: &Result<T, L, F>) {
        match (self, source) {
            (Result::Ok(to), Result::Ok(from)) => to.clone_from(from),
            (Result::LocalErr(to), Result::LocalErr(from)) => to.clone_from(from),
            (Result::FatalErr(to), Result::FatalErr(from)) => to.clone_from(from),
            (to, from) => *to = from.clone(),
        }
    }
}

impl<A, V, L, F> FromIterator<Result<A, L, F>> for Result<V, L, F>
where
    V: FromIterator<A>,
{
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

    fn into_iter(self) -> IterMut<'a, T> {
        self.iter_mut()
    }
}

impl<'a, T, L, F> IntoIterator for &'a Result<T, L, F> {
    type Item = &'a T;
    type IntoIter = Iter<'a, T>;

    fn into_iter(self) -> Iter<'a, T> {
        self.iter()
    }
}

impl<T, L, F> IntoIterator for Result<T, L, F> {
    type Item = T;
    type IntoIter = IntoIter<T>;

    fn into_iter(self) -> IntoIter<T> {
        IntoIter { inner: self.ok() }
    }
}

impl<T, U, L, F> Product<Result<U, L, F>> for Result<T, L, F>
where
    T: Product<U>,
{
    fn product<I>(iter: I) -> Result<T, L, F>
    where
        I: Iterator<Item = Result<U, L, F>>,
    {
        process_results(iter, |i| i.product())
    }
}

impl<T, U, L, F> Sum<Result<U, L, F>> for Result<T, L, F>
where
    T: Sum<U>,
{
    fn sum<I>(iter: I) -> Result<T, L, F>
    where
        I: Iterator<Item = Result<U, L, F>>,
    {
        process_results(iter, |i| i.sum())
    }
}

#[cfg(feature = "termination_trait_lib")]
impl<T, L, F> Termination for Result<(), L, F>
where
    L: Debug,
    F: Debug,
{
    fn report(self) -> i32 {
        match self {
            Result::Ok(()) => ().report(),
            Result::LocalErr(err) => Result::LocalErr::<!, _>(err).report(),
            Result::FatalErr(err) => Result::FatalErr::<!, _>(err).report(),
        }
    }
}

#[cfg(feature = "termination_trait_lib")]
impl<T, L, F> Termination for Result<!, L, F>
where
    L: Debug,
    F: Debug,
{
    fn report(self) -> i32 {
        let Err(err) = self;
        eprintln!("Error: {:?}", err);
        ExitCode::FAILURE.report()
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

pub struct IntoIter<T> {
    inner: Option<T>,
}

impl<T> Iterator for IntoIter<T> {
    type Item = T;

    #[inline]
    fn next(&mut self) -> Option<T> {
        self.inner.take()
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

pub(crate) struct ResultShunt<'a, I, L, F> {
    iter: I,
    error: &'a mut Result<(), L, F>,
}

pub(crate) fn process_results<I, T, L, F, G, U>(iter: I, mut f: G) -> Result<U, L, F>
where
    I: Iterator<Item = Result<T, L, F>>,
    for<'a> G: FnMut(ResultShunt<'a, I, L, F>) -> U,
{
    let mut error = Result::Ok(());
    let shunt = ResultShunt {
        iter,
        error: &mut error,
    };
    let value = f(shunt);
    error.map(|()| value)
}

impl<I, T, L, F> Iterator for ResultShunt<'_, I, L, F>
where
    I: Iterator<Item = Result<T, L, F>>,
{
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        self.find(|_| true)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        if self.error.is_err() {
            (0, Some(0))
        } else {
            let (_, upper) = self.iter.size_hint();
            (0, upper)
        }
    }

    fn try_fold<B, G, R>(&mut self, init: B, mut f: G) -> R
    where
        G: FnMut(B, Self::Item) -> R,
        R: Try<Ok = B>,
    {
        let error = &mut *self.error;
        self.iter
            .try_fold(init, |acc, x| match x {
                Result::Ok(x) => LoopState::from_try(f(acc, x)),
                Result::LocalErr(e) => {
                    *error = Result::LocalErr(e);
                    LoopState::Break(Try::from_ok(acc))
                }
                Result::FatalErr(e) => {
                    *error = Result::FatalErr(e);
                    LoopState::Break(Try::from_ok(acc))
                }
            })
            .into_try()
    }
}

#[derive(PartialEq)]
enum LoopState<C, B> {
    Continue(C),
    Break(B),
}

impl<C, B> Try for LoopState<C, B> {
    type Ok = C;
    type Error = B;
    #[inline]
    fn into_result(self) -> StdResult<Self::Ok, Self::Error> {
        match self {
            LoopState::Continue(y) => Ok(y),
            LoopState::Break(x) => Err(x),
        }
    }
    #[inline]
    fn from_error(v: Self::Error) -> Self {
        LoopState::Break(v)
    }
    #[inline]
    fn from_ok(v: Self::Ok) -> Self {
        LoopState::Continue(v)
    }
}

impl<R: Try> LoopState<R::Ok, R> {
    #[inline]
    fn from_try(r: R) -> Self {
        match Try::into_result(r) {
            Ok(v) => LoopState::Continue(v),
            Err(v) => LoopState::Break(Try::from_error(v)),
        }
    }
    #[inline]
    fn into_try(self) -> R {
        match self {
            LoopState::Continue(v) => Try::from_ok(v),
            LoopState::Break(v) => v,
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
