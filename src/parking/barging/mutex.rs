use core::fmt::{self, Debug, Display, Formatter};

use crate::inner::barging as inner;
use crate::parking::park::{Park, ParkWait};
use crate::parking::parker::Parker;

#[cfg(test)]
use crate::test::{LockNew, LockWith};

/// A mutual exclusion primitive useful for protecting shared data.
pub struct Mutex<T: ?Sized, P> {
    inner: inner::Mutex<T, Parker, Parker, ParkWait<P>>,
}

// Same unsafe impls as `crate::inner::raw::Mutex`.
unsafe impl<T: ?Sized + Send, P> Send for Mutex<T, P> {}
unsafe impl<T: ?Sized + Send, P> Sync for Mutex<T, P> {}

impl<T, P> Mutex<T, P> {
    /// Creates a new mutex in an unlocked state ready for use.
    #[cfg(not(all(loom, test)))]
    #[inline]
    pub const fn new(value: T) -> Self {
        Self { inner: inner::Mutex::new(value) }
    }

    /// Creates a new unlocked mutex with Loom primitives (non-const).
    #[cfg(all(loom, test))]
    #[cfg(not(tarpaulin_include))]
    fn new(value: T) -> Self {
        Self { inner: inner::Mutex::new(value) }
    }

    /// Consumes this mutex, returning the underlying data.
    #[inline(always)]
    pub fn into_inner(self) -> T {
        self.inner.into_inner()
    }
}

impl<T: ?Sized, P: Park> Mutex<T, P> {
    /// Acquires this mutex, blocking the current thread until it is able to do so.
    #[inline]
    pub fn lock(&self) -> MutexGuard<'_, T, P> {
        self.inner.lock().into()
    }

    /// Acquires this mutex and then runs the closure against its guard.
    #[inline]
    pub fn lock_with<F, Ret>(&self, f: F) -> Ret
    where
        F: FnOnce(MutexGuard<'_, T, P>) -> Ret,
    {
        f(self.lock())
    }
}

impl<T: ?Sized, P> Mutex<T, P> {
    /// Attempts to acquire this mutex without blocking the thread.
    #[inline]
    pub fn try_lock(&self) -> Option<MutexGuard<'_, T, P>> {
        self.inner.try_lock().map(From::from)
    }

    /// Attempts to acquire this mutex and then runs a closure against its guard.
    #[inline]
    pub fn try_lock_with<F, Ret>(&self, f: F) -> Ret
    where
        F: FnOnce(Option<MutexGuard<'_, T, P>>) -> Ret,
    {
        f(self.try_lock())
    }

    /// Returns `true` if the lock is currently held.
    #[inline]
    pub fn is_locked(&self) -> bool {
        self.inner.is_locked()
    }

    /// Returns a mutable reference to the underlying data.
    #[cfg(not(all(loom, test)))]
    #[inline(always)]
    pub fn get_mut(&mut self) -> &mut T {
        self.inner.get_mut()
    }
}

impl<T: Default, P> Default for Mutex<T, P> {
    /// Creates a `Mutex<T, R>`, with the `Default` value for `T`.
    #[inline]
    fn default() -> Self {
        Self::new(Default::default())
    }
}

impl<T, R> From<T> for Mutex<T, R> {
    /// Creates a `Mutex<T, R>` from a instance of `T`.
    #[inline]
    fn from(data: T) -> Self {
        Self::new(data)
    }
}

impl<T: ?Sized + Debug, P> Debug for Mutex<T, P> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        self.inner.fmt(f)
    }
}

#[cfg(test)]
impl<T: ?Sized, P> LockNew for Mutex<T, P> {
    type Target = T;

    fn new(value: Self::Target) -> Self
    where
        Self::Target: Sized,
    {
        Self::new(value)
    }
}

#[cfg(test)]
impl<T: ?Sized, P: Park> LockWith for Mutex<T, P> {
    type Guard<'a> = MutexGuard<'a, Self::Target, P>
    where
        Self: 'a,
        Self::Target: 'a;

    fn try_lock_with<F, Ret>(&self, f: F) -> Ret
    where
        F: FnOnce(Option<MutexGuard<'_, T, P>>) -> Ret,
    {
        self.try_lock_with(f)
    }

    fn lock_with<F, Ret>(&self, f: F) -> Ret
    where
        F: FnOnce(MutexGuard<'_, T, P>) -> Ret,
    {
        self.lock_with(f)
    }

    fn is_locked(&self) -> bool {
        self.is_locked()
    }
}

#[cfg(all(not(loom), test))]
impl<T: ?Sized, P> crate::test::LockData for Mutex<T, P> {
    fn into_inner(self) -> Self::Target
    where
        Self::Target: Sized,
    {
        self.into_inner()
    }

    fn get_mut(&mut self) -> &mut Self::Target {
        self.get_mut()
    }
}

#[cfg(all(feature = "lock_api", not(loom)))]
unsafe impl<P: Park> lock_api::RawMutex for Mutex<(), P> {
    type GuardMarker = lock_api::GuardSend;

    // It is fine to const initialize `Mutex<(), R>` since the data is not going
    // to be shared. And since it is a `Unit` type, copies will be optimized away.
    #[allow(clippy::declare_interior_mutable_const)]
    const INIT: Self = Self::new(());

    #[inline]
    fn lock(&self) {
        core::mem::forget(Self::lock(self));
    }

    #[inline]
    fn try_lock(&self) -> bool {
        Self::try_lock(self).map(core::mem::forget).is_some()
    }

    #[inline]
    unsafe fn unlock(&self) {
        self.inner.unlock();
    }

    #[inline]
    fn is_locked(&self) -> bool {
        self.is_locked()
    }
}

/// An RAII implementation of a "scoped lock" of a mutex. When this structure is
/// dropped (falls out of scope), the lock will be unlocked.
#[must_use = "if unused the Mutex will immediately unlock"]
pub struct MutexGuard<'a, T: ?Sized, P> {
    inner: inner::MutexGuard<'a, T, Parker, Parker, ParkWait<P>>,
}

// Same unsafe impls as `crate::inner::raw::MutexGuard`.
unsafe impl<T: ?Sized + Send, P> Send for MutexGuard<'_, T, P> {}
unsafe impl<T: ?Sized + Sync, P> Sync for MutexGuard<'_, T, P> {}

impl<'a, T: ?Sized, P> From<inner::MutexGuard<'a, T, Parker, Parker, ParkWait<P>>>
    for MutexGuard<'a, T, P>
{
    fn from(inner: inner::MutexGuard<'a, T, Parker, Parker, ParkWait<P>>) -> Self {
        Self { inner }
    }
}

impl<'a, T: ?Sized + Debug, P> Debug for MutexGuard<'a, T, P> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        self.inner.fmt(f)
    }
}

impl<'a, T: ?Sized + Display, P> Display for MutexGuard<'a, T, P> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        self.inner.fmt(f)
    }
}

#[cfg(not(all(loom, test)))]
impl<'a, T: ?Sized, P> core::ops::Deref for MutexGuard<'a, T, P> {
    type Target = T;

    /// Dereferences the guard to access the underlying data.
    #[inline(always)]
    fn deref(&self) -> &T {
        &self.inner
    }
}

#[cfg(not(all(loom, test)))]
impl<'a, T: ?Sized, P> core::ops::DerefMut for MutexGuard<'a, T, P> {
    /// Mutably dereferences the guard to access the underlying data.
    #[inline(always)]
    fn deref_mut(&mut self) -> &mut T {
        &mut self.inner
    }
}

/// SAFETY: A guard instance hold the lock locked, with exclusive access to the
/// underlying data.
#[cfg(all(loom, test))]
#[cfg(not(tarpaulin_include))]
unsafe impl<T: ?Sized, P> crate::loom::Guard for MutexGuard<'_, T, P> {
    type Target = T;

    fn get(&self) -> &loom::cell::UnsafeCell<Self::Target> {
        self.inner.get()
    }
}

#[cfg(all(not(loom), test))]
mod test {
    use crate::parking::barging::{immediate, yields};
    use crate::test::tests;

    type Mutex<T> = immediate::Mutex<T>;

    type ImmediateMutex<T> = immediate::Mutex<T>;
    type YieldThenParkMutex<T> = yields::Mutex<T>;

    #[test]
    fn node_waiter_drop_does_not_matter() {
        tests::node_waiter_drop_does_not_matter::<super::Parker>();
    }

    #[test]
    fn lots_and_lots_lock_immediate_park() {
        tests::lots_and_lots_lock::<ImmediateMutex<_>>();
    }

    #[test]
    fn lots_and_lots_lock_yield_than_park() {
        tests::lots_and_lots_lock::<YieldThenParkMutex<_>>();
    }

    #[test]
    fn lots_and_lots_try_lock_immediate_park() {
        tests::lots_and_lots_try_lock::<ImmediateMutex<_>>();
    }

    #[test]
    fn lots_and_lots_try_lock_yield_than_park() {
        tests::lots_and_lots_try_lock::<YieldThenParkMutex<_>>();
    }

    #[test]
    fn lots_and_lots_mixed_lock_immediate_park() {
        tests::lots_and_lots_mixed_lock::<ImmediateMutex<_>>();
    }

    #[test]
    fn lots_and_lots_mixed_lock_yield_than_park() {
        tests::lots_and_lots_mixed_lock::<YieldThenParkMutex<_>>();
    }

    #[test]
    fn smoke() {
        tests::smoke::<Mutex<_>>();
    }

    #[test]
    fn test_guard_debug_display() {
        tests::test_guard_debug_display::<Mutex<_>>();
    }

    #[test]
    fn test_mutex_debug() {
        tests::test_mutex_debug::<Mutex<_>>();
    }

    #[test]
    fn test_mutex_from() {
        tests::test_mutex_from::<Mutex<_>>();
    }

    #[test]
    fn test_mutex_default() {
        tests::test_mutex_default::<Mutex<_>>();
    }

    #[test]
    fn test_try_lock() {
        tests::test_try_lock::<Mutex<_>>();
    }

    #[test]
    fn test_into_inner() {
        tests::test_into_inner::<Mutex<_>>();
    }

    #[test]
    fn test_into_inner_drop() {
        tests::test_into_inner_drop::<Mutex<_>>();
    }

    #[test]
    fn test_get_mut() {
        tests::test_get_mut::<Mutex<_>>();
    }

    #[test]
    fn test_lock_arc_nested() {
        tests::test_lock_arc_nested::<Mutex<_>, Mutex<_>>();
    }

    #[test]
    fn test_acquire_more_than_one_lock() {
        tests::test_acquire_more_than_one_lock::<Mutex<_>>();
    }

    #[test]
    fn test_lock_arc_access_in_unwind() {
        tests::test_lock_arc_access_in_unwind::<Mutex<_>>();
    }

    #[test]
    fn test_lock_unsized() {
        tests::test_lock_unsized::<Mutex<_>>();
    }
}

#[cfg(all(loom, test))]
mod model {
    use crate::loom::models;
    use crate::parking::barging::{immediate, yields};

    #[test]
    fn try_lock_join_immediate_park() {
        models::try_lock_join::<immediate::Mutex<_>>();
    }

    #[test]
    fn lock_join_immediate_park() {
        models::lock_join::<immediate::Mutex<_>>();
    }

    #[test]
    fn mixed_lock_join_immediate_park() {
        models::mixed_lock_join::<immediate::Mutex<_>>();
    }

    #[test]
    fn try_lock_join_yield_than_park() {
        models::try_lock_join::<yields::Mutex<_>>();
    }

    #[test]
    fn lock_join_yield_than_park() {
        models::lock_join::<yields::Mutex<_>>();
    }

    #[test]
    fn mixed_lock_join_yield_than_park() {
        models::mixed_lock_join::<yields::Mutex<_>>();
    }
}
