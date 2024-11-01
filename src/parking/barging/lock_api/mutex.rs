use crate::parking::barging;

#[cfg(test)]
use crate::parking::park::Park;
#[cfg(test)]
use crate::test::{LockData, LockNew, LockThen, TryLockThen};

/// A [`lock_api::Mutex`] alias that wraps a [`parking::barging::Mutex`].
///
/// [`parking::barging::Mutex`]: crate::parking::barging::Mutex
/// [`lock_api::Mutex`]: https://docs.rs/lock_api/latest/lock_api/struct.Mutex.html
pub type Mutex<T, Ps, Pq> = lock_api::Mutex<barging::Mutex<(), Ps, Pq>, T>;

/// A [`lock_api::MutexGuard`] alias that wraps a [`parking::barging::MutexGuard`].
///
/// [`parking::barging::MutexGuard`]: crate::parking::barging::MutexGuard
/// [`lock_api::MutexGuard`]: https://docs.rs/lock_api/latest/lock_api/struct.MutexGuard.html
pub type MutexGuard<'a, T, Ps, Pq> = lock_api::MutexGuard<'a, barging::Mutex<(), Ps, Pq>, T>;

#[cfg(test)]
impl<T: ?Sized, Ps: Park, Pq: Park> LockNew for Mutex<T, Ps, Pq> {
    type Target = T;

    fn new(value: Self::Target) -> Self
    where
        Self::Target: Sized,
    {
        Self::new(value)
    }
}

#[cfg(test)]
impl<T: ?Sized, Ps: Park, Pq: Park> LockThen for Mutex<T, Ps, Pq> {
    type Guard<'a> = &'a mut Self::Target
    where
        Self: 'a,
        Self::Target: 'a;

    fn lock_then<F, Ret>(&self, f: F) -> Ret
    where
        F: FnOnce(&mut Self::Target) -> Ret,
    {
        f(&mut *self.lock())
    }
}

#[cfg(test)]
impl<T: ?Sized, Ps: Park, Pq: Park> TryLockThen for Mutex<T, Ps, Pq> {
    fn try_lock_then<F, Ret>(&self, f: F) -> Ret
    where
        F: FnOnce(Option<&mut Self::Target>) -> Ret,
    {
        f(self.try_lock().as_deref_mut())
    }

    fn is_locked(&self) -> bool {
        self.is_locked()
    }
}

#[cfg(test)]
impl<T: ?Sized, Ps: Park, Pq: Park> LockData for Mutex<T, Ps, Pq> {
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

#[cfg(test)]
mod test {
    use crate::parking::barging::lock_api::{immediate, yields};
    use crate::test::tests;

    type Mutex<T> = immediate::Mutex<T>;

    type ImmediateMutex<T> = immediate::Mutex<T>;
    type YieldThenParkMutex<T> = yields::Mutex<T>;

    #[test]
    fn lots_and_lots_lock_immediate_park() {
        tests::lots_and_lots_lock::<ImmediateMutex<_>>();
    }

    #[test]
    fn lots_and_lots_lock_yield_then_park() {
        tests::lots_and_lots_lock::<YieldThenParkMutex<_>>();
    }

    #[test]
    fn lots_and_lots_try_lock_immediate_park() {
        tests::lots_and_lots_try_lock::<ImmediateMutex<_>>();
    }

    #[test]
    fn lots_and_lots_try_lock_yield_then_park() {
        tests::lots_and_lots_try_lock::<YieldThenParkMutex<_>>();
    }

    #[test]
    fn lots_and_lots_mixed_lock_immediate_park() {
        tests::lots_and_lots_mixed_lock::<ImmediateMutex<_>>();
    }

    #[test]
    fn lots_and_lots_mixed_lock_yield_then_park() {
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
