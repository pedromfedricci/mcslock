use crate::barging;

#[cfg(test)]
use crate::relax::Relax;
#[cfg(test)]
use crate::test::{LockData, LockNew, LockThen, TryLockThen};

/// A [`lock_api::Mutex`] alias that wraps a [`barging::Mutex`].
///
/// [`lock_api::Mutex`]: https://docs.rs/lock_api/latest/lock_api/struct.Mutex.html
pub type Mutex<T, Rs, Rq> = lock_api::Mutex<barging::Mutex<(), Rs, Rq>, T>;

/// A [`lock_api::MutexGuard`] alias that wraps a [`barging::MutexGuard`].
///
/// [`lock_api::MutexGuard`]: https://docs.rs/lock_api/latest/lock_api/struct.MutexGuard.html
pub type MutexGuard<'a, T, Rs, Rq> = lock_api::MutexGuard<'a, barging::Mutex<(), Rs, Rq>, T>;

#[cfg(test)]
impl<T: ?Sized, Rs: Relax, Rq: Relax> LockNew for Mutex<T, Rs, Rq> {
    type Target = T;

    fn new(value: Self::Target) -> Self
    where
        Self::Target: Sized,
    {
        Self::new(value)
    }
}

#[cfg(test)]
impl<T: ?Sized, Rs: Relax, Rq: Relax> LockThen for Mutex<T, Rs, Rq> {
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
impl<T: ?Sized, Rs: Relax, Rq: Relax> TryLockThen for Mutex<T, Rs, Rq> {
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
impl<T: ?Sized, Rs: Relax, Rq: Relax> LockData for Mutex<T, Rs, Rq> {
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
    use crate::barging::lock_api::yields::Mutex;
    use crate::test::tests;

    #[test]
    fn lots_and_lots_lock() {
        tests::lots_and_lots_lock::<Mutex<_>>();
    }

    #[test]
    fn lots_and_lots_try_lock() {
        tests::lots_and_lots_try_lock::<Mutex<_>>();
    }

    #[test]
    fn lots_and_lots_mixed_lock() {
        tests::lots_and_lots_mixed_lock::<Mutex<_>>();
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
