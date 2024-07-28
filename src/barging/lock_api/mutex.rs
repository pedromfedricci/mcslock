use crate::barging;

#[cfg(test)]
use crate::relax::Relax;
#[cfg(test)]
use crate::test::{LockData, LockNew, LockWith};

/// A lock that provides mutually exclusive data access that is compatible with
/// [`lock_api`](https://crates.io/crates/lock_api).
pub type Mutex<T, Rs, Rq> = lock_api::Mutex<barging::Mutex<(), Rs, Rq>, T>;

/// A guard that provides mutable data access that is compatible with
/// [`lock_api`](https://crates.io/crates/lock_api).
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
impl<T: ?Sized, Rs: Relax, Rq: Relax> LockWith for Mutex<T, Rs, Rq> {
    type Guard<'a> = MutexGuard<'a, Self::Target, Rs, Rq>
    where
        Self: 'a,
        Self::Target: 'a;

    fn try_lock_with<F, Ret>(&self, f: F) -> Ret
    where
        F: FnOnce(Option<MutexGuard<'_, T, Rs, Rq>>) -> Ret,
    {
        f(self.try_lock())
    }

    fn lock_with<F, Ret>(&self, f: F) -> Ret
    where
        F: FnOnce(MutexGuard<'_, T, Rs, Rq>) -> Ret,
    {
        f(self.lock())
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
    fn lots_and_lots() {
        tests::lots_and_lots::<Mutex<_>>();
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
