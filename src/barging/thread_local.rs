use super::{Mutex, MutexGuard};
use crate::relax::Relax;

#[cfg(test)]
use crate::test::{LockNew, LockThen, LockWithThen, TryLockThen, TryLockWithThen};

impl<T: ?Sized, Rs: Relax, Rq: Relax> Mutex<T, Rs, Rq> {
    /// Underlying implementation of `lock` that is only enabled when the
    /// `thread_local` feature is enabled.
    ///
    /// This implementation will access and modify queue nodes that are stored
    /// in the thread local storage of the locking threads. That is, the number
    /// of queue nodes is proportional at 1:1 to the number of locking threads.
    pub(super) fn lock_with_local_queue_node(&self) -> MutexGuard<'_, T, Rs, Rq> {
        crate::thread_local_node!(static NODE);
        // SAFETY: The thread local node: `NODE` is not borrowed to any other
        // locking operation for all duration of the `inner` borrow of it.
        unsafe { self.inner.lock_with_local_unchecked(&NODE.inner) }.into()
    }
}

/// A Mutex wrapper type that calls `lock_with_local_queue_node` when
/// implementing testing traits.
#[cfg(test)]
struct MutexLocalNode<T: ?Sized, Rs, Rq>(Mutex<T, Rs, Rq>);

#[cfg(test)]
impl<T: ?Sized, Rs, Rq> LockNew for MutexLocalNode<T, Rs, Rq> {
    type Target = T;

    fn new(value: Self::Target) -> Self
    where
        Self::Target: Sized,
    {
        Self(Mutex::new(value))
    }
}

#[cfg(test)]
impl<T: ?Sized, Rs: Relax, Rq: Relax> LockWithThen for MutexLocalNode<T, Rs, Rq> {
    // The barging mutex does not require queue node access.
    type Node = ();

    type Guard<'a>
        = MutexGuard<'a, T, Rs, Rq>
    where
        Self: 'a,
        Self::Target: 'a;

    fn lock_with_then<F, Ret>(&self, (): &mut Self::Node, f: F) -> Ret
    where
        F: FnOnce(MutexGuard<'_, T, Rs, Rq>) -> Ret,
    {
        f(self.0.lock_with_local_queue_node())
    }
}

#[cfg(test)]
impl<T: ?Sized, Rs: Relax, Rq: Relax> TryLockWithThen for MutexLocalNode<T, Rs, Rq> {
    fn try_lock_with_then<F, Ret>(&self, (): &mut Self::Node, f: F) -> Ret
    where
        F: FnOnce(Option<MutexGuard<'_, T, Rs, Rq>>) -> Ret,
    {
        self.0.try_lock_then(f)
    }

    fn is_locked(&self) -> bool {
        self.0.is_locked()
    }
}

#[cfg(test)]
impl<T: ?Sized, Rs: Relax, Rq: Relax> LockThen for MutexLocalNode<T, Rs, Rq> {
    fn lock_then<F, Ret>(&self, f: F) -> Ret
    where
        F: FnOnce(MutexGuard<'_, T, Rs, Rq>) -> Ret,
    {
        self.0.lock_then(f)
    }
}

#[cfg(test)]
impl<T: ?Sized, Rs: Relax, Rq: Relax> TryLockThen for MutexLocalNode<T, Rs, Rq> {}

#[cfg(all(not(loom), test))]
mod test {
    use crate::relax::Yield;
    use crate::test::tests;

    type Mutex<T> = super::MutexLocalNode<T, Yield, Yield>;

    #[test]
    fn lots_and_lots_lock() {
        tests::lots_and_lots_lock::<Mutex<_>>();
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
    use crate::relax::Yield;

    type Mutex<T> = super::MutexLocalNode<T, Yield, Yield>;

    #[test]
    fn lock_join() {
        models::lock_join::<Mutex<_>>();
    }
}
