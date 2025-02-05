use super::{Mutex, MutexGuard};
use crate::parking::park::Park;

#[cfg(test)]
use crate::test::{LockNew, LockThen, LockWithThen, TryLockThen, TryLockWithThen};

impl<T: ?Sized, Ps: Park, Pq: Park> Mutex<T, Ps, Pq> {
    /// Underlying implementation of `lock` that is only enabled when the
    /// `thread_local` feature is enabled.
    ///
    /// This implementation will access and modify queue nodes that are stored
    /// in the thread local storage of the locking threads. That is, the number
    /// of queue nodes is proportional at 1:1 to the number of locking threads.
    pub(super) fn lock_with_local_queue_node(&self) -> MutexGuard<'_, T, Ps, Pq> {
        crate::thread_local_parking_node!(static NODE);
        // SAFETY: The thread local node: `NODE` is not borrowed to any other
        // locking operation for all duration of the `inner` borrow of it.
        unsafe { self.inner.lock_with_local_unchecked(&NODE.inner) }.into()
    }
}

/// A Mutex wrapper type that calls `lock_with_local_queue_node` when
/// implementing testing traits.
#[cfg(test)]
struct MutexLocalNode<T: ?Sized, Ps, Pq>(Mutex<T, Ps, Pq>);

#[cfg(test)]
impl<T: ?Sized, Ps, Pq> LockNew for MutexLocalNode<T, Ps, Pq> {
    type Target = T;

    fn new(value: Self::Target) -> Self
    where
        Self::Target: Sized,
    {
        Self(Mutex::new(value))
    }
}

#[cfg(test)]
impl<T: ?Sized, Ps: Park, Pq: Park> LockWithThen for MutexLocalNode<T, Ps, Pq> {
    // The barging mutex does not require queue node access.
    type Node = ();

    type Guard<'a>
        = MutexGuard<'a, T, Ps, Pq>
    where
        Self: 'a,
        Self::Target: 'a;

    fn lock_with_then<F, Ret>(&self, (): &mut Self::Node, f: F) -> Ret
    where
        F: FnOnce(MutexGuard<'_, T, Ps, Pq>) -> Ret,
    {
        f(self.0.lock_with_local_queue_node())
    }
}

#[cfg(test)]
impl<T: ?Sized, Ps: Park, Pq: Park> TryLockWithThen for MutexLocalNode<T, Ps, Pq> {
    fn try_lock_with_then<F, Ret>(&self, (): &mut Self::Node, f: F) -> Ret
    where
        F: FnOnce(Option<MutexGuard<'_, T, Ps, Pq>>) -> Ret,
    {
        self.0.try_lock_then(f)
    }

    fn is_locked(&self) -> bool {
        self.0.is_locked()
    }
}

#[cfg(test)]
impl<T: ?Sized, Ps: Park, Pq: Park> LockThen for MutexLocalNode<T, Ps, Pq> {
    fn lock_then<F, Ret>(&self, f: F) -> Ret
    where
        F: FnOnce(MutexGuard<'_, T, Ps, Pq>) -> Ret,
    {
        self.0.lock_then(f)
    }
}

#[cfg(test)]
impl<T: ?Sized, Ps: Park, Pq: Park> TryLockThen for MutexLocalNode<T, Ps, Pq> {}

#[cfg(all(not(loom), test))]
mod test {
    use crate::parking::park::ImmediatePark;
    use crate::test::tests;

    type Mutex<T> = super::MutexLocalNode<T, ImmediatePark, ImmediatePark>;

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
    use crate::parking::park::ImmediatePark;

    type Mutex<T> = super::MutexLocalNode<T, ImmediatePark, ImmediatePark>;

    #[test]
    fn lock_join() {
        models::lock_join::<Mutex<_>>();
    }
}
