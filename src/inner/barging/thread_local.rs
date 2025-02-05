use core::ops::DerefMut;

use super::{Mutex, MutexGuard};
use crate::inner::raw::{self, Key};
use crate::lock::{Lock, Wait};

impl<T: ?Sized, L: Lock, Ws: Wait, Wq: Wait> Mutex<T, L, Ws, Wq> {
    /// Acquires this mutex, blocking the current thread until it is able to do so.
    ///
    /// This implementation will access and modify queue nodes that are stored
    /// in the thread local storage of the locking threads. That is, the number
    /// of queue nodes is proportional at 1:1 to the number of locking threads.
    ///
    /// # Safety
    ///
    /// See: `lock_with_local_then_unchecked`.
    ///
    /// # Panics
    ///
    /// See: `lock_with_local_then_unchecked`.
    pub unsafe fn lock_with_local_unchecked<N>(&self, node: Key<N>) -> MutexGuard<'_, T, L, Ws, Wq>
    where
        N: DerefMut<Target = raw::MutexNode<L>>,
    {
        if self.lock.try_lock_acquire_weak() {
            return MutexGuard::new(self);
        }
        // SAFETY: Caller guaranteed that the target thread local queue node is
        // exclusively borrowed to this function. And, within this scope, the
        // borrow of the queue node is exclusively given to the inner queue
        // `lock with local` operation, throughout all of its scope duration.
        unsafe {
            self.queue.lock_with_local_then_unchecked(node, |()| {
                while !self.lock.try_lock_acquire_weak() {
                    self.lock.wait_lock_relaxed::<Ws>();
                }
            });
        }
        MutexGuard::new(self)
    }
}
