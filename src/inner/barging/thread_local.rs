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
    /// Caller must guarantee that the thread local node is not already in use
    /// by another locking operation for the current thread. The thread local
    /// node borrow is released to the current thread once this functions returns.
    ///
    /// # Panics
    ///
    /// Panics if the key currently has its destructor running, and it **may**
    /// panic if the destructor has previously been run for this thread.
    pub unsafe fn lock_with_local_unchecked<N>(&self, node: Key<N>) -> MutexGuard<'_, T, L, Ws, Wq>
    where
        N: DerefMut<Target = raw::MutexNode<L>>,
    {
        // SAFETY: Caller guaranteed that we have exclusive access over `node`.
        self.lock(|f| unsafe { self.queue.lock_with_local_then_unchecked(node, |()| f(self)) })
    }
}
