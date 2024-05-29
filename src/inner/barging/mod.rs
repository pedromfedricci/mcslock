use core::fmt::{self, Debug, Display, Formatter};

use crate::cfg::cell::{UnsafeCell, WithUnchecked};
use crate::inner::raw;
use crate::wait::{QueueWaiter, Wait, Waiter};

pub struct Mutex<T: ?Sized, W, Q, P> {
    waiter: W,
    queue: raw::Mutex<(), Q, P>,
    data: UnsafeCell<T>,
}

// Same unsafe impls as `crate::inner::raw::Mutex`.
unsafe impl<T: ?Sized + Send, W: Send, Q, P> Send for Mutex<T, W, Q, P> {}
unsafe impl<T: ?Sized + Send, W: Send, Q, P> Sync for Mutex<T, W, Q, P> {}

impl<T, W, Q, P> Mutex<T, W, Q, P> {
    /// Consumes this mutex, returning the underlying data.
    pub fn into_inner(self) -> T {
        self.data.into_inner()
    }
}

impl<T, W: Waiter, Q, P> Mutex<T, W, Q, P> {
    /// Creates a new mutex in an unlocked state ready for use.
    #[cfg(not(all(loom, test)))]
    pub const fn new(value: T) -> Self {
        let waiter = Waiter::UNLOCKED;
        let queue = raw::Mutex::new(());
        let data = UnsafeCell::new(value);
        Self { waiter, queue, data }
    }

    /// Creates a new unlocked mutex with Loom primitives (non-const).
    #[cfg(all(loom, test))]
    #[cfg(not(tarpaulin_include))]
    pub fn new(value: T) -> Self {
        let waiter = Waiter::unlocked();
        let queue = raw::Mutex::new(());
        let data = UnsafeCell::new(value);
        Self { waiter, queue, data }
    }
}

impl<T: ?Sized, W: Waiter, Q: QueueWaiter<raw::MutexNodeInit<Q>>, P: Wait> Mutex<T, W, Q, P> {
    /// Acquires this mutex, blocking the current thread until it is able to do so.
    pub fn lock(&self) -> MutexGuard<'_, T, W, Q, P> {
        if self.waiter.try_lock() {
            return MutexGuard::new(self);
        }
        let mut node = raw::MutexNode::<Q>::new();
        let guard = self.queue.lock(&mut node);
        while !self.waiter.try_lock_weak() {
            self.waiter.lock_wait::<P>();
        }
        drop(guard);
        MutexGuard::new(self)
    }
}

impl<T: ?Sized, W: Waiter, Q, P> Mutex<T, W, Q, P> {
    /// Attempts to acquire this mutex without blocking the thread.
    pub fn try_lock(&self) -> Option<MutexGuard<'_, T, W, Q, P>> {
        self.waiter.try_lock().then(|| MutexGuard::new(self))
    }

    /// Returns `true` if the lock is currently held.
    ///
    /// This function does not guarantee strong ordering, only atomicity.
    pub fn is_locked(&self) -> bool {
        self.waiter.is_locked()
    }

    /// Unlocks this mutex.
    pub fn unlock(&self) {
        self.waiter.notify();
    }
}

impl<T: ?Sized, W, Q, P> Mutex<T, W, Q, P> {
    /// Returns a mutable reference to the underlying data.
    #[cfg(not(all(loom, test)))]
    pub fn get_mut(&mut self) -> &mut T {
        // SAFETY: We hold exclusive access to the Mutex data.
        unsafe { &mut *self.data.get() }
    }
}

impl<T: ?Sized + Debug, W: Waiter, Q, P> Debug for Mutex<T, W, Q, P> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let mut d = f.debug_struct("Mutex");
        match self.try_lock() {
            Some(guard) => guard.with(|data| d.field("data", &data)),
            None => d.field("data", &format_args!("<locked>")),
        };
        d.finish()
    }
}

pub struct MutexGuard<'a, T: ?Sized, W: Waiter, Q, P> {
    lock: &'a Mutex<T, W, Q, P>,
}

// Same unsafe impls as `crate::inner::raw::MutexGuard`.
unsafe impl<T: ?Sized + Send, W: Waiter, Q, P> Send for MutexGuard<'_, T, W, Q, P> {}
unsafe impl<T: ?Sized + Sync, W: Waiter, Q, P> Sync for MutexGuard<'_, T, W, Q, P> {}

impl<'a, T: ?Sized, W: Waiter, Q, P> MutexGuard<'a, T, W, Q, P> {
    /// Creates a new `MutexGuard` instance.
    const fn new(lock: &'a Mutex<T, W, Q, P>) -> Self {
        Self { lock }
    }

    /// Runs `f` against an shared reference pointing to the underlying data.
    fn with<F, Ret>(&self, f: F) -> Ret
    where
        F: FnOnce(&T) -> Ret,
    {
        // SAFETY: A guard instance holds the lock locked.
        unsafe { self.lock.data.with_unchecked(f) }
    }
}

impl<T: ?Sized, W: Waiter, Q, P> Drop for MutexGuard<'_, T, W, Q, P> {
    fn drop(&mut self) {
        self.lock.unlock();
    }
}

impl<'a, T: ?Sized + Debug, W: Waiter, Q, P> Debug for MutexGuard<'a, T, W, Q, P> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        self.with(|data| data.fmt(f))
    }
}

impl<'a, T: ?Sized + Display, W: Waiter, Q, P> Display for MutexGuard<'a, T, W, Q, P> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        self.with(|data| data.fmt(f))
    }
}

#[cfg(not(all(loom, test)))]
impl<'a, T: ?Sized, W: Waiter, Q, P> core::ops::Deref for MutexGuard<'a, T, W, Q, P> {
    type Target = T;

    /// Dereferences the guard to access the underlying data.
    fn deref(&self) -> &T {
        // SAFETY: A guard instance holds the lock locked.
        unsafe { &*self.lock.data.get() }
    }
}

#[cfg(not(all(loom, test)))]
impl<'a, T: ?Sized, W: Waiter, Q, P> core::ops::DerefMut for MutexGuard<'a, T, W, Q, P> {
    /// Mutably dereferences the guard to access the underlying data.
    fn deref_mut(&mut self) -> &mut T {
        // SAFETY: A guard instance holds the lock locked.
        unsafe { &mut *self.lock.data.get() }
    }
}

/// SAFETY: A guard instance hold the lock locked, with exclusive access to the
/// underlying data.
#[cfg(all(loom, test))]
#[cfg(not(tarpaulin_include))]
unsafe impl<T: ?Sized, W: Waiter, Q, P> crate::loom::Guard for MutexGuard<'_, T, W, Q, P> {
    type Target = T;

    fn get(&self) -> &loom::cell::UnsafeCell<Self::Target> {
        &self.lock.data
    }
}
