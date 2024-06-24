use core::fmt::{self, Debug, Display, Formatter};

use crate::cfg::cell::{UnsafeCell, WithUnchecked};
use crate::inner::raw;
use crate::lock::{Lock, Wait};

pub struct Mutex<T: ?Sized, L, Q, W> {
    lock: L,
    queue: raw::Mutex<(), Q, W>,
    data: UnsafeCell<T>,
}

// Same unsafe impls as `crate::inner::raw::Mutex`.
unsafe impl<T: ?Sized + Send, L: Send, Q, W> Send for Mutex<T, L, Q, W> {}
unsafe impl<T: ?Sized + Send, L: Send, Q, W> Sync for Mutex<T, L, Q, W> {}

impl<T, L: Lock, Q, W> Mutex<T, L, Q, W> {
    /// Creates a new mutex in an unlocked state ready for use.
    #[cfg(not(all(loom, test)))]
    pub const fn new(value: T) -> Self {
        let lock = Lock::UNLOCKED;
        let queue = raw::Mutex::new(());
        let data = UnsafeCell::new(value);
        Self { lock, queue, data }
    }

    /// Creates a new unlocked mutex with Loom primitives (non-const).
    #[cfg(all(loom, test))]
    #[cfg(not(tarpaulin_include))]
    pub fn new(value: T) -> Self {
        let lock = Lock::unlocked();
        let queue = raw::Mutex::new(());
        let data = UnsafeCell::new(value);
        Self { lock, queue, data }
    }
}

impl<T: ?Sized, L: Lock, Q: Lock, W: Wait> Mutex<T, L, Q, W> {
    /// Acquires this mutex, blocking the current thread until it is able to do so.
    pub fn lock(&self) -> MutexGuard<'_, T, L, Q, W> {
        if self.lock.try_lock_acquire_weak() {
            return MutexGuard::new(self);
        }
        let mut node = raw::MutexNode::<Q>::new();
        let guard = self.queue.lock(&mut node);
        while !self.lock.try_lock_acquire_weak() {
            self.lock.lock_wait_relaxed::<W>();
        }
        drop(guard);
        MutexGuard::new(self)
    }
}

impl<T: ?Sized, L: Lock, Q, W> Mutex<T, L, Q, W> {
    /// Attempts to acquire this mutex without blocking the thread.
    pub fn try_lock(&self) -> Option<MutexGuard<'_, T, L, Q, W>> {
        self.lock.try_lock_acquire().then(|| MutexGuard::new(self))
    }

    /// Returns `true` if the lock is currently held.
    ///
    /// This function does not guarantee strong ordering, only atomicity.
    pub fn is_locked(&self) -> bool {
        self.lock.is_locked()
    }

    /// Unlocks this mutex.
    pub fn unlock(&self) {
        self.lock.notify();
    }
}

impl<T, L, Q, W> Mutex<T, L, Q, W> {
    /// Consumes this mutex, returning the underlying data.
    pub fn into_inner(self) -> T {
        self.data.into_inner()
    }
}

impl<T: ?Sized, L, Q, W> Mutex<T, L, Q, W> {
    /// Returns a mutable reference to the underlying data.
    #[cfg(not(all(loom, test)))]
    pub fn get_mut(&mut self) -> &mut T {
        // SAFETY: We hold exclusive access to the Mutex data.
        unsafe { &mut *self.data.get() }
    }
}

impl<T: ?Sized + Debug, L: Lock, Q, W> Debug for Mutex<T, L, Q, W> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let mut d = f.debug_struct("Mutex");
        match self.try_lock() {
            Some(guard) => guard.with(|data| d.field("data", &data)),
            None => d.field("data", &format_args!("<locked>")),
        };
        d.finish()
    }
}

pub struct MutexGuard<'a, T: ?Sized, L: Lock, Q, W> {
    lock: &'a Mutex<T, L, Q, W>,
}

// Same unsafe impls as `crate::inner::raw::MutexGuard`.
unsafe impl<T: ?Sized + Send, L: Lock, Q, W> Send for MutexGuard<'_, T, L, Q, W> {}
unsafe impl<T: ?Sized + Sync, L: Lock, Q, W> Sync for MutexGuard<'_, T, L, Q, W> {}

impl<'a, T: ?Sized, L: Lock, Q, W> MutexGuard<'a, T, L, Q, W> {
    /// Creates a new `MutexGuard` instance.
    const fn new(lock: &'a Mutex<T, L, Q, W>) -> Self {
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

impl<T: ?Sized, L: Lock, Q, W> Drop for MutexGuard<'_, T, L, Q, W> {
    fn drop(&mut self) {
        self.lock.unlock();
    }
}

impl<'a, T: ?Sized + Debug, L: Lock, Q, W> Debug for MutexGuard<'a, T, L, Q, W> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        self.with(|data| data.fmt(f))
    }
}

impl<'a, T: ?Sized + Display, L: Lock, Q, W> Display for MutexGuard<'a, T, L, Q, W> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        self.with(|data| data.fmt(f))
    }
}

#[cfg(not(all(loom, test)))]
impl<'a, T: ?Sized, L: Lock, Q, W> core::ops::Deref for MutexGuard<'a, T, L, Q, W> {
    type Target = T;

    /// Dereferences the guard to access the underlying data.
    fn deref(&self) -> &T {
        // SAFETY: A guard instance holds the lock locked.
        unsafe { &*self.lock.data.get() }
    }
}

#[cfg(not(all(loom, test)))]
impl<'a, T: ?Sized, L: Lock, Q, W> core::ops::DerefMut for MutexGuard<'a, T, L, Q, W> {
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
unsafe impl<T: ?Sized, L: Lock, Q, W> crate::loom::Guard for MutexGuard<'_, T, L, Q, W> {
    type Target = T;

    fn get(&self) -> &loom::cell::UnsafeCell<Self::Target> {
        &self.lock.data
    }
}
