use core::fmt::{self, Debug, Display, Formatter};
use core::marker::PhantomData;

use crate::cfg::cell::{UnsafeCell, UnsafeCellWith};
use crate::inner::raw;
use crate::lock::{Lock, Wait};

#[cfg(feature = "thread_local")]
mod thread_local;

/// A mutual exclusion primitive implementing a barging MCS lock protocol, useful
/// for protecting shared data.
pub struct Mutex<T: ?Sized, L, Ws, Wq> {
    lock: L,
    queue: raw::Mutex<(), L, Wq>,
    marker: PhantomData<Ws>,
    data: UnsafeCell<T>,
}

// Same unsafe impls as `crate::inner::raw::Mutex`.
unsafe impl<T: ?Sized + Send, L: Send, Ws, Wq> Send for Mutex<T, L, Ws, Wq> {}
unsafe impl<T: ?Sized + Send, L: Send, Ws, Wq> Sync for Mutex<T, L, Ws, Wq> {}

impl<T, L: Lock, Ws, Wq> Mutex<T, L, Ws, Wq> {
    /// Creates a new, unlocked and core based mutex (const).
    #[cfg(not(all(loom, test)))]
    pub const fn new(value: T) -> Self {
        let lock = Lock::UNLOCKED;
        let queue = raw::Mutex::new(());
        let data = UnsafeCell::new(value);
        Self { lock, queue, data, marker: PhantomData }
    }

    /// Creates a new, unlocked and loom base mutex (non-const).
    #[cfg(all(loom, test))]
    #[cfg(not(tarpaulin_include))]
    pub fn new(value: T) -> Self {
        let lock = Lock::unlocked();
        let queue = raw::Mutex::new(());
        let data = UnsafeCell::new(value);
        Self { lock, queue, data, marker: PhantomData }
    }
}

impl<T: ?Sized, L: Lock, Ws: Wait, Wq: Wait> Mutex<T, L, Ws, Wq> {
    /// Acquires this mutex, blocking the current thread until it is able to do so.
    ///
    /// This implementation will allocate, access and modify a queue node for
    /// each call, storing it at the current stack frame.
    #[cfg(any(test, not(feature = "thread_local")))]
    pub fn lock(&self) -> MutexGuard<'_, T, L, Ws, Wq> {
        if self.lock.try_lock_acquire_weak() {
            return MutexGuard::new(self);
        }
        let mut node = raw::MutexNode::new();
        self.queue.lock_with_then(&mut node, |()| {
            while !self.lock.try_lock_acquire_weak() {
                self.lock.wait_lock_relaxed::<Ws>();
            }
        });
        MutexGuard::new(self)
    }
}

impl<T: ?Sized, L: Lock, Ws, Wq> Mutex<T, L, Ws, Wq> {
    /// Attempts to acquire this mutex without blocking the thread.
    pub fn try_lock(&self) -> Option<MutexGuard<'_, T, L, Ws, Wq>> {
        self.lock.try_lock_acquire().then(|| MutexGuard::new(self))
    }

    /// Returns `true` if the lock is currently held.
    ///
    /// This function does not guarantee strong ordering, only atomicity.
    pub fn is_locked(&self) -> bool {
        self.lock.is_locked_relaxed()
    }

    /// Unlocks this mutex.
    pub fn unlock(&self) {
        self.lock.notify_release();
    }
}

impl<T, L, Ws, Wq> Mutex<T, L, Ws, Wq> {
    /// Consumes this mutex, returning the underlying data.
    pub fn into_inner(self) -> T {
        self.data.into_inner()
    }
}

impl<T: ?Sized, L, Ws, Wq> Mutex<T, L, Ws, Wq> {
    /// Returns a mutable reference to the underlying data.
    #[cfg(not(all(loom, test)))]
    pub fn get_mut(&mut self) -> &mut T {
        // SAFETY: We hold exclusive access to the Mutex data.
        unsafe { &mut *self.data.get() }
    }
}

impl<T: ?Sized + Debug, L: Lock, Ws, Wq> Debug for Mutex<T, L, Ws, Wq> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let mut d = f.debug_struct("Mutex");
        match self.try_lock() {
            Some(guard) => guard.with(|data| d.field("data", &data)),
            None => d.field("data", &format_args!("<locked>")),
        };
        d.finish()
    }
}

/// An RAII implementation of a "scoped lock" of a mutex. When this structure is
/// dropped (falls out of scope), the lock will be unlocked.
#[must_use = "if unused the Mutex will immediately unlock"]
pub struct MutexGuard<'a, T: ?Sized, L: Lock, Ws, Wq> {
    lock: &'a Mutex<T, L, Ws, Wq>,
}

// Rust's `std::sync::MutexGuard` is not Send for pthread compatibility, but this
// impl is safe to be Send. Same unsafe Sync impl as `std::sync::MutexGuard`.
unsafe impl<T: ?Sized + Send, L: Lock, Ws, Wq> Send for MutexGuard<'_, T, L, Ws, Wq> {}
unsafe impl<T: ?Sized + Sync, L: Lock, Ws, Wq> Sync for MutexGuard<'_, T, L, Ws, Wq> {}

impl<'a, T: ?Sized, L: Lock, Ws, Wq> MutexGuard<'a, T, L, Ws, Wq> {
    /// Creates a new `MutexGuard` instance.
    const fn new(lock: &'a Mutex<T, L, Ws, Wq>) -> Self {
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

impl<T: ?Sized + Debug, L: Lock, Ws, Wq> Debug for MutexGuard<'_, T, L, Ws, Wq> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        self.with(|data| data.fmt(f))
    }
}

impl<T: ?Sized + Display, L: Lock, Ws, Wq> Display for MutexGuard<'_, T, L, Ws, Wq> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        self.with(|data| data.fmt(f))
    }
}

#[cfg(not(all(loom, test)))]
impl<T: ?Sized, L: Lock, Ws, Wq> core::ops::Deref for MutexGuard<'_, T, L, Ws, Wq> {
    type Target = T;

    /// Dereferences the guard to access the underlying data.
    fn deref(&self) -> &T {
        // SAFETY: A guard instance holds the lock locked.
        unsafe { &*self.lock.data.get() }
    }
}

#[cfg(not(all(loom, test)))]
impl<T: ?Sized, L: Lock, Ws, Wq> core::ops::DerefMut for MutexGuard<'_, T, L, Ws, Wq> {
    /// Mutably dereferences the guard to access the underlying data.
    fn deref_mut(&mut self) -> &mut T {
        // SAFETY: A guard instance holds the lock locked.
        unsafe { &mut *self.lock.data.get() }
    }
}

impl<T: ?Sized, L: Lock, Ws, Wq> Drop for MutexGuard<'_, T, L, Ws, Wq> {
    fn drop(&mut self) {
        self.lock.unlock();
    }
}

// SAFETY: A guard instance hold the lock locked, with exclusive access to the
// underlying data.
#[cfg(all(loom, test))]
#[cfg(not(tarpaulin_include))]
unsafe impl<T: ?Sized, L: Lock, Ws, Wq> crate::loom::Guard for MutexGuard<'_, T, L, Ws, Wq> {
    type Target = T;

    fn get(&self) -> &loom::cell::UnsafeCell<Self::Target> {
        &self.lock.data
    }
}
