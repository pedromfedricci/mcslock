use core::marker::PhantomData;
use core::sync::atomic::Ordering::{Acquire, Relaxed, Release};

use crate::cfg::atomic::{AtomicBool, AtomicPtr};
use crate::relax::Relax;

pub trait Waiter {
    /// Creates a new Waiter instance with the a locked state.
    ///
    /// It's expected for a implementing type to be compiler-time evaluable,
    /// since they compose node types that do require it (except Loom based
    /// nodes).
    #[cfg(not(all(loom, test)))]
    const LOCKED: Self;

    /// Creates a new Waiter instance with the a locked state.
    ///
    /// It's expected for a implementing type to be compiler-time evaluable,
    /// since they compose node types that do require it (except Loom based
    /// nodes).
    #[cfg(not(all(loom, test)))]
    const UNLOCKED: Self;

    /// Creates a new Waiter locked instance with Loom primitives (non-const).
    ///
    /// Loom primitives are not compiler-time evaluable.
    #[cfg(all(loom, test))]
    fn locked() -> Self;

    /// Creates a new Waiter unlocked instance with Loom primitives (non-const).
    ///
    /// Loom primitives are not compiler-time evaluable.
    #[cfg(all(loom, test))]
    fn unlocked() -> Self;

    /// Tries to lock the mutex.
    ///
    /// Returns `true` if successfully moved from unlocked state to locked
    /// state, `false` otherwise.
    fn try_lock(&self) -> bool;

    /// Tries to lock the mutex with a weak exchange.
    ///
    /// Returns `true` if successfully moved from unlocked state to locked
    /// state, `false` otherwise.
    fn try_lock_weak(&self) -> bool;

    fn lock_wait<W: Wait>(&self);

    /// Returns `true` if the lock is currently held.
    ///
    /// This function does not guarantee strong ordering, only atomicity.
    fn is_locked(&self) -> bool;

    fn notify(&self);
}

pub trait QueueWaiter<T>: Waiter {
    fn unlock_relax<R: Relax>(next: &AtomicPtr<T>) -> *mut T {
        let mut relax = R::default();
        loop {
            let ptr = next.load(Relaxed);
            let true = ptr.is_null() else { return ptr };
            relax.relax();
        }
    }
}

/// TODO: Docs
pub trait Wait: Default {
    /// TODO: Docs
    type Relax: Relax;

    /// TODO: Docs
    fn should_wait(&self) -> bool;

    /// TODO: Dcos
    fn relax(&mut self);
}

impl Waiter for AtomicBool {
    #[cfg(not(all(loom, test)))]
    #[allow(clippy::declare_interior_mutable_const)]
    const LOCKED: Self = Self::new(true);

    #[cfg(not(all(loom, test)))]
    #[allow(clippy::declare_interior_mutable_const)]
    const UNLOCKED: Self = Self::new(false);

    #[cfg(all(loom, test))]
    #[cfg(not(tarpaulin_include))]
    fn locked() -> Self {
        Self::new(true)
    }

    #[cfg(all(loom, test))]
    #[cfg(not(tarpaulin_include))]
    fn unlocked() -> Self {
        Self::new(false)
    }

    fn try_lock(&self) -> bool {
        self.compare_exchange(false, true, Acquire, Relaxed).is_ok()
    }

    fn try_lock_weak(&self) -> bool {
        self.compare_exchange_weak(false, true, Acquire, Relaxed).is_ok()
    }

    fn lock_wait<W: Wait>(&self) {
        // Block the thread with a relaxed loop until the load returns `false`,
        // indicating that the lock was handed off to the current thread.
        let mut relax = W::Relax::default();
        while self.load(Relaxed) {
            relax.relax();
        }
    }

    fn is_locked(&self) -> bool {
        self.load(Relaxed)
    }

    fn notify(&self) {
        self.store(false, Release);
    }
}

impl<T> QueueWaiter<T> for AtomicBool {}

#[derive(Default)]
pub struct SpinWait<R> {
    marker: PhantomData<R>,
}

impl<R: Relax> Wait for SpinWait<R> {
    type Relax = R;

    fn should_wait(&self) -> bool {
        unreachable!();
    }

    fn relax(&mut self) {
        unreachable!();
    }
}
