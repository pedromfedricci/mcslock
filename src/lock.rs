use core::sync::atomic::Ordering::{Acquire, Relaxed, Release};

use crate::cfg::atomic::AtomicBool;
use crate::relax::Relax;

/// A `Lock` is some arbitrary data type used by a lock implementation to
/// manage the state of the lock.
pub trait Lock {
    /// Creates a new locked `Lock` instance.
    ///
    /// It's expected for a implementing type to be compiler-time evaluable,
    /// since they compose node types that do require it (except Loom based
    /// nodes).
    #[cfg(not(all(loom, test)))]
    const LOCKED: Self;

    /// Creates a new unlocked `Lock` instance.
    ///
    /// It's expected for a implementing type to be compiler-time evaluable,
    /// since they compose node types that do require it (except Loom based
    /// nodes).
    #[cfg(not(all(loom, test)))]
    const UNLOCKED: Self;

    /// Creates a new locked `Lock` instance with Loom primitives (non-const).
    ///
    /// Loom primitives are not compiler-time evaluable.
    #[cfg(all(loom, test))]
    fn locked() -> Self;

    /// Creates a new unlocked `Lock` instance with Loom primitives (non-const).
    ///
    /// Loom primitives are not compiler-time evaluable.
    #[cfg(all(loom, test))]
    fn unlocked() -> Self;

    /// Tries to lock the mutex with acquire ordering.
    ///
    /// Returns `true` if successfully moved from unlocked state to locked
    /// state, `false` otherwise.
    fn try_lock_acquire(&self) -> bool;

    /// Tries to lock the mutex with acquire ordering and weak exchange.
    ///
    /// Returns `true` if successfully moved from unlocked state to locked
    /// state, `false` otherwise.
    fn try_lock_acquire_weak(&self) -> bool;

    /// Blocks the thread untill the lock is acquired, applies some arbitrary
    /// waiting policy while the lock is still on hold somewhere else.
    ///
    /// The lock is loaded with a relaxed ordering.
    fn wait_lock_relaxed<W: Wait>(&self);

    /// Returns `true` if the lock is currently held.
    ///
    /// This function does not guarantee strong ordering, only atomicity.
    fn is_locked_relaxed(&self) -> bool;

    /// Changes the state of the lock and, possibly, notifies that change
    /// to some other interested party.
    fn notify_release(&self);
}

/// The waiting policy that should be applied while the lock state has not
/// reached some target state.
pub trait Wait {
    /// The relax operation excuted inside `lock` busy-wait loops.
    type LockRelax: Relax;

    /// The relax operation excuted inside `unlock` busy-wait loops.
    type UnlockRelax: Relax;

    /// Returns a initialzed relax waiting policy.
    fn relax_policy() -> RelaxPolicy<Self> {
        let relax = Self::LockRelax::new();
        RelaxPolicy { relax }
    }
}

/// A waiting policy that is only composed of a relax policy.
pub struct RelaxPolicy<W: Wait + ?Sized> {
    pub relax: W::LockRelax,
}

impl Lock for AtomicBool {
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

    fn try_lock_acquire(&self) -> bool {
        self.compare_exchange(false, true, Acquire, Relaxed).is_ok()
    }

    fn try_lock_acquire_weak(&self) -> bool {
        self.compare_exchange_weak(false, true, Acquire, Relaxed).is_ok()
    }

    fn wait_lock_relaxed<W: Wait>(&self) {
        // Block the thread with a relaxed loop until the load returns `false`,
        // indicating that the lock was handed off to the current thread.
        let mut relax_policy = W::relax_policy();
        while self.load(Relaxed) {
            relax_policy.relax.relax();
        }
    }

    fn is_locked_relaxed(&self) -> bool {
        self.load(Relaxed)
    }

    fn notify_release(&self) {
        self.store(false, Release);
    }
}
