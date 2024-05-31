use core::sync::atomic::Ordering::{Acquire, Relaxed, Release};

use crate::cfg::atomic::AtomicBool;
use crate::relax::Relax;

/// A `Lock` is some arbitrary data type used by a lock implementation to
/// manage the state of the lock.
///
/// The `no_std` implementations (eg `raw` and `barging`) can simply use a
/// `AtomicBool` to manage state. The parking variants thought, need platform
/// specific data types. We are currently using the `atomic_wait` crate for
/// easy parking integration. It uses `AtomicU32` as the data type for all
/// major platforms.
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

    /// Blocks the thread untill the lock is acquired, applies some arbitrary
    /// waiting policy while the lock is still on hold somewhere else.
    ///
    /// This function is only meant to return when the lock has been acquired.
    fn lock_wait<W: Wait>(&self);

    /// Returns `true` if the lock is currently held.
    ///
    /// This function does not guarantee strong ordering, only atomicity.
    fn is_locked(&self) -> bool;

    /// Changes the state of the lock and, possibly, notifies that change
    /// to some other interested party.
    fn notify(&self);
}

/// The waiting policy that should be applied while the lock state has not
/// reached some target state.
pub trait Wait: Relax {
    /// The relax operation that should be applied during unlock waiting loops.
    type UnlockRelax: Relax;

    /// Hints whether or not should the `parking` operation be executed at this
    /// time.
    ///
    /// Returning `true` means we are not ready to run the park operation yet,
    /// there is some other event that should occur first. Returning `false`
    /// indicates that we are no longer waiting for any event, hinting that the
    /// park operation should be executed.
    ///
    /// `no_std` implementations will simply ignore this function and only use
    /// the `Self::relax` and `Self::UnlockRelax::relax` functions.
    fn should_wait(&self) -> bool;
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

    fn try_lock(&self) -> bool {
        self.compare_exchange(false, true, Acquire, Relaxed).is_ok()
    }

    fn try_lock_weak(&self) -> bool {
        self.compare_exchange_weak(false, true, Acquire, Relaxed).is_ok()
    }

    fn lock_wait<W: Wait>(&self) {
        // Block the thread with a relaxed loop until the load returns `false`,
        // indicating that the lock was handed off to the current thread.
        let mut wait = W::default();
        while self.load(Relaxed) {
            wait.relax();
        }
    }

    fn is_locked(&self) -> bool {
        self.load(Relaxed)
    }

    fn notify(&self) {
        self.store(false, Release);
    }
}
