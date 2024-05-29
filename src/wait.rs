use core::marker::PhantomData;
use core::sync::atomic::Ordering::{Acquire, Relaxed, Release};

use crate::cfg::atomic::AtomicBool;
use crate::relax::Relax;

/// A `Waiter` is some arbitrary data type used by a lock implementation to
/// manage the state of the lock.
///
/// The `no_std` implementations (eg `raw` and `barging`) can simply use a
/// `AtomicBool` to manage state. The parking variants thought, need platform
/// specific data types. We are currently using the `atomic_wait` crate for
/// easy parking integration. It uses `AtomicU32` as the data type for all
/// major platforms.
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

/// The waiting policy that should be applied while lock state has not reached
/// some target state.
pub trait Wait: Default {
    /// The relax operation that should be applied during spin loops.
    type Relax: Relax;

    /// Wheter or not should the `relax` or `parking` operation be executed
    /// at this time.
    ///
    /// Returning `true` means we are not ready yet to run the operation, there
    /// is some other event that should occur first. Otherwise the operation
    /// must be executed.
    fn should_wait(&self) -> bool;

    /// Executes the relax operation inside a waiting loop and also updates
    /// any inner state required by the policy.
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
