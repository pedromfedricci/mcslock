use crate::lock::{Lock, Wait};
use crate::parking::park::Park;
use crate::relax::Relax;

#[cfg(not(all(loom, test)))]
pub(super) use common::Parker;

#[cfg(all(loom, test))]
pub(super) use loom::Parker;

/// A trait the specifies the contract of use for Parker implementations.
///
/// Currently, this crate leverages `atomic_wait`'s API for parking purposes,
/// that provides unified, cross platform wait and wake functionality. This
/// makes implementation simpler, at the cost of loosing platform specific
/// features. Should we choose to integrate with system's interfaces in the
/// future, each Parker implementation should follow this same contract.
pub trait ParkerT {
    /// Creates a new locked `Parker` instance.
    ///
    /// It's expected for a implementing type to be compiler-time evaluable.
    #[cfg(not(all(loom, test)))]
    const LOCKED: Self;

    /// Creates a new unlocked `Parker` instance.
    ///
    /// It's expected for a implementing type to be compiler-time evaluable.
    #[cfg(not(all(loom, test)))]
    const UNLOCKED: Self;

    /// Creates a new locked `Parker` instance with Loom primitives (non-const).
    ///
    /// Loom primitives are not compiler-time evaluable.
    #[cfg(all(loom, test))]
    #[cfg(not(tarpaulin_include))]
    fn locked() -> Self;

    /// Creates a new unlocked `Parker` instance with Loom primitives (non-const).
    ///
    /// Loom primitives are not compiler-time evaluable.
    #[cfg(all(loom, test))]
    #[cfg(not(tarpaulin_include))]
    fn unlocked() -> Self;

    /// Returns `true` if the lock is currently held.
    ///
    /// This function does not guarantee strong ordering, only atomicity.
    fn is_locked_relaxed(&self) -> bool;

    /// Tries to lock this mutex with acquire load.
    ///
    /// Returns `true` if successfully moved from unlocked state to locked
    /// state, `false` otherwise.
    fn try_lock_acquire(&self) -> bool;

    /// Tries to lock this mutex with acquire load and weak exchange.
    ///
    /// Returns `true` if successfully moved from unlocked state to locked
    /// state, `false` otherwise.
    fn try_lock_acquire_weak(&self) -> bool;

    /// Blocks unless or until the current thread's token is made availiable.
    ///
    /// Implementors of this function are expected to call the platform's
    /// specific APIs for thread parking and to also implement a mechanism
    /// to safeguard agains spurious wake-ups if they are possible. That is,
    /// this function should only unblock once a corresponding unpark call has
    /// been issued to this parked thread.
    fn park_loop_relaxed(&self);

    /// Atomically makes the handle’s token available if it is not already.
    ///
    /// Implementors of this function are expected to call the platform's
    /// specific API for thread unparking.
    fn unpark_release(&self);
}

/// Parks the current thread under the specified policy and `futex` compatible
/// atomic value.
///
/// If the current thread manages to acquire the lock within the limit of
/// attempts, then just return and unblock the thread, without ever requesting
/// the OS to put the thread to sleep.
///
/// Else, if the limit has been reached and the lock remains locked, then park
/// the thread and protect it from being awaken by spurious wakeups.
fn park_current_thread_relaxed<P: ParkerT, W: Wait>(parker: &P) {
    let mut parking_policy = W::parking_policy();
    while !parking_policy.park.should_park() {
        let true = parker.is_locked_relaxed() else { return };
        parking_policy.park.on_failure();
        parking_policy.relax.relax();
    }
    parker.park_loop_relaxed();
}

impl Lock for Parker {
    #[cfg(not(all(loom, test)))]
    #[allow(clippy::declare_interior_mutable_const)]
    const LOCKED: Self = ParkerT::LOCKED;

    #[cfg(not(all(loom, test)))]
    #[allow(clippy::declare_interior_mutable_const)]
    const UNLOCKED: Self = ParkerT::UNLOCKED;

    #[cfg(all(loom, test))]
    #[cfg(not(tarpaulin_include))]
    fn locked() -> Self {
        ParkerT::locked()
    }

    #[cfg(all(loom, test))]
    #[cfg(not(tarpaulin_include))]
    fn unlocked() -> Self {
        ParkerT::unlocked()
    }

    fn try_lock_acquire(&self) -> bool {
        ParkerT::try_lock_acquire(self)
    }

    fn try_lock_acquire_weak(&self) -> bool {
        ParkerT::try_lock_acquire_weak(self)
    }

    fn wait_lock_relaxed<W: Wait>(&self) {
        park_current_thread_relaxed::<Self, W>(self);
    }

    fn is_locked_relaxed(&self) -> bool {
        ParkerT::is_locked_relaxed(self)
    }

    fn notify_release(&self) {
        ParkerT::unpark_release(self);
    }
}

#[cfg(not(all(loom, test)))]
mod common {
    use core::ptr;
    use core::sync::atomic::AtomicU32;
    use core::sync::atomic::Ordering::{Acquire, Relaxed, Release};

    use super::ParkerT;

    #[derive(Debug)]
    pub struct Parker {
        state: AtomicU32,
    }

    const UNLOCKED: u32 = 0;
    const LOCKED: u32 = 1;

    impl ParkerT for Parker {
        #[allow(clippy::declare_interior_mutable_const)]
        const LOCKED: Self = {
            let state = AtomicU32::new(LOCKED);
            Self { state }
        };

        #[allow(clippy::declare_interior_mutable_const)]
        const UNLOCKED: Self = {
            let state = AtomicU32::new(UNLOCKED);
            Self { state }
        };

        fn try_lock_acquire(&self) -> bool {
            self.state.compare_exchange(UNLOCKED, LOCKED, Acquire, Relaxed).is_ok()
        }

        fn try_lock_acquire_weak(&self) -> bool {
            self.state.compare_exchange_weak(UNLOCKED, LOCKED, Acquire, Relaxed).is_ok()
        }

        fn is_locked_relaxed(&self) -> bool {
            self.state.load(Relaxed) == LOCKED
        }

        fn park_loop_relaxed(&self) {
            while self.state.load(Relaxed) == LOCKED {
                atomic_wait::wait(&self.state, LOCKED);
            }
        }

        fn unpark_release(&self) {
            let state = &self.state;
            // TODO: 1.82.0 supports native syntax:
            // let ptr = &raw const self.state;
            let ptr = ptr::addr_of!(*state);
            state.store(UNLOCKED, Release);
            atomic_wait::wake_one(ptr);
        }
    }
}

#[cfg(all(loom, test))]
#[cfg(not(tarpaulin_include))]
mod loom {
    use core::sync::atomic::Ordering::{Acquire, Relaxed, Release};

    use loom::sync::atomic::AtomicBool;
    use loom::thread;

    use super::ParkerT;

    #[derive(Debug)]
    pub struct Parker {
        locked: AtomicBool,
    }

    const UNLOCKED: bool = false;
    const LOCKED: bool = true;

    impl ParkerT for Parker {
        fn locked() -> Self {
            let locked = AtomicBool::new(LOCKED);
            Self { locked }
        }

        fn unlocked() -> Self {
            let locked = AtomicBool::new(UNLOCKED);
            Self { locked }
        }

        fn try_lock_acquire(&self) -> bool {
            self.locked.compare_exchange(UNLOCKED, LOCKED, Acquire, Relaxed).is_ok()
        }

        fn try_lock_acquire_weak(&self) -> bool {
            self.locked.compare_exchange_weak(UNLOCKED, LOCKED, Acquire, Relaxed).is_ok()
        }

        fn is_locked_relaxed(&self) -> bool {
            self.locked.load(Relaxed) == LOCKED
        }

        fn park_loop_relaxed(&self) {
            while self.locked.load(Relaxed) == LOCKED {
                thread::yield_now();
            }
        }

        fn unpark_release(&self) {
            self.locked.store(UNLOCKED, Release);
            thread::yield_now();
        }
    }
}
