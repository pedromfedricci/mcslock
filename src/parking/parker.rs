use core::sync::atomic::Ordering::{self, Acquire, Release};

use crate::wait::{Wait, Waiter};

#[cfg(not(all(loom, test)))]
pub(super) use common::Parker;

#[cfg(all(loom, test))]
pub(super) use loom::Parker;

// We need the same exact park/unpark ordering relationship for both `common`
// and `loom`, else `loom` would not correctly represent our protocol's memory
// ordering.
//
/// Parking ordering.
const PARK_ORDERING: Ordering = Acquire;
/// Unparking ordering.
const UNPARK_ORDERING: Ordering = Release;

/// A trait the specifies the contract of use for Parker implementations.
///
/// Currently, this crate leverages `atomic_wait`'s API for parking purposes,
/// that provides unified, cross platform wait and wake functionality. This
/// makes implementation simpler, at the cost of loosing platform specific
/// features. Should we choose to integrate with system's interfaces in the
/// future, each Parker implementation should follow this same contract.
pub trait ParkerT {
    /// Creates a new Parker instance.
    ///
    /// It's expected for a implementing type to be compiler-time evaluable.
    #[cfg(not(all(loom, test)))]
    const NEW: Self;

    /// Creates a new Parker instance with Loom primitives (non-const).
    ///
    /// Loom primitives are not compiler-time evaluable.
    #[cfg(all(loom, test))]
    #[cfg(not(tarpaulin_include))]
    fn new() -> Self;

    /// Returns `true` if the lock is currently held.
    ///
    /// This function does not guarantee strong ordering, only atomicity.
    fn is_locked(&self) -> bool;

    /// Blocks unless or until the current thread's token is made availiable.
    ///
    /// Implementors of this function are expected to call the platform's
    /// specific APIs for thread parking and also to also implement a mechanism
    /// to safeguard agains spurious wake-ups if they are possible. That is,
    /// this function should only unblock once a corresponding unpark call has
    /// been issued to this parked thread.
    fn park_loop(&self);

    /// Atomically makes the handle’s token available if it is not already.
    ///
    /// Implementors of this function are expected to call the platform's
    /// specific API for thread unparking.
    fn unpark(&self);
}

impl<T> Waiter<T> for Parker {
    #[cfg(not(all(loom, test)))]
    #[allow(clippy::declare_interior_mutable_const)]
    const NEW: Self = ParkerT::NEW;

    #[cfg(all(loom, test))]
    #[cfg(not(tarpaulin_include))]
    fn new() -> Self {
        ParkerT::new()
    }

    fn lock_wait<W: Wait>(&self) {
        let mut wait = W::default();
        while wait.should_wait() {
            let true = self.is_locked() else { return };
            wait.relax();
        }
        self.park_loop();
    }

    fn notify(&self) {
        self.unpark();
    }
}

#[cfg(not(all(loom, test)))]
mod common {
    use core::ptr;
    use core::sync::atomic::AtomicU32;
    use core::sync::atomic::Ordering::Relaxed;

    use super::{ParkerT, PARK_ORDERING, UNPARK_ORDERING};

    #[derive(Debug)]
    pub struct Parker {
        state: AtomicU32,
    }

    const UNLOCKED: u32 = 0;
    const LOCKED: u32 = 1;

    impl ParkerT for Parker {
        #[allow(clippy::declare_interior_mutable_const)]
        const NEW: Self = {
            let state = AtomicU32::new(LOCKED);
            Self { state }
        };

        fn is_locked(&self) -> bool {
            self.state.load(Relaxed) == LOCKED
        }

        fn park_loop(&self) {
            while self.state.load(PARK_ORDERING) == LOCKED {
                atomic_wait::wait(&self.state, LOCKED);
            }
        }

        fn unpark(&self) {
            let state = &self.state;
            let ptr = ptr::addr_of!(*state);
            state.store(UNLOCKED, UNPARK_ORDERING);
            atomic_wait::wake_one(ptr);
        }
    }
}

#[cfg(all(loom, test))]
#[cfg(not(tarpaulin_include))]
mod loom {
    use core::sync::atomic::Ordering::Relaxed;

    use loom::sync::atomic::AtomicBool;
    use loom::thread::{self, Thread};

    use super::{ParkerT, PARK_ORDERING, UNPARK_ORDERING};

    #[derive(Debug)]
    pub struct Parker {
        locked: AtomicBool,
        thread: Thread,
    }

    const UNLOCKED: bool = false;
    const LOCKED: bool = true;

    impl ParkerT for Parker {
        fn new() -> Self {
            let locked = AtomicBool::new(LOCKED);
            let thread = thread::current();
            Self { locked, thread }
        }

        fn is_locked(&self) -> bool {
            self.locked.load(Relaxed) == LOCKED
        }

        fn park_loop(&self) {
            while self.locked.load(PARK_ORDERING) {
                thread::park();
            }
        }

        fn unpark(&self) {
            self.locked.store(UNLOCKED, UNPARK_ORDERING);
            self.thread.unpark();
        }
    }
}
