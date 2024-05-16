use core::sync::atomic::Ordering::{self, Acquire, Release};

use crate::{relax::Relax, wait::Waiter};

#[cfg(not(all(loom, test)))]
pub(super) use common::Parker;

#[cfg(all(loom, test))]
pub(super) use loom::Parker;

const PARK_ORDERING: Ordering = Acquire;
const UNPARK_ORDERING: Ordering = Release;

pub(super) trait ParkerT {
    #[cfg(not(all(loom, test)))]
    const NEW: Self;

    #[cfg(all(loom, test))]
    fn new() -> Self;

    fn is_locked(&self) -> bool;

    fn park_loop(&self);

    fn unpark(&self);
}

impl<T, P: ParkerT> Waiter<T> for P {
    #[cfg(not(all(loom, test)))]
    const NEW: Self = Self::NEW;

    #[cfg(all(loom, test))]
    fn new() -> Self {
        Self::new()
    }

    fn lock_wait<R: Relax>(&self) {
        let mut relax = R::default();
        while self.is_locked() {
            relax.relax();
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
