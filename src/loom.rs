#[cfg(feature = "barging")]
pub use guard::{Guard, GuardDeref, GuardDerefMut};

#[cfg(feature = "barging")]
mod guard {
    use core::marker::PhantomData;
    use core::ops::{Deref, DerefMut};

    use loom::cell::{ConstPtr, MutPtr, UnsafeCell};

    /// A trait for guard types that protect the access to the underlying data
    /// behind Loom's [`UnsafeCell`].
    ///
    /// # Safety
    ///
    /// Must guarantee that an instance of the guard is the only access point
    /// to the underlying data through all its lifetime.
    pub unsafe trait Guard: Sized {
        /// The target type after dereferencing [`GuardDeref`] or [`GuardDerefMut`].
        type Target: ?Sized;

        /// Returns a shared reference to the underlying [`UnsafeCell`].
        fn get(&self) -> &UnsafeCell<Self::Target>;

        /// Get a Loom immutable pointer bounded by this guard lifetime.
        fn get_ref(&self) -> GuardDeref<'_, Self> {
            GuardDeref::new(self)
        }

        /// Get a Loom mutable pointer bounded by this guard lifetime.
        fn get_mut(&mut self) -> GuardDerefMut<'_, Self> {
            GuardDerefMut::new(self)
        }
    }

    /// A Loom immutable pointer borrowed from a guard instance.
    pub struct GuardDeref<'a, G: Guard> {
        ptr: ConstPtr<G::Target>,
        marker: PhantomData<(&'a G::Target, &'a G)>,
    }

    impl<G: Guard> GuardDeref<'_, G> {
        fn new(guard: &G) -> Self {
            let ptr = guard.get().get();
            Self { ptr, marker: PhantomData }
        }
    }

    impl<G: Guard> Deref for GuardDeref<'_, G> {
        type Target = G::Target;

        fn deref(&self) -> &Self::Target {
            // SAFETY: Our lifetime is bounded by the guard borrow.
            unsafe { self.ptr.deref() }
        }
    }

    /// A Loom mutable pointer borrowed from a guard instance.
    pub struct GuardDerefMut<'a, G: Guard> {
        ptr: MutPtr<G::Target>,
        marker: PhantomData<(&'a mut G::Target, &'a mut G)>,
    }

    impl<G: Guard> GuardDerefMut<'_, G> {
        #[allow(clippy::needless_pass_by_ref_mut)]
        fn new(guard: &mut G) -> Self {
            let ptr = guard.get().get_mut();
            Self { ptr, marker: PhantomData }
        }
    }

    impl<G: Guard> Deref for GuardDerefMut<'_, G> {
        type Target = G::Target;

        fn deref(&self) -> &Self::Target {
            // SAFETY: Our lifetime is bounded by the guard borrow.
            unsafe { self.ptr.deref() }
        }
    }

    impl<G: Guard> DerefMut for GuardDerefMut<'_, G> {
        fn deref_mut(&mut self) -> &mut Self::Target {
            // SAFETY: Our lifetime is bounded by the guard borrow.
            unsafe { self.ptr.deref() }
        }
    }
}

pub mod models {
    use core::array;

    use loom::sync::Arc;
    use loom::{model, thread};

    use crate::test::{AsDeref, AsDerefMut, LockThen, TryLockThen};

    type Int = usize;
    // TODO: Three or more threads make lock models run for too long. It would
    // be nice to run a lock model with at least three threads because that
    // would cover a queue with head, tail and at least one more queue node
    // instead of a queue with just head and tail.
    const LOCKS: Int = 2;
    const TRY_LOCKS: Int = 3;

    /// Increments a shared integer.
    fn inc<L: LockThen<Target = Int>>(lock: &Arc<L>) {
        lock.lock_then(|mut data| *data.as_deref_mut() += 1);
    }

    /// Tries to increment a shared integer.
    fn try_inc<L: TryLockThen<Target = Int>>(lock: &Arc<L>) {
        lock.try_lock_then(|opt| opt.map(|mut data| *data.as_deref_mut() += 1));
    }

    /// Get the shared integer.
    fn get<L: LockThen<Target = Int>>(lock: &Arc<L>) -> Int {
        lock.lock_then(|data| *data.as_deref())
    }

    /// Evaluates that concurrent `try_lock` calls will serialize all mutations
    /// against the shared data, therefore no data races.
    pub fn try_lock_join<L: TryLockThen<Target = Int> + 'static>() {
        model(|| {
            const RUNS: Int = TRY_LOCKS;
            let lock = Arc::new(L::new(0));
            let handles: [_; RUNS] = array::from_fn(|_| {
                let lock = Arc::clone(&lock);
                thread::spawn(move || try_inc(&lock))
            });
            for handle in handles {
                handle.join().unwrap();
            }
            let value = get(&lock);
            assert!((1..=RUNS).contains(&value));
        });
    }

    /// Evaluates that concurrent `lock` calls will serialize all mutations
    /// against the shared data, therefore no data races.
    pub fn lock_join<L: LockThen<Target = Int> + 'static>() {
        model(|| {
            const RUNS: Int = LOCKS;
            let lock = Arc::new(L::new(0));
            let handles: [_; RUNS] = array::from_fn(|_| {
                let lock = Arc::clone(&lock);
                thread::spawn(move || inc(&lock))
            });
            for handle in handles {
                handle.join().unwrap();
            }
            let value = get(&lock);
            assert_eq!(RUNS, value);
        });
    }

    /// Evaluates that concurrent `lock` and `try_lock` calls will serialize
    /// all mutations against the shared data, therefore no data races.
    pub fn mixed_lock_join<L: TryLockThen<Target = Int> + 'static>() {
        model(|| {
            const RUNS: Int = LOCKS;
            let lock = Arc::new(L::new(0));
            let handles: [_; RUNS] = array::from_fn(|run| {
                let lock = Arc::clone(&lock);
                let f = if run % 2 == 0 { inc } else { try_inc };
                thread::spawn(move || f(&lock))
            });
            for handle in handles {
                handle.join().unwrap();
            }
            let value = get(&lock);
            assert!((1..=RUNS).contains(&value));
        });
    }
}
