use core::marker::PhantomData;
use core::ops::{Deref, DerefMut};

use loom::cell::{ConstPtr, MutPtr, UnsafeCell};

/// A trait for guard types that hold exclusive access to the underlying data
/// behind Loom's [`UnsafeCell`].
///
/// # Safety
///
/// Must guarantee that an instance of the guard holds exclusive access to its
/// underlying data through all its lifetime.
pub unsafe trait Guard<T: ?Sized>: Sized {
    /// Get a shared reference from the [`UnsafeCell`] holding the data.
    fn get(&self) -> &UnsafeCell<T>;

    /// Get a Loom immutable pointer bounded by this guard lifetime.
    fn deref(&self) -> GuardDeref<'_, T, Self> {
        GuardDeref::new(self)
    }

    /// Get a Loom mutable pointer bounded by this guard lifetime.
    fn deref_mut(&self) -> GuardDerefMut<'_, T, Self> {
        GuardDerefMut::new(self)
    }
}

/// A Loom immutable pointer borrowed from a guard instance.
pub struct GuardDeref<'a, T: ?Sized, G: Guard<T>> {
    ptr: ConstPtr<T>,
    marker: PhantomData<&'a G>,
}

impl<T: ?Sized, G: Guard<T>> GuardDeref<'_, T, G> {
    fn new(guard: &G) -> Self {
        let ptr = guard.get().get();
        Self { ptr, marker: PhantomData }
    }
}

impl<T: ?Sized, G: Guard<T>> Deref for GuardDeref<'_, T, G> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        // SAFETY: Our lifetime is bounded by the guard borrow.
        unsafe { self.ptr.deref() }
    }
}

/// A Loom mutable pointer borrowed from a guard instance.
pub struct GuardDerefMut<'a, T: ?Sized, G: Guard<T>> {
    ptr: MutPtr<T>,
    marker: PhantomData<&'a G>,
}

impl<T: ?Sized, G: Guard<T>> GuardDerefMut<'_, T, G> {
    fn new(guard: &G) -> Self {
        let ptr = guard.get().get_mut();
        Self { ptr, marker: PhantomData }
    }
}

impl<T: ?Sized, G: Guard<T>> Deref for GuardDerefMut<'_, T, G> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        // SAFETY: Our lifetime is bounded by the guard borrow.
        unsafe { self.ptr.deref() }
    }
}

impl<T: ?Sized, G: Guard<T>> DerefMut for GuardDerefMut<'_, T, G> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        // SAFETY: Our lifetime is bounded by the guard borrow.
        unsafe { self.ptr.deref() }
    }
}

/// A trait for lock types that can run closures against the guard.
#[rustfmt::skip]
pub trait LockWith<T: ?Sized> {
    type Guard<'a>: Guard<T> where T: 'a, Self: 'a;

    /// Creates a new mutex in an unlocked state ready for use.
    fn new(value: T) -> Self where T: Sized;

    // Attempts to acquire this lock and then runs the closure against its
    // guard.
    fn try_lock_with<F, Ret>(&self, f: F) -> Ret
    where
        F: FnOnce(Option<Self::Guard<'_>>) -> Ret;

    /// Acquires a mutex and then runs the closure against its guard.
    fn lock_with<F, Ret>(&self, f: F) -> Ret
    where
        F: FnOnce(Self::Guard<'_>) -> Ret;
}

pub mod model {
    use std::ops::Range;

    use loom::sync::Arc;
    use loom::{model, thread};

    use super::{Guard, LockWith};

    type Int = u32;
    const RUN2: Range<Int> = Range { start: 0, end: 2 };
    const RUN3: Range<Int> = Range { start: 0, end: 3 };

    /// Increments a shared integer.
    fn inc<L: LockWith<Int>>(lock: &Arc<L>) {
        lock.lock_with(|guard| *guard.deref_mut() += 1);
    }

    /// Tries to increment a shared integer.
    fn try_inc<L: LockWith<Int>>(lock: &Arc<L>) {
        lock.try_lock_with(|opt| opt.map(|guard| *guard.deref_mut() += 1));
    }

    /// Get the shared integer.
    fn get<L: LockWith<Int>>(lock: &Arc<L>) -> Int {
        lock.lock_with(|guard| *guard.deref())
    }

    /// Evaluates that concurrent `try_lock` calls will serialize all mutations
    /// against the share data, therefore no data races.
    pub fn try_lock_join<L: LockWith<Int> + 'static>() {
        model(|| {
            let data = Arc::new(L::new(0));
            let runs @ Range { end, .. } = RUN3;
            let handles = runs
                .into_iter()
                .map(|_| Arc::clone(&data))
                .map(|data| thread::spawn(move || try_inc(&data)))
                .collect::<Vec<_>>();
            for handle in handles {
                handle.join().unwrap();
            }
            let data = get(&data);
            assert!(0 < data && data < end + 1);
        });
    }

    /// Evaluates that concurrent `lock` calls will serialize all mutations
    /// against the share data, therefore no data races.
    pub fn lock_join<L: LockWith<Int> + 'static>() {
        model(|| {
            let data = Arc::new(L::new(0));
            // TODO: Three or more threads make this model run for too long.
            // It would be nice to run a model with at least three thread
            // because that would cover a queue with head, tail and at least
            // one more queue node instead of just head and tail.
            let runs @ Range { end, .. } = RUN2;
            let handles = runs
                .into_iter()
                .map(|_| Arc::clone(&data))
                .map(|data| thread::spawn(move || inc(&data)))
                .collect::<Vec<_>>();
            for handle in handles {
                handle.join().unwrap();
            }
            assert_eq!(end, get(&data));
        });
    }

    /// Evaluates that concurrent `lock` and `try_lock` calls will serialize
    /// all mutations against the share data, therefore no data races.
    pub fn mixed_lock_join<L: LockWith<Int> + 'static>() {
        model(|| {
            let data = Arc::new(L::new(0));
            // TODO: Three or more threads make this model run for too long.
            // It would be nice to run a model with at least three thread
            // because that would cover a queue with head, tail and at least
            // one more queue node instead of just head and tail.
            let runs @ Range { end, .. } = RUN2;
            let handles = runs
                .into_iter()
                .map(|run| (Arc::clone(&data), run))
                .map(|(data, run)| {
                    let f = if run % 2 == 0 { inc } else { try_inc };
                    thread::spawn(move || f(&data))
                })
                .collect::<Vec<_>>();
            for handle in handles {
                handle.join().unwrap();
            }
            let data = get(&data);
            assert!(0 < data && data < end + 1);
        });
    }
}
