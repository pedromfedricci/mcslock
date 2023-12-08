#![allow(clippy::redundant_pub_crate)]

use core::marker::PhantomData;
use core::ops::{Deref, DerefMut};
use std::sync::Arc as StdArc;

use loom::cell::{ConstPtr, MutPtr};
use loom::sync::Arc as LoomArc;
use loom::{model, thread};

/// A trait for guard types pointing to data backed by Loom's `UnsafeCell`.
///
/// # Safety
///
/// Must guarantee that an instance of the guard holds exclusive access to its
/// underlying data through all its lifetime.
#[rustfmt::skip]
pub(crate) unsafe trait Guard<T: ?Sized> {
    /// The target guard type. Could be `Self` or a wrapped guard type
    /// that `Self` can refer to.
    type Guard<'a>: Guard<T> where T: 'a, Self: 'a;

    /// Get a Loom immutable pointer bounded by this guard lifetime.
    fn deref(&self) -> GuardDeref<'_, T, Self::Guard<'_>>;

    /// Get a Loom mutable pointer bounded by this guard lifetime.
    fn deref_mut(&self) -> GuardDerefMut<'_, T, Self::Guard<'_>>;
}

/// A Loom immutable pointer borrowed from a guard instance.
pub(crate) struct GuardDeref<'a, T: ?Sized + 'a, G: Guard<T>> {
    ptr: ConstPtr<T>,
    marker: PhantomData<&'a G>,
}

impl<T: ?Sized, G: Guard<T>> GuardDeref<'_, T, G> {
    pub(crate) const fn new(ptr: ConstPtr<T>) -> Self {
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
pub(crate) struct GuardDerefMut<'a, T: ?Sized + 'a, G: Guard<T>> {
    ptr: MutPtr<T>,
    marker: PhantomData<&'a G>,
}

impl<T: ?Sized, G: Guard<T>> GuardDerefMut<'_, T, G> {
    pub(crate) const fn new(ptr: MutPtr<T>) -> Self {
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
pub(crate) trait LockWith<T: ?Sized>: Send + Sync + 'static {
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

/// Increments a shared u32 value.
fn inc_std<L: LockWith<u32>>(lock: StdArc<L>) {
    lock.lock_with(|g| g.deref_mut().wrapping_add(1));
}

/// Increments a shared u32 value.
fn inc_loom<L: LockWith<u32>>(lock: LoomArc<L>) {
    lock.lock_with(|guard| guard.deref_mut().wrapping_add(1));
}

/// Get the shared u32 value.
fn get_loom<L: LockWith<u32>>(lock: LoomArc<L>) -> u32 {
    lock.lock_with(|guard| *guard.deref())
}

#[allow(unused)]
pub(crate) fn threads_join<L: LockWith<u32>>() {
    use loom::sync::Arc;
    model(|| {
        let data = Arc::new(L::new(0));
        // 3 or more threads make this model run for too long.
        let runs @ core::ops::Range { end, .. } = 0..2;
        let handles = runs
            .into_iter()
            .map(|_| Arc::clone(&data))
            .map(|data| thread::spawn(move || inc_loom(data)))
            .collect::<Vec<_>>();
        for handle in handles {
            handle.join().unwrap();
        }
        assert_eq!(end, get_loom(data));
    });
}

#[allow(unused)]
pub(crate) fn threads_fork<L: LockWith<u32>>() {
    // Using std's Arc or else this model takes to long to run.
    use std::sync::Arc;
    model(|| {
        let data = Arc::new(L::new(0));
        // 4 or more threads make this model run for too long.
        for _ in 0..3 {
            let data = Arc::clone(&data);
            thread::spawn(move || inc_std(data));
        }
    });
}
