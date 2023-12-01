#![allow(clippy::needless_pass_by_value)]
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
pub(crate) unsafe trait Guard<'a, T: ?Sized + 'a> {
    /// The target guard type. Could be `Self` or a wrapped guard type
    /// that `Self` can refer to.
    type Guard: Guard<'a, T>;

    /// Get a Loom immutable pointer bounded by this guard lifetime.
    fn deref(&'a self) -> GuardDeref<'a, T, Self::Guard>;

    /// Get a Loom mutable pointer bounded by this guard lifetime.
    fn deref_mut(&'a self) -> GuardDerefMut<'a, T, Self::Guard>;
}

/// A Loom immutable pointer borrowed from a guard instance.
pub(crate) struct GuardDeref<'a, T: ?Sized + 'a, G: Guard<'a, T>> {
    ptr: ConstPtr<T>,
    marker: PhantomData<&'a G>,
}

impl<'a, T: ?Sized + 'a, G: Guard<'a, T>> GuardDeref<'a, T, G> {
    pub(crate) const fn new(ptr: ConstPtr<T>) -> Self {
        Self { ptr, marker: PhantomData }
    }
}

impl<'a, T: ?Sized + 'a, G: Guard<'a, T>> Deref for GuardDeref<'a, T, G> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        // SAFETY: Our lifetime is bounded by the guard borrow.
        unsafe { self.ptr.deref() }
    }
}

/// A Loom mutable pointer borrowed from a guard instance.
pub(crate) struct GuardDerefMut<'a, T: ?Sized + 'a, G: Guard<'a, T>> {
    ptr: MutPtr<T>,
    marker: PhantomData<&'a mut G>,
}

impl<'a, T: ?Sized + 'a, G: Guard<'a, T>> GuardDerefMut<'a, T, G> {
    pub(crate) fn new(ptr: MutPtr<T>) -> Self {
        Self { ptr, marker: PhantomData }
    }
}

impl<'a, T: ?Sized + 'a, G: Guard<'a, T>> Deref for GuardDerefMut<'a, T, G> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        // SAFETY: Our lifetime is bounded by the guard's borrow.
        unsafe { self.ptr.deref() }
    }
}

impl<'a, T: ?Sized + 'a, G: Guard<'a, T>> DerefMut for GuardDerefMut<'a, T, G> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        // SAFETY: Our lifetime is bounded by the guard's borrow.
        unsafe { self.ptr.deref() }
    }
}

/// A trait for lock types that can run closures against the guard.
//
// It would be nice to use GATs here but unfortunately we've hit a known limitation,
// so currently we define loom models for each MCS lock implementation.
// link: https://blog.rust-lang.org/2022/10/28/gats-stabilization.html#the-borrow-checker-isnt-perfect-and-it-shows
#[allow(unused)]
#[rustfmt::skip]
pub(crate) trait LockWith<T: ?Sized> {
    type Guard<'a>: Guard<'a, T> where T: 'a, Self: 'a;

    /// Creates a new mutex in an unlocked state ready for use.
    fn new(value: T) -> Self where T: Sized;

    // Attempts to acquire this lock and then runs the closure against its
    // guard.
    fn try_lock_with<F, R>(&self, f: F) -> R
    where
        F: FnOnce(Option<Self::Guard<'_>>) -> R;

    /// Acquires a mutex and then runs the closure against its guard.
    fn lock_with<F, R>(&self, f: F) -> R
    where
        F: FnOnce(Self::Guard<'_>) -> R;
}

/// Increments a shared i32 value.
#[allow(unused_variables)]
fn inc_std<L: LockWith<i32>>(lock: StdArc<L>) {
    // TODO: This does not compile on today's GAT, it hits some limitations
    // with borrow checker, see link above.
    // lock.lock_with(|g: L::Guard<'_>| *g.deref_mut() += 1);
    todo!();
}

/// Increments a shared i32 value.
#[allow(unused_variables)]
fn inc_loom<L: LockWith<i32>>(lock: LoomArc<L>) {
    // TODO: This does not compile on today's GAT, it hits some limitations
    // with borrow checker, see link above.
    // lock.lock_with(|g: L::Guard<'_>| *g.deref_mut() += 1);
    todo!();
}

/// Get the shared i32 value.
#[allow(unused_variables)]
fn get_loom<L: LockWith<i32>>(lock: LoomArc<L>) -> i32 {
    // TODO: This does not compile on today's GAT, it hits some limitations
    // with borrow checker, see link above.
    // lock.lock_with(|g: L::Guard<'_>| *g.deref())
    todo!();
}

#[allow(unused)]
pub(crate) fn threads_join<L: LockWith<i32> + 'static>() {
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
pub(crate) fn threads_fork<L: LockWith<i32> + 'static>() {
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
