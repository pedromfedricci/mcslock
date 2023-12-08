use core::marker::PhantomData;
use core::ops::{Deref, DerefMut};
use std::sync::Arc as StdArc;

use loom::cell::{ConstPtr, MutPtr, UnsafeCell};
use loom::sync::Arc as LoomArc;
use loom::{model, thread};

/// A trait for guard types that hold exclusive access to the underlying data
/// behind Loom's `UnsafeCell`.
///
/// # Safety
///
/// Must guarantee that an instance of the guard holds exclusive access to its
/// underlying data through all its lifetime.
pub unsafe trait GetUnsafeCell<T: ?Sized> {
    fn get(&self) -> &UnsafeCell<T>;
}

/// A trait for guard types that return `GuardDeref` and `GuardDerefMut`.
pub trait Guard<T: ?Sized>: GetUnsafeCell<T> + Sized {
    /// Get a Loom immutable pointer bounded by this guard lifetime.
    fn deref(&self) -> GuardDeref<'_, T, Self> {
        GuardDeref::new(self.get())
    }

    /// Get a Loom mutable pointer bounded by this guard lifetime.
    fn deref_mut(&self) -> GuardDerefMut<'_, T, Self> {
        GuardDerefMut::new(self.get())
    }
}

// Implements `Guard` for all types that implement `GetUnsafeCell`.
impl<T: ?Sized, U: GetUnsafeCell<T>> Guard<T> for U {}

/// A Loom immutable pointer borrowed from a guard instance.
pub struct GuardDeref<'a, T: ?Sized + 'a, G: Guard<T>> {
    ptr: ConstPtr<T>,
    marker: PhantomData<&'a G>,
}

impl<'a, T: ?Sized, G: Guard<T>> GuardDeref<'a, T, G> {
    fn new(data: &'a UnsafeCell<T>) -> Self {
        let ptr = data.get();
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
pub struct GuardDerefMut<'a, T: ?Sized + 'a, G: Guard<T>> {
    ptr: MutPtr<T>,
    marker: PhantomData<&'a G>,
}

impl<'a, T: ?Sized, G: Guard<T>> GuardDerefMut<'a, T, G> {
    fn new(data: &'a UnsafeCell<T>) -> Self {
        let ptr = data.get_mut();
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
fn threads_join<L: LockWith<u32> + 'static>() {
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
fn threads_fork<L: LockWith<u32> + 'static>() {
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
