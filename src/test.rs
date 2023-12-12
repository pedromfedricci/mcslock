#[cfg(all(not(loom), test))]
pub use core::ops::DerefMut as Guard;

#[cfg(all(loom, test))]
pub use crate::loom::Guard;

/// A trait for lock types that can run closures against the guard.
pub trait LockWith {
    /// The resulting type after dereferencing.
    type Target: ?Sized;

    /// The guard type that holds exclusive access to the underlying data.
    type Guard<'a>: Guard<Target = Self::Target>
    where
        Self: 'a,
        Self::Target: 'a;

    /// Creates a new mutex in an unlocked state ready for use.
    fn new(value: Self::Target) -> Self
    where
        Self::Target: Sized;

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
