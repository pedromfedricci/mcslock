use core::fmt::{self, Debug, Display, Formatter};
use core::ops::{Deref, DerefMut};

use super::park::Park;
use super::parker::Parker;
use crate::inner;

#[cfg(test)]
use crate::test::{LockNew, LockWith};

/// A locally-accessible record for forming the waiting queue.
#[repr(transparent)]
#[derive(Debug)]
pub struct MutexNode {
    inner: inner::MutexNode<Parker>,
}

impl MutexNode {
    /// Creates new `MutexNode` instance.
    #[must_use]
    #[inline(always)]
    pub const fn new() -> Self {
        Self { inner: inner::MutexNode::new() }
    }
}

#[cfg(not(tarpaulin_include))]
impl Deref for MutexNode {
    type Target = inner::MutexNode<Parker>;

    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}

impl DerefMut for MutexNode {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.inner
    }
}

#[cfg(not(tarpaulin_include))]
impl Default for MutexNode {
    #[inline(always)]
    fn default() -> Self {
        Self::new()
    }
}

/// A mutual exclusion primitive useful for protecting shared data.
pub struct Mutex<T: ?Sized, P> {
    pub(super) inner: inner::Mutex<T, Parker, P>,
}

// Same unsafe impls as `std::sync::Mutex`.
unsafe impl<T: ?Sized + Send, P> Send for Mutex<T, P> {}
unsafe impl<T: ?Sized + Send, P> Sync for Mutex<T, P> {}

impl<T, P> Mutex<T, P> {
    /// Creates a new mutex in an unlocked state ready for use.
    #[cfg(not(all(loom, test)))]
    #[inline]
    pub const fn new(value: T) -> Self {
        Self { inner: inner::Mutex::new(value) }
    }

    /// Creates a new unlocked mutex with Loom primitives (non-const).
    #[cfg(all(loom, test))]
    #[cfg(not(tarpaulin_include))]
    fn new(value: T) -> Self {
        Self { inner: inner::Mutex::new(value) }
    }

    /// TODO: Docs
    #[inline(always)]
    pub fn into_inner(self) -> T {
        self.inner.into_inner()
    }
}

impl<T: ?Sized, P: Park> Mutex<T, P> {
    /// Attempts to acquire this mutex without blocking the thread.
    #[inline]
    pub fn try_lock<'a>(&'a self, node: &'a mut MutexNode) -> Option<MutexGuard<'a, T, P>> {
        self.inner.try_lock(&mut node.inner).map(From::from)
    }

    /// Attempts to acquire this mutex and then runs a closure against its guard.
    #[inline]
    pub fn try_lock_with<F, Ret>(&self, f: F) -> Ret
    where
        F: FnOnce(Option<MutexGuard<'_, T, P>>) -> Ret,
    {
        let mut node = MutexNode::new();
        f(self.try_lock(&mut node))
    }

    /// Acquires this mutex, blocking the current thread until it is able to do so.
    #[inline]
    pub fn lock<'a>(&'a self, node: &'a mut MutexNode) -> MutexGuard<'a, T, P> {
        self.inner.lock(&mut node.inner).into()
    }

    /// Acquires this mutex and then runs the closure against its guard.
    #[inline]
    pub fn lock_with<F, Ret>(&self, f: F) -> Ret
    where
        F: FnOnce(MutexGuard<'_, T, P>) -> Ret,
    {
        let mut node = MutexNode::new();
        f(self.lock(&mut node))
    }
}

impl<T: ?Sized, P> Mutex<T, P> {
    /// Returns `true` if the lock is currently held.
    #[inline]
    pub fn is_locked(&self) -> bool {
        self.inner.is_locked()
    }

    /// Returns a mutable reference to the underlying data.
    #[cfg(not(all(loom, test)))]
    #[inline(always)]
    pub fn get_mut(&mut self) -> &mut T {
        self.inner.get_mut()
    }
}

impl<T: ?Sized + Default, P> Default for Mutex<T, P> {
    /// Creates a `Mutex<T, R>`, with the `Default` value for `T`.
    #[inline]
    fn default() -> Self {
        Self::new(Default::default())
    }
}

impl<T, R> From<T> for Mutex<T, R> {
    /// Creates a `Mutex<T, R>` from a instance of `T`.
    #[inline]
    fn from(data: T) -> Self {
        Self::new(data)
    }
}

impl<T: ?Sized + Debug, P: Park> Debug for Mutex<T, P> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        self.inner.fmt(f)
    }
}

#[cfg(test)]
impl<T: ?Sized, P> LockNew for Mutex<T, P> {
    type Target = T;

    fn new(value: Self::Target) -> Self
    where
        Self::Target: Sized,
    {
        Self::new(value)
    }
}

#[cfg(test)]
impl<T: ?Sized, P: Park> LockWith for Mutex<T, P> {
    type Guard<'a> = MutexGuard<'a, Self::Target, P>
    where
        Self: 'a,
        Self::Target: 'a;

    fn try_lock_with<F, Ret>(&self, f: F) -> Ret
    where
        F: FnOnce(Option<MutexGuard<'_, T, P>>) -> Ret,
    {
        self.try_lock_with(f)
    }

    fn lock_with<F, Ret>(&self, f: F) -> Ret
    where
        F: FnOnce(MutexGuard<'_, T, P>) -> Ret,
    {
        self.lock_with(f)
    }

    fn is_locked(&self) -> bool {
        self.is_locked()
    }
}

#[cfg(all(not(loom), test))]
impl<T: ?Sized, P> crate::test::LockData for Mutex<T, P> {
    fn into_inner(self) -> Self::Target
    where
        Self::Target: Sized,
    {
        self.into_inner()
    }

    fn get_mut(&mut self) -> &mut Self::Target {
        self.get_mut()
    }
}

/// An RAII implementation of a "scoped lock" of a mutex. When this structure is
/// dropped (falls out of scope), the lock will be unlocked.
#[must_use = "if unused the Mutex will immediately unlock"]
pub struct MutexGuard<'a, T: ?Sized, P: Park> {
    inner: inner::MutexGuard<'a, T, Parker, P>,
}

// `std::sync::MutexGuard` is not Send for pthread compatibility, but this
// implementation is safe to be Send.
unsafe impl<T: ?Sized + Send, P: Park> Send for MutexGuard<'_, T, P> {}
// Same unsafe Sync impl as `std::sync::MutexGuard`.
unsafe impl<T: ?Sized + Sync, P: Park> Sync for MutexGuard<'_, T, P> {}

impl<'a, T: ?Sized, P: Park> From<inner::MutexGuard<'a, T, Parker, P>> for MutexGuard<'a, T, P> {
    fn from(inner: inner::MutexGuard<'a, T, Parker, P>) -> Self {
        Self { inner }
    }
}

impl<'a, T: ?Sized + Debug, P: Park> Debug for MutexGuard<'a, T, P> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        self.inner.fmt(f)
    }
}

impl<'a, T: ?Sized + Display, P: Park> Display for MutexGuard<'a, T, P> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        self.inner.fmt(f)
    }
}

#[cfg(not(all(loom, test)))]
impl<'a, T: ?Sized, P: Park> Deref for MutexGuard<'a, T, P> {
    type Target = T;

    /// Dereferences the guard to access the underlying data.
    #[inline(always)]
    fn deref(&self) -> &T {
        &self.inner
    }
}

#[cfg(not(all(loom, test)))]
impl<'a, T: ?Sized, P: Park> DerefMut for MutexGuard<'a, T, P> {
    /// Mutably dereferences the guard to access the underlying data.
    #[inline(always)]
    fn deref_mut(&mut self) -> &mut T {
        &mut self.inner
    }
}

/// SAFETY: A guard instance hold the lock locked, with exclusive access to the
/// underlying data.
#[cfg(all(loom, test))]
#[cfg(not(tarpaulin_include))]
unsafe impl<T: ?Sized, P: Park> crate::loom::Guard for MutexGuard<'_, T, P> {
    type Target = T;

    fn get(&self) -> &loom::cell::UnsafeCell<Self::Target> {
        self.inner.get()
    }
}

#[cfg(all(not(loom), test))]
mod test {
    use crate::parking::immediate::Mutex;
    use crate::test::tests;

    #[test]
    fn node_waiter_drop_does_not_matter() {
        tests::node_waiter_drop_does_not_matter::<super::Parker>();
    }

    #[test]
    fn lots_and_lots_immediate_park() {
        use crate::parking::immediate::Mutex;
        tests::lots_and_lots::<Mutex<_>>();
    }

    #[test]
    fn lots_and_lots_yield_than_park() {
        use crate::parking::yields::Mutex;
        tests::lots_and_lots::<Mutex<_>>();
    }

    #[test]
    fn smoke() {
        tests::smoke::<Mutex<_>>();
    }

    #[test]
    fn test_guard_debug_display() {
        tests::test_guard_debug_display::<Mutex<_>>();
    }

    #[test]
    fn test_mutex_debug() {
        tests::test_mutex_debug::<Mutex<_>>();
    }

    #[test]
    fn test_mutex_from() {
        tests::test_mutex_from::<Mutex<_>>();
    }

    #[test]
    fn test_mutex_default() {
        tests::test_mutex_default::<Mutex<_>>();
    }

    #[test]
    fn test_try_lock() {
        tests::test_try_lock::<Mutex<_>>();
    }

    #[test]
    fn test_into_inner() {
        tests::test_into_inner::<Mutex<_>>();
    }

    #[test]
    fn test_into_inner_drop() {
        tests::test_into_inner_drop::<Mutex<_>>();
    }

    #[test]
    fn test_get_mut() {
        tests::test_get_mut::<Mutex<_>>();
    }

    #[test]
    fn test_lock_arc_nested() {
        tests::test_lock_arc_nested::<Mutex<_>, Mutex<_>>();
    }

    #[test]
    fn test_acquire_more_than_one_lock() {
        tests::test_acquire_more_than_one_lock::<Mutex<_>>();
    }

    #[test]
    fn test_lock_arc_access_in_unwind() {
        tests::test_lock_arc_access_in_unwind::<Mutex<_>>();
    }

    #[test]
    fn test_lock_unsized() {
        tests::test_lock_unsized::<Mutex<_>>();
    }
}

#[cfg(all(loom, test))]
mod model {
    use crate::loom::models;
    use crate::parking::{immediate, yields};

    #[test]
    fn try_lock_join_immediate_park() {
        models::try_lock_join::<immediate::Mutex<_>>();
    }

    #[test]
    fn lock_join_immediate_park() {
        models::lock_join::<immediate::Mutex<_>>();
    }

    #[test]
    fn mixed_lock_join_immediate_park() {
        models::mixed_lock_join::<immediate::Mutex<_>>();
    }

    #[test]
    fn try_lock_join_yield_than_park() {
        models::try_lock_join::<yields::Mutex<_>>();
    }

    #[test]
    fn lock_join_yield_than_park() {
        models::lock_join::<yields::Mutex<_>>();
    }

    #[test]
    fn mixed_lock_join_yield_than_park() {
        models::mixed_lock_join::<yields::Mutex<_>>();
    }
}
