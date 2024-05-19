use core::fmt::{self, Debug, Display, Formatter};
use core::marker::PhantomData;
use core::mem::MaybeUninit;
use core::ptr;
use core::sync::atomic::Ordering::{AcqRel, Acquire, Relaxed, Release};

use crate::cfg::atomic::{fence, AtomicPtr};
use crate::cfg::cell::{UnsafeCell, WithUnchecked};
use crate::wait::{Wait, Waiter};

/// The inner definition of [`MutexNode`], which is known to be in a initialized
/// state.
#[derive(Debug)]
pub struct MutexNodeInit<W> {
    next: AtomicPtr<Self>,
    waiter: W,
}

impl<W> MutexNodeInit<W> {
    /// Returns a raw mutable pointer of this node.
    const fn as_ptr(&self) -> *mut Self {
        (self as *const Self).cast_mut()
    }
}

impl<W: Waiter<Self>> MutexNodeInit<W> {
    /// Crates a new `MutexNodeInit` instance.
    #[cfg(not(all(loom, test)))]
    pub const fn new() -> Self {
        let next = AtomicPtr::new(ptr::null_mut());
        let waiter = Waiter::NEW;
        Self { next, waiter }
    }

    /// Creates a new Loom based `MutexNodeInit` instance (non-const).
    #[cfg(all(loom, test))]
    #[cfg(not(tarpaulin_include))]
    pub fn new() -> Self {
        let next = AtomicPtr::new(ptr::null_mut());
        let waiter = Waiter::new();
        Self { next, waiter }
    }
}

impl<W: Waiter<Self>> Default for MutexNodeInit<W> {
    fn default() -> Self {
        Self::new()
    }
}

/// A locally-accessible record for forming the waiting queue.
///
/// The inner state is never dropped, only overwritten. This is desirable and
/// well suited for our use cases, since all `W` types used are only composed
/// of `no drop needed` types (eg. atomic types) with the exception of Loom's
/// `Thread`, which is only used for tests.
///
/// `W` must fail [`core::mem::needs_drop`] check, else `W` will leak.
#[derive(Debug)]
pub struct MutexNode<W> {
    inner: MaybeUninit<MutexNodeInit<W>>,
}

impl<W> MutexNode<W> {
    /// Creates new `MutexNode` instance.
    #[must_use]
    pub const fn new() -> Self {
        Self { inner: MaybeUninit::uninit() }
    }
}

impl<W: Waiter<MutexNodeInit<W>>> MutexNode<W> {
    /// Initializes this node's inner state, returning an exclusive reference
    /// pointing to it.
    fn initialize(&mut self) -> &mut MutexNodeInit<W> {
        self.inner.write(MutexNodeInit::new())
    }
}

impl<W> Default for MutexNode<W> {
    fn default() -> Self {
        Self::new()
    }
}

/// A mutual exclusion primitive implementing the MCS lock protocol, useful for
/// protecting shared data.
pub struct Mutex<T: ?Sized, W, P> {
    tail: AtomicPtr<MutexNodeInit<W>>,
    marker: PhantomData<P>,
    data: UnsafeCell<T>,
}

// Same unsafe impls as `std::sync::Mutex`.
unsafe impl<T: ?Sized + Send, W, P> Send for Mutex<T, W, P> {}
unsafe impl<T: ?Sized + Send, W, P> Sync for Mutex<T, W, P> {}

impl<T, W, P> Mutex<T, W, P> {
    /// Creates a new mutex in an unlocked state ready for use.
    #[cfg(not(all(loom, test)))]
    pub const fn new(value: T) -> Self {
        let tail = AtomicPtr::new(ptr::null_mut());
        let data = UnsafeCell::new(value);
        Self { tail, data, marker: PhantomData }
    }

    /// Creates a new unlocked mutex with Loom primitives (non-const).
    #[cfg(all(loom, test))]
    #[cfg(not(tarpaulin_include))]
    pub fn new(value: T) -> Self {
        let tail = AtomicPtr::new(ptr::null_mut());
        let data = UnsafeCell::new(value);
        Self { tail, data, marker: PhantomData }
    }

    /// Consumes this mutex, returning the underlying data.
    pub fn into_inner(self) -> T {
        self.data.into_inner()
    }
}

impl<T: ?Sized, W: Waiter<MutexNodeInit<W>>, P: Wait> Mutex<T, W, P> {
    /// Attempts to acquire this mutex without blocking the thread.
    pub fn try_lock<'a>(&'a self, node: &'a mut MutexNode<W>) -> Option<MutexGuard<'a, T, W, P>> {
        let node = node.initialize();
        self.tail
            .compare_exchange(ptr::null_mut(), node.as_ptr(), AcqRel, Relaxed)
            .map(|_| MutexGuard::new(self, node))
            .ok()
    }

    /// Acquires this mutex, blocking the current thread until it is able to do so.
    pub fn lock<'a>(&'a self, node: &'a mut MutexNode<W>) -> MutexGuard<'a, T, W, P> {
        let node = node.initialize();
        let pred = self.tail.swap(node.as_ptr(), AcqRel);
        // If we have a predecessor, complete the link so it will notify us.
        if !pred.is_null() {
            // SAFETY: Already verified that predecessor is not null.
            unsafe { &*pred }.next.store(node.as_ptr(), Release);
            // Acquire this mutex, applying some waiting policy.
            node.waiter.lock_wait::<P>();
            fence(Acquire);
        }
        MutexGuard::new(self, node)
    }

    /// Unlocks this mutex. If there is a successor node in the queue, the lock
    /// is passed directly to them.
    pub fn unlock(&self, node: &MutexNodeInit<W>) {
        let mut next = node.next.load(Relaxed);
        // If we don't have a known successor currently,
        if next.is_null() {
            // and we are the tail, then dequeue and free the lock.
            let false = self.try_unlock(node.as_ptr()) else { return };
            // But if we are not the tail, then we have a pending successor. We
            // must wait for them to finish linking with us.
            next = W::unlock_relax::<P::Relax>(&node.next);
        }
        // Notify our successor that they hold the lock.
        fence(Acquire);
        // SAFETY: We already verified that our successor is not null.
        unsafe { &*next }.waiter.notify();
    }
}

impl<T: ?Sized, W, P> Mutex<T, W, P> {
    /// Returns `true` if the lock is currently held.
    ///
    /// This function does not guarantee strong ordering, only atomicity.
    pub fn is_locked(&self) -> bool {
        !self.tail.load(Relaxed).is_null()
    }

    /// Returns a mutable reference to the underlying data.
    #[cfg(not(all(loom, test)))]
    pub fn get_mut(&mut self) -> &mut T {
        // SAFETY: We hold exclusive access to the Mutex data.
        unsafe { &mut *self.data.get() }
    }

    /// Unlocks the lock if the candidate node is the queue's tail.
    fn try_unlock(&self, node: *mut MutexNodeInit<W>) -> bool {
        self.tail.compare_exchange(node, ptr::null_mut(), Release, Relaxed).is_ok()
    }
}

impl<T: ?Sized + Debug, W: Waiter<MutexNodeInit<W>>, P: Wait> Debug for Mutex<T, W, P> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let mut node = MutexNode::new();
        let mut d = f.debug_struct("Mutex");
        match self.try_lock(&mut node) {
            Some(guard) => guard.with(|data| d.field("data", &data)),
            None => d.field("data", &format_args!("<locked>")),
        };
        d.finish()
    }
}

/// An RAII implementation of a "scoped lock" of a mutex. When this structure is
/// dropped (falls out of scope), the lock will be unlocked.
#[must_use = "if unused the Mutex will immediately unlock"]
pub struct MutexGuard<'a, T: ?Sized, W: Waiter<MutexNodeInit<W>>, P: Wait> {
    lock: &'a Mutex<T, W, P>,
    node: &'a MutexNodeInit<W>,
}

// `std::sync::MutexGuard` is not Send for pthread compatibility, but this
// implementation is safe to be Send.
unsafe impl<T: ?Sized + Send, W: Waiter<MutexNodeInit<W>>, P: Wait> Send
    for MutexGuard<'_, T, W, P>
{
}

// Same unsafe Sync impl as `std::sync::MutexGuard`.
unsafe impl<T: ?Sized + Sync, W: Waiter<MutexNodeInit<W>>, P: Wait> Sync
    for MutexGuard<'_, T, W, P>
{
}

impl<'a, T: ?Sized, W: Waiter<MutexNodeInit<W>>, P: Wait> MutexGuard<'a, T, W, P> {
    /// Creates a new `MutexGuard` instance.
    const fn new(lock: &'a Mutex<T, W, P>, node: &'a MutexNodeInit<W>) -> Self {
        Self { lock, node }
    }

    /// Runs `f` against a shared reference pointing to the underlying data.
    fn with<F, Ret>(&self, f: F) -> Ret
    where
        F: FnOnce(&T) -> Ret,
    {
        // SAFETY: A guard instance holds the lock locked.
        unsafe { self.lock.data.with_unchecked(f) }
    }
}

impl<'a, T: ?Sized + Debug, W: Waiter<MutexNodeInit<W>>, P: Wait> Debug
    for MutexGuard<'a, T, W, P>
{
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        self.with(|data| data.fmt(f))
    }
}

impl<'a, T: ?Sized + Display, W: Waiter<MutexNodeInit<W>>, P: Wait> Display
    for MutexGuard<'a, T, W, P>
{
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        self.with(|data| data.fmt(f))
    }
}

#[cfg(not(all(loom, test)))]
impl<'a, T: ?Sized, W: Waiter<MutexNodeInit<W>>, P: Wait> core::ops::Deref
    for MutexGuard<'a, T, W, P>
{
    type Target = T;

    /// Dereferences the guard to access the underlying data.
    fn deref(&self) -> &T {
        // SAFETY: A guard instance holds the lock locked.
        unsafe { &*self.lock.data.get() }
    }
}

#[cfg(not(all(loom, test)))]
impl<'a, T: ?Sized, W: Waiter<MutexNodeInit<W>>, P: Wait> core::ops::DerefMut
    for MutexGuard<'a, T, W, P>
{
    /// Mutably dereferences the guard to access the underlying data.
    fn deref_mut(&mut self) -> &mut T {
        // SAFETY: A guard instance holds the lock locked.
        unsafe { &mut *self.lock.data.get() }
    }
}

impl<'a, T: ?Sized, W: Waiter<MutexNodeInit<W>>, P: Wait> Drop for MutexGuard<'a, T, W, P> {
    fn drop(&mut self) {
        self.lock.unlock(self.node);
    }
}

/// SAFETY: A guard instance hold the lock locked, with exclusive access to the
/// underlying data.
#[cfg(all(loom, test))]
#[cfg(not(tarpaulin_include))]
unsafe impl<T: ?Sized, W: Waiter<MutexNodeInit<W>>, P: Wait> crate::loom::Guard
    for MutexGuard<'_, T, W, P>
{
    type Target = T;

    fn get(&self) -> &loom::cell::UnsafeCell<Self::Target> {
        &self.lock.data
    }
}
