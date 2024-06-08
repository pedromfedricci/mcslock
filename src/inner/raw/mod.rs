use core::fmt::{self, Debug, Display, Formatter};
use core::marker::PhantomData;
use core::mem::MaybeUninit;
use core::ptr;
use core::sync::atomic::Ordering::{AcqRel, Acquire, Relaxed, Release};

use crate::cfg::atomic::{fence, AtomicPtr};
use crate::cfg::cell::{UnsafeCell, WithUnchecked};
use crate::lock::{Lock, Wait};
use crate::relax::Relax;

#[cfg(feature = "thread_local")]
mod thread_local;
#[cfg(feature = "thread_local")]
pub use thread_local::LocalMutexNode;

/// The inner definition of [`MutexNode`], which is known to be in a initialized
/// state.
#[derive(Debug)]
pub struct MutexNodeInit<L> {
    next: AtomicPtr<Self>,
    lock: L,
}

impl<L> MutexNodeInit<L> {
    /// Returns a raw mutable pointer of this node.
    const fn as_ptr(&self) -> *mut Self {
        (ptr::from_ref(self)).cast_mut()
    }
}

impl<L: Lock> MutexNodeInit<L> {
    /// Crates a new `MutexNodeInit` instance.
    #[cfg(not(all(loom, test)))]
    const fn new() -> Self {
        let next = AtomicPtr::new(ptr::null_mut());
        let lock = Lock::LOCKED;
        Self { next, lock }
    }

    /// Creates a new Loom based `MutexNodeInit` instance (non-const).
    #[cfg(all(loom, test))]
    #[cfg(not(tarpaulin_include))]
    fn new() -> Self {
        let next = AtomicPtr::new(ptr::null_mut());
        let lock = Lock::locked();
        Self { next, lock }
    }
}

#[cfg(not(tarpaulin_include))]
impl<L: Lock> Default for MutexNodeInit<L> {
    fn default() -> Self {
        Self::new()
    }
}

/// A locally-accessible record for forming the waiting queue.
///
/// The inner state is never dropped, only overwritten. This is desirable and
/// well suited for our use cases, since all `W` types used are only composed
/// of `no drop needed` types (eg. atomic types).
///
/// `W` must fail [`core::mem::needs_drop`] check, else `W` will leak.
#[derive(Debug)]
pub struct MutexNode<L> {
    inner: MaybeUninit<MutexNodeInit<L>>,
}

impl<L> MutexNode<L> {
    /// Creates new `MutexNode` instance.
    #[must_use]
    pub const fn new() -> Self {
        Self { inner: MaybeUninit::uninit() }
    }
}

impl<L: Lock> MutexNode<L> {
    /// Initializes this node's inner state, returning an exclusive reference
    /// pointing to it.
    fn initialize(&mut self) -> &mut MutexNodeInit<L> {
        self.inner.write(MutexNodeInit::new())
    }
}

#[cfg(not(tarpaulin_include))]
impl<L> Default for MutexNode<L> {
    fn default() -> Self {
        Self::new()
    }
}

/// A mutual exclusion primitive implementing the MCS lock protocol, useful for
/// protecting shared data.
pub struct Mutex<T: ?Sized, L, W> {
    tail: AtomicPtr<MutexNodeInit<L>>,
    marker: PhantomData<W>,
    data: UnsafeCell<T>,
}

// Same unsafe impls as `std::sync::Mutex`.
unsafe impl<T: ?Sized + Send, L, W> Send for Mutex<T, L, W> {}
unsafe impl<T: ?Sized + Send, L, W> Sync for Mutex<T, L, W> {}

impl<T, L, W> Mutex<T, L, W> {
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

impl<T: ?Sized, L: Lock, W: Wait> Mutex<T, L, W> {
    /// Attempts to acquire this mutex without blocking the thread.
    pub fn try_lock<'a>(&'a self, node: &'a mut MutexNode<L>) -> Option<MutexGuard<'a, T, L, W>> {
        let node = node.initialize();
        self.tail
            .compare_exchange(ptr::null_mut(), node.as_ptr(), AcqRel, Relaxed)
            .map(|_| MutexGuard::new(self, node))
            .ok()
    }

    /// Acquires this mutex, blocking the current thread until it is able to do so.
    pub fn lock<'a>(&'a self, node: &'a mut MutexNode<L>) -> MutexGuard<'a, T, L, W> {
        let node = node.initialize();
        let pred = self.tail.swap(node.as_ptr(), AcqRel);
        // If we have a predecessor, complete the link so it will notify us.
        if !pred.is_null() {
            // SAFETY: Already verified that predecessor is not null.
            unsafe { &*pred }.next.store(node.as_ptr(), Release);
            // Acquire this mutex, applying some waiting policy.
            node.lock.lock_wait_relaxed::<W>();
            fence(Acquire);
        }
        MutexGuard::new(self, node)
    }

    /// Unlocks this mutex. If there is a successor node in the queue, the lock
    /// is passed directly to them.
    fn unlock(&self, head: &MutexNodeInit<L>) {
        let mut next = head.next.load(Relaxed);
        // If we don't have a known successor currently,
        if next.is_null() {
            // and we are the tail, then dequeue and free the lock.
            let false = self.try_unlock_release(head.as_ptr()) else { return };
            // But if we are not the tail, then we have a pending successor. We
            // must wait for them to finish linking with us.
            next = wait_next_relaxed::<L, W::UnlockRelax>(&head.next);
        }
        fence(Acquire);
        // Notify our successor that they hold the lock.
        // SAFETY: We already verified that our successor is not null.
        unsafe { &*next }.lock.notify();
    }
}

/// A relaxed loop that returns a pointer to the successor once it finishes
/// linking with the current thread.
///
/// The successor node is loaded with a relaxed ordering.
fn wait_next_relaxed<L, R: Relax>(next: &AtomicPtr<MutexNodeInit<L>>) -> *mut MutexNodeInit<L> {
    let mut relax = R::default();
    loop {
        let ptr = next.load(Relaxed);
        let true = ptr.is_null() else { return ptr };
        relax.relax();
    }
}

impl<T: ?Sized, L, W> Mutex<T, L, W> {
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
    fn try_unlock_release(&self, node: *mut MutexNodeInit<L>) -> bool {
        self.tail.compare_exchange(node, ptr::null_mut(), Release, Relaxed).is_ok()
    }
}

impl<T: ?Sized + Debug, L: Lock, W: Wait> Debug for Mutex<T, L, W> {
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
pub struct MutexGuard<'a, T: ?Sized, L: Lock, W: Wait> {
    lock: &'a Mutex<T, L, W>,
    head: &'a MutexNodeInit<L>,
}

// `std::sync::MutexGuard` is not Send for pthread compatibility, but this
// implementation is safe to be Send.
unsafe impl<T: ?Sized + Send, L: Lock, W: Wait> Send for MutexGuard<'_, T, L, W> {}

// Same unsafe Sync impl as `std::sync::MutexGuard`.
unsafe impl<T: ?Sized + Sync, L: Lock, W: Wait> Sync for MutexGuard<'_, T, L, W> {}

impl<'a, T: ?Sized, L: Lock, W: Wait> MutexGuard<'a, T, L, W> {
    /// Creates a new `MutexGuard` instance.
    const fn new(lock: &'a Mutex<T, L, W>, head: &'a MutexNodeInit<L>) -> Self {
        Self { lock, head }
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

impl<'a, T: ?Sized + Debug, L: Lock, W: Wait> Debug for MutexGuard<'a, T, L, W> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        self.with(|data| data.fmt(f))
    }
}

impl<'a, T: ?Sized + Display, L: Lock, W: Wait> Display for MutexGuard<'a, T, L, W> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        self.with(|data| data.fmt(f))
    }
}

#[cfg(not(all(loom, test)))]
impl<'a, T: ?Sized, L: Lock, W: Wait> core::ops::Deref for MutexGuard<'a, T, L, W> {
    type Target = T;

    /// Dereferences the guard to access the underlying data.
    fn deref(&self) -> &T {
        // SAFETY: A guard instance holds the lock locked.
        unsafe { &*self.lock.data.get() }
    }
}

#[cfg(not(all(loom, test)))]
impl<'a, T: ?Sized, L: Lock, W: Wait> core::ops::DerefMut for MutexGuard<'a, T, L, W> {
    /// Mutably dereferences the guard to access the underlying data.
    fn deref_mut(&mut self) -> &mut T {
        // SAFETY: A guard instance holds the lock locked.
        unsafe { &mut *self.lock.data.get() }
    }
}

impl<'a, T: ?Sized, L: Lock, W: Wait> Drop for MutexGuard<'a, T, L, W> {
    fn drop(&mut self) {
        self.lock.unlock(self.head);
    }
}

/// SAFETY: A guard instance hold the lock locked, with exclusive access to the
/// underlying data.
#[cfg(all(loom, test))]
#[cfg(not(tarpaulin_include))]
unsafe impl<T: ?Sized, L: Lock, W: Wait> crate::loom::Guard for MutexGuard<'_, T, L, W> {
    type Target = T;

    fn get(&self) -> &loom::cell::UnsafeCell<Self::Target> {
        &self.lock.data
    }
}
