use core::fmt::{self, Debug, Display, Formatter};
use core::marker::PhantomData;
use core::mem::MaybeUninit;
use core::ptr;
use core::sync::atomic::Ordering::{AcqRel, Acquire, Relaxed, Release};

use crate::cfg::atomic::{fence, AtomicPtr, AtomicPtrNull};
use crate::cfg::cell::{UnsafeCell, UnsafeCellOptionWith, UnsafeCellWith};
use crate::lock::{Lock, Wait};
use crate::relax::Relax;

#[cfg(feature = "thread_local")]
mod thread_local;

#[cfg(feature = "thread_local")]
pub use thread_local::LocalMutexNode;

#[cfg(all(feature = "thread_local", feature = "barging"))]
pub use thread_local::Key;

/// The inner type of [`MutexNode`], which is known to be in initialized state.
#[derive(Debug)]
pub struct MutexNodeInit<L> {
    next: AtomicPtr<Self>,
    lock: L,
}

impl<L> MutexNodeInit<L> {
    /// Returns a raw mutable pointer of this node.
    const fn as_ptr(&self) -> *mut Self {
        (self as *const Self).cast_mut()
    }

    /// A relaxed loop that returns a pointer to the successor once it finishes
    /// linking with the current thread.
    ///
    /// The successor node is loaded with a relaxed ordering.
    fn wait_next_relaxed<R: Relax>(&self) -> *mut Self {
        let mut relax = R::new();
        loop {
            let ptr = self.next.load(Relaxed);
            let true = ptr.is_null() else { return ptr };
            relax.relax();
        }
    }
}

impl<L: Lock> MutexNodeInit<L> {
    /// Creates a new, locked, initialized and core based node (const).
    #[cfg(not(all(loom, test)))]
    const fn locked() -> Self {
        let next = AtomicPtr::NULL_MUT;
        let lock = Lock::LOCKED;
        Self { next, lock }
    }

    /// Creates a new, locked, initialized and loom based node (non-const).
    #[cfg(all(loom, test))]
    #[cfg(not(tarpaulin_include))]
    fn locked() -> Self {
        let next = AtomicPtr::null_mut();
        let lock = Lock::locked();
        Self { next, lock }
    }
}

/// A locally-accessible record for forming the waiting queue.
///
/// The inner state is never dropped, only overwritten. This is desirable and
/// well suited for our use cases, since all `L` types used are only composed
/// of `no drop glue` types (eg. atomic types).
///
/// `L` must fail [`core::mem::needs_drop`] check, else `L` will leak.
#[derive(Debug)]
#[repr(transparent)]
pub struct MutexNode<L> {
    inner: MaybeUninit<MutexNodeInit<L>>,
}

impl<L> MutexNode<L> {
    /// Creates new `MutexNode` instance.
    pub const fn new() -> Self {
        Self { inner: MaybeUninit::uninit() }
    }
}

impl<L: Lock> MutexNode<L> {
    /// Initializes this node's inner state, returning a shared reference
    /// pointing to it.
    fn initialize(&mut self) -> &MutexNodeInit<L> {
        self.inner.write(MutexNodeInit::locked())
    }
}

#[cfg(not(tarpaulin_include))]
impl<L> Default for MutexNode<L> {
    #[inline(always)]
    fn default() -> Self {
        Self::new()
    }
}

/// A mutual exclusion primitive implementing the MCS lock protocol, useful for
/// protecting shared data.
pub struct Mutex<T: ?Sized, L, W> {
    tail: AtomicPtr<MutexNodeInit<L>>,
    wait: PhantomData<W>,
    data: UnsafeCell<T>,
}

// SAFETY: A `Mutex` is safe to be sent across thread boundaries as long as
// the inlined protected data `T` is also safe to be sent to other threads.
unsafe impl<T: ?Sized + Send, L, W> Send for Mutex<T, L, W> {}
// SAFETY: A `Mutex` is safe to be shared across thread boundaries since it
// guarantees linearization of access and modification to the protected data,
// but only if the protected data `T` is safe to be sent to other threads.
unsafe impl<T: ?Sized + Send, L, W> Sync for Mutex<T, L, W> {}

impl<T, L, W> Mutex<T, L, W> {
    /// Creates a new, unlocked and core based mutex (const).
    #[cfg(not(all(loom, test)))]
    pub const fn new(value: T) -> Self {
        let tail = AtomicPtr::NULL_MUT;
        let data = UnsafeCell::new(value);
        Self { tail, data, wait: PhantomData }
    }

    /// Creates a new, unlocked and loom based mutex (non-const).
    #[cfg(all(loom, test))]
    #[cfg(not(tarpaulin_include))]
    pub fn new(value: T) -> Self {
        let tail = AtomicPtr::null_mut();
        let data = UnsafeCell::new(value);
        Self { tail, data, wait: PhantomData }
    }

    /// Consumes this mutex, returning the underlying data.
    pub fn into_inner(self) -> T {
        self.data.into_inner()
    }
}

impl<T: ?Sized, L: Lock, W: Wait> Mutex<T, L, W> {
    /// Attempts to acquire this mutex without blocking the thread.
    ///
    /// # Safety
    ///
    /// The returned guard instance **must** be dropped, that is, it **must not**
    /// be "forgotten" (e.g. `core::mem::forget`), or being targeted by any
    /// other operation that would prevent it from executing its `drop` call.
    unsafe fn try_lock_with<'a>(&'a self, n: &'a mut MutexNode<L>) -> OptionGuard<'a, T, L, W> {
        let node = n.initialize();
        self.tail
            .compare_exchange(ptr::null_mut(), node.as_ptr(), AcqRel, Relaxed)
            .map(|_| MutexGuard::new(self, node))
            .ok()
    }

    /// Acquires this mutex, blocking the current thread until it is able to do so.
    ///
    /// # Safety
    ///
    /// The returned guard instance **must** be dropped, that is, it **must not**
    /// be "forgotten" (e.g. `core::mem::forget`), or being targeted of any
    /// other operation that would prevent it from executing its `drop` call.
    unsafe fn lock_with<'a>(&'a self, n: &'a mut MutexNode<L>) -> MutexGuard<'a, T, L, W> {
        let node = n.initialize();
        let pred = self.tail.swap(node.as_ptr(), AcqRel);
        // If we have a predecessor, complete the link so it will notify us.
        if !pred.is_null() {
            // SAFETY: Already verified that our predecessor is not null.
            unsafe { &(*pred).next }.store(node.as_ptr(), Release);
            // Verify the lock hand-off, while applying some waiting policy.
            node.lock.wait_lock_relaxed::<W>();
            fence(Acquire);
        }
        MutexGuard::new(self, node)
    }

    /// Unlocks this mutex. If there is a successor node in the queue, the lock
    /// is passed directly to them.
    fn unlock_with(&self, head: &MutexNodeInit<L>) {
        let mut next = head.next.load(Relaxed);
        // If we don't have a known successor currently,
        if next.is_null() {
            // and we are the tail, then dequeue and free the lock.
            let false = self.try_unlock_release(head.as_ptr()) else { return };
            // But if we are not the tail, then we have a pending successor. We
            // must wait for them to finish linking with us.
            next = head.wait_next_relaxed::<W::UnlockRelax>();
        }
        fence(Acquire);
        // Notify our successor that they hold the lock.
        // SAFETY: We already verified that our successor is not null.
        unsafe { &(*next).lock }.notify_release();
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

impl<T: ?Sized, L: Lock, W: Wait> Mutex<T, L, W> {
    /// Attempts to acquire this mutex and then runs a closure against the
    /// protected data.
    ///
    /// This function does not block.
    pub fn try_lock_with_then<F, Ret>(&self, node: &mut MutexNode<L>, f: F) -> Ret
    where
        F: FnOnce(Option<&mut T>) -> Ret,
    {
        // SAFETY: The guard's `drop` call is executed within this scope.
        unsafe { self.try_lock_with(node) }.as_deref_mut_with_mut(f)
    }

    /// Acquires this mutex and then runs the closure against the protected data.
    ///
    /// This function will block if the lock is unavailable.
    pub fn lock_with_then<F, Ret>(&self, node: &mut MutexNode<L>, f: F) -> Ret
    where
        F: FnOnce(&mut T) -> Ret,
    {
        // SAFETY: The guard's `drop` call is executed within this scope.
        unsafe { self.lock_with(node) }.with_mut(f)
    }
}

impl<T: ?Sized + Debug, L: Lock, W: Wait> Debug for Mutex<T, L, W> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let mut d = f.debug_struct("Mutex");
        let mut node = MutexNode::new();
        self.try_lock_with_then(&mut node, |data| match data {
            Some(data) => d.field("data", &data),
            None => d.field("data", &format_args!("<locked>")),
        });
        d.finish()
    }
}

/// Short alias for a `Option` wrapped `MutexGuard`;
type OptionGuard<'a, T, L, W> = Option<MutexGuard<'a, T, L, W>>;

/// An RAII implementation of a "scoped lock" of a mutex. When this structure is
/// dropped (falls out of scope), the lock will be unlocked.
#[must_use = "if unused the Mutex will immediately unlock"]
struct MutexGuard<'a, T: ?Sized, L: Lock, W: Wait> {
    lock: &'a Mutex<T, L, W>,
    head: &'a MutexNodeInit<L>,
}

// SAFETY: A `MutexGuard` is safe to be sent across thread boundaries as long as
// the referenced protected data `T` is also safe to be sent to other threads.
// Note that `std::sync::MutexGuard` is `!Send` because it must be compatible
// with `Pthreads` implementation on Linux, but we do not have this constraint.
unsafe impl<T: ?Sized + Send, L: Lock + Send, W: Wait> Send for MutexGuard<'_, T, L, W> {}
// SAFETY: A `MutexGuard` is safe to be shared across thread boundaries since
// it owns exclusive access over the protected data during its lifetime, and so
// the can safely share references to the data, but only if the protected data
// is also safe to be shared with other cuncurrent threads.
unsafe impl<T: ?Sized + Sync, L: Lock + Sync, W: Wait> Sync for MutexGuard<'_, T, L, W> {}

impl<'a, T: ?Sized, L: Lock, W: Wait> MutexGuard<'a, T, L, W> {
    /// Creates a new `MutexGuard` instance.
    const fn new(lock: &'a Mutex<T, L, W>, head: &'a MutexNodeInit<L>) -> Self {
        Self { lock, head }
    }

    /// Runs `f` against a shared reference pointing to the underlying data.
    #[cfg(not(tarpaulin_include))]
    fn with<F, Ret>(&self, f: F) -> Ret
    where
        F: FnOnce(&T) -> Ret,
    {
        // SAFETY: A guard instance holds the lock locked.
        unsafe { self.lock.data.with_unchecked(f) }
    }

    /// Runs `f` against a mutable reference pointing to the underlying data.
    fn with_mut<F, Ret>(&mut self, f: F) -> Ret
    where
        F: FnOnce(&mut T) -> Ret,
    {
        // SAFETY: A guard instance holds the lock locked.
        unsafe { self.lock.data.with_mut_unchecked(f) }
    }
}

/// A trait that converts a `&mut Self` to a `Option<&mut Self::Target>` and
/// then runs closures against it.
trait AsDerefMutWithMut {
    type Target: ?Sized;

    /// Converts `&mut Self` to `Option<&mut Self::Target>` and then runs `f`
    /// against it.
    fn as_deref_mut_with_mut<F, Ret>(&mut self, f: F) -> Ret
    where
        F: FnOnce(Option<&mut Self::Target>) -> Ret;
}

impl<T: ?Sized, L: Lock, W: Wait> AsDerefMutWithMut for OptionGuard<'_, T, L, W> {
    type Target = T;

    fn as_deref_mut_with_mut<F, Ret>(&mut self, f: F) -> Ret
    where
        F: FnOnce(Option<&mut Self::Target>) -> Ret,
    {
        let data = self.as_ref().map(|guard| &guard.lock.data);
        // SAFETY: A guard instance holds the lock locked.
        unsafe { data.as_deref_with_mut_unchecked(f) }
    }
}

#[cfg(not(tarpaulin_include))]
impl<T: ?Sized + Debug, L: Lock, W: Wait> Debug for MutexGuard<'_, T, L, W> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        self.with(|data| data.fmt(f))
    }
}

#[cfg(not(tarpaulin_include))]
impl<T: ?Sized + Display, L: Lock, W: Wait> Display for MutexGuard<'_, T, L, W> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        self.with(|data| data.fmt(f))
    }
}

#[cfg(not(all(loom, test)))]
#[cfg(not(tarpaulin_include))]
impl<T: ?Sized, L: Lock, W: Wait> core::ops::Deref for MutexGuard<'_, T, L, W> {
    type Target = T;

    /// Dereferences the guard to access the underlying data.
    #[inline(always)]
    fn deref(&self) -> &T {
        // SAFETY: A guard instance holds the lock locked.
        unsafe { &*self.lock.data.get() }
    }
}

#[cfg(not(all(loom, test)))]
#[cfg(not(tarpaulin_include))]
impl<T: ?Sized, L: Lock, W: Wait> core::ops::DerefMut for MutexGuard<'_, T, L, W> {
    /// Mutably dereferences the guard to access the underlying data.
    #[inline(always)]
    fn deref_mut(&mut self) -> &mut T {
        // SAFETY: A guard instance holds the lock locked.
        unsafe { &mut *self.lock.data.get() }
    }
}

impl<T: ?Sized, L: Lock, W: Wait> Drop for MutexGuard<'_, T, L, W> {
    #[inline]
    fn drop(&mut self) {
        self.lock.unlock_with(self.head);
    }
}
