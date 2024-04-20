use core::mem::MaybeUninit;
use core::sync::atomic::Ordering::{AcqRel, Acquire, Relaxed, Release};
use core::{fmt, ptr};

use crate::cfg::atomic::{fence, AtomicBool, AtomicPtr};
use crate::cfg::cell::{UnsafeCell, WithUnchecked};
use crate::cfg::thread::{self, Thread};

thread_local!(static THREAD: Thread = thread::current());

/// TODO: Docs
struct MutexNodeInit {
    next: AtomicPtr<MutexNodeInit>,
    locked: AtomicBool,
    thread: *const Thread,
}

impl MutexNodeInit {
    /// Crates a new `MutexNodeInit` instance.
    #[cfg(not(all(loom, test)))]
    #[inline]
    fn new(thread: *const Thread) -> Self {
        let next = AtomicPtr::new(ptr::null_mut());
        let locked = AtomicBool::new(true);
        // let thread = thread::current();
        Self { next, locked, thread }
    }

    /// Returns a raw mutable pointer of this node.
    const fn as_ptr(&self) -> *mut Self {
        (self as *const Self).cast_mut()
    }

    // unsafe fn unpark(this: *mut Self) {
    //     (*this).locked.store(false, Release);
    //     (*(*this).thread).unpark();
    // }
}

/// TODO: Docs
#[derive(Debug)]
pub struct MutexNode {
    inner: MaybeUninit<MutexNodeInit>,
    // next: AtomicPtr<MutexNode>,
    // locked: AtomicBool,
    // thread: UnsafeCell<Option<Thread>>,
}

impl MutexNode {
    /// TODO: Docs
    pub const fn new() -> Self {
        Self { inner: MaybeUninit::uninit() }
    }

    /// TODO: Docs
    fn initialize(&mut self) -> &mut MutexNodeInit {
        THREAD.with(|thread| self.inner.write(MutexNodeInit::new(thread)))
    }

    // /// TODO: Docs
    // #[inline]
    // pub fn new() -> Self {
    //     let next = AtomicPtr::new(ptr::null_mut());
    //     let locked = AtomicBool::new(true);
    //     let thread = UnsafeCell::new(None);
    //     Self { next, locked, thread }
    // }

    // /// Returns a raw mutable pointer of this node.
    // const fn as_ptr(&self) -> *mut Self {
    //     (self as *const Self).cast_mut()
    // }

    // /// TODO: Docs
    // fn initialize(&mut self) -> &mut MutexNode {
    //     self.next = AtomicPtr::new(ptr::null_mut());
    //     self.locked = AtomicBool::new(true);
    //     *unsafe { &mut *self.thread.get() } = Some(thread::current());
    //     // self.thread = Some(thread::current());
    //     self
    // }
}

impl Default for MutexNode {
    fn default() -> Self {
        Self::new()
    }
}

/// TODO: Docs
pub struct Mutex<T: ?Sized> {
    tail: AtomicPtr<MutexNodeInit>,
    data: UnsafeCell<T>,
}

// Same unsafe impls as `std::sync::Mutex`.
unsafe impl<T: ?Sized + Send> Send for Mutex<T> {}
unsafe impl<T: ?Sized + Send> Sync for Mutex<T> {}

impl<T> Mutex<T> {
    /// TODO: Docs
    #[cfg(not(all(loom, test)))]
    #[inline]
    pub const fn new(value: T) -> Self {
        let tail = AtomicPtr::new(ptr::null_mut());
        let data = UnsafeCell::new(value);
        Self { tail, data }
    }

    /// Creates a new unlocked mutex with Loom primitives (non-const).
    #[cfg(all(loom, test))]
    #[cfg(not(tarpaulin_include))]
    fn new(value: T) -> Self {
        let tail = AtomicPtr::new(ptr::null_mut());
        let data = UnsafeCell::new(value);
        Self { tail, data }
    }

    /// TODO: Docs
    #[inline(always)]
    pub fn into_inner(self) -> T {
        self.data.into_inner()
    }
}

impl<T: ?Sized> Mutex<T> {
    /// TODO: Docs
    #[inline]
    pub fn try_lock<'a>(&'a self, node: &'a mut MutexNode) -> Option<MutexGuard<'a, T>> {
        let node = node.initialize();
        self.tail
            .compare_exchange(ptr::null_mut(), node.as_ptr(), AcqRel, Relaxed)
            .map(|_| MutexGuard::new(self, node))
            .ok()
    }

    /// TODO: Docs
    #[inline]
    pub fn try_lock_with<F, Ret>(&self, f: F) -> Ret
    where
        F: FnOnce(Option<MutexGuard<'_, T>>) -> Ret,
    {
        let mut node = MutexNode::new();
        f(self.try_lock(&mut node))
    }

    /// TODO: Docs
    #[inline]
    pub fn lock<'a>(&'a self, node: &'a mut MutexNode) -> MutexGuard<'a, T> {
        let node = node.initialize();
        let pred = self.tail.swap(node.as_ptr(), AcqRel);
        // If we have a predecessor, complete the link so it will notify us.
        if !pred.is_null() {
            // SAFETY: Already verified that predecessor is not null.
            unsafe { &*pred }.next.store(node.as_ptr(), Release);
            while node.locked.load(Relaxed) {
                thread::park();
            }
            fence(Acquire);
        }
        MutexGuard::new(self, node)
    }

    /// TODO: Docs
    #[inline]
    pub fn lock_with<F, Ret>(&self, f: F) -> Ret
    where
        F: FnOnce(MutexGuard<'_, T>) -> Ret,
    {
        let mut node = MutexNode::new();
        f(self.lock(&mut node))
    }

    /// TODO: Docs
    #[inline]
    pub fn is_locked(&self) -> bool {
        // Relaxed is sufficient because this method only guarantees atomicity.
        !self.tail.load(Relaxed).is_null()
    }

    /// TODO: Docs
    #[cfg(not(all(loom, test)))]
    #[inline(always)]
    pub fn get_mut(&mut self) -> &mut T {
        // SAFETY: We hold exclusive access to the Mutex data.
        unsafe { &mut *self.data.get() }
    }

    /// Unlocks this mutex. If there is a successor node in the queue, the lock
    /// is passed directly to them.
    fn unlock(&self, node: &MutexNodeInit) {
        let mut next = node.next.load(Relaxed);
        // If we don't have a known successor currently,
        if next.is_null() {
            // and we are the tail, then dequeue and free the lock.
            let false = self.try_unlock(node.as_ptr()) else { return };
            // But if we are not the tail, then we have a pending successor. We
            // must wait for them to finish linking with us.
            loop {
                next = node.next.load(Relaxed);
                let true = next.is_null() else { break };
                thread::yield_now();
            }
        }
        fence(Acquire);
        // SAFETY: We already verified that our successor is not null.
        unsafe {
            // MutexNodeInit::unpark(next);
            (*next).locked.store(false, Release);
            (*(*next).thread).unpark();
        }
    }

    /// Unlocks the lock if the candidate node is the queue's tail.
    fn try_unlock(&self, node: *mut MutexNodeInit) -> bool {
        self.tail.compare_exchange(node, ptr::null_mut(), Release, Relaxed).is_ok()
    }
}

impl<T: ?Sized + Default> Default for Mutex<T> {
    /// Creates a `Mutex<T, R>`, with the `Default` value for `T`.
    #[inline]
    fn default() -> Self {
        Self::new(Default::default())
    }
}

impl<T> From<T> for Mutex<T> {
    /// Creates a `Mutex<T, R>` from a instance of `T`.
    #[inline]
    fn from(data: T) -> Self {
        Self::new(data)
    }
}

impl<T: ?Sized + fmt::Debug> fmt::Debug for Mutex<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut node = MutexNode::new();
        let mut d = f.debug_struct("Mutex");
        match self.try_lock(&mut node) {
            Some(guard) => guard.with(|data| d.field("data", &data)),
            None => d.field("data", &format_args!("<locked>")),
        };
        d.finish()
    }
}

#[cfg(test)]
impl<T: ?Sized> crate::test::LockNew for Mutex<T> {
    type Target = T;

    fn new(value: Self::Target) -> Self
    where
        Self::Target: Sized,
    {
        Self::new(value)
    }
}

#[cfg(test)]
impl<T: ?Sized> crate::test::LockWith for Mutex<T> {
    type Guard<'a> = MutexGuard<'a, Self::Target>
    where
        Self: 'a,
        Self::Target: 'a;

    fn try_lock_with<F, Ret>(&self, f: F) -> Ret
    where
        F: FnOnce(Option<MutexGuard<'_, T>>) -> Ret,
    {
        self.try_lock_with(f)
    }

    fn lock_with<F, Ret>(&self, f: F) -> Ret
    where
        F: FnOnce(MutexGuard<'_, T>) -> Ret,
    {
        self.lock_with(f)
    }

    fn is_locked(&self) -> bool {
        self.is_locked()
    }
}

#[cfg(all(not(loom), test))]
impl<T: ?Sized> crate::test::LockData for Mutex<T> {
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

/// TODO: Docs
#[must_use = "if unused the Mutex will immediately unlock"]
pub struct MutexGuard<'a, T: ?Sized> {
    lock: &'a Mutex<T>,
    node: &'a MutexNodeInit,
}

// `std::sync::MutexGuard` is not Send for pthread compatibility, but this
// implementation is safe to be Send.
unsafe impl<T: ?Sized + Send> Send for MutexGuard<'_, T> {}
// Same unsafe Sync impl as `std::sync::MutexGuard`.
unsafe impl<T: ?Sized + Sync> Sync for MutexGuard<'_, T> {}

impl<'a, T: ?Sized> MutexGuard<'a, T> {
    /// Creates a new `MutexGuard` instance.
    const fn new(lock: &'a Mutex<T>, node: &'a MutexNodeInit) -> Self {
        Self { lock, node }
    }

    /// Runs `f` against an shared reference pointing to the underlying data.
    fn with<F, Ret>(&self, f: F) -> Ret
    where
        F: FnOnce(&T) -> Ret,
    {
        // SAFETY: A guard instance holds the lock locked.
        unsafe { self.lock.data.with_unchecked(f) }
    }
}

impl<'a, T: ?Sized> Drop for MutexGuard<'a, T> {
    #[inline]
    fn drop(&mut self) {
        self.lock.unlock(self.node);
    }
}

impl<'a, T: ?Sized + fmt::Debug> fmt::Debug for MutexGuard<'a, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.with(|data| fmt::Debug::fmt(data, f))
    }
}

impl<'a, T: ?Sized + fmt::Display> fmt::Display for MutexGuard<'a, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.with(|data| fmt::Display::fmt(data, f))
    }
}

#[cfg(not(all(loom, test)))]
impl<'a, T: ?Sized> core::ops::Deref for MutexGuard<'a, T> {
    type Target = T;

    /// Dereferences the guard to access the underlying data.
    #[inline(always)]
    fn deref(&self) -> &T {
        // SAFETY: A guard instance holds the lock locked.
        unsafe { &*self.lock.data.get() }
    }
}

#[cfg(not(all(loom, test)))]
impl<'a, T: ?Sized> core::ops::DerefMut for MutexGuard<'a, T> {
    /// Mutably dereferences the guard to access the underlying data.
    #[inline(always)]
    fn deref_mut(&mut self) -> &mut T {
        // SAFETY: A guard instance holds the lock locked.
        unsafe { &mut *self.lock.data.get() }
    }
}

/// SAFETY: A guard instance hold the lock locked, with exclusive access to the
/// underlying data.
#[cfg(all(loom, test))]
#[cfg(not(tarpaulin_include))]
unsafe impl<T: ?Sized> crate::loom::Guard for MutexGuard<'_, T> {
    type Target = T;

    fn get(&self) -> &loom::cell::UnsafeCell<Self::Target> {
        &self.lock.data
    }
}

#[cfg(all(not(loom), test))]
mod test {
    use super::{Mutex, MutexNode};
    use crate::test::tests;
    use std::sync::mpsc::channel;

    #[test]
    fn node_default_and_new_init() {
        let mut d = MutexNode::default();
        let d_init = d.initialize();
        assert!(d_init.next.get_mut().is_null());
        assert!(*d_init.locked.get_mut());

        let mut n = MutexNode::new();
        let n_init = n.initialize();
        assert!(n_init.next.get_mut().is_null());
        assert!(*n_init.locked.get_mut());
    }

    #[test]
    fn do_something() {
        use std::sync::Arc;
        let data = Arc::new(Mutex::new(0));
        let (tx, rx) = channel();
        const CONCURRENCY: u32 = 3;
        const ITERS: u32 = 1000;
        for _ in 0..CONCURRENCY {
            let tx2 = tx.clone();
            let c_data = Arc::clone(&data);
            std::thread::spawn(move || {
                let mut node = MutexNode::new();
                for _ in 0..ITERS {
                    *c_data.lock(&mut node) += 1;
                }
                tx2.send(()).unwrap();
            });
            let tx2 = tx.clone();
            let d_data = Arc::clone(&data);
            std::thread::spawn(move || {
                let mut node = MutexNode::new();
                for _ in 0..ITERS {
                    *d_data.lock(&mut node) += 1;
                }
                tx2.send(()).unwrap();
            });
        }
        drop(tx);
        for _ in 0..2 * CONCURRENCY {
            rx.recv().unwrap();
        }
        let mut node = MutexNode::new();
        assert_eq!(CONCURRENCY * ITERS * 2, *data.lock(&mut node));
    }

    #[test]
    fn lots_and_lots() {
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
    use crate::parking::Mutex;

    #[test]
    fn try_lock_join() {
        models::try_lock_join::<Mutex<_>>();
    }

    #[test]
    fn lock_join() {
        models::lock_join::<Mutex<_>>();
    }

    #[test]
    fn mixed_lock_join() {
        models::mixed_lock_join::<Mutex<_>>();
    }
}
