use core::fmt;
use core::marker::PhantomData;
use core::mem::MaybeUninit;
use core::ptr;
use core::sync::atomic::Ordering::{AcqRel, Acquire, Relaxed, Release};

#[cfg(not(all(loom, test)))]
use core::cell::UnsafeCell;
#[cfg(not(all(loom, test)))]
use core::ops::{Deref, DerefMut};
#[cfg(not(all(loom, test)))]
use core::sync::atomic::{fence, AtomicBool, AtomicPtr};

#[cfg(all(loom, test))]
use loom::cell::{ConstPtr, MutPtr, UnsafeCell};
#[cfg(all(loom, test))]
use loom::sync::atomic::{fence, AtomicBool, AtomicPtr};

#[cfg(all(loom, test))]
use crate::loom::{Guard, GuardDeref, GuardDerefMut};

use crate::relax::Relax;

/// The inner definition of [`MutexNode`], which is known to be in a initialized
/// state.
#[derive(Debug)]
struct MutexNodeInit {
    next: AtomicPtr<MutexNodeInit>,
    locked: AtomicBool,
}

impl MutexNodeInit {
    /// Crates a new `MutexNodeInit` instance.
    #[cfg(not(all(loom, test)))]
    const fn new() -> Self {
        let next = AtomicPtr::new(ptr::null_mut());
        let locked = AtomicBool::new(true);
        Self { next, locked }
    }

    /// Creates a new Loom based `MutexNodeInit` instance (non-const).
    #[cfg(all(loom, test))]
    fn new() -> Self {
        let next = AtomicPtr::new(ptr::null_mut());
        let locked = AtomicBool::new(true);
        Self { next, locked }
    }

    /// Returns a raw mutable pointer of this node.
    const fn as_ptr(&self) -> *mut Self {
        (self as *const Self).cast_mut()
    }
}

/// A locally-accessible record for forming the waiting queue.
///
/// `MutexNode` is an opaque type that holds metadata for the [`Mutex`]'s
/// waiting queue. To acquire a MCS lock, an instance of queue node must be
/// reachable and mutably borrowed for the duration of some associated
/// [`MutexGuard`]. Once the guard is dropped, a node instance can be reused as
/// the backing allocation for another lock acquisition. See [`lock`] and
/// [`try_lock`] methods on [`Mutex`].
///
/// [`lock`]: Mutex::lock
/// [`try_lock`]: Mutex::try_lock
#[repr(transparent)]
#[derive(Debug)]
pub struct MutexNode(MaybeUninit<MutexNodeInit>);

impl MutexNode {
    /// Creates new `MutexNode` instance.
    ///
    /// # Examples
    ///
    /// ```
    /// use mcslock::raw::MutexNode;
    ///
    /// let node = MutexNode::new();
    /// ```
    #[inline]
    #[must_use]
    pub const fn new() -> Self {
        Self(MaybeUninit::uninit())
    }

    /// Initializes this node and returns a exclusive reference to the initialized
    /// inner state.
    fn initialize(&mut self) -> &mut MutexNodeInit {
        self.0.write(MutexNodeInit::new())
    }
}

/// A mutual exclusion primitive useful for protecting shared data.
///
/// This mutex will block threads waiting for the lock to become available. The
/// mutex can also be statically initialized or created via a [`new`]
/// constructor. Each mutex has a type parameter which represents the data that
/// it is protecting. The data can only be accessed through the RAII guards
/// returned from [`lock`] and [`try_lock`], which guarantees that the data is only
/// ever accessed when the mutex is locked.
///
/// # Examples
///
/// ```
/// use std::sync::Arc;
/// use std::thread;
/// use std::sync::mpsc::channel;
///
/// use mcslock::raw::{Mutex, MutexNode};
/// use mcslock::relax::Spin;
///
/// type SpinMutex<T> = Mutex<T, Spin>;
///
/// const N: usize = 10;
///
/// // Spawn a few threads to increment a shared variable (non-atomically), and
/// // let the main thread know once all increments are done.
/// //
/// // Here we're using an Arc to share memory among threads, and the data inside
/// // the Arc is protected with a mutex.
/// let data = Arc::new(SpinMutex::new(0));
///
/// let (tx, rx) = channel();
/// for _ in 0..N {
///     let (data, tx) = (data.clone(), tx.clone());
///     thread::spawn(move || {
///         // A queue node must be mutably accessible.
///         let mut node = MutexNode::new();
///         // The shared state can only be accessed once the lock is held.
///         // Our non-atomic increment is safe because we're the only thread
///         // which can access the shared state when the lock is held.
///         //
///         // We unwrap() the return value to assert that we are not expecting
///         // threads to ever fail while holding the lock.
///         let mut data = data.lock(&mut node);
///         *data += 1;
///         if *data == N {
///             tx.send(()).unwrap();
///         }
///         // the lock is unlocked here when `data` goes out of scope.
///     });
/// }
///
/// rx.recv().unwrap();
/// ```
/// [`new`]: Mutex::new
/// [`lock`]: Mutex::lock
/// [`try_lock`]: Mutex::try_lock
pub struct Mutex<T: ?Sized, R> {
    tail: AtomicPtr<MutexNodeInit>,
    marker: PhantomData<R>,
    data: UnsafeCell<T>,
}

// Same unsafe impls as `std::sync::Mutex`.
unsafe impl<T: ?Sized + Send, R> Sync for Mutex<T, R> {}
unsafe impl<T: ?Sized + Send, R> Send for Mutex<T, R> {}

impl<T, R> Mutex<T, R> {
    /// Creates a new mutex in an unlocked state ready for use.
    ///
    /// # Examples
    ///
    /// ```
    /// use mcslock::raw::Mutex;
    /// use mcslock::relax::Spin;
    ///
    /// type SpinMutex<T> = Mutex<T, Spin>;
    ///
    /// const MUTEX: SpinMutex<i32> = SpinMutex::new(0);
    /// let mutex = SpinMutex::new(0);
    /// ```
    #[cfg(not(all(loom, test)))]
    #[inline]
    pub const fn new(value: T) -> Self {
        let tail = AtomicPtr::new(ptr::null_mut());
        let data = UnsafeCell::new(value);
        Self { tail, data, marker: PhantomData }
    }

    /// Creates a new unlocked mutex with Loom primitives (non-const).
    #[cfg(all(loom, test))]
    pub(crate) fn new(value: T) -> Self {
        let tail = AtomicPtr::new(ptr::null_mut());
        let data = UnsafeCell::new(value);
        Self { tail, data, marker: PhantomData }
    }

    /// Consumes this mutex, returning the underlying data.
    ///
    /// # Examples
    ///
    /// ```
    /// use mcslock::raw::Mutex;
    /// use mcslock::relax::Spin;
    ///
    /// type SpinMutex<T> = Mutex<T, Spin>;
    ///
    /// let mutex = SpinMutex::new(0);
    /// assert_eq!(mutex.into_inner(), 0);
    /// ```
    #[inline]
    pub fn into_inner(self) -> T {
        self.data.into_inner()
    }
}

impl<T: ?Sized, R: Relax> Mutex<T, R> {
    /// Attempts to acquire this lock.
    ///
    /// If the lock could not be acquired at this time, then [`None`] is returned.
    /// Otherwise, an RAII guard is returned. The lock will be unlocked when the
    /// guard is dropped. To acquire a MCS lock, it's also required a mutably
    /// borrowed queue node, which is a record that keeps a link for forming the
    /// queue, see [`MutexNode`].
    ///
    /// This function does not block.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::sync::Arc;
    /// use std::thread;
    ///
    /// use mcslock::raw::{Mutex, MutexNode};
    /// use mcslock::relax::Spin;
    ///
    /// type SpinMutex<T> = Mutex<T, Spin>;
    ///
    /// let mutex = Arc::new(SpinMutex::new(0));
    /// let c_mutex = Arc::clone(&mutex);
    ///
    /// thread::spawn(move || {
    ///     let mut node = MutexNode::new();
    ///     let mut lock = c_mutex.try_lock(&mut node);
    ///     if let Some(ref mut mutex) = lock {
    ///         **mutex = 10;
    ///     } else {
    ///         println!("try_lock failed");
    ///     }
    /// })
    /// .join().expect("thread::spawn failed");
    ///
    /// let mut node = MutexNode::new();
    /// assert_eq!(*mutex.lock(&mut node), 10);
    /// ```
    pub fn try_lock<'a>(&'a self, node: &'a mut MutexNode) -> Option<MutexGuard<'a, T, R>> {
        let node = node.initialize();
        self.tail
            .compare_exchange(ptr::null_mut(), node.as_ptr(), Acquire, Relaxed)
            .map(|_| MutexGuard::new(self, node))
            .ok()
    }

    /// Attempts to acquire this lock and then runs the closure against its guard.
    ///
    /// If the lock could not be acquired at this time, then a [`None`] value is
    /// given to the user provided closure as the argument. If the lock has been
    /// acquired, then a [`Some`] with the mutex guard is given instead. The lock
    /// will be unlocked when the guard is dropped.
    ///
    /// This function does not block.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::sync::Arc;
    /// use std::thread;
    ///
    /// use mcslock::raw::Mutex;
    /// use mcslock::relax::Spin;
    ///
    /// type SpinMutex<T> = Mutex<T, Spin>;
    ///
    /// let mutex = Arc::new(SpinMutex::new(0));
    /// let c_mutex = Arc::clone(&mutex);
    ///
    /// thread::spawn(move || {
    ///     c_mutex.try_lock_with(|mut guard| {
    ///         *guard.unwrap() = 10;
    ///     });
    /// })
    /// .join().expect("thread::spawn failed");
    ///
    /// assert_eq!(mutex.lock_with(|guard| *guard), 10);
    /// ```
    ///
    /// Borrows of the guard or its data cannot escape the given closure.
    ///
    /// ```compile_fail,E0515
    /// use mcslock::raw::spins::Mutex;
    ///
    /// let mutex = Mutex::new(1);
    /// let data = mutex.try_lock_with(|guard| &*guard.unwrap());
    /// ```
    pub fn try_lock_with<F, Ret>(&self, f: F) -> Ret
    where
        F: FnOnce(Option<MutexGuard<'_, T, R>>) -> Ret,
    {
        let mut node = MutexNode::new();
        f(self.try_lock(&mut node))
    }

    /// Acquires a mutex, blocking the current thread until it is able to do so.
    ///
    /// This function will block the local thread until it is available to acquire
    /// the mutex. Upon returning, the thread is the only thread with the lock
    /// held. An RAII guard is returned to allow scoped unlock of the lock. When
    /// the guard goes out of scope, the mutex will be unlocked. To acquire a MCS
    /// lock, it's also required a mutably borrowed queue node, which is a record
    /// that keeps a link for forming the queue, see [`MutexNode`].
    ///
    /// This function will block if the lock is unavailable.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::sync::Arc;
    /// use std::thread;
    ///
    /// use mcslock::raw::{Mutex, MutexNode};
    /// use mcslock::relax::Spin;
    ///
    /// type SpinMutex<T> = Mutex<T, Spin>;
    ///
    /// let mutex = Arc::new(SpinMutex::new(0));
    /// let c_mutex = Arc::clone(&mutex);
    ///
    /// thread::spawn(move || {
    ///     let mut node = MutexNode::new();
    ///     *c_mutex.lock(&mut node) = 10;
    /// })
    /// .join().expect("thread::spawn failed");
    ///
    /// let mut node = MutexNode::new();
    /// assert_eq!(*mutex.lock(&mut node), 10);
    /// ```
    pub fn lock<'a>(&'a self, node: &'a mut MutexNode) -> MutexGuard<'a, T, R> {
        let node = node.initialize();
        let pred = self.tail.swap(node.as_ptr(), AcqRel);
        // If we have a predecessor, complete the link so it will notify us.
        if !pred.is_null() {
            // SAFETY: Already verified that predecessor is not null.
            unsafe { &*pred }.next.store(node.as_ptr(), Release);
            let mut relax = R::default();
            while node.locked.load(Relaxed) {
                relax.relax();
            }
            fence(Acquire);
        }
        MutexGuard::new(self, node)
    }

    /// Acquires a mutex and then runs the closure against its guard.
    ///
    /// This function will block the local thread until it is available to acquire
    /// the mutex. Upon acquiring the mutex, the user provided closure will be
    /// executed against the mutex guard. Once the guard goes out of scope, it
    /// will unlock the mutex.
    ///
    /// This function will block if the lock is unavailable.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::sync::Arc;
    /// use std::thread;
    ///
    /// use mcslock::raw::Mutex;
    /// use mcslock::relax::Spin;
    ///
    /// type SpinMutex<T> = Mutex<T, Spin>;
    ///
    /// let mutex = Arc::new(SpinMutex::new(0));
    /// let c_mutex = Arc::clone(&mutex);
    ///
    /// thread::spawn(move || {
    ///     c_mutex.lock_with(|mut guard| *guard = 10);
    /// })
    /// .join().expect("thread::spawn failed");
    ///
    /// assert_eq!(mutex.lock_with(|guard| *guard), 10);
    /// ```
    ///
    /// Borrows of the guard or its data cannot escape the given closure.
    ///
    /// ```compile_fail,E0515
    /// use mcslock::raw::spins::Mutex;
    ///
    /// let mutex = Mutex::new(1);
    /// let data = mutex.lock_with(|guard| &*guard);
    /// ```
    pub fn lock_with<F, Ret>(&self, f: F) -> Ret
    where
        F: FnOnce(MutexGuard<'_, T, R>) -> Ret,
    {
        let mut node = MutexNode::new();
        f(self.lock(&mut node))
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
            let mut relax = R::default();
            loop {
                next = node.next.load(Relaxed);
                let true = next.is_null() else { break };
                relax.relax();
            }
        }
        fence(Acquire);
        // SAFETY: We already verified that our successor is not null.
        unsafe { &*next }.locked.store(false, Release);
    }
}

impl<T: ?Sized, R> Mutex<T, R> {
    /// Returns `true` if the lock is currently held.
    ///
    /// This method does not provide any synchronization guarantees, so its only
    /// useful as a heuristic, and so must be considered not up to date.
    ///
    /// # Example
    ///
    /// ```
    /// use mcslock::raw::{Mutex, MutexNode};
    /// use mcslock::relax::Spin;
    ///
    /// type SpinMutex<T> = Mutex<T, Spin>;
    ///
    /// let mutex = SpinMutex::new(0);
    /// let mut node = MutexNode::new();
    ///
    /// let guard = mutex.lock(&mut node);
    /// drop(guard);
    ///
    /// assert_eq!(mutex.is_locked(), false);
    /// ```
    #[inline]
    pub fn is_locked(&self) -> bool {
        // Relaxed is sufficient because this method only guarantees atomicity.
        !self.tail.load(Relaxed).is_null()
    }

    /// Returns a mutable reference to the underlying data.
    ///
    /// Since this call borrows the `Mutex` mutably, no actual locking needs to
    /// take place - the mutable borrow statically guarantees no locks exist.
    ///
    /// # Examples
    ///
    /// ```
    /// use mcslock::raw::{Mutex, MutexNode};
    /// use mcslock::relax::Spin;
    ///
    /// type SpinMutex<T> = Mutex<T, Spin>;
    ///
    /// let mut mutex = SpinMutex::new(0);
    /// *mutex.get_mut() = 10;
    ///
    /// let mut node = MutexNode::new();
    /// assert_eq!(*mutex.lock(&mut node), 10);
    /// ```
    #[cfg(not(all(loom, test)))]
    #[inline]
    pub fn get_mut(&mut self) -> &mut T {
        // SAFETY: We hold exclusive access to the Mutex data.
        unsafe { &mut *self.data_ptr() }
    }

    /// Unlocks the lock if the candidate node is the queue's tail.
    fn try_unlock(&self, node: *mut MutexNodeInit) -> bool {
        self.tail.compare_exchange(node, ptr::null_mut(), Release, Relaxed).is_ok()
    }

    /// Returns a reference to the queue's tail debug impl.
    #[cfg(feature = "thread_local")]
    pub(crate) fn tail_debug(&self) -> &impl fmt::Debug {
        &self.tail
    }

    #[cfg(not(all(loom, test)))]
    /// Returns a raw mutable pointer to the underlying data.
    pub(crate) const fn data_ptr(&self) -> *mut T {
        self.data.get()
    }

    /// Get a Loom immutable raw pointer to the underlying data.
    #[cfg(all(loom, test))]
    pub(crate) fn data_get(&self) -> ConstPtr<T> {
        self.data.get()
    }

    /// Get a Loom mutable raw pointer to the underlying data.
    #[cfg(all(loom, test))]
    pub(crate) fn data_get_mut(&self) -> MutPtr<T> {
        self.data.get_mut()
    }
}

impl<T: ?Sized + Default, R> Default for Mutex<T, R> {
    /// Creates a `Mutex<T, R>`, with the `Default` value for `T`.
    fn default() -> Self {
        Self::new(Default::default())
    }
}

impl<T, R> From<T> for Mutex<T, R> {
    /// Creates a `Mutex<T, R>` from a instance of `T`.
    fn from(data: T) -> Self {
        Self::new(data)
    }
}

impl<T: ?Sized + fmt::Debug, R: Relax> fmt::Debug for Mutex<T, R> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut node = MutexNode::new();
        let mut d = f.debug_struct("Mutex");
        match self.try_lock(&mut node) {
            Some(guard) => guard.data_with(|data| d.field("data", &data)),
            None => d.field("data", &format_args!("<locked>")),
        };
        d.field("tail", &self.tail);
        d.finish()
    }
}

/// An RAII implementation of a "scoped lock" of a mutex. When this structure is
/// dropped (falls out of scope), the lock will be unlocked.
///
/// The data protected by the mutex can be access through this guard via its
/// [`Deref`] and [`DerefMut`] implementations.
///
/// This structure is returned by [`lock`] and [`try_lock`] methods on [`Mutex`].
/// It is also given as closure argument by [`lock_with`] and [`try_lock_with`]
/// methods.
///
/// [`lock`]: Mutex::lock
/// [`try_lock`]: Mutex::lock
/// [`lock_with`]: Mutex::lock_with
/// [`try_lock_with`]: Mutex::try_lock_with
#[must_use = "if unused the Mutex will immediately unlock"]
pub struct MutexGuard<'a, T: ?Sized, R: Relax> {
    lock: &'a Mutex<T, R>,
    node: &'a MutexNodeInit,
}

// Same unsafe impl as `std::sync::MutexGuard`.
unsafe impl<T: ?Sized + Sync, R: Relax> Sync for MutexGuard<'_, T, R> {}

impl<'a, T: ?Sized, R: Relax> MutexGuard<'a, T, R> {
    /// Creates a new `MutexGuard` instance.
    const fn new(lock: &'a Mutex<T, R>, node: &'a MutexNodeInit) -> Self {
        Self { lock, node }
    }

    /// Runs `f` with an immutable reference to the wrapped value.
    #[cfg(not(all(loom, test)))]
    pub(crate) fn data_with<F, Ret>(&self, f: F) -> Ret
    where
        F: FnOnce(&T) -> Ret,
    {
        // SAFETY: A guard instance holds the lock locked.
        f(unsafe { &*self.lock.data_ptr() })
    }

    /// Runs `f` with an immutable reference to the wrapped value.
    #[cfg(all(loom, test))]
    pub(crate) fn data_with<F, Ret>(&self, f: F) -> Ret
    where
        F: FnOnce(&T) -> Ret,
    {
        // SAFETY: A guard instance holds the lock locked.
        f(unsafe { self.lock.data_get().deref() })
    }
}

impl<'a, T: ?Sized, R: Relax> Drop for MutexGuard<'a, T, R> {
    fn drop(&mut self) {
        self.lock.unlock(self.node);
    }
}

#[cfg(not(all(loom, test)))]
impl<'a, T: ?Sized, R: Relax> Deref for MutexGuard<'a, T, R> {
    type Target = T;

    /// Dereferences the guard to access the underlying data.
    fn deref(&self) -> &T {
        // SAFETY: A guard instance holds the lock locked.
        unsafe { &*self.lock.data_ptr() }
    }
}

#[cfg(not(all(loom, test)))]
impl<'a, T: ?Sized, R: Relax> DerefMut for MutexGuard<'a, T, R> {
    /// Mutably dereferences the guard to access the underlying data.
    fn deref_mut(&mut self) -> &mut T {
        // SAFETY: A guard instance holds the lock locked.
        unsafe { &mut *self.lock.data_ptr() }
    }
}

impl<'a, T: ?Sized + fmt::Debug, R: Relax> fmt::Debug for MutexGuard<'a, T, R> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.data_with(|data| fmt::Debug::fmt(data, f))
    }
}

impl<'a, T: ?Sized + fmt::Display, R: Relax> fmt::Display for MutexGuard<'a, T, R> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.data_with(|data| fmt::Display::fmt(data, f))
    }
}

/// SAFETY: A guard instance hold the lock locked, with exclusive access to the
/// underlying data.
#[cfg(all(loom, test))]
unsafe impl<'a, T: ?Sized, R: Relax> Guard<'a, T> for MutexGuard<'a, T, R> {
    type Guard = Self;

    fn deref(&'a self) -> GuardDeref<'a, T, Self::Guard> {
        GuardDeref::new(self.lock.data_get())
    }

    fn deref_mut(&'a self) -> GuardDerefMut<'a, T, Self::Guard> {
        GuardDerefMut::new(self.lock.data_get_mut())
    }
}

#[cfg(all(not(loom), test))]
mod test {
    // Test suite from the Rust's Mutex implementation with minor modifications
    // since the API is not compatible with this crate implementation and some
    // new tests as well.
    //
    // Copyright 2014 The Rust Project Developers.
    //
    // Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
    // http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
    // <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
    // option. This file may not be copied, modified, or distributed
    // except according to those terms.

    use std::sync::atomic::{AtomicUsize, Ordering};
    use std::sync::mpsc::channel;
    use std::sync::Arc;
    use std::thread;

    use crate::raw::yields::{Mutex, MutexNode};

    #[derive(Eq, PartialEq, Debug)]
    struct NonCopy(i32);

    #[test]
    fn smoke() {
        let mut node = MutexNode::new();
        let m = Mutex::new(());
        drop(m.lock(&mut node));
        drop(m.lock(&mut node));
    }

    #[test]
    fn lots_and_lots() {
        static LOCK: Mutex<u32> = Mutex::new(0);

        const ITERS: u32 = 1000;
        const CONCURRENCY: u32 = 3;

        fn inc() {
            let mut node = MutexNode::new();
            for _ in 0..ITERS {
                let mut g = LOCK.lock(&mut node);
                *g += 1;
            }
        }

        let (tx, rx) = channel();
        for _ in 0..CONCURRENCY {
            let tx2 = tx.clone();
            thread::spawn(move || {
                inc();
                tx2.send(()).unwrap();
            });
            let tx2 = tx.clone();
            thread::spawn(move || {
                inc();
                tx2.send(()).unwrap();
            });
        }

        drop(tx);
        for _ in 0..2 * CONCURRENCY {
            rx.recv().unwrap();
        }
        let mut node = MutexNode::new();
        assert_eq!(*LOCK.lock(&mut node), ITERS * CONCURRENCY * 2);
    }

    #[test]
    fn try_lock() {
        let mut node = MutexNode::new();
        let m = Mutex::new(());
        *m.try_lock(&mut node).unwrap() = ();
    }

    #[test]
    fn test_into_inner() {
        let m = Mutex::new(NonCopy(10));
        assert_eq!(m.into_inner(), NonCopy(10));
    }

    #[test]
    fn test_into_inner_drop() {
        struct Foo(Arc<AtomicUsize>);
        impl Drop for Foo {
            fn drop(&mut self) {
                self.0.fetch_add(1, Ordering::SeqCst);
            }
        }
        let num_drops = Arc::new(AtomicUsize::new(0));
        let m = Mutex::new(Foo(num_drops.clone()));
        assert_eq!(num_drops.load(Ordering::SeqCst), 0);
        {
            let _inner = m.into_inner();
            assert_eq!(num_drops.load(Ordering::SeqCst), 0);
        }
        assert_eq!(num_drops.load(Ordering::SeqCst), 1);
    }

    #[test]
    fn test_get_mut() {
        let mut m = Mutex::new(NonCopy(10));
        *m.get_mut() = NonCopy(20);
        assert_eq!(m.into_inner(), NonCopy(20));
    }

    #[test]
    fn test_lock_arc_nested() {
        // Tests nested locks and access
        // to underlying data.
        let arc = Arc::new(Mutex::new(1));
        let arc2 = Arc::new(Mutex::new(arc));
        let (tx, rx) = channel();
        let _t = thread::spawn(move || {
            let mut node1 = MutexNode::new();
            let mut node2 = MutexNode::new();

            let lock = arc2.lock(&mut node1);
            let lock2 = lock.lock(&mut node2);
            assert_eq!(*lock2, 1);
            tx.send(()).unwrap();
        });
        rx.recv().unwrap();
    }

    #[test]
    fn test_recursive_lock() {
        let arc = Arc::new(Mutex::new(1));
        let (tx, rx) = channel();
        for _ in 0..4 {
            let tx2 = tx.clone();
            let c_arc = Arc::clone(&arc);
            let _t = thread::spawn(move || {
                let mutex = Mutex::new(1);
                let mut node1 = MutexNode::new();
                let _lock = c_arc.lock(&mut node1);
                let mut node2 = MutexNode::new();
                let lock2 = mutex.lock(&mut node2);
                assert_eq!(*lock2, 1);
                tx2.send(()).unwrap();
            });
        }
        drop(tx);
        rx.recv().unwrap();
    }

    #[test]
    fn test_lock_arc_access_in_unwind() {
        let arc = Arc::new(Mutex::new(1));
        let arc2 = arc.clone();
        let _ = thread::spawn(move || -> () {
            struct Unwinder {
                i: Arc<Mutex<i32>>,
            }
            impl Drop for Unwinder {
                fn drop(&mut self) {
                    let mut node = MutexNode::new();
                    *self.i.lock(&mut node) += 1;
                }
            }
            let _u = Unwinder { i: arc2 };
            panic!();
        })
        .join();
        let mut node = MutexNode::new();
        let lock = arc.lock(&mut node);
        assert_eq!(*lock, 2);
    }

    #[test]
    fn test_lock_unsized() {
        let mut node = MutexNode::new();
        let lock: &Mutex<[i32]> = &Mutex::new([1, 2, 3]);
        {
            let b = &mut *lock.lock(&mut node);
            b[0] = 4;
            b[2] = 5;
        }
        let comp: &[i32] = &[4, 2, 5];
        assert_eq!(&*lock.lock(&mut node), comp);
    }
}

#[cfg(all(loom, test))]
mod test {
    use loom::{model, thread};

    use crate::loom::Guard;
    use crate::raw::yields::{Mutex, MutexNode};

    #[test]
    fn threads_join() {
        use core::ops::Range;
        use loom::sync::Arc;

        fn inc(lock: Arc<Mutex<i32>>) {
            let mut node = MutexNode::new();
            let guard = lock.lock(&mut node);
            *guard.deref_mut() += 1;
        }

        model(|| {
            let data = Arc::new(Mutex::new(0));
            // 3 or more threads make this model run for too long.
            let runs @ Range { end, .. } = 0..2;

            let handles = runs
                .into_iter()
                .map(|_| Arc::clone(&data))
                .map(|data| thread::spawn(move || inc(data)))
                .collect::<Vec<_>>();

            for handle in handles {
                handle.join().unwrap();
            }

            let mut node = MutexNode::new();
            assert_eq!(end, *data.lock(&mut node).deref());
        });
    }

    #[test]
    fn threads_fork() {
        // Using std's Arc or else this model runs for loo long.
        use std::sync::Arc;

        fn inc(lock: Arc<Mutex<i32>>) {
            let mut node = MutexNode::new();
            let guard = lock.lock(&mut node);
            *guard.deref_mut() += 1;
        }

        model(|| {
            let data = Arc::new(Mutex::new(0));
            // 4 or more threads make this model run for too long.
            for _ in 0..3 {
                let data = Arc::clone(&data);
                thread::spawn(move || inc(data));
            }
        });
    }
}
