//! Raw locking APIs require exclusive access to a local queue node. This node is
//! represented by the `MutexNode` type.
//!
//! The `raw` module provides `no_std` compatible interfaces but also requires
//! that queue nodes must be instantiated by the callers.

use core::fmt;
use core::mem::MaybeUninit;
use core::ops::{Deref, DerefMut};
use core::ptr;
use core::sync::atomic::Ordering::{AcqRel, Acquire, Relaxed, Release};

#[cfg(not(all(loom, test)))]
use core::cell::UnsafeCell;
#[cfg(not(all(loom, test)))]
use core::sync::atomic::{fence, AtomicBool, AtomicPtr};

#[cfg(all(loom, test))]
use core::marker::PhantomData;
#[cfg(all(loom, test))]
use loom::cell::{ConstPtr, MutPtr, UnsafeCell};
#[cfg(all(loom, test))]
use loom::sync::atomic::{fence, AtomicBool, AtomicPtr};

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
#[derive(Debug)]
pub struct MutexNode {
    next: MaybeUninit<AtomicPtr<AtomicBool>>,
}

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
    pub const fn new() -> MutexNode {
        MutexNode { next: MaybeUninit::uninit() }
    }

    /// Writes a null mutable raw pointer into `self.next`.
    fn next_write_null(&mut self) {
        self.next.write(AtomicPtr::new(ptr::null_mut()));
    }

    /// Returns a reference of `self.next`.
    ///
    /// # Safety
    ///
    /// User must garantee that `self.next` has been previously initialized.
    unsafe fn next_assume_init_ref(&self) -> &AtomicPtr<AtomicBool> {
        unsafe { self.next.assume_init_ref() }
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
///
/// const N: usize = 10;
///
/// // Spawn a few threads to increment a shared variable (non-atomically), and
/// // let the main thread know once all increments are done.
/// //
/// // Here we're using an Arc to share memory among threads, and the data inside
/// // the Arc is protected with a mutex.
/// let data = Arc::new(Mutex::new(0));
///
/// let (tx, rx) = channel();
/// for _ in 0..N {
///     let (data, tx) = (data.clone(), tx.clone());
///     thread::spawn(move || {
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
/// let _message = rx.recv();
///
/// // A queue node must be mutably accessible.
/// let mut node = MutexNode::new();
/// // Would return `None` if lock was already held.
/// let count = data.try_lock(&mut node).unwrap();
/// assert_eq!(N, *count);
/// // lock is unlock here when `count` goes out of scope.
/// ```
/// [`new`]: crate::raw::Mutex::new
/// [`lock`]: crate::raw::Mutex::lock
/// [`try_lock`]: crate::raw::Mutex::try_lock
pub struct Mutex<T: ?Sized> {
    tail: AtomicPtr<MutexNode>,
    data: UnsafeCell<T>,
}

unsafe impl<T: ?Sized + Send> Sync for Mutex<T> {}
unsafe impl<T: ?Sized + Send> Send for Mutex<T> {}

impl<T> Mutex<T> {
    /// Creates a new mutex in an unlocked state ready for use.
    ///
    /// # Examples
    ///
    /// ```
    /// use mcslock::raw::Mutex;
    ///
    /// const MUTEX: Mutex<i32> = Mutex::new(0);
    /// let mutex = Mutex::new(0);
    /// ```
    #[cfg(not(all(loom, test)))]
    #[inline]
    pub const fn new(value: T) -> Mutex<T> {
        let tail = AtomicPtr::new(ptr::null_mut());
        let data = UnsafeCell::new(value);
        Mutex { tail, data }
    }

    /// Creates a new mutex with Loom primitives (non-const).
    #[cfg(all(loom, test))]
    fn new(value: T) -> Mutex<T> {
        let tail = AtomicPtr::new(ptr::null_mut());
        let data = UnsafeCell::new(value);
        Mutex { tail, data }
    }

    /// Consumes this mutex, returning the underlying data.
    ///
    /// # Examples
    ///
    /// ```
    /// use mcslock::raw::Mutex;
    ///
    /// let mutex = Mutex::new(0);
    /// assert_eq!(mutex.into_inner(), 0);
    /// ```
    #[inline]
    pub fn into_inner(self) -> T {
        self.data.into_inner()
    }
}

impl<T: ?Sized> Mutex<T> {
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
    ///
    /// let mutex = Arc::new(Mutex::new(0));
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
    pub fn try_lock<'a>(&'a self, node: &'a mut MutexNode) -> Option<MutexGuard<'a, T>> {
        // SAFETY: We have exclusive access to the queue node.
        unsafe { self.try_lock_raw(node) }
    }

    /// Attempts to acquire this lock.
    ///
    /// # Safety
    ///
    /// This requires exclusive access to the queue node.
    pub(crate) unsafe fn try_lock_raw(&self, node: *mut MutexNode) -> Option<MutexGuard<'_, T>> {
        // Must initialize `node.next` before any possible access to it.
        unsafe { &mut *node }.next_write_null();

        self.tail
            .compare_exchange(ptr::null_mut(), node, Acquire, Relaxed)
            .map(|_| MutexGuard::new(self, unsafe { &*node }))
            .ok()
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
    ///
    /// let mutex = Arc::new(Mutex::new(0));
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
    pub fn lock<'a>(&'a self, node: &'a mut MutexNode) -> MutexGuard<'a, T> {
        // SAFETY: We have exclusive access to the queue node.
        unsafe { self.lock_raw(node) }
    }

    /// Acquires a mutex, blocking the current thread until it is able to do so.
    ///
    /// # Safety
    ///
    /// This requires exclusive access to the queue node.
    pub(crate) unsafe fn lock_raw(&self, node: *mut MutexNode) -> MutexGuard<'_, T> {
        // Must initialize `node.next` before any possible access to it.
        unsafe { &mut *node }.next_write_null();
        let pred = self.tail.swap(node, AcqRel);

        // We do have a predecessor, complete the link so it will notify us.
        if !pred.is_null() {
            let locked = AtomicBool::new(true);
            // SAFETY: we already checked that `pred` is not null, it's `next`
            // has already been inialized by either `lock` or `try_lock`,
            // and we do not dereference `next`, only write into it.
            let next = unsafe { (*pred).next_assume_init_ref() };
            next.store(&locked as *const _ as *mut _, Release);

            while locked.load(Relaxed) {
                wait();
            }
            fence(Acquire);
        }

        MutexGuard::new(self, unsafe { &*node })
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
    ///
    /// let mut mutex = Mutex::new(0);
    /// *mutex.get_mut() = 10;
    ///
    /// let mut node = MutexNode::new();
    /// assert_eq!(*mutex.lock(&mut node), 10);
    /// ```
    #[cfg(not(all(loom, test)))]
    #[inline]
    pub fn get_mut(&mut self) -> &mut T {
        // SAFETY: We hold exclusive access to the Mutex data.
        unsafe { &mut *self.data.get() }
    }
}

impl<T: ?Sized + Default> Default for Mutex<T> {
    /// Creates a `Mutex<T>`, with the `Default` value for `T`.
    fn default() -> Mutex<T> {
        Mutex::new(Default::default())
    }
}

impl<T> From<T> for Mutex<T> {
    /// Creates a `Mutex<T>` from a instance of `T`.
    fn from(data: T) -> Self {
        Self::new(data)
    }
}

impl<T: ?Sized + fmt::Debug> fmt::Debug for Mutex<T> {
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
pub struct MutexGuard<'a, T: ?Sized> {
    lock: &'a Mutex<T>,
    node: &'a MutexNode,
}

impl<'a, T: ?Sized> MutexGuard<'a, T> {
    /// Creates a new `MutexGuard` instance.
    fn new(lock: &'a Mutex<T>, node: &'a MutexNode) -> Self {
        Self { lock, node }
    }

    /// Dequeues the current node as the queue's tail, if it is in fact the tail.
    /// If returns `true`, then node was the queue's tail, and now the queue is
    /// empty. Returns `false` if the tail points somewhere else.
    fn dequeue(&self) -> bool {
        let node = self.node as *const _ as *mut _;
        self.lock.tail.compare_exchange(node, ptr::null_mut(), Release, Relaxed).is_ok()
    }

    /// Runs `f` with an immutable reference to the wrapped value.
    #[cfg(not(all(loom, test)))]
    fn data_with<F, R>(&self, f: F) -> R
    where
        F: FnOnce(&T) -> R,
    {
        // SAFETY: A guard instance holds the lock locked.
        f(unsafe { &*self.lock.data.get() })
    }

    /// Runs `f` with an immutable reference to the wrapped value.
    #[cfg(all(loom, test))]
    fn data_with<F, R>(&self, f: F) -> R
    where
        F: FnOnce(&T) -> R,
    {
        // SAFETY: A guard instance holds the lock locked.
        f(unsafe { self.lock.data.get().deref() })
    }

    /// Get a Loom immutable data pointer that borrows from this guard.
    #[cfg(all(loom, test))]
    fn deref(&self) -> MutexGuardDeref<'a, T> {
        MutexGuardDeref::new(self.lock.data.get())
    }

    /// Get a Loom mutable data pointer that mutably borrows from this guard.
    #[cfg(all(loom, test))]
    fn deref_mut(&mut self) -> MutexGuardDerefMut<'a, T> {
        MutexGuardDerefMut::new(self.lock.data.get_mut())
    }
}

#[cfg(not(all(loom, test)))]
impl<'a, T: ?Sized> Deref for MutexGuard<'a, T> {
    type Target = T;

    /// Dereferences the guard to access the underlying data.
    fn deref(&self) -> &T {
        // SAFETY: A guard instance holds the lock locked.
        unsafe { &*self.lock.data.get() }
    }
}

#[cfg(not(all(loom, test)))]
impl<'a, T: ?Sized> DerefMut for MutexGuard<'a, T> {
    /// Mutably dereferences the guard to access the underlying data.
    fn deref_mut(&mut self) -> &mut T {
        // SAFETY: A guard instance holds the lock locked.
        unsafe { &mut *self.lock.data.get() }
    }
}

impl<'a, T: ?Sized + fmt::Debug> fmt::Debug for MutexGuard<'a, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.data_with(|data| fmt::Debug::fmt(data, f))
    }
}

impl<'a, T: ?Sized + fmt::Display> fmt::Display for MutexGuard<'a, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.data_with(|data| fmt::Display::fmt(data, f))
    }
}

impl<'a, T: ?Sized> Drop for MutexGuard<'a, T> {
    fn drop(&mut self) {
        // SAFETY: `MutexGuard` can only be constructed by either `lock` or
        // `try_lock`, and both must have initialized `self.node.next`.
        let next = unsafe { self.node.next_assume_init_ref() };
        let mut locked = next.load(Relaxed);

        // If we don't have a successor currently,
        if locked.is_null() {
            // and we are the tail, then dequeue and free the lock.
            let false = self.dequeue() else { return };

            // But if we are not the tail, then we have a pending successor.
            while locked.is_null() {
                wait();
                locked = next.load(Relaxed);
            }
        }

        fence(Acquire);
        // SAFETY: Already verified that successor is not null.
        let locked = unsafe { &*locked };
        locked.store(false, Release);
    }
}

/// A Loom immutable pointer borrowed from a [`MutexGuard`] instance.
#[cfg(all(loom, test))]
struct MutexGuardDeref<'a, T: ?Sized> {
    ptr: ConstPtr<T>,
    marker: PhantomData<&'a MutexGuard<'a, T>>,
}

#[cfg(all(loom, test))]
impl<'a, T: ?Sized> MutexGuardDeref<'a, T> {
    fn new(ptr: ConstPtr<T>) -> Self {
        Self { ptr, marker: PhantomData }
    }
}

#[cfg(all(loom, test))]
impl<'a, T: ?Sized> Deref for MutexGuardDeref<'a, T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        // SAFETY: Our lifetime is bounded by the guard borrow.
        unsafe { self.ptr.deref() }
    }
}

/// A Loom mutable pointer mutably borrowed from a [`MutexGuard`] instance.
#[cfg(all(loom, test))]
struct MutexGuardDerefMut<'a, T: ?Sized> {
    ptr: MutPtr<T>,
    marker: PhantomData<&'a mut MutexGuard<'a, T>>,
}

#[cfg(all(loom, test))]
impl<'a, T: ?Sized> MutexGuardDerefMut<'a, T> {
    fn new(ptr: MutPtr<T>) -> Self {
        Self { ptr, marker: PhantomData }
    }
}

#[cfg(all(loom, test))]
impl<'a, T: ?Sized> Deref for MutexGuardDerefMut<'a, T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        // SAFETY: Our lifetime is bounded by the guard's borrow.
        unsafe { self.ptr.deref() }
    }
}

#[cfg(all(loom, test))]
impl<'a, T> DerefMut for MutexGuardDerefMut<'a, T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        // SAFETY: Our lifetime is bounded by the guard's borrow.
        unsafe { self.ptr.deref() }
    }
}

/// This strategy cooperatively gives up a timeslice to the OS scheduler.
/// Requires that `std` feature is enabled and therefore it is not suitable
/// for `no_std` environments as it links to the `std` library.
#[cfg(all(feature = "yield", not(loom)))]
fn wait() {
    std::thread::yield_now();
}

/// This strategy yields the current thread execution to the loom executor
/// so it can eventually work on the thread that we are waiting on to make
/// progress.
#[cfg(all(loom, test))]
fn wait() {
    loom::thread::yield_now();
}

/// This strategy emits machine instruction to signal the processor that it is
/// running in a busy-wait spin-loop. Does not require linking to the `std`
/// library, so it is suitable for `no_std` environments.
#[cfg(all(not(feature = "yield"), not(loom)))]
fn wait() {
    core::hint::spin_loop();
}

#[cfg(all(not(loom), test))]
mod test {
    use super::{Mutex, MutexNode};
    // Test suite from the Rust's Mutex implementation with minor modifications
    // since the API is not compatible with this crate implementation.
    use std::sync::atomic::{AtomicUsize, Ordering};
    use std::sync::mpsc::channel;
    use std::sync::Arc;
    use std::thread;

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
    use super::{Mutex, MutexNode};
    use loom::{model, thread};

    #[test]
    fn threads_join() {
        use core::ops::Range;
        use loom::sync::Arc;

        fn inc(lock: Arc<Mutex<i32>>) {
            let mut node = MutexNode::new();
            let mut guard = lock.lock(&mut node).deref_mut();
            *guard += 1;
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
            let mut guard = lock.lock(&mut node).deref_mut();
            *guard += 1;
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
