//! A simple and correct implementation of Mellor-Crummey and Scott
//! contention-free [spin-lock] for mutual exclusion, referred to as MCS lock.
//!
//! MCS lock is a List-Based Queuing Lock that avoids network contention by
//! having threads spin on local memory locations. The main properties of this
//! mechanism are:
//!
//! - guarantees FIFO ordering of lock acquisitions;
//! - spins on locally-accessible flag variables only;
//! - requires a small constant amount of space per lock; and
//! - works equally well (requiring only O(1) network transactions per lock
//!   acquisition) on machines with and without coherent caches.
//!
//! This algorithm and serveral others were introduced by [Mellor-Crummey and Scott] paper.
//! And a simpler correctness proof of the MCS lock was proposed by [Johnson and Harathi].
//!
//! ## Use cases
//!
//! [Spinlocks are usually not what you want]. The majority of use cases are well
//! covered by OS-based mutexes like [`std::sync::Mutex`] or [`parking_lot::Mutex`].
//! These implementations will notify the system that the waiting thread should
//! be parked, freeing the processor to work on something else.
//!
//! Spinlocks are only efficient in very few circunstances where the overhead
//! of context switching or process rescheduling are greater than busy waiting
//! for very short periods. Spinlocks can be useful inside operating-system kernels,
//! on embedded systems or even complement other locking designs. As a reference
//! use case, some [Linux kernel mutexes] run an customized MCS lock specifically
//! tailored for optimistic spinning during contention before actually sleeping.
//! This implementation is `no_std` by default, so it's useful in those environments.
//!
//! ## API compatibility
//!
//! The locking interface of a MCS lock is not quite the same as other mutexes.
//! To acquire a MCS lock, a queue record must be mutably accessible for the
//! durating of the [`lock`] and [`try_lock`] calls. This record is exposed as
//! the [`MutexNode`] type. See their documentation for more information.
//! If you are looking for spin-based primitives that are compatible with
//! [lock_api], consider using [spin-rs], which is also suitable for `no_std`.
//!
//! ## Features
//!
//! This crate dos not provide any default features. Features that can be enabled
//! are:
//!
//! ### yield
//!
//! The `yield` feature requires linking to the standard library, so it is not
//! suitable for `no_std` environments. By enabling the `yield` feature, instead
//! of busy-waiting during lock acquisitions and releases, this will call
//! [`std::thread::yield_now`], which cooperatively gives up a timeslice to the
//! OS scheduler. This may cause a context switch, so you may not want to enable
//! this feature if your intention is to to actually do optimistic spinning. The
//! default implementation calls [`core::hint::spin_loop`], which does in fact
//! just simply busy-waits.
//!
//! ## Related projects
//!
//! These projects provide MCS lock implementations with slightly different APIs,
//! implementation details or compiler requirements, you can check their
//! repositories:
//!
//! - `mcs-rs`: <https://github.com/gereeter/mcs-rs>
//! - `libmcs`: <https://github.com/topecongiro/libmcs>
//!
//! [`lock`]: Mutex::lock
//! [`try_lock`]: Mutex::try_lock
//! [`std::sync::Mutex`]: https://doc.rust-lang.org/std/sync/struct.Mutex.html
//! [`parking_lot::Mutex`]: https://docs.rs/parking_lot/latest/parking_lot/type.Mutex.html
//! [`std::thread::yield_now`]: https://doc.rust-lang.org/std/thread/fn.yield_now.html
//! [spin-lock]: https://en.wikipedia.org/wiki/Spinlock
//! [spin-rs]: https://docs.rs/spin/latest/spin
//! [lock_api]: https://docs.rs/lock_api/latest/lock_api
//! [Linux kernel mutexes]: https://www.kernel.org/doc/html/latest/locking/mutex-design.html
//! [Spinlocks are usually not what you want]: https://matklad.github.io/2020/01/02/spinlocks-considered-harmful.html
//! [Mellor-Crummey and Scott]: https://www.cs.rochester.edu/~scott/papers/1991_TOCS_synch.pdf
//! [Johnson and Harathi]: https://web.archive.org/web/20140411142823/http://www.cise.ufl.edu/tr/DOC/REP-1992-71.pdf

#![cfg_attr(all(not(feature = "yield"), not(test)), no_std)]
#![warn(missing_docs)]

use core::cell::UnsafeCell;
use core::fmt;
use core::mem::MaybeUninit;
use core::ops::{Deref, DerefMut};
use core::ptr;
use core::sync::atomic::Ordering::{AcqRel, Acquire, Relaxed, Release};
use core::sync::atomic::{fence, AtomicBool, AtomicPtr};

/// A locally-accessible record for forming the waiting queue.
///
/// `MutexNode` is an opaque type that holds metadata for the [`Mutex`]'s
/// wainting queue. To acquire a MCS lock, an instance of queue node must be
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
    /// use mcslock::MutexNode;
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
    /// User must garantee that `self.next` has been previously written into
    /// before calling this function. If `self.next` memory is not initialized
    /// and this function is called, that will cause undefined behaviour.
    unsafe fn next_assume_init_ref(&self) -> &AtomicPtr<AtomicBool> {
        self.next.assume_init_ref()
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
/// use mcslock::{Mutex, MutexNode};
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
///
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
    /// use mcslock::Mutex;
    ///
    /// let mutex = Mutex::new(0);
    /// ```
    #[inline]
    pub const fn new(value: T) -> Mutex<T> {
        let tail = AtomicPtr::new(ptr::null_mut());
        let data = UnsafeCell::new(value);
        Mutex { tail, data }
    }

    /// Consumes this mutex, returning the underlying data.
    ///
    /// # Examples
    ///
    /// ```
    /// use mcslock::Mutex;
    ///
    /// let mutex = Mutex::new(0);
    /// assert_eq!(mutex.into_inner().unwrap(), 0);
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
    /// use mcslock::{Mutex, MutexNode};
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
        // Must initialize `node.next` before any possible access to it.
        node.next_write_null();

        self.tail
            .compare_exchange(ptr::null_mut(), node, Acquire, Relaxed)
            .map(|_| MutexGuard::new(self, node))
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
    /// use mcslock::{Mutex, MutexNode};
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
        // Must initialize `node.next` before any possible access to it.
        node.next_write_null();
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

        MutexGuard::new(self, node)
    }

    /// Returns a mutable reference to the underlying data.
    ///
    /// Since this call borrows the `Mutex` mutably, no actual locking needs to
    /// take place - the mutable borrow statically guarantees no locks exist.
    ///
    /// # Examples
    ///
    /// ```
    /// use mcslock::{Mutex, MutexNode};
    ///
    /// let mut mutex = Mutex::new(0);
    /// *mutex.get_mut() = 10;
    ///
    /// let mut node = MutexNode::new();
    /// assert_eq!(*mutex.lock(&mut node), 10);
    /// ```
    #[inline]
    pub fn get_mut(&mut self) -> &mut T {
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
            Some(guard) => d.field("data", &&*guard),
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

    /// Returns a reference to the tail's atomic pointer.
    fn tail(&self) -> &AtomicPtr<MutexNode> {
        &self.lock.tail
    }

    /// Dequeues the current node as the queue's tail, if it is in fact the tail.
    /// If returns `true`, then node was the queue's tail, and now the queue is
    /// empty. Returns `false` if the tail points somewhere else.
    fn dequeue(&self) -> bool {
        let node = self.node as *const _ as *mut _;
        self.tail().compare_exchange(node, ptr::null_mut(), Release, Relaxed).is_ok()
    }

    /// Returns a raw `self.data` pointer.
    fn data_ptr(&self) -> *mut T {
        self.lock.data.get()
    }
}

impl<'a, T: ?Sized> Deref for MutexGuard<'a, T> {
    type Target = T;

    /// Dereferences the guard to access the underlying data.
    fn deref(&self) -> &T {
        unsafe { &*self.data_ptr() }
    }
}

impl<'a, T: ?Sized> DerefMut for MutexGuard<'a, T> {
    /// Mutably dereferences the guard to access the underlying data.
    fn deref_mut(&mut self) -> &mut T {
        unsafe { &mut *self.data_ptr() }
    }
}

impl<'a, T: ?Sized + fmt::Debug> fmt::Debug for MutexGuard<'a, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&**self, f)
    }
}

impl<'a, T: ?Sized + fmt::Display> fmt::Display for MutexGuard<'a, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&**self, f)
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

/// This strategy cooperatively gives up a timeslice to the OS scheduler.
/// Requires that `std` feature is enabled and therefore it is not suitable
/// for `no_std` environments as it links to the `std` library.
#[cfg(feature = "yield")]
fn wait() {
    std::thread::yield_now();
}

/// This strategy emits machine instruction to signal the processor that it is
/// running in a busy-wait spin-loop. Does not require linking to the `std`
/// library, so it is suitable for `no_std` environments.
#[cfg(not(feature = "yield"))]
fn wait() {
    core::hint::spin_loop();
}

#[cfg(test)]
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
