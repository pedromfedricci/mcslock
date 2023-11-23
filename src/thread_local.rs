//! A MCS lock implementation that stores queue nodes in the thread local
//! storage of the waiting threads.
//!
//! This module provide MCS locking APIs that do not require user-side node
//! instantiation, by managing the queue's nodes allocations internally. Queue
//! nodes are stored in the thread local storage, therefore this implementation
//! requires support from the standard library.

use core::fmt;

#[cfg(not(all(loom, test)))]
use core::cell::UnsafeCell;

#[cfg(all(loom, test))]
use crate::raw::{MutexGuardDeref, MutexGuardDerefMut};
#[cfg(all(loom, test))]
use loom::cell::UnsafeCell;

use crate::raw::{Mutex as RawMutex, MutexGuard, MutexNode};

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
/// use mcslock::thread_local::Mutex;
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
///         // The shared state can only be accessed once the lock is held.
///         // Our non-atomic increment is safe because we're the only thread
///         // which can access the shared state when the lock is held.
///         //
///         // We unwrap() the return value to assert that we are not expecting
///         // threads to ever fail while holding the lock.
///         let mut data = data.lock();
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
pub struct Mutex<T: ?Sized>(RawMutex<T>);

impl<T> Mutex<T> {
    /// Creates a new mutex in an unlocked state ready for use.
    ///
    /// # Examples
    ///
    /// ```
    /// use mcslock::Mutex;
    ///
    /// const MUTEX: Mutex<i32> = Mutex::new(0);
    /// let mutex = Mutex::new(0);
    /// ```
    #[cfg(not(all(loom, test)))]
    #[inline]
    pub const fn new(value: T) -> Mutex<T> {
        Self(RawMutex::new(value))
    }

    /// Creates a new unlocked mutex with Loom primitives (non-const).
    #[cfg(all(loom, test))]
    fn new(value: T) -> Mutex<T> {
        Self(RawMutex::new(value))
    }

    /// Consumes this mutex, returning the underlying data.
    ///
    /// # Examples
    ///
    /// ```
    /// use mcslock::Mutex;
    ///
    /// let mutex = Mutex::new(0);
    /// assert_eq!(mutex.into_inner(), 0);
    /// ```
    #[inline]
    pub fn into_inner(self) -> T {
        self.0.into_inner()
    }
}

impl<T: ?Sized> Mutex<T> {
    /// Runs `f` over the inner mutex and the thread local node.
    ///
    /// # Safety
    ///
    /// The node pointer must not escape the closure, and node mutations must
    /// guarantee serialization.
    #[cfg(not(all(loom, test)))]
    unsafe fn node_with<F, R>(&self, f: F) -> R
    where
        F: FnOnce(&RawMutex<T>, &mut MutexNode) -> R,
    {
        std::thread_local! {
            static NODE: UnsafeCell<MutexNode> = const {
                UnsafeCell::new(MutexNode::new())
            }
        }
        NODE.with(|node| f(&self.0, unsafe { &mut *node.get() }))
    }

    /// Runs `f` over the inner Loom based mutex and the thread local node.
    ///
    /// # Safety
    ///
    /// The node pointer must not escape the closure, and node mutations must
    /// guarantee serialization.
    #[cfg(all(loom, test))]
    unsafe fn node_with<F, R>(&self, f: F) -> R
    where
        F: FnOnce(&RawMutex<T>, &mut MutexNode) -> R,
    {
        loom::thread_local! {
            static NODE: UnsafeCell<MutexNode> = {
                UnsafeCell::new(MutexNode::new())
            }
        }
        NODE.with(|node| node.with_mut(|node| f(&self.0, unsafe { &mut *node })))
    }

    /// Attempts to acquire this lock.
    ///
    /// If the lock could not be acquired at this time, then [`None`] is returned.
    /// Otherwise, an RAII guard is returned. The lock will be unlocked when the
    /// guard is dropped.
    ///
    /// This function does not block.
    pub fn try_lock_with<F, R>(&self, f: F) -> R
    where
        F: FnOnce(Option<&mut MutexGuard<'_, T>>) -> R,
    {
        unsafe { self.node_with(|raw, node| f(raw.try_lock(node).as_mut())) }
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
    /// use mcslock::Mutex;
    ///
    /// let mutex = Arc::new(Mutex::new(0));
    /// let c_mutex = Arc::clone(&mutex);
    ///
    /// thread::spawn(move || {
    ///     *c_mutex.lock() = 10;
    /// })
    /// .join().expect("thread::spawn failed");
    ///
    /// assert_eq!(*mutex.lock(), 10);
    /// ```
    pub fn lock_with<F, R>(&self, f: F) -> R
    where
        F: FnOnce(&mut MutexGuard<'_, T>) -> R,
    {
        unsafe { self.node_with(|raw, node| f(&mut raw.lock(node))) }
    }

    /// Returns `true` if the lock is currently held.
    ///
    /// This method does not provide any synchronization guarantees, so its only
    /// useful as a heuristic, and so must be considered not up to date.
    ///
    /// # Example
    ///
    /// ```
    /// use mcslock::Mutex;
    ///
    /// let mutex = Mutex::new(0);
    ///
    /// let guard = mutex.lock();
    /// drop(guard);
    ///
    /// assert_eq!(mutex.is_locked(), false);
    /// ```
    #[inline]
    pub fn is_locked(&self) -> bool {
        self.0.is_locked()
    }

    /// Returns a mutable reference to the underlying data.
    ///
    /// Since this call borrows the `Mutex` mutably, no actual locking needs to
    /// take place - the mutable borrow statically guarantees no locks exist.
    ///
    /// # Examples
    ///
    /// ```
    /// use mcslock::Mutex;
    ///
    /// let mut mutex = Mutex::new(0);
    /// *mutex.get_mut() = 10;
    ///
    /// assert_eq!(*mutex.lock(), 10);
    /// ```
    #[cfg(not(all(loom, test)))]
    #[inline]
    pub fn get_mut(&mut self) -> &mut T {
        self.0.get_mut()
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
    fn from(data: T) -> Mutex<T> {
        Mutex::new(data)
    }
}

impl<T: ?Sized + fmt::Debug> fmt::Debug for Mutex<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut d = f.debug_struct("Mutex");
        self.try_lock_with(|guard| match guard {
            Some(g) => g.data_with(|data| d.field("data", &data)),
            None => d.field("data", &format_args!("<locked>")),
        });
        d.field("tail", self.0.tail());
        d.finish()
    }
}

#[cfg(all(not(loom), test))]
mod test {
    use super::Mutex;
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
        let m = Mutex::new(1);
        let data = m.lock_with(|guard| **guard);
        assert_eq!(data, 1);
        m.lock_with(|guard| **guard = 2);
        let data = m.lock_with(|guard| **guard);
        assert_eq!(data, 2);
    }

    // #[test]
    // fn should_not_compile() {
    //     let m = Mutex::new(1);
    //     let guard = m.lock_with(|guard| guard);
    //     let _value = *guard;

    //     let m = Mutex::new(1);
    //     let _val = m.lock_with(|guard| &mut **guard);

    //     let m = Mutex::new(1);
    //     let _val = m.lock_with(|guard| &**guard);
    // }

    #[test]
    fn lots_and_lots() {
        static LOCK: Mutex<u32> = Mutex::new(0);

        const ITERS: u32 = 1000;
        const CONCURRENCY: u32 = 3;

        fn inc() {
            for _ in 0..ITERS {
                LOCK.lock_with(|data| **data += 1);
                LOCK.lock_with(|data| **data += 1);
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
        let data = LOCK.lock_with(|data| **data);
        assert_eq!(data, ITERS * CONCURRENCY * 2 * 2);
    }

    #[test]
    fn test_try_lock() {
        let m = Mutex::new(());
        let val = m.try_lock_with(|g| g.map(|_| ())).unwrap();
        assert_eq!(val, ());
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

    // TODO: this must panic, else it's UB.
    #[test]
    fn test_lock_arc_nested() {
        // Tests nested locks and access
        // to underlying data.
        let arc = Arc::new(Mutex::new(1));
        let arc2 = Arc::new(Mutex::new(arc));
        let (tx, rx) = channel();
        let _t = thread::spawn(move || {
            let val = arc2.lock_with(|arc2| arc2.lock_with(|g| **g));
            assert_eq!(val, 1);
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
                    self.i.lock_with(|g| **g += 1);
                }
            }
            let _u = Unwinder { i: arc2 };
            panic!();
        })
        .join();
        let value = arc.lock_with(|g| **g);
        assert_eq!(value, 2);
    }

    #[test]
    fn test_lock_unsized() {
        let lock: &Mutex<[i32]> = &Mutex::new([1, 2, 3]);
        {
            lock.lock_with(|g| {
                g[0] = 4;
                g[2] = 5;
            });
        }
        let comp: &[i32] = &[4, 2, 5];
        lock.lock_with(|g| assert_eq!(&**g, comp));
    }
}

#[cfg(all(loom, test))]
mod test {
    use super::Mutex;
    use loom::{model, thread};

    #[test]
    fn threads_join() {
        use core::ops::Range;
        use loom::sync::Arc;

        fn inc(lock: Arc<Mutex<i32>>) {
            let mut guard = lock.lock().deref_mut();
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

            assert_eq!(end, *data.lock().deref());
        });
    }

    #[test]
    fn threads_fork() {
        // Using std's Arc or else this model runs for loo long.
        use std::sync::Arc;

        fn inc(lock: Arc<Mutex<i32>>) {
            let mut guard = lock.lock().deref_mut();
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
