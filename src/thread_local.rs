//! A MCS lock implementation that stores queue nodes in the thread local
//! storage of the waiting threads.
//!
//! This module provide MCS locking APIs that do not require user-side node
//! instantiation, by managing the queue's nodes allocations internally. Queue
//! nodes are stored in the thread local storage, therefore this implementation
//! requires support from the standard library. The critical sections must be
//! provided to [`lock_with`] and [`try_lock_with`] as closures. Closure arguments
//! provide a reference to a RAII guard that has exclusive over the data. These
//! guards will be dropped at the end of the call, freeing the mutex.
//!
//! # Panics
//!
//! The `thread_local` [`Mutex`] implementation does not allow recursive locking,
//! doing so will cause a panic. See [`lock_with`] and [`try_lock_with`] functions
//! for more information.
//!
//! [`lock_with`]: Mutex::lock_with
//! [`try_lock_with`]: Mutex::try_lock_with

use core::fmt;
use core::{cell::RefCell, marker::PhantomData};

#[cfg(not(all(loom, test)))]
use core::ops::{Deref, DerefMut};

#[cfg(all(loom, test))]
use crate::raw::{MutexGuardDeref, MutexGuardDerefMut};

use crate::raw::{Mutex as RawMutex, MutexGuard as RawMutexGuard, MutexNode};

/// A mutual exclusion primitive useful for protecting shared data.
///
/// This mutex will block threads waiting for the lock to become available. The
/// mutex can also be statically initialized or created via a [`new`]
/// constructor. Each mutex has a type parameter which represents the data that
/// it is protecting. The data can only be accessed through the RAII guards
/// provided as closure arguments from [`lock_with`] and [`try_lock_with`], which
/// guarantees that the data is only ever accessed when the mutex is locked.
///
/// # Panics
///
/// The `thread_local` [`Mutex`] implementation does not allow recursive locking,
/// doing so will cause a panic. See [`lock_with`] and [`try_lock_with`] functions
/// for more information.
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
///         //
///         // Data is exclusively accessed by the guard argument.
///         data.lock_with(|data| {
///             **data += 1;
///             if **data == N {
///                 tx.send(()).unwrap();
///             }
///             // the lock is unlocked here when `data` goes out of scope.
///         })
///     });
/// }
///
/// rx.recv().unwrap();
/// ```
/// [`new`]: Mutex::new
/// [`lock_with`]: Mutex::lock_with
/// [`try_lock_with`]: Mutex::try_lock_with
pub struct Mutex<T: ?Sized>(RawMutex<T>);

impl<T> Mutex<T> {
    /// Creates a new mutex in an unlocked state ready for use.
    ///
    /// # Examples
    ///
    /// ```
    /// use mcslock::thread_local::Mutex;
    ///
    /// const MUTEX: Mutex<i32> = Mutex::new(0);
    /// let mutex = Mutex::new(0);
    /// ```
    #[cfg(not(all(loom, test)))]
    #[inline]
    pub const fn new(value: T) -> Self {
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
    /// use mcslock::thread_local::Mutex;
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
    #[cfg(not(all(loom, test)))]
    fn node_with<F, R>(&self, f: F) -> R
    where
        F: FnOnce(&RawMutex<T>, &mut MutexNode) -> R,
    {
        std::thread_local! {
            static NODE: RefCell<MutexNode> = const {
                RefCell::new(MutexNode::new())
            }
        }
        NODE.with(|node| f(&self.0, &mut node.borrow_mut()))
    }

    #[cfg(all(loom, test))]
    fn node_with<F, R>(&self, f: F) -> R
    where
        F: FnOnce(&RawMutex<T>, &mut MutexNode) -> R,
    {
        loom::thread_local! {
            static NODE: RefCell<MutexNode> = {
                RefCell::new(MutexNode::new())
            }
        }
        NODE.with(|node| f(&self.0, &mut node.borrow_mut()))
    }

    /// Attempts to acquire this lock.
    ///
    /// If the lock could not be acquired at this time, then a [`None`] value is
    /// given to the user provided closure as the argument. If the lock has been
    /// acquired, then a [`Some`] with the mutex guard is given instead. The lock
    /// will be unlocked when the guard is dropped at the end of the call.
    ///
    /// This function does not block.
    ///
    /// # Panics
    ///
    /// This lock implementation cannot be recursively acquired, doing so it
    /// result in a panic. That is the case for both `lock_with` and
    /// `try_lock_with`.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::sync::Arc;
    /// use std::thread;
    ///
    /// use mcslock::thread_local::Mutex;
    ///
    /// let mutex = Arc::new(Mutex::new(0));
    /// let c_mutex = Arc::clone(&mutex);
    ///
    /// thread::spawn(move || {
    ///     c_mutex.try_lock_with(|guard| {
    ///         **guard.unwrap() = 10;
    ///     });
    /// })
    /// .join().expect("thread::spawn failed");
    ///
    /// assert_eq!(mutex.lock_with(|guard| **guard), 10);
    /// ```
    ///
    /// An example of panic:
    ///
    /// ```should_panic
    /// use mcslock::thread_local::Mutex;
    ///
    /// let mutex = Mutex::new(0);
    ///
    /// mutex.try_lock_with(|guard| {
    ///     let mutex = Mutex::new(());
    ///     // Recursive locking a thread_local::Mutex
    ///     // is not allowed, this will panic.
    ///     mutex.lock_with(|_guard| ());
    /// });
    /// ```
    pub fn try_lock_with<F, R>(&self, f: F) -> R
    where
        F: FnOnce(Option<&mut MutexGuard<'_, T>>) -> R,
    {
        self.node_with(|raw, node| f(raw.try_lock(node).map(MutexGuard::new).as_mut()))
    }

    /// Acquires a mutex, blocking the current thread until it is able to do so.
    ///
    /// This function will block the local thread until it is available to acquire
    /// the mutex. Upon acquiring the mutex, the user provided closure will be
    /// executed against the mutex guard reference, then the guard will be
    /// automatically dropped at the end of the call.
    ///
    /// This function will block if the lock is unavailable.
    ///
    /// # Panics
    ///
    /// This lock implementation cannot be recursively acquired, doing so it
    /// result in a panic. That is the case for both `lock_with` and
    /// `try_lock_with`.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::sync::Arc;
    /// use std::thread;
    ///
    /// use mcslock::thread_local::Mutex;
    ///
    /// let mutex = Arc::new(Mutex::new(0));
    /// let c_mutex = Arc::clone(&mutex);
    ///
    /// thread::spawn(move || {
    ///     c_mutex.lock_with(|guard| **guard = 10);
    /// })
    /// .join().expect("thread::spawn failed");
    ///
    /// assert_eq!(mutex.lock_with(|guard| **guard), 10);
    /// ```
    ///
    /// An example of panic:
    ///
    /// ```should_panic
    /// use mcslock::thread_local::Mutex;
    ///
    /// let mutex = Mutex::new(0);
    ///
    /// mutex.lock_with(|_guard| {
    ///     let mutex = Mutex::new(());
    ///     // Recursive locking a thread_local::Mutex
    ///     // is not allowed, this will panic.
    ///     mutex.try_lock_with(|_guard| ());
    /// });
    /// ```
    pub fn lock_with<F, R>(&self, f: F) -> R
    where
        F: FnOnce(&mut MutexGuard<'_, T>) -> R,
    {
        self.node_with(|raw, node| f(&mut MutexGuard::new(raw.lock(node))))
    }

    /// Returns `true` if the lock is currently held.
    ///
    /// This method does not provide any synchronization guarantees, so its only
    /// useful as a heuristic, and so must be considered not up to date.
    ///
    /// # Example
    ///
    /// ```
    /// use mcslock::thread_local::Mutex;
    ///
    /// let mutex = Mutex::new(0);
    ///
    /// mutex.lock_with(|guard| **guard = 1);
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
    /// use mcslock::thread_local::Mutex;
    ///
    /// let mut mutex = Mutex::new(0);
    /// *mutex.get_mut() = 10;
    ///
    /// assert_eq!(mutex.lock_with(|guard| **guard), 10);
    /// ```
    #[cfg(not(all(loom, test)))]
    #[inline]
    pub fn get_mut(&mut self) -> &mut T {
        self.0.get_mut()
    }
}

impl<T: ?Sized + Default> Default for Mutex<T> {
    /// Creates a `Mutex<T>`, with the `Default` value for `T`.
    fn default() -> Self {
        Self::new(Default::default())
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
        let mut d = f.debug_struct("Mutex");
        self.try_lock_with(|guard| match guard {
            Some(g) => g.raw.data_with(|data| d.field("data", &data)),
            None => d.field("data", &format_args!("<locked>")),
        });
        d.field("tail", self.0.tail());
        d.finish()
    }
}
/// An RAII implementation of a "scoped lock" of a mutex. When this structure is
/// dropped (falls out of scope), the lock will be unlocked.
///
/// The data protected by the mutex can be access through this guard via its
/// [`Deref`] and [`DerefMut`] implementations.
pub struct MutexGuard<'a, T: ?Sized> {
    raw: RawMutexGuard<'a, T>,
    // Guard will access thread local storage during drop call, can't be Send.
    marker: PhantomData<*mut ()>,
}

// SAFETY: Guard only access thread local storage during drop call, can be Sync.
unsafe impl<'a, T: ?Sized + Sync> Sync for MutexGuard<'a, T> {}

impl<'a, T: ?Sized> MutexGuard<'a, T> {
    fn new(raw: RawMutexGuard<'a, T>) -> Self {
        Self { raw, marker: PhantomData }
    }

    /// Get a Loom immutable data pointer that borrows from this guard.
    #[cfg(all(loom, test))]
    fn deref(&self) -> MutexGuardDeref<'a, T> {
        self.raw.deref()
    }

    /// Get a Loom mutable data pointer that mutably borrows from this guard.
    #[cfg(all(loom, test))]
    fn deref_mut(&mut self) -> MutexGuardDerefMut<'a, T> {
        self.raw.deref_mut()
    }
}

#[cfg(not(all(loom, test)))]
impl<'a, T: ?Sized> Deref for MutexGuard<'a, T> {
    type Target = T;

    /// Dereferences the guard to access the underlying data.
    fn deref(&self) -> &T {
        &self.raw
    }
}

#[cfg(not(all(loom, test)))]
impl<'a, T: ?Sized> DerefMut for MutexGuard<'a, T> {
    /// Mutably dereferences the guard to access the underlying data.
    fn deref_mut(&mut self) -> &mut T {
        &mut self.raw
    }
}

impl<'a, T: ?Sized + fmt::Debug> fmt::Debug for MutexGuard<'a, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.raw.fmt(f)
    }
}

impl<'a, T: ?Sized + fmt::Display> fmt::Display for MutexGuard<'a, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.raw.fmt(f)
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
    // fn must_not_compile() {
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
        assert_eq!(data, ITERS * CONCURRENCY * 2);
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

    #[test]
    #[should_panic]
    fn test_lock_arc_nested() {
        // Tests nested locks are not allowed and
        // will panic, else this would be UB.
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
    #[should_panic]
    fn test_recursive_lock() {
        let arc = Arc::new(Mutex::new(1));
        let (tx, rx) = channel();
        for _ in 0..4 {
            let tx2 = tx.clone();
            let c_arc = Arc::clone(&arc);
            let _t = thread::spawn(move || {
                let _lock = c_arc.lock_with(|_g| {
                    let mutex = Mutex::new(());
                    let _lock = mutex.lock_with(|_g| ());
                });
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
            lock.lock_with(|guard| *guard.deref_mut() += 1);
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

            assert_eq!(end, data.lock_with(|guard| *guard.deref()));
        });
    }

    #[test]
    fn threads_fork() {
        // Using std's Arc or else this model runs for loo long.
        use std::sync::Arc;

        fn inc(lock: Arc<Mutex<i32>>) {
            lock.lock_with(|guard| *guard.deref_mut() += 1);
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
