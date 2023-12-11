use core::cell::RefCell;
use core::fmt;
use core::marker::PhantomData;

use crate::raw::{Mutex as RawMutex, MutexGuard as RawMutexGuard, MutexNode};
use crate::relax::Relax;

// A thread_local key holding a [`MutexNode`] instance behind a [`RefCell`].
//
// This node definition can be evaluated as constant.
#[cfg(not(all(loom, test)))]
std::thread_local! {
    static NODE: RefCell<MutexNode> = const {
        RefCell::new(MutexNode::new())
    }
}

// A Loom's thread_local key holding a [`MutexNode`] instance behind a
// [`RefCell`].
//
// This node definition uses Loom primitives and it can't be evaluated at
// compile-time since Loom does not support that feature.
#[cfg(all(loom, test))]
loom::thread_local! {
    static NODE: RefCell<MutexNode> = {
        RefCell::new(MutexNode::new())
    }
}

/// The panic message as a string literal.
macro_rules! literal_panic_msg {
    () => {
        "At most one thread_local MCS lock can be held at any time within a thread"
    };
}

/// A mutual exclusion primitive useful for protecting shared data.
///
/// This mutex will block threads waiting for the lock to become available. The
/// mutex can also be statically initialized or created via a [`new`]
/// constructor. Each mutex has a type parameter which represents the data that
/// it is protecting. The data can only be accessed through the RAII guards
/// provided as closure arguments from [`lock_with`] and [`try_lock_with`], which
/// guarantees that the data is only ever accessed when the mutex is locked.
///
/// # Examples
///
/// ```
/// use std::sync::Arc;
/// use std::thread;
/// use std::sync::mpsc::channel;
///
/// use mcslock::thread_local::Mutex;
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
///         // The shared state can only be accessed once the lock is held.
///         // Our non-atomic increment is safe because we're the only thread
///         // which can access the shared state when the lock is held.
///         //
///         // We unwrap() the return value to assert that we are not expecting
///         // threads to ever fail while holding the lock.
///         //
///         // Data is exclusively accessed by the guard argument.
///         data.lock_with(|mut data| {
///             *data += 1;
///             if *data == N {
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
pub struct Mutex<T: ?Sized, R>(RawMutex<T, R>);

impl<T, R> Mutex<T, R> {
    /// Creates a new mutex in an unlocked state ready for use.
    ///
    /// # Examples
    ///
    /// ```
    /// use mcslock::thread_local::Mutex;
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
        Self(RawMutex::new(value))
    }

    /// Creates a new unlocked mutex with Loom primitives (non-const).
    #[cfg(all(loom, test))]
    fn new(value: T) -> Self {
        Self(RawMutex::new(value))
    }

    /// Consumes this mutex, returning the underlying data.
    ///
    /// # Examples
    ///
    /// ```
    /// use mcslock::thread_local::Mutex;
    /// use mcslock::relax::Spin;
    ///
    /// type SpinMutex<T> = Mutex<T, Spin>;
    ///
    /// let mutex = SpinMutex::new(0);
    /// assert_eq!(mutex.into_inner(), 0);
    /// ```
    #[inline]
    pub fn into_inner(self) -> T {
        self.0.into_inner()
    }
}

impl<T: ?Sized, R: Relax> Mutex<T, R> {
    /// Attempts to acquire this lock and run the closure against its guard.
    ///
    /// If the lock could not be acquired at this time, then a [`None`] value is
    /// given to the user provided closure as the argument. If the lock has been
    /// acquired, then a [`Some`] with the mutex guard is given instead. The lock
    /// will be unlocked when the guard is dropped.
    ///
    /// This function does not block.
    ///
    /// # Panics
    ///
    /// At most one lock of this implementation might be held within a single
    /// thread at any time. Trying to acquire a second lock while a guard is
    /// still alive will cause a panic.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::sync::Arc;
    /// use std::thread;
    ///
    /// use mcslock::thread_local::Mutex;
    /// use mcslock::relax::Spin;
    ///
    /// type SpinMutex<T> = Mutex<T, Spin>;
    ///
    /// let mutex = Arc::new(SpinMutex::new(0));
    /// let c_mutex = Arc::clone(&mutex);
    ///
    /// thread::spawn(move || {
    ///     c_mutex.try_lock_with(|guard| {
    ///         if let Some(mut guard) = guard {
    ///             *guard = 10;
    ///         } else {
    ///             println!("try_lock failed");
    ///         }
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
    /// use mcslock::thread_local::spins::Mutex;
    ///
    /// let mutex = Mutex::new(1);
    /// let data = mutex.try_lock_with(|guard| &*guard.unwrap());
    /// ```
    ///
    /// An example of panic:
    ///
    #[doc = concat!("```should_panic,", literal_panic_msg!())]
    /// use mcslock::thread_local::Mutex;
    /// use mcslock::relax::Spin;
    ///
    /// type SpinMutex<T> = Mutex<T, Spin>;
    ///
    /// let mutex = SpinMutex::new(0);
    ///
    /// mutex.try_lock_with(|guard| {
    ///     let _guard = guard.unwrap();
    ///     let mutex = SpinMutex::new(());
    ///     // Acquiring more than one thread_local::Mutex within a single
    ///     // thread at the same time is not allowed, this will panic.
    ///     mutex.lock_with(|_guard| ());
    /// });
    /// ```
    pub fn try_lock_with<F, Ret>(&self, f: F) -> Ret
    where
        F: FnOnce(Option<MutexGuard<'_, T, R>>) -> Ret,
    {
        self.node_with(|raw, node| f(raw.try_lock(node).map(MutexGuard::new)))
    }

    /// Acquires a mutex, blocking the current thread until it is able to do so.
    ///
    /// This function will block the local thread until it is available to acquire
    /// the mutex. Upon acquiring the mutex, the user provided closure will be
    /// executed against the mutex guard. Once the guard goes out of scope, it
    /// will unlock the mutex.
    ///
    /// This function will block if the lock is unavailable.
    ///
    /// # Panics
    ///
    /// At most one lock of this implementation might be held within a single
    /// thread at any time. Trying to acquire a second lock while a guard is
    /// still alive will cause a panic.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::sync::Arc;
    /// use std::thread;
    ///
    /// use mcslock::thread_local::Mutex;
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
    /// use mcslock::thread_local::spins::Mutex;
    ///
    /// let mutex = Mutex::new(1);
    /// let data = mutex.lock_with(|guard| &*guard);
    /// ```
    ///
    /// An example of panic:
    ///
    #[doc = concat!("```should_panic,", literal_panic_msg!())]
    /// use mcslock::thread_local::Mutex;
    /// use mcslock::relax::Spin;
    ///
    /// type SpinMutex<T> = Mutex<T, Spin>;
    ///
    /// let mutex = SpinMutex::new(0);
    ///
    /// mutex.lock_with(|_guard| {
    ///     let mutex = SpinMutex::new(());
    ///     // Acquiring more than one thread_local::Mutex within a single
    ///     // thread at the same time is not allowed, this will panic.
    ///     mutex.try_lock_with(|_guard| ());
    /// });
    /// ```
    pub fn lock_with<F, Ret>(&self, f: F) -> Ret
    where
        F: FnOnce(MutexGuard<'_, T, R>) -> Ret,
    {
        self.node_with(|raw, node| f(MutexGuard::new(raw.lock(node))))
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
    /// use mcslock::thread_local::Mutex;
    /// use mcslock::relax::Spin;
    ///
    /// type SpinMutex<T> = Mutex<T, Spin>;
    ///
    /// let mutex = SpinMutex::new(0);
    ///
    /// mutex.lock_with(|mut guard| *guard = 1);
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
    /// use mcslock::relax::Spin;
    ///
    /// type SpinMutex<T> = Mutex<T, Spin>;
    ///
    /// let mut mutex = SpinMutex::new(0);
    /// *mutex.get_mut() = 10;
    ///
    /// assert_eq!(mutex.lock_with(|guard| *guard), 10);
    /// ```
    #[cfg(not(all(loom, test)))]
    #[inline]
    pub fn get_mut(&mut self) -> &mut T {
        self.0.get_mut()
    }

    /// Runs `f` over the inner mutex and the thread local node.
    ///
    /// # Panics
    ///
    /// Will panic if the thread local [`MutexNode`] is already in use by a held
    /// lock from this thread.
    fn node_with<F, Ret>(&self, f: F) -> Ret
    where
        F: FnOnce(&RawMutex<T, R>, &mut MutexNode) -> Ret,
    {
        #[allow(clippy::option_if_let_else)]
        NODE.with(|node| match node.try_borrow_mut() {
            Ok(mut node) => f(&self.0, &mut node),
            Err(_) => Self::panic_already_held(),
        })
    }

    /// Panics the thread with an appropiate message.
    #[inline(never)]
    #[track_caller]
    #[cold]
    fn panic_already_held() -> ! {
        panic!("{}", literal_panic_msg!())
    }
}

impl<T: ?Sized + Default, R> Default for Mutex<T, R> {
    /// Creates a `Mutex<T, R>` with the `Default` value for `T`.
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
        let mut d = f.debug_struct("Mutex");
        self.try_lock_with(|guard| match guard {
            Some(guard) => guard.inner.with(|data| d.field("data", &data)),
            None => d.field("data", &format_args!("<locked>")),
        });
        d.field("tail", self.0.tail_debug());
        d.finish()
    }
}

#[cfg(all(loom, test))]
#[rustfmt::skip]
impl<T: ?Sized, R: Relax> crate::loom::LockWith<T> for Mutex<T, R> {
    type Guard<'a> = MutexGuard<'a, T, R> where T: 'a, Self: 'a;

    fn new(value: T) -> Self where T: Sized {
        Self::new(value)
    }

    fn try_lock_with<F, Ret>(&self, f: F) -> Ret
    where
        F: FnOnce(Option<MutexGuard<'_, T, R>>) -> Ret,
    {
        self.try_lock_with(f)
    }

    fn lock_with<F, Ret>(&self, f: F) -> Ret
    where
        F: FnOnce(MutexGuard<'_, T, R>) -> Ret,
    {
        self.lock_with(f)
    }
}

/// An RAII implementation of a "scoped lock" of a mutex. When this structure is
/// dropped (falls out of scope), the lock will be unlocked.
///
/// The data protected by the mutex can be access through this guard via its
/// [`Deref`] and [`DerefMut`] implementations.
///
/// This structure is given as closure argument by [`lock_with`] and
/// [`try_lock_with`] methods on [`Mutex`].
///
/// [`lock_with`]: Mutex::lock_with
/// [`try_lock_with`]: Mutex::try_lock_with
#[must_use = "if unused the Mutex will immediately unlock"]
pub struct MutexGuard<'a, T: ?Sized, R: Relax> {
    inner: RawMutexGuard<'a, T, R>,
    // Guard will access thread local storage during drop call, can't be Send.
    marker: PhantomData<*mut ()>,
}

// SAFETY: Guard only access thread local storage during drop call, can be Sync.
unsafe impl<'a, T: ?Sized + Sync, R: Relax> Sync for MutexGuard<'a, T, R> {}

impl<'a, T: ?Sized, R: Relax> MutexGuard<'a, T, R> {
    fn new(inner: RawMutexGuard<'a, T, R>) -> Self {
        Self { inner, marker: PhantomData }
    }
}

#[cfg(not(all(loom, test)))]
impl<'a, T: ?Sized, R: Relax> core::ops::Deref for MutexGuard<'a, T, R> {
    type Target = T;

    /// Dereferences the guard to access the underlying data.
    fn deref(&self) -> &T {
        &self.inner
    }
}

#[cfg(not(all(loom, test)))]
impl<'a, T: ?Sized, R: Relax> core::ops::DerefMut for MutexGuard<'a, T, R> {
    /// Mutably dereferences the guard to access the underlying data.
    fn deref_mut(&mut self) -> &mut T {
        &mut self.inner
    }
}

impl<'a, T: ?Sized + fmt::Debug, R: Relax> fmt::Debug for MutexGuard<'a, T, R> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.inner.fmt(f)
    }
}

impl<'a, T: ?Sized + fmt::Display, R: Relax> fmt::Display for MutexGuard<'a, T, R> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.inner.fmt(f)
    }
}

/// SAFETY: A guard instance hold the lock locked, with exclusive access to the
/// underlying data.
#[cfg(all(loom, test))]
unsafe impl<T: ?Sized, R: Relax> crate::loom::Guard<T> for MutexGuard<'_, T, R> {
    fn get(&self) -> &loom::cell::UnsafeCell<T> {
        self.inner.get()
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

    use crate::thread_local::yields::Mutex;

    #[derive(Eq, PartialEq, Debug)]
    struct NonCopy(i32);

    #[test]
    fn smoke() {
        let m = Mutex::new(1);
        let data = m.lock_with(|guard| *guard);
        assert_eq!(data, 1);
        m.lock_with(|mut guard| *guard = 2);
        let data = m.lock_with(|guard| *guard);
        assert_eq!(data, 2);
    }

    #[test]
    fn lots_and_lots() {
        static LOCK: Mutex<u32> = Mutex::new(0);

        const ITERS: u32 = 1000;
        const CONCURRENCY: u32 = 3;

        fn inc() {
            for _ in 0..ITERS {
                LOCK.lock_with(|mut data| *data += 1);
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
        let data = LOCK.lock_with(|data| *data);
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
    #[should_panic = literal_panic_msg!()]
    fn test_lock_arc_nested() {
        // Tests nested locks are not allowed and
        // will panic, else this would be UB.
        let arc = Arc::new(Mutex::new(1));
        let arc2 = Arc::new(Mutex::new(arc));
        let (tx, rx) = channel();
        let _t = thread::spawn(move || {
            let val = arc2.lock_with(|arc2| arc2.lock_with(|g| *g));
            assert_eq!(val, 1);
            tx.send(()).unwrap();
        });
        rx.recv().unwrap();
    }

    #[test]
    #[should_panic = literal_panic_msg!()]
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
                    self.i.lock_with(|mut g| *g += 1);
                }
            }
            let _u = Unwinder { i: arc2 };
            panic!();
        })
        .join();
        let value = arc.lock_with(|g| *g);
        assert_eq!(value, 2);
    }

    #[test]
    fn test_lock_unsized() {
        let lock: &Mutex<[i32]> = &Mutex::new([1, 2, 3]);
        {
            lock.lock_with(|mut g| {
                g[0] = 4;
                g[2] = 5;
            });
        }
        let comp: &[i32] = &[4, 2, 5];
        lock.lock_with(|g| assert_eq!(&*g, comp));
    }
}

#[cfg(all(loom, test))]
mod test {
    use crate::loom::model;
    use crate::thread_local::yields::Mutex;

    #[test]
    fn try_lock_join() {
        model::try_lock_join::<Mutex<_>>();
    }

    #[test]
    fn lock_join() {
        model::lock_join::<Mutex<_>>();
    }

    #[test]
    fn mixed_lock_join() {
        model::mixed_lock_join::<Mutex<_>>();
    }
}
