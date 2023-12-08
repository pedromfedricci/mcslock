use core::fmt;
use core::marker::PhantomData;
use core::sync::atomic::Ordering::{Acquire, Relaxed, Release};

#[cfg(not(all(loom, test)))]
use core::ops::{Deref, DerefMut};
#[cfg(not(all(loom, test)))]
use core::sync::atomic::AtomicBool;

#[cfg(all(loom, test))]
use loom::cell::{ConstPtr, MutPtr};
#[cfg(all(loom, test))]
use loom::sync::atomic::AtomicBool;

#[cfg(all(loom, test))]
use crate::loom::{Guard, GuardDeref, GuardDerefMut};

use crate::raw::{Mutex as RawMutex, MutexNode};
use crate::relax::Relax;

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
/// use mcslock::barging::Mutex;
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
pub struct Mutex<T: ?Sized, R> {
    locked: AtomicBool,
    marker: PhantomData<R>,
    inner: RawMutex<T, R>,
}

impl<T, R> Mutex<T, R> {
    /// Creates a new mutex in an unlocked state ready for use.
    ///
    /// # Examples
    ///
    /// ```
    /// use mcslock::barging::Mutex;
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
        let locked = AtomicBool::new(false);
        let inner = RawMutex::new(value);
        Self { locked, inner, marker: PhantomData }
    }

    /// Creates a new unlocked mutex with Loom primitives (non-const).
    #[cfg(all(loom, test))]
    fn new(value: T) -> Self {
        let locked = AtomicBool::new(false);
        let inner = RawMutex::new(value);
        Self { locked, inner, marker: PhantomData }
    }

    /// Consumes this mutex, returning the underlying data.
    ///
    /// # Examples
    ///
    /// ```
    /// use mcslock::barging::Mutex;
    /// use mcslock::relax::Spin;
    ///
    /// type SpinMutex<T> = Mutex<T, Spin>;
    ///
    /// let mutex = SpinMutex::new(0);
    /// assert_eq!(mutex.into_inner(), 0);
    /// ```
    #[inline]
    pub fn into_inner(self) -> T {
        self.inner.into_inner()
    }
}

impl<T: ?Sized, R: Relax> Mutex<T, R> {
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
    /// use mcslock::barging::Mutex;
    /// use mcslock::relax::Spin;
    ///
    /// type SpinMutex<T> = Mutex<T, Spin>;
    ///
    /// let mutex = Arc::new(SpinMutex::new(0));
    /// let c_mutex = Arc::clone(&mutex);
    ///
    /// thread::spawn(move || {
    ///     *c_mutex.lock() = 10;
    /// })
    /// .join().expect("thread::spawn failed");
    ///
    /// assert_eq!(*mutex.lock(), 10);
    /// ```
    pub fn lock(&self) -> MutexGuard<'_, T, R> {
        if self.try_lock_fast() {
            return MutexGuard::new(self);
        }
        let mut node = MutexNode::new();
        let guard = self.inner.lock(&mut node);
        while !self.try_lock_fast() {
            let mut relax = R::default();
            while self.locked.load(Relaxed) {
                relax.relax();
            }
        }
        drop(guard);
        MutexGuard::new(self)
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
    /// use mcslock::barging::Mutex;
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
    /// use mcslock::barging::spins::Mutex;
    ///
    /// let mutex = Mutex::new(1);
    /// let data = mutex.lock_with(|guard| &*guard);
    /// ```
    pub fn lock_with<F, Ret>(&self, f: F) -> Ret
    where
        F: FnOnce(MutexGuard<'_, T, R>) -> Ret,
    {
        f(self.lock())
    }
}

impl<T: ?Sized, R> Mutex<T, R> {
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
    /// use mcslock::barging::Mutex;
    /// use mcslock::relax::Spin;
    ///
    /// type SpinMutex<T> = Mutex<T, Spin>;
    ///
    /// let mutex = Arc::new(SpinMutex::new(0));
    /// let c_mutex = Arc::clone(&mutex);
    ///
    /// thread::spawn(move || {
    ///     let mut lock = c_mutex.try_lock();
    ///     if let Some(ref mut mutex) = lock {
    ///         **mutex = 10;
    ///     } else {
    ///         println!("try_lock failed");
    ///     }
    /// })
    /// .join().expect("thread::spawn failed");
    ///
    /// assert_eq!(*mutex.lock(), 10);
    /// ```
    pub fn try_lock(&self) -> Option<MutexGuard<'_, T, R>> {
        self.locked
            .compare_exchange(false, true, Acquire, Relaxed)
            .map(|_| MutexGuard::new(self))
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
    /// use mcslock::barging::Mutex;
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
    /// use mcslock::barging::spins::Mutex;
    ///
    /// let mutex = Mutex::new(1);
    /// let data = mutex.try_lock_with(|guard| &*guard.unwrap());
    /// ```
    pub fn try_lock_with<F, Ret>(&self, f: F) -> Ret
    where
        F: FnOnce(Option<MutexGuard<'_, T, R>>) -> Ret,
    {
        f(self.try_lock())
    }

    /// Returns `true` if the lock is currently held.
    ///
    /// This method does not provide any synchronization guarantees, so its only
    /// useful as a heuristic, and so must be considered not up to date.
    ///
    /// # Example
    ///
    /// ```
    /// use mcslock::barging::Mutex;
    /// use mcslock::relax::Spin;
    ///
    /// type SpinMutex<T> = Mutex<T, Spin>;
    ///
    /// let mutex = SpinMutex::new(0);
    /// let guard = mutex.lock();
    /// drop(guard);
    ///
    /// assert_eq!(mutex.is_locked(), false);
    /// ```
    #[inline]
    pub fn is_locked(&self) -> bool {
        // Relaxed is sufficient because this method only guarantees atomicity.
        self.locked.load(Relaxed)
    }

    /// Returns a mutable reference to the underlying data.
    ///
    /// Since this call borrows the `Mutex` mutably, no actual locking needs to
    /// take place - the mutable borrow statically guarantees no locks exist.
    ///
    /// # Examples
    ///
    /// ```
    /// use mcslock::barging::Mutex;
    /// use mcslock::relax::Spin;
    ///
    /// type SpinMutex<T> = Mutex<T, Spin>;
    ///
    /// let mut mutex = SpinMutex::new(0);
    /// *mutex.get_mut() = 10;
    ///
    /// assert_eq!(*mutex.lock(), 10);
    /// ```
    #[cfg(not(all(loom, test)))]
    #[inline]
    pub fn get_mut(&mut self) -> &mut T {
        self.inner.get_mut()
    }

    /// Tries to lock this mutex with a weak exchange.
    fn try_lock_fast(&self) -> bool {
        self.locked.compare_exchange_weak(false, true, Acquire, Relaxed).is_ok()
    }

    /// Unlocks this mutex.
    fn unlock(&self) {
        self.locked.store(false, Release);
    }

    #[cfg(not(all(loom, test)))]
    /// Returns a raw mutable pointer to the underlying data.
    const fn data_ptr(&self) -> *mut T {
        self.inner.data_ptr()
    }

    /// Get a Loom immutable raw pointer to the underlying data.
    #[cfg(all(loom, test))]
    fn data_get(&self) -> ConstPtr<T> {
        self.inner.data_get()
    }

    /// Get a Loom mutable raw pointer to the underlying data.
    #[cfg(all(loom, test))]
    fn data_get_mut(&self) -> MutPtr<T> {
        self.inner.data_get_mut()
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
        self.inner.fmt(f)
    }
}

#[cfg(all(feature = "lock_api", not(loom)))]
unsafe impl<R: Relax> lock_api::RawMutex for Mutex<(), R> {
    type GuardMarker = lock_api::GuardSend;

    // It is fine to const initialize `Mutex<(), R>` since the data is not going
    // to be shared. And since it is a `Unit` type, copies will be optimized away.
    #[allow(clippy::declare_interior_mutable_const)]
    const INIT: Self = Self::new(());

    fn lock(&self) {
        core::mem::forget(Self::lock(self));
    }

    fn try_lock(&self) -> bool {
        Self::try_lock(self).map(core::mem::forget).is_some()
    }

    unsafe fn unlock(&self) {
        self.unlock();
    }

    fn is_locked(&self) -> bool {
        self.is_locked()
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
pub struct MutexGuard<'a, T: ?Sized, R> {
    lock: &'a Mutex<T, R>,
}

// Same unsafe impl as `std::sync::MutexGuard`.
unsafe impl<T: ?Sized + Sync, R> Sync for MutexGuard<'_, T, R> {}

impl<'a, T: ?Sized, R> MutexGuard<'a, T, R> {
    /// Creates a new `MutexGuard` instance.
    const fn new(lock: &'a Mutex<T, R>) -> Self {
        Self { lock }
    }

    /// Runs `f` with an immutable reference to the wrapped value.
    #[cfg(not(all(loom, test)))]
    fn data_with<F, Ret>(&self, f: F) -> Ret
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

impl<T: ?Sized, R> Drop for MutexGuard<'_, T, R> {
    fn drop(&mut self) {
        self.lock.unlock();
    }
}

#[cfg(not(all(loom, test)))]
impl<'a, T: ?Sized, R> Deref for MutexGuard<'a, T, R> {
    type Target = T;

    /// Dereferences the guard to access the underlying data.
    fn deref(&self) -> &T {
        // SAFETY: A guard instance holds the lock locked.
        unsafe { &*self.lock.data_ptr() }
    }
}

#[cfg(not(all(loom, test)))]
impl<'a, T: ?Sized, R> DerefMut for MutexGuard<'a, T, R> {
    /// Mutably dereferences the guard to access the underlying data.
    fn deref_mut(&mut self) -> &mut T {
        // SAFETY: A guard instance holds the lock locked.
        unsafe { &mut *self.lock.data_ptr() }
    }
}

impl<'a, T: ?Sized + fmt::Debug, R> fmt::Debug for MutexGuard<'a, T, R> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.data_with(|data| fmt::Debug::fmt(data, f))
    }
}

impl<'a, T: ?Sized + fmt::Display, R> fmt::Display for MutexGuard<'a, T, R> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.data_with(|data| fmt::Display::fmt(data, f))
    }
}

/// SAFETY: A guard instance hold the lock locked, with exclusive access to the
/// underlying data.
#[cfg(all(loom, test))]
unsafe impl<T: ?Sized, R> Guard<T> for MutexGuard<'_, T, R> {
    type Guard<'a> = Self where T: 'a, Self: 'a;

    fn deref(&self) -> GuardDeref<'_, T, Self::Guard<'_>> {
        GuardDeref::new(self.lock.data_get())
    }

    fn deref_mut(&self) -> GuardDerefMut<'_, T, Self::Guard<'_>> {
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

    use crate::barging::yields::Mutex;

    #[derive(Eq, PartialEq, Debug)]
    struct NonCopy(i32);

    #[test]
    fn smoke() {
        let m = Mutex::new(());
        drop(m.lock());
        drop(m.lock());
    }

    #[test]
    fn lots_and_lots() {
        static LOCK: Mutex<u32> = Mutex::new(0);

        const ITERS: u32 = 1000;
        const CONCURRENCY: u32 = 3;

        fn inc() {
            for _ in 0..ITERS {
                let mut g = LOCK.lock();
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
        assert_eq!(*LOCK.lock(), ITERS * CONCURRENCY * 2);
    }

    #[test]
    fn try_lock() {
        let m = Mutex::new(());
        *m.try_lock().unwrap() = ();
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
            let lock = arc2.lock();
            let lock2 = lock.lock();
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
                let _lock = c_arc.lock();
                let lock2 = mutex.lock();
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
                    *self.i.lock() += 1;
                }
            }
            let _u = Unwinder { i: arc2 };
            panic!();
        })
        .join();
        let lock = arc.lock();
        assert_eq!(*lock, 2);
    }

    #[test]
    fn test_lock_unsized() {
        let lock: &Mutex<[i32]> = &Mutex::new([1, 2, 3]);
        {
            let b = &mut *lock.lock();
            b[0] = 4;
            b[2] = 5;
        }
        let comp: &[i32] = &[4, 2, 5];
        assert_eq!(&*lock.lock(), comp);
    }
}

#[cfg(all(loom, test))]
mod test {
    use loom::{model, thread};

    use crate::barging::yields::Mutex;
    use crate::loom::Guard;

    #[test]
    fn threads_join() {
        use core::ops::Range;
        use loom::sync::Arc;

        fn inc(lock: Arc<Mutex<i32>>) {
            let guard = lock.lock();
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

            assert_eq!(end, *data.lock().deref());
        });
    }

    #[test]
    fn threads_fork() {
        // Using std's Arc or else this model runs for loo long.
        use std::sync::Arc;

        fn inc(lock: Arc<Mutex<i32>>) {
            let guard = lock.lock();
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
