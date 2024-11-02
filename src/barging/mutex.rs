use core::fmt::{self, Debug, Display, Formatter};

use crate::cfg::atomic::AtomicBool;
use crate::inner::barging as inner;
use crate::relax::{Relax, RelaxWait};

#[cfg(test)]
use crate::test::{LockNew, LockThen, TryLockThen};

#[cfg(all(loom, test))]
use crate::loom::{Guard, GuardDeref, GuardDerefMut};
#[cfg(all(loom, test))]
use crate::test::{AsDeref, AsDerefMut};

// The inner type of mutex, with a boolean as the atomic data.
type MutexInner<T, Rs, Rq> = inner::Mutex<T, AtomicBool, RelaxWait<Rs>, RelaxWait<Rq>>;

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
/// use mcslock::relax::{Spin, SpinBackoff};
///
/// type SpinMutex<T> = Mutex<T, SpinBackoff, Spin>;
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
pub struct Mutex<T: ?Sized, Rs, Rq> {
    inner: MutexInner<T, Rs, Rq>,
}

// Same unsafe impls as `crate::inner::barging::Mutex`.
unsafe impl<T: ?Sized + Send, Rs, Rq> Send for Mutex<T, Rs, Rq> {}
unsafe impl<T: ?Sized + Send, Rs, Rq> Sync for Mutex<T, Rs, Rq> {}

impl<T, Rs, Rq> Mutex<T, Rs, Rq> {
    /// Creates a new mutex in an unlocked state ready for use.
    ///
    /// # Examples
    ///
    /// ```
    /// use mcslock::barging::Mutex;
    /// use mcslock::relax::{Spin, SpinBackoff};
    ///
    /// type SpinMutex<T> = Mutex<T, SpinBackoff, Spin>;
    ///
    /// const MUTEX: SpinMutex<i32> = SpinMutex::new(0);
    /// let mutex = SpinMutex::new(0);
    /// ```
    #[cfg(not(all(loom, test)))]
    #[inline]
    pub const fn new(value: T) -> Self {
        Self { inner: inner::Mutex::new(value) }
    }

    /// Creates a new unlocked mutex with Loom primitives (non-const).
    #[cfg(all(loom, test))]
    #[cfg(not(tarpaulin_include))]
    fn new(value: T) -> Self {
        Self { inner: inner::Mutex::new(value) }
    }

    /// Consumes this mutex, returning the underlying data.
    ///
    /// # Examples
    ///
    /// ```
    /// use mcslock::barging::Mutex;
    /// use mcslock::relax::{Spin, SpinBackoff};
    ///
    /// type SpinMutex<T> = Mutex<T, SpinBackoff, Spin>;
    ///
    /// let mutex = SpinMutex::new(0);
    /// assert_eq!(mutex.into_inner(), 0);
    /// ```
    #[inline(always)]
    pub fn into_inner(self) -> T {
        self.inner.into_inner()
    }
}

impl<T: ?Sized, Rs: Relax, Rq: Relax> Mutex<T, Rs, Rq> {
    /// Acquires this mutex, blocking the current thread until it is able to do so.
    ///
    /// This function will block the local thread until it is available to acquire
    /// the mutex. Upon returning, the thread is the only thread with the lock
    /// held. An RAII guard is returned to allow scoped unlock of the lock. When
    /// the guard goes out of scope, the mutex will be unlocked.
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
    /// use mcslock::relax::{Spin, SpinBackoff};
    ///
    /// type SpinMutex<T> = Mutex<T, SpinBackoff, Spin>;
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
    #[inline]
    pub fn lock(&self) -> MutexGuard<'_, T, Rs, Rq> {
        self.inner.lock().into()
    }

    /// Acquires this mutex and then runs the closure against its guard.
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
    /// use mcslock::relax::{Spin, SpinBackoff};
    ///
    /// type SpinMutex<T> = Mutex::<T, SpinBackoff, Spin>;
    ///
    /// let mutex = Arc::new(SpinMutex::new(0));
    /// let c_mutex = Arc::clone(&mutex);
    ///
    /// thread::spawn(move || {
    ///     c_mutex.lock_then(|mut guard| *guard = 10);
    /// })
    /// .join().expect("thread::spawn failed");
    ///
    /// assert_eq!(mutex.lock_then(|guard| *guard), 10);
    /// ```
    ///
    /// Compile fail: borrows of the guard or its data cannot escape the given
    /// closure:
    ///
    /// ```compile_fail,E0515
    /// use mcslock::barging::spins::Mutex;
    ///
    /// let mutex = Mutex::new(1);
    /// let data = mutex.lock_then(|guard| &*guard);
    /// ```
    #[inline]
    pub fn lock_then<F, Ret>(&self, f: F) -> Ret
    where
        F: FnOnce(MutexGuard<'_, T, Rs, Rq>) -> Ret,
    {
        f(self.lock())
    }
}

impl<T: ?Sized, Rs, Rq> Mutex<T, Rs, Rq> {
    /// Attempts to acquire this mutex without blocking the thread.
    ///
    /// If the lock could not be acquired at this time, then [`None`] is returned.
    /// Otherwise, an RAII guard is returned. The lock will be unlocked when the
    /// guard is dropped.
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
    /// use mcslock::relax::{Spin, SpinBackoff};
    ///
    /// type SpinMutex<T> = Mutex::<T, SpinBackoff, Spin>;
    ///
    /// let mutex = Arc::new(SpinMutex::new(0));
    /// let c_mutex = Arc::clone(&mutex);
    ///
    /// thread::spawn(move || {
    ///     let mut guard = c_mutex.try_lock();
    ///     if let Some(mut guard) = guard {
    ///         *guard = 10;
    ///     } else {
    ///         println!("try_lock failed");
    ///     }
    /// })
    /// .join().expect("thread::spawn failed");
    ///
    /// assert_eq!(*mutex.lock(), 10);
    /// ```
    #[inline]
    pub fn try_lock(&self) -> Option<MutexGuard<'_, T, Rs, Rq>> {
        self.inner.try_lock().map(From::from)
    }

    /// Attempts to acquire this mutex and then runs a closure against its guard.
    ///
    /// If the lock could not be acquired at this time, then a [`None`] value is
    /// given back as the closure argument. If the lock has been acquired, then
    /// a [`Some`] value with the mutex guard is given instead. The lock will be
    /// unlocked when the guard is dropped.
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
    /// use mcslock::relax::{Spin, SpinBackoff};
    ///
    /// type SpinMutex<T> = Mutex::<T, SpinBackoff, Spin>;
    ///
    /// let mutex = Arc::new(SpinMutex::new(0));
    /// let c_mutex = Arc::clone(&mutex);
    ///
    /// thread::spawn(move || {
    ///     c_mutex.try_lock_then(|guard| {
    ///         if let Some(mut guard) = guard {
    ///             *guard = 10;
    ///         } else {
    ///             println!("try_lock_then failed");
    ///         }
    ///     });
    /// })
    /// .join().expect("thread::spawn failed");
    ///
    /// assert_eq!(mutex.lock_then(|guard| *guard), 10);
    /// ```
    ///
    /// Compile fail: borrows of the guard or its data cannot escape the given
    /// closure:
    ///
    /// ```compile_fail,E0515
    /// use mcslock::barging::spins::Mutex;
    ///
    /// let mutex = Mutex::new(1);
    /// let data = mutex.try_lock_then(|guard| &*guard.unwrap());
    /// ```
    #[inline]
    pub fn try_lock_then<F, Ret>(&self, f: F) -> Ret
    where
        F: FnOnce(Option<MutexGuard<'_, T, Rs, Rq>>) -> Ret,
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
    /// use mcslock::relax::{Spin, SpinBackoff};
    ///
    /// type SpinMutex<T> = Mutex<T, SpinBackoff, Spin>;
    ///
    /// let mutex = SpinMutex::new(0);
    /// let guard = mutex.lock();
    /// drop(guard);
    ///
    /// assert_eq!(mutex.is_locked(), false);
    /// ```
    #[inline]
    pub fn is_locked(&self) -> bool {
        self.inner.is_locked()
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
    /// use mcslock::relax::{Spin, SpinBackoff};
    ///
    /// type SpinMutex<T> = Mutex<T, SpinBackoff, Spin>;
    ///
    /// let mut mutex = SpinMutex::new(0);
    /// *mutex.get_mut() = 10;
    ///
    /// assert_eq!(*mutex.lock(), 10);
    /// ```
    #[cfg(not(all(loom, test)))]
    #[inline(always)]
    pub fn get_mut(&mut self) -> &mut T {
        self.inner.get_mut()
    }
}

impl<T: Default, Rs, Rq> Default for Mutex<T, Rs, Rq> {
    /// Creates a `Mutex<T, Rs, Rq>`, with the `Default` value for `T`.
    #[inline]
    fn default() -> Self {
        Self::new(Default::default())
    }
}

impl<T, Rs, Rq> From<T> for Mutex<T, Rs, Rq> {
    /// Creates a `Mutex<T, Rs, Rq>` from a instance of `T`.
    #[inline]
    fn from(data: T) -> Self {
        Self::new(data)
    }
}

impl<T: ?Sized + Debug, Rs, Rq> Debug for Mutex<T, Rs, Rq> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        self.inner.fmt(f)
    }
}

#[cfg(test)]
impl<T: ?Sized, Rs, Rq> LockNew for Mutex<T, Rs, Rq> {
    type Target = T;

    fn new(value: Self::Target) -> Self
    where
        Self::Target: Sized,
    {
        Self::new(value)
    }
}

#[cfg(test)]
impl<T: ?Sized, Rs: Relax, Rq: Relax> LockThen for Mutex<T, Rs, Rq> {
    type Guard<'a> = MutexGuard<'a, T, Rs, Rq>
    where
        Self: 'a,
        Self::Target: 'a;

    fn lock_then<F, Ret>(&self, f: F) -> Ret
    where
        F: FnOnce(MutexGuard<'_, T, Rs, Rq>) -> Ret,
    {
        self.lock_then(f)
    }
}

#[cfg(test)]
impl<T: ?Sized, Rs: Relax, Rq: Relax> TryLockThen for Mutex<T, Rs, Rq> {
    fn try_lock_then<F, Ret>(&self, f: F) -> Ret
    where
        F: FnOnce(Option<MutexGuard<'_, T, Rs, Rq>>) -> Ret,
    {
        self.try_lock_then(f)
    }

    fn is_locked(&self) -> bool {
        self.is_locked()
    }
}

#[cfg(all(not(loom), test))]
impl<T: ?Sized, Rs, Rq> crate::test::LockData for Mutex<T, Rs, Rq> {
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

#[cfg(all(feature = "lock_api", not(loom)))]
unsafe impl<Rs: Relax, Rq: Relax> lock_api::RawMutex for Mutex<(), Rs, Rq> {
    type GuardMarker = lock_api::GuardSend;

    // It is fine to const initialize `Mutex<(), Rs, Rq>` since the data is not
    // going to be shared. And since it is a `Unit` type, copies will be
    // optimized away.
    #[allow(clippy::declare_interior_mutable_const)]
    const INIT: Self = Self::new(());

    #[inline]
    fn lock(&self) {
        core::mem::forget(Self::lock(self));
    }

    #[inline]
    fn try_lock(&self) -> bool {
        Self::try_lock(self).map(core::mem::forget).is_some()
    }

    #[inline]
    unsafe fn unlock(&self) {
        self.inner.unlock();
    }

    #[inline]
    fn is_locked(&self) -> bool {
        self.is_locked()
    }
}

// The inner type of mutex's guard, with a boolean as the atomic data.
type GuardInner<'a, T, Rs, Rq> = inner::MutexGuard<'a, T, AtomicBool, RelaxWait<Rs>, RelaxWait<Rq>>;

/// An RAII implementation of a "scoped lock" of a mutex. When this structure is
/// dropped (falls out of scope), the lock will be unlocked.
///
/// The data protected by the mutex can be access through this guard via its
/// [`Deref`] and [`DerefMut`] implementations.
///
/// This structure is returned by [`lock`] and [`try_lock`] methods on [`Mutex`].
/// It is also given as closure parameter by [`lock_then`] and [`try_lock_then`]
/// methods.
///
/// [`Deref`]: core::ops::Deref
/// [`DerefMut`]: core::ops::DerefMut
/// [`lock`]: Mutex::lock
/// [`try_lock`]: Mutex::lock
/// [`lock_then`]: Mutex::lock_then
/// [`try_lock_then`]: Mutex::try_lock_then
#[must_use = "if unused the Mutex will immediately unlock"]
pub struct MutexGuard<'a, T: ?Sized, Rs, Rq> {
    inner: GuardInner<'a, T, Rs, Rq>,
}

// Same unsafe impls as `crate::inner::barging::MutexGuard`.
unsafe impl<T: ?Sized + Send, Rs, Rq> Send for MutexGuard<'_, T, Rs, Rq> {}
unsafe impl<T: ?Sized + Sync, Rs, Rq> Sync for MutexGuard<'_, T, Rs, Rq> {}

#[doc(hidden)]
impl<'a, T: ?Sized, Rs, Rq> From<GuardInner<'a, T, Rs, Rq>> for MutexGuard<'a, T, Rs, Rq> {
    fn from(inner: GuardInner<'a, T, Rs, Rq>) -> Self {
        Self { inner }
    }
}

impl<'a, T: ?Sized + Debug, Rs, Rq> Debug for MutexGuard<'a, T, Rs, Rq> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        self.inner.fmt(f)
    }
}

impl<'a, T: ?Sized + Display, Rs, Rq> Display for MutexGuard<'a, T, Rs, Rq> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        self.inner.fmt(f)
    }
}

#[cfg(not(all(loom, test)))]
impl<'a, T: ?Sized, Rs, Rq> core::ops::Deref for MutexGuard<'a, T, Rs, Rq> {
    type Target = T;

    /// Dereferences the guard to access the underlying data.
    #[inline(always)]
    fn deref(&self) -> &T {
        &self.inner
    }
}

#[cfg(not(all(loom, test)))]
impl<'a, T: ?Sized, Rs, Rq> core::ops::DerefMut for MutexGuard<'a, T, Rs, Rq> {
    /// Mutably dereferences the guard to access the underlying data.
    #[inline(always)]
    fn deref_mut(&mut self) -> &mut T {
        &mut self.inner
    }
}

/// SAFETY: A guard instance hold the lock locked, with exclusive access to the
/// underlying data.
#[cfg(all(loom, test))]
#[cfg(not(tarpaulin_include))]
unsafe impl<T: ?Sized, Rs, Rq> Guard for MutexGuard<'_, T, Rs, Rq> {
    type Target = T;

    fn get(&self) -> &loom::cell::UnsafeCell<Self::Target> {
        self.inner.get()
    }
}

#[cfg(all(loom, test))]
#[cfg(not(tarpaulin_include))]
impl<T: ?Sized, Rs, Rq> AsDeref for MutexGuard<'_, T, Rs, Rq> {
    type Target = T;

    type Deref<'a> = GuardDeref<'a, Self>
    where
        Self: 'a,
        Self::Target: 'a;

    fn as_deref(&self) -> Self::Deref<'_> {
        self.get_ref()
    }
}

#[cfg(all(loom, test))]
#[cfg(not(tarpaulin_include))]
impl<T: ?Sized, Rs, Rq> AsDerefMut for MutexGuard<'_, T, Rs, Rq> {
    type DerefMut<'a> = GuardDerefMut<'a, Self>
    where
        Self: 'a,
        Self::Target: 'a;

    fn as_deref_mut(&mut self) -> Self::DerefMut<'_> {
        self.get_mut()
    }
}

#[cfg(all(not(loom), test))]
mod test {
    use crate::barging::yields::Mutex;
    use crate::test::tests;

    #[test]
    fn node_waiter_drop_does_not_matter() {
        tests::node_waiter_drop_does_not_matter::<super::AtomicBool>();
    }

    #[test]
    fn lots_and_lots_lock() {
        tests::lots_and_lots_lock::<Mutex<_>>();
    }

    #[test]
    fn lots_and_lots_try_lock() {
        tests::lots_and_lots_try_lock::<Mutex<_>>();
    }

    #[test]
    fn lots_and_lots_mixed_lock() {
        tests::lots_and_lots_mixed_lock::<Mutex<_>>();
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
    use crate::barging::yields::Mutex;
    use crate::loom::models;

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
