use core::fmt;
use core::marker::PhantomData;
use core::sync::atomic::Ordering::{Acquire, Relaxed, Release};

use crate::cfg::atomic::AtomicBool;
use crate::cfg::cell::WithUnchecked;
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
    #[cfg(not(tarpaulin_include))]
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
    #[inline(always)]
    pub fn into_inner(self) -> T {
        self.inner.into_inner()
    }
}

impl<T: ?Sized, R: Relax> Mutex<T, R> {
    /// Acquires this mutex, blocking the current thread until it is able to do so.
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
    #[inline]
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
    #[inline]
    pub fn lock_with<F, Ret>(&self, f: F) -> Ret
    where
        F: FnOnce(MutexGuard<'_, T, R>) -> Ret,
    {
        f(self.lock())
    }
}

impl<T: ?Sized, R> Mutex<T, R> {
    /// Attempts to acquire this mutex without blocking the thread.
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
    pub fn try_lock(&self) -> Option<MutexGuard<'_, T, R>> {
        self.locked
            .compare_exchange(false, true, Acquire, Relaxed)
            .map(|_| MutexGuard::new(self))
            .ok()
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
    /// use mcslock::barging::spins::Mutex;
    ///
    /// let mutex = Mutex::new(1);
    /// let data = mutex.try_lock_with(|guard| &*guard.unwrap());
    /// ```
    #[inline]
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
    #[inline(always)]
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
}

impl<T: ?Sized + Default, R> Default for Mutex<T, R> {
    /// Creates a `Mutex<T, R>`, with the `Default` value for `T`.
    #[inline]
    fn default() -> Self {
        Self::new(Default::default())
    }
}

impl<T, R> From<T> for Mutex<T, R> {
    /// Creates a `Mutex<T, R>` from a instance of `T`.
    #[inline]
    fn from(data: T) -> Self {
        Self::new(data)
    }
}

impl<T: ?Sized + fmt::Debug, R: Relax> fmt::Debug for Mutex<T, R> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut d = f.debug_struct("Mutex");
        match self.try_lock() {
            Some(guard) => guard.with(|data| d.field("data", &data)),
            None => d.field("data", &format_args!("<locked>")),
        };
        d.finish()
    }
}

#[cfg(test)]
impl<T: ?Sized, R> crate::test::LockNew for Mutex<T, R> {
    type Target = T;

    fn new(value: Self::Target) -> Self
    where
        Self::Target: Sized,
    {
        Self::new(value)
    }
}

#[cfg(test)]
impl<T: ?Sized, R: Relax> crate::test::LockWith for Mutex<T, R> {
    type Guard<'a> = MutexGuard<'a, Self::Target, R>
    where
        Self: 'a,
        Self::Target: 'a;

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

    fn is_locked(&self) -> bool {
        self.is_locked()
    }
}

#[cfg(all(not(loom), test))]
impl<T: ?Sized, R> crate::test::LockData for Mutex<T, R> {
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
unsafe impl<R: Relax> lock_api::RawMutex for Mutex<(), R> {
    type GuardMarker = lock_api::GuardSend;

    // It is fine to const initialize `Mutex<(), R>` since the data is not going
    // to be shared. And since it is a `Unit` type, copies will be optimized away.
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
        self.unlock();
    }

    #[inline]
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
/// [`Deref`]: core::ops::Deref
/// [`DerefMut`]: core::ops::DerefMut
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

    /// Runs `f` against an shared reference pointing to the underlying data.
    fn with<F, Ret>(&self, f: F) -> Ret
    where
        F: FnOnce(&T) -> Ret,
    {
        // SAFETY: A guard instance holds the lock locked.
        unsafe { self.lock.inner.data.with_unchecked(f) }
    }
}

impl<T: ?Sized, R> Drop for MutexGuard<'_, T, R> {
    #[inline(always)]
    fn drop(&mut self) {
        self.lock.unlock();
    }
}

impl<'a, T: ?Sized + fmt::Debug, R> fmt::Debug for MutexGuard<'a, T, R> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.with(|data| fmt::Debug::fmt(data, f))
    }
}

impl<'a, T: ?Sized + fmt::Display, R> fmt::Display for MutexGuard<'a, T, R> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.with(|data| fmt::Display::fmt(data, f))
    }
}

#[cfg(not(all(loom, test)))]
impl<'a, T: ?Sized, R> core::ops::Deref for MutexGuard<'a, T, R> {
    type Target = T;

    /// Dereferences the guard to access the underlying data.
    #[inline(always)]
    fn deref(&self) -> &T {
        // SAFETY: A guard instance holds the lock locked.
        unsafe { &*self.lock.inner.data.get() }
    }
}

#[cfg(not(all(loom, test)))]
impl<'a, T: ?Sized, R> core::ops::DerefMut for MutexGuard<'a, T, R> {
    /// Mutably dereferences the guard to access the underlying data.
    #[inline(always)]
    fn deref_mut(&mut self) -> &mut T {
        // SAFETY: A guard instance holds the lock locked.
        unsafe { &mut *self.lock.inner.data.get() }
    }
}

/// SAFETY: A guard instance hold the lock locked, with exclusive access to the
/// underlying data.
#[cfg(all(loom, test))]
#[cfg(not(tarpaulin_include))]
unsafe impl<T: ?Sized, R> crate::loom::Guard for MutexGuard<'_, T, R> {
    type Target = T;

    fn get(&self) -> &loom::cell::UnsafeCell<Self::Target> {
        &self.lock.inner.data
    }
}

#[cfg(all(not(loom), test))]
mod test {
    use crate::barging::yields::Mutex;
    use crate::test::tests;

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
