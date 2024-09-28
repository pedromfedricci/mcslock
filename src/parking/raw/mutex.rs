use core::fmt::{self, Debug, Display, Formatter};
use core::ops::{Deref, DerefMut};

use crate::inner::raw as inner;
use crate::parking::park::{Park, ParkWait};
use crate::parking::parker::Parker;

#[cfg(test)]
use crate::test::{LockNew, LockWith};

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
#[repr(transparent)]
pub struct MutexNode {
    inner: inner::MutexNode<Parker>,
}

impl MutexNode {
    /// Creates new `MutexNode` instance.
    ///
    /// # Examples
    ///
    /// ```
    /// use mcslock::parking::raw::MutexNode;
    ///
    /// let node = MutexNode::new();
    /// ```
    #[must_use]
    #[inline(always)]
    pub const fn new() -> Self {
        Self { inner: inner::MutexNode::new() }
    }
}

#[cfg(not(tarpaulin_include))]
#[doc(hidden)]
impl Deref for MutexNode {
    type Target = inner::MutexNode<Parker>;

    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}

#[doc(hidden)]
impl DerefMut for MutexNode {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.inner
    }
}

#[cfg(not(tarpaulin_include))]
impl Default for MutexNode {
    #[inline(always)]
    fn default() -> Self {
        Self::new()
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
/// use mcslock::parking::raw::{self, MutexNode};
/// use mcslock::parking::park::SpinThenPark;
///
/// type Mutex<T> = raw::Mutex<T, SpinThenPark>;
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
pub struct Mutex<T: ?Sized, P> {
    pub(super) inner: inner::Mutex<T, Parker, ParkWait<P>>,
}

// Same unsafe impls as `crate::inner::raw::Mutex`.
unsafe impl<T: ?Sized + Send, P> Send for Mutex<T, P> {}
unsafe impl<T: ?Sized + Send, P> Sync for Mutex<T, P> {}

impl<T, P> Mutex<T, P> {
    /// Creates a new mutex in an unlocked state ready for use.
    ///
    /// # Examples
    ///
    /// ```
    /// use mcslock::parking::raw;
    /// use mcslock::parking::park::SpinThenPark;
    ///
    /// type Mutex<T> = raw::Mutex<T, SpinThenPark>;
    ///
    /// const MUTEX: Mutex<i32> = Mutex::new(0);
    /// let mutex = Mutex::new(0);
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
    /// use mcslock::parking::raw;
    /// use mcslock::parking::park::SpinThenPark;
    ///
    /// type Mutex<T> = raw::Mutex<T, SpinThenPark>;
    ///
    /// let mutex = Mutex::new(0);
    /// assert_eq!(mutex.into_inner(), 0);
    /// ```
    #[inline(always)]
    pub fn into_inner(self) -> T {
        self.inner.into_inner()
    }
}

impl<T: ?Sized, P: Park> Mutex<T, P> {
    /// Attempts to acquire this mutex without blocking the thread.
    ///
    /// If the lock could not be acquired at this time, then [`None`] is returned.
    /// Otherwise, an RAII guard is returned. The lock will be unlocked when the
    /// guard is dropped.
    ///
    /// To acquire a MCS lock through this function, it's also required a mutably
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
    /// use mcslock::parking::raw::{self, MutexNode};
    /// use mcslock::parking::park::SpinThenPark;
    ///
    /// type Mutex<T> = raw::Mutex<T, SpinThenPark>;
    ///
    /// let mutex = Arc::new(Mutex::new(0));
    /// let c_mutex = Arc::clone(&mutex);
    ///
    /// thread::spawn(move || {
    ///     let mut node = MutexNode::new();
    ///     let mut guard = c_mutex.try_lock(&mut node);
    ///     if let Some(mut guard) = guard {
    ///         *guard = 10;
    ///     } else {
    ///         println!("try_lock failed");
    ///     }
    /// })
    /// .join().expect("thread::spawn failed");
    ///
    /// let mut node = MutexNode::new();
    /// assert_eq!(*mutex.lock(&mut node), 10);
    /// ```
    #[inline]
    pub fn try_lock<'a>(&'a self, node: &'a mut MutexNode) -> Option<MutexGuard<'a, T, P>> {
        self.inner.try_lock(&mut node.inner).map(From::from)
    }

    /// Attempts to acquire this mutex and then runs a closure against its guard.
    ///
    /// If the lock could not be acquired at this time, then a [`None`] value is
    /// given back as the closure argument. If the lock has been acquired, then
    /// a [`Some`] value with the mutex guard is given instead. The lock will be
    /// unlocked when the guard is dropped.
    ///
    /// This function instantiates a [`MutexNode`] for each call, which is
    /// convenient for one-liners by not particularly efficient on hot paths.
    /// If that is your use case, consider calling [`try_lock`] in busy loops
    /// while reusing one single node allocation.
    ///
    /// This function does not block.
    ///
    /// ```
    /// use std::sync::Arc;
    /// use std::thread;
    ///
    /// use mcslock::raw;
    /// use mcslock::parking::park::SpinThenPark;
    ///
    /// type Mutex<T> = raw::Mutex<T, SpinThenPark>;
    ///
    /// let mutex = Arc::new(Mutex::new(0));
    /// let c_mutex = Arc::clone(&mutex);
    ///
    /// thread::spawn(move || {
    ///     c_mutex.try_lock_with(|guard| {
    ///         if let Some(mut guard) = guard {
    ///             *guard = 10;
    ///         } else {
    ///             println!("try_lock_with failed");
    ///         }
    ///     });
    /// })
    /// .join().expect("thread::spawn failed");
    ///
    /// assert_eq!(mutex.lock_with(|guard| *guard), 10);
    /// ```
    ///
    /// Compile fail: borrows of the guard or its data cannot escape the given
    /// closure:
    ///
    /// ```compile_fail,E0515
    /// use mcslock::parking::raw::spins::Mutex;
    ///
    /// let mutex = Mutex::new(1);
    /// let data = mutex.try_lock_with(|guard| &*guard.unwrap());
    /// ```
    /// [`try_lock`]: Mutex::try_lock
    #[inline]
    pub fn try_lock_with<F, Ret>(&self, f: F) -> Ret
    where
        F: FnOnce(Option<MutexGuard<'_, T, P>>) -> Ret,
    {
        let mut node = MutexNode::new();
        f(self.try_lock(&mut node))
    }

    /// Acquires this mutex, blocking the current thread until it is able to do so.
    ///
    /// This function will block the local thread until it is available to acquire
    /// the mutex. Upon returning, the thread is the only thread with the lock
    /// held. An RAII guard is returned to allow scoped unlock of the lock. When
    /// the guard goes out of scope, the mutex will be unlocked.
    ///
    /// To acquire a MCS lock through this function, it's also required a mutably
    /// borrowed queue node, which is a record that keeps a link for forming the
    /// queue, see [`MutexNode`].
    ///
    /// This function will block if the lock is unavailable.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::sync::Arc;
    /// use std::thread;
    ///
    /// use mcslock::parking::raw::{self, MutexNode};
    /// use mcslock::parking::park::SpinThenPark;
    ///
    /// type Mutex<T> = raw::Mutex<T, SpinThenPark>;
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
    #[inline]
    pub fn lock<'a>(&'a self, node: &'a mut MutexNode) -> MutexGuard<'a, T, P> {
        self.inner.lock(&mut node.inner).into()
    }

    /// Acquires this mutex and then runs the closure against its guard.
    ///
    /// This function will block the local thread until it is available to acquire
    /// the mutex. Upon acquiring the mutex, the user provided closure will be
    /// executed against the mutex guard. Once the guard goes out of scope, it
    /// will unlock the mutex.
    ///
    /// This function instantiates a [`MutexNode`] for each call, which is
    /// convenient for one-liners by not particularly efficient on hot paths.
    /// If that is your use case, consider calling [`lock`] in the busy loop
    /// while reusing one single node allocation.
    ///
    /// This function will block if the lock is unavailable.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::sync::Arc;
    /// use std::thread;
    ///
    /// use mcslock::parking::raw;
    /// use mcslock::parking::park::SpinThenPark;
    ///
    /// type Mutex<T> = raw::Mutex<T, SpinThenPark>;
    ///
    /// let mutex = Arc::new(Mutex::new(0));
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
    /// Compile fail: borrows of the guard or its data cannot escape the given
    /// closure:
    ///
    /// ```compile_fail,E0515
    /// use mcslock::parking::raw::spins::Mutex;
    ///
    /// let mutex = Mutex::new(1);
    /// let data = mutex.lock_with(|guard| &*guard);
    /// ```
    /// [`lock`]: Mutex::lock
    #[inline]
    pub fn lock_with<F, Ret>(&self, f: F) -> Ret
    where
        F: FnOnce(MutexGuard<'_, T, P>) -> Ret,
    {
        let mut node = MutexNode::new();
        f(self.lock(&mut node))
    }
}

impl<T: ?Sized, P> Mutex<T, P> {
    #[inline]
    /// Returns `true` if the lock is currently held.
    ///
    /// This method does not provide any synchronization guarantees, so its only
    /// useful as a heuristic, and so must be considered not up to date.
    ///
    /// # Example
    ///
    /// ```
    /// use mcslock::parking::raw::{self, MutexNode};
    /// use mcslock::parking::park::SpinThenPark;
    ///
    /// type Mutex<T> = raw::Mutex<T, SpinThenPark>;
    ///
    /// let mutex = Mutex::new(0);
    /// let mut node = MutexNode::new();
    ///
    /// let guard = mutex.lock(&mut node);
    /// drop(guard);
    ///
    /// assert_eq!(mutex.is_locked(), false);
    /// ```
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
    /// use mcslock::raw::{self, MutexNode};
    /// use mcslock::parking::park::SpinThenPark;
    ///
    /// type Mutex<T> = raw::Mutex<T, SpinThenPark>;
    ///
    /// let mut mutex = Mutex::new(0);
    /// *mutex.get_mut() = 10;
    ///
    /// let mut node = MutexNode::new();
    /// assert_eq!(*mutex.lock(&mut node), 10);
    /// ```
    #[cfg(not(all(loom, test)))]
    #[inline(always)]
    pub fn get_mut(&mut self) -> &mut T {
        self.inner.get_mut()
    }
}

impl<T: Default, P> Default for Mutex<T, P> {
    /// Creates a `Mutex<T, P>`, with the `Default` value for `T`.
    #[inline]
    fn default() -> Self {
        Self::new(Default::default())
    }
}

impl<T, P> From<T> for Mutex<T, P> {
    /// Creates a `Mutex<T, P>` from a instance of `T`.
    #[inline]
    fn from(data: T) -> Self {
        Self::new(data)
    }
}

impl<T: ?Sized + Debug, P: Park> Debug for Mutex<T, P> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        self.inner.fmt(f)
    }
}

#[cfg(test)]
impl<T: ?Sized, P> LockNew for Mutex<T, P> {
    type Target = T;

    fn new(value: Self::Target) -> Self
    where
        Self::Target: Sized,
    {
        Self::new(value)
    }
}

#[cfg(test)]
impl<T: ?Sized, P: Park> LockWith for Mutex<T, P> {
    type Guard<'a> = MutexGuard<'a, Self::Target, P>
    where
        Self: 'a,
        Self::Target: 'a;

    fn try_lock_with<F, Ret>(&self, f: F) -> Ret
    where
        F: FnOnce(Option<MutexGuard<'_, T, P>>) -> Ret,
    {
        self.try_lock_with(f)
    }

    fn lock_with<F, Ret>(&self, f: F) -> Ret
    where
        F: FnOnce(MutexGuard<'_, T, P>) -> Ret,
    {
        self.lock_with(f)
    }

    fn is_locked(&self) -> bool {
        self.is_locked()
    }
}

#[cfg(all(not(loom), test))]
impl<T: ?Sized, P> crate::test::LockData for Mutex<T, P> {
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
pub struct MutexGuard<'a, T: ?Sized, P: Park> {
    inner: inner::MutexGuard<'a, T, Parker, ParkWait<P>>,
}

// Same unsafe impls as `crate::inner::raw::MutexGuard`.
unsafe impl<T: ?Sized + Send, P: Park> Send for MutexGuard<'_, T, P> {}
unsafe impl<T: ?Sized + Sync, P: Park> Sync for MutexGuard<'_, T, P> {}

#[doc(hidden)]
impl<'a, T: ?Sized, P: Park> From<inner::MutexGuard<'a, T, Parker, ParkWait<P>>>
    for MutexGuard<'a, T, P>
{
    fn from(inner: inner::MutexGuard<'a, T, Parker, ParkWait<P>>) -> Self {
        Self { inner }
    }
}

impl<'a, T: ?Sized + Debug, P: Park> Debug for MutexGuard<'a, T, P> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        self.inner.fmt(f)
    }
}

impl<'a, T: ?Sized + Display, P: Park> Display for MutexGuard<'a, T, P> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        self.inner.fmt(f)
    }
}

#[cfg(not(all(loom, test)))]
impl<'a, T: ?Sized, P: Park> Deref for MutexGuard<'a, T, P> {
    type Target = T;

    /// Dereferences the guard to access the underlying data.
    #[inline(always)]
    fn deref(&self) -> &T {
        &self.inner
    }
}

#[cfg(not(all(loom, test)))]
impl<'a, T: ?Sized, P: Park> DerefMut for MutexGuard<'a, T, P> {
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
unsafe impl<T: ?Sized, P: Park> crate::loom::Guard for MutexGuard<'_, T, P> {
    type Target = T;

    fn get(&self) -> &loom::cell::UnsafeCell<Self::Target> {
        self.inner.get()
    }
}

#[cfg(all(not(loom), test))]
mod test {
    use crate::parking::raw::{immediate, yields};
    use crate::test::tests;

    type Mutex<T> = immediate::Mutex<T>;

    type ImmediateMutex<T> = immediate::Mutex<T>;
    type YieldThenParkMutex<T> = yields::Mutex<T>;

    #[test]
    fn node_waiter_drop_does_not_matter() {
        tests::node_waiter_drop_does_not_matter::<super::Parker>();
    }

    #[test]
    fn lots_and_lots_lock_immediate_park() {
        tests::lots_and_lots_lock::<ImmediateMutex<_>>();
    }

    #[test]
    fn lots_and_lots_lock_yield_than_park() {
        tests::lots_and_lots_lock::<YieldThenParkMutex<_>>();
    }

    #[test]
    fn lots_and_lots_try_lock_immediate_park() {
        tests::lots_and_lots_try_lock::<ImmediateMutex<_>>();
    }

    #[test]
    fn lots_and_lots_try_lock_yield_than_park() {
        tests::lots_and_lots_try_lock::<YieldThenParkMutex<_>>();
    }

    #[test]
    fn lots_and_lots_mixed_lock_immediate_park() {
        tests::lots_and_lots_mixed_lock::<ImmediateMutex<_>>();
    }

    #[test]
    fn lots_and_lots_mixed_lock_yield_than_park() {
        tests::lots_and_lots_mixed_lock::<YieldThenParkMutex<_>>();
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
    use crate::parking::raw::{immediate, yields};

    #[test]
    fn try_lock_join_immediate_park() {
        models::try_lock_join::<immediate::Mutex<_>>();
    }

    #[test]
    fn lock_join_immediate_park() {
        models::lock_join::<immediate::Mutex<_>>();
    }

    #[test]
    fn mixed_lock_join_immediate_park() {
        models::mixed_lock_join::<immediate::Mutex<_>>();
    }

    #[test]
    fn try_lock_join_yield_than_park() {
        models::try_lock_join::<yields::Mutex<_>>();
    }

    #[test]
    fn lock_join_yield_than_park() {
        models::lock_join::<yields::Mutex<_>>();
    }

    #[test]
    fn mixed_lock_join_yield_than_park() {
        models::mixed_lock_join::<yields::Mutex<_>>();
    }
}
