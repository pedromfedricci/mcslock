use core::fmt::{self, Debug, Formatter};
use core::ops::{Deref, DerefMut};

use crate::inner::raw as inner;
use crate::parking::park::{Park, ParkWait};
use crate::parking::parker::Parker;

#[cfg(test)]
use crate::test::{LockNew, LockThen, LockWithThen, TryLockThen, TryLockWithThen};

/// A locally-accessible record for forming the waiting queue.
///
/// `MutexNode` is an opaque type that holds metadata for the [`Mutex`]'s
/// waiting queue. To acquire a MCS lock, an instance of queue node must be
/// reachable and mutably borrowed for the duration of some associate locking
/// closure. Once the closure goes out of scope, a node instance can be reused
/// as the backing allocation for another lock acquisition. See [`lock_with_then`]
/// and [`try_lock_with_then`] methods on [`Mutex`].
///
/// [`lock_with_then`]: Mutex::lock_with_then
/// [`try_lock_with_then`]: Mutex::try_lock_with_then
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
/// it is protecting. The data can only be accessed through closure parameters
/// provided by [`lock_then`], [`lock_with_then`], [`try_lock_then`] and
/// [`try_lock_with_then`] that guarantees that the data is only ever accessed
/// when the mutex is locked.
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
///         data.lock_with_then(&mut node, |data| {
///             *data += 1;
///             if *data == N {
///                 tx.send(()).unwrap();
///             }
///             // The lock is unlocked here at the end of the closure scope.
///         });
///     });
/// }
///
/// rx.recv().unwrap();
/// ```
/// [`new`]: Mutex::new
/// [`lock_then`]: Mutex::lock_then
/// [`lock_with_then`]: Mutex::lock_with_then
/// [`try_lock_then`]: Mutex::try_lock_then
/// [`try_lock_with_then`]: Mutex::try_lock_with_then
pub struct Mutex<T: ?Sized, P> {
    pub(super) inner: inner::Mutex<T, Parker, ParkWait<P>>,
}

// SAFETY: `inner::Mutex` is `Send` if `T` is `Send`.
unsafe impl<T: ?Sized + Send, P> Send for Mutex<T, P> {}
// SAFETY: `inner::Mutex` is `Sync` if `T` is `Send`.
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
    /// Attempts to acquire this mutex and then runs a closure against the
    /// proteced data.
    ///
    /// If the lock could not be acquired at this time, then [`None`] is returned.
    /// Otherwise, an [`Some`] with a `&mut T` is returned. The lock will be
    /// unlocked once the closure goes out of scope.
    ///
    /// This function transparently allocates a [`MutexNode`] in the stack for
    /// each call, and so it will not reuse the same node for other calls.
    /// Consider callig [`try_lock_with_then`] if you want to reuse node
    /// allocations.
    ///
    /// This function does not block.
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
    ///     c_mutex.try_lock_then(|data| {
    ///         if let Some(data) = data {
    ///             *data = 10;
    ///         } else {
    ///             println!("try_lock failed");
    ///         }
    ///     });
    /// })
    /// .join().expect("thread::spawn failed");
    ///
    /// let value = mutex.lock_then(|data| *data);
    /// assert_eq!(value, 10);
    /// ```
    ///
    /// Compile fail: borrows of the data cannot escape the given closure:
    ///
    /// ```compile_fail,E0515
    /// use mcslock::parking::raw::spins::Mutex;
    ///
    /// let mutex = Mutex::new(1);
    /// let borrow = mutex.try_lock_then(|data| &*data.unwrap());
    /// ```
    /// [`try_lock_with_then`]: Mutex::try_lock_with_then
    #[inline]
    pub fn try_lock_then<F, Ret>(&self, f: F) -> Ret
    where
        F: FnOnce(Option<&mut T>) -> Ret,
    {
        self.try_lock_with_then(&mut MutexNode::new(), f)
    }

    /// Attempts to acquire this mutex and then runs a closure against the
    /// protected data.
    ///
    /// If the lock could not be acquired at this time, then [`None`] is returned.
    /// Otherwise, an [`Some`] with a `&mut T` is returned. The lock will be
    /// unlocked once the closure goes out of scope.
    ///
    /// To acquire a MCS lock through this function, it's also required a mutably
    /// borrowed queue node, which is a record that keeps a link for forming the
    /// queue, see [`MutexNode`].
    ///
    /// This function does not block.
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
    ///     c_mutex.try_lock_with_then(&mut node, |data| {
    ///         if let Some(data) = data {
    ///             *data = 10;
    ///         } else {
    ///             println!("try_lock failed");
    ///         }
    ///     });
    /// })
    /// .join().expect("thread::spawn failed");
    ///
    /// let mut node = MutexNode::new();
    /// let value = mutex.lock_with_then(&mut node, |data| *data);
    /// assert_eq!(value, 10);
    /// ```
    ///
    /// Compile fail: borrows of the data cannot escape the given closure:
    ///
    /// ```compile_fail,E0515
    /// use mcslock::parking::raw::{spins::Mutex, MutexNode};
    ///
    /// let mutex = Mutex::new(1);
    /// let mut node = MutexNode::new();
    /// let borrow = mutex.try_lock_with_then(&mut node, |data| &*data.unwrap());
    /// ```
    #[inline]
    pub fn try_lock_with_then<'a, F, Ret>(&'a self, node: &'a mut MutexNode, f: F) -> Ret
    where
        F: FnOnce(Option<&mut T>) -> Ret,
    {
        self.inner.try_lock_with_then(&mut node.inner, f)
    }

    /// Acquires this mutex and then runs the closure against the protected data.
    ///
    /// This function will block the local thread until it is available to acquire
    /// the mutex. Upon acquiring the mutex, the user provided closure will be
    /// executed against the mutex proteced data. Once the closure goes out of
    /// scope, it will unlock the mutex.
    ///
    /// This function transparently allocates a [`MutexNode`] in the stack for
    /// each call, and so it will not reuse the same node for other calls.
    /// Consider callig [`lock_with_then`] if you want to reuse node
    /// allocations.
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
    ///     c_mutex.lock_then(|data| *data = 10);
    /// })
    /// .join().expect("thread::spawn failed");
    ///
    /// assert_eq!(mutex.lock_then(|data| *data), 10);
    /// ```
    ///
    /// Compile fail: borrows of the data cannot escape the given closure:
    ///
    /// ```compile_fail,E0515
    /// use mcslock::parking::raw::spins::Mutex;
    ///
    /// let mutex = Mutex::new(1);
    /// let borrow = mutex.lock_then(|data| &*data);
    /// ```
    /// [`lock_with_then`]: Mutex::lock_with_then
    #[inline]
    pub fn lock_then<F, Ret>(&self, f: F) -> Ret
    where
        F: FnOnce(&mut T) -> Ret,
    {
        self.lock_with_then(&mut MutexNode::new(), f)
    }

    /// Acquires this mutex and then runs the closure against the proteced data.
    ///
    /// This function will block the local thread until it is available to acquire
    /// the mutex. Upon acquiring the mutex, the user provided closure will be
    /// executed against the mutex proteced data. Once the closure goes out of
    /// scope, it will unlock the mutex.
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
    ///     c_mutex.lock_with_then(&mut node, |data| {
    ///         *data = 10;
    ///     });
    /// })
    /// .join().expect("thread::spawn failed");
    ///
    /// let mut node = MutexNode::new();
    /// assert_eq!(mutex.lock_with_then(&mut node, |data| *data), 10);
    /// ```
    ///
    /// Compile fail: borrows of the data cannot escape the given closure:
    ///
    /// ```compile_fail,E0515
    /// use mcslock::parking::raw::{spins::Mutex, MutexNode};
    ///
    /// let mutex = Mutex::new(1);
    /// let mut node = MutexNode::new();
    /// let borrow = mutex.lock_with_then(&mut node, |data| &*data);
    /// ```
    #[inline]
    pub fn lock_with_then<'a, F, Ret>(&'a self, node: &'a mut MutexNode, f: F) -> Ret
    where
        F: FnOnce(&mut T) -> Ret,
    {
        self.inner.lock_with_then(&mut node.inner, f)
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
    /// use mcslock::parking::raw;
    /// use mcslock::parking::park::SpinThenPark;
    ///
    /// type Mutex<T> = raw::Mutex<T, SpinThenPark>;
    ///
    /// let mutex = Mutex::new(0);
    ///
    /// mutex.lock_then(|_data| {
    ///     assert_eq!(mutex.is_locked(), true);
    /// });
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
    /// use mcslock::parking::raw;
    /// use mcslock::parking::park::SpinThenPark;
    ///
    /// type Mutex<T> = raw::Mutex<T, SpinThenPark>;
    ///
    /// let mut mutex = Mutex::new(0);
    /// *mutex.get_mut() = 10;
    ///
    /// assert_eq!(mutex.lock_then(|data| *data), 10);
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
impl<T: ?Sized, P: Park> LockWithThen for Mutex<T, P> {
    type Node = MutexNode;

    type Guard<'a>
        = &'a mut Self::Target
    where
        Self: 'a,
        Self::Target: 'a;

    fn lock_with_then<F, Ret>(&self, node: &mut Self::Node, f: F) -> Ret
    where
        F: FnOnce(&mut Self::Target) -> Ret,
    {
        self.lock_with_then(node, f)
    }
}

#[cfg(test)]
impl<T: ?Sized, P: Park> TryLockWithThen for Mutex<T, P> {
    fn try_lock_with_then<F, Ret>(&self, node: &mut Self::Node, f: F) -> Ret
    where
        F: FnOnce(Option<&mut Self::Target>) -> Ret,
    {
        self.try_lock_with_then(node, f)
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

#[cfg(test)]
impl<T: ?Sized, P: Park> LockThen for Mutex<T, P> {
    fn lock_then<F, Ret>(&self, f: F) -> Ret
    where
        F: FnOnce(&mut Self::Target) -> Ret,
    {
        self.lock_then(f)
    }
}

#[cfg(test)]
impl<T: ?Sized, P: Park> TryLockThen for Mutex<T, P> {
    fn try_lock_then<F, Ret>(&self, f: F) -> Ret
    where
        F: FnOnce(Option<&mut Self::Target>) -> Ret,
    {
        self.try_lock_then(f)
    }
}

#[cfg(all(not(loom), test))]
mod test {
    use crate::parking::raw::{immediate, yields};
    use crate::test::tests;

    type Mutex<T> = immediate::Mutex<T>;

    #[test]
    fn node_waiter_drop_does_not_matter() {
        tests::node_waiter_drop_does_not_matter::<super::Parker>();
    }

    #[test]
    fn lots_and_lots_lock_yield_backoff_then_park() {
        tests::lots_and_lots_lock::<yields::backoff::Mutex<_>>();
    }

    #[test]
    fn lots_and_lots_try_lock_yield_backoff_then_park() {
        tests::lots_and_lots_try_lock::<yields::backoff::Mutex<_>>();
    }

    #[test]
    fn lots_and_lots_mixed_lock_yield_backoff_then_park() {
        tests::lots_and_lots_mixed_lock::<yields::backoff::Mutex<_>>();
    }

    #[test]
    fn smoke() {
        tests::smoke::<Mutex<_>>();
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
    use crate::parking::raw::immediate::Mutex;

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
