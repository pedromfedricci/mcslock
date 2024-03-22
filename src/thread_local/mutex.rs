use core::cell::{RefCell, RefMut};
use core::fmt::{self, Debug, Display};
use core::marker::PhantomData;
use core::panic::Location;

use crate::raw::{Mutex as RawMutex, MutexGuard as RawMutexGuard, MutexNode};
use crate::relax::Relax;

#[cfg(test)]
use crate::test::{LockNew, LockWith};

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
#[cfg(not(tarpaulin_include))]
loom::thread_local! {
    static NODE: RefCell<MutexNode> = {
        RefCell::new(MutexNode::new())
    }
}

/// The panic message as a string literal.
macro_rules! literal_panic_msg {
    () => {
        "a thread local MCS lock is already held by this thread"
    };
}

/// Panics the thread with a message pointing to the panic location.
#[inline(never)]
#[cold]
fn panic_already_held(caller: &Location<'static>) -> ! {
    panic!("{}, conflict at: {}", literal_panic_msg!(), caller)
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
    #[cfg(not(tarpaulin_include))]
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
    #[inline(always)]
    pub fn into_inner(self) -> T {
        self.0.into_inner()
    }
}

impl<T: ?Sized, R: Relax> Mutex<T, R> {
    /// Attempts to acquire this mutex and then runs a closure against its guard.
    ///
    /// If the lock could not be acquired at this time, then a [`None`] value is
    /// given back as the closure argument. If the lock has been acquired, then
    /// a [`Some`] value with the mutex guard is given instead. The lock will be
    /// unlocked when the guard is dropped.
    ///
    /// This function does not block.
    ///
    /// # Panics
    ///
    /// At most one [`thread_local::Mutex`] may be held within a single thread at
    /// any time. Trying to acquire a second lock while a guard is still alive
    /// will cause a panic.
    ///
    /// [`thread_local::Mutex`]: Mutex
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
    /// mutex.lock_with(|_guard| {
    ///     let mutex = SpinMutex::new(());
    ///     // Acquiring more than one thread_local::Mutex within a single
    ///     // thread at the same time is not allowed, this will panic.
    ///     mutex.try_lock_with(|_guard| ());
    /// });
    /// ```
    #[inline]
    #[track_caller]
    pub fn try_lock_with<F, Ret>(&self, f: F) -> Ret
    where
        F: FnOnce(Option<MutexGuard<'_, T, R>>) -> Ret,
    {
        self.with_borrow_mut(|raw, node| f(MutexGuard::try_new(raw, node)))
    }

    /// Attempts to acquire this mutex and then runs a closure against its guard.
    ///
    /// If the lock could not be acquired at this time, then a [`None`] value is
    /// given back as the closure argument. If the lock has been acquired, then
    /// a [`Some`] value with the mutex guard is given instead. The lock will be
    /// unlocked when the guard is dropped.
    ///
    /// This function does not block, and also does not check if the thread local
    /// node is already in use.
    ///
    /// # Safety
    ///
    /// At most one [`thread_local::Mutex`] may be held within a single thread at
    /// any time. Trying to acquire a second lock while a guard is still alive
    /// is undefined behavior.
    ///
    /// [`thread_local::Mutex`]: Mutex
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
    /// thread::spawn(move || unsafe {
    ///     c_mutex.try_lock_with_unchecked(|guard| {
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
    /// let data = unsafe { mutex.try_lock_with_unchecked(|g| &*g.unwrap()) };
    /// ```
    ///
    /// An example of undefined behavior:
    ///
    /// ```no_run
    /// use mcslock::thread_local::Mutex;
    /// use mcslock::relax::Spin;
    ///
    /// type SpinMutex<T> = Mutex<T, Spin>;
    ///
    /// let mutex = SpinMutex::new(0);
    ///
    /// mutex.lock_with(|_guard| unsafe {
    ///     let mutex = SpinMutex::new(());
    ///     // Acquiring more than one thread_local::Mutex within a single
    ///     // thread at the same time is not allowed, this is UB.
    ///     mutex.try_lock_with_unchecked(|_guard| ());
    /// });
    /// ```
    #[inline]
    pub unsafe fn try_lock_with_unchecked<F, Ret>(&self, f: F) -> Ret
    where
        F: FnOnce(Option<MutexGuard<'_, T, R>>) -> Ret,
    {
        self.with_borrow_mut_unchecked(|raw, node| f(MutexGuard::try_new(raw, node)))
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
    /// # Panics
    ///
    /// At most one [`thread_local::Mutex`] may be held within a single thread at
    /// any time. Trying to acquire a second lock while a guard is still alive
    /// will cause a panic.
    ///
    /// [`thread_local::Mutex`]: Mutex
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
    ///     mutex.lock_with(|_guard| ());
    /// });
    /// ```
    #[inline]
    #[track_caller]
    pub fn lock_with<F, Ret>(&self, f: F) -> Ret
    where
        F: FnOnce(MutexGuard<'_, T, R>) -> Ret,
    {
        self.with_borrow_mut(|raw, node| f(MutexGuard::new(raw, node)))
    }

    /// Acquires this mutex and then runs the closure against its guard.
    ///
    /// This function will block the local thread until it is available to acquire
    /// the mutex. Upon acquiring the mutex, the user provided closure will be
    /// executed against the mutex guard. Once the guard goes out of scope, it
    /// will unlock the mutex.
    ///
    /// This function will block if the lock is unavailable, and also does not
    /// check if the thread local node is already in use.
    ///
    /// # Safety
    ///
    /// At most one [`thread_local::Mutex`] may be held within a single thread at
    /// any time. Trying to acquire a second lock while a guard is still alive
    /// is undefined behavior.
    ///
    /// [`thread_local::Mutex`]: Mutex
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
    ///     unsafe { c_mutex.lock_with_unchecked(|mut g| *g = 10) };
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
    /// let data = unsafe { mutex.lock_with_unchecked(|g| &*g) };
    /// ```
    ///
    /// An example of undefined behavior:
    ///
    /// ```no_run
    /// use mcslock::thread_local::Mutex;
    /// use mcslock::relax::Spin;
    ///
    /// type SpinMutex<T> = Mutex<T, Spin>;
    ///
    /// let mutex = SpinMutex::new(0);
    ///
    /// mutex.lock_with(|_guard| unsafe {
    ///     let mutex = SpinMutex::new(());
    ///     // Acquiring more than one thread_local::Mutex within a single
    ///     // thread at the same time is not allowed, this is UB.
    ///     mutex.lock_with_unchecked(|_guard| ());
    /// });
    /// ```
    #[inline]
    pub unsafe fn lock_with_unchecked<F, Ret>(&self, f: F) -> Ret
    where
        F: FnOnce(MutexGuard<'_, T, R>) -> Ret,
    {
        self.with_borrow_mut_unchecked(|raw, node| f(MutexGuard::new(raw, node)))
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
    #[inline(always)]
    pub fn get_mut(&mut self) -> &mut T {
        self.0.get_mut()
    }

    /// Runs `f` over a raw mutex and thread local node as arguments.
    ///
    /// # Panics
    ///
    /// Will panic if the thread local [`MutexNode`] is already in use by a
    /// lock guard from the same thread.
    #[track_caller]
    fn with_borrow_mut<F, Ret>(&self, f: F) -> Ret
    where
        F: FnOnce(&RawMutex<T, R>, &mut MutexNode) -> Ret,
    {
        let caller = Location::caller();
        let panic = |_| panic_already_held(caller);
        let f = |mut node: RefMut<_>| f(&self.0, &mut node);
        NODE.with(|node| node.try_borrow_mut().map_or_else(panic, f))
    }

    /// Runs 'f' over the a raw mutex and thread local node as arguments without
    /// checking if the node is currently mutably borrowed.
    ///
    /// # Safety
    ///
    /// Mutably borrowing a [`RefCell`] while references are still live is
    /// undefined behaviour. This means that two or more guards can not be in
    /// scope within a single thread at the same time.
    unsafe fn with_borrow_mut_unchecked<F, Ret>(&self, f: F) -> Ret
    where
        F: FnOnce(&RawMutex<T, R>, &mut MutexNode) -> Ret,
    {
        // SAFETY: Caller guaranteed that no other references are live.
        NODE.with(|node| f(&self.0, unsafe { &mut *node.as_ptr() }))
    }
}

impl<T: ?Sized + Default, R> Default for Mutex<T, R> {
    /// Creates a `Mutex<T, R>` with the `Default` value for `T`.
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
        self.try_lock_with(|guard| match guard {
            Some(guard) => guard.inner.with(|data| d.field("data", &data)),
            None => d.field("data", &format_args!("<locked>")),
        });
        d.finish()
    }
}

#[cfg(test)]
impl<T: ?Sized, R> LockNew for Mutex<T, R> {
    type Target = T;

    fn new(value: Self::Target) -> Self
    where
        Self::Target: Sized,
    {
        Self::new(value)
    }
}

#[cfg(test)]
impl<T: ?Sized, R: Relax> LockWith for Mutex<T, R> {
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

/// A type that calls the unchecked versions of `lock_with` and `try_lock_with`
/// when implementing the `LockWith` trait.
#[cfg(test)]
struct MutexUnchecked<T: ?Sized, R>(Mutex<T, R>);

#[cfg(test)]
impl<T: ?Sized, R> LockNew for MutexUnchecked<T, R> {
    type Target = T;

    fn new(value: Self::Target) -> Self
    where
        Self::Target: Sized,
    {
        Self(Mutex::new(value))
    }
}

/// Implements the test locking interface to verify the unchecked APIs:
/// `lock_with_unchecked` and `try_lock_with_unchecked`.
///
/// # Safety
///
/// Callers must guarantee that no more than ONE mutex guard is alive at any
/// time within a single thread. When failling to do so under Miri testing, Miri
/// has flagged the test as invoking UB, which is nice. Loom execution does not
/// necessarily catch such problems, although those can inadvertently break the
/// memory model invariants which will then fire Loom errors.
#[cfg(test)]
impl<T: ?Sized, R: Relax> LockWith for MutexUnchecked<T, R> {
    type Guard<'a> = MutexGuard<'a, Self::Target, R>
    where
        Self: 'a,
        Self::Target: 'a;

    fn try_lock_with<F, Ret>(&self, f: F) -> Ret
    where
        F: FnOnce(Option<MutexGuard<'_, T, R>>) -> Ret,
    {
        unsafe { self.0.try_lock_with_unchecked(f) }
    }

    fn lock_with<F, Ret>(&self, f: F) -> Ret
    where
        F: FnOnce(MutexGuard<'_, T, R>) -> Ret,
    {
        unsafe { self.0.lock_with_unchecked(f) }
    }

    fn is_locked(&self) -> bool {
        self.0.is_locked()
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
/// [`Deref`]: core::ops::Deref
/// [`DerefMut`]: core::ops::DerefMut
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
    /// Creates a new guard instance from a raw guard.
    fn raw(inner: RawMutexGuard<'a, T, R>) -> Self {
        Self { inner, marker: PhantomData }
    }

    /// Creates a new guard instance only if the mutex is not already locked.
    fn try_new(mutex: &'a RawMutex<T, R>, node: &'a mut MutexNode) -> Option<Self> {
        mutex.try_lock(node).map(Self::raw)
    }

    /// Creates a new guard instance by locking a raw mutex.
    fn new(mutex: &'a RawMutex<T, R>, node: &'a mut MutexNode) -> Self {
        Self::raw(mutex.lock(node))
    }
}

impl<'a, T: ?Sized + Debug, R: Relax> Debug for MutexGuard<'a, T, R> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.inner.fmt(f)
    }
}

impl<'a, T: ?Sized + Display, R: Relax> Display for MutexGuard<'a, T, R> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.inner.fmt(f)
    }
}

#[cfg(not(all(loom, test)))]
impl<'a, T: ?Sized, R: Relax> core::ops::Deref for MutexGuard<'a, T, R> {
    type Target = T;

    /// Dereferences the guard to access the underlying data.
    #[inline(always)]
    fn deref(&self) -> &T {
        &self.inner
    }
}

#[cfg(not(all(loom, test)))]
impl<'a, T: ?Sized, R: Relax> core::ops::DerefMut for MutexGuard<'a, T, R> {
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
unsafe impl<T: ?Sized, R: Relax> crate::loom::Guard for MutexGuard<'_, T, R> {
    type Target = T;

    fn get(&self) -> &loom::cell::UnsafeCell<Self::Target> {
        self.inner.get()
    }
}

#[cfg(all(not(loom), test))]
mod test {
    use crate::relax::Yield;
    use crate::test::tests;
    use crate::thread_local::yields::Mutex;

    type MutexUnchecked<T> = super::MutexUnchecked<T, Yield>;

    #[test]
    fn lots_and_lots() {
        tests::lots_and_lots::<Mutex<_>>();
    }

    #[test]
    fn lots_and_lots_unchecked() {
        tests::lots_and_lots::<MutexUnchecked<_>>();
    }

    #[test]
    fn smoke() {
        tests::smoke::<Mutex<_>>();
    }

    #[test]
    fn smoke_unchecked() {
        tests::smoke::<MutexUnchecked<_>>();
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
    fn test_try_lock_unchecked() {
        tests::test_try_lock::<MutexUnchecked<_>>();
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
    #[should_panic = literal_panic_msg!()]
    fn test_lock_arc_nested() {
        tests::test_lock_arc_nested::<Mutex<_>, Mutex<_>>();
    }

    #[test]
    #[should_panic = literal_panic_msg!()]
    fn test_acquire_more_than_one_lock() {
        tests::test_acquire_more_than_one_lock::<Mutex<_>>();
    }

    #[test]
    fn test_lock_arc_access_in_unwind() {
        tests::test_lock_arc_access_in_unwind::<Mutex<_>>();
    }

    #[test]
    fn test_lock_arc_access_in_unwind_uncheckd() {
        tests::test_lock_arc_access_in_unwind::<MutexUnchecked<_>>();
    }

    #[test]
    fn test_lock_unsized() {
        tests::test_lock_unsized::<Mutex<_>>();
    }

    #[test]
    fn test_lock_unsized_unchecked() {
        tests::test_lock_unsized::<MutexUnchecked<_>>();
    }
}

#[cfg(all(loom, test))]
mod model {
    use super::MutexUnchecked as InnerUnchecked;

    use crate::loom::models;
    use crate::relax::Yield;
    use crate::thread_local::yields::Mutex;

    type MutexUnchecked<T> = InnerUnchecked<T, Yield>;

    #[test]
    fn try_lock_join() {
        models::try_lock_join::<Mutex<_>>();
    }

    #[test]
    fn try_lock_join_unchecked() {
        models::try_lock_join::<MutexUnchecked<_>>();
    }

    #[test]
    fn lock_join() {
        models::lock_join::<Mutex<_>>();
    }

    #[test]
    fn lock_join_unchecked() {
        models::lock_join::<MutexUnchecked<_>>();
    }

    #[test]
    fn mixed_lock_join() {
        models::mixed_lock_join::<Mutex<_>>();
    }

    #[test]
    fn mixed_lock_join_unchecked() {
        models::mixed_lock_join::<MutexUnchecked<_>>();
    }
}
