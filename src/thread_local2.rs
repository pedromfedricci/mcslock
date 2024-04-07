//! TODO: Update
//! A MCS lock implementation that stores queue nodes in the thread local
//! storage of the waiting threads.
//!
//! The `thread_local` implementation of MCS lock is fair, that is, it
//! guarantees that thread that have waited for longer will be scheduled first
//! (FIFO). Each waiting thread will spin against its own, thread local atomic
//! lock state, which then avoids the network contention of the state access.
//!
//! This module provide MCS locking APIs that do not require user-side node
//! allocation, by managing the queue's node allocations internally. Queue
//! nodes are stored in the thread local storage, therefore this implementation
//! requires support from the standard library. Critical sections must be
//! provided to [`lock_with`] and [`try_lock_with`] as closures. Closure arguments
//! provide a RAII guard that has exclusive over the data. The mutex guard will
//! be dropped at the end of the call, freeing the mutex.
//!
//! The Mutex is generic over the relax strategy. User may choose a strategy
//! as long as it implements the [`Relax`] trait. There is a number of strategies
//! provided by the [`relax`] module. Each module in `thread_local` provides type
//! aliases for [`Mutex`] and [`MutexGuard`] associated with one relax strategy.
//! See their documentation for more information.
//!
//! # Panics
//!
//! The `thread_local` [`Mutex`] implementation only allows at most on lock held
//! within a single thread at any time. Trying to acquire a second lock while a
//! guard is alive will cause a panic. See [`lock_with`] and [`try_lock_with`]
//! functions for more information.
//!
//! [`lock_with`]: Mutex::lock_with
//! [`try_lock_with`]: Mutex::try_lock_with
//! [`relax`]: crate::relax
//! [`Relax`]: crate::relax::Relax

use core::cell::{RefCell, RefMut};
use core::panic::Location;

use crate::cfg::thread::LocalKey;
use crate::raw::{Mutex, MutexGuard, MutexNode};
use crate::relax::Relax;

/// A handle to a [`MutexNode`] stored at the thread local storage.
///
/// Thread local nodes can be claimed for temporary, exclusive access during
/// runtime for locking purposes. Node handles refer to the node stored at
/// the current running thread.
///
/// Just like `MutexNode`, this is an opaque type that holds metadata for the
/// [`raw::Mutex`]'s waiting queue. You must declare a thread local node with
/// the [`thread_local_node!`] macro, and provide the generated handle to the
/// appropriate [`raw::Mutex`] locking APIs. Attempting to lock a mutex with a
/// thread local node that already is in used for the locking thread will cause
/// a panic. Handles are provided by reference to functions.
///
/// See: [`try_lock_with_local`], [`lock_with_local`],
/// [`try_lock_with_local_unchecked`] or [`lock_with_local_unchecked`].
///
/// [`MutexNode`]: MutexNode
/// [`raw::Mutex`]: Mutex
/// [`thread_local_node!`]: crate::thread_local_node
/// [`try_lock_with_local`]: Mutex::try_lock_with_local
/// [`lock_with_local`]: Mutex::lock_with_local
/// [`try_lock_with_local_unchecked`]: Mutex::try_lock_with_local_unchecked
/// [`lock_with_local_unchecked`]: Mutex::lock_with_local_unchecked
#[repr(transparent)]
#[derive(Debug)]
pub struct LocalMutexNode {
    #[cfg(not(all(loom, test)))]
    key: LocalKey<RefCell<MutexNode>>,
    // We can't take ownership of Loom's `thread_local!` value since it is a
    // `static`, non-copy value, so we just point to it.
    #[cfg(all(loom, test))]
    key: &'static LocalKey<RefCell<MutexNode>>,
}

impl LocalMutexNode {
    /// Creates a new `LocalMutexNode` key from the provided thread local node
    /// key.
    ///
    /// This function is **NOT** part of the public API and so must not be
    /// called directly by user's code. It is subjected to changes **WITHOUT**
    /// prior notice or accompanied with relevant SemVer changes.
    #[cfg(not(all(loom, test)))]
    #[doc(hidden)]
    #[must_use]
    #[inline(always)]
    pub const fn __new(key: LocalKey<RefCell<MutexNode>>) -> Self {
        Self { key }
    }
}

/// Non-recursive definition of `thread_local_node!`.
///
/// This macro is **NOT** part of the public API and so must not be called
/// directly by user's code. It is subjected to changes **WITHOUT** prior
/// notice or accompanied with relevant SemVer changes.
#[cfg(not(all(loom, test)))]
#[doc(hidden)]
#[macro_export]
macro_rules! __thread_local_node_inner {
    ($vis:vis $node:ident) => {
        $vis const $node: $crate::thread_local2::LocalMutexNode = {
            ::std::thread_local! {
                static NODE: ::core::cell::RefCell<$crate::raw::MutexNode> = const {
                    ::core::cell::RefCell::new($crate::raw::MutexNode::new())
                };
            }
            $crate::thread_local2::LocalMutexNode::__new(NODE)
        };
    };
}

/// Non-recursive, Loom based definition of `thread_local_node!`.
///
/// This node definition uses Loom primitives and it can't be evaluated at
/// compile-time since Loom does not support that feature. Loom's `thread_local!`
/// macro defines a `static` value as oppose to std's `const` value.
#[cfg(all(loom, test))]
#[macro_export]
macro_rules! __thread_local_node_inner {
    ($vis:vis $node:ident) => {
        $vis static $node: $crate::thread_local2::LocalMutexNode = {
            ::loom::thread_local! {
                static NODE: ::core::cell::RefCell<$crate::raw::MutexNode> = {
                    ::core::cell::RefCell::new($crate::raw::MutexNode::new())
                };
            }
            $crate::thread_local2::LocalMutexNode { key: &NODE }
        };
    };
}

/// Declares a new [`LocalMutexNode`] key, which is a handle to the thread local
/// node of the currently running thread.
///
/// The macro wraps any number of static declarations and make them thread
/// local. Each provided name is associated with a single thread local key. The
/// keys are wrapped and managed by the [`LocalMutexNode`] type, which are the
/// actual handles meant to be used with the `lock_with_local` API family from
/// [`raw::Mutex`]. Handles are provided by reference to functions.
///
/// See: [`try_lock_with_local`], [`lock_with_local`],
/// [`try_lock_with_local_unchecked`] or [`lock_with_local_unchecked`].
///
/// The thread local node definition generated by this macro avoids lazy
/// initialization and does not need to be dropped, which enables a more
/// efficient underlying implementation. See [`std::thread_local!`] macro.
///
/// # Sintax
///
/// * Allows multiple static definitions, must be separated with semicolons.
/// * Visibility is optional (private by default).
/// * Requires `static` keyword and a **UPPER_SNAKE_CASE** name.
///
/// # Example
///
/// ```
/// use mcslock::raw::spins::Mutex;
///
/// // Multiple difenitions.
/// mcslock::thread_local_node! {
///     pub static NODE;
///     static OTHER_NODE1;
/// }
///
/// // Single definition.
/// mcslock::thread_local_node!(pub static OTHER_NODE2);
///
/// let mutex = Mutex::new(0);
/// // Keys are provided to APIs by reference.
/// mutex.lock_with_local(&NODE, |mut guard| *guard = 10);
/// assert_eq!(mutex.lock_with_local(&NODE, |guard| *guard), 10);
/// ```
/// [`raw::Mutex`]: Mutex
/// [`std::thread_local!`]: https://doc.rust-lang.org/std/macro.thread_local.html
/// [`try_lock_with_local`]: Mutex::try_lock_with_local
/// [`lock_with_local`]: Mutex::lock_with_local
/// [`try_lock_with_local_unchecked`]: Mutex::try_lock_with_local_unchecked
/// [`lock_with_local_unchecked`]: Mutex::lock_with_local_unchecked
#[macro_export]
macro_rules! thread_local_node {
    // Empty (base for recursion).
    () => {};
    // Process multiply definitions (recursive).
    ($vis:vis static $node:ident; $($rest:tt)*) => {
        $crate::__thread_local_node_inner!($vis $node);
        $crate::thread_local_node!($($rest)*);
    };
    // Process single declaration.
    ($vis:vis static $node:ident) => {
        $crate::__thread_local_node_inner!($vis $node);
    };
}

/// The local node error message as a string literal.
macro_rules! already_borrowed_error {
    () => {
        "thread local MCS lock node is already mutably borrowed"
    };
}

/// Panics the thread with a message pointing to the panic location.
#[inline(never)]
#[cold]
fn panic_already_borrowed(caller: &Location<'static>) -> ! {
    panic!("{}, conflict at: {}", already_borrowed_error!(), caller)
}

impl<T: ?Sized, R: Relax> Mutex<T, R> {
    /// Attempts to acquire this mutex and then runs a closure against its guard.
    ///
    /// If the lock could not be acquired at this time, then a [`None`] value is
    /// given back as the closure argument. If the lock has been acquired, then
    /// a [`Some`] value with the mutex guard is given instead. The lock will be
    /// unlocked when the guard is dropped.
    ///
    /// To acquire a MCS lock through this function, it's also required a
    /// queue node, which is a record that keeps a link for forming the queue,
    /// to be stored in the current locking thread local storage. See
    /// [`LocalMutexNode`] and [`thread_local_node!`].
    ///
    /// This function does not block.
    ///
    /// # Panics
    ///
    /// Will panic if the thread local node is already mutably borrowed.
    ///
    /// Panics if the key currently has its destructor running, and it **may**
    /// panic if the destructor has previously been run for this thread.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::sync::Arc;
    /// use std::thread;
    ///
    /// use mcslock::raw::spins::Mutex;
    ///
    /// mcslock::thread_local_node!(static NODE);
    ///
    /// let mutex = Arc::new(Mutex::new(0));
    /// let c_mutex = Arc::clone(&mutex);
    ///
    /// thread::spawn(move || {
    ///     c_mutex.try_lock_with_local(&NODE, |guard| {
    ///         if let Some(mut guard) = guard {
    ///             *guard = 10;
    ///         } else {
    ///             println!("try_lock failed");
    ///         }
    ///     });
    /// })
    /// .join().expect("thread::spawn failed");
    ///
    /// assert_eq!(mutex.lock_with_local(&NODE, |guard| *guard), 10);
    /// ```
    ///
    /// Compile fail: borrows of the guard or its data cannot escape the given
    /// closure:
    ///
    /// ```compile_fail,E0515
    /// use mcslock::raw::spins::Mutex;
    ///
    /// mcslock::thread_local_node!(static NODE);
    ///
    /// let mutex = Mutex::new(1);
    /// let data = mutex.try_lock_with_local(&NODE, |guard| &*guard.unwrap());
    /// ```
    ///
    /// Panic: thread local node cannot be borrowed more than once at the same
    /// time:
    ///
    #[doc = concat!("```should_panic,", already_borrowed_error!())]
    /// use mcslock::raw::spins::Mutex;
    ///
    /// mcslock::thread_local_node!(static NODE);
    ///
    /// let mutex = Mutex::new(0);
    ///
    /// mutex.lock_with_local(&NODE, |_guard| {
    ///     // `NODE` is already mutably borrowed in this thread by the
    ///     // enclosing `lock_with_local`, the borrow is live for the full
    ///     // duration of this closure scope.
    ///     let mutex = Mutex::new(());
    ///     mutex.try_lock_with_local(&NODE, |_guard| ());
    /// });
    /// ```
    /// [`LocalMutexNode`]: LocalMutexNode
    /// [`thread_local_node!`]: crate::thread_local_node
    #[inline]
    #[track_caller]
    pub fn try_lock_with_local<F, Ret>(&self, node: &'static LocalMutexNode, f: F) -> Ret
    where
        F: FnOnce(Option<MutexGuard<'_, T, R>>) -> Ret,
    {
        self.with_local_node(node, |mutex, node| f(mutex.try_lock(node)))
    }

    /// Attempts to acquire this mutex and then runs a closure against its guard.
    ///
    /// If the lock could not be acquired at this time, then a [`None`] value is
    /// given back as the closure argument. If the lock has been acquired, then
    /// a [`Some`] value with the mutex guard is given instead. The lock will be
    /// unlocked when the guard is dropped.
    ///
    /// To acquire a MCS lock through this function, it's also required a
    /// queue node, which is a record that keeps a link for forming the queue,
    /// to be stored in the current locking thread local storage. See
    /// [`LocalMutexNode`] and [`thread_local_node!`].
    ///
    /// This function does not block.
    ///
    /// # Safety
    ///
    /// Unlike [`try_lock_with_local`], this method is unsafe because it does
    /// not check if the current thread local node is already mutably borrowed.
    /// If the current thread local node is already borrowed, calling this
    /// function is undefined behavior.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::sync::Arc;
    /// use std::thread;
    ///
    /// use mcslock::raw::spins::Mutex;
    ///
    /// mcslock::thread_local_node!(static NODE);
    ///
    /// let mutex = Arc::new(Mutex::new(0));
    /// let c_mutex = Arc::clone(&mutex);
    ///
    /// thread::spawn(move || unsafe {
    ///     c_mutex.try_lock_with_local_unchecked(&NODE, |mut guard| *guard = 10);
    /// })
    /// .join().expect("thread::spawn failed");
    ///
    /// assert_eq!(mutex.lock_with_local(&NODE, |guard| *guard), 10);
    /// ```
    ///
    /// Compile fail: borrows of the guard or its data cannot escape the given
    /// closure:
    ///
    /// ```compile_fail,E0515
    /// use mcslock::raw::spins::Mutex;
    ///
    /// mcslock::thread_local_node!(static NODE);
    ///
    /// let mutex = Mutex::new(1);
    /// let data = unsafe {
    ///     mutex.try_lock_with_local_unchecked(&NODE, |g| &*g.unwrap())
    /// };
    /// ```
    ///
    /// Undefined behavior: thread local node cannot be borrowed more than once
    /// at the same time:
    ///
    /// ```no_run
    /// use mcslock::raw::spins::Mutex;
    ///
    /// mcslock::thread_local_node!(static NODE);
    ///
    /// let mutex = Mutex::new(0);
    ///
    /// mutex.lock_with_local(&NODE, |_guard| unsafe {
    ///     // UB: `NODE` is already mutably borrowed in this thread by the
    ///     // enclosing `lock_with_local`, the borrow is live for the full
    ///     // duration of this closure scope.
    ///     let mutex = Mutex::new(());
    ///     mutex.try_lock_with_local_unchecked(&NODE, |_guard| ());
    /// });
    /// ```
    /// [`try_lock_with_local`]: Mutex::try_lock_with_local
    pub unsafe fn try_lock_with_local_unchecked<F, Ret>(
        &self,
        node: &'static LocalMutexNode,
        f: F,
    ) -> Ret
    where
        F: FnOnce(Option<MutexGuard<'_, T, R>>) -> Ret,
    {
        self.with_local_node_unchecked(node, |mutex, node| f(mutex.try_lock(node)))
    }

    /// Acquires this mutex and then runs the closure against its guard.
    ///
    /// This function will block the local thread until it is available to acquire
    /// the mutex. Upon acquiring the mutex, the user provided closure will be
    /// executed against the mutex guard. Once the guard goes out of scope, it
    /// will unlock the mutex.
    ///
    /// To acquire a MCS lock through this function, it's also required a
    /// queue node, which is a record that keeps a link for forming the queue,
    /// to be stored in the current locking thread local storage. See
    /// [`LocalMutexNode`] and [`thread_local_node!`].
    ///
    /// This function will block if the lock is unavailable.
    ///
    /// # Panics
    ///
    /// Will panic if the thread local node is already mutably borrowed.
    ///
    /// Panics if the key currently has its destructor running, and it **may**
    /// panic if the destructor has previously been run for this thread.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::sync::Arc;
    /// use std::thread;
    ///
    /// use mcslock::raw::spins::Mutex;
    ///
    /// mcslock::thread_local_node!(static NODE);
    ///
    /// let mutex = Arc::new(Mutex::new(0));
    /// let c_mutex = Arc::clone(&mutex);
    ///
    /// thread::spawn(move || {
    ///     c_mutex.lock_with_local(&NODE, |mut guard| *guard = 10);
    /// })
    /// .join().expect("thread::spawn failed");
    ///
    /// assert_eq!(mutex.lock_with_local(&NODE, |guard| *guard), 10);
    /// ```
    ///
    /// Compile fail: borrows of the guard or its data cannot escape the given
    /// closure:
    ///
    /// ```compile_fail,E0515
    /// use mcslock::raw::spins::Mutex;
    ///
    /// mcslock::thread_local_node!(static NODE);
    ///
    /// let mutex = Mutex::new(1);
    /// let data = mutex.lock_with_local(&NODE, |guard| &*guard);
    /// ```
    ///
    /// Panic: thread local node cannot be borrowed more than once at the same
    /// time:
    ///
    #[doc = concat!("```should_panic,", already_borrowed_error!())]
    /// use mcslock::raw::spins::Mutex;
    ///
    /// mcslock::thread_local_node!(static NODE);
    ///
    /// let mutex = Mutex::new(0);
    ///
    /// mutex.lock_with_local(&NODE, |_guard| {
    ///     // `NODE` is already mutably borrowed in this thread by the
    ///     // enclosing `lock_with_local`, the borrow is live for the full
    ///     // duration of this closure scope.
    ///     let mutex = Mutex::new(());
    ///     mutex.lock_with_local(&NODE, |_guard| ());
    /// });
    /// ```
    /// [`LocalMutexNode`]: LocalMutexNode
    /// [`thread_local_node!`]: crate::thread_local_node
    #[inline]
    #[track_caller]
    pub fn lock_with_local<F, Ret>(&self, node: &'static LocalMutexNode, f: F) -> Ret
    where
        F: FnOnce(MutexGuard<'_, T, R>) -> Ret,
    {
        self.with_local_node(node, |mutex, node| f(mutex.lock(node)))
    }

    /// Acquires this mutex and then runs the closure against its guard.
    ///
    /// This function will block the local thread until it is available to acquire
    /// the mutex. Upon acquiring the mutex, the user provided closure will be
    /// executed against the mutex guard. Once the guard goes out of scope, it
    /// will unlock the mutex.
    ///
    /// To acquire a MCS lock through this function, it's also required a
    /// queue node, which is a record that keeps a link for forming the queue,
    /// to be stored in the current locking thread local storage. See
    /// [`LocalMutexNode`] and [`thread_local_node!`].
    ///
    /// This function will block if the lock is unavailable.
    ///
    /// # Safety
    ///
    /// Unlike [`lock_with_local`], this method is unsafe because it does not
    /// check if the current thread local node is already mutably borrowed. If
    /// the current thread local node is already borrowed, calling this
    /// function is undefined behavior.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::sync::Arc;
    /// use std::thread;
    ///
    /// use mcslock::raw::spins::Mutex;
    ///
    /// mcslock::thread_local_node!(static NODE);
    ///
    /// let mutex = Arc::new(Mutex::new(0));
    /// let c_mutex = Arc::clone(&mutex);
    ///
    /// thread::spawn(move || unsafe {
    ///     c_mutex.lock_with_local_unchecked(&NODE, |mut guard| *guard = 10);
    /// })
    /// .join().expect("thread::spawn failed");
    ///
    /// assert_eq!(mutex.lock_with_local(&NODE, |guard| *guard), 10);
    /// ```
    ///
    /// Compile fail: borrows of the guard or its data cannot escape the given
    /// closure:
    ///
    /// ```compile_fail,E0515
    /// use mcslock::raw::spins::Mutex;
    ///
    /// mcslock::thread_local_node!(static NODE);
    ///
    /// let mutex = Mutex::new(1);
    /// let data = unsafe {
    ///     mutex.lock_with_local_unchecked(&NODE, |g| &*g)
    /// };
    /// ```
    ///
    /// Undefined behavior: thread local node cannot be borrowed more than once
    /// at the same time:
    ///
    /// ```no_run
    /// use mcslock::raw::spins::Mutex;
    ///
    /// mcslock::thread_local_node!(static NODE);
    ///
    /// let mutex = Mutex::new(0);
    ///
    /// mutex.lock_with_local(&NODE, |_guard| unsafe {
    ///     // UB: `NODE` is already mutably borrowed in this thread by the
    ///     // enclosing `lock_with_local`, the borrow is live for the full
    ///     // duration of this closure scope.
    ///     let mutex = Mutex::new(());
    ///     mutex.lock_with_local_unchecked(&NODE, |_guard| ());
    /// });
    /// ```
    /// [`lock_with_local`]: Mutex::lock_with_local
    #[inline]
    pub unsafe fn lock_with_local_unchecked<F, Ret>(
        &self,
        node: &'static LocalMutexNode,
        f: F,
    ) -> Ret
    where
        F: FnOnce(MutexGuard<'_, T, R>) -> Ret,
    {
        self.with_local_node_unchecked(node, |mutex, node| f(mutex.lock(node)))
    }

    /// Guard cannot outlive the closure or else it would allow the guard drop
    /// call to access the thread local node even though its exclusive borrow
    /// has already expired at the end of the closure.
    ///
    /// ```compile_fail
    /// use mcslock::raw::spins::Mutex;
    /// mcslock::thread_local_node!(static NODE);
    ///
    /// let mutex = Mutex::new(1);
    /// let guard = mutex.lock_with_local(&NODE, |guard| guard);
    /// ```
    ///
    /// ```compile_fail,E0521
    /// use std::thread;
    /// use mcslock::raw::spins::Mutex;
    /// mcslock::thread_local_node!(static NODE);
    ///
    /// let mutex = Mutex::new(1);
    /// mutex.lock_with_local(&NODE, |guard| {
    ///     thread::spawn(move || {
    ///         let guard = guard;
    ///     });
    /// });
    /// ```
    const fn __guard_cant_escape_closure() {}
}

impl<T: ?Sized, R> Mutex<T, R> {
    /// Runs `f` over a raw mutex and a thread local node as arguments.
    ///
    /// # Panics
    ///
    /// Will panic if the thread local node is already mutably borrowed.
    ///
    /// Panics if the key currently has its destructor running, and it **may**
    /// panic if the destructor has previously been run for this thread.
    #[track_caller]
    fn with_local_node<F, Ret>(&self, node: &'static LocalMutexNode, f: F) -> Ret
    where
        F: FnOnce(&Self, &mut MutexNode) -> Ret,
    {
        let caller = Location::caller();
        let panic = |_| panic_already_borrowed(caller);
        let f = |mut node: RefMut<_>| f(self, &mut node);
        node.key.with(|node| node.try_borrow_mut().map_or_else(panic, f))
    }

    /// Runs 'f' over the a raw mutex and thread local node as arguments without
    /// checking if the node is currently mutably borrowed.
    ///
    /// # Safety
    ///
    /// Mutably borrowing a [`RefCell`] while references are still live is
    /// undefined behaviour. Threfore, caller must guarantee that the thread
    /// local node is not already in use for the current thread. A thread local
    /// node is release to the current thread once the associated `with_local`'s
    /// f closure runs out of scope.
    unsafe fn with_local_node_unchecked<F, Ret>(&self, node: &'static LocalMutexNode, f: F) -> Ret
    where
        F: FnOnce(&Self, &mut MutexNode) -> Ret,
    {
        // SAFETY: Caller guaranteed that no other references are live.
        node.key.with(|node| f(self, unsafe { &mut *node.as_ptr() }))
    }
}

// A thread local node definition used for testing.
#[cfg(test)]
thread_local_node!(static TEST_NODE);

/// A Mutex wrapper type that calls the `lock_with_local` and
/// `try_lock_with_local` when implementing testing traits.
#[cfg(test)]
struct MutexPanic<T: ?Sized, R>(Mutex<T, R>);

#[cfg(test)]
impl<T: ?Sized, R> crate::test::LockNew for MutexPanic<T, R> {
    type Target = T;

    fn new(value: Self::Target) -> Self
    where
        Self::Target: Sized,
    {
        Self(Mutex::new(value))
    }
}

#[cfg(all(not(loom), test))]
impl<T: ?Sized, R> crate::test::LockData for MutexPanic<T, R> {
    fn into_inner(self) -> Self::Target
    where
        Self::Target: Sized,
    {
        self.0.into_inner()
    }

    fn get_mut(&mut self) -> &mut Self::Target {
        self.0.get_mut()
    }
}

#[cfg(test)]
impl<T: ?Sized, R: Relax> crate::test::LockWith for MutexPanic<T, R> {
    type Guard<'a> = MutexGuard<'a, Self::Target, R>
    where
        Self: 'a,
        Self::Target: 'a;

    fn try_lock_with<F, Ret>(&self, f: F) -> Ret
    where
        F: FnOnce(Option<MutexGuard<'_, T, R>>) -> Ret,
    {
        self.0.try_lock_with_local(&TEST_NODE, f)
    }

    fn lock_with<F, Ret>(&self, f: F) -> Ret
    where
        F: FnOnce(MutexGuard<'_, T, R>) -> Ret,
    {
        self.0.lock_with_local(&TEST_NODE, f)
    }

    fn is_locked(&self) -> bool {
        self.0.is_locked()
    }
}

/// A Mutex wrapper type that calls the `lock_with_local_unchecked` and
/// `try_lock_with_local_unchecked` when implementing testing traits.
#[cfg(test)]
struct MutexUnchecked<T: ?Sized, R>(Mutex<T, R>);

#[cfg(test)]
impl<T: ?Sized, R> crate::test::LockNew for MutexUnchecked<T, R> {
    type Target = T;

    fn new(value: Self::Target) -> Self
    where
        Self::Target: Sized,
    {
        Self(Mutex::new(value))
    }
}

#[cfg(all(not(loom), test))]
impl<T: ?Sized, R> crate::test::LockData for MutexUnchecked<T, R> {
    fn into_inner(self) -> Self::Target
    where
        Self::Target: Sized,
    {
        self.0.into_inner()
    }

    fn get_mut(&mut self) -> &mut Self::Target {
        self.0.get_mut()
    }
}

#[cfg(test)]
impl<T: ?Sized, R: Relax> crate::test::LockWith for MutexUnchecked<T, R> {
    type Guard<'a> = MutexGuard<'a, Self::Target, R>
    where
        Self: 'a,
        Self::Target: 'a;

    fn try_lock_with<F, Ret>(&self, f: F) -> Ret
    where
        F: FnOnce(Option<MutexGuard<'_, T, R>>) -> Ret,
    {
        // SAFETY: caller must guarantee that this thread local NODE is not
        // already mutably borrowed for some other lock acquisition.
        unsafe { self.0.try_lock_with_local_unchecked(&TEST_NODE, f) }
    }

    fn lock_with<F, Ret>(&self, f: F) -> Ret
    where
        F: FnOnce(MutexGuard<'_, T, R>) -> Ret,
    {
        // SAFETY: caller must guarantee that this thread local NODE is not
        // already mutably borrowed for some other lock acquisition.
        unsafe { self.0.lock_with_local_unchecked(&TEST_NODE, f) }
    }

    fn is_locked(&self) -> bool {
        self.0.is_locked()
    }
}

#[cfg(all(not(loom), test))]
mod test {
    use crate::raw::MutexNode;
    use crate::relax::Yield;
    use crate::test::tests;

    type MutexPanic<T> = super::MutexPanic<T, Yield>;
    type MutexUnchecked<T> = super::MutexUnchecked<T, Yield>;

    #[test]
    fn ref_cell_node_drop_does_not_matter() {
        use core::{cell::RefCell, mem};
        assert!(!mem::needs_drop::<RefCell<MutexNode>>());
    }

    #[test]
    fn lots_and_lots() {
        tests::lots_and_lots::<MutexPanic<_>>();
    }

    #[test]
    fn lots_and_lots_unchecked() {
        tests::lots_and_lots::<MutexUnchecked<_>>();
    }

    #[test]
    fn smoke() {
        tests::smoke::<MutexPanic<_>>();
    }

    #[test]
    fn smoke_unchecked() {
        tests::smoke::<MutexUnchecked<_>>();
    }

    #[test]
    fn test_try_lock() {
        tests::test_try_lock::<MutexPanic<_>>();
    }

    #[test]
    fn test_try_lock_unchecked() {
        tests::test_try_lock::<MutexUnchecked<_>>();
    }

    #[test]
    #[should_panic = already_borrowed_error!()]
    fn test_lock_arc_nested() {
        tests::test_lock_arc_nested::<MutexPanic<_>, MutexPanic<_>>();
    }

    #[test]
    #[should_panic = already_borrowed_error!()]
    fn test_acquire_more_than_one_lock() {
        tests::test_acquire_more_than_one_lock::<MutexPanic<_>>();
    }

    #[test]
    fn test_lock_arc_access_in_unwind() {
        tests::test_lock_arc_access_in_unwind::<MutexPanic<_>>();
    }

    #[test]
    fn test_lock_arc_access_in_unwind_unchecked() {
        tests::test_lock_arc_access_in_unwind::<MutexUnchecked<_>>();
    }

    #[test]
    fn test_lock_unsized() {
        tests::test_lock_unsized::<MutexPanic<_>>();
    }

    #[test]
    fn test_lock_unsized_unchecked() {
        tests::test_lock_unsized::<MutexUnchecked<_>>();
    }
}

#[cfg(all(loom, test))]
mod model {
    use crate::loom::models;
    use crate::relax::Yield;

    type MutexPanic<T> = super::MutexPanic<T, Yield>;
    type MutexUnchecked<T> = super::MutexUnchecked<T, Yield>;

    #[test]
    fn try_lock_join() {
        models::try_lock_join::<MutexPanic<_>>();
    }

    #[test]
    fn try_lock_join_unchecked() {
        models::try_lock_join::<MutexUnchecked<_>>();
    }

    #[test]
    fn lock_join() {
        models::lock_join::<MutexPanic<_>>();
    }

    #[test]
    fn lock_join_unchecked() {
        models::lock_join::<MutexUnchecked<_>>();
    }

    #[test]
    fn mixed_lock_join() {
        models::mixed_lock_join::<MutexPanic<_>>();
    }

    #[test]
    fn mixed_lock_join_unchecked() {
        models::mixed_lock_join::<MutexUnchecked<_>>();
    }
}
