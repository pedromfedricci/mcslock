use core::cell::{RefCell, RefMut};
use core::panic::Location;

use crate::cfg::thread::LocalKey;
use crate::raw::{Mutex, MutexGuard, MutexNode};
use crate::relax::Relax;

/// A local node is a [`MutexNode`] stored at the thread local storage that can
/// be claimed for temporary, exclusive access during runtime.
pub type LocalNode = LocalKey<RefCell<MutexNode>>;

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

/// Declare a new thread local storage key of type [`LocalKey<RefCell<MutexNode>>`].
///
/// This thread local node definition avoids lazy initialization and does not
/// need to be dropped, which enables a more efficient underlying implementation.
/// See [std::thread_local].
///
/// [std::thread_local]: https://doc.rust-lang.org/std/macro.thread_local.html
#[cfg(not(all(loom, test)))]
#[macro_export]
macro_rules! thread_local_node {
    ($node:ident) => {
        ::std::thread_local! {
            static $node: ::core::cell::RefCell<$crate::raw::MutexNode> = const {
                ::core::cell::RefCell::new($crate::raw::MutexNode::new())
            }
        }
    };
}

/// Declare a new Loom thread local storage key of type [`LocalKey<RefCell<MutexNode>>`].
///
// This node definition uses Loom primitives and it can't be evaluated as a
// constant since Loom does not support that feature.
#[cfg(all(loom, test))]
#[cfg(not(tarpaulin_include))]
#[macro_export]
macro_rules! thread_local_node {
    ($node:ident) => {
        ::loom::thread_local! {
            static $node: ::core::cell::RefCell<$crate::raw::MutexNode> = {
                ::core::cell::RefCell::new($crate::raw::MutexNode::new())
            }
        }
    };
}

impl<T: ?Sized, R: Relax> Mutex<T, R> {
    /// Attempts to acquire this mutex and then runs a closure against its guard.
    ///
    /// If the lock could not be acquired at this time, then a [`None`] value is
    /// given back as the closure argument. If the lock has been acquired, then
    /// a [`Some`] value with the mutex guard is given instead. The lock will be
    /// unlocked when the guard is dropped.
    ///
    /// This function does not block and requires that the node must be stored
    /// at thread local storage. See: [std::thread_local].
    ///
    /// # Panics
    ///
    /// Will panic if the thread local node is already mutably borrowed.
    ///
    /// Panics if the key currently has its destructor running, and it **may**
    /// panic if the destructor has previously been run for this thread.
    ///
    /// [thread_local]: https://doc.rust-lang.org/std/macro.thread_local.html
    ///
    /// # Examples
    ///
    /// ```
    /// use std::sync::Arc;
    /// use std::thread;
    ///
    /// use mcslock::raw::Mutex;
    /// use mcslock::relax::Spin;
    ///
    /// type SpinMutex<T> = Mutex<T, Spin>;
    ///
    /// mcslock::thread_local_node!(NODE);
    ///
    /// let mutex = Arc::new(SpinMutex::new(0));
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
    /// mcslock::thread_local_node!(NODE);
    ///
    /// let mutex = Mutex::new(1);
    /// let data = mutex.try_lock_with_local(&NODE, |guard| &*guard.unwrap());
    /// ```
    ///
    /// Panic: thread local node cannot be borrowed more than once at the same
    /// time:
    ///
    #[doc = concat!("```should_panic,", already_borrowed_error!())]
    /// use mcslock::raw::Mutex;
    /// use mcslock::relax::Spin;
    ///
    /// type SpinMutex<T> = Mutex<T, Spin>;
    ///
    /// mcslock::thread_local_node!(NODE);
    ///
    /// let mutex = SpinMutex::new(0);
    ///
    /// mutex.lock_with_local(&NODE, |_guard| {
    ///     // `NODE` is already mutably borrowed in this thread by the
    ///     // inclosing `lock_with_local`, the borrow is live for the full
    ///     // duration of this closure scope.
    ///     let mutex = SpinMutex::new(());
    ///     mutex.try_lock_with_local(&NODE, |_guard| ());
    /// });
    /// ```
    #[inline]
    #[track_caller]
    pub fn try_lock_with_local<F, Ret>(&self, node: &'static LocalNode, f: F) -> Ret
    where
        F: FnOnce(Option<MutexGuard<'_, T, R>>) -> Ret,
    {
        self.with_local_node(node, |mutex, node| f(mutex.try_lock(node)))
    }

    /// Acquires this mutex and then runs the closure against its guard.
    ///
    /// This function will block the local thread until it is available to acquire
    /// the mutex. Upon acquiring the mutex, the user provided closure will be
    /// executed against the mutex guard. Once the guard goes out of scope, it
    /// will unlock the mutex.
    ///
    /// This function will block if the lock is unavailable and requires that the
    /// node must be stored at thread local storage. See: [std::thread_local].
    ///
    /// # Panics
    ///
    /// Will panic if the thread local node is already mutably borrowed.
    ///
    /// Panics if the key currently has its destructor running, and it **may**
    /// panic if the destructor has previously been run for this thread.
    ///
    /// [thread_local]: https://doc.rust-lang.org/std/macro.thread_local.html
    ///
    /// # Examples
    ///
    /// ```
    /// use std::sync::Arc;
    /// use std::thread;
    ///
    /// use mcslock::raw::Mutex;
    /// use mcslock::relax::Spin;
    ///
    /// type SpinMutex<T> = Mutex<T, Spin>;
    ///
    /// mcslock::thread_local_node!(NODE);
    ///
    /// let mutex = Arc::new(SpinMutex::new(0));
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
    /// mcslock::thread_local_node!(NODE);
    ///
    /// let mutex = Mutex::new(1);
    /// let data = mutex.lock_with_local(&NODE, |guard| &*guard);
    /// ```
    ///
    /// Panic: thread local node cannot be borrowed more than once at the same
    /// time:
    ///
    #[doc = concat!("```should_panic,", already_borrowed_error!())]
    /// use mcslock::raw::Mutex;
    /// use mcslock::relax::Spin;
    ///
    /// type SpinMutex<T> = Mutex<T, Spin>;
    ///
    /// let mutex = SpinMutex::new(0);
    ///
    /// mcslock::thread_local_node!(NODE);
    ///
    /// mutex.lock_with_local(&NODE, |_guard| {
    ///     // `NODE` is already mutably borrowed in this thread by the
    ///     // inclosing `lock_with_local`, the borrow is live for the full
    ///     // duration of this closure scope.
    ///     let mutex = SpinMutex::new(());
    ///     mutex.lock_with_local(&NODE, |_guard| ());
    /// });
    /// ```
    #[inline]
    #[track_caller]
    pub fn lock_with_local<F, Ret>(&self, node: &'static LocalNode, f: F) -> Ret
    where
        F: FnOnce(MutexGuard<'_, T, R>) -> Ret,
    {
        self.with_local_node(node, |mutex, node| f(mutex.lock(node)))
    }

    /// Guard cannot outlive the closure or else it would allow the guard drop
    /// call to access the thread local node even though its exclusive borrow
    /// has already expired at the end of the closure.
    ///
    /// ```compile_fail
    /// use mcslock::raw::spins::Mutex;
    /// mcslock::thread_local_node!(NODE);
    ///
    /// let mutex = Mutex::new(1);
    /// let guard = mutex.lock_with_local(&NODE, |guard| guard);
    /// ```
    ///
    /// ```compile_fail,E0521
    /// use std::thread;
    /// use mcslock::raw::spins::Mutex;
    /// mcslock::thread_local_node!(NODE);
    ///
    /// let mutex = Mutex::new(1);
    /// mutex.lock_with_local(&NODE, |guard| {
    ///     thread::spawn(move || {
    ///         let guard = guard;
    ///     });
    /// });
    /// ```
    fn __guard_cant_escape_closure() {}
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
    fn with_local_node<F, Ret>(&self, node: &'static LocalNode, f: F) -> Ret
    where
        F: FnOnce(&Self, &mut MutexNode) -> Ret,
    {
        let caller = Location::caller();
        let panic = |_| panic_already_borrowed(caller);
        let f = |mut node: RefMut<_>| f(self, &mut node);
        node.with(|node| node.try_borrow_mut().map_or_else(panic, f))
    }

    /// Runs 'f' over the a raw mutex and thread local node as arguments without
    /// checking if the node is currently mutably borrowed.
    ///
    /// # Safety
    ///
    /// Mutably borrowing a [`RefCell`] while references are still live is
    /// undefined behaviour. This means that two or more guards can not be in
    /// scope within a single thread at the same time.
    #[allow(unused)]
    unsafe fn with_borrow_mut_unchecked<F, Ret>(&self, node: &'static LocalNode, f: F) -> Ret
    where
        F: FnOnce(&Self, &mut MutexNode) -> Ret,
    {
        // SAFETY: Caller guaranteed that no other references are live.
        node.with(|node| f(self, unsafe { &mut *node.as_ptr() }))
    }
}

#[cfg(test)]
mod test {
    use crate::raw::MutexNode;

    #[test]
    fn ref_cell_node_drop_does_not_matter() {
        use core::cell::RefCell;
        assert!(!core::mem::needs_drop::<RefCell<MutexNode>>());
    }
}
