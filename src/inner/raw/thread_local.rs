use core::cell::{RefCell, RefMut};
use core::ops::DerefMut;
use core::panic::Location;

use super::{Mutex, MutexNode};
use crate::cfg::thread::LocalKey;
use crate::lock::{Lock, Wait};

type Key<N> = &'static LocalMutexNode<N>;

/// A handle to a [`MutexNode`] stored at the thread local storage.
#[derive(Debug)]
#[repr(transparent)]
pub struct LocalMutexNode<N: 'static> {
    #[cfg(not(all(loom, test)))]
    key: LocalKey<RefCell<N>>,

    // We can't take ownership of Loom's `thread_local!` value since it is a
    // `static`, non-copy value, so we just point to it.
    #[cfg(all(loom, test))]
    key: &'static LocalKey<RefCell<N>>,
}

#[cfg(not(tarpaulin_include))]
impl<N> LocalMutexNode<N> {
    /// Creates a new `LocalMutexNode` key from the provided thread local node
    /// key.
    #[cfg(not(all(loom, test)))]
    pub const fn new(key: LocalKey<RefCell<N>>) -> Self {
        Self { key }
    }

    /// Creates a new Loom based `LocalMutexNode` key from the provided thread
    /// local node key.
    #[cfg(all(loom, test))]
    pub const fn new(key: &'static LocalKey<RefCell<N>>) -> Self {
        Self { key }
    }
}

/// Panics the thread with a message pointing to the panic location.
#[inline(never)]
#[cold]
fn panic_already_borrowed(caller: &Location<'static>) -> ! {
    panic!("{}, conflict at: {}", already_borrowed_error!(), caller)
}

impl<T: ?Sized, L: Lock, W: Wait> Mutex<T, L, W> {
    /// Attempts to acquire this mutex with a thread local node and then runs
    /// a closure against the protected data.
    ///
    /// # Panics
    ///
    /// See: `with_local_node_then`.
    #[track_caller]
    pub fn try_lock_with_local_then<N, F, Ret>(&self, node: Key<N>, f: F) -> Ret
    where
        N: DerefMut<Target = MutexNode<L>>,
        F: FnOnce(Option<&mut T>) -> Ret,
    {
        self.with_local_node_then(node, |m, n| m.try_lock_with_then(n, f))
    }

    /// Attempts to acquire this mutex with a thread local node and then runs
    /// a closure against the protected data.
    ///
    /// # Safety
    ///
    /// See: `with_local_node_then_unchecked`.
    ///
    /// # Panics
    ///
    /// See: `with_local_node_then_unchecked`.
    pub unsafe fn try_lock_with_local_then_unchecked<F, Ret, N>(&self, node: Key<N>, f: F) -> Ret
    where
        N: DerefMut<Target = MutexNode<L>>,
        F: FnOnce(Option<&mut T>) -> Ret,
    {
        self.with_local_node_then_unchecked(node, |m, n| m.try_lock_with_then(n, f))
    }

    /// Attempts to acquire this mutex with a thread local node and then runs
    /// a closure against the protected data.
    ///
    /// # Panics
    ///
    /// See: `with_local_node_then`.
    #[track_caller]
    pub fn lock_with_local_then<N, F, Ret>(&self, node: Key<N>, f: F) -> Ret
    where
        N: DerefMut<Target = MutexNode<L>>,
        F: FnOnce(&mut T) -> Ret,
    {
        self.with_local_node_then(node, |m, n| m.lock_with_then(n, f))
    }

    /// Attempts to acquire this mutex with a thread local node and then runs
    /// a closure against the protected data.
    ///
    /// # Safety
    ///
    /// See: `with_local_node_then_unchecked`.
    ///
    /// # Panics
    ///
    /// See: `with_local_node_then_unchecked`.
    pub unsafe fn lock_with_local_then_unchecked<N, F, Ret>(&self, node: Key<N>, f: F) -> Ret
    where
        N: DerefMut<Target = MutexNode<L>>,
        F: FnOnce(&mut T) -> Ret,
    {
        self.with_local_node_then_unchecked(node, |m, n| m.lock_with_then(n, f))
    }

    /// Runs `f` over a raw mutex and a thread local node as arguments.
    ///
    /// # Panics
    ///
    /// Will panic if the thread local node is already mutably borrowed.
    ///
    /// Panics if the key currently has its destructor running, and it **may**
    /// panic if the destructor has previously been run for this thread.
    #[track_caller]
    fn with_local_node_then<N, F, Ret>(&self, node: Key<N>, f: F) -> Ret
    where
        N: DerefMut<Target = MutexNode<L>>,
        F: FnOnce(&Self, &mut MutexNode<L>) -> Ret,
    {
        let caller = Location::caller();
        let panic = |_| panic_already_borrowed(caller);
        let f = |mut node: RefMut<N>| f(self, &mut node);
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
    ///
    /// # Panics
    ///
    /// Panics if the key currently has its destructor running, and it **may**
    /// panic if the destructor has previously been run for this thread.
    unsafe fn with_local_node_then_unchecked<N, F, Ret>(&self, node: Key<N>, f: F) -> Ret
    where
        N: DerefMut<Target = MutexNode<L>>,
        F: FnOnce(&Self, &mut MutexNode<L>) -> Ret,
    {
        // SAFETY: Caller guaranteed that no other references are live.
        node.key.with(|node| f(self, unsafe { &mut *node.as_ptr() }))
    }
}
