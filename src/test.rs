use core::ops::{Deref, DerefMut};

use crate::cfg::sync::Arc;

/// A trait for convertion from `&Self` to a type that implements the [`Deref`]
/// trait.
pub trait AsDeref {
    /// The type of the value that `Self::Deref` dereferences to.
    type Target: ?Sized;

    /// The type that implements [`Deref`] trait.
    type Deref<'a>: Deref<Target = Self::Target>
    where
        Self: 'a,
        Self::Target: 'a;

    /// Returns a instance of the type that implements the [`Deref`] trait.
    fn as_deref(&self) -> Self::Deref<'_>;
}

/// A trait for convertion from `&mut Self` to a type that implements the
/// [`DerefMut`] trait.
pub trait AsDerefMut: AsDeref {
    /// The type that implements [`DerefMut`] trait.
    type DerefMut<'a>: DerefMut<Target = Self::Target>
    where
        Self: 'a,
        Self::Target: 'a;

    /// Returns a instance of the type that implements the [`DerefMut`] trait.
    fn as_deref_mut(&mut self) -> Self::DerefMut<'_>;
}

/// A trait for lock types that can hold user defined values.
pub trait LockNew {
    /// The type of the value this lock holds.
    type Target: ?Sized;

    /// Creates a new mutex in an unlocked state ready for use.
    fn new(value: Self::Target) -> Self
    where
        Self::Target: Sized;
}

/// A trait for locks that mutably borrow from nodes and run closures against
/// the shared protected data.
pub trait LockWithThen: LockNew {
    /// The queue node type to borrow from and form the implicit queue.
    type Node: Default;

    /// A `guard` has access to a type that can can give shared and exclusive
    /// references to the protected data.
    type Guard<'a>: AsDerefMut<Target = Self::Target>
    where
        Self: 'a,
        Self::Target: 'a;

    /// Acquires a mutex and then runs the closure against the protected data.
    ///
    /// Requires mutably borrowing a `Self::Node` for the closure scope.
    fn lock_with_then<F, Ret>(&self, node: &mut Self::Node, f: F) -> Ret
    where
        F: FnOnce(Self::Guard<'_>) -> Ret;
}

/// A trait for locks that run closures against the shared protected data.
pub trait LockThen: LockWithThen {
    /// Acquires a mutex and then runs the closure against the protected data.
    ///
    /// A `Self::Node` is transparently allocated in the stack.
    fn lock_then<F, Ret>(&self, f: F) -> Ret
    where
        F: FnOnce(Self::Guard<'_>) -> Ret,
    {
        self.lock_with_then(&mut Self::Node::default(), f)
    }
}

/// A trait for locks that mutably borrow from nodes, test if the lock is busy
/// and run closures against the protected data in case of success.
pub trait TryLockWithThen: LockWithThen {
    /// Attempts to acquire this lock and then runs the closure against the
    /// protected data if successful.
    ///
    /// Requires mutably borrowing a `Self::Node` for the closure scope.
    fn try_lock_with_then<F, Ret>(&self, node: &mut Self::Node, f: F) -> Ret
    where
        F: FnOnce(Option<Self::Guard<'_>>) -> Ret;

    /// Returns `true` if the lock is currently held.
    #[cfg_attr(all(loom, test), allow(dead_code))]
    fn is_locked(&self) -> bool;
}

/// A trait for locks that test if the lock is busy and run closures against the
/// protected data in case of success.
pub trait TryLockThen: TryLockWithThen + LockThen {
    /// Attempts to acquire this lock and then runs the closure against the
    /// protected data if successful.
    ///
    /// A `Self::Node` is transparently allocated in the stack.
    #[cfg_attr(all(loom, test), allow(dead_code))]
    fn try_lock_then<F, Ret>(&self, f: F) -> Ret
    where
        F: FnOnce(Option<Self::Guard<'_>>) -> Ret,
    {
        self.try_lock_with_then(&mut Self::Node::default(), f)
    }
}

/// A trait for lock types that can return either the underlying value (by
// consuming the mutex) or a exclusive reference to it.
#[cfg(not(loom))]
pub trait LockData: LockNew {
    /// Consumes this mutex, returning the underlying data.
    fn into_inner(self) -> Self::Target
    where
        Self::Target: Sized;

    /// Returns a mutable reference to the underlying data.
    fn get_mut(&mut self) -> &mut Self::Target;
}

// Trivial implementation of `AsDeref` for `T` where `T: Deref`.
impl<T: Deref> AsDeref for T {
    type Target = <Self as Deref>::Target;

    type Deref<'a>
        = &'a <Self as Deref>::Target
    where
        Self: 'a,
        Self::Target: 'a;

    fn as_deref(&self) -> Self::Deref<'_> {
        self
    }
}

// Trivial implementation of `AsDerefMut` for `T` where `T: DerefMut`.
impl<T: DerefMut> AsDerefMut for T {
    type DerefMut<'a>
        = &'a mut <Self as Deref>::Target
    where
        Self: 'a,
        Self::Target: 'a;

    fn as_deref_mut(&mut self) -> Self::DerefMut<'_> {
        self
    }
}

/// An arbitrary unsigned integer type.
pub type Int = u32;

/// Get a copy of the mutex protected data.
pub fn lock_get<L>(mutex: &Arc<L>) -> L::Target
where
    L: LockThen<Target: Sized + Copy>,
{
    mutex.lock_then(|data| *data.as_deref())
}

/// Increments a shared integer.
pub fn lock_inc<L>(mutex: &Arc<L>)
where
    L: LockThen<Target = Int>,
{
    mutex.lock_then(inc_inner::<L>);
}

/// Increments a shared integer, mutably borrows a queue node.
#[cfg(not(all(loom, test)))]
pub fn lock_inc_with<L>(mutex: &Arc<L>, node: &mut L::Node)
where
    L: LockWithThen<Target = Int>,
{
    mutex.lock_with_then(node, inc_inner::<L>);
}

/// Tries to increment a shared integer, mutably borrows a queue node.
#[cfg(not(all(loom, test)))]
pub fn try_lock_inc_with<L>(mutex: &Arc<L>, node: &mut L::Node)
where
    L: TryLockWithThen<Target = Int>,
{
    mutex.try_lock_with_then(node, try_inc_inner::<L>);
}

/// Tries to increment a shared integer.
#[cfg(all(loom, test))]
pub fn try_lock_inc<L>(mutex: &Arc<L>)
where
    L: TryLockThen<Target = Int>,
{
    mutex.try_lock_then(try_inc_inner::<L>);
}

/// Increments a shared integer through a guard instance.
fn inc_inner<L>(mut guard: L::Guard<'_>)
where
    L: LockWithThen<Target = Int>,
{
    *guard.as_deref_mut() += 1;
}

/// Tries to increment a shared integer through a guard instance.
fn try_inc_inner<L>(guard: Option<L::Guard<'_>>)
where
    L: TryLockWithThen<Target = Int>,
{
    guard.map(inc_inner::<L>);
}

#[cfg(all(not(loom), test))]
pub mod tests {
    // Modified test suite from the Rust's Mutex implementation with minor changes
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

    use core::ops::RangeInclusive;
    use std::fmt::Debug;
    use std::format;
    use std::string::ToString;
    use std::sync::atomic::{AtomicUsize, Ordering};
    use std::sync::mpsc::channel;
    use std::sync::Arc;
    use std::thread;

    #[cfg(feature = "barging")]
    use std::fmt::Display;
    use std::vec::Vec;

    use super::{lock_get, lock_inc, lock_inc_with, try_lock_inc_with, Int};
    use super::{AsDeref, AsDerefMut};
    use super::{LockData, LockThen, LockWithThen, TryLockThen, TryLockWithThen};

    #[derive(Eq, PartialEq, Debug)]
    pub struct NonCopy(u32);

    pub struct Foo(Arc<AtomicUsize>);

    impl Drop for Foo {
        fn drop(&mut self) {
            self.0.fetch_add(1, Ordering::SeqCst);
        }
    }

    const ITERS: Int = 1000;
    const THREADS: Int = 4;
    const EXPECTED_VALUE: Int = ITERS * THREADS;
    const EXPECTED_RANGE: RangeInclusive<Int> = 1..=EXPECTED_VALUE;

    fn lock_inc_for<L, const END: Int>(mutex: &Arc<L>)
    where
        L: LockWithThen<Target = Int>,
    {
        let mut node = L::Node::default();
        for _ in 0..END {
            lock_inc_with::<L>(mutex, &mut node);
        }
    }

    fn try_lock_inc_for<L, const END: Int>(mutex: &Arc<L>)
    where
        L: TryLockWithThen<Target = Int>,
    {
        let mut node = L::Node::default();
        for _ in 0..END {
            try_lock_inc_with::<L>(mutex, &mut node);
        }
    }

    fn mixed_lock_inc_for<L, const END: Int>(mutex: &Arc<L>)
    where
        L: TryLockWithThen<Target = Int>,
    {
        let mut node = L::Node::default();
        for r in 0..END {
            let f = if r % 2 == 0 { lock_inc_with } else { try_lock_inc_with };
            f(mutex, &mut node);
        }
    }

    fn lots_and_lots<L, const THREADS: Int>(f: fn(&Arc<L>)) -> Int
    where
        L: LockThen<Target = Int> + Send + Sync + 'static,
    {
        let mutex = Arc::new(L::new(0));
        let (tx, rx) = channel();
        for _ in 0..THREADS {
            let c_mutex = Arc::clone(&mutex);
            let c_tx = tx.clone();
            thread::spawn(move || {
                f(&c_mutex);
                c_tx.send(()).unwrap();
            });
        }
        drop(tx);
        for _ in 0..THREADS {
            rx.recv().unwrap();
        }
        lock_get(&mutex)
    }

    pub fn node_waiter_drop_does_not_matter<W>() {
        use crate::inner::raw::{MutexNode, MutexNodeInit};
        assert!(!core::mem::needs_drop::<W>());
        assert!(!core::mem::needs_drop::<MutexNode<W>>());
        assert!(!core::mem::needs_drop::<MutexNodeInit<W>>());
    }

    pub fn lots_and_lots_lock<L>()
    where
        L: LockThen<Target = Int> + Send + Sync + 'static,
    {
        let value = lots_and_lots::<L, THREADS>(lock_inc_for::<L, ITERS>);
        assert_eq!(value, EXPECTED_VALUE);
    }

    pub fn lots_and_lots_try_lock<L>()
    where
        L: TryLockThen<Target = Int> + Send + Sync + 'static,
    {
        let value = lots_and_lots::<L, THREADS>(try_lock_inc_for::<L, ITERS>);
        assert!(EXPECTED_RANGE.contains(&value));
    }

    pub fn lots_and_lots_mixed_lock<L>()
    where
        L: TryLockThen<Target = Int> + Send + Sync + 'static,
    {
        let value = lots_and_lots::<L, THREADS>(mixed_lock_inc_for::<L, ITERS>);
        assert!(EXPECTED_RANGE.contains(&value));
    }

    pub fn smoke<L>()
    where
        L: LockWithThen<Target = Int>,
    {
        let mutex = L::new(1);
        let mut node = L::Node::default();
        mutex.lock_with_then(&mut node, |data| drop(data));
        mutex.lock_with_then(&mut node, |data| drop(data));
    }

    #[cfg(feature = "barging")]
    pub fn test_guard_debug_display<L>()
    where
        L: LockThen<Target = Int>,
        for<'a> <L as LockWithThen>::Guard<'a>: Debug + Display,
    {
        let value = 42;
        let mutex = L::new(value);
        mutex.lock_then(|data| {
            assert_eq!(format!("{value:?}"), format!("{data:?}"));
            assert_eq!(format!("{value}"), format!("{data}"));
        });
    }

    pub fn test_mutex_debug<L>()
    where
        L: LockThen<Target = Int> + Debug + Send + Sync + 'static,
    {
        let value = 42;
        let mutex = Arc::new(L::new(value));
        let msg = format!("Mutex {{ data: {value:?} }}");
        assert_eq!(msg, format!("{mutex:?}"));

        let c_mutex = Arc::clone(&mutex);
        let msg = "Mutex { data: <locked> }".to_string();
        mutex.lock_then(|_data| {
            assert_eq!(msg, format!("{:?}", *c_mutex));
        });
    }

    pub fn test_mutex_default<L>()
    where
        L: LockData<Target = Int> + Default,
    {
        let mutex: L = Default::default();
        assert_eq!(u32::default(), mutex.into_inner());
    }

    pub fn test_mutex_from<L>()
    where
        L: LockData<Target = Int> + From<Int>,
    {
        let value = 42;
        let mutex = L::from(value);
        assert_eq!(value, mutex.into_inner());
    }

    pub fn test_try_lock<L>()
    where
        L: TryLockThen<Target = ()>,
    {
        use std::rc::Rc;
        let mutex = Rc::new(L::new(()));
        let c_mutex = Rc::clone(&mutex);
        mutex.try_lock_then(|data| {
            assert!(c_mutex.is_locked());
            *data.unwrap().as_deref_mut() = ();
        });
        assert!(!mutex.is_locked());
    }

    pub fn test_into_inner<M>()
    where
        M: LockData<Target = NonCopy>,
    {
        let mutex = M::new(NonCopy(10));
        assert_eq!(mutex.into_inner(), NonCopy(10));
    }

    pub fn test_into_inner_drop<M>()
    where
        M: LockData<Target = Foo>,
    {
        let num_drops = Arc::new(AtomicUsize::new(0));
        let mutex = M::new(Foo(num_drops.clone()));
        assert_eq!(num_drops.load(Ordering::SeqCst), 0);
        {
            let _inner = mutex.into_inner();
            assert_eq!(num_drops.load(Ordering::SeqCst), 0);
        }
        assert_eq!(num_drops.load(Ordering::SeqCst), 1);
    }

    pub fn test_get_mut<M>()
    where
        M: LockData<Target = NonCopy>,
    {
        let mut mutex = M::new(NonCopy(10));
        *mutex.get_mut() = NonCopy(20);
        assert_eq!(mutex.into_inner(), NonCopy(20));
    }

    pub fn test_lock_arc_nested<L1, L2>()
    where
        L1: LockThen<Target = Int>,
        L2: LockThen<Target = Arc<L1>> + Send + Sync + 'static,
    {
        // Tests nested locks and access
        // to underlying data.
        let arc1 = Arc::new(L1::new(1));
        let arc2 = Arc::new(L2::new(arc1));
        let _t = thread::spawn(move || {
            let val = arc2.lock_then(|arc1| {
                let arc1 = arc1.as_deref();
                lock_get(&arc1)
            });
            assert_eq!(val, 1);
        })
        .join();
    }

    pub fn test_acquire_more_than_one_lock<L>()
    where
        L: LockThen<Target = Int> + Send + Sync + 'static,
    {
        let arc = Arc::new(L::new(1));
        let mut threads = Vec::new();
        for _ in 0..4 {
            let c_arc = Arc::clone(&arc);
            let t = thread::spawn(move || {
                c_arc.lock_then(|_d| {
                    let mutex = L::new(1);
                    mutex.lock_then(|_d| ());
                });
            });
            threads.push(t);
        }
        for thread in threads {
            let _t = thread.join();
        }
    }

    pub fn test_lock_arc_access_in_unwind<L>()
    where
        L: LockThen<Target = Int> + Send + Sync + 'static,
    {
        let arc = Arc::new(L::new(1));
        let arc2 = arc.clone();
        let _ = thread::spawn(move || {
            struct Unwinder<T: LockThen<Target = Int>> {
                i: Arc<T>,
            }
            impl<T: LockThen<Target = Int>> Drop for Unwinder<T> {
                fn drop(&mut self) {
                    lock_inc(&self.i);
                }
            }
            let _u = Unwinder { i: arc2 };
            panic!();
        })
        .join();
        let value = lock_get(&arc);
        assert_eq!(value, 2);
    }

    pub fn test_lock_unsized<L>()
    where
        L: LockThen<Target = [Int; 3]>,
    {
        let mutex = Arc::new(L::new([1, 2, 3]));
        {
            mutex.lock_then(|mut d| {
                d.as_deref_mut()[0] = 4;
                d.as_deref_mut()[2] = 5;
            });
        }
        let comp: &[Int] = &[4, 2, 5];
        let data = lock_get(&mutex);
        assert_eq!(comp, data);
    }
}
