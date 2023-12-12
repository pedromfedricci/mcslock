#[cfg(all(not(loom), test))]
pub use core::ops::DerefMut as Guard;

#[cfg(all(loom, test))]
pub use crate::loom::Guard;

/// A trait for lock types that can run closures against the guard.
pub trait LockWith {
    /// The resulting type after dereferencing.
    type Target: ?Sized;

    /// The guard type that holds exclusive access to the underlying data.
    type Guard<'a>: Guard<Target = Self::Target>
    where
        Self: 'a,
        Self::Target: 'a;

    /// Creates a new mutex in an unlocked state ready for use.
    fn new(value: Self::Target) -> Self
    where
        Self::Target: Sized;

    // Attempts to acquire this lock and then runs the closure against its
    // guard.
    fn try_lock_with<F, Ret>(&self, f: F) -> Ret
    where
        F: FnOnce(Option<Self::Guard<'_>>) -> Ret;

    /// Acquires a mutex and then runs the closure against its guard.
    fn lock_with<F, Ret>(&self, f: F) -> Ret
    where
        F: FnOnce(Self::Guard<'_>) -> Ret;
}

#[cfg(all(not(loom), test))]
pub mod tests {
    use super::LockWith;

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

    // use std::sync::atomic::{AtomicUsize, Ordering};
    use std::sync::mpsc::channel;
    use std::sync::Arc;
    use std::thread;

    type Int = u32;

    #[derive(Eq, PartialEq, Debug)]
    struct NonCopy(u32);

    pub fn smoke<L>()
    where
        L: LockWith<Target = Int>,
    {
        let mutex = L::new(1);
        mutex.lock_with(|guard| drop(guard));
        mutex.lock_with(|guard| drop(guard));
    }

    pub fn lots_and_lots<L>(data: &Arc<L>)
    where
        L: LockWith<Target = Int> + Send + Sync + 'static,
    {
        const ITERS: u32 = 1000;
        const CONCURRENCY: u32 = 3;

        fn inc<L: LockWith<Target = Int>>(data: &Arc<L>) {
            for _ in 0..ITERS {
                data.lock_with(|mut guard| *guard += 1);
            }
        }

        let (tx, rx) = channel();
        for _ in 0..CONCURRENCY {
            let data1 = Arc::clone(data);
            let tx2 = tx.clone();
            thread::spawn(move || {
                inc(&data1);
                tx2.send(()).unwrap();
            });
            let data2 = Arc::clone(data);
            let tx2 = tx.clone();
            thread::spawn(move || {
                inc(&data2);
                tx2.send(()).unwrap();
            });
        }

        drop(tx);
        for _ in 0..2 * CONCURRENCY {
            rx.recv().unwrap();
        }
        let value = data.lock_with(|guard| *guard);
        assert_eq!(value, ITERS * CONCURRENCY * 2);
    }

    pub fn test_try_lock<L>()
    where
        L: LockWith<Target = ()>,
    {
        let mutex = L::new(());
        mutex.try_lock_with(|guard| *guard.unwrap() = ());
    }

    // fn test_into_inner<L: LockWith<Target = NonCopy>>() {
    //     let m = L::new(NonCopy(10));
    //     assert_eq!(m.into_inner(), NonCopy(10));
    // }

    // fn test_into_inner_drop() {
    //     struct Foo(Arc<AtomicUsize>);
    //     impl Drop for Foo {
    //         fn drop(&mut self) {
    //             self.0.fetch_add(1, Ordering::SeqCst);
    //         }
    //     }
    //     let num_drops = Arc::new(AtomicUsize::new(0));
    //     let m = Mutex::new(Foo(num_drops.clone()));
    //     assert_eq!(num_drops.load(Ordering::SeqCst), 0);
    //     {
    //         let _inner = m.into_inner();
    //         assert_eq!(num_drops.load(Ordering::SeqCst), 0);
    //     }
    //     assert_eq!(num_drops.load(Ordering::SeqCst), 1);
    // }

    // fn test_get_mut() {
    //     let mut m = Mutex::new(NonCopy(10));
    //     *m.get_mut() = NonCopy(20);
    //     assert_eq!(m.into_inner(), NonCopy(20));
    // }

    // #[should_panic = literal_panic_msg!()]
    pub fn test_lock_arc_nested<L1, L2>()
    where
        L1: LockWith<Target = Int>,
        L2: LockWith<Target = Arc<L1>> + Send + Sync + 'static,
    {
        // Tests nested locks and access
        // to underlying data.
        let arc = Arc::new(L1::new(1));
        let arc2 = Arc::new(L2::new(arc));
        let (tx, rx) = channel();
        let _t = thread::spawn(move || {
            let val = arc2.lock_with(|arc2| arc2.lock_with(|g| *g));
            assert_eq!(val, 1);
            tx.send(()).unwrap();
        });
        rx.recv().unwrap();
    }

    // #[should_panic = literal_panic_msg!()]
    pub fn test_acquire_more_than_one_lock<L>()
    where
        L: LockWith<Target = Int> + Send + Sync + 'static,
    {
        let arc = Arc::new(L::new(1));
        let (tx, rx) = channel();
        for _ in 0..4 {
            let tx2 = tx.clone();
            let c_arc = Arc::clone(&arc);
            let _t = thread::spawn(move || {
                c_arc.lock_with(|_g| {
                    let mutex = L::new(1);
                    mutex.lock_with(|_g| ());
                });
                tx2.send(()).unwrap();
            });
        }
        drop(tx);
        rx.recv().unwrap();
    }

    pub fn test_lock_arc_access_in_unwind<L>()
    where
        L: LockWith<Target = Int> + Send + Sync + 'static,
    {
        let arc = Arc::new(L::new(1));
        let arc2 = arc.clone();
        let _ = thread::spawn(move || {
            struct Unwinder<T: LockWith<Target = Int>> {
                i: Arc<T>,
            }
            impl<T: LockWith<Target = Int>> Drop for Unwinder<T> {
                fn drop(&mut self) {
                    self.i.lock_with(|mut g| *g += 1);
                }
            }
            let _u = Unwinder { i: arc2 };
            panic!();
        })
        .join();
        let value = arc.lock_with(|g| *g);
        assert_eq!(value, 2);
    }

    pub fn test_lock_unsized<L>()
    where
        L: LockWith<Target = [Int; 3]>,
    {
        let lock: &L = &L::new([1, 2, 3]);
        {
            lock.lock_with(|mut g| {
                g[0] = 4;
                g[2] = 5;
            });
        }
        let comp: &[Int] = &[4, 2, 5];
        lock.lock_with(|g| assert_eq!(&*g, comp));
    }
}
