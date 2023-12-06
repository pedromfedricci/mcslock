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

use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::mpsc::channel;
use std::sync::Arc;
use std::thread;

use mcslock::lock_api::yields::Mutex;

#[derive(Eq, PartialEq, Debug)]
struct NonCopy(i32);

#[test]
fn smoke() {
    let m = Mutex::new(());
    drop(m.lock());
    drop(m.lock());
}

#[test]
fn lots_and_lots() {
    static LOCK: Mutex<u32> = Mutex::new(0);

    const ITERS: u32 = 1000;
    const CONCURRENCY: u32 = 3;

    fn inc() {
        for _ in 0..ITERS {
            let mut g = LOCK.lock();
            *g += 1;
        }
    }

    let (tx, rx) = channel();
    for _ in 0..CONCURRENCY {
        let tx2 = tx.clone();
        thread::spawn(move || {
            inc();
            tx2.send(()).unwrap();
        });
        let tx2 = tx.clone();
        thread::spawn(move || {
            inc();
            tx2.send(()).unwrap();
        });
    }

    drop(tx);
    for _ in 0..2 * CONCURRENCY {
        rx.recv().unwrap();
    }
    assert_eq!(*LOCK.lock(), ITERS * CONCURRENCY * 2);
}

#[test]
fn try_lock() {
    let m = Mutex::new(());
    *m.try_lock().unwrap() = ();
}

#[test]
fn test_into_inner() {
    let m = Mutex::new(NonCopy(10));
    assert_eq!(m.into_inner(), NonCopy(10));
}

#[test]
fn test_into_inner_drop() {
    struct Foo(Arc<AtomicUsize>);
    impl Drop for Foo {
        fn drop(&mut self) {
            self.0.fetch_add(1, Ordering::SeqCst);
        }
    }
    let num_drops = Arc::new(AtomicUsize::new(0));
    let m = Mutex::new(Foo(num_drops.clone()));
    assert_eq!(num_drops.load(Ordering::SeqCst), 0);
    {
        let _inner = m.into_inner();
        assert_eq!(num_drops.load(Ordering::SeqCst), 0);
    }
    assert_eq!(num_drops.load(Ordering::SeqCst), 1);
}

#[test]
fn test_get_mut() {
    let mut m = Mutex::new(NonCopy(10));
    *m.get_mut() = NonCopy(20);
    assert_eq!(m.into_inner(), NonCopy(20));
}

#[test]
fn test_lock_arc_nested() {
    // Tests nested locks and access
    // to underlying data.
    let arc = Arc::new(Mutex::new(1));
    let arc2 = Arc::new(Mutex::new(arc));
    let (tx, rx) = channel();
    let _t = thread::spawn(move || {
        let lock = arc2.lock();
        let lock2 = lock.lock();
        assert_eq!(*lock2, 1);
        tx.send(()).unwrap();
    });
    rx.recv().unwrap();
}

#[test]
fn test_recursive_lock() {
    let arc = Arc::new(Mutex::new(1));
    let (tx, rx) = channel();
    for _ in 0..4 {
        let tx2 = tx.clone();
        let c_arc = Arc::clone(&arc);
        let _t = thread::spawn(move || {
            let mutex = Mutex::new(1);
            let _lock = c_arc.lock();
            let lock2 = mutex.lock();
            assert_eq!(*lock2, 1);
            tx2.send(()).unwrap();
        });
    }
    drop(tx);
    rx.recv().unwrap();
}

#[test]
fn test_lock_arc_access_in_unwind() {
    let arc = Arc::new(Mutex::new(1));
    let arc2 = arc.clone();
    let _ = thread::spawn(move || -> () {
        struct Unwinder {
            i: Arc<Mutex<i32>>,
        }
        impl Drop for Unwinder {
            fn drop(&mut self) {
                *self.i.lock() += 1;
            }
        }
        let _u = Unwinder { i: arc2 };
        panic!();
    })
    .join();
    let lock = arc.lock();
    assert_eq!(*lock, 2);
}

#[test]
fn test_lock_unsized() {
    let lock: &Mutex<[i32]> = &Mutex::new([1, 2, 3]);
    {
        let b = &mut *lock.lock();
        b[0] = 4;
        b[2] = 5;
    }
    let comp: &[i32] = &[4, 2, 5];
    assert_eq!(&*lock.lock(), comp);
}
