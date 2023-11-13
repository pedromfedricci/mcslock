use std::sync::mpsc::channel;
use std::sync::Arc;
use std::thread;

use mcslock::raw::{Mutex, MutexNode};

fn main() {
    const N: usize = 10;

    // Spawn a few threads to increment a shared variable (non-atomically), and
    // let the main thread know once all increments are done.
    //
    // Here we're using an Arc to share memory among threads, and the data inside
    // the Arc is protected with a mutex.
    let data = Arc::new(Mutex::new(0));

    let (tx, rx) = channel();
    for _ in 0..N {
        let (data, tx) = (data.clone(), tx.clone());
        thread::spawn(move || {
            // A queue node must be mutably accessible.
            let mut node = MutexNode::new();
            // The shared state can only be accessed once the lock is held.
            // Our non-atomic increment is safe because we're the only thread
            // which can access the shared state when the lock is held.
            //
            // We unwrap() the return value to assert that we are not expecting
            // threads to ever fail while holding the lock.
            let mut data = data.lock(&mut node);
            *data += 1;
            if *data == N {
                tx.send(()).unwrap();
            }
            // the lock is unlocked here when `data` goes out of scope.
        });
    }
    let _message = rx.recv();

    // A queue node must be mutably accessible.
    let mut node = MutexNode::new();
    // Would return `None` if lock was already held.
    let count = data.try_lock(&mut node).unwrap();
    assert_eq!(*count, N);
    // lock is unlock here when `count` goes out of scope.
}