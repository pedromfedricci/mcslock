use std::sync::mpsc::channel;
use std::sync::Arc;
use std::thread;

// Requires `parking` feature.
// `spins::Mutex` spins for a while then parks during contention.
use mcslock::parking::raw::{spins::Mutex, MutexNode};

// Requires that the `thread_local` feature is enabled.
mcslock::thread_local_parking_node! {
    // * Allows multiple static definitions, must be separated with semicolons.
    // * Visibility is optional (private by default).
    // * Requires `static` keyword and a UPPER_SNAKE_CASE name.
    pub static NODE;
    static UNUSED_NODE;
}

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
            data.lock_with_then(&mut node, |data| {
                *data += 1;
                if *data == N {
                    tx.send(()).unwrap();
                }
                // The lock is unlocked here at the end of the closure scope.
            });
            // The node can now be reused for other locking operations.
            let _ = data.lock_with_then(&mut node, |data| *data);
        });
    }
    let _message = rx.recv();

    // A thread local node is borrowed.
    let count = data.lock_with_local_then(&NODE, |data| *data);
    assert_eq!(count, N);
}
