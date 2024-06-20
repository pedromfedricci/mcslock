use std::sync::Arc;
use std::thread;

// Requires `parking` feature.
// `spins::Mutex` spins for a while then parks during contention.
use mcslock::parking::raw::{spins::Mutex, MutexNode};

// Requires `thread_local` feature.
mcslock::thread_local_parking_node!(static NODE);

fn main() {
    let mutex = Arc::new(Mutex::new(0));
    let c_mutex = Arc::clone(&mutex);

    thread::spawn(move || {
        // Local node handles are provided by reference.
        // Critical section must be defined as a closure.
        c_mutex.lock_with_local(&NODE, |mut guard| *guard = 10);
    })
    .join()
    .expect("thread::spawn failed");

    // A queue node must be mutably accessible.
    let mut node = MutexNode::new();
    assert_eq!(*mutex.try_lock(&mut node).unwrap(), 10);
}
