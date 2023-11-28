use std::sync::mpsc::channel;
use std::sync::Arc;
use std::thread;

use mcslock::thread_local::Mutex;

const N: usize = 10;

fn main() {
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
            // The shared state can only be accessed once the lock is held.
            // Our non-atomic increment is safe because we're the only thread
            // which can access the shared state when the lock is held.
            //
            // We unwrap() the return value to assert that we are not expecting
            // threads to ever fail while holding the lock.
            //
            // Data is exclusively accessed by the guard argument.
            data.lock_with(|mut data| {
                *data += 1;
                if *data == N {
                    tx.send(()).unwrap();
                }
                // the lock is unlocked here when `data` goes out of scope.
            })
        });
    }
    let _message = rx.recv().unwrap();

    let count = data.lock_with(|guard| *guard);
    assert_eq!(count, N);
}
