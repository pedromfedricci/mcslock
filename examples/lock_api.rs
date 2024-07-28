use std::sync::mpsc::channel;
use std::sync::Arc;
use std::thread;

// Requires that both `lock_api` and `barging` features are enabled.
//
// You may export these types to your callers, change the inner mutex type
// (as long as it implements the same raw mutex interfaces), without breaking
// their code.
//
// Maybe spin::lock_api::{Mutex, MutexGuard} is better for your use case? Switch it!
pub type Mutex<T> = mcslock::barging::lock_api::spins::Mutex<T>;
pub type MutexGuard<'a, T> = mcslock::barging::lock_api::spins::MutexGuard<'a, T>;

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
            // The shared state can only be accessed once the lock is held.
            // Our non-atomic increment is safe because we're the only thread
            // which can access the shared state when the lock is held.
            //
            // We unwrap() the return value to assert that we are not expecting
            // threads to ever fail while holding the lock.
            let mut data = data.lock();
            *data += 1;
            if *data == N {
                tx.send(()).unwrap();
            }
            // the lock is unlocked here when `data` goes out of scope.
        });
    }
    let _message = rx.recv();

    let count = data.lock();
    assert_eq!(*count, N);
    // lock is unlock here when `count` goes out of scope.
}
