# A simple and correct implementation of Mellor-Crummey and Scott Lock

MCS lock is a List-Based Queuing Lock that avoids network contention by
having threads spin on local memory locations. The main properties of this
mechanism are:

- guarantees FIFO ordering of lock acquisitions;
- spins on locally-accessible flag variables only;
- requires a small constant amount of space per lock; and
- works equally well (requiring only O(1) network transactions per lock
  acquisition) on machines with and without coherent caches.

This algorithm and serveral others were introduced by [Mellor-Crummey and Scott] paper.
And a simpler correctness proof of the MCS lock was proposed by [Johnson and Harathi].

## Install

```toml
# Cargo.toml

[dependencies]
mcslock = { version = "0.1", git = "https://github.com/pedromfedricci/mcslock" }
```

## Example

```rust
use std::sync::Arc;
use std::thread;
use std::sync::mpsc::channel;

use mcslock::{Mutex, MutexNode};

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
  let Some(count) = data.try_lock(&mut node) else { return };
  assert_eq!(N, *count);
  // lock is unlock here when `count` goes out of scope.
}
```

## Documentation

Currently this project documentation is not hosted anywhere, you can render
the documentation by cloning this repository and then run:

```bash
cargo doc --open
```

## Use cases

[Spinlocks are usually not what you want]. The majority of use cases are well
covered by OS-based mutexes like [`std::sync::Mutex`] or [`parking_lot::Mutex`].
These implementations will notify the system that the waiting thread should
be parked, freeing the processor to work on something else.

Spinlocks are only efficient in very few circunstances where the overhead
of context switching or process rescheduling are greater than busy waiting
for very short periods. Spinlocks can be useful inside operating-system kernels,
on embedded systems or even complement other locking designs. As a reference
use case, some [Linux kernel mutexes] run an customized MCS lock specifically
tailored for optimistic spinning during contention before actually sleeping.
This implementation is `no_std` by default, so it's useful in those environments.

## API compatibility

The locking interface of a MCS lock is not quite the same as other mutexes.
To acquire a MCS lock, a queue record must be mutably accessible for the
durating of the [`lock`] and [`try_lock`] calls. This record is exposed as
the [`MutexNode`] type. See their documentation for more information.
If you are looking for spin-based primitives that are compatible with
[lock_api], consider using [spin-rs], which is also suitable for `no_std`.

## Features

This crate dos not provide any default features. Features that can be enabled
are:

### yield

The `yield` feature requires linking to the standard library, so it is not
suitable for `no_std` environments. By enabling the `yield` feature, instead
of busy-waiting during lock acquisitions and releases, this will call
[`std::thread::yield_now`], which cooperatively gives up a timeslice to the
OS scheduler. This may cause a context switch, so you may not want to enable
this feature if your intention is to to actually do optimistic spinning. The
default implementation calls [`core::hint::spin_loop`], which does in fact
just simply busy-waits.

## Related projects

These projects provide MCS lock implementations with slightly different APIs,
implementation details or compiler requirements, you can check their
repositories:

- `mcs-rs`: <https://github.com/gereeter/mcs-rs>
- `libmcs`: <https://github.com/topecongiro/libmcs>

## License

Licensed under either of

- Apache License, Version 2.0 ([LICENSE-APACHE] or <http://apache.org/licenses/LICENSE-2.0>)
- MIT license ([LICENSE-MIT] or <http://opensource.org/licenses/MIT>)

## Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in the work by you, as defined in the Apache-2.0 license, shall
be dual licensed as above, without any additional terms or conditions.

## Code review

It is recommended to always use [cargo-crev] to verify the trustworthiness of
each of your dependencies, including this one.

[`lock`]: Mutex::lock
[`try_lock`]: Mutex::try_lock
[`std::sync::Mutex`]: https://doc.rust-lang.org/std/sync/struct.Mutex.html
[`parking_lot::Mutex`]: https://docs.rs/parking_lot/latest/parking_lot/type.Mutex.html
[`std::thread::yield_now`]: https://doc.rust-lang.org/std/thread/fn.yield_now.html
[spin-lock]: https://en.wikipedia.org/wiki/Spinlock
[spin-rs]: https://docs.rs/spin/latest/spin
[lock_api]: https://docs.rs/lock_api/latest/lock_api
[Linux kernel mutexes]: https://www.kernel.org/doc/html/latest/locking/mutex-design.html
[Spinlocks are usually not what you want]: https://matklad.github.io/2020/01/02/spinlocks-considered-harmful.html
[Mellor-Crummey and Scott]: https://www.cs.rochester.edu/~scott/papers/1991_TOCS_synch.pdf
[Johnson and Harathi]: https://web.archive.org/web/20140411142823/http://www.cise.ufl.edu/tr/DOC/REP-1992-71.pdf
