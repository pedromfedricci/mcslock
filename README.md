# A simple and correct implementation of MCS lock

[![MIT][mit-badge]][mit]
[![Apache 2.0][apache2-badge]][apache2]
[![Docs][docs-badge]][docs]
[![Crates][crates-badge]][crates]
[![CI][ci-badge]][ci]
[![Codecov][codecov-badge]][codecov]
![No_std][no_std-badge]

MCS lock is a List-Based Queuing Lock that avoids network contention by
having threads spin on local memory locations. The main properties of this
mechanism are:

- guarantees FIFO ordering of lock acquisitions;
- spins on locally-accessible flag variables only;
- requires a small constant amount of space per lock; and
- works equally well (requiring only O(1) network transactions per lock
  acquisition) on machines with and without coherent caches.

This algorithm and several others were introduced by [Mellor-Crummey and Scott] paper.
And a simpler correctness proof of the MCS lock was proposed by [Johnson and Harathi].

## Use cases

It is noteworthy to mention that [spinlocks are usually not what you want]. The
majority of use cases are well covered by OS-based mutexes like
[`std::sync::Mutex`] or [`parking_lot::Mutex`]. These implementations will notify
the system that the waiting thread should be parked, freeing the processor to
work on something else.

Spinlocks are only efficient in very few circumstances where the overhead
of context switching or process rescheduling are greater than busy waiting
for very short periods. Spinlocks can be useful inside operating-system kernels,
on embedded systems or even complement other locking designs. As a reference
use case, some [Linux kernel mutexes] run an customized MCS lock specifically
tailored for optimistic spinning during contention before actually sleeping.
This implementation is `no_std` by default, so it's useful in those environments.

## Install

Run the following Cargo command in your project directory:

```bash
cargo add mcslock
```

Or add a entry under the `[dependencies]` section in your `Cargo.toml`:

```toml
# Cargo.toml

[dependencies]
# Available features: `yield`, `barging`, `thread_local` and `lock_api`.
mcslock = { version = "0.1", features = ["barging"] }
```

## Documentation

This project documentation is hosted at [docs.rs][docs]. Or you can build it
locally with the following command:

```bash
RUSTDOCFLAGS="--cfg docsrs" cargo +nightly doc --all-features --open
```

## Raw MCS lock

This implementation operates under FIFO. Raw locking APIs require exclusive
access to a locally accessible queue node. This node is represented by the
[`MutexNode`] type. Callers are responsible for instantiating the queue nodes
themselves. This implementation is `no_std` compatible. See [`raw`] module for
more information.

```rust
use std::sync::Arc;
use std::thread;

use mcslock::raw::spins::{Mutex, MutexNode};

fn main() {
    let mutex = Arc::new(Mutex::new(0));
    let c_mutex = Arc::clone(&mutex);

    thread::spawn(move || {
        // A queue node must be mutably accessible.
        let mut node = MutexNode::new();
        *c_mutex.lock(&mut node) = 10;
    })
    .join().expect("thread::spawn failed");

    // A queue node must be mutably accessible.
    let mut node = MutexNode::new();
    assert_eq!(*mutex.try_lock(&mut node).unwrap(), 10);
}
```

## Barging MCS lock

This implementation will have non-waiting threads race for the lock against
the front of the waiting queue thread, which means this it is an unfair lock.
This implementation is suitable for `no_std` environments, and the locking
APIs are compatible with the [lock_api] crate. See [`barging`] and [`lock_api`]
modules for more information.

```rust
use std::sync::Arc;
use std::thread;

// Requires `barging` feature.
use mcslock::barging::spins::Mutex;

fn main() {
    let mutex = Arc::new(Mutex::new(0));
    let c_mutex = Arc::clone(&mutex);

    thread::spawn(move || {
        *c_mutex.lock() = 10;
    })
    .join().expect("thread::spawn failed");

    assert_eq!(*mutex.try_lock().unwrap(), 10);
}
```

## Thread local MCS lock

This implementation also operates under FIFO. The locking APIs provided
by this module do not require user-side node allocation, critical
sections must be provided as closures and at most one lock can be held at
any time within a thread. It is not `no_std` compatible and can be enabled
through the `thread_local` feature. See [`thread_local`] module for more
information.

```rust
use std::sync::Arc;
use std::thread;

// Requires `thread_local` feature.
use mcslock::thread_local::spins::Mutex;

fn main() {
    let mutex = Arc::new(Mutex::new(0));
    let c_mutex = Arc::clone(&mutex);

    thread::spawn(move || {
        // Critical section must be defined as closure.
        c_mutex.lock_with(|mut guard| *guard = 10);
    })
    .join().expect("thread::spawn failed");

    // Critical section must be defined as closure.
    assert_eq!(mutex.try_lock_with(|guard| *guard.unwrap()), 10);
}
```

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

### barging

The `barging` feature provides locking APIs that are compatible with the
[lock_api] crate. It does not require node allocations from the caller,
and it is suitable for `no_std` environments. This implementation is not
fair (does not guarantee FIFO), but can improve throughput when the lock
is heavily contended.

### thread_local

The `thread_local` feature provides locking APIs that do not require user-side
node allocation, but critical sections must be provided as closures. This
implementation handles the queue's nodes transparently, by storing them in
the thread local storage of the waiting threads. These locking implementations
will panic if recursively acquired. Not `no_std` compatible.

### lock_api

This feature implements the [`RawMutex`] trait from the [lock_api] crate for
[`barging::Mutex`]. Aliases are provided by the [`lock_api`] module. This feature
is `no_std` compatible.

## Minimum Supported Rust Version (MSRV)

This crate is guaranteed to compile on a Minimum Supported Rust Version (MSRV)
of 1.65.0 and above. This version will not be changed without a minor version
bump. If you intend to use this crate but can only target a older Rust version,
feel free to open a issue with your specific target, it is possible to lower
this crate MSRV substantially, it just has not been explored yet.

## Related projects

These projects provide MCS lock implementations with slightly different APIs,
implementation details or compiler requirements, you can check their
repositories:

- mcs-rs: <https://github.com/gereeter/mcs-rs>
- libmcs: <https://github.com/topecongiro/libmcs>

## License

Licensed under either of

- Apache License, Version 2.0 ([LICENSE-APACHE](LICENSE-APACHE) or <http://apache.org/licenses/LICENSE-2.0>)
- MIT license ([LICENSE-MIT](LICENSE-MIT) or <http://opensource.org/licenses/MIT>)

## Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in the work by you, as defined in the Apache-2.0 license, shall
be dual licensed as above, without any additional terms or conditions.

## Code review

It is recommended to always use [cargo-crev] to verify the trustworthiness of
each of your dependencies, including this one.

[mit-badge]: https://img.shields.io/badge/License-MIT-blue.svg
[apache2-badge]: https://img.shields.io/badge/License-Apache_2.0-yellow.svg
[docs-badge]: https://img.shields.io/docsrs/mcslock
[crates-badge]: https://img.shields.io/crates/v/mcslock
[ci-badge]: https://github.com/pedromfedricci/mcslock/actions/workflows/ci.yml/badge.svg
[codecov-badge]: https://codecov.io/gh/pedromfedricci/mcslock/graph/badge.svg?token=A54PAF1K74
[no_std-badge]: https://img.shields.io/badge/no__std-compatible-success.svg

[mit]: https://opensource.org/licenses/MIT
[apache2]: https://opensource.org/licenses/Apache-2.0
[docs]: https://docs.rs/mcslock
[crates]: https://crates.io/crates/mcslock
[ci]: https://github.com/pedromfedricci/mcslock/actions/workflows/ci.yml
[codecov]: https://codecov.io/gh/pedromfedricci/mcslock
[cargo-crev]: https://github.com/crev-dev/cargo-crev

[`MutexNode`]: https://docs.rs/mcslock/latest/mcslock/raw/struct.MutexNode.html
[`barging::Mutex`]: https://docs.rs/mcslock/latest/mcslock/barging/struct.Mutex.html
[`raw`]: https://docs.rs/mcslock/latest/mcslock/raw/index.html
[`barging`]: https://docs.rs/mcslock/latest/mcslock/barging/index.html
[`lock_api`]: https://docs.rs/mcslock/latest/mcslock/lock_api/index.html
[`thread_local`]: https://docs.rs/mcslock/latest/mcslock/thread_local/index.html
[`std::sync::Mutex`]: https://doc.rust-lang.org/std/sync/struct.Mutex.html
[`parking_lot::Mutex`]: https://docs.rs/parking_lot/latest/parking_lot/type.Mutex.html
[`RawMutex`]: https://docs.rs/lock_api/latest/lock_api/trait.RawMutex.html
[`RawMutexFair`]: https://docs.rs/lock_api/latest/lock_api/trait.RawMutexFair.html
[`std::thread::yield_now`]: https://doc.rust-lang.org/std/thread/fn.yield_now.html
[`core::hint::spin_loop`]: https://doc.rust-lang.org/core/hint/fn.spin_loop.html
[spin-lock]: https://en.wikipedia.org/wiki/Spinlock
[spin-rs]: https://docs.rs/spin/latest/spin
[lock_api]: https://docs.rs/lock_api/latest/lock_api
[Linux kernel mutexes]: https://www.kernel.org/doc/html/latest/locking/mutex-design.html
[spinlocks are usually not what you want]: https://matklad.github.io/2020/01/02/spinlocks-considered-harmful.html
[Mellor-Crummey and Scott]: https://www.cs.rochester.edu/~scott/papers/1991_TOCS_synch.pdf
[Johnson and Harathi]: https://web.archive.org/web/20140411142823/http://www.cise.ufl.edu/tr/DOC/REP-1992-71.pdf
