# A simple and correct implementation of the MCS lock

[![MIT][mit-badge]][mit]
[![Apache 2.0][apache2-badge]][apache2]
[![Crates][crates-badge]][crates]
[![Docs][docs-badge]][docs]
[![CI][ci-badge]][ci]
[![Codecov][codecov-badge]][codecov]
![No_std][no_std-badge]

MCS lock is a List-Based Queuing Lock that avoids network contention by having
threads spin on local memory locations. The main properties of this mechanism are:

- guarantees FIFO ordering of lock acquisitions;
- spins on locally-accessible flag variables only;
- requires a small constant amount of space per lock; and
- works equally well (requiring only O(1) network transactions per lock
  acquisition) on machines with and without coherent caches.

This algorithm and several others were introduced by [Mellor-Crummey and Scott]
paper. And a simpler correctness proof of the MCS lock was proposed by
[Johnson and Harathi].

## Spinlock use cases

It is noteworthy to mention that [spinlocks are usually not what you want]. The
majority of use cases are well covered by OS-based mutexes like [`std::sync::Mutex`]
and [`parking_lot::Mutex`]. These implementations will notify the system that the
waiting thread should be parked, freeing the processor to work on something else.

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
# Features: `yield`, `barging`, `thread_local` and `lock_api`.
mcslock = { version = "0.4", features = ["thread_local"] }
```

## Documentation

This project documentation is hosted at [docs.rs][docs]. Or you can build it
locally with the following command:

```bash
RUSTDOCFLAGS="--cfg docsrs" cargo +nightly doc --all-features --open
```

## Locking with a raw MCS spinlock

This implementation operates under FIFO. Raw locking APIs require exclusive
access to a locally accessible queue node. This node is represented by the
[`raw::MutexNode`] type. Callers are responsible for instantiating the queue
nodes themselves. This implementation is `no_std` compatible. See the [`raw`]
module for more information.

```rust
use std::sync::Arc;
use std::thread;

// Simply spins during contention.
use mcslock::raw::{spins::Mutex, MutexNode};

fn main() {
    let mutex = Arc::new(Mutex::new(0));
    let c_mutex = Arc::clone(&mutex);

    thread::spawn(move || {
        // A queue node must be mutably accessible.
        // Critical section must be defined as a closure.
        let mut node = MutexNode::new();
        c_mutex.lock_with_then(&mut node, |data| *data = 10);
    })
    .join().expect("thread::spawn failed");

    // A node may also be transparently allocated in the stack.
    // Critical section must be defined as a closure.
    assert_eq!(mutex.try_lock_then(|data| *data.unwrap()), 10);
}
```

## Thread local queue nodes

[`raw::Mutex`] supports locking APIs that access queue nodes that are stored in
the thread local storage. These locking APIs require a static reference to a
[`raw::LocalMutexNode`] key. Keys must be generated by the [`thread_local_node!`]
macro. Thread local nodes are not `no_std` compatible and can be enabled through
the `thread_local` feature.

```rust
use std::sync::Arc;
use std::thread;

// Simply spins during contention.
use mcslock::raw::spins::Mutex;

// Requires `thread_local` feature.
mcslock::thread_local_node!(static NODE);

fn main() {
    let mutex = Arc::new(Mutex::new(0));
    let c_mutex = Arc::clone(&mutex);

    thread::spawn(move || {
        // Local node handles are provided by reference.
        // Critical section must be defined as a closure.
        c_mutex.lock_with_local_then(&NODE, |data| *data = 10);
    })
    .join().expect("thread::spawn failed");

    // A node may also be transparently allocated in the stack.
    // Critical section must be defined as a closure.
    assert_eq!(mutex.try_lock_then(|data| *data.unwrap()), 10);
}
```

## Locking with a barging MCS spinlock

This implementation will have non-waiting threads race for the lock against
the front of the waiting queue thread, which means this it is an unfair lock.
This implementation is suitable for `no_std` environments, and the locking
APIs are compatible with the [lock_api] crate. See [`barging`] and
[`barging::lock_api`] modules for more information.

```rust
use std::sync::Arc;
use std::thread;

// Requires `barging` feature.
// Spins with exponential backoff during contention.
use mcslock::barging::spins::backoff::Mutex;

fn main() {
    let mutex = Arc::new(Mutex::new(0));
    let c_mutex = Arc::clone(&mutex);

    thread::spawn(move || {
        *c_mutex.try_lock().unwrap() = 10;
    })
    .join().expect("thread::spawn failed");

    assert_eq!(*mutex.lock(), 10);
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
just simply busy-waits. This feature is not `no_std` compatible.

### thread_local

The `thread_local` feature enables [`raw::Mutex`] locking APIs that operate over
queue nodes that are stored at the thread local storage. These locking APIs
require a static reference to [`raw::LocalMutexNode`] keys. Keys must be generated
by the [`thread_local_node!`] macro. This feature also enables memory optimizations
for [`barging::Mutex`] locking operations. This feature is not `no_std`
compatible.

### barging

The `barging` feature provides locking APIs that are compatible with the
[lock_api] crate. It does not require node allocations from the caller.
The [`barging`] module is suitable for `no_std` environments. This implementation
is not fair (does not guarantee FIFO), but can improve throughput when the lock
is heavily contended.

### lock_api

This feature implements the [`RawMutex`] trait from the [lock_api] crate for
[`barging::Mutex`]. Aliases are provided by the [`barging::lock_api`] (`no_std`)
module.

## Minimum Supported Rust Version (MSRV)

This crate is guaranteed to compile on a Minimum Supported Rust Version (MSRV)
of 1.65.0 and above. This version will not be changed without a minor version
bump. If you intend to use this crate but can only target a older Rust version,
feel free to open a issue with your specific target, it is possible to lower
this crate MSRV substantially, it just has not been explored yet.

## Related projects

These projects provide MCS lock implementations with different APIs, capabilities,
implementation details or compiler requirements, you can check their repositories:

- mcs-rs: <https://github.com/gereeter/mcs-rs>
- libmcs: <https://github.com/topecongiro/libmcs>

## License

Licensed under either of

- Apache License, Version 2.0 ([LICENSE-APACHE](LICENSE-APACHE) or <http://apache.org/licenses/LICENSE-2.0>)
- MIT license ([LICENSE-MIT](LICENSE-MIT) or <http://opensource.org/licenses/MIT>)

## Contributing

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

[Mellor-Crummey and Scott]: https://www.cs.rochester.edu/~scott/papers/1991_TOCS_synch.pdf
[Johnson and Harathi]: https://web.archive.org/web/20140411142823/http://www.cise.ufl.edu/tr/DOC/REP-1992-71.pdf
[spinlocks are usually not what you want]: https://matklad.github.io/2020/01/02/spinlocks-considered-harmful.html
[Linux kernel mutexes]: https://www.kernel.org/doc/html/latest/locking/mutex-design.html

[`raw`]: https://docs.rs/mcslock/latest/mcslock/raw/index.html
[`raw::Mutex`]: https://docs.rs/mcslock/latest/mcslock/raw/struct.Mutex.html
[`raw::MutexNode`]: https://docs.rs/mcslock/latest/mcslock/raw/struct.MutexNode.html
[`raw::LocalMutexNode`]: https://docs.rs/mcslock/latest/mcslock/raw/struct.LocalMutexNode.html
[`barging`]: https://docs.rs/mcslock/latest/mcslock/barging/index.html
[`barging::lock_api`]: https://docs.rs/mcslock/latest/mcslock/barging/lock_api/index.html
[`barging::Mutex`]: https://docs.rs/mcslock/latest/mcslock/barging/struct.Mutex.html
[`thread_local_node!`]: https://docs.rs/mcslock/latest/mcslock/macro.thread_local_node.html

[`std::sync::Mutex`]: https://doc.rust-lang.org/std/sync/struct.Mutex.html
[`std::thread::yield_now`]: https://doc.rust-lang.org/std/thread/fn.yield_now.html
[`core::hint::spin_loop`]: https://doc.rust-lang.org/core/hint/fn.spin_loop.html

[lock_api]: https://docs.rs/lock_api/latest/lock_api
[`RawMutex`]: https://docs.rs/lock_api/latest/lock_api/trait.RawMutex.html
[`RawMutexFair`]: https://docs.rs/lock_api/latest/lock_api/trait.RawMutexFair.html
[`parking_lot::Mutex`]: https://docs.rs/parking_lot/latest/parking_lot/type.Mutex.html
