//! A simple and correct implementation of Mellor-Crummey and Scott
//! contention-free [spin-lock] for mutual exclusion, referred to as MCS lock.
//!
//! MCS lock is a List-Based Queuing Lock that avoids network contention by
//! having threads spin on local memory locations. The main properties of this
//! mechanism are:
//!
//! - guarantees FIFO ordering of lock acquisitions;
//! - spins on locally-accessible flag variables only;
//! - requires a small constant amount of space per lock; and
//! - works equally well (requiring only O(1) network transactions per lock
//!   acquisition) on machines with and without coherent caches.
//!
//! This algorithm and serveral others were introduced by [Mellor-Crummey and Scott] paper.
//! And a simpler correctness proof of the MCS lock was proposed by [Johnson and Harathi].
//!
//! ## Raw locking APIs
//!
//! Raw locking APIs require exclusive access to a local queue node. This node is
//! represented by the `MutexNode` type. The `raw` module provides an implmentation
//! that is `no_std` compatible, but also requires that queue nodes must be
//! instantiated by the callers.
//!
//! ```
//! use std::sync::Arc;
//! use std::thread;
//!
//! use mcslock::raw::{Mutex, MutexNode};
//!
//! let mutex = Arc::new(Mutex::new(0));
//! let c_mutex = Arc::clone(&mutex);
//!
//! thread::spawn(move || {
//!     // A queue node must be mutably accessible.
//!     let mut node = MutexNode::new();
//!     *c_mutex.lock(&mut node) = 10;
//! })
//! .join().expect("thread::spawn failed");
//!
//! // A queue node must be mutably accessible.
//! let mut node = MutexNode::new();
//! assert_eq!(*mutex.try_lock(&mut node).unwrap(), 10);
//! ```
//!
//! ## Thread local locking APIs
//!
//! This crate also provides locking APIs that do not require user-side node
//! instantiation, by enabling the `thread_local` feature. These APIs require
//! that critical sections must be provided as closures, and are not compatible
//! with `no_std` environments as they require thread local storage.
//!
//! ```
//! # #[cfg(feature = "thread_local")]
//! # {
//! use std::sync::Arc;
//! use std::thread;
//!
//! // Requires `thread_local` feature.
//! use mcslock::thread_local::Mutex;
//!
//! let mutex = Arc::new(Mutex::new(0));
//! let c_mutex = Arc::clone(&mutex);
//!
//! thread::spawn(move || {
//!     // Node instantiation is not required.
//!     // Critical section must be defined as closure.
//!     c_mutex.lock_with(|mut guard| *guard = 10);
//! })
//! .join().expect("thread::spawn failed");
//!
//! // Node instantiation is not required.
//! // Critical section must be defined as closure.
//! assert_eq!(mutex.try_lock_with(|guard| *guard.unwrap()), 10);
//! # }
//! # #[cfg(not(feature = "thread_local"))]
//! # fn main() {}
//! ```
//!
//! ## Use cases
//!
//! [Spinlocks are usually not what you want]. The majority of use cases are well
//! covered by OS-based mutexes like [`std::sync::Mutex`] or [`parking_lot::Mutex`].
//! These implementations will notify the system that the waiting thread should
//! be parked, freeing the processor to work on something else.
//!
//! Spinlocks are only efficient in very few circunstances where the overhead
//! of context switching or process rescheduling are greater than busy waiting
//! for very short periods. Spinlocks can be useful inside operating-system kernels,
//! on embedded systems or even complement other locking designs. As a reference
//! use case, some [Linux kernel mutexes] run an customized MCS lock specifically
//! tailored for optimistic spinning during contention before actually sleeping.
//! This implementation is `no_std` by default, so it's useful in those environments.
//!
//! ## API for `no_std` environments
//!
//! The [`raw`] locking interface of a MCS lock is not quite the same as other
//! mutexes. To acquire a raw MCS lock, a queue node must be exclusively borrowed for
//! the lifetime of the guard returned by [`lock`] or [`try_lock`]. This node is exposed
//! as the [`MutexNode`] type. See their documentation for more information. If you
//! are looking for spin-based primitives that implement the [lock_api] interface
//! and also compatible with `no_std`, consider using [spin-rs].
//!
//! ## Features
//!
//! This crate dos not provide any default features. Features that can be enabled
//! are:
//!
//! ### `yield`
//!
//! The `yield` feature requires linking to the standard library, so it is not
//! suitable for `no_std` environments. By enabling the `yield` feature, instead
//! of busy-waiting during lock acquisitions and releases, this will call
//! [`std::thread::yield_now`], which cooperatively gives up a timeslice to the
//! OS scheduler. This may cause a context switch, so you may not want to enable
//! this feature if your intention is to to actually do optimistic spinning. The
//! default implementation calls [`core::hint::spin_loop`], which does in fact
//! just simply busy-waits.
//!
//! ### `thread_local`
//!
//! The `thread_local` feature provides locking APIs that do not require user-side
//! node instantiation, but critical sections must be provided as closures. This
//! implementation handles the queue's nodes transparently, by storing them in
//! the thread local storage of the waiting threads. Thes locking implementations
//! will panic if recursively acquired. Not `no_std` compatible.
//!
//! ## Related projects
//!
//! These projects provide MCS lock implementations with different APIs,
//! implementation details or compiler requirements, you can check their
//! repositories:
//!
//! - `mcs-rs`: <https://github.com/gereeter/mcs-rs>
//! - `libmcs`: <https://github.com/topecongiro/libmcs>
//!
//! [`MutexNode`]: raw::MutexNode
//! [`lock`]: raw::Mutex::lock
//! [`try_lock`]: raw::Mutex::try_lock
//! [`std::sync::Mutex`]: https://doc.rust-lang.org/std/sync/struct.Mutex.html
//! [`parking_lot::Mutex`]: https://docs.rs/parking_lot/latest/parking_lot/type.Mutex.html
//! [`mcslock::Mutex`]: crate::Mutex
//! [`RawMutex`]: https://docs.rs/lock_api/latest/lock_api/trait.RawMutex.html
//! [`RawMutexFair`]: https://docs.rs/lock_api/latest/lock_api/trait.RawMutexFair.html
//! [`std::thread::yield_now`]: https://doc.rust-lang.org/std/thread/fn.yield_now.html
//! [spin-lock]: https://en.wikipedia.org/wiki/Spinlock
//! [spin-rs]: https://docs.rs/spin/latest/spin
//! [lock_api]: https://docs.rs/lock_api/latest/lock_api
//! [Linux kernel mutexes]: https://www.kernel.org/doc/html/latest/locking/mutex-design.html
//! [Spinlocks are usually not what you want]: https://matklad.github.io/2020/01/02/spinlocks-considered-harmful.html
//! [Mellor-Crummey and Scott]: https://www.cs.rochester.edu/~scott/papers/1991_TOCS_synch.pdf
//! [Johnson and Harathi]: https://web.archive.org/web/20140411142823/http://www.cise.ufl.edu/tr/DOC/REP-1992-71.pdf

#![cfg_attr(
    all(not(any(feature = "yield", feature = "thread_local")), not(loom), not(test)),
    no_std
)]
#![cfg_attr(docsrs, feature(doc_cfg))]
#![warn(missing_docs)]

#[cfg(all(loom, test))]
pub(crate) mod loom;

pub mod raw;

// The `thread_local` feature requires linking with std.
#[cfg(feature = "thread_local")]
#[cfg_attr(docsrs, doc(cfg(feature = "thread_local")))]
pub mod thread_local;
