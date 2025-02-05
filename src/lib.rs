//! A simple and correct implementation of Mellor-Crummey and Scott
//! contention-free [lock] for mutual exclusion, referred to as MCS lock.
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
//! This algorithm and serveral others were introduced by
//! [Mellor-Crummey and Scott] paper. And a simpler correctness proof of the
//! MCS lock was proposed by [Johnson and Harathi].
//!
//! ## Spinlock use cases
//!
//! It is noteworthy to mention that [spinlocks are usually not what you want].
//! The majority of use cases are well covered by OS-based mutexes like
//! [`std::sync::Mutex`], [`parking_lot::Mutex`]. These implementations will
//! notify the system that the waiting thread should be parked, freeing the
//! processor to work on something else.
//!
//! Spinlocks are only efficient in very few circunstances where the overhead
//! of context switching or process rescheduling are greater than busy waiting
//! for very short periods. Spinlocks can be useful inside operating-system kernels,
//! on embedded systems or even complement other locking designs. As a reference
//! use case, some [Linux kernel mutexes] run an customized MCS lock specifically
//! tailored for optimistic spinning during contention before actually sleeping.
//! This implementation is `no_std` by default, so it's useful in those environments.
//!
//! ## Locking with a raw MCS spinlock
//!
//! This implementation operates under FIFO. Raw locking APIs require exclusive
//! access to a locally accessible queue node. This node is represented by the
//! [`raw::MutexNode`] type. Callers are responsible for instantiating the queue
//! nodes themselves. This implementation is `no_std` compatible. See the [`raw`]
//! module for more information.
//!
//! ```
//! use std::sync::Arc;
//! use std::thread;
//!
//! // Simply spins during contention.
//! use mcslock::raw::{spins::Mutex, MutexNode};
//!
//! let mutex = Arc::new(Mutex::new(0));
//! let c_mutex = Arc::clone(&mutex);
//!
//! thread::spawn(move || {
//!     // A queue node must be mutably accessible.
//!     // Critical section must be defined as a closure.
//!     let mut node = MutexNode::new();
//!     c_mutex.lock_with_then(&mut node, |data| *data = 10);
//! })
//! .join().expect("thread::spawn failed");
//!
//! // A node may also be transparently allocated in the stack.
//! // Critical section must be defined as a closure.
//! assert_eq!(mutex.try_lock_then(|data| *data.unwrap()), 10);
//! ```
//!
//! ## Thread local queue nodes
//!
//! [`raw::Mutex`] supports locking APIs that access queue nodes that are stored
//! in the thread local storage. These locking APIs require a static reference
//! to a [`raw::LocalMutexNode`] key. Keys must be generated by the
//! [`thread_local_node!`] macro. Thread local nodes are not `no_std` compatible
//! and can be enabled through the `thread_local` feature.
//!
//! ```
//! # #[cfg(feature = "thread_local")]
//! # {
//! use std::sync::Arc;
//! use std::thread;
//!
//! // Simply spins during contention.
//! use mcslock::raw::spins::Mutex;
//!
//! // Requires `thread_local` feature.
//! mcslock::thread_local_node!(static NODE);
//!
//! let mutex = Arc::new(Mutex::new(0));
//! let c_mutex = Arc::clone(&mutex);
//!
//! thread::spawn(move || {
//!     // Local node handles are provided by reference.
//!     // Critical section must be defined as a closure.
//!     c_mutex.lock_with_local_then(&NODE, |data| *data = 10);
//! })
//! .join().expect("thread::spawn failed");
//!
//! // A node may also be transparently allocated in the stack.
//! // Critical section must be defined as a closure.
//! assert_eq!(mutex.try_lock_then(|data| *data.unwrap()), 10);
//! # }
//! # #[cfg(not(feature = "thread_local"))]
//! # fn main() {}
//! ```
//!
//! ## Locking with a barging MCS spinlock
//!
//! This implementation will have non-waiting threads race for the lock against
//! the front of the waiting queue thread, which means this it is an unfair lock.
//! This implementation can be enabled through the `barging` feature, it is
//! suitable for `no_std` environments, and the locking APIs are compatible with
//! the `lock_api` crate. See [`barging`] and [`lock_api`] modules for
//! more information.
//!
//! ```
//! # #[cfg(feature = "barging")]
//! # {
//! use std::sync::Arc;
//! use std::thread;
//!
//! // Requires `barging` feature.
//! // Spins with exponential backoff during contention.
//! use mcslock::barging::spins::backoff::Mutex;
//!
//! let mutex = Arc::new(Mutex::new(0));
//! let c_mutex = Arc::clone(&mutex);
//!
//! thread::spawn(move || {
//!     *c_mutex.try_lock().unwrap() = 10;
//! })
//! .join().expect("thread::spawn failed");
//!
//! assert_eq!(*mutex.lock(), 10);
//! # }
//! # #[cfg(not(feature = "barging"))]
//! # fn main() {}
//! ```
//!
//! ## Features
//!
//! This crate dos not provide any default features. Features that can be enabled
//! are:
//!
//! ### yield
//!
//! The `yield` feature requires linking to the standard library, so it is not
//! suitable for `no_std` environments. By enabling the `yield` feature, instead
//! of busy-waiting during lock acquisitions and releases, this will call
//! [`std::thread::yield_now`], which cooperatively gives up a timeslice to the
//! OS scheduler. This may cause a context switch, so you may not want to enable
//! this feature if your intention is to to actually do optimistic spinning. The
//! default implementation calls [`core::hint::spin_loop`], which does in fact
//! just simply busy-waits. This feature is not `not_std` compatible.
//!
//! ### thread_local
//!
//! The `thread_local` feature enables [`raw::Mutex`] locking APIs that operate
//! over queue nodes that are stored at the thread local storage. These locking
//! APIs require a static reference to [`raw::LocalMutexNode`] keys. Keys must be
//! generated by the [`thread_local_node!`] macro. This feature also enables memory
//! optimizations for [`barging::Mutex`] locking operations. This feature is not
//! `no_std` compatible.
//!
//! This feature is not `no_std` compatible.
//!
//! ### barging
//!
//! The `barging` feature provides locking APIs that are compatible with the
//! [lock_api] crate. It does not require node allocations from the caller. The
//! [`barging`] module is suitable for `no_std` environments. This implementation
//! is not fair (does not guarantee FIFO), but can improve throughput when the lock
//! is heavily contended.
//!
//! ### lock_api
//!
//! This feature implements the [`RawMutex`] trait from the [lock_api]
//! crate for [`barging::Mutex`]. Aliases are provided by the [`barging::lock_api`]
//! (`no_std`) module.
//!
//! ## Related projects
//!
//! These projects provide MCS lock implementations with different APIs,
//! implementation details or compiler requirements, you can check their
//! repositories:
//!
//! - mcs-rs: <https://github.com/gereeter/mcs-rs>
//! - libmcs: <https://github.com/topecongiro/libmcs>
//!
//! [lock]: https://en.wikipedia.org/wiki/Lock_(computer_science)
//! [Mellor-Crummey and Scott]: https://www.cs.rochester.edu/~scott/papers/1991_TOCS_synch.pdf
//! [Johnson and Harathi]: https://web.archive.org/web/20140411142823/http://www.cise.ufl.edu/tr/DOC/REP-1992-71.pdf
//! [spinlocks are usually not what you want]: https://matklad.github.io/2020/01/02/spinlocks-considered-harmful.html
//! [Linux kernel mutexes]: https://www.kernel.org/doc/html/latest/locking/mutex-design.html
//!
//! [`parking_lot::Mutex`]: https://docs.rs/parking_lot/latest/parking_lot/type.Mutex.html
//! [lock_api]: https://docs.rs/lock_api/latest/lock_api
//! [`RawMutex`]: https://docs.rs/lock_api/latest/lock_api/trait.RawMutex.html
//! [`RawMutexFair`]: https://docs.rs/lock_api/latest/lock_api/trait.RawMutexFair.html
//! [`parking_lot::Mutex`]: https://docs.rs/parking_lot/latest/parking_lot/type.Mutex.html

#![no_std]
#![allow(clippy::doc_markdown)]
#![allow(clippy::inline_always)]
#![allow(clippy::module_name_repetitions)]
#![cfg_attr(docsrs, feature(doc_cfg))]
#![warn(missing_docs)]
#![warn(rust_2024_compatibility)]

#[cfg(any(feature = "yield", feature = "thread_local", loom, test))]
extern crate std;

#[cfg(feature = "thread_local")]
#[macro_use]
pub(crate) mod thread_local;

pub mod raw;
pub mod relax;

pub(crate) mod cfg;
pub(crate) mod inner;
pub(crate) mod lock;

#[cfg(feature = "barging")]
#[cfg_attr(docsrs, doc(cfg(feature = "barging")))]
pub mod barging;

#[cfg(test)]
pub(crate) mod test;

#[cfg(all(loom, test))]
#[cfg(not(tarpaulin))]
pub(crate) mod loom;
