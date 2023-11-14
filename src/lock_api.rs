//! Locking interfaces for MCS lock that are compatible with [lock_api].
//!
//! This module exports [`lock_api::Mutex`] and [`lock_api::MutexGuard`] aliases
//! with a MCS lock and guard as their inner types.
//!
//! [`mcslock::Mutex`] implements [`RawMutex`] and [`RawMutexFair`] only if the
//! `thread_local` feature is enabled. Therefore, this integration is not
//! compatible with `no_std` environments.
//!
//! [lock_api]: https://crates.io/crates/lock_api
//! [`lock_api::Mutex`]: https://docs.rs/lock_api/latest/lock_api/struct.Mutex.html
//! [`lock_api::MutexGuard`]: https://docs.rs/lock_api/latest/lock_api/struct.MutexGuard.html
//! [`mcslock::Mutex`]: crate::Mutex
//! [`RawMutex`]: https://docs.rs/lock_api/latest/lock_api/trait.RawMutex.html
//! [`RawMutexFair`]: https://docs.rs/lock_api/latest/lock_api/trait.RawMutexFair.html

use crate::thread_local::Mutex as McsLock;

/// A lock that provides mutually exclusive data access that is compatible with
/// [`lock_api`](https://crates.io/crates/lock_api).
pub type Mutex<T> = lock_api::Mutex<McsLock<()>, T>;

/// A guard that provides mutable data access that is compatible with
/// [`lock_api`](https://crates.io/crates/lock_api).
pub type MutexGuard<'a, T> = lock_api::MutexGuard<'a, McsLock<()>, T>;
