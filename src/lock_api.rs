//! Locking interfaces for MCS lock that are compatible with [lock_api].
//!
//! This module exports [`lock_api::Mutex`] and [`lock_api::MutexGuard`] type
//! aliases with a `barging` MCS lock and guard as their inner types. The
//! [`barging::Mutex`] type will implement the [`lock_api::RawMutex`] trait when
//! this feature is enabled.
//!
//! The Mutex is generic over the relax strategy. User may choose a strategy
//! as long as it implements the [`Relax`] trait. There is a number of strategies
//! provided by the [`relax`] module. The following modules provide type aliases
//! for [`lock_api::Mutex`] and [`lock_api::MutexGuard`] associated with one
//! relax strategy. See their documentation for more information.
//!
//! [`relax`]: crate::relax
//! [`Relax`]: crate::relax::Relax
//! [`barging::Mutex`]: crate::barging::Mutex
//! [lock_api]: https://crates.io/crates/lock_api
//! [`lock_api::Mutex`]: https://docs.rs/lock_api/latest/lock_api/struct.Mutex.html
//! [`lock_api::MutexGuard`]: https://docs.rs/lock_api/latest/lock_api/struct.MutexGuard.html
//! [`lock_api::RawMutex`]: https://docs.rs/lock_api/latest/lock_api/trait.RawMutex.html
//! [`RawMutexFair`]: https://docs.rs/lock_api/latest/lock_api/trait.RawMutexFair.html

/// A lock that provides mutually exclusive data access that is compatible with
/// [`lock_api`](https://crates.io/crates/lock_api).
pub type Mutex<T, R> = lock_api::Mutex<crate::barging::Mutex<(), R>, T>;

/// A guard that provides mutable data access that is compatible with
/// [`lock_api`](https://crates.io/crates/lock_api).
pub type MutexGuard<'a, T, R> = lock_api::MutexGuard<'a, crate::barging::Mutex<(), R>, T>;

/// A `barging` MCS lock alias that signals the processor that it is running
/// a busy-wait spin-loop during lock contention.
pub mod spins {
    use crate::relax::Spin;

    /// A `barging` MCS lock that implements the [`Spin`] relax strategy
    /// and compatible with the `lock_api` crate.
    ///
    /// # Example
    ///
    /// ```
    /// use mcslock::lock_api::spins::Mutex;
    ///
    /// let mutex = Mutex::new(0);
    /// let guard = mutex.lock();
    /// assert_eq!(*guard, 0);
    /// ```
    pub type Mutex<T> = super::Mutex<T, Spin>;

    /// A `barging` MCS guard that implements the [`Spin`] relax strategy
    /// and compatible with the `lock_api` crate.
    pub type MutexGuard<'a, T> = super::MutexGuard<'a, T, Spin>;
}

/// A `barging` MCS lock alias that yields the current time slice to the
/// OS scheduler during lock contention.
#[cfg(any(feature = "yield", loom, test))]
#[cfg_attr(docsrs, doc(cfg(feature = "yield")))]
pub mod yields {
    use crate::relax::Yield;

    /// A `barging` MCS lock that implements the [`Yield`] relax strategy
    /// and compatible with the `lock_api` crate.
    ///
    /// # Example
    ///
    /// ```
    /// use mcslock::lock_api::yields::Mutex;
    ///
    /// let mutex = Mutex::new(0);
    /// let guard = mutex.lock();
    /// assert_eq!(*guard, 0);
    /// ```
    pub type Mutex<T> = super::Mutex<T, Yield>;

    /// A `barging` MCS guard that implements the [`Yield`] relax strategy
    /// and compatible with the `lock_api` crate.
    pub type MutexGuard<'a, T> = super::MutexGuard<'a, T, Yield>;
}

/// A `barging` MCS lock alias that rapidly spins without telling the CPU
/// to do any power down during lock contention.
pub mod loops {
    use crate::relax::Loop;

    /// A `barging` MCS lock that implements the [`Loop`] relax strategy
    /// and compatible with the `lock_api` crate.
    ///
    /// # Example
    ///
    /// ```
    /// use mcslock::lock_api::loops::Mutex;
    ///
    /// let mutex = Mutex::new(0);
    /// let guard = mutex.lock();
    /// assert_eq!(*guard, 0);
    /// ```
    pub type Mutex<T> = super::Mutex<T, Loop>;

    /// A `barging` MCS guard that implements the [`Loop`] relax strategy
    /// and compatible with the `lock_api` crate.
    pub type MutexGuard<'a, T> = super::MutexGuard<'a, T, Loop>;
}

/// A `barging` MCS lock alias that, during lock contention, will perform
/// exponential backoff while signaling the processor that it is running a
/// busy-wait spin-loop.
pub mod spins_backoff {
    use crate::relax::SpinBackoff;

    /// A `barging` MCS lock that implements the [`SpinBackoff`] relax
    /// strategy and compatible with the `lock_api` crate.
    ///
    /// # Example
    ///
    /// ```
    /// use mcslock::lock_api::spins_backoff::Mutex;
    ///
    /// let mutex = Mutex::new(0);
    /// let guard = mutex.lock();
    /// assert_eq!(*guard, 0);
    /// ```
    pub type Mutex<T> = super::Mutex<T, SpinBackoff>;

    /// A `barging` MCS guard that implements the [`SpinBackoff`] relax
    /// strategy and compatible with the `lock_api` crate.
    pub type MutexGuard<'a, T> = super::MutexGuard<'a, T, SpinBackoff>;
}

/// A `barging` MCS lock alias that, during lock contention, will perform
/// exponential backoff while spinning up to a threshold, then yields back to
/// the OS scheduler.
#[cfg(feature = "yield")]
#[cfg_attr(docsrs, doc(cfg(feature = "yield")))]
pub mod yields_backoff {
    use crate::relax::YieldBackoff;

    /// A `barging` MCS lock that implements the [`YieldBackoff`] relax
    /// strategy and compatible with the `lock_api` crate.
    ///
    /// # Example
    ///
    /// ```
    /// use mcslock::lock_api::yields_backoff::Mutex;
    ///
    /// let mutex = Mutex::new(0);
    /// let guard = mutex.lock();
    /// assert_eq!(*guard, 0);
    /// ```
    pub type Mutex<T> = super::Mutex<T, YieldBackoff>;

    /// A `barging` MCS guard that implements the [`YieldBackoff`] relax
    /// strategy and compatible with the `lock_api` crate.
    pub type MutexGuard<'a, T> = super::MutexGuard<'a, T, YieldBackoff>;
}