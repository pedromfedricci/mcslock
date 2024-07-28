//! A barging MCS lock implementation that is compliant with the [lock_api] crate.
//!
//! This implementation will have non-waiting threads race for the lock against
//! the front of the waiting queue thread. If the front of the queue thread
//! looses the race, it will simply keep spinning, while holding its position
//! in the queue. By allowing barging instead of forcing FIFO, a higher throughput
//! can be achieved when the lock is heavily contended. This implementation is
//! suitable for `no_std` environments, and the locking APIs are compatible with
//! the [lock_api] crate (see `lock_api` feature).
//!
//! The lock is hold for as long as its associated RAII guard is in scope. Once
//! the guard is dropped, the mutex is freed. Mutex guards are returned by
//! [`lock`] and [`try_lock`]. Guards are also accessible as the closure argument
//! for [`lock_with`] and [`try_lock_with`] methods.
//!
//! This Mutex is generic over the two layers of relax strategies. User may
//! choose a strategy as long as it implements the [`Relax`] trait. The shared
//! lock relax strategy is associated with the `Rs` generic paramater. The
//! handoff relax strategy is then associated with the `Rq` generic parameter.
//! Backoff relax strategies are usually prefered for shared lock contention,
//! while non-backoff relax strategies are usually prefered for handoffs.
//!
//! There is a number of strategies provided by the [`relax`] module. Each
//! submodule provides type aliases for [`Mutex`] and [`MutexGuard`] associated
//! with one relax strategy. See their documentation for more information.
//!
//! [lock_api]: https://crates.io/crates/lock_api
//! [`lock`]: Mutex::lock
//! [`try_lock`]: Mutex::try_lock
//! [`lock_with`]: Mutex::lock_with
//! [`try_lock_with`]: Mutex::try_lock_with
//! [`relax`]: crate::relax
//! [`Relax`]: crate::relax::Relax

mod mutex;
pub use mutex::{Mutex, MutexGuard};

#[cfg(all(feature = "lock_api", not(loom)))]
#[cfg_attr(docsrs, doc(cfg(feature = "lock_api")))]
pub mod lock_api;

/// A `barging` MCS lock alias that signals the processor that it is running
/// a busy-wait spin-loop during lock contention.
pub mod spins {
    use super::mutex;
    use crate::relax::Spin;

    /// A `barging` MCS lock that implements the [`Spin`] relax strategy.
    ///
    /// # Example
    ///
    /// ```
    /// use mcslock::barging::spins::Mutex;
    ///
    /// let mutex = Mutex::new(0);
    /// let guard = mutex.lock();
    /// assert_eq!(*guard, 0);
    /// ```
    pub type Mutex<T> = mutex::Mutex<T, Spin, Spin>;

    /// A `barging` MCS guard that implements the [`Spin`] relax strategy.
    pub type MutexGuard<'a, T> = mutex::MutexGuard<'a, T, Spin, Spin>;

    /// A `barging` MCS lock alias that, during lock contention, will perform
    /// exponential backoff while signaling the processor that it is running a
    /// busy-wait spin-loop.
    pub mod backoff {
        use super::mutex;
        use crate::relax::{Spin, SpinBackoff};

        /// A `barging` MCS lock that implements the [`SpinBackoff`] relax
        /// strategy.
        ///
        /// # Example
        ///
        /// ```
        /// use mcslock::barging::spins::backoff::Mutex;
        ///
        /// let mutex = Mutex::new(0);
        /// let guard = mutex.lock();
        /// assert_eq!(*guard, 0);
        /// ```
        pub type Mutex<T> = mutex::Mutex<T, SpinBackoff, Spin>;

        /// A `barging` MCS guard that implements the [`SpinBackoff`] relax
        /// strategy.
        pub type MutexGuard<'a, T> = mutex::MutexGuard<'a, T, SpinBackoff, Spin>;
    }
}

/// A `barging` MCS lock alias that yields the current time slice to the
/// OS scheduler during lock contention.
#[cfg(any(feature = "yield", loom, test))]
#[cfg_attr(docsrs, doc(cfg(feature = "yield")))]
pub mod yields {
    use super::mutex;
    use crate::relax::Yield;

    /// A `barging` MCS lock that implements the [`Yield`] relax strategy.
    ///
    /// # Example
    ///
    /// ```
    /// use mcslock::barging::yields::Mutex;
    ///
    /// let mutex = Mutex::new(0);
    /// let guard = mutex.lock();
    /// assert_eq!(*guard, 0);
    /// ```
    pub type Mutex<T> = mutex::Mutex<T, Yield, Yield>;

    /// A `barging` MCS guard that implements the [`Yield`] relax strategy.
    pub type MutexGuard<'a, T> = mutex::MutexGuard<'a, T, Yield, Yield>;

    /// A `barging` MCS lock alias that, during lock contention, will perform
    /// exponential backoff while spinning up to a threshold, then yields back
    /// to the OS scheduler.
    #[cfg(feature = "yield")]
    pub mod backoff {
        use super::mutex;
        use crate::relax::{Yield, YieldBackoff};

        /// A `barging` MCS lock that implements the [`YieldBackoff`] relax
        /// strategy.
        ///
        /// # Example
        ///
        /// ```
        /// use mcslock::barging::yields::backoff::Mutex;
        ///
        /// let mutex = Mutex::new(0);
        /// let guard = mutex.lock();
        /// assert_eq!(*guard, 0);
        /// ```
        pub type Mutex<T> = mutex::Mutex<T, YieldBackoff, Yield>;

        /// A `barging` MCS guard that implements the [`YieldBackoff`] relax
        /// strategy.
        pub type MutexGuard<'a, T> = mutex::MutexGuard<'a, T, YieldBackoff, Yield>;
    }
}

/// A `barging` MCS lock alias that rapidly spins without telling the CPU
/// to do any power down during lock contention.
pub mod loops {
    use super::mutex;
    use crate::relax::Loop;

    /// A `barging` MCS lock that implements the [`Loop`] relax strategy.
    ///
    /// # Example
    ///
    /// ```
    /// use mcslock::barging::loops::Mutex;
    ///
    /// let mutex = Mutex::new(0);
    /// let guard = mutex.lock();
    /// assert_eq!(*guard, 0);
    /// ```
    pub type Mutex<T> = mutex::Mutex<T, Loop, Loop>;

    /// A `barging` MCS guard that implements the [`Loop`] relax strategy.
    pub type MutexGuard<'a, T> = mutex::MutexGuard<'a, T, Loop, Loop>;
}
