//! Unfair MCS lock implementation.
//!
//! This implementation will have non-waiting threads race for the lock against
//! the front of the waiting queue thread. If the front of the queue thread
//! looses the race, it will simply keep spinning, while holding its position
//! in the queue. By allowing barging instead of forcing FIFO, a higher
//! throughput can be achieved when the lock is heavily contended.
//!
//! This module provides an implementation that is `no_std` compatible, it does
//! not require queue nodes to be allocated by the callers, and so it is
//! compatible with the [lock_api] crate (see `lock_api` feature).
//!
//! The lock is hold for as long as its associated RAII guard is in scope. Once
//! the guard is dropped, the mutex is freed. Mutex guards are returned by
//! [`lock`] and [`try_lock`]. Guards are also accessible as the closure argument
//! for [`lock_with`] and [`try_lock_with`] methods.
//!
//! The Mutex is generic over the relax policy. User may choose a policy as long
//! as it implements the [`Relax`] trait. There is a number of relax policies
//! provided by the [`relax`] module. Each module in `barging` provides type
//! aliases for [`Mutex`] and [`MutexGuard`] associated with one relax policy.
//! See their documentation for more information.
//!
//! [`lock`]: Mutex::lock
//! [`try_lock`]: Mutex::try_lock
//! [`lock_with`]: Mutex::lock_with
//! [`try_lock_with`]: Mutex::try_lock_with
//! [`relax`]: crate::relax
//! [`Relax`]: crate::relax::Relax
//! [lock_api]: https://crates.io/crates/lock_api

mod mutex;
pub use mutex::{Mutex, MutexGuard};

/// An unfair MCS lock that implements a `spin` relax policy.
///
/// During lock contention, this lock spins while signaling the processor that
/// it is running a busy-wait spin-loop.
pub mod spins {
    use super::mutex;
    use crate::relax::Spin;

    /// A [`barging::Mutex`] that implements the [`Spin`] relax policy.
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
    /// [`barging::Mutex`]: mutex::Mutex
    pub type Mutex<T> = mutex::Mutex<T, Spin>;

    /// A [`barging::MutexGuard`] that implements the [`Spin`] relax policy.
    ///
    /// [`barging::MutexGuard`]: mutex::MutexGuard
    pub type MutexGuard<'a, T> = mutex::MutexGuard<'a, T, Spin>;

    /// An unfair MCS lock that implements a `spin with backoff` relax policy.
    ///
    /// During lock contention, this lock will perform exponential backoff
    /// while spinning, signaling the processor that it is running a busy-wait
    /// spin-loop.
    pub mod backoff {
        use super::mutex;
        use crate::relax::SpinBackoff;

        /// A [`barging::Mutex`] that implements the [`SpinBackoff`] relax
        /// policy.
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
        /// [`barging::Mutex`]: mutex::Mutex
        pub type Mutex<T> = mutex::Mutex<T, SpinBackoff>;

        /// A [`barging::MutexGuard`] that implements the [`SpinBackoff`] relax
        /// policy.
        ///
        /// [`barging::MutexGuard`]: mutex::MutexGuard
        pub type MutexGuard<'a, T> = mutex::MutexGuard<'a, T, SpinBackoff>;
    }
}

/// An unfair MCS lock that implements a `yield` relax policy.
///
/// During lock contention, this lock will yield the current time slice to the
/// OS scheduler.
#[cfg(any(feature = "yield", loom, test))]
#[cfg_attr(docsrs, doc(cfg(feature = "yield")))]
pub mod yields {
    use super::mutex;
    use crate::relax::Yield;

    /// A [`barging::Mutex`] that implements the [`Yield`] relax policy.
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
    /// [`barging::Mutex`]: mutex::Mutex
    pub type Mutex<T> = mutex::Mutex<T, Yield>;

    /// A [`barging::MutexGuard`] that implements the [`Yield`] relax policy.
    ///
    /// [`barging::MutexGuard`]: mutex::MutexGuard
    pub type MutexGuard<'a, T> = mutex::MutexGuard<'a, T, Yield>;

    /// An unfair MCS lock that implements a `yield with backoff` relax policy.
    ///
    /// During lock contention, this lock will perform exponential backoff while
    /// spinning, up to a threshold, then yields back to the OS scheduler.
    #[cfg(feature = "yield")]
    pub mod backoff {
        use super::mutex;
        use crate::relax::YieldBackoff;

        /// A [`barging::Mutex`] that implements the [`YieldBackoff`] relax
        /// policy.
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
        /// [`barging::Mutex`]: mutex::Mutex
        pub type Mutex<T> = mutex::Mutex<T, YieldBackoff>;

        /// A [`barging::MutexGuard`] that implements the [`YieldBackoff`]
        /// relax policy.
        ///
        /// [`barging::MutexGuard`]: mutex::MutexGuard
        pub type MutexGuard<'a, T> = mutex::MutexGuard<'a, T, YieldBackoff>;
    }
}

/// An unfair MCS lock that implements a `loop` relax policy.
///
/// During lock contention, this lock will rapidly spin without telling the CPU
/// to do any power down.
pub mod loops {
    use super::mutex;
    use crate::relax::Loop;

    /// A [`barging::Mutex`] that implements the [`Loop`] relax policy.
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
    /// [`barging::Mutex`]: mutex::Mutex
    pub type Mutex<T> = mutex::Mutex<T, Loop>;

    /// A [`barging::MutexGuard`] that implements the [`Loop`] relax policy.
    ///
    /// [`barging::MutexGuard`]: mutex::MutexGuard
    pub type MutexGuard<'a, T> = mutex::MutexGuard<'a, T, Loop>;
}
