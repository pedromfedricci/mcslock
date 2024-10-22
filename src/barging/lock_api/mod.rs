//! Unfair MCS lock aliases for [`lock_api::Mutex`].
//!
//! This module exports [`lock_api::Mutex`] and [`lock_api::MutexGuard`] type
//! aliases with a `barging` MCS lock and guard as their inner types. The
//! [`barging::Mutex`] type will implement the [`lock_api::RawMutex`] trait when
//! this feature is enabled. The `barging` MCS lock is a unfair lock.
//!
//! This module provides an implementation that is `no_std` compatible.
//!
//! The lock is hold for as long as its associated RAII guard is in scope. Once
//! the guard is dropped, the mutex is freed. Mutex guards are returned by
//! [`lock`] and [`try_lock`].
//!
//! This Mutex is generic over the two layers of relax policies. User may
//! choose a policy as long as it implements the [`Relax`] trait. The shared
//! lock relax policy is associated with the `Rs` generic paramater. The
//! handoff relax policy is then associated with the `Rq` generic parameter.
//! Backoff relax policies are usually prefered for shared lock contention,
//! while non-backoff relax policies are usually prefered for handoffs.
//!
//! There is a number of relax policies provided by the [`relax`] module. The
//! following modules provide type aliases for [`lock_api::Mutex`] and
//! [`lock_api::MutexGuard`] associated with a relax policy. See their
//! documentation for more information.
//!
//! [`relax`]: crate::relax
//! [`Relax`]: crate::relax::Relax
//! [`barging::Mutex`]: crate::barging::Mutex
//!
//! [lock_api]: https://crates.io/crates/lock_api
//! [`lock_api::Mutex`]: https://docs.rs/lock_api/latest/lock_api/struct.Mutex.html
//! [`lock_api::MutexGuard`]: https://docs.rs/lock_api/latest/lock_api/struct.MutexGuard.html
//! [`lock_api::RawMutex`]: https://docs.rs/lock_api/latest/lock_api/trait.RawMutex.html
//! [`lock`]: https://docs.rs/lock_api/latest/lock_api/struct.Mutex.html#method.lock
//! [`try_lock`]: https://docs.rs/lock_api/latest/lock_api/struct.Mutex.html#method.try_lock

mod mutex;
pub use mutex::{Mutex, MutexGuard};

/// An unfair MCS lock that implements a `spin` relax policy.
///
/// During lock contention, this lock spins while signaling the processor that
/// it is running a busy-wait spin-loop.
pub mod spins {
    use super::mutex;
    use crate::relax::Spin;

    /// A [`lock_api::Mutex`] that implements the [`Spin`] relax policy.
    ///
    /// # Example
    ///
    /// ```
    /// use mcslock::barging::lock_api::spins::Mutex;
    ///
    /// let mutex = Mutex::new(0);
    /// let guard = mutex.lock();
    /// assert_eq!(*guard, 0);
    /// ```
    /// [`lock_api::Mutex`]: mutex::Mutex
    pub type Mutex<T> = mutex::Mutex<T, Spin, Spin>;

    /// A [`lock_api::MutexGuard`] that implements the [`Spin`] relax policy.
    ///
    /// [`lock_api::MutexGuard`]: mutex::MutexGuard
    pub type MutexGuard<'a, T> = mutex::MutexGuard<'a, T, Spin, Spin>;

    /// An unfair MCS lock that implements a `spin with backoff` relax policy.
    ///
    /// During lock contention, this lock will perform exponential backoff
    /// while spinning, signaling the processor that it is running a busy-wait
    /// spin-loop.
    pub mod backoff {
        use super::mutex;
        use crate::relax::{Spin, SpinBackoff};

        /// A [`lock_api::Mutex`] that implements the [`SpinBackoff`] relax
        /// policy.
        ///
        /// # Example
        ///
        /// ```
        /// use mcslock::barging::lock_api::spins::backoff::Mutex;
        ///
        /// let mutex = Mutex::new(0);
        /// let guard = mutex.lock();
        /// assert_eq!(*guard, 0);
        /// ```
        /// [`lock_api::Mutex`]: mutex::Mutex
        pub type Mutex<T> = mutex::Mutex<T, SpinBackoff, Spin>;

        /// A [`lock_api::MutexGuard`] that implements the [`SpinBackoff`] relax
        /// policy.
        ///
        /// [`lock_api::MutexGuard`]: mutex::MutexGuard
        pub type MutexGuard<'a, T> = mutex::MutexGuard<'a, T, SpinBackoff, Spin>;
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

    /// A [`lock_api::Mutex`] that implements the [`Yield`] relax policy.
    ///
    /// # Example
    ///
    /// ```
    /// use mcslock::barging::lock_api::yields::Mutex;
    ///
    /// let mutex = Mutex::new(0);
    /// let guard = mutex.lock();
    /// assert_eq!(*guard, 0);
    /// ```
    /// [`lock_api::Mutex`]: mutex::Mutex
    pub type Mutex<T> = mutex::Mutex<T, Yield, Yield>;

    /// A [`lock_api::MutexGuard`] that implements the [`Yield`] relax policy.
    ///
    /// [`lock_api::MutexGuard`]: mutex::MutexGuard
    pub type MutexGuard<'a, T> = mutex::MutexGuard<'a, T, Yield, Yield>;

    /// An unfair MCS lock that implements a `yield with backoff` relax policy.
    ///
    /// During lock contention, this lock will perform exponential backoff while
    /// spinning, up to a threshold, then yields back to the OS scheduler.
    pub mod backoff {
        use super::mutex;
        use crate::relax::{Yield, YieldBackoff};

        /// A [`lock_api::Mutex`] that implements the [`YieldBackoff`] relax
        /// policy.
        ///
        /// # Example
        ///
        /// ```
        /// use mcslock::barging::lock_api::yields::backoff::Mutex;
        ///
        /// let mutex = Mutex::new(0);
        /// let guard = mutex.lock();
        /// assert_eq!(*guard, 0);
        /// ```
        /// [`lock_api::Mutex`]: mutex::Mutex
        pub type Mutex<T> = mutex::Mutex<T, YieldBackoff, Yield>;

        /// A [`lock_api::MutexGuard`] that implements the [`YieldBackoff`]
        /// relax policy.
        ///
        /// [`lock_api::MutexGuard`]: mutex::MutexGuard
        pub type MutexGuard<'a, T> = mutex::MutexGuard<'a, T, YieldBackoff, Yield>;
    }
}

/// An unfair MCS lock that implements a `loop` relax policy.
///
/// During lock contention, this lock will rapidly spin without telling the CPU
/// to do any power down.
pub mod loops {
    use super::mutex;
    use crate::relax::Loop;

    /// A [`lock_api::Mutex`] that implements the [`Loop`] relax policy.
    ///
    /// # Example
    ///
    /// ```
    /// use mcslock::barging::lock_api::loops::Mutex;
    ///
    /// let mutex = Mutex::new(0);
    /// let guard = mutex.lock();
    /// assert_eq!(*guard, 0);
    /// ```
    /// [`lock_api::Mutex`]: mutex::Mutex
    pub type Mutex<T> = mutex::Mutex<T, Loop, Loop>;

    /// A [`lock_api::MutexGuard`] that implements the [`Loop`] relax policy.
    ///
    /// [`lock_api::MutexGuard`]: mutex::MutexGuard
    pub type MutexGuard<'a, T> = mutex::MutexGuard<'a, T, Loop, Loop>;
}
