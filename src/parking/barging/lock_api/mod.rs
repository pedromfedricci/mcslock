//! Unfair MCS lock aliases for [`lock_api::Mutex`] with thread parking support.
//!
//! This module exports [`lock_api::Mutex`] and [`lock_api::MutexGuard`] type
//! aliases with a `barging` MCS lock and guard as their inner types. The
//! [`parking::barging::Mutex`] type will implement the [`lock_api::RawMutex`]
//! trait when this feature is enabled. The `barging` MCS lock is a unfair lock.
//!
//! This module provides an implementation that is **not** `no_std` compatible.
//!
//! The lock is hold for as long as its associated RAII guard is in scope. Once
//! the guard is dropped, the mutex is freed. Mutex guards are returned by
//! [`lock`] and [`try_lock`].
//!
//! This Mutex is generic over the two layers of parking policies. User may
//! choose a policy as long as it implements the [`Park`] trait. The shared
//! lock parking policy is associated with the `Ps` generic paramater. The
//! handoff parking policy is then associated with the `Pq` generic parameter.
//! Backoff parking policies are usually prefered for shared lock contention,
//! while non-backoff parking policies are usually prefered for handoffs.
//!
//! There is a number of parking policies provided by the [`park`] module. The
//! following modules provide type aliases for [`lock_api::Mutex`] and
//! [`lock_api::MutexGuard`] associated with a parking policy. See their
//! documentation for more information.
//!
//! [`park`]: crate::parking::park
//! [`Park`]: crate::parking::park::Park
//! [`parking::barging::Mutex`]: crate::parking::barging::Mutex
//!
//! [lock_api]: https://crates.io/crates/lock_api
//! [`lock_api::Mutex`]: https://docs.rs/lock_api/latest/lock_api/struct.Mutex.html
//! [`lock_api::MutexGuard`]: https://docs.rs/lock_api/latest/lock_api/struct.MutexGuard.html
//! [`lock_api::RawMutex`]: https://docs.rs/lock_api/latest/lock_api/trait.RawMutex.html
//! [`lock`]: https://docs.rs/lock_api/latest/lock_api/struct.Mutex.html#method.lock
//! [`try_lock`]: https://docs.rs/lock_api/latest/lock_api/struct.Mutex.html#method.try_lock

mod mutex;
pub use mutex::{Mutex, MutexGuard};

/// An unfair MCS lock that implements a `spin then park` parking policy.
///
/// During lock contention, this lock spins while signaling the processor that
/// it is running a busy-wait spin-loop.
pub mod spins {
    use super::mutex;
    use crate::parking::park::SpinThenPark;

    /// A [`lock_api::Mutex`] that implements the [`SpinThenPark`] parking policy.
    ///
    /// # Example
    ///
    /// ```
    /// use mcslock::parking::barging::lock_api::spins::Mutex;
    ///
    /// let mutex = Mutex::new(0);
    /// let guard = mutex.lock();
    /// assert_eq!(*guard, 0);
    /// ```
    /// [`lock_api::Mutex`]: mutex::Mutex
    pub type Mutex<T> = mutex::Mutex<T, SpinThenPark, SpinThenPark>;

    /// A [`lock_api::MutexGuard`] that implements the [`SpinThenPark`] parking
    /// policy.
    ///
    /// [`lock_api::MutexGuard`]: mutex::MutexGuard
    pub type MutexGuard<'a, T> = mutex::MutexGuard<'a, T, SpinThenPark, SpinThenPark>;

    /// An unfair MCS lock that implements a `spin with backoff then park` parking
    /// policy.
    ///
    /// During lock contention, this lock will perform exponential backoff
    /// while spinning, signaling the processor that it is running a busy-wait
    /// spin-loop.
    pub mod backoff {
        use super::mutex;
        use crate::parking::park::{SpinBackoffThenPark, SpinThenPark};

        /// A [`lock_api::Mutex`] that implements the [`SpinBackoffThenPark`]
        /// parking policy.
        ///
        /// # Example
        ///
        /// ```
        /// use mcslock::parking::barging::lock_api::spins::backoff::Mutex;
        ///
        /// let mutex = Mutex::new(0);
        /// let guard = mutex.lock();
        /// assert_eq!(*guard, 0);
        /// ```
        /// [`lock_api::Mutex`]: mutex::Mutex
        pub type Mutex<T> = mutex::Mutex<T, SpinBackoffThenPark, SpinThenPark>;

        /// A [`lock_api::MutexGuard`] that implements the [`SpinBackoffThenPark`]
        /// parking policy.
        ///
        /// [`lock_api::MutexGuard`]: mutex::MutexGuard
        pub type MutexGuard<'a, T> = mutex::MutexGuard<'a, T, SpinBackoffThenPark, SpinThenPark>;
    }
}

/// An unfair MCS lock that implements a `yield then park` parking policy.
///
/// During lock contention, this lock will yield the current time slice to the
/// OS scheduler.
#[cfg(any(feature = "yield", loom, test))]
#[cfg_attr(docsrs, doc(cfg(feature = "yield")))]
pub mod yields {
    use super::mutex;
    use crate::parking::park::YieldThenPark;

    /// A [`lock_api::Mutex`] that implements the [`YieldThenPark`] parking policy.
    ///
    /// # Example
    ///
    /// ```
    /// use mcslock::parking::barging::lock_api::yields::Mutex;
    ///
    /// let mutex = Mutex::new(0);
    /// let guard = mutex.lock();
    /// assert_eq!(*guard, 0);
    /// ```
    /// [`lock_api::Mutex`]: mutex::Mutex
    pub type Mutex<T> = mutex::Mutex<T, YieldThenPark, YieldThenPark>;

    /// A [`lock_api::MutexGuard`] that implements the [`YieldThenPark`] parking
    /// policy.
    ///
    /// [`lock_api::MutexGuard`]: mutex::MutexGuard
    pub type MutexGuard<'a, T> = mutex::MutexGuard<'a, T, YieldThenPark, YieldThenPark>;

    /// An unfair MCS lock that implements a `yield with backoff then park`
    /// parking policy.
    ///
    /// During lock contention, this lock will perform exponential backoff while
    /// spinning, up to a threshold, then yields back to the OS scheduler.
    pub mod backoff {
        use super::mutex;
        use crate::parking::park::{YieldBackoffThenPark, YieldThenPark};

        /// A [`lock_api::Mutex`] that implements the [`YieldBackoffThenPark`]
        /// parking policy.
        ///
        /// # Example
        ///
        /// ```
        /// use mcslock::parking::barging::lock_api::yields::backoff::Mutex;
        ///
        /// let mutex = Mutex::new(0);
        /// let guard = mutex.lock();
        /// assert_eq!(*guard, 0);
        /// ```
        /// [`lock_api::Mutex`]: mutex::Mutex
        pub type Mutex<T> = mutex::Mutex<T, YieldBackoffThenPark, YieldThenPark>;

        /// A [`lock_api::MutexGuard`] that implements the [`YieldBackoffThenPark`]
        /// parking policy.
        ///
        /// [`lock_api::MutexGuard`]: mutex::MutexGuard
        pub type MutexGuard<'a, T> = mutex::MutexGuard<'a, T, YieldBackoffThenPark, YieldThenPark>;
    }
}

/// An unfair MCS lock that implements a `loop then park` parking policy.
///
/// During lock contention, this lock will rapidly spin without telling the CPU
/// to do any power down.
pub mod loops {
    use super::mutex;
    use crate::parking::park::LoopThenPark;

    /// A [`lock_api::Mutex`] that implements the [`LoopThenPark`] parking policy.
    ///
    /// # Example
    ///
    /// ```
    /// use mcslock::parking::barging::lock_api::loops::Mutex;
    ///
    /// let mutex = Mutex::new(0);
    /// let guard = mutex.lock();
    /// assert_eq!(*guard, 0);
    /// ```
    /// [`lock_api::Mutex`]: mutex::Mutex
    pub type Mutex<T> = mutex::Mutex<T, LoopThenPark, LoopThenPark>;

    /// A [`lock_api::MutexGuard`] that implements the [`LoopThenPark`] parking
    /// policy.
    ///
    /// [`lock_api::MutexGuard`]: mutex::MutexGuard
    pub type MutexGuard<'a, T> = mutex::MutexGuard<'a, T, LoopThenPark, LoopThenPark>;
}

/// An unfair MCS lock that implements an `immediate park` parking policy.
///
/// During lock contention, this lock will immediately put the thread to sleep.
pub mod immediate {
    use super::mutex;
    use crate::parking::park::ImmediatePark;

    /// A [`lock_api::Mutex`] that implements the [`ImmediatePark`] parking policy.
    ///
    /// # Example
    ///
    /// ```
    /// use mcslock::parking::barging::lock_api::immediate::Mutex;
    ///
    /// let mutex = Mutex::new(0);
    /// let guard = mutex.lock();
    /// assert_eq!(*guard, 0);
    /// ```
    /// [`lock_api::Mutex`]: mutex::Mutex
    pub type Mutex<T> = mutex::Mutex<T, ImmediatePark, ImmediatePark>;

    /// A [`lock_api::MutexGuard`] that implements the [`ImmediatePark`] parking
    /// policy.
    ///
    /// [`lock_api::MutexGuard`]: mutex::MutexGuard
    pub type MutexGuard<'a, T> = mutex::MutexGuard<'a, T, ImmediatePark, ImmediatePark>;
}
