//! Unfair MCS lock implementation with thread parking support.
//!
//! This implementation will have non-waiting threads race for the lock against
//! the front of the waiting queue thread. If the front of the queue thread
//! looses the race, it will simply go back to sleep, while holding its position
//! in the queue. By allowing barging instead of forcing FIFO, a higher
//! throughput can be achieved when the lock is heavily contended.
//!
//! This module provides an implementation that ** is not** `no_std` compatible,
//! it does not require queue nodes to be allocated by the callers, and so it
//! is compatible with the [lock_api] crate (see `lock_api` feature).
//!
//! The lock is hold for as long as its associated RAII guard is in scope. Once
//! the guard is dropped, the mutex is freed. Mutex guards are returned by
//! [`lock`] and [`try_lock`]. Guards are also accessible as the closure argument
//! for [`lock_then`] and [`try_lock_then`] methods.
//!
//! This Mutex is generic over the two layers of parking policies. User may
//! choose a policy as long as it implements the [`Park`] trait. The shared
//! lock parking policy is associated with the `Ps` generic paramater. The
//! handoff parking policy is then associated with the `Pq` generic parameter.
//! Backoff parking policies are usually prefered for shared lock contention,
//! while non-backoff parking policies are usually prefered for handoffs.
//!
//! There is a number of policies provided by the [`park`] module. The
//! following modules provide type aliases for [`Mutex`] and [`MutexGuard`]
//! associated a parking policy. See their documentation for more information.
//!
//! [`lock`]: Mutex::lock
//! [`try_lock`]: Mutex::try_lock
//! [`lock_then`]: Mutex::lock_then
//! [`try_lock_then`]: Mutex::try_lock_then
//! [`park`]: crate::parking::park
//! [`Park`]: crate::parking::park::Park
//!
//! [lock_api]: https://crates.io/crates/lock_api

mod mutex;
pub use mutex::{Mutex, MutexGuard};

#[cfg(all(feature = "lock_api", not(loom)))]
#[cfg_attr(docsrs, doc(cfg(feature = "lock_api")))]
pub mod lock_api;

#[cfg(feature = "thread_local")]
mod thread_local;

/// A unfair MCS lock that implements a `spin then park` parking policy.
///
/// During lock contention, and for a certain amount of attempts, this lock spins
/// while signaling the processor that it is running a busy-wait spin-loop. Once
/// all attempts have been tried, puts the thread to sleep.
pub mod spins {
    use super::mutex;
    use crate::parking::park::SpinThenPark;

    /// A [`parking::barging::Mutex`] that implements the [`SpinThenPark`]
    /// parking policy.
    ///
    /// # Example
    ///
    /// ```
    /// use mcslock::parking::barging::spins::Mutex;
    ///
    /// let mutex = Mutex::new(0);
    /// let guard = mutex.lock();
    /// assert_eq!(*guard, 0);
    /// ```
    /// [`parking::barging::Mutex`]: mutex::Mutex
    pub type Mutex<T> = mutex::Mutex<T, SpinThenPark, SpinThenPark>;

    /// A [`parking::barging::MutexGuard`] that implements the [`SpinThenPark`]
    /// parking policy.
    ///
    /// [`parking::barging::MutexGuard`]: mutex::MutexGuard
    pub type MutexGuard<'a, T> = mutex::MutexGuard<'a, T, SpinThenPark, SpinThenPark>;

    /// A unfair MCS lock that implements a `spin with backoff then park`
    /// parking policy.
    ///
    /// During lock contention, and for a certain amount of attempts, this lock
    /// will perform exponential backoff spinning, signaling the processor that
    /// its is running a busy-wait spin-loop. Once all attempts have been tried,
    /// puts the thread to sleep.
    pub mod backoff {
        use super::mutex;
        use crate::parking::park::{SpinBackoffThenPark, SpinThenPark};

        /// A [`parking::barging::Mutex`] that implements the
        /// [`SpinBackoffThenPark`] parking policy.
        ///
        /// # Example
        ///
        /// ```
        /// use mcslock::parking::barging::spins::backoff::Mutex;
        ///
        /// let mutex = Mutex::new(0);
        /// let guard = mutex.lock();
        /// assert_eq!(*guard, 0);
        /// ```
        /// [`parking::barging::Mutex`]: mutex::Mutex
        pub type Mutex<T> = mutex::Mutex<T, SpinBackoffThenPark, SpinThenPark>;

        /// A [`parking::barging::MutexGuard`] that implements the
        /// [`SpinBackoffThenPark`] parking policy.
        ///
        /// [`parking::barging::MutexGuard`]: mutex::MutexGuard
        pub type MutexGuard<'a, T> = mutex::MutexGuard<'a, T, SpinBackoffThenPark, SpinThenPark>;
    }
}

/// A unfair MCS lock that implements a `yield then park` parking policy.
///
/// During lock contention, and for a certain amount of attempts, this lock will
/// yield the current time slice to the OS scheduler. Once all attempts have
/// been tried, puts the thread to sleep.
#[cfg(any(feature = "yield", loom, test))]
#[cfg_attr(docsrs, doc(cfg(feature = "yield")))]
pub mod yields {
    use super::mutex;
    use crate::parking::park::YieldThenPark;

    /// A [`parking::barging::Mutex`] that implements the [`YieldThenPark`]
    /// parking policy.
    ///
    /// # Example
    ///
    /// ```
    /// use mcslock::parking::barging::yields::Mutex;
    ///
    /// let mutex = Mutex::new(0);
    /// let guard = mutex.lock();
    /// assert_eq!(*guard, 0);
    /// ```
    /// [`parking::barging::Mutex`]: mutex::Mutex
    pub type Mutex<T> = mutex::Mutex<T, YieldThenPark, YieldThenPark>;

    /// A [`parking::barging::MutexGuard`] that implements the [`YieldThenPark`]
    /// parking policy.
    ///
    /// [`parking::barging::MutexGuard`]: mutex::MutexGuard
    pub type MutexGuard<'a, T> = mutex::MutexGuard<'a, T, YieldThenPark, YieldThenPark>;

    /// A unfair MCS lock that implements a `yield with backoff then park`
    /// parking policy.
    ///
    /// During lock contention, and for a certain amount of attempts, this lock
    /// will perform exponential backoff while spinning, up to a threshold, then
    /// yields back to the OS scheduler. Once all attempts have been tried, it
    /// will then put the thread to sleep.
    pub mod backoff {
        use super::mutex;
        use crate::parking::park::{YieldBackoffThenPark, YieldThenPark};

        /// A [`parking::barging::Mutex`] that implements the
        /// [`YieldBackoffThenPark`] parking policy.
        ///
        /// # Example
        ///
        /// ```
        /// use mcslock::parking::barging::yields::backoff::Mutex;
        ///
        /// let mutex = Mutex::new(0);
        /// let guard = mutex.lock();
        /// assert_eq!(*guard, 0);
        /// ```
        /// [`parking::barging::Mutex`]: mutex::Mutex
        pub type Mutex<T> = mutex::Mutex<T, YieldBackoffThenPark, YieldThenPark>;

        /// A [`parking::barging::MutexGuard`] that implements the
        /// [`YieldBackoffThenPark`] parking policy.
        ///
        /// [`parking::barging::MutexGuard`]: mutex::MutexGuard
        pub type MutexGuard<'a, T> = mutex::MutexGuard<'a, T, YieldBackoffThenPark, YieldThenPark>;
    }
}

/// A unfair MCS lock that implements a `loop then park` parking policy.
///
/// During lock contention, and for a certain amount of attempts, this lock
/// will rapidly spin without telling the CPU to do any power down. Once all
/// attempts have been tried, it will then put the thread to sleep.
pub mod loops {
    use super::mutex;
    use crate::parking::park::LoopThenPark;

    /// A [`parking::barging::Mutex`] that implements the [`LoopThenPark`]
    /// parking policy.
    ///
    /// # Example
    ///
    /// ```
    /// use mcslock::parking::barging::loops::Mutex;
    ///
    /// let mutex = Mutex::new(0);
    /// let guard = mutex.lock();
    /// assert_eq!(*guard, 0);
    /// ```
    /// [`parking::barging::Mutex`]: mutex::Mutex
    pub type Mutex<T> = mutex::Mutex<T, LoopThenPark, LoopThenPark>;

    /// A [`parking::barging::MutexGuard`] that implements the [`LoopThenPark`]
    /// parking policy.
    ///
    /// [`parking::barging::MutexGuard`]: mutex::MutexGuard
    pub type MutexGuard<'a, T> = mutex::MutexGuard<'a, T, LoopThenPark, LoopThenPark>;
}

/// A unfair MCS lock that implements an `immediate park` parking policy.
///
/// During lock contention, this lock will immediately put the thread to sleep.
pub mod immediate {
    use super::mutex;
    use crate::parking::park::ImmediatePark;

    /// A [`parking::barging::Mutex`] that implements the [`ImmediatePark`]
    /// parking policy.
    ///
    /// # Example
    ///
    /// ```
    /// use mcslock::parking::barging::immediate::Mutex;
    ///
    /// let mutex = Mutex::new(0);
    /// let guard = mutex.lock();
    /// assert_eq!(*guard, 0);
    /// ```
    /// [`parking::barging::Mutex`]: mutex::Mutex
    pub type Mutex<T> = mutex::Mutex<T, ImmediatePark, ImmediatePark>;

    /// A [`parking::barging::MutexGuard`] that implements the [`ImmediatePark`]
    /// parking policy.
    ///
    /// [`parking::barging::MutexGuard`]: mutex::MutexGuard
    pub type MutexGuard<'a, T> = mutex::MutexGuard<'a, T, ImmediatePark, ImmediatePark>;
}
