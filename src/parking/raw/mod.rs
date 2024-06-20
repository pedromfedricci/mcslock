//! A `parking` MCS lock implementation that requires exclusive access to
//! a locally accessible queue node.
//!
//! The `raw` implementation of MCS lock is fair, that is, it guarantees that
//! thread that have waited for longer will be scheduled first (FIFO). Each
//! waiting thread will spin against its own, locally-accessible atomic lock
//! state, which then avoids the network contention of the state access.
//!
//! This module provides an implementation that is **not** `no_std` compatible,
//! and it also requires that queue nodes must be allocated by the callers.
//! Queue nodes are represented by the [`MutexNode`] type.
//!
//! The lock is hold for as long as its associated RAII guard is in scope. Once
//! the guard is dropped, the mutex is freed. Mutex guards are returned by
//! [`lock`] and [`try_lock`]. Guards are also accessible as the closure argument
//! for [`lock_with`] and [`try_lock_with`] methods.

//! The Mutex is generic over the parking policy. User may choose a policy
//! as long as it implements the [`Park`] trait. There is a number of policies
//! provided by the [`park`] module. Each module in `parking::raw` provides type
//! aliases for [`Mutex`] and [`MutexGuard`] associated with one parking policy.
//! See their documentation for more information.
//!
//! [`lock`]: Mutex::lock
//! [`try_lock`]: Mutex::try_lock
//! [`lock_with`]: Mutex::lock_with
//! [`try_lock_with`]: Mutex::try_lock_with
//! [`park`]: crate::parking::park
//! [`Park`]: crate::parking::park::Park

mod mutex;
pub use mutex::{Mutex, MutexGuard, MutexNode};

#[cfg(feature = "thread_local")]
#[cfg_attr(docsrs, doc(cfg(feature = "thread_local")))]
mod thread_local;
#[cfg(feature = "thread_local")]
pub use thread_local::LocalMutexNode;

/// A `parking` MCS lock that implements a `spin than park` parking policy.
///
/// During lock contention, and for a certain amount of attempts, this lock spins
/// while signaling the processor that it is running a busy-wait spin-loop. Once
/// all attempts have been tried, puts the thread to sleep.
pub mod spins {
    use super::mutex;
    use crate::parking::park::SpinThanPark;

    /// A [`parking::raw::Mutex`] alias that implements the [`SpinThanPark`]
    /// parking policy.
    ///
    /// # Example
    ///
    /// ```
    /// use mcslock::parking::raw::{spins::Mutex, MutexNode};
    ///
    /// let mutex = Mutex::new(0);
    /// let mut node = MutexNode::new();
    /// let guard = mutex.lock(&mut node);
    /// assert_eq!(*guard, 0);
    /// ```
    /// [`parking::raw::Mutex`]: mutex::Mutex
    pub type Mutex<T> = mutex::Mutex<T, SpinThanPark>;

    /// A [`parking::raw::MutexGuard`] that implements the [`SpinThanPark`]
    /// parking policy.
    ///
    /// [`parking::raw::MutexGuard`]: mutex::MutexGuard
    pub type MutexGuard<'a, T> = mutex::MutexGuard<'a, T, SpinThanPark>;

    /// A `parking` MCS lock that implements a `spin with backoff than park`
    /// policy.
    ///
    /// During lock contention, and for a certain amount of attempts, this lock
    /// will perform exponential backoff spinning, signaling the processor that
    /// its is running a busy-wait spin-loop. Once all attempts have been tried,
    /// puts the thread to sleep.
    pub mod backoff {
        use super::mutex;
        use crate::parking::park::SpinBackoffThanPark;

        /// A [`parking::raw::Mutex`] that implements the [`SpinBackoffThanPark`]
        /// parking policy.
        ///
        /// # Example
        ///
        /// ```
        /// use mcslock::parking::raw::{spins::backoff::Mutex, MutexNode};
        ///
        /// let mutex = Mutex::new(0);
        /// let mut node = MutexNode::new();
        /// let guard = mutex.lock(&mut node);
        /// assert_eq!(*guard, 0);
        /// ```
        /// [`parking::raw::Mutex`]: mutex::Mutex
        pub type Mutex<T> = mutex::Mutex<T, SpinBackoffThanPark>;

        /// A [`parking::raw::MutexGuard`] that implements the [`SpinBackoffThanPark`]
        /// parking policy.
        ///
        /// [`parking::raw::MutexGuard`]: mutex::MutexGuard
        pub type MutexGuard<'a, T> = mutex::MutexGuard<'a, T, SpinBackoffThanPark>;
    }
}

/// A `parking` MCS lock that implements a `yield than park` parking policy.
///
/// During lock contention, and for a certain amount of attempts, this lock will
/// yield the current time slice to the OS scheduler. Once all attempts have
/// been tried, puts the thread to sleep.
pub mod yields {
    use super::mutex;
    use crate::parking::park::YieldThanPark;

    /// A [`parking::raw::Mutex`] that implements the [`YieldThanPark`] parking
    /// policy.
    ///
    /// # Example
    ///
    /// ```
    /// use mcslock::parking::raw::{yields::Mutex, MutexNode};
    ///
    /// let mutex = Mutex::new(0);
    /// let mut node = MutexNode::new();
    /// let guard = mutex.lock(&mut node);
    /// assert_eq!(*guard, 0);
    /// ```
    /// [`parking::raw::Mutex`]: mutex::Mutex
    pub type Mutex<T> = mutex::Mutex<T, YieldThanPark>;

    /// A [`parking::raw::MutexGuard`] that implements the [`YieldThanPark`]
    /// parking policy.
    ///
    /// [`parking::raw::MutexGuard`]: mutex::MutexGuard
    pub type MutexGuard<'a, T> = mutex::MutexGuard<'a, T, YieldThanPark>;

    /// A `parking` MCS lock that implements a `yield with backoff than park`
    /// parking policy.
    ///
    /// During lock contention, and for a certain amount of attempts, this lock
    /// will perform exponential backoff while spinning, up to a threshold, then
    /// yields back to the OS scheduler. Once all attempts have been tried, it
    /// will then put the thread to sleep.
    pub mod backoff {
        use super::mutex;
        use crate::parking::park::YieldBackoffThanPark;

        /// A [`parking::raw::Mutex`] that implements the [`YieldBackoffThanPark`]
        /// parking policy.
        ///
        /// # Example
        ///
        /// ```
        /// use mcslock::parking::raw::{yields::backoff::Mutex, MutexNode};
        ///
        /// let mutex = Mutex::new(0);
        /// let mut node = MutexNode::new();
        /// let guard = mutex.lock(&mut node);
        /// assert_eq!(*guard, 0);
        /// ```
        /// [`parking::raw::Mutex`]: mutex::Mutex
        pub type Mutex<T> = mutex::Mutex<T, YieldBackoffThanPark>;

        /// A [`parking::raw::MutexGuard`] that implements the [`YieldBackoffThanPark`]
        /// parking policy.
        ///
        /// [`parking::raw::MutexGuard`]: mutex::MutexGuard
        pub type MutexGuard<'a, T> = mutex::MutexGuard<'a, T, YieldBackoffThanPark>;
    }
}
/// A `parking` MCS lock that implements a `loop than park` parking policy.
///
/// During lock contention, and for a certain amount of attempts, this lock
/// will rapidly spin without telling the CPU to do any power down. Once all
/// attempts have been tried, it will then put the thread to sleep.
pub mod loops {
    use super::mutex;
    use crate::parking::park::LoopThanPark;

    /// A [`parking::raw::Mutex`] that implements the [`LoopThanPark`] parking
    /// policy.
    ///
    /// # Example
    ///
    /// ```
    /// use mcslock::parking::raw::{loops::Mutex, MutexNode};
    ///
    /// let mutex = Mutex::new(0);
    /// let mut node = MutexNode::new();
    /// let guard = mutex.lock(&mut node);
    /// assert_eq!(*guard, 0);
    /// ```
    /// [`parking::raw::Mutex`]: mutex::Mutex
    pub type Mutex<T> = mutex::Mutex<T, LoopThanPark>;

    /// A [`parking::raw::MutexGuard`] that implements the [`LoopThanPark`] parking
    /// policy.
    ///
    /// [`parking::raw::MutexGuard`]: mutex::MutexGuard
    pub type MutexGuard<'a, T> = mutex::MutexGuard<'a, T, LoopThanPark>;
}

/// A `parking` MCS lock that implements a `immediate park` parking policy.
///
/// During lock contention, this lock will immediately put the thread to sleep.
pub mod immediate {
    use super::mutex;
    use crate::parking::park::ImmediatePark;

    /// A [`parking::raw::Mutex`] that implements the [`ImmediatePark`] parking
    /// policy.
    ///
    /// # Example
    ///
    /// ```
    /// use mcslock::parking::raw::{immediate::Mutex, MutexNode};
    ///
    /// let mutex = Mutex::new(0);
    /// let mut node = MutexNode::new();
    /// let guard = mutex.lock(&mut node);
    /// assert_eq!(*guard, 0);
    /// ```
    /// [`parking::raw::Mutex`]: mutex::Mutex
    pub type Mutex<T> = mutex::Mutex<T, ImmediatePark>;

    /// A [`parking::raw::MutexGuard`] that implements the [`ImmediatePark`]
    /// parking policy.
    ///
    /// [`parking::raw::MutexGuard`]: mutex::MutexGuard
    pub type MutexGuard<'a, T> = mutex::MutexGuard<'a, T, ImmediatePark>;
}
