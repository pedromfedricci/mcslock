//! MCS lock implementation with thread parking support.
//!
//! The `raw` implementation of MCS lock is fair, that is, it guarantees that
//! thread that have waited for longer will be scheduled first (FIFO). Each
//! waiting thread will spin and park against its own, locally-accessible atomic
//! lock state, which then avoids the network contention of the state access.
//!
//! This module provides an implementation that **is not** `no_std` compatible,
//! and it also requires that queue nodes must be allocated by the callers.
//! Queue nodes are represented by the [`MutexNode`] type.
//!
//! The lock is held for all the duration of the locking closure scope provided
//! to [`Mutex`]'s [`try_lock_then`], [`try_lock_with_then`], [`lock_then`] and
//! [`lock_with_then`] methods.
//!
//! This Mutex is generic over the parking policy. User may choose a policy as
//! long as it implements the [`Park`] trait.
//!
//! There is a number of parking policies provided by the [`park`] module. The
//! following modules provide type aliases for [`Mutex`] associated with a parking
//! policy. See their documentation for more information.
//!
//! [`try_lock_then`]: Mutex::try_lock_then
//! [`try_lock_with_then`]: Mutex::try_lock_with_then
//! [`lock_then`]: Mutex::lock_then
//! [`lock_with_then`]: Mutex::try_lock_with_then
//! [`park`]: crate::parking::park
//! [`Park`]: crate::parking::park::Park

mod mutex;
pub use mutex::{Mutex, MutexNode};

#[cfg(feature = "thread_local")]
#[cfg_attr(docsrs, doc(cfg(feature = "thread_local")))]
mod thread_local;
#[cfg(feature = "thread_local")]
pub use thread_local::LocalMutexNode;

/// A MCS lock that implements a `spin then park` parking policy.
///
/// During lock contention, and for a certain amount of attempts, this lock spins
/// while signaling the processor that it is running a busy-wait spin-loop. Once
/// all attempts have been tried, puts the thread to sleep.
pub mod spins {
    use super::mutex;
    use crate::parking::park::SpinThenPark;

    /// A [`parking::raw::Mutex`] that implements the [`SpinThenPark`]
    /// parking policy.
    ///
    /// # Example
    ///
    /// ```
    /// use mcslock::parking::raw::{spins::Mutex, MutexNode};
    ///
    /// let mutex = Mutex::new(0);
    /// let mut node = MutexNode::new();
    /// let value = mutex.lock_with_then(&mut node, |data| *data);
    /// assert_eq!(value, 0);
    /// ```
    /// [`parking::raw::Mutex`]: mutex::Mutex
    pub type Mutex<T> = mutex::Mutex<T, SpinThenPark>;

    /// A MCS lock that implements a `spin with backoff then park`
    /// policy.
    ///
    /// During lock contention, and for a certain amount of attempts, this lock
    /// will perform exponential backoff spinning, signaling the processor that
    /// its is running a busy-wait spin-loop. Once all attempts have been tried,
    /// puts the thread to sleep.
    pub mod backoff {
        use super::mutex;
        use crate::parking::park::SpinBackoffThenPark;

        /// A [`parking::raw::Mutex`] that implements the [`SpinBackoffThenPark`]
        /// parking policy.
        ///
        /// # Example
        ///
        /// ```
        /// use mcslock::parking::raw::{spins::backoff::Mutex, MutexNode};
        ///
        /// let mutex = Mutex::new(0);
        /// let mut node = MutexNode::new();
        /// let value = mutex.lock_with_then(&mut node, |data| *data);
        /// assert_eq!(value, 0);
        /// ```
        /// [`parking::raw::Mutex`]: mutex::Mutex
        pub type Mutex<T> = mutex::Mutex<T, SpinBackoffThenPark>;
    }
}

/// A MCS lock that implements a `yield then park` parking policy.
///
/// During lock contention, and for a certain amount of attempts, this lock will
/// yield the current time slice to the OS scheduler. Once all attempts have
/// been tried, puts the thread to sleep.
pub mod yields {
    use super::mutex;
    use crate::parking::park::YieldThenPark;

    /// A [`parking::raw::Mutex`] that implements the [`YieldThenPark`] parking
    /// policy.
    ///
    /// # Example
    ///
    /// ```
    /// use mcslock::parking::raw::{yields::Mutex, MutexNode};
    ///
    /// let mutex = Mutex::new(0);
    /// let mut node = MutexNode::new();
    /// let value = mutex.lock_with_then(&mut node, |data| *data);
    /// assert_eq!(value, 0);
    /// ```
    /// [`parking::raw::Mutex`]: mutex::Mutex
    pub type Mutex<T> = mutex::Mutex<T, YieldThenPark>;

    /// A MCS lock that implements a `yield with backoff then park`
    /// parking policy.
    ///
    /// During lock contention, and for a certain amount of attempts, this lock
    /// will perform exponential backoff while spinning, up to a threshold, then
    /// yields back to the OS scheduler. Once all attempts have been tried, it
    /// will then put the thread to sleep.
    pub mod backoff {
        use super::mutex;
        use crate::parking::park::YieldBackoffThenPark;

        /// A [`parking::raw::Mutex`] that implements the [`YieldBackoffThenPark`]
        /// parking policy.
        ///
        /// # Example
        ///
        /// ```
        /// use mcslock::parking::raw::{yields::backoff::Mutex, MutexNode};
        ///
        /// let mutex = Mutex::new(0);
        /// let mut node = MutexNode::new();
        /// let value = mutex.lock_with_then(&mut node, |data| *data);
        /// assert_eq!(value, 0);
        /// ```
        /// [`parking::raw::Mutex`]: mutex::Mutex
        pub type Mutex<T> = mutex::Mutex<T, YieldBackoffThenPark>;
    }
}
/// A MCS lock that implements a `loop then park` parking policy.
///
/// During lock contention, and for a certain amount of attempts, this lock
/// will rapidly spin without telling the CPU to do any power down. Once all
/// attempts have been tried, it will then put the thread to sleep.
pub mod loops {
    use super::mutex;
    use crate::parking::park::LoopThenPark;

    /// A [`parking::raw::Mutex`] that implements the [`LoopThenPark`] parking
    /// policy.
    ///
    /// # Example
    ///
    /// ```
    /// use mcslock::parking::raw::{loops::Mutex, MutexNode};
    ///
    /// let mutex = Mutex::new(0);
    /// let mut node = MutexNode::new();
    /// let value = mutex.lock_with_then(&mut node, |data| *data);
    /// assert_eq!(value, 0);
    /// ```
    /// [`parking::raw::Mutex`]: mutex::Mutex
    pub type Mutex<T> = mutex::Mutex<T, LoopThenPark>;
}

/// A MCS lock that implements a `immediate park` parking policy.
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
    /// let value = mutex.lock_with_then(&mut node, |data| *data);
    /// assert_eq!(value, 0);
    /// ```
    /// [`parking::raw::Mutex`]: mutex::Mutex
    pub type Mutex<T> = mutex::Mutex<T, ImmediatePark>;
}
