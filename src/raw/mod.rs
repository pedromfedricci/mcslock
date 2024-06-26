//! A MCS lock implementation that requires exclusive access to a locally
//! accessible queue node.
//!
//! The `raw` implementation of MCS lock is fair, that is, it guarantees that
//! thread that have waited for longer will be scheduled first (FIFO). Each
//! waiting thread will spin against its own, locally-accessible atomic lock
//! state, which then avoids the network contention of the state access.
//!
//! This module provides an implementation that is `no_std` compatible, but
//! also requires that queue nodes must be allocated by the callers. Queue
//! nodes are represented by the [`MutexNode`] type.
//!
//! The lock is hold for as long as its associated RAII guard is in scope. Once
//! the guard is dropped, the mutex is freed. Mutex guards are returned by
//! [`lock`] and [`try_lock`]. Guards are also accessible as the closure argument
//! for [`lock_with`] and [`try_lock_with`] methods.
//!
//! The Mutex is generic over the relax strategy. User may choose a strategy
//! as long as it implements the [`Relax`] trait. There is a number of strategies
//! provided by the [`relax`] module. Each module in `raw` provides type aliases
//! for [`Mutex`] and [`MutexGuard`] associated with one relax strategy. See
//! their documentation for more information.
//!
//! [`lock`]: Mutex::lock
//! [`try_lock`]: Mutex::try_lock
//! [`lock_with`]: Mutex::lock_with
//! [`try_lock_with`]: Mutex::try_lock_with
//! [`relax`]: crate::relax
//! [`Relax`]: crate::relax::Relax

mod mutex;
pub use mutex::{Mutex, MutexGuard, MutexNode};

#[cfg(feature = "thread_local")]
pub use crate::thread_local::LocalMutexNode;

/// A `raw` MCS lock alias that signals the processor that it is running a
/// busy-wait spin-loop during lock contention.
pub mod spins {
    use super::mutex;
    use crate::relax::Spin;

    /// A `raw` MCS lock that implements the [`Spin`] relax strategy.
    ///
    /// # Example
    ///
    /// ```
    /// use mcslock::raw::{spins::Mutex, MutexNode};
    ///
    /// let mutex = Mutex::new(0);
    /// let mut node = MutexNode::new();
    /// let guard = mutex.lock(&mut node);
    /// assert_eq!(*guard, 0);
    /// ```
    pub type Mutex<T> = mutex::Mutex<T, Spin>;

    /// A `raw` MCS guard that implements the [`Spin`] relax strategy.
    pub type MutexGuard<'a, T> = mutex::MutexGuard<'a, T, Spin>;

    /// A `raw` MCS lock alias that, during lock contention, will perform
    /// exponential backoff while signaling the processor that it is running a
    /// busy-wait spin-loop.
    pub mod backoff {
        use super::mutex;
        use crate::relax::SpinBackoff;

        /// A `raw` MCS lock that implements the [`SpinBackoff`] relax strategy.
        ///
        /// # Example
        ///
        /// ```
        /// use mcslock::raw::{spins::backoff::Mutex, MutexNode};
        ///
        /// let mutex = Mutex::new(0);
        /// let mut node = MutexNode::new();
        /// let guard = mutex.lock(&mut node);
        /// assert_eq!(*guard, 0);
        /// ```
        pub type Mutex<T> = mutex::Mutex<T, SpinBackoff>;

        /// A `raw` MCS guard that implements the [`SpinBackoff`] relax strategy.
        pub type MutexGuard<'a, T> = mutex::MutexGuard<'a, T, SpinBackoff>;
    }
}

/// A `raw` MCS lock alias that yields the current time slice to the OS scheduler
/// during lock contention.
#[cfg(any(feature = "yield", loom, test))]
#[cfg_attr(docsrs, doc(cfg(feature = "yield")))]
pub mod yields {
    use super::mutex;
    use crate::relax::Yield;

    /// A `raw` MCS lock that implements the [`Yield`] relax strategy.
    ///
    /// # Example
    ///
    /// ```
    /// use mcslock::raw::{yields::Mutex, MutexNode};
    ///
    /// let mutex = Mutex::new(0);
    /// let mut node = MutexNode::new();
    /// let guard = mutex.lock(&mut node);
    /// assert_eq!(*guard, 0);
    /// ```
    pub type Mutex<T> = mutex::Mutex<T, Yield>;

    /// A `raw` MCS guard that implements the [`Yield`] relax strategy.
    pub type MutexGuard<'a, T> = mutex::MutexGuard<'a, T, Yield>;

    /// A `raw` MCS lock alias that, during lock contention, will perform
    /// exponential backoff while spinning up to a threshold, then yields
    /// back to the OS scheduler.
    #[cfg(feature = "yield")]
    pub mod backoff {
        use super::mutex;
        use crate::relax::YieldBackoff;

        /// A `raw` MCS lock that implements the [`YieldBackoff`] relax strategy.
        ///
        /// # Example
        ///
        /// ```
        /// use mcslock::raw::{yields::backoff::Mutex, MutexNode};
        ///
        /// let mutex = Mutex::new(0);
        /// let mut node = MutexNode::new();
        /// let guard = mutex.lock(&mut node);
        /// assert_eq!(*guard, 0);
        /// ```
        pub type Mutex<T> = mutex::Mutex<T, YieldBackoff>;

        /// A `raw` MCS guard that implements the [`YieldBackoff`] relax strategy.
        pub type MutexGuard<'a, T> = mutex::MutexGuard<'a, T, YieldBackoff>;
    }
}

/// A `raw` MCS lock alias that rapidly spins without telling the CPU to do any
/// power down during lock contention.
pub mod loops {
    use super::mutex;
    use crate::relax::Loop;

    /// A `raw` MCS lock that implements the [`Loop`] relax strategy.
    ///
    /// # Example
    ///
    /// ```
    /// use mcslock::raw::{loops::Mutex, MutexNode};
    ///
    /// let mutex = Mutex::new(0);
    /// let mut node = MutexNode::new();
    /// let guard = mutex.lock(&mut node);
    /// assert_eq!(*guard, 0);
    /// ```
    pub type Mutex<T> = mutex::Mutex<T, Loop>;

    /// A `raw` MCS guard that implements the [`Loop`] relax strategy.
    pub type MutexGuard<'a, T> = mutex::MutexGuard<'a, T, Loop>;
}
