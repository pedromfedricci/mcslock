//! MCS lock implementation.
//!
//! The `raw` implementation of MCS lock is fair, that is, it guarantees that
//! thread that have waited for longer will be scheduled first (FIFO). Each
//! waiting thread will spin against its own, locally-accessible atomic lock
//! state, which then avoids the network contention of the state access.
//!
//! This module provides an implementation that is `no_std` compatible, and
//! it also requires that queue nodes must be allocated by the callers. Queue
//! nodes are represented by the [`MutexNode`] type.
//!
//! The lock is held for all the duration of the locking closure scope provided
//! to [`Mutex`]'s [`try_lock_then`], [`try_lock_with_then`], [`lock_then`] and
//! [`lock_with_then`] methods.
//!
//! This Mutex is generic over the relax policy. User may choose a policy as long
//! as it implements the [`Relax`] trait.
//!
//! There is a number of relax policies provided by the [`relax`] module. The
//! following modules provide type aliases for [`Mutex`] associated with a relax
//! policy. See their documentation for more information.
//!
//! [`try_lock_then`]: Mutex::try_lock_then
//! [`try_lock_with_then`]: Mutex::try_lock_with_then
//! [`lock_then`]: Mutex::lock_then
//! [`lock_with_then`]: Mutex::lock_with_then
//! [`relax`]: crate::relax
//! [`Relax`]: crate::relax::Relax

mod mutex;
pub use mutex::{Mutex, MutexNode};

#[cfg(feature = "thread_local")]
#[cfg_attr(docsrs, doc(cfg(feature = "thread_local")))]
mod thread_local;

#[cfg(feature = "thread_local")]
pub use thread_local::LocalMutexNode;

/// A MCS lock that implements a `spin` relax policy.
///
/// During lock contention, this lock spins while signaling the processor that
/// it is running a busy-wait spin-loop.
pub mod spins {
    use super::mutex;
    use crate::relax::Spin;

    /// A [`raw::Mutex`] that implements the [`Spin`] relax policy.
    ///
    /// # Example
    ///
    /// ```
    /// use mcslock::raw::{spins::Mutex, MutexNode};
    ///
    /// let mutex = Mutex::new(0);
    /// let mut node = MutexNode::new();
    /// let value = mutex.lock_with_then(&mut node, |data| *data);
    /// assert_eq!(value, 0);
    /// ```
    /// [`raw::Mutex`]: mutex::Mutex
    pub type Mutex<T> = mutex::Mutex<T, Spin>;

    /// A MCS lock that implements a `spin with backoff` relax policy.
    ///
    /// During lock contention, this lock will perform exponential backoff
    /// while spinning, signaling the processor that it is running a busy-wait
    /// spin-loop.
    pub mod backoff {
        use super::mutex;
        use crate::relax::SpinBackoff;

        /// A [`raw::Mutex`] that implements the [`SpinBackoff`] relax policy.
        ///
        /// # Example
        ///
        /// ```
        /// use mcslock::raw::{spins::backoff::Mutex, MutexNode};
        ///
        /// let mutex = Mutex::new(0);
        /// let mut node = MutexNode::new();
        /// let value = mutex.lock_with_then(&mut node, |data| *data);
        /// assert_eq!(value, 0);
        /// ```
        /// [`raw::Mutex`]: mutex::Mutex
        pub type Mutex<T> = mutex::Mutex<T, SpinBackoff>;
    }
}

/// A MCS lock that implements a `yield` relax policy.
///
/// During lock contention, this lock will yield the current time slice to the
/// OS scheduler.
#[cfg(any(feature = "yield", loom, test))]
#[cfg_attr(docsrs, doc(cfg(feature = "yield")))]
pub mod yields {
    use super::mutex;
    use crate::relax::Yield;

    /// A [`raw::Mutex`] that implements the [`Yield`] relax policy.
    ///
    /// # Example
    ///
    /// ```
    /// use mcslock::raw::{yields::Mutex, MutexNode};
    ///
    /// let mutex = Mutex::new(0);
    /// let mut node = MutexNode::new();
    /// let value = mutex.lock_with_then(&mut node, |data| *data);
    /// assert_eq!(value, 0);
    /// ```
    /// [`raw::Mutex`]: mutex::Mutex
    pub type Mutex<T> = mutex::Mutex<T, Yield>;

    /// A MCS lock that implements a `yield with backoff` relax policy.
    ///
    /// During lock contention, this lock will perform exponential backoff while
    /// spinning, up to a threshold, then yields back to the OS scheduler.
    pub mod backoff {
        use super::mutex;
        use crate::relax::YieldBackoff;

        /// A [`raw::Mutex`] that implements the [`YieldBackoff`] relax policy.
        ///
        /// # Example
        ///
        /// ```
        /// use mcslock::raw::{yields::backoff::Mutex, MutexNode};
        ///
        /// let mutex = Mutex::new(0);
        /// let mut node = MutexNode::new();
        /// let value = mutex.lock_with_then(&mut node, |data| *data);
        /// assert_eq!(value, 0);
        /// ```
        /// [`raw::Mutex`]: mutex::Mutex
        pub type Mutex<T> = mutex::Mutex<T, YieldBackoff>;
    }
}

/// A MCS lock that implements a `loop` relax policy.
///
/// During lock contention, this lock will rapidly spin without telling the CPU
/// to do any power down.
pub mod loops {
    use super::mutex;
    use crate::relax::Loop;

    /// A [`raw::Mutex`] that implements the [`Loop`] relax policy.
    ///
    /// # Example
    ///
    /// ```
    /// use mcslock::raw::{loops::Mutex, MutexNode};
    ///
    /// let mutex = Mutex::new(0);
    /// let mut node = MutexNode::new();
    /// let value = mutex.lock_with_then(&mut node, |data| *data);
    /// assert_eq!(value, 0);
    /// ```
    /// [`raw::Mutex`]: mutex::Mutex
    pub type Mutex<T> = mutex::Mutex<T, Loop>;
}
