//! A MCS lock implementation that stores queue nodes in the thread local
//! storage of the waiting threads.
//!
//! This module provide MCS locking APIs that do not require user-side node
//! instantiation, by managing the queue's nodes allocations internally. Queue
//! nodes are stored in the thread local storage, therefore this implementation
//! requires support from the standard library. Critical sections must be
//! provided to [`lock_with`] and [`try_lock_with`] as closures. Closure arguments
//! provide a RAII guard that has exclusive over the data. The mutex guard will
//! be dropped at the end of the call, freeing the mutex.
//!
//! The Mutex is generic over the relax strategy. User may choose a strategy
//! as long as it implements the [`Relax`] trait. There is a number of strategies
//! provided by the [`relax`] module. Each module in `thread_local` provides type
//! aliases for [`Mutex`] and [`MutexGuard`] associated with one relax strategy.
//! See their documentation for more information.
//!
//! # Panics
//!
//! The `thread_local` [`Mutex`] implementation does not allow recursive locking,
//! doing so will cause a panic. See [`lock_with`] and [`try_lock_with`] functions
//! for more information.
//!
//! [`lock_with`]: Mutex::lock_with
//! [`try_lock_with`]: Mutex::try_lock_with
//! [`relax`]: crate::relax
//! [`Relax`]: crate::relax::Relax

mod mutex;
pub use mutex::{Mutex, MutexGuard};

/// A `thread_local` MCS lock alias that signals the processor that it is running
/// a busy-wait spin-loop during lock contention.
pub mod spins {
    use crate::relax::Spin;

    /// A `thread_local` MCS lock that implements the [`Spin`] relax strategy.
    ///
    /// # Example
    ///
    /// ```
    /// use mcslock::thread_local::spins::Mutex;
    ///
    /// let mutex = Mutex::new(0);
    /// let data = mutex.lock_with(|guard| *guard);
    /// assert_eq!(data, 0);
    /// ```
    pub type Mutex<T> = super::Mutex<T, Spin>;

    /// A `thread_local` MCS guard that implements the [`Spin`] relax strategy.
    pub type MutexGuard<'a, T> = super::MutexGuard<'a, T, Spin>;
}

/// A `thread_local` MCS lock alias that yields the current time slice to the
/// OS scheduler during lock contention.
#[cfg(any(feature = "yield", loom, test))]
#[cfg_attr(docsrs, doc(cfg(feature = "yield")))]
pub mod yields {
    use crate::relax::Yield;

    /// A `thread_local` MCS lock that implements the [`Yield`] relax strategy.
    ///
    /// # Example
    ///
    /// ```
    /// use mcslock::thread_local::yields::Mutex;
    ///
    /// let mutex = Mutex::new(0);
    /// let data = mutex.lock_with(|guard| *guard);
    /// assert_eq!(data, 0);
    /// ```
    pub type Mutex<T> = super::Mutex<T, Yield>;

    /// A `thread_local` MCS guard that implements the [`Yield`] relax strategy.
    pub type MutexGuard<'a, T> = super::MutexGuard<'a, T, Yield>;
}

/// A `thread_local` MCS lock alias that rapidly spins without telling the CPU
/// to do any power down during lock contention.
pub mod loops {
    use crate::relax::Loop;

    /// A `thread_local` MCS lock that implements the [`Loop`] relax strategy.
    ///
    /// # Example
    ///
    /// ```
    /// use mcslock::thread_local::loops::Mutex;
    ///
    /// let mutex = Mutex::new(0);
    /// let data = mutex.lock_with(|guard| *guard);
    /// assert_eq!(data, 0);
    /// ```
    pub type Mutex<T> = super::Mutex<T, Loop>;

    /// A `thread_local` MCS guard that implements the [`Loop`] relax strategy.
    pub type MutexGuard<'a, T> = super::MutexGuard<'a, T, Loop>;
}

/// A `thread_local` MCS lock alias that, during lock contention, will perform
/// exponential backoff while signaling the processor that it is running a
/// busy-wait spin-loop.
pub mod spins_backoff {
    use crate::relax::SpinBackoff;

    /// A `thread_local` MCS lock that implements the [`SpinBackoff`] relax
    /// strategy.
    ///
    /// # Example
    ///
    /// ```
    /// use mcslock::thread_local::spins_backoff::Mutex;
    ///
    /// let mutex = Mutex::new(0);
    /// let data = mutex.lock_with(|guard| *guard);
    /// assert_eq!(data, 0);
    /// ```
    pub type Mutex<T> = super::Mutex<T, SpinBackoff>;

    /// A `thread_local` MCS guard that implements the [`SpinBackoff`] relax
    /// strategy.
    pub type MutexGuard<'a, T> = super::MutexGuard<'a, T, SpinBackoff>;
}

/// A `thread_local` MCS lock alias that, during lock contention, will perform
/// exponential backoff while spinning up to a threshold, then yields back to
/// the OS scheduler.
#[cfg(feature = "yield")]
#[cfg_attr(docsrs, doc(cfg(feature = "yield")))]
pub mod yields_backoff {
    use crate::relax::YieldBackoff;

    /// A `thread_local` MCS lock that implements the [`YieldBackoff`] relax
    /// strategy.
    ///
    /// # Example
    ///
    /// ```
    /// use mcslock::thread_local::yields_backoff::Mutex;
    ///
    /// let mutex = Mutex::new(0);
    /// let data = mutex.lock_with(|guard| *guard);
    /// assert_eq!(data, 0);
    /// ```
    pub type Mutex<T> = super::Mutex<T, YieldBackoff>;

    /// A `thread_local` MCS guard that implements the [`YieldBackoff`] relax
    /// strategy.
    pub type MutexGuard<'a, T> = super::MutexGuard<'a, T, YieldBackoff>;
}
