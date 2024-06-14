//! TODO: Docs

mod mutex;
pub use mutex::{Mutex, MutexGuard, MutexNode};

#[cfg(feature = "thread_local")]
#[cfg_attr(docsrs, doc(cfg(feature = "thread_local")))]
mod thread_local;
#[cfg(feature = "thread_local")]
pub use thread_local::LocalMutexNode;

/// TODO: Docs
pub mod spins {
    use super::mutex;
    use crate::parking::park::SpinThanPark;

    /// TODO: Docs
    pub type Mutex<T> = mutex::Mutex<T, SpinThanPark>;

    /// TODO: Docs
    pub type MutexGuard<'a, T> = mutex::MutexGuard<'a, T, SpinThanPark>;

    /// TODO: Docs
    pub mod backoff {
        use super::mutex;
        use crate::parking::park::SpinBackoffThanPark;

        /// TODO: Docs
        pub type Mutex<T> = mutex::Mutex<T, SpinBackoffThanPark>;

        /// TODO: Docs
        pub type MutexGuard<'a, T> = mutex::MutexGuard<'a, T, SpinBackoffThanPark>;
    }
}

/// TODO: Docs
pub mod yields {
    use super::mutex;
    use crate::parking::park::YieldThanPark;

    /// TODO: Docs
    pub type Mutex<T> = mutex::Mutex<T, YieldThanPark>;

    /// TODO: Docs
    pub type MutexGuard<'a, T> = mutex::MutexGuard<'a, T, YieldThanPark>;

    /// TODO: Docs
    pub mod backoff {
        use super::mutex;
        use crate::parking::park::YieldBackoffThanPark;

        /// TODO: Docs
        pub type Mutex<T> = mutex::Mutex<T, YieldBackoffThanPark>;

        /// TODO: Docs
        pub type MutexGuard<'a, T> = mutex::MutexGuard<'a, T, YieldBackoffThanPark>;
    }
}

/// TODO: Docs
pub mod loops {
    use super::mutex;
    use crate::parking::park::LoopThanPark;

    /// TODO: Docs
    pub type Mutex<T> = mutex::Mutex<T, LoopThanPark>;

    /// TODO: Docs
    pub type MutexGuard<'a, T> = mutex::MutexGuard<'a, T, LoopThanPark>;
}

/// TODO: Docs
pub mod immediate {
    use super::mutex;
    use crate::parking::park::ImmediatePark;

    /// TODO: Docs
    pub type Mutex<T> = mutex::Mutex<T, ImmediatePark>;

    /// TODO: Docs
    pub type MutexGuard<'a, T> = mutex::MutexGuard<'a, T, ImmediatePark>;
}
