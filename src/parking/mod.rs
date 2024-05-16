//! TODO: Docs

mod parker;

mod mutex;
pub use mutex::{Mutex, MutexGuard, MutexNode};

/// TODO: Docs
pub mod spins {
    use super::mutex;
    use crate::relax::Spin;

    /// TODO: Docs
    pub type Mutex<T> = mutex::Mutex<T, Spin>;

    /// TODO: Docs
    pub type MutexGuard<'a, T> = mutex::MutexGuard<'a, T, Spin>;

    /// TODO: Docs
    pub mod backoff {
        use super::mutex;
        use crate::relax::SpinBackoff;

        /// TODO: Docs
        pub type Mutex<T> = mutex::Mutex<T, SpinBackoff>;

        /// TODO: Docs
        pub type MutexGuard<'a, T> = mutex::MutexGuard<'a, T, SpinBackoff>;
    }
}

/// TODO: Docs
#[cfg(any(feature = "yield", loom, test))]
#[cfg_attr(docsrs, doc(cfg(feature = "yield")))]
pub mod yields {
    use super::mutex;
    use crate::relax::Yield;

    /// TODO: Docs
    pub type Mutex<T> = mutex::Mutex<T, Yield>;

    /// TODO: Docs
    pub type MutexGuard<'a, T> = mutex::MutexGuard<'a, T, Yield>;

    /// TODO: Docs
    #[cfg(feature = "yield")]
    pub mod backoff {
        use super::mutex;
        use crate::relax::YieldBackoff;

        /// TODO: Docs
        pub type Mutex<T> = mutex::Mutex<T, YieldBackoff>;

        /// TODO: Docs
        pub type MutexGuard<'a, T> = mutex::MutexGuard<'a, T, YieldBackoff>;
    }
}

/// TODO: Docs
pub mod loops {
    use super::mutex;
    use crate::relax::Loop;

    /// TODO: Docs
    pub type Mutex<T> = mutex::Mutex<T, Loop>;

    /// TODO: Docs
    pub type MutexGuard<'a, T> = mutex::MutexGuard<'a, T, Loop>;
}
