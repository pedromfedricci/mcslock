//! MCS lock implementations with thread parking support.
//!
//! This module provides implementations that **are not** `no_std` compatible.
//!
//! Each [`raw`] and [`barging`] modules implement the same protocols as their
//! root level counter parts and the same locking interfaces. The distinction
//! is that these Mutex implementations will transparently put the waiting
//! threads to sleep under some policy. Users are free to implement their own
//! policies or pick sensible ones under the [`park`] module. To define your
//! own policy, users must implement the [`Park`] trait.
//!
//! [`raw`]: crate::parking::raw
//! [`barging`]: crate::parking::barging
//! [`park`]: crate::parking::park
//! [`Park`]: crate::parking::park::Park

pub mod park;
pub mod raw;

#[cfg(feature = "barging")]
#[cfg_attr(docsrs, doc(cfg(feature = "barging")))]
pub mod barging;

mod parker;
