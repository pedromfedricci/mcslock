//! TODO: Docs

use core::marker::PhantomData;

use crate::relax::{Loop, Relax, Spin, SpinBackoff};
use crate::wait::Wait;

#[cfg(feature = "yield")]
use crate::relax::{Yield, YieldBackoff};

pub use sealed::Park;

mod sealed {
    /// TODO: Docs
    pub trait Park: crate::wait::Wait {}
}

struct Limited<R: Relax, const MAX: u8 = 100> {
    marker: PhantomData<R>,
}

impl<R: Relax, const MAX: u8> Wait for Limited<R, MAX> {
    type Relax = R;

    fn wait<T, F>(event: &T, not_ready: F)
    where
        F: Fn(&T) -> bool,
    {
        let mut relax = Self::Relax::default();
        let mut attempts: u8 = 0;
        while attempts < MAX && not_ready(event) {
            relax.relax();
            attempts += 1;
        }
    }
}

/// TODO: Docs
#[non_exhaustive]
pub struct SpinThanPark;

impl Wait for SpinThanPark {
    type Relax = Spin;

    #[inline(always)]
    fn wait<T, F>(event: &T, not_ready: F)
    where
        F: Fn(&T) -> bool,
    {
        Limited::<Self::Relax>::wait(event, not_ready)
    }
}

impl Park for SpinThanPark {}

/// TODO: Docs
#[non_exhaustive]
pub struct LoopThanPark;

impl Wait for LoopThanPark {
    type Relax = Loop;

    #[inline(always)]
    fn wait<T, F>(event: &T, not_ready: F)
    where
        F: Fn(&T) -> bool,
    {
        Limited::<Self::Relax>::wait(event, not_ready)
    }
}

impl Park for LoopThanPark {}

/// TODO: Docs
#[cfg(feature = "yield")]
#[non_exhaustive]
pub struct YieldThanPark;

#[cfg(feature = "yield")]
impl Wait for YieldThanPark {
    type Relax = Yield;

    #[inline(always)]
    fn wait<T, F>(event: &T, not_ready: F)
    where
        F: Fn(&T) -> bool,
    {
        Limited::<Self::Relax>::wait(event, not_ready)
    }
}

#[cfg(feature = "yield")]
impl Park for YieldThanPark {}

/// TODO: Docs
#[non_exhaustive]
pub struct ImmediatePark;

impl Wait for ImmediatePark {
    // Relax strategy doesn't matter here since it won't be used.
    type Relax = Loop;

    #[inline(always)]
    fn wait<T, F>(_: &T, _: F)
    where
        F: Fn(&T) -> bool,
    {
    }
}

impl Park for ImmediatePark {}

/// TODO: Docs
#[non_exhaustive]
pub struct SpinBackoffThanPark;

impl Wait for SpinBackoffThanPark {
    type Relax = SpinBackoff;

    #[inline(always)]
    fn wait<T, F>(event: &T, not_ready: F)
    where
        F: Fn(&T) -> bool,
    {
        Limited::<Self::Relax>::wait(event, not_ready)
    }
}

impl Park for SpinBackoffThanPark {}

/// TODO: Docs
#[cfg(feature = "yield")]
pub struct YieldBackoffThanPark;

#[cfg(feature = "yield")]
impl Wait for YieldBackoffThanPark {
    type Relax = YieldBackoff;

    #[inline(always)]
    fn wait<T, F>(event: &T, not_ready: F)
    where
        F: Fn(&T) -> bool,
    {
        Limited::<Self::Relax>::wait(event, not_ready)
    }
}

#[cfg(feature = "yield")]
impl Park for YieldBackoffThanPark {}
