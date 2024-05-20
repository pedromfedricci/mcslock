//! TODO: Docs

use core::marker::PhantomData;

use crate::relax::{Loop, Relax, Spin, SpinBackoff, Yield, YieldBackoff};
use crate::wait::Wait;

pub use sealed::Park;

mod sealed {
    /// TODO: Docs
    pub trait Park: crate::wait::Wait {}
}

/// TODO: Docs
#[non_exhaustive]
pub struct SpinThanPark;

impl Wait for SpinThanPark {
    type Relax = Spin;

    #[inline(always)]
    fn wait<T, F>(event: &T, not_ready: F) -> bool
    where
        F: Fn(&T) -> bool,
    {
        Bounded::<Self::Relax>::wait(event, not_ready)
    }
}

impl Park for SpinThanPark {}

/// TODO: Docs
#[non_exhaustive]
pub struct LoopThanPark;

impl Wait for LoopThanPark {
    type Relax = Loop;

    #[inline(always)]
    fn wait<T, F>(event: &T, not_ready: F) -> bool
    where
        F: Fn(&T) -> bool,
    {
        Bounded::<Self::Relax>::wait(event, not_ready)
    }
}

impl Park for LoopThanPark {}

/// TODO: Docs
#[non_exhaustive]
pub struct YieldThanPark;

impl Wait for YieldThanPark {
    type Relax = Yield;

    #[inline(always)]
    fn wait<T, F>(event: &T, not_ready: F) -> bool
    where
        F: Fn(&T) -> bool,
    {
        Bounded::<Self::Relax>::wait(event, not_ready)
    }
}

impl Park for YieldThanPark {}

/// TODO: Docs
#[non_exhaustive]
pub struct ImmediatePark;

// Immediately inform that the event was not observed, without checking.
impl Wait for ImmediatePark {
    type Relax = Yield;

    #[inline(always)]
    fn wait<T, F>(_: &T, _: F) -> bool
    where
        F: Fn(&T) -> bool,
    {
        false
    }
}

impl Park for ImmediatePark {}

/// TODO: Docs
#[non_exhaustive]
pub struct SpinBackoffThanPark;

impl Wait for SpinBackoffThanPark {
    type Relax = SpinBackoff;

    #[inline(always)]
    fn wait<T, F>(event: &T, not_ready: F) -> bool
    where
        F: Fn(&T) -> bool,
    {
        Bounded::<Self::Relax>::wait(event, not_ready)
    }
}

impl Park for SpinBackoffThanPark {}

/// TODO: Docs
pub struct YieldBackoffThanPark;

impl Wait for YieldBackoffThanPark {
    type Relax = YieldBackoff;

    #[inline(always)]
    fn wait<T, F>(event: &T, not_ready: F) -> bool
    where
        F: Fn(&T) -> bool,
    {
        Bounded::<Self::Relax>::wait(event, not_ready)
    }
}

impl Park for YieldBackoffThanPark {}

/// A bounded, relaxed waiting policy that will block against an event for at
/// most some number of attempts.
///
/// If the event was not ready until all attempts have been issued, then return
/// `false`, indicating to the `Waiter` (eg. Parker) that the event was not
/// observed within the limit. If the event was observed, then return `true`.  
struct Bounded<R: Relax, const MAX: u8 = 100> {
    marker: PhantomData<R>,
}

impl<R: Relax, const MAX: u8> Wait for Bounded<R, MAX> {
    type Relax = R;

    fn wait<T, F>(event: &T, not_ready: F) -> bool
    where
        F: Fn(&T) -> bool,
    {
        let mut relax = Self::Relax::default();
        let mut attempts = 0;
        while attempts < MAX {
            let true = not_ready(event) else { return true };
            relax.relax();
            attempts += 1;
        }
        false
    }
}

#[cfg(all(not(loom), test))]
mod test {
    use super::Wait;

    fn ready<W: Wait>() -> bool {
        W::wait(&(), |()| false)
    }

    fn not_ready<W: Wait>() -> bool {
        W::wait(&(), |()| true)
    }

    fn assert_bounded<W: Wait>() {
        assert!(ready::<W>());
        assert!(!not_ready::<W>());
    }

    #[test]
    fn spins() {
        assert_bounded::<super::SpinThanPark>();
    }

    #[test]
    fn spins_backoff() {
        assert_bounded::<super::SpinBackoffThanPark>();
    }

    #[test]
    fn yields() {
        assert_bounded::<super::YieldThanPark>();
    }

    #[test]
    fn yields_backoff() {
        assert_bounded::<super::YieldBackoffThanPark>();
    }

    #[test]
    fn loops() {
        assert_bounded::<super::LoopThanPark>();
    }

    #[test]
    fn immediate() {
        use super::ImmediatePark;
        assert!(!ready::<ImmediatePark>());
        assert!(!not_ready::<ImmediatePark>());
    }
}
