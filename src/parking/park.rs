//! TODO: Docs

use crate::relax::{Loop, Relax, Spin, SpinBackoff, Yield, YieldBackoff};
use crate::wait::Wait;

pub use sealed::Park;

mod sealed {
    /// TODO: Docs
    pub trait Park: crate::wait::Wait {}
}

type Uint = u8;
const DEFMAX: Uint = 100;

/// TODO: Docs
#[derive(Default)]
pub struct SpinThanPark<const MAX: Uint = DEFMAX> {
    bounded: Bounded<Spin, MAX>,
}

impl<const MAX: Uint> Wait for SpinThanPark<MAX> {
    type Relax = Spin;

    #[inline(always)]
    fn should_wait(&self) -> bool {
        self.bounded.should_wait()
    }

    #[inline(always)]
    fn relax(&mut self) {
        self.bounded.relax();
    }
}

impl Park for SpinThanPark {}

/// TODO: Docs
#[derive(Default)]
pub struct LoopThanPark<const MAX: Uint = DEFMAX> {
    bounded: Bounded<Loop, MAX>,
}

impl<const MAX: Uint> Wait for LoopThanPark<MAX> {
    type Relax = Loop;

    #[inline(always)]
    fn should_wait(&self) -> bool {
        self.bounded.should_wait()
    }

    #[inline(always)]
    fn relax(&mut self) {
        self.bounded.relax();
    }
}

impl Park for LoopThanPark {}

/// TODO: Docs
#[derive(Default)]
pub struct YieldThanPark<const MAX: Uint = DEFMAX> {
    bounded: Bounded<Yield, MAX>,
}

impl<const MAX: Uint> Wait for YieldThanPark<MAX> {
    type Relax = Yield;

    #[inline(always)]
    fn should_wait(&self) -> bool {
        self.bounded.should_wait()
    }

    #[inline(always)]
    fn relax(&mut self) {
        self.bounded.relax();
    }
}

impl Park for YieldThanPark {}

/// Immediately inform that the current should be parked.
#[derive(Default)]
#[non_exhaustive]
pub struct ImmediatePark;

impl Wait for ImmediatePark {
    // We still want to apply some relax operation during `unlock_wait`, even
    // thought we don't want to run any before asking the thread to be parked.
    type Relax = Yield;

    #[inline(always)]
    fn should_wait(&self) -> bool {
        false
    }

    #[cfg(not(tarpaulin_include))]
    #[inline(always)]
    fn relax(&mut self) {}
}

impl Park for ImmediatePark {}

/// TODO: Docs
#[derive(Default)]
pub struct SpinBackoffThanPark<const MAX: Uint = DEFMAX> {
    bounded: Bounded<SpinBackoff, MAX>,
}

impl<const MAX: Uint> Wait for SpinBackoffThanPark<MAX> {
    type Relax = SpinBackoff;

    #[inline(always)]
    fn should_wait(&self) -> bool {
        self.bounded.should_wait()
    }

    #[inline(always)]
    fn relax(&mut self) {
        self.bounded.relax();
    }
}

impl Park for SpinBackoffThanPark {}

/// TODO: Docs
#[derive(Default)]
pub struct YieldBackoffThanPark<const MAX: Uint = DEFMAX> {
    bounded: Bounded<YieldBackoff, MAX>,
}

impl<const MAX: Uint> Wait for YieldBackoffThanPark<MAX> {
    type Relax = YieldBackoff;

    #[inline(always)]
    fn should_wait(&self) -> bool {
        self.bounded.should_wait()
    }

    #[inline(always)]
    fn relax(&mut self) {
        self.bounded.relax();
    }
}

impl Park for YieldBackoffThanPark {}

/// A bounded, relaxed waiting policy that will block the thread against a
/// condition for at most some number of attempts.
///
/// While the condition holds `true`, we are signaling to the Parker than it
/// should not park the current thread yet. Once all attempts have been issued,
/// return `false`, indicating to the Parker that it should park the thread.
#[derive(Default)]
struct Bounded<R, const MAX: Uint> {
    relax: R,
    attempts: Uint,
}

impl<R: Relax, const MAX: Uint> Wait for Bounded<R, MAX> {
    type Relax = R;

    fn should_wait(&self) -> bool {
        self.attempts < MAX
    }

    fn relax(&mut self) {
        self.relax.relax();
        self.attempts += 1;
    }
}

#[cfg(all(not(loom), test))]
mod test {
    use super::{Uint, Wait};

    trait Bounded<const MAX: Uint>: Wait {}

    use super::SpinThanPark;
    impl<const MAX: Uint> Bounded<MAX> for SpinThanPark<MAX> {}

    use super::YieldThanPark;
    impl<const MAX: Uint> Bounded<MAX> for YieldThanPark<MAX> {}

    use super::LoopThanPark;
    impl<const MAX: Uint> Bounded<MAX> for LoopThanPark<MAX> {}

    use super::SpinBackoffThanPark;
    impl<const MAX: Uint> Bounded<MAX> for SpinBackoffThanPark<MAX> {}

    use super::YieldBackoffThanPark;
    impl<const MAX: Uint> Bounded<MAX> for YieldBackoffThanPark<MAX> {}

    fn counter_loop<W: Wait>() -> (W, Uint) {
        let mut wait = W::default();
        let mut counter = 0;
        while wait.should_wait() {
            wait.relax();
            counter += 1;
        }
        (wait, counter)
    }

    fn should_wait<W: Bounded<MAX>, const MAX: Uint>() {
        let (wait, counter): (W, Uint) = counter_loop();
        assert!(!wait.should_wait());
        assert_eq!(MAX, counter);
    }

    fn should_not_wait<W: Wait>() {
        let (wait, counter): (W, Uint) = counter_loop();
        assert!(!wait.should_wait());
        assert_eq!(0, counter);
    }

    #[test]
    fn spins() {
        should_wait::<SpinThanPark<0>, 0>();
        should_wait::<SpinThanPark<1>, 1>();
        should_wait::<SpinThanPark<10>, 10>();
    }

    #[test]
    fn yields() {
        should_wait::<YieldThanPark<0>, 0>();
        should_wait::<YieldThanPark<1>, 1>();
        should_wait::<YieldThanPark<10>, 10>();
    }

    #[test]
    fn loops() {
        should_wait::<LoopThanPark<0>, 0>();
        should_wait::<LoopThanPark<1>, 1>();
        should_wait::<LoopThanPark<10>, 10>();
    }

    #[test]
    fn spin_backoff() {
        should_wait::<SpinBackoffThanPark<0>, 0>();
        should_wait::<SpinBackoffThanPark<1>, 1>();
        should_wait::<SpinBackoffThanPark<10>, 10>();
    }

    #[test]
    fn yield_backoff() {
        should_wait::<YieldBackoffThanPark<0>, 0>();
        should_wait::<YieldBackoffThanPark<1>, 1>();
        should_wait::<YieldBackoffThanPark<10>, 10>();
    }

    #[test]
    fn immediate() {
        should_not_wait::<super::ImmediatePark>();
    }
}
