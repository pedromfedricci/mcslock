//! TODO: Docs

use crate::lock::Wait;
use crate::relax::{Loop, Relax, Spin, SpinBackoff, Yield, YieldBackoff};

/// A thread parking waiting policy to be applied when the lock is contended.
pub trait Park: Relax {
    /// The relax operation that should be applied during unlock waiting loops.
    type UnlockRelax: Relax;

    /// Hints whether or not should the parking operation be executed at this
    /// time.
    ///
    /// Returning `true` means we are not ready to run the park operation yet,
    /// there is some other event that should occur first. Returning `false`
    /// indicates that the thread is no longer waiting for any event, and so
    /// it is hinting that it should be parked.
    fn should_wait(&self) -> bool;
}

type Uint = u16;
const DEFMAX: Uint = 100;

/// TODO: Docs
#[derive(Default)]
pub struct SpinThanPark<const MAX: Uint = DEFMAX> {
    bounded: Bounded<Spin, MAX>,
}

impl<const MAX: Uint> Relax for SpinThanPark<MAX> {
    #[inline(always)]
    fn relax(&mut self) {
        self.bounded.relax();
    }
}

impl<const MAX: Uint> Park for SpinThanPark<MAX> {
    type UnlockRelax = Spin;

    #[inline(always)]
    fn should_wait(&self) -> bool {
        self.bounded.should_wait()
    }
}

/// TODO: Docs
#[derive(Default)]
pub struct LoopThanPark<const MAX: Uint = DEFMAX> {
    bounded: Bounded<Loop, MAX>,
}

impl<const MAX: Uint> Relax for LoopThanPark<MAX> {
    #[inline(always)]
    fn relax(&mut self) {
        self.bounded.relax();
    }
}

impl<const MAX: Uint> Park for LoopThanPark<MAX> {
    type UnlockRelax = Loop;

    #[inline(always)]
    fn should_wait(&self) -> bool {
        self.bounded.should_wait()
    }
}

/// TODO: Docs
#[derive(Default)]
pub struct YieldThanPark<const MAX: Uint = DEFMAX> {
    bounded: Bounded<Yield, MAX>,
}

impl<const MAX: Uint> Relax for YieldThanPark<MAX> {
    #[inline(always)]
    fn relax(&mut self) {
        self.bounded.relax();
    }
}

impl<const MAX: Uint> Park for YieldThanPark<MAX> {
    type UnlockRelax = Yield;

    #[inline(always)]
    fn should_wait(&self) -> bool {
        self.bounded.should_wait()
    }
}

/// Immediately inform that the current should be parked.
#[derive(Default)]
#[non_exhaustive]
pub struct ImmediatePark;

impl Relax for ImmediatePark {
    #[cfg(not(tarpaulin_include))]
    #[inline(always)]
    fn relax(&mut self) {}
}

impl Park for ImmediatePark {
    type UnlockRelax = Yield;

    #[inline(always)]
    fn should_wait(&self) -> bool {
        false
    }
}

/// TODO: Docs
#[derive(Default)]
pub struct SpinBackoffThanPark<const MAX: Uint = DEFMAX> {
    bounded: Bounded<SpinBackoff, MAX>,
}

impl<const MAX: Uint> Relax for SpinBackoffThanPark<MAX> {
    #[inline(always)]
    fn relax(&mut self) {
        self.bounded.relax();
    }
}

impl<const MAX: Uint> Park for SpinBackoffThanPark<MAX> {
    type UnlockRelax = SpinBackoff;

    #[inline(always)]
    fn should_wait(&self) -> bool {
        self.bounded.should_wait()
    }
}

/// TODO: Docs
#[derive(Default)]
pub struct YieldBackoffThanPark<const MAX: Uint = DEFMAX> {
    bounded: Bounded<YieldBackoff, MAX>,
}

impl<const MAX: Uint> Relax for YieldBackoffThanPark<MAX> {
    #[inline(always)]
    fn relax(&mut self) {
        self.bounded.relax();
    }
}

impl<const MAX: Uint> Park for YieldBackoffThanPark<MAX> {
    type UnlockRelax = YieldBackoff;

    #[inline(always)]
    fn should_wait(&self) -> bool {
        self.bounded.should_wait()
    }
}

/// A bounded, relaxed waiting policy that will block the thread against a
/// condition for at most some number of attempts.
///
/// While the condition holds `true`, we are signaling to the Parker than it
/// should not park the current thread yet. Once all attempts have been made,
/// return `false`, indicating to the Parker that it should park the thread.
#[derive(Default)]
struct Bounded<R, const MAX: Uint> {
    relax: R,
    attempts: Uint,
}

impl<R: Relax, const MAX: Uint> Bounded<R, MAX> {
    const fn should_wait(&self) -> bool {
        self.attempts < MAX
    }

    fn relax(&mut self) {
        self.relax.relax();
        self.attempts += 1;
    }
}

#[derive(Default)]
pub(super) struct ParkWait<P> {
    wait: P,
}

impl<P: Park> Relax for ParkWait<P> {
    fn relax(&mut self) {
        self.wait.relax();
    }
}

impl<P: Park> Wait for ParkWait<P> {
    type UnlockRelax = P::UnlockRelax;

    fn should_wait(&self) -> bool {
        self.wait.should_wait()
    }
}

#[cfg(all(not(loom), test))]
mod test {
    use super::{Park, Uint};

    trait Bounded<const MAX: Uint>: Park {}

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

    fn counter_loop<P: Park>() -> (P, Uint) {
        let mut wait = P::default();
        let mut counter = 0;
        while wait.should_wait() {
            wait.relax();
            counter += 1;
        }
        (wait, counter)
    }

    fn should_wait<P: Bounded<MAX>, const MAX: Uint>() {
        let (wait, counter): (P, Uint) = counter_loop();
        assert!(!wait.should_wait());
        assert_eq!(MAX, counter);
    }

    fn should_not_wait<P: Park>() {
        let (wait, counter): (P, Uint) = counter_loop();
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
