use crate::lock::Wait;
use crate::relax::{Loop, Relax, Spin, SpinBackoff, Yield, YieldBackoff};

/// A thread parking waiting policy to be applied when the lock is contended.
pub unsafe trait Park: Relax {
    /// The relax operation that should be applied during unlock waiting loops.
    type UnlockRelax: Relax;

    /// Hints whether or not should the parking operation be executed at this
    /// time.
    ///
    /// Returning `false` means that the thread is not ready to be put to sleep
    /// yet, there is some other event that should occur first. Returning `true`
    /// indicates that the thread is no longer waiting for any event, and so it
    /// is hinting that it should be parked.
    fn should_park(&self) -> bool;
}

type Uint = u16;

pub const DEFMAX: Uint = 100;

pub struct SpinThenPark<const MAX: Uint = DEFMAX> {
    bounded: Bounded<Spin, MAX>,
}

// SAFETY: None of the associated function implementations contain any code
// that could cause a thread exit.
unsafe impl<const MAX: Uint> Relax for SpinThenPark<MAX> {
    #[inline(always)]
    fn new() -> Self {
        Self { bounded: Bounded::new() }
    }

    #[inline(always)]
    fn relax(&mut self) {
        self.bounded.relax();
    }
}

// SAFETY: None of the associated function implementations contain any code
// that could cause a thread exit.
unsafe impl<const MAX: Uint> Park for SpinThenPark<MAX> {
    type UnlockRelax = Spin;

    #[inline(always)]
    fn should_park(&self) -> bool {
        self.bounded.should_park()
    }
}

pub struct LoopThenPark<const MAX: Uint = DEFMAX> {
    bounded: Bounded<Loop, MAX>,
}

// SAFETY: None of the associated function implementations contain any code
// that could cause a thread exit.
unsafe impl<const MAX: Uint> Relax for LoopThenPark<MAX> {
    #[inline(always)]
    fn new() -> Self {
        Self { bounded: Bounded::new() }
    }

    #[inline(always)]
    fn relax(&mut self) {
        self.bounded.relax();
    }
}

// SAFETY: None of the associated function implementations contain any code
// that could cause a thread exit.
unsafe impl<const MAX: Uint> Park for LoopThenPark<MAX> {
    type UnlockRelax = Loop;

    #[inline(always)]
    fn should_park(&self) -> bool {
        self.bounded.should_park()
    }
}

pub struct YieldThenPark<const MAX: Uint = DEFMAX> {
    bounded: Bounded<Yield, MAX>,
}

// SAFETY: None of the associated function implementations contain any code
// that could cause a thread exit.
unsafe impl<const MAX: Uint> Relax for YieldThenPark<MAX> {
    #[inline(always)]
    fn new() -> Self {
        Self { bounded: Bounded::new() }
    }

    #[inline(always)]
    fn relax(&mut self) {
        self.bounded.relax();
    }
}

// SAFETY: None of the associated function implementations contain any code
// that could cause a thread exit.
unsafe impl<const MAX: Uint> Park for YieldThenPark<MAX> {
    type UnlockRelax = Yield;

    #[inline(always)]
    fn should_park(&self) -> bool {
        self.bounded.should_park()
    }
}

// Immediately inform that the current should be parked.
pub struct ImmediatePark;

// SAFETY: None of the associated function implementations contain any code
// that could cause a thread exit.
unsafe impl Relax for ImmediatePark {
    #[inline(always)]
    fn new() -> Self {
        Self
    }

    #[cfg(not(tarpaulin_include))]
    #[inline(always)]
    fn relax(&mut self) {}
}

// SAFETY: None of the associated function implementations contain any code
// that could cause a thread exit.
unsafe impl Park for ImmediatePark {
    type UnlockRelax = Yield;

    #[inline(always)]
    fn should_park(&self) -> bool {
        true
    }
}

pub struct SpinBackoffThenPark<const MAX: Uint = DEFMAX> {
    bounded: Bounded<SpinBackoff, MAX>,
}

// SAFETY: None of the associated function implementations contain any code
// that could cause a thread exit.
unsafe impl<const MAX: Uint> Relax for SpinBackoffThenPark<MAX> {
    #[inline(always)]
    fn new() -> Self {
        Self { bounded: Bounded::new() }
    }

    #[inline(always)]
    fn relax(&mut self) {
        self.bounded.relax();
    }
}

// SAFETY: None of the associated function implementations contain any code
// that could cause a thread exit.
unsafe impl<const MAX: Uint> Park for SpinBackoffThenPark<MAX> {
    type UnlockRelax = SpinBackoff;

    #[inline(always)]
    fn should_park(&self) -> bool {
        self.bounded.should_park()
    }
}

pub struct YieldBackoffThenPark<const MAX: Uint = DEFMAX> {
    bounded: Bounded<YieldBackoff, MAX>,
}

// SAFETY: None of the associated function implementations contain any code
// that could cause a thread exit.
unsafe impl<const MAX: Uint> Relax for YieldBackoffThenPark<MAX> {
    #[inline(always)]
    fn new() -> Self {
        Self { bounded: Bounded::new() }
    }

    #[inline(always)]
    fn relax(&mut self) {
        self.bounded.relax();
    }
}

// SAFETY: None of the associated function implementations contain any code
// that could cause a thread exit.
unsafe impl<const MAX: Uint> Park for YieldBackoffThenPark<MAX> {
    type UnlockRelax = YieldBackoff;

    #[inline(always)]
    fn should_park(&self) -> bool {
        self.bounded.should_park()
    }
}

/// A bounded, relaxed waiting policy that will block the thread for at most
/// some number of attempts.
struct Bounded<R, const MAX: Uint> {
    relax: R,
    attempts: Uint,
}

impl<R: Relax, const MAX: Uint> Bounded<R, MAX> {
    fn new() -> Self {
        Self { relax: R::new(), attempts: 0 }
    }

    const fn should_park(&self) -> bool {
        self.attempts >= MAX
    }

    fn relax(&mut self) {
        self.relax.relax();
        self.attempts += 1;
    }
}

/// A generic parking waiter, that implements [`Park`] so long as `P`
/// implements it too.
///
/// This saves us from defining a blanket [`Wait`] impl for a generic `T` where
/// `T` implements [`Park`], because that would prevent us from implementing
/// `Wait` for `T` when it implements [`Relax`], since they would conflict. We
/// need both `Park` and `Relax` types to implement `Wait`.
pub(super) struct ParkWait<P> {
    waiter: P,
}

// SAFETY: None of the associated function implementations contain any code
// that could cause a thread exit.
unsafe impl<P: Park> Relax for ParkWait<P> {
    fn new() -> Self {
        Self { waiter: P::new() }
    }

    fn relax(&mut self) {
        self.waiter.relax();
    }
}

impl<P: Park> Wait for ParkWait<P> {
    type UnlockRelax = P::UnlockRelax;

    fn should_park(&self) -> bool {
        self.waiter.should_park()
    }
}

#[cfg(all(not(loom), test))]
mod test {
    use super::{Park, Uint};

    trait Bounded<const MAX: Uint>: Park {}

    use super::SpinThenPark;
    impl<const MAX: Uint> Bounded<MAX> for SpinThenPark<MAX> {}

    use super::YieldThenPark;
    impl<const MAX: Uint> Bounded<MAX> for YieldThenPark<MAX> {}

    use super::LoopThenPark;
    impl<const MAX: Uint> Bounded<MAX> for LoopThenPark<MAX> {}

    use super::SpinBackoffThenPark;
    impl<const MAX: Uint> Bounded<MAX> for SpinBackoffThenPark<MAX> {}

    use super::YieldBackoffThenPark;
    impl<const MAX: Uint> Bounded<MAX> for YieldBackoffThenPark<MAX> {}

    fn parking_policy_loop<P: Park>() -> (P, Uint) {
        let mut parking_waiter = P::new();
        let mut counter = 0;
        while !parking_waiter.should_park() {
            parking_waiter.relax();
            counter += 1;
        }
        (parking_waiter, counter)
    }

    fn should_park_eventually<P: Bounded<MAX>, const MAX: Uint>() {
        let (waiter, counter): (P, Uint) = parking_policy_loop();
        assert!(waiter.should_park());
        assert_eq!(MAX, counter);
    }

    fn should_park_immediately<P: Park>() {
        let (waiter, counter): (P, Uint) = parking_policy_loop();
        assert!(waiter.should_park());
        assert_eq!(0, counter);
    }

    #[test]
    fn spins() {
        should_park_eventually::<SpinThenPark<0>, 0>();
        should_park_eventually::<SpinThenPark<1>, 1>();
        should_park_eventually::<SpinThenPark<10>, 10>();
    }

    #[test]
    fn yields() {
        should_park_eventually::<YieldThenPark<0>, 0>();
        should_park_eventually::<YieldThenPark<1>, 1>();
        should_park_eventually::<YieldThenPark<10>, 10>();
    }

    #[test]
    fn loops() {
        should_park_eventually::<LoopThenPark<0>, 0>();
        should_park_eventually::<LoopThenPark<1>, 1>();
        should_park_eventually::<LoopThenPark<10>, 10>();
    }

    #[test]
    fn spin_backoff() {
        should_park_eventually::<SpinBackoffThenPark<0>, 0>();
        should_park_eventually::<SpinBackoffThenPark<1>, 1>();
        should_park_eventually::<SpinBackoffThenPark<10>, 10>();
    }

    #[test]
    fn yield_backoff() {
        should_park_eventually::<YieldBackoffThenPark<0>, 0>();
        should_park_eventually::<YieldBackoffThenPark<1>, 1>();
        should_park_eventually::<YieldBackoffThenPark<10>, 10>();
    }

    #[test]
    fn immediately() {
        should_park_immediately::<super::ImmediatePark>();
    }
}
