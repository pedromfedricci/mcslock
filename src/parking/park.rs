//! Thread parking policies that determine the behaviour of locks when
//! encountering contention.
//!
//! When a thread is "parked", it essentially goes into a sleeping state until
//! it is awakened by the OS when a event or condition occurs. This is used to
//! prevent busy-waiting, where a thread continuously checks for a condition to
//! be true, wasting CPU resources.
//!
//! This crate integrates with the OS specific thread sleeping and awakening
//! infrastructure transparently. Users are then responsible solely to tell
//! _when_ should the current thread be put to sleep. The `Park` trait defines
//! the interface of which users will then conditionally request the current
//! waiting thread to be parked.

use core::marker::PhantomData;

use crate::cfg::debug_abort;
use crate::relax::{Loop, Relax, Spin, SpinBackoff};

#[cfg(any(feature = "yield", test))]
use crate::relax::{Yield, YieldBackoff};

pub(crate) use wait::{CantPark, ParkWait};

/// The thread parking waiting policy to be applied when the lock is contended.
///
/// # Example
///
/// ```
/// // Requires `parking` feature.
/// use mcslock::parking::park::Park;
/// use mcslock::relax::Spin;
///
/// #[derive(Default)]
/// struct SpinThenPark(u32);
///
/// unsafe impl Park for SpinThenPark {
///     type Relax = Spin;
///
///     #[inline(always)]
///     fn new() -> Self {
///         Self::default()
///     }
///
///     #[inline(always)]
///     fn should_park(&self) -> bool {
///         self.0 >= 100
///     }
///
///     #[inline(always)]
///     fn on_failure(&mut self) {
///         self.0 += 1;
///     }
/// }
/// ```
///
/// # Safety
///
/// All associated function implementations **must not** cause a thread exit,
/// such as envoking a uncaught [`core::panic!`] call, or any other operation
/// that will panic the thread. Exiting the thread will result in undefined
/// behiavior.
pub unsafe trait Park {
    /// The relax operation that should be run during a period of contention.
    type Relax: Relax;

    /// Returns the initial value for this parking policy.
    fn new() -> Self;

    /// Hints whether or not should the parking operation be executed at this
    /// time.
    ///
    /// Returning `false` means that the thread is not ready to be put to sleep
    /// yet, there is some other event that should occur first. Returning `true`
    /// indicates that the thread is no longer waiting for any event, and so it
    /// is hinting that it should be parked.
    fn should_park(&self) -> bool;

    /// Updates the inner state whenever the thread fails to acquire the lock.
    ///
    /// This function will be called once whenever both `should_park` returns
    /// `false` **and** the thread fails to acquire the lock. This will not be
    /// called otherwise.
    fn on_failure(&mut self);
}

mod sealed {
    /// The actual implementation of this crate's `Park` types.
    pub trait ParkImpl {
        type Relax: super::Relax;

        /// The actual `new` implementation.
        fn new() -> Self;

        /// The actual `should_park` implementation.
        fn should_park(&self) -> bool;

        /// The actual `on_failure` implementation.
        fn on_failure(&mut self);
    }
}
use sealed::ParkImpl;

// SAFETY: All `new`, `should_park` and `on_failure` function implementations are
// protected with a process abort (under test with unwind on panic configuration)
// in case any of them where to panic the thread.
#[doc(hidden)]
unsafe impl<P: ParkImpl> Park for P {
    type Relax = P::Relax;

    #[inline(always)]
    fn new() -> Self {
        debug_abort::on_unwind(|| P::new())
    }

    #[inline(always)]
    fn should_park(&self) -> bool {
        debug_abort::on_unwind(|| P::should_park(self))
    }

    #[inline(always)]
    fn on_failure(&mut self) {
        debug_abort::on_unwind(|| P::on_failure(self));
    }
}

/// A busy-wait spin-loop then thread sleeping policy.
///
/// A thread parking policy that, while trying to acquire the lock, will initially
/// run a busy-wait spin-loop (signaling the CPU to power down) for a number of
/// attempts and then, if unsuccessful, requests for the current thread to be put
/// to sleep.
///
/// The [`Spin`] relax strategy is executed during waiting loops.
pub struct SpinThenPark {
    bounded: Bounded<{ Self::ATTEMPTS }>,
}

impl SpinThenPark {
    /// The maximum number of attempts this policy will run before being parked.
    const ATTEMPTS: Uint = DEFAULT_ATTEMPTS;
}

impl ParkImpl for SpinThenPark {
    type Relax = Spin;

    fn new() -> Self {
        Self { bounded: Bounded::new() }
    }

    fn should_park(&self) -> bool {
        self.bounded.should_park()
    }

    fn on_failure(&mut self) {
        self.bounded.on_failure();
    }
}

/// A no power down spin-loop then thread sleeping policy.
///
/// A thread parking policy that, while trying to acquire the lock, will initially
/// rapidly spin in a loop (without signaling the CPU to power down) for a number
/// of attempts and then, if unsuccessful, requests for the current thread to be
/// put to sleep.
///
/// The [`Loop`] relax strategy is executed during waiting loops.
pub struct LoopThenPark {
    bounded: Bounded<{ Self::ATTEMPTS }>,
}

impl LoopThenPark {
    /// The maximum number of attempts this policy will run before being parked.
    const ATTEMPTS: Uint = DEFAULT_ATTEMPTS;
}

impl ParkImpl for LoopThenPark {
    type Relax = Loop;

    fn new() -> Self {
        Self { bounded: Bounded::new() }
    }

    fn should_park(&self) -> bool {
        self.bounded.should_park()
    }

    fn on_failure(&mut self) {
        self.bounded.on_failure();
    }
}

/// A thread yielding then thread sleeping policy.
///
/// A thread parking policy that, while trying to acquire the lock, will initially
/// request the OS to yield the current thread, for number of attempts and then,
/// if unsuccessful, requests for the current thread to be put to sleep.
///
/// The [`Yield`] relax strategy is executed during waiting loops.
#[cfg(any(feature = "yield", test))]
#[cfg_attr(docsrs, doc(cfg(feature = "yield")))]
pub struct YieldThenPark {
    bounded: Bounded<{ Self::ATTEMPTS }>,
}

#[cfg(any(feature = "yield", test))]
impl YieldThenPark {
    /// The maximum number of attempts this policy will run before being parked.
    const ATTEMPTS: Uint = DEFAULT_ATTEMPTS;
}

#[cfg(any(feature = "yield", test))]
impl ParkImpl for YieldThenPark {
    type Relax = Yield;

    fn new() -> Self {
        Self { bounded: Bounded::new() }
    }

    fn should_park(&self) -> bool {
        self.bounded.should_park()
    }

    fn on_failure(&mut self) {
        self.bounded.on_failure();
    }
}

/// Immediately requests the thread to be put to sleep.
///
/// A thread parking policy that immediately requests that the current thread
/// should be put to sleep. No relax operation is executed during lock waiting
/// loops. During unlock waiting loops, the generic `R` type's relax strategy
/// will be executed.
///
/// The default relax operation executed is [`Spin`].
pub struct ImmediatePark<R: Relax = Spin> {
    relax: PhantomData<R>,
}

impl<R: Relax> ParkImpl for ImmediatePark<R> {
    type Relax = R;

    fn new() -> Self {
        Self { relax: PhantomData }
    }

    fn should_park(&self) -> bool {
        true
    }

    #[cfg(not(tarpaulin_include))]
    fn on_failure(&mut self) {}
}

/// A spin-loop with exponential backoff then thread sleeping policy.
///
/// A thread parking policy that, while trying to acquire the lock, will initially
/// run a busy-wait spin-loop with exponential backoff (signaling the CPU to
/// power down) for a number of attempts and then, if unsuccessful, requests
/// for the current thread to be put to sleep.
///
/// The [`SpinBackoff`] relax strategy is executed during waiting loops.
pub struct SpinBackoffThenPark {
    bounded: Bounded<{ Self::ATTEMPTS }>,
}

impl SpinBackoffThenPark {
    /// The maximum number of attempts this policy will run before being parked.
    const ATTEMPTS: Uint = DEFAULT_ATTEMPTS;
}

impl ParkImpl for SpinBackoffThenPark {
    type Relax = SpinBackoff;

    fn new() -> Self {
        Self { bounded: Bounded::new() }
    }

    fn should_park(&self) -> bool {
        self.bounded.should_park()
    }

    fn on_failure(&mut self) {
        self.bounded.on_failure();
    }
}

/// A spin-loop with exponential backoff, then thread yielding and finally thread
/// sleeping policy.
///
/// A thread parking policy that, while trying to acquire the lock, will initially
/// run a busy-wait spin-loop with exponential backoff (signaling the CPU to
/// power down) up to a threshold, then requests the OS to yield the current
/// thread, for a number of attempts and finally, if unsuccessful, requests for
/// the current thread to be put to sleep.
///
/// The [`YieldBackoff`] relax strategy is executed during waiting loops.
#[cfg(any(feature = "yield", test))]
#[cfg_attr(docsrs, doc(cfg(feature = "yield")))]
pub struct YieldBackoffThenPark {
    bounded: Bounded<{ Self::ATTEMPTS }>,
}

#[cfg(any(feature = "yield", test))]
impl YieldBackoffThenPark {
    /// The maximum number of attempts this policy will run before being parked.
    const ATTEMPTS: Uint = DEFAULT_ATTEMPTS;
}

#[cfg(any(feature = "yield", test))]
impl ParkImpl for YieldBackoffThenPark {
    type Relax = YieldBackoff;

    fn new() -> Self {
        Self { bounded: Bounded::new() }
    }

    fn should_park(&self) -> bool {
        self.bounded.should_park()
    }

    fn on_failure(&mut self) {
        self.bounded.on_failure();
    }
}

/// An unsigned integer type use as the inner type for [`Bounded`].
///
/// All `Bounded` related arithmetic operations (eg. sum) should only
/// use this same type as the right-hand and lef-hand side types.
type Uint = u32;

/// A default number of attempts to acquire the lock before parking the thread.
const DEFAULT_ATTEMPTS: Uint = 100;

/// A bounded parking policy that will block the thread for at most some number
/// of attempts.
struct Bounded<const MAX: Uint> {
    attempts: Uint,
}

impl<const MAX: Uint> Bounded<MAX> {
    const fn new() -> Self {
        Self { attempts: 0 }
    }

    const fn should_park(&self) -> bool {
        self.attempts >= MAX
    }

    fn on_failure(&mut self) {
        self.attempts += 1;
    }
}

mod wait {
    use core::marker::PhantomData;

    use crate::lock::Wait;
    use crate::parking::park::Park;
    use crate::relax::Relax;

    use super::ParkImpl;

    /// A generic parking waiter, that implements [`Park`] so long as `P`
    /// implements it too.
    ///
    /// This saves us from defining a blanket [`Wait`] impl for a generic `T` where
    /// `T` implements [`Park`], because that would prevent us from implementing
    /// `Wait` for `T` when it implements [`Relax`], since they would conflict. We
    /// need both `Park` and `Relax` types to implement `Wait`.
    pub struct ParkWait<P>(PhantomData<P>);

    impl<P: Park> Wait for ParkWait<P> {
        type LockRelax = P::Relax;
        type UnlockRelax = P::Relax;
        type Park = P;
    }

    /// A parking policy that never requests the thread to be parked.
    ///
    /// Useful for `Relax` types so that they can implement the `Wait` trait, even
    /// though they will never call any of the `Park` methods.
    pub struct CantPark<R>(PhantomData<R>);

    #[cfg(not(tarpaulin_include))]
    impl<R: Relax> ParkImpl for CantPark<R> {
        type Relax = R;

        fn new() -> Self {
            Self(PhantomData)
        }

        fn should_park(&self) -> bool {
            false
        }

        fn on_failure(&mut self) {}
    }
}

#[cfg(all(not(loom), test))]
mod test {
    use super::{Park, Uint};

    fn parking_loop<P: Park, const MAX: Uint>() -> (P, Uint) {
        let mut parker = P::new();
        let mut counter = 0;
        for _ in 0..=MAX.saturating_mul(10) {
            while !parker.should_park() {
                parker.on_failure();
                counter += 1;
            }
        }
        (parker, counter)
    }

    fn should_park_eventually<P: Park, const MAX: Uint>() {
        let (waiter, counter) = parking_loop::<P, MAX>();
        assert!(waiter.should_park());
        assert_eq!(MAX, counter);
    }

    fn should_park_immediately<P: Park, const MAX: Uint>() {
        let (waiter, counter) = parking_loop::<P, MAX>();
        assert!(waiter.should_park());
        assert_eq!(0, counter);
    }

    #[test]
    fn spins() {
        use super::SpinThenPark;
        const MAX: Uint = SpinThenPark::ATTEMPTS;
        should_park_eventually::<SpinThenPark, MAX>();
    }

    #[test]
    fn yields() {
        use super::YieldThenPark;
        const MAX: Uint = YieldThenPark::ATTEMPTS;
        should_park_eventually::<YieldThenPark, MAX>();
    }

    #[test]
    fn loops() {
        use super::LoopThenPark;
        const MAX: Uint = LoopThenPark::ATTEMPTS;
        should_park_eventually::<LoopThenPark, MAX>();
    }

    #[test]
    fn spin_backoff() {
        use super::SpinBackoffThenPark;
        const MAX: Uint = SpinBackoffThenPark::ATTEMPTS;
        should_park_eventually::<SpinBackoffThenPark, MAX>();
    }

    #[test]
    fn yield_backoff() {
        use super::YieldBackoffThenPark;
        const MAX: Uint = YieldBackoffThenPark::ATTEMPTS;
        should_park_eventually::<YieldBackoffThenPark, MAX>();
    }

    #[test]
    fn immediately() {
        should_park_immediately::<super::ImmediatePark, 10>();
    }
}
