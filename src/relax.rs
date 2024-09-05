// Modified version of relax.rs from spin-rs to support Loom yielding,
// exponential backoff and requires unsafe for `Relax`.
//
// Original file at its most recent change (at the time of writing):
// https://github.com/mvdnes/spin-rs/blob/5860ee114094cf200b97348ff332155fbd7159b4/src/relax.rs
//
// Copyright (c) 2014 Mathijs van de Nes
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Strategies that determine the behaviour of locks when encountering contention.

use crate::{cfg::hint, lock::Wait};

#[cfg(any(feature = "yield", test))]
use crate::cfg::thread;

/// A trait implemented by spinning relax strategies.
///
/// # Example
///
/// ```
/// use mcslock::relax::Relax;
///
/// struct Spin;
///
/// unsafe impl Relax for Spin {
///     #[inline(always)]
///     fn new() -> Self {
///         Self
///     }
///
///     #[inline(always)]
///     fn relax(&mut self) {
///         core::hint::spin_loop();
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
pub unsafe trait Relax {
    /// Returns the initial value for this relaxing strategy.
    fn new() -> Self;

    /// Performs the relaxing operation during a period of contention.
    fn relax(&mut self);
}

/// A strategy that rapidly spins while informing the CPU that it should power
/// down non-essential components via [`core::hint::spin_loop`].
///
/// Note that spinning is a 'dumb' strategy and most schedulers cannot correctly
/// differentiate it from useful work, thereby misallocating even more CPU time
/// to the spinning process. This is known as [priority inversion].
///
/// If you see signs that priority inversion is occurring, consider switching to
/// [`Yield`] or, even better, not using a spinlock at all and opting for a proper
/// scheduler-aware lock. Remember also that different targets, operating systems,
/// schedulers, and even the same scheduler with different workloads will exhibit
/// different behaviour. Just because priority inversion isn't occurring in your
/// tests does not mean that it will not occur. Use a scheduler-aware lock if at
/// all possible.
///
/// [priority inversion]: https://matklad.github.io/2020/01/02/spinlocks-considered-harmful.html
pub struct Spin;

// SAFETY: None of the associated function implementations contain any code
// that could cause a thread exit.
unsafe impl Relax for Spin {
    #[inline(always)]
    fn new() -> Self {
        Self
    }

    #[inline(always)]
    fn relax(&mut self) {
        hint::spin_loop();
    }
}

/// A strategy that yields the current time slice to the scheduler in favour of
/// other threads or processes.
///
/// This is generally used as a strategy for minimising power consumption and
/// priority inversion on targets that have a standard library available. Note
/// that such targets have scheduler-integrated concurrency primitives available,
/// and you should generally use these instead, except in rare circumstances.
#[cfg(any(feature = "yield", test))]
#[cfg_attr(docsrs, doc(cfg(feature = "yield")))]
pub struct Yield;

// SAFETY: None of the associated function implementations contain any code
// that could cause a thread exit.
#[cfg(any(feature = "yield", test))]
unsafe impl Relax for Yield {
    #[inline(always)]
    fn new() -> Self {
        Self
    }

    #[inline(always)]
    fn relax(&mut self) {
        thread::yield_now();
    }
}

/// A strategy that rapidly spins, without telling the CPU to do any powering down.
///
/// You almost certainly do not want to use this. Use [`Spin`] instead. It exists
/// for completeness and for targets that, for some reason, miscompile or do not
/// support spin hint intrinsics despite attempting to generate code for them
/// (i.e: this is a workaround for possible compiler bugs).
pub struct Loop;

// SAFETY: None of the associated function implementations contain any code
// that could cause a thread exit.
unsafe impl Relax for Loop {
    #[inline(always)]
    fn new() -> Self {
        Self
    }

    #[inline(always)]
    fn relax(&mut self) {}
}

// Exponential backoff is based on the crossbeam-utils implementation.
// link to most recent change (as the time of writing):
// https://github.com/crossbeam-rs/crossbeam/blob/371de8c2d304db07662450995848f3dc9598ac99/crossbeam-utils/src/backoff.rs
//
// Copyright (c) 2019 The Crossbeam Project Developers
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

/// An unsigned integer type use as the inner type for [`Backoff`].
///
/// All backoff related arithmetic operations (eg. left shift, sum) should only
/// only use this same type as the right-hand and lef-hand side types.
type Uint = u32;

/// A strategy that, as [`Spin`], will run a busy-wait spin-loop, except this
/// implementation will perform exponential backoff.
///
/// Backing off in spin loops can reduce contention and improve overall
/// performance for some use cases. Further profiling is important to measure
/// any significant improvement. As with [`Spin`], this implementation is
/// subject to priority inversion problems, you may want to consider a yielding
/// strategy or using a scheduler-aware lock.
pub struct SpinBackoff {
    inner: Backoff<{ Self::MAX }>,
}

impl SpinBackoff {
    /// The largest value the inner backoff counter can reach.
    const MAX: Uint = 6;

    /// The actual relax implementation.
    fn relax_impl(&mut self) {
        self.inner.saturating_spin();
        self.inner.saturating_step();
    }
}

// The maximum inner value **must** be smaller than Uint::BITS, or else the
// bitshift operation will overflow, which is not only incorrect but it will
// also result in UB when executed under `Relax::relax` on debug mode since it
// will panic and exit the thread which is forbidded by `Relax`.
const _: () = assert!(SpinBackoff::MAX < Uint::BITS);

// SAFETY: The `new` function implementation does contain any code that could
// could cause a thread exit. The `relax` function implementation is protected
// with a process abort (under test with unwind on panic configuration) in case
// an arithmetic operation overflow were to panic the thread.
unsafe impl Relax for SpinBackoff {
    #[inline(always)]
    fn new() -> Self {
        Self { inner: Backoff::default() }
    }

    #[cfg(not(all(test, panic = "unwind")))]
    #[cfg(not(tarpaulin_include))]
    #[inline(always)]
    fn relax(&mut self) {
        self.relax_impl();
    }

    #[cfg(all(test, panic = "unwind"))]
    fn relax(&mut self) {
        Abort::on_unwind(|| self.relax_impl());
    }
}

/// A strategy that, as [`Yield`], will yield back to the OS scheduler, but only
/// after performing exponential backoff in a spin loop within a threshold.
///
/// Backing off in spin loops can reduce contention and improve overall
/// performance for some use cases. Further profiling is important to measure
/// any significant improvement. Just like [`Yield`], this is an strategy for
/// minimising power consumption and priority inversion on targets that have
/// a standard library available. Note that you should prefer scheduler-aware
/// locks if you have access to the standard library.
#[cfg(any(feature = "yield", test))]
#[cfg_attr(docsrs, doc(cfg(feature = "yield")))]
pub struct YieldBackoff {
    inner: Backoff<{ Self::MAX }>,
}

#[cfg(any(feature = "yield", test))]
impl YieldBackoff {
    /// The largest value the inner backoff counter can reach.
    const MAX: Uint = SpinBackoff::MAX;

    /// The actual relax implementation.
    fn relax_impl(&mut self) {
        if self.inner.0 < Self::MAX {
            self.inner.wrapping_spin();
        } else {
            thread::yield_now();
        }
        self.inner.saturating_step();
    }
}

// The maximum inner value **must** be smaller than Uint::BITS, or else the
// bitshift operation will overflow, which is not only incorrect but it will
// also result in UB when executed under `Relax::relax` on debug mode since it
// will panic and exit the thread which is forbidded by `Relax`.
#[cfg(any(feature = "yield", test))]
const _: () = assert!(YieldBackoff::MAX < Uint::BITS);

// SAFETY: The `new` function implementation does contain any code that could
// could cause a thread exit. The `relax` function implementation is protected
// with a process abort (under test with unwind on panic configuration) in case
// an arithmetic operation overflow were to panic the thread.
#[cfg(any(feature = "yield", test))]
unsafe impl Relax for YieldBackoff {
    #[inline(always)]
    fn new() -> Self {
        Self { inner: Backoff::default() }
    }

    #[cfg(not(all(test, panic = "unwind")))]
    #[cfg(not(tarpaulin_include))]
    #[inline(always)]
    fn relax(&mut self) {
        self.relax_impl();
    }

    #[cfg(all(test, panic = "unwind"))]
    fn relax(&mut self) {
        Abort::on_unwind(|| self.relax_impl());
    }
}

/// Inner backoff counter that keeps track of the number of shifts applied.
///
/// The maximum value the inner shift counter can take is defined by `MAX`.
#[derive(Default)]
struct Backoff<const MAX: Uint>(Uint);

impl<const MAX: Uint> Backoff<MAX> {
    /// The number of iterations that the backoff spin loop will execute, the
    /// result of the expression may overflow.
    const fn end(shifts: Uint) -> Uint {
        1 << shifts
    }

    /// Runs a bounded spin loop `1 << self.inner` times, up to `MAX` times.
    fn saturating_spin(&self) {
        let shifts = self.0.min(MAX);
        for _ in 0..Self::end(shifts) {
            hint::spin_loop();
        }
    }

    /// Runs a unbounded spin loop `1 << self.inner` times, the result of the
    /// expression may overflow.
    #[cfg(any(feature = "yield", test))]
    fn wrapping_spin(&self) {
        for _ in 0..Self::end(self.0) {
            hint::spin_loop();
        }
    }

    /// Incremets one to the inner counter, saturating the counter at `MAX`.
    fn saturating_step(&mut self) {
        (self.0 < MAX).then(|| self.0 += 1);
    }
}

/// A test only type that will abort the program execution once dropped.
///
/// To avoid aborting the proccess, callers must `forget` all instance of the
/// `Abort` type.
#[cfg(all(test, panic = "unwind"))]
struct Abort;

#[cfg(all(test, panic = "unwind"))]
impl Abort {
    /// Runs the closure, aborting the process if a unwinding panic occurs.
    fn on_unwind<F: FnOnce()>(f: F) {
        let abort = Abort;
        f();
        core::mem::forget(abort);
    }
}

#[cfg(all(test, panic = "unwind"))]
#[cfg(not(tarpaulin_include))]
impl Drop for Abort {
    fn drop(&mut self) {
        panic!("thread exits are forbidden inside `relax`, aborting");
    }
}

/// A generic relaxed waiter, that implements [`Relax`] so long as `R`
/// implements it too.
///
/// This saves us from defining a blanket [`Wait`] impl for a generic `T` where
/// `T` implements [`Relax`], because that would prevent us from implementing
/// `Wait` for `T` when it implements [`Park`], since they would conflict. We
/// need both `Relax` and `Park` types to implement `Wait`.
pub(crate) struct RelaxWait<R> {
    waiter: R,
}

// SAFETY: A generic type `R` that implements `Relax` guarantees that their
// implementation fullfils the `Relax` safety contract.
unsafe impl<R: Relax> Relax for RelaxWait<R> {
    fn new() -> Self {
        Self { waiter: R::new() }
    }

    fn relax(&mut self) {
        self.waiter.relax();
    }
}

impl<R: Relax> Wait for RelaxWait<R> {
    type UnlockRelax = R;

    #[cfg(not(tarpaulin_include))]
    fn should_park(&self) -> bool {
        unimplemented!("should_park` should not be called by `RelaxWait`");
    }
}

#[cfg(all(not(loom), test))]
mod test {
    use super::{Relax, Uint};

    fn returns<R: Relax, const MAX: Uint>() {
        let mut relax = R::new();
        for _ in 0..=MAX.saturating_mul(10) {
            relax.relax();
        }
    }

    #[test]
    fn spins() {
        returns::<super::Spin, 10>();
    }

    #[test]
    fn spins_backoff() {
        use super::SpinBackoff;
        const MAX: Uint = SpinBackoff::MAX;
        returns::<SpinBackoff, MAX>();
    }

    #[test]
    fn yields() {
        returns::<super::Yield, 10>();
    }

    #[test]
    fn yields_backoff() {
        use super::YieldBackoff;
        const MAX: u32 = YieldBackoff::MAX;
        returns::<YieldBackoff, MAX>();
    }

    #[test]
    fn loops() {
        returns::<super::Loop, 10>();
    }
}
