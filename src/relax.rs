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

use crate::cfg::hint;
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

/// A strategy that, as [`Spin`], will run a busy-wait spin-loop, except this
/// implementation will perform exponential backoff.
///
/// Backing off in spin loops can reduce contention and improve overall
/// performance for some use cases. Further profiling is important to measure
/// any significant improvement. As with [`Spin`], this implementation is
/// subject to priority inversion problems, you may want to consider a yielding
/// strategy or using a scheduler-aware lock.
pub struct SpinBackoff {
    step: Step,
}

impl SpinBackoff {
    const SPIN_LIMIT: u32 = 6;
}

// SAFETY: None of the associated function implementations contain any code
// that could cause a thread exit.
unsafe impl Relax for SpinBackoff {
    #[inline(always)]
    fn new() -> Self {
        Self { step: Step::default() }
    }

    #[inline(always)]
    fn relax(&mut self) {
        self.step.spin_to(Self::SPIN_LIMIT);
        self.step.step_to(Self::SPIN_LIMIT);
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
    step: Step,
}

#[cfg(any(feature = "yield", test))]
impl YieldBackoff {
    const SPIN_LIMIT: u32 = SpinBackoff::SPIN_LIMIT;
    const YIELD_LIMIT: u32 = 10;
}

// SAFETY: None of the associated function implementations contain any code
// that could cause a thread exit.
#[cfg(any(feature = "yield", test))]
unsafe impl Relax for YieldBackoff {
    #[inline(always)]
    fn new() -> Self {
        Self { step: Step::default() }
    }

    #[inline(always)]
    fn relax(&mut self) {
        if self.step.0 <= Self::SPIN_LIMIT {
            self.step.spin();
        } else {
            thread::yield_now();
        }
        self.step.step_to(Self::YIELD_LIMIT);
    }
}

/// Keeps count of the number of steps taken.
#[derive(Default)]
struct Step(u32);

impl Step {
    /// Unbounded backoff spinning.
    #[cfg(any(feature = "yield", test))]
    #[inline(always)]
    fn spin(&self) {
        for _ in 0..1 << self.0 {
            hint::spin_loop();
        }
    }

    /// Bounded backoff spinning.
    #[inline(always)]
    fn spin_to(&self, max: u32) {
        for _ in 0..1 << self.0.min(max) {
            hint::spin_loop();
        }
    }

    /// Bounded step increment.
    #[inline(always)]
    fn step_to(&mut self, end: u32) {
        if self.0 <= end {
            self.0 += 1;
        }
    }
}

#[cfg(all(not(loom), test))]
mod test {
    fn returns<R: super::Relax>() {
        let mut relax = R::new();
        for _ in 0..10 {
            relax.relax();
        }
    }

    #[test]
    fn spins() {
        returns::<super::Spin>();
    }

    #[test]
    fn spins_backoff() {
        returns::<super::SpinBackoff>();
    }

    #[test]
    fn yields() {
        returns::<super::Yield>();
    }

    #[test]
    fn yields_backoff() {
        returns::<super::YieldBackoff>();
    }

    #[test]
    fn loops() {
        returns::<super::Loop>();
    }
}
