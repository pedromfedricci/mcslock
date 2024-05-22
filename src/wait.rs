use core::sync::atomic::Ordering::Relaxed;

use crate::cfg::atomic::AtomicPtr;
use crate::relax::Relax;

pub trait Waiter<T> {
    /// Creates a new Waiter instance.
    ///
    /// It's expected for a implementing type to be compiler-time evaluable,
    /// since they compose node types that do require it (except Loom based
    /// nodes).
    #[cfg(not(all(loom, test)))]
    const NEW: Self;

    /// Creates a new Waiter instance with Loom primitives (non-const).
    ///
    /// Loom primitives are not compiler-time evaluable.
    #[cfg(all(loom, test))]
    fn new() -> Self;

    fn lock_wait<W: Wait>(&self);

    fn unlock_relax<R: Relax>(next: &AtomicPtr<T>) -> *mut T {
        let mut relax = R::default();
        loop {
            let ptr = next.load(Relaxed);
            let true = ptr.is_null() else { return ptr };
            relax.relax();
        }
    }

    fn notify(&self);
}

/// TODO: Docs
pub trait Wait: Default {
    /// TODO: Docs
    type Relax: Relax;

    /// TODO: Docs
    fn should_wait(&self) -> bool;

    /// TODO: Dcos
    fn relax(&mut self);
}
