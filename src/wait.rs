use core::sync::atomic::Ordering::Relaxed;

use crate::cfg::atomic::AtomicPtr;
use crate::relax::Relax;

pub trait Waiter<T>: Sized {
    #[cfg(not(all(loom, test)))]
    const NEW: Self;

    #[cfg(all(loom, test))]
    fn new() -> Self;

    fn lock_wait<R: Relax>(&self);

    fn unlock_wait<R: Relax>(&self, next: &AtomicPtr<T>) -> *mut T {
        let mut relax = R::default();
        loop {
            let ptr = next.load(Relaxed);
            let true = ptr.is_null() else { return ptr };
            relax.relax();
        }
    }

    fn notify(&self);
}
