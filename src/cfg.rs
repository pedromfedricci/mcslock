pub mod atomic {
    #[cfg(not(all(loom, test)))]
    pub use core::sync::atomic::{fence, AtomicBool, AtomicPtr};

    #[cfg(all(loom, test))]
    pub use loom::sync::atomic::{fence, AtomicBool, AtomicPtr};
}

pub mod cell {
    pub use sealed::WithUnchecked;

    #[cfg(not(all(loom, test)))]
    pub use core::cell::UnsafeCell;

    #[cfg(all(loom, test))]
    pub use loom::cell::UnsafeCell;

    #[cfg(not(all(loom, test)))]
    impl<T: ?Sized> WithUnchecked<T> for UnsafeCell<T> {
        unsafe fn with_unchecked<F, Ret>(&self, f: F) -> Ret
        where
            F: FnOnce(&T) -> Ret,
        {
            // SAFETY: Caller must guarantee there are no mutable aliases.
            f(unsafe { &*self.get() })
        }
    }

    #[cfg(all(loom, test))]
    impl<T: ?Sized> WithUnchecked<T> for UnsafeCell<T> {
        unsafe fn with_unchecked<F, Ret>(&self, f: F) -> Ret
        where
            F: FnOnce(&T) -> Ret,
        {
            // SAFETY: Caller must guarantee there are no mutable aliases.
            self.with(|ptr| f(unsafe { &*ptr }))
        }
    }

    mod sealed {
        /// A trait that extends [`UnsafeCell`] to allow running closures against
        /// its underlying data.
        pub trait WithUnchecked<T: ?Sized> {
            /// Runs `f` against a shared reference borrowed from a [`UnsafeCell`].
            ///
            /// # Safety
            ///
            /// Caller must guarantee there are no mutable aliases to the
            /// underlying data.
            unsafe fn with_unchecked<F, Ret>(&self, f: F) -> Ret
            where
                F: FnOnce(&T) -> Ret;
        }
    }
}

pub mod hint {
    #[cfg(not(all(loom, test)))]
    pub use core::hint::spin_loop;

    #[cfg(all(loom, test))]
    pub use loom::hint::spin_loop;
}

#[cfg(any(feature = "yield", test))]
pub mod thread {
    #[cfg(not(all(loom, test)))]
    pub use std::thread::yield_now;

    #[cfg(all(loom, test))]
    pub use loom::thread::yield_now;
}
