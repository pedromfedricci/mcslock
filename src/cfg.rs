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
    impl<T: ?Sized> WithUnchecked for UnsafeCell<T> {
        type Target = T;

        unsafe fn with_unchecked<F, Ret>(&self, f: F) -> Ret
        where
            F: FnOnce(&Self::Target) -> Ret,
        {
            // SAFETY: Caller must guarantee there are no mutable aliases.
            f(unsafe { &*self.get() })
        }
    }

    #[cfg(all(loom, test))]
    #[cfg(not(tarpaulin_include))]
    impl<T: ?Sized> WithUnchecked for UnsafeCell<T> {
        type Target = T;

        unsafe fn with_unchecked<F, Ret>(&self, f: F) -> Ret
        where
            F: FnOnce(&Self::Target) -> Ret,
        {
            // SAFETY: Caller must guarantee there are no mutable aliases.
            self.with(|ptr| f(unsafe { &*ptr }))
        }
    }

    mod sealed {
        /// A trait that extends [`UnsafeCell`] to allow running closures against
        /// its underlying data.
        pub trait WithUnchecked {
            /// The type of the underlying data.
            type Target: ?Sized;

            /// Runs `f` against a shared reference borrowed from a [`UnsafeCell`].
            ///
            /// # Safety
            ///
            /// Caller must guarantee there are no mutable aliases to the
            /// underlying data.
            unsafe fn with_unchecked<F, Ret>(&self, f: F) -> Ret
            where
                F: FnOnce(&Self::Target) -> Ret;
        }
    }
}

pub mod hint {
    #[cfg(not(all(loom, test)))]
    pub use core::hint::spin_loop;

    #[cfg(all(loom, test))]
    pub use loom::hint::spin_loop;
}

pub mod thread {
    #[cfg(all(any(feature = "yield", test), not(all(loom, test))))]
    pub use std::thread::yield_now;

    #[cfg(all(loom, test))]
    pub use loom::thread::yield_now;

    #[cfg(all(feature = "thread_local", not(all(loom, test))))]
    pub use std::thread::LocalKey;

    #[cfg(all(feature = "thread_local", loom, test))]
    pub use loom::thread::LocalKey;
}
