#![warn(missing_docs)]
#![warn(missing_doc_code_examples)]
#![warn(rust_2018_idioms)]

//! Traits and implementations for the allocation of aligned heap memory.

/// Error type for custom errors of AlignedBox.
#[derive(Debug)]
pub enum AlignedBoxError {
    /// Too many elements. The requested size exceeds the maximum size for a slice.
    TooManyElements,
    /// Memory allocation failed. This is likely caused by an out of memory situation.
    OutOfMemory,
}

impl std::error::Error for AlignedBoxError {}

impl std::fmt::Display for AlignedBoxError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            AlignedBoxError::TooManyElements => write!(f, "Too many elements for a slice."),
            AlignedBoxError::OutOfMemory => write!(f, "Memory allocation failed. Out of memory?"),
        }
    }
}

/// Allows moving single values into aligned heap memory.
pub trait AlignedBox<T> {
    /// Store `value` of type `T` on the heap, making sure that it is aligned to a multiple of
    /// `alignment`. The implementation of this trait should also make sure that the requested
    /// alignment is a valid alignment for type `T` or increase it to a valid alignment otherwise.
    fn new_aligned(
        alignment: usize,
        value: T,
    ) -> std::result::Result<std::boxed::Box<T>, std::boxed::Box<dyn std::error::Error>>;
}

/// Allows allocating aligned heap memory for multiple values and initializing them by copying a
/// template value.
pub trait AlignedBoxedSliceFromValue<T: Copy> {
    /// Allocate memory for `nelems` values of type `T` on the heap, making sure that it is aligned
    /// to a multiple of `alignment`. All values are initialized by copies of `value`. The
    /// implementation of this trait should also make sure that the requested alignment is a valid
    /// alignment for type `T` or increase it to a valid alignment otherwise.
    fn new_aligned_slice_from_value(
        alignment: usize,
        nelems: usize,
        value: T,
    ) -> std::result::Result<std::boxed::Box<[T]>, std::boxed::Box<dyn std::error::Error>>;
}

/// Allows allocating aligned heap memory for multiple values and initializing them with default
/// values.
pub trait AlignedBoxedSliceFromDefault<T: Default> {
    /// Allocate memory for `nelems` values of type `T` on the heap, making sure that it is aligned
    /// to a multiple of `alignment`. All values are initialized by the default value of type `T`.
    /// The implementation of this trait should also make sure that the requested alignment is a
    /// valid alignment for type `T` or increase it to a valid alignment otherwise.
    fn new_aligned_slice_from_default(
        alignment: usize,
        nelems: usize,
    ) -> std::result::Result<std::boxed::Box<[T]>, std::boxed::Box<dyn std::error::Error>>;
}

impl<T> AlignedBox<T> for std::boxed::Box<T> {
    /// # Example
    /// Place value 17 of type `i32` on the heap, aligned to 64 bytes:
    /// ```
    /// use aligned_box::AlignedBox;
    ///
    /// let b = Box::<i32>::new_aligned(64, 17);
    /// ```
    fn new_aligned(
        mut alignment: usize,
        value: T,
    ) -> std::result::Result<std::boxed::Box<T>, std::boxed::Box<dyn std::error::Error>> {
        if alignment < std::mem::align_of::<T>() {
            alignment = std::mem::align_of::<T>();
        }

        let memsize: usize = std::mem::size_of::<T>();
        let layout = std::alloc::Layout::from_size_align(memsize, alignment)?;

        // SAFETY: Requirements on layout are enforced by using from_size_align().
        let ptr = unsafe { std::alloc::alloc(layout) as *mut T };
        if ptr.is_null() {
            return Err(AlignedBoxError::OutOfMemory.into());
        }

        // SAFETY: The pointer is non-null, refers to properly sized and aligned memory and it is
        // consumed such that it cannot be used from anywhere outside the Box.
        let mut b = unsafe { std::boxed::Box::from_raw(ptr) };

        // *b is not a valid instance but uninitialized memory. We have to write to it without
        // dropping the old (invalid) value. Also the original value must not be dropped.
        // SAFETY: Both value and b point to valid and properly aligned memory.
        unsafe { std::ptr::write(&mut *b, value) };

        Ok(b)
    }
}

impl<T: Default> AlignedBoxedSliceFromDefault<T> for std::boxed::Box<[T]> {
    /// # Example
    /// Allocate memory for 1024 values of type `f32` on the heap, aligned to 128 bytes. Values
    /// are initialized by their default value:
    /// ```
    /// use aligned_box::AlignedBoxedSliceFromDefault;
    ///
    /// let b = Box::<[f32]>::new_aligned_slice_from_default(128, 1024);
    /// ```
    fn new_aligned_slice_from_default(
        mut alignment: usize,
        nelems: usize,
    ) -> std::result::Result<std::boxed::Box<[T]>, std::boxed::Box<dyn std::error::Error>> {
        if alignment < std::mem::align_of::<T>() {
            alignment = std::mem::align_of::<T>();
        }

        // Make sure the requested amount of Ts will fit into a slice.
        let maxelems = (isize::MAX as usize) / std::mem::size_of::<T>();
        if nelems > maxelems {
            return Err(AlignedBoxError::TooManyElements.into());
        }

        let memsize: usize = std::mem::size_of::<T>() * nelems;
        let layout = std::alloc::Layout::from_size_align(memsize, alignment)?;

        // SAFETY: Requirements on layout are enforced by using from_size_align().
        let ptr = unsafe { std::alloc::alloc(layout) as *mut T };
        if ptr.is_null() {
            return Err(AlignedBoxError::OutOfMemory.into());
        }

        // SAFETY: Requirements on ptr and nelems have been verified: ptr is non-null, nelems does
        // not exceed the maximum size. The referenced memory is not accessed as long as slice
        // exists.
        let slice = unsafe { std::slice::from_raw_parts_mut(ptr, nelems) };

        // SAFETY: We only create a single Box from the given slice. The slice itself is consumed
        // so that the referenced memory can be modified from now on.
        let mut b = unsafe { std::boxed::Box::from_raw(slice) };

        for i in b.iter_mut() {
            let d = T::default(); // create new default value

            // *i is not a valid instance but uninitialized memory. We have to write to it without
            // dropping the old (invalid) value. Also d must not be dropped.
            // SAFETY: Both value and b point to valid and properly aligned memory.
            unsafe { std::ptr::write(&mut *i, d) };
        }

        Ok(b)
    }
}

impl<T: Copy> AlignedBoxedSliceFromValue<T> for std::boxed::Box<[T]> {
    /// # Example
    /// Allocate memory for 1024 values of type `f32` on the heap, aligned to 128 bytes. All values
    /// are initialized with PI:
    /// ```
    /// use aligned_box::AlignedBoxedSliceFromValue;
    ///
    /// let b = Box::<[f32]>::new_aligned_slice_from_value(128, 1024, std::f32::consts::PI);
    /// ```
    fn new_aligned_slice_from_value(
        mut alignment: usize,
        nelems: usize,
        value: T,
    ) -> std::result::Result<std::boxed::Box<[T]>, std::boxed::Box<dyn std::error::Error>> {
        if alignment < std::mem::align_of::<T>() {
            alignment = std::mem::align_of::<T>();
        }

        // Make sure the requested amount of Ts will fit into a slice.
        let maxelems = (isize::MAX as usize) / std::mem::size_of::<T>();
        if nelems > maxelems {
            return Err(AlignedBoxError::TooManyElements.into());
        }

        let memsize: usize = std::mem::size_of::<T>() * nelems;
        let layout = std::alloc::Layout::from_size_align(memsize, alignment)?;

        // SAFETY: Requirements on layout are enforced by using from_size_align().
        let ptr = unsafe { std::alloc::alloc(layout) as *mut T };
        if ptr.is_null() {
            return Err(AlignedBoxError::OutOfMemory.into());
        }

        // SAFETY: Requirements on ptr and nelems have been verified: ptr is non-null, nelems does
        // not exceed the maximum size. The referenced memory is not accessed as long as slice
        // exists.
        let slice = unsafe { std::slice::from_raw_parts_mut(ptr, nelems) };

        // SAFETY: We only create a single Box from the given slice. The slice itself is consumed
        // so that the referenced memory can be modified from now on.
        let mut b = unsafe { std::boxed::Box::from_raw(slice) };

        for i in b.iter_mut() {
            // T is Copy and therefore also !Drop. We can simply copy from value to *i without
            // worrying about dropping.
            *i = value;
        }

        Ok(b)
    }
}

#[cfg(test)]
mod tests {
    use super::{AlignedBox, AlignedBoxedSliceFromDefault, AlignedBoxedSliceFromValue};
    use lazy_static::lazy_static;

    lazy_static! {
        static ref SEQ_TEST_MUTEX: std::sync::RwLock<()> = std::sync::RwLock::new(());
    }

    #[test]
    fn alignment() {
        let _m = SEQ_TEST_MUTEX.read().unwrap();

        let alignments = [
            1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536,
            131072, 262144, 524288, 1048576,
        ];

        for a in alignments.iter() {
            let b = std::boxed::Box::<[u8]>::new_aligned_slice_from_value(*a, 42, 0).unwrap();
            assert_eq!((b.as_ptr() as usize) % *a, 0);
        }
    }

    #[test]
    fn size() {
        let _m = SEQ_TEST_MUTEX.read().unwrap();

        let sizes = [
            1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536,
            131072, 262144, 524288, 1048576,
        ];

        for s in sizes.iter() {
            let b = std::boxed::Box::<[u8]>::new_aligned_slice_from_value(1, *s, 0).unwrap();
            assert_eq!(b.len(), *s);
        }
    }

    #[test]
    fn free() {
        // This test should not run concurrently with other tests since multiple threads influence
        // each other and addresses are not reproducible.
        let _m = SEQ_TEST_MUTEX.write().unwrap();

        const ATTEMPTS: usize = 1000;
        let alignment = 1024 * 1024; // 1MB
        let size = 1024; // 1KB

        let mut addrs = std::collections::HashSet::new();

        // Test if dropping the box actually frees the memory. If any two allocations give us the
        // same address, this is the case.
        for _ in 0..ATTEMPTS {
            let b =
                std::boxed::Box::<[u8]>::new_aligned_slice_from_value(alignment, size, 0).unwrap();
            addrs.insert(b.as_ptr() as usize);
        }
        assert_ne!(addrs.len(), ATTEMPTS);
    }

    #[test]
    fn aliasing() {
        let _m = SEQ_TEST_MUTEX.read().unwrap();

        let size = 1024; // 1KB

        let b1 = std::boxed::Box::<[u8]>::new_aligned_slice_from_value(1, size, 0).unwrap();
        let b2 = std::boxed::Box::<[u8]>::new_aligned_slice_from_value(1, size, 0).unwrap();
        let addr1 = b1.as_ptr() as usize;
        let addr2 = b2.as_ptr() as usize;
        assert_ne!(addr1, addr2);
        if addr1 > addr2 {
            assert!((addr1 - addr2) >= size);
        } else {
            assert!((addr2 - addr1) >= size);
        }
    }

    #[test]
    fn read_write() {
        let _m = SEQ_TEST_MUTEX.read().unwrap();

        let mut b =
            std::boxed::Box::<[f32]>::new_aligned_slice_from_value(128, 1024, 3.1415).unwrap();
        for i in b.iter() {
            assert_eq!(*i, 3.1415);
        }
        let mut ctr: f32 = 0.0;
        for i in b.iter_mut() {
            *i = ctr;
            ctr += 1.0;
        }
        ctr = 0.0;
        for i in b.iter() {
            assert_eq!(*i, ctr);
            ctr += 1.0;
        }
    }

    #[test]
    fn defaults() {
        let _m = SEQ_TEST_MUTEX.read().unwrap();

        #[derive(PartialEq, Eq, Debug)]
        struct SomeVaryingDefault {
            i: i32,
        }

        static COUNTER: std::sync::atomic::AtomicI32 = std::sync::atomic::AtomicI32::new(0);

        impl Default for SomeVaryingDefault {
            fn default() -> SomeVaryingDefault {
                SomeVaryingDefault {
                    i: COUNTER.fetch_add(1, std::sync::atomic::Ordering::Relaxed),
                }
            }
        }

        let b = std::boxed::Box::<[SomeVaryingDefault]>::new_aligned_slice_from_default(128, 1024)
            .unwrap();
        assert_eq!(SomeVaryingDefault::default().i, 1024);
        let mut ctr = 0;
        for i in b.iter() {
            assert_eq!(i.i, ctr);
            ctr += 1;
        }
    }

    #[test]
    fn move_sem() {
        let _m = SEQ_TEST_MUTEX.read().unwrap();

        let v = vec![1, 2, 3];
        let b = std::boxed::Box::new_aligned(128, v).unwrap();
        assert_eq!(*b, vec![1, 2, 3]);
    }

    #[test]
    fn copy_sem() {
        let _m = SEQ_TEST_MUTEX.read().unwrap();

        let v = 17;
        let _ = std::boxed::Box::new_aligned(128, v).unwrap();
        let _ = std::boxed::Box::new_aligned_slice_from_value(128, 1024, v).unwrap();
        assert_eq!(v, 17);
    }

    #[test]
    fn min_align() {
        let _m = SEQ_TEST_MUTEX.read().unwrap();

        #[repr(C, align(131072))]
        struct LargeAlign {
            x: u8,
        }

        assert_eq!(std::mem::align_of::<LargeAlign>(), 131072);

        let a = LargeAlign { x: 0 };
        let b = std::boxed::Box::<LargeAlign>::new_aligned(1, a).unwrap();
        let ptr = std::boxed::Box::into_raw(b);
        assert_eq!((ptr as usize) % std::mem::align_of::<LargeAlign>(), 0);
        let _ = unsafe { std::boxed::Box::from_raw(ptr) };
    }
}
