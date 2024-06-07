//! Allocate heap memory with user-specified alignment.

#![cfg_attr(all(not(feature = "std"), not(test)), no_std)]

#![warn(missing_docs)]
#![warn(rustdoc::missing_doc_code_examples)]
#![warn(rust_2018_idioms)]

extern crate alloc;


#[cfg(all(not(feature = "std"), not(test)))]
extern crate core as std;


/// Error type for custom errors of `AlignedBox`.
#[derive(Debug)]
pub enum AlignedBoxError {
    /// Too many elements. The requested size exceeds the maximum size for a slice.
    TooManyElements,
    /// Memory allocation failed. This is likely caused by an out of memory situation.
    OutOfMemory,
    /// Zero byte allocation are currently not supported by AlignedBox.
    ZeroAlloc,
    /// The alignment provided is not a power of 2
    InvalidAlign
}

#[cfg(feature = "std")]
impl std::error::Error for AlignedBoxError {}

impl std::fmt::Display for AlignedBoxError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            AlignedBoxError::TooManyElements => write!(f, "Too many elements for a slice."),
            AlignedBoxError::OutOfMemory => write!(f, "Memory allocation failed. Out of memory?"),
            AlignedBoxError::ZeroAlloc => write!(f, "Zero byte allocations not supported."),
            AlignedBoxError::InvalidAlign => write!(f, "Invalid alignment. Alignment must be a power of 2"),
        }
    }
}

/// A wrapper around `alloc::boxed::Box` which allows allocating aligned heap memory. An instance of
/// `AlignedBox<T>` consists of a `Box<T>` and the `alloc::alloc::Layout` that has been used to
/// allocate the referenced memory.
pub struct AlignedBox<T: ?Sized> {
    container: std::mem::ManuallyDrop<alloc::boxed::Box<T>>,
    layout: alloc::alloc::Layout,
}

impl<T: ?Sized> std::ops::Deref for AlignedBox<T> {
    type Target = T;

    fn deref(&self) -> &T {
        &self.container
    }
}

impl<T: ?Sized> std::ops::DerefMut for AlignedBox<T> {
    fn deref_mut(&mut self) -> &mut T {
        &mut self.container
    }
}

impl<T: ?Sized> Drop for AlignedBox<T> {
    fn drop(&mut self) {
        // SAFETY:
        // * self being dropped right now, self.container is not used after taking the Box out of it
        let container = unsafe { std::mem::ManuallyDrop::take(&mut self.container) };
        let ptr = alloc::boxed::Box::into_raw(container);
        // SAFETY:
        // * value behind ptr is valid for R/W, properly aligned and valid to drop
        // * dealloc is called with layout that has been used for allocation earlier
        unsafe {
            std::ptr::drop_in_place(ptr);
            alloc::alloc::dealloc(ptr as *mut u8, self.layout);
        }
    }
}

impl<T: Clone + ?Sized> Clone for AlignedBox<T> {
    fn clone(&self) -> Self {
        // SAFETY:
        // layout is certainly valid as it has already been used to create self
        let ptr = unsafe { alloc::alloc::alloc(self.layout) as *mut T };
        if ptr.is_null() {
            panic!("Failed to allocate memory for a clone of AlignedBox");
        }

        // SAFETY:
        // * The pointer is non-null, refers to properly sized and aligned memory and it is
        //   consumed such that it cannot be used from anywhere outside the Box. There is no
        //   aliasing with other pointers.
        let mut b = unsafe { AlignedBox::<T>::from_raw_parts(ptr, self.layout) };

        // *b is not a valid instance of T but uninitialized memory. We have to write to it without
        // dropping the old (invalid) value. Also the original value must not be dropped.
        // SAFETY:
        // * *b points to valid and properly aligned memory and clone() also provides us with
        //   a valid value.
        unsafe { std::ptr::write(&mut *b, (**self.container).clone()) };

        b
    }
}

impl<T: ?Sized> AlignedBox<T> {
    /// Decompose the `AlignedBox` into a raw pointer and the layout used during allocation.
    /// The caller of this function becomes responsible for proper deallocation of the memory
    /// behind the pointer. This can for example be done by reconstructing the `AlignedBox` using
    /// `AlignedBox::from_raw_parts`.
    pub fn into_raw_parts(mut from: AlignedBox<T>) -> (*mut T, alloc::alloc::Layout) {
        // SAFETY:
        // * from being consumed by this function, from.container is not used anymore afterwards
        let container = unsafe { std::mem::ManuallyDrop::take(&mut from.container) };
        let ptr = alloc::boxed::Box::into_raw(container);
        let layout = from.layout;
        std::mem::forget(from); // AlignedBox::drop() must not be called
        (ptr, layout)
    }

    /// Construct an `AlignedBox` from a raw pointer and the layout that has been used to allocate
    /// the memory behind that pointer. After calling this function, the pointer is owned by the
    /// `AlignedBox`. In particular, the memory will be freed when the `AlignedBox` is dropped.
    /// This is only safe if the given layout is the same as the one that was used during memory
    /// allocation.
    ///
    /// # Safety
    /// The function is unsafe because improper use can lead to issues, such as double-free. Also,
    /// behavior is undefined if the given layout does not correspond to the one used for
    /// allocation.
    pub unsafe fn from_raw_parts(ptr: *mut T, layout: alloc::alloc::Layout) -> AlignedBox<T> {
        let container = std::mem::ManuallyDrop::new(alloc::boxed::Box::from_raw(ptr));
        AlignedBox::<T> { container, layout }
    }
}

impl<T> AlignedBox<T> {
    fn allocate(
        mut alignment: usize,
        nelems: usize,
    ) -> std::result::Result<(*mut T, alloc::alloc::Layout), AlignedBoxError>
    {
        if alignment < std::mem::align_of::<T>() {
            alignment = std::mem::align_of::<T>();
        }

        let memsize: usize = std::mem::size_of::<T>() * nelems;
        if memsize == 0 {
            return Err(AlignedBoxError::ZeroAlloc);
        }

        let layout = alloc::alloc::Layout::from_size_align(memsize, alignment).map_err(|_| AlignedBoxError::InvalidAlign)?;

        // SAFETY:
        // * Requirements on layout are enforced by using from_size_align().
        let ptr = unsafe { alloc::alloc::alloc(layout) as *mut T };
        if ptr.is_null() {
            return Err(AlignedBoxError::OutOfMemory);
        }

        Ok((ptr, layout))
    }

    /// Store `value` of type `T` on the heap, making sure that it is aligned to a multiple of
    /// `alignment`. It is also checked if `alignment` is a valid alignment for type `T` or
    /// increased to a valid alignment otherwise.
    ///
    /// # Example
    /// Place value 17 of type `i32` on the heap, aligned to 64 bytes:
    /// ```
    /// use aligned_box::AlignedBox;
    ///
    /// let b = AlignedBox::<i32>::new(64, 17);
    /// ```
    pub fn new(
        alignment: usize,
        value: T,
    ) -> std::result::Result<AlignedBox<T>, AlignedBoxError> {
        let (ptr, layout) = AlignedBox::<T>::allocate(alignment, 1)?;

        // ptr is not a valid instance of T but uninitialized memory. We have to write to it without
        // dropping the old (invalid) value. Also the original value must not be dropped.
        // SAFETY:
        // * *b is valid for writes and properly aligned.
        unsafe { std::ptr::write(ptr, value) };

        // SAFETY:
        // * The pointer is non-null, refers to properly sized and aligned memory and it is
        //   consumed such that it cannot be used from anywhere outside the Box. It does not
        //   alias with any other pointer.
        let b = unsafe { AlignedBox::<T>::from_raw_parts(ptr, layout) };

        Ok(b)
    }
}

impl<T> AlignedBox<[T]> {
    // Create a AlignedBox<[T]> where each value is initialized by the given initializer
    // function.
    //
    // # SAFETY
    // The initializer function has to initialize the value behind the pointer without
    // reading or dropping the old uninitialized value, e.g., using std::ptr::write.
    #[allow(unused_unsafe)] // https://github.com/rust-lang/rfcs/pull/2585
    unsafe fn new_slice(
        alignment: usize,
        nelems: usize,
        initializer: impl Fn(*mut T),
    ) -> std::result::Result<AlignedBox<[T]>, AlignedBoxError> {
        // Make sure the requested amount of Ts will fit into a slice.
        let maxelems = (isize::MAX as usize) / std::mem::size_of::<T>();
        if nelems > maxelems {
            return Err(AlignedBoxError::TooManyElements);
        }

        let (ptr, layout) = AlignedBox::<T>::allocate(alignment, nelems)?;

        // Initialize values. The caller must ensure that initializer does not expect valid
        // values behind ptr.
        for i in 0..nelems {
            initializer(ptr.add(i));
        }

        // SAFETY:
        // * Requirements on ptr and nelems have been verified here and by AlignedBox::allocate():
        //   ptr is non-null, nelems does not exceed the maximum size.
        // * The referenced memory is not accessed through any other pointer.
        // * ptr points to nelems properly initialized values.
        let slice = unsafe { std::slice::from_raw_parts_mut(ptr, nelems) };

        // SAFETY:
        // * We only create a single Box from the given slice. The slice itself is consumed
        //   so that the referenced memory can be modified from now on.
        let b = unsafe { AlignedBox::<[T]>::from_raw_parts(slice, layout) };

        Ok(b)
    }

    // Resize the given AlignedBox<[T]> using alloc::alloc::realloc. Any newly allocated
    // elements will be initialized using the initializer. In case the slice is to be
    // shrunk but realloc fails, any elements that have been dropped are reinitialized
    // using the initializer.
    //
    // # SAFETY
    // The initializer function has to initialize the value behind the pointer without
    // reading or dropping the old uninitialized value, e.g., using std::ptr::write.
    #[allow(unused_unsafe)] // https://github.com/rust-lang/rfcs/pull/2585
    unsafe fn realloc(
        &mut self,
        nelems: usize,
        initializer: impl Fn(*mut T),
    ) -> std::result::Result<(), AlignedBoxError> {
        // Make sure the requested amount of Ts will fit into a slice.
        let maxelems = (isize::MAX as usize) / std::mem::size_of::<T>();
        if nelems > maxelems {
            return Err(AlignedBoxError::TooManyElements);
        }

        let memsize: usize = std::mem::size_of::<T>() * nelems;
        if memsize == 0 {
            return Err(AlignedBoxError::ZeroAlloc);
        }

        let old_nelems = self.container.len();
        let new_layout = alloc::alloc::Layout::from_size_align(memsize, self.layout.align()).map_err(|_| AlignedBoxError::InvalidAlign)?;

        // SAFETY:
        // * self.container is not used afterwards but re-assigned with a new
        //   instance of std::mem::ManuallyDrop<alloc::boxed::Box> in all possible cases.
        let b = unsafe { std::mem::ManuallyDrop::take(&mut self.container) };
        let ptr = alloc::boxed::Box::into_raw(b);

        // Drop any values that will be deallocated by realloc
        for i in nelems..old_nelems {
            // SAFETY:
            // * (*ptr)[i] is valid for R/W, properly aligned and valid to drop
            // * the element will not be read as it will either be re-initialized using
            //   std::ptr::write or the slice behind ptr will not be used anymore.
            std::ptr::drop_in_place(&mut (*ptr)[i]);
        }

        // SAFETY:
        // * ptr has been assigned by the same (that is: global) allocator
        // * layout has been used to allocate ptr
        // * new_size > 0 has been explicitly checked before
        // * due to the restrictions of a slice, memsize does not even overflow isize::MAX
        let new_ptr =
            unsafe { alloc::alloc::realloc(ptr as *mut u8, self.layout, memsize) as *mut T };

        if new_ptr.is_null() {
            // realloc failed. We need to restore a valid state and return an error.

            // Reinitialize previously dropped values. The caller must ensure that
            // initializer does not expect valid values behind ptr.
            for i in nelems..old_nelems {
                initializer(&mut (*ptr)[i]);
            }

            // SAFETY:
            // * Nobody owns the memory behind ptr right now.
            let b = unsafe { alloc::boxed::Box::from_raw(ptr) };
            self.container = std::mem::ManuallyDrop::new(b);
            return Err(AlignedBoxError::OutOfMemory);
        }

        // Initialize newly allocated values. The caller must ensure that
        // initializer does not expect valid values behind ptr.
        for i in old_nelems..nelems {
            initializer(new_ptr.add(i));
        }

        // Create a new slice, a new Box and update layout.
        // SAFETY:
        // * new_ptr is non-null, nelems does not exceed the maximum size.
        // * The referenced memory is not accessed via other pointers as long as slice exists.
        // * All nelems values behind new_ptr are properly initialized.
        let slice = unsafe { std::slice::from_raw_parts_mut(new_ptr, nelems) };
        // SAFETY:
        // * Nobody else references this slice or the ptr behind it.
        let b = unsafe { alloc::boxed::Box::from_raw(slice) };
        self.container = std::mem::ManuallyDrop::new(b);
        self.layout = new_layout;

        Ok(())
    }
}

impl<T: Default> AlignedBox<[T]> {
    /// Allocate memory for `nelems` values of type `T` on the heap, making sure that it is aligned
    /// to a multiple of `alignment`. All values are initialized by the default value of type `T`.
    /// It is also checked if `alignment` is a valid alignment for type `T` or increased to a
    /// valid alignment otherwise.
    ///
    /// # Example
    /// Allocate memory for 1024 values of type `f32` on the heap, aligned to 128 bytes. Values
    /// are initialized by their default value:
    /// ```
    /// use aligned_box::AlignedBox;
    ///
    /// let b = AlignedBox::<[f32]>::slice_from_default(128, 1024);
    /// ```
    pub fn slice_from_default(
        alignment: usize,
        nelems: usize,
    ) -> std::result::Result<AlignedBox<[T]>, AlignedBoxError> {
        // SAFETY:
        // * The initializer we pass to new_slice does not read or drop the value behind ptr.
        let b = unsafe {
            AlignedBox::<[T]>::new_slice(alignment, nelems, |ptr: *mut T| {
                let d = T::default(); // create new default value

                // Write to ptr without dropping the old value. Also d must not be dropped.
                // SAFETY: ptr points to valid and properly aligned memory.
                std::ptr::write(ptr, d)
            })?
        };

        Ok(b)
    }

    /// Resize allocated memory to fit `nelem` values of type `T`. The original alignment requested
    /// when creating the `AlignedBox` will still be obeyed. If `nelem` is larger than the current
    /// amount of stored elements, the newly allocated elements will be initialized with the
    /// default value of type `T`. If `nelem` is smaller than the current amount of stored elements,
    /// any excess elements will be dropped. In case realloc fails, those dropped elements will be
    /// reinitialized with the default value of type `T`.
    ///
    /// # Example
    /// Create an AlignedBox::<[f32]> with 1024 elements. Extend to 2048 elements. Initialize all new
    /// elements by the default value of f32, i.e., 0.0.
    /// ```
    /// use aligned_box::AlignedBox;
    ///
    /// let mut b = AlignedBox::<[f32]>::slice_from_default(128, 1024).unwrap();
    /// b.realloc_with_default(2048);
    /// ```
    pub fn realloc_with_default(
        &mut self,
        nelems: usize,
    ) -> std::result::Result<(), AlignedBoxError> {
        // SAFETY:
        // * The initializer we pass to new_slice does not read or drop the value behind ptr.
        unsafe {
            self.realloc(nelems, |ptr: *mut T| {
                let d = T::default(); // create new default value

                // Write to ptr without dropping the old value. Also d must not be dropped.
                // SAFETY: ptr points to valid and properly aligned memory.
                std::ptr::write(ptr, d)
            })?
        };

        Ok(())
    }
}

impl<T: Copy> AlignedBox<[T]> {
    /// Allocate memory for `nelems` values of type `T` on the heap, making sure that it is aligned
    /// to a multiple of `alignment`. All values are initialized by copies of `value`. It is also
    /// checked if `alignment` is a valid alignment for type `T` or increased to a
    /// valid alignment otherwise.
    ///
    /// # Example
    /// Allocate memory for 1024 values of type `f32` on the heap, aligned to 128 bytes. All values
    /// are initialized with PI:
    /// ```
    /// use aligned_box::AlignedBox;
    ///
    /// let b = AlignedBox::<[f32]>::slice_from_value(128, 1024, std::f32::consts::PI);
    pub fn slice_from_value(
        alignment: usize,
        nelems: usize,
        value: T,
    ) -> std::result::Result<AlignedBox<[T]>, AlignedBoxError> {
        // SAFETY:
        // * The initializer we pass to new_slice does not read or drop the value behind ptr.
        let b = unsafe {
            AlignedBox::<[T]>::new_slice(alignment, nelems, |ptr: *mut T| {
                // T is Copy and therefore also !Drop. We can simply copy from value to ptr
                // without worrying about the old value being dropped.
                *ptr = value;
            })?
        };

        Ok(b)
    }

    /// Resize allocated memory to fit `nelem` values of type `T`. The original alignment requested
    /// when creating the `AlignedBox` will still be obeyed. If `nelem` is larger than the current
    /// amount of stored elements, the newly allocated elements will be initialized with the
    /// value given as argument to this function. If `nelem` is smaller than the current amount of
    /// stored elements, any excess elements will be dropped. In case realloc fails, those dropped
    /// elements will be reinitialized with the value given to this function.
    ///
    /// # Example
    /// Create an AlignedBox::<[f32]> with 1024 elements. Extend to 2048 elements. Initialize all new
    /// elements by 3.14.
    /// ```
    /// use aligned_box::AlignedBox;
    ///
    /// let mut b = AlignedBox::<[f32]>::slice_from_default(128, 1024).unwrap();
    /// b.realloc_with_value(2048, 3.14);
    /// ```
    pub fn realloc_with_value(
        &mut self,
        nelems: usize,
        value: T,
    ) -> std::result::Result<(), AlignedBoxError> {
        // SAFETY:
        // * The initializer we pass to new_slice does not read or drop the value behind ptr.
        unsafe {
            self.realloc(nelems, |ptr: *mut T| {
                // T is Copy and therefore also !Drop. We can simply copy from value to ptr
                // without worrying about the old value being dropped.
                *ptr = value;
            })?
        };

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::AlignedBox;
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
            let b = AlignedBox::<[u8]>::slice_from_value(*a, 42, 0).unwrap();
            assert_eq!((b.as_ptr() as usize) % *a, 0);
        }
    }

    #[test]
    fn size() {
        let _m = SEQ_TEST_MUTEX.read().unwrap();

        let sizes = [1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096];

        for s in sizes.iter() {
            let b = AlignedBox::<[u8]>::slice_from_value(1, *s, 0).unwrap();
            assert_eq!(b.len(), *s);
        }
    }

    // This is a probabilistic test and it relies on re-use of addresses by the standard library or
    // the operating system. It does not work with address sanitizer enabled, so it is disabled by
    // default. It can be run via:
    //  `cargo t free -- --ignored`
    #[test]
    #[ignore]
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
            let b = AlignedBox::<[u8]>::slice_from_value(alignment, size, 0).unwrap();
            addrs.insert(b.as_ptr() as usize);
        }
        assert_ne!(addrs.len(), ATTEMPTS);
    }

    #[test]
    fn drop_contained() {
        let _m = SEQ_TEST_MUTEX.read().unwrap();

        static COUNTER: std::sync::atomic::AtomicI32 = std::sync::atomic::AtomicI32::new(0);

        struct Tracking {
            #[allow(dead_code)]
            something: i32,
        }
        impl Tracking {
            pub fn new() -> Tracking {
                COUNTER.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                Tracking { something: 7 }
            }
        }
        impl Drop for Tracking {
            fn drop(&mut self) {
                COUNTER.fetch_sub(1, std::sync::atomic::Ordering::Relaxed);
            }
        }

        impl Default for Tracking {
            fn default() -> Tracking {
                Tracking::new()
            }
        }

        let b = AlignedBox::new(128, Tracking::new()).unwrap();
        drop(b);

        let mut b = AlignedBox::<[Tracking]>::slice_from_default(128, 3).unwrap();

        b.realloc_with_default(1).unwrap();
        assert_eq!(COUNTER.load(std::sync::atomic::Ordering::Relaxed), 1);

        drop(b);
        assert_eq!(COUNTER.load(std::sync::atomic::Ordering::Relaxed), 0);
    }

    #[test]
    fn aliasing() {
        let _m = SEQ_TEST_MUTEX.read().unwrap();

        let size = 1024; // 1KB

        let b1 = AlignedBox::<[u8]>::slice_from_value(1, size, 0).unwrap();
        let b2 = AlignedBox::<[u8]>::slice_from_value(1, size, 0).unwrap();
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

        let mut b = AlignedBox::<[f32]>::slice_from_value(128, 1024, std::f32::consts::PI).unwrap();
        for i in b.iter() {
            assert_eq!(*i, std::f32::consts::PI);
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

        let b = AlignedBox::<[SomeVaryingDefault]>::slice_from_default(128, 1024).unwrap();
        assert_eq!(SomeVaryingDefault::default().i, 1024);
        for (ctr, i) in b.iter().enumerate() {
            assert_eq!(i.i, ctr as i32);
        }
    }

    #[test]
    fn move_sem() {
        let _m = SEQ_TEST_MUTEX.read().unwrap();

        let v = vec![1, 2, 3];
        let b = AlignedBox::new(128, v).unwrap();
        assert_eq!(*b, vec![1, 2, 3]);
    }

    #[test]
    fn copy_sem() {
        let _m = SEQ_TEST_MUTEX.read().unwrap();

        let v = 17;
        let _ = AlignedBox::new(128, v).unwrap();
        let _ = AlignedBox::slice_from_value(128, 1024, v).unwrap();
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

        let a = LargeAlign { x: 28 };
        let b = AlignedBox::<LargeAlign>::new(1, a).unwrap();
        let (ptr, layout) = AlignedBox::into_raw_parts(b);
        assert_eq!((ptr as usize) % std::mem::align_of::<LargeAlign>(), 0);
        let _ = unsafe { AlignedBox::from_raw_parts(ptr, layout) };
    }

    #[test]
    fn clone() {
        let _m = SEQ_TEST_MUTEX.read().unwrap();

        let mut b = AlignedBox::new(128, vec![47, 11]).unwrap();
        let mut another_b = b.clone();

        assert_eq!(*b, *another_b);

        b[0] = 48;
        another_b[1] = 12;

        assert_eq!(b[0], 48);
        assert_eq!(b[1], 11);
        assert_eq!(another_b[0], 47);
        assert_eq!(another_b[1], 12);
    }

    #[test]
    fn realloc_with_default() {
        let alignment = 1024 * 1024; // 1MB

        let mut b = AlignedBox::<[usize]>::slice_from_default(alignment, 10).unwrap();
        for i in 0..10 {
            b[i] = i;
        }

        b.realloc_with_default(20).unwrap();

        for i in 0..10 {
            assert_eq!(b[i], i);
        }
        let def: usize = Default::default();
        for i in 10..20 {
            assert_eq!(b[i], def);
        }

        b.realloc_with_default(5).unwrap();
        for i in 0..5 {
            assert_eq!(b[i], i);
        }
    }

    #[test]
    fn realloc_with_value() {
        let alignment = 1024 * 1024; // 1MB

        let mut b = AlignedBox::<[usize]>::slice_from_value(alignment, 10, 3).unwrap();

        b.realloc_with_value(20, 7).unwrap();

        for i in 0..10 {
            assert_eq!(b[i], 3);
        }
        for i in 10..20 {
            assert_eq!(b[i], 7);
        }

        b.realloc_with_default(5).unwrap();
        for i in 0..5 {
            assert_eq!(b[i], 3);
        }
    }

    #[test]
    #[should_panic]
    fn shrink() {
        let alignment = 1024 * 1024; // 1MB

        let mut b = AlignedBox::<[usize]>::slice_from_default(alignment, 10).unwrap();
        for i in 0..10 {
            b[i] = i;
        }

        b.realloc_with_default(5).unwrap();
        for i in 0..6 {
            assert_eq!(b[i], i);
        }
    }

    // Manual test to check for any leaks in new(), clone() and drop(). Run via
    //  `RUST_MIN_STACK=120000000 RUST_MAX_STACK=120000000 cargo t --release clone_rss -- --nocapture --ignored`
    // and at the same time watch the process memory use.
    #[test]
    #[ignore]
    fn clone_rss() {
        const SIZE: usize = 1024 * 1024 * 100; // 100MiB
        const DELAY: u64 = 4;

        #[repr(C)]
        #[repr(align(1))]
        #[derive(Copy, Clone)]
        union BigThing {
            a: u32,
            b: [u8; SIZE],
        }

        assert_eq!(std::mem::size_of::<BigThing>(), SIZE);

        let x = BigThing { a: 7 };
        println!("100"); // Stack of this function
        std::thread::sleep(std::time::Duration::from_secs(DELAY));

        let b1 = AlignedBox::new(64, x).unwrap();
        println!("200"); // Stack of this function + 1 element on heap
        std::thread::sleep(std::time::Duration::from_secs(DELAY));

        let b2 = b1.clone();
        println!("300"); // Stack of this function + 2 elements on heap
        std::thread::sleep(std::time::Duration::from_secs(DELAY));

        drop(b2);
        println!("200"); // Stack of this function + 1 element on heap
        std::thread::sleep(std::time::Duration::from_secs(DELAY));

        drop(b1);
        println!("100"); // Stack of this function
        std::thread::sleep(std::time::Duration::from_secs(DELAY));
    }
}
