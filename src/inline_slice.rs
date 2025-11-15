use std::{borrow::Borrow, hash::Hash, ops::Deref};


#[repr(C)]
struct SliceData<T> {
    len: usize,
    data: [T; 0],
}

pub struct InlineSlice<T> {
    data: SliceData<T>,
    _opaque: OpaqueContents 
}

unsafe extern "C" {
    type OpaqueContents;
}

impl<T> InlineSlice<T> {
    pub fn empty() -> &'static Self {
        #[repr(align(64))]
        struct MaxAlign;

        static EMPTY_DATA: SliceData<MaxAlign> = SliceData { len: 0, data: [] };

        return unsafe { &*(std::ptr::addr_of!(EMPTY_DATA) as *const Self) };
    }

    pub fn alloc_in_arena<'r>(arena: &'r bumpalo::Bump, slice: &[T]) -> &'r Self
    where
        T: Copy
    {
        let (layout, _offset) = std::alloc::Layout::new::<SliceData<T>>()
            .extend(std::alloc::Layout::for_value(slice))
            .unwrap();
        let ptr = arena.alloc_layout(layout).as_ptr() as *mut InlineSlice<T>;

        unsafe {
            (*ptr).data.len = slice.len();
            (*ptr).data.data.as_mut_ptr()
                .copy_from_nonoverlapping(slice.as_ptr(), slice.len());

            &*ptr
        }
    }

    pub fn as_slice(&self) -> &[T] {
        let data = self.data.data.as_ptr();
        unsafe { std::slice::from_raw_parts(data, self.data.len) }
    }
}

impl<T: std::fmt::Debug> std::fmt::Debug for InlineSlice<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        <[T] as std::fmt::Debug>::fmt(self.as_slice(), f)
    }
}

impl<T> Hash for InlineSlice<T> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        state.write_usize(self.as_ptr().addr());
    }
}

impl<T> PartialEq for InlineSlice<T> {
    fn eq(&self, other: &Self) -> bool {
        return std::ptr::eq(self.as_ptr(), other.as_ptr());
    }
}

impl<T> Eq for InlineSlice<T> {}

impl<T> Deref for InlineSlice<T> {
    type Target = [T];

    fn deref(&self) -> &Self::Target {
        self.as_slice()
    }
}

impl<'tcx, T> Borrow<[T]> for &'tcx InlineSlice<T> {
    fn borrow(&self) -> &[T] {
        self.as_slice()
    }
}

