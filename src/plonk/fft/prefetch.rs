extern crate prefetch;

use self::prefetch::prefetch::*;

#[inline(always)]
pub(crate) fn prefetch_index<T>(slice: &[T], idx: usize) {
    let p: *const T = &slice[idx];
    prefetch::<Write, High, Data, _>(p);
}

#[inline(always)]
pub(crate) fn prefetch_index_read<T>(slice: &[T], idx: usize) {
    let p: *const T = &slice[idx];
    prefetch::<Read, High, Data, _>(p);
}