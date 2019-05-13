use core::{
    mem,
    ops::{Add, Rem, Sub},
};

use crate::{consts, Index};

/// Find Last Set
pub fn fls(size: u16) -> u8 {
    8 * mem::size_of::<u16>() as u8 - size.leading_zeros() as u8 - 1
}

// Find First Set
pub fn ffs(x: u16) -> u8 {
    x.trailing_zeros() as u8
}

pub(crate) fn mapping_insert(size: u16) -> Index {
    debug_assert_eq!(size % u16::from(consts::ALIGN_SIZE), 0);
    debug_assert!(size <= consts::MAX_BLOCK_SIZE);

    mapping_insert_(size)
}

pub(crate) fn mapping_insert_(size: u16) -> Index {
    let mut fl;
    let sl;
    if size < consts::SIZE_THRESHOLD {
        fl = 0;
        sl = (size >> consts::ALIGN_SIZE_LOG2) as u8;
    } else {
        fl = fls(size);
        sl = (size >> (fl - consts::SLI_LOG2)) as u8 ^ consts::SLI;
        fl -= consts::FLI_SHIFT - 1;
    }

    debug_assert!(fl < consts::FLI);
    debug_assert!(sl < consts::SLI);

    Index { fl, sl }
}

// Computes the index where we are likely to find a block of at least `size` bytes
pub(crate) fn mapping_search(size: u16) -> Index {
    debug_assert_eq!(size % u16::from(consts::ALIGN_SIZE), 0);
    debug_assert!(size <= consts::MAX_REQUEST_SIZE);

    mapping_search_(size)
}

pub(crate) fn mapping_search_(mut size: u16) -> Index {
    if size >= consts::SIZE_THRESHOLD {
        size += (1 << (fls(size) - consts::SLI_LOG2)) - 1;
    }

    mapping_insert_(size)
}

pub fn round_down<T>(x: T, multiple: T) -> T
where
    T: Copy + Rem<T, Output = T> + PartialEq + Sub<T, Output = T>,
{
    let zero = unsafe { mem::zeroed() };
    let rem = x % multiple;
    if rem == zero {
        x
    } else {
        x - rem
    }
}

pub fn round_up<T>(x: T, multiple: T) -> (/* x */ T, /* rem */ T)
where
    T: Add<T, Output = T> + Copy + Rem<T, Output = T> + PartialEq + Sub<T, Output = T>,
{
    let zero = unsafe { mem::zeroed() };
    let rem = x % multiple;
    if rem == zero {
        (x, zero)
    } else {
        (x + (multiple - rem), rem)
    }
}
