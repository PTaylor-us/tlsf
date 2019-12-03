#[cfg(not(any(
    feature = "FLI6",
    feature = "FLI7",
    feature = "FLI8",
    feature = "FLI9",
    feature = "FLI10",
    feature = "FLI11",
    feature = "FLI12",
    feature = "FLI13",
    feature = "FLI14",
    feature = "FLI15",
    feature = "FLI16",
)))]
compile_error!("you must enable one of the 'FLI*' features to compile this crate");

/// First Level Index (FLI)
#[cfg(feature = "FLI6")]
pub const USER_FLI: u8 = 6;

/// First Level Index (FLI)
#[cfg(feature = "FLI7")]
pub const USER_FLI: u8 = 7;

/// First Level Index (FLI)
#[cfg(feature = "FLI8")]
pub const USER_FLI: u8 = 8;

/// First Level Index (FLI)
#[cfg(feature = "FLI9")]
pub const USER_FLI: u8 = 9;

/// First Level Index (FLI)
#[cfg(feature = "FLI10")]
pub const USER_FLI: u8 = 10;

/// First Level Index (FLI)
#[cfg(feature = "FLI11")]
pub const USER_FLI: u8 = 11;

/// First Level Index (FLI)
#[cfg(feature = "FLI12")]
pub const USER_FLI: u8 = 12;

/// First Level Index (FLI)
#[cfg(feature = "FLI13")]
pub const USER_FLI: u8 = 13;

/// First Level Index (FLI)
#[cfg(feature = "FLI14")]
pub const USER_FLI: u8 = 14;

/// First Level Index (FLI)
#[cfg(feature = "FLI15")]
pub const USER_FLI: u8 = 15;

/// First Level Index (FLI)
#[cfg(feature = "FLI16")]
pub const USER_FLI: u8 = 16;

// NOTE USER_FLI MUST be equal or less than 16 because we don't support block sizes greater than `1
// << 16`
#[allow(dead_code)]
const ASSERT0: [(); 0 - !(USER_FLI <= 16) as usize] = [];

/// Maximum block size that can be managed by the allocator
pub const MAX_BLOCK_SIZE: u16 = ((1u32 << USER_FLI) - ALIGN_SIZE as u32) as u16;

/// Maximum block size that can be requested from the allocator
pub const MAX_REQUEST_SIZE: u16 = ((1u32 << USER_FLI) - (1 << (USER_FLI - SLI_LOG2))) as u16;

// All blocks are 4-byte aligned and their sizes are always multiple of 4
pub const ALIGN_SIZE_LOG2: u8 = 2;
/// All block sizes are multiple of this number; this number is also the minimum alignment of all
/// allocations
pub const ALIGN_SIZE: u8 = 1 << ALIGN_SIZE_LOG2;

pub const SLI_LOG2: u8 = 4;
/// Second Level Index (FLI)
pub const SLI: u8 = 1 << SLI_LOG2;

// For small values of `fl` we would have to split sizes in the range of e.g. `4..8` into `SLI`
// smaller ranges. That doesn't make much sense so instead we merge all the rows with `fl <
// FLI_SHIFT` into a single row.
pub const FLI_SHIFT: u8 = SLI_LOG2 + ALIGN_SIZE_LOG2;
pub const FLI: u8 = USER_FLI - FLI_SHIFT + 1;

// NOTE FLI MUST be equal or less than 16 because `Tlsf.fl_bitmap` is a `u16`
#[allow(dead_code)]
const ASSERT1: [(); 0 - !(FLI <= 16) as usize] = [];

// NOTE FLI can't be smaller than `1` or `free_lists` would be a zero-element array
#[allow(dead_code)]
const ASSERT2: [(); 0 - !(FLI >= 1) as usize] = [];

/// Block with sizes below this threshold will always have FL = 0; they'll all go into the merged
/// row
pub const SIZE_THRESHOLD: u16 = 1 << FLI_SHIFT;

/// If the excess space has at least this many *usable* bytes then this block should be split
pub const SPLIT_THRESHOLD: u16 = 1 * ALIGN_SIZE as u16;
