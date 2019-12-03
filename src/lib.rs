//! A Two Level Segregated Fit (TLSF) allocator optimized for memory-constrained systems
//!
//! # Features
//!
//! - Bounded execution time for the `alloc` and `dealloc` operations (WCET analysis friendly)
//!
//! - Optimized memory footprint (*fixed* cost)
//!
//! - Only 4 bytes of metadata (overhead) per allocation (*variable* cost)
//!
//! - The "size" of the allocator can be configured at compile time (pay for what you use)
//!
//! # Example
//!
//! ``` ignore
//! #![no_main]
//! #![no_std]
//!
//! use core::{
//!     alloc::Layout,
//!     sync::atomic::{AtomicUsize, Ordering},
//! };
//!
//! // see https://github.com/japaric/alloc-many
//! // or use the (still) unstable `alloc` crate
//! use alloc_many_collections::vec::Vec;
//! // or use the unstable `#[global_allocator]` / `#[alloc_error_handler]` features
//! use alloc_many::{oom, Alloc};
//! use cortex_m::asm;
//! use cortex_m_rt::entry;
//! use panic_halt as _; // panic handler
//! use spin::Mutex; // don't use this in interrupts because it can deadlock
//! use tlsf::{Tlsf, MAX_BLOCK_SIZE};
//!
//! static ALLOC: Mutex<Tlsf> = Mutex::new(Tlsf::new());
//!
//! // An allocator singleton
//! struct A;
//!
//! // or use the `#[alloc_many::allocator]` attribute
//! unsafe impl Alloc for A {
//!     unsafe fn alloc(layout: Layout) -> *mut u8 {
//!         ALLOC.lock().alloc(layout)
//!     }
//!
//!     unsafe fn dealloc(ptr: *mut u8, _: Layout) {
//!         ALLOC.lock().dealloc(ptr)
//!     }
//!
//!     unsafe fn realloc(
//!         ptr: *mut u8,
//!         layout: Layout,
//!         new_size: usize,
//!     ) -> *mut u8 {
//!         ALLOC.lock().realloc(ptr, layout, new_size)
//!     }
//!
//!     unsafe fn alloc_zeroed(layout: Layout) -> *mut u8 {
//!         ALLOC.lock().alloc_zeroed(layout)
//!     }
//! }
//!
//! #[repr(align(4))]
//! struct Aligned<T>(T);
//!
//! #[entry]
//! fn main() -> ! {
//!     // NOTE(Aligned) align this buffer to `tlsf::ALIGN_SIZE` bytes to avoid padding
//!     // NOTE(SIZE) use a size multiple of `MAX_BLOCK_SIZE` to maximize coalescing
//!     // NOTE(bss) initialize this to all zeros to put `M` in the `.bss` linker
//!     //           section and close to `tlsf::ANCHOR`
//!     static mut M: Aligned<[u8; MAX_BLOCK_SIZE as usize]> =
//!         Aligned([0; MAX_BLOCK_SIZE as usize]);
//!
//!     ALLOC.lock().grow(&mut M.0);
//!
//!     // allocate a vector in allocator `A`
//!     let mut xs: Vec<A, _> = Vec::new();
//!     loop {
//!         // push until we run out of memory (see `oom` function below)
//!         xs.push(X.fetch_add(1, Ordering::Relaxed) as u8);
//!     }
//! }
//!
//! static X: AtomicUsize = AtomicUsize::new(0);
//!
//! #[oom] // instead of the unstable `#[alloc_error_handler]`
//! fn oom(_: Layout) -> ! {
//!     // check `X` at this point
//!     asm::bkpt();
//!
//!     loop {}
//! }
//! ```
//!
//! # Cargo features
//!
//! The TLSF allocator has two main parameters associated to it: the First Level Index (FLI) and the
//! Second Level Index (SLI). In a nutshell: the SLI has an effect on fragmentation and the FLI
//! controls how big the memory blocks managed by the allocator can get.  See [2][1] for the full
//! details.
//!
//! The greater the value of the SLI the lesser the fragmentation. This crate hard codes the value
//! of SLI to the recommended value of `4`.
//!
//! The bigger the value of FLI the bigger the memory blocks you can request from the allocator.
//! However, increasing the FLI also increases the memory footprint of the allocator. This crate
//! lets you pick the the value of FLI through Cargo features named: `FLI6`, `FLI7`, ..., `FLI16`.
//! The table below shows the footprint of `Tlsf` and the maximum block size you can request from it
//! for every supported value of `FLI`.
//!
//! |FLI|`size_of(Tlsf)`|`MAX_REQUEST_SIZE`|`MAX_BLOCK_SIZE`|
//! |---|---------------|------------------|----------------|
//! |6  |36             |60                |60              |
//! |7  |70             |120               |124             |
//! |8  |104            |240               |252             |
//! |9  |138            |480               |508             |
//! |10 |172            |960               |1,020           |
//! |11 |206            |1,920             |2,044           |
//! |12 |240            |3,840             |4,092           |
//! |13 |274            |7,680             |8,188           |
//! |14 |308            |15,360            |16,380          |
//! |15 |342            |30,720            |32,764          |
//! |16 |376            |61,440            |65,532          |
//!
//! *All sizes are in bytes*
//!
//! `MAX_REQUEST_SIZE` is the maximum block size with alignment of `ALIGN_SIZE` bytes (or less) that
//! can be requested from the allocator. Requesting a bigger size will immediately result in OOM. If
//! you request a block with alignment greater than `ALIGN_SIZE` bytes then `MAX_REQUEST_SIZE` will
//! effectively be lower because the allocator may need to insert padding to satisfy the alignment
//! requirement.
//!
//! `MAX_BLOCK_SIZE` is the maximum size of any individual memory block managed by the allocator.
//! This number is **not** the maximum amount of memory the allocator can manage but you should
//! consider it when you use [`Tlsf.grow`] because the allocator will split the given slice into
//! blocks of `MAX_BLOCK_SIZE` bytes if it's too big. These initial blocks -- they are more like
//! regions -- will never be coalesced by the allocator; also, the allocator will *not* coalesce
//! blocks from different regions even if they are next to each other.
//!
//! [`Tlsf.grow`]: struct.Tlsf.html#method.grow
//!
//! # Limitations
//!
//! To minimize the memory footprint of the allocator this implementation internally uses 16-bit
//! *offsets* instead of pointers (halves memory footprint on a 32-bit machine). These offsets are
//! computed from the address of the `tlsf::ANCHOR` variable. This decision limits the *location* of
//! the memory blocks that the allocator can manage to those whose address are within `±(1 << 17)`
//! bytes (±128 KiBi) of the `tlsf::ANCHOR` variable, will be located in the output `.bss` linker
//! section.
//!
//! # Benchmarks
//!
//! Platform: ARM Cortex-M3 @ 8 MHz (zero Flash wait cycles).
//!
//! Compilation flags: `opt-level=3`, `lto=true`, `codegen-units=1`
//!
//! Cargo features: `+FLI8`
//!
//! |Code            |Time|
//! |----------------|----|
//! |`Tlsf.alloc`    |    |
//! |- no split      |83  |
//! |- split         |159 |
//! |- split & pad   |294 |
//! |`Tlsf.dealloc`  |    |
//! |- no merge      |80  |
//! |- merge next    |203 |
//! |- merge previous|201 |
//! |- merge both    |263 |
//!
//! *All times are in core clock cycles (1 core clock cycle = 125 ns)*
//!
//! # Minimum Supported Rust Version (MSRV)
//!
//! This crate is guaranteed to compile on stable Rust 1.34 and up. It *might* compile on older
//! versions but that may change in any new patch release.
//!
//! # References
//!
//! 1. [Implementation of a constant-time dynamic storage allocator][0]
//! 2. [TLSF: a New Dynamic Memory Allocator for Real-Time Systems][1]
//!
//! [0]: http://www.gii.upv.es/tlsf/files/spe_2008.pdf
//! [1]: http://wks.gii.upv.es/tlsf/files/ecrts04_tlsf_0.pdf

#![cfg_attr(not(test), no_std)]
#![deny(missing_docs)]
#![deny(rust_2018_compatibility)]
#![deny(rust_2018_idioms)]
#![deny(warnings)]

use core::{alloc::Layout, cmp, convert::TryFrom, fmt, marker::PhantomData, ptr::NonNull};

#[cfg(feature = "ufmt")]
use ufmt::derive::uDebug;

pub use crate::consts::{ALIGN_SIZE, MAX_BLOCK_SIZE, MAX_REQUEST_SIZE, SLI, USER_FLI as FLI};
use crate::{
    block::{Block, BlockHeader},
    free_block::{FreeBlock, FreeBlockHeader},
};

#[macro_use]
mod macros;
mod block;
mod consts;
mod free_block;
#[cfg(test)]
mod tests;
mod util;

type Offset = core::num::NonZeroI16;

/// The Two Level Segregated Fit (TLSF) allocator
pub struct Tlsf {
    fl_bitmap: u16,
    sl_bitmaps: [u16; consts::FLI as usize],
    free_lists: [[Option<Offset>; consts::SLI as usize]; consts::FLI as usize],
}

/// A 1-byte struct that's `ALIGN_SIZE`-bytes aligned
#[repr(align(4))]
pub struct Anchor(u8);

/// All internal *offsets* are relative to this "anchor"
///
/// This `ANCHOR` will be placed in the output `.bss` linker section
#[link_section = ".bss.TLSF_ANCHOR"]
pub static ANCHOR: Anchor = Anchor(0);

fn anchor() -> *mut u8 {
    let anchor = &ANCHOR as *const Anchor as *mut u8;
    debug_assert_eq!(anchor as usize % usize::from(consts::ALIGN_SIZE), 0);
    anchor
}

impl Tlsf {
    /* Constructors */
    /// Constructs a new, empty `Tlsf` allocator
    pub const fn new() -> Self {
        Self {
            fl_bitmap: 0,
            sl_bitmaps: [0; consts::FLI as usize],
            free_lists: [[None; consts::SLI as usize]; consts::FLI as usize],
        }
    }

    /* Public API */
    /// Adds a `memory` chunk to the `Tlsf` memory pool
    ///
    /// This method returns the amount of *usable* memory in bytes
    ///
    /// Note that the given `memory` chunk may not be fully utilized due to alignment requirements.
    /// Align `memory` to `ALIGN_SIZE` bytes to avoid any padding.
    ///
    /// Also note that `memory` must be located within 128 KiBi of the [`tlsf::ANCHOR`] variable,
    /// which will be located in the output `.bss` linker section. Passing a `memory` chunk outside
    /// this address range will result in it being discarded and the `grow` call will return `0`.
    ///
    /// [`tlsf::ANCHOR`]: static.ANCHOR.html
    ///
    /// Finally note that the allocator will split `memory` into blocks of `MAX_BLOCK_SIZE` bytes if
    /// it's bigger than `MAX_BLOCK_SIZE`. These initial blocks, or *regions*, will *never* be
    /// coalesced at runtime; also, blocks from different regions will *not* be coalesced even if
    /// they are next to each other.
    ///
    /// To get the most of `memory` use the initialization method shown in the
    /// [example](index.html#example)
    pub fn extend(&mut self, memory: &'static mut [u8]) -> usize {
        unsafe {
            let ptr = memory.as_mut_ptr();
            let mut len = memory.len();

            let anchor = anchor() as isize;
            if ((ptr as isize).wrapping_sub(anchor))
                < (isize::from(i16::min_value()) << consts::ALIGN_SIZE)
                || ((ptr.add(len) as isize).wrapping_sub(anchor))
                    > (isize::from(i16::max_value()) << consts::ALIGN_SIZE)
            {
                // can't use this memory because it's too far away from the `anchor`
                return 0;
            }

            // align the pointer
            let (ptr, offset) =
                util::round_up(memory.as_ptr() as usize, usize::from(consts::ALIGN_SIZE));
            len -= offset;

            let mut ptr = ptr as *mut u8;
            let mut total = 0;
            while len >= usize::from(BlockHeader::SIZE + consts::ALIGN_SIZE) {
                let size = if len > usize::from(MAX_BLOCK_SIZE) + usize::from(BlockHeader::SIZE) {
                    consts::MAX_BLOCK_SIZE + u16::from(BlockHeader::SIZE)
                } else {
                    util::round_down(len, usize::from(consts::ALIGN_SIZE)) as u16
                };

                let fb = FreeBlock::from_parts(ptr as *mut _, size, true);
                total += usize::from(fb.usable_size());
                self.insert(fb);

                len -= usize::from(size);
                ptr = ptr.add(usize::from(size));
            }

            total
        }
    }

    /// Returns a pointer meeting the size and alignment guarantees of `layout`.
    ///
    /// See [`core::alloc::Alloc.alloc`][0] for more details.
    ///
    /// [0]: https://doc.rust-lang.org/core/alloc/trait.Alloc.html#tymethod.alloc
    ///
    /// This method has a bounded execution time, meaning that it will complete within some time `T`
    /// regardless of the input and the state of the allocator -- the implementation of this method
    /// contains no loops, recursion or panicking branches.
    pub unsafe fn alloc(&mut self, layout: Layout) -> Result<NonNull<u8>, ()> {
        let align = layout.align();
        let size = layout.size();

        // fast path for zero sized types like `()`
        if size == 0 {
            return Ok(NonNull::new_unchecked(align as *mut u8));
        }

        let align = if let Ok(align) = u16::try_from(align) {
            align
        } else {
            return Err(());
        };

        // assumptions
        debug_assert_eq!(size % usize::from(align), 0);
        debug_assert_eq!(consts::ALIGN_SIZE % BlockHeader::SIZE, 0);

        // increase the size to satisfy alignment requirements; also block sizes are always a
        // multiple of `ALIGN_SIZE`
        let size = if align <= u16::from(consts::ALIGN_SIZE) {
            util::round_up(size, usize::from(consts::ALIGN_SIZE)).0
        } else {
            // In the worst case scenario the pointer into usable memory will be a multiple of
            // `align` plus `BHS`. Thus we'll need a padding block of at least `K * align - BHS`
            // where K can be any non-zero integer. However, padding blocks, which are free blocks,
            // can't be smaller than `FBHS` so we need to pick `K` such that `K * align - BHS >=
            // FBHS`.
            //
            // The following logic likely only makes sense for the current values of BHS (4) and
            // FBHS (8)
            if align - u16::from(BlockHeader::SIZE) < u16::from(FreeBlockHeader::SIZE) {
                size + 2 * usize::from(align) - usize::from(BlockHeader::SIZE)
            } else {
                size + usize::from(align) - usize::from(BlockHeader::SIZE)
            }
        };

        if size > usize::from(consts::MAX_REQUEST_SIZE) {
            return Err(());
        }

        let size = size as u16;
        let guess = util::mapping_search(size);

        let hit = if let Some(hit) = self.find_suitable_block(guess) {
            hit
        } else {
            // OOM
            return Err(());
        };

        // remove head from free list
        let mut fb = self.remove_head(hit);

        // head should be unlinked
        debug_assert!(fb.next_free().is_none());
        debug_assert!(fb.prev_free().is_none());

        // create a padding block, if necessary
        if align > u16::from(consts::ALIGN_SIZE) {
            let rem = ((fb.header() as usize + usize::from(BlockHeader::SIZE)) % usize::from(align))
                as u16;

            if rem != 0 {
                let mut padding = align - rem;

                // padding blocks are free blocks so they can't be smaller than the free block
                // header
                if padding < u16::from(FreeBlockHeader::SIZE) {
                    padding += align;
                }

                let (left, right) = fb.split(padding);

                // both parts should be unlinked
                debug_assert!(left.next_free().is_none());
                debug_assert!(left.prev_free().is_none());
                debug_assert!(right.next_free().is_none());
                debug_assert!(right.prev_free().is_none());

                self.insert(left);
                fb = right;
            }
        }

        // let's try to chop off the end of this block into another free block
        let at = size + u16::from(BlockHeader::SIZE);
        if fb.should_split(at) {
            let (left, right) = fb.split(at);

            // both parts should be unlinked
            debug_assert!(left.next_free().is_none());
            debug_assert!(left.prev_free().is_none());
            debug_assert!(right.next_free().is_none());
            debug_assert!(right.prev_free().is_none());

            self.insert(right);
            fb = left;
        }

        let block = fb.into_used();

        Ok(NonNull::new_unchecked(
            (block.header() as *mut u8).add(usize::from(BlockHeader::SIZE)),
        ))
    }

    /// Deallocate the memory referenced by `ptr`.
    ///
    /// See [`core::alloc::Alloc.dealloc`][0] for more details
    ///
    /// [0]: https://doc.rust-lang.org/core/alloc/trait.Alloc.html#tymethod.dealloc
    ///
    /// This method has a bounded execution time, meaning that it will complete within some time `T`
    /// regardless of the input and the state of the allocator -- the implementation of this method
    /// contains no loops, recursion or panicking branches.
    pub unsafe fn dealloc(&mut self, ptr: NonNull<u8>) {
        let mut fb = Block::new_unchecked(
            ptr.as_ptr().offset(-isize::from(BlockHeader::SIZE)) as *mut BlockHeader
        )
        .into_free();

        // unlink
        fb.set_next_free(None);
        fb.set_prev_free(None);

        // merge
        fb = self.merge_prev(fb);
        fb = self.merge_next(fb);

        self.insert(fb);
    }

    /// Attempts to extend the allocation referenced by `ptr` to fit `new_size.`
    ///
    /// See [`core::alloc::Alloc.grow_in_place`][0] for more details
    ///
    /// [0]: https://doc.rust-lang.org/core/alloc/trait.Alloc.html#method.grow_in_place
    ///
    /// This method has a bounded execution time, meaning that it will complete within some time `T`
    /// regardless of the input and the state of the allocator -- the implementation of this method
    /// contains no loops, recursion or panicking branches.
    pub unsafe fn grow_in_place(&mut self, ptr: NonNull<u8>, new_size: usize) -> Result<(), ()> {
        let actual_size = FreeBlock::new_unchecked(
            ptr.as_ptr().offset(-isize::from(BlockHeader::SIZE)) as *mut _,
        )
        .usable_size();

        if usize::from(actual_size) >= new_size {
            Ok(())
        } else {
            // TODO we should try to merge with the following free block, if there's one
            Err(())
        }
    }

    /// Attempts to shrink the allocation referenced by `ptr` to fit `new_size`.
    ///
    /// See [`core::alloc::Alloc.shrink_in_place`][0] for more details
    ///
    /// [0]: https://doc.rust-lang.org/core/alloc/trait.Alloc.html#method.shrink_in_place
    ///
    /// This method has a bounded execution time, meaning that it will complete within some time `T`
    /// regardless of the input and the state of the allocator -- the implementation of this method
    /// contains no loops, recursion or panicking branches.
    pub unsafe fn shrink_in_place(
        &mut self,
        _ptr: NonNull<u8>,
        _new_size: usize,
    ) -> Result<(), ()> {
        // TODO we should try to carve off a free block out of the excess space
        // because we store the size in the block header shrinking a block can be a no-op
        Ok(())
    }

    /// Returns a pointer suitable for holding data described by a new layout with `layout`’s
    /// alignment and a size given by `new_size`. To accomplish this, this may extend or shrink the
    /// allocation referenced by `ptr` to fit the new layout.
    ///
    /// See [`core::alloc::Alloc.realloc`][0] for more details
    ///
    /// [0]: https://doc.rust-lang.org/core/alloc/trait.Alloc.html#method.realloc
    ///
    /// This method does **not** have a bounded execution time. It may complete in `O(N)` time where
    /// `N = layout.size()`
    pub unsafe fn realloc(
        &mut self,
        ptr: NonNull<u8>,
        layout: Layout,
        new_size: usize,
    ) -> Result<NonNull<u8>, ()> {
        let old_size = layout.size();

        if new_size >= old_size {
            if self.grow_in_place(ptr, new_size).is_ok() {
                return Ok(ptr);
            }
        } else if new_size < old_size {
            if self.shrink_in_place(ptr, new_size).is_ok() {
                return Ok(ptr);
            }
        }

        // otherwise, fall back on alloc + copy + dealloc.
        let new_layout = Layout::from_size_align_unchecked(new_size, layout.align());
        let result = self.alloc(new_layout);
        if let Ok(new_ptr) = result {
            // NOTE `util::`, not `ptr::`
            util::copy_nonoverlapping(ptr.as_ptr(), new_ptr.as_ptr(), cmp::min(old_size, new_size));
            self.dealloc(ptr);
        }
        result
    }

    /* Private API */
    fn insert(&mut self, mut block: FreeBlock) {
        unsafe {
            let i = util::mapping_insert(block.usable_size());

            if let Some(offset) = self.free_list_head(i) {
                let mut head = FreeBlock::from_offset(offset);
                block.set_next_free(Some(offset));
                block.set_prev_free(None);
                head.set_prev_free(Some(block.offset()));
            }

            self.set_free_list_head(i, Some(block.offset()));
            self.fl_bitmap |= 1 << i.fl;
            *self.sl_bitmap_mut(i.fl) |= 1 << i.sl;
        }
    }

    fn merge_next(&mut self, mut unlinked: FreeBlock) -> FreeBlock {
        unsafe {
            debug_assert!(unlinked.next_free().is_none());
            debug_assert!(unlinked.prev_free().is_none());

            if unlinked.is_last_phys_block() {
                // no next block; we are at the boundary of the pool
                unlinked
            } else {
                let next = Block::new_unchecked(
                    (unlinked.header() as *mut u8).add(usize::from(unlinked.size())) as *mut _,
                );

                if next.is_free() {
                    let mut next = FreeBlock::new_unchecked(next.header() as *mut _);

                    // unlink the next block
                    self.unlink(&mut next);

                    // grow this block
                    let size = unlinked.size();
                    unlinked.set_size(size + next.size());

                    if next.is_last_phys_block() {
                        // the merged block is now the last physical block
                        unlinked.set_last_phys_block_bit(true);
                    }
                } else {
                    // next block is being used; nothing to do
                }

                unlinked
            }
        }
    }

    fn merge_prev(&mut self, unlinked: FreeBlock) -> FreeBlock {
        unsafe {
            debug_assert!(unlinked.next_free().is_none());
            debug_assert!(unlinked.prev_free().is_none());

            if let Some(offset) = unlinked.prev_phys_block() {
                let prev = Block::from_offset(offset);

                if prev.is_free() {
                    // merge them!
                    let mut prev = FreeBlock::new_unchecked(prev.header() as *mut _);

                    self.unlink(&mut prev);

                    // grow the previous block
                    let size = prev.size();
                    prev.set_size(size + unlinked.size());

                    if unlinked.is_last_phys_block() {
                        // the merged block is now the last physical block
                        prev.set_last_phys_block_bit(true);
                    }

                    prev
                } else {
                    // previous block is being used; nothing to do
                    unlinked
                }
            } else {
                // no previous block
                unlinked
            }
        }
    }

    unsafe fn find_suitable_block(&self, i: Index) -> Option<Index> {
        let mut bitmap = self.sl_bitmap(i.fl) & (!0 << i.sl);

        let sl;
        let fl;
        if bitmap != 0 {
            sl = util::ffs(bitmap);
            fl = i.fl;
        } else {
            bitmap = self.fl_bitmap & (!0 << (i.fl + 1));

            if bitmap == 0 {
                // Out of Memory
                return None;
            }

            fl = util::ffs(bitmap);
            sl = util::ffs(self.sl_bitmap(fl));
        }

        Some(Index { fl, sl })
    }

    /// Remove this block from the free list
    unsafe fn unlink(&mut self, block: &mut FreeBlock) {
        let next = block.next_free();
        let prev = block.prev_free();

        if let Some(prev) = prev {
            FreeBlock::from_offset(prev).set_next_free(next);
            block.set_prev_free(None);
        } else {
            // this is the head of the list
            let i = util::mapping_insert(block.usable_size());

            // replace the head of the free list
            if let Some(next) = next {
                FreeBlock::from_offset(next).set_prev_free(None);
            } else {
                // the list is now empty
                self.clear_bit(i);
            }
            self.set_free_list_head(i, next);
        }

        if let Some(next) = next {
            FreeBlock::from_offset(next).set_prev_free(prev);
            block.set_next_free(None);
        }
    }

    unsafe fn remove_head(&mut self, i: Index) -> FreeBlock {
        let fl = self.free_list_head(i);

        let mut head = FreeBlock::from_offset(fl.unwrap_or_else(|| assume_unreachable!()));
        debug_assert_eq!(head.prev_free(), None);

        let next = head.next_free();
        if let Some(next) = next {
            FreeBlock::from_offset(next).set_prev_free(None);
            head.set_next_free(None);
        }
        // replace the head of the free list
        self.set_free_list_head(i, next);

        // the list is now empty
        if next.is_none() {
            self.clear_bit(i);
        }

        head
    }

    unsafe fn clear_bit(&mut self, i: Index) {
        // clear the corresponding bit in the SL bitmap
        *self.sl_bitmap_mut(i.fl) &= !(1 << i.sl);

        if self.sl_bitmap(i.fl) == 0 {
            // if the SL bitmap is now empty; clear the corresponding bit in the FL bitmap
            self.fl_bitmap &= !(1 << i.fl);
        }
    }

    /* Getters */
    unsafe fn free_list_head(&self, i: Index) -> Option<Offset> {
        let head = *self
            .free_lists
            .get(usize::from(i.fl))
            .unwrap_or_else(|| assume_unreachable!())
            .get(usize::from(i.sl))
            .unwrap_or_else(|| assume_unreachable!());

        debug_assert!(head
            .map(|offset| FreeBlock::from_offset(offset).prev_free().is_none())
            .unwrap_or(true));

        head
    }

    unsafe fn set_free_list_head(&mut self, i: Index, head: Option<Offset>) {
        debug_assert!(
            head.map(|offset| FreeBlock::from_offset(offset).prev_free().is_none())
                .unwrap_or(true),
            "{:#?}{:#?}",
            head.map(|offset| FreeBlock::from_offset(offset)),
            self
        );

        *self
            .free_lists
            .get_mut(usize::from(i.fl))
            .unwrap_or_else(|| assume_unreachable!())
            .get_mut(usize::from(i.sl))
            .unwrap_or_else(|| assume_unreachable!()) = head;
    }

    unsafe fn sl_bitmap(&self, fl: u8) -> u16 {
        *self
            .sl_bitmaps
            .get(usize::from(fl))
            .unwrap_or_else(|| assume_unreachable!())
    }

    unsafe fn sl_bitmap_mut(&mut self, fl: u8) -> &mut u16 {
        self.sl_bitmaps
            .get_mut(usize::from(fl))
            .unwrap_or_else(|| assume_unreachable!())
    }

    #[cfg(test)]
    fn free_blocks<'a>(&'a self) -> impl Iterator<Item = (Index, FreeBlock)> + 'a {
        self.indices().flat_map(move |i| {
            let head = unsafe { self.free_list_head(i) };

            debug_assert!(head.is_some());

            FreeListIterator {
                head,
                _marker: PhantomData,
            }
            .map(move |fb| (i, fb))
        })
    }

    fn indices<'a>(&'a self) -> impl Iterator<Item = Index> + 'a {
        Bits(self.fl_bitmap)
            .flat_map(move |fl| Bits(unsafe { self.sl_bitmap(fl) }).map(move |sl| Index { fl, sl }))
    }
}

struct Bits(u16);

impl Iterator for Bits {
    type Item = u8;

    fn next(&mut self) -> Option<u8> {
        if self.0 == 0 {
            None
        } else {
            let i = util::fls(self.0);
            self.0 &= !(1 << i);
            Some(i)
        }
    }
}

struct FreeListIterator<'a> {
    head: Option<Offset>,
    // freeze the `Tlsf` struct
    _marker: PhantomData<&'a ()>,
}

impl<'a> Iterator for FreeListIterator<'a> {
    type Item = FreeBlock;

    fn next(&mut self) -> Option<FreeBlock> {
        if let Some(head) = self.head {
            let fb = unsafe { FreeBlock::from_offset(head) };
            self.head = fb.next_free();
            Some(fb)
        } else {
            None
        }
    }
}

#[cfg(feature = "ufmt")]
#[derive(Clone, Copy, Debug, uDebug)]
pub(crate) struct Index {
    fl: u8,
    sl: u8,
}

#[cfg(not(feature = "ufmt"))]
#[derive(Clone, Copy, Debug)]
pub(crate) struct Index {
    fl: u8,
    sl: u8,
}

struct FreeBlocks<'a>(&'a Tlsf);

#[cfg(feature = "ufmt")]
impl<'a> ufmt::uDebug for FreeBlocks<'a> {
    fn fmt<W>(&self, f: &mut ufmt::Formatter<'_, W>) -> Result<(), W::Error>
    where
        W: ufmt::uWrite,
    {
        let mut map = f.debug_map()?;
        for i in self.0.indices() {
            map.entry(
                &i,
                &List(unsafe {
                    self.0
                        .free_list_head(i)
                        .unwrap_or_else(|| assume_unreachable!())
                }),
            )?;
        }
        map.finish()
    }
}

impl fmt::Debug for FreeBlocks<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut map = f.debug_map();
        for i in self.0.indices() {
            map.entry(
                &i,
                &List(unsafe {
                    self.0
                        .free_list_head(i)
                        .unwrap_or_else(|| assume_unreachable!())
                }),
            );
        }
        map.finish()
    }
}

struct List(Offset);

#[cfg(feature = "ufmt")]
impl ufmt::uDebug for List {
    fn fmt<W>(&self, f: &mut ufmt::Formatter<'_, W>) -> Result<(), W::Error>
    where
        W: ufmt::uWrite,
    {
        f.debug_list()?
            .entries(FreeListIterator {
                head: Some(self.0),
                _marker: PhantomData,
            })?
            .finish()
    }
}

impl fmt::Debug for List {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list()
            .entries(FreeListIterator {
                head: Some(self.0),
                _marker: PhantomData,
            })
            .finish()
    }
}

#[cfg(feature = "ufmt")]
impl ufmt::uDebug for Tlsf {
    fn fmt<W>(&self, f: &mut ufmt::Formatter<'_, W>) -> Result<(), W::Error>
    where
        W: ufmt::uWrite,
    {
        f.debug_struct("Tlsf")?
            .field("fl_bitmap", &self.fl_bitmap)?
            .field("sl_bitmaps", &self.sl_bitmaps)?
            .field("free_blocks", &FreeBlocks(self))?
            .finish()
    }
}

impl fmt::Debug for Tlsf {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Tlsf")
            .field("fl_bitmap", &self.fl_bitmap)
            .field("sl_bitmaps", &self.sl_bitmaps)
            .field("free_blocks", &FreeBlocks(self))
            .finish()
    }
}
