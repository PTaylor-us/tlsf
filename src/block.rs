use core::{convert::TryFrom, mem, num::NonZeroI16, ops, ptr};

use crate::{consts, free_block::FreeBlockHeader, FreeBlock, Offset};

#[repr(C)]
#[repr(align(4))]
pub struct BlockHeader {
    size: u16,
    prev_phys_block: Option<NonZeroI16>,
}

impl BlockHeader {
    pub const SIZE: u8 = mem::size_of::<BlockHeader>() as u8;

    const FREE_BIT: u16 = 1 << 0;
    const LAST_PHYS_BLOCK_BIT: u16 = 1 << 1;

    /* Setters */
    pub unsafe fn set_size(&mut self, size: u16) {
        debug_assert!(size % u16::from(consts::ALIGN_SIZE) == 0);
        debug_assert!(size >= u16::from(Self::SIZE));

        self.size = size | (self.size & 0b11);
    }

    pub fn set_last_phys_block_bit(&mut self, last_phys_block: bool) {
        if last_phys_block {
            self.size |= Self::LAST_PHYS_BLOCK_BIT;
        } else {
            self.size &= !Self::LAST_PHYS_BLOCK_BIT;
        }
    }

    pub fn set_free_bit(&mut self, free: bool) {
        if free {
            self.size |= Self::FREE_BIT;
        } else {
            self.size &= !Self::FREE_BIT;
        }
    }

    // XXX there's some LLVM bug (?) where the `Block.size` fields gets cached in a register and
    // `set_free_bit` ends up writing an old value into the field. This has been observed in the
    // `set_free_bit` invocation in `FreeBlock.into_used` after splitting a `FreeBlock` in
    // `Tlsf.alloc` with `opt-level=3`, `lto=true` and `codegen-units=1` -- it doesn't occur if you
    // use `opt-level=z`
    pub fn volatile_set_free_bit(&mut self, free: bool) {
        let size = unsafe { ptr::read_volatile(&self.size) };
        if free {
            self.size = size | Self::FREE_BIT;
        } else {
            self.size = size & !Self::FREE_BIT;
        }
    }

    pub fn set_prev_phys_block(&mut self, prev_phys_block: Option<NonZeroI16>) {
        self.prev_phys_block = prev_phys_block;
    }

    /* Getters */
    pub fn size(&self) -> u16 {
        self.size & !(Self::FREE_BIT | Self::LAST_PHYS_BLOCK_BIT)
    }

    pub fn is_free(&self) -> bool {
        self.size & Self::FREE_BIT != 0
    }

    pub fn is_last_phys_block(&self) -> bool {
        self.size & Self::LAST_PHYS_BLOCK_BIT != 0
    }

    pub fn prev_phys_block(&self) -> Option<NonZeroI16> {
        self.prev_phys_block
    }

    /* Miscellaneous */
    pub fn usable_size(&self) -> u16 {
        self.size() - u16::from(Self::SIZE)
    }

    // NOTE(safety) this does not check whether we are the last physical block or not
    pub unsafe fn next_neighbor(&self) -> Block {
        debug_assert!(!self.is_last_phys_block());

        Block::new_unchecked(
            (self as *const _ as *const u8).add(usize::from(self.size())) as *mut _,
        )
    }

    pub fn prev_neighbor(&self) -> Option<Block> {
        self.prev_phys_block
            .map(|off| unsafe { Block::from_offset(off) })
    }
}

#[repr(transparent)]
pub struct Block {
    header: *mut BlockHeader,
}

impl Block {
    /* Constructors */
    pub unsafe fn new_unchecked(header: *mut BlockHeader) -> Self {
        debug_assert_eq!(header as usize % usize::from(consts::ALIGN_SIZE), 0);

        Block { header }
    }

    pub unsafe fn from_offset(offset: Offset) -> Self {
        let header = crate::anchor().offset(isize::from(offset.get() << consts::ALIGN_SIZE_LOG2));

        Block::new_unchecked(header as *mut _)
    }

    pub unsafe fn from_data_pointer(ptr: *mut u8) -> Self {
        Block::new_unchecked(ptr.offset(-isize::from(BlockHeader::SIZE)) as *mut _)
    }

    pub fn offset(&self) -> Offset {
        unsafe {
            Offset::new(
                i16::try_from(
                    (self.header as isize - crate::anchor() as isize) >> consts::ALIGN_SIZE_LOG2,
                )
                .unwrap_or_else(|_| assume_unreachable!()),
            )
            .unwrap_or_else(|| assume_unreachable!())
        }
    }

    /* Getters */
    pub fn header(&self) -> *mut BlockHeader {
        self.header
    }

    /* Miscellaneous */
    pub fn into_free(mut self) -> FreeBlock {
        unsafe {
            self.set_free_bit(true);
            FreeBlock::new_unchecked(self.header() as *mut _)
        }
    }

    /// Splits this free block in two free blocks
    ///
    /// The first free block will have a *block* size of `n` bytes
    pub unsafe fn split(self, n: u16) -> (Self, FreeBlock) {
        debug_assert_eq!(n % u16::from(consts::ALIGN_SIZE), 0);

        let total = self.size();

        debug_assert!(n >= u16::from(BlockHeader::SIZE));
        debug_assert!(total >= n + u16::from(FreeBlockHeader::SIZE));

        let last_phys_block = self.is_last_phys_block();

        let mut left = self;

        // create the right ("remainder") block
        let start = (left.header as *mut u8).add(usize::from(n));
        let right = FreeBlock::from_parts(
            start as *mut _,
            total - n,
            last_phys_block,
            Some(left.offset()),
        );

        // update the original free block
        if last_phys_block {
            // `right` became the last physical block
            left.set_last_phys_block_bit(false);
        }
        left.set_size(n);

        (left, right)
    }

    pub fn assume_free(self) -> FreeBlock {
        unsafe { FreeBlock::new_unchecked(self.header() as *mut _) }
    }
}

impl ops::Deref for Block {
    type Target = BlockHeader;

    fn deref(&self) -> &BlockHeader {
        unsafe { &*self.header }
    }
}

impl ops::DerefMut for Block {
    fn deref_mut(&mut self) -> &mut BlockHeader {
        unsafe { &mut *self.header }
    }
}
