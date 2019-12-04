use core::{mem, num::NonZeroI16, ops, ptr};

use crate::{consts, FreeBlock, Offset};

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

        Block::new_unchecked((self as *const _ as *const u8).add(usize::from(self.size())) as *mut _)
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
