use core::{convert::TryFrom, mem, num::NonZeroI16, ops, ptr::NonNull};

use crate::{
    consts,
    free_block::{FreeBlock, FreeBlockHeader},
    Offset,
};

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

    pub fn set_last_phys_block_bit(&mut self, is_last_phys_block: bool) {
        if is_last_phys_block {
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
    pub unsafe fn _next_neighbor<'a>(&self) -> Block<'a> {
        debug_assert!(!self.is_last_phys_block());

        Block::from_header(NonNull::new_unchecked(
            NonNull::from(self)
                .cast::<u8>()
                .as_ptr()
                .add(usize::from(self.size()))
                .cast(),
        ))
    }

    // NOTE(safety) caller needs to ensure that two instances of the same block won't be created
    // (mutable aliasing); this can easily occur if you call this method twice
    pub unsafe fn _prev_neighbor<'a>(&self) -> Option<Block<'a>> {
        self.prev_phys_block.map(|off| Block::from_offset(off))
    }
}

#[repr(transparent)]
pub struct Block<'a> {
    // NOTE we use a reference here because the block header points into statically allocated memory
    // (originally `&'static mut [u8]`) which is always safe to dereference (the memory will never
    // be deallocated). We do *not* use a `'static` lifetime here because that may hint the compiler
    // that certain piece of memory will *always* be a block header and that won't be the case
    // because blocks are constantly being split and coalesced
    header: &'a mut BlockHeader,
}

impl<'a> Block<'a> {
    /* Constructors */
    pub unsafe fn from_header(header: NonNull<BlockHeader>) -> Self {
        let header = header.as_ptr();
        debug_assert_eq!(header as usize % usize::from(consts::ALIGN_SIZE), 0);

        Block {
            header: &mut *header,
        }
    }

    pub unsafe fn from_offset(offset: Offset) -> Self {
        let header = crate::anchor()
            .as_ptr()
            .offset(isize::from(offset.get() << consts::ALIGN_SIZE_LOG2));

        Block::from_header(NonNull::new_unchecked(header.cast()))
    }

    pub unsafe fn from_data_pointer(ptr: NonNull<u8>) -> Self {
        Block::from_header(NonNull::new_unchecked(
            ptr.as_ptr().offset(-isize::from(BlockHeader::SIZE)).cast(),
        ))
    }

    /* Getters */
    pub fn offset(&self) -> Offset {
        unsafe {
            Offset::new(
                i16::try_from(
                    (self.header().as_ptr() as isize - crate::anchor().as_ptr() as isize)
                        >> consts::ALIGN_SIZE_LOG2,
                )
                .unwrap_or_else(|_| assume_unreachable!()),
            )
            .unwrap_or_else(|| assume_unreachable!())
        }
    }

    pub fn header(&self) -> NonNull<BlockHeader> {
        NonNull::from(&*self.header)
    }

    /* Miscellaneous */
    pub fn into_free(mut self) -> FreeBlock<'a> {
        unsafe {
            self.set_free_bit(true);
            FreeBlock::from_header(self.header().cast())
        }
    }

    pub unsafe fn next_neighbor(&self) -> Block<'a> {
        self._next_neighbor()
    }

    /// Splits this free block in two free blocks
    ///
    /// The first free block will have a *block* size of `n` bytes
    pub unsafe fn split(self, n: u16) -> (Self, FreeBlock<'a>) {
        debug_assert_eq!(n % u16::from(consts::ALIGN_SIZE), 0);

        let total = self.size();

        debug_assert!(n >= u16::from(BlockHeader::SIZE));
        debug_assert!(total >= n + u16::from(FreeBlockHeader::SIZE));

        let last_phys_block = self.is_last_phys_block();

        let mut left = self;

        // create the right ("remainder") block
        let start =
            NonNull::new_unchecked((left.header().as_ptr().cast::<u8>()).add(usize::from(n)));
        let right = FreeBlock::from_parts(
            start.cast(),
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

    pub fn assume_free(self) -> FreeBlock<'a> {
        unsafe { FreeBlock::from_header(self.header().cast()) }
    }
}

impl ops::Deref for Block<'_> {
    type Target = BlockHeader;

    fn deref(&self) -> &BlockHeader {
        self.header
    }
}

impl ops::DerefMut for Block<'_> {
    fn deref_mut(&mut self) -> &mut BlockHeader {
        self.header
    }
}
