use core::{convert::TryFrom, fmt, mem, num::NonZeroI16, ops, ptr::NonNull};

use crate::{
    block::{Block, BlockHeader},
    consts, Offset,
};

#[repr(C)]
#[repr(align(4))]
pub struct FreeBlockHeader {
    // inheritance
    block: BlockHeader,
    next_free: Option<Offset>,
    prev_free: Option<Offset>,
}

impl FreeBlockHeader {
    pub const SIZE: u8 = mem::size_of::<Self>() as u8;

    /* Setters */
    pub fn set_next_free(&mut self, next_free: Option<Offset>) {
        self.next_free = next_free;
    }

    pub fn set_prev_free(&mut self, prev_free: Option<Offset>) {
        self.prev_free = prev_free;
    }

    /* Getters */
    pub fn next_free(&self) -> Option<Offset> {
        self.next_free
    }

    pub fn prev_free(&self) -> Option<Offset> {
        self.prev_free
    }
}

impl ops::Deref for FreeBlockHeader {
    type Target = BlockHeader;

    fn deref(&self) -> &BlockHeader {
        &self.block
    }
}

impl ops::DerefMut for FreeBlockHeader {
    fn deref_mut(&mut self) -> &mut BlockHeader {
        &mut self.block
    }
}

#[repr(transparent)]
pub struct FreeBlock<'a> {
    // NOTE for the rationale of this being a reference check the comment on the `struct Block` item
    header: &'a mut FreeBlockHeader,
}

impl<'a> FreeBlock<'a> {
    /* Constructors */
    pub unsafe fn from_header(header: NonNull<FreeBlockHeader>) -> Self {
        let header = header.as_ptr();
        debug_assert_eq!(header as usize % usize::from(consts::ALIGN_SIZE), 0);

        FreeBlock {
            header: &mut *header,
        }
    }

    pub unsafe fn from_parts(
        header: NonNull<FreeBlockHeader>,
        size: u16,
        is_last_phys_block: bool,
        prev_phys_block: Option<NonZeroI16>,
    ) -> Self {
        // check size
        debug_assert_eq!(size % u16::from(consts::ALIGN_SIZE), 0);
        debug_assert!(size >= u16::from(FreeBlockHeader::SIZE));

        let mut fb = FreeBlock::from_header(header);
        fb.set_size(size);
        fb.set_free_bit(true);
        fb.set_last_phys_block_bit(is_last_phys_block);
        fb.set_prev_phys_block(prev_phys_block);
        fb.set_next_free(None);
        fb.set_prev_free(None);

        fb
    }

    pub unsafe fn from_offset(offset: Offset) -> Self {
        let header = NonNull::new_unchecked(
            crate::anchor()
                .as_ptr()
                .offset(isize::from(offset.get() << consts::ALIGN_SIZE_LOG2)),
        )
        .cast();

        debug_assert!(Block::from_header(header.cast()).is_free());

        FreeBlock::from_header(header)
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

    pub fn header(&self) -> NonNull<FreeBlockHeader> {
        NonNull::from(&*self.header)
    }

    /* Miscellaneous */
    /// Splits this free block in two free blocks
    ///
    /// The first free block will have a *block* size of `n` bytes
    pub unsafe fn split(self, n: u16) -> (FreeBlock<'a>, FreeBlock<'a>) {
        debug_assert!(n >= u16::from(FreeBlockHeader::SIZE));

        let block = Block::from_header(self.header().cast());
        let (left, right) = block.split(n);

        (left.assume_free(), right)
    }

    pub fn should_split(&self, size: u16) -> bool {
        debug_assert_eq!(size % u16::from(consts::ALIGN_SIZE), 0);

        self.usable_size() >= size + u16::from(BlockHeader::SIZE) + consts::SPLIT_THRESHOLD
    }

    pub unsafe fn next_neighbor(&self) -> Block<'a> {
        self._next_neighbor()
    }

    pub unsafe fn prev_neighbor(&self) -> Option<Block<'a>> {
        self._prev_neighbor()
    }

    pub fn into_used(mut self) -> Block<'a> {
        unsafe {
            // Clear the `free` bit
            self.set_free_bit(false);
            Block::from_header(self.header().cast())
        }
    }
}

#[cfg(feature = "ufmt")]
impl ufmt::uDebug for FreeBlock {
    fn fmt<W>(&self, f: &mut ufmt::Formatter<'_, W>) -> Result<(), W::Error>
    where
        W: ufmt::uWrite,
    {
        f.debug_struct("FreeBlock")?
            .field("header", &self.header)?
            .field("offset", &self.offset())?
            .field("size", &self.size())?
            .field("last_phys_block", &self.is_last_phys_block())?
            .field("prev_phys_block", &self.prev_phys_block())?
            .field("next_free", &self.next_free())?
            .field("prev_free", &self.prev_free())?
            .finish()
    }
}

impl fmt::Debug for FreeBlock<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("FreeBlock")
            .field("header", &self.header())
            .field("offset", &self.offset())
            .field("size", &self.size())
            .field("last_phys_block", &self.is_last_phys_block())
            .field("prev_phys_block", &self.prev_phys_block())
            .field("next_free", &self.next_free())
            .field("prev_free", &self.prev_free())
            .finish()
    }
}

impl ops::Deref for FreeBlock<'_> {
    type Target = FreeBlockHeader;

    fn deref(&self) -> &FreeBlockHeader {
        self.header
    }
}

impl ops::DerefMut for FreeBlock<'_> {
    fn deref_mut(&mut self) -> &mut FreeBlockHeader {
        self.header
    }
}
