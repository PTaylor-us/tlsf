use core::alloc::Layout;

use crate::{consts, util, Bits, BlockHeader, Tlsf};

const N: usize = consts::MAX_BLOCK_SIZE as usize + BlockHeader::SIZE as usize;

#[repr(align(4))]
struct Aligned<T>(T);

#[test]
fn alloc_reuse() {
    static mut MEMORY: Aligned<[u8; N]> = Aligned([0; N]);

    unsafe {
        let mut tlsf = Tlsf::new();
        tlsf.extend(&mut MEMORY.0);

        let layout = Layout::new::<u8>();

        // X ~
        let x = tlsf.alloc(layout).unwrap();

        // X Y ~
        let _y = tlsf.alloc(layout).unwrap();

        // (X) Y ~
        tlsf.dealloc(x);

        assert_eq!(tlsf.free_blocks().count(), 2);

        // Z Y ~
        // This operation will reclaim the previously freed `x` block
        let z = tlsf.alloc(layout).unwrap();

        assert_eq!(tlsf.free_blocks().count(), 1);
        assert_eq!(z, x);
    }
}

// bigger alignments
#[test]
fn alignment() {
    // align to a 32-byte boundary
    static mut MEMORY: A32<[u8; 2 * N]> = A32([0; 2 * N]);

    #[repr(align(8))]
    struct A8(u8);

    #[repr(align(16))]
    struct A16(u8);

    #[repr(align(32))]
    struct A32<T>(T);

    unsafe {
        let mut tlsf = Tlsf::new();
        tlsf.extend(&mut MEMORY.0);

        let layout = Layout::new::<A32<u8>>();
        // worst-case padding
        let x = tlsf.alloc(layout).unwrap();
        assert_eq!(x.as_ptr() as usize % layout.align(), 0);

        let layout = Layout::new::<A8>();
        let y = tlsf.alloc(layout).unwrap();
        assert_eq!(y.as_ptr() as usize % layout.align(), 0);

        let layout = Layout::new::<A16>();
        let z = tlsf.alloc(layout).unwrap();
        assert_eq!(z.as_ptr() as usize % layout.align(), 0);
    }
}

// small requests will be round up to a multiple of `ALIGN_SIZE`
#[test]
fn align_size() {
    static mut MEMORY: Aligned<[u8; N]> = Aligned([0; N]);

    unsafe {
        let mut tlsf = Tlsf::new();
        tlsf.extend(&mut MEMORY.0);

        let x = tlsf.alloc(Layout::new::<u8>()).unwrap();

        let y = tlsf.alloc(Layout::new::<u16>()).unwrap();

        let z = tlsf.alloc(Layout::new::<u32>()).unwrap();

        assert_eq!(x.as_ptr() as usize % usize::from(consts::ALIGN_SIZE), 0);
        assert_eq!(y.as_ptr() as usize % usize::from(consts::ALIGN_SIZE), 0);
        assert_eq!(z.as_ptr() as usize % usize::from(consts::ALIGN_SIZE), 0);

        assert_eq!(
            y.as_ptr() as usize - x.as_ptr() as usize,
            usize::from(consts::ALIGN_SIZE + BlockHeader::SIZE)
        );
        assert_eq!(
            z.as_ptr() as usize - y.as_ptr() as usize,
            usize::from(consts::ALIGN_SIZE + BlockHeader::SIZE)
        );
    }
}

#[test]
fn bits() {
    let mut bits = Bits(0b110011);

    assert_eq!(bits.next(), Some(5));
    assert_eq!(bits.next(), Some(4));
    assert_eq!(bits.next(), Some(1));
    assert_eq!(bits.next(), Some(0));
    assert_eq!(bits.next(), None);
}

#[test]
fn new() {
    static mut MEMORY: Aligned<[u8; N]> = Aligned([0; N]);

    unsafe {
        let mut tlsf = Tlsf::new();
        let size = tlsf.extend(&mut MEMORY.0);

        // There should be a single free block after initialization
        assert_eq!(tlsf.free_blocks().count(), 1);

        // This free block should fully utilize `MEMORY` minus the space used by the block header
        assert_eq!(
            usize::from(size),
            MEMORY.0.len() - usize::from(BlockHeader::SIZE),
        );
    }
}

#[test]
fn new_unaligned() {
    static mut MEMORY: Aligned<[u8; N]> = Aligned([0; N]);

    unsafe {
        let mut tlsf = Tlsf::new();
        let size = tlsf.extend(&mut MEMORY.0[1..]);

        // There should be a single free block after initialization
        assert_eq!(tlsf.free_blocks().count(), 1);

        // This free block should fully utilize `MEMORY` minus the space used by the block header
        // and padding required to align the free block
        assert_eq!(
            usize::from(size),
            MEMORY.0.len() - usize::from(BlockHeader::SIZE + consts::ALIGN_SIZE),
        );
    }
}

#[test]
fn merge_both() {
    static mut MEMORY: Aligned<[u8; N]> = Aligned([0; N]);

    unsafe {
        let mut tlsf = Tlsf::new();
        tlsf.extend(&mut MEMORY.0);
        assert_eq!(tlsf.free_blocks().count(), 1);

        let layout = Layout::new::<u8>();

        // X ~
        let x = tlsf.alloc(layout).unwrap();
        assert_eq!(tlsf.free_blocks().count(), 1);

        // X Y ~
        let y = tlsf.alloc(layout).unwrap();
        assert_eq!(tlsf.free_blocks().count(), 1);

        // X Y Z ~
        let z = tlsf.alloc(layout).unwrap();
        assert_eq!(tlsf.free_blocks().count(), 1);

        // X Y Z W ~
        let _w = tlsf.alloc(layout).unwrap();
        assert_eq!(tlsf.free_blocks().count(), 1);

        // (X) Y Z W ~
        tlsf.dealloc(x);
        assert_eq!(tlsf.free_blocks().count(), 2);

        // (X) Y (Z) W ~
        tlsf.dealloc(z);
        assert_eq!(tlsf.free_blocks().count(), 3);

        // Previously freed `x` and `z` blocks will be merged with `y`
        // (X<-Y->Z) W ~
        tlsf.dealloc(y);
        assert_eq!(tlsf.free_blocks().count(), 2);
    }
}

#[test]
fn merge_prev() {
    static mut MEMORY: Aligned<[u8; N]> = Aligned([0; N]);

    unsafe {
        let mut tlsf = Tlsf::new();
        tlsf.extend(&mut MEMORY.0);

        let layout = Layout::new::<u8>();

        // X ~
        let x = tlsf.alloc(layout).unwrap();

        // X Y ~
        let y = tlsf.alloc(layout).unwrap();

        // X Y Z ~
        let _z = tlsf.alloc(layout).unwrap();

        // (X) Y Z ~
        tlsf.dealloc(x);
        assert_eq!(tlsf.free_blocks().count(), 2);

        // (X<-Y) Z ~
        // Previously freed `x` block will be merged with `y`
        tlsf.dealloc(y);
        assert_eq!(tlsf.free_blocks().count(), 2);
    }
}

#[test]
fn merge_next() {
    static mut MEMORY: Aligned<[u8; N]> = Aligned([0; N]);

    unsafe {
        let mut tlsf = Tlsf::new();
        tlsf.extend(&mut MEMORY.0);

        let layout = Layout::new::<u8>();

        // X ~
        let x = tlsf.alloc(layout).unwrap();

        // X Y ~
        let y = tlsf.alloc(layout).unwrap();

        // X Y Z ~
        let _z = tlsf.alloc(layout).unwrap();

        // X (Y) Z ~
        tlsf.dealloc(y);
        assert_eq!(tlsf.free_blocks().count(), 2);

        // Previously freed `y` block will be merged with `x`
        // (X->Y) Z ~
        tlsf.dealloc(x);
        assert_eq!(tlsf.free_blocks().count(), 2);
    }
}

#[test]
fn oom() {
    unsafe {
        let mut tlsf = Tlsf::new();

        let layout = Layout::new::<u8>();

        let x = tlsf.alloc(layout);
        assert!(x.is_err());
    }
}

#[test]
fn two_phys_blocks() {
    static mut MEMORY: Aligned<[u8; 2 * N]> = Aligned([0; 2 * N]);

    unsafe {
        let mut tlsf = Tlsf::new();
        tlsf.extend(&mut MEMORY.0);

        // both free blocks should be marked as `last_phys_block`
        assert_eq!(tlsf.free_blocks().count(), 2);
        assert!(tlsf.free_blocks().all(|(_, fb)| fb.is_last_phys_block()));

        let layout = Layout::new::<[u8; N / 2]>();

        // X ~ | ~
        let _x = tlsf.alloc(layout).unwrap();

        // X ~ | Y ~
        let y = tlsf.alloc(layout).unwrap();

        // X ~ | (Y) ~
        // deallocating `Y` should not merge blocks that belong to different physical regions
        tlsf.dealloc(y);
        assert_eq!(tlsf.free_blocks().count(), 2);
        assert!(tlsf.free_blocks().all(|(_, fb)| fb.is_last_phys_block()));
    }
}

#[test]
fn realloc() {
    static mut MEMORY: Aligned<[u8; N]> = Aligned([0; N]);

    unsafe {
        let mut tlsf = Tlsf::new();
        tlsf.extend(&mut MEMORY.0);

        let layout = Layout::new::<u8>();

        let x = tlsf.alloc(layout).unwrap();

        // blocks always have size `>= 4` so these re-allocations should be a no-ops
        let y = tlsf.realloc(x, layout, 2).unwrap();
        assert_eq!(x, y);

        let z = tlsf.realloc(y, layout, 4).unwrap();
        assert_eq!(x, z);
    }
}

#[test]
fn maximums() {
    util::mapping_insert_(consts::MAX_BLOCK_SIZE);
    util::mapping_search_(consts::MAX_REQUEST_SIZE);
}

#[cfg(debug_assertions)]
#[test]
#[should_panic]
fn exceed_block_size() {
    util::mapping_insert(consts::MAX_BLOCK_SIZE + u16::from(consts::ALIGN_SIZE));
}

#[cfg(debug_assertions)]
#[test]
#[should_panic]
fn exceed_request_size() {
    util::mapping_search(consts::MAX_REQUEST_SIZE + u16::from(consts::ALIGN_SIZE));
}
