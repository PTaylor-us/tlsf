#![no_main]
#![no_std]
#![feature(alloc_prelude)]
#![feature(alloc_error_handler)]

extern crate alloc;

use alloc::prelude::v1::*;
use core::{
    alloc::{GlobalAlloc, Layout},
    sync::atomic::{AtomicUsize, Ordering},
};
use cortex_m_rt::entry;

extern crate nrf52832_hal;
extern crate panic_rtt;

use core::ptr::NonNull;
use spin::Mutex;
// don't use this in interrupts because it can deadlock
use tlsf::{Tlsf, MAX_BLOCK_SIZE};

static ALLOC: Mutex<Tlsf> = Mutex::new(Tlsf::new());

// An allocator singleton
struct A;

#[global_allocator]
static GLOBAL_ALLOCATOR: A = A {};

// or use the `#[alloc_many::allocator]` attribute
unsafe impl GlobalAlloc for A {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        ALLOC.lock().alloc(layout).unwrap().as_ptr()
    }

    unsafe fn dealloc(&self, ptr: *mut u8, _: Layout) {
        ALLOC
            .lock()
            .dealloc(core::ptr::NonNull::from(ptr.as_ref().unwrap()));
    }

    unsafe fn realloc(&self, ptr: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
        ALLOC
            .lock()
            .realloc(NonNull::new(ptr).unwrap(), layout, new_size)
            .unwrap()
            .as_ptr()
    }
}

#[repr(align(4))]
struct Aligned<T>(T);

#[entry]
fn main() -> ! {
    // NOTE(Aligned) align this buffer to `tlsf::ALIGN_SIZE` bytes to avoid padding
    // NOTE(SIZE) use a size multiple of `MAX_BLOCK_SIZE` to maximize coalescing
    // NOTE(bss) initialize this to all zeros to put `M` in the `.bss` linker
    //           section and close to `tlsf::ANCHOR`
    static mut M: Aligned<[u8; MAX_BLOCK_SIZE as usize]> = Aligned([0; MAX_BLOCK_SIZE as usize]);

    ALLOC.lock().extend(&mut M.0);

    // allocate a vector in allocator `A`
    let mut xs: Vec<_> = Vec::new();
    loop {
        // push until we run out of memory (see `oom` function below)
        let next_byte = X.fetch_add(1, Ordering::Relaxed) as u8;
        xs.push(next_byte);
    }
}

static X: AtomicUsize = AtomicUsize::new(0);

#[alloc_error_handler]
fn oom(_: Layout) -> ! {
    loop {}
}
