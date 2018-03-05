// Copyright 2013-2017 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// https://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Helper functions for implementing `RngCore` functions.
//!
//! For cross-platform reproducibility, these functions all use Little Endian:
//! least-significant part first. For example, `next_u64_via_u32` takes `u32`
//! values `x, y`, then outputs `(y << 32) | x`. To implement `next_u32`
//! from `next_u64` in little-endian order, one should use `next_u64() as u32`.
//!
//! Byte-swapping (like the std `to_le` functions) is only needed to convert
//! to/from byte sequences, and since its purpose is reproducibility,
//! non-reproducible sources (e.g. `OsRng`) need not bother with it.

// TODO: eventually these should be exported somehow
#![allow(unused)]

use core::intrinsics::transmute;
use core::ptr::copy_nonoverlapping;
use core::slice;
use core::cmp::min;
use core::mem::size_of;
use RngCore;

/// Implement `next_u64` via `next_u32`, little-endian order.
pub fn next_u64_via_u32<R: RngCore + ?Sized>(rng: &mut R) -> u64 {
    // Use LE; we explicitly generate one value before the next.
    let x = rng.next_u32() as u64;
    let y = rng.next_u32() as u64;
    (y << 32) | x
}

macro_rules! fill_bytes_via {
    ($rng:ident, $next_u:ident, $BYTES:expr, $dest:ident) => {{
        let mut left = $dest;
        while left.len() >= $BYTES {
            let (l, r) = {left}.split_at_mut($BYTES);
            left = r;
            let chunk: [u8; $BYTES] = unsafe {
                transmute($rng.$next_u().to_le())
            };
            l.copy_from_slice(&chunk);
        }
        let n = left.len();
        if n > 0 {
            let chunk: [u8; $BYTES] = unsafe {
                transmute($rng.$next_u().to_le())
            };
            left.copy_from_slice(&chunk[..n]);
        }
    }}
}

/// Implement `fill_bytes` via `next_u32`, little-endian order.
pub fn fill_bytes_via_u32<R: RngCore + ?Sized>(rng: &mut R, dest: &mut [u8]) {
    fill_bytes_via!(rng, next_u32, 4, dest)
}

/// Implement `fill_bytes` via `next_u64`, little-endian order.
pub fn fill_bytes_via_u64<R: RngCore + ?Sized>(rng: &mut R, dest: &mut [u8]) {
    fill_bytes_via!(rng, next_u64, 8, dest)
}

macro_rules! impl_uint_from_fill {
    ($rng:expr, $ty:ty, $N:expr) => ({
        debug_assert!($N == size_of::<$ty>());

        let mut int: $ty = 0;
        unsafe {
            let ptr = &mut int as *mut $ty as *mut u8;
            let slice = slice::from_raw_parts_mut(ptr, $N);
            $rng.fill_bytes(slice);
        }
        int
    });
}

macro_rules! fill_via_chunks {
    ($src:expr, $dst:expr, $ty:ty, $size:expr) => ({
        let chunk_size_u8 = min($src.len() * $size, $dst.len());
        let chunk_size = (chunk_size_u8 + $size - 1) / $size;
        if cfg!(target_endian="little") {
            unsafe {
                copy_nonoverlapping(
                    $src.as_ptr() as *const u8,
                    $dst.as_mut_ptr(),
                    chunk_size_u8);
            }
        } else {
            for (&n, chunk) in $src.iter().zip($dst.chunks_mut($size)) {
                let tmp = n.to_le();
                let src_ptr = &tmp as *const $ty as *const u8;
                unsafe {
                    copy_nonoverlapping(src_ptr,
                                        chunk.as_mut_ptr(),
                                        chunk.len());
                }
            }
        }

        (chunk_size, chunk_size_u8)
    });
}

/// Implement `fill_bytes` by reading chunks from the output buffer of a block
/// based RNG.
///
/// The return values are `(consumed_u32, filled_u8)`.
///
/// `filled_u8` is the number of filled bytes in `dest`, which may be less than
/// the length of `dest`.
/// `consumed_u32` is the number of words consumed from `src`, which is the same
/// as `filled_u8 / 4` rounded up.
///
/// # Example
/// (from `IsaacRng`)
///
/// ```rust,ignore
/// fn fill_bytes(&mut self, dest: &mut [u8]) {
///     let mut read_len = 0;
///     while read_len < dest.len() {
///         if self.index >= self.rsl.len() {
///             self.isaac();
///         }
///
///         let (consumed_u32, filled_u8) =
///             impls::fill_via_u32_chunks(&mut self.rsl[self.index..],
///                                        &mut dest[read_len..]);
///
///         self.index += consumed_u32;
///         read_len += filled_u8;
///     }
/// }
/// ```
pub fn fill_via_u32_chunks(src: &[u32], dest: &mut [u8]) -> (usize, usize) {
    fill_via_chunks!(src, dest, u32, 4)
}

/// Implement `fill_bytes` by reading chunks from the output buffer of a block
/// based RNG.
///
/// The return values are `(consumed_u64, filled_u8)`.
/// `filled_u8` is the number of filled bytes in `dest`, which may be less than
/// the length of `dest`.
/// `consumed_u64` is the number of words consumed from `src`, which is the same
/// as `filled_u8 / 8` rounded up.
///
/// See `fill_via_u32_chunks` for an example.
pub fn fill_via_u64_chunks(src: &[u64], dest: &mut [u8]) -> (usize, usize) {
    fill_via_chunks!(src, dest, u64, 8)
}

/// Implement `next_u32` via `fill_bytes`, little-endian order.
pub fn next_u32_via_fill<R: RngCore + ?Sized>(rng: &mut R) -> u32 {
    impl_uint_from_fill!(rng, u32, 4)
}

/// Implement `next_u64` via `fill_bytes`, little-endian order.
pub fn next_u64_via_fill<R: RngCore + ?Sized>(rng: &mut R) -> u64 {
    impl_uint_from_fill!(rng, u64, 8)
}

pub fn fill_slice_by_repeating(int: u64, seed: &mut [u8]) {
    let int = int.to_le();
    let slice = unsafe {
        let ptr = &int as *const u64 as *const u8;
        slice::from_raw_parts(ptr, 8)
    };
    for (x, y) in seed.iter_mut().zip(slice.iter().cycle()) { *x = *y; }
}

pub fn fill_slice_with splitmix(int: u64, seed: &mut [u8]) {
    let int = int.to_le();
    let slice = unsafe {
        let ptr = &int as *const u64 as *const u8;
        slice::from_raw_parts(ptr, 8)
    };
    for (x, y) in seed.iter_mut().zip(slice.iter().cycle()) { *x = *y; }
        // Initialize the first integer of the state directly with the seed.
        // The second integer is generated with a SplitMix64 RNG[1] from the
        // same seed, as recommended by Sebastiano Vigna[2].
        //
        // This implementation followes his, which doesn't support different
        // streams with ɣ-values (completely unnecessary here), and with the
        // finalizer constants from David Stafford’s Mix13 variant[3] of the
        // MurmurHash3 finalizer (also mentioned as a good variant in [1]).
        //
        // The Xorshift algorithm does not work if the entire seed is 0. If the
        // second integer is generated with SplitMix it is impossible for both
        // integers to be zero.
        //
        // [1] Guy Steele, Doug Lea, Christine Flood (Oktober 2014).
        //     ["Fast Splittable Pseudorandom Number Generators"]
        //     (http://gee.cs.oswego.edu/dl/papers/oopsla14.pdf)
        // [2] Sebastiano Vigna, David Blackman (2016). ["xoroshiro+ /
        //     xorshift* / xorshift+ generators and the PRNG shootout"]
        //     (http://vigna.di.unimi.it/xorshift/).
        // [3] David Stafford (September 2011). ["Better bit mixing: Improving
        //     on MurmurHash3’s 64-bit finalizer"]
        //     (http://zimbry.blogspot.nl/2011/09/better-bit-mixing-improving-on.html).
        let s0 = seed;
        // TODO: does the trick from 32-bit make sense?

        let mut s1 = s0.wrapping_add(0x9E3779B97F4A7C15); // Weyl sequence, golden ratio * 2^64
        s1 = (s1 ^ (s1 >> 30)).wrapping_mul(0xBF58476D1CE4E5B9);
        s1 = (s1 ^ (s1 >> 27)).wrapping_mul(0x94D049BB133111EB);
        s1 ^ (s1 >> 31);

        XorshiftMultRng { s0: s0, s1: s1 }
}

// TODO: implement tests for the above
