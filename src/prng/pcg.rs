// Copyright 2017 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! PCG generator

use {Rng, SeedFromRng, SeedableRng, Result};

/// A PCG random number generator.

/// PCG XSH 64/32 (LCG)
/// Permuted Congruential Generators, "xorshift high (bits), random rotation"
/// using an underlying Linear congruential generator
#[derive(Clone, Debug)]
pub struct PcgRng {
    state: u64,
    increment: u64,
}

const INCREMENT: u64 = 1442695040888963407;
const MULTIPLIER: u64 = 6364136223846793005;

impl PcgRng {
    #[inline]
    fn init(init_state: u64, increment: u64) -> PcgRng {
        // TODO: explain
        let mut state = init_state.wrapping_add(INCREMENT);
        // increment must always be odd
        // TODO: shift left if small number
        let increment = increment | 1;
        // prepare for the next round
        state = state.wrapping_mul(MULTIPLIER).wrapping_add(increment);
        PcgRng { state: state }
    }
}

impl SeedFromRng for PcgRng {
    fn from_rng<R: Rng+?Sized>(rng: &mut R) -> Result<Self> {
        Ok(PcgRng::init(rng.next_u64()))
    }
}

impl Rng for PcgRng {
    #[inline]
    fn next_u32(&mut self) -> u32 {
        let state = self.state;
        // prepare the LCG for the next round
        self.state = state.wrapping_mul(MULTIPLIER).wrapping_add(self.increment);

        // output function XSH RR: xorshift high (bits), followed by a random rotate
        // good for 64-bit state, 32-bit output
        const IN_BITS: u32 = 64;
        const OUT_BITS: u32 = 32;
        const OP_BITS: u32 = 5; // log2(OUT_BITS)

        const ROTATE: u32 = IN_BITS - OP_BITS; // 59
        const XSHIFT: u32 = (OUT_BITS + OP_BITS) / 2; // 18
        const SPARE: u32 = IN_BITS - OUT_BITS - OP_BITS; // 27

        let xsh = (((state >> XSHIFT) ^ state) >> SPARE) as u32;
        xsh.rotate_right((state >> ROTATE) as u32)
    }

    #[inline]
    fn next_u64(&mut self) -> u64 {
       ::rand_core::impls::next_u64_via_u32(self)
    }

    #[cfg(feature = "i128_support")]
    fn next_u128(&mut self) -> u128 {
        ::rand_core::impls::next_u128_via_u64(self)
    }

    fn try_fill(&mut self, dest: &mut [u8]) -> Result<()> {
        ::rand_core::impls::try_fill_via_u32(self, dest)
    }
}

impl SeedableRng<[u64; 1]> for PcgRng {
    /// Reseed a PcgRng.
    fn reseed(&mut self, seed: [u64; 1]) {
        self.state = seed[0]; // TODO
    }

    /// Create a new PcgRng.
    fn from_seed(seed: [u64; 1]) -> PcgRng {
        PcgRng::init(seed[0])
    }
}
