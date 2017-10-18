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

/// PCG XSL 128/64 (LCG)
/// Permuted Congruential Generators, "xorshift low (bits), random rotation"
/// using an underlying Linear congruential generator
#[derive(Clone, Debug)]
pub struct Pcg64Rng {
    state: u128,
}

const INCREMENT: u128 = 6364136223846793005u128 << 64 | 1442695040888963407;
const MULTIPLIER: u128 = 2549297995355413924u128 << 64 | 4865540595714422341;

impl Rng for Pcg64Rng {
    #[inline]
    fn next_u32(&mut self) -> u32 {
        self.next_u64() as u32
    }

    #[inline]
    fn next_u64(&mut self) -> u64 {
        let state = self.state;
        // prepare for the next round
        self.state = state.wrapping_mul(MULTIPLIER).wrapping_add(INCREMENT);

        // Output function XSL RR ("xorshift low (bits), random rotation"):
        // XSL uses xor folding of the high and the low u64. This minimizes the
        // amount of information about internal state that leaks out.
        // TODO: mostly performance
        // good for 128-bit state, 64-bit output
        const IN_BITS: u32 = 128;
        const OUT_BITS: u32 = 64;
        const SPARE_BITS: u32 = IN_BITS - OUT_BITS;
        const OP_BITS: u32 = 6; // log2(OUT_BITS)

        const XSHIFT: u32 = (SPARE_BITS + OUT_BITS) / 2; // 64
        const ROTATE: u32 = IN_BITS - OP_BITS; // 122

        let xsl = ((state >> XSHIFT) as u64) ^ (state as u64);
        xsl.rotate_right((state >> ROTATE) as u32)
    }

    #[cfg(feature = "i128_support")]
    fn next_u128(&mut self) -> u128 {
        ::rand_core::impls::next_u128_via_u64(self)
    }

    fn try_fill(&mut self, dest: &mut [u8]) -> Result<()> {
        ::rand_core::impls::try_fill_via_u64(self, dest)
    }
}

impl Pcg64Rng {
    #[inline]
    fn init(init_state: u128) -> Pcg64Rng {
        // TODO: explain
        let mut state = init_state.wrapping_add(INCREMENT);
        // prepare for the next round
        state = state.wrapping_mul(MULTIPLIER).wrapping_add(INCREMENT);
        Pcg64Rng { state: state }
    }
}

impl SeedFromRng for Pcg64Rng {
    fn from_rng<R: Rng+?Sized>(rng: &mut R) -> Result<Self> {
        let high = rng.next_u64() as u128;
        let low = rng.next_u64() as u128;
        Ok(Pcg64Rng::init(high << 64 | low))
    }
}

impl SeedableRng<[u64; 2]> for Pcg64Rng {
    /// Create a new Pcg64Rng.
    fn from_seed(seed: [u64; 2]) -> Pcg64Rng {
        Pcg64Rng::init((seed[0] as u128) << 64 | seed[1] as u128)
    }
}
