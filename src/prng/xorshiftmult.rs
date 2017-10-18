// Copyright 2017 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Xorshift* generator

use {Rng, SeedFromRng, SeedableRng, Result};

/// A Xorshift random number generator.
///
/// The Xorshift algorithm is not suitable for cryptographic purposes
/// but is very fast. If you do not know for sure that it fits your
/// requirements, use a more secure one such as `IsaacRng` or `OsRng`.
///
/// [1]: Marsaglia, George (July 2003). ["Xorshift
/// RNGs"](http://www.jstatsoft.org/v08/i14/paper). *Journal of
/// Statistical Software*. Vol. 8 (Issue 14).
#[allow(missing_copy_implementations)]
#[derive(Clone, Debug)]
pub struct XorshiftMultRng {
    s0: u64,
    s1: u64,
}

const A: usize = 23;
const B: usize = 18;
const C: usize = 5;
const D: u64 = 2685821657736338717;

impl XorshiftMultRng {
    #[inline]
    fn xorshift(&mut self) -> u64 {

        let x = self.s0;
        let y = self.s1;
        let t = x ^ (x >> B) ^ (y ^ (y >> C));
        self.s0 = y ^ (y << A); // first xorshift step of the next round
        self.s1 = t;
        t

/*
        // without preparing the next step (faster on 32-bit)
        let mut x = self.s0;
        let y = self.s1;
        self.s0 = y;
        x ^= x << A;
        let t = x ^ (x >> B) ^ (y ^ (y >> C));
        self.s1 = t;
        t
*/
    }

    pub fn new_from_u64(seed: u64) -> XorshiftMultRng {
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
}

impl Rng for XorshiftMultRng {
    #[inline]
    fn next_u32(&mut self) -> u32 {
        (self.xorshift().wrapping_mul(D) >> 16) as u32
    }

    #[inline]
    fn next_u64(&mut self) -> u64 {
        ((self.xorshift() as u128 * D as u128) >> 32) as u64
    }

    fn next_u128(&mut self) -> u128 {
        ::rand_core::impls::next_u128_via_u64(self)
    }

    fn try_fill(&mut self, dest: &mut [u8]) -> Result<()> {
        ::rand_core::impls::try_fill_via_u64(self, dest)
    }
}

impl SeedFromRng for XorshiftMultRng {
    fn from_rng<R: Rng+?Sized>(rng: &mut R) -> Result<Self> {
        // If one of the integers of the state is 0, that integer will remain 0
        // for all future rounds. While we technically still have a working RNG
        // if at least one integer is nonzero, it will have a much smaller
        // period. So we just require that all integers of the state are seeded
        // with a nonzero integer.
        // TODO: wrong!
        let mut s0 = 0;
        let mut s1 = 0;
        while s0 == 0 { s0 = rng.next_u64() };
        while s1 == 0 { s1 = rng.next_u64() };
        Ok(XorshiftMultRng {
            s0: s0,
            // As an optimisation in the xorshift algorithm we always prepare
            // s0 with the first xorshift step of the next round.
            // But because we assume that the seeding RNG is random, the
            // preparation should not be neccesary for the initial step.
            s1: s1,
        })
    }
}

impl SeedableRng<[u64; 2]> for XorshiftMultRng {
    /// Create a new XorShiftStarRng. This will panic if `seed` is entirely 0.
    fn from_seed(seed: [u64; 2]) -> XorshiftMultRng {
        assert!(!seed.iter().all(|&x| x == 0),
                "XorshiftMultRng.reseed called with an all zero seed.");

        XorshiftMultRng {
            // first xorshift step of the next round
            s0: seed[0] ^ (seed[0] << A),
            s1: seed[1],
        }
    }
}

#[cfg(test)]
mod test {
    use {Rng, NewSeeded};
    use super::XorshiftMultRng;

    #[test]
    fn test_1000_rounds() {
        let mut rng = XorshiftMultRng::new().unwrap();
        let mut i = 0;
        for _ in 0..1000 {
            i ^= rng.next_u32();
        }
        assert!(i > 0);
    }
}
