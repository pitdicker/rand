// Copyright 2017 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Xorshift* generator (32-bit)

use core::num::Wrapping as w;
use {Rng, SeedFromRng, SeedableRng, Result};

/// A Xorshift random number generator.
///
/// Xorshift is a family of pseudorandom number generators designed by George
/// Marsaglia in 2003[1]. They are among the fastest random number generators,
/// requiring little code and state.
///
/// The implementation in `rand` uses the variant `xorshift64/32*_truncated`,
/// that multiplies and truncates the results of its underlying Xorshift
/// generator. This greatly improves the quality of the results, with little
/// performance loss. It has a period of 2^64 - 1.
///
/// As a confirmation of its statistical quality, this implementation easily
/// passes the Big Crush test suite, even when the bits are reversed. It also
/// passes the PractRand test suite, until it has generated about as many
/// numbers as the square root of its period (e.g. 2^32 ). This means the advise
/// to not use more numbers than the square root of a RNG is true for this
/// truncated Xorshift* generator.
///
/// Because `0 ^ 0 = 0`, a Xorshift generator can never work from a seed that is
/// 0. Also it can never reach a state where all its bits are 0. Therefore the
/// period is not a power of 2, but a power of 2 minus 1. It is however possible
/// for the result to be 0, because of the extra multiply and truncation step on
/// the result.
///
/// The properties of the Xorshift family of RNGs are well-studied, and several
/// variations are proposed over the years:
///
/// - In 2004 Richard Brent[4] showed that Xorshift generators are equivalent to
///   certain linear-feedback shift registers (LFSRs), which makes previous
///   studies applicable to them.
/// - In 2005 François Panneton and Pierre L’Ecuyer[3] analyzed in detail the
///   theoretical properties of the generators, and found weaknesses using the
///   TestU01 suite. They suggested using a fourth xorshift to improve quality,
///   and to combine the output with other RNGs from different classes.
/// - In 2007 Richard Brent[4] analyzed how to pick good shift constants,
///   especially for large states. He implemented the results in the `xorgens`
///   package.
/// - In 2012 Mutsuo Saito and Makoto Matsumoto[5] analyzed the statistical
///   quality of`xorwow`, a variant by Marsaglia that combines Xorshift with a
///   Weyl sequence.
/// - In 2014 Sebastiano Vigna[6] did an experimental exploration on the
///   influence of different shift constants on the results with the TestU01
///   suite. He also expanded on Marsaglia's note to use multiplication to
///   improve the generators output, making `xorshift*` more popular.
/// - In 2014 Mutsuo Saito and Makoto Matsumoto proposed a variant called
///   `XSadd`, which adds two consecutive outputs of an underlying xorshift
///   generator as a faster non-linear transformation[7]. Sebastiano Vigna
///   improved upon this design with `xorshift128+`[8]. He later improved upon
///   that with a different algorithm called `xoroshiro128+`.
/// - In 2014 Melissa O'Neil commented on the effectiveness of different
///   permutation techniques used in the Xorshift variants[9]. Especially
///   truncated Xorshift* generators are of high quality, while the other
///   variants mask their lower quality by using larger state sizes.
///
///
/// ## Overview of the Xorshift algorithm
/// The basic operations used by a Xorshift RNG are xorshifts.
/// The base algorithm can be described as:
///
/// ```text
/// Input: state
///
/// state ^= state >> a;
/// state ^= state << b;
/// state ^= state >> c;
/// return state;
/// ```
///
/// The algorithm can be modified to operate on a larger state than the integers
/// it operates on:
///
/// ```text
/// Input: s[n], i // state of n integers, and index
///
/// s0 = state[i]; i = (i + 1) % n;
/// s1 = state[i];
/// s1 ^= s1 << a;
/// s1 ^= s1 >> b;
/// s0 ^= s0 >> c;
/// s[i] = s0 ^ s1;
/// return s[i];
/// ```
///
/// For the truncated Xorshift* algorithm we use, the result of the base
/// algorithm is multiplied by a constant `d`, and truncated.
///
///
/// ### State size and performance
/// A state size of only 32 bits is generally considered as too small. So we use
/// the algorithm extended for larger states.
///
/// This is also good for performance. In the base algorithm every step depends
/// on the result of the previous step. This gives the compiler and processor no
/// room to do some calculations in parallel. The extended algorithm allows
/// a xorshift to happen on both `s0` and `s1` independently.
///
/// Also it is possible to move the first xorshift on `s1` to the end of the
/// algorithm, as a preperation for the next step. This allows it to run in
/// parallel with the multiplication step.
///
///
/// ### Choice of constants
/// In the above algorithms, `a`, `b`, and `c` are the shift constants. The
/// choice for these constants determines whether the RNG can cover a period
/// that is as large as its state, and the 'randomness' of the generated
/// numbers.
///
/// This implementation uses a state size that is twice the size of the integers
/// it operates on. Marsaglia[1] describes how to calculate shifts that fit a
/// certain period. Vigna provides scripts that can calculate shift constants in
/// the [source tarball](http://xoroshiro.di.unimi.it/) that support his
/// papers. As constants we use one of the triples generated by those scripts.
///
/// The state transitions of every xorshift can mathematically be desribed using
/// a binary matrix multiply, or by a polynomal. As noted in [5] it is a good
/// property to pick constants that belong to a polynomal with a weight close to
/// n/2. That is, the number of nonzero terms in it should be close to half the
/// number of bits of the state.
///
/// Finally some combinations of constants just give slightly better statistical
/// results, with no clear explanation why. So we pick constants that perform
/// well on the Big Crush test.
///
/// How to pick a good multiply constant `d` is well studied for a different
/// type of RNGs, Linear Congruential generators (LCGs). Because the same
/// principles apply, we pick one of the good constants for those as calculated
/// by Pierre L'Ecuyer[10].
///
/// This implementation uses the shift constants 21, 23 and 4 for `a`, `b`, and
/// `c`. For the multiply constant `d` we use `741103597`.
///
/// ### Truncation step
///
/// The multiplication step mixes more of the state bits into the high bits of
/// the result, than in the low bits. Consider the following table to see why
/// this is so (simplified for 8-bits instead of the 32 we work on):
///
/// ```text
/// | bits from |   |  random  |   |   random bits in    |
/// | constant  |   |   bits   |   |      in result      |
/// +-----------+   +----------+   +----------+----------+
/// | 00000001  | x | 11111111 | = | 0000000½ | 1111111½ |
/// | 00000010  | x | 11111111 | = | 000000½1 | 111111½0 |
/// | 00000100  | x | 11111111 | = | 00000½11 | 11111½00 |
/// | 00001000  | x | 11111111 | = | 0000½111 | 1111½000 |
/// | 00010000  | x | 11111111 | = | 000½1111 | 111½0000 |
/// | 00100000  | x | 11111111 | = | 00½11111 | 11½00000 |
/// | 01000000  | x | 11111111 | = | 0½111111 | 1½000000 |
/// | 10000000  | x | 11111111 | = | ½1111111 | ½0000000 |
/// +-----------+   +----------+   +----------+----------+
///                                             <--> used with simple truncation
///                                      <---   ---> alternative truncation
/// ```
///
/// On average every bit of the truncated result is influenced by 75% of the
/// state bits. A simple truncation uses only the high half of bits from the
/// underlying state integer. This implementation uses a different method. If we
/// use all the bits of the multiplication, as returned by a widening multiply,
/// we can truncate the result to use all the middle 32 bits, which are just as
/// good.
///
/// ## References
/// [1]: George Marsaglia (July 2003). ["Xorshift RNGs"]
///      (http://www.jstatsoft.org/v08/i14/paper).
///      *Journal of Statistical Software*. Vol. 8 (Issue 14).
///
/// [2]: Richard Brent (August 2004). ["Note on Marsaglia’s Xorshift Random
///      Number Generators"](http://www.jstatsoft.org/v11/i05/paper).
///      *Journal of Statistical Software*. Vol. 11 (Issue 5).
///
/// [3]: François Panneton and Pierre L'Ecuyer (October 2005).
///      ["On the xorshift random number generators"]
///      (http://www.iro.umontreal.ca/~lecuyer/myftp/papers/xorshift.pdf).
///      *ACM Transactions on Modeling and Computer Simulation*.
///
/// [4]: Richard Brent (Juli 2007). ["Some long-period random number generators
///      using shifts and xors"]
///      (https://maths-people.anu.edu.au/~brent/pd/rpb224.pdf)
///
/// [5]: Mutsuo Saito and Makoto Matsumoto (Februari 2012). ["A deviation of
///      CURAND: standard pseudorandom number generator in CUDA for GPGPU"]
///      (http://www.mcqmc2012.unsw.edu.au/slides/MCQMC2012_Matsumoto.pdf)
///
/// [6]: Sebastiano Vigna (March 2014). ["An experimental exploration of
///      Marsaglia's xorshift generators, scrambled"]
///      (http://vigna.di.unimi.it/ftp/papers/xorshift.pdf)
///
/// [7]: Mutsuo Saito and Makoto Matsumoto (Februari 2014). ["XORSHIFT-ADD
///      (XSadd): A variant of XORSHIFT"](http://eprint.iacr.org/2006/438)
///
/// [8]: Sebastiano Vigna (March 2014).
///      ["Further scramblings of Marsaglia's xorshift generators"]
///      (http://vigna.di.unimi.it/ftp/papers/xorshiftplus.pdf)
///
/// [9]: Melissa O'Neil (September 2014). ["PCG: A Family of Simple Fast
///      Space-Efficient Statistically Good Algorithms for Random Number
///      Generation"](http://www.pcg-random.org/pdf/hmc-cs-2014-0905.pdf).
///
/// [10]: Pierre L'Ecuyer (Januari 1999). ["Tables of linear congruential
///       generators of different sizes and good lattice structure"]
///       (http://www.ams.org/journals/mcom/1999-68-225/S0025-5718-99-00996-5/S0025-5718-99-00996-5.pdf).
///       *Mathematics of Computation*. Vol. 68 (Number 225). [Errata]
///       (https://www.iro.umontreal.ca/~lecuyer/myftp/papers/latrules99Errata.pdf).
#[allow(missing_copy_implementations)]
#[derive(Clone, Debug)]
pub struct XorshiftMult32Rng {
    pub s0: w<u32>,
    pub s1: w<u32>,
}

// TODO: 21-4-23	17	x^64 + x^32 + x^31 + x^23 + x^22 + x^21 + x^20 + x^19 + x^18 + x^16 + x^14 + x^12 + x^11 + x^10 + x^9 + x^8 + 1

// 15-7-1	37	x^64 + x^57 + x^51 + x^50 + x^48 + x^45 + x^44 + x^43 + x^42 + x^41 + x^38 + x^37 + x^36 + x^34 + x^31 + x^29 + x^28 + x^27 + x^26 + x^25 + x^24 + x^22 + x^21 + x^20 + x^19 + x^14 + x^12 + x^11 + x^10 + x^8 + x^6 + x^5 + x^4 + x^3 + x^2 + x + 1
// const P: [u32; 2] = [0b00000010_00001101_00111110_01110100,
//                      0b10111111_01111000_01011101_01111111];

// 13-11-4	31 (1+16+14)	x^64 + x^59 + x^58 + x^55 + x^54 + x^51 + x^50 + x^48 + x^46 + x^43 + x^42 + x^41 + x^37 + x^36 + x^35 + x^34 + x^33 + x^30 + x^25 + x^24 + x^23 + x^19 + x^18 + x^17 + x^16 + x^11 + x^7 + x^6 + x^5 + x^3 + 1

// The left shifts(s) should not both be greater than the right-shift(s)

const A: usize = 13;
const B: usize = 11;
const C: usize = 4;
const D: u32 = 741103597;
// Characteristic polynomal
// const P: [u32; 2] = [0b00001100_11001101_01001110_00111110,
//                      0b01000011_10001111_00001000_11101001];


impl XorshiftMult32Rng {
    #[inline]
    fn xorshift(&mut self) -> u32 {
        let x = self.s0;
        let y = self.s1;
        let t = x ^ (x >> B) ^ (y ^ (y >> C));
        self.s0 = y ^ (y << A); // first xorshift step of the next round
        self.s1 = t;
        t.0
    }

    pub fn jump(&mut self) {
        // jump polynomal
        const P2: [u32; 2] = [0b10110011_11010110_11011010_01100011,
                              0b00101010_00100110_00101010_01000010]; // 100
        let mut s0 = w(0);
        let mut s1 = w(0);
/*
        for jump_int in P2.iter().rev() {
            for b in 0..32 {
                let apply: bool = jump_int & (1u32 << b) != 0;
                let apply: w<u32> = w(-(apply as i32) as u32);

                s0 ^= self.s0 & apply;
                s1 ^= self.s1 & apply;

                self.xorshift(); // useless when this is the last round
            }
        }
*/

        for jump_int in P2.iter().rev() {
            for b in 0..32 {
                if jump_int & (1u32 << b) != 0 {
                    s0 ^= self.s0;
                    s1 ^= self.s1;
                }
                self.xorshift(); // useless when this is the last round
            }
        }
/*
        let jump_int = P2[0];
        for b in 0..32 {
            let apply: bool = jump_int & (1u32 << b) != 0;
            let apply: w<u32> = w(-(apply as i32) as u32);

            s0 ^= self.s0 & apply;
            s1 ^= self.s1 & apply;

            self.xorshift(); // useless when this is the last round
        }
        let jump_int = P2[1];
        for b in 0..31 {
            let apply: bool = jump_int & (1u32 << b) != 0;
            let apply: w<u32> = w(-(apply as i32) as u32);

            s0 ^= self.s0 & apply;
            s1 ^= self.s1 & apply;

            self.xorshift(); // useless when this is the last round
        }
        let apply: bool = jump_int & (1u32 << 31) != 0;
        let apply: w<u32> = w(-(apply as i32) as u32);

        s0 ^= self.s0 & apply;
        s1 ^= self.s1 & apply;
*/
        self.s0 = s0;
        self.s1 = s1;
    }

    pub fn new_from_u64(seed: u64) -> XorshiftMult32Rng {
        // Because the state size of this generator is 64 bits, it is tempting
        // to use the seed directly as state. But if this function where then to
        // be called with a simple hand-picked integer like 1, 4 or 8, it would
        // perform poorly for the first ~10 rounds.
        //
        // That is because Xorshift works best when about half of the bits in
        // its state are ones. If most of the bits are zero, the changes between
        // one internal state and the next are smaller than normal.
        //
        // As an extra precaution against this case we xor the seed with a
        // rondom number that has about half its bits set to 1.
        // This is not a simple pattern like 0xaaaaaaaaa, because that again
        // would be a likely candidate for someone to naively enter as seed.
        // The multiply constant D seems as good as any number.
        //
        // We should be careful to never create a seed that is completely 0.
        // Substituting zero with some other seed seems in the spirit of
        // `new_from_u64`, as it stives to be a practical, infallible way to
        // initialize a RNG, at the cost of predictability.
        let mut seed = seed;
        if seed != 2685821657736338717 {
            seed ^= 2685821657736338717;
        }
        XorshiftMult32Rng {
            s0: w(seed as u32),
            s1: w((seed >> 32) as u32),
        }
    }
}

impl Rng for XorshiftMult32Rng {
    #[inline]
    fn next_u32(&mut self) -> u32 {
        ((w(self.xorshift() as u64) * w(D as u64)).0 >> 16) as u32
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

impl SeedFromRng for XorshiftMult32Rng {
    fn from_rng<R: Rng+?Sized>(rng: &mut R) -> Result<Self> {
        // If one of the integers of the state is 0, that integer will remain 0
        // for all future rounds. While we technically still have a working RNG
        // if at least one integer is nonzero, it will have a much smaller
        // period. So we just require that all integers of the state are seeded
        // with a nonzero integer.
        let mut s0 = 0;
        let mut s1 = 0;
        while s0 == 0 { s0 = rng.next_u32() };
        while s1 == 0 { s1 = rng.next_u32() };
        Ok(XorshiftMult32Rng {
            // As an optimisation in the xorshift algorithm we always prepare
            // s0 with the first xorshift step of the next round.
            // But because we assume that the seeding RNG is random, the
            // preparation should not be neccesary for the initial step.
            s0: w(s0),
            s1: w(s1),
        })
    }
}

impl SeedableRng<[u32; 2]> for XorshiftMult32Rng {
    /// Create a new XorshiftMult32Rng. This will panic if `seed` is entirely 0.
    fn from_seed(seed: [u32; 2]) -> XorshiftMult32Rng {
        assert!(!seed.iter().all(|&x| x == 0),
                "XorshiftMult32Rng.reseed called with an all zero seed.");

        XorshiftMult32Rng {
            // first xorshift step of the next round
            s0: w(seed[0]) ^ w(seed[0]) << A,
            s1: w(seed[1]),
        }
    }
}

#[cfg(test)]
mod test {
    use {Rng, SeedableRng};
    use super::XorshiftMult32Rng;

    #[test]
    fn test_xorshift_jump_100() {
        let mut rng1 = XorshiftMult32Rng::from_seed([1, 2]);
        let mut rng2 = rng1.clone();
        for _ in 0..100 {
            let _ = rng1.next_u32();
        }
        rng2.jump();
        assert!(rng1.next_u32() == rng2.next_u32());
    }
}
