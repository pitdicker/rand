// Copyright 2017 Paul Dicker.
// See the COPYRIGHT file at the top-level directory of this distribution.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Xoroshiro with multiply and truncation random number generator

use core::{fmt, slice};
use rand_core::{Rng, SeedableRng, Error, impls, le};

/// XoroshiroMT random number generator.
///
/// - Period: 2<sup>128</sup> - 1
/// - State: 128 bits
/// - Word size: 64 bits
/// - Seed size: 128 bits
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
#[derive(Clone)]
pub struct XoroshiroMtRng {
    s0: u64,
    s1: u64,
}

// Custom Debug implementation that does not expose the internal state
impl fmt::Debug for XoroshiroMtRng {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "XoroshiroMtRng {{}}")
    }
}

impl SeedableRng for XoroshiroMtRng {
    type Seed = [u8; 16];

    fn from_seed(seed: Self::Seed) -> Self {
        let mut seed_u64 = [0u64; 2];
        le::read_u64_into(&seed, &mut seed_u64);

        if seed_u64 == [0u64; 2] {
            seed_u64 = [0x0DD_B1A5E5_BAD_5EED, 0x0DD_B1A5E5_BAD_5EED];
        }

        Self { s0: seed_u64[0], s1: seed_u64[1] }
    }

    fn from_rng<R: Rng>(mut rng: R) -> Result<Self, Error> {
        let mut seed_u64 = [0u64; 2];
        loop {
            unsafe {
                let ptr = seed_u64.as_mut_ptr() as *mut u8;

                let slice = slice::from_raw_parts_mut(ptr, 8*2);
                rng.try_fill(slice)?;
            }
            if seed_u64 != [0u64; 2] { break; }
        }

        Ok(Self { s0: seed_u64[0], s1: seed_u64[1] })
    }
}

impl Rng for XoroshiroMtRng {
    #[inline]
    fn next_u32(&mut self) -> u32 {
        let s0 = self.s0;
        let mut s1 = self.s1;

        s1 ^= s0;
        self.s0 = s0.rotate_left(55) ^ s1 ^ (s1 << 14); // a, b
        self.s1 = s1.rotate_left(36); // c
        let mult = (self.s1 as u32 as u64).wrapping_mul(3857418925 as u64);
        (mult >> 16) as u32
    }

    #[inline]
    #[cfg(not(any(target_pointer_width = "32", not(feature = "i128_support"))))]
    fn next_u64(&mut self) -> u64 {
        let s0 = self.s0;
        let mut s1 = self.s1;
        let mult = s0 as u128 * 2685821657736338717 as u128;

        s1 ^= s0;
        self.s0 = s0.rotate_left(55) ^ s1 ^ (s1 << 14); // a, b
        self.s1 = s1.rotate_left(36); // c

        (mult >> 32) as u64
    }

    #[inline]
    #[cfg(any(target_pointer_width = "32", not(feature = "i128_support")))]
    fn next_u64(&mut self) -> u64 {
        let s0 = self.s0;
        let mut s1 = self.s1;
        let (high, low) = s0.wmul(2685821657736338717);

        s1 ^= s0;
        self.s0 = s0.rotate_left(55) ^ s1 ^ (s1 << 14); // a, b
        self.s1 = s1.rotate_left(36); // c

        high << 32 | low >> 32
    }

    #[cfg(feature = "i128_support")]
    fn next_u128(&mut self) -> u128 {
        impls::next_u128_via_u64(self)
    }

    fn fill_bytes(&mut self, dest: &mut [u8]) {
        impls::fill_bytes_via_u64(self, dest)
    }

    fn try_fill(&mut self, dest: &mut [u8]) -> Result<(), Error> {
        Ok(self.fill_bytes(dest))
    }
}



trait WideningMultiply<RHS = Self> {
    type Output;

    fn wmul(self, x: RHS) -> Self::Output;
}

macro_rules! wmul_impl {
    ($ty:ty, $wide:ident, $shift:expr) => {
        impl WideningMultiply for $ty {
            type Output = ($ty, $ty);

            #[inline(always)]
            fn wmul(self, x: $ty) -> Self::Output {
                let tmp = (self as $wide) * (x as $wide);
                ((tmp >> $shift) as $ty, tmp as $ty)
            }
        }
    }
}

wmul_impl! { u32, u64, 32 }
#[cfg(not(any(target_pointer_width = "32", not(feature = "i128_support"))))]
wmul_impl! { u64, u128, 64 }

#[cfg(any(target_pointer_width = "32", not(feature = "i128_support")))]
impl WideningMultiply for u64 {
    type Output = (u64, u64);

    // This code is a translation of the __mulddi3 function in LLVM's
    // compiler-rt. It is an optimised variant of the common method
    // `(a + b) * (c + d) = ac + ad + bc + bd`.
    //
    // For some reason LLVM can optimise the C version very well, but keeps
    // shuffeling registers in this Rust translation.
    #[inline(always)]
    fn wmul(self, b: u64) -> Self::Output {
        const LOWER_MASK: u64 = !0u64 >> 32;
        let mut low = (self & LOWER_MASK).wrapping_mul(b & LOWER_MASK);
        let mut t = low >> 32;
        low &= LOWER_MASK;
        t += (self >> 32).wrapping_mul(b & LOWER_MASK);
        low += (t & LOWER_MASK) << 32;
        let mut high = (t >> 32) as i64;
        t = low >> 32;
        low &= LOWER_MASK;
        t += (b >> 32).wrapping_mul(self & LOWER_MASK);
        low += (t & LOWER_MASK) << 32;
        high += (t >> 32) as i64;
        high += (self >> 32).wrapping_mul(b >> 32) as i64;

        (high as u64, low)
    }
}

#[cfg(test)]
mod test {
    use {Rng, SeedableRng};
    use super::XoroshiroMtRng;

    #[test]
    fn test_xoroshiro_mt_construction() {
        // Test that various construction techniques produce a working RNG.
        let seed = [1,2,3,4, 5,6,7,8, 9,10,11,12, 13,14,15,16];
        let mut rng1 = XoroshiroMtRng::from_seed(seed);
        assert_eq!(rng1.next_u64(), 11034744347067857020);

        let mut rng2 = XoroshiroMtRng::from_rng(&mut rng1).unwrap();
        assert_eq!(rng2.next_u64(), 11445740179313917501);
    }

    #[test]
    fn test_xoroshiro_mt_true_values() {
        let seed = [16,15,14,13, 12,11,10,9, 8,7,6,5, 4,3,2,1];
        let mut rng = XoroshiroMtRng::from_seed(seed);

        let v = (0..9).map(|_| rng.next_u64()).collect::<Vec<_>>();
        assert_eq!(v,
                   vec!(7793545882806995014, 9322909604671780092,
                        13915916945674983277, 10460014316441953243,
                        16673642240486093366, 10814824514063739446,
                        7287804679463899652, 4682297091186437162,
                        7205193359114086513));

        let v = (0..9).map(|_| rng.next_u32()).collect::<Vec<_>>();
        assert_eq!(v,
                   vec!(3617900510, 2615577833, 1287368405,
                        3596532497, 2779255349, 2922443453,
                        413461093, 2967351294, 2125314236));

        let mut buf = [0u8; 32];
        rng.fill_bytes(&mut buf);
        assert_eq!(buf,
                   [236, 186, 13, 169, 36, 22, 113, 213,
                   12, 21, 28, 253, 104, 247, 90, 186,
                   105, 165, 3, 194, 70, 68, 26, 103,
                   114, 38, 73, 241, 77, 110, 95, 151]);
    }

    #[test]
    fn test_xoroshiro_mt_zero_seed() {
        // Xoroshiro does not work with an all zero seed.
        // Assert it does not panic.
        let seed = [0,0,0,0, 0,0,0,0, 0,0,0,0, 0,0,0,0];
        let mut rng = XoroshiroMtRng::from_seed(seed);
        let a = rng.next_u64();
        let b = rng.next_u64();
        assert!(a != 0);
        assert!(b != a);
    }

    #[test]
    fn test_xoroshiro_mt_clone() {
        let seed = [1,2,3,4, 5,5,7,8, 8,7,6,5, 4,3,2,1];
        let mut rng1 = XoroshiroMtRng::from_seed(seed);
        let mut rng2 = rng1.clone();
        for _ in 0..16 {
            assert_eq!(rng1.next_u64(), rng2.next_u64());
        }
    }
}
