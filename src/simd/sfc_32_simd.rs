// use core::simd::{u32x2, u32x4, u32x8};
use core::simd::*;
use core::fmt;

use rand_core::BlockRngCore;

use simd::rng_impl::*;
use simd::{Sfc32Rng, SimdRng, SimdArray};

/// The non-SIMD version of this same PRNG.
pub type NonSimdRng = Sfc32Rng;


macro_rules! make_sfc_32_simd {
    ($rng_name:ident, $vector:ident, $next_u:ident, $test_name:ident, $rng_core_name:ident) => (
        /// A SIMD implementation of Chris Doty-Humphrey's Small Fast Counting RNG (32-bit)
        pub struct $rng_name {
            a: $vector,
            b: $vector,
            c: $vector,
            counter: $vector,
        }

        // Custom Debug implementation that does not expose the internal state
        impl fmt::Debug for $rng_name {
            fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
                write!(f, "$rng_name {{}}")
            }
        }

        impl BlockRngCore for $rng_name {
            type Item = u32;
            type Results = SimdArray<$vector>;

            #[inline(always)]
            fn generate(&mut self, results: &mut Self::Results) {
                #[inline]
                fn rotate_left(x: $vector, n: u32) -> $vector {
                    const BITS: u32 = 32;
                    // Protect against undefined behaviour for over-long bit shifts
                    let n = n % BITS;
                    (x << n) | (x >> ((BITS - n) % BITS))
                }

                const BARREL_SHIFT: u32 = 21;
                const RSHIFT: u32 = 9;
                const LSHIFT: u32 = 3;

                let tmp = self.a + self.b + self.counter;
                self.counter += $vector::splat(1); // FIXME
                self.a = self.b ^ (self.b >> RSHIFT);
                self.b = self.c + (self.c << LSHIFT);
                self.c = rotate_left(self.c, BARREL_SHIFT) + tmp;
                *results = SimdArray(tmp);
            }
        }

        impl RngCore for $rng_name {
            #[inline(always)]
            fn next_u32(&mut self) -> u32 {
                let mut results = <$rng_name as BlockRngCore>::Results::default();
                self.generate(&mut results);
                results.as_ref()[0]
            }

            #[inline(always)]
            fn next_u64(&mut self) -> u64 {
                let mut results = <$rng_name as BlockRngCore>::Results::default();
                self.generate(&mut results);
                let x = u64::from(results.as_ref()[0]);
                let y = u64::from(results.as_ref()[1]);
                (y << 32) | x
            }

            #[inline(always)]
            fn fill_bytes(&mut self, dest: &mut [u8]) {
                let len = ::core::mem::size_of::<<$rng_name as BlockRngCore>::Results>(); // FIXME?
                if dest.len() == len {
                    let mut results = <$rng_name as BlockRngCore>::Results::default();
                    self.generate(&mut results);
                    unsafe {
                        ::core::ptr::copy_nonoverlapping(
                            results.as_ref().as_ptr() as *const u8,
                            dest.as_mut_ptr(),
                            len);
                    }
                    return;
                }
                unimplemented!()
            }

            fn try_fill_bytes(&mut self, dest: &mut [u8]) -> Result<(), Error> {
                self.fill_bytes(dest);
                Ok(())
            }
        }

        impl SimdRng for $rng_name {
            #[inline]
            fn $next_u(&mut self) -> $vector {
                #[inline]
                fn rotate_left(x: $vector, n: u32) -> $vector {
                    const BITS: u32 = 32;
                    // Protect against undefined behaviour for over-long bit shifts
                    let n = n % BITS;
                    (x << n) | (x >> ((BITS - n) % BITS))
                }

                const BARREL_SHIFT: u32 = 21;
                const RSHIFT: u32 = 9;
                const LSHIFT: u32 = 3;

                let tmp = self.a + self.b + self.counter;
                self.counter += Self::INC;
                self.a = self.b ^ (self.b >> RSHIFT);
                self.b = self.c + (self.c << LSHIFT);
                self.c = rotate_left(self.c, BARREL_SHIFT) + tmp;
                tmp
            }
        }

        impl $rng_name {
            const INC: $vector = $vector::splat(1);

            /// Create a new PRNG using the given vector seeds.
            pub fn from_vector(a: $vector, b: $vector, c: $vector) -> Self {
                Self {
                    a, b, c,
                    counter: Self::INC,
                }
            }

            /// Create a new PRNG using the given non-SIMD PRNGs.
            pub fn from_non_simd(reg_rngs: &[NonSimdRng]) -> Self {
                let mut a = $vector::default();
                let mut b = $vector::default();
                let mut c = $vector::default();

                for (i, rng) in reg_rngs.iter().enumerate().take($vector::lanes()) {
                    a = a.replace(i, rng.a);
                    b = b.replace(i, rng.b);
                    c = c.replace(i, rng.c);
                }

                Self::from_vector(a, b, c)
            }
        }

        impl SeedableRng for $rng_name {
            type Seed = [u8; 0];

            fn from_seed(_seed: Self::Seed) -> Self {
                unimplemented!();
            }

            #[inline]
            fn from_rng<R: RngCore>(mut rng: R) -> Result<Self, Error> {
                let mut seed_u32 = [0u32; $vector::lanes() * 3];
                unsafe {
                    let ptr = seed_u32.as_mut_ptr() as *mut u8;

                    let slice = slice::from_raw_parts_mut(ptr, 32 / 8);
                    rng.try_fill_bytes(slice)?;
                }

                let lanes = $vector::lanes();
                let load = |x| $vector::load_unaligned(x);

                Ok(Self::from_vector(
                    load(&seed_u32[..lanes]),
                    load(&seed_u32[lanes..2 * lanes]),
                    load(&seed_u32[lanes * 2..]),
                ))
            }
        }

        #[test]
        fn $test_name() {
            use thread_rng;

            fn test(reg_rngs: &mut [NonSimdRng]) {
                let mut simd_rng = $rng_name::from_non_simd(reg_rngs);

                for i in 0..super::SIMD_CORRECTNESS_N {
                    let expected = reg_rngs.iter_mut().map(|x| x.gen::<u32>());
                    let next = simd_rng.$next_u();

                    for (j, exp) in expected.enumerate() {
                        let actual = next.extract(j);
                        assert_eq!(actual, exp, "{:?}", i);
                    }
                }
            }

            let mut zero_rngs: Vec<_> = (0..$vector::lanes())
                .map(|_| NonSimdRng::from_good_seed(Default::default()))
                .collect();
            test(&mut zero_rngs);

            let mut rng = thread_rng();
            for _ in 0..super::SIMD_CORRECTNESS_SEEDS {
                let mut reg_rngs: Vec<_> = (0..$vector::lanes())
                    .map(|_| NonSimdRng::from_rng(&mut rng).unwrap())
                    .collect();
                test(&mut reg_rngs);
            }
        }
    )
}

make_sfc_32_simd!(Sfc32X2, u32x2, next_u32x2, test_sfc_32_x2, Sfc32X2Core);
make_sfc_32_simd!(Sfc32X4, u32x4, next_u32x4, test_sfc_32_x4, Sfc32X4Core);
make_sfc_32_simd!(Sfc32X8, u32x8, next_u32x8, test_sfc_32_x8, Sfc32X8Core);
