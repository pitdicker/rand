use core::simd::*;
use core::mem;

use {thread_rng, SeedableRng, Rng};

use distributions::{Standard, IntoFloat};
use distributions::range::{RangeFloat, RangeImpl};

use simd::SimdRng;

///
pub trait SimdDistribution<T> {
    ///
    fn sample<R: SimdRng + ?Sized>(&self, rng: &mut R) -> T;
}

macro_rules! simd_float_impls {
    ($ty:ident, $uty:ident, $f_scalar:ty, $u_scalar:ty, $fraction_bits:expr, $exponent_bias:expr,
     $next_u:ident) => {
        impl SimdDistribution<$ty> for Standard {
            /// Generate a floating point number in the open interval `(0, 1)`
            /// (not including either endpoint) with a uniform distribution.
            fn sample<R: SimdRng + ?Sized>(&self, rng: &mut R) -> $ty {
                const EPSILON: $f_scalar = 1.0 / (1u64 << $fraction_bits) as $f_scalar;
                let float_size = mem::size_of::<$f_scalar>() * 8;

                let value = rng.$next_u();
                let fraction = value >> (float_size - $fraction_bits);
                fraction.into_float_with_exponent(0) - $ty::splat(1.0 - EPSILON / 2.0)
            }
        }
    }
}

simd_float_impls! { f32x2, u32x2, f32, u32, 23, 127, next_u32x2 }
simd_float_impls! { f32x4, u32x4, f32, u32, 23, 127, next_u32x4 }
simd_float_impls! { f32x8, u32x8, f32, u32, 23, 127, next_u32x8 }

simd_float_impls! { f64x2, u64x2, f64, u64, 52, 1023, next_u64x2 }
simd_float_impls! { f64x4, u64x4, f64, u64, 52, 1023, next_u64x4 }
simd_float_impls! { f64x8, u64x8, f64, u64, 52, 1023, next_u64x8 }

#[test]
fn simd_float_gen() {
    use simd::sfc_32_simd::*;

    let mut thread_rng = thread_rng();

    for _ in 0..100 {
        let mut a = NonSimdRng::from_rng(&mut thread_rng).unwrap();
        let mut b = NonSimdRng::from_rng(&mut thread_rng).unwrap();

        let mut simd_rng = Sfc32X2::from_non_simd(&[a.clone(), b.clone()]);

        for _ in 0..100_000 {
            // The trait implementation isn't worked out yet so this is just a 
            // global function returning f32x2.
            let actual: f32x2 = Standard.sample(&mut simd_rng);
            let expected = f32x2::new(a.gen::<f32>(), b.gen::<f32>());

            assert_eq!(expected, actual);
        }
    }
}

trait SimdRangeImpl {
    type X;

    fn new(low: Self::X, high: Self::X) -> Self;
    fn new_inclusive(low: Self::X, high: Self::X) -> Self;
    fn sample<R: SimdRng + ?Sized>(&self, rng: &mut R) -> Self::X;
}

macro_rules! simd_range_float_impl {
    ($ty:ty, $uty:ty, $bits_to_discard:expr, $next_u:ident) => {
        impl SimdRangeImpl for RangeFloat<$ty> {
            type X = $ty;

            fn new(low: Self::X, high: Self::X) -> Self {
                let scale = high - low;
                let offset = low - scale;
                RangeFloat {
                    scale: scale,
                    offset: offset,
                }
            }

            fn new_inclusive(low: Self::X, high: Self::X) -> Self {
                // Same as `new`, because the boundaries of a floats range are
                // (at least currently) not exact due to rounding errors.
                Self::new(low, high)
            }

            fn sample<R: SimdRng + ?Sized>(&self, rng: &mut R) -> Self::X {
                // Generate a value in the range [1, 2)
                let integers: $uty = rng.$next_u() >> $bits_to_discard;
                let value1_2: $ty = integers.into_float_with_exponent(0);
                // Doing multiply before addition allows some architectures to
                // use a single instruction.
                value1_2 * self.scale + self.offset
            }
        }
    }
}

simd_range_float_impl! { f32x2, u32x2, 32 - 23, next_u32x2 }
simd_range_float_impl! { f32x4, u32x4, 32 - 23, next_u32x4 }
simd_range_float_impl! { f32x8, u32x8, 32 - 23, next_u32x8 }

simd_range_float_impl! { f64x2, u64x2, 64 - 52, next_u64x2 }
simd_range_float_impl! { f64x4, u64x4, 64 - 52, next_u64x4 }
simd_range_float_impl! { f64x8, u64x8, 64 - 52, next_u64x8 }

#[test]
fn simd_float_range() {
    use simd::sfc_32_simd::*;
    use core::f32;

    let mut thread_rng = thread_rng();

    for i in 0..10_000 {
        let low: f32 = thread_rng.gen_range(0.0, f32::MAX / 3.0);
        let high: f32 = thread_rng.gen_range(low, f32::MAX / 2.0);

        let mut a = NonSimdRng::from_rng(&mut thread_rng).unwrap();
        let mut b = NonSimdRng::from_rng(&mut thread_rng).unwrap();
        let reg_range = RangeFloat::<f32>::new(low, high);

        let mut simd_rng = Sfc32X2::from_non_simd(&[a.clone(), b.clone()]);
        let simd_range: RangeFloat<f32x2> = SimdRangeImpl::new(f32x2::splat(low), f32x2::splat(high));

        for j in 0..1000 {
            let actual: f32x2 = simd_range.sample(&mut simd_rng);
            let expected = f32x2::new(
                reg_range.sample(&mut a),
                reg_range.sample(&mut b),
            );

            assert_eq!(expected, actual, "i {} j {}", i, j);
        }
    }
}
