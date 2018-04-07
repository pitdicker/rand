// Copyright 2017 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// https://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Basic floating-point number distributions

use core::mem;
use Rng;
use distributions::{Distribution, Standard};
use core::simd::*;

pub(crate) trait IntoFloat {
    type F;

    /// Helper method to combine the fraction and a contant exponent into a
    /// float.
    ///
    /// Only the least significant bits of `self` may be set, 23 for `f32` and
    /// 52 for `f64`.
    /// The resulting value will fall in a range that depends on the exponent.
    /// As an example the range with exponent 0 will be
    /// [2<sup>0</sup>..2<sup>1</sup>), which is [1..2).
    fn into_float_with_exponent(self, exponent: i32) -> Self::F;
}

macro_rules! float_impls {
    ($ty:ty, $uty:ty, $fraction_bits:expr, $exponent_bias:expr,
     $next_u:ident) => {
        impl IntoFloat for $uty {
            type F = $ty;
            #[inline(always)]
            fn into_float_with_exponent(self, exponent: i32) -> $ty {
                // The exponent is encoded using an offset-binary representation
                let exponent_bits =
                    (($exponent_bias + exponent) as $uty) << $fraction_bits;
                unsafe { mem::transmute(self | exponent_bits) }
            }
        }

        impl Distribution<$ty> for Standard {
            /// Generate a floating point number in the open interval `(0, 1)`
            /// (not including either endpoint) with a uniform distribution.
            fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> $ty {
                const EPSILON: $ty = 1.0 / (1u64 << $fraction_bits) as $ty;
                let float_size = mem::size_of::<$ty>() * 8;

                let value = rng.$next_u();
                let fraction = value >> (float_size - $fraction_bits);
                fraction.into_float_with_exponent(0) - (1.0 - EPSILON / 2.0)
            }
        }
    }
}
float_impls! { f32, u32, 23, 127, next_u32 }
float_impls! { f64, u64, 52, 1023, next_u64 }


macro_rules! simd_float_impls {
    ($ty:ident, $uty:ident, $f_scalar:ty, $u_scalar:ty, $fraction_bits:expr, $exponent_bias:expr) => {
        impl IntoFloat for $uty {
            type F = $ty;
            #[inline(always)]
            fn into_float_with_exponent(self, exponent: i32) -> $ty {
                // The exponent is encoded using an offset-binary representation
                let exponent_bits: $u_scalar =
                    (($exponent_bias + exponent) as $u_scalar) << $fraction_bits;
                unsafe { mem::transmute(self | $uty::splat(exponent_bits)) }
            }
        }

        impl Distribution<$ty> for Standard {
            /// Generate a floating point number in the open interval `(0, 1)`
            /// (not including either endpoint) with a uniform distribution.
            fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> $ty {
                const EPSILON: $f_scalar = 1.0 / (1u64 << $fraction_bits) as $f_scalar;
                let float_size = mem::size_of::<$f_scalar>() * 8;

                let value: $uty = rng.gen();
                let fraction = value >> (float_size - $fraction_bits);
                fraction.into_float_with_exponent(0) - $ty::splat(1.0 - EPSILON / 2.0)
            }
        }
    }
}

simd_float_impls! { f32x2, u32x2, f32, u32, 23, 127 }
simd_float_impls! { f32x4, u32x4, f32, u32, 23, 127 }
simd_float_impls! { f32x8, u32x8, f32, u32, 23, 127 }

simd_float_impls! { f64x2, u64x2, f64, u64, 52, 1023 }
simd_float_impls! { f64x4, u64x4, f64, u64, 52, 1023 }
simd_float_impls! { f64x8, u64x8, f64, u64, 52, 1023 }


#[cfg(test)]
mod tests {
    use Rng;
    use mock::StepRng;

    const EPSILON32: f32 = ::core::f32::EPSILON;
    const EPSILON64: f64 = ::core::f64::EPSILON;

    #[test]
    fn floating_point_edge_cases() {
        let mut zeros = StepRng::new(0, 0);
        assert_eq!(zeros.gen::<f32>(), 0.0 + EPSILON32 / 2.0);
        assert_eq!(zeros.gen::<f64>(), 0.0 + EPSILON64 / 2.0);

        let mut one = StepRng::new(1 << 9, 0);
        let one32 = one.gen::<f32>();
        assert!(EPSILON32 < one32 && one32 < EPSILON32 * 2.0);

        let mut one = StepRng::new(1 << 12, 0);
        let one64 = one.gen::<f64>();
        assert!(EPSILON64 < one64 && one64 < EPSILON64 * 2.0);

        let mut max = StepRng::new(!0, 0);
        assert_eq!(max.gen::<f32>(), 1.0 - EPSILON32 / 2.0);
        assert_eq!(max.gen::<f64>(), 1.0 - EPSILON64 / 2.0);
    }
}
