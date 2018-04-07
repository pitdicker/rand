//! SIMD implementations

#[cfg(test)]
const SIMD_CORRECTNESS_N: usize = 30;
#[cfg(test)]
const SIMD_CORRECTNESS_SEEDS: usize = 10;

#[macro_use]
mod macros;

mod float;
mod sfc_32_simd;
mod sfc;

pub use self::sfc_32_simd::*;
pub use self::float::SimdDistribution;

use self::sfc::*;
use core::simd::*;

/// FIXME
#[derive(Copy, Clone, Debug)]
pub struct SimdArray<T>(T);

impl<T> ::core::convert::AsRef<[u32]> for SimdArray<T> where T: AsRefHelper {
    #[inline(always)]
    fn as_ref(&self) -> &[u32] {
        AsRefHelper::as_ref_helper(&self.0)
    }
}

impl<T> ::core::default::Default for SimdArray<T> where T: Copy + Default {
    fn default() -> SimdArray<T> {
        SimdArray( T::default() )
    }
}

/// FIXME
pub trait AsRefHelper {
    /// FIXME
    fn as_ref_helper(&self) -> &[u32];
}

macro_rules! asref_helper {
    ($bits:expr,) => {};
    ($bits:expr, $ty:ty, $($ty_more:ty,)*) => {
        asref_helper!($bits, $($ty_more,)*);

        impl AsRefHelper for $ty {
            fn as_ref_helper(&self) -> &[u32]{
                unsafe {
                    &*(self as *const Self as *const [u32; $bits/8])
                }
            }
        }
    }
}

// Not implemented for SIMD types < 64 bits
asref_helper!(64, u8x8, i8x8, u16x4, i16x4, u32x2, i32x2,);
asref_helper!(128, u8x16, i8x16, u16x8, i16x8, u32x4, i32x4, u64x2, i64x2,);
asref_helper!(256, u8x32, i8x32, u16x16, i16x16, u32x8, i32x8, u64x4, i64x4,);
asref_helper!(512, u8x64, i8x64, u16x32, i16x32, u32x16, i32x16, u64x8, i64x8,);




/// A convenience import for implementing PRNGs
pub mod rng_impl {
    pub use rand_core::{RngCore, SeedableRng, Error, impls, le};
    pub use core::slice;
    pub use Rng;
}

///
pub trait SimdRng {
    ///
    fn next_u32x2(&mut self) -> u32x2 {
        unimplemented!()
    }
    ///
    fn next_u32x4(&mut self) -> u32x4 {
        unimplemented!()
    }
    ///
    fn next_u32x8(&mut self) -> u32x8 {
        unimplemented!()
    }
    ///
    fn next_u64x2(&mut self) -> u64x2 {
        unimplemented!()
    }
    ///
    fn next_u64x4(&mut self) -> u64x4 {
        unimplemented!()
    }
    ///
    fn next_u64x8(&mut self) -> u64x8 {
        unimplemented!()
    }
}
