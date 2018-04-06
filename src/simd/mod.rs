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
