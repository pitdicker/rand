// Copyright 2018 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// https://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! `AsRef<[u32]>` support for SIMD types.

#[cfg(feature="simd_support")]
use core::simd::*;


/// FIXME
#[derive(Copy, Clone, Debug)]
pub struct SimdArray<T>(T);


impl<T: AsRefHelper> From<T> for SimdArray<T> {
    fn from(vector: T) -> SimdArray<T> {
        SimdArray(vector)
    }
}

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
            #[inline(always)]
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
