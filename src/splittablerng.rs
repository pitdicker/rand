// Copyright 2013 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// https://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! A wrapper around another PRNG that reseeds it after it
//! generates a certain number of random bytes.

use core::cell::Cell;
use rand_core::{RngCore, CryptoRng, SeedableRng, Error};

/// FIXME: documentation
#[derive(Debug)]
pub struct SplittableRng<R> {
    split_level: Cell<u8>,
    rng: R,
}

impl<R> SplittableRng<R>
    where R: RngCore + SeedableRng + Clone
{
    /// Create a new `SplittableRng` around an existing RNG.
    pub fn new(rng: R) -> Self {
        SplittableRng { split_level: Cell::new(0), rng }
    }

    /// Return a reference the wrapped RNG.
    pub fn inner(&self) -> &R {
        &self.rng
    }

    /// Return a mutable reference the wrapped RNG.
    pub fn inner_mut(&mut self) -> &mut R {
        &mut self.rng
    }

    /// Split: BIG WARNING use recursively, not sequentially
    pub fn split_recursive(&mut self) -> Self {
        self.clone()
    }

    // TODO: inner, inner_mut
    // split_recursive
    // split_n
}

impl<R: Clone + RngCore + SeedableRng> Clone for SplittableRng<R> {
    fn clone(&self) -> Self {
        self.split_level.set(self.split_level.get().wrapping_add(1)); // FIXME: what to do on overflow?
        SplittableRng {
            split_level: self.split_level.clone(),
            rng: self.rng.split(self.split_level.get()),
        }
    }
}

impl<R: RngCore> RngCore for SplittableRng<R> {
    #[inline(always)]
    fn next_u32(&mut self) -> u32 {
        self.rng.next_u32()
    }

    #[inline(always)]
    fn next_u64(&mut self) -> u64 {
        self.rng.next_u64()
    }

    #[inline(always)]
    fn fill_bytes(&mut self, dest: &mut [u8]) {
        self.rng.fill_bytes(dest)
    }

    #[inline(always)]
    fn try_fill_bytes(&mut self, dest: &mut [u8]) -> Result<(), Error> {
        self.rng.try_fill_bytes(dest)
    }
}

impl<R: SeedableRng> SeedableRng for SplittableRng<R> {
    type Seed = <R as SeedableRng>::Seed;

    fn from_seed(seed: Self::Seed) -> Self {
        SplittableRng { split_level: Cell::new(0), rng: R::from_seed(seed) }
    }

    fn from_rng<S: RngCore>(rng: S) -> Result<Self, Error> {
        R::from_rng(rng).map(|new|
            SplittableRng { split_level: Cell::new(0), rng: new }
        )
    }
    
    // TODO: split
}

impl<R: CryptoRng> CryptoRng for SplittableRng<R> {}
