use simd::rng_impl::*;
use core::fmt;

#[derive(Clone)]
pub struct Sfc32Rng {
    pub(crate) a: u32,
    pub(crate) b: u32,
    pub(crate) c: u32,
    counter: u32,
}


// Custom Debug implementation that does not expose the internal state
impl fmt::Debug for Sfc32Rng {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Sfc32Rng {{}}")
    }
}

impl Sfc32Rng {
    pub fn from_good_seed(seed: [u32; 3]) -> Self {
        Self {
            a: seed[0],
            b: seed[1],
            c: seed[2],
            counter: 1,
        }
    }
}

impl SeedableRng for Sfc32Rng {
    type Seed = [u8; 32 * 3 / 8];

    fn from_seed(seed: Self::Seed) -> Self {
        let mut seed_u32 = [0_u32; 3];
        le::read_u32_into(&seed, &mut seed_u32);

        let mut state = Self::from_good_seed(seed_u32);
        // Skip the first 15 outputs, just in case we have a bad seed.
        for _ in 0..15 {
            state.next_u32();
        }
        state
    }

    fn from_rng<R: RngCore>(mut rng: R) -> Result<Self, Error> {
        let mut seed_u32 = [0_u32; 3];
        unsafe {
            let ptr = seed_u32.as_mut_ptr() as *mut u8;

            let slice = slice::from_raw_parts_mut(ptr, 32 * 3 / 8);
            rng.try_fill_bytes(slice)?;
        }

        // Custom `from_rng` function. Because we can assume the seed to be of
        // good quality, it is not necessary to discard the first couple of
        // rounds.
        for s in &mut seed_u32 {
            *s |= 1;
        }
        Ok(Self::from_good_seed(seed_u32))
    }
}

impl RngCore for Sfc32Rng {
    #[inline]
    fn next_u32(&mut self) -> u32 {
        // good sets include {21,9,3} and {15,8,3}
        const BARREL_SHIFT: u32 = 21;
        const RSHIFT: u32 = 9;
        const LSHIFT: u32 = 3;

        let tmp = self.a.wrapping_add(self.b).wrapping_add(self.counter);
        self.counter += 1;
        self.a = self.b ^ (self.b >> RSHIFT);
        self.b = self.c.wrapping_add(self.c << LSHIFT);
        self.c = self.c.rotate_left(BARREL_SHIFT).wrapping_add(tmp);
        tmp
    }

    fn next_u64(&mut self) -> u64 {
        impls::next_u64_via_u32(self)
    }

    fn fill_bytes(&mut self, dest: &mut [u8]) {
        impls::fill_bytes_via_u32(self, dest)
    }

    fn try_fill_bytes(&mut self, dest: &mut [u8]) -> Result<(), Error> {
        Ok(self.fill_bytes(dest))
    }
}

/// A Small Fast Counting RNG designed by Chris Doty-Humphrey (64-bit version).
///
/// - Author: Chris Doty-Humphrey
/// - License: Public domain
/// - Source: [PractRand](http://pracrand.sourceforge.net/)
/// - Period: avg ~ 2<sup>255</sup>, min >= 2<sup>64</sup>
/// - State: 256 bits
/// - Word size: 64 bits
/// - Seed size: 192 bits
/// - Passes BigCrush and PractRand
#[derive(Clone, Copy, Debug)]
pub struct Sfc64Rng {
    pub(crate) a: u64,
    pub(crate) b: u64,
    pub(crate) c: u64,
    counter: u64,
}

impl Sfc64Rng {
    pub fn from_good_seed(seed: [u64; 3]) -> Self {
        Self {
            a: seed[0],
            b: seed[1],
            c: seed[2],
            counter: 1,
        }
    }
}

impl SeedableRng for Sfc64Rng {
    type Seed = [u8; 64 * 3 / 8];

    fn from_seed(seed: Self::Seed) -> Self {
        let mut seed_u64 = [0_u64; 3];
        le::read_u64_into(&seed, &mut seed_u64);

        let mut state = Self::from_good_seed(seed_u64);
        // Skip the first 15 outputs, just in case we have a bad seed.
        for _ in 0..15 {
            state.next_u64();
        }
        state
    }

    fn from_rng<R: RngCore>(mut rng: R) -> Result<Self, Error> {
        let mut seed_u64 = [0_u64; 3];
        unsafe {
            let ptr = seed_u64.as_mut_ptr() as *mut u8;

            let slice = slice::from_raw_parts_mut(ptr, 64 * 3 / 8);
            rng.try_fill_bytes(slice)?;
        }

        // Custom `from_rng` function. Because we can assume the seed to be of
        // good quality, it is not necessary to discard the first couple of
        // rounds.
        for s in &mut seed_u64 {
            *s |= 1;
        }
        Ok(Self::from_good_seed(seed_u64))
    }
}

impl RngCore for Sfc64Rng {
    #[inline]
    fn next_u32(&mut self) -> u32 {
        self.next_u64() as u32
    }

    #[inline]
    fn next_u64(&mut self) -> u64 {
        // good sets include {24,11,3} and {25,12,3}
        const BARREL_SHIFT: u32 = 24;
        const RSHIFT: u32 = 11;
        const LSHIFT: u32 = 3;

        let tmp = self.a.wrapping_add(self.b).wrapping_add(self.counter);
        self.counter += 1;
        self.a = self.b ^ (self.b >> RSHIFT);
        self.b = self.c.wrapping_add(self.c << LSHIFT);
        self.c = self.c.rotate_left(BARREL_SHIFT).wrapping_add(tmp);
        tmp
    }

    fn fill_bytes(&mut self, dest: &mut [u8]) {
        impls::fill_bytes_via_u32(self, dest)
    }

    fn try_fill_bytes(&mut self, dest: &mut [u8]) -> Result<(), Error> {
        Ok(self.fill_bytes(dest))
    }
}
