// Copyright 2017 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// https://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Functions for randomly accessing and sampling sequences.

use core;
use core::cmp;
use Rng;
use distributions::range::WideningMultiply;
use distributions::Exp1;

#[cfg(feature="std")] use std::collections::HashMap;
#[cfg(all(feature="alloc", not(feature="std")))] use alloc::btree_map::BTreeMap;

#[cfg(all(feature="alloc", not(feature="std")))] use alloc::Vec;

pub trait SliceRandom {
    type Item;

    /// Shuffle a slice in place.
    ///
    /// This applies Durstenfeld's algorithm for the [Fisher–Yates shuffle](
    /// https://wikipedia.org/wiki/Fisher%E2%80%93Yates_shuffle), which produces
    /// an unbiased permutation.
    ///
    /// # Example
    ///
    /// ```rust
    /// use rand::thread_rng;
    /// use rand::seq::SliceRandom;
    ///
    /// let mut rng = thread_rng();
    /// let mut y = [1, 2, 3];
    /// y.shuffle(&mut rng);
    /// println!("{:?}", y);
    /// y.shuffle(&mut rng);
    /// println!("{:?}", y);
    /// ```
    fn shuffle<R>(&mut self, rng: &mut R)
        where R: Rng + ?Sized;

    /// Shuffle a slice in place, but exit early.
    ///
    /// Returns two mutable slices from the source slice. The first contains
    /// `amount` elements randomly permuted. The second has the remaining
    /// elements that are not fully shuffled.
    ///
    /// This is an efficient method to select `amount` elements at random from
    /// the slice, provided the slice may be mutated.
    ///
    /// If you only need to chose elements randomly and `amount > self.len()/2`
    /// then you may improve performance by taking
    /// `amount = values.len() - amount` and using only the second slice.
    ///
    /// If `amount` is greater than the number of elements in the slice, this
    /// will perform a full shuffle.
    fn partial_shuffle<R>(&mut self, rng: &mut R, amount: usize)
        -> (&mut [Self::Item], &mut [Self::Item]) where R: Rng + ?Sized;

    /// Returns a reference to one random element of the slice, or `None` if the
    /// slice is empty.
    ///
    /// # Example
    ///
    /// ```
    /// use rand::thread_rng;
    /// use rand::seq::SliceRandom;
    ///
    /// let choices = [1, 2, 4, 8, 16, 32];
    /// let mut rng = thread_rng();
    /// println!("{:?}", choices.pick(&mut rng));
    /// assert_eq!(choices[..0].pick(&mut rng), None);
    /// ```
    fn pick<R>(&self, rng: &mut R) -> Option<&Self::Item>
        where R: Rng + ?Sized;

    /// Returns a mutable reference to one random element of the slice, or
    /// `None` if the slice is empty.
    fn pick_mut<R>(&mut self, rng: &mut R) -> Option<&mut Self::Item>
        where R: Rng + ?Sized;

    /// Produces an iterator that chooses `amount` elements from the slice at
    /// random without repeating any, in sequential order.
    fn pick_multiple<'a, R: Rng>(&'a self, amount: usize, rng: &'a mut R)
        -> RandomSampler<'a, Self::Item, R>;

    // TODO: pick_multiple_mut
}

impl<T> SliceRandom for [T] {
    type Item = T;

    fn shuffle<R>(&mut self, rng: &mut R)
        where R: Rng + ?Sized
    {
        let len = self.len();
        self.partial_shuffle(rng, len);
    }

    fn partial_shuffle<R>(&mut self, rng: &mut R, amount: usize)
        -> (&mut [Self::Item], &mut [Self::Item]) where R: Rng + ?Sized
    {
        let stop = self.len().saturating_sub(amount);

        let mut i = self.len() as u64;
        while i > cmp::max(1 << 31, stop as u64) {
            i -= 1;
            self.swap(i as usize, rng.gen_range(0, i + 1) as usize);
        }

        let mut i = i as u32;
        while i > cmp::max(1 << 15, stop as u32) {
            i -= 1;
            self.swap(i as usize, rng.gen_range(0, i + 1) as usize);
        }

        let mut i = i as u16;
        while i > cmp::max(4, stop as u16) {
            // Reimplement the range reduction here, because we can do better
            // than generating 32 bits and throwing away half of them.
            let mut value: u64 = rng.gen();
            for _ in 0..4 {
                let val = value as u16;
                value = value >> 16;
                let range = i + 1;
                let (hi, lo) = val.wmul(range);
                let zone = core::u16::MAX - (core::u16::MAX - range + 1) % range;
                if lo <= zone {
                    i -= 1;
                    self.swap(i as usize, hi as usize);
                }
            }
        }

        while i > cmp::max(1, stop as u16) {
            i -= 1;
            self.swap(i as usize, rng.gen_range(0, i + 1) as usize);
        }

        let r = self.split_at_mut(stop);
        (r.1, r.0)
    }

    fn pick<R>(&self, rng: &mut R) -> Option<&Self::Item>
        where R: Rng + ?Sized
    {
        if self.is_empty() {
            None
        } else {
            Some(&self[rng.gen_range(0, self.len())])
        }
    }

    fn pick_mut<R>(&mut self, rng: &mut R) -> Option<&mut Self::Item>
        where R: Rng + ?Sized
    {
        if self.is_empty() {
            None
        } else {
            let len = self.len();
            Some(&mut self[rng.gen_range(0, len)])
        }
    }

    fn pick_multiple<'a, R: Rng>(&'a self, amount: usize, rng: &'a mut R)
        -> RandomSampler<'a, Self::Item, R>
    {
        let sampler = SequentialRandomSampler::new(amount, self.len(), rng);
        RandomSampler {
            slice: self,
            index: 0,
            sampler: sampler,
            rng: rng,
        }
    }
}

#[derive(Debug)]
pub struct RandomSampler<'a, T: 'a, R: Rng + 'a> {
    slice: &'a [T],
    index: usize, // FIXME: or do we want to move the base pointer of the slice?
    sampler: SequentialRandomSampler,
    rng: &'a mut R,
}

impl<'a, T: 'a, R: Rng + 'a> Iterator for RandomSampler<'a, T, R> {
    type Item = &'a T;

    #[inline(always)]
    fn next(&mut self) -> Option<&'a T> {
        if self.sampler.n > 1 {
            self.index += self.sampler.calculate_skip(self.rng) + 1;
            Some(&self.slice[self.index - 1])
        } else if self.sampler.n == 1 {
            // Optimization: only one more element left to sample.
            // Pick directly, instead of calculating the number of elements
            // to skip.
            self.index += (self.sampler.remaining as f64 * self.sampler.v_prime) as usize;
            self.sampler.n = 0;
            Some(&self.slice[self.index])
        } else {
            None
        }
    }
}

impl<'a, T: 'a, R: Rng + 'a> ExactSizeIterator for RandomSampler<'a, T, R> {
    // Remaining number of iterations.
    fn len(&self) -> usize {
        self.sampler.n
    }
}

/*
Jeffrey Vitter introduced algorithm **A** and **D** (Edit: and **B** and **C** in-between) to efficiently sample from a known number of elements sequentially, without needing extra memory. ([*Faster Methods for Random Sampling*](http://www.mathcs.emory.edu/~cheung/papers/StreamDB/RandomSampling/1984-Vitter-Faster-random-sampling.pdf), 1984 and [*Efficient Algorithm for Sequential Random Sampling*](http://www.ittc.ku.edu/~jsv/Papers/Vit87.RandomSampling.pdf), 1987)

K. Aiyappan Nair improved upon it with algorithm **E**. (*An Improved Algorithm for Ordered Sequential Random Sampling*, 1990)
*/


// We convert between `f64` and `usize` without caring about possible round-off
// errors. All `usize` values up to 2^52 are exactly representable in `f64`.
// For comparison: on 32-bit we can't have slices > 2^31, and on 64-bit the
// current virtual address space is limited to 2^48 (256 TiB).
#[derive(Debug)]
struct SequentialRandomSampler {
    // remaining number of elements to sample from.
    pub remaining: usize, // Called `N` in the paper.
    // number of elements that should still be sampled.
    pub n: usize,
    // Values cached between runs:
    v_prime: f64,     // FIXME
    threshold: usize, // threshold before switching from method D to method A.
}

// Threshold before switching from method D to method A.
// Typical values of α can be expected in the range 0.05-0.15. The paper
// suggests 1/13, but we because we can make use of the fast Ziggurat method to
// generate exponential values, our method D is relatively fast so α = 1/10
// seems better.
const ALPHA_INV: usize = 10; // (1.0 / α)

impl SequentialRandomSampler {
    fn new<R: Rng>(n: usize, total: usize, rng: &mut R) -> Self {
        let n = cmp::min(n, total);
        Self {
            remaining: total,
            n: n,
            v_prime: (rng.gen::<f64>().ln() / (n as f64)).exp(),
            threshold: n * ALPHA_INV,
        }
    }

    // FIXME: should this handle n <= 1?
    fn calculate_skip<R: Rng>(&mut self, rng: &mut R) -> usize {
        if self.remaining > self.threshold {
            self.threshold -= ALPHA_INV;
            self.method_d_skip(rng)
        } else {
            self.threshold -= ALPHA_INV;
            self.method_a_skip(rng)
        }
    }

    fn method_a_skip<R: Rng>(&mut self, rng: &mut R) -> usize {
        let mut skip = 0; // Called `S` in the paper.
        let mut remaining_f = self.remaining as f64;
        let n_f = self.n as f64;

        // Step A1
        let v: f64 = rng.gen();

        // Step A2
        // Search sequentially for the smallest integer S satisfying the
        // inequality  V ≤ ((N - n) / n)^(S+1).
        let mut top = remaining_f - n_f;
        let mut quot = top / remaining_f;
        while quot > v {
            skip += 1;
            top -= 1.0;
            remaining_f -= 1.0;
            quot = quot * top / remaining_f;
        }

        // Prepare variables for the next iteration.
        // Note: the paper(s) forgot to subtract `skip`.
        self.remaining -= skip + 1;
        self.n -= 1;
        skip
    }

    fn method_d_skip<R: Rng>(&mut self, rng: &mut R) -> usize {
        let mut skip; // Called `S` in the paper.

        // Cache a couple of variables and expressions we use multiple times.
        let remaining_f = self.remaining as f64;
        let n_f = self.n as f64;
        let ninv = 1.0 / n_f;
        let nmin1inv = 1.0 / (n_f - 1.0);
        let qu1 = self.remaining - self.n + 1;
        let qu1_f = remaining_f - n_f + 1.0;

        loop {
            // Step D2: Generate U and X.
            // "Generate a random variate U that is uniformly distributed
            // between 0 and 1, and a random variate X that has density
            // function or probability function g(x)."
            //
            //        ⎧  n  ⎛      x  ⎞ n-1
            //        ⎪ --- ⎜ 1 - --- ⎟    ,   0 ≤ x ≤ N;
            // g(x) = ⎨  N  ⎝      N  ⎠
            //        ⎪
            //        ⎩  0,                    otherwise;
            //
            // Note: we rename U → u and X → x.
            let mut x;
            loop {
                x = remaining_f * (1.0 - self.v_prime);
                skip = x as usize;
                if skip < qu1 { break; }
                self.v_prime = (-rng.sample(Exp1) * ninv).exp();
            }
            let skip_f = skip as f64;

            // Step D3: Accept?
            // Do a quick approximation to decide whether `x` should be rejected
            //
            // If `x` ≤ h(⌊x⌋)/cg(x), then set `skip` = ⌊x⌋ and go to Step D5.
            // We use the fast method from formula (2.7 + 2.8) here.
            //

            //      ⎛     N U     ⎞ n-1    N - n + 1       N - X
            // V' = ⎜ ----------- ⎟     --------------- * -------
            //      ⎝  N - n + 1  ⎠      N - n - S + 1       N
            //
            // V' ≤ 1?
            //
            // Note: `qu1_f == N - n + 1`
            let y1 = (1.0 / qu1_f - rng.sample(Exp1) * nmin1inv).exp();
            self.v_prime =
                y1 * (qu1_f / (qu1_f - skip_f)) * (1.0 - x / remaining_f);
            if self.v_prime <= 1.0 { break; }

            // Step D4: Accept?
            // Try again using the more expensive method:
            // If U ≤ f(⌊X⌋)/cg(X), then set S := ⌊X⌋.
            // Otherwise, return to Step D2.
            let mut y2 = 1.0;
            let mut top = remaining_f - 1.0;

            let mut bottom;
            let limit;
            if self.n > skip + 1 {
                bottom = remaining_f - n_f;
                limit = self.remaining - skip;
            } else {
                bottom = remaining_f - skip_f - 1.0;
                limit = qu1;
            }
            let mut t = self.remaining - 1;
            while t >= limit {
                y2 = y2 * top / bottom;
                top -= 1.0;
                bottom -= 1.0;
                t -= 1;
            }

            if remaining_f / (remaining_f - x) >= y1 * (y2.ln() * nmin1inv).exp() {
                self.v_prime = (-rng.sample(Exp1) * nmin1inv).exp();
                break; // Accept!
            }

            // We were unlucky, `x` is rejected.
            // Generate a new V' and go back to the beginning.
            self.v_prime = (-rng.sample(Exp1) * ninv).exp();
        }

        // Prepare variables for the next iteration.
        // V' (`self.v_prime`) is already prepared in the loop)
        self.remaining -= skip + 1;
        self.n -= 1;
        skip
    }
}


/// Robert FLoyd's algorithm
/// ```text
/// initialize set S to empty
/// for J := N - M + 1 to N do
///     T := RandInt(1, J)
///     if T is not in S then
///         insert T in S
///       else
///         insert J in S
/// ```
pub fn choose_from_range<R: Rng + ?Sized>(rng: &mut R, n: u32, results: &mut [u32]) {
    let m = results.len() as u32;
    assert!(m <= n); // FIXME: check
    let s = results;

    let mut i = 0;
    for j in (n - m + 1)..(n + 1) { // FIXME: should this be N or N+1?
        let t = rng.gen_range(1, j);
        s[i] = if s[0..i].contains(&t) { j - 1 } else { j };
        i += 1
    }
}

/// Randomly sample `amount` elements from a finite iterator.
///
/// The following can be returned:
///
/// - `Ok`: `Vec` of `amount` non-repeating randomly sampled elements. The order is not random.
/// - `Err`: `Vec` of all the elements from `iterable` in sequential order. This happens when the
///   length of `iterable` was less than `amount`. This is considered an error since exactly
///   `amount` elements is typically expected.
///
/// This implementation uses `O(len(iterable))` time and `O(amount)` memory.
///
/// # Example
///
/// ```rust
/// use rand::{thread_rng, seq};
///
/// let mut rng = thread_rng();
/// let sample = seq::sample_iter(&mut rng, 1..100, 5).unwrap();
/// println!("{:?}", sample);
/// ```
#[cfg(feature="alloc")]
pub fn sample_iter<T, I, R>(rng: &mut R, iterable: I, amount: usize) -> Result<Vec<T>, Vec<T>>
    where I: IntoIterator<Item=T>,
          R: Rng + ?Sized,
{
    let mut iter = iterable.into_iter();
    let mut reservoir = Vec::with_capacity(amount);
    reservoir.extend(iter.by_ref().take(amount));

    // Continue unless the iterator was exhausted
    //
    // note: this prevents iterators that "restart" from causing problems.
    // If the iterator stops once, then so do we.
    if reservoir.len() == amount {
        for (i, elem) in iter.enumerate() {
            let k = rng.gen_range(0, i + 1 + amount);
            if let Some(spot) = reservoir.get_mut(k) {
                *spot = elem;
            }
        }
        Ok(reservoir)
    } else {
        // Don't hang onto extra memory. There is a corner case where
        // `amount` was much less than `len(iterable)`.
        reservoir.shrink_to_fit();
        Err(reservoir)
    }
}

/// Randomly sample exactly `amount` values from `slice`.
///
/// The values are non-repeating and in random order.
///
/// This implementation uses `O(amount)` time and memory.
///
/// Panics if `amount > slice.len()`
///
/// # Example
///
/// ```rust
/// use rand::{thread_rng, seq};
///
/// let mut rng = thread_rng();
/// let values = vec![5, 6, 1, 3, 4, 6, 7];
/// println!("{:?}", seq::sample_slice(&mut rng, &values, 3));
/// ```
#[cfg(feature="alloc")]
pub fn sample_slice<R, T>(rng: &mut R, slice: &[T], amount: usize) -> Vec<T>
    where R: Rng + ?Sized,
          T: Clone
{
    let indices = sample_indices(rng, slice.len(), amount);

    let mut out = Vec::with_capacity(amount);
    out.extend(indices.iter().map(|i| slice[*i].clone()));
    out
}

/// Randomly sample exactly `amount` references from `slice`.
///
/// The references are non-repeating and in random order.
///
/// This implementation uses `O(amount)` time and memory.
///
/// Panics if `amount > slice.len()`
///
/// # Example
///
/// ```rust
/// use rand::{thread_rng, seq};
///
/// let mut rng = thread_rng();
/// let values = vec![5, 6, 1, 3, 4, 6, 7];
/// println!("{:?}", seq::sample_slice_ref(&mut rng, &values, 3));
/// ```
#[cfg(feature="alloc")]
pub fn sample_slice_ref<'a, R, T>(rng: &mut R, slice: &'a [T], amount: usize) -> Vec<&'a T>
    where R: Rng + ?Sized
{
    let indices = sample_indices(rng, slice.len(), amount);

    let mut out = Vec::with_capacity(amount);
    out.extend(indices.iter().map(|i| &slice[*i]));
    out
}

/// Randomly sample exactly `amount` indices from `0..length`.
///
/// The values are non-repeating and in random order.
///
/// This implementation uses `O(amount)` time and memory.
///
/// This method is used internally by the slice sampling methods, but it can sometimes be useful to
/// have the indices themselves so this is provided as an alternative.
///
/// Panics if `amount > length`
#[cfg(feature="alloc")]
pub fn sample_indices<R>(rng: &mut R, length: usize, amount: usize) -> Vec<usize>
    where R: Rng + ?Sized,
{
    if amount > length {
        panic!("`amount` must be less than or equal to `slice.len()`");
    }

    // We are going to have to allocate at least `amount` for the output no matter what. However,
    // if we use the `cached` version we will have to allocate `amount` as a HashMap as well since
    // it inserts an element for every loop.
    //
    // Therefore, if `amount >= length / 2` then inplace will be both faster and use less memory.
    // In fact, benchmarks show the inplace version is faster for length up to about 20 times
    // faster than amount.
    //
    // TODO: there is probably even more fine-tuning that can be done here since
    // `HashMap::with_capacity(amount)` probably allocates more than `amount` in practice,
    // and a trade off could probably be made between memory/cpu, since hashmap operations
    // are slower than array index swapping.
    if amount >= length / 20 {
        sample_indices_inplace(rng, length, amount)
    } else {
        sample_indices_cache(rng, length, amount)
    }
}

/// Sample an amount of indices using an inplace partial fisher yates method.
///
/// This allocates the entire `length` of indices and randomizes only the first `amount`.
/// It then truncates to `amount` and returns.
///
/// This is better than using a `HashMap` "cache" when `amount >= length / 2`
/// since it does not require allocating an extra cache and is much faster.
#[cfg(feature="alloc")]
fn sample_indices_inplace<R>(rng: &mut R, length: usize, amount: usize) -> Vec<usize>
    where R: Rng + ?Sized,
{
    debug_assert!(amount <= length);
    let mut indices: Vec<usize> = Vec::with_capacity(length);
    indices.extend(0..length);
    for i in 0..amount {
        let j: usize = rng.gen_range(i, length);
        indices.swap(i, j);
    }
    indices.truncate(amount);
    debug_assert_eq!(indices.len(), amount);
    indices
}


/// This method performs a partial fisher-yates on a range of indices using a
/// `HashMap` as a cache to record potential collisions.
///
/// The cache avoids allocating the entire `length` of values. This is especially useful when
/// `amount <<< length`, i.e. select 3 non-repeating from `1_000_000`
#[cfg(feature="alloc")]
fn sample_indices_cache<R>(
    rng: &mut R,
    length: usize,
    amount: usize,
) -> Vec<usize>
    where R: Rng + ?Sized,
{
    debug_assert!(amount <= length);
    #[cfg(feature="std")] let mut cache = HashMap::with_capacity(amount);
    #[cfg(not(feature="std"))] let mut cache = BTreeMap::new();
    let mut out = Vec::with_capacity(amount);
    for i in 0..amount {
        let j: usize = rng.gen_range(i, length);

        // equiv: let tmp = slice[i];
        let tmp = match cache.get(&i) {
            Some(e) => *e,
            None => i,
        };

        // equiv: slice[i] = slice[j];
        let x = match cache.get(&j) {
            Some(x) => *x,
            None => j,
        };

        // equiv: slice[j] = tmp;
        cache.insert(j, tmp);

        // note that in the inplace version, slice[i] is automatically "returned" value
        out.push(x);
    }
    debug_assert_eq!(out.len(), amount);
    out
}

#[cfg(test)]
mod test {
    use super::*;
    use {XorShiftRng, Rng, SeedableRng};
    #[cfg(all(feature="alloc", not(feature="std")))]
    use alloc::Vec;
    use thread_rng;

    #[test]
    #[cfg(feature="alloc")]
    fn test_algorithm_d() {
        let min_val = 1;
        let max_val = 1000;

        let mut r = thread_rng();
        let vals = (min_val..max_val).collect::<Vec<i32>>();
        let small_sample: Vec<_> = vals.pick_multiple(15, &mut r).collect();

        println!("{:?}", small_sample);
    }

    #[test]
    #[cfg(feature="alloc")]
    fn test_algorithm_d_50_of_100() {
        let mut r = thread_rng();
        let vals = (0..100).collect::<Vec<i32>>();
        let small_sample: Vec<_> = vals.pick_multiple(50, &mut r).collect();

        println!("{:?}", small_sample);
    }

    #[test]
    #[cfg(feature="alloc")]
    fn test_sample_iter() {
        let min_val = 1;
        let max_val = 100;

        let mut r = ::test::rng(401);
        let vals = (min_val..max_val).collect::<Vec<i32>>();
        let small_sample = sample_iter(&mut r, vals.iter(), 5).unwrap();
        let large_sample = sample_iter(&mut r, vals.iter(), vals.len() + 5).unwrap_err();

        assert_eq!(small_sample.len(), 5);
        assert_eq!(large_sample.len(), vals.len());
        // no randomization happens when amount >= len
        assert_eq!(large_sample, vals.iter().collect::<Vec<_>>());

        assert!(small_sample.iter().all(|e| {
            **e >= min_val && **e <= max_val
        }));
    }

    #[test]
    #[cfg(feature="alloc")]
    fn test_sample_slice_boundaries() {
        let empty: &[u8] = &[];

        let mut r = ::test::rng(402);

        // sample 0 items
        assert_eq!(&sample_slice(&mut r, empty, 0)[..], [0u8; 0]);
        assert_eq!(&sample_slice(&mut r, &[42, 2, 42], 0)[..], [0u8; 0]);

        // sample 1 item
        assert_eq!(&sample_slice(&mut r, &[42], 1)[..], [42]);
        let v = sample_slice(&mut r, &[1, 42], 1)[0];
        assert!(v == 1 || v == 42);

        // sample "all" the items
        let v = sample_slice(&mut r, &[42, 133], 2);
        assert!(&v[..] == [42, 133] || v[..] == [133, 42]);

        assert_eq!(&sample_indices_inplace(&mut r, 0, 0)[..], [0usize; 0]);
        assert_eq!(&sample_indices_inplace(&mut r, 1, 0)[..], [0usize; 0]);
        assert_eq!(&sample_indices_inplace(&mut r, 1, 1)[..], [0]);

        assert_eq!(&sample_indices_cache(&mut r, 0, 0)[..], [0usize; 0]);
        assert_eq!(&sample_indices_cache(&mut r, 1, 0)[..], [0usize; 0]);
        assert_eq!(&sample_indices_cache(&mut r, 1, 1)[..], [0]);

        // Make sure lucky 777's aren't lucky
        let slice = &[42, 777];
        let mut num_42 = 0;
        let total = 1000;
        for _ in 0..total {
            let v = sample_slice(&mut r, slice, 1);
            assert_eq!(v.len(), 1);
            let v = v[0];
            assert!(v == 42 || v == 777);
            if v == 42 {
                num_42 += 1;
            }
        }
        let ratio_42 = num_42 as f64 / 1000 as f64;
        assert!(0.4 <= ratio_42 || ratio_42 <= 0.6, "{}", ratio_42);
    }

    #[test]
    #[cfg(feature="alloc")]
    fn test_sample_slice() {
        let xor_rng = XorShiftRng::from_seed;

        let max_range = 100;
        let mut r = ::test::rng(403);

        for length in 1usize..max_range {
            let amount = r.gen_range(0, length);
            let mut seed = [0u8; 16];
            r.fill(&mut seed);

            // assert that the two index methods give exactly the same result
            let inplace = sample_indices_inplace(
                &mut xor_rng(seed), length, amount);
            let cache = sample_indices_cache(
                &mut xor_rng(seed), length, amount);
            assert_eq!(inplace, cache);

            // assert the basics work
            let regular = sample_indices(
                &mut xor_rng(seed), length, amount);
            assert_eq!(regular.len(), amount);
            assert!(regular.iter().all(|e| *e < length));
            assert_eq!(regular, inplace);

            // also test that sampling the slice works
            let vec: Vec<usize> = (0..length).collect();
            {
                let result = sample_slice(&mut xor_rng(seed), &vec, amount);
                assert_eq!(result, regular);
            }

            {
                let result = sample_slice_ref(&mut xor_rng(seed), &vec, amount);
                let expected = regular.iter().map(|v| v).collect::<Vec<_>>();
                assert_eq!(result, expected);
            }
        }
    }
}
