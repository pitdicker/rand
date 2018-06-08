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

use super::Rng;

// This crate is only enabled when either std or alloc is available.
// BTreeMap is not as fast in tests, but better than nothing.
#[cfg(feature="std")] use std::collections::HashMap;
#[cfg(not(feature="std"))] use alloc::btree_map::BTreeMap;

#[cfg(not(feature="std"))] use alloc::Vec;

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
/// ```
/// use rand::{thread_rng, seq};
///
/// let mut rng = thread_rng();
/// let sample = seq::sample_iter(&mut rng, 1..100, 5).unwrap();
/// println!("{:?}", sample);
/// ```
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
/// The values are non-repeating (distinct). The ordering of values is fully
/// random if `shuffled == true` but may not be fully random otherwise; see
/// documentation on [`sample_indices`].
///
/// This implementation uses `O(amount)` time and memory.
///
/// Panics if `amount > slice.len()`
///
/// # Example
///
/// ```
/// use rand::{thread_rng, seq};
///
/// let mut rng = thread_rng();
/// let values = vec![5, 6, 1, 3, 4, 6, 7];
/// println!("{:?}", seq::sample_slice(&mut rng, &values, 3, true));
/// ```
///
/// [`sample_indices`]: fn.sample_indices.html
pub fn sample_slice<R, T>(rng: &mut R, slice: &[T], amount: usize,
    shuffled: bool) -> Vec<T>
    where R: Rng + ?Sized,
          T: Clone
{
    let indices = sample_indices(rng, slice.len(), amount, shuffled);

    let mut out = Vec::with_capacity(amount);
    out.extend(indices.iter().map(|i| slice[*i as usize].clone()));
    out
}

/// Randomly sample exactly `amount` references from `slice`.
///
/// The values are non-repeating (distinct). The ordering of values is fully
/// random if `shuffled == true` but may not be fully random otherwise; see
/// documentation on [`sample_indices`].
///
/// This implementation uses `O(amount)` time and memory.
///
/// Panics if `amount > slice.len()`
///
/// # Example
///
/// ```
/// use rand::{thread_rng, seq};
///
/// let mut rng = thread_rng();
/// let values = vec![5, 6, 1, 3, 4, 6, 7];
/// println!("{:?}", seq::sample_slice_ref(&mut rng, &values, 3, true));
/// ```
///
/// [`sample_indices`]: fn.sample_indices.html
pub fn sample_slice_ref<'a, R, T>(rng: &mut R, slice: &'a [T], amount: usize,
    shuffled: bool) -> Vec<&'a T>
    where R: Rng + ?Sized
{
    let indices = sample_indices(rng, slice.len(), amount, shuffled);

    let mut out = Vec::with_capacity(amount);
    out.extend(indices.iter().map(|i| &slice[*i as usize]));
    out
}

/// Randomly sample exactly `amount` distinct indices from `0..length`.
///
/// If `shuffled == true` then the sampled values will be fully shuffled;
/// otherwise the values may only partially shuffled, depending on the
/// algorithm used (i.e. biases may exist in the ordering of sampled elements).
/// Depending on the algorithm used internally, full shuffling may add
/// significant overhead for `amount` > 10 or so, but not more than double
/// the time and often much less.
///
/// This method is used internally by the slice sampling methods, but it can
/// sometimes be useful to have the indices themselves so this is provided as
/// an alternative.
///
/// The implementation used is not specified; we automatically select the
/// fastest available implementation for the `length` and `amount` parameters
/// (based on detailed profiling on an Intel Haswell CPU). Roughly speaking,
/// complexity is `O(amount)`, except that when `amount` is small, performance
/// is closer to `O(amount^2)`, and when `length` is close to `amount` then
/// `O(length)`.
///
/// Note that we only support `u32` indices since this covers the vast majority
/// of uses, and performance is significantly better than with `u64`.
/// 
/// If an allocation-free `no_std` function is required, it is suggested
/// to adapt the internal `sample_indices_floyd` implementation.
///
/// Panics if `amount > length` or if `length` is not reprentable as a `u32`.
pub fn sample_indices<R>(rng: &mut R, length: usize, amount: usize,
    shuffled: bool) -> Vec<usize>
    where R: Rng + ?Sized,
{
    if amount > length {
        panic!("`amount` of samples must be less than or equal to `length`");
    }
    if length > (::core::u32::MAX as usize) {
        panic!("`length` is not representable as `u32`");
    }

    // Choice of algorithm here depends on both length and amount. See:
    // https://github.com/rust-lang-nursery/rand/pull/479
    // We do some calculations with u64 to avoid overflow.

    if amount < 442 {
        const C: [[u64; 2]; 2] = [[5, 45], [50, 350]];
        let j = if length < 500_000 { 0 } else { 1 };
        let m4 = 6 * amount as u64;
        if C[0][j] * (length as u64) < (C[1][j] + m4) * amount as u64 {
            sample_indices_inplace(rng, length, amount)
        } else if shuffled {
            let mut indices = sample_indices_floyd(rng, length, amount);
            rng.shuffle(&mut indices);
            indices
        } else {
            sample_indices_floyd(rng, length, amount)
        }
    } else {
        const C: [[u64; 2]; 2] = [[1, 9], [590, 600]];
        let j = if length < 500_000 { 0 } else { 1 };
        if C[0][j] * (length as u64) < C[1][j] * amount as u64 {
            sample_indices_inplace(rng, length, amount)
        } else {
            sample_indices_cache(rng, length, amount)
        }
    }
}

/// Randomly sample exactly `amount` indices from `0..length`, using Floyd's
/// combination algorithm.
/// 
/// The values are only partially shuffled (i.e. biases exist in the ordering of
/// sampled elements).
///
/// This implementation uses `O(amount)` memory and `O(amount^2)` time.
fn sample_indices_floyd<R>(rng: &mut R, length: usize, amount: usize)
    -> Vec<usize>
    where R: Rng + ?Sized,
{
    debug_assert!(amount <= length);
    let mut indices = Vec::with_capacity(amount);
    if length <= ::core::u32::MAX as usize {
        let length = length as u32;
        let amount = amount as u32;
        for j in length - amount .. length {
            let t = rng.gen_range(0, j + 1) as usize;
            if indices.contains(&t) {
                indices.push(j as usize)
            } else {
                indices.push(t)
            };
        }
    } else {
        for j in length - amount .. length {
            let t = rng.gen_range(0, j + 1);
            if indices.contains(&t) {
                indices.push(j)
            } else {
                indices.push(t)
            };
        }
    }
    indices
}

/// Randomly sample exactly `amount` indices from `0..length`, using Floyd's
/// combination algorithm (fully shuffled variant).
/// 
/// Full shuffling adds significant overhead once `amount` > 10 or so, but not
/// more than double the time since our implementation is already `O(amount^2)`.
///
/// This implementation uses `O(amount)` memory and `O(amount^2)` time.
fn sample_indices_floyd_shuffled<R>(rng: &mut R, length: usize, amount: usize)
    -> Vec<usize>
    where R: Rng + ?Sized,
{
    debug_assert!(amount <= length);
    let mut indices = Vec::with_capacity(amount as usize);
    for j in length - amount .. length {
        let t = rng.gen_range(0, j + 1);
        let mut idx = None;
        for (i, x) in indices.iter().enumerate() {
            if *x == t {
                idx = Some(i);
                break;
            }
        }
        if let Some(i) = idx {
            indices.insert(i, j);   // shift rest to right
        } else {
            indices.push(t);
        }
    }
    indices
}

/// Randomly sample exactly `amount` indices from `0..length`, using an inplace
/// partial Fisher-Yates method.
///
/// This allocates the entire `length` of indices and randomizes only the first `amount`.
/// It then truncates to `amount` and returns.
/// 
/// This method is not appropriate for large `length` and potentially uses a lot
/// of memory; because of this we only implement for `u32` index (which improves
/// performance in all cases).
///
/// This is likely the fastest for small lengths since it avoids the need for
/// allocations. Set-up is `O(length)` time and memory and shuffling is
/// `O(amount)` time.
fn sample_indices_inplace<R>(rng: &mut R, length: usize, amount: usize)
    -> Vec<usize>
    where R: Rng + ?Sized,
{
    debug_assert!(amount <= length);
    let mut indices: Vec<usize> = Vec::with_capacity(length);
    indices.extend(0..length);
    for i in 0..amount {
        let j = rng.gen_range(i, length);
        indices.swap(i, j);
    }
    indices.truncate(amount);
    debug_assert_eq!(indices.len(), amount);
    indices
}

/// Randomly sample exactly `amount` indices from `0..length`, using a
/// dynamically-cached partial Fisher-Yates method.
///
/// The cache avoids allocating the entire `length` of values. This is
/// especially useful when `amount <<< length`; e.g. selecting 3 non-repeating
/// values from `1_000_000`. The algorithm is `O(amount)` time and memory,
/// but due to overheads will often be slower than other approaches.
fn sample_indices_cache<R>(rng: &mut R, length: usize, amount: usize)
    -> Vec<usize>
    where R: Rng + ?Sized,
{
    debug_assert!(amount <= length);
    #[cfg(feature="std")] let mut cache = HashMap::with_capacity(amount);
    #[cfg(not(feature="std"))] let mut cache = BTreeMap::new();
    let mut indices = Vec::with_capacity(amount);
    for i in 0..amount {
        let j = rng.gen_range(i, length);

        // get the current values at i and j ...
        let x_i = match cache.get(&i) {
            Some(x) => *x,
            None => i,
        };
        let x_j = match cache.get(&j) {
            Some(x) => *x,
            None => j,
        };

        // ... and swap them
        cache.insert(j, x_i);
        indices.push(x_j);  // push at position i
    }
    debug_assert_eq!(indices.len(), amount);
    indices
}

#[cfg(test)]
mod test {
    use super::*;
    use {XorShiftRng, Rng, SeedableRng};
    #[cfg(not(feature="std"))]
    use alloc::Vec;

    #[test]
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
    fn test_sample_slice_boundaries() {
        let empty: &[u8] = &[];

        let mut r = ::test::rng(402);

        // sample 0 items
        assert_eq!(&sample_slice(&mut r, empty, 0, false)[..], [0u8; 0]);
        assert_eq!(&sample_slice(&mut r, &[42, 2, 42], 0, false)[..], [0u8; 0]);

        // sample 1 item
        assert_eq!(&sample_slice(&mut r, &[42], 1, false)[..], [42]);
        let v = sample_slice(&mut r, &[1, 42], 1, false)[0];
        assert!(v == 1 || v == 42);

        // sample "all" the items
        let v = sample_slice(&mut r, &[42, 133], 2, false);
        assert!(&v[..] == [42, 133] || v[..] == [133, 42]);

        assert_eq!(&sample_indices_inplace(&mut r, 0, 0)[..], [0; 0]);
        assert_eq!(&sample_indices_inplace(&mut r, 1, 0)[..], [0; 0]);
        assert_eq!(&sample_indices_inplace(&mut r, 1, 1)[..], [0]);

        assert_eq!(&sample_indices_cache(&mut r, 0, 0)[..], [0; 0]);
        assert_eq!(&sample_indices_cache(&mut r, 1, 0)[..], [0; 0]);
        assert_eq!(&sample_indices_cache(&mut r, 1, 1)[..], [0]);

        assert_eq!(&sample_indices_floyd(&mut r, 0, 0)[..], [0; 0]);
        assert_eq!(&sample_indices_floyd(&mut r, 1, 0)[..], [0; 0]);
        assert_eq!(&sample_indices_floyd(&mut r, 1, 1)[..], [0]);
        assert_eq!(&sample_indices_floyd_shuffled(&mut r, 0, 0)[..], [0; 0]);
        assert_eq!(&sample_indices_floyd_shuffled(&mut r, 1, 0)[..], [0; 0]);
        assert_eq!(&sample_indices_floyd_shuffled(&mut r, 1, 1)[..], [0]);
        
        // These algorithms should be fast with big numbers. Test average.
        let sum = sample_indices_cache(&mut r, 1 << 25, 10)
            .iter().fold(0, |a, b| a + b);
        assert!(1 << 25 < sum && sum < (1 << 25) * 25);
        
        let sum = sample_indices_floyd(&mut r, 1 << 25, 10)
            .iter().fold(0, |a, b| a + b);
        assert!(1 << 25 < sum && sum < (1 << 25) * 25);

        // Make sure lucky 777's aren't lucky
        let slice = &[42, 777];
        let mut num_42 = 0;
        let total = 1000;
        for _ in 0..total {
            let v = sample_slice(&mut r, slice, 1, true);
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
    fn test_sample_slice() {
        let xor_rng = XorShiftRng::from_seed;

        let mut r = ::test::rng(403);

        for n in 1..20 {
            let length = 5*n - 4;   // 1, 6, ...
            let amount = r.gen_range(0, length);
            let mut seed = [0u8; 16];
            r.fill(&mut seed);

            // assert the basics work
            let regular = sample_indices(
                &mut xor_rng(seed), length, amount, false);
            assert_eq!(regular.len(), amount);
            assert!(regular.iter().all(|e| *e < length));

            // also test that sampling the slice works
            let vec: Vec<usize> = (0..length).collect();
            let result = sample_slice(&mut xor_rng(seed), &vec, amount, false);
            assert_eq!(result, regular);

            let result = sample_slice_ref(&mut xor_rng(seed), &vec, amount, true);
            let expected = regular.iter().map(|v| v).collect::<Vec<_>>();
            assert_eq!(result, expected);
        }
    }
    
    #[test]
    fn test_sample_alg() {
        let xor_rng = XorShiftRng::from_seed;

        let mut r = ::test::rng(403);
        let mut seed = [0u8; 16];
        
        // We can't test which algorithm is used directly, but Floyd's alg
        // should produce different results from the others.
        
        // A small length and relatively large amount should use inplace
        r.fill(&mut seed);
        let (length, amount): (usize, usize) = (100, 50);
        let v1 = sample_indices(&mut xor_rng(seed), length, amount, true);
        let v2 = sample_indices_inplace(&mut xor_rng(seed), length, amount);
        assert!(v1.iter().all(|e| *e < length));
        assert_eq!(v1, v2);
        
        // Test Floyd's alg does produce different results
        let v3 = sample_indices_floyd_shuffled(&mut xor_rng(seed), length, amount);
        assert!(v1 != v3);
        // However, the cache alg should produce the same results
        let v4 = sample_indices_cache(&mut xor_rng(seed), length, amount);
        assert_eq!(v1, v4);
        
        // A large length and small amount should use Floyd
        r.fill(&mut seed);
        let (length, amount): (usize, usize) = (1<<20, 50);
        let v1 = sample_indices(&mut xor_rng(seed), length, amount, true);
        let v2 = sample_indices_floyd_shuffled(&mut xor_rng(seed), length, amount);
        assert!(v1.iter().all(|e| *e < length));
        assert_eq!(v1, v2);
        
        // A large length and larger amount should use cache
        r.fill(&mut seed);
        let (length, amount): (usize, usize) = (1<<20, 600);
        let v1 = sample_indices(&mut xor_rng(seed), length, amount, true);
        let v2 = sample_indices_cache(&mut xor_rng(seed), length, amount);
        assert!(v1.iter().all(|e| *e < length));
        assert_eq!(v1, v2);
    }
}
