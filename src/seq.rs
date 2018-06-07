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
/// The values are non-repeating and in random order.
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
/// println!("{:?}", seq::sample_slice(&mut rng, &values, 3));
/// ```
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
/// ```
/// use rand::{thread_rng, seq};
///
/// let mut rng = thread_rng();
/// let values = vec![5, 6, 1, 3, 4, 6, 7];
/// println!("{:?}", seq::sample_slice_ref(&mut rng, &values, 3));
/// ```
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
        sample_indices_inplace(rng, length as u32, amount as u32)
            .into_iter().map(|x| x as usize).collect()
    } else {
        sample_indices_cache(rng, length, amount)
    }
}

/// Randomly sample exactly `amount` indices from `0..length`, using Floyd's
/// combination algorithm.
///
/// This implementation uses `O(amount)` memory and `O(amount^2)` time.
fn sample_indices_floyd<R>(rng: &mut R, length: usize, amount: usize)
    -> Vec<usize>
    where R: Rng + ?Sized,
{
    debug_assert!(amount <= length);
    let mut indices = Vec::with_capacity(amount);
    for j in length - amount .. length {
        let t = rng.gen_range(0, j + 1);
        let t = if indices.contains(&t) { j } else { t };
        indices.push( t );
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
fn sample_indices_inplace<R>(rng: &mut R, length: u32, amount: u32)
    -> Vec<u32>
    where R: Rng + ?Sized,
{
    debug_assert!(amount <= length);
    let mut indices: Vec<u32> = Vec::with_capacity(length as usize);
    indices.extend(0..length);
    for i in 0..amount {
        let j: u32 = rng.gen_range(i, length);
        indices.swap(i as usize, j as usize);
    }
    indices.truncate(amount as usize);
    debug_assert_eq!(indices.len(), amount as usize);
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
        let j: usize = rng.gen_range(i, length);

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
        assert_eq!(&sample_slice(&mut r, empty, 0)[..], [0u8; 0]);
        assert_eq!(&sample_slice(&mut r, &[42, 2, 42], 0)[..], [0u8; 0]);

        // sample 1 item
        assert_eq!(&sample_slice(&mut r, &[42], 1)[..], [42]);
        let v = sample_slice(&mut r, &[1, 42], 1)[0];
        assert!(v == 1 || v == 42);

        // sample "all" the items
        let v = sample_slice(&mut r, &[42, 133], 2);
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
        
        // These algorithms should be fast with big numbers. Test average.
        let sum = sample_indices_cache(&mut r, 1 << 50, 10)
            .iter().fold(0, |a, b| a + b);
        assert!(1 << 50 < sum && sum < (1 << 50) * 25);
        
        let sum = sample_indices_floyd(&mut r, 1 << 50, 10)
            .iter().fold(0, |a, b| a + b);
        assert!(1 << 50 < sum && sum < (1 << 50) * 25);

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
    fn test_sample_slice() {
        let xor_rng = XorShiftRng::from_seed;

        let mut r = ::test::rng(403);

        for n in 1usize..20 {
            let length = 5*n - 4;   // 1, 6, ...
            let amount = r.gen_range(0, length);
            let mut seed = [0u8; 16];
            r.fill(&mut seed);

            // assert the basics work
            let regular = sample_indices(
                &mut xor_rng(seed), length, amount);
            assert_eq!(regular.len(), amount);
            assert!(regular.iter().all(|e| *e < length));

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
