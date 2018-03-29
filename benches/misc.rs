#![feature(test)]

extern crate test;
extern crate rand;

const RAND_BENCH_N: u64 = 1000;

use test::{black_box, Bencher};

use rand::{SeedableRng, SmallRng, Rng, thread_rng};
use rand::seq::*;

#[bench]
fn misc_gen_bool(b: &mut Bencher) {
    let mut rng = SmallRng::from_rng(&mut thread_rng()).unwrap();
    b.iter(|| {
        let mut accum = true;
        for _ in 0..::RAND_BENCH_N {
            accum ^= rng.gen_bool(0.18);
        }
        black_box(accum);
    })
}

#[bench]
fn misc_gen_bool_var(b: &mut Bencher) {
    let mut rng = SmallRng::from_rng(&mut thread_rng()).unwrap();
    b.iter(|| {
        let mut p = 0.18;
        let mut accum = true;
        for _ in 0..::RAND_BENCH_N {
            accum ^= rng.gen_bool(p);
            p += 0.0001;
        }
        black_box(accum);
    })
}

#[bench]
fn misc_shuffle_1000(b: &mut Bencher) {
    let mut rng = SmallRng::from_rng(thread_rng()).unwrap();
    let x : &mut [usize] = &mut [1; 1000];
    b.iter(|| {
        rng.shuffle(x);
        black_box(x[0]);
    })
}

#[bench]
fn misc_sample_iter_10_of_100(b: &mut Bencher) {
    let mut rng = SmallRng::from_rng(thread_rng()).unwrap();
    let x : &[usize] = &[1; 100];
    b.iter(|| {
        black_box(sample_iter(&mut rng, x, 10).unwrap_or_else(|e| e));
    })
}

#[bench]
fn misc_sample_slice_1000_of_8000(b: &mut Bencher) {
    let mut rng = SmallRng::from_rng(thread_rng()).unwrap();
    let x : &[usize] = &[1; 8000];
    b.iter(|| {
        black_box(sample_slice(&mut rng, x, 1000));
    })
}

#[bench]
fn misc_sample_slice_50000_of_1m(b: &mut Bencher) {
    let mut rng = SmallRng::from_rng(thread_rng()).unwrap();
    let x : &[usize] = &[1; 1_000_000];
    b.iter(|| {
        black_box(sample_slice(&mut rng, x, 50_000));
    })
}

#[bench]
fn misc_sample_slice_10_of_100(b: &mut Bencher) {
    let mut rng = SmallRng::from_rng(thread_rng()).unwrap();
    let x : &[usize] = &[1; 100];
    b.iter(|| {
        black_box(sample_slice(&mut rng, x, 10));
    })
}

#[bench]
fn misc_sample_slice_ref_10_of_100(b: &mut Bencher) {
    let mut rng = SmallRng::from_rng(thread_rng()).unwrap();
    let x : &[usize] = &[1; 100];
    b.iter(|| {
        black_box(sample_slice_ref(&mut rng, x, 10));
    })
}

macro_rules! sample_indices {
    ($name:ident, $amount:expr, $length:expr) => {
        #[bench]
        fn $name(b: &mut Bencher) {
            let mut rng = SmallRng::from_rng(thread_rng()).unwrap();
            b.iter(|| {
                black_box(sample_indices(&mut rng, $length, $amount));
            })
        }
    }
}

sample_indices!(misc_sample_indices_10_of_1k, 10, 1000);
sample_indices!(misc_sample_indices_50_of_1k, 50, 1000);
sample_indices!(misc_sample_indices_100_of_1k, 100, 1000);

#[bench]
fn misc_sample_multiple_10_of_1000(b: &mut Bencher) {
    let mut rng = thread_rng();
    let x : &[usize] = &[1; 1000];
    b.iter(|| {
        let results: Vec<_> = x.pick_multiple(10, &mut rng).collect();
        black_box(results);
    })
}

#[bench]
fn misc_sample_multiple_50000_of_1m(b: &mut Bencher) {
    let mut rng = thread_rng();
    let x : &[usize] = &[1; 1_000_000];
    b.iter(|| {
        let results: Vec<_> = x.pick_multiple(50_000, &mut rng).collect();
        black_box(results);
    })
}

#[bench]
fn misc_sample_multiple_boundary_07(b: &mut Bencher) {
    let mut rng = SmallRng::from_rng(&mut thread_rng()).unwrap();
    let x : &[usize] = &[1; 7_000];
    b.iter(|| {
        let results: Vec<_> = x.pick_multiple(1000, &mut rng).collect();
        black_box(results);
    })
}

#[bench]
fn misc_sample_multiple_boundary_08(b: &mut Bencher) {
    let mut rng = SmallRng::from_rng(&mut thread_rng()).unwrap();
    let x : &[usize] = &[1; 8_000];
    b.iter(|| {
        let results: Vec<_> = x.pick_multiple(1000, &mut rng).collect();
        black_box(results);
    })
}

#[bench]
fn misc_sample_multiple_boundary_09(b: &mut Bencher) {
    let mut rng = SmallRng::from_rng(&mut thread_rng()).unwrap();
    let x : &[usize] = &[1; 9_000];
    b.iter(|| {
        let results: Vec<_> = x.pick_multiple(1000, &mut rng).collect();
        black_box(results);
    })
}

#[bench]
fn misc_sample_multiple_boundary_10(b: &mut Bencher) {
    let mut rng = SmallRng::from_rng(&mut thread_rng()).unwrap();
    let x : &[usize] = &[1; 10_000];
    b.iter(|| {
        let results: Vec<_> = x.pick_multiple(1000, &mut rng).collect();
        black_box(results);
    })
}

#[bench]
fn misc_sample_multiple_boundary_11(b: &mut Bencher) {
    let mut rng = SmallRng::from_rng(&mut thread_rng()).unwrap();
    let x : &[usize] = &[1; 11_000];
    b.iter(|| {
        let results: Vec<_> = x.pick_multiple(1000, &mut rng).collect();
        black_box(results);
    })
}

#[bench]
fn misc_sample_multiple_boundary_12(b: &mut Bencher) {
    let mut rng = SmallRng::from_rng(&mut thread_rng()).unwrap();
    let x : &[usize] = &[1; 12_000];
    b.iter(|| {
        let results: Vec<_> = x.pick_multiple(1000, &mut rng).collect();
        black_box(results);
    })
}

#[bench]
fn misc_sample_multiple_boundary_13(b: &mut Bencher) {
    let mut rng = SmallRng::from_rng(&mut thread_rng()).unwrap();
    let x : &[usize] = &[1; 13_000];
    b.iter(|| {
        let results: Vec<_> = x.pick_multiple(1000, &mut rng).collect();
        black_box(results);
    })
}

#[bench]
fn misc_sample_multiple_boundary_14(b: &mut Bencher) {
    let mut rng = SmallRng::from_rng(&mut thread_rng()).unwrap();
    let x : &[usize] = &[1; 14_000];
    b.iter(|| {
        let results: Vec<_> = x.pick_multiple(1000, &mut rng).collect();
        black_box(results);
    })
}

#[bench]
fn misc_sample_multiple_boundary_15(b: &mut Bencher) {
    let mut rng = SmallRng::from_rng(&mut thread_rng()).unwrap();
    let x : &[usize] = &[1; 15_000];
    b.iter(|| {
        let results: Vec<_> = x.pick_multiple(1000, &mut rng).collect();
        black_box(results);
    })
}
