#![feature(test)]

extern crate test;
extern crate rand;
#[cfg(feature = "rayon")]
extern crate rayon;

use test::{black_box, Bencher};

use rand::{Rng, FromEntropy, XorShiftRng, thread_rng};
use rand::distributions::*;

#[cfg(feature = "rayon")]
use rayon::iter::{ParallelIterator, IntoParallelIterator};

#[bench]
fn gen_100_000_sequential(b: &mut Bencher) {
    let mut rng = XorShiftRng::from_entropy();

    b.iter(|| {
        let vec: Vec<f64> = (0..100_000)
            .into_iter()
            .map(|_| { rng.gen::<f64>() })
            .collect();
        black_box(vec[0]);
    });
    b.bytes = 100_000 * 8;
}

#[bench]
fn gen_100_000_sample_iter(b: &mut Bencher) {
    let mut rng = XorShiftRng::from_entropy();

    b.iter(|| {
        let vec: Vec<f64> = rng.sample_iter(&Standard).take(100_000).collect();
        black_box(vec[0]);
    });
    b.bytes = 100_000 * 8;
}

#[cfg(feature = "rayon")]
#[bench]
fn gen_100_000_parallel(b: &mut Bencher) {
    let mut rng = XorShiftRng::from_entropy();

    b.iter(|| {
        let vec: Vec<f64> = Standard.sample_par_iter(&mut rng, 100_000).collect();
        black_box(vec[0]);
    });
    b.bytes = 100_000 * 8;
}

#[cfg(feature = "rayon")]
#[bench]
fn gen_100_000_thread_local(b: &mut Bencher) {
    b.iter(|| {
        let vec: Vec<f64> = (0..100_000)
            .into_par_iter()
            .map(|_| { thread_rng().gen::<f64>() })
            .collect();
        black_box(vec[0]);
    });
    b.bytes = 100_000 * 8;
}
