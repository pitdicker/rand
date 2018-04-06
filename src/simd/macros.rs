#[macro_export]
macro_rules! make_simd_correctness_test {
    ($test_name:ident, $rng:ident, $vector:ident, $x_scalar:ident) => (
        #[test]
        fn $test_name() {
            use ::rand::thread_rng;

            fn test(reg_rngs: &mut [NonSimdRng]) {
                let mut simd_rng = $rng::from_non_simd(reg_rngs);

                for i in 0..super::SIMD_CORRECTNESS_N {
                    let expected = reg_rngs.iter_mut().map(|x| x.gen::<$x_scalar>());
                    let next = simd_rng.next_vector();

                    for (j, exp) in expected.enumerate() {
                        let actual = next.extract(j);
                        assert_eq!(actual, exp, "{:?}", i);
                    }
                }
            }

            let mut zero_rngs: Vec<_> = (0..$vector::lanes()).map(|_| NonSimdRng::from_seed(Default::default())).collect();
            test(&mut zero_rngs);

            let mut rng = thread_rng();
            for _ in 0..super::SIMD_CORRECTNESS_SEEDS {
                let mut reg_rngs: Vec<_> = (0..$vector::lanes())
                    .map(|_| NonSimdRng::from_rng(&mut rng).unwrap())
                    .collect();
                test(&mut reg_rngs);
            }
        }
    )
}
