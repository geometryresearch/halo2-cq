use group::{Curve, GroupEncoding};
use std::collections::HashMap;

use crate::pairing::{Engine, MultiMillerLoop};

/// Dynamically batches tuples of points and returns output compatible with MultiMillerLoop
pub struct PairingBatcher<E: MultiMillerLoop> {
    /// Mapping of g2 repr to overcome trait bounds
    g2_to_g2: HashMap<Vec<u8>, E::G2>,
    /// Mapping of all G2 points serialized with correlated G1 points
    g2_to_g1: HashMap<Vec<u8>, E::G1>,
    /// challenge
    challenge: E::Scalar,
    /// running challenge
    running_challenge: E::Scalar,
    /// is finalized
    finalized: bool,
}

impl<E: MultiMillerLoop> PairingBatcher<E> {
    pub fn new(challenge: E::Scalar) -> Self {
        Self {
            g2_to_g2: HashMap::default(),
            g2_to_g1: HashMap::default(),
            challenge,
            running_challenge: E::Scalar::from(1),
            finalized: false,
        }
    }

    /// Adds new pairing equation that needs to be checked
    pub fn add_pairing(&mut self, pairs: &[(E::G1Affine, E::G2Affine)]) {
        let g2_reprs: Vec<_> = pairs
            .iter()
            .map(|&(_, g2)| g2.to_bytes().as_ref().to_vec())
            .collect();

        // For each g2 point
        let mut is_present: bool = false;
        for repr in g2_reprs.iter() {
            if self.g2_to_g1.get(repr).is_some() {
                is_present = true;
                break;
            }
        }

        let g2_points: Vec<E::G2> = pairs.iter().map(|&(_, g2)| g2.into()).collect();
        let g1_points: Vec<E::G1> = if is_present {
            let running_challenge = self.running_challenge * self.challenge;
            self.running_challenge = running_challenge;
            pairs
                .iter()
                .map(|&(g1, _)| g1 * running_challenge)
                .collect()
        } else {
            pairs.iter().map(|pair| pair.0.into()).collect()
        };

        self.update_mapping(&g2_reprs, &g1_points, &g2_points);
    }

    fn update_mapping(&mut self, g2_reprs: &[Vec<u8>], g1_points: &[E::G1], g2_points: &[E::G2]) {
        assert_eq!(g1_points.len(), g2_reprs.len());
        assert_eq!(g2_points.len(), g2_reprs.len());

        g2_reprs
            .iter()
            .zip(g1_points.iter())
            .zip(g2_points.iter())
            .for_each(|((g2_repr, g1), g2)| {
                self.g2_to_g1
                    .entry(g2_repr.to_vec())
                    .and_modify(|g1_point: &mut <E as Engine>::G1| *g1_point += g1)
                    .or_insert(*g1);
                self.g2_to_g2.insert(g2_repr.to_vec(), *g2);
            });
    }

    /// Returns output ready for MultiMillerLoop
    pub fn finalize(mut self) -> Vec<(E::G1Affine, E::G2Prepared)> {
        if self.finalized {
            panic!("Batcher is already consumed!");
        }
        self.finalized = true;
        let g2_map = self.g2_to_g2.clone();
        self.g2_to_g1
            .iter()
            .map(|(g2_repr, g1)| {
                let g2 = g2_map.get(g2_repr).unwrap().to_affine();
                let g2_prepared: E::G2Prepared = g2.into();
                (g1.to_affine(), g2_prepared)
            })
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use ff::Field;
    use rand_core::OsRng;

    use super::*;
    use crate::{
        bn256::{Bn256, Fr, G1Affine, G2Affine, G2Prepared, Gt, G1, G2},
        pairing::MillerLoopResult,
    };

    #[test]
    fn test_bn256_batch_pairing() {
        /*
           e(a, b) = e(c, d)
           e(j, b) = e(f, g)
           e(e, d) = e(h, b)
        */

        let a = Fr::random(OsRng);
        let b = Fr::random(OsRng);
        let c = Fr::random(OsRng);
        let d = a * b * c.invert().unwrap();
        let f = Fr::random(OsRng);
        let j = Fr::random(OsRng);
        let g = j * b * f.invert().unwrap();
        let e = Fr::random(OsRng);
        let h = e * d * b.invert().unwrap();

        let a: G1Affine = (G1::generator() * a).into();
        let b: G2Affine = (G2::generator() * b).to_affine();
        let c: G1Affine = (G1::generator() * c).into();
        let d: G2Affine = (G2::generator() * d).to_affine();
        let j: G1Affine = (G1::generator() * j).into();
        let f: G1Affine = (G1::generator() * f).into();
        let g: G2Affine = (G2::generator() * g).to_affine();
        let e: G1Affine = (G1::generator() * e).into();
        let h: G1Affine = (G1::generator() * h).into();

        // Manual Miller loop
        {
            let b: G2Prepared = b.into();
            let d: G2Prepared = d.into();
            let g: G2Prepared = g.into();

            let result: Gt = {
                Bn256::multi_miller_loop(&[
                    (&a, &b),
                    (&(-c), &d),
                    (&j, &b),
                    (&(-f), &g),
                    (&e, &d),
                    (&(-h), &b),
                ])
            };

            let pairing_result = result.final_exponentiation();
            assert_eq!(pairing_result, Gt::identity());
        }

        {
            // Batched test
            let mut pairing_batcher = PairingBatcher::<Bn256>::new(Fr::random(OsRng));

            pairing_batcher.add_pairing(&[(a, b), ((-c), d)]);
            pairing_batcher.add_pairing(&[(j, b), ((-f), g)]);
            pairing_batcher.add_pairing(&[(e, d), ((-h), b)]);

            let batched_tuples = pairing_batcher.finalize();
            let result: Gt = Bn256::multi_miller_loop(
                &batched_tuples
                    .iter()
                    .map(|(g1, g2)| (g1, g2))
                    .collect::<Vec<_>>(),
            );

            let pairing_result = result.final_exponentiation();
            assert_eq!(pairing_result, Gt::identity());

            /*
                e(a, b) = e(c, d)
                e(j, b) = e(f, g)
                e(e, d) = e(h, b)

                ==>

                e(a + [R]j + [R^2]h, b).e(c + [R^2]e, d).e([R]f, g)
            */
            assert_eq!(3, batched_tuples.len());
        }
    }
}
