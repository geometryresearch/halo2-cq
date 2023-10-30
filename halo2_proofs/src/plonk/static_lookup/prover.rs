use ff::Field;
use halo2curves::{
    bn256::{G1Affine, G1},
    pairing::{Engine, MultiMillerLoop},
    serde::SerdeObject,
    FieldExt,
};

// TODO: COMPUTE A(0) COMMITMENT FROM LAGRANGE AT 0 COMMITMENTS

use crate::{
    arithmetic::{best_multiexp, eval_polynomial},
    plonk::{
        evaluation::evaluate, ChallengeBeta, ChallengeTheta, ChallengeX, Expression, ProvingKey,
    },
    poly::{
        commitment::{Blind, Params, ParamsProver},
        kzg::commitment::ParamsKZG,
        Coeff, EvaluationDomain, LagrangeCoeff, Polynomial, ProverQuery,
    },
    transcript::{EncodedChallenge, TranscriptWrite},
};
use std::{
    collections::{BTreeMap, BTreeSet},
    fmt::Debug,
    iter,
};

use crate::plonk::Error;
use group::{prime::PrimeCurveAffine, Curve, Group};

use super::StaticTableId;

#[derive(Debug)]
pub struct Committed<E: MultiMillerLoop> {
    pub(in crate::plonk) f: Polynomial<E::Scalar, LagrangeCoeff>,
    pub(in crate::plonk) m_sparse: BTreeMap<usize, E::Scalar>,
    pub(in crate::plonk) table_ids: Vec<StaticTableId<String>>,
    pub(in crate::plonk) table_index_value_mappings: Vec<BTreeMap<usize, E::Scalar>>,
}

#[derive(Debug, Clone)]
pub struct CommittedLogDerivative<E: MultiMillerLoop> {
    pub(in crate::plonk) b: Polynomial<E::Scalar, Coeff>,
    pub(in crate::plonk) b0: Polynomial<E::Scalar, Coeff>,
    pub(in crate::plonk) f: Polynomial<E::Scalar, Coeff>,
    pub(in crate::plonk) a_at_zero: E::Scalar,
}

pub(in crate::plonk) struct Evaluated<E: MultiMillerLoop> {
    constructed: CommittedLogDerivative<E>,
}

impl<F: FieldExt> super::Argument<F> {
    pub(in crate::plonk) fn commit<'a, E, EC, T>(
        &self,
        pk: &ProvingKey<E>,
        params: &ParamsKZG<E>,
        domain: &EvaluationDomain<F>,
        theta: ChallengeTheta<E::G1Affine>,
        challenges: &'a [E::Scalar],
        advice_values: &'a [Polynomial<E::Scalar, LagrangeCoeff>],
        fixed_values: &'a [Polynomial<E::Scalar, LagrangeCoeff>],
        instance_values: &'a [Polynomial<E::Scalar, LagrangeCoeff>],
        transcript: &mut T,
    ) -> Result<Committed<E>, Error>
    where
        E: MultiMillerLoop<Scalar = F> + Debug,
        E::G1Affine: SerdeObject,
        E::G2Affine: SerdeObject,
        EC: EncodedChallenge<E::G1Affine>,
        T: TranscriptWrite<E::G1Affine, EC>,
    {
        // TODO: make nicer error
        let tables: Vec<_> = self
            .table_ids
            .iter()
            .map(|table_id| {
                pk.static_table_mapping
                    .get(table_id)
                    .expect("Key not exists")
            })
            .collect();

        if !tables.iter().all(|&table| table.size == tables[0].size) {
            panic!("Tables should all be of the same size");
        }

        let table_config = pk
            .static_table_configs
            .get(&tables[0].size)
            .expect("Config does not exists");

        let evaluate_expressions = |expressions: &[Expression<E::Scalar>]| {
            expressions
                .iter()
                .map(|expression| {
                    pk.vk.domain.lagrange_from_vec(evaluate(
                        expression,
                        params.n() as usize,
                        1,
                        fixed_values,
                        advice_values,
                        instance_values,
                        challenges,
                    ))
                })
                .collect::<Vec<_>>()
        };

        // Closure to get values of expressions and compress them
        let compress_expressions =
            |evaluated_expressions: &[Polynomial<E::Scalar, LagrangeCoeff>]| {
                let compressed_expression = evaluated_expressions
                    .iter()
                    .fold(domain.empty_lagrange(), |acc, expression| {
                        acc * *theta + &expression
                    });
                compressed_expression
            };

        // Get values of input expressions involved in the lookup
        let evaluated_expressions = evaluate_expressions(&self.input);
        let f = compress_expressions(&evaluated_expressions);

        // NOTE: For completeness we just ignore blinding rows
        // make sure to add selector and change cq as in our hackmd for soundness
        let blinding_factors = pk.vk.cs.blinding_factors();
        let usable_rows = params.n() as usize - (blinding_factors + 1);
        let mut m_sparse = BTreeMap::<usize, E::Scalar>::default();

        let mut table_index_value_mappings: Vec<_> = (0..tables.len())
            .map(|_| BTreeMap::<usize, E::Scalar>::default())
            .collect();

        for row in 0..usable_rows {
            let mut idx_set: Option<BTreeSet<usize>> = None;
            for (table_idx, (evals, table)) in
                evaluated_expressions.iter().zip(tables.iter()).enumerate()
            {
                let fi = evals.get(row).unwrap();
                let indices: &BTreeSet<usize> = table
                    .value_index_mapping
                    .get(fi)
                    .expect(&format!("{:?} not in table", *fi));

                // append in new map
                for index in indices.iter() {
                    table_index_value_mappings[table_idx].insert(*index, *fi);
                }

                if let Some(prev_indices) = idx_set {
                    let intersection: Vec<usize> =
                        prev_indices.intersection(&indices).copied().collect();
                    if intersection.is_empty() {
                        panic!("Vector lookup must be on the same table row")
                    }
                    idx_set = Some(intersection.into_iter().collect())
                } else {
                    idx_set = Some(indices.clone())
                }
            }

            if let Some(idx_set) = idx_set {
                m_sparse
                    .entry(*idx_set.first().unwrap())
                    .and_modify(|m| *m += E::Scalar::one())
                    .or_insert(E::Scalar::one());
            } else {
                panic!("Lookup failed")
            }
        }

        // zk is not currently supported
        let blind = Blind(E::Scalar::zero());
        let f_cm: E::G1Affine = params.commit_lagrange(&f, blind).into();

        let mut m_cm = E::G1::identity();
        for (&index, &multiplicity) in m_sparse.iter() {
            m_cm = table_config.g1_lagrange[index] * multiplicity + m_cm;
        }

        let m_cm: E::G1Affine = m_cm.into();

        transcript.write_point(f_cm)?;
        transcript.write_point(m_cm)?;

        Ok(Committed {
            f,
            m_sparse,
            table_ids: self.table_ids.clone(),
            table_index_value_mappings,
        })
    }
}

impl<E: MultiMillerLoop> Committed<E> {
    pub(in crate::plonk) fn commit_log_derivatives<'a, EC, T>(
        &self,
        pk: &ProvingKey<E>,
        params: &ParamsKZG<E>,
        domain: &EvaluationDomain<E::Scalar>,
        beta: ChallengeBeta<E::G1Affine>,
        theta: ChallengeTheta<E::G1Affine>,
        transcript: &mut T,
    ) -> Result<CommittedLogDerivative<E>, Error>
    where
        E: MultiMillerLoop + Debug,
        E::G1Affine: SerdeObject,
        E::G2Affine: SerdeObject,
        EC: EncodedChallenge<E::G1Affine>,
        T: TranscriptWrite<E::G1Affine, EC>,
    {
        // TODO: make nicer error
        let tables: Vec<_> = self
            .table_ids
            .iter()
            .map(|table_id| {
                pk.static_table_mapping
                    .get(table_id)
                    .expect("Key not exists")
            })
            .collect();

        // We already checked that they are all of the same size
        let table_config = pk
            .static_table_configs
            .get(&tables[0].size)
            .expect("Config does not exists");

        let mut a_cm = E::G1::identity();
        let mut qa_cm = E::G1::identity();
        let mut a0_cm = E::G1::identity();

        let compress_tables = |index: usize| {
            tables.iter().enumerate().fold(
                (E::Scalar::zero(), E::G1Affine::identity()),
                |acc, (table_idx, &table)| {
                    let (values, qs) = acc;

                    let values = values * *theta
                        + self.table_index_value_mappings[table_idx]
                            .get(&index)
                            .unwrap();
                    let qs = qs * *theta + table.qs[index];

                    // TODO: do this in projectiv
                    (values, qs.into())
                },
            )
        };

        let f_set: std::collections::BTreeSet<E::Scalar> = self.f.iter().cloned().collect();

        // step 2&3&4: computes A sparse representation, a commitment and qa commitment in single pass
        for (&index, &multiplicity) in self.m_sparse.iter() {
            let (table_values, table_qs) = compress_tables(index);
            let a_i = multiplicity * (table_values + *beta).invert().unwrap();

            // sanity
            assert!(f_set.get(&table_values).is_some());

            // a_cm = table_g1_lagrange * a_i + a_cm;
            a_cm = table_config.g1_lagrange[index] * a_i + a_cm;
            qa_cm = table_qs * a_i + qa_cm;
            // a0_cm = table_lagrange_0 * a_i + a0_cm;
            a0_cm = table_config.g_lagrange_opening_at_0[index] * a_i + a0_cm;
        }

        let blinding_factors = pk.vk.cs.blinding_factors();
        let usable_rows = params.n() as usize - (blinding_factors + 1);
        let mut bs: Vec<_> = self
            .f
            .iter()
            .take(usable_rows)
            .map(|&fi| (fi + *beta).invert().unwrap())
            .collect();

        let beta_inv = beta.invert().unwrap();
        bs.extend_from_slice(&vec![beta_inv; blinding_factors + 1]);

        EvaluationDomain::ifft(
            bs.as_mut_slice(),
            domain.get_omega_inv(),
            domain.k(),
            domain.ifft_divisor(),
        );

        // (b - b(0)) / X
        let mut b0_poly_coeffs: Vec<<E as Engine>::Scalar> = bs[1..].to_vec();

        let n = 1 << domain.k();
        let b_poly = domain.coeff_from_vec(bs);

        #[cfg(feature = "sanity-checks")]
        {
            let mut selector = vec![E::Scalar::one(); usable_rows];
            selector.extend_from_slice(&vec![E::Scalar::zero(); n - usable_rows]);
            assert_eq!(selector.len(), n);
            let root = domain.get_omega();
            for i in 0..n {
                assert_eq!(
                    E::Scalar::zero(),
                    eval_polynomial(&b_poly, root.pow(&[i as u64, 0, 0, 0]))
                        * (selector[i] * self.f[i] + *beta)
                        - E::Scalar::one()
                )
            }
        }
        let p_cm = best_multiexp(&b0_poly_coeffs, &pk.b0_g1_bound);

        b0_poly_coeffs.push(E::Scalar::zero());
        let b0_poly: Polynomial<<E as Engine>::Scalar, Coeff> =
            domain.coeff_from_vec(b0_poly_coeffs.clone());

        // write all commitements to transcript
        transcript.write_point(a_cm.into())?;
        transcript.write_point(qa_cm.into())?;
        transcript.write_point(a0_cm.into())?;

        let b0_cm = params.commit(&b0_poly, Blind(E::Scalar::zero()));

        transcript.write_point(b0_cm.into())?;
        transcript.write_point(p_cm.into())?;

        // Sumcheck identity:
        //      n * B(0) = N * A(0)
        //      A(0) = n * B(0) / N
        let b_at_zero = eval_polynomial(&b_poly, E::Scalar::zero());
        let a_at_zero = {
            let n_table_inv = E::Scalar::from(table_config.size as u64).invert().unwrap();
            let n = E::Scalar::from(n as u64);
            let blinding_factors = E::Scalar::from(blinding_factors as u64);
            (b_at_zero * n - (blinding_factors + E::Scalar::one()) * beta_inv) * n_table_inv
        };

        let mut f = self.f.to_vec();
        EvaluationDomain::ifft(
            &mut f,
            domain.get_omega_inv(),
            domain.k(),
            domain.ifft_divisor(),
        );

        let f = domain.coeff_from_vec(f);

        Ok(CommittedLogDerivative {
            b: b_poly,
            b0: b0_poly,
            f,
            a_at_zero,
        })
    }
}

impl<E: MultiMillerLoop> CommittedLogDerivative<E> {
    pub(in crate::plonk) fn evaluate<
        EC: EncodedChallenge<E::G1Affine>,
        T: TranscriptWrite<E::G1Affine, EC>,
    >(
        self,
        pk: &ProvingKey<E>,
        x: ChallengeX<E::G1Affine>,
        transcript: &mut T,
    ) -> Result<Evaluated<E>, Error>
    where
        E: MultiMillerLoop + Debug,
        E::G1Affine: SerdeObject,
        E::G2Affine: SerdeObject,
    {
        let b0_eval = eval_polynomial(&self.b0, *x);
        let f_eval = eval_polynomial(&self.f, *x);

        // Hash each advice evaluation
        for eval in iter::empty()
            .chain(Some(b0_eval))
            .chain(Some(f_eval))
            .chain(Some(self.a_at_zero))
        {
            transcript.write_scalar(eval)?;
        }

        Ok(Evaluated {
            constructed: self.clone(),
        })
    }
}

impl<E: MultiMillerLoop> Evaluated<E> {
    pub(in crate::plonk) fn open<'a>(
        &'a self,
        x: ChallengeX<E::G1Affine>,
    ) -> impl Iterator<Item = ProverQuery<'a, E::G1Affine>> + Clone
    where
        E: MultiMillerLoop + Debug,
        E::G1Affine: SerdeObject,
        E::G2Affine: SerdeObject,
    {
        iter::empty()
            .chain(Some(ProverQuery {
                point: *x,
                poly: &self.constructed.b0,
                blind: Blind(E::Scalar::zero()),
            }))
            .chain(Some(ProverQuery {
                point: *x,
                poly: &self.constructed.f,
                blind: Blind(E::Scalar::zero()),
            }))
    }
}
