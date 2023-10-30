use std::iter;

use super::super::{
    circuit::Expression, ChallengeBeta, ChallengeGamma, ChallengeTheta, ChallengeX,
};
use super::{Argument, StaticTableId};
use crate::poly::kzg::commitment::ParamsKZG;
use crate::{
    arithmetic::{CurveAffine, FieldExt},
    plonk::{Error, VerifyingKey},
    poly::{commitment::MSM, Rotation, VerifierQuery},
    transcript::{EncodedChallenge, TranscriptRead},
};
use ff::Field;
use group::{prime::PrimeCurveAffine, Group};
use halo2curves::batch_pairing::PairingBatcher;
use halo2curves::pairing::{Engine, MultiMillerLoop};
use halo2curves::serde::SerdeObject;
use std::fmt::Debug;

pub struct CommittedWitness<E: MultiMillerLoop> {
    f: E::G1Affine,
    m: E::G1Affine,
    table_ids: Vec<StaticTableId<String>>,
}

pub struct CommittedLogDerivative<E: MultiMillerLoop> {
    committed_witness: CommittedWitness<E>,
    a: E::G1Affine,
    qa: E::G1Affine,
    a0: E::G1Affine,
    b0: E::G1Affine,
    p: E::G1Affine,
}

pub struct Evaluated<E: MultiMillerLoop> {
    committed: CommittedLogDerivative<E>,
    b0_eval: E::Scalar,
    f_eval: E::Scalar,
    a_at_zero: E::Scalar,
}

impl<F: FieldExt> Argument<F> {
    pub(in crate::plonk) fn read_committed<
        E: MultiMillerLoop + Debug,
        EC: EncodedChallenge<E::G1Affine>,
        T: TranscriptRead<E::G1Affine, EC>,
    >(
        &self,
        transcript: &mut T,
    ) -> Result<CommittedWitness<E>, Error> {
        let f = transcript.read_point()?;
        let m = transcript.read_point()?;

        // TODO: CHECK THAT ALL TABLES ARE OF SAME SIZE

        Ok(CommittedWitness {
            f,
            m,
            table_ids: self.table_ids.clone(),
        })
    }
}

impl<E: MultiMillerLoop> CommittedWitness<E> {
    pub(in crate::plonk) fn read_committed_log_derivative<
        EC: EncodedChallenge<E::G1Affine>,
        T: TranscriptRead<E::G1Affine, EC>,
    >(
        self,
        transcript: &mut T,
    ) -> Result<CommittedLogDerivative<E>, Error> {
        let a = transcript.read_point()?;
        let qa = transcript.read_point()?;
        let a0 = transcript.read_point()?;
        let b0 = transcript.read_point()?;
        let p = transcript.read_point()?;

        Ok(CommittedLogDerivative {
            committed_witness: self,
            a,
            qa,
            a0,
            b0,
            p,
        })
    }
}

impl<E: MultiMillerLoop> CommittedLogDerivative<E> {
    pub(crate) fn evaluate<
        EC: EncodedChallenge<E::G1Affine>,
        T: TranscriptRead<E::G1Affine, EC>,
    >(
        self,
        transcript: &mut T,
    ) -> Result<Evaluated<E>, Error> {
        let b0_eval = transcript.read_scalar()?;
        let f_eval = transcript.read_scalar()?;
        let a_at_zero = transcript.read_scalar()?;

        Ok(Evaluated {
            committed: self,
            b0_eval,
            f_eval,
            a_at_zero,
        })
    }
}

impl<E> Evaluated<E>
where
    E: MultiMillerLoop + Debug,
    E::G1Affine: SerdeObject,
    E::G2Affine: SerdeObject,
{
    pub(in crate::plonk) fn register_pairings<'a>(
        &self,
        vk: &'a VerifyingKey<E>,
        params: &ParamsKZG<E>,
        pairing_batcher: &mut PairingBatcher<E>,
        beta: ChallengeBeta<E::G1Affine>,
        theta: ChallengeTheta<E::G1Affine>,
    ) -> Result<(), Error> {
        // TODO: make nicer error
        let tables: Vec<_> = self
            .committed
            .committed_witness
            .table_ids
            .iter()
            .map(|table_id| {
                vk.static_table_mapping
                    .get(table_id)
                    .expect("Key not exists")
            })
            .collect();

        // Check that A encodes the correct values:
        // e(a, [T(x)]_2) = e(q_a, [Z_V(x)]_2) * e(m - ß * a, [1]_2)
        //
        // Check that B_0 has the appropriate degree:
        // e(b_0, [x_b0_bound]_2) = e(p, [1]_2)

        // e(m - ß * a, [1]_2)
        let m_minus_beta_a: E::G1Affine =
            (self.committed.committed_witness.m - (self.committed.a * *beta).into()).into();

        let a_at_zero_cm: E::G1Affine =
            (<E as Engine>::G1Affine::generator() * self.a_at_zero).into();

        let compress_tables = || {
            tables.iter().fold(E::G2Affine::identity(), |acc, table| {
                let acc = acc * *theta + table.t;

                // TODO: do this in projective
                acc.into()
            })
        };

        let table_t = compress_tables();

        pairing_batcher.add_pairing(&[
            // e(a, [T(x)]_2)
            (self.committed.a, table_t),
            // e(-q_a, [Z_V(x)]_2)
            ((-self.committed.qa).into(), tables[0].zv),
            // e(- (m - ß * a), [1]_2)
            ((-m_minus_beta_a).into(), params.g2()),
            // e(b_0, [x_b0_bound]_2)
            (self.committed.b0, tables[0].x_b0_bound), //TODO: MAKE THIS SHARED
            // e(-p, [1]_2)
            ((-self.committed.p).into(), params.g2()),
            // e(a - [a0], [1]_2)
            ((self.committed.a - a_at_zero_cm).into(), params.g2()),
            // e(-a0, [x]_2)
            ((-self.committed.a0).into(), params.s_g2()),
        ]);

        Ok(())
    }

    pub(in crate::plonk) fn expressions<'a>(
        &'a self,
        vk: &'a VerifyingKey<E>,
        l_last: E::Scalar,
        l_blind: E::Scalar,
        beta: ChallengeBeta<E::G1Affine>,
        x: ChallengeX<E::G1Affine>,
    ) -> impl Iterator<Item = E::Scalar> + 'a {
        let active_rows = E::Scalar::one() - (l_last + l_blind);

        let tables: Vec<_> = self
            .committed
            .committed_witness
            .table_ids
            .iter()
            .map(|table_id| {
                vk.static_table_mapping
                    .get(&table_id)
                    .expect("Key does not exists")
            })
            .collect();

        let table_size = E::Scalar::from(tables[0].size as u64);

        let blinding_factors = vk.cs.blinding_factors();
        let unusable_rows = E::Scalar::from((blinding_factors + 1) as u64);

        let b_at_zero = {
            let beta_inv = beta.invert().unwrap();
            let circuit_domain_inv = E::Scalar::from(vk.get_domain().n).invert().unwrap();
            (table_size * self.a_at_zero + unusable_rows * beta_inv) * circuit_domain_inv
        };

        let b_eval = self.b0_eval * *x + b_at_zero;

        std::iter::empty().chain(Some(
            // b(l_active * f + beta) - 1 = 0
            b_eval * (active_rows * self.f_eval + *beta) - E::Scalar::one(),
        ))
    }

    pub(in crate::plonk) fn queries<'r, M: MSM<E::G1Affine> + 'r>(
        &'r self,
        vk: &'r VerifyingKey<E>,
        x: ChallengeX<E::G1Affine>,
    ) -> impl Iterator<Item = VerifierQuery<'r, E::G1Affine, M>> + Clone {
        iter::empty()
            .chain(Some(VerifierQuery::new_commitment(
                &self.committed.b0,
                *x,
                self.b0_eval,
            )))
            .chain(Some(VerifierQuery::new_commitment(
                &self.committed.committed_witness.f,
                *x,
                self.f_eval,
            )))
    }
}
