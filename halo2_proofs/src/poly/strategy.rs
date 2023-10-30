use std::fmt::Debug;

use halo2curves::CurveAffine;
use rand_core::RngCore;

use super::{
    commitment::{CommitmentScheme, Verifier, MSM},
    kzg::commitment::KZGCommitmentScheme,
};
use crate::{
    plonk::Error,
    transcript::{EncodedChallenge, TranscriptRead},
};
use halo2curves::serde::SerdeObject;
use halo2curves::{batch_pairing::PairingBatcher, pairing::MultiMillerLoop};

/// Guards is unfinished verification result. Implement this to construct various
/// verification strategies such as aggregation and recursion.
pub trait Guard<Scheme: CommitmentScheme> {
    /// Multi scalar engine which is not evaluated yet.
    type MSMAccumulator;
}

/// Trait representing a strategy for verifying Halo 2 proofs.
pub trait VerificationStrategy<'params, E: MultiMillerLoop + Debug, V: Verifier<'params, E>>
where
    E::G1Affine: SerdeObject,
    E::G2Affine: SerdeObject,
{
    /// The output type of this verification strategy after processing a proof.
    type Output;

    /// Creates new verification strategy instance
    fn new(params: &'params <KZGCommitmentScheme<E> as CommitmentScheme>::ParamsVerifier) -> Self;

    /// Obtains an MSM from the verifier strategy and yields back the strategy's
    /// output.
    fn process(
        self,
        f: impl FnOnce(V::MSMAccumulator) -> Result<V::Guard, Error>,
    ) -> Result<Self::Output, Error>;

    /// Finalizes the batch and checks its validity.
    ///
    /// Returns `false` if *some* proof was invalid. If the caller needs to identify
    /// specific failing proofs, it must re-process the proofs separately.
    fn finalize(self) -> bool;

    /// Merges the pairing with a pairing batcher.
    fn merge_with_pairing_batcher(self, pairing_batcher: &mut PairingBatcher<E>);
}
