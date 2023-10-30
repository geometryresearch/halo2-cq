//! This module provides an implementation of a variant of (Turbo)[PLONK][plonk]
//! that is designed specifically for the polynomial commitment scheme described
//! in the [Halo][halo] paper.
//!
//! [halo]: https://eprint.iacr.org/2019/1021
//! [plonk]: https://eprint.iacr.org/2019/953

use blake2b_simd::Params as Blake2bParams;
use ff::PrimeField;
use group::{ff::Field, GroupEncoding};
use halo2curves::pairing::{Engine, MultiMillerLoop};
use halo2curves::serde::SerdeObject;
use halo2curves::CurveExt;

use crate::arithmetic::{CurveAffine, FieldExt};
use crate::helpers::{
    polynomial_slice_byte_length, read_polynomial_vec, write_polynomial_slice, SerdeCurveAffine,
    SerdePrimeField,
};
use crate::poly::{
    commitment::Params, Coeff, EvaluationDomain, ExtendedLagrangeCoeff, LagrangeCoeff,
    PinnedEvaluationDomain, Polynomial,
};
use crate::transcript::{ChallengeScalar, EncodedChallenge, Transcript};
use crate::SerdeFormat;

mod assigned;
mod circuit;
mod error;
mod evaluation;
mod keygen;
mod lookup;
pub(crate) mod permutation;
pub mod static_lookup;
mod vanishing;

mod prover;
mod verifier;

pub use assigned::*;
pub use circuit::*;
pub use error::*;
pub use keygen::*;
pub use prover::*;
pub use verifier::*;

use evaluation::Evaluator;
use std::collections::BTreeMap;
use std::fmt::Debug;
use std::io;

use self::static_lookup::{
    StaticCommittedTable, StaticTable, StaticTableConfig, StaticTableId, StaticTableValues,
};

/// This is a verifying key which allows for the verification of proofs for a
/// particular circuit.
#[derive(Clone, Debug)]
pub struct VerifyingKey<E>
where
    E: MultiMillerLoop + Debug,
    E::G1Affine: SerdeCurveAffine,
    E::G2Affine: SerdeCurveAffine,
{
    domain: EvaluationDomain<E::Scalar>,
    fixed_commitments: Vec<E::G1Affine>,
    permutation: permutation::VerifyingKey<E::G1Affine>,
    cs: ConstraintSystem<E::Scalar>,
    /// Cached maximum degree of `cs` (which doesn't change after construction).
    cs_degree: usize,
    /// The representative of this `VerifyingKey` in transcripts.
    transcript_repr: E::Scalar,
    selectors: Vec<Vec<bool>>,
    static_table_mapping: BTreeMap<StaticTableId<String>, StaticCommittedTable<E>>,
}

impl<E> VerifyingKey<E>
where
    E: MultiMillerLoop + Debug,
    E::G1Affine: SerdeCurveAffine,
    E::G2Affine: SerdeCurveAffine,
    E::Scalar: SerdePrimeField,
{
    /// Writes a verifying key to a buffer.
    ///
    /// Writes a curve element according to `format`:
    /// - `Processed`: Writes a compressed curve element with coordinates in standard form.
    /// Writes a field element in standard form, with endianness specified by the
    /// `PrimeField` implementation.
    /// - Otherwise: Writes an uncompressed curve element with coordinates in Montgomery form
    /// Writes a field element into raw bytes in its internal Montgomery representation,
    /// WITHOUT performing the expensive Montgomery reduction.
    pub fn write<W: io::Write>(&self, writer: &mut W, format: SerdeFormat) -> io::Result<()> {
        writer.write_all(&self.domain.k().to_be_bytes()).unwrap();
        writer
            .write_all(&(self.fixed_commitments.len() as u32).to_be_bytes())
            .unwrap();
        for commitment in &self.fixed_commitments {
            commitment.write(writer, format);
        }
        self.permutation.write(writer, format);

        // write self.selectors
        for selector in &self.selectors {
            // since `selector` is filled with `bool`, we pack them 8 at a time into bytes and then write
            for bits in selector.chunks(8) {
                writer.write_all(&[crate::helpers::pack(bits)]).unwrap();
            }
        }
        Ok(())
    }

    /// Reads a verification key from a buffer.
    ///
    /// Reads a curve element from the buffer and parses it according to the `format`:
    /// - `Processed`: Reads a compressed curve element and decompresses it.
    /// Reads a field element in standard form, with endianness specified by the
    /// `PrimeField` implementation, and checks that the element is less than the modulus.
    /// - `RawBytes`: Reads an uncompressed curve element with coordinates in Montgomery form.
    /// Checks that field elements are less than modulus, and then checks that the point is on the curve.
    /// - `RawBytesUnchecked`: Reads an uncompressed curve element with coordinates in Montgomery form;
    /// does not perform any checks
    pub fn read<R: io::Read, ConcreteCircuit: Circuit<E>>(
        reader: &mut R,
        format: SerdeFormat,
    ) -> io::Result<Self> {
        let mut k = [0u8; 4];
        reader.read_exact(&mut k)?;
        let k = u32::from_be_bytes(k);
        let (domain, cs, _) = keygen::create_domain::<E, ConcreteCircuit>(k);
        let mut num_fixed_columns = [0u8; 4];
        reader.read_exact(&mut num_fixed_columns).unwrap();
        let num_fixed_columns = u32::from_be_bytes(num_fixed_columns);

        let fixed_commitments: Vec<_> = (0..num_fixed_columns)
            .map(|_| E::G1Affine::read(reader, format))
            .collect();

        let permutation = permutation::VerifyingKey::read(reader, &cs.permutation, format);

        // read selectors
        let selectors: Vec<Vec<bool>> = vec![vec![false; 1 << k]; cs.num_selectors]
            .into_iter()
            .map(|mut selector| {
                let mut selector_bytes = vec![0u8; (selector.len() + 7) / 8];
                reader.read_exact(&mut selector_bytes).unwrap();
                for (bits, byte) in selector.chunks_mut(8).into_iter().zip(selector_bytes) {
                    crate::helpers::unpack(byte, bits);
                }
                selector
            })
            .collect();
        let (cs, _) = cs.compress_selectors(selectors.clone());

        Ok(Self::from_parts(
            domain,
            fixed_commitments,
            permutation,
            cs,
            selectors,
            // TODO: FIXME
            BTreeMap::default(),
        ))
    }

    /// Writes a verifying key to a vector of bytes using [`Self::write`].
    pub fn to_bytes(&self, format: SerdeFormat) -> Vec<u8> {
        let mut bytes = Vec::<u8>::with_capacity(self.bytes_length());
        Self::write(self, &mut bytes, format).expect("Writing to vector should not fail");
        bytes
    }

    /// Reads a verification key from a slice of bytes using [`Self::read`].
    pub fn from_bytes<ConcreteCircuit: Circuit<E>>(
        mut bytes: &[u8],
        format: SerdeFormat,
    ) -> io::Result<Self> {
        Self::read::<_, ConcreteCircuit>(&mut bytes, format)
    }
}

impl<E: MultiMillerLoop + Debug> VerifyingKey<E>
where
    E::G1Affine: SerdeCurveAffine,
    E::G2Affine: SerdeCurveAffine,
{
    fn bytes_length(&self) -> usize {
        8 + (self.fixed_commitments.len() * E::G1Affine::default().to_bytes().as_ref().len())
            + self.permutation.bytes_length()
            + self.selectors.len()
                * (self
                    .selectors
                    .get(0)
                    .map(|selector| selector.len() / 8 + 1)
                    .unwrap_or(0))
    }

    fn from_parts(
        domain: EvaluationDomain<E::Scalar>,
        fixed_commitments: Vec<E::G1Affine>,
        permutation: permutation::VerifyingKey<E::G1Affine>,
        cs: ConstraintSystem<E::Scalar>,
        selectors: Vec<Vec<bool>>,
        static_table_mapping: BTreeMap<StaticTableId<String>, StaticCommittedTable<E>>,
    ) -> Self {
        // Compute cached values.
        let cs_degree = cs.degree();

        let mut vk = Self {
            domain,
            fixed_commitments,
            permutation,
            cs,
            cs_degree,
            // Temporary, this is not pinned.
            transcript_repr: E::Scalar::zero(),
            selectors,
            static_table_mapping,
        };

        let mut hasher = Blake2bParams::new()
            .hash_length(64)
            .personal(b"Halo2-Verify-Key")
            .to_state();

        let s = format!("{:?}", vk.pinned());

        hasher.update(&(s.len() as u64).to_le_bytes());
        hasher.update(s.as_bytes());

        // Hash in final Blake2bState
        vk.transcript_repr = E::Scalar::from_bytes_wide(hasher.finalize().as_array());

        vk
    }

    /// Hashes a verification key into a transcript.
    pub fn hash_into<EC: EncodedChallenge<E::G1Affine>, T: Transcript<E::G1Affine, EC>>(
        &self,
        transcript: &mut T,
    ) -> io::Result<()> {
        transcript.common_scalar(self.transcript_repr)?;

        Ok(())
    }

    /// Obtains a pinned representation of this verification key that contains
    /// the minimal information necessary to reconstruct the verification key.
    pub fn pinned(&self) -> PinnedVerificationKey<'_, E::G1Affine> {
        PinnedVerificationKey {
            base_modulus: <E::G1Affine as CurveAffine>::Base::MODULUS,
            scalar_modulus: <E::Scalar as FieldExt>::MODULUS,
            domain: self.domain.pinned(),
            fixed_commitments: &self.fixed_commitments,
            permutation: &self.permutation,
            cs: self.cs.pinned(),
        }
    }

    /// Returns commitments of fixed polynomials
    pub fn fixed_commitments(&self) -> &Vec<E::G1Affine> {
        &self.fixed_commitments
    }

    /// Returns `VerifyingKey` of permutation
    pub fn permutation(&self) -> &permutation::VerifyingKey<E::G1Affine> {
        &self.permutation
    }

    /// Returns `ConstraintSystem`
    pub fn cs(&self) -> &ConstraintSystem<E::Scalar> {
        &self.cs
    }
}

/// Minimal representation of a verification key that can be used to identify
/// its active contents.
#[allow(dead_code)]
#[derive(Debug)]
pub struct PinnedVerificationKey<'a, C: CurveAffine> {
    base_modulus: &'static str,
    scalar_modulus: &'static str,
    domain: PinnedEvaluationDomain<'a, C::Scalar>,
    cs: PinnedConstraintSystem<'a, C::Scalar>,
    fixed_commitments: &'a Vec<C>,
    permutation: &'a permutation::VerifyingKey<C>,
}
/// This is a proving key which allows for the creation of proofs for a
/// particular circuit.
#[derive(Clone, Debug)]
pub struct ProvingKey<E: MultiMillerLoop + Debug>
where
    E::G1Affine: SerdeObject,
    E::G2Affine: SerdeObject,
{
    vk: VerifyingKey<E>,
    l0: Polynomial<E::Scalar, ExtendedLagrangeCoeff>,
    l_last: Polynomial<E::Scalar, ExtendedLagrangeCoeff>,
    l_active_row: Polynomial<E::Scalar, ExtendedLagrangeCoeff>,
    fixed_values: Vec<Polynomial<E::Scalar, LagrangeCoeff>>,
    fixed_polys: Vec<Polynomial<E::Scalar, Coeff>>,
    fixed_cosets: Vec<Polynomial<E::Scalar, ExtendedLagrangeCoeff>>,
    permutation: permutation::ProvingKey<E::G1Affine>,
    ev: Evaluator<E::G1Affine>,
    static_table_mapping: BTreeMap<StaticTableId<String>, StaticTableValues<E>>,
    static_table_configs: BTreeMap<usize, StaticTableConfig<E>>,
    b0_g1_bound: Vec<E::G1Affine>,
}

impl<E: MultiMillerLoop + Debug> ProvingKey<E>
where
    E::G1Affine: SerdeObject,
    E::G2Affine: SerdeObject,
{
    /// Get the underlying [`VerifyingKey`].
    pub fn get_vk(&self) -> &VerifyingKey<E> {
        &self.vk
    }

    /// Gets the total number of bytes in the serialization of `self`
    fn bytes_length(&self) -> usize {
        let scalar_len = E::Scalar::default().to_repr().as_ref().len();
        self.vk.bytes_length()
            + 12
            + scalar_len * (self.l0.len() + self.l_last.len() + self.l_active_row.len())
            + polynomial_slice_byte_length(&self.fixed_values)
            + polynomial_slice_byte_length(&self.fixed_polys)
            + polynomial_slice_byte_length(&self.fixed_cosets)
            + self.permutation.bytes_length()
    }
}

impl<E: MultiMillerLoop + Debug> ProvingKey<E>
where
    E::Scalar: SerdePrimeField,
    E::G1Affine: SerdeObject,
    E::G2Affine: SerdeObject,
{
    /// Writes a proving key to a buffer.
    ///
    /// Writes a curve element according to `format`:
    /// - `Processed`: Writes a compressed curve element with coordinates in standard form.
    /// Writes a field element in standard form, with endianness specified by the
    /// `PrimeField` implementation.
    /// - Otherwise: Writes an uncompressed curve element with coordinates in Montgomery form
    /// Writes a field element into raw bytes in its internal Montgomery representation,
    /// WITHOUT performing the expensive Montgomery reduction.
    /// Does so by first writing the verifying key and then serializing the rest of the data (in the form of field polynomials)
    pub fn write<W: io::Write>(&self, writer: &mut W, format: SerdeFormat) -> io::Result<()> {
        self.vk.write(writer, format).unwrap();
        self.l0.write(writer, format);
        self.l_last.write(writer, format);
        self.l_active_row.write(writer, format);
        write_polynomial_slice(&self.fixed_values, writer, format);
        write_polynomial_slice(&self.fixed_polys, writer, format);
        write_polynomial_slice(&self.fixed_cosets, writer, format);
        self.permutation.write(writer, format);
        Ok(())
    }

    /// Reads a proving key from a buffer.
    /// Does so by reading verification key first, and then deserializing the rest of the file into the remaining proving key data.
    ///
    /// Reads a curve element from the buffer and parses it according to the `format`:
    /// - `Processed`: Reads a compressed curve element and decompresses it.
    /// Reads a field element in standard form, with endianness specified by the
    /// `PrimeField` implementation, and checks that the element is less than the modulus.
    /// - `RawBytes`: Reads an uncompressed curve element with coordinates in Montgomery form.
    /// Checks that field elements are less than modulus, and then checks that the point is on the curve.
    /// - `RawBytesUnchecked`: Reads an uncompressed curve element with coordinates in Montgomery form;
    /// does not perform any checks
    pub fn read<R: io::Read, ConcreteCircuit: Circuit<E>>(
        reader: &mut R,
        format: SerdeFormat,
    ) -> io::Result<Self> {
        let vk = VerifyingKey::<E>::read::<R, ConcreteCircuit>(reader, format).unwrap();
        let l0 = Polynomial::read(reader, format);
        let l_last = Polynomial::read(reader, format);
        let l_active_row = Polynomial::read(reader, format);
        let fixed_values = read_polynomial_vec(reader, format);
        let fixed_polys = read_polynomial_vec(reader, format);
        let fixed_cosets = read_polynomial_vec(reader, format);
        let permutation = permutation::ProvingKey::read(reader, format);
        // TODO:
        // let static_tables = static_lookup::StaticTable::read(reader, format);
        let ev = Evaluator::new(vk.cs());

        Ok(Self {
            vk,
            l0,
            l_last,
            l_active_row,
            fixed_values,
            fixed_polys,
            fixed_cosets,
            permutation,
            ev,
            // FIXME
            static_table_mapping: BTreeMap::default(),
            static_table_configs: BTreeMap::default(),
            b0_g1_bound: vec![],
        })
    }

    /// Writes a proving key to a vector of bytes using [`Self::write`].
    pub fn to_bytes(&self, format: SerdeFormat) -> Vec<u8> {
        let mut bytes = Vec::<u8>::with_capacity(self.bytes_length());
        Self::write(self, &mut bytes, format).expect("Writing to vector should not fail");
        bytes
    }

    /// Reads a proving key from a slice of bytes using [`Self::read`].
    pub fn from_bytes<ConcreteCircuit: Circuit<E>>(
        mut bytes: &[u8],
        format: SerdeFormat,
    ) -> io::Result<Self> {
        Self::read::<_, ConcreteCircuit>(&mut bytes, format)
    }
}

impl<E: MultiMillerLoop + Debug> VerifyingKey<E>
where
    E::G1Affine: SerdeObject,
    E::G2Affine: SerdeObject,
{
    /// Get the underlying [`EvaluationDomain`].
    pub fn get_domain(&self) -> &EvaluationDomain<E::Scalar> {
        &self.domain
    }
}

#[derive(Clone, Copy, Debug)]
struct Theta;
type ChallengeTheta<F> = ChallengeScalar<F, Theta>;

#[derive(Clone, Copy, Debug)]
struct Beta;
type ChallengeBeta<F> = ChallengeScalar<F, Beta>;

#[derive(Clone, Copy, Debug)]
struct Gamma;
type ChallengeGamma<F> = ChallengeScalar<F, Gamma>;

#[derive(Clone, Copy, Debug)]
struct Y;
type ChallengeY<F> = ChallengeScalar<F, Y>;

#[derive(Clone, Copy, Debug)]
struct X;
type ChallengeX<F> = ChallengeScalar<F, X>;
