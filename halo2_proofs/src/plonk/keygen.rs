#![allow(clippy::int_plus_one)]

use std::ops::Range;
use std::{collections::BTreeMap, fmt::Debug};

use ff::Field;
use group::Curve;
use halo2curves::{pairing::MultiMillerLoop, serde::SerdeObject};

use super::static_lookup::{StaticCommittedTable, StaticTableConfig, StaticTableValues};
use super::{
    circuit::{
        Advice, Any, Assignment, Circuit, Column, ConstraintSystem, Fixed, FloorPlanner, Instance,
        Selector,
    },
    evaluation::Evaluator,
    permutation,
    static_lookup::{StaticTable, StaticTableId},
    Assigned, Challenge, Error, Expression, LagrangeCoeff, Polynomial, ProvingKey, VerifyingKey,
};
use crate::{
    arithmetic::{parallelize, CurveAffine},
    circuit::Value,
    poly::{
        batch_invert_assigned,
        commitment::{Blind, Params, MSM},
        EvaluationDomain,
    },
};

pub(crate) fn create_domain<E, ConcreteCircuit>(
    k: u32,
) -> (
    EvaluationDomain<E::Scalar>,
    ConstraintSystem<E::Scalar>,
    ConcreteCircuit::Config,
)
where
    E: MultiMillerLoop,
    ConcreteCircuit: Circuit<E>,
{
    let mut cs = ConstraintSystem::default();
    let config = ConcreteCircuit::configure(&mut cs);

    let degree = cs.degree();

    let domain = EvaluationDomain::new(degree as u32, k);

    (domain, cs, config)
}

#[derive(Debug)]
enum SynthCtx {
    Prover,
    Verifier,
}

/// Assembly to be used in circuit synthesis.
#[derive(Debug)]
struct Assembly<F: Field, E: MultiMillerLoop<Scalar = F>> {
    k: u32,
    fixed: Vec<Polynomial<Assigned<F>, LagrangeCoeff>>,
    permutation: permutation::keygen::Assembly,
    selectors: Vec<Vec<bool>>,
    // A range of available rows for assignment and copies.
    usable_rows: Range<usize>,
    static_table_mapping: BTreeMap<StaticTableId<String>, StaticTable<E>>,
    ctx: SynthCtx,
    _marker: std::marker::PhantomData<F>,
}

impl<F: Field, E: MultiMillerLoop<Scalar = F>> Assignment<F> for Assembly<F, E> {
    type E = E;

    fn enter_region<NR, N>(&mut self, _: N)
    where
        NR: Into<String>,
        N: FnOnce() -> NR,
    {
        // Do nothing; we don't care about regions in this context.
    }

    fn exit_region(&mut self) {
        // Do nothing; we don't care about regions in this context.
    }

    fn register_static_table(&mut self, id: StaticTableId<String>, static_table: StaticTable<E>) {
        // if ctx = prover then check that prover part is some and take it else panic
        // if ctx = verifier then check that verifier part is some and take it else panic
        match self.ctx {
            SynthCtx::Prover => {
                assert!(static_table.opened.is_some());
            }
            SynthCtx::Verifier => {
                assert!(static_table.committed.is_some());
            }
        }

        self.static_table_mapping.insert(id, static_table);
    }

    fn enable_selector<A, AR>(&mut self, _: A, selector: &Selector, row: usize) -> Result<(), Error>
    where
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        if !self.usable_rows.contains(&row) {
            return Err(Error::not_enough_rows_available(self.k));
        }

        self.selectors[selector.0][row] = true;

        Ok(())
    }

    fn query_instance(&self, _: Column<Instance>, row: usize) -> Result<Value<F>, Error> {
        if !self.usable_rows.contains(&row) {
            return Err(Error::not_enough_rows_available(self.k));
        }

        // There is no instance in this context.
        Ok(Value::unknown())
    }

    fn assign_advice<'r, 'v>(
        //<V, VR, A, AR>(
        &'r mut self,
        //_: A,
        _: Column<Advice>,
        _: usize,
        _: Value<Assigned<F>>,
    ) -> Result<Value<&'v Assigned<F>>, Error> {
        Ok(Value::unknown())
    }

    fn assign_fixed(&mut self, column: Column<Fixed>, row: usize, to: Assigned<F>) {
        if !self.usable_rows.contains(&row) {
            panic!(
                "Assign Fixed {:?}",
                Error::not_enough_rows_available(self.k)
            );
        }

        *self
            .fixed
            .get_mut(column.index())
            .and_then(|v| v.get_mut(row))
            .unwrap_or_else(|| panic!("{:?}", Error::BoundsFailure)) = to;
    }

    fn copy(
        &mut self,
        left_column: Column<Any>,
        left_row: usize,
        right_column: Column<Any>,
        right_row: usize,
    ) {
        if !self.usable_rows.contains(&left_row) || !self.usable_rows.contains(&right_row) {
            panic!("{:?}", Error::not_enough_rows_available(self.k));
        }

        self.permutation
            .copy(left_column, left_row, right_column, right_row)
            .unwrap_or_else(|err| panic!("{err:?}"))
    }

    fn fill_from_row(
        &mut self,
        column: Column<Fixed>,
        from_row: usize,
        to: Value<Assigned<F>>,
    ) -> Result<(), Error> {
        if !self.usable_rows.contains(&from_row) {
            return Err(Error::not_enough_rows_available(self.k));
        }

        let col = self
            .fixed
            .get_mut(column.index())
            .ok_or(Error::BoundsFailure)?;

        let filler = to.assign()?;
        for row in self.usable_rows.clone().skip(from_row) {
            col[row] = filler;
        }

        Ok(())
    }

    fn get_challenge(&self, _: Challenge) -> Value<F> {
        Value::unknown()
    }

    fn push_namespace<NR, N>(&mut self, _: N)
    where
        NR: Into<String>,
        N: FnOnce() -> NR,
    {
        // Do nothing; we don't care about namespaces in this context.
    }

    fn pop_namespace(&mut self, _: Option<String>) {
        // Do nothing; we don't care about namespaces in this context.
    }
}

/// Generate a `VerifyingKey` from an instance of `Circuit`.
pub fn keygen_vk<'params, E, P, ConcreteCircuit>(
    params: &P,
    circuit: &ConcreteCircuit,
) -> Result<VerifyingKey<E>, Error>
where
    E: MultiMillerLoop + Debug,
    E::G1Affine: SerdeObject,
    E::G2Affine: SerdeObject,
    P: Params<'params, E::G1Affine>,
    ConcreteCircuit: Circuit<E>,
{
    let (domain, cs, config) = create_domain::<E, ConcreteCircuit>(params.k());

    if (params.n() as usize) < cs.minimum_rows() {
        return Err(Error::not_enough_rows_available(params.k()));
    }

    let mut assembly: Assembly<E::Scalar, E> = Assembly {
        k: params.k(),
        fixed: vec![domain.empty_lagrange_assigned(); cs.num_fixed_columns],
        permutation: permutation::keygen::Assembly::new(params.n() as usize, &cs.permutation),
        selectors: vec![vec![false; params.n() as usize]; cs.num_selectors],
        usable_rows: 0..params.n() as usize - (cs.blinding_factors() + 1),
        static_table_mapping: BTreeMap::default(),
        ctx: SynthCtx::Verifier,
        _marker: std::marker::PhantomData,
    };

    // Synthesize the circuit to obtain URS
    ConcreteCircuit::FloorPlanner::synthesize(
        &mut assembly,
        circuit,
        config,
        cs.constants.clone(),
    )?;

    let mut fixed = batch_invert_assigned(assembly.fixed);
    let (cs, selector_polys) = cs.compress_selectors(assembly.selectors.clone());
    fixed.extend(
        selector_polys
            .into_iter()
            .map(|poly| domain.lagrange_from_vec(poly)),
    );

    let permutation_vk = assembly
        .permutation
        .build_vk(params, &domain, &cs.permutation);

    let fixed_commitments = fixed
        .iter()
        .map(|poly| params.commit_lagrange(poly, Blind::default()).to_affine())
        .collect();

    let static_table_mapping: BTreeMap<StaticTableId<String>, StaticCommittedTable<E>> = assembly
        .static_table_mapping
        .iter()
        .map(|(k, v)| (k.clone(), v.committed.clone().unwrap())) //safe to unwrap since this is checked in register_static_table method
        .collect();

    Ok(VerifyingKey::from_parts(
        domain,
        fixed_commitments,
        permutation_vk,
        cs,
        assembly.selectors,
        static_table_mapping,
    ))
}

/// Generate a `ProvingKey` from a `VerifyingKey` and an instance of `Circuit`.
pub fn keygen_pk<'params, E, P, ConcreteCircuit>(
    params: &P,
    static_table_configs: BTreeMap<usize, StaticTableConfig<E>>,
    b0_g1_bound: Vec<E::G1Affine>,
    vk: VerifyingKey<E>,
    circuit: &ConcreteCircuit,
) -> Result<ProvingKey<E>, Error>
where
    E: MultiMillerLoop + Debug,
    E::G1Affine: SerdeObject,
    E::G2Affine: SerdeObject,
    P: Params<'params, E::G1Affine>,
    ConcreteCircuit: Circuit<E>,
{
    let mut cs = ConstraintSystem::default();
    let config = ConcreteCircuit::configure(&mut cs);

    let cs = cs;

    if (params.n() as usize) < cs.minimum_rows() {
        return Err(Error::not_enough_rows_available(params.k()));
    }

    let mut assembly: Assembly<E::Scalar, E> = Assembly {
        k: params.k(),
        fixed: vec![vk.domain.empty_lagrange_assigned(); cs.num_fixed_columns],
        permutation: permutation::keygen::Assembly::new(params.n() as usize, &cs.permutation),
        selectors: vec![vec![false; params.n() as usize]; cs.num_selectors],
        usable_rows: 0..params.n() as usize - (cs.blinding_factors() + 1),
        static_table_mapping: BTreeMap::default(),
        ctx: SynthCtx::Prover,
        _marker: std::marker::PhantomData,
    };

    // Synthesize the circuit to obtain URS
    ConcreteCircuit::FloorPlanner::synthesize(
        &mut assembly,
        circuit,
        config,
        cs.constants.clone(),
    )?;

    let mut fixed = batch_invert_assigned(assembly.fixed);
    let (cs, selector_polys) = cs.compress_selectors(assembly.selectors);
    fixed.extend(
        selector_polys
            .into_iter()
            .map(|poly| vk.domain.lagrange_from_vec(poly)),
    );

    let fixed_polys: Vec<_> = fixed
        .iter()
        .map(|poly| vk.domain.lagrange_to_coeff(poly.clone()))
        .collect();

    let fixed_cosets = fixed_polys
        .iter()
        .map(|poly| vk.domain.coeff_to_extended(poly.clone()))
        .collect();

    let permutation_pk = assembly
        .permutation
        .build_pk(params, &vk.domain, &cs.permutation);

    // Compute l_0(X)
    // TODO: this can be done more efficiently
    let mut l0 = vk.domain.empty_lagrange();
    l0[0] = E::Scalar::one();
    let l0 = vk.domain.lagrange_to_coeff(l0);
    let l0 = vk.domain.coeff_to_extended(l0);

    // Compute l_blind(X) which evaluates to 1 for each blinding factor row
    // and 0 otherwise over the domain.
    let mut l_blind = vk.domain.empty_lagrange();
    for evaluation in l_blind[..].iter_mut().rev().take(cs.blinding_factors()) {
        *evaluation = E::Scalar::one();
    }
    let l_blind = vk.domain.lagrange_to_coeff(l_blind);
    let l_blind = vk.domain.coeff_to_extended(l_blind);

    // Compute l_last(X) which evaluates to 1 on the first inactive row (just
    // before the blinding factors) and 0 otherwise over the domain
    let mut l_last = vk.domain.empty_lagrange();
    l_last[params.n() as usize - cs.blinding_factors() - 1] = E::Scalar::one();
    let l_last = vk.domain.lagrange_to_coeff(l_last);
    let l_last = vk.domain.coeff_to_extended(l_last);

    // Compute l_active_row(X)
    let one = E::Scalar::one();
    let mut l_active_row = vk.domain.empty_extended();
    parallelize(&mut l_active_row, |values, start| {
        for (i, value) in values.iter_mut().enumerate() {
            let idx = i + start;
            *value = one - (l_last[idx] + l_blind[idx]);
        }
    });

    // Compute the optimized evaluation data structure
    let ev = Evaluator::new(&vk.cs);
    let static_table_mapping: BTreeMap<StaticTableId<String>, StaticTableValues<E>> = assembly
        .static_table_mapping
        .iter()
        .map(|(k, v)| (k.clone(), v.opened.clone().unwrap())) //safe to unwrap since this is checked in register_static_table method
        .collect();

    Ok(ProvingKey {
        vk,
        l0,
        l_last,
        l_active_row,
        fixed_values: fixed,
        fixed_polys,
        fixed_cosets,
        permutation: permutation_pk,
        ev,
        static_table_mapping,
        static_table_configs,
        b0_g1_bound,
    })
}
