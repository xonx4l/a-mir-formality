use crate::grammar::{
    Crate, Fallible, NegTraitImpl, NegTraitImplBoundData, TraitImpl, TraitImplBoundData, Wc, Wcs,
};
use crate::prove::prove::{Env, Program};
use anyhow::bail;
use formality_core::{
    judgment::{FailedJudgment, ProofTree},
    judgment_fn, Downcasted,
};
use itertools::Itertools;

/// Converts a failed orphan judgment into anyhow for check_coherence's Fallible result.
fn map_failed_judgment(e: Box<FailedJudgment>) -> anyhow::Error {
    anyhow::Error::from(*e)
}

pub(crate) fn check_coherence(program: &Program, current_crate: &Crate) -> Fallible<ProofTree> {
    let current_crate_impls: Vec<TraitImpl> = current_crate.items.iter().downcasted().collect();

    // Reject duplicate impls in this crate otherwise the overlap cartesian product would treat
    // an impl as overlapping with itself.
    for (impl_a, i) in current_crate_impls.iter().zip(0..) {
        if current_crate_impls[i + 1..].contains(impl_a) {
            bail!("duplicate impl in current crate: {:?}", impl_a);
        }
    }

    let orphan_tree = check_coherence_orphans_judgment(program.clone(), current_crate.clone())
        .check_proven()
        .map_err(map_failed_judgment)?;

    // Each current-crate impl vs every impl in the program overlap.
    let all_crate_impls = all_trait_impls(program);
    let mut children = vec![orphan_tree];
    for pair in overlap_pairs(&current_crate_impls, &all_crate_impls) {
        children.push(overlap_check_impl(
            program.clone(),
            pair.0.clone(),
            pair.1.clone(),
        )?);
    }

    Ok(ProofTree::new(
        format!("check_coherence({:?})", current_crate.id),
        None,
        children,
    ))
}

judgment_fn! {
    fn check_coherence_orphans_judgment(program: Program, current_crate: Crate) => () {
        debug(program, current_crate)

        (
            (let current_crate_impls: Vec<TraitImpl> = current_crate.items.iter().downcasted().collect())
            (let current_crate_neg_impls: Vec<NegTraitImpl> = current_crate.items.iter().downcasted().collect())
            (for_all(impl_a in current_crate_impls.iter().cloned())
                (orphan_check(program, impl_a) => ()))
            (for_all(impl_a in current_crate_neg_impls.iter().cloned())
                (orphan_check_neg(program, impl_a) => ()))
            --- ("check_coherence_orphans")
            (check_coherence_orphans_judgment(program, current_crate) => ())
        )
    }
}

// Orphan rule (RFC 2451): prove the trait ref is local under the impl's where-clauses.
judgment_fn! {
    fn orphan_check(program: Program, impl_a: TraitImpl) => () {
        debug(program, impl_a)

        (
            (let (env, a) = open_trait_impl(&impl_a))
            (let trait_ref = a.trait_ref())
            (super::prove_goal(program, env, &a.where_clauses, trait_ref.is_local()) => ())
            --- ("orphan_check")
            (orphan_check(program, impl_a) => ())
        )
    }
}

judgment_fn! {
    fn orphan_check_neg(program: Program, impl_a: NegTraitImpl) => () {
        debug(program, impl_a)

        (
            (let (env, a) = open_neg_trait_impl(&impl_a))
            (let trait_ref = a.trait_ref())
            (super::prove_goal(program, env, &a.where_clauses, trait_ref.is_local()) => ())
            --- ("orphan_check_neg")
            (orphan_check_neg(program, impl_a) => ())
        )
    }
}

/// Two impls of the same trait prove they do not overlap or report impls may overlap.
#[tracing::instrument(level = "Debug", skip(program, impl_a, impl_b))]
fn overlap_check_impl(
    program: Program,
    impl_a: TraitImpl,
    impl_b: TraitImpl,
) -> Fallible<ProofTree> {
    let program = &program;
    let mut env = Env::default();

    // ∀P_a, ∀P_b — e.g. impl<P_a..> Tr<T_a…> for T_a0 where Wc_a vs same for b.
    let a = env.instantiate_universally(&impl_a.binder);
    let b = env.instantiate_universally(&impl_b.binder);

    let trait_ref_a = a.trait_ref();
    let trait_ref_b = b.trait_ref();

    assert_eq!(trait_ref_a.trait_id, trait_ref_b.trait_id);

    // ∀P_a, ∀P_b. ¬(coherence_mode => (Ts_a = Ts_b ∧ Wc_a ∧ Wc_b)) — then no overlap.
    if let Ok(proof_tree) = super::prove_not_goal(
        program,
        &env,
        (),
        (
            Wcs::all_eq(&trait_ref_a.parameters, &trait_ref_b.parameters),
            &a.where_clauses,
            &b.where_clauses,
        ),
    ) {
        tracing::debug!(
            "proved not {:?}",
            (
                Wcs::all_eq(&trait_ref_a.parameters, &trait_ref_b.parameters),
                &a.where_clauses,
                &b.where_clauses,
            )
        );

        return Ok(ProofTree::new(
            "overlap_check",
            Some("not_goal"),
            vec![proof_tree],
        ));
    }

    // try inverted where-clauses from Wc_a / Wc_b (e.g. T: Debug => T: !Debug).
    // If (equal params ∧ Wc_a ∧ Wc_b) => Wc_i is provable the two impls cannot both apply.
    let inverted: Vec<Wc> = a
        .where_clauses
        .iter()
        .chain(&b.where_clauses)
        .flat_map(|wc| wc.invert())
        .collect();

    if let Some(inverted_wc) = inverted.iter().find(|inverted_wc| {
        super::prove_goal(
            program,
            &env,
            (
                Wcs::all_eq(&trait_ref_a.parameters, &trait_ref_b.parameters),
                &a.where_clauses,
                &b.where_clauses,
            ),
            inverted_wc,
        )
        .is_ok()
    }) {
        tracing::debug!(
            "proved {:?} assuming {:?}",
            inverted_wc,
            (
                Wcs::all_eq(&trait_ref_a.parameters, &trait_ref_b.parameters),
                &a.where_clauses,
                &b.where_clauses,
            )
        );

        return Ok(ProofTree::new("overlap_check", Some("inverted"), vec![]));
    }

    bail!("impls may overlap:\n{impl_a:?}\n{impl_b:?}")
}

/// Binder opening via universal_substitution so judgment rules need not use &mut Env.
fn open_trait_impl(impl_a: &TraitImpl) -> (Env, TraitImplBoundData) {
    let (env, subst) = Env::default().universal_substitution(&impl_a.binder);
    let a = impl_a.binder.instantiate_with(&subst).unwrap();
    (env, a)
}

/// Same pattern as open_trait_impl for negative impls.
fn open_neg_trait_impl(impl_a: &NegTraitImpl) -> (Env, NegTraitImplBoundData) {
    let (env, subst) = Env::default().universal_substitution(&impl_a.binder);
    let a = impl_a.binder.instantiate_with(&subst).unwrap();
    (env, a)
}

/// All TraitImpl`s visible across crates.
fn all_trait_impls(program: &Program) -> Vec<TraitImpl> {
    program
        .program()
        .items_from_all_crates()
        .downcasted()
        .collect()
}

/// Pairs with the same trait and distinct impls.
fn overlap_pairs(
    current_crate_impls: &[TraitImpl],
    all_crate_impls: &[TraitImpl],
) -> Vec<(TraitImpl, TraitImpl)> {
    current_crate_impls
        .iter()
        .cartesian_product(all_crate_impls)
        .filter(|(impl_a, impl_b)| impl_a != impl_b)
        .filter(|(impl_a, impl_b)| impl_a.trait_id() == impl_b.trait_id())
        .map(|(impl_a, impl_b)| (impl_a.clone(), impl_b.clone()))
        .collect()
}
