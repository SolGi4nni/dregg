//! **THE OUTCOME→CELL-FIELD WELD BITES — driven through the deployed app-root fold node.**
//!
//! The named residual of the Braid was: nothing in-circuit forced a composed entity's committed
//! outcome field to equal the sub-proof's published `outcome_commitment` — "the host wrote both".
//! This crate closes it by ADOPTING the deployed app-root atom (the same in-circuit tie the
//! multiway-tug win-proof ships): the outcome rides the entity cell's native `fields[0..8]` octet,
//! the binding is declared, and the fold routes through
//! `prove_custom_binding_node_app_root_segmented`.
//!
//! THE CANARY (this test): an HONEST composition — whose committed octet equals its published
//! outcome — FOLDS (the node produces a root; the property is light-client-visible). A FORGED one
//! — whose committed octet disagrees with the published outcome by a single lane — has NO
//! satisfying fold (UNSAT, refused). The honest pole runs FIRST, so the refusal is attributable to
//! the app-root connect and not to some unrelated breakage.
//!
//! The folds are real recursions (minutes), so this is `#[ignore]` and needs the `prove` feature:
//!   cargo test -p dregg-braid-hook --features prove --test weld_canary -- --ignored --nocapture
#![cfg(feature = "prove")]

use dregg_braid_hook::fold::{fold_composition_app_root, forged_after, honest_after};
use dregg_braid_hook::{ComposeShape, Knot, LinearTerm, Ruleset, Subject, compose_entity};

const ROLE_ACTOR: u64 = 101;
const ROLE_PARTNER: u64 = 202;

fn shape() -> ComposeShape {
    ComposeShape::new(3, 4, 3, 2)
}

fn actor() -> Subject {
    Subject {
        identity: 7,
        role: ROLE_ACTOR,
        params: vec![2, 5, 0, 0],
    }
}

fn partner() -> Subject {
    Subject {
        identity: 9,
        role: ROLE_PARTNER,
        params: vec![3, 4, 0, 0],
    }
}

/// A law with one LINEAR term and one nonlinear KNOT: `outcome = 10*p_actor[0] + (-2)*p_actor[1]*p_partner[1]`.
fn ruleset() -> Ruleset {
    Ruleset {
        id: 0xAB,
        version: 1,
        linear: vec![LinearTerm {
            role: ROLE_ACTOR,
            param: 0,
            coeff: 10,
        }],
        knots: vec![Knot {
            role_a: ROLE_ACTOR,
            param_a: 1,
            role_b: ROLE_PARTNER,
            param_b: 1,
            coeff: -2,
        }],
    }
}

/// **THE WELD CANARY.** An honest composed entity folds through the deployed app-root node; a
/// composed entity whose committed outcome field disagrees with its published outcome is refused.
#[test]
#[ignore = "SLOW: real deployed app-root weld recursion folds (~minutes each); run with --ignored"]
fn braid_outcome_weld_bites() {
    let (entity, landed) = compose_entity(1, 1_000, actor(), &[partner()], ruleset(), shape(), 4)
        .expect("the entity composes through the Braid");
    assert_eq!(
        landed.outcome, -20,
        "10*2 + (-2)*5*4 = -20 (the licensed outcome)"
    );
    assert!(
        landed.harness_verify_outcome_welded(),
        "sanity: the post cell's native octet carries the published outcome_commitment"
    );

    // S1 — THE HONEST POLE FIRST. The forged chain below differs only in one committed field lane,
    // so without an accept here the refusal proves nothing.
    fold_composition_app_root(&entity.cell, &honest_after(&landed), &landed, 2).expect(
        "an HONEST composition (committed octet == published outcome) must FOLD through the \
         deployed app-root node",
    );
    eprintln!("BRAID WELD: honest composition FOLDED through the app-root node (outcome welded).");

    // THE BITE — a composed entity whose committed outcome field (native slot 0, +1) disagrees
    // with the sub-proof's published outcome. The app-root connect conflicts ⇒ UNSAT ⇒ refused.
    let err = fold_composition_app_root(&entity.cell, &forged_after(&landed, 0), &landed, 2)
        .expect_err(
            "a composed entity whose committed outcome field does NOT match the published outcome \
             must be REFUSED by the app-root weld",
        );
    assert!(
        err.contains("app-root fold refused"),
        "the refusal must come from the app-root fold node (the weld), got: {err}"
    );
    eprintln!("BRAID WELD: forged outcome REFUSED by the app-root fold connect: {err}");
}
