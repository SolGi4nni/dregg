//! Constraint-binding weld: the REQUIRED-TAG re-derivation + the omission-proof
//! round-trip at the executor altitude (`docs/deos/VK-EPOCH-CONSTRAINT-BINDING-DESIGN.md`).
//!
//! `required_capacity_caveat_tags` re-derives the capacity caveat tags a cell's
//! declared constraint-set REQUIRES. ⚠ There is NO concrete Lean counterpart:
//! `Dregg2/Deos/ConstraintBinding.lean` takes `requiredTags : Decl → List Tag` as an
//! ABSTRACT parameter and proves only the binding floor (`DeclCommitBinds`) over it —
//! the concrete tag derivation exists ONLY in this Rust. This test pins the mapping and
//! closes the omission-proof loop: the SAME declaration both PROJECTS its manifest
//! entry (`project_slot_caveat_manifest`) AND yields its required tag, and coverage
//! (`verify_slot_caveat_coverage`) accepts the honest projection but rejects a turn
//! that drops the entry.

use dregg_cell::program::StateConstraint;
use dregg_circuit::effect_vm::pi;
use dregg_circuit::effect_vm::{verify_slot_caveat_coverage, verify_slot_caveat_manifest};
use dregg_circuit::field::BabyBear;
use dregg_turn::executor::{project_slot_caveat_manifest, required_capacity_caveat_tags};

fn pi_from_projection(constraints: &[StateConstraint]) -> Vec<BabyBear> {
    let (count, entries) = project_slot_caveat_manifest(constraints);
    let mut public_inputs = vec![BabyBear::ZERO; pi::ACTIVE_BASE_COUNT];
    public_inputs[pi::SLOT_CAVEAT_COUNT] = BabyBear::new(count);
    for (i, entry) in entries.iter().enumerate().take(count as usize) {
        let base = pi::SLOT_CAVEAT_MANIFEST_BASE + i * pi::SLOT_CAVEAT_ENTRY_SIZE;
        entry.write_to(&mut public_inputs[base..base + pi::SLOT_CAVEAT_ENTRY_SIZE]);
    }
    public_inputs
}

#[test]
fn re_derivation_maps_each_capacity_to_its_tag() {
    assert_eq!(
        required_capacity_caveat_tags(&[StateConstraint::SettleEscrow {
            leg_a_index: 3,
            leg_b_index: 4
        }]),
        vec![pi::SLOT_CAVEAT_TAG_SETTLE_ESCROW]
    );
    assert_eq!(
        required_capacity_caveat_tags(&[StateConstraint::DischargeObligation {
            cursor_slot: 1,
            due_slot: 2,
            amount_slot: 3,
            period: 10,
            amount: 5
        }]),
        vec![pi::SLOT_CAVEAT_TAG_DISCHARGE_OBLIGATION]
    );
    assert_eq!(
        required_capacity_caveat_tags(&[StateConstraint::VaultDeposit {
            assets_slot: 0,
            shares_slot: 1
        }]),
        vec![pi::SLOT_CAVEAT_TAG_VAULT_DEPOSIT]
    );
}

#[test]
fn non_capacity_constraints_require_nothing() {
    // Per-slot caveats are independently re-evaluated when present; they impose no
    // coverage floor (no omission attack — a missing per-slot caveat just isn't bound).
    let tags = required_capacity_caveat_tags(&[
        StateConstraint::Monotonic { index: 0 },
        StateConstraint::WriteOnce { index: 1 },
    ]);
    assert!(tags.is_empty());
}

#[test]
fn declaration_dedups_required_tags() {
    let tags = required_capacity_caveat_tags(&[
        StateConstraint::SettleEscrow {
            leg_a_index: 3,
            leg_b_index: 4,
        },
        StateConstraint::SettleEscrow {
            leg_a_index: 5,
            leg_b_index: 6,
        },
    ]);
    assert_eq!(tags, vec![pi::SLOT_CAVEAT_TAG_SETTLE_ESCROW]);
}

#[test]
fn omission_proof_round_trip() {
    let declaration = [StateConstraint::SettleEscrow {
        leg_a_index: 3,
        leg_b_index: 4,
    }];
    let required = required_capacity_caveat_tags(&declaration);

    // HONEST: the declaration's projection covers its own required tag, and the
    // atomic settle satisfies the gate.
    let honest_pi = pi_from_projection(&declaration);
    let mut before = [BabyBear::ZERO; 8];
    let mut after = [BabyBear::ZERO; 8];
    before[3] = BabyBear::new(pi::SETTLE_ESCROW_STATUS_DEPOSITED);
    before[4] = BabyBear::new(pi::SETTLE_ESCROW_STATUS_DEPOSITED);
    after[3] = BabyBear::new(pi::SETTLE_ESCROW_STATUS_CONSUMED);
    after[4] = BabyBear::new(pi::SETTLE_ESCROW_STATUS_CONSUMED);
    assert!(verify_slot_caveat_coverage(&honest_pi, &required).is_ok());
    assert!(verify_slot_caveat_manifest(&honest_pi, &before, &after, 0).is_ok());

    // FORGED OMISSION: the prover publishes an EMPTY manifest while the COMMITTED
    // declaration still requires the escrow tag. Coverage (re-derived from the
    // committed declaration, not the prover manifest) catches it.
    let forged_pi = pi_from_projection(&[]);
    assert!(
        verify_slot_caveat_coverage(&forged_pi, &required).is_err(),
        "a turn whose COMMITTED declaration requires SettleEscrow but whose manifest omits it \
         MUST be rejected — omission caught, not prover-optional"
    );
}
