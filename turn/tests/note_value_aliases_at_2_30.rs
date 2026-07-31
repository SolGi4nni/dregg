//! **A8 — the committed note value aliases at `2^30`.** The constructed exhibit,
//! measured at the CONSENSUS ANCHOR rather than at a helper.
//!
//! The mechanism, verified at source:
//!
//! * `circuit/src/effect_vm/helpers.rs` `split_u64` masks the low limb to 30 bits;
//! * `cell/src/commitment_set.rs` / `cell/src/nullifier_set.rs` `accumulator_leaf`
//!   commits `split_u64(value).0` ALONE — `param::NOTE_VALUE_HI` is written by
//!   `circuit/src/effect_vm/trace.rs:742,752` and read by nothing;
//! * `turn/src/executor/mod.rs::consensus_state_commitment` folds those accumulator
//!   `root8()`s into the value stamped into `TurnReceipt::{pre,post}_state_hash` —
//!   which the executor signs, the federation receipt QC certifies, and the
//!   `AttestedRoot` quorum transitively covers.
//!
//! So a `2^30` shift in a recorded note value is invisible all the way up to the
//! signed anchor. This file constructs that, states which side refuses it and
//! which does not, and pins the anti-cap pole: a legal LARGE value still works.
//!
//! The Lean tooth for the same shape is `metatheory/Dregg2/Bignum/LedgerBalance.lean`
//! `accumulatorLeaf_aliases_at_2_30`.
//!
//! ═══ ⚑ WHY THIS TOOTH IS STILL DOCUMENTING AND NOT YET ASSERTING A REPAIR ════════
//! The sibling wound at `fields[0..7]` (`turn/tests/fields_octet_aliases_at_the_anchor.rs`) was
//! closed in a Rust helper with no descriptor, VK or Lean consequence, and the plan that closed it
//! proposed the same move here: route `accumulator_leaf` onto the injective
//! `commitment_set::exact_commitment_leaf8`. **That is not available, and the deployed descriptors
//! say so rather than a doc comment.** Measured 2026-07-30 over all four rotation registries:
//!
//! ```text
//!   noteSpendVmDescriptor2R24   map_op aafi_insert  key={"var":68}  value={"var":69}
//!   noteCreateVmDescriptor2R24  map_op aafi_insert  key={"var":68}  value={"var":69}
//! ```
//!
//! Column 68 is `PARAM_BASE + param::NULLIFIER` (`= param::NOTE_COMMITMENT` on the create side) and
//! column 69 is `PARAM_BASE + param::NOTE_VALUE_LO`. The leaf's ADDRESS and its VALUE are each ONE
//! trace column, bound BY CONSTRAINT, in all three deployed registries — and the IR types them that
//! way at the source: `Dregg2/Circuit/DescriptorIR2.lean` gives `MapOp` a `root, newRoot : Fin 8 →
//! EmittedExpr` but `key : EmittedExpr`, a single expression. An eight-felt exact leaf is not
//! REPRESENTABLE in the deployed map-op, so swapping the Rust leaf would make the executor-derived
//! accumulator root disagree with the `CanonicalHeapTree8` the grow-gate opens against, and every
//! noteSpend / noteCreate turn would go UNSAT.
//!
//! So A2 (the address) and A3 (the value) are **not** the same class of repair as the fields octet.
//! Closing them is a Lean AIR change — followed by a descriptor re-emit and a VK rotation.
//! `circuit/src/effect_vm/trace_rotated.rs` registers the address half as felt-width wound site #20
//! and reaches the same conclusion independently.
//!
//! ⚑ **TWO OF THE THREE BLOCKERS THIS COMMENT NAMED ARE GONE, AND THE PRESCRIPTION WAS WRONG.**
//! Re-measured 2026-07-31:
//!
//! 1. **The PROVENANCE blocker is CLEARED.** `circuit/descriptors/PROVENANCE.json` now reads
//!    `"source_dirty": false`, and all 75 `descriptor_sha256` pins rehash byte-exact against the
//!    files on disk (0 drift). Nothing riding the emit pipeline inherits drift any more.
//!
//! 2. **The fields-octet sibling is no longer a Rust-helper repair with no Lean consequence.** It
//!    is now `metatheory/Dregg2/Circuit/FieldLanes9.lean` — `fieldToLanes9_injective`, a genuine
//!    INJECTION with a total decoder and a machine-checked left inverse — and it cost the geometry
//!    flag day `rotatedNumPreLimbs` 178 -> 184 (`B_SPAN` 239 -> 247), because eight lanes cannot be
//!    injective at all (`nine_lanes_is_the_minimum : P^8 < 2^256 <= P^9`). The precedent for A2/A3
//!    is therefore "pay the flag day", not "swap a helper".
//!
//! 3. ⚠ **BUT "widen `MapOp.key`/`value` to eight felts plus lex-8 bracketing" IS NOT THE REPAIR,
//!    AND DONE LITERALLY IT IS A REGRESSION.**
//!    `Dregg2/Circuit/MapOpWideKeyGate.lean::halfWideLeaf_forges_absence_of_present` proves — for
//!    EVERY hash, with NO collision-resistance hypothesis — that widening the ADDRESS while the
//!    POINTER stays projected to lane 0 gives the honest low leaf `<keyLo, 1, keyE>` and the
//!    fabricated `<keyLo, 1, ptrHi>` the SAME digest, and the fabricated bracket then CONTAINS a key
//!    the honest chain PRESENTS: a non-membership FORGERY, strictly worse than today's aliasing.
//!    There is no width knob. The schema is the **arity-17 leaf** `addr8 || value || next8`
//!    (`imtLeafHash8`), or it is broken.
//!
//! What is actually left is narrower than this comment used to imply, and it is already built in
//! Lean: `MapOpWideKey` / `MapOpWideKeyGate` / `MapOpWideKeyCanonDischarge` /
//! `MapOpWideKeyRowBoundary` / `MapAbsentImtGateWide` carry the widened node (`MapOpW`), the
//! arity-17 leaf, the canonicity discharge (`lexLt8_refines_canon`, hypothesis-free), the row-boundary
//! weld (`absentRow_of_lexBlocks_forces_absence`) and the both-sides-must-move-together refusals
//! (`insertW_absentW_jointly_unsat`, `narrowInsert_wideOpen_double_spend`), all `#assert_axioms`-clean.
//! The residual those files name as W3/W4 is exactly two things: **register the widened node in the
//! DEPLOYED descriptor** (`DescriptorIR2.MapOp.key : EmittedExpr` -> `Fin 8 -> EmittedExpr`, and the
//! same for `value`/the pointer) and **widen the Rust chip row + decoder**. That is one epoch, and it
//! moves the insert and open sides together or it is a double spend.
//!
//! Until then the assertions below are TRUE and must stay: they are the characterization that keeps
//! the aliasing detected. `a8_the_exact_duals_separate_what_the_committed_roots_alias` is the pole
//! that shows the injective successor already exists and already separates the pair — it is simply
//! not what any consensus object commits to.

use dregg_cell::commitment_set::CommitmentSet;
use dregg_cell::note::{NoteCommitment, Nullifier};
use dregg_cell::nullifier_set::NullifierSet;
use dregg_cell::{Cell, CellId, Ledger};
use dregg_turn::state_commit::{consensus_ctx, consensus_state_commitment};

fn cell_with(seed: u8) -> Cell {
    let mut pk = [0u8; 32];
    pk[0] = seed;
    pk[31] = seed.wrapping_mul(7);
    Cell::new(pk, [seed; 32])
}

fn ledger_with(seed: u8) -> (Ledger, CellId) {
    let cell = cell_with(seed);
    let id = cell.id();
    let mut ledger = Ledger::new();
    ledger.insert_cell(cell).unwrap();
    (ledger, id)
}

/// The anchor over a ledger plus one created note recorded at `value`.
fn anchor_for_created_note(seed: u8, commitment: NoteCommitment, value: u64) -> [u8; 32] {
    let (ledger, agent) = ledger_with(seed);
    let mut commitments = CommitmentSet::new();
    commitments.insert(commitment, value).unwrap();
    let ctx = consensus_ctx(
        &ledger,
        NullifierSet::new().root8(),
        commitments.root8(),
        dregg_turn::rotation_witness::empty_revoked_root_8(),
    );
    consensus_state_commitment(&ledger, &agent, &ctx)
}

/// The anchor over a ledger plus one spent nullifier recorded at `value`.
fn anchor_for_spent_note(seed: u8, nullifier: Nullifier, value: u64) -> [u8; 32] {
    let (ledger, agent) = ledger_with(seed);
    let mut nullifiers = NullifierSet::new();
    nullifiers.insert(nullifier, value).unwrap();
    let ctx = consensus_ctx(
        &ledger,
        nullifiers.root8(),
        dregg_turn::rotation_witness::empty_commitments_root_8(),
        dregg_turn::rotation_witness::empty_revoked_root_8(),
    );
    consensus_state_commitment(&ledger, &agent, &ctx)
}

/// ⚑ **THE EXHIBIT.** Two note-create histories whose values differ by exactly
/// `2^30` — both ordinary, both far inside `u64`, neither refused anywhere —
/// produce a BYTE-IDENTICAL consensus state anchor. The signature, the receipt
/// QC and the attestation quorum therefore certify a state that cannot testify
/// to which of the two values the host actually recorded.
///
/// This test asserts the wound, deliberately: it is the CHARACTERIZATION that
/// makes the aliasing DETECTED instead of merely documented. If a future leaf
/// widening breaks it, that is the flag day landing and this assertion is the
/// thing that says so out loud.
#[test]
fn a8_two_note_values_2_30_apart_share_one_consensus_anchor() {
    let commitment = NoteCommitment([0x11; 32]);
    let low = 4_242u64;
    let aliased = low + (1u64 << 30);

    // Vacuity guard: the pair must genuinely share the deployed leaf felt, or this
    // test is measuring something other than the 2^30 alias.
    assert_eq!(
        dregg_circuit::effect_vm::split_u64(low).0,
        dregg_circuit::effect_vm::split_u64(aliased).0,
        "vacuity guard: the pair must share `split_u64(..).0`"
    );
    assert_ne!(
        dregg_circuit::effect_vm::split_u64(low).1,
        dregg_circuit::effect_vm::split_u64(aliased).1,
        "vacuity guard: the pair must DIFFER in the high limb — the column that is \
         written (`trace.rs:742,752`) and read by nothing"
    );

    let anchor_low = anchor_for_created_note(9, commitment, low);
    let anchor_aliased = anchor_for_created_note(9, commitment, aliased);

    assert_eq!(
        anchor_low, anchor_aliased,
        "A8: the signed consensus anchor is 2^30-periodic in a created note's value"
    );

    // And the anchor is not simply insensitive to note values in general — a value
    // BELOW the aliasing period does move it. Without this the test above would be
    // satisfied by an anchor that ignored the accumulator entirely.
    let anchor_other = anchor_for_created_note(9, commitment, low + 1);
    assert_ne!(
        anchor_low, anchor_other,
        "non-vacuity: the anchor DOES move for a sub-2^30 value change, so the \
         equality above is the aliasing period and not blanket insensitivity"
    );
}

/// The same shift on the SPEND side also collapses the anchor. Both accumulators
/// commit through the identical `split_u64(value).0` leaf.
#[test]
fn a8_the_spend_side_accumulator_aliases_identically() {
    let nullifier = Nullifier([0x33; 32]);
    let low = 7u64;
    let aliased = low + (1u64 << 30);

    assert_eq!(
        anchor_for_spent_note(4, nullifier, low),
        anchor_for_spent_note(4, nullifier, aliased),
        "the nullifier accumulator's committed root is 2^30-periodic too"
    );
    assert_ne!(
        anchor_for_spent_note(4, nullifier, low),
        anchor_for_spent_note(4, nullifier, low + 1),
        "non-vacuity: a sub-period change does move the anchor"
    );
}

/// ⚑ **WHAT REFUSES IT, AND WHAT DOES NOT.** The spend side has carried a
/// value-faithful dual since the FNSP-v3 work: `NullifierSet::faithful_root8_exact`
/// binds all 64 value bits, and `turn/src/executor/apply.rs:1720` compares a
/// spend proof's `successor_nullifier_root` against exactly that — so an aliased
/// spend value is REFUSED on the live admission path.
///
/// The create side had no such object at any width until the create-side dual
/// landed beside it; this pins that both now separate the pair.
#[test]
fn a8_the_exact_duals_separate_what_the_committed_roots_alias() {
    let raw = [0x5c; 32];
    let low = 17u64;
    let aliased = low + (1u64 << 30);

    let mut spend_low = NullifierSet::new();
    spend_low.insert(Nullifier(raw), low).unwrap();
    let mut spend_alias = NullifierSet::new();
    spend_alias.insert(Nullifier(raw), aliased).unwrap();
    assert_eq!(
        spend_low.root8(),
        spend_alias.root8(),
        "vacuity guard: the committed spend root aliases"
    );
    assert_ne!(
        spend_low.faithful_root8_exact(),
        spend_alias.faithful_root8_exact(),
        "the spend-side exact root binds all 64 value bits (the live FNSP-v3 check)"
    );

    let mut create_low = CommitmentSet::new();
    create_low.insert(NoteCommitment(raw), low).unwrap();
    let mut create_alias = CommitmentSet::new();
    create_alias.insert(NoteCommitment(raw), aliased).unwrap();
    assert_eq!(
        create_low.root8(),
        create_alias.root8(),
        "vacuity guard: the committed create root aliases"
    );
    assert_ne!(
        create_low.faithful_root8_exact(),
        create_alias.faithful_root8_exact(),
        "the create-side exact dual must bind all 64 value bits too"
    );
}

/// ⚑ **ANTI-CAP POLE.** The repair is a WIDENING of the testimony, not a
/// restriction of the domain: a legal LARGE note value — above `2^30`, above
/// `2^32`, and up to `u64::MAX` — is still accepted end to end, still round-trips
/// through the accumulator, and still commits distinguishably. Nothing here is
/// refused, so the aliasing was not "closed" by capping the protocol.
#[test]
fn a8_legal_large_values_still_work_and_still_separate() {
    let commitment = NoteCommitment([0x77; 32]);
    let large = [
        1u64 << 30,
        (1u64 << 30) + 1,
        1_000_000_000_000u64,
        1u64 << 40,
        1u64 << 62,
        u64::MAX,
    ];

    let mut exact_roots = Vec::new();
    for value in large {
        let mut set = CommitmentSet::new();
        set.insert(commitment, value)
            .expect("a large legal note value is still accepted by the accumulator");
        assert_eq!(
            set.value_of(&commitment),
            Some(value),
            "the FULL u64 survives the round trip — the store is not the lossy part"
        );
        exact_roots.push(set.faithful_root8_exact());
    }

    for i in 0..exact_roots.len() {
        for j in (i + 1)..exact_roots.len() {
            assert_ne!(
                exact_roots[i], exact_roots[j],
                "legal large values {} and {} must commit differently in the exact root",
                large[i], large[j]
            );
        }
    }

    // The same set of values does NOT separate under the deployed committed root:
    // 2^30 and 2^62 both fold onto the value-0 leaf. This is the measurement of
    // what the flag day has to move.
    let mut at_zero = CommitmentSet::new();
    at_zero.insert(commitment, 0).unwrap();
    for value in [1u64 << 30, 1u64 << 62] {
        let mut set = CommitmentSet::new();
        set.insert(commitment, value).unwrap();
        assert_eq!(
            at_zero.root8(),
            set.root8(),
            "the deployed committed root cannot distinguish {value} from 0"
        );
    }
}
