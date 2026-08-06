//! # The emit-from-Lean EQUALITY GATE — the note-spend recursion leaf.
//!
//! Validates the `emit-from-Lean` pattern on the `note_spending` family: the descriptor whose
//! constraint SEMANTICS are now authored in `metatheory/Dregg2/Circuit/Emit/NoteSpendingLeafEmit.lean`
//! (`noteSpendLeafDesc`) and byte-pinned there (`emitVmJson2` `#guard`). This test READS those EXACT
//! bytes ([`GOLDEN_JSON`]) and:
//!
//!   1. DECODES it via [`parse_vm_descriptor2`] and asserts the decode EQUALS the PRODUCTION Rust
//!      lowering [`note_spend_to_descriptor2`] — the independently-built descriptor `circuit-prove`
//!      ships. A byte drift on either side breaks this OR the Lean `#guard`. (Every constraint the
//!      hand AIR enforces — the 7-site full-width commitment chain, the two-step nullifier, position
//!      validity, the position-aware Merkle membership + chain continuity, the boundary pins, and the
//!      in-AIR mint-hash recompute — is carried; this asserts the Lean emit reproduces them ALL.)
//!   2. proves an HONEST note-spend witness (real spending key + 28-limb commitment + Merkle path)
//!      through the REAL [`prove_vm_descriptor2`], asserts ACCEPT, and re-verifies with
//!      [`verify_vm_descriptor2`];
//!   3. the MUTATION CANARY — a forged nullifier / merkle-root / mint-hash public input, and a
//!      tampered Merkle co-path in the trace, each asserts the prove-or-verify REFUSES (real UNSAT),
//!      biting a specific descriptor tooth (PiBinding pins and the C6 Poseidon2 membership lookup).
//!
//! The canaries are NON-VACUOUS: the honest witness proves (step 2) and each negative first re-asserts
//! that the honest statement is ACCEPTED before asserting the tampered one is REFUSED.
//!
//! Prove-THEN-verify is the faithful gate: `prove_vm_descriptor2` self-verifies only under
//! `cfg!(debug_assertions)` (`descriptor_ir2.rs`), so in a `--release` run the eager replay alone does
//! not check the first-row `PiBinding` against the public inputs — the CONSUMER's
//! `verify_vm_descriptor2` is the real check (the production posture).

use std::panic::AssertUnwindSafe;

use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, MemBoundaryWitness, TID_P2, VmConstraint2, parse_vm_descriptor2,
    prove_vm_descriptor2, verify_vm_descriptor2,
};
use dregg_circuit::dsl::note_spending::generate_note_spending_trace;
use dregg_circuit::field::BabyBear;
use dregg_circuit::lean_descriptor_air::VmConstraint;
use dregg_circuit::note_spending_witness::{
    NOTE_SPENDING_WIDTH, NoteSpendingWitness, merkle_col, pi, test_spending_key,
};
use dregg_circuit::poseidon2::{hash_fact, hash_many};
use dregg_circuit::refusal::{Outcome, classify};
use dregg_circuit_prove::note_spend_leaf_adapter::{
    note_spend_leaf_public_inputs, note_spend_to_descriptor2,
};

/// The BYTE-IDENTICAL wire string `emitVmJson2 noteSpendLeafDesc` emits (pinned by the `#guard` in
/// `NoteSpendingLeafEmit.lean`). If Lean's emitter drifts, that `#guard` fails; if this literal
/// drifts, the `decoded == note_spend_to_descriptor2()` assertion fails. Neither can silently diverge.
/// ⚑ **THE EMITTED ARTIFACT ITSELF, NOT A COPY OF IT (2026-08-06).** This was an inline
/// `r#"…"#` transcription of the Lean `#guard` bytes, and the `challenges` flag day
/// (2026-08-05) broke it along with 27 siblings: the artifact under
/// `circuit/descriptors/` was re-emitted, the literal was not, and
/// `parse_vm_descriptor2` refused it with `ir:2 descriptor missing "challenges"`. An
/// inline golden is a copy that no re-emit reaches, so every flag day breaks exactly
/// that set again — the fix is to have no copy. `check-emit-gate-weld.py` still gates
/// the literals that remain (the descriptors with no checked-in artifact to name), and
/// `check-descriptor-drift.sh` gates this file against its Lean author.
const GOLDEN_JSON: &str = include_str!("../../circuit/descriptors/by-name/note-spend-leaf.json");

// Mint-extension columns (from `note_spend_leaf_adapter`): the 3 columns appended past the source
// width, then the per-site chip lanes.
const MINT_ROOT_COL: usize = NOTE_SPENDING_WIDTH; // 62
const MINT_M1_COL: usize = NOTE_SPENDING_WIDTH + 1; // 63
const MINT_HASH_COL: usize = NOTE_SPENDING_WIDTH + 2; // 64
const EXT_BASE_WIDTH: usize = NOTE_SPENDING_WIDTH + 3; // 65

/// A REAL full-width witness (raw 32-byte fields + a > 2^30 u64 value so the high limb is live).
/// Depth 2 → 4 trace rows (1 commitment + 2 Merkle + 1 pad), the deployed DSL circuit's own shape.
/// Byte-identical to `note_spend_leaf_adapter`'s `make_witness`.
fn make_witness(tag: u8) -> NoteSpendingWitness {
    let owner = [tag; 32];
    let nonce = [tag ^ 0x5A; 32];
    let rand = [tag ^ 0xA5; 32];
    let key = test_spending_key(tag as u32 + 0x77);
    let depth = 2;
    let mut siblings = Vec::with_capacity(depth);
    let mut positions = Vec::with_capacity(depth);
    for i in 0..depth {
        siblings.push([
            hash_many(&[BabyBear::new((i * 3 + 1) as u32), BabyBear::new(tag as u32)]),
            hash_many(&[BabyBear::new((i * 3 + 2) as u32), BabyBear::new(tag as u32)]),
            hash_many(&[BabyBear::new((i * 3 + 3) as u32), BabyBear::new(tag as u32)]),
        ]);
        positions.push((i % 4) as u8);
    }
    NoteSpendingWitness::from_note_limbs(
        &owner,
        0xDEAD_BEEF_CAFE, // > 2^30: the value_hi limb is live
        3,
        &nonce,
        &rand,
        key,
        siblings,
        positions,
    )
}

/// The HONEST base trace (source trace + the 3 mint columns filled on row 0) and its 7-slot claim
/// tuple — a faithful reconstruction of `note_spend_leaf_adapter::note_spend_leaf_base_trace` from
/// PUBLIC APIs. The chip lane columns (65..149) are left to the prover's `trace_with_chip_lanes`.
fn honest_base_trace(w: &NoteSpendingWitness) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    let (mut trace, pis) = generate_note_spending_trace(w);
    for row in &mut trace {
        row.resize(EXT_BASE_WIDTH, BabyBear::ZERO);
    }
    let m1 = hash_fact(
        pis[pi::NULLIFIER],
        &[
            pis[pi::MERKLE_ROOT],
            pis[pi::DESTINATION_FEDERATION],
            pis[pi::ASSET_TYPE],
        ],
    );
    let mint = hash_fact(m1, &[pis[pi::VALUE], pis[pi::VALUE_HI]]);
    trace[0][MINT_ROOT_COL] = pis[pi::MERKLE_ROOT];
    trace[0][MINT_M1_COL] = m1;
    trace[0][MINT_HASH_COL] = mint;

    let full_pis = note_spend_leaf_public_inputs(w);
    assert_eq!(
        full_pis[pi::VALUE_HI + 1],
        mint,
        "the mint identity is the appended 7th PI slot"
    );
    (trace, full_pis)
}

/// `true` iff this `(trace, pis)` is REJECTED end-to-end — proving refuses OR the produced proof
/// fails to VERIFY against `pis`. `false` iff it both proves AND verifies (an accepted spend).
fn rejects(desc: &EffectVmDescriptor2, trace: &[Vec<BabyBear>], pis: &[BabyBear]) -> bool {
    match classify("rejects", || {
        let proof = prove_vm_descriptor2(desc, trace, pis, &MemBoundaryWitness::default(), &[])?;
        verify_vm_descriptor2(desc, &proof, pis)
    }) {
        // The p3 debug prover's DOCUMENTED unsat verdict — a real refusal.
        // `classify` REDs on any other panic (a stray unwrap, a trace-assembly
        // debug_assert), which used to land here and read as "rejected".
        Outcome::UnsatPanic(_) => true,
        Outcome::Err(_) => true,
        Outcome::Accepted(_) => false,
    }
}

/// STEP 1 — the Lean-emitted descriptor decodes and EQUALS the production `note_spend_to_descriptor2`
/// lowering (Lean emit ≡ Rust semantics), with the expected shape.
#[test]
fn note_spend_emit_decodes_to_production_lowering() {
    let decoded = parse_vm_descriptor2(GOLDEN_JSON).expect("the Lean-emitted golden JSON decodes");
    let production =
        note_spend_to_descriptor2().expect("the production note-spend lowering builds");
    assert_eq!(
        decoded, production,
        "the Lean-emitted descriptor must equal the production note_spend_to_descriptor2() lowering"
    );

    // Shape pins (mirror the Lean `#guard`s): width 149, 7 PIs, 12 chip lookups, 8 pins, 1 window.
    assert_eq!(decoded.trace_width, 149);
    assert_eq!(decoded.public_input_count, 7);
    let chip_lookups = decoded
        .constraints
        .iter()
        .filter(|c| matches!(c, VmConstraint2::Lookup(l) if l.table == TID_P2))
        .count();
    assert_eq!(
        chip_lookups, 12,
        "7 commitment-chain + 2 nullifier + 1 Merkle + 2 mint fact sites"
    );
    let pins = decoded
        .constraints
        .iter()
        .filter(|c| matches!(c, VmConstraint2::Base(VmConstraint::PiBinding { .. })))
        .count();
    assert_eq!(pins, 8, "6 source boundary pins + MINT_ROOT + MINT_HASH");
    let windows = decoded
        .constraints
        .iter()
        .filter(|c| matches!(c, VmConstraint2::WindowGate(_)))
        .count();
    assert_eq!(windows, 1, "the C7 Merkle-chain continuity");
}

/// STEP 2 — THE POSITIVE POLE: an honest note-spend witness proves through the emitted descriptor
/// and re-verifies against its 7-slot claim tuple.
#[test]
fn honest_note_spend_proves_and_verifies() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    let w = make_witness(0x10);
    let (trace, pis) = honest_base_trace(&w);
    let proof = prove_vm_descriptor2(&desc, &trace, &pis, &MemBoundaryWitness::default(), &[])
        .expect("the honest note-spend witness must prove through the emitted descriptor");
    verify_vm_descriptor2(&desc, &proof, &pis)
        .expect("the honest proof must re-verify against the claim tuple");
}

/// STEP 3a — MUTATION CANARY (nullifier PI): a forged nullifier slot. The boundary pin
/// `PiBinding{First, col::NULLIFIER, pi0}` is violated → UNSAT. The nullifier is bound to the spend.
#[test]
fn forged_nullifier_pi_refuses() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    let w = make_witness(0x21);
    let (trace, pis) = honest_base_trace(&w);
    assert!(
        !rejects(&desc, &trace, &pis),
        "honest witness must be accepted — else the canary is vacuous"
    );
    let mut forged = pis.clone();
    forged[pi::NULLIFIER] += BabyBear::ONE;
    assert!(
        rejects(&desc, &trace, &forged),
        "a forged nullifier PI must be REJECTED (nullifier binding tooth)"
    );
}

/// STEP 3b — MUTATION CANARY (merkle-root PI): a forged root slot. The last-row root pin
/// `PiBinding{Last, CURRENT, pi1}` (and the MINT_ROOT pin at pi1) is violated → UNSAT.
#[test]
fn forged_merkle_root_pi_refuses() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    let w = make_witness(0x32);
    let (trace, pis) = honest_base_trace(&w);
    assert!(
        !rejects(&desc, &trace, &pis),
        "non-vacuity: honest accepted"
    );
    let mut forged = pis.clone();
    forged[pi::MERKLE_ROOT] += BabyBear::ONE;
    assert!(
        rejects(&desc, &trace, &forged),
        "a forged merkle-root PI must be REJECTED (membership root binding)"
    );
}

/// STEP 3c — MUTATION CANARY (mint-hash PI): a forged mint identity slot. The pin
/// `PiBinding{First, MINT_HASH_COL, pi6}` over the in-AIR-recomputed identity is violated → UNSAT.
#[test]
fn forged_mint_hash_pi_refuses() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    let w = make_witness(0x43);
    let (trace, pis) = honest_base_trace(&w);
    assert!(
        !rejects(&desc, &trace, &pis),
        "non-vacuity: honest accepted"
    );
    let mut forged = pis.clone();
    let mint_pi = pi::VALUE_HI + 1; // the appended 7th slot
    forged[mint_pi] += BabyBear::ONE;
    assert!(
        rejects(&desc, &trace, &forged),
        "a forged mint-hash PI must be REJECTED (mint identity weld tooth)"
    );
}

/// STEP 3d — MUTATION CANARY (Merkle co-path): a tampered sibling on a Merkle row, claim tuple
/// honest. The C6 `Poseidon2Chip` membership lookup names a parent digest no genuine permutation of
/// the tampered inputs serves → UNSAT. A forged co-path is refused (the membership tooth).
#[test]
fn tampered_merkle_sibling_refuses() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    let w = make_witness(0x54);
    let (mut trace, pis) = honest_base_trace(&w);
    assert!(
        !rejects(&desc, &trace, &pis),
        "non-vacuity: honest accepted"
    );
    // Row 1 is the first Merkle row (is_merkle = 1). Tamper its SIB0 without recomputing PARENT:
    // the C6 lookup's out0 (PARENT) no longer matches the genuine hash of the tampered inputs.
    trace[1][merkle_col::SIB0] += BabyBear::ONE;
    assert!(
        rejects(&desc, &trace, &pis),
        "a forged Merkle sibling (wrong co-path) must be REJECTED (C6 chip membership lookup)"
    );
}
