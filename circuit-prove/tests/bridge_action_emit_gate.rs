//! # The emit-from-Lean EQUALITY GATE — the bridge-action BINDING leaf (table-free).
//!
//! The descriptor is AUTHORED in Lean (`metatheory/Dregg2/Circuit/Emit/BridgeActionEmit.lean`,
//! `bridgeActionDesc`) and its wire string is byte-pinned there (`emitVmJson2` `#guard`). This
//! test READS those EXACT bytes ([`GOLDEN_JSON`]) and:
//!
//!   1. DECODES it via [`parse_vm_descriptor2`] and asserts the decode equals BOTH an independently
//!      hand-built [`EffectVmDescriptor2`] (term-for-term) AND the already-proven Rust builder
//!      [`bridge_action_to_descriptor2`] (`circuit-prove/src/bridge_leaf_adapter.rs`, proven
//!      total/always-`Ok`, folded through `prove_vm_descriptor2_for_config`). A byte drift on any
//!      side breaks this OR the Lean `#guard`;
//!   2. proves an HONEST 26-slot bridge-action witness (the same `BridgeActionAir::generate_trace`
//!      the hand AIR uses: one typed row replicated for FRI power-of-2 padding) through the REAL
//!      [`prove_vm_descriptor2`], asserts ACCEPT, and re-verifies the proof;
//!   3. the MUTATION CANARY — two teeth, isolated:
//!        * a FORGED public input (one nullifier limb flipped, and a swapped nullifier/recipient)
//!          violates the first-row `PiBinding{First}` boundary tooth → UNSAT;
//!        * a BROKEN-CONTINUITY padding row (one column of a padding row perturbed, row 0 and the
//!          PIs left honest) violates the `WindowGate{on_transition}` "every column constant across
//!          rows" tooth → UNSAT.
//!
//! The two families the hand AIR (`circuit/src/bridge_action_witness.rs`) enforces — 26 boundary pins
//! (`boundary_constraints`) and 26 column-constancy transitions (`eval_constraints`) — are the
//! whole binding: there is NO range decomposition, NO in-AIR hashing, and NO verifier-wrapper tooth
//! to preserve (the felts are bound directly). Each canary is NON-VACUOUS: it asserts the honest
//! witness ACCEPTS (step 2) before asserting the tamper REJECTS.
//!
//! Scope: `BridgeActionAir` is a BINDING-ONLY shadow AIR; it does NOT re-prove the underlying
//! note-spend (that is `note_spending`'s job, and the sound deployed backing is the note-spend leaf
//! folded to the published `mint_hash`). This gate certifies the emit-from-Lean law migration of
//! that binding shadow, not a soundness change to the deployed bridge.

use std::panic::AssertUnwindSafe;

use dregg_circuit::bridge_action_witness::{
    BRIDGE_ACTION_PI_COUNT, BRIDGE_ACTION_WIDTH, BridgeActionAir, BridgeActionWitness,
};
use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, MemBoundaryWitness, VmConstraint2, WindowExpr, WindowGateSpec,
    parse_vm_descriptor2, prove_vm_descriptor2, verify_vm_descriptor2,
};
use dregg_circuit::field::BabyBear;
use dregg_circuit::lean_descriptor_air::{VmConstraint, VmRow};

use dregg_circuit::refusal::{Outcome, classify};
use dregg_circuit_prove::bridge_leaf_adapter::bridge_action_to_descriptor2;

/// The BYTE-IDENTICAL wire string Lean's `emitVmJson2 bridgeActionDesc` emits (pinned by the
/// `#guard` in `BridgeActionEmit.lean`). If Lean's emitter drifts, that `#guard` fails; if this
/// literal drifts, the `decoded == hand_built` assertion fails. Neither can silently diverge.
/// ⚑ **THE EMITTED ARTIFACT ITSELF, NOT A COPY OF IT (2026-08-06).** This was an inline
/// `r#"…"#` transcription of the Lean `#guard` bytes, and the `challenges` flag day
/// (2026-08-05) broke it along with 27 siblings: the artifact under
/// `circuit/descriptors/` was re-emitted, the literal was not, and
/// `parse_vm_descriptor2` refused it with `ir:2 descriptor missing "challenges"`. An
/// inline golden is a copy that no re-emit reaches, so every flag day breaks exactly
/// that set again — the fix is to have no copy. `check-emit-gate-weld.py` still gates
/// the literals that remain (the descriptors with no checked-in artifact to name), and
/// `check-descriptor-drift.sh` gates this file against its Lean author.
const GOLDEN_JSON: &str = include_str!("../../circuit/descriptors/by-name/bridge-action.json");

/// The per-column continuity `WindowGate{Nxt(c) + (−1)·Loc(c), on_transition}` — the faithful twin
/// of the hand AIR's `next[c] − local[c] == 0` (built EXACTLY as Lean's `contBody` /
/// `bridge_action_to_descriptor2`).
fn window_gate(c: usize) -> VmConstraint2 {
    VmConstraint2::WindowGate(WindowGateSpec {
        body: WindowExpr::Add(
            Box::new(WindowExpr::Nxt(c)),
            Box::new(WindowExpr::Mul(
                Box::new(WindowExpr::Const(-1)),
                Box::new(WindowExpr::Loc(c)),
            )),
        ),
        on_transition: true,
    })
}

/// The independently-hand-built twin of the Lean `bridgeActionDesc` (the "hand AIR semantics"
/// shape): 26 first-row `PiBinding{First, col=c, pi=c}` boundary pins ++ 26 column-constancy
/// `WindowGate`s, table-free.
fn hand_built_desc() -> EffectVmDescriptor2 {
    let mut constraints: Vec<VmConstraint2> = Vec::with_capacity(2 * BRIDGE_ACTION_WIDTH);
    for c in 0..BRIDGE_ACTION_PI_COUNT {
        constraints.push(VmConstraint2::Base(VmConstraint::PiBinding {
            row: VmRow::First,
            col: c,
            pi_index: c,
        }));
    }
    for c in 0..BRIDGE_ACTION_WIDTH {
        constraints.push(window_gate(c));
    }
    EffectVmDescriptor2 {
        name: "bridge-action-leaf::bridge_action_air_v1".to_string(),
        trace_width: BRIDGE_ACTION_WIDTH,
        public_input_count: BRIDGE_ACTION_PI_COUNT,
        challenges: 0,
        tables: vec![],
        constraints,
        hash_sites: vec![],
        ranges: vec![],
    }
}

/// A typed bridge-action witness (distinct 32-byte fields + a full 64-bit amount above 2^32, so
/// exercising the high limb) — the same fixture shape `bridge_action_witness`'s own tests use.
fn fixture() -> BridgeActionWitness {
    BridgeActionWitness {
        nullifier: [0x10; 32],
        recipient: [0x20; 32],
        destination_federation: [0x30; 32],
        amount: 0xDEAD_BEEF_CAFE_F00D,
    }
}

/// `true` iff this `(trace, pis)` is REJECTED end-to-end — proving refuses OR the produced proof
/// fails to VERIFY against `pis`. `false` iff it both proves AND verifies.
///
/// Prove-THEN-verify is the faithful gate: `prove_vm_descriptor2` self-verifies only under
/// `cfg!(debug_assertions)` (`descriptor_ir2.rs:4857`), so in a `--release` test the eager replay
/// alone does not check the first-row `PiBinding` against the public inputs — the CONSUMER's
/// `verify_vm_descriptor2` is the real check (exactly the production posture).
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

/// STEP 1 — the emitted descriptor decodes and equals BOTH the hand-built twin AND the proven Rust
/// builder `bridge_action_to_descriptor2` (Lean emit ≡ Rust semantics), with the expected shape.
#[test]
fn bridge_action_emit_decodes_to_hand_built() {
    let decoded = parse_vm_descriptor2(GOLDEN_JSON).expect("the Lean-emitted golden JSON decodes");
    let hand = hand_built_desc();
    assert_eq!(
        decoded, hand,
        "the Lean-emitted descriptor must equal the independently hand-built descriptor"
    );
    let adapter = bridge_action_to_descriptor2().expect("the proven Rust adapter builds");
    assert_eq!(
        decoded, adapter,
        "the Lean-emitted descriptor must equal the already-proven bridge_action_to_descriptor2()"
    );

    // shape pins
    assert_eq!(decoded.trace_width, BRIDGE_ACTION_WIDTH);
    assert_eq!(decoded.public_input_count, BRIDGE_ACTION_PI_COUNT);
    assert!(decoded.tables.is_empty(), "bridge uses no declared tables");
    assert!(decoded.hash_sites.is_empty());
    assert!(decoded.ranges.is_empty());
    assert_eq!(decoded.constraints.len(), 2 * BRIDGE_ACTION_WIDTH);

    let pins = decoded
        .constraints
        .iter()
        .filter(|c| matches!(c, VmConstraint2::Base(VmConstraint::PiBinding { .. })))
        .count();
    assert_eq!(pins, BRIDGE_ACTION_PI_COUNT, "one boundary pin per PI slot");
    let gates = decoded
        .constraints
        .iter()
        .filter(|c| matches!(c, VmConstraint2::WindowGate(_)))
        .count();
    assert_eq!(gates, BRIDGE_ACTION_WIDTH, "one continuity gate per column");

    // The PI layout is identity (`pi_index == col`), preserving the 8/8/8/2-limb slot order.
    for (i, (col, pi)) in decoded
        .constraints
        .iter()
        .filter_map(|c| match c {
            VmConstraint2::Base(VmConstraint::PiBinding { col, pi_index, .. }) => {
                Some((*col, *pi_index))
            }
            _ => None,
        })
        .enumerate()
    {
        assert_eq!(
            (col, pi),
            (i, i),
            "PiBinding {i} pins col == pi_index == {i}"
        );
    }
}

/// STEP 2 — THE POSITIVE POLE: an honest 26-slot bridge-action witness proves through the emitted
/// descriptor (the canonical `generate_trace`: one typed row replicated for FRI padding), and the
/// proof re-verifies against the bound tuple as public inputs.
#[test]
fn honest_bridge_action_proves_and_verifies() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    let w = fixture();
    let (trace, pis) = BridgeActionAir::generate_trace(&w);
    assert_eq!(pis.len(), BRIDGE_ACTION_PI_COUNT);
    assert_eq!(trace.len(), 4, "one typed row padded to a power of 2");
    let proof = prove_vm_descriptor2(&desc, &trace, &pis, &MemBoundaryWitness::default(), &[])
        .expect("the honest bridge-action witness must prove (row0 pinned to the 26 PIs)");
    verify_vm_descriptor2(&desc, &proof, &pis)
        .expect("the honest proof must re-verify against the bound 26-slot tuple");
}

/// STEP 3a — MUTATION CANARY (forged PI → the `PiBinding` boundary tooth): honest trace, but the
/// claimed public input at a nullifier limb is FLIPPED. The first-row `PiBinding{col 0 == pi 0}`
/// requires `row0[0] == pi[0]`, so a mismatched PI is UNSAT. A verifier claiming a tuple the trace
/// does not carry is refused.
#[test]
fn forged_public_input_refuses() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    let w = fixture();
    let (trace, pis) = BridgeActionAir::generate_trace(&w);
    // sanity: the honest trace with the RIGHT PIs is ACCEPTED (non-vacuity of the negative below).
    assert!(
        !rejects(&desc, &trace, &pis),
        "honest witness must be accepted — else the canary is vacuous"
    );
    let mut forged = pis.clone();
    forged[0] += BabyBear::ONE; // flip a nullifier limb the trace still carries un-flipped
    assert_ne!(forged, pis);
    assert!(
        rejects(&desc, &trace, &forged),
        "a forged public input (row0 does not carry it) must be REJECTED (boundary tooth)"
    );
}

/// STEP 3b — MUTATION CANARY (swapped positional binding → the `PiBinding` boundary tooth): the
/// nullifier and recipient PI blocks are SWAPPED while the trace stays honest. The positional pins
/// (`row0[0..8] == pi[0..8]` nullifier, `row0[8..16] == pi[8..16]` recipient) are violated → UNSAT.
/// A prover cannot relabel which 32-byte field is the nullifier vs the recipient.
#[test]
fn swapped_nullifier_recipient_refuses() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    let w = fixture();
    let (trace, pis) = BridgeActionAir::generate_trace(&w);
    assert!(
        !rejects(&desc, &trace, &pis),
        "honest must accept (non-vacuity)"
    );
    // swap the two 8-limb blocks (nullifier ↔ recipient); distinct fixtures ⇒ genuinely different.
    let mut swapped = pis.clone();
    for i in 0..8 {
        swapped.swap(i, 8 + i);
    }
    assert_ne!(
        swapped, pis,
        "distinct nullifier/recipient ⇒ the swap changes the PI vector"
    );
    assert!(
        rejects(&desc, &trace, &swapped),
        "swapped nullifier/recipient PIs must be REJECTED (positional boundary binding)"
    );
}

/// STEP 3c — MUTATION CANARY (broken continuity → the `WindowGate` transition tooth): honest row 0
/// and honest PIs, but a PADDING row is perturbed in one column. The `WindowGate{on_transition}`
/// asserts `next[c] − local[c] == 0` on every transition, so a padding row differing from row 0
/// breaks the 0→1 (and 1→2) transition → UNSAT — while the first-row `PiBinding`s still hold. This
/// isolates the "one typed row replicated for FRI padding" glue: a prover cannot bind one tuple in
/// row 0 and a different one in a padding row.
#[test]
fn broken_padding_continuity_refuses() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    let w = fixture();
    let (trace, pis) = BridgeActionAir::generate_trace(&w);
    assert!(
        !rejects(&desc, &trace, &pis),
        "honest must accept (non-vacuity)"
    );
    let mut tampered = trace.clone();
    // Perturb ONE column of a PADDING row (row 1); row 0 and the PIs are untouched, so the ONLY
    // violated relation is the column-constancy WindowGate on the 0→1 transition.
    tampered[1][0] += BabyBear::ONE;
    assert!(
        rejects(&desc, &tampered, &pis),
        "a padding row diverging from row 0 must be REJECTED (transition-continuity tooth)"
    );
}
