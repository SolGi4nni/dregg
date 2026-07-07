//! # The emit-from-Lean EQUALITY GATE — `presentation` family (token-presentation summary AIR +
//! its off-AIR FRESHNESS binding).
//!
//! Validates the `emit-from-Lean` pattern for the `presentation` family
//! (`circuit/src/presentation.rs`). The deployed hand AIR (`PresentationAir::constraints`,
//! `presentation.rs:807`) enforces ONLY a 19-column `row[i] == pi[i]` summary copy; ALL the real
//! security lives in plaintext `PresentationProof::verify` (`presentation.rs:224`). This descriptor
//! is faithful to the literal hand AIR (the 19 summary `PiBinding` copies) AND internalizes the one
//! off-AIR check that is a self-contained arithmetic tooth: the FRESHNESS binding
//! (`verify_freshness_binding`, `presentation.rs:316` — accept iff
//! `diff = not_after − verifier ∈ [0, p/2]`, `p/2 = 1_006_632_960`).
//!
//! The descriptor is AUTHORED in Lean
//! (`metatheory/Dregg2/Circuit/Emit/PresentationEmit.lean`, `presentationFreshnessDesc`) and its
//! wire string is byte-pinned there (`emitVmJson2` `#guard`). This test embeds that EXACT string
//! ([`GOLDEN_JSON`]) and:
//!
//!   1. DECODES it via [`parse_vm_descriptor2`] and asserts the decode equals an independently
//!      hand-built `EffectVmDescriptor2` (Lean emit ≡ Rust builder — a byte drift on either side
//!      breaks this OR the Lean `#guard`);
//!   2. proves an HONEST fresh-token witness through [`prove_vm_descriptor2`], asserts ACCEPT, and
//!      re-verifies against the public summary + `verifier_block_height`;
//!   3. the MUTATION CANARIES — each tampers ONE thing and asserts prove-or-verify REFUSES (real
//!      UNSAT), biting a DISTINCT constraint:
//!        - an EXPIRED token (`not_after < verifier`) → `diff` wraps to `p − …`, out of `[0, 2^30)`
//!          → the **diff Range** tooth (asserted with the range-specific error, so the refusal is
//!          provably the range mechanism);
//!        - an in-`[0,2^30)`-but-`> p/2` `diff` → the complement `hi = p/2 − diff` wraps → the
//!          **hi Range** tooth (the EXACT non-power-of-two `p/2` bound — the star tooth, the thing a
//!          single `Range{bits}` could NOT express);
//!        - an in-range but inconsistent `diff` → the **diff-binding gate**;
//!        - a forged summary PI → a **summary copy** (the literal deployed hand-AIR tooth);
//!        - a forged `verifier_block_height` PI → the **freshness public anchor**.
//!
//! Each canary is NON-VACUOUS: the honest witness proves-and-verifies (step 2 + in-canary sanity),
//! and each tamper genuinely breaks a named constraint.
//!
//! ## The NAMED gates (out of descriptor by design, per the `FITS_WITH_NAMED_GATE` verdict)
//!
//! `verify()`'s fold-chain continuity + derivation-root binding, issuer Merkle membership STARK,
//! temporal-predicate STARKs, and the presentation-tag hash ride the named recursion / STARK-leaf
//! argument (DECO-leaf posture) and are executor-verified — NOT internalized here. `not_after_height`
//! is a value published by the derivation leaf; this descriptor binds the freshness ARITHMETIC over
//! it and names the leaf that furnishes it.

use std::panic::AssertUnwindSafe;

use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, LookupSpec, MemBoundaryWitness, TID_RANGE, TableDef2, TableSem,
    VmConstraint2, parse_vm_descriptor2, prove_vm_descriptor2, verify_vm_descriptor2,
};
use dregg_circuit::field::BabyBear;
use dregg_circuit::lean_descriptor_air::{LeanExpr, VmConstraint, VmRow};

/// The BYTE-IDENTICAL wire string Lean's `emitVmJson2 presentationFreshnessDesc` emits (pinned by
/// the `#guard` in `PresentationEmit.lean`). If Lean's emitter drifts, that `#guard` fails; if this
/// literal drifts, the `decoded == hand_built` assertion fails. Neither can silently diverge.
const GOLDEN_JSON: &str = r#"{"name":"dregg-presentation-freshness::summary-v1","ir":2,"trace_width":23,"public_input_count":20,"tables":[{"id":2,"name":"range","arity":1,"sem":"range","bits":30}],"constraints":[{"t":"pi_binding","row":"first","col":0,"pi_index":0},{"t":"pi_binding","row":"first","col":1,"pi_index":1},{"t":"pi_binding","row":"first","col":2,"pi_index":2},{"t":"pi_binding","row":"first","col":3,"pi_index":3},{"t":"pi_binding","row":"first","col":4,"pi_index":4},{"t":"pi_binding","row":"first","col":5,"pi_index":5},{"t":"pi_binding","row":"first","col":6,"pi_index":6},{"t":"pi_binding","row":"first","col":7,"pi_index":7},{"t":"pi_binding","row":"first","col":8,"pi_index":8},{"t":"pi_binding","row":"first","col":9,"pi_index":9},{"t":"pi_binding","row":"first","col":10,"pi_index":10},{"t":"pi_binding","row":"first","col":11,"pi_index":11},{"t":"pi_binding","row":"first","col":12,"pi_index":12},{"t":"pi_binding","row":"first","col":13,"pi_index":13},{"t":"pi_binding","row":"first","col":14,"pi_index":14},{"t":"pi_binding","row":"first","col":15,"pi_index":15},{"t":"pi_binding","row":"first","col":16,"pi_index":16},{"t":"pi_binding","row":"first","col":17,"pi_index":17},{"t":"pi_binding","row":"first","col":18,"pi_index":18},{"t":"pi_binding","row":"first","col":19,"pi_index":19},{"t":"gate","body":{"t":"add","l":{"t":"add","l":{"t":"var","v":21},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":20}}},"r":{"t":"var","v":19}}},{"t":"gate","body":{"t":"add","l":{"t":"add","l":{"t":"var","v":21},"r":{"t":"var","v":22}},"r":{"t":"const","v":-1006632960}}},{"t":"lookup","table":2,"tuple":[{"t":"var","v":21}]},{"t":"lookup","table":2,"tuple":[{"t":"var","v":22}]}],"hash_sites":[],"ranges":[]}"#;

// --- Trace column layout (must match `PresentationEmit.lean` §1). ---
const FEDERATION_ROOT: usize = 0;
const REQUEST_PREDICATE_BASE: usize = 1; // cols 1..=8 (ACTION_BINDING_WIDTH = 8)
const TIMESTAMP: usize = 9;
const PRESENTATION_TAG: usize = 10;
const REVEALED_FACTS_BASE: usize = 11; // cols 11..=18 (WideHash::WIDTH = 8)
const SUMMARY_WIDTH: usize = 19;
const VERIFIER: usize = 19;
const NOT_AFTER: usize = 20;
const DIFF: usize = 21;
const HI: usize = 22;
const PRES_WIDTH: usize = 23;
const PI_VERIFIER: usize = 19;
const PI_COUNT: usize = 20;
const FRESH_BITS: usize = 30;
/// `p/2 = 1_006_632_960` (`p = 2013265921`) — the freshness acceptance bound (`presentation.rs:341`).
const HALF_P: u32 = 1_006_632_960;

/// The independently-hand-built twin of the Lean `presentationFreshnessDesc`: 19 summary
/// `PiBinding` copies (`col i == pi[i]`), the `verifier_block_height` anchor pin, the diff-binding
/// gate (`diff = not_after − verifier`), the bound gate (`diff + hi = p/2`), and the two range
/// lookups (`diff`, `hi` in `[0, 2^30)`).
fn hand_built_desc() -> EffectVmDescriptor2 {
    let mut constraints: Vec<VmConstraint2> = Vec::new();
    // 19 summary copies (PresentationAir::constraints).
    for i in 0..SUMMARY_WIDTH {
        constraints.push(VmConstraint2::Base(VmConstraint::PiBinding {
            row: VmRow::First,
            col: i,
            pi_index: i,
        }));
    }
    // The verifier-height public anchor.
    constraints.push(VmConstraint2::Base(VmConstraint::PiBinding {
        row: VmRow::First,
        col: VERIFIER,
        pi_index: PI_VERIFIER,
    }));
    // diff-binding gate: (DIFF + (-1)*NOT_AFTER) + VERIFIER == 0.
    constraints.push(VmConstraint2::Base(VmConstraint::Gate(LeanExpr::add(
        LeanExpr::add(
            LeanExpr::Var(DIFF),
            LeanExpr::mul(LeanExpr::Const(-1), LeanExpr::Var(NOT_AFTER)),
        ),
        LeanExpr::Var(VERIFIER),
    ))));
    // bound gate: (DIFF + HI) + (-p/2) == 0.
    constraints.push(VmConstraint2::Base(VmConstraint::Gate(LeanExpr::add(
        LeanExpr::add(LeanExpr::Var(DIFF), LeanExpr::Var(HI)),
        LeanExpr::Const(-(HALF_P as i64)),
    ))));
    // range lookups.
    constraints.push(VmConstraint2::Lookup(LookupSpec {
        table: TID_RANGE,
        tuple: vec![LeanExpr::Var(DIFF)],
    }));
    constraints.push(VmConstraint2::Lookup(LookupSpec {
        table: TID_RANGE,
        tuple: vec![LeanExpr::Var(HI)],
    }));
    EffectVmDescriptor2 {
        name: "dregg-presentation-freshness::summary-v1".to_string(),
        trace_width: PRES_WIDTH,
        public_input_count: PI_COUNT,
        tables: vec![TableDef2 {
            id: TID_RANGE,
            name: "range".to_string(),
            arity: 1,
            sem: TableSem::Range { bits: FRESH_BITS },
        }],
        constraints,
        hash_sites: vec![],
        ranges: vec![],
    }
}

/// The honest summary values (arbitrary distinct felts). Returns the 19 summary column felts in
/// layout order.
fn honest_summary() -> Vec<BabyBear> {
    let mut s = vec![BabyBear::ZERO; SUMMARY_WIDTH];
    s[FEDERATION_ROOT] = BabyBear::new(111);
    for k in 0..8 {
        s[REQUEST_PREDICATE_BASE + k] = BabyBear::new(200 + k as u32);
    }
    s[TIMESTAMP] = BabyBear::new(300);
    s[PRESENTATION_TAG] = BabyBear::new(400);
    for k in 0..8 {
        s[REVEALED_FACTS_BASE + k] = BabyBear::new(500 + k as u32);
    }
    s
}

/// One presentation row for `(verifier, not_after)`, with `diff = not_after − verifier` and
/// `hi = p/2 − diff` filled IN-FIELD (so the two gates hold by construction — only the range
/// lookups can bite on the freshness columns). The range limb columns are appended by the prover.
fn row_for(verifier: u32, not_after: u32) -> Vec<BabyBear> {
    let mut row = vec![BabyBear::ZERO; PRES_WIDTH];
    let summary = honest_summary();
    row[..SUMMARY_WIDTH].copy_from_slice(&summary);
    let verifier_f = BabyBear::new(verifier);
    let not_after_f = BabyBear::new(not_after);
    let diff = not_after_f - verifier_f;
    let hi = BabyBear::new(HALF_P) - diff;
    row[VERIFIER] = verifier_f;
    row[NOT_AFTER] = not_after_f;
    row[DIFF] = diff;
    row[HI] = hi;
    row
}

/// A 4-row (power-of-two) base trace of identical rows.
fn trace_for(verifier: u32, not_after: u32) -> Vec<Vec<BabyBear>> {
    let row = row_for(verifier, not_after);
    vec![row.clone(), row.clone(), row.clone(), row]
}

/// The honest public inputs: the 19 summary felts followed by the `verifier_block_height` anchor.
fn pis_for(verifier: u32) -> Vec<BabyBear> {
    let mut p = honest_summary();
    p.push(BabyBear::new(verifier));
    p
}

/// `true` iff this `(trace, pis)` is REJECTED end-to-end — proving refuses OR the produced proof
/// fails to VERIFY against `pis`. `false` iff it both proves AND verifies. Prove-THEN-verify is the
/// faithful gate: in `--release` the CONSUMER's `verify_vm_descriptor2` is the real PI/constraint
/// check (the production posture).
fn rejects(desc: &EffectVmDescriptor2, trace: &[Vec<BabyBear>], public: &[BabyBear]) -> bool {
    let r = std::panic::catch_unwind(AssertUnwindSafe(|| {
        let proof = prove_vm_descriptor2(desc, trace, public, &MemBoundaryWitness::default(), &[])?;
        verify_vm_descriptor2(desc, &proof, public)
    }));
    match r {
        Err(_) => true,      // panicked anywhere → rejected
        Ok(Err(_)) => true,  // prove OR verify returned Err → rejected
        Ok(Ok(())) => false, // proved AND verified → ACCEPTED
    }
}

/// STEP 1 — the emitted descriptor decodes and equals the hand-built twin (Lean emit ≡ Rust
/// semantics), and has exactly the expected shape.
#[test]
fn presentation_emit_decodes_to_hand_built() {
    let decoded = parse_vm_descriptor2(GOLDEN_JSON).expect("the Lean-emitted golden JSON decodes");
    let hand = hand_built_desc();
    assert_eq!(
        decoded, hand,
        "the Lean-emitted descriptor must equal the independently hand-built descriptor"
    );
    assert_eq!(decoded.trace_width, PRES_WIDTH);
    assert_eq!(decoded.public_input_count, PI_COUNT);
    // one range table declared at 30 bits.
    assert_eq!(decoded.tables.len(), 1);
    assert_eq!(decoded.tables[0].sem, TableSem::Range { bits: FRESH_BITS });
    // two range lookups (diff, hi) — the exact non-power-of-two p/2 gadget.
    let range_lookups = decoded
        .constraints
        .iter()
        .filter(|c| matches!(c, VmConstraint2::Lookup(l) if l.table == TID_RANGE))
        .count();
    assert_eq!(range_lookups, 2, "the diff + hi range lookups");
    // 20 PI bindings: 19 summary copies + the verifier-height anchor.
    let pins = decoded
        .constraints
        .iter()
        .filter(|c| matches!(c, VmConstraint2::Base(VmConstraint::PiBinding { .. })))
        .count();
    assert_eq!(pins, 20, "19 summary copies + the verifier-height anchor");
}

/// STEP 2 — THE POSITIVE POLE: an honest fresh-token witness (`not_after ≥ verifier`,
/// `diff = 500 ∈ [0, p/2]`) proves and re-verifies against the public summary + verifier height.
/// A range-only descriptor commits main + byte/range table (no chip, no mem/map).
#[test]
fn honest_fresh_token_proves_and_verifies() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    let trace = trace_for(1000, 1500); // diff = 500, hi = p/2 − 500, both in range
    let public = pis_for(1000);
    let proof = prove_vm_descriptor2(&desc, &trace, &public, &MemBoundaryWitness::default(), &[])
        .expect("the honest fresh-token witness must prove");
    assert_eq!(
        proof.degree_bits.len(),
        2,
        "a range-only descriptor commits main + byte/range table (no chip, no mem/map)"
    );
    verify_vm_descriptor2(&desc, &proof, &public)
        .expect("the honest proof must re-verify against the public summary + verifier height");
}

/// STEP 3a — MUTATION CANARY (diff Range tooth): an EXPIRED token, `not_after < verifier`.
/// `diff = not_after − verifier` wraps to `p − (verifier − not_after)`, out of `[0, 2^30)` — no
/// valid limb decomposition. The gates still hold (diff/hi filled in-field), so ONLY the diff range
/// can fail; the refusal is asserted to name the range mechanism.
#[test]
fn expired_token_refuses_on_diff_range() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    // non-vacuity: the honest fresh token is ACCEPTED.
    assert!(
        !rejects(&desc, &trace_for(1000, 1500), &pis_for(1000)),
        "honest fresh token must be accepted — else the canary is vacuous"
    );
    // verifier 1500 > not_after 1000 ⇒ diff = -500 (field) = p - 500, out of [0, 2^30).
    let trace = trace_for(1500, 1000);
    let public = pis_for(1500);
    let err =
        match prove_vm_descriptor2(&desc, &trace, &public, &MemBoundaryWitness::default(), &[]) {
            Ok(_) => panic!("an expired token must be REFUSED (diff wraps out of range)"),
            Err(e) => e,
        };
    assert!(
        err.contains("range") || err.contains("2^"),
        "the refusal must be the diff RANGE mechanism, got: {err}"
    );
    assert!(rejects(&desc, &trace, &public));
}

/// STEP 3b — MUTATION CANARY (hi Range tooth — the EXACT `p/2` bound). A `diff = p/2 + 1`, still in
/// `[0, 2^30)` (so its OWN range passes), forces the complement `hi = p/2 − diff = -1 = p − 1`, out
/// of `[0, 2^30)` → the `hi` range is UNSAT. This is the tooth a single `Range{bits}` could NOT
/// express: it distinguishes the real non-power-of-two bound `≤ p/2` from the loose `< 2^30`.
#[test]
fn just_expired_token_refuses_on_hi_range() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    // verifier 1, not_after = p/2 + 2 ⇒ diff = p/2 + 1 (in [0,2^30)), hi = -1 = p-1 (out of range).
    let verifier = 1u32;
    let not_after = HALF_P + 2;
    let trace = trace_for(verifier, not_after);
    let public = pis_for(verifier);
    // sanity: diff itself is IN 30-bit range (so the bite is genuinely the hi range, not diff).
    let diff = BabyBear::new(not_after) - BabyBear::new(verifier);
    assert!(
        (diff.as_u32() as u64) < (1u64 << FRESH_BITS),
        "diff = p/2 + 1 must itself be in [0, 2^30) — else this is the diff tooth, not hi"
    );
    assert!(
        diff.as_u32() > HALF_P,
        "diff must be strictly above p/2 (the token is expired by the exact bound)"
    );
    let err =
        match prove_vm_descriptor2(&desc, &trace, &public, &MemBoundaryWitness::default(), &[]) {
            Ok(_) => panic!("a diff > p/2 must be REFUSED (hi = p/2 − diff wraps out of range)"),
            Err(e) => e,
        };
    assert!(
        err.contains("range") || err.contains("2^"),
        "the refusal must be the hi RANGE mechanism (the exact p/2 bound), got: {err}"
    );
    assert!(rejects(&desc, &trace, &public));
}

/// STEP 3c — MUTATION CANARY (diff-binding gate): an in-range but INCONSISTENT `diff` (600 where
/// `not_after − verifier = 500`), with `hi = p/2 − 600` re-consistent so the bound gate + both
/// ranges pass. ONLY the diff-binding gate `diff − not_after + verifier == 0` is violated → rejected.
#[test]
fn inconsistent_diff_refuses_on_binding_gate() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    let mut trace = trace_for(1000, 1500); // correct diff = 500
    for row in &mut trace {
        row[DIFF] = BabyBear::new(600); // should be 500; in range, but breaks the binding gate
        row[HI] = BabyBear::new(HALF_P) - BabyBear::new(600); // keep the bound gate + hi range OK
    }
    let public = pis_for(1000);
    assert!(
        rejects(&desc, &trace, &public),
        "an in-range diff inconsistent with (not_after − verifier) must be REJECTED (binding gate)"
    );
}

/// STEP 3d — MUTATION CANARY (summary copy — the literal deployed hand-AIR tooth): honest trace,
/// forged public `federation_root` (summary PI 0). The first-row column (111) no longer equals
/// `pi[0]` (112) → the summary copy is violated at verify → rejected.
#[test]
fn forged_summary_pi_refuses() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    let trace = trace_for(1000, 1500);
    // non-vacuity: the honest summary PIs are accepted.
    assert!(!rejects(&desc, &trace, &pis_for(1000)));
    let mut forged = pis_for(1000);
    forged[FEDERATION_ROOT] = BabyBear::new(112); // honest is 111
    assert!(
        rejects(&desc, &trace, &forged),
        "a forged summary PI (federation_root) must be REJECTED (summary copy)"
    );
}

/// STEP 3e — MUTATION CANARY (freshness public anchor): honest trace, forged
/// `verifier_block_height` PI. The first-row `VERIFIER` column (1000) no longer equals `pi[19]`
/// (1001) → the anchor PI binding is violated → rejected. The public height the freshness check
/// reads is bound to the witness, so an attacker cannot claim a different verifier height.
#[test]
fn forged_verifier_height_pi_refuses() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    let trace = trace_for(1000, 1500);
    assert!(!rejects(&desc, &trace, &pis_for(1000)));
    let mut forged = pis_for(1000);
    forged[PI_VERIFIER] = BabyBear::new(1001); // honest is 1000
    assert!(
        rejects(&desc, &trace, &forged),
        "a forged verifier_block_height PI must be REJECTED (freshness anchor)"
    );
}
