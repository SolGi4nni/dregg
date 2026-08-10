//! ⚑ **THE IR-v2 RECURSION SEAM, ON THE DEPLOYED PROVER: proved BEFORE, REFUSED AFTER.**
//!
//! # What was measured, and what it cost
//!
//! `VmConstraint2::ProofBind` was, until 2026-08-04, the one constraint kind that denoted **nothing
//! in either language**. In Lean `DescriptorIR2.VmConstraint2.holdsAt` returned `True` for it; in
//! Rust `Ir2Air::eval` grouped it with the bus kinds and `continue`d. The other four bus kinds get
//! their content back from a LogUp send the caller emits — `ProofBind` emitted no interaction
//! either. And no served descriptor emitted one, so five light-client hash folds were queued behind
//! a seam that, had they used it, would have checked nothing.
//!
//! ⚠ **And the hole was not only the `True`.** The existential it deferred to,
//! `ProofBind.boundAt`, reads
//!
//! ```text
//! guard = 1 → ∃ p, E.verify p ∧ E.piCommit p = commit ∧ E.vkOf p = vk
//! ```
//!
//! over **free prover-chosen `commit` and `vk` columns**. `EngineBinding.commit_determines_vk` makes
//! commit ⇒ vk functional across verifying proofs; it does not say WHICH program. So a fully
//! deployed recursion layer would still have discharged the leg with a verifying sub-proof of any
//! program about any statement — the decorative-anchor shape, one level up.
//!
//! # What this file proves, on the shipped prover
//!
//! The seam is three row-local polynomials (Lean `ProofBind.holdsAt`, Rust `Ir2Air::eval`'s
//! `ProofBind` arm):
//!
//! ```text
//! guard·(guard − 1)          the selector is a bit
//! guard·(vk − vk_pin)        the attested program is the DECLARED one    [if pinned]
//! guard·(commit − bound)     the commitment is the DECLARED row expr     [if bound]
//! ```
//!
//! Each test below hands the **identical trace** to two descriptors differing in exactly one field,
//! and shows the row PROVES under the declarative descriptor (`vk_pin`/`bound` = `null`, the shape
//! every `proof_bind` had before this change) and is REFUSED under the pinned one. That two-poled
//! form is the point: a tooth that only shows the current object refusing has not shown the value
//! would ever have been admitted.
//!
//! ⚠ **PROFILE.** plonky3's ALGEBRAIC refusals are `#[cfg(debug_assertions)]` panics under a plain
//! `cargo test` and clean `Err(OodEvaluationMismatch)` under `--release`. Every refusal here goes
//! through `dregg_circuit::refusal`, which catches both, so the file is meaningful in either — but
//! the RELEASE reading is the deployed one and is what the seam's landing report quotes.
//!
//! # Scope, said plainly
//!
//! This is a prover running a synthetic descriptor that exercises the seam's three polynomials. It
//! is **not** evidence that any sub-proof exists or verifies: no row-local gate of any shape can
//! see that, which is exactly why `CustomCarrierAttack.deployed_admits_unbacked` survives the seam
//! with a re-witnessed proof. The dregg-side STARK inherits the undischarged FRI floor, and a Rust
//! case-test quantifies over nothing — the machine-checked statements are the Lean ones this file
//! names (`demoC_seam_refutes_forged_commit`, `demoC_seam_refutes_swapped_vk`,
//! `demoC_seam_refutes_fractional_guard`).

use dregg_circuit::BabyBear;
use dregg_circuit::descriptor_ir2::{
    CommitBinding, EffectVmDescriptor2, MemBoundaryWitness, PortCover, ProofBindSpec, TableDef2,
    TableSem, VmConstraint2, prove_vm_descriptor2, verify_vm_descriptor2,
};
use dregg_circuit::heap_root::HeapLeaf;
use dregg_circuit::lean_descriptor_air::LeanExpr;
use dregg_circuit::refusal;

/// Trace column layout of the synthetic seam descriptor — the same three roles the deployed
/// `customProofBind` names (`sel::CUSTOM`, `custom_proof_commitment`, `custom_program_vk_hash`),
/// plus a lane block standing for the row-derived object a light-client fold's `bound` would be.
///
/// ⚑ **EIGHT LANES EACH since 2026-08-05.** This file measured a ONE-FELT seam until the widening,
/// which is the whole reason the widening happened: a one-felt tie is worth `2^31`.
const GUARD: usize = 0;
const COMMIT_BASE: usize = 1;
const VK_BASE: usize = 9;
/// The row-local object the commitment must equal, lane by lane. In a landed fold this is the
/// in-AIR anchor digest; here it is a plain column block so the tooth measures the SEAM and not a
/// hash gadget.
const ANCHOR_BASE: usize = 17;

const LANES: usize = 8;
const WIDTH: usize = 25;
const ROWS: usize = 8;

/// The program VK the pinned descriptor declares — EIGHT lanes, arbitrary but FIXED. The whole
/// content of `vk_pin` is that the prover cannot choose it, and the whole content of the widening is
/// that it cannot choose any of the eight.
const DECLARED_VK: [i64; LANES] = [
    0x5eed_51, 0x5eed_52, 0x5eed_53, 0x5eed_54, 0x5eed_55, 0x5eed_56, 0x5eed_57, 0x5eed_58,
];

/// The honest commitment vector — what an honest row's anchor block carries.
const HONEST_COMMIT: [i64; LANES] = [42, 43, 44, 45, 46, 47, 48, 49];

fn felt(v: i64) -> BabyBear {
    BabyBear::new(v.rem_euclid(2_013_265_921) as u32)
}

fn lanes(base: usize) -> Vec<LeanExpr> {
    (0..LANES).map(|k| LeanExpr::Var(base + k)).collect()
}

/// A ported commit half, naming a cover. ⚑ Since the 2026-08-10 flag day this is the ONLY way to
/// say "this AIR does not force the commit lanes" — the retired `None` said it by emitting nothing
/// and naming nothing.
fn ported() -> CommitBinding {
    CommitBinding::Port(PortCover {
        port: "demo-commitment".into(),
        seam: "dregg-seam-demo::v1".into(),
    })
}

/// The seam descriptor, parameterised by the two declared halves. `(None, ported())` is the shape
/// every `proof_bind` in the tree carried before 2026-08-04 and is the BEFORE pole of every tooth
/// here.
fn seam_desc(vk_pin: Option<Vec<i64>>, bound: CommitBinding) -> EffectVmDescriptor2 {
    EffectVmDescriptor2 {
        name: "ir2-proof-bind-seam".into(),
        trace_width: WIDTH,
        public_input_count: 0,
        challenges: 0,
        tables: vec![TableDef2 {
            id: 0,
            name: "main".into(),
            arity: WIDTH,
            sem: TableSem::Main,
        }],
        constraints: vec![VmConstraint2::ProofBind(ProofBindSpec {
            guard: LeanExpr::Var(GUARD),
            commit: lanes(COMMIT_BASE),
            vk: lanes(VK_BASE),
            vk_pin,
            bound,
        })],
        hash_sites: vec![],
        ranges: vec![],
    }
}

/// The DECLARATIVE seam — both halves `null`. This is the object the whole tree shipped.
fn declarative() -> EffectVmDescriptor2 {
    seam_desc(None, ported())
}

/// The PINNED seam — the program is `DECLARED_VK` on all eight lanes and the commitment must equal
/// the row's anchor block, lane for lane.
fn pinned() -> EffectVmDescriptor2 {
    seam_desc(
        Some(DECLARED_VK.to_vec()),
        CommitBinding::Bound(lanes(ANCHOR_BASE)),
    )
}

/// ⚑ **THE RETIRED ONE-FELT TIE, RECONSTRUCTED AT EIGHT LANES** — the containment this widening
/// replaced, expressed in the widened IR so the two can be measured against ONE trace.
///
/// Lane 0 is pinned to the anchor; lanes 1..8 are pinned to the COMMITMENT COLUMNS THEMSELVES, i.e.
/// `commitᵢ − commitᵢ = 0`, which is decoration (`feedback-a-pin-against-its-own-definition-is-
/// decoration`). That is exactly what the pre-widening seam asserted: one felt of an eight-felt
/// object, `2^31`.
fn limb0_only() -> EffectVmDescriptor2 {
    let mut bound = vec![LeanExpr::Var(ANCHOR_BASE)];
    bound.extend((1..LANES).map(|k| LeanExpr::Var(COMMIT_BASE + k)));
    let mut vk_pin = vec![DECLARED_VK[0]];
    // The high VK lanes are pinned to their own honest values, so this seam is satisfied by any row
    // agreeing with the declaration on lane 0 alone — the pre-widening reach.
    vk_pin.extend(DECLARED_VK[1..].iter().copied());
    seam_desc(Some(vk_pin), CommitBinding::Bound(bound))
}

fn row(
    guard: i64,
    commit: [i64; LANES],
    vk: [i64; LANES],
    anchor: [i64; LANES],
) -> Vec<Vec<BabyBear>> {
    let mut cells = vec![0i64; WIDTH];
    cells[GUARD] = guard;
    for k in 0..LANES {
        cells[COMMIT_BASE + k] = commit[k];
        cells[VK_BASE + k] = vk[k];
        cells[ANCHOR_BASE + k] = anchor[k];
    }
    let r: Vec<BabyBear> = cells.iter().map(|&v| felt(v)).collect();
    vec![r; ROWS]
}

/// A lane vector with ONE lane moved — the seven-of-eight forgery.
fn moved(base: [i64; LANES], lane: usize, to: i64) -> [i64; LANES] {
    let mut v = base;
    v[lane] = to;
    v
}

fn prove_and_verify(d: &EffectVmDescriptor2, trace: &[Vec<BabyBear>]) -> Result<(), String> {
    let mem = MemBoundaryWitness::default();
    let heaps: Vec<Vec<HeapLeaf>> = vec![];
    let proof = prove_vm_descriptor2(d, trace, &[], &mem, &heaps)
        .map_err(|e| format!("prover refused: {e}"))?;
    verify_vm_descriptor2(d, &proof, &[]).map_err(|e| format!("verifier refused: {e:?}"))
}

/// The shared two-pole measurement: the SAME trace proves under `before` and is refused under
/// `after`. Returns the refusal text so each tooth can print what the deployed prover actually said.
fn proved_before_refused_after(
    what: &str,
    before: &EffectVmDescriptor2,
    after: &EffectVmDescriptor2,
    trace: &[Vec<BabyBear>],
) -> String {
    refusal::must_accept(&format!("{what} — BEFORE (declarative seam)"), || {
        prove_and_verify(before, trace)
    });
    refusal::must_refuse(&format!("{what} — AFTER (pinned seam)"), || {
        prove_and_verify(after, trace)
    })
}

// ═══════════════════════════════════════════════════════════════════════════════════════════
// The three conjuncts, each proved-before / refused-after on the deployed prover
// ═══════════════════════════════════════════════════════════════════════════════════════════

/// ⚑ **THE BOUND RELATION.** A row whose commitment is not the object the descriptor says it is.
/// Everything else about this witness is satisfied — the guard is a bit, the attested program is the
/// declared one — and it PROVES against the declarative seam. Under the pinned seam
/// `guard·(commit − anchor) = 777 − 42 ≠ 0` and the prover refuses.
///
/// Lean twin: `DescriptorIR2.demoC_seam_refutes_forged_commit`.
#[test]
fn a_commitment_that_is_not_the_declared_row_object_proves_before_and_is_refused_after() {
    let trace = row(1, [777; LANES], DECLARED_VK, HONEST_COMMIT);
    let reason = proved_before_refused_after(
        "a commitment unrelated to the row it claims to be about",
        &declarative(),
        &pinned(),
        &trace,
    );
    eprintln!("forged commitment: {reason}");
}

/// ⚑ **THE PROGRAM PIN.** A row bound to a verifying sub-proof of the WRONG PROGRAM. This is the
/// conjunct `EngineBinding` structurally cannot supply — it makes commit ⇒ vk functional, it never
/// says which program — so before this seam there was no object anywhere in the stack that refused
/// it.
///
/// Lean twin: `DescriptorIR2.demoC_seam_refutes_swapped_vk`.
#[test]
fn a_swapped_program_vk_proves_before_and_is_refused_after() {
    let trace = row(
        1,
        HONEST_COMMIT,
        moved(DECLARED_VK, 0, DECLARED_VK[0] + 1),
        HONEST_COMMIT,
    );
    let reason = proved_before_refused_after(
        "a sub-proof of a program the descriptor did not name",
        &declarative(),
        &pinned(),
        &trace,
    );
    eprintln!("swapped program vk: {reason}");
}

/// ⚑ **THE GUARD.** A fractional selector. Note the polarity: this one is refused by the seam even
/// in its DECLARATIVE form, because `guard·(guard − 1)` is asserted unconditionally — so the BEFORE
/// pole here is not the declarative descriptor but the tree's state one commit ago, where the arm
/// was a bare `continue` and emitted no polynomial at all. What this test can measure is that the
/// shipped arm refuses it under BOTH declarations, which is what makes "declarative" weaker than
/// the pinned form without being the old `True`.
///
/// Lean twin: `DescriptorIR2.demoC_seam_refutes_fractional_guard`.
#[test]
fn a_fractional_selector_is_refused_by_the_seam_in_both_declarations() {
    let trace = row(2, HONEST_COMMIT, DECLARED_VK, HONEST_COMMIT);
    for (label, d) in [("declarative", declarative()), ("pinned", pinned())] {
        let reason = refusal::must_refuse(&format!("a fractional selector ({label} seam)"), || {
            prove_and_verify(&d, &trace)
        });
        eprintln!("fractional selector ({label}): {reason}");
    }
}

// ═══════════════════════════════════════════════════════════════════════════════════════════
// Completeness — the seam is not refusing everything
// ═══════════════════════════════════════════════════════════════════════════════════════════

/// The HONEST row proves under the PINNED seam: guard `1`, the declared program, and a commitment
/// equal to the row's anchor. Without this the three refusals above would be consistent with a seam
/// that is simply unsatisfiable.
#[test]
fn the_honest_row_proves_under_the_pinned_seam() {
    refusal::must_accept("an honest bound row under the pinned seam", || {
        prove_and_verify(
            &pinned(),
            &row(1, HONEST_COMMIT, DECLARED_VK, HONEST_COMMIT),
        )
    });
}

/// An INACTIVE row (guard `0`) proves under the pinned seam with a junk commitment and a junk vk —
/// the seam is genuinely guarded and does not force the columns of rows it does not claim. Every
/// deployed descriptor has such rows (the Custom selector is off on transfer rows), so a seam that
/// forced them would be uncompletable rather than sound.
#[test]
fn an_inactive_row_is_not_constrained_by_the_seam() {
    refusal::must_accept("an inactive seam row carrying junk", || {
        prove_and_verify(
            &pinned(),
            &row(0, [999_999; LANES], [12_345; LANES], HONEST_COMMIT),
        )
    });
}

// ═══════════════════════════════════════════════════════════════════════════════════════════
// The wire format — the declaration is a VALUE, and the fingerprint sees it
// ═══════════════════════════════════════════════════════════════════════════════════════════

/// ⚑ A descriptor that DROPS its program pin or its bound expression must move its canonical
/// fingerprint. Otherwise the registry could not tell a bound seam from a declarative one and "the
/// seam landed" would be a claim about a source file rather than about the committed object.
#[test]
fn the_declared_halves_are_inside_the_canonical_fingerprint() {
    use dregg_circuit::descriptor_ir2_canonical::canonical_effect_vm_descriptor2_bytes as enc;
    let d0 = enc(&declarative()).expect("declarative seam encodes");
    let d1 = enc(&pinned()).expect("pinned seam encodes");
    let d2 = enc(&seam_desc(Some(DECLARED_VK.to_vec()), ported())).expect("vk-only encodes");
    let d3 = enc(&seam_desc(None, CommitBinding::Bound(lanes(ANCHOR_BASE))))
        .expect("bound-only encodes");
    let d4 = enc(&limb0_only()).expect("limb-0 seam encodes");
    for (a, an, b, bn) in [
        (&d0, "declarative", &d1, "pinned"),
        (&d0, "declarative", &d2, "vk-pin only"),
        (&d0, "declarative", &d3, "bound only"),
        (&d1, "pinned", &d2, "vk-pin only"),
        (&d1, "pinned", &d3, "bound only"),
        // ⚑ And the WIDTH is in the fingerprint: a seam that ties lane 0 and decorates the rest is
        // a different committed object from one that ties all eight.
        (&d1, "pinned", &d4, "limb-0-only"),
    ] {
        assert_ne!(
            a, b,
            "{an} and {bn} seams must not share a canonical encoding — the fingerprint is what a \
             registry compares, and an invisible declaration is the wound this seam closes"
        );
    }
}

/// `is_declarative` is the countable form of "this seam pins neither half", and it is the number
/// that must ratchet down. Its Lean twin is `DescriptorIR2.ProofBind.isDeclarative`.
#[test]
fn is_declarative_reports_exactly_the_unpinned_seams() {
    let cases = [
        (declarative(), true),
        (pinned(), false),
        (seam_desc(Some(DECLARED_VK.to_vec()), ported()), false),
        (
            seam_desc(None, CommitBinding::Bound(lanes(ANCHOR_BASE))),
            false,
        ),
    ];
    for (d, want) in cases {
        let binds: Vec<&ProofBindSpec> = d
            .constraints
            .iter()
            .filter_map(|c| match c {
                VmConstraint2::ProofBind(m) => Some(m),
                _ => None,
            })
            .collect();
        assert_eq!(binds.len(), 1);
        assert_eq!(
            binds[0].is_declarative(),
            want,
            "is_declarative disagreed for {}",
            d.name
        );
    }
}

// ═══════════════════════════════════════════════════════════════════════════════════════════
// ⚑ THE WIDENING'S OWN POLARITY — what a seam tie is worth now
// ═══════════════════════════════════════════════════════════════════════════════════════════

/// ⚑⚑ **A SEVEN-OF-EIGHT FORGERY: PROVED BEFORE, REFUSED AFTER.**
///
/// The row's commitment agrees with the object it claims to be on SEVEN lanes and differs on lane 3.
/// Under `limb0_only` — the retired one-felt tie, reconstructed in the widened IR — it PROVES: that
/// seam ties lane 0, lane 0 is honest, and the other seven congruences compare a column to itself.
/// Under the real eight-lane pin it is REFUSED.
///
/// This is the number the widening bought, measured rather than asserted: forging a commitment past
/// the retired seam meant matching ONE felt (`2^31` offline, seconds on a laptop); past this one it
/// means matching all eight lanes of the digest — `2^123.6` birthday, `~2^247` second-preimage,
/// which is the class `PROOF_BIND_COMMIT_WIDTH = 8` was chosen for and the class the rest of the
/// stack's ~124-bit bar demands.
#[test]
fn a_seven_of_eight_commitment_forgery_proves_at_one_felt_and_is_refused_at_eight() {
    let trace = row(
        1,
        moved(HONEST_COMMIT, 3, 999_999),
        DECLARED_VK,
        HONEST_COMMIT,
    );
    let reason = proved_before_refused_after(
        "a commitment that agrees on seven of eight lanes",
        &limb0_only(),
        &pinned(),
        &trace,
    );
    eprintln!("seven-of-eight commitment forgery: {reason}");
}

/// ⚑⚑ **A HIGH-LANE PROGRAM SWAP: PROVED BEFORE, REFUSED AFTER.** Same shape on the VK half — the
/// attested program agrees with the declared fingerprint on lane 0 and differs on lane 7. The
/// retired seam pinned lane 0 and could not see it.
#[test]
fn a_high_lane_program_swap_proves_at_one_felt_and_is_refused_at_eight() {
    let trace = row(
        1,
        HONEST_COMMIT,
        moved(DECLARED_VK, 7, 0xdead),
        HONEST_COMMIT,
    );
    let reason = proved_before_refused_after(
        "a program fingerprint that agrees on lane 0 and differs on lane 7",
        &limb0_only_vk_swapped(),
        &pinned(),
        &trace,
    );
    eprintln!("high-lane program swap: {reason}");
}

/// The BEFORE pole for the high-lane swap: a seam whose VK pin names the FORGED lane-7 value (the
/// prover's choice) while everything else matches — i.e. a descriptor that did not pin lane 7,
/// reconstructed as a pin the forger could satisfy. Under the real pin lane 7 is `DECLARED_VK[7]`.
fn limb0_only_vk_swapped() -> EffectVmDescriptor2 {
    seam_desc(
        Some(moved(DECLARED_VK, 7, 0xdead).to_vec()),
        CommitBinding::Bound(lanes(ANCHOR_BASE)),
    )
}

/// ⚑ **A NARROW SEAM CANNOT BE BUILT AT ALL.** The retired one-felt shape is refused by
/// `check_descriptor2` before any prover sees it — the containment is structurally unshippable
/// rather than merely discouraged.
#[test]
fn a_narrow_seam_is_refused_by_the_descriptor_check() {
    use dregg_circuit::descriptor_ir2::check_descriptor2_wellformed;
    let mut d = pinned();
    if let VmConstraint2::ProofBind(m) = &mut d.constraints[0] {
        m.commit.truncate(1);
        m.vk.truncate(1);
        m.vk_pin = Some(vec![DECLARED_VK[0]]);
        m.bound = CommitBinding::Bound(vec![LeanExpr::Var(ANCHOR_BASE)]);
    }
    let err = check_descriptor2_wellformed(&d).expect_err("a one-lane seam must be refused");
    assert!(
        err.contains("below the floor"),
        "the refusal must name the lane floor, got: {err}"
    );
}

/// ⚑ **AND A TRUNCATED PIN CANNOT EITHER.** Eight lanes with a four-lane `vk_pin` is not "pin the
/// prefix"; it is a seam that would check half its object.
#[test]
fn a_truncated_pin_is_refused_by_the_descriptor_check() {
    use dregg_circuit::descriptor_ir2::check_descriptor2_wellformed;
    let mut d = pinned();
    if let VmConstraint2::ProofBind(m) = &mut d.constraints[0] {
        m.vk_pin = Some(DECLARED_VK[..4].to_vec());
    }
    let err = check_descriptor2_wellformed(&d).expect_err("a truncated pin must be refused");
    assert!(
        err.contains("not a prefix"),
        "the refusal must name the truncation, got: {err}"
    );
}
