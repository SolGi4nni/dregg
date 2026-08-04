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
    EffectVmDescriptor2, MemBoundaryWitness, ProofBindSpec, TableDef2, TableSem, VmConstraint2,
    prove_vm_descriptor2, verify_vm_descriptor2,
};
use dregg_circuit::heap_root::HeapLeaf;
use dregg_circuit::lean_descriptor_air::LeanExpr;
use dregg_circuit::refusal;

/// Trace column layout of the synthetic seam descriptor — the same three roles the deployed
/// `customProofBind` names (`sel::CUSTOM`, `custom_proof_commitment`, `custom_program_vk_hash`),
/// plus one column standing for the row-derived object a light-client fold's `bound` would be.
const GUARD: usize = 0;
const COMMIT: usize = 1;
const VK: usize = 2;
/// The row-local object the commitment must equal. In a landed fold this is the in-AIR anchor
/// digest; here it is a plain column so the tooth measures the SEAM and not a hash gadget.
const ANCHOR: usize = 3;

const WIDTH: usize = 4;
const ROWS: usize = 8;

/// The program VK limb the pinned descriptor declares. Arbitrary but FIXED — the whole content of
/// `vk_pin` is that the prover cannot choose it.
const DECLARED_VK: i64 = 0x5eed_51;

fn felt(v: i64) -> BabyBear {
    BabyBear::new(v.rem_euclid(2_013_265_921) as u32)
}

/// The seam descriptor, parameterised by the two declared halves. `(None, None)` is the shape every
/// `proof_bind` in the tree carried before 2026-08-04 and is the BEFORE pole of every tooth here.
fn seam_desc(vk_pin: Option<i64>, bound: Option<LeanExpr>) -> EffectVmDescriptor2 {
    EffectVmDescriptor2 {
        name: "ir2-proof-bind-seam".into(),
        trace_width: WIDTH,
        public_input_count: 0,
        tables: vec![TableDef2 {
            id: 0,
            name: "main".into(),
            arity: WIDTH,
            sem: TableSem::Main,
        }],
        constraints: vec![VmConstraint2::ProofBind(ProofBindSpec {
            guard: LeanExpr::Var(GUARD),
            commit: LeanExpr::Var(COMMIT),
            vk: LeanExpr::Var(VK),
            vk_pin,
            bound,
        })],
        hash_sites: vec![],
        ranges: vec![],
    }
}

/// The DECLARATIVE seam — both halves `null`. This is the object the whole tree shipped.
fn declarative() -> EffectVmDescriptor2 {
    seam_desc(None, None)
}

/// The PINNED seam — the program is `DECLARED_VK` and the commitment must equal the row's anchor.
fn pinned() -> EffectVmDescriptor2 {
    seam_desc(Some(DECLARED_VK), Some(LeanExpr::Var(ANCHOR)))
}

fn row(guard: i64, commit: i64, vk: i64, anchor: i64) -> Vec<Vec<BabyBear>> {
    let cells = [guard, commit, vk, anchor];
    let r: Vec<BabyBear> = cells.iter().map(|&v| felt(v)).collect();
    vec![r; ROWS]
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
    let trace = row(1, 777, DECLARED_VK, 42);
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
    let trace = row(1, 42, DECLARED_VK + 1, 42);
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
    let trace = row(2, 42, DECLARED_VK, 42);
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
        prove_and_verify(&pinned(), &row(1, 42, DECLARED_VK, 42))
    });
}

/// An INACTIVE row (guard `0`) proves under the pinned seam with a junk commitment and a junk vk —
/// the seam is genuinely guarded and does not force the columns of rows it does not claim. Every
/// deployed descriptor has such rows (the Custom selector is off on transfer rows), so a seam that
/// forced them would be uncompletable rather than sound.
#[test]
fn an_inactive_row_is_not_constrained_by_the_seam() {
    refusal::must_accept("an inactive seam row carrying junk", || {
        prove_and_verify(&pinned(), &row(0, 999_999, 12_345, 42))
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
    let d2 = enc(&seam_desc(Some(DECLARED_VK), None)).expect("vk-only encodes");
    let d3 = enc(&seam_desc(None, Some(LeanExpr::Var(ANCHOR)))).expect("bound-only encodes");
    for (a, an, b, bn) in [
        (&d0, "declarative", &d1, "pinned"),
        (&d0, "declarative", &d2, "vk-pin only"),
        (&d0, "declarative", &d3, "bound only"),
        (&d1, "pinned", &d2, "vk-pin only"),
        (&d1, "pinned", &d3, "bound only"),
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
        (seam_desc(Some(DECLARED_VK), None), false),
        (seam_desc(None, Some(LeanExpr::Var(ANCHOR))), false),
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
