//! ⚑⚑ **FIVE `verify_block` PREAMBLE LEGS ON THE DEPLOYED PROVER — AND THE REFUSAL IS THE AIR'S.**
//!
//! `Dregg2.Circuit.Emit.MinaPreambleLegsAir` authors `dregg-mina-preamble-legs::v1` in Lean
//! (House Law #1 — not one `VmConstraint2` is written in Rust) and proves both polarities on its
//! `PreambleRowOk` predicate. This file runs the SAME object through the deployed IR-v2 prover,
//! so every refusal below is the constraint system's verdict and not a Lean statement about it.
//!
//! ## ⚑ THE HOLE IT CLOSES, IN ONE LINE
//!
//! `docs/PICKLES-VERIFY-BLOCK-LEG-TABLE.md` §6 (2026-08-08): *"How many of upstream's legs does
//! dregg close BY CONSTRAINT? **Zero**."* — and the worked example was D1b: `shapeOkRec`'s
//! public-input conjunct `decide (0 < publicLen)` compared trusted config against zero and could
//! not fail, admitting an index declaring 41 public inputs against a 40-word packing, a pair the
//! VK digest cannot separate (`the_index_digest_cannot_see_the_circuit_shape`). §2 below is that
//! exact forgery, refused by an emitted polynomial: `PUB_LEN − IDX_PUBLIC = 0`.
//!
//! ## The five legs, and the gate that refuses each
//!
//! | leg | upstream | refusing gate |
//! |---|---|---|
//! | B1 non-chunking | `verification.rs:628` | `MAXLEN·(MAXLEN−1) = 0` |
//! | B1 non-empty walk | `nonChunking_nil`'s vacuous accept | `PAIR_COUNT·PAIR_INV − 1 = 0` |
//! | B3 step domain ≤ 16 | `verification.rs:648-651` | `DOMAIN_LOG2 + Σ2ⁱ·SBITᵢ − 16 = 0` |
//! | C3 packing length | `prepared_statement.rs:179` | `PUB_LEN − 24 − N_CHAL = 0` |
//! | D1a prev count | `verifier.rs:810-815` | `PROOF_PREV − IDX_PREV = 0` |
//! | D1b public length | `verifier.rs:816-820` | `PUB_LEN − IDX_PUBLIC = 0` |
//!
//! ## ⚠ WHERE THE FORCING LIVES — the AIR forces the RELATIONS; the BINDING of the eight
//! published slots to the real wire (`mina_pickles::WrapProofShape`'s counts, the pinned index
//! params) is the verifying host's, exactly the position `MinaBodyPreimageBitsAir`'s 302 limbs
//! are in. Publication makes a future fold weld reachable; the compiled gate
//! (`dregg_mina_wrap_shape_ok`) keeps running on the deployed path unchanged.
//!
//! ## PREREQUISITE — the witness row
//!
//! The row is Lean's own (`MinaPreambleLegsAir.realRow` — block 539508's preamble tuple as the
//! wire decoder measures it), TRACKED, regenerated with:
//!
//! ```text
//! cd metatheory && lake env lean --run MinaPreambleLegsEmit.lean ../circuit/tests/fixtures
//! ```
//!
//! Run: `cargo test -p dregg-circuit --release --test mina_preamble_legs_proves -- --nocapture`

use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, MemBoundaryWitness, TableSem, VmConstraint2, decomp_cols_pub,
    parse_vm_descriptor2, prove_vm_descriptor2, prove_vm_descriptor2_unchecked,
    verify_vm_descriptor2,
};
use dregg_circuit::field::BabyBear;

const LEGS_JSON: &str = include_str!("../descriptors/by-name/dregg-mina-preamble-legs-v1.json");
const ROW_TXT: &str = include_str!("fixtures/mina-preamble-legs-row.txt");

/// `MinaPreambleLegsAir.PREAMBLE_WIDTH`.
const WIDTH: usize = 30;
/// `MinaPreambleLegsAir.PREAMBLE_PI_COUNT` — PI slot `s` IS column `s`.
const NPI: usize = 8;

// Column indices, `MinaPreambleLegsAir` §1.
const PROOF_PREV: usize = 0;
const IDX_PREV: usize = 1;
const N_CHAL: usize = 2;
const PUB_LEN: usize = 3;
const IDX_PUBLIC: usize = 4;
const DOMAIN_LOG2: usize = 5;
const MAXLEN: usize = 6;
const PAIR_COUNT: usize = 7;
const DBIT0: usize = 14;
const NBIT0: usize = 9;
const CBIT0: usize = 24;

fn legs_desc() -> EffectVmDescriptor2 {
    parse_vm_descriptor2(LEGS_JSON).expect("the Lean preamble-legs descriptor parses")
}

/// The honest row, as Lean emitted it — the real block's preamble tuple.
fn honest_row() -> Vec<BabyBear> {
    let row: Vec<BabyBear> = ROW_TXT
        .split_whitespace()
        .map(|c| BabyBear::new(c.parse::<u32>().expect("cell is a u32 decimal")))
        .collect();
    assert_eq!(
        row.len(),
        WIDTH,
        "the Lean-emitted row is {WIDTH} cells; re-emit it with \
         `lake env lean --run MinaPreambleLegsEmit.lean ../circuit/tests/fixtures`"
    );
    row
}

/// The published slots ARE the first eight columns — one slice, no re-encoding.
fn public_inputs(row: &[BabyBear]) -> Vec<BabyBear> {
    row[..NPI].to_vec()
}

/// A power-of-two trace: the row, CLONED. ⚠ Not zero-padded: the schedule, equality and inverse
/// gates are `.all`-row and a zero row fails `PUB_LEN = 24 + N_CHAL` (0 ≠ 24) — deliberately, so
/// a padding row cannot smuggle a second, unchecked tuple.
fn trace_from(row: Vec<BabyBear>, rows: usize) -> Vec<Vec<BabyBear>> {
    assert!(rows.is_power_of_two() && rows >= 2);
    let mut t = vec![row.clone()];
    while t.len() < rows {
        t.push(row.clone());
    }
    t
}

/// Declared width plus the nibble aux block `MainLayout::build` appends per declared range
/// lookup — `mina_body_preimage_bits_proves.rs`'s helper, verbatim in intent.
fn committed_width(desc: &EffectVmDescriptor2) -> (usize, usize, usize) {
    let mut aux = 0usize;
    let mut range_lookups = 0usize;
    for c in &desc.constraints {
        if let VmConstraint2::Lookup(l) = c {
            if let Some(bits) =
                desc.tables
                    .iter()
                    .find(|t| t.id == l.table)
                    .and_then(|t| match t.sem {
                        TableSem::Range { bits } => Some(bits),
                        _ => None,
                    })
            {
                aux += decomp_cols_pub(bits);
                range_lookups += 1;
            }
        }
    }
    (desc.trace_width, desc.trace_width + aux, range_lookups)
}

fn prove_and_verify_adversarial(
    d: &EffectVmDescriptor2,
    t: &[Vec<BabyBear>],
    pis: &[BabyBear],
) -> Result<(), String> {
    let proof = prove_vm_descriptor2_unchecked(d, t, pis, &MemBoundaryWitness::default(), &[])?;
    verify_vm_descriptor2(d, &proof, pis)
}

/// Assert a refusal is the constraint system's own — not a ROM verdict, not a producer
/// pre-flight. This AIR declares no table, so no lookup can be the refusal either.
fn assert_air_refusal(err: &str) {
    assert!(
        !err.contains("exact-public"),
        "no table is declared, so the refusal cannot be a ROM verdict; got: {err}"
    );
    assert!(
        !err.contains("pre-flight") && !err.contains("replay"),
        "the refusal must be the constraint system's, not a producer pre-flight; got: {err}"
    );
}

// ============================================================================
// §0 — THE SHAPE AND THE COMMITTED WIDTH. Cheap, unconditional.
// ============================================================================

/// ⚑ The emitted bytes are the shape Lean pins (`preambleDesc_width` / `_piCount` /
/// `_constraint_count`), and — re-derived for THIS shape, as the campaign demands — **its aux
/// block is empty**: these legs are field-only booleanity and affine sums, no curve ops, so
/// neither the scheduled row's 4.60× leaf figure nor the 6.6× wrap figure has anything to touch.
#[test]
fn the_preamble_legs_declare_no_table_and_commit_what_they_declare() {
    let d = legs_desc();
    assert_eq!(d.name, "dregg-mina-preamble-legs::v1");
    assert_eq!(
        d.trace_width, WIDTH,
        "8 published + 1 inverse + 21 bit columns"
    );
    assert_eq!(d.public_input_count, NPI, "the eight-slot preamble tuple");
    assert_eq!(
        d.constraints.len(),
        38,
        "8 arithmetic + 22 booleanity + 8 pins"
    );
    assert!(
        d.tables.is_empty(),
        "a booleanity or affine gate is not a bus query; this descriptor declares NO table"
    );

    let (declared, committed, range_lookups) = committed_width(&d);
    assert_eq!(
        range_lookups, 0,
        "no range lookup, therefore no nibble aux block"
    );
    assert_eq!(
        declared, committed,
        "the committed row must equal the declared row — 1.00×, re-derived from the bytes"
    );
    assert_eq!(committed, WIDTH);

    println!("\n═══ §0  COMMITTED WIDTH — re-derived for this shape ═══");
    println!(
        "  dregg-mina-preamble-legs::v1 : {declared} declared → {committed} committed (1.00×), {range_lookups} range lookups"
    );
    println!("  field-only legs: booleanity + affine sums + one inverse product; no curve ops,");
    println!("  so the scheduled-row 4.60×/6.6× figures do not apply to this cone.");
}

/// ⚑ The published PI vector IS the row's first eight cells, and they are the real block's
/// preamble tuple — the numbers `mina_pickles::decode_proof_at` measures on the wire.
#[test]
fn the_public_inputs_are_the_preamble_tuple() {
    let row = honest_row();
    let pis = public_inputs(&row);
    assert_eq!(pis.len(), NPI);
    assert_eq!(&pis[..], &row[..NPI]);
    let expect: [(usize, u32, &str); 8] = [
        (PROOF_PREV, 2, "the proof's prev-challenge count"),
        (IDX_PREV, 2, "the index's declared prev_challenges"),
        (N_CHAL, 16, "BACKEND_TICK_ROUNDS_N bulletproof challenges"),
        (PUB_LEN, 40, "the packing length to_public_input produces"),
        (IDX_PUBLIC, 40, "the index's declared public"),
        (DOMAIN_LOG2, 16, "branch domain_log2 — B3's BOUNDARY case"),
        (MAXLEN, 1, "max prev_evals pair length"),
        (PAIR_COUNT, 43, "15 w + 15 coeff + z + 6 s + 6 selectors"),
    ];
    for (col, v, what) in expect {
        assert_eq!(pis[col].as_u32(), v, "{what}");
    }
}

// ============================================================================
// §1 — THE HONEST ROW PROVES, on the CHECKED rail.
// ============================================================================

/// ⚑⚑ **THE REAL BLOCK'S PREAMBLE TUPLE PROVES.** Asserted FIRST so every refusal below is
/// about the forgery and not about the rail. `domain_log2 = 16` is AT the B3 boundary — a bound
/// emitted as `< 16` would refuse every real Mina block right here.
#[test]
fn the_real_preamble_tuple_proves() {
    let d = legs_desc();
    let row = honest_row();
    let pis = public_inputs(&row);
    let t = trace_from(row, 2);

    let proof = prove_vm_descriptor2(&d, &t, &pis, &MemBoundaryWitness::default(), &[])
        .expect("the real block's preamble tuple MUST prove");
    verify_vm_descriptor2(&d, &proof, &pis).expect("…and verify");

    println!("\n§1 ⚑⚑ the real devnet block's preamble tuple PROVES and VERIFIES.");
}

// ============================================================================
// §2 — BOTH POLARITIES. Each refusing gate is the AIR's, and named.
// ============================================================================

/// ⚑⚑ **THE MARQUEE: THE 41-WORD INDEX IS REFUSED** — `IDX_PUBLIC` 40 → 41 in trace AND slot
/// (so the pin holds and the D1b equality gate `PUB_LEN − IDX_PUBLIC = 0` is what refuses).
/// This is `the_old_gate_admits_a_public_input_it_should_refuse`'s exact object: the old
/// `decide (0 < publicLen)` ACCEPTS it, the VK digest cannot see it, and the emitted polynomial
/// refuses it. The mutation moves a NON-ZERO value (40) to a valid BabyBear element (41).
#[test]
fn the_41_word_index_is_refused_by_the_air() {
    let d = legs_desc();
    let honest = honest_row();

    assert_eq!(
        honest[IDX_PUBLIC].as_u32(),
        40,
        "the falsifier must move a NON-ZERO value"
    );
    let mut forged = honest.clone();
    forged[IDX_PUBLIC] = BabyBear::new(41);
    assert_ne!(
        forged[IDX_PUBLIC].as_u32(),
        honest[IDX_PUBLIC].as_u32(),
        "…and must MOVE it"
    );
    let pis = public_inputs(&forged);

    let err = prove_and_verify_adversarial(&d, &trace_from(forged, 2), &pis).expect_err(
        "an index declaring 41 public inputs against a 16-challenge packing must be REFUSED",
    );
    println!("\n§2 ⚑⚑ THE 41-WORD INDEX REFUSED BY THE AIR (D1b equality gate): {err}");
    assert_air_refusal(&err);

    // …and the CHECKED rail refuses it too.
    let mut forged2 = honest_row();
    forged2[IDX_PUBLIC] = BabyBear::new(41);
    let pis2 = public_inputs(&forged2);
    assert!(
        prove_vm_descriptor2(
            &d,
            &trace_from(forged2, 2),
            &pis2,
            &MemBoundaryWitness::default(),
            &[]
        )
        .is_err(),
        "the checked rail must refuse it as well"
    );
}

/// ⚑ **A 17 STEP DOMAIN IS REFUSED — by the slack gate, i.e. the BOUND itself.** The mutation
/// moves `DOMAIN_LOG2` 16 → 17 AND its decomposition bits to 17's (`10001`) AND its slot — so
/// the decomposition gate and the pin both hold, and what refuses is
/// `DOMAIN_LOG2 + Σ2ⁱ·SBITᵢ − 16 = 0`: seventeen leaves the slack no in-range value. 17 fits
/// the 5 declared bits, and this AIR has no range table, so no lookup can be the refusal.
#[test]
fn a_17_step_domain_is_refused_by_the_air() {
    let d = legs_desc();
    let honest = honest_row();

    assert_eq!(
        honest[DOMAIN_LOG2].as_u32(),
        16,
        "the honest value is non-zero and AT the bound"
    );
    let mut forged = honest.clone();
    forged[DOMAIN_LOG2] = BabyBear::new(17);
    forged[DBIT0] = BabyBear::new(1); // 17 = 10001₂ — the decomposition gate stays satisfied
    let pis = public_inputs(&forged);

    let err = prove_and_verify_adversarial(&d, &trace_from(forged, 2), &pis)
        .expect_err("a step domain of 17 (> BACKEND_TICK_ROUNDS_N) must be REFUSED");
    println!("\n§2b ⚑ A 17 DOMAIN REFUSED BY THE AIR (the B3 slack gate): {err}");
    assert_air_refusal(&err);
}

/// ⚑ **A CHUNKED WALK SUMMARY IS REFUSED — by booleanity on `MAXLEN`.** `maxPairLen ≤ 1` IS
/// upstream's `non_chunking` (`maxPairLen_le_one_iff_nonChunking`); a summary of 2 has no row.
#[test]
fn a_chunked_walk_summary_is_refused_by_the_air() {
    let d = legs_desc();
    let honest = honest_row();

    assert_eq!(
        honest[MAXLEN].as_u32(),
        1,
        "the falsifier must move a NON-ZERO value"
    );
    let mut forged = honest.clone();
    forged[MAXLEN] = BabyBear::new(2);
    let pis = public_inputs(&forged);

    let err = prove_and_verify_adversarial(&d, &trace_from(forged, 2), &pis)
        .expect_err("a prev_evals walk with a length-2 vector must be REFUSED");
    println!("\n§2c ⚑ A CHUNKED SUMMARY REFUSED BY THE AIR (B1 booleanity): {err}");
    assert_air_refusal(&err);
}

/// ⚑ **THE EMPTY WALK IS REFUSED — by the inverse gate.** Upstream's `all` accepts an empty
/// `prev_evals` walk VACUOUSLY (`nonChunking_nil`); here `PAIR_COUNT = 0` makes
/// `PAIR_COUNT·PAIR_INV − 1 = 0` unsatisfiable for EVERY inverse value the prover could choose.
/// The mutation moves the non-zero 43 to 0 (bits zeroed so only the inverse gate refuses).
#[test]
fn an_empty_walk_is_refused_by_the_air() {
    let d = legs_desc();
    let honest = honest_row();

    assert_eq!(
        honest[PAIR_COUNT].as_u32(),
        43,
        "the falsifier must move a NON-ZERO value"
    );
    let mut forged = honest.clone();
    forged[PAIR_COUNT] = BabyBear::new(0);
    for i in 0..6 {
        forged[CBIT0 + i] = BabyBear::new(0);
    }
    let pis = public_inputs(&forged);

    let err = prove_and_verify_adversarial(&d, &trace_from(forged, 2), &pis)
        .expect_err("an empty prev_evals walk must be REFUSED, not vacuously accepted");
    println!("\n§2d ⚑ THE EMPTY WALK REFUSED BY THE AIR (the inverse gate): {err}");
    assert_air_refusal(&err);
}

/// **A MISMATCHED RECURSION COUNT IS REFUSED — by the D1a equality gate** (`verifier.rs:810-815`).
#[test]
fn a_mismatched_recursion_count_is_refused_by_the_air() {
    let d = legs_desc();
    let honest = honest_row();

    assert_eq!(
        honest[IDX_PREV].as_u32(),
        2,
        "the falsifier must move a NON-ZERO value"
    );
    let mut forged = honest.clone();
    forged[IDX_PREV] = BabyBear::new(1);
    let pis = public_inputs(&forged);

    let err = prove_and_verify_adversarial(&d, &trace_from(forged, 2), &pis).expect_err(
        "an index declaring 1 prev challenge against a proof carrying 2 must be REFUSED",
    );
    println!("\n§2e A MISMATCHED RECURSION COUNT REFUSED BY THE AIR (D1a): {err}");
    assert_air_refusal(&err);
}

/// ⚑ **ONE CHALLENGE SHORT IS REFUSED — by the C3 schedule gate.** `N_CHAL` 16 → 15 with its
/// bits moved to 15's (`01111`): the packing produces 24 + 15 = 39 words and the row still
/// claims 40, so `PUB_LEN − 24 − N_CHAL = 0` is what refuses — the produced length is COMPUTED
/// in-constraint, not accepted as a second opinion.
#[test]
fn one_challenge_short_is_refused_by_the_air() {
    let d = legs_desc();
    let honest = honest_row();

    assert_eq!(
        honest[N_CHAL].as_u32(),
        16,
        "the falsifier must move a NON-ZERO value"
    );
    let mut forged = honest.clone();
    forged[N_CHAL] = BabyBear::new(15);
    for i in 0..4 {
        forged[NBIT0 + i] = BabyBear::new(1); // 15 = 01111₂
    }
    forged[NBIT0 + 4] = BabyBear::new(0);
    let pis = public_inputs(&forged);

    let err = prove_and_verify_adversarial(&d, &trace_from(forged, 2), &pis)
        .expect_err("a 15-challenge packing against a public = 40 index must be REFUSED");
    println!("\n§2f ⚑ ONE CHALLENGE SHORT REFUSED BY THE AIR (the C3 schedule gate): {err}");
    assert_air_refusal(&err);
}

// ============================================================================
// §3 — old admits / new rejects, as one statement.
// ============================================================================

/// ⚑ The honest tuple is admitted and the marquee forgery is rejected — on the emitted object,
/// at the deployed prover. The old gate's verdict on the same pair was accept/accept
/// (`the_old_public_conjunct_could_not_fail_on_this_path`).
#[test]
fn preamble_legs_discriminate() {
    let d = legs_desc();
    let honest = honest_row();
    let pis = public_inputs(&honest);

    assert!(
        prove_and_verify_adversarial(&d, &trace_from(honest.clone(), 2), &pis).is_ok(),
        "the honest tuple is admitted"
    );
    let mut forged = honest;
    forged[IDX_PUBLIC] = BabyBear::new(41);
    let forged_pis = public_inputs(&forged);
    assert!(
        prove_and_verify_adversarial(&d, &trace_from(forged, 2), &forged_pis).is_err(),
        "the 41-word index is rejected"
    );
    println!("\n§3 ⚑ old admits / new rejects — on the emitted object, at the deployed prover.");
}
