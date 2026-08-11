//! ⚑⚑ **THE CHUNK RANGE GATES ON THE DEPLOYED PROVER — AND THE REFUSAL IS THE AIR'S.**
//!
//! `Dregg2.Circuit.Emit.MinaBodyPreimageBitsAir` authors `dregg-mina-body-preimage-bits::v1` in
//! Lean (House Law #1 — not one `VmConstraint2` is written in Rust) and proves both polarities on
//! its source predicate. This file runs the SAME object through the deployed IR-v2 prover, so the
//! refusal below is the constraint system's verdict and not a Lean statement about it.
//!
//! ## ⚑ THE HOLE IT CLOSES, IN ONE LINE
//!
//! `Bridge.MinaPackInjective.the_range_hypothesis_is_load_bearing`:
//!
//! ```text
//! packToFields ⟨[], [(1,1),(0,1)]⟩ = [2] = packToFields ⟨[], [(0,1),(2,1)]⟩
//! ```
//!
//! Two different bodies, the SAME 49 absorbed field elements, therefore the same `state_body_hash`,
//! the same 25-link chain, the same root — **and every link honest.** §2's forgery is the left half
//! of that alias on the real block: a one-bit chunk carrying `2`.
//!
//! ## ⚑ COMMITTED WIDTH — and the 1.00× headline is RETIRED, not carried forward
//!
//! `MainLayout::build` appends `decomp_cols(bits)` columns per RANGE lookup. On 2026-08-08 this
//! descriptor gated only the 819 chunk bits — a booleanity assertion is a degree-2 window gate, not
//! a bus query — so it declared no table, emitted no lookup, and measured **2 683 declared → 2 683
//! committed, 1.00×**. **That number is dead.** The 2026-08-09 rung gave the OTHER half of the
//! preimage — the 38 whole field elements — `SK = 32` base-256 limb columns each under one `.limbs`
//! leg at `bits := 8`, and §0 now measures **3 899 declared → 6 331 committed, 1.62×**, on a bill
//! of `NFIELD × SK = 1 216` eight-bit range lookups at `decomp_cols(8) = 2` aux columns each.
//! That is the descriptor's ENTIRE lookup bill; the 819 chunks still cost zero.
//!
//! ## ⚑ THE FLAG DAY THIS FILE FOLLOWS
//!
//! `trace_width` **2 683 → 3 899**, `piCount` **302 → 1 518**, `tables` `[] → [range_w8]`,
//! constraints **2 985 → 5 417**. The PI vector is now the **ABSORB ORDER** — `[0, 1216)` the 38
//! whole field elements, `[1216, 1518)` the packed ones — so **`PI_PLIMB` MOVED by +1216** and the
//! claim is no longer a suffix of the row but a REORDERING of two row slices. The old shape refuses
//! to load rather than being reinterpreted: `prove_vm_descriptor2` rejects both a 2 683-wide trace
//! and a 302-slot PI vector against this descriptor.
//!
//! ## PREREQUISITE — the witness row AND its claim
//!
//! Rust does not decode a Mina protocol state; a Rust-side reconstruction of the 2 381 bits or the
//! 38 field elements would be a twin. Both files are Lean's own
//! (`MinaBodyPreimageBitsAir.realRow` / `.realPub`), TRACKED, and regenerated with:
//!
//! ```text
//! cd metatheory && lake env lean --run MinaBodyBitsEmit.lean ../circuit/tests/fixtures
//! ```
//!
//! §0b asserts the two agree — the emitted CLAIM against the emitted ROW's two reordered slices —
//! which is a real cross-check of two Lean functions over one layout, and is why this file does not
//! carry a Rust slice as the source of truth.
//!
//! ## ⚠ WHY THE 2026-08-08 "NEVER RUN" NOTE IS GONE
//!
//! It said the workspace did not build because `dregg-lean-ffi`'s release gate refused a stale
//! verified runtime. Measured again 2026-08-10: the build script's `metatheory_dir()` /
//! `lean_sysroot()` resolution had gone stale in a cached build-script binary, and both are
//! runtime-overridable. This file runs under
//! `DREGG_METATHEORY_DIR=<repo>/metatheory DREGG_LEAN_SYSROOT=$(lean --print-prefix)`.
//!
//! ⚠ Read the COUNT, not the exit code: an `exit 0` with no `test result:` line means nothing ran.
//!
//! Run: `cargo test -p dregg-circuit --release --test mina_body_preimage_bits_proves -- --nocapture`

use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, MemBoundaryWitness, TableSem, VmConstraint2, decomp_cols_pub,
    parse_vm_descriptor2, prove_vm_descriptor2, prove_vm_descriptor2_unchecked,
    verify_vm_descriptor2,
};
use dregg_circuit::field::BabyBear;
use dregg_circuit::refusal::assert_violated_constraint_not_bus;

/// Assert a refusal is the constraint system's own.
///
/// ⚑ **THE POSITIVE CLAUSE WAS MISSING UNTIL 2026-08-09.** The teeth here used to assert only
/// that the error did NOT name the ROM or a producer replay — and a pair of negatives is
/// satisfied by every error string there is. `prove_and_verify_adversarial` is
/// `prove_vm_descriptor2_unchecked(..)?` then `verify_vm_descriptor2`, and the `?` hands back
/// any prove-side `Err` in the same `String` the verifier's verdict uses. `check: false` gates
/// the pre-flight replay and the `verify_batch` self-check, which is why the forgery reaches the
/// circuit at all — but `check_descriptor2` and the trace/PI SHAPE pre-flight still run and still
/// return `Err` before one witness cell is read. Requiring a `CONSTRAINT_REFUSAL_MARKERS` verdict
/// (`OodEvaluationMismatch`, every profile; or p3's debug `constraints not satisfied on row`)
/// makes a shape fault RED. Measured in `--release`: both teeth refuse with
/// `OodEvaluationMismatch { index: Some(0) }`.
fn assert_air_refusal(err: &str) {
    assert!(
        !err.contains("exact-public"),
        "no table is declared, so the refusal cannot be a ROM verdict; got: {err}"
    );
    assert!(
        !err.contains("pre-flight") && !err.contains("replay"),
        "the refusal must be the constraint system's, not a producer pre-flight; got: {err}"
    );
    assert_violated_constraint_not_bus("body-preimage-bits forgery", err);
}

const BITS_JSON: &str =
    include_str!("../descriptors/by-name/dregg-mina-body-preimage-bits-v1.json");
const ROW_TXT: &str = include_str!("fixtures/mina-body-preimage-bits-row.txt");
/// ⚑ The Lean-emitted CLAIM (`MinaBodyPreimageBitsAir.realPub`), tracked since 2026-08-10. It is
/// NOT derivable from the row by a tail slice any more — see §0b.
const PIS_TXT: &str = include_str!("fixtures/mina-body-preimage-bits-pis.txt");

/// `MinaBodyPreimageBitsAir.NBITS` — the packed half of `Body.to_input`.
const NBITS: usize = 2381;
/// `MinaBodyPreimageBitsAir.NLIMB` — `Σ ⌈W_e/8⌉` over the eleven packed runs.
const NLIMB: usize = 302;
/// `MinaBodyPreimageBitsAir.NFIELD` — the whole field elements `packToFields` prepends untouched.
const NFIELD: usize = 38;
/// `MinaBodyPreimageBitsAir.SK` — base-256 limbs per whole field element.
const SK: usize = 32;
/// `MinaBodyPreimageBitsAir.NFLIMB`.
const NFLIMB: usize = NFIELD * SK;
const WIDTH: usize = NBITS + NLIMB + NFLIMB;
/// `MinaBodyPreimageBitsAir.BODY_BITS_PI_COUNT`.
const PI_COUNT: usize = NFLIMB + NLIMB;
/// `MinaBodyPreimageBitsAir.FALSIFIER_BIT` — the FIRST `1` in the real block's chunk stream.
const FALSIFIER_BIT: usize = 23;

fn bits_desc() -> EffectVmDescriptor2 {
    parse_vm_descriptor2(BITS_JSON).expect("the Lean body-preimage-bits descriptor parses")
}

fn decimals(text: &str, want: usize, what: &str) -> Vec<BabyBear> {
    let v: Vec<BabyBear> = text
        .split_whitespace()
        .map(|c| BabyBear::new(c.parse::<u32>().expect("cell is a u32 decimal")))
        .collect();
    assert_eq!(
        v.len(),
        want,
        "the Lean-emitted {what} is {want} cells; re-emit it with \
         `cd metatheory && lake env lean --run MinaBodyBitsEmit.lean ../circuit/tests/fixtures`"
    );
    v
}

/// The honest row, as Lean emitted it.
fn honest_row() -> Vec<BabyBear> {
    decimals(ROW_TXT, WIDTH, "row")
}

/// ⚑ **THE CLAIM, AS LEAN EMITTED IT.** `realPub`'s own output — not a Rust slice of the row.
fn honest_pis() -> Vec<BabyBear> {
    decimals(PIS_TXT, PI_COUNT, "claim")
}

/// The claim a given row publishes: the 38 whole field elements' limbs FIRST, then the eleven
/// packed elements' — the ABSORB order the 2026-08-09 flag day installed.
///
/// ⚠ This is used to move the claim WITH a forged row, never as the source of truth for the honest
/// one; §0b is what pins it to `realPub`.
fn claim_of(row: &[BabyBear]) -> Vec<BabyBear> {
    let mut pis = Vec::with_capacity(PI_COUNT);
    pis.extend_from_slice(&row[NBITS + NLIMB..WIDTH]);
    pis.extend_from_slice(&row[NBITS..NBITS + NLIMB]);
    pis
}

/// A power-of-two trace: the real row, then zero padding. ⚑ A zero row satisfies every gate — the
/// booleanity legs because `0·(0−1) = 0`, the limb legs because an all-zero byte composes to zero —
/// which is why the boolean pin is `.all` rather than `.first` and costs nothing on the pad.
fn trace_from(row: Vec<BabyBear>, rows: usize) -> Vec<Vec<BabyBear>> {
    assert!(rows.is_power_of_two() && rows >= 2);
    let mut t = vec![row];
    while t.len() < rows {
        t.push(vec![BabyBear::new(0); WIDTH]);
    }
    t
}

/// `mina_accumulator_leaf_anatomy.rs`'s helper, verbatim in intent: declared width plus the nibble
/// aux block `MainLayout::build` appends per declared range lookup.
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

// ============================================================================
// §0 — THE SHAPE AND THE COMMITTED WIDTH. Cheap, unconditional.
// ============================================================================

/// ⚑ The emitted bytes are the shape Lean pins (`bodyBitsDesc_width` / `_piCount` /
/// `_constraint_count`), and — the measurement this rung exists to report — **the field gate's
/// 1 216 eight-bit lookups are the descriptor's entire lookup bill.**
#[test]
fn the_field_gate_is_the_whole_lookup_bill_and_the_chunk_gates_are_free() {
    let d = bits_desc();
    assert_eq!(d.name, "dregg-mina-body-preimage-bits::v1");
    assert_eq!(
        d.trace_width, WIDTH,
        "2 381 bit + 302 packed-limb + 1 216 field-limb columns"
    );
    assert_eq!(
        d.public_input_count, PI_COUNT,
        "the 38 whole field elements' limbs, then the eleven packed blocks"
    );
    assert_eq!(d.constraints.len(), 5417, "gates + pins + the field limbs");
    assert_eq!(
        d.tables.len(),
        1,
        "ONE table — the `range_w8` the `.limbs` leg queries"
    );

    let (declared, committed, range_lookups) = committed_width(&d);
    assert_eq!(
        range_lookups,
        NFIELD * SK,
        "one eight-bit lookup per whole-field limb, and NOT ONE for the 819 chunks — a booleanity \
         assertion is a degree-2 window gate, not a bus query"
    );
    assert_eq!(declared, WIDTH);
    assert_eq!(
        committed,
        WIDTH + 2 * NFIELD * SK,
        "`decomp_cols(8) = 2` aux columns per range lookup"
    );
    assert_eq!(committed, 6331);
    // ⚑ THE HEADLINE THAT WAS RETIRED, asserted as retired rather than deleted quietly.
    assert_ne!(
        declared, committed,
        "the 2026-08-08 `1.00×` result is DEAD: this descriptor now pays an aux block"
    );

    // The two rungs it is measured against, from their own emitted bytes.
    let chainlink = parse_vm_descriptor2(include_str!(
        "../descriptors/by-name/pasta-fp-chainlink.json"
    ))
    .expect("the deployed Fp chain-link descriptor parses");
    let (cd, cc, cr) = committed_width(&chainlink);
    assert!(
        cr > 0 && cc > cd,
        "the chain link DOES pay a nibble aux block"
    );

    println!("\n═══ §0  COMMITTED WIDTH — the unit that binds ═══");
    println!(
        "  dregg-mina-body-preimage-bits::v1 : {declared} declared → {committed} committed ({:.2}×), {range_lookups} range lookups",
        committed as f64 / declared as f64
    );
    println!(
        "  dregg-pasta-fp-chainlink::v1      : {cd} declared → {cc} committed ({:.2}×), {cr} range lookups",
        cc as f64 / cd as f64
    );
    println!("  ⚑ 1 216 = NFIELD × SK is the ENTIRE bill; the 819 chunk gates still cost zero.");
}

/// ⚑⚑ **§0b — THE EMITTED CLAIM IS THE EMITTED ROW, REORDERED.** Two Lean functions (`realPub`
/// and `realRow`) over one layout, compared on the wire.
///
/// ⚠ This is the assertion that keeps `claim_of` honest. The 2026-08-09 flag day moved `PI_PLIMB`
/// by `+1216`, so the claim stopped being the row's tail; a consumer that kept slicing the tail
/// reads field element 38's limbs and every value still looks like a plausible byte.
#[test]
fn the_emitted_claim_is_the_emitted_row_in_absorb_order() {
    let row = honest_row();
    let pis = honest_pis();
    assert_eq!(pis, claim_of(&row), "realPub and realRow disagree");

    // The two blocks, named at their new bases.
    assert_eq!(&pis[..NFLIMB], &row[NBITS + NLIMB..WIDTH]);
    assert_eq!(&pis[NFLIMB..], &row[NBITS..NBITS + NLIMB]);
    // ⚑ And the OLD reading is not merely different — it is WRONG AND PLAUSIBLE, which is why the
    // flag day needed a refusal rather than a note.
    assert_ne!(
        &pis[..NLIMB],
        &row[NBITS..NBITS + NLIMB],
        "the pre-flag-day base must no longer land on the packed limbs"
    );

    // Every published limb is a byte — a consequence of the gates, checked on the witness.
    assert!(
        pis.iter().all(|v| v.as_u32() < 256),
        "a published limb is a byte: eight boolean bits, or a `range_w8` query"
    );
    // …and every bit column really is a bit.
    assert!(
        row[..NBITS].iter().all(|v| v.as_u32() <= 1),
        "the honest row's bit columns are boolean"
    );
}

// ============================================================================
// §1 — THE HONEST ROW PROVES, on the CHECKED rail.
// ============================================================================

/// ⚑⚑ **THE REAL BLOCK'S PACKED PREIMAGE PROVES.** Asserted FIRST so every refusal below is about
/// the forgery and not about the rail.
#[test]
fn the_real_body_preimage_proves() {
    let d = bits_desc();
    let row = honest_row();
    let pis = honest_pis();
    let t = trace_from(row, 2);

    let proof = prove_vm_descriptor2(&d, &t, &pis, &MemBoundaryWitness::default(), &[])
        .expect("the real block's packed preimage MUST prove");
    verify_vm_descriptor2(&d, &proof, &pis).expect("…and verify");

    println!("\n§1 ⚑⚑ the real devnet block's 2 381 packed-preimage bits PROVE and VERIFY.");
}

// ============================================================================
// §2 — BOTH POLARITIES. The refusing gate is the AIR's.
// ============================================================================

/// ⚑⚑ **THE FORGERY: A ONE-BIT CHUNK CARRYING `2`** — the left half of
/// `MinaPackInjective.the_range_hypothesis_is_load_bearing`, on the real block.
///
/// Three properties of the falsifier, each of which a sibling lane's first draft got wrong:
///
/// * bit column 23 is the FIRST `1` in the stream, so the mutation moves a **NON-ZERO** value —
///   not the zero-into-zero mutation `decide` cheerfully proves is not a tamper;
/// * the value it moves to is a valid BabyBear element, so no field-range check can be what refuses;
/// * **nothing else moves** — the other 2 682 cells and all 302 public inputs are the honest row's,
///   so the refusal cannot come from a pre-existing pin.
#[test]
fn an_over_wide_chunk_bit_is_refused_by_the_air() {
    let d = bits_desc();
    let honest = honest_row();
    let pis = honest_pis();

    assert_eq!(
        honest[FALSIFIER_BIT].as_u32(),
        1,
        "the falsifier must move a NON-ZERO bit, or it is a tautology about an unchanged row"
    );
    let mut forged = honest.clone();
    forged[FALSIFIER_BIT] = BabyBear::new(2);
    assert_ne!(
        forged[FALSIFIER_BIT].as_u32(),
        honest[FALSIFIER_BIT].as_u32(),
        "the falsifier must MOVE"
    );
    assert_eq!(
        &forged[NBITS..],
        &honest[NBITS..],
        "the PUBLISHED limbs must be untouched — the forgery is the bit, not the claim"
    );

    let err = prove_and_verify_adversarial(&d, &trace_from(forged, 2), &pis)
        .expect_err("a one-bit chunk carrying 2 must be REFUSED");
    println!("\n§2 ⚑⚑ OVER-WIDE CHUNK BIT REFUSED BY THE AIR: {err}");
    assert_air_refusal(&err);

    // …and the CHECKED rail refuses it too.
    prove_vm_descriptor2(
        &d,
        &trace_from(honest_row(), 2),
        &pis,
        &MemBoundaryWitness::default(),
        &[],
    )
    .expect("the honest row still proves on the checked rail");
    let mut forged2 = honest_row();
    forged2[FALSIFIER_BIT] = BabyBear::new(2);
    assert!(
        prove_vm_descriptor2(
            &d,
            &trace_from(forged2, 2),
            &pis,
            &MemBoundaryWitness::default(),
            &[]
        )
        .is_err(),
        "the checked rail must refuse it as well"
    );
}

/// ⚑ **AND A PUBLISHED LIMB THAT IS NOT WHAT ITS BITS COMPOSE IS REFUSED.** Move the first limb by
/// one — in both the trace and the PI vector, so the pin is satisfied and only the COMPOSITION gate
/// is false. ⚠ Without this half the booleanity would be a gate on columns nobody reads.
#[test]
fn a_limb_that_is_not_its_bits_is_refused_by_the_air() {
    let d = bits_desc();
    let honest = honest_row();

    let mut forged = honest.clone();
    let before = forged[NBITS].as_u32();
    forged[NBITS] = BabyBear::new(before + 1);
    assert_ne!(forged[NBITS].as_u32(), before, "the falsifier must MOVE");
    assert!(
        honest[..NBITS] == forged[..NBITS],
        "not one bit moves — only the published limb"
    );
    let pis = claim_of(&forged);

    let err = prove_and_verify_adversarial(&d, &trace_from(forged, 2), &pis)
        .expect_err("a limb that is not the composition of its bits must be REFUSED");
    println!("\n§2b ⚑ MIS-COMPOSED LIMB REFUSED BY THE AIR: {err}");
    assert_air_refusal(&err);
}

/// ⚑⚑ **§2c — AN OVER-WIDE *FIELD* LIMB IS REFUSED BY THE `range_w8` LOOKUP.** The tooth for the
/// half the 2026-08-09 rung added and which had none: the 38 whole field elements are gated by ONE
/// `.limbs` leg at `bits := 8`, and that is `the_field_gate_bounds_every_whole_element_limb`'s
/// entire content — *a row this descriptor accepts publishes 38 values below `2^256`*, which is
/// exactly `Seam.Renders`' canonicality hypothesis and exactly what an elementwise 32-limb weld
/// needs to carry a whole value with no digest.
///
/// Three properties of the falsifier:
///
/// * it moves a **NON-ZERO** limb (asserted, not assumed) to `256` — the first value the table
///   does not contain, so the gate is tested at its boundary and not at a wild value;
/// * `256` is a perfectly valid BabyBear element, so no FIELD-range check can be what refuses it;
/// * the limb moves in the ROW **and** in the CLAIM, so the pin leg is satisfied and the ONLY
///   false thing is the range query. Without that, this would be a tooth about a pin.
///
/// ⚠⚠ **AND THE REFUSAL IS THE PRODUCER'S, NOT THE VERIFIER'S — SAID AT THAT RESOLUTION.**
/// The first draft of this tooth asserted `assert_bus_imbalance_not_constraint` and went RED, which
/// is the useful outcome: the measured refusal is
///
/// ```text
/// row 0: range wire 2683 value 256 >= 2^8
/// ```
///
/// i.e. the RANGE-DECOMPOSITION WITNESS GENERATOR refusing to decompose a value the eight-bit table
/// cannot hold. `prove_vm_descriptor2_unchecked`'s `check: false` disables the producer REPLAY and
/// the `verify_batch` self-check, but it does not disable witness generation, and there is no aux
/// block for an out-of-range value — so the forgery never reaches a verifier verdict on this rail.
///
/// **What this tooth therefore claims, exactly:** the 38 whole field elements really are gated by a
/// `range_w8` query at the columns `FLIMB f k` names — a descriptor whose `.limbs` leg went missing
/// would prove this row happily — and the refusal is at the FIRST field-limb column, `2683`, which
/// is `NBITS + NLIMB`. **What it does NOT claim:** that the deployed verifier refuses an over-wide
/// limb. Reaching that verdict needs a hand-crafted aux block this harness does not mint, and
/// calling a producer refusal an AIR verdict is the substitution this cone keeps paying for.
#[test]
fn an_over_wide_field_limb_is_refused_by_the_range_decomposition() {
    let d = bits_desc();
    let honest = honest_row();

    // The first whole-field limb column, `FLIMB 0 0`.
    let col = NBITS + NLIMB;
    let before = honest[col].as_u32();
    assert_ne!(
        before, 0,
        "the falsifier must move a NON-ZERO limb, or it is a tautology about an unchanged row"
    );
    let mut forged = honest.clone();
    forged[col] = BabyBear::new(256);
    assert_ne!(forged[col].as_u32(), before, "the falsifier must MOVE");
    assert!(
        forged[col].as_u32() >= 256,
        "the point of this tooth is a limb OUTSIDE the eight-bit table"
    );
    assert_eq!(
        &forged[..col],
        &honest[..col],
        "not one bit and not one packed limb moves — only the field limb"
    );

    // The claim moves WITH the row, so the pin leg is satisfied and only the query is false.
    let pis = claim_of(&forged);
    assert_eq!(pis[0].as_u32(), 256, "the claim carries the over-wide limb");

    let err = prove_and_verify_adversarial(&d, &trace_from(forged, 2), &pis)
        .expect_err("a whole-field limb of 256 must be REFUSED by the eight-bit range gate");
    println!("\n§2c ⚑⚑ OVER-WIDE FIELD LIMB REFUSED BY THE RANGE DECOMPOSITION: {err}");
    // ⚑ The POSITIVE clause: the refusal names the range gate AND the column. A bare `is_err()`
    // here would be satisfied by a shape fault, an OOM or a parse failure just as readily.
    assert!(
        err.contains("range wire"),
        "the refusal must be the RANGE gate's — a descriptor whose `.limbs` leg went missing would \
         prove this row, and any other error means this tooth is measuring something else; got: \
         {err}"
    );
    assert!(
        err.contains(&format!("range wire {col} ")),
        "the refusal must name the FIRST WHOLE-FIELD limb column ({col} = NBITS + NLIMB); a \
         refusal at another column would mean the mutation landed somewhere else; got: {err}"
    );
    // …and it is NOT a shape fault: the trace and the claim are both the declared width.
    assert!(
        dregg_circuit::refusal::shape_fault(&err).is_none(),
        "a geometry complaint is the prover rejecting the trace's SHAPE, not this gate; got: {err}"
    );
    // ⚑ THE CONTROL. The same rail admits the honest row, so the refusal is the mutation.
    prove_and_verify_adversarial(&d, &trace_from(honest_row(), 2), &honest_pis())
        .expect("the honest row is admitted on the very same rail");
}

/// ⚑ **AND THE OLD-ADMITS-NEW-REJECTS PAIR, AS ONE STATEMENT.**
#[test]
fn body_preimage_bits_discriminates() {
    let d = bits_desc();
    let honest = honest_row();
    let pis = honest_pis();

    assert!(
        prove_and_verify_adversarial(&d, &trace_from(honest.clone(), 2), &pis).is_ok(),
        "the honest row is admitted"
    );
    let mut forged = honest;
    forged[FALSIFIER_BIT] = BabyBear::new(2);
    // ⚑ Not a bare `is_err()` — that is satisfied by the prover's shape pre-flight as readily as
    // by the circuit, which is not the sentence this pair is written to support.
    let err = prove_and_verify_adversarial(&d, &trace_from(forged, 2), &pis)
        .expect_err("the over-wide chunk is rejected");
    assert_air_refusal(&err);
    println!("\n§3 ⚑ old admits / new rejects — on the emitted object, at the deployed prover.");
}
