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
//! ## ⚑ COMMITTED WIDTH — the unit that binds, and the brief expected the other answer
//!
//! `MainLayout::build` appends `decomp_cols(bits)` columns per RANGE lookup; range decomposition was
//! **71.7%** of the unnarrowed accumulator row. This descriptor declares **no table** and emits **no
//! lookup** — a booleanity assertion is a degree-2 window gate, not a bus query — so its aux block
//! is empty and §0 measures **2 683 declared → 2 683 committed, 1.00×**. Against
//! `dregg-pasta-fp-chainlink::v1`'s 469 → 1 037 (2.21×) and `dregg-mina-accumulator-seg::v1`'s
//! 3 048 → 10 756 (3.53×).
//!
//! ## PREREQUISITE — the witness row
//!
//! Rust does not decode a Mina protocol state; a Rust-side reconstruction of the 2 381 bits would be
//! a twin. The row is Lean's own (`MinaBodyPreimageBitsAir.realRow`), TRACKED, and regenerated with:
//!
//! ```text
//! cd metatheory && lake env lean --run MinaBodyBitsEmit.lean ../circuit/tests/fixtures
//! ```
//!
//! ## ⚠⚠ THIS FILE HAS NEVER RUN, AND THE REASON IS NOT THIS FILE
//!
//! Measured 2026-08-08, and the FIRST diagnosis was wrong — recorded here because a guess in an
//! assertion becomes a diagnosis. The commit that landed this said *"the workspace cargo lock ate
//! three attempts"*; the lock is real (five sibling `cargo test` processes) but it is a DELAY, not
//! the cause. The terminal cause is that **the workspace does not build at all**:
//!
//! ```text
//! error: failed to run custom build command for `dregg-lean-ffi`
//!   panicked at dregg-lean-ffi/build.rs:1294:
//!   DREGG_REQUIRE_LEAN/current release gate refuses a stale verified runtime: `lake build` of the
//!   FFI + gate modules exited exit status: 1 (a module failed to elaborate)
//! ```
//!
//! and `lake build Dregg2.Ffi` names it exactly:
//!
//! ```text
//! Dregg2/Games/PathOfAngels/NetworkJudgeWire.lean:1648: `native_decide` evaluated that the
//!   proposition is false
//! Dregg2/Games/PathOfAngels/NetworkJudgeWire.lean:1678: compiled-pin FAIL:
//!   fixture_output_semantic_inhabited depends on axioms [sorryAx]
//! ```
//!
//! That module is **not in `Dregg2.lean`'s import closure** (which is why the whole-tree
//! `lake build Dregg2` this lane ran is green at 10 683 jobs) and its last touch is `8a336a74e`,
//! a Path-of-Angels commit. It is not this lane's, and the correct response is NOT to disable
//! `DREGG_REQUIRE_LEAN` — this file's subject is the verified runtime.
//!
//! ⚠ **So there is no `test result:` line anywhere for this file, which means NOTHING RAN.** Do not
//! read it as a gate until it prints one. When the Path-of-Angels red clears:
//!
//! Run: `cargo test -p dregg-circuit --release --test mina_body_preimage_bits_proves -- --nocapture`

use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, MemBoundaryWitness, TableSem, VmConstraint2, decomp_cols_pub,
    parse_vm_descriptor2, prove_vm_descriptor2, prove_vm_descriptor2_unchecked,
    verify_vm_descriptor2,
};
use dregg_circuit::field::BabyBear;

const BITS_JSON: &str =
    include_str!("../descriptors/by-name/dregg-mina-body-preimage-bits-v1.json");
const ROW_TXT: &str = include_str!("fixtures/mina-body-preimage-bits-row.txt");

/// `MinaBodyPreimageBitsAir.NBITS` — the packed half of `Body.to_input`.
const NBITS: usize = 2381;
/// `MinaBodyPreimageBitsAir.NLIMB` — `Σ ⌈W_e/8⌉` over the eleven runs.
const NLIMB: usize = 302;
const WIDTH: usize = NBITS + NLIMB;
/// `MinaBodyPreimageBitsAir.FALSIFIER_BIT` — the FIRST `1` in the real block's chunk stream.
const FALSIFIER_BIT: usize = 23;

fn bits_desc() -> EffectVmDescriptor2 {
    parse_vm_descriptor2(BITS_JSON).expect("the Lean body-preimage-bits descriptor parses")
}

/// The honest row, as Lean emitted it.
fn honest_row() -> Vec<BabyBear> {
    let row: Vec<BabyBear> = ROW_TXT
        .split_whitespace()
        .map(|c| BabyBear::new(c.parse::<u32>().expect("cell is a u32 decimal")))
        .collect();
    assert_eq!(
        row.len(),
        WIDTH,
        "the Lean-emitted row is {WIDTH} cells; re-emit it with \
         `lake env lean --run MinaBodyBitsEmit.lean ../circuit/tests/fixtures`"
    );
    row
}

/// The public inputs ARE the limb block — `PI_PLIMB e k = limbBase e + k`, and `PLIMB e k` is
/// `NBITS + limbBase e + k`. One slice, no re-encoding.
fn public_inputs(row: &[BabyBear]) -> Vec<BabyBear> {
    row[NBITS..].to_vec()
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
/// `_constraint_count`), and — the measurement this rung exists to report — **its aux block is
/// empty**.
#[test]
fn the_chunk_gates_declare_no_table_and_commit_what_they_declare() {
    let d = bits_desc();
    assert_eq!(d.name, "dregg-mina-body-preimage-bits::v1");
    assert_eq!(d.trace_width, WIDTH, "2 381 bit columns + 302 limb columns");
    assert_eq!(d.public_input_count, NLIMB, "the eleven limb blocks");
    assert_eq!(d.constraints.len(), NBITS + NLIMB + NLIMB, "gates + pins");
    assert!(
        d.tables.is_empty(),
        "a booleanity gate is not a bus query; this descriptor declares NO table"
    );

    let (declared, committed, range_lookups) = committed_width(&d);
    assert_eq!(
        range_lookups, 0,
        "no range lookup, therefore no nibble aux block"
    );
    assert_eq!(
        declared, committed,
        "the committed row must equal the declared row — the whole committed-width result"
    );
    assert_eq!(committed, 2683);

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
        "  dregg-mina-body-preimage-bits::v1 : {declared} declared → {committed} committed (1.00×), {range_lookups} range lookups"
    );
    println!(
        "  dregg-pasta-fp-chainlink::v1      : {cd} declared → {cc} committed ({:.2}×), {cr} range lookups",
        cc as f64 / cd as f64
    );
    println!(
        "  ⚑ the brief expected chunk gates to ADD range lookups; a booleanity assertion is a"
    );
    println!(
        "    degree-2 window gate, so this is the first rung in the cone whose aux block is empty."
    );
}

/// ⚑ The published PI vector IS the row's limb block — one slice, so a weld to the body-hash
/// chain's absorbed limbs is a slice comparison and not a re-encoding.
#[test]
fn the_public_inputs_are_the_limb_block() {
    let row = honest_row();
    let pis = public_inputs(&row);
    assert_eq!(pis.len(), NLIMB);
    assert_eq!(&pis[..], &row[NBITS..]);
    // Every limb is a byte — a consequence of the gates, checked on the witness.
    assert!(
        pis.iter().all(|v| v.as_u32() < 256),
        "a limb is the composition of eight boolean bits, so it is below 256"
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
    let pis = public_inputs(&row);
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
    let pis = public_inputs(&honest);

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
    assert!(
        !err.contains("exact-public"),
        "no table is declared, so the refusal cannot be a ROM verdict; got: {err}"
    );
    assert!(
        !err.contains("pre-flight") && !err.contains("replay"),
        "the refusal must be the constraint system's, not a producer pre-flight; got: {err}"
    );

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
    let pis = public_inputs(&forged);

    let err = prove_and_verify_adversarial(&d, &trace_from(forged, 2), &pis)
        .expect_err("a limb that is not the composition of its bits must be REFUSED");
    println!("\n§2b ⚑ MIS-COMPOSED LIMB REFUSED BY THE AIR: {err}");
    assert!(
        !err.contains("exact-public") && !err.contains("pre-flight"),
        "the refusal must be the constraint system's; got: {err}"
    );
}

/// ⚑ **AND THE OLD-ADMITS-NEW-REJECTS PAIR, AS ONE STATEMENT.**
#[test]
fn body_preimage_bits_discriminates() {
    let d = bits_desc();
    let honest = honest_row();
    let pis = public_inputs(&honest);

    assert!(
        prove_and_verify_adversarial(&d, &trace_from(honest.clone(), 2), &pis).is_ok(),
        "the honest row is admitted"
    );
    let mut forged = honest;
    forged[FALSIFIER_BIT] = BabyBear::new(2);
    assert!(
        prove_and_verify_adversarial(&d, &trace_from(forged, 2), &pis).is_err(),
        "the over-wide chunk is rejected"
    );
    println!("\n§3 ⚑ old admits / new rejects — on the emitted object, at the deployed prover.");
}
