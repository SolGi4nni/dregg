//! ⚑⚑ **`dregg-mina-bodyhash-relimb::v1` AT THE DEPLOYED PROVER — BOTH POLARITIES, AND THE
//! LOOKUP-FREE MEASUREMENT.**
//!
//! `Dregg2.Circuit.Emit.MinaBodyHashRelimbAir` authors the AIR in Lean (House Law #1) and proves
//! both polarities on its `relimbRowOk` predicate. This file is the other half: the SAME row
//! through the deployed `prove_vm_descriptor2` / `verify_vm_descriptor2`, plus the two numbers a
//! Lean theorem cannot report — the **committed** width `MainLayout::build` actually commits, and
//! the **LDE domain** the FRI config actually opens over.
//!
//! ## ⚑ WHAT THIS DESCRIPTOR IS FOR
//!
//! Tie 2 — the body-hash tie — could not be a `SeamSpec` at all, for a measured arithmetic reason:
//! the body-hash chain publishes thirty-two 8-bit limbs and the light-client link publishes nine
//! 29-bit `Faithful9` lanes, and a direct recomposition carries coefficients to `2^248` against
//! BabyBear's `2^31`. This descriptor publishes BOTH spellings of ONE 254-bit boolean bit block —
//! byte gates at `2^7`, lane gates at `2^28`, all in-field — so each END of the tie becomes an
//! elementwise pin list and tie 2 becomes two descriptor-ended seams
//! (`Dregg2.Circuit.Emit.MinaBodyHashRelimbSeams`).
//!
//! ## ⚠ THE FALSIFIERS CALL THE VERIFIER THEMSELVES
//!
//! `prove_vm_descriptor2_unchecked` returns `Ok` for a forged witness — it gates the pre-flight
//! replay and the `verify_batch` self-check. Every red pole below therefore goes through
//! [`prove_and_verify_adversarial`], which is `prove_vm_descriptor2_unchecked(..)?` **then**
//! `verify_vm_descriptor2`, and asserts the refusal is the constraint system's own rather than a
//! shape fault or a bus verdict.
//!
//! ⚠ Read the COUNT, not the exit code: an `exit 0` with no `test result:` line means nothing ran.
//!
//! Run:
//! ```text
//! DREGG_METATHEORY_DIR=$PWD/metatheory DREGG_LEAN_SYSROOT=$(lean --print-prefix) \
//!   cargo test -p dregg-circuit --release --test mina_bodyhash_relimb_proves -- --nocapture
//! ```

use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, MemBoundaryWitness, TableSem, VmConstraint2, decomp_cols_pub,
    parse_vm_descriptor2, prove_vm_descriptor2, prove_vm_descriptor2_unchecked,
    verify_vm_descriptor2,
};
use dregg_circuit::faithful9::Faithful9;
use dregg_circuit::field::BabyBear;
use dregg_circuit::refusal::assert_violated_constraint_not_bus;

const RELIMB_JSON: &str = include_str!("../descriptors/by-name/dregg-mina-bodyhash-relimb-v1.json");
/// The Lean-emitted witness row (`MinaBodyHashRelimbEmit`), the real block's own
/// `state_body_hash`. Regenerate with
/// `cd metatheory && lake env lean --run MinaBodyHashRelimbEmit.lean ../circuit/tests/fixtures`.
const ROW_TXT: &str = include_str!("fixtures/mina-bodyhash-relimb-row.txt");
/// The Lean-emitted CLAIM (`pubOfValue`) — not a Rust slice of the row.
const PIS_TXT: &str = include_str!("fixtures/mina-bodyhash-relimb-pis.txt");

/// `MinaBodyHashRelimbAir.NBIT` — 254, the link's `MINA_TOP_LANE_BITS = 22` reading of canonicality.
const NBIT: usize = 254;
/// `MinaBodyHashRelimbAir.NBYTE` — the chain's spelling, `SK`.
const NBYTE: usize = 32;
/// `MinaBodyHashRelimbAir.NLANE` — the link's spelling.
const NLANE: usize = 9;
/// `MinaBodyHashRelimbAir.RELIMB_WIDTH`.
const WIDTH: usize = NBIT + NBYTE + NLANE;
/// `MinaBodyHashRelimbAir.RELIMB_PI_COUNT`.
const PI_COUNT: usize = NBYTE + NLANE;
/// `MinaBodyHashRelimbAir` constraint count: 32 byte gates + 9 lane gates + 254 booleanity + 41 pins.
const CONSTRAINTS: usize = NBYTE + NLANE + NBIT + PI_COUNT;
/// The IR-v2 FRI configuration's blowup (`descriptor_ir2::ir2_config`, `log_blowup = 6`).
const LOG_BLOWUP: u32 = 6;

/// ⚑ The alias's own left half, as a falsifier target: bit column 28 sits inside byte 3 and
/// straddles the lane 0 / lane 1 boundary (`laneStart 1 = 29`). Lean:
/// `the_alias_pair_straddles_a_lane_boundary_inside_one_byte`.
const ALIAS_BIT: usize = 28;

fn relimb_desc() -> EffectVmDescriptor2 {
    parse_vm_descriptor2(RELIMB_JSON).expect("the Lean re-limbing descriptor parses")
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
         `cd metatheory && lake env lean --run MinaBodyHashRelimbEmit.lean ../circuit/tests/fixtures`"
    );
    v
}

fn honest_row() -> Vec<BabyBear> {
    decimals(ROW_TXT, WIDTH, "row")
}

fn honest_pis() -> Vec<BabyBear> {
    decimals(PIS_TXT, PI_COUNT, "claim")
}

/// The claim a given row publishes: the 32 byte columns, then the 9 lane columns.
///
/// ⚠ Used to move the claim WITH a forged row, never as the source of truth for the honest one —
/// §0b is what pins it to `pubOfValue`.
fn claim_of(row: &[BabyBear]) -> Vec<BabyBear> {
    row[NBIT..WIDTH].to_vec()
}

/// A power-of-two trace: the real row, then zero padding. ⚑ A zero row satisfies every gate — the
/// booleanity legs because `0·(0−1) = 0`, the composition legs because an all-zero run composes to
/// zero — which is why every gate is `.all` rather than `.first` and costs nothing on the pad.
fn trace_from(row: Vec<BabyBear>, rows: usize) -> Vec<Vec<BabyBear>> {
    assert!(rows.is_power_of_two() && rows >= 2);
    let mut t = vec![row];
    while t.len() < rows {
        t.push(vec![BabyBear::new(0); WIDTH]);
    }
    t
}

/// Declared width plus the nibble aux block `MainLayout::build` appends per declared range lookup.
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
                range_lookups += 1;
                aux += decomp_cols_pub(bits);
            }
        }
    }
    (desc.trace_width, desc.trace_width + aux, range_lookups)
}

/// ⚑ Prove WITHOUT the pre-flight and then VERIFY — the only shape in which a forged witness
/// reaches the constraint system.
fn prove_and_verify_adversarial(
    d: &EffectVmDescriptor2,
    t: &[Vec<BabyBear>],
    pis: &[BabyBear],
) -> Result<(), String> {
    let proof = prove_vm_descriptor2_unchecked(d, t, pis, &MemBoundaryWitness::default(), &[])?;
    verify_vm_descriptor2(d, &proof, pis)
}

/// Assert a refusal is the constraint system's own — not a ROM verdict, not a producer pre-flight.
fn assert_air_refusal(err: &str) {
    assert!(
        !err.contains("exact-public"),
        "no table is declared, so the refusal cannot be a ROM verdict; got: {err}"
    );
    assert!(
        !err.contains("pre-flight") && !err.contains("replay"),
        "the refusal must be the constraint system's, not a producer pre-flight; got: {err}"
    );
    assert_violated_constraint_not_bus("bodyhash-relimb forgery", err);
}

// ============================================================================
// §0 — THE SHAPE, THE COMMITTED WIDTH, AND THE LDE DOMAIN. Cheap, unconditional.
// ============================================================================

/// ⚑⚑⚑ **THE MEASUREMENT THE FIX WAS SPECIFIED BY: LOOKUP-FREE.**
///
/// The re-limbing was named with its shape — *"256 boolean columns, byte gates ≤ `2^7`, lane gates
/// ≤ `2^28`, all in-field, **lookup-free**"*. This is that, measured on the emitted bytes rather
/// than asserted: ZERO range lookups, so `MainLayout::build` appends no aux block and the committed
/// width IS the declared width.
///
/// ⚠ Reported against its sibling one rung down, whose felt-level `.limbs` gate pays 1 216 eight-bit
/// lookups and commits 1.62× its declaration. A bound on a whole felt has to be a bus query; a
/// bound on a byte or a lane does not, because the bits under it are already gated.
#[test]
fn the_relimbing_is_lookup_free_and_commits_what_it_declares() {
    let d = relimb_desc();
    assert_eq!(d.name, "dregg-mina-bodyhash-relimb::v1");
    assert_eq!(d.trace_width, WIDTH, "254 bit + 32 byte + 9 lane columns");
    assert_eq!(
        d.public_input_count, PI_COUNT,
        "32 chain-facing byte slots, then 9 link-facing lane slots"
    );
    assert_eq!(d.constraints.len(), CONSTRAINTS);
    assert!(
        d.tables.is_empty(),
        "the fix was specified lookup-free and declares NO table"
    );

    let (declared, committed, range_lookups) = committed_width(&d);
    assert_eq!(
        range_lookups, 0,
        "a booleanity assertion is a degree-2 window gate, not a bus query — and a composition \
         gate is affine"
    );
    assert_eq!(declared, WIDTH);
    assert_eq!(
        committed, declared,
        "no range lookup means no nibble aux block: committed width = declared width"
    );

    // The two rungs it is measured against, from their own emitted bytes.
    let bits = parse_vm_descriptor2(include_str!(
        "../descriptors/by-name/dregg-mina-body-preimage-bits-v1.json"
    ))
    .expect("the body-preimage-bits descriptor parses");
    let (bd, bc, br) = committed_width(&bits);
    let chainlink = parse_vm_descriptor2(include_str!(
        "../descriptors/by-name/pasta-fp-chainlink.json"
    ))
    .expect("the deployed Fp chain-link descriptor parses");
    let (cd, cc, cr) = committed_width(&chainlink);
    assert!(
        br > 0 && bc > bd,
        "the sibling DOES pay an aux block — so `1.00×` here is a property of this rung, not of \
         the measuring function"
    );

    // ⚑ THE LDE DOMAIN — the quantity the FRI config actually opens over, which no Lean theorem
    // in this cone can report. One real row plus the power-of-two pad.
    let rows = 2usize;
    let lde_rows = rows << LOG_BLOWUP;
    println!("\n═══ §0  COMMITTED WIDTH AND LDE — the units that bind ═══");
    println!(
        "  dregg-mina-bodyhash-relimb::v1    : {declared} declared → {committed} committed ({:.2}×), {range_lookups} range lookups",
        committed as f64 / declared as f64
    );
    println!(
        "  dregg-mina-body-preimage-bits::v1 : {bd} declared → {bc} committed ({:.2}×), {br} range lookups",
        bc as f64 / bd as f64
    );
    println!(
        "  dregg-pasta-fp-chainlink::v1      : {cd} declared → {cc} committed ({:.2}×), {cr} range lookups",
        cc as f64 / cd as f64
    );
    println!(
        "  LDE: {rows} rows × 2^{LOG_BLOWUP} = {lde_rows} rows × {committed} committed columns \
         = {} field elements",
        lde_rows * committed
    );
    println!("  ⚑ ZERO lookups. The bound on a byte is the count of bit columns under it.");
}

/// ⚑⚑ **§0b — THE EMITTED CLAIM IS THE EMITTED ROW'S TWO PUBLISHED BLOCKS.** Two Lean functions
/// (`pubOfValue` and `rowOfValue`) over one layout, compared on the wire — which is what keeps
/// `claim_of` from becoming a second author of the layout.
#[test]
fn the_emitted_claim_is_the_emitted_rows_two_blocks() {
    let row = honest_row();
    let pis = honest_pis();
    assert_eq!(pis, claim_of(&row), "pubOfValue and rowOfValue disagree");
    assert_eq!(&pis[..NBYTE], &row[NBIT..NBIT + NBYTE], "the byte block");
    assert_eq!(&pis[NBYTE..], &row[NBIT + NBYTE..WIDTH], "the lane block");
}

// ============================================================================
// §1 — ⚑⚑⚑ THE DIFFERENTIAL: THE LEAN RE-LIMBING *IS* THE DEPLOYED `Faithful9`.
// ============================================================================

/// ⚑⚑ **THE RE-LIMBING AGREES WITH THE SHIPPED ENCODER, ON THE REAL BLOCK'S `state_body_hash`.**
///
/// The Lean descriptor computes the nine lanes as bit runs of its own gated bit block;
/// `Faithful9::from_key_lanes9` computes them by byte-shifting a 32-byte canonical string. Those
/// are two independent implementations of one function and this is the assertion that they agree —
/// without it the descriptor could be a parallel encoding that no deployed consumer speaks.
///
/// ⚠ Note the width subtlety, stated rather than absorbed: the deployed KEY nonet is `29·8 + 24`
/// and the Mina AIRs' is `29·8 + 22`. They agree on every value below `2^254`, which is exactly
/// what this descriptor's 254 bit columns make unrepresentable to exceed — so the agreement is
/// structural here, not a coincidence of this block.
#[test]
fn the_lean_relimbing_is_the_deployed_faithful9_encoding() {
    let pis = honest_pis();

    // The chain's spelling, as the 32-byte canonical string it is.
    let mut bytes = [0u8; 32];
    for (i, b) in bytes.iter_mut().enumerate() {
        let v = pis[i].as_u32();
        assert!(v < 256, "byte slot {i} is not a byte: {v}");
        *b = v as u8;
    }

    // The link's spelling, as the descriptor publishes it.
    let lean_lanes: Vec<u32> = (0..NLANE).map(|l| pis[NBYTE + l].as_u32()).collect();

    // The deployed encoder's opinion of the same 32 bytes.
    let shipped = Faithful9::from_key_lanes9(&bytes);
    let shipped_lanes: Vec<u32> = shipped.lanes().iter().map(|f| f.as_u32()).collect();

    assert_eq!(
        lean_lanes, shipped_lanes,
        "the Lean re-limbing and `Faithful9::from_key_lanes9` disagree on the real block's \
         state_body_hash — the descriptor would be a parallel encoding"
    );

    // …and the round trip, so the agreement is not on a degenerate value.
    assert_eq!(
        shipped.to_key_bytes(),
        bytes,
        "the nonet does not recompose to the byte block"
    );
    assert!(
        lean_lanes.iter().all(|&l| l != 0),
        "every lane of the real block's body hash is non-zero — this control refuses a degenerate \
         agreement (Lean: `the_real_welds_are_mostly_non_zero`)"
    );
    assert!(
        lean_lanes[8] < (1 << 22),
        "the top lane is inside the link's own canonicality window (`MINA_TOP_LANE_BITS = 22`)"
    );

    println!("\n═══ §1  THE RE-LIMBING, DIFFERENTIAL ═══");
    println!("  32 chain limbs → 9 link lanes: Lean and `Faithful9::from_key_lanes9` AGREE");
    println!("  lanes = {lean_lanes:?}");
}

// ============================================================================
// §2 — ⚑⚑⚑ BOTH POLARITIES AT THE DEPLOYED PROVER.
// ============================================================================

/// ⚑⚑ **THE HONEST POLE.** The real block's `state_body_hash`, re-limbed, proves and verifies.
#[test]
fn the_real_body_hash_row_proves_and_verifies() {
    let d = relimb_desc();
    let t = trace_from(honest_row(), 2);
    let pis = honest_pis();
    let proof = prove_vm_descriptor2(&d, &t, &pis, &MemBoundaryWitness::default(), &[])
        .expect("the honest re-limbing row proves");
    verify_vm_descriptor2(&d, &proof, &pis).expect("…and verifies");
    println!("\n═══ §2  BOTH POLARITIES ═══\n  honest row: PROVED and VERIFIED");
}

/// ⚑⚑⚑ **THE ALIAS'S OWN LEFT HALF, REFUSED BY THE AIR.** Bit column 28 carrying `2` — the vector
/// that, without booleanity, keeps all thirty-two bytes and moves two lanes
/// (`MinaBodyHashRelimbAir.the_booleanity_hypothesis_is_load_bearing`). The refusal is one degree-2
/// window gate: no lookup, no table, no producer pre-flight.
#[test]
fn an_over_wide_bit_is_refused_by_the_air() {
    let d = relimb_desc();
    let mut row = honest_row();
    let before = row[ALIAS_BIT];
    row[ALIAS_BIT] = BabyBear::new(2);
    assert_ne!(
        before, row[ALIAS_BIT],
        "the mutation must MOVE the value — a control that became a no-op is how a sibling lane's \
         falsifier died"
    );
    let pis = honest_pis();
    let err = prove_and_verify_adversarial(&d, &trace_from(row, 2), &pis)
        .expect_err("a non-boolean bit column must be refused");
    assert_air_refusal(&err);
    println!("  over-wide bit column {ALIAS_BIT}: REFUSED — {err}");
}

/// ⚑ **A PUBLISHED BYTE THAT IS NOT WHAT ITS BITS COMPOSE.** The chain-facing half of the tie: a
/// prover who could move this could weld a `state_body_hash` the bit block does not carry.
#[test]
fn a_byte_that_is_not_its_bits_is_refused_by_the_air() {
    let d = relimb_desc();
    let mut row = honest_row();
    let col = NBIT; // BYTE 0
    let before = row[col];
    row[col] = before + BabyBear::new(1);
    assert_ne!(before, row[col], "the mutation must move the value");
    let pis = claim_of(&row);
    let err = prove_and_verify_adversarial(&d, &trace_from(row, 2), &pis)
        .expect_err("a byte that is not its bits must be refused");
    assert_air_refusal(&err);
    println!("  byte 0 ≠ its bits: REFUSED — {err}");
}

/// ⚑⚑ **A PUBLISHED LANE THAT IS NOT WHAT ITS BITS COMPOSE.** The link-facing half — and the one a
/// byte-only gate would miss entirely, which is the whole reason the descriptor gates BOTH
/// partitions of the same bit block rather than one and a recomposition.
#[test]
fn a_lane_that_is_not_its_bits_is_refused_by_the_air() {
    let d = relimb_desc();
    let mut row = honest_row();
    let col = NBIT + NBYTE; // LANE 0
    let before = row[col];
    row[col] = before + BabyBear::new(1);
    assert_ne!(before, row[col], "the mutation must move the value");
    let pis = claim_of(&row);
    let err = prove_and_verify_adversarial(&d, &trace_from(row, 2), &pis)
        .expect_err("a lane that is not its bits must be refused");
    assert_air_refusal(&err);
    println!("  lane 0 ≠ its bits: REFUSED — {err}");
}

/// ⚑ **A CLAIM THAT IS NOT THE COLUMN IT PINS.** Without the pin conjunct the gates would bound
/// columns the seams never read, and both seams weld CLAIM slots.
#[test]
fn a_claim_that_is_not_its_column_is_refused_by_the_air() {
    let d = relimb_desc();
    let row = honest_row();
    let mut pis = honest_pis();
    let slot = NBYTE + NLANE - 1; // PI_LANE 8
    let before = pis[slot];
    pis[slot] = before + BabyBear::new(1);
    assert_ne!(before, pis[slot], "the mutation must move the value");
    let err = prove_and_verify_adversarial(&d, &trace_from(row, 2), &pis)
        .expect_err("a claim slot that is not its column must be refused");
    assert_air_refusal(&err);
    println!("  claim slot {slot} ≠ its column: REFUSED — {err}");
}
