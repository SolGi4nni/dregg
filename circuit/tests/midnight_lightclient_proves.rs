//! ⚑ **THE MIDNIGHT GRANDPA LIGHT CLIENT, PROVED ON THE DEPLOYED PROVER.**
//!
//! # What had never happened
//!
//! Five peer chains have a Lean-authored light-client verify AIR routed through `EmitByName.lean`
//! into `circuit/src/descriptor_by_name.rs`. As of 2026-08-03 three had ever been proved: Mina
//! (`turn/tests/mina_anchored_head_lands.rs`), Tendermint
//! (`circuit/tests/tendermint_lightclient_proves.rs`) and Solana
//! (`circuit/tests/solana_lightclient_proves.rs`). Midnight was served by name and no prover had
//! ever run it — *"producible by a node" was a claim about DISPATCH*. This file closes Midnight.
//!
//! The Lean side already accepts (`Dregg2.Circuit.Emit.LightClientMidnightAir
//! .midLcAir_accepts_the_live_authority_set`, `…_accepts_at_the_u64_type_ceiling`) with both
//! refusals proved as named theorems. What was missing was the machine-specific half: that the
//! DEPLOYED Rust prover produces a proof for the honest row and REFUSES the exhibited forgeries.
//!
//! # ⚠ What Midnight's tally IS — the counter-claim this file must not launder
//!
//! Measured live 2026-08-03 against `https://rpc.mainnet.midnight.network`
//! (`GrandpaApi_grandpa_authorities` → **130 entries, every weight exactly 1**; the `1` is
//! polkadot-sdk's, `substrate/frame/grandpa/src/lib.rs:609`), Midnight's total authority weight is
//! a **SEAT COUNT of 130 — seven bits — and it fits a BabyBear felt with 24 bits to spare.**
//!
//! ⚑ **So limbing Midnight's tally did NOT close a live representability shortfall, and this file
//! does not claim it did.** Tendermint (`MaxTotalVotingPower = 2^60 − 1`) and Solana (2^58.6
//! lamports of live stake) genuinely could not fit a column; that is their modules' claim and it is
//! not transferable to this one. What the limbing bought here, in order of worth:
//!
//!  1. ⚑ **the refusal stopped depending on the field size** — the single-felt tooth refused the
//!     exactly-2/3 sub-quorum because `p − 1 ∉ [0, 2^29)`, a fact about `p`, false at 30 and
//!     catastrophically false at the 128 that shipped;
//!  2. the DECLARED type is `pub type AuthorityWeight = u64`
//!     (`substrate/primitives/consensus/grandpa/src/lib.rs:65`), and 130 is a governance-set
//!     D-parameter rather than a bound — `a_committee_at_the_u64_type_ceiling_proves` exercises
//!     that capability rather than asserting it.
//!
//! # The two teeth this file makes bite on the running prover
//!
//! `dregg-midnight-lightclient-verify::v1` shipped `bits: 128` on its range table, and BabyBear is
//! `p = 2013265921 < 2^31 < 2^128`, so the declared interval already contained every field element
//! and the lookups refused nothing (`RangeFieldContainment.range_vacuous_at_or_above_31`). BOTH of
//! its floors then failed CONCRETELY, on the same admitted element `p − 1 = 2013265920`
//! (`mid_both_floors_filled_the_admitted_element`):
//!
//!  * **exactly 2/3.** `WDIFF = 3·signed − 2·total − 1` fills to `−1` at exactly 2/3 — the
//!    sub-quorum GRANDPA's STRICT threshold exists to reject. 130 is not divisible by 3, so the
//!    case is exhibited at `total = 129`, `signed = 86` (`3·86 = 258 = 2·129`), with the honest
//!    `87 of 129` as its paired positive.
//!  * **the empty authority set.** `TPOS = total − 1` fills to `−1` at `total = 0` — the empty set
//!    passed its own emptiness floor.
//!
//! ⚑ And unlike Solana's, Midnight's threshold is STRICT (`γ = 1`), so at `total = 0` BOTH chains
//! refuse independently. `the_empty_authority_set_is_refused_by_BOTH_floors` measures that on the
//! deployed prover by disarming them one at a time: force the quorum's out-of-range top limb into
//! range and the refusal MOVES to the floor chain's top limb, and only with both forced does an
//! algebraic gate become what refuses.
//!
//! # Scope, said plainly
//!
//! `ED_OK` / `AUTHSET_OK` / `ROUND_OK` / `ERA_OK` are witnessed carrier bits, not in-AIR Ed25519
//! and SHA-256; the dregg-side STARK inherits the undischarged FRI floor. This is a prover running
//! the served object. It is **not** "Midnight-valid", and it is not "machine-checked" — the
//! machine-checked statements are the Lean ones this file names, and a Rust case-test quantifies
//! over nothing.
//!
//! ⚠ **PROFILE.** plonky3's ALGEBRAIC refusals are `#[cfg(debug_assertions)]` panics under
//! `cargo test` and clean `Err(OodEvaluationMismatch)` under `--release`; RANGE refusals are `Err`
//! in both. Every refusal here goes through `dregg_circuit::refusal`.

use dregg_circuit::BabyBear;
use dregg_circuit::descriptor_by_name::descriptor_by_name;
use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, MemBoundaryWitness, TableSem, parse_vm_descriptor2, prove_vm_descriptor2,
    verify_vm_descriptor2,
};
use dregg_circuit::heap_root::HeapLeaf;
use dregg_circuit::refusal;

const MID_LC_VERIFY_DESCRIPTOR: &str = "dregg-midnight-lightclient-verify::v1";

// ═══════════════════════════════════════════════════════════════════════════════════════════
// Trace column layout — pinned to `LightClientMidnightAir`'s Lean `def`s (§1).
// ═══════════════════════════════════════════════════════════════════════════════════════════

/// CARRIER — the aggregate Ed25519 verify result over the counted authorities' precommits.
const ED_OK: usize = 0;
/// CARRIER — the derived authority set binds the pinned WS anchor root.
const AUTHSET_OK: usize = 1;
/// GATE — every counted precommit names the claimed round R (cross-round).
const ROUND_OK: usize = 2;
/// GATE — the claimed set id equals the anchored era (stale-authority-set).
const ERA_OK: usize = 3;
/// `TOTAL_WEIGHT` limb 0 (LSB). Limbs 0..3 are columns 4..7.
const TOTAL_WEIGHT_0: usize = 4;
/// `SIGNED_WEIGHT` limb 0 (LSB). Limbs 0..3 are columns 8..11.
const SIGNED_WEIGHT_0: usize = 8;
/// `WDIFF` limb 0 (LSB) — `3·signed − 2·total − 1`. FIVE limbs, columns 12..16.
const WDIFF_0: usize = 12;
/// The offset carry out of quorum rung 0. Four carries, columns 17..20; each denotes `col − 128`.
const WDIFF_CARRY_0: usize = 17;
/// `TPOS` limb 0 (LSB) — the empty-set floor difference `total − 1`. Columns 21..25.
const TPOS_0: usize = 21;
/// The offset carry out of floor rung 0. Four carries, columns 26..29.
const TPOS_CARRY_0: usize = 26;
/// PUBLIC ANCHOR — the pinned WS authority-set root.
const ANCHOR_ROOT: usize = 30;
/// PUBLIC ANCHOR limb 0 — the finalized target root as nine radix-`2^31` MSB-first limbs, 31..39.
const TARGET_ROOT_0: usize = 31;
const TARGET_ROOT_LIMBS: usize = 9;
/// PUBLIC ANCHOR — the GRANDPA round R.
const ROUND_COL: usize = 40;
/// PUBLIC ANCHOR — the authority-set id (era) E.
const ERA_COL: usize = 41;

const MID_LC_WIDTH: usize = 42;
const MID_PI_COUNT: usize = 12;

/// The tally limb width. `4 · 16 = 64` — four limbs are exactly `AuthorityWeight = u64`.
const MID_LIMB_BITS: usize = 16;
/// The chain-carry width (the prover's own byte bus).
const MID_CARRY_BITS: usize = 8;

/// Declared wire id of the 16-bit tally-limb table (`.custom (64 + 16)` ⇒ `5 + 80`).
const TID_TALLY_LIMB: usize = 85;
/// Declared wire id of the 8-bit chain-carry table (`.custom (64 + 8)` ⇒ `5 + 72`).
const TID_TALLY_CARRY: usize = 77;
/// The shared felt-wide `range` table's wire id. ⚑ This descriptor MUST NOT declare it — the
/// 29-bit declaration was DELETED when both comparisons became limbed chains
/// (`mid_no_felt_wide_range_table_is_declared`), because Midnight has no time-window slacks and a
/// declared table nothing looks up is a width nothing checks.
const TID_FELT_RANGE: usize = 2;

const CARRY_OFF: i64 = 128;
const RUNGS: usize = 4;

/// The width that SHIPPED. `128 % 64 == 0`, so the layout filler's `(v as u64) >= (1u64 << bits)`
/// masked to a shift by 0 and the test collapsed to `v >= 1`: vacuous in the denotation, refusing
/// EVERYTHING in the deployed prover.
///
/// ⚑ **BOTH HALVES CLOSED 2026-08-03 — this constant now names a REFUSED declaration, not a live
/// one.** `parse_table_def` refuses a range width at or above `VACUOUS_RANGE_BITS` (31) at
/// descriptor LOAD, and the filler's bound is total (`value_fits_bits`), so an in-memory descriptor
/// at this width admits everything exactly as `DescriptorIR2.rangeRows` says. Both are measured by
/// `the_shipped_128_bit_width_refuses_even_an_honest_justification` below.
const SHIPPED_MID_BITS: usize = 128;

/// The smallest FULLY VACUOUS width (`2^32 > p`) the deployed prover can still execute.
const VACUOUS_BITS: usize = 32;

const TRACE_ROWS: usize = 8;

const P: i64 = 2_013_265_921;

fn desc() -> EffectVmDescriptor2 {
    descriptor_by_name(MID_LC_VERIFY_DESCRIPTOR).unwrap_or_else(|| {
        panic!(
            "{MID_LC_VERIFY_DESCRIPTOR} must dispatch: the Lean-emitted descriptor is routed \
             through EmitByName.lean and included by circuit/src/descriptor_by_name.rs"
        )
    })
}

/// The SAME served descriptor with the **16-bit TALLY-LIMB table's** declared width set to `bits`.
/// The declared table wins over the `CUSTOM_RANGE_WIDTHS` fallback
/// (`descriptor_ir2.rs:1472` `range_bits_for`), so one integer moves and nothing else does.
fn desc_with_limb_range_width(bits: usize) -> EffectVmDescriptor2 {
    let mut d = desc();
    let mut touched = 0usize;
    for t in d.tables.iter_mut() {
        if t.id == TID_TALLY_LIMB {
            if let TableSem::Range { bits: b } = &mut t.sem {
                *b = bits;
                touched += 1;
            }
        }
    }
    assert_eq!(
        touched, 1,
        "exactly the 16-bit tally-limb table must be re-declared; the carry table stays at 8"
    );
    d
}

fn felt(v: i64) -> BabyBear {
    BabyBear::new(v.rem_euclid(P) as u32)
}

// ═══════════════════════════════════════════════════════════════════════════════════════════
// ⚑ THE HONEST FILL — `LimbTally.fillDigit` / `LimbTally.fillCarry`, transcribed as a LOOP.
// ═══════════════════════════════════════════════════════════════════════════════════════════

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct ChainFill {
    /// `α·A − β·B − γ` as FIVE 16-bit limbs, LSB first. `diff[4]` IS the final carry.
    diff: [i64; RUNGS + 1],
    /// The carry out of each rung, OFFSET: `carry[i] = c_{i+1} + 128`.
    carry: [i64; RUNGS],
}

fn limbs4(v: u64) -> [i64; RUNGS] {
    let mut out = [0i64; RUNGS];
    for (i, o) in out.iter_mut().enumerate() {
        *o = ((v >> (MID_LIMB_BITS * i)) & 0xFFFF) as i64;
    }
    out
}

/// ⚑ **THE HONEST FILL**, parametric because this AIR runs TWO chains that do not share constants:
///
///  * the QUORUM chain is `α = 3` on signed weight, `β = 2` on total weight, **`γ = 1`** — GRANDPA's
///    STRICT `3·signed > 2·total`. ⚠ This is where Midnight differs from its Solana sibling, whose
///    `γ = 0` makes exactly 2/3 ACCEPT.
///  * the FLOOR chain is `α = 1`, `β = 0`, `γ = 1` — `total − 1 ≥ 0`, the empty-set refusal.
///
/// `fillDigit` is a FLOOR mod and `fillCarry` the exact floor quotient, so `raw − d − c·2^16 = 0`
/// holds identically (`LimbTally.fill_splits`). When the comparison FAILS the final carry is
/// NEGATIVE and `diff[4]` comes out negative — that is the refusal, expressed rather than hidden.
fn fill_chain(alpha: i64, a: [i64; RUNGS], beta: i64, b: [i64; RUNGS], gamma: i64) -> ChainFill {
    let radix: i64 = 1 << MID_LIMB_BITS;
    let mut diff = [0i64; RUNGS + 1];
    let mut carry = [0i64; RUNGS];
    let mut c: i64 = 0;
    for i in 0..RUNGS {
        let g = if i == 0 { gamma } else { 0 };
        let raw = alpha * a[i] - beta * b[i] - g + c;
        let d = raw.rem_euclid(radix);
        c = (raw - d) / radix;
        diff[i] = d;
        carry[i] = c + CARRY_OFF;
    }
    // The chain's CLOSURE: the operands have run out, so the final carry IS the top digit.
    diff[RUNGS] = c;
    ChainFill { diff, carry }
}

fn limb_value(limbs: &[i64]) -> i128 {
    let mut acc: i128 = 0;
    for &l in limbs.iter().rev() {
        acc = acc * (1i128 << MID_LIMB_BITS) + l as i128;
    }
    acc
}

// ═══════════════════════════════════════════════════════════════════════════════════════════
// One logical row of the Midnight GRANDPA verify decision
// ═══════════════════════════════════════════════════════════════════════════════════════════

#[derive(Clone, Copy)]
struct Justification {
    /// ⚑ `u64` — `AuthorityWeight`. 130 live; the type permits `2^64 − 1`.
    total_weight: u64,
    /// ⚑ `u64`. The counted SIGNED authority weight; its Ed25519 provenance is `ED_OK`.
    signed_weight: u64,
    ed_ok: u32,
    authset_ok: u32,
    round_ok: u32,
    era_ok: u32,
    anchor_root: u32,
    target_root: [u32; TARGET_ROOT_LIMBS],
    round: u32,
    era: u32,
}

fn honest(total_weight: u64, signed_weight: u64) -> Justification {
    Justification {
        total_weight,
        signed_weight,
        ed_ok: 1,
        authset_ok: 1,
        round_ok: 1,
        era_ok: 1,
        anchor_root: 77777,
        target_root: [1, 2, 3, 4, 5, 6, 7, 8, 9],
        round: 4242,
        era: LIVE_ERA,
    }
}

/// The 42 cells of one logical row, **as integers** — the same 42 numbers, in the same order, as
/// `LightClientMidnightAir.midLiveCells`.
fn row_cells(j: Justification) -> Vec<i64> {
    let total = limbs4(j.total_weight);
    let signed = limbs4(j.signed_weight);
    // §2: `α = 3` on signed, `β = 2` on total, `γ = 1` — GRANDPA's STRICT `3·signed > 2·total`.
    let w = fill_chain(3, signed, 2, total, 1);
    // §2: `α = 1`, `β = 0`, `γ = 1` — `total − 1 ≥ 0`. The `β` column points at the total-weight
    // limb ON PURPOSE (`tPosRungs`): at `β = 0` the emitted term is `0 · var`, so no dedicated zero
    // column is needed and none has to be pinned.
    let t = fill_chain(1, total, 0, total, 1);

    let mut r = vec![0i64; MID_LC_WIDTH];
    r[ED_OK] = j.ed_ok as i64;
    r[AUTHSET_OK] = j.authset_ok as i64;
    r[ROUND_OK] = j.round_ok as i64;
    r[ERA_OK] = j.era_ok as i64;
    r[TOTAL_WEIGHT_0..TOTAL_WEIGHT_0 + RUNGS].copy_from_slice(&total);
    r[SIGNED_WEIGHT_0..SIGNED_WEIGHT_0 + RUNGS].copy_from_slice(&signed);
    r[WDIFF_0..WDIFF_0 + RUNGS + 1].copy_from_slice(&w.diff);
    r[WDIFF_CARRY_0..WDIFF_CARRY_0 + RUNGS].copy_from_slice(&w.carry);
    r[TPOS_0..TPOS_0 + RUNGS + 1].copy_from_slice(&t.diff);
    r[TPOS_CARRY_0..TPOS_CARRY_0 + RUNGS].copy_from_slice(&t.carry);
    r[ANCHOR_ROOT] = j.anchor_root as i64;
    for (i, l) in j.target_root.iter().enumerate() {
        r[TARGET_ROOT_0 + i] = *l as i64;
    }
    r[ROUND_COL] = j.round as i64;
    r[ERA_COL] = j.era as i64;
    r
}

/// The twelve published anchors, in PI order.
fn pis_of(j: Justification) -> Vec<BabyBear> {
    let mut pis = vec![BabyBear::new(0); MID_PI_COUNT];
    pis[0] = BabyBear::new(j.anchor_root);
    for (i, l) in j.target_root.iter().enumerate() {
        pis[1 + i] = BabyBear::new(*l);
    }
    pis[10] = BabyBear::new(j.round);
    pis[11] = BabyBear::new(j.era);
    pis
}

fn trace_of(cells: &[i64]) -> Vec<Vec<BabyBear>> {
    let row: Vec<BabyBear> = cells.iter().map(|&v| felt(v)).collect();
    vec![row; TRACE_ROWS]
}

fn prove_and_verify(
    d: &EffectVmDescriptor2,
    cells: &[i64],
    pis: &[BabyBear],
) -> Result<(), String> {
    let trace = trace_of(cells);
    refusal::assert_committed_shape("midnight lightclient", d, &trace, pis);
    let mem = MemBoundaryWitness::default();
    let heaps: Vec<Vec<HeapLeaf>> = vec![];
    let proof = prove_vm_descriptor2(d, &trace, pis, &mem, &heaps)
        .map_err(|e| format!("prover refused: {e}"))?;
    verify_vm_descriptor2(d, &proof, pis).map_err(|e| format!("verifier refused: {e:?}"))
}

fn must_prove(what: &str, j: Justification) {
    must_prove_under(what, &desc(), j);
}

fn must_prove_under(what: &str, d: &EffectVmDescriptor2, j: Justification) {
    let cells = row_cells(j);
    let pis = pis_of(j);
    refusal::must_accept(what, || prove_and_verify(d, &cells, &pis));
}

/// A RANGE refusal — an `Err` in EVERY profile, never a panic, never debug-only.
fn must_refuse_out_of_range(
    what: &str,
    d: &EffectVmDescriptor2,
    cells: &[i64],
    pis: &[BabyBear],
) -> String {
    let e: String = refusal::must_refuse(what, || prove_and_verify(d, cells, pis));
    assert!(
        e.contains("range wire"),
        "{what}: expected the RANGE tooth (`row R: range wire N value V >= 2^b`), got: {e}"
    );
    e
}

/// An ALGEBRAIC refusal — a p3 unsat panic under `cargo test`, `OodEvaluationMismatch` under
/// `--release`. The load-bearing half is the NEGATIVE clause: a tooth whose subject is a specific
/// gate must not be satisfied by the lookup bus failing instead.
fn must_refuse_violated_gate(
    what: &str,
    d: &EffectVmDescriptor2,
    cells: &[i64],
    pis: &[BabyBear],
) -> String {
    let r = refusal::must_refuse_or_unsat_panic(what, || prove_and_verify(d, cells, pis));
    let reason = r.reason();
    refusal::assert_violated_constraint_not_bus(what, &reason);
    reason
}

// ═══════════════════════════════════════════════════════════════════════════════════════════
// ⚑ MIDNIGHT MAINNET, MEASURED LIVE
// ═══════════════════════════════════════════════════════════════════════════════════════════

/// Midnight mainnet's live GRANDPA total authority weight, measured 2026-08-03 against
/// `https://rpc.mainnet.midnight.network` (`system_version` = "1.0.1-5edf8ddd"):
/// `GrandpaApi_grandpa_authorities` SCALE-decodes to **130 entries, each of weight exactly 1**.
const LIVE_TOTAL_WEIGHT: u64 = 130;

/// The SMALLEST strict supermajority of 130: `3·87 = 261 > 260 = 2·130`, and `3·86 = 258 < 260`.
const LIVE_MIN_SUPERMAJORITY: u64 = 87;

/// The authority-set id (era) at the same sample (`systemParameters_getAriadneParameters(647)`).
const LIVE_ERA: u32 = 647;

/// `AuthorityWeight` is `u64` (`substrate/primitives/consensus/grandpa/src/lib.rs:65`). This is the
/// only hard bound citable — 130 is a governance-set D-parameter, NOT a documented protocol cap.
const U64_CEILING: u64 = 18_446_744_073_709_551_615;

/// The minimal strict supermajority of `2^64 − 1`.
const U64_CEILING_MIN_SUPERMAJORITY: u64 = 12_297_829_382_473_034_411;

/// `LightClientMidnightAir.midLiveCells`, transcribed. Lean hand-writes these 42 numbers and
/// `decide`s what they denote; Rust COMPUTES them from `total`/`signed` through `fill_chain`.
const LEAN_LIVE_CELLS: [i64; MID_LC_WIDTH] = [
    1, 1, 1, 1, 130, 0, 0, 0, 87, 0, 0, 0, 0, 0, 0, 0, 0, 128, 128, 128, 128, 129, 0, 0, 0, 0, 128,
    128, 128, 128, 77777, 1, 2, 3, 4, 5, 6, 7, 8, 9, 4242, 647,
];

/// `LightClientMidnightAir.midU64CeilingCells`, transcribed.
const LEAN_U64_CEILING_CELLS: [i64; MID_LC_WIDTH] = [
    1, 1, 1, 1, 65535, 65535, 65535, 65535, 43691, 43690, 43690, 43690, 2, 0, 0, 0, 0, 128, 128,
    128, 128, 65534, 65535, 65535, 65535, 0, 128, 128, 128, 128, 77777, 1, 2, 3, 4, 5, 6, 7, 8, 9,
    4242, 647,
];

// ═══════════════════════════════════════════════════════════════════════════════════════════
// The served object
// ═══════════════════════════════════════════════════════════════════════════════════════════

#[test]
fn the_served_descriptor_is_the_lean_emitted_one() {
    let d = desc();
    assert_eq!(d.name, MID_LC_VERIFY_DESCRIPTOR);
    assert_eq!(
        d.trace_width, MID_LC_WIDTH,
        "⚑ the two tallies became limb vectors: 20 → 42 columns"
    );
    assert_eq!(d.public_input_count, MID_PI_COUNT);
    // 26 per-limb lookups + 10 generated chain gates + 4 carrier/logic gates + 12 PI pins = 52
    // (`LightClientMidnightAir.mid_shape_pins`).
    assert_eq!(d.constraints.len(), 52);
    assert_eq!(d.tables.len(), 2);

    let bits_of = |id: usize| -> usize {
        let t = d
            .tables
            .iter()
            .find(|t| t.id == id)
            .unwrap_or_else(|| panic!("no declared table with wire id {id}"));
        match t.sem {
            TableSem::Range { bits } => bits,
            _ => panic!("table {id} must be a range table"),
        }
    };

    // ⚠ Read out of the SERVED descriptor, not out of this file's constants — a constant compared
    // against its own definition is decoration.
    let served_limb_bits = bits_of(TID_TALLY_LIMB);
    assert_eq!(served_limb_bits, MID_LIMB_BITS);
    assert_eq!(bits_of(TID_TALLY_CARRY), MID_CARRY_BITS);

    // ⚑ The felt-wide `range` table is GONE — the 29-bit declaration was DELETED when both
    // comparisons became chains (`mid_no_felt_wide_range_table_is_declared`). Midnight has no
    // time-window slacks, so nothing was left to query it.
    assert!(
        d.tables.iter().all(|t| t.id != TID_FELT_RANGE),
        "⚑ the shared felt-wide range table must NOT be declared"
    );

    let served_capacity: u128 = 1u128 << (served_limb_bits * RUNGS);
    assert_eq!(
        served_capacity,
        1u128 << 64,
        "four 16-bit limbs tile a u64 exactly"
    );
    assert_eq!(
        U64_CEILING as u128,
        served_capacity - 1,
        "…and the tiled capacity is exactly `AuthorityWeight`'s declared range"
    );

    // ⚠ THE COUNTER-CLAIM, ASSERTED SO IT CANNOT BE QUIETLY DROPPED: Midnight's LIVE tally fits one
    // BabyBear felt, comfortably. The limbing here bought field-independence and the `u64` type
    // ceiling — NOT a live representability repair. Its two siblings' claim is not transferable.
    assert!(
        (LIVE_TOTAL_WEIGHT as i64) < P / 15_000_000,
        "⚑ 130 fits a felt with 24 bits to spare — this AIR did NOT need limbs for today's set"
    );
}

/// The Rust filler and the two Lean rows are the same 42 numbers each.
#[test]
fn the_honest_fill_reproduces_the_lean_rows() {
    let live = row_cells(honest(LIVE_TOTAL_WEIGHT, LIVE_MIN_SUPERMAJORITY));
    assert_eq!(
        live.as_slice(),
        LEAN_LIVE_CELLS.as_slice(),
        "the computed live row must equal LightClientMidnightAir.midLiveCells"
    );
    let ceiling = row_cells(honest(U64_CEILING, U64_CEILING_MIN_SUPERMAJORITY));
    assert_eq!(
        ceiling.as_slice(),
        LEAN_U64_CEILING_CELLS.as_slice(),
        "the computed ceiling row must equal LightClientMidnightAir.midU64CeilingCells"
    );

    // The fills recompose (`LimbTally.chain_recomposes`), as arithmetic about THESE rows.
    let w = fill_chain(
        3,
        limbs4(LIVE_MIN_SUPERMAJORITY),
        2,
        limbs4(LIVE_TOTAL_WEIGHT),
        1,
    );
    assert_eq!(
        limb_value(&w.diff),
        0,
        "87 of 130 sits EXACTLY on the strict boundary"
    );
    let t = fill_chain(
        1,
        limbs4(LIVE_TOTAL_WEIGHT),
        0,
        limbs4(LIVE_TOTAL_WEIGHT),
        1,
    );
    assert_eq!(limb_value(&t.diff), 129);

    // ⚑ …and the operand limbs on the WIRE denote the tallies this file claims. Read back out of
    // the emitted row rather than off the constants, so this is the row measured against its own
    // denotation rather than a constant compared with itself.
    let denoted = |cells: &[i64], base: usize| limb_value(&cells[base..base + RUNGS]);
    for (cells, total, signed) in [
        (&live, LIVE_TOTAL_WEIGHT, LIVE_MIN_SUPERMAJORITY),
        (&ceiling, U64_CEILING, U64_CEILING_MIN_SUPERMAJORITY),
    ] {
        assert_eq!(denoted(cells, TOTAL_WEIGHT_0), total as i128);
        assert_eq!(denoted(cells, SIGNED_WEIGHT_0), signed as i128);
        // The supermajority really is minimal, BOTH WAYS, at what the row denotes.
        let (t128, s128) = (total as i128, signed as i128);
        assert!(
            2 * t128 < 3 * s128,
            "the row must clear GRANDPA's STRICT threshold"
        );
        assert!(
            2 * t128 >= 3 * (s128 - 1),
            "…and one unit below it must NOT — otherwise the row is not the boundary it claims"
        );
    }
}

// ═══════════════════════════════════════════════════════════════════════════════════════════
// ⚑⚑ THE MEASUREMENT — a prover has run this descriptor
// ═══════════════════════════════════════════════════════════════════════════════════════════

/// ⚑⚑ **THE DELIVERABLE: MIDNIGHT MAINNET'S LIVE AUTHORITY SET PROVES AND VERIFIES ON THE DEPLOYED
/// RUST PROVER.** 87 of 130, at the exact strict-supermajority boundary (`WDIFF = 0`, the tightest
/// accepting row there is). The Lean counterpart is
/// `LightClientMidnightAir.midLcAir_accepts_the_live_authority_set`, over the same 42 cells.
#[test]
fn the_live_midnight_authority_set_proves() {
    let j = honest(LIVE_TOTAL_WEIGHT, LIVE_MIN_SUPERMAJORITY);
    assert!(2 * j.total_weight < 3 * j.signed_weight);

    let t0 = std::time::Instant::now();
    must_prove(
        "⚑ Midnight mainnet's live 130-seat authority set at the minimal strict supermajority",
        j,
    );
    eprintln!(
        "⚑ MIDNIGHT LIVE AUTHORITY SET: total={} signed={} round={} era={} PROVED AND VERIFIED in \
         {:?} ({TRACE_ROWS} trace rows, {MID_LC_WIDTH} base columns)",
        j.total_weight,
        j.signed_weight,
        j.round,
        j.era,
        t0.elapsed()
    );
}

/// ⚑ **THE CAPABILITY, EXERCISED RATHER THAN ASSERTED.** 130 fits a felt; `2^64 − 1` does not fit
/// anything narrower than the four limbs this AIR now carries, and it is what
/// `pub type AuthorityWeight = u64` actually permits. If Midnight's governance ever moves the
/// D-parameter to a stake-weighted committee, this row is the evidence the AIR does not change.
///
/// ⚠ And the honest framing, kept: this is a TYPE ceiling, not a measured protocol maximum. There is
/// no documented cap on Midnight's committee size to cite.
#[test]
fn a_committee_at_the_u64_type_ceiling_proves() {
    let j = honest(U64_CEILING, U64_CEILING_MIN_SUPERMAJORITY);
    assert!(2 * (j.total_weight as i128) < 3 * (j.signed_weight as i128));
    assert!(
        (j.total_weight as i128) > 9_000_000_000i128 * P as i128,
        "⚑ the ceiling row is 9.16 BILLION field moduli — no declared width ever made it fit a felt"
    );

    let t0 = std::time::Instant::now();
    must_prove("⚑ an authority set at the u64 AuthorityWeight ceiling", j);
    eprintln!(
        "⚑ MIDNIGHT u64 CEILING: total={} signed={} PROVED AND VERIFIED in {:?}\n   total limbs \
         {:?}\n   signed limbs {:?}",
        j.total_weight,
        j.signed_weight,
        t0.elapsed(),
        limbs4(j.total_weight),
        limbs4(j.signed_weight)
    );
}

/// The paired positive for the exactly-2/3 tooth, at the SAME total: `87 of 129` is a genuine
/// (non-boundary) supermajority and PROVES. Without this the refusal below is satisfied by a
/// descriptor that refuses everything.
#[test]
fn a_genuine_supermajority_at_129_proves() {
    let j = honest(129, 87);
    let w = fill_chain(3, limbs4(87), 2, limbs4(129), 1);
    assert_eq!(limb_value(&w.diff), 2);
    assert_eq!(row_cells(j)[WDIFF_0], 2);
    must_prove("87 of 129 — a genuine strict supermajority", j);
}

// ═══════════════════════════════════════════════════════════════════════════════════════════
// ⚑ TOOTH 1 — EXACTLY 2/3
// ═══════════════════════════════════════════════════════════════════════════════════════════

/// ⚑ **EXACTLY 2/3 IS REFUSED.** `86 of 129`: `3·86 = 258 = 2·129`, so `WDIFF = −1`.
///
/// 130 is not divisible by 3, so exactly-2/3 is not representable at the live total; 129 is, and
/// the paired positive `87 of 129` proves above. This is the precise defect the shipped 128-bit
/// table ADMITTED (`mid_exactly_two_thirds_was_admitted_at_128`) — GRANDPA's threshold is STRICT
/// and a `>2/3` client that finalizes at exactly 2/3 is a safety failure, not a rounding one.
///
/// Both legs are exercised: the honest fill's top difference limb is `p − 1` and the 16-bit tooth
/// has no row for it; forcing that limb to `0` leaves the closure gate `c₃ − d₄ − 128 = −1 ≠ 0`.
///
/// ⚠ Neither leg is the general statement. "NO assignment of difference limbs and carries satisfies
/// the chain" is `midLcAir_refuses_exactly_two_thirds`, a Lean theorem over the emitted bodies with
/// no width, field or magnitude hypothesis. A Rust test quantifies over nothing.
#[test]
fn the_exactly_two_thirds_sub_quorum_is_refused() {
    let j = honest(129, 86);
    assert_eq!(
        3 * j.signed_weight,
        2 * j.total_weight,
        "EXACTLY two thirds — GRANDPA's threshold is STRICT and this must not finalize"
    );

    let w = fill_chain(3, limbs4(86), 2, limbs4(129), 1);
    assert_eq!(limb_value(&w.diff), -1);
    assert_eq!(w.diff[RUNGS], -1, "carried into the TOP limb");
    assert_eq!(
        felt(w.diff[RUNGS]).as_u32() as i64,
        P - 1,
        "…which on the wire is p − 1, the exact element the shipped [0, 2^128) admitted"
    );
    assert_eq!(w.carry, [127, 127, 127, 127], "and every rung BORROWED");

    let d = desc();
    let cells = row_cells(j);
    let pis = pis_of(j);
    let e = must_refuse_out_of_range("⚑ exactly 2/3 (86 of 129), honest fill", &d, &cells, &pis);
    eprintln!("⚑ MIDNIGHT exactly-2/3 refused: {e}");
    assert!(
        e.contains(&format!("range wire {}", WDIFF_0 + RUNGS)),
        "the refusal must be the QUORUM tooth on the top difference limb (col {}): {e}",
        WDIFF_0 + RUNGS
    );

    let mut forged = cells.clone();
    forged[WDIFF_0 + RUNGS] = 0;
    let e2 = must_refuse_violated_gate(
        "⚑ exactly 2/3 (top limb forced into range)",
        &d,
        &forged,
        &pis,
    );
    eprintln!("⚑ MIDNIGHT exactly-2/3, top limb forged to 0: {e2}");
}

/// ⚑ **THE CONTROL: THE SAME EXACTLY-2/3 ROW IS ADMITTED WHEN THE LIMB TABLE IS VACUOUS.**
///
/// One integer moves — the tally-limb table's declared width, 16 → 32, an interval covering the
/// whole field as the shipped 128 was meant to. At that width `p − 1 = 2013265920 < 2^32` is IN
/// range and the chain gates are satisfied identically over `𝔽_p` (they are ℤ identities, so they
/// hold mod `p`). **The sub-quorum PROVES.** That is what the per-limb containment buys: the chain
/// gates alone pin the difference to the operands, and the containment is what makes the difference
/// vector denote a NON-NEGATIVE integer (`LimbTally.limbValue_nonneg`).
#[test]
fn the_exactly_two_thirds_sub_quorum_is_admitted_when_the_limb_table_is_vacuous() {
    assert!(
        (1u64 << VACUOUS_BITS) > P as u64,
        "the control width must actually be vacuous — its interval must cover the field"
    );
    must_prove_under(
        "⚑ the SAME exactly-2/3 sub-quorum at a VACUOUS tally-limb width",
        &desc_with_limb_range_width(VACUOUS_BITS),
        honest(129, 86),
    );
    eprintln!(
        "⚑ MIDNIGHT exactly-2/3 ADMITTED at a vacuous 32-bit limb width — a GRANDPA justification \
         with no strict supermajority, accepted, which is what bits:128 shipped as"
    );
}

// ═══════════════════════════════════════════════════════════════════════════════════════════
// ⚑⚑ TOOTH 2 — THE EMPTY AUTHORITY SET, refused by BOTH floors
// ═══════════════════════════════════════════════════════════════════════════════════════════

/// ⚑⚑ **THE EMPTY AUTHORITY SET IS REFUSED — AND BY BOTH FLOORS INDEPENDENTLY.**
///
/// At `totalWeight = 0` the emptiness floor `TPOS = total − 1` fills to `−1`, and — because
/// Midnight's threshold is STRICT (`γ = 1`, unlike Solana's `γ = 0`) — the quorum chain
/// independently fills to `3·0 − 2·0 − 1 = −1`. A forger must defeat both.
///
/// The test DISARMS THEM ONE AT A TIME rather than asserting the pair: with the honest fill the
/// quorum's top limb is what the layout filler reaches first; force it into range and the refusal
/// MOVES to the floor chain's top limb (col 25); force both and an algebraic closure gate is what
/// is left standing. Two floors, three refusals, none of them the same one twice.
#[test]
fn the_empty_authority_set_is_refused_by_both_floors() {
    let j = honest(0, 0);
    let cells = row_cells(j);
    let d = desc();
    let pis = pis_of(j);

    let w = fill_chain(3, limbs4(0), 2, limbs4(0), 1);
    let t = fill_chain(1, limbs4(0), 0, limbs4(0), 1);
    assert_eq!(
        limb_value(&w.diff),
        -1,
        "3·0 − 2·0 − 1 = −1: the STRICT quorum fails"
    );
    assert_eq!(
        limb_value(&t.diff),
        -1,
        "0 − 1 = −1: the emptiness floor fails"
    );
    assert_eq!(felt(w.diff[RUNGS]).as_u32() as i64, P - 1);
    assert_eq!(felt(t.diff[RUNGS]).as_u32() as i64, P - 1);

    // Leg 1 — the QUORUM floor.
    let e1 = must_refuse_out_of_range("⚑⚑ the EMPTY authority set", &d, &cells, &pis);
    eprintln!("⚑⚑ MIDNIGHT empty authority set refused (quorum floor): {e1}");
    assert!(e1.contains(&format!("range wire {}", WDIFF_0 + RUNGS)));

    // Leg 2 — disarm the quorum floor and the EMPTINESS floor is what refuses.
    let mut q_forged = cells.clone();
    q_forged[WDIFF_0 + RUNGS] = 0;
    let e2 = must_refuse_out_of_range(
        "⚑⚑ the EMPTY authority set with the quorum's top limb forced into range",
        &d,
        &q_forged,
        &pis,
    );
    eprintln!("⚑⚑ MIDNIGHT empty authority set refused (emptiness floor): {e2}");
    assert!(
        e2.contains(&format!("range wire {}", TPOS_0 + RUNGS)),
        "with the quorum disarmed, the EMPTINESS floor (col {}) must be what bites: {e2}",
        TPOS_0 + RUNGS
    );

    // Leg 3 — disarm both range teeth and an algebraic closure gate is what is left.
    let mut both_forged = q_forged.clone();
    both_forged[TPOS_0 + RUNGS] = 0;
    let e3 = must_refuse_violated_gate(
        "⚑⚑ the EMPTY authority set with BOTH top limbs forced into range",
        &d,
        &both_forged,
        &pis,
    );
    eprintln!("⚑⚑ MIDNIGHT empty authority set, both top limbs forged to 0: {e3}");
}

/// ⚑ **AND THE CONTROL.** The empty authority set at a VACUOUS 32-bit limb width PROVES — a
/// GRANDPA justification signed by nobody, accepted by the deployed prover, at the shape this
/// descriptor shipped with.
#[test]
fn the_empty_authority_set_is_admitted_when_the_limb_table_is_vacuous() {
    must_prove_under(
        "⚑ the EMPTY authority set at a VACUOUS tally-limb width",
        &desc_with_limb_range_width(VACUOUS_BITS),
        honest(0, 0),
    );
    eprintln!(
        "⚑ MIDNIGHT EMPTY AUTHORITY SET ADMITTED at a vacuous 32-bit limb width — both floors had \
         no teeth at the width that shipped"
    );
}

// ═══════════════════════════════════════════════════════════════════════════════════════════
// ⚑ THE CHAINS' OWN TEETH
// ═══════════════════════════════════════════════════════════════════════════════════════════

/// ⚑ **A FORGED DIFFERENCE LIMB IS REFUSED — all TEN, five per chain.** Add one to a difference
/// limb, keeping it inside `[0, 2^16)` so the RANGE tooth still admits it; the rung's own gate (or,
/// for a top limb, the closure gate) no longer vanishes. This is what makes each difference vector
/// a DERIVED quantity rather than a claim.
///
/// ⚠ Run at the `u64` CEILING row, not the live one: at `total = 130` every limb above the first is
/// zero and a forgery there would be caught with the carry chain never having done any work.
#[test]
fn a_forged_difference_limb_is_refused_on_both_chains() {
    let j = honest(U64_CEILING, U64_CEILING_MIN_SUPERMAJORITY);
    let pis = pis_of(j);
    let honest_cells = row_cells(j);
    let d = desc();
    must_prove("the honest u64-ceiling pole", j);

    for (chain, base) in [
        ("WDIFF (quorum)", WDIFF_0),
        ("TPOS (empty-set floor)", TPOS_0),
    ] {
        for i in 0..=RUNGS {
            let mut forged = honest_cells.clone();
            // ⚠ Perturb whichever way keeps the limb INSIDE `[0, 2^16)`. At the `u64` ceiling the
            // floor chain's limbs are SATURATED (`65535`), so a blind `+1` would leave the interval
            // and the RANGE tooth — not the gate under test — would be what refused.
            forged[base + i] += if forged[base + i] == (1 << MID_LIMB_BITS) - 1 {
                -1
            } else {
                1
            };
            assert!(
                forged[base + i] >= 0 && forged[base + i] < (1 << MID_LIMB_BITS),
                "the forged limb must stay INSIDE the declared 16-bit interval, so the range tooth \
                 is not what catches it"
            );
            let reason = must_refuse_violated_gate(
                &format!("⚑ forged {chain} limb {i} (col {})", base + i),
                &d,
                &forged,
                &pis,
            );
            eprintln!("⚑ forged {chain} limb {i}: {reason}");
        }
    }
}

/// ⚑ **A FORGED CARRY IS REFUSED — all EIGHT, four per chain.** Each carry appears in exactly two
/// gates (weighted `−2^16` in the rung it exits, `+1` in the rung it enters), so one perturbation
/// breaks both.
///
/// ⚠ What this does NOT show: `LimbTally.chain_recomposes` holds for ANY integer carries — they
/// cancel pairwise. The carry lookups exist only for the mod-`p` ↔ ℤ bridge
/// (`mid_tpos_rung_no_alias_at_deployed_constants`). This measures that the CHAIN pins the carries
/// to the operands, not that the carry range check is load-bearing for soundness. It is not.
#[test]
fn a_forged_carry_is_refused_on_both_chains() {
    let j = honest(U64_CEILING, U64_CEILING_MIN_SUPERMAJORITY);
    let pis = pis_of(j);
    let honest_cells = row_cells(j);
    let d = desc();

    for (chain, base) in [
        ("WDIFF (quorum)", WDIFF_CARRY_0),
        ("TPOS (empty-set floor)", TPOS_CARRY_0),
    ] {
        for i in 0..RUNGS {
            let mut forged = honest_cells.clone();
            forged[base + i] += 1;
            assert!(
                forged[base + i] < (1 << MID_CARRY_BITS),
                "the forged carry must stay INSIDE the declared 8-bit interval"
            );
            let reason = must_refuse_violated_gate(
                &format!("⚑ forged {chain} carry {i} (col {})", base + i),
                &d,
                &forged,
                &pis,
            );
            eprintln!("⚑ forged {chain} carry {i}: {reason}");
        }
    }
}

/// ⚑ **A RE-SPELT DENOMINATOR IS REFUSED.** Both chains read the SAME four total-weight columns
/// (`mid_tpos_operands_are_the_total_weight_limbs`), so a forger who shrinks the denominator to
/// manufacture a supermajority breaks the emptiness floor at the same time. There is no second,
/// unchecked copy of the total to disagree with.
#[test]
fn a_re_spelt_denominator_is_refused() {
    let j = honest(U64_CEILING, U64_CEILING_MIN_SUPERMAJORITY);
    let pis = pis_of(j);
    let d = desc();
    for i in 0..RUNGS {
        let mut forged = row_cells(j);
        forged[TOTAL_WEIGHT_0 + i] -= 1;
        assert!(forged[TOTAL_WEIGHT_0 + i] >= 0);
        let reason = must_refuse_violated_gate(
            &format!(
                "⚑ a shrunk total-weight limb {i} (col {})",
                TOTAL_WEIGHT_0 + i
            ),
            &d,
            &forged,
            &pis,
        );
        eprintln!("⚑ shrunk denominator limb {i}: {reason}");
    }
}

// ═══════════════════════════════════════════════════════════════════════════════════════════
// The carrier and addressing teeth
// ═══════════════════════════════════════════════════════════════════════════════════════════

/// A forged CARRIER or logic bit — the Ed25519 aggregate verify, the authority-set-root compare,
/// the round binding or the era binding, cleared to `0` — is refused by its own gate.
///
/// ⚠ `ED_OK` / `AUTHSET_OK` are witnessed bits, not in-AIR crypto. What the AIR enforces is that a
/// prover claiming acceptance must ASSERT all four; the soundness behind them is consumed one layer
/// up, inside `mid_no_forgery`.
///
/// ⚑ `ROUND_OK` and `ERA_OK` are the CROSS-ROUND and STALE-AUTHORITY-SET refusals: a justification
/// replayed from a different GRANDPA round, or validated against a retired authority set, is what
/// those two bits exist to stop.
#[test]
fn a_cleared_carrier_or_logic_bit_is_refused() {
    for (name, col) in [
        ("ED_OK (aggregate Ed25519 verify)", ED_OK),
        ("AUTHSET_OK (authority-set root compare)", AUTHSET_OK),
        ("ROUND_OK (cross-round binding)", ROUND_OK),
        ("ERA_OK (stale-authority-set binding)", ERA_OK),
    ] {
        let j = honest(LIVE_TOTAL_WEIGHT, LIVE_MIN_SUPERMAJORITY);
        let mut cells = row_cells(j);
        assert_eq!(cells[col], 1, "the honest carrier is set");
        cells[col] = 0;
        let reason = must_refuse_violated_gate(
            &format!("a cleared carrier {name}"),
            &desc(),
            &cells,
            &pis_of(j),
        );
        eprintln!("cleared carrier {name}: {reason}");
    }
}

/// A forged PUBLIC ANCHOR: a target-root limb on the wire disagreeing with the published PI. The
/// nine `.piBinding` pins bind the WHOLE 256-bit finalized root — a SINGLE anchor felt bound only a
/// 31-bit PROJECTION, so two roots agreeing in 31 bits both verified. Perturbing any ONE of the nine
/// is refused, which is the observable half of that repair.
#[test]
fn a_target_root_limb_that_disagrees_with_its_public_input_is_refused() {
    let j = honest(LIVE_TOTAL_WEIGHT, LIVE_MIN_SUPERMAJORITY);
    let d = desc();
    for i in 0..TARGET_ROOT_LIMBS {
        let mut cells = row_cells(j);
        cells[TARGET_ROOT_0 + i] += 1;
        let reason = must_refuse_violated_gate(
            &format!("a target-root limb {i} disagreeing with its PI pin"),
            &d,
            &cells,
            &pis_of(j),
        );
        eprintln!("forged target-root limb {i}: {reason}");
    }
}

/// The round and era anchors are PI-pinned too: a proof about round R, era E must say so publicly.
/// This is the addressing half of the cross-round / stale-set story — `ROUND_OK` and `ERA_OK` say
/// the counted precommits agree with the claimed values, and these pins say what was claimed.
#[test]
fn a_round_or_era_that_disagrees_with_its_public_input_is_refused() {
    for (name, col) in [("GRANDPA round", ROUND_COL), ("authority-set era", ERA_COL)] {
        let j = honest(LIVE_TOTAL_WEIGHT, LIVE_MIN_SUPERMAJORITY);
        let mut cells = row_cells(j);
        cells[col] += 1;
        let reason = must_refuse_violated_gate(
            &format!("a {name} disagreeing with its PI pin"),
            &desc(),
            &cells,
            &pis_of(j),
        );
        eprintln!("forged {name}: {reason}");
    }
}

// ═══════════════════════════════════════════════════════════════════════════════════════════
// ⚑ THE SECOND DEFECT — CLOSED 2026-08-03: the over-wide width is REFUSED AT DESCRIPTOR LOAD
// ═══════════════════════════════════════════════════════════════════════════════════════════

/// The served descriptor's own JSON bytes, so a width substitution below is done to the REAL wire
/// object rather than to a hand-typed stand-in.
const MIDNIGHT_LC_JSON: &str =
    include_str!("../descriptors/by-name/dregg-midnight-lightclient-verify-v1.json");

/// ⚑⚑ **THE WIDTH THAT SHIPPED IS NOW REFUSED AT THE DOOR, AND THIS TEST CHANGED MEANING.**
///
/// # What it used to assert, and why that was the bug and not the tooth
///
/// `dregg-midnight-lightclient-verify::v1` shipped `bits: 128` on its range table. In Lean's `rangeRows 128` that interval
/// contains every BabyBear element and the tooth refuses NOTHING. In the deployed Rust prover it
/// refused EVERYTHING: the layout filler's bound was `(v as u64) >= (1u64 << rb.bits)`, and a `u64`
/// shift by 128 masks to a shift by 0, so the test collapsed to `v >= 1` and every nonzero value on
/// a ranged wire was refused (`row 0: range wire 4 value 62195 >= 2^128`). Under `cargo test` the
/// same expression was an OVERFLOW PANIC. **That was the mechanical reason no prover had ever run
/// this descriptor: the first honest attempt would have been refused.**
///
/// This harness EXHIBITED that as a tooth. It was never a tooth — it was the defect wearing one.
///
/// # What it asserts now
///
/// Both halves of the repair, on the real bytes:
///
///  1. **The declaration is REFUSED AT LOAD.** `parse_vm_descriptor2` rejects a range table at or
///     above `VACUOUS_RANGE_BITS = 31`, naming the reason. A width that refuses nothing at BabyBear
///     is a defect however it got onto the wire, so it cannot be served at all — this is the gate,
///     and it is at the DOOR rather than deep in the prover.
///  2. **The mask is gone.** The filler's bound is now total (`value_fits_bits`), so a descriptor
///     constructed IN MEMORY at a vacuous width behaves the way its denotation says: it admits
///     everything, including the honest row. That is the difference between "the prover disagrees
///     with `rangeRows`" and "the prover implements it".
///
/// ⚠ The in-memory path is deliberately left open: that is exactly what a vacuity CONTROL does
/// (`the_*_is_admitted_when_the_width_is_vacuous`), and a control that could not construct a vacuous
/// width could not measure vacuity.
#[test]
fn the_shipped_128_bit_width_refuses_even_an_honest_justification() {
    // ── 1. LOAD REFUSES the width, on the real served bytes with one integer moved.
    let served = MIDNIGHT_LC_JSON;
    assert!(
        parse_vm_descriptor2(served).is_ok(),
        "the SERVED descriptor must still load — its declared widths are 16 and 8"
    );
    for bad in [31usize, 32, 64, SHIPPED_MID_BITS] {
        let mutated = served.replace("\"bits\":16", &format!("\"bits\":{bad}"));
        assert_ne!(mutated, served, "the width substitution must have bitten");
        let e = parse_vm_descriptor2(&mutated)
            .expect_err("a range table at or above 31 bits must be REFUSED AT LOAD");
        assert!(
            e.contains(&format!("declares bits {bad}")) && e.contains("refuses nothing"),
            "the refusal must name the width and the reason, got: {e}"
        );
        eprintln!("⚑ dregg-midnight-lightclient-verify::v1 at bits={bad}: REFUSED AT LOAD — {e}");
    }

    // ── 2. THE MASK IS GONE: the honest row, at an in-memory vacuous width, now PROVES.
    //     Before the repair this was `row 0: range wire N value V >= 2^128` in release and a
    //     `shift left with overflow` panic under `cargo test`. The denotation always said it should
    //     be admitted; now the prover says so too.
    let j = honest(LIVE_TOTAL_WEIGHT, LIVE_MIN_SUPERMAJORITY);
    must_prove("the honest live-scale j at the declared limb widths", j);
    must_prove_under(
        "⚑ the SAME honest j at an in-memory bits=128 — vacuous, therefore ADMITTED",
        &desc_with_limb_range_width(SHIPPED_MID_BITS),
        j,
    );
    eprintln!(
        "⚑ dregg-midnight-lightclient-verify::v1: the honest j now PROVES at an in-memory bits=128 (vacuous, admits \
         everything) instead of being refused by a masked comparison — and bits=128 can no \
         longer be LOADED at all"
    );
}
