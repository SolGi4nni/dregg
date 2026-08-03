//! ⚑ **A TENDERMINT LIGHT CLIENT PROVED AT COMETBFT'S PROTOCOL MAXIMUM — ON THE DEPLOYED PROVER.**
//!
//! # What had never happened, in three layers
//!
//! **Layer 1 — nothing had ever proved it.** Five peer chains have a Lean-authored light-client
//! verify AIR routed through `EmitByName.lean` into `circuit/src/descriptor_by_name.rs`. Measured
//! 2026-08-02, **none of the four non-Mina ones had ever been proved**:
//! `grep -rl lightclient-verify --include='*.rs'` returned only `descriptor_by_name.rs`.
//! "Producible by a node" was a claim about DISPATCH — a descriptor that decodes and a name that
//! resolves, with no prover ever having run the object. Mina closed 2026-08-02
//! (`turn/tests/mina_anchored_head_lands.rs`). This file closed Tendermint.
//!
//! **Layer 2 — the range width was vacuous.** `dregg-tm-lightclient-verify::v1` shipped `bits: 64`
//! on its range table. BabyBear is `p = 2013265921 < 2^31 < 2^64`, so the declared interval
//! `[0, 2^64)` **already contained every field element** and every range lookup refused nothing
//! (`Dregg2.Circuit.RangeFieldContainment.range_vacuous_at_or_above_31`, over all widths `≥ 31` and
//! all field elements — a theorem, not a witness). Every INEQUALITY in the AIR — the strict `>2/3`
//! voting-power threshold and the three time-window bounds — rides as a non-negative slack, because
//! a field has no order. At 64 bits every one of them was satisfied by any assignment. `TM_BITS` is
//! now **29**, the maximum wrap-free width at BabyBear (`wrap_free_iff_le_29`; 30 already fails),
//! and the three TIME teeth still ride it — `the_shipped_64_bit_width_refuses_even_an_honest_header`
//! and the two `…_is_admitted_when_vacuous` legs below are that repair, both polarities, measured.
//!
//! **Layer 3 — ⚑ AND THE REPAIR EXPOSED A WOUND IT COULD NOT CLOSE: THE TALLY NEVER FIT.**
//! `TOTAL_POW` and `SIGNED_POW` were ONE BabyBear COLUMN EACH. A felt holds 30.9 bits. CometBFT's
//! `MaxTotalVotingPower = int64(math.MaxInt64)/8 = 2^60 − 1 = 1152921504606846975`
//! (`cometbft/types/validator_set.go:27`) is **572 million times the modulus**. It did not fit at 29
//! bits, it did not fit at the 64 that shipped, and it would not have fit at 128: a declared width
//! declares an INTERVAL, and the wire is one field element. The 64-bit declaration did not make the
//! tally fit — **it made the shortfall invisible**, and the 29-bit repair made it visible and no
//! smaller. The client was sound and could not represent a real validator set.
//!
//! # What this file now measures
//!
//! The tally is a **LIMB VECTOR**: four 16-bit limbs each — exactly a `u64`, exactly CometBFT's own
//! wire type for voting power — with the strict-threshold difference `3·signedPow − 2·totalPow − 1`
//! carried as its own five-limb vector tied to the operands by an offset borrow chain
//! (`Dregg2.Circuit.LimbTally`, `Dregg2.Circuit.Emit.LightClientTendermintAir` §3c/§7). Trace width
//! 29 → **43**; one range table → **three** (29 / 16 / 8); one threshold gate and one lookup →
//! **five generated chain gates and seventeen per-limb lookups**.
//!
//! `the_protocol_maximum_validator_set_proves` hands the deployed Rust prover a validator set at
//! `MaxTotalVotingPower` with the SMALLEST strictly-supermajority signed power
//! (`768614336404564651`), and it PROVES and VERIFIES.
//! `one_unit_below_the_threshold_is_refused_at_the_protocol_maximum` moves ONE unit of voting power
//! out of 2^60 and the same row is REFUSED.
//!
//! ⚑ **AND THE REFUSAL NO LONGER MENTIONS THE FIELD.** The single-felt tooth refused the exactly-2/3
//! sub-quorum because `p − 1 ∉ [0, 2^29)` — a fact about the FIELD SIZE, false at 30, catastrophically
//! false at 64, and the entire reason a width census had to happen. The limbed tooth refuses it
//! because a vector of non-negative limbs denotes a non-negative value and the difference is `−1`.
//! That statement is `LightClientTendermintAir.tmLcAir_refuses_exactly_two_thirds_at_max_voting_power`
//! (and `LimbTally.refusal_is_field_independent`, quantified over EVERY limb width, in EVERY field) —
//! a Lean theorem over the emitted gate bodies, and **there is deliberately no Rust imitation of it
//! here**: a Rust case-test quantifies over nothing. What Rust measures is the complementary,
//! machine-specific half — that the DEPLOYED prover refuses the honest fill of that row, and that
//! the obvious repair (forcing the out-of-range top difference limb to zero) is caught by the chain's
//! closure gate instead. `the_exactly_two_thirds_sub_quorum_is_refused` runs the sub-quorum at a
//! VACUOUS time-range width as well, which is the observable shadow of field-independence: the felt
//! range table is no longer what refuses it.
//!
//! # The honest fill, and why it is a loop rather than a table of constants
//!
//! `fill_tally` is `LimbTally.fillDigit` / `LimbTally.fillCarry` transcribed: floor-mod digit, exact
//! floor-division carry, offset by `TALLY_CARRY_OFF = 128` on the wire because a difference chain
//! BORROWS and a field wire has no sign. It is written as a loop over the four rungs so the harness
//! works at any tally, and `the_honest_fill_reproduces_the_lean_row` pins its output for the
//! protocol-maximum row against `LightClientTendermintAir.tmMaxScaleCells` — the same 43 numbers in
//! the same order, hand-written in Lean and `decide`-checked there, computed here. Two independent
//! sources, one object.
//!
//! # Scope, said plainly
//!
//! `ED_OK` / `VSET_OK` / `EPOCH_OK` are witnessed carrier bits, not in-AIR Ed25519 and SHA-256; the
//! dregg-side STARK inherits the undischarged FRI floor. The mod-`p` ↔ ℤ residual that every Emit
//! descriptor names is DISCHARGED for the chain gates (`LimbTally.rung_no_alias_at_deployed_constants`
//! — the reachable ℤ image is 236× inside `p`, with a measured failure point at limb width 24) and
//! still stands for the rest. This is a prover running the served object; it is **not**
//! "Tendermint-valid", and it is not "machine-checked".
//!
//! ⚠ And the residual this change did NOT close, stated because it is now the only one of its kind
//! left in the file: the three TIME slacks still ride the 29-bit felt table. CometBFT header times are
//! `google.protobuf.Timestamp` with NANOSECONDS, where a 14-day trusting period is `1.2096e15` (50.1
//! bits) and does not fit — the caller must supply SECONDS, and every row here does. The identical
//! limb machinery closes it (`1·X − 1·Y − γ ≥ 0` is the same shape at `α = β = 1`). Named, measured,
//! not done.
//!
//! ⚠ **PROFILE.** plonky3's ALGEBRAIC refusals are `#[cfg(debug_assertions)]` panics under
//! `cargo test` and clean `Err(OodEvaluationMismatch)` under `--release`; RANGE refusals are `Err` in
//! both. The refusals here are a mix — a forged difference limb is algebraic, an out-of-range limb is
//! a range refusal — so every one of them goes through `dregg_circuit::refusal`, which discriminates
//! the two mechanisms identically in both profiles and REDS on a crash wearing a refusal's clothes.

use dregg_circuit::BabyBear;
use dregg_circuit::descriptor_by_name::descriptor_by_name;
use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, MemBoundaryWitness, TableSem, prove_vm_descriptor2, verify_vm_descriptor2,
};
use dregg_circuit::heap_root::HeapLeaf;
use dregg_circuit::refusal;

const TM_LC_VERIFY_DESCRIPTOR: &str = "dregg-tm-lightclient-verify::v1";

// ═══════════════════════════════════════════════════════════════════════════════════════════
// Trace column layout — pinned to `LightClientTendermintAir`'s Lean `def`s (§1).
// ⚑ It was 29 columns. The +14 is the tally becoming REPRESENTABLE: two `u64` operands, their
// five-limb difference, and the four-rung borrow chain that ties them.
// ═══════════════════════════════════════════════════════════════════════════════════════════

const CHAIN_ID: usize = 0;
const TS_CHAIN_ID: usize = 1;
const HEIGHT: usize = 2;
const TS_HEIGHT: usize = 3;
const HEADER_TIME: usize = 4;
const TIME: usize = 5;
const NOW: usize = 6;
const CLOCK_DRIFT: usize = 7;
const TRUSTING_PERIOD: usize = 8;
const TW_MONO: usize = 9;
const TW_DRIFT: usize = 10;
const TW_TRUST: usize = 11;
const ED_OK: usize = 12;
const VSET_OK: usize = 13;
const EPOCH_OK: usize = 14;
/// `TOTAL_POW` limb 0 (LSB). Limbs 0..3 are columns 15..18.
const TOTAL_POW_0: usize = 15;
/// `SIGNED_POW` limb 0 (LSB). Limbs 0..3 are columns 19..22.
const SIGNED_POW_0: usize = 19;
/// `TDIFF` limb 0 (LSB). FIVE limbs, columns 23..27 — `3·A` needs two bits beyond `A`.
const TDIFF_0: usize = 23;
/// The offset carry out of rung 0. Four carries, columns 28..31; each denotes `col − 128`.
const TDIFF_CARRY_0: usize = 28;
const TRUSTED_NEXT_VALS_ROOT: usize = 32;
const COMMITTED_APP_HASH_0: usize = 33;
const APP_HASH_LIMBS: usize = 9;
const CHAIN_ID_DOMAIN: usize = 42;

const TM_LC_WIDTH: usize = 43;
const TM_PI_COUNT: usize = 11;

/// The time-slack width. `2^29 = 536870912` — the maximum WRAP-FREE width at BabyBear.
const TM_BITS: usize = 29;
/// The tally limb width. `4 · 16 = 64` — four limbs are exactly a `u64`.
const TM_LIMB_BITS: usize = 16;
/// The chain-carry width (the prover's own byte bus: one aux column, one byte lookup).
const TM_CARRY_BITS: usize = 8;

/// Declared wire id of the 29-bit time-slack table (`TableId.range`).
const TID_TIME_RANGE: usize = 2;
/// Declared wire id of the 16-bit tally-limb table (`.custom (64 + 16)` ⇒ `5 + 80`).
const TID_TALLY_LIMB: usize = 85;
/// Declared wire id of the 8-bit chain-carry table (`.custom (64 + 8)` ⇒ `5 + 72`).
const TID_TALLY_CARRY: usize = 77;

/// The offset a carry rides at on the wire: a difference chain BORROWS, and a field wire has no
/// sign, so `c` is written `c + 128` with the declared range `[0, 2^8)` giving `c ∈ [−128, 127]`.
/// The honest chain never leaves `[−3, 2]` (`LimbTally.honest_carry_window`).
const CARRY_OFF: i64 = 128;

/// The number of tally rungs. Four rungs generate FIVE gate bodies — one per rung plus the closure
/// gate that forces the final carry into the top difference limb.
const TALLY_RUNGS: usize = 4;

/// The width that SHIPPED on the time table.
///
/// ⚑ In the DENOTATION (`DescriptorIR2.rangeRows 64`) this interval contains every BabyBear element,
/// so it refuses nothing. In the DEPLOYED Rust prover it refuses EVERYTHING — see
/// `the_shipped_64_bit_width_refuses_even_an_honest_header`. The two readings of the same declared
/// constant disagree maximally, and nothing had ever run to notice.
const SHIPPED_TM_BITS: usize = 64;

/// The smallest FULLY VACUOUS width (`2^32 > p`, so `[0, 2^32)` covers the field) that the deployed
/// prover can still execute — `1u64 << 32` is well-defined where `1u64 << 64` is not.
const VACUOUS_BITS: usize = 32;

/// `LightClientTendermintAir` pads to a FRI-shaped power-of-two row count; the gates are single-row
/// and the pins are first-row, so every row is the same logical row.
const TRACE_ROWS: usize = 8;

const P: i64 = 2_013_265_921;

fn desc() -> EffectVmDescriptor2 {
    descriptor_by_name(TM_LC_VERIFY_DESCRIPTOR).unwrap_or_else(|| {
        panic!(
            "{TM_LC_VERIFY_DESCRIPTOR} must dispatch: the Lean-emitted descriptor is routed through \
             EmitByName.lean and included by circuit/src/descriptor_by_name.rs"
        )
    })
}

/// The SAME served descriptor with the **29-bit TIME table's** declared width set to `bits`.
///
/// ⚑ This is the control for the three time-window teeth. A repair that only shows the NEW width
/// refusing a value has not shown the value was ever admitted; this hands the identical trace to the
/// identical AIR under the identical prover, differing in exactly one integer.
///
/// ⚠ It touches table `2` ONLY. The 16-bit tally and 8-bit carry tables are left alone, because the
/// threshold no longer rides a felt interval — widening the time table must not, and does not, move
/// the threshold tooth. `the_exactly_two_thirds_sub_quorum_is_refused` measures exactly that.
fn desc_with_time_range_width(bits: usize) -> EffectVmDescriptor2 {
    let mut d = desc();
    let mut touched = 0usize;
    for t in d.tables.iter_mut() {
        if t.id == TID_TIME_RANGE {
            if let TableSem::Range { bits: b } = &mut t.sem {
                *b = bits;
                touched += 1;
            }
        }
    }
    assert_eq!(
        touched, 1,
        "exactly the 29-bit time table must be re-declared; the tally tables stay at 16/8"
    );
    d
}

/// Field-encode a possibly-negative integer: in BabyBear a negative value IS `p − k`, which is the
/// element a range tooth must refuse. This is where a failed quorum's `TDIFF` top limb lands.
fn felt(v: i64) -> BabyBear {
    BabyBear::new(v.rem_euclid(P) as u32)
}

// ═══════════════════════════════════════════════════════════════════════════════════════════
// ⚑ THE HONEST FILL — `LimbTally.fillDigit` / `LimbTally.fillCarry`, transcribed as a LOOP.
// ═══════════════════════════════════════════════════════════════════════════════════════════

/// The tally block of one row: the two operands' limbs, the difference's five limbs, and the four
/// OFFSET carries. Everything as `i64` so a failed quorum's negative top limb is expressible —
/// that value is precisely what a refusal test wants to hand the prover.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct TallyFill {
    /// `totalPow` as four 16-bit limbs, LSB first.
    total: [i64; TALLY_RUNGS],
    /// `signedPow` as four 16-bit limbs, LSB first.
    signed: [i64; TALLY_RUNGS],
    /// `3·signedPow − 2·totalPow − 1` as FIVE 16-bit limbs, LSB first. `diff[4]` IS the final carry.
    diff: [i64; TALLY_RUNGS + 1],
    /// The carry out of each rung, OFFSET: `carry[i] = c_{i+1} + 128`.
    carry: [i64; TALLY_RUNGS],
}

/// ⚑ **THE HONEST FILL.** `α = 3` on signed power, `β = 2` on total power, `γ = 1` for the STRICT
/// inequality — CometBFT's `3·S > 2·T` (`tendermint-rs/tendermint/src/trust_threshold.rs:98`).
///
/// Written as a loop over the rungs rather than a table of constants, so the harness fills ANY
/// tally a `u64` holds — which is the entire capability under measurement. `fillDigit` is a FLOOR
/// mod (`rem_euclid`, always in `[0, 2^16)` by construction, never by check) and `fillCarry` is the
/// exact floor quotient, so `raw − d − c·2^16 = 0` holds identically (`LimbTally.fill_splits`).
///
/// ⚠ When the quorum FAILS the final carry is NEGATIVE and `diff[4]` comes out negative. That is
/// the refusal, and this function expresses it rather than hiding it: the caller puts `p + v` on the
/// wire, which is the element the 16-bit tooth has no row for.
fn fill_tally(total: u64, signed: u64) -> TallyFill {
    let radix: i64 = 1 << TM_LIMB_BITS;
    let mut t = [0i64; TALLY_RUNGS];
    let mut s = [0i64; TALLY_RUNGS];
    for i in 0..TALLY_RUNGS {
        t[i] = ((total >> (TM_LIMB_BITS * i)) & 0xFFFF) as i64;
        s[i] = ((signed >> (TM_LIMB_BITS * i)) & 0xFFFF) as i64;
    }
    let mut diff = [0i64; TALLY_RUNGS + 1];
    let mut carry = [0i64; TALLY_RUNGS];
    let mut c: i64 = 0;
    for i in 0..TALLY_RUNGS {
        let gamma = if i == 0 { 1 } else { 0 };
        let raw = 3 * s[i] - 2 * t[i] - gamma + c;
        let d = raw.rem_euclid(radix);
        // Exact: `raw − d` is a multiple of the radix, so truncating and floor division agree.
        c = (raw - d) / radix;
        diff[i] = d;
        carry[i] = c + CARRY_OFF;
    }
    // The chain's CLOSURE: the operands have run out, so the final carry IS the top digit. Without
    // this the prover could dump a residue into a carry nothing reads and the recomposition would
    // be off by `2^64` (`LimbTally.ChainOk`, the `[]` case).
    diff[TALLY_RUNGS] = c;
    TallyFill {
        total: t,
        signed: s,
        diff,
        carry,
    }
}

/// The value the difference limb vector denotes, over ℤ (`LimbTally.limbValue`, LSB-first Horner).
/// Used only to re-assert, in the harness, that the fill really recomposes.
fn limb_value(limbs: &[i64]) -> i128 {
    let mut acc: i128 = 0;
    for &l in limbs.iter().rev() {
        acc = acc * (1i128 << TM_LIMB_BITS) + l as i128;
    }
    acc
}

// ═══════════════════════════════════════════════════════════════════════════════════════════
// One logical row of the Tendermint verify decision
// ═══════════════════════════════════════════════════════════════════════════════════════════

#[derive(Clone, Copy)]
struct Header {
    chain_id: u32,
    ts_chain_id: u32,
    height: u32,
    ts_height: u32,
    header_time: u32,
    time: u32,
    now: u32,
    clock_drift: u32,
    trusting_period: u32,
    /// ⚑ `u64`, not `u32`. CometBFT voting power is `int64`; the tally rides four 16-bit limbs.
    total_pow: u64,
    /// ⚑ `u64`. The Ed25519-VERIFIED signed power, whose provenance is the `ED_OK` carrier.
    signed_pow: u64,
    ed_ok: u32,
    vset_ok: u32,
    epoch_ok: u32,
    next_vals: u32,
    app_hash: [u32; APP_HASH_LIMBS],
    domain: u32,
}

/// The 32-byte anchors this descriptor publishes, as the nine radix-`2^31` MSB-first limbs the Lean
/// module pins (`COMMITTED_APP_HASH_LIMBS = 9`, `⌈256/31⌉ = 9`).
fn limbs9(seed: u32) -> [u32; APP_HASH_LIMBS] {
    let mut out = [0u32; APP_HASH_LIMBS];
    for (i, o) in out.iter_mut().enumerate() {
        // Any in-field limb values will do: this leg is the PI-binding shape, not the hash.
        *o = seed.wrapping_mul(2_654_435_761).wrapping_add(i as u32 * 7) % 0x7fff_ffff;
    }
    out
}

/// An HONEST header: every slack is COMPUTED from the identity its gate forces, never claimed.
/// A caller cannot hand this a slack or a difference limb; it can only hand it the facts they are
/// derived from.
#[allow(clippy::too_many_arguments)]
fn honest(
    height: u32,
    ts_height: u32,
    header_time: u32,
    time: u32,
    now: u32,
    clock_drift: u32,
    trusting_period: u32,
    total_pow: u64,
    signed_pow: u64,
) -> Header {
    Header {
        chain_id: 0x0c05_0001,
        ts_chain_id: 0x0c05_0001,
        height,
        ts_height,
        header_time,
        time,
        now,
        clock_drift,
        trusting_period,
        total_pow,
        signed_pow,
        ed_ok: 1,
        vset_ok: 1,
        epoch_ok: 1,
        next_vals: 0x51a7_e001,
        app_hash: limbs9(0xa17c_0de1),
        domain: 0x0c05_0001,
    }
}

/// The 43 cells of one logical row, **as integers** — the same 43 numbers, in the same order, as
/// `LightClientTendermintAir.tmMaxScaleCells`. Kept in `i64` so a forgery test can perturb a cell
/// and so a failed quorum's negative top difference limb survives to `felt` unaltered.
fn row_cells(h: Header) -> Vec<i64> {
    let tally = fill_tally(h.total_pow, h.signed_pow);
    let mut r = vec![0i64; TM_LC_WIDTH];

    r[CHAIN_ID] = h.chain_id as i64;
    r[TS_CHAIN_ID] = h.ts_chain_id as i64;
    r[HEIGHT] = h.height as i64;
    r[TS_HEIGHT] = h.ts_height as i64;
    r[HEADER_TIME] = h.header_time as i64;
    r[TIME] = h.time as i64;
    r[NOW] = h.now as i64;
    r[CLOCK_DRIFT] = h.clock_drift as i64;
    r[TRUSTING_PERIOD] = h.trusting_period as i64;

    // The three TIME slack identities, verbatim from `LightClientTendermintAir` §2. These still
    // ride the 29-bit felt table — the residual named in the module header.
    r[TW_MONO] = h.time as i64 - h.header_time as i64 - 1;
    r[TW_DRIFT] = h.now as i64 + h.clock_drift as i64 - h.time as i64;
    r[TW_TRUST] = h.header_time as i64 + h.trusting_period as i64 - h.now as i64 - 1;

    r[ED_OK] = h.ed_ok as i64;
    r[VSET_OK] = h.vset_ok as i64;
    r[EPOCH_OK] = h.epoch_ok as i64;

    // The tally block, columns 15..31: four total-power limbs, four signed-power limbs, five
    // difference limbs, four offset carries — contiguous, LSB first, exactly as §1 lays them out.
    r[TOTAL_POW_0..TOTAL_POW_0 + TALLY_RUNGS].copy_from_slice(&tally.total);
    r[SIGNED_POW_0..SIGNED_POW_0 + TALLY_RUNGS].copy_from_slice(&tally.signed);
    r[TDIFF_0..TDIFF_0 + TALLY_RUNGS + 1].copy_from_slice(&tally.diff);
    r[TDIFF_CARRY_0..TDIFF_CARRY_0 + TALLY_RUNGS].copy_from_slice(&tally.carry);

    r[TRUSTED_NEXT_VALS_ROOT] = h.next_vals as i64;
    for (i, l) in h.app_hash.iter().enumerate() {
        r[COMMITTED_APP_HASH_0 + i] = *l as i64;
    }
    r[CHAIN_ID_DOMAIN] = h.domain as i64;
    r
}

/// The eleven published anchors, in PI order.
fn pis_of(h: Header) -> Vec<BabyBear> {
    let mut pis = vec![BabyBear::new(0); TM_PI_COUNT];
    pis[0] = BabyBear::new(h.next_vals);
    for (i, l) in h.app_hash.iter().enumerate() {
        pis[1 + i] = BabyBear::new(*l);
    }
    pis[10] = BabyBear::new(h.domain);
    pis
}

/// Field-encode the integer row into the `TRACE_ROWS`-tall trace the prover ingests.
fn trace_of(cells: &[i64]) -> Vec<Vec<BabyBear>> {
    let row: Vec<BabyBear> = cells.iter().map(|&v| felt(v)).collect();
    vec![row; TRACE_ROWS]
}

/// PROVE and VERIFY, both legs, exactly as a deployed consumer would.
///
/// Refusals arrive in three shapes and all three are refusals: an `Err` from the prover's layout
/// filler (how the RANGE teeth refuse — `row 0: range wire N value V >= 2^16`), a `#[cfg(debug_
/// assertions)]` panic out of plonky3's constraint check (how the ALGEBRAIC chain gates refuse
/// under `cargo test`), and an `Err(OodEvaluationMismatch)` from the producer self-verify (how the
/// same gate refuses under `--release`). Discriminating them is `dregg_circuit::refusal`'s job, so
/// this function does not catch anything — the caller wraps it.
fn prove_and_verify(
    d: &EffectVmDescriptor2,
    cells: &[i64],
    pis: &[BabyBear],
) -> Result<(), String> {
    let trace = trace_of(cells);
    refusal::assert_committed_shape("tm lightclient", d, &trace, pis);
    let mem = MemBoundaryWitness::default();
    let heaps: Vec<Vec<HeapLeaf>> = vec![];
    let proof = prove_vm_descriptor2(d, &trace, pis, &mem, &heaps)
        .map_err(|e| format!("prover refused: {e}"))?;
    verify_vm_descriptor2(d, &proof, pis).map_err(|e| format!("verifier refused: {e:?}"))
}

/// The honest pole through the served descriptor. Panics (with the underlying reason) if the honest
/// witness is REJECTED — an honest pole that fails makes every paired refusal vacuous.
fn must_prove(what: &str, h: Header) {
    must_prove_under(what, &desc(), h);
}

fn must_prove_under(what: &str, d: &EffectVmDescriptor2, h: Header) {
    let cells = row_cells(h);
    let pis = pis_of(h);
    refusal::must_accept(what, || prove_and_verify(d, &cells, &pis));
}

/// A RANGE refusal: the prover's layout filler has no honest completion for a wire whose value sits
/// outside its declared interval. An `Err` in EVERY profile — never a panic, never debug-only.
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

/// An ALGEBRAIC refusal: some emitted gate does not vanish on the row. Under `cargo test` this is
/// p3's `constraints not satisfied on row N`; under `--release` it is the deployed verifier's
/// `OodEvaluationMismatch`. The load-bearing half is the NEGATIVE clause — a tooth whose subject is
/// a specific gate must not be satisfied by the lookup bus failing instead.
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

/// An honest adjacent header: height 1001 on trust at 1000, second-resolution times, a genuine
/// supermajority (`signedPow = 700` of `totalPow = 1000` — comfortably over 2/3).
fn honest_header() -> Header {
    honest(
        1001,
        1000,
        1_700_000_000,
        1_700_000_006,
        1_700_000_010,
        5,
        1_209_600,
        1000,
        700,
    )
}

// ═══════════════════════════════════════════════════════════════════════════════════════════
// ⚑ THE PROTOCOL MAXIMUM — the row the whole change exists for
// ═══════════════════════════════════════════════════════════════════════════════════════════

/// CometBFT's `MaxTotalVotingPower = int64(math.MaxInt64) / 8 = 2^60 − 1`
/// (`cometbft/types/validator_set.go:27`). 572 million times the BabyBear modulus.
const MAX_TOTAL_VOTING_POWER: u64 = 1_152_921_504_606_846_975;

/// The SMALLEST signed power satisfying CometBFT's strict `3·S > 2·T` at `MaxTotalVotingPower`.
const MIN_STRICT_SUPERMAJORITY: u64 = 768_614_336_404_564_651;

/// Cosmos Hub's LIVE total voting power — 328,774,071 across 180 validators at height 32,325,597,
/// measured 2026-08-03 via `cosmos-rpc.polkachu.com/validators`.
const COSMOS_HUB_TOTAL_POWER: u64 = 328_774_071;

/// The protocol-maximum row, cell for cell the one `LightClientTendermintAir.tmMaxScaleCells`
/// declares — chain id 7, Cosmos Hub's live height, second-resolution times, a 14-day trusting
/// period, and the modal 40s clock drift.
fn protocol_max_header() -> Header {
    Header {
        chain_id: 7,
        ts_chain_id: 7,
        height: 32_325_598,
        ts_height: 32_325_597,
        header_time: 1_785_734_519,
        time: 1_785_734_619,
        now: 1_785_734_624,
        clock_drift: 40,
        trusting_period: 1_209_600,
        total_pow: MAX_TOTAL_VOTING_POWER,
        signed_pow: MIN_STRICT_SUPERMAJORITY,
        ed_ok: 1,
        vset_ok: 1,
        epoch_ok: 1,
        next_vals: 11111,
        app_hash: [1, 2, 3, 4, 5, 6, 7, 8, 9],
        domain: 22222,
    }
}

/// `LightClientTendermintAir.tmMaxScaleCells`, transcribed. The Lean side hand-writes these 43
/// numbers and `decide`s that they denote `MaxTotalVotingPower`; the Rust side COMPUTES them from
/// `fill_tally`. Two independent sources for one object — which is the only kind of pin worth
/// having.
const LEAN_MAX_SCALE_CELLS: [i64; TM_LC_WIDTH] = [
    7,
    7,
    32_325_598,
    32_325_597,
    1_785_734_519,
    1_785_734_619,
    1_785_734_624,
    40,
    1_209_600,
    99,
    45,
    1_209_494,
    1,
    1,
    1,
    65535,
    65535,
    65535,
    4095,
    43691,
    43690,
    43690,
    2730,
    2,
    0,
    0,
    0,
    0,
    128,
    128,
    128,
    128,
    11111,
    1,
    2,
    3,
    4,
    5,
    6,
    7,
    8,
    9,
    22222,
];

// ═══════════════════════════════════════════════════════════════════════════════════════════
// The served object
// ═══════════════════════════════════════════════════════════════════════════════════════════

/// The descriptor this tree serves is the one the Lean module declares — width, PI count,
/// constraint count, and all THREE declared range widths.
#[test]
fn the_served_descriptor_is_the_lean_emitted_one() {
    let d = desc();
    assert_eq!(d.name, TM_LC_VERIFY_DESCRIPTOR);
    assert_eq!(
        d.trace_width, TM_LC_WIDTH,
        "⚑ the tally became a limb vector: 29 → 43 columns"
    );
    assert_eq!(d.public_input_count, TM_PI_COUNT);
    // 2 shape gates + 3 time gates + 3 time lookups + 17 tally lookups + 5 generated chain gates
    // + 3 carrier gates + 11 PI pins = 44 (`LightClientTendermintAir.tm_shape_pins`).
    assert_eq!(d.constraints.len(), 44);
    assert_eq!(
        d.tables.len(),
        3,
        "⚑ THREE declared range widths where there was one"
    );

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

    // The 29-bit TIME table — the wrap-free repair, still load-bearing for the three time teeth.
    //
    // ⚠ Every check below reads the width OUT OF THE SERVED DESCRIPTOR (`served_time_bits`) rather
    // than out of this file's `TM_BITS`. A constant compared against its own definition is
    // decoration; these are the emitted object measured against the field it is evaluated in, so a
    // re-emission that moved the width would red them.
    let served_time_bits = bits_of(TID_TIME_RANGE);
    assert_eq!(served_time_bits, TM_BITS);
    assert!(
        (1i64 << served_time_bits) < P,
        "the declared interval must sit INSIDE the field — the containment leg, FALSE at 64 bits"
    );
    assert!(
        (1i64 << (served_time_bits + 1)) <= P,
        "and it must be WRAP-FREE: p - 2^bits >= 2^bits, so a negative slack of any magnitude the \
         interval can itself reach lands outside it. False at 30, false at 64."
    );

    // ⚑ The TALLY tables. 16 bits × 4 limbs is exactly a `u64`; 8 bits is the carry's byte bus.
    let served_limb_bits = bits_of(TID_TALLY_LIMB);
    assert_eq!(served_limb_bits, TM_LIMB_BITS);
    assert_eq!(bits_of(TID_TALLY_CARRY), TM_CARRY_BITS);
    let served_capacity: u128 = 1u128 << (served_limb_bits * TALLY_RUNGS);
    assert_eq!(
        served_capacity,
        1u128 << 64,
        "four 16-bit limbs must tile a u64 exactly, without slack or truncation"
    );
    assert!(
        (MAX_TOTAL_VOTING_POWER as u128) < served_capacity,
        "…and the tiled capacity must contain CometBFT's MaxTotalVotingPower"
    );
    assert!(
        (MAX_TOTAL_VOTING_POWER as i128) > 572_000_000i128 * P as i128,
        "⚑ …which the single felt it replaces could not hold at ANY declared width: the same value \
         is 572 million field moduli. A width declares an INTERVAL; the wire is one element."
    );
}

// ═══════════════════════════════════════════════════════════════════════════════════════════
// The honest fill, against the Lean row
// ═══════════════════════════════════════════════════════════════════════════════════════════

/// The Rust filler and the Lean row are the same 43 numbers. Lean hand-writes them
/// (`tmMaxScaleCells`) and `decide`s that limbs 15..18 denote `2^60 − 1`; Rust derives them from
/// `total`/`signed` through `fill_tally`. A drift on either side is a diff on ONE object.
#[test]
fn the_honest_fill_reproduces_the_lean_row() {
    let cells = row_cells(protocol_max_header());
    assert_eq!(cells.len(), TM_LC_WIDTH);
    assert_eq!(
        cells.as_slice(),
        LEAN_MAX_SCALE_CELLS.as_slice(),
        "the computed protocol-maximum row must equal LightClientTendermintAir.tmMaxScaleCells"
    );

    // …and the fill really recomposes: `limbValue d = 3·S − 2·T − 1`, the telescoping identity
    // (`LimbTally.chain_recomposes`) as an arithmetic fact about THIS row.
    let f = fill_tally(MAX_TOTAL_VOTING_POWER, MIN_STRICT_SUPERMAJORITY);
    assert_eq!(
        limb_value(&f.diff),
        3 * MIN_STRICT_SUPERMAJORITY as i128 - 2 * MAX_TOTAL_VOTING_POWER as i128 - 1
    );
    assert_eq!(limb_value(&f.total), MAX_TOTAL_VOTING_POWER as i128);
    assert_eq!(limb_value(&f.signed), MIN_STRICT_SUPERMAJORITY as i128);

    // The threshold really is at the boundary: one unit less fails CometBFT's strict `3·S > 2·T`.
    assert!(3 * MIN_STRICT_SUPERMAJORITY as i128 > 2 * MAX_TOTAL_VOTING_POWER as i128);
    assert!(3 * (MIN_STRICT_SUPERMAJORITY - 1) as i128 <= 2 * MAX_TOTAL_VOTING_POWER as i128);
}

// ═══════════════════════════════════════════════════════════════════════════════════════════
// Positive polarity — without this every refusal below is satisfied by a descriptor that
// refuses everything.
// ═══════════════════════════════════════════════════════════════════════════════════════════

/// ⚑ **A PROVER HAS RUN THIS DESCRIPTOR.** An honest adjacent Tendermint header with a genuine
/// supermajority PROVES and VERIFIES against the served, Lean-emitted AIR.
#[test]
fn an_honest_supermajority_header_proves_and_verifies() {
    let h = honest_header();
    let f = fill_tally(h.total_pow, h.signed_pow);
    // The honest difference is +99 and it needs exactly one limb; the chain is quiet here.
    assert_eq!(limb_value(&f.diff), 99);
    must_prove("an honest Tendermint header", h);
}

/// A header at the very edge of honesty still proves: the smallest strictly-over-2/3 commit
/// (`signedPow = 3` of `totalPow = 4` — `3·3 − 2·4 − 1 = 0`) fills every difference limb to zero,
/// the interval's floor.
#[test]
fn the_minimal_strict_supermajority_proves() {
    let mut h = honest_header();
    h.total_pow = 4;
    h.signed_pow = 3;
    let f = fill_tally(h.total_pow, h.signed_pow);
    assert_eq!(limb_value(&f.diff), 0);
    must_prove("the minimal strict supermajority", h);
}

// ═══════════════════════════════════════════════════════════════════════════════════════════
// ⚑⚑ THE MEASUREMENT — a validator set at COMETBFT'S PROTOCOL MAXIMUM
// ═══════════════════════════════════════════════════════════════════════════════════════════

/// ⚑⚑ **THE DELIVERABLE: A VALIDATOR SET AT COMETBFT'S PROTOCOL MAXIMUM PROVES AND VERIFIES ON THE
/// DEPLOYED RUST PROVER.**
///
/// `totalPow = 1152921504606846975 = 2^60 − 1` is `MaxTotalVotingPower`, the largest voting power
/// the protocol permits. `signedPow = 768614336404564651` is the SMALLEST value satisfying the
/// strict `3·S > 2·T`.
///
/// At a single felt this update could not be REPRESENTED, let alone accepted: `3·signedPow =
/// 2305843009213693953` is 1.14 billion times the BabyBear modulus, so no declared width — 29, 30,
/// 64 or 128 — ever made it provable. The Lean counterpart is
/// `LightClientTendermintAir.tmLcAir_accepts_at_max_total_voting_power`, over the same 43 cells.
#[test]
fn the_protocol_maximum_validator_set_proves() {
    let h = protocol_max_header();
    assert_eq!(h.total_pow, MAX_TOTAL_VOTING_POWER);
    assert!(3 * h.signed_pow as i128 > 2 * h.total_pow as i128);

    let t0 = std::time::Instant::now();
    must_prove(
        "⚑ a validator set at CometBFT's MaxTotalVotingPower (2^60 − 1)",
        h,
    );
    let dt = t0.elapsed();
    eprintln!(
        "⚑ PROTOCOL MAXIMUM: total={} signed={} PROVED AND VERIFIED in {:?} ({} trace rows, \
         {TM_LC_WIDTH} base columns)",
        h.total_pow, h.signed_pow, dt, TRACE_ROWS
    );
}

/// ⚑ **AND THE TOOTH SURVIVED THE WIDENING, AT THE SAME SCALE.** The same row with ONE unit of
/// voting power moved out of 2^60 — `signedPow = 768614336404564650`, exactly 2/3 — is REFUSED.
///
/// Both legs of the refusal are exercised, because they catch different forgers:
///
///  * **The honest fill is out of range.** The true difference is `−1`, so `fillCarry` borrows all
///    the way up and the top difference limb comes out `−1`, i.e. the field element `p − 1 =
///    2013265920`, which the 16-bit tooth has no row for. A prover that simply fills honestly is
///    refused by the layout filler, in every profile.
///  * **The obvious repair is caught by the CLOSURE GATE.** A forger who forces that top limb to
///    `0` to satisfy the range tooth then leaves `c₃ − d₄ − 128 = 127 − 0 − 128 = −1 ≠ 0`. That is
///    the gate whose absence would let a residue hide in a carry nothing reads.
///
/// ⚠ Neither leg is the general statement. "NO assignment of difference limbs and carries satisfies
/// the chain" is `tmLcAir_refuses_exactly_two_thirds_at_max_voting_power`, a Lean theorem over the
/// emitted bodies with no width, field or magnitude hypothesis. A Rust test quantifies over nothing
/// and this file does not pretend otherwise.
#[test]
fn one_unit_below_the_threshold_is_refused_at_the_protocol_maximum() {
    let mut h = protocol_max_header();
    h.signed_pow = MIN_STRICT_SUPERMAJORITY - 1;
    assert!(
        3 * h.signed_pow as i128 <= 2 * h.total_pow as i128,
        "one unit below is EXACTLY 2/3 — Tendermint's threshold is STRICT and this must not finalize"
    );

    let f = fill_tally(h.total_pow, h.signed_pow);
    assert_eq!(
        limb_value(&f.diff),
        -1,
        "the exactly-2/3 commit makes the true difference −1"
    );
    assert_eq!(f.diff[TALLY_RUNGS], -1, "…carried into the TOP limb");
    assert_eq!(
        felt(f.diff[TALLY_RUNGS]).as_u32() as i64,
        P - 1,
        "…which on the wire is p − 1, an element with no row in [0, 2^16)"
    );
    assert_eq!(
        f.carry,
        [127, 127, 127, 127],
        "and every rung BORROWED — the offset carry rides one below its honest 128"
    );

    let d = desc();
    let pis = pis_of(h);
    let cells = row_cells(h);
    let e = must_refuse_out_of_range(
        "⚑ exactly 2/3 at MaxTotalVotingPower (honest fill)",
        &d,
        &cells,
        &pis,
    );
    eprintln!("⚑ one unit below the threshold, honest fill: {e}");

    // The in-circuit tooth: force the out-of-range top limb to zero so the RANGE tooth is satisfied
    // and the CLOSURE GATE is the only thing left standing.
    let mut forged = cells.clone();
    forged[TDIFF_0 + TALLY_RUNGS] = 0;
    let e2 = must_refuse_violated_gate(
        "⚑ exactly 2/3 at MaxTotalVotingPower (top limb forced into range)",
        &d,
        &forged,
        &pis,
    );
    eprintln!("⚑ one unit below the threshold, top limb forged to 0: {e2}");
}

/// ⚑ **A LIVE VALIDATOR SET.** Cosmos Hub's total voting power at height 32,325,597 — 328,774,071
/// across 180 validators, measured 2026-08-03 — with a realistic supermajority, PROVES and VERIFIES.
///
/// ⚠ This is the value that motivates the whole change and it is easy to miss why: 328,774,071 fits
/// a BabyBear felt. What did not fit was the THRESHOLD SLACK the old single-felt tooth range-checked,
/// `3·signedPow − 2·totalPow − 1`, which needed `3·signedPow < 2^29 = 536,870,912`. At this live
/// tally `3·signedPow = 750,000,000` — **1.4× over the ceiling**. The deployed Cosmos Hub was
/// already outside the honest domain of the repaired 29-bit client.
#[test]
fn the_live_cosmos_hub_validator_set_proves() {
    let mut h = honest_header();
    h.height = 32_325_598;
    h.ts_height = 32_325_597;
    h.total_pow = COSMOS_HUB_TOTAL_POWER;
    h.signed_pow = 250_000_000;
    assert!(3 * h.signed_pow as i128 > 2 * h.total_pow as i128);
    assert!(
        3 * h.signed_pow > (1u64 << TM_BITS),
        "⚑ the live Cosmos Hub threshold slack overflows the 29-bit felt tooth this replaces"
    );

    let f = fill_tally(h.total_pow, h.signed_pow);
    assert_eq!(
        limb_value(&f.diff),
        3 * h.signed_pow as i128 - 2 * h.total_pow as i128 - 1
    );
    let t0 = std::time::Instant::now();
    must_prove("⚑ the live Cosmos Hub validator set", h);
    eprintln!(
        "⚑ COSMOS HUB (live 2026-08-03, height 32,325,597, 180 validators): total={} signed={} \
         PROVED AND VERIFIED in {:?}",
        h.total_pow,
        h.signed_pow,
        t0.elapsed()
    );
}

/// ⚑ **THE EMPTY VALIDATOR SET IS REFUSED**, and by the same tooth as the sub-quorum: at
/// `totalPow = signedPow = 0` the strict difference is `0 − 0 − 1 = −1`. Tendermint's strict
/// threshold subsumes the empty-set floor its Solana and Midnight siblings carry as a separate
/// slack (`LightClientTendermintAir.tmLcAir_refuses_the_empty_validator_set`).
#[test]
fn the_empty_validator_set_is_refused() {
    let mut h = protocol_max_header();
    h.total_pow = 0;
    h.signed_pow = 0;

    let f = fill_tally(0, 0);
    assert_eq!(limb_value(&f.diff), -1);
    assert_eq!(f.total, [0, 0, 0, 0]);
    assert_eq!(f.signed, [0, 0, 0, 0]);

    let d = desc();
    let cells = row_cells(h);
    let pis = pis_of(h);
    let e = must_refuse_out_of_range("⚑ the EMPTY validator set", &d, &cells, &pis);
    eprintln!("⚑ empty validator set refused: {e}");

    // …and the in-circuit leg, so this is not only the layout filler's pre-flight: force the
    // out-of-range top limb into `[0, 2^16)` and the chain's CLOSURE GATE is what refuses.
    let mut forged = cells.clone();
    forged[TDIFF_0 + TALLY_RUNGS] = 0;
    let e2 = must_refuse_violated_gate(
        "⚑ the EMPTY validator set (top limb forced into range)",
        &d,
        &forged,
        &pis,
    );
    eprintln!("⚑ empty validator set, top limb forged to 0: {e2}");
}

/// ⚑ **A TALLY THAT MAKES THE CARRY CHAIN DO REAL WORK.** `totalPow = 1147797409030816545`
/// (`0x0FEDCBA987654321`, just under the protocol maximum) has a non-zero top limb and low limbs
/// that are not saturated, and a 3/4 supermajority of it drives carries in BOTH directions:
/// `+2` out of rung 0 and `−1` out of rungs 1 and 2.
///
/// ⚠ This test exists because **several natural test values give an all-zero carry chain**, where
/// every rung is independently satisfiable and the chain is never exercised. The protocol-maximum
/// row is one of them (its carries are all `128`), as are the Cosmos Hub row and the honest small
/// header. So the assertion below is not decoration: without a carry that differs from the offset,
/// this test would pass while measuring nothing about the borrow structure.
#[test]
fn a_tally_that_needs_all_four_limbs_proves() {
    let total: u64 = 0x0FED_CBA9_8765_4321;
    let signed: u64 = total / 4 * 3;
    assert!(3 * signed as i128 > 2 * total as i128);
    assert!(
        total < MAX_TOTAL_VOTING_POWER,
        "still a protocol-legal tally"
    );

    let f = fill_tally(total, signed);
    assert_ne!(f.total[3], 0, "the top operand limb must be occupied");
    assert!(
        f.total[..3].iter().any(|&l| l != 0xFFFF),
        "the low limbs must not be saturated — a saturated operand hides the borrow structure"
    );
    let nontrivial: Vec<i64> = f
        .carry
        .iter()
        .copied()
        .filter(|&c| c != CARRY_OFF)
        .collect();
    assert!(
        !nontrivial.is_empty(),
        "⚑ THE POINT OF THIS TEST: at least one carry must differ from the {CARRY_OFF} offset, or \
         the chain is never exercised and this passes vacuously. carries = {:?}",
        f.carry
    );
    assert!(
        f.carry.iter().any(|&c| c > CARRY_OFF) && f.carry.iter().any(|&c| c < CARRY_OFF),
        "…and this value drives the chain in BOTH directions: a positive carry and a BORROW. \
         carries = {:?}",
        f.carry
    );
    assert_eq!(
        limb_value(&f.diff),
        3 * signed as i128 - 2 * total as i128 - 1,
        "the chain must still recompose exactly with non-trivial carries"
    );

    let mut h = protocol_max_header();
    h.total_pow = total;
    h.signed_pow = signed;
    must_prove("⚑ a four-limb tally with a working carry chain", h);
    eprintln!(
        "⚑ FOUR-LIMB TALLY: total={total} signed={signed}\n   total limbs {:?}\n   signed limbs \
         {:?}\n   diff limbs {:?}\n   offset carries {:?} (offset {CARRY_OFF}; non-trivial {:?})",
        f.total, f.signed, f.diff, f.carry, nontrivial
    );
}

// ═══════════════════════════════════════════════════════════════════════════════════════════
// ⚑ THE CHAIN'S OWN TEETH — a forged difference limb and a forged carry
// ═══════════════════════════════════════════════════════════════════════════════════════════

/// ⚑ **A FORGED DIFFERENCE LIMB IS REFUSED — every one of the five.**
///
/// Take the honest protocol-maximum row and add one to a `TDIFF` limb, keeping it inside `[0, 2^16)`
/// so the RANGE tooth still admits it. The rung's own gate no longer vanishes (for the top limb, the
/// closure gate does not), and the refusal is a VIOLATED CONSTRAINT rather than a bus imbalance.
///
/// This is the tooth that makes the difference vector a DERIVED quantity rather than a claim: a
/// prover cannot re-spell the difference and move the comparison
/// (`LimbTally.limbValue_unique` is the canonicity statement one layer up).
#[test]
fn a_forged_difference_limb_is_refused() {
    let h = protocol_max_header();
    let pis = pis_of(h);
    let honest_cells = row_cells(h);
    let d = desc();
    must_prove("the honest protocol-maximum pole", h);

    for i in 0..=TALLY_RUNGS {
        let mut forged = honest_cells.clone();
        forged[TDIFF_0 + i] += 1;
        assert!(
            forged[TDIFF_0 + i] < (1 << TM_LIMB_BITS),
            "the forged limb must stay INSIDE the declared 16-bit interval, so the range tooth is \
             not what catches it"
        );
        let reason = must_refuse_violated_gate(
            &format!("⚑ forged TDIFF limb {i} (col {})", TDIFF_0 + i),
            &d,
            &forged,
            &pis,
        );
        eprintln!("⚑ forged TDIFF limb {i}: {reason}");
    }
}

/// ⚑ **A FORGED CARRY IS REFUSED — every one of the four.**
///
/// Perturb one offset carry column, keeping it inside the declared `[0, 2^8)` so the 8-bit tooth
/// still admits it. Each carry appears in exactly two gates — weighted `−2^16` in the rung it exits
/// and `+1` in the rung it enters — so a single perturbation breaks both.
///
/// ⚠ Worth saying what this does NOT show. `LimbTally.chain_recomposes` holds for **any** integer
/// carries whatsoever: they cancel pairwise and no bound on them enters the recomposition. The carry
/// range lookups exist ONLY for the mod-`p` ↔ ℤ bridge
/// (`LimbTally.rung_no_alias_at_deployed_constants`). So this tooth measures that the CHAIN pins the
/// carries to the operands — not that the carry range check is load-bearing for soundness. It is not.
#[test]
fn a_forged_carry_is_refused() {
    let h = protocol_max_header();
    let pis = pis_of(h);
    let honest_cells = row_cells(h);
    let d = desc();

    for i in 0..TALLY_RUNGS {
        let mut forged = honest_cells.clone();
        forged[TDIFF_CARRY_0 + i] += 1;
        assert!(
            forged[TDIFF_CARRY_0 + i] < (1 << TM_CARRY_BITS),
            "the forged carry must stay INSIDE the declared 8-bit interval"
        );
        let reason = must_refuse_violated_gate(
            &format!("⚑ forged TDIFF carry {i} (col {})", TDIFF_CARRY_0 + i),
            &d,
            &forged,
            &pis,
        );
        eprintln!("⚑ forged TDIFF carry {i}: {reason}");
    }
}

// ═══════════════════════════════════════════════════════════════════════════════════════════
// The sub-quorum at small scale, and the width that is no longer what refuses it
// ═══════════════════════════════════════════════════════════════════════════════════════════

/// ⚑ **THE TOOTH, AND THE FIELD IS NO LONGER IN ITS PREMISES.** The exactly-2/3 sub-quorum
/// (`signedPow = 2` of `totalPow = 3`) is REFUSED.
///
/// This case is the historical one: under the single-felt tally it filled `TDIFF = −1`, the field
/// element `p − 1 = 2013265920`, and the refusal was "that element is not in `[0, 2^29)`" — a fact
/// about the FIELD SIZE, false at 30 and catastrophically false at the 64 that shipped. The file
/// used to carry a paired leg showing the same row PROVING at a vacuous width, because that is what
/// made the narrowing a repair rather than a renumbering.
///
/// ⚑ That leg has been INVERTED, and the inversion is the result. The sub-quorum is run here at a
/// VACUOUS 32-bit time-range width — an interval that covers the whole field, exactly as the shipped
/// 64 did — and it is refused there too. The felt range table is no longer what rejects it; a limb
/// vector of non-negative limbs simply cannot denote `−1`. That is the observable shadow of
/// `LimbTally.refusal_is_field_independent`, which quantifies over every limb width in every field
/// and which no Rust test can state.
#[test]
fn the_exactly_two_thirds_sub_quorum_is_refused() {
    let mut h = honest_header();
    h.total_pow = 3;
    h.signed_pow = 2;

    let f = fill_tally(3, 2);
    assert_eq!(limb_value(&f.diff), -1, "the exactly-2/3 commit fills −1");
    assert_eq!(felt(f.diff[TALLY_RUNGS]).as_u32() as i64, P - 1);

    let cells = row_cells(h);
    let pis = pis_of(h);

    let e = must_refuse_out_of_range("the exactly-2/3 sub-quorum", &desc(), &cells, &pis);
    eprintln!("exactly-2/3 sub-quorum refused: {e}");

    // ⚑ The inverted control: a time-range width whose interval covers the field. It admits every
    // wrapped TIME slack — and the threshold does not care, because the threshold left that table.
    assert!(
        (1u64 << VACUOUS_BITS) > P as u64,
        "the control width must actually be vacuous — its interval must cover the field"
    );
    let vacuous = desc_with_time_range_width(VACUOUS_BITS);
    let e2 = must_refuse_out_of_range(
        "⚑ the exactly-2/3 sub-quorum at a VACUOUS time-range width",
        &vacuous,
        &cells,
        &pis,
    );
    eprintln!("⚑ …and refused again at a vacuous time-range width: {e2}");
    assert!(
        e2.contains(&format!("range wire {}", TDIFF_0 + TALLY_RUNGS)),
        "the refusal must be the TALLY tooth on the top difference limb (col {}), not the time \
         table: {e2}",
        TDIFF_0 + TALLY_RUNGS
    );

    // …and the in-circuit leg: force the top limb into range and the CLOSURE GATE refuses.
    let mut forged = cells.clone();
    forged[TDIFF_0 + TALLY_RUNGS] = 0;
    let e3 = must_refuse_violated_gate(
        "the exactly-2/3 sub-quorum (top limb forced into range)",
        &desc(),
        &forged,
        &pis,
    );
    eprintln!("exactly-2/3 sub-quorum, top limb forged to 0: {e3}");
}

// ═══════════════════════════════════════════════════════════════════════════════════════════
// The THREE TIME teeth — still on the 29-bit felt table, still both polarities
// ═══════════════════════════════════════════════════════════════════════════════════════════

/// ⚑ **WHAT THE SHIPPED WIDTH ACTUALLY DID, AND IT IS NOT WHAT THE DENOTATION SAYS.**
///
/// `dregg-tm-lightclient-verify::v1` shipped `bits: 64`. In Lean's `rangeRows 64` that interval
/// contains every field element and the tooth refuses NOTHING. In the deployed Rust prover it
/// refuses EVERYTHING: the layout filler's bound is `(v as u64) >= (1u64 << rb.bits)`
/// (`circuit/src/descriptor_ir2.rs:4310`), and a `u64` shift by 64 is masked to a shift by 0 in a
/// release build, so the test becomes `v >= 1` and every nonzero value on a ranged wire is refused.
/// Under `cargo test` the same expression is an OVERFLOW PANIC, because `[profile.dev]` leaves
/// `overflow-checks` on.
///
/// So an HONEST Tendermint header — the positive polarity that proves at 29 bits — could not be
/// proved at all at the width that shipped. **That is the mechanical reason no prover had ever run
/// this descriptor: the first honest attempt would have been refused.** The same masking hits the
/// two 128-bit siblings (`128 % 64 == 0`).
///
/// ⚠ Stated at the resolution it was measured: this is the observed behaviour of THIS prover on THIS
/// descriptor, and the refusal SHAPE differs by profile — which is itself the finding, so the test
/// names both rather than accepting either. It is not a claim about what any `bits >= 31` descriptor
/// does; 32 through 63 shift fine and are vacuous in both readings, which is what the two tests
/// below exhibit.
#[test]
fn the_shipped_64_bit_width_refuses_even_an_honest_header() {
    let h = honest_header();
    let cells = row_cells(h);
    let pis = pis_of(h);
    // The very witness that PROVES at the repaired width.
    must_prove("the honest header at 29 bits", h);

    let shipped = desc_with_time_range_width(SHIPPED_TM_BITS);
    if cfg!(debug_assertions) {
        let msg = refusal::must_panic_containing(
            "⚑ the honest header at the SHIPPED bits=64",
            "shift left with overflow",
            || {
                let _ = prove_and_verify(&shipped, &cells, &pis);
            },
        );
        eprintln!("honest header at the shipped bits=64 (debug): {msg}");
    } else {
        let e: String =
            refusal::must_refuse("⚑ the honest header at the SHIPPED bits=64", || {
                prove_and_verify(&shipped, &cells, &pis)
            });
        eprintln!("honest header at the shipped bits=64 (release): {e}");
        assert!(
            e.contains("range wire"),
            "the refusal must come from the range layout bound, got: {e}"
        );
    }
}

/// A header from the FUTURE: `time` beyond `now + clockDrift` fills `TW_DRIFT` negative — refused at
/// 29 bits, ADMITTED at a vacuous width. The pairing is what makes the 29 a check rather than a
/// number, and it is measured on the running prover rather than asserted.
#[test]
fn a_header_from_the_future_is_refused_and_is_admitted_when_vacuous() {
    let mut h = honest_header();
    h.time = h.now + h.clock_drift + 7; // seven seconds past the drift bound

    let cells = row_cells(h);
    let pis = pis_of(h);
    assert_eq!(cells[TW_DRIFT], -7);
    assert_eq!(felt(cells[TW_DRIFT]).as_u32() as i64, P - 7);

    let e = must_refuse_out_of_range("a header from the FUTURE", &desc(), &cells, &pis);
    eprintln!("header from the future refused: {e}");
    assert!(
        e.contains(&format!("range wire {TW_DRIFT}")),
        "the drift tooth is what must bite: {e}"
    );

    must_prove_under(
        "⚑ the SAME future header at a vacuous time-range width",
        &desc_with_time_range_width(VACUOUS_BITS),
        h,
    );
}

/// And on the trusting-period tooth: a header older than the trusting period fills `TW_TRUST`
/// negative. Refused at 29, admitted at a vacuous width.
#[test]
fn an_expired_trusting_period_is_refused_and_is_admitted_when_vacuous() {
    let mut h = honest_header();
    // now sits one second past headerTime + trustingPeriod
    h.now = h.header_time + h.trusting_period;
    h.time = h.header_time + 1;
    h.clock_drift = h.now - h.time; // keep the drift tooth satisfied so only TW_TRUST bites

    let cells = row_cells(h);
    let pis = pis_of(h);
    assert_eq!(cells[TW_TRUST], -1);

    let e = must_refuse_out_of_range("an EXPIRED trusting period", &desc(), &cells, &pis);
    eprintln!("expired trusting period refused: {e}");
    assert!(
        e.contains(&format!("range wire {TW_TRUST}")),
        "the trusting-period tooth is what must bite: {e}"
    );

    must_prove_under(
        "⚑ the SAME expired header at a vacuous time-range width",
        &desc_with_time_range_width(VACUOUS_BITS),
        h,
    );
}

// ═══════════════════════════════════════════════════════════════════════════════════════════
// The ALGEBRAIC teeth still bite — the tally work did not become the only check
// ═══════════════════════════════════════════════════════════════════════════════════════════

/// A cross-chain replay is refused by the chain-id gate at BOTH widths — this refusal never depended
/// on any range table, and the test says so by exercising both descriptors.
#[test]
fn a_cross_chain_replay_is_refused_at_both_widths() {
    let mut h = honest_header();
    h.chain_id = 0x0c05_0002; // a different chain's header against this trust store
    let cells = row_cells(h);
    let pis = pis_of(h);

    must_refuse_violated_gate("a foreign chain-id", &desc(), &cells, &pis);
    must_refuse_violated_gate(
        "a foreign chain-id at a vacuous time-range width",
        &desc_with_time_range_width(VACUOUS_BITS),
        &cells,
        &pis,
    );
}

/// A non-adjacent height is refused by the height gate at both widths. Skipping verification is not
/// this descriptor's shape.
#[test]
fn a_non_adjacent_height_is_refused_at_both_widths() {
    let mut h = honest_header();
    h.height = h.ts_height + 5;
    let cells = row_cells(h);
    let pis = pis_of(h);

    must_refuse_violated_gate("a non-adjacent height", &desc(), &cells, &pis);
    must_refuse_violated_gate(
        "a non-adjacent height at a vacuous time-range width",
        &desc_with_time_range_width(VACUOUS_BITS),
        &cells,
        &pis,
    );
}

/// A forged CARRIER — the Ed25519 batch-verify result, the header self-binding, or the
/// next-validators epoch binding, cleared to `0` — is refused by its own gate.
///
/// ⚠ These are witnessed bits, not in-AIR crypto. What the AIR enforces is that a prover claiming
/// acceptance must ASSERT all three; the Ed25519/SHA-256 soundness behind them is consumed one layer
/// up, inside `tmNoForgery` (`LightClientTendermintAir` module header, "the crypto boundary").
#[test]
fn a_cleared_crypto_carrier_is_refused() {
    for (name, col) in [
        ("ED_OK (Ed25519 batch verify)", ED_OK),
        ("VSET_OK (header self-binding)", VSET_OK),
        ("EPOCH_OK (next-validators epoch binding)", EPOCH_OK),
    ] {
        let h = honest_header();
        let mut cells = row_cells(h);
        assert_eq!(cells[col], 1, "the honest carrier is set");
        cells[col] = 0;
        let reason = must_refuse_violated_gate(
            &format!("a cleared carrier {name}"),
            &desc(),
            &cells,
            &pis_of(h),
        );
        eprintln!("cleared carrier {name}: {reason}");
    }
}

/// A forged PUBLIC ANCHOR: the committed app-hash on the wire disagreeing with the published PI.
/// The nine `.piBinding` pins are the addressing layer — they say WHICH trust root and WHICH full
/// 256-bit app-hash the proof is about — and a proof whose trace disagrees with its own public
/// statement must not verify.
#[test]
fn a_committed_app_hash_that_disagrees_with_its_public_input_is_refused() {
    let h = honest_header();
    let mut cells = row_cells(h);
    cells[COMMITTED_APP_HASH_0 + 4] += 1;
    let reason = must_refuse_violated_gate(
        "a committed app-hash limb disagreeing with its PI pin",
        &desc(),
        &cells,
        &pis_of(h),
    );
    eprintln!("forged app-hash limb: {reason}");
}
