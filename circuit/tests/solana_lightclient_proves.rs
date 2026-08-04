//! ⚑ **THE SOLANA ROOTED-FINALITY LIGHT CLIENT, PROVED ON THE DEPLOYED PROVER — AT MAINNET-BETA'S
//! LIVE ACTIVE STAKE.**
//!
//! # What had never happened
//!
//! Five peer chains have a Lean-authored light-client verify AIR routed through `EmitByName.lean`
//! into `circuit/src/descriptor_by_name.rs`. As of 2026-08-03 **two had ever been proved**: Mina
//! (`turn/tests/mina_anchored_head_lands.rs`) and Tendermint
//! (`circuit/tests/tendermint_lightclient_proves.rs`). Solana was served by name and no prover had
//! ever run it — *"producible by a node" was a claim about DISPATCH*, a descriptor that decodes and
//! a name that resolves. This file closes Solana.
//!
//! The Lean side already accepts at live scale
//! (`Dregg2.Circuit.Emit.LightClientSolanaAir.solLcAir_accepts_at_live_active_stake`) with both
//! refusals proved as named theorems. What was missing was the machine-specific half: that the
//! DEPLOYED Rust prover produces a proof for the honest row and REFUSES the two exhibited forgeries.
//!
//! # The two teeth this file makes bite on the running prover
//!
//! **The empty stake table**, which is the one that FAILED. `dregg-solana-lightclient-verify::v1`
//! shipped `bits: 128` on its range table, and BabyBear is `p = 2013265921 < 2^31 < 2^128`, so the
//! declared interval `[0, 2^128)` already contained every field element and the lookup refused
//! nothing (`RangeFieldContainment.range_vacuous_at_or_above_31`). The `EmptyStakeTable` floor
//! `TPOS = TOTAL_STK − 1 ≥ 0` filled to `−1` at `TOTAL_STK = 0`, which rides as `p − 1 =
//! 2013265920`, and the 128-bit interval contained it. **The empty stake table passed its own
//! emptiness floor.**
//!
//! ⚠ And the quorum did not save it — because the threshold was the WRONG POLARITY. This descriptor
//! shipped the NON-STRICT `3·rooted ≥ 2·total` (`γ = 0`), so at `rooted = total = 0` the quorum
//! difference was `3·0 − 2·0 = 0`: an HONEST, in-range, ACCEPTING fill, and the emptiness floor was
//! the ONLY thing between this client and a block signed by nobody.
//!
//! ⚑⚑ **That was not Solana's rule.** `get_highest_super_majority_root`
//! (`core/src/commitment_service.rs:54-64`, agave `c7670b260b8cd34674e05c03c0babdaf54e15987`) — the
//! rooted-finality rule this AIR models — compares
//! `(stake_sum as f64 / total_stake as f64) > VOTE_THRESHOLD_SIZE`, **strictly**, against
//! `2f64/3f64` (`runtime/src/commitment.rs:9`). Transcribing that comparison and sweeping it: over
//! 6,684,470 pairs with both operands below 2^53 (including EVERY `(rooted, total)` with
//! `total <= 3000`) the strict integer rule `3·rooted > 2·total` matches agave on **all of them**,
//! while the non-strict rule differs on 1000 — every one the exact-2/3 point, every one this
//! descriptor accepting where agave refuses. And at `total = 0`, agave computes `0f64/0f64 = NaN`
//! and `NaN > x` is `false`, so **agave refuses the empty stake table at the threshold itself**.
//!
//! So `γ` is now `1`, and the empty stake table is refused by BOTH chains.
//! `the_empty_stake_table_is_refused_by_both_teeth` and
//! `with_the_emptiness_floor_disarmed_the_strict_quorum_still_refuses_the_empty_table` disarm them
//! ONE AT A TIME on the deployed prover — quorum disarmed ⇒ the floor bites, floor disarmed ⇒ the
//! quorum bites — and `at_the_shipped_non_strict_gamma_disarming_the_floor_left_nothing` exhibits
//! the state that preceded it, where disarming the floor left every tally wire in range.
//!
//! **The exact-2/3 point**, one lamport out of 4.3e17. At mainnet-beta's live active stake the
//! minimal STRICT quorum is `288433455950417059`; `288433455950417058` is exactly 2/3
//! (`3·R = 2·T = 865300367851251174`), **proved before this repair**, and is refused now.
//! `288433455950417057` gives `3·R − 2·T − 1 = −4` and was refused before and after.
//!
//! # The tally is a LIMB VECTOR, and that is what makes live scale representable at all
//!
//! `TOTAL_STK` and `ROOTED_STK` were ONE BabyBear COLUMN EACH. A felt holds 30.9 bits;
//! mainnet-beta's active stake, measured live 2026-08-03, is `432650183925625587` lamports =
//! `2^58.586` = **214,899,670 × the modulus**. It did not fit at 128 bits, it did not fit at 29,
//! and it would not have fit at any width: a declared width declares an INTERVAL and the wire is
//! ONE field element. Both tallies are now four 16-bit limbs — exactly Solana's own `u64` — with
//! the quorum difference and the emptiness floor each carried as a five-limb vector tied to the
//! operands by an offset borrow chain (`Dregg2.Circuit.LimbTally`,
//! `Dregg2.Circuit.Emit.LightClientSolanaAir` §1/§2). Trace width `19 → 41`; one range table →
//! **two** (16 / 8); two threshold gates and two lookups → **ten generated chain gates and
//! twenty-six per-limb lookups**.
//!
//! # Scope, said plainly
//!
//! `ED_OK` / `STAKE_TABLE_OK` / `ROOTED_OK` / `AUTH_OK` are witnessed carrier bits, not in-AIR
//! ed25519 and SHA-256; the dregg-side STARK inherits the undischarged FRI floor. The mod-`p` ↔ ℤ
//! residual is DISCHARGED for the chain gates at THIS AIR's constants
//! (`LightClientSolanaAir.sol_qdiff_rung_no_alias` at `α=3, β=2, γ=1` and `sol_tpos_rung_no_alias`
//! at `α=1, β=0, γ=1`; the quorum's constants now coincide with `LimbTally`'s deployed ones, and it
//! is still proved locally rather than by citation) and still stands elsewhere.
//! This is a prover running the served object. It is **not** "Solana-valid", and it is not
//! "machine-checked" — the machine-checked statements are the Lean ones this file names, and a Rust
//! case-test quantifies over nothing.
//!
//! ⚠ **PROFILE.** plonky3's ALGEBRAIC refusals are `#[cfg(debug_assertions)]` panics under
//! `cargo test` and clean `Err(OodEvaluationMismatch)` under `--release`; RANGE refusals are `Err`
//! in both. Every refusal here goes through `dregg_circuit::refusal`, which discriminates the two
//! mechanisms identically in both profiles and REDS on a crash wearing a refusal's clothes.

use dregg_circuit::BabyBear;
use dregg_circuit::descriptor_by_name::descriptor_by_name;
use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, MemBoundaryWitness, TableSem, parse_vm_descriptor2, prove_vm_descriptor2,
    verify_vm_descriptor2,
};
use dregg_circuit::heap_root::HeapLeaf;
use dregg_circuit::refusal;

const SOL_LC_VERIFY_DESCRIPTOR: &str = "dregg-solana-lightclient-verify::v1";

// ═══════════════════════════════════════════════════════════════════════════════════════════
// Trace column layout — pinned to `LightClientSolanaAir`'s Lean `def`s (§1).
// ⚑ It was 19 columns. The +22 is the tally becoming REPRESENTABLE: two `u64` operands and TWO
// comparison chains (the quorum and the emptiness floor), each with a difference vector and a
// borrow chain.
// ═══════════════════════════════════════════════════════════════════════════════════════════

/// CARRIER — the aggregate ed25519 verify result over the counted authorized voters.
const ED_OK: usize = 0;
/// CARRIER — the derived stake table binds the pinned WS anchor root (the HOLE-2 denominator pin).
const STAKE_TABLE_OK: usize = 1;
/// GATE — every counted vote's tower root reaches the slot (HOLE-1).
const ROOTED_OK: usize = 2;
/// GATE — every counted signer is the on-chain authorized voter (BR-2-A).
const AUTH_OK: usize = 3;
/// `TOTAL_STK` limb 0 (LSB). Limbs 0..3 are columns 4..7.
const TOTAL_STK_0: usize = 4;
/// `ROOTED_STK` limb 0 (LSB). Limbs 0..3 are columns 8..11.
const ROOTED_STK_0: usize = 8;
/// `QDIFF` limb 0 (LSB). FIVE limbs, columns 12..16 — `3·A` needs two bits beyond `A`.
const QDIFF_0: usize = 12;
/// The offset carry out of quorum rung 0. Four carries, columns 17..20; each denotes `col − 128`.
const QDIFF_CARRY_0: usize = 17;
/// `TPOS` limb 0 (LSB) — the `EmptyStakeTable` floor difference `total − 1`. Columns 21..25.
const TPOS_0: usize = 21;
/// The offset carry out of floor rung 0. Four carries, columns 26..29.
const TPOS_CARRY_0: usize = 26;
/// PUBLIC ANCHOR limb 0 — ⚑ the pinned WS stake-table root as NINE radix-`2^31` MSB-first limbs,
/// cols 30..38. It was ONE column until 2026-08-04, i.e. a 256-bit SHA-256 root
/// (`WeakSubjectivityAnchor::stake_table_root`, `[u8; 32]`) compared at 31 bits — the same felt-width
/// defect this file already closed for the bank root, left standing on the trust anchor itself.
const ANCHOR_ROOT_0: usize = 30;
const ROOT_LIMBS: usize = 9;
/// PUBLIC ANCHOR limb 0 — the rooted bank hash as nine radix-`2^31` MSB-first limbs, cols 39..47.
const BANK_ROOT_0: usize = 39;
const BANK_ROOT_LIMBS: usize = 9;
/// PUBLIC ANCHOR — the rooted slot S.
const SLOT_COL: usize = 48;

const SOL_LC_WIDTH: usize = 49;
const SOL_PI_COUNT: usize = 23;
/// ⚑ PI slot of total-stake limb 0. Slots 19..22 publish the active-stake DENOMINATOR, so the prover
/// no longer chooses the number its own quorum is a fraction of (`totalStakePins`).
const PI_TOTAL_STK_0: usize = 19;

/// The tally limb width. `4 · 16 = 64` — four limbs are exactly a `u64`, Solana's lamport type.
const SOL_LIMB_BITS: usize = 16;
/// The chain-carry width (the prover's own byte bus: one aux column, one byte lookup).
const SOL_CARRY_BITS: usize = 8;

/// Declared wire id of the 16-bit tally-limb table (`.custom (64 + 16)` ⇒ `5 + 80`).
const TID_TALLY_LIMB: usize = 85;
/// Declared wire id of the 8-bit chain-carry table (`.custom (64 + 8)` ⇒ `5 + 72`).
const TID_TALLY_CARRY: usize = 77;
/// The shared felt-wide `range` table's wire id. ⚑ This descriptor MUST NOT declare it — both
/// slacks that queried it are limbed chains now (`sol_range_table_is_not_declared`).
const TID_FELT_RANGE: usize = 2;

/// The offset a carry rides at on the wire: a difference chain BORROWS, and a field wire has no
/// sign, so `c` is written `c + 128` with the declared range `[0, 2^8)` giving `c ∈ [−128, 127]`.
const CARRY_OFF: i64 = 128;

/// The number of rungs per chain. Four rungs generate FIVE gate bodies — one per rung plus the
/// closure gate that forces the final carry into the top difference limb.
const RUNGS: usize = 4;

/// The width that SHIPPED on this descriptor's single range table.
///
/// ⚑ **BOTH HALVES OF THAT DEFECT ARE CLOSED (2026-08-03) AND THIS CONSTANT NOW NAMES A REFUSED
/// DECLARATION, NOT A LIVE ONE.** `128 >= 31`, so the interval contained the whole BabyBear field
/// and the lookup refused nothing; and the layout filler's `(v as u64) >= (1u64 << bits)` masked to
/// a shift by 0, so the same declaration ALSO refused every nonzero row in the prover. Now
/// `parse_table_def` refuses the declaration at descriptor LOAD (`VACUOUS_RANGE_BITS`), and the
/// filler's bound is total (`value_fits_bits`), so an in-memory descriptor at this width behaves the
/// way `DescriptorIR2.rangeRows` says: it admits everything. Both are measured by
/// `the_shipped_128_bit_width_refuses_even_an_honest_update` below.
const SHIPPED_SOL_BITS: usize = 128;

/// The smallest FULLY VACUOUS width (`2^32 > p`, so `[0, 2^32)` covers the field) the deployed
/// prover can still execute — `1u64 << 32` is well-defined where `1u64 << 128` is not.
const VACUOUS_BITS: usize = 32;

/// The AIR's gates are single-row and its pins are first-row, so every row is the same logical row;
/// the count is FRI-shaped.
const TRACE_ROWS: usize = 8;

const P: i64 = 2_013_265_921;

fn desc() -> EffectVmDescriptor2 {
    descriptor_by_name(SOL_LC_VERIFY_DESCRIPTOR).unwrap_or_else(|| {
        panic!(
            "{SOL_LC_VERIFY_DESCRIPTOR} must dispatch: the Lean-emitted descriptor is routed \
             through EmitByName.lean and included by circuit/src/descriptor_by_name.rs"
        )
    })
}

/// The SAME served descriptor with the **16-bit TALLY-LIMB table's** declared width set to `bits`.
///
/// ⚑ This is the control that makes the limb teeth a check rather than a number. The declared table
/// wins over the `CUSTOM_RANGE_WIDTHS` fallback (`descriptor_ir2.rs:1472` `range_bits_for`), so one
/// integer moves and nothing else does. It touches the 16-bit table ONLY; the 8-bit carry table is
/// left alone.
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

/// Field-encode a possibly-negative integer: in BabyBear a negative value IS `p − k`, which is the
/// element a limb tooth must refuse. This is where a failed quorum's top difference limb lands.
fn felt(v: i64) -> BabyBear {
    BabyBear::new(v.rem_euclid(P) as u32)
}

// ═══════════════════════════════════════════════════════════════════════════════════════════
// ⚑ THE HONEST FILL — `LimbTally.fillDigit` / `LimbTally.fillCarry`, transcribed as a LOOP.
// ═══════════════════════════════════════════════════════════════════════════════════════════

/// One comparison chain's fill: the five difference limbs and the four OFFSET carries. Everything
/// as `i64` so a refused row's negative top limb is expressible — that value is precisely what a
/// refusal test wants to hand the prover.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct ChainFill {
    /// `α·A − β·B − γ` as FIVE 16-bit limbs, LSB first. `diff[4]` IS the final carry.
    diff: [i64; RUNGS + 1],
    /// The carry out of each rung, OFFSET: `carry[i] = c_{i+1} + 128`.
    carry: [i64; RUNGS],
}

/// Decompose a `u64` into its four 16-bit limbs, LSB first — Solana's own wire type for lamports.
fn limbs4(v: u64) -> [i64; RUNGS] {
    let mut out = [0i64; RUNGS];
    for (i, o) in out.iter_mut().enumerate() {
        *o = ((v >> (SOL_LIMB_BITS * i)) & 0xFFFF) as i64;
    }
    out
}

/// ⚑ **THE HONEST FILL**, parametric in the chain constants, because this AIR runs TWO chains over
/// the same limb vectors and they do not share constants:
///
///  * the QUORUM chain is `α = 3` on rooted stake, `β = 2` on total stake, ⚑ `γ = 1` — agave's
///    STRICT `3·rooted > 2·total`. It shipped `γ = 0`; `get_highest_super_majority_root`
///    (`core/src/commitment_service.rs:54-64`) compares `> VOTE_THRESHOLD_SIZE`, and over 6,684,470
///    pairs below 2^53 the strict integer rule matches agave's float on ALL of them while the
///    non-strict rule differs on the exact-2/3 point every time (`LightClientSolanaAir` header),
///  * the FLOOR chain is `α = 1`, `β = 0`, `γ = 1` — `total − 1 ≥ 0`, the `EmptyStakeTable` refusal.
///
/// `fillDigit` is a FLOOR mod (`rem_euclid`, always in `[0, 2^16)` by construction, never by check)
/// and `fillCarry` is the exact floor quotient, so `raw − d − c·2^16 = 0` holds identically
/// (`LimbTally.fill_splits`).
///
/// ⚠ When the comparison FAILS the final carry is NEGATIVE and `diff[4]` comes out negative. That
/// is the refusal, and this function expresses it rather than hiding it: the caller puts `p + v` on
/// the wire, which is the element the 16-bit tooth has no row for.
fn fill_chain(alpha: i64, a: [i64; RUNGS], beta: i64, b: [i64; RUNGS], gamma: i64) -> ChainFill {
    let radix: i64 = 1 << SOL_LIMB_BITS;
    let mut diff = [0i64; RUNGS + 1];
    let mut carry = [0i64; RUNGS];
    let mut c: i64 = 0;
    for i in 0..RUNGS {
        let g = if i == 0 { gamma } else { 0 };
        let raw = alpha * a[i] - beta * b[i] - g + c;
        let d = raw.rem_euclid(radix);
        // Exact: `raw − d` is a multiple of the radix, so truncating and floor division agree.
        c = (raw - d) / radix;
        diff[i] = d;
        carry[i] = c + CARRY_OFF;
    }
    // The chain's CLOSURE: the operands have run out, so the final carry IS the top digit. Without
    // this the prover could dump a residue into a carry nothing reads and the recomposition would
    // be off by `2^64` (`LimbTally.ChainOk`, the `[]` case).
    diff[RUNGS] = c;
    ChainFill { diff, carry }
}

/// The value a limb vector denotes over ℤ (`LimbTally.limbValue`, LSB-first Horner). Used only to
/// re-assert, in the harness, that the fill really recomposes.
fn limb_value(limbs: &[i64]) -> i128 {
    let mut acc: i128 = 0;
    for &l in limbs.iter().rev() {
        acc = acc * (1i128 << SOL_LIMB_BITS) + l as i128;
    }
    acc
}

// ═══════════════════════════════════════════════════════════════════════════════════════════
// One logical row of the Solana rooted-finality verify decision
// ═══════════════════════════════════════════════════════════════════════════════════════════

#[derive(Clone, Copy)]
struct Update {
    /// ⚑ `u64` — Solana's lamport type. The tally rides four 16-bit limbs.
    total_stk: u64,
    /// ⚑ `u64`. The counted rooted authorized voting stake; its ed25519 provenance is `ED_OK`.
    rooted_stk: u64,
    ed_ok: u32,
    stake_table_ok: u32,
    rooted_ok: u32,
    auth_ok: u32,
    anchor_root: [u32; ROOT_LIMBS],
    bank_root: [u32; BANK_ROOT_LIMBS],
    slot: u32,
}

/// An HONEST update: every difference limb and carry is COMPUTED from the identity its gate forces,
/// never claimed. A caller cannot hand this a slack; it can only hand it the facts they derive from.
fn honest(total_stk: u64, rooted_stk: u64) -> Update {
    Update {
        total_stk,
        rooted_stk,
        ed_ok: 1,
        stake_table_ok: 1,
        rooted_ok: 1,
        auth_ok: 1,
        anchor_root: [11, 22, 33, 44, 55, 66, 77, 88, 99],
        bank_root: [1, 2, 3, 4, 5, 6, 7, 8, 9],
        slot: LIVE_SLOT,
    }
}

/// The 41 cells of one logical row, **as integers** — the same 41 numbers, in the same order, as
/// `LightClientSolanaAir.solMaxScaleCells`. Kept in `i64` so a forgery test can perturb a cell and
/// so a refused row's negative top difference limb survives to `felt` unaltered.
fn row_cells(u: Update) -> Vec<i64> {
    let total = limbs4(u.total_stk);
    let rooted = limbs4(u.rooted_stk);
    // §2: `α = 3` on rooted, `β = 2` on total, ⚑ `γ = 1` — agave's STRICT `3·rooted > 2·total`.
    let q = fill_chain(3, rooted, 2, total, QUORUM_GAMMA);
    // §2: `α = 1`, `β = 0`, `γ = 1` — `total − 1 ≥ 0`. The `β` operand column is the total-stake
    // limb ON PURPOSE (`tposRungs`): at `β = 0` the emitted term is `0 · var`, so no dedicated zero
    // column is needed and none has to be pinned.
    let t = fill_chain(1, total, 0, total, FLOOR_GAMMA);

    let mut r = vec![0i64; SOL_LC_WIDTH];
    r[ED_OK] = u.ed_ok as i64;
    r[STAKE_TABLE_OK] = u.stake_table_ok as i64;
    r[ROOTED_OK] = u.rooted_ok as i64;
    r[AUTH_OK] = u.auth_ok as i64;
    r[TOTAL_STK_0..TOTAL_STK_0 + RUNGS].copy_from_slice(&total);
    r[ROOTED_STK_0..ROOTED_STK_0 + RUNGS].copy_from_slice(&rooted);
    r[QDIFF_0..QDIFF_0 + RUNGS + 1].copy_from_slice(&q.diff);
    r[QDIFF_CARRY_0..QDIFF_CARRY_0 + RUNGS].copy_from_slice(&q.carry);
    r[TPOS_0..TPOS_0 + RUNGS + 1].copy_from_slice(&t.diff);
    r[TPOS_CARRY_0..TPOS_CARRY_0 + RUNGS].copy_from_slice(&t.carry);
    for (i, l) in u.anchor_root.iter().enumerate() {
        r[ANCHOR_ROOT_0 + i] = *l as i64;
    }
    for (i, l) in u.bank_root.iter().enumerate() {
        r[BANK_ROOT_0 + i] = *l as i64;
    }
    r[SLOT_COL] = u.slot as i64;
    r
}

/// The twenty-three published anchors, in PI order: nine WS anchor-root limbs, nine bank-root limbs,
/// the slot, and ⚑ the four TOTAL-STAKE limbs — the governance-pinned active-stake denominator.
fn pis_of(u: Update) -> Vec<BabyBear> {
    let mut pis = vec![BabyBear::new(0); SOL_PI_COUNT];
    for (i, l) in u.anchor_root.iter().enumerate() {
        pis[i] = BabyBear::new(*l);
    }
    for (i, l) in u.bank_root.iter().enumerate() {
        pis[ROOT_LIMBS + i] = BabyBear::new(*l);
    }
    pis[ROOT_LIMBS + BANK_ROOT_LIMBS] = BabyBear::new(u.slot);
    // ⚑ The denominator is PUBLISHED. A light client supplies these four limbs from its
    // weak-subjectivity anchor; a prover that fills a different total in cols 4..7 no longer matches
    // its own public statement and the `.piBinding` refuses it.
    for (i, l) in limbs4(u.total_stk).iter().enumerate() {
        pis[PI_TOTAL_STK_0 + i] = BabyBear::new(*l as u32);
    }
    pis
}

fn trace_of(cells: &[i64]) -> Vec<Vec<BabyBear>> {
    let row: Vec<BabyBear> = cells.iter().map(|&v| felt(v)).collect();
    vec![row; TRACE_ROWS]
}

/// PROVE and VERIFY, both legs, exactly as a deployed consumer would.
fn prove_and_verify(
    d: &EffectVmDescriptor2,
    cells: &[i64],
    pis: &[BabyBear],
) -> Result<(), String> {
    let trace = trace_of(cells);
    refusal::assert_committed_shape("solana lightclient", d, &trace, pis);
    let mem = MemBoundaryWitness::default();
    let heaps: Vec<Vec<HeapLeaf>> = vec![];
    let proof = prove_vm_descriptor2(d, &trace, pis, &mem, &heaps)
        .map_err(|e| format!("prover refused: {e}"))?;
    verify_vm_descriptor2(d, &proof, pis).map_err(|e| format!("verifier refused: {e:?}"))
}

/// The honest pole through the served descriptor. An honest pole that fails makes every paired
/// refusal vacuous, so it is asserted rather than assumed.
fn must_prove(what: &str, u: Update) {
    must_prove_under(what, &desc(), u);
}

fn must_prove_under(what: &str, d: &EffectVmDescriptor2, u: Update) {
    let cells = row_cells(u);
    let pis = pis_of(u);
    refusal::must_accept(what, || prove_and_verify(d, &cells, &pis));
}

/// A RANGE refusal: the prover's layout filler has no honest completion for a wire outside its
/// declared interval. An `Err` in EVERY profile — never a panic, never debug-only.
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

// ═══════════════════════════════════════════════════════════════════════════════════════════
// ⚑ MAINNET-BETA, MEASURED LIVE — the numbers the whole change exists for
// ═══════════════════════════════════════════════════════════════════════════════════════════

/// Mainnet-beta's ACTIVE stake, measured live 2026-08-03 via `getVoteAccounts` on
/// `api.mainnet-beta.solana.com` (689 current + 14 delinquent vote accounts, epoch 1011):
/// `432.650M SOL = 2^58.586`. **214,899,670 × the BabyBear modulus.**
const LIVE_ACTIVE_STAKE: u64 = 432_650_183_925_625_587;

/// ⚑ The EXACT-2/3 point at that total: `3 · 288_433_455_950_417_058 = 865_300_367_851_251_174`
/// is `2 · LIVE_ACTIVE_STAKE` on the nose. It was the accepting anchor under the shipped non-strict
/// rule; under agave's STRICT `>` it is a **REFUSAL**, and it is kept precisely because it is the
/// one row the strictness repair flips.
const EXACT_TWO_THIRDS: u64 = 288_433_455_950_417_058;

/// The SMALLEST rooted stake satisfying agave's STRICT `3·rooted > 2·total` at that total —
/// **one lamport** above the exact-2/3 point, out of 4.3e17.
const MIN_QUORUM: u64 = 288_433_455_950_417_059;

/// The quorum chain's `γ`. ⚑ `1` = STRICT (`3·rooted ≥ 2·total + 1`), matching
/// `get_highest_super_majority_root`'s `>` and the constants Midnight and Tendermint already used.
/// It shipped `0`. Named rather than inlined so the DISARM tests below can build the non-strict
/// fill by name and show what it admitted.
const QUORUM_GAMMA: i64 = 1;

/// The emptiness floor's `γ` — `total − 1 ≥ 0`. Unchanged by the strictness repair.
const FLOOR_GAMMA: i64 = 1;

/// Mainnet-beta's total SUPPLY at the same sample (`getSupply`): `2^59.13`. The protocol ceiling on
/// what a stake tally could ever have to hold — no stake table can exceed the supply.
const LIVE_TOTAL_SUPPLY: u64 = 631_503_420_149_974_995;

/// The measured live slot at the same sample.
const LIVE_SLOT: u32 = 436_909_708;

/// `LightClientSolanaAir.solMaxScaleCells`, transcribed. The Lean side hand-writes these 41 numbers
/// and `decide`s that limbs 4..7 denote the live active stake; the Rust side COMPUTES them from
/// `total`/`rooted` through `fill_chain`. Two independent sources for one object.
const LEAN_MAX_SCALE_CELLS: [i64; SOL_LC_WIDTH] = [
    1,
    1,
    1,
    1,
    62195,
    52452,
    5388,
    1537,
    19619,
    13123,
    47283,
    1024,
    2,
    0,
    0,
    0,
    0,
    127,
    127,
    130,
    128,
    62194,
    52452,
    5388,
    1537,
    0,
    128,
    128,
    128,
    128,
    // ⚑ ANCHOR_ROOT limbs 0..8 — the WS stake-table root, MSB-first. It was the single cell `11111`
    // until 2026-08-04: a 256-bit SHA-256 root carried in one 31-bit BabyBear element.
    11,
    22,
    33,
    44,
    55,
    66,
    77,
    88,
    99,
    // BANK_ROOT limbs 0..8
    1,
    2,
    3,
    4,
    5,
    6,
    7,
    8,
    9,
    436_909_708,
];

// ═══════════════════════════════════════════════════════════════════════════════════════════
// The served object
// ═══════════════════════════════════════════════════════════════════════════════════════════

/// The descriptor this tree serves is the one the Lean module declares — width, PI count,
/// constraint count, and both declared limb widths.
#[test]
fn the_served_descriptor_is_the_lean_emitted_one() {
    let d = desc();
    assert_eq!(d.name, SOL_LC_VERIFY_DESCRIPTOR);
    assert_eq!(
        d.trace_width, SOL_LC_WIDTH,
        "⚑ the two tallies became limb vectors (19 → 41) and the WS anchor root became nine \
         radix-2^31 limbs instead of one 31-bit felt (41 → 49)"
    );
    assert_eq!(
        d.public_input_count, SOL_PI_COUNT,
        "⚑ 11 → 23: eight more anchor-root limbs, plus the four PUBLISHED total-stake limbs"
    );
    // 26 per-limb lookups + 10 generated chain gates + 4 carrier/logic gates
    //   + 9 anchor-root pins + 9 bank-root pins + 1 slot pin + 4 denominator pins = 63
    // (`LightClientSolanaAir.sol_shape_pins`).
    assert_eq!(d.constraints.len(), 63);
    assert_eq!(
        d.tables.len(),
        2,
        "⚑ TWO declared limb widths where there was one felt table"
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

    // ⚠ Every check below reads the width OUT OF THE SERVED DESCRIPTOR rather than out of this
    // file's constants. A constant compared against its own definition is decoration; these are the
    // emitted object measured against the field it is evaluated in, so a re-emission that moved a
    // width would red them.
    let served_limb_bits = bits_of(TID_TALLY_LIMB);
    assert_eq!(served_limb_bits, SOL_LIMB_BITS);
    assert_eq!(bits_of(TID_TALLY_CARRY), SOL_CARRY_BITS);

    // ⚑ The felt-wide `range` table is GONE. Both slacks that queried it are limbed chains, and a
    // declared table no constraint reads is a width nothing checks
    // (`sol_range_table_is_not_declared`). This is the tripwire if a felt slack is re-introduced.
    assert!(
        d.tables.iter().all(|t| t.id != TID_FELT_RANGE),
        "⚑ the shared felt-wide range table must NOT be declared — it is where the 128-bit vacuity \
         lived, and both of its lookups are limbed chains now"
    );

    let served_capacity: u128 = 1u128 << (served_limb_bits * RUNGS);
    assert_eq!(
        served_capacity,
        1u128 << 64,
        "four 16-bit limbs must tile a u64 exactly, without slack or truncation"
    );
    assert!(
        (LIVE_TOTAL_SUPPLY as u128) < served_capacity,
        "…and the tiled capacity must contain mainnet-beta's TOTAL SUPPLY, which bounds any stake \
         table that can ever exist"
    );
    assert!(
        (LIVE_ACTIVE_STAKE as i128) > 214_899_670i128 * P as i128,
        "⚑ …which the single felt it replaces could not hold at ANY declared width: live active \
         stake is 214.9 million field moduli. A width declares an INTERVAL; the wire is one element."
    );
}

// ═══════════════════════════════════════════════════════════════════════════════════════════
// The honest fill, against the Lean row
// ═══════════════════════════════════════════════════════════════════════════════════════════

/// The Rust filler and the Lean row are the same 41 numbers. Lean hand-writes them
/// (`solMaxScaleCells`) and `decide`s what they denote; Rust derives them from `total`/`rooted`
/// through `fill_chain`. A drift on either side is a diff on ONE object.
#[test]
fn the_honest_fill_reproduces_the_lean_row() {
    let cells = row_cells(honest(LIVE_ACTIVE_STAKE, MIN_QUORUM));
    assert_eq!(cells.len(), SOL_LC_WIDTH);
    assert_eq!(
        cells.as_slice(),
        LEAN_MAX_SCALE_CELLS.as_slice(),
        "the computed live-scale row must equal LightClientSolanaAir.solMaxScaleCells"
    );

    // …and the fills really recompose (`LimbTally.chain_recomposes`), as arithmetic about THIS row.
    let total = limbs4(LIVE_ACTIVE_STAKE);
    let rooted = limbs4(MIN_QUORUM);
    assert_eq!(limb_value(&total), LIVE_ACTIVE_STAKE as i128);
    assert_eq!(limb_value(&rooted), MIN_QUORUM as i128);
    let q = fill_chain(3, rooted, 2, total, QUORUM_GAMMA);
    assert_eq!(
        limb_value(&q.diff),
        3 * MIN_QUORUM as i128 - 2 * LIVE_ACTIVE_STAKE as i128 - QUORUM_GAMMA as i128
    );
    let t = fill_chain(1, total, 0, total, FLOOR_GAMMA);
    assert_eq!(limb_value(&t.diff), LIVE_ACTIVE_STAKE as i128 - 1);

    // The quorum really is at the boundary: one lamport less fails agave's STRICT `3·R > 2·T`.
    assert!(3 * MIN_QUORUM as i128 > 2 * LIVE_ACTIVE_STAKE as i128);
    assert!(3 * ((MIN_QUORUM - 1) as i128) == 2 * LIVE_ACTIVE_STAKE as i128);
    assert_eq!(MIN_QUORUM - 1, EXACT_TWO_THIRDS);
    // ⚑ …and that one-lamport-below value is EXACTLY 2/3 — the row the shipped non-strict rule
    // accepted and agave refuses. The whole strictness repair is this single lamport.
    assert!(
        3 * EXACT_TWO_THIRDS as i128 >= 2 * LIVE_ACTIVE_STAKE as i128,
        "non-strict ACCEPTS it"
    );
    assert!(
        !(3 * EXACT_TWO_THIRDS as i128 > 2 * LIVE_ACTIVE_STAKE as i128),
        "strict REFUSES it"
    );

    // ⚑ And the quorum carries are NOT trivial: `[127, 127, 130, 128]` is `[−1, −1, +2, 0]`. The
    // chain does real work in BOTH directions — this row is the boundary, not a degenerate one.
    assert_eq!(q.carry, [127, 127, 130, 128]);
    assert!(q.carry.iter().any(|&c| c > CARRY_OFF) && q.carry.iter().any(|&c| c < CARRY_OFF));
}

// ═══════════════════════════════════════════════════════════════════════════════════════════
// ⚑⚑ THE MEASUREMENT — a prover has run this descriptor
// ═══════════════════════════════════════════════════════════════════════════════════════════

/// ⚑⚑ **THE DELIVERABLE: MAINNET-BETA'S LIVE ACTIVE STAKE PROVES AND VERIFIES ON THE DEPLOYED RUST
/// PROVER.**
///
/// `totalStk = 432650183925625587` lamports is the measured live active stake;
/// `rootedStk = 288433455950417059` is the SMALLEST value satisfying agave's STRICT
/// `3·rooted > 2·total`. At a single felt this update could not be REPRESENTED, let alone accepted:
/// `3·rootedStk = 865300367851251174` is 429.8 million times the BabyBear modulus, so no declared
/// width — 29, 30, 64 or the 128 that shipped — ever made it provable. The Lean counterpart is
/// `LightClientSolanaAir.solLcAir_accepts_at_live_active_stake`, over the same 41 cells.
#[test]
fn the_live_mainnet_beta_active_stake_proves() {
    let u = honest(LIVE_ACTIVE_STAKE, MIN_QUORUM);
    assert!(3 * u.rooted_stk as i128 > 2 * u.total_stk as i128);

    let t0 = std::time::Instant::now();
    must_prove(
        "⚑ mainnet-beta's live active stake at the minimal STRICT quorum",
        u,
    );
    let dt = t0.elapsed();
    eprintln!(
        "⚑ SOLANA LIVE ACTIVE STAKE: total={} rooted={} slot={} PROVED AND VERIFIED in {:?} \
         ({TRACE_ROWS} trace rows, {SOL_LC_WIDTH} base columns)",
        u.total_stk, u.rooted_stk, u.slot, dt
    );
}

/// ⚑ **AND AT THE PROTOCOL CEILING.** Mainnet-beta's TOTAL SUPPLY (`631503420149974995` lamports,
/// `2^59.13`) bounds any stake table that can ever exist — no validator set can stake more SOL than
/// exists. A stake table at the whole supply, with its minimal quorum, proves.
#[test]
fn a_stake_table_at_the_whole_supply_proves() {
    let total = LIVE_TOTAL_SUPPLY;
    // ⚑ ceil((2T+1)/3), the minimal STRICT quorum (agave's `>`), not ceil(2T/3).
    let rooted = (2 * total as u128 + 1).div_ceil(3) as u64;
    assert!(3 * rooted as u128 > 2 * total as u128);
    assert!(!(3 * ((rooted - 1) as u128) > 2 * total as u128));

    let u = honest(total, rooted);
    let cells = row_cells(u);
    // The chain must actually be exercised at this scale, or the test measures nothing.
    let q = fill_chain(3, limbs4(rooted), 2, limbs4(total), QUORUM_GAMMA);
    assert!(
        q.carry.iter().any(|&c| c != CARRY_OFF),
        "the carry chain must do real work at the supply ceiling; carries = {:?}",
        q.carry
    );
    assert_eq!(cells[TOTAL_STK_0..TOTAL_STK_0 + RUNGS], limbs4(total)[..]);

    let t0 = std::time::Instant::now();
    must_prove("⚑ a stake table at mainnet-beta's TOTAL SUPPLY", u);
    eprintln!(
        "⚑ SUPPLY CEILING: total={total} rooted={rooted} PROVED AND VERIFIED in {:?}\n   total \
         limbs {:?}\n   qdiff limbs {:?}\n   offset carries {:?} (offset {CARRY_OFF})",
        t0.elapsed(),
        limbs4(total),
        q.diff,
        q.carry
    );
}

/// ⚑⚑ **THE EXACT-2/3 BOUNDARY IS REFUSED — the strictness repair, at the smallest scale there is.**
///
/// `rooted = 2` of `total = 3` is exactly 2/3 (`3·2 = 6 = 2·3`). It **proved** under the shipped
/// `γ = 0` and it is refused now, which is what agave does: transcribing
/// `(2f64 / 3f64) > (2f64 / 3f64)` gives `false`, and this pair is one of the 1000 cases in the
/// full exhaustive sweep (`t <= 3000`) where agave and the non-strict rule disagreed.
///
/// ⚠ Both legs, because they catch different forgers: the honest fill's top difference limb is out
/// of range, and forcing it into range leaves the closure gate violated.
#[test]
fn the_exact_two_thirds_boundary_is_refused() {
    let u = honest(3, 2);
    let q = fill_chain(3, limbs4(2), 2, limbs4(3), QUORUM_GAMMA);
    assert_eq!(
        limb_value(&q.diff),
        -1,
        "3·2 − 2·3 − 1 = −1: the STRICT quorum refuses the exact-2/3 point"
    );
    // …and the NON-STRICT fill this descriptor used to ship accepted the very same row.
    let q_old = fill_chain(3, limbs4(2), 2, limbs4(3), 0);
    assert_eq!(
        limb_value(&q_old.diff),
        0,
        "γ = 0 filled it to an accepting zero"
    );
    assert_eq!(q_old.diff, [0; RUNGS + 1]);

    let d = desc();
    let cells = row_cells(u);
    let pis = pis_of(u);
    let e = must_refuse_out_of_range(
        "⚑⚑ the EXACT-2/3 point (total 3, rooted 2)",
        &d,
        &cells,
        &pis,
    );
    eprintln!("⚑⚑ SOLANA exact-2/3 refused: {e}");
    assert!(
        e.contains(&format!("range wire {}", QDIFF_0 + RUNGS)),
        "the refusal must be the QUORUM tooth on col {}: {e}",
        QDIFF_0 + RUNGS
    );

    let mut forged = cells.clone();
    forged[QDIFF_0 + RUNGS] = 0;
    let e2 = must_refuse_violated_gate(
        "⚑⚑ the EXACT-2/3 point with the quorum top limb forced into range",
        &d,
        &forged,
        &pis,
    );
    eprintln!("⚑⚑ SOLANA exact-2/3, quorum top limb forged to 0: {e2}");
}

/// ⚑ **AND THE ACCEPTING SIDE AT THE SAME SCALE**, so the refusal above is a boundary and not a
/// blanket. `rooted = 3` of `total = 3` clears the strict threshold (`9 > 6`) and PROVES.
#[test]
fn the_strict_two_thirds_boundary_proves() {
    let u = honest(3, 3);
    let q = fill_chain(3, limbs4(3), 2, limbs4(3), QUORUM_GAMMA);
    assert_eq!(limb_value(&q.diff), 2, "3·3 − 2·3 − 1 = 2");
    must_prove("agave's STRICT >2/3 boundary (rooted 3 of total 3)", u);
}

// ═══════════════════════════════════════════════════════════════════════════════════════════
// ⚑ TOOTH 1 — the sub-quorum, one lamport out of 4.3e17
// ═══════════════════════════════════════════════════════════════════════════════════════════

/// ⚑⚑ **ONE LAMPORT BELOW THE MINIMAL STRICT QUORUM IS REFUSED, AT LIVE SCALE — and that value is
/// the EXACT-2/3 POINT, which PROVED before the strictness repair.**
///
/// `rootedStk = 288433455950417058` gives `3·R = 2·T = 865300367851251174` exactly, so the strict
/// difference `3·R − 2·T − 1` is `−1`. This is the row agave refuses (`d > d` is false) and the
/// shipped `γ = 0` accepted. Both legs are exercised, because they catch different forgers:
///
///  * **The honest fill is out of range.** `fillCarry` borrows all the way up and the top
///    difference limb comes out `−1`, i.e. the field element `p − 1 = 2013265920`, which the 16-bit
///    tooth has no row for. A prover that simply fills honestly is refused by the layout filler.
///  * **The obvious repair is caught by the CLOSURE GATE.** A forger who forces that top limb to
///    `0` to satisfy the range tooth then leaves `c₃ − d₄ − 128 = 127 − 0 − 128 = −1 ≠ 0`.
///
/// ⚠ Neither leg is the general statement. "NO assignment of difference limbs and carries satisfies
/// the chain" is `solLcAir_refuses_the_exact_two_thirds_point_at_live_active_stake`, a Lean theorem
/// over the emitted bodies with no width, field or magnitude hypothesis. A Rust test quantifies over
/// nothing and this file does not pretend otherwise.
#[test]
fn one_lamport_below_the_quorum_is_refused_at_live_active_stake() {
    let u = honest(LIVE_ACTIVE_STAKE, MIN_QUORUM - 1);
    assert_eq!(u.rooted_stk, EXACT_TWO_THIRDS);
    assert!(
        !(3 * (u.rooted_stk as i128) > 2 * u.total_stk as i128),
        "the exact-2/3 point must not finalize under agave's STRICT rule"
    );
    assert!(
        3 * (u.rooted_stk as i128) >= 2 * u.total_stk as i128,
        "…and it DID under the non-strict rule this descriptor shipped"
    );

    let q = fill_chain(
        3,
        limbs4(u.rooted_stk),
        2,
        limbs4(u.total_stk),
        QUORUM_GAMMA,
    );
    assert_eq!(
        limb_value(&q.diff),
        -1,
        "the exact-2/3 point's strict difference"
    );
    assert_eq!(q.diff[RUNGS], -1, "…carried into the TOP limb");
    assert_eq!(
        felt(q.diff[RUNGS]).as_u32() as i64,
        P - 1,
        "…which on the wire is p − 1, an element with no row in [0, 2^16)"
    );

    let d = desc();
    let pis = pis_of(u);
    let cells = row_cells(u);
    let e = must_refuse_out_of_range(
        "⚑ one lamport below the minimal quorum (honest fill)",
        &d,
        &cells,
        &pis,
    );
    eprintln!("⚑ SOLANA sub-quorum, honest fill: {e}");
    assert!(
        e.contains(&format!("range wire {}", QDIFF_0 + RUNGS)),
        "the refusal must be the QUORUM tooth on the top difference limb (col {}): {e}",
        QDIFF_0 + RUNGS
    );

    // The in-circuit tooth: force the out-of-range top limb to zero so the RANGE tooth is satisfied
    // and the CLOSURE GATE is the only thing left standing.
    let mut forged = cells.clone();
    forged[QDIFF_0 + RUNGS] = 0;
    let e2 = must_refuse_violated_gate(
        "⚑ one lamport below the minimal quorum (top limb forced into range)",
        &d,
        &forged,
        &pis,
    );
    eprintln!("⚑ SOLANA sub-quorum, top limb forged to 0: {e2}");
}

/// ⚑ **THE CONTROL: THE SAME SUB-QUORUM IS ADMITTED WHEN THE LIMB TABLE IS VACUOUS.**
///
/// A repair that only shows the NEW width refusing a value has not shown the value was ever
/// admitted. This hands the identical trace to the identical AIR under the identical prover,
/// differing in exactly one integer: the tally-limb table's declared width, moved from 16 to 32 —
/// an interval that covers the whole field, exactly as the shipped 128 was meant to.
///
/// At that width `p − 1 = 2013265920 < 2^32` is IN range, and the honest fill's chain gates are
/// satisfied identically over `𝔽_p` (they are ℤ identities, so they hold mod `p` too). The
/// sub-quorum PROVES. **That is what the 16-bit limb lookups are buying**: the chain gates alone
/// pin the difference to the operands, and it is the per-limb containment that makes the difference
/// vector denote a NON-NEGATIVE integer (`LimbTally.limbValue_nonneg`).
#[test]
fn the_sub_quorum_is_admitted_when_the_limb_table_is_vacuous() {
    assert!(
        (1u64 << VACUOUS_BITS) > P as u64,
        "the control width must actually be vacuous — its interval must cover the field"
    );
    let u = honest(LIVE_ACTIVE_STAKE, MIN_QUORUM - 1);
    must_prove_under(
        "⚑ the SAME sub-quorum at a VACUOUS tally-limb width",
        &desc_with_limb_range_width(VACUOUS_BITS),
        u,
    );
    eprintln!(
        "⚑ SOLANA sub-quorum ADMITTED at a vacuous 32-bit limb width — the per-limb containment is \
         what refuses it at 16"
    );
}

// ═══════════════════════════════════════════════════════════════════════════════════════════
// ⚑⚑ TOOTH 2 — THE EMPTY STAKE TABLE, and the STRICT quorum that now also catches it
// ═══════════════════════════════════════════════════════════════════════════════════════════

/// ⚑⚑ **THE EMPTY STAKE TABLE IS REFUSED BY BOTH TEETH — DISARMED ONE AT A TIME.**
///
/// This is the check that FAILED. At `TOTAL_STK = 0` the `EmptyStakeTable` floor
/// `TPOS = TOTAL_STK − 1 ≥ 0` fills to `−1`, which in the deployed mod-`p` reading rides as
/// `p − 1 = 2013265920` — and the shipped `[0, 2^128)` CONTAINED it
/// (`sol_empty_stake_table_was_admitted_at_128`).
///
/// ⚑ **And the quorum used to be no help, which is what the strictness repair changed.** Under the
/// shipped `γ = 0` the quorum difference at `rooted = total = 0` was `3·0 − 2·0 = 0`: an honest,
/// in-range, ACCEPTING fill — the floor was the ONLY thing between this descriptor and a block
/// signed by nobody. Under agave's actual STRICT rule (`γ = 1`) the difference is `−1` and the
/// QUORUM chain refuses it too, from its own columns.
///
/// The test DISARMS THEM ONE AT A TIME rather than asserting the pair — the same shape the Midnight
/// harness uses. Three refusals, none of them the same one twice:
///
///  * **Leg 1** — the honest row: the QUORUM top limb (col 16) is what the layout filler reaches
///    first.
///  * **Leg 2** — force the quorum's top limb into range: the refusal MOVES to the EMPTINESS floor's
///    top limb (col 25). With the quorum tooth disarmed the floor still bites.
///  * **Leg 3** — force BOTH into range: an algebraic closure gate is what is left standing, so
///    neither refusal was the layout filler's pre-flight alone.
///
/// ⚠ Leg 2 is the load-bearing one for "depth": it is the state the descriptor was ACTUALLY in
/// before this repair (one tooth), and it still refuses.
#[test]
fn the_empty_stake_table_is_refused_by_both_teeth() {
    let u = honest(0, 0);
    let cells = row_cells(u);
    let d = desc();
    let pis = pis_of(u);

    // Both chains fill to −1 — the same wire value, from two different linear forms over two
    // different column sets.
    let q = fill_chain(3, limbs4(0), 2, limbs4(0), QUORUM_GAMMA);
    let t = fill_chain(1, limbs4(0), 0, limbs4(0), FLOOR_GAMMA);
    assert_eq!(
        limb_value(&q.diff),
        -1,
        "3·0 − 2·0 − 1 = −1: the STRICT quorum fails"
    );
    assert_eq!(
        limb_value(&t.diff),
        -1,
        "0 − 1 = −1: the emptiness floor fails"
    );
    assert_eq!(felt(q.diff[RUNGS]).as_u32() as i64, P - 1);
    assert_eq!(felt(t.diff[RUNGS]).as_u32() as i64, P - 1);

    // ⚑ …and the SHIPPED non-strict quorum admitted exactly this row. Stated as a measurement of
    // the fill, not a mood: every difference limb zero, every carry at the honest offset.
    let q_old = fill_chain(3, limbs4(0), 2, limbs4(0), 0);
    assert_eq!(
        limb_value(&q_old.diff),
        0,
        "γ = 0: `3·0 − 2·0 = 0` is an ACCEPTING fill"
    );
    assert_eq!(q_old.diff, [0; RUNGS + 1]);
    assert_eq!(q_old.carry, [CARRY_OFF; RUNGS]);

    // Leg 1 — the QUORUM tooth (this is new; it did not exist at γ = 0).
    let e1 = must_refuse_out_of_range("⚑⚑ the EMPTY stake table", &d, &cells, &pis);
    eprintln!("⚑⚑ SOLANA empty stake table refused (STRICT quorum): {e1}");
    assert!(
        e1.contains(&format!("range wire {}", QDIFF_0 + RUNGS)),
        "the first refusal must be the QUORUM tooth on col {}: {e1}",
        QDIFF_0 + RUNGS
    );

    // Leg 2 — DISARM the quorum and the EMPTINESS floor is what refuses.
    let mut q_forged = cells.clone();
    q_forged[QDIFF_0 + RUNGS] = 0;
    let e2 = must_refuse_out_of_range(
        "⚑⚑ the EMPTY stake table with the quorum's top limb forced into range",
        &d,
        &q_forged,
        &pis,
    );
    eprintln!("⚑⚑ SOLANA empty stake table refused (emptiness floor): {e2}");
    assert!(
        e2.contains(&format!("range wire {}", TPOS_0 + RUNGS)),
        "with the quorum disarmed, the EMPTINESS floor (col {}) must be what bites: {e2}",
        TPOS_0 + RUNGS
    );

    // Leg 3 — disarm BOTH range teeth and an algebraic closure gate is what is left.
    let mut both_forged = q_forged.clone();
    both_forged[TPOS_0 + RUNGS] = 0;
    let e3 = must_refuse_violated_gate(
        "⚑⚑ the EMPTY stake table with BOTH top limbs forced into range",
        &d,
        &both_forged,
        &pis,
    );
    eprintln!("⚑⚑ SOLANA empty stake table, both top limbs forged to 0: {e3}");
}

/// ⚑⚑ **THE OTHER DIRECTION OF THE DISARM: with the FLOOR disabled, the STRICT QUORUM still refuses
/// the empty stake table.**
///
/// Leg 2 above disarms the quorum and shows the floor bites. This disarms the FLOOR — by forcing its
/// whole difference vector to the honest fill of a chain that is not being asked anything — and
/// shows the quorum bites. Together they are the claim "no single gate is the whole defence",
/// demonstrated on the deployed prover rather than asserted.
///
/// ⚠ The floor is disarmed at the WITNESS, not by editing the descriptor: forcing `TPOS`'s top limb
/// to `0` is exactly what a forger with a working floor bypass would hand the prover.
#[test]
fn with_the_emptiness_floor_disarmed_the_strict_quorum_still_refuses_the_empty_table() {
    let u = honest(0, 0);
    let d = desc();
    let pis = pis_of(u);

    let mut floor_disarmed = row_cells(u);
    floor_disarmed[TPOS_0 + RUNGS] = 0;

    let e = must_refuse_out_of_range(
        "⚑⚑ the EMPTY stake table with the EMPTINESS FLOOR disarmed",
        &d,
        &floor_disarmed,
        &pis,
    );
    eprintln!("⚑⚑ SOLANA empty stake table, floor disarmed, refused by the STRICT quorum: {e}");
    assert!(
        e.contains(&format!("range wire {}", QDIFF_0 + RUNGS)),
        "with the FLOOR disarmed, the STRICT QUORUM (col {}) must be what bites: {e}",
        QDIFF_0 + RUNGS
    );
}

/// ⚑ **AND THE COUNTERFACTUAL THAT MAKES THE DEPTH REAL: at the SHIPPED `γ = 0`, disarming the floor
/// leaves NOTHING.**
///
/// The same row, filled with the non-strict quorum this descriptor used to emit, and with the
/// emptiness floor's top limb forced into range: every cell is inside its declared interval. There
/// is no second tooth to move the refusal to. That is the state the finding described, exhibited
/// rather than recalled — and the reason `γ` was the fix rather than a new gate.
///
/// ⚠ This asserts about CELLS, not about the served descriptor: the deployed descriptor is `γ = 1`
/// now, so a `γ = 0` row does not satisfy its quorum gates. The claim being made is exactly the
/// range-containment one — under the old constant the empty row had no out-of-range wire left once
/// the floor was disarmed.
#[test]
fn at_the_shipped_non_strict_gamma_disarming_the_floor_left_nothing() {
    let q_old = fill_chain(3, limbs4(0), 2, limbs4(0), 0);
    let t = fill_chain(1, limbs4(0), 0, limbs4(0), FLOOR_GAMMA);

    // The floor is the ONLY out-of-range wire at γ = 0…
    assert_eq!(t.diff[RUNGS], -1);
    for i in 0..=RUNGS {
        assert!(
            q_old.diff[i] >= 0 && q_old.diff[i] < (1 << SOL_LIMB_BITS),
            "at γ = 0 every quorum difference limb is INSIDE the declared interval — the quorum \
             tooth had nothing to bite on"
        );
    }
    for i in 0..RUNGS {
        assert!(q_old.carry[i] >= 0 && q_old.carry[i] < (1 << SOL_CARRY_BITS));
    }
    // …so with the floor's top limb forced into range, nothing is left out of range.
    let mut old_cells = vec![0i64; SOL_LC_WIDTH];
    old_cells[QDIFF_0..QDIFF_0 + RUNGS + 1].copy_from_slice(&q_old.diff);
    old_cells[QDIFF_CARRY_0..QDIFF_CARRY_0 + RUNGS].copy_from_slice(&q_old.carry);
    old_cells[TPOS_0..TPOS_0 + RUNGS + 1].copy_from_slice(&t.diff);
    old_cells[TPOS_CARRY_0..TPOS_CARRY_0 + RUNGS].copy_from_slice(&t.carry);
    old_cells[TPOS_0 + RUNGS] = 0; // disarm the floor
    for i in QDIFF_0..=(TPOS_0 + RUNGS) {
        assert!(
            old_cells[i] >= 0 && old_cells[i] < (1 << SOL_LIMB_BITS),
            "col {i} out of range at γ = 0 — expected NOTHING left to refuse the empty table"
        );
    }
    eprintln!(
        "⚑ AT γ = 0, WITH THE FLOOR DISARMED, EVERY TALLY WIRE OF THE EMPTY STAKE TABLE IS IN \
         RANGE — one tooth, and this is what it looked like from the other side"
    );
}

/// ⚑ **AND THE CONTROL, ON THE FLOOR.** The empty stake table at a VACUOUS 32-bit limb width — an
/// interval covering the field, as the shipped 128 was meant to be — PROVES. A block signed by
/// nobody, accepted by the deployed prover, at the width this descriptor shipped with.
#[test]
fn the_empty_stake_table_is_admitted_when_the_limb_table_is_vacuous() {
    must_prove_under(
        "⚑ the EMPTY stake table at a VACUOUS tally-limb width",
        &desc_with_limb_range_width(VACUOUS_BITS),
        honest(0, 0),
    );
    eprintln!(
        "⚑ SOLANA EMPTY STAKE TABLE ADMITTED at a vacuous 32-bit limb width — this is what the \
         shipped bits:128 was reaching for, and it is why the floor had no teeth"
    );
}

// ═══════════════════════════════════════════════════════════════════════════════════════════
// ⚑ THE CHAINS' OWN TEETH — forged difference limbs and forged carries, on BOTH chains
// ═══════════════════════════════════════════════════════════════════════════════════════════

/// ⚑ **A FORGED DIFFERENCE LIMB IS REFUSED — all TEN of them, five per chain.**
///
/// Take the honest live-scale row and add one to a difference limb, keeping it inside `[0, 2^16)`
/// so the RANGE tooth still admits it. The rung's own gate no longer vanishes (for a top limb, the
/// closure gate does not), and the refusal is a VIOLATED CONSTRAINT rather than a bus imbalance.
///
/// This is the tooth that makes each difference vector a DERIVED quantity rather than a claim: a
/// prover cannot re-spell the difference and move the comparison.
#[test]
fn a_forged_difference_limb_is_refused_on_both_chains() {
    let u = honest(LIVE_ACTIVE_STAKE, MIN_QUORUM);
    let pis = pis_of(u);
    let honest_cells = row_cells(u);
    let d = desc();
    must_prove("the honest live-scale pole", u);

    for (chain, base) in [
        ("QDIFF (quorum)", QDIFF_0),
        ("TPOS (empty-set floor)", TPOS_0),
    ] {
        for i in 0..=RUNGS {
            let mut forged = honest_cells.clone();
            forged[base + i] += 1;
            assert!(
                forged[base + i] < (1 << SOL_LIMB_BITS),
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

/// ⚑ **A FORGED CARRY IS REFUSED — all EIGHT of them, four per chain.**
///
/// Perturb one offset carry column, keeping it inside the declared `[0, 2^8)` so the 8-bit tooth
/// still admits it. Each carry appears in exactly two gates — weighted `−2^16` in the rung it exits
/// and `+1` in the rung it enters — so a single perturbation breaks both.
///
/// ⚠ Worth saying what this does NOT show. `LimbTally.chain_recomposes` holds for **any** integer
/// carries whatsoever: they cancel pairwise and no bound on them enters the recomposition. The
/// carry range lookups exist ONLY for the mod-`p` ↔ ℤ bridge (`sol_qdiff_rung_no_alias`,
/// `sol_tpos_rung_no_alias`). So this tooth measures that the CHAIN pins the carries to the
/// operands — not that the carry range check is load-bearing for soundness. It is not.
#[test]
fn a_forged_carry_is_refused_on_both_chains() {
    let u = honest(LIVE_ACTIVE_STAKE, MIN_QUORUM);
    let pis = pis_of(u);
    let honest_cells = row_cells(u);
    let d = desc();

    for (chain, base) in [
        ("QDIFF (quorum)", QDIFF_CARRY_0),
        ("TPOS (empty-set floor)", TPOS_CARRY_0),
    ] {
        for i in 0..RUNGS {
            let mut forged = honest_cells.clone();
            forged[base + i] += 1;
            assert!(
                forged[base + i] < (1 << SOL_CARRY_BITS),
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

/// ⚑ **A RE-SPELT DENOMINATOR IS REFUSED.** The two chains SHARE the total-stake limb columns —
/// the floor reads the same four columns the quorum reads as its `β` operand
/// (`sol_tpos_reads_the_quorum_denominator`). So a forger who shrinks the denominator to
/// manufacture a quorum breaks the floor chain at the same time, and vice versa: there is no
/// second, unchecked copy of the total to disagree with.
#[test]
fn a_re_spelt_denominator_is_refused() {
    let u = honest(LIVE_ACTIVE_STAKE, MIN_QUORUM);
    let pis = pis_of(u);
    let d = desc();
    for i in 0..RUNGS {
        let mut forged = row_cells(u);
        forged[TOTAL_STK_0 + i] -= 1;
        assert!(forged[TOTAL_STK_0 + i] >= 0);
        let reason = must_refuse_violated_gate(
            &format!("⚑ a shrunk total-stake limb {i} (col {})", TOTAL_STK_0 + i),
            &d,
            &forged,
            &pis,
        );
        eprintln!("⚑ shrunk denominator limb {i}: {reason}");
    }
}

// ═══════════════════════════════════════════════════════════════════════════════════════════
// ⚑⚑ THE SWAPPED STAKE TABLE — the forgery this pass exists to refuse (2026-08-04)
// ═══════════════════════════════════════════════════════════════════════════════════════════

/// A stake universe the FORGER prefers: 1% of mainnet-beta's real active stake. A cartel holding
/// 4.3M SOL cannot clear 2/3 of 432.6M — but it clears 2/3 of a table it gets to pick.
const FORGED_TOTAL: u64 = LIVE_ACTIVE_STAKE / 100;

/// The minimal STRICT quorum of the forged universe (`3·R > 2·T`).
const FORGED_QUORUM: u64 = (2 * FORGED_TOTAL) / 3 + 1;

/// ⚑⚑ **THE SWAPPED STAKE TABLE PROVES ON ITS OWN TERMS — and that is the whole attack.**
///
/// The forger claims the SAME block (same WS anchor root, same 256-bit bank hash, same rooted slot)
/// but tallies it against a stake table 100× smaller. Every gate in the descriptor is satisfied:
/// the quorum chain, the emptiness floor, both borrow chains, all twenty-six range lookups. The
/// arithmetic is not being cheated — it is being applied to a universe the prover chose.
///
/// This test asserts the forgery is ARITHMETICALLY PERFECT, which is precisely what made it
/// dangerous: until 2026-08-04 the descriptor checked nothing else about the denominator, so this
/// row and the honest one were indistinguishable to it.
#[test]
fn a_swapped_stake_table_is_arithmetically_perfect() {
    let forged = honest(FORGED_TOTAL, FORGED_QUORUM);
    assert!(
        2 * FORGED_TOTAL < 3 * FORGED_QUORUM,
        "the forged tally must clear agave's STRICT 2/3 in its own universe"
    );
    assert!(
        3 * FORGED_QUORUM < 2 * LIVE_ACTIVE_STAKE,
        "…and must NOT clear 2/3 of the REAL active stake — otherwise it is not a forgery"
    );
    // Given the forger's OWN public statement, this proves. Before the denominator pin, the
    // light client's statement and the forger's were the same statement.
    prove_and_verify(&desc(), &row_cells(forged), &pis_of(forged))
        .expect("the swapped stake table satisfies every arithmetic gate in the descriptor");
    eprintln!(
        "⚑ swapped stake table PROVES on its own terms: total {FORGED_TOTAL}          (1% of {LIVE_ACTIVE_STAKE}), rooted {FORGED_QUORUM}"
    );
}

/// ⚑⚑ **AND IT IS REFUSED AGAINST THE LIGHT CLIENT'S ANCHOR.** Same forged cells, but the public
/// statement is the one a light client actually supplies: the bank hash and slot it is asking
/// about, and — since `totalStakePins` — the active-stake denominator from its weak-subjectivity
/// anchor. Columns 4..7 now disagree with PI 19..22 and the proof does not verify.
///
/// ⚠ **This is the exact pair the campaign asked for: PROVED BEFORE, REFUSED AFTER.** The "before"
/// is the test above — the forgery still satisfies every gate; nothing about the tally arithmetic
/// changed. What changed is that the denominator left the prover's control.
///
/// ⚠ **Bound the claim.** This refuses every swap that MOVES THE TOTAL. A swap to a different
/// validator set with the SAME total active stake is NOT refused here — `ROOTED_STK` is a witnessed
/// projection and `ED_OK` a witnessed carrier. Deriving the table itself needs the SHA-256 fold,
/// priced at 18,049,248 constraints / 12,831,336 columns at 703 live vote accounts
/// (`LightClientSolanaAir` §6c).
#[test]
fn a_swapped_stake_table_is_refused_against_the_pinned_denominator() {
    let forged = honest(FORGED_TOTAL, FORGED_QUORUM);
    let honest_client = honest(LIVE_ACTIVE_STAKE, MIN_QUORUM);
    let mut pis = pis_of(honest_client);
    // The forger claims the SAME block: only the stake universe differs. Everything the light
    // client publishes about WHICH block this is already agrees.
    assert_eq!(
        pis[..ROOT_LIMBS + BANK_ROOT_LIMBS + 1],
        pis_of(forged)[..ROOT_LIMBS + BANK_ROOT_LIMBS + 1],
        "anchor root, bank root and slot must be identical — the swap is of the TABLE, not the block"
    );
    // …and the light client supplies the REAL denominator from its anchor.
    for (i, l) in limbs4(LIVE_ACTIVE_STAKE).iter().enumerate() {
        pis[PI_TOTAL_STK_0 + i] = BabyBear::new(*l as u32);
    }
    let reason = must_refuse_violated_gate(
        "⚑ a swapped stake table tallied against a prover-chosen denominator",
        &desc(),
        &row_cells(forged),
        &pis,
    );
    eprintln!("⚑ SWAPPED STAKE TABLE REFUSED: {reason}");
}

/// A forged WS ANCHOR-ROOT limb on the wire disagreeing with the published PI is refused.
///
/// ⚑ **This is the felt-width close finished.** Until 2026-08-04 `ANCHOR_ROOT` was ONE column, so
/// the 256-bit `WeakSubjectivityAnchor::stake_table_root` reached the circuit as a single BabyBear
/// element — 31 bits. Two stake tables whose SHA-256 roots agree in those 31 bits were the same
/// anchor as far as this descriptor could tell, and such a pair is findable in `2^31` hashes. Nine
/// radix-`2^31` limbs bind the whole root; perturbing any ONE is refused.
#[test]
fn an_anchor_root_limb_that_disagrees_with_its_public_input_is_refused() {
    let u = honest(LIVE_ACTIVE_STAKE, MIN_QUORUM);
    let d = desc();
    for i in 0..ROOT_LIMBS {
        let mut cells = row_cells(u);
        cells[ANCHOR_ROOT_0 + i] += 1;
        let reason = must_refuse_violated_gate(
            &format!("a WS anchor-root limb {i} disagreeing with its PI pin"),
            &d,
            &cells,
            &pis_of(u),
        );
        eprintln!("forged anchor-root limb {i}: {reason}");
    }
}

/// ⚑ **A DENOMINATOR LIMB THAT DISAGREES WITH ITS PUBLIC INPUT IS REFUSED** — the pin itself, one
/// limb at a time, so a partial binding (three of four pinned) cannot pass unnoticed.
#[test]
fn a_total_stake_limb_that_disagrees_with_its_public_input_is_refused() {
    let u = honest(LIVE_ACTIVE_STAKE, MIN_QUORUM);
    let d = desc();
    for i in 0..RUNGS {
        let mut pis = pis_of(u);
        pis[PI_TOTAL_STK_0 + i] += BabyBear::new(1);
        let reason = must_refuse_violated_gate(
            &format!("a published total-stake limb {i} disagreeing with the trace"),
            &d,
            &row_cells(u),
            &pis,
        );
        eprintln!("⚑ forged denominator PI {i}: {reason}");
    }
}

// ═══════════════════════════════════════════════════════════════════════════════════════════
// The carrier and addressing teeth
// ═══════════════════════════════════════════════════════════════════════════════════════════

/// A forged CARRIER or logic bit — the ed25519 batch-verify result, the stake-table-root compare,
/// the rooted flag, or the authorized-voter binding, cleared to `0` — is refused by its own gate.
///
/// ⚠ `ED_OK` and `STAKE_TABLE_OK` are witnessed bits, not in-AIR ed25519 and SHA-256. What the AIR
/// enforces is that a prover claiming acceptance must ASSERT all four; the crypto soundness behind
/// them is consumed one layer up, inside `sol_no_forgery` (`LightClientSolanaAir` module header,
/// "the crypto boundary").
#[test]
fn a_cleared_carrier_or_logic_bit_is_refused() {
    for (name, col) in [
        ("ED_OK (aggregate ed25519 verify)", ED_OK),
        ("STAKE_TABLE_OK (stake-table root compare)", STAKE_TABLE_OK),
        ("ROOTED_OK (tower root reaches the slot)", ROOTED_OK),
        ("AUTH_OK (authorized-voter binding)", AUTH_OK),
    ] {
        let u = honest(LIVE_ACTIVE_STAKE, MIN_QUORUM);
        let mut cells = row_cells(u);
        assert_eq!(cells[col], 1, "the honest carrier is set");
        cells[col] = 0;
        let reason = must_refuse_violated_gate(
            &format!("a cleared carrier {name}"),
            &desc(),
            &cells,
            &pis_of(u),
        );
        eprintln!("cleared carrier {name}: {reason}");
    }
}

/// A forged PUBLIC ANCHOR: a bank-root limb on the wire disagreeing with the published PI. The nine
/// `.piBinding` pins are the addressing layer — they say WHICH trust root and WHICH full 256-bit
/// bank hash the proof is about — and a proof whose trace disagrees with its own public statement
/// must not verify.
///
/// ⚠ This is also the felt-width close: a SINGLE anchor felt bound only a 31-bit PROJECTION of the
/// bank hash, so two 256-bit roots agreeing in 31 bits both verified. Perturbing any ONE of the nine
/// limbs is refused, which is the observable half of that repair.
#[test]
fn a_bank_root_limb_that_disagrees_with_its_public_input_is_refused() {
    let u = honest(LIVE_ACTIVE_STAKE, MIN_QUORUM);
    let d = desc();
    for i in 0..BANK_ROOT_LIMBS {
        let mut cells = row_cells(u);
        cells[BANK_ROOT_0 + i] += 1;
        let reason = must_refuse_violated_gate(
            &format!("a bank-root limb {i} disagreeing with its PI pin"),
            &d,
            &cells,
            &pis_of(u),
        );
        eprintln!("forged bank-root limb {i}: {reason}");
    }
}

/// A replayed proof pointed at a DIFFERENT slot is refused: the slot rides `PI[10]` and the trace
/// column must agree with it.
#[test]
fn a_slot_that_disagrees_with_its_public_input_is_refused() {
    let u = honest(LIVE_ACTIVE_STAKE, MIN_QUORUM);
    let mut cells = row_cells(u);
    cells[SLOT_COL] += 1;
    let reason = must_refuse_violated_gate(
        "a rooted slot disagreeing with its PI pin",
        &desc(),
        &cells,
        &pis_of(u),
    );
    eprintln!("forged slot: {reason}");
}

// ═══════════════════════════════════════════════════════════════════════════════════════════
// ⚑ THE SECOND DEFECT — CLOSED 2026-08-03: the over-wide width is REFUSED AT DESCRIPTOR LOAD
// ═══════════════════════════════════════════════════════════════════════════════════════════

/// The served descriptor's own JSON bytes, so a width substitution below is done to the REAL wire
/// object rather than to a hand-typed stand-in.
const SOLANA_LC_JSON: &str =
    include_str!("../descriptors/by-name/dregg-solana-lightclient-verify-v1.json");

/// ⚑⚑ **THE WIDTH THAT SHIPPED IS NOW REFUSED AT THE DOOR, AND THIS TEST CHANGED MEANING.**
///
/// # What it used to assert, and why that was the bug and not the tooth
///
/// `dregg-solana-lightclient-verify::v1` shipped `bits: 128` on its range table. In Lean's `rangeRows 128` that interval
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
fn the_shipped_128_bit_width_refuses_even_an_honest_update() {
    // ── 1. LOAD REFUSES the width, on the real served bytes with one integer moved.
    let served = SOLANA_LC_JSON;
    assert!(
        parse_vm_descriptor2(served).is_ok(),
        "the SERVED descriptor must still load — its declared widths are 16 and 8"
    );
    for bad in [31usize, 32, 64, SHIPPED_SOL_BITS] {
        let mutated = served.replace("\"bits\":16", &format!("\"bits\":{bad}"));
        assert_ne!(mutated, served, "the width substitution must have bitten");
        let e = parse_vm_descriptor2(&mutated)
            .expect_err("a range table at or above 31 bits must be REFUSED AT LOAD");
        assert!(
            e.contains(&format!("declares bits {bad}")) && e.contains("refuses nothing"),
            "the refusal must name the width and the reason, got: {e}"
        );
        eprintln!("⚑ dregg-solana-lightclient-verify::v1 at bits={bad}: REFUSED AT LOAD — {e}");
    }

    // ── 2. THE MASK IS GONE: the honest row, at an in-memory vacuous width, now PROVES.
    //     Before the repair this was `row 0: range wire N value V >= 2^128` in release and a
    //     `shift left with overflow` panic under `cargo test`. The denotation always said it should
    //     be admitted; now the prover says so too.
    let u = honest(LIVE_ACTIVE_STAKE, MIN_QUORUM);
    must_prove("the honest live-scale u at the declared limb widths", u);
    must_prove_under(
        "⚑ the SAME honest u at an in-memory bits=128 — vacuous, therefore ADMITTED",
        &desc_with_limb_range_width(SHIPPED_SOL_BITS),
        u,
    );
    eprintln!(
        "⚑ dregg-solana-lightclient-verify::v1: the honest u now PROVES at an in-memory bits=128 (vacuous, admits \
         everything) instead of being refused by a masked comparison — and bits=128 can no \
         longer be LOADED at all"
    );
}
