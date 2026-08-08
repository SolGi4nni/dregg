//! ⚑⚑ **THE SOLANA ROOTED-FINALITY LIGHT CLIENT, PROVED ON THE DEPLOYED PROVER — AT MAINNET-BETA'S
//! LIVE ACTIVE STAKE, AND WITH ITS STAKE TABLE INSIDE THE PROOF.**
//!
//! # What this descriptor now is
//!
//! `dregg-solana-lightclient-verify::v1` is **MULTI-ROW** since 2026-08-04: one row per stake-table
//! entry. Its columns 0..43 are `dregg-solana-stake-table-fold::v1`'s columns, built from the SAME
//! Lean source leg list (`LightClientSolanaAir.foldLegs`,
//! `sol_fold_block_is_the_shared_source`), and the two numbers a Solana light client's trust story
//! hangs from are DERIVED from those rows:
//!
//!  * **`ANCHOR_ROOT` is the fold's eight `.last` output lanes** (`PI[0..7]`) — the weak-subjectivity
//!    stake-table root, as the IMAGE of the rows this proof exhibited. It was ONE column holding a
//!    256-bit SHA-256 root (compared at 31 bits), then NINE `.first` radix-`2^31` limbs that bound the
//!    full width and were read by no constraint at all.
//!  * **The active-stake DENOMINATOR is the fold's accumulator** (`ACC`, `PI[18..21]`, `.last`).
//!
//! `STAKE_TABLE_OK` is **DELETED**: it was a witnessed bit forced `= 1` asserting the sentence the
//! fold now computes. `LightClientSolStakeFoldAir.solLcAir_table_carrier_from_the_fold` discharges
//! the bridge's `stakeTableOk` from the emitted pin instead.
//!
//! ⚑ SUBSTRATE: the descriptor under test is Lean-authored and LEAN-COMPILED — `solLcVerifyDesc` is
//! `EffectLower.lowerAir` applied to the `EffectAir` source `solLcVerifyAir`
//! (`solLcVerifyAir_mainRailOk = true` by `rfl`), and that module contains no hand-written
//! `VmConstraint2`. This file writes NO constraints. It builds traces and asks the deployed prover.
//!
//! # The pair this file delivers, and it is the one the campaign asked for
//!
//!  * `a_same_tally_swap_is_arithmetically_perfect` — a FORGED validator set whose lamports sum to a
//!    **bit-identical published denominator** proves against its OWN root. Every carry, every range
//!    lookup, every accumulator gate, every chip absorb is satisfied. The forgery is not caught by
//!    arithmetic.
//!  * ⚑⚑ `a_same_tally_swap_is_refused_against_the_pinned_anchor_root` — the SAME forged table
//!    against the light client's pinned anchor, with the IDENTICAL four denominator felts. REFUSED by
//!    a violated gate.
//!
//! That is exactly the forgery the previous pass named as outside its scope:
//!
//! > ⚠ **Bound the claim.** This pins the DENOMINATOR, not the TABLE. … **a swap to a different
//! > validator set with the SAME total active stake is NOT refused by this.**
//!
//! # The two tally teeth, unchanged and still exercised
//!
//! **The empty stake table** and **the exact-2/3 point**. `γ = 1` — agave's STRICT `>` from
//! `get_highest_super_majority_root` (`core/src/commitment_service.rs:54-64`), which over 6,684,470
//! pairs below 2^53 matches the strict integer rule on ALL of them while the non-strict rule differs
//! on the exact-2/3 point every time; and at `total = 0`, `0f64/0f64 = NaN` and `NaN > x` is `false`,
//! so agave refuses the empty stake table at the threshold itself.
//!
//! # Scope, said plainly
//!
//! `ED_OK` / `ROOTED_OK` / `AUTH_OK` are witnessed carrier bits, not in-AIR ed25519; `ROOTED_STK` is a
//! witnessed projection (the prover still chooses WHICH of the bound validators it claims voted); the
//! bank root and slot are carried by no gate; the dregg-side STARK inherits the undischarged FRI
//! floor. The eight-lane anchor root is `8 · 30.906891 = 247.26` bits of image, so an equivocating
//! prover needs a **`2^123.63`** birthday collision — ⚠ **not** the `2^247.3` second-preimage figure
//! for the same object. This is a prover running the served object. It is **not** "Solana-valid" and
//! it is not "machine-checked" — the machine-checked statements are the Lean ones this file names,
//! and a Rust case-test quantifies over nothing.
//!
//! ⚠ **PROFILE — RUN IN RELEASE.** plonky3's ALGEBRAIC refusals are `#[cfg(debug_assertions)]` panics
//! under `cargo test` and clean `Err(OodEvaluationMismatch)` under `--release`; RANGE refusals are
//! `Err` in both. Every refusal here goes through `dregg_circuit::refusal`, which discriminates the
//! two mechanisms identically in both profiles and REDS on a crash wearing a refusal's clothes.
//!
//!     cargo nextest run --release -p dregg-circuit --test solana_lightclient_proves

use dregg_circuit::BabyBear;
use dregg_circuit::descriptor_by_name::descriptor_by_name;
use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, MemBoundaryWitness, TableSem, VmConstraint2, chip_absorb_all_lanes,
    parse_vm_descriptor2, prove_vm_descriptor2, verify_vm_descriptor2,
};
use dregg_circuit::heap_root::HeapLeaf;
use dregg_circuit::lean_descriptor_air::{VmConstraint, VmRow};
use dregg_circuit::refusal;

const SOL_LC_VERIFY_DESCRIPTOR: &str = "dregg-solana-lightclient-verify::v1";

// ═══════════════════════════════════════════════════════════════════════════════════════════
// Trace column layout — pinned to `LightClientSolanaAir`'s Lean `def`s (§1).
// ⚑ Columns 0..43 are the FOLD, at the same indices `dregg-solana-stake-table-fold::v1` uses.
// ═══════════════════════════════════════════════════════════════════════════════════════════

/// Lane 0 of the running eight-felt table root ENTERING this row (cols 0..7).
const ROOT_IN_0: usize = 0;
/// Lane 0 of this entry's vote-account pubkey — nine radix-`2^29` lanes (cols 8..16).
const VOTER_0: usize = 8;
/// Limb 0 of this entry's active stake, LSB-first (cols 17..20).
const STAKE_0: usize = 17;
/// Lane 0 of the INTERMEDIATE state, after the row's first message block (cols 21..28).
const MID_0: usize = 21;
/// ⚑ Lane 0 of the running table root LEAVING this row (cols 29..36). Its LAST-row value is
/// `ANCHOR_ROOT` — the light client's trust anchor, DERIVED.
const ROOT_OUT_0: usize = 29;
/// ⚑ Limb 0 of the running TOTAL active stake (cols 37..40). Its LAST-row value is the quorum's
/// DENOMINATOR and `PI[18..21]`.
const ACC_0: usize = 37;
/// Carry 0 of the accumulator's limb addition, boolean-pinned on EVERY row (cols 41..43).
const CARRY_0: usize = 41;
/// The fold block's width.
const FOLD_WIDTH: usize = 44;

/// ⚑ The denominator IS the accumulator. Not a copy forced equal by a gate — the same column.
const TOTAL_STK_0: usize = ACC_0;

/// CARRIER — the aggregate ed25519 verify result over the counted authorized voters.
const ED_OK: usize = 44;
/// GATE — every counted vote's tower root reaches the slot (HOLE-1).
const ROOTED_OK: usize = 45;
/// GATE — every counted signer is the on-chain authorized voter (BR-2-A).
const AUTH_OK: usize = 46;
/// `ROOTED_STK` limb 0 (LSB). Limbs 0..3 are columns 47..50.
const ROOTED_STK_0: usize = 47;
/// `QDIFF` limb 0 (LSB). FIVE limbs, columns 51..55 — `3·A` needs two bits beyond `A`.
const QDIFF_0: usize = 51;
/// The offset carry out of quorum rung 0. Four carries, columns 56..59; each denotes `col − 128`.
const QDIFF_CARRY_0: usize = 56;
/// `TPOS` limb 0 (LSB) — the `EmptyStakeTable` floor difference `total − 1`. Columns 60..64.
const TPOS_0: usize = 60;
/// The offset carry out of floor rung 0. Four carries, columns 65..68.
const TPOS_CARRY_0: usize = 65;
/// PUBLIC ANCHOR limb 0 — the rooted bank hash as nine radix-`2^31` MSB-first limbs, cols 69..77.
/// ⚠ Read by no gate; the tripwire that says so is
/// `sol_bank_root_and_slot_remain_arithmetically_inert`.
const BANK_ROOT_0: usize = 69;
const BANK_ROOT_LIMBS: usize = 9;
/// PUBLIC ANCHOR — the rooted slot S. ⚠ Also read by no gate.
const SLOT_COL: usize = 78;

const SOL_LC_WIDTH: usize = 79;
const SOL_PI_COUNT: usize = 22;

/// ⚑ The eight lanes the WS stake-table anchor root is bound at — the chip's squeeze width.
const ANCHOR_LANES: usize = 8;
/// PI slot of anchor-root lane 0 — pinned on the LAST row from `ROOT_OUT`.
const PI_ANCHOR_ROOT_0: usize = 0;
/// PI slot of bank-root limb 0.
const PI_BANK_ROOT_0: usize = 8;
/// PI slot of the rooted slot.
const PI_SLOT: usize = 17;
/// ⚑ PI slot of total-stake limb 0 — pinned on the LAST row from the fold's accumulator.
const PI_TOTAL_STK_0: usize = 18;

/// The tally limb width. `4 · 16 = 64` — four limbs are exactly a `u64`, Solana's lamport type.
const SOL_LIMB_BITS: usize = 16;
/// The chain-carry width (the prover's own byte bus: one aux column, one byte lookup).
const SOL_CARRY_BITS: usize = 8;
/// The fold's pubkey-lane width — 29 is the last wrap-free width at BabyBear.
const SOL_LANE_BITS: usize = 29;
/// The fold's TOP pubkey lane width: `8·29 + 24 = 256`, exactly a 32-byte pubkey.
const SOL_TOP_LANE_BITS: usize = 24;

/// Declared wire id of the 16-bit tally-limb table (`.custom (64 + 16)` ⇒ `5 + 80`). ⚑ SHARED with
/// the fold's stake and accumulator limbs — one table, because they are one kind of number.
const TID_TALLY_LIMB: usize = 85;
/// Declared wire id of the 8-bit chain-carry table (`.custom (64 + 8)` ⇒ `5 + 72`).
const TID_TALLY_CARRY: usize = 77;
/// Declared wire id of the fold's 29-bit pubkey-lane table.
const TID_LANE: usize = 98;
/// Declared wire id of the fold's 24-bit top-lane table.
const TID_TOP_LANE: usize = 93;
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
/// a shift by 0, so the same declaration ALSO refused every nonzero row in the prover.
const SHIPPED_SOL_BITS: usize = 128;

/// The smallest FULLY VACUOUS width (`2^32 > p`, so `[0, 2^32)` covers the field) the deployed
/// prover can still execute — `1u64 << 32` is well-defined where `1u64 << 128` is not.
const VACUOUS_BITS: usize = 32;

/// ⚑ **ONE ROW PER STAKE-TABLE ENTRY.** The committed trace must be a power of two; rows a table does
/// not fill are the canonical ZERO ENTRY, which is how a shorter table is padded — a zero row adds
/// nothing to the tally and is part of what the anchor root commits to.
const TRACE_ROWS: usize = 8;

/// The BabyBear modulus. ⚑ **READ FROM THE FIELD MODULE, NOT RETYPED.** It was
/// `const P: i64 = 2_013_265_921;` — a second spelling of `BABYBEAR_P`, and the pin below is a
/// claim about THE FIELD, not about a number that happens to sit in this file.
const P: i64 = dregg_circuit::field::BABYBEAR_P as i64;

/// ⚑ **THE VACUITY CONTROL REALLY IS VACUOUS — PINNED AT BUILD TIME.** Both operands are
/// constants, so this stood as `assert!` inside whichever `#[test]` happened to carry it: a
/// build-time obligation reported only after every other leg in this file had already been
/// compiled against it, and only when that one test ran. `const _` refuses the BUILD instead.
const _: () = assert!(
    (1u64 << VACUOUS_BITS) > P as u64,
    "the control width must actually be vacuous — its interval must cover the field, or every \
     paired-polarity leg in this file silently degrades into a one-sided assertion"
);

/// `LightClientSolStakeFoldAir.FOLD_TAG` — ASCII `SSTF`, lane 0 of the pinned initial state.
const FOLD_TAG: u32 = 0x5353_5446;

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
/// wins over the `CUSTOM_RANGE_WIDTHS` fallback, so one integer moves and nothing else does. It
/// touches the 16-bit table ONLY; the 29-, 24- and 8-bit tables are left alone.
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
        "exactly the 16-bit tally-limb table must be re-declared; the other three stay put"
    );
    d
}

/// Field-encode a possibly-negative integer: in BabyBear a negative value IS `p − k`, which is the
/// element a limb tooth must refuse. This is where a failed quorum's top difference limb lands.
fn felt(v: i64) -> BabyBear {
    BabyBear::new(v.rem_euclid(P) as u32)
}

fn f(v: u32) -> BabyBear {
    BabyBear::new(v)
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

/// The same decomposition as `u32` limbs, for the fold's accumulator arithmetic.
fn limbs4_u32(v: u64) -> [u32; RUNGS] {
    let mut out = [0u32; RUNGS];
    for (i, o) in out.iter_mut().enumerate() {
        *o = ((v >> (SOL_LIMB_BITS * i)) & 0xFFFF) as u32;
    }
    out
}

/// ⚑ **THE HONEST FILL**, parametric in the chain constants, because this AIR runs TWO chains over
/// the same limb vectors and they do not share constants:
///
///  * the QUORUM chain is `α = 3` on rooted stake, `β = 2` on the fold's accumulator, ⚑ `γ = 1` —
///    agave's STRICT `3·rooted > 2·total`,
///  * the FLOOR chain is `α = 1`, `β = 0`, `γ = 1` — `total − 1 ≥ 0`, the `EmptyStakeTable` refusal.
///
/// `fillDigit` is a FLOOR mod (`rem_euclid`) and `fillCarry` is the exact floor quotient, so
/// `raw − d − c·2^16 = 0` holds identically (`LimbTally.fill_splits`).
///
/// ⚠ When the comparison FAILS the final carry is NEGATIVE and `diff[4]` comes out negative. That
/// is the refusal, and this function expresses it rather than hiding it.
fn fill_chain(alpha: i64, a: [i64; RUNGS], beta: i64, b: [i64; RUNGS], gamma: i64) -> ChainFill {
    let radix: i64 = 1 << SOL_LIMB_BITS;
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

/// The value a limb vector denotes over ℤ (`LimbTally.limbValue`, LSB-first Horner).
fn limb_value(limbs: &[i64]) -> i128 {
    let mut acc: i128 = 0;
    for &l in limbs.iter().rev() {
        acc = acc * (1i128 << SOL_LIMB_BITS) + l as i128;
    }
    acc
}

// ═══════════════════════════════════════════════════════════════════════════════════════════
// ⚑ THE STAKE TABLE — the rows the fold binds
// ═══════════════════════════════════════════════════════════════════════════════════════════

/// One stake-table entry: a 32-byte vote pubkey as nine radix-`2^29` lanes, and a `u64` of lamports.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
struct Entry {
    voter: [u32; 9],
    stake: u64,
}

/// The canonical padding entry — a zero row adds nothing to the tally and IS part of the frame the
/// anchor root commits to.
const ZERO_ENTRY: Entry = Entry {
    voter: [0; 9],
    stake: 0,
};

/// Validator A. (Any canonical nonet does: the fold binds the ROWS, not what they mean on Solana.)
const PK_A: [u32; 9] = [11, 22, 33, 44, 55, 66, 77, 88, 99];
/// Validator B — the minority holder that wants to be the majority holder.
const PK_B: [u32; 9] = [111, 222, 333, 444, 555, 666, 777, 888, 999];
/// A third member, for the "one more validator at the same tally" case.
const PK_C: [u32; 9] = [7, 7, 7, 7, 7, 7, 7, 7, 7];

/// The update a Solana rooted-finality proof carries. ⚑ The DENOMINATOR is not a field of this
/// struct — it is `total_stk()`, summed off the table, exactly as the AIR's accumulator sums it.
#[derive(Clone)]
struct Update {
    /// The stake table, one entry per trace row (padded with `ZERO_ENTRY`).
    entries: Vec<Entry>,
    /// ⚑ `u64`. The counted rooted authorized voting stake; its ed25519 provenance is `ED_OK`.
    /// ⚠ Still a WITNESSED PROJECTION — the fold binds who is in the table, not who voted.
    rooted_stk: u64,
    ed_ok: u32,
    rooted_ok: u32,
    auth_ok: u32,
    bank_root: [u32; BANK_ROOT_LIMBS],
    slot: u32,
}

impl Update {
    /// The active-stake denominator, summed off the exhibited table.
    fn total_stk(&self) -> u64 {
        self.entries.iter().map(|e| e.stake).sum()
    }
}

/// An HONEST update over an EXPLICIT stake table.
fn honest_table(entries: Vec<Entry>, rooted_stk: u64) -> Update {
    assert!(
        entries.len() <= TRACE_ROWS,
        "the table must fit the committed trace height"
    );
    Update {
        entries,
        rooted_stk,
        ed_ok: 1,
        rooted_ok: 1,
        auth_ok: 1,
        bank_root: [1, 2, 3, 4, 5, 6, 7, 8, 9],
        slot: LIVE_SLOT,
    }
}

/// An HONEST update at a chosen TOTAL: a single vote account holding all of it, placed on the LAST
/// row with zero entries before it. ⚑ Placing it last is what makes the last row's `STAKE` limbs and
/// its `ACC` limbs the same four numbers, which is the arrangement `LightClientSolanaAir.
/// solMaxScaleCells` exhibits and `solMaxScaleRow_accumulator_is_the_row_stake` checks.
fn honest(total_stk: u64, rooted_stk: u64) -> Update {
    let mut entries = vec![ZERO_ENTRY; TRACE_ROWS - 1];
    entries.push(Entry {
        voter: PK_A,
        stake: total_stk,
    });
    honest_table(entries, rooted_stk)
}

/// ⚑ **THE PRODUCER.** One row per entry: two arity-16 absorbs of the SAME `state8 ‖ block8` shape,
/// a four-limb `u64` accumulator with boolean carries — and the quorum block, filled identically on
/// every row because it is a fact about the FINAL total and the `.last`-scoped gates read it there.
///
/// Returns the whole trace as `i64` cells so a forgery test can perturb a cell and so a refused row's
/// negative top difference limb survives to `felt` unaltered.
fn trace_cells(u: &Update) -> Vec<Vec<i64>> {
    assert!(u.entries.len() <= TRACE_ROWS);
    let total = u.total_stk();
    let total_l = limbs4(total);
    let rooted_l = limbs4(u.rooted_stk);
    // §2: `α = 3` on rooted, `β = 2` on the accumulator, ⚑ `γ = 1` — agave's STRICT `3·R > 2·T`.
    let q = fill_chain(3, rooted_l, 2, total_l, QUORUM_GAMMA);
    // §2: `α = 1`, `β = 0`, `γ = 1` — `total − 1 ≥ 0`. The `β` operand column is the accumulator ON
    // PURPOSE (`tposRungs`): at `β = 0` the emitted term is `0 · var`.
    let t = fill_chain(1, total_l, 0, total_l, FLOOR_GAMMA);

    let mut st = [BabyBear::new(0); 8];
    st[0] = f(FOLD_TAG);
    let mut acc = [0u32; RUNGS];
    let mut rows: Vec<Vec<i64>> = Vec::with_capacity(TRACE_ROWS);

    for r in 0..TRACE_ROWS {
        let e = u.entries.get(r).copied().unwrap_or(ZERO_ENTRY);
        let stk = limbs4_u32(e.stake);

        // Block A: the running state and the eight LOW pubkey lanes.
        let mut ins_a = [BabyBear::new(0); 16];
        ins_a[..8].copy_from_slice(&st);
        for j in 0..8 {
            ins_a[8 + j] = f(e.voter[j]);
        }
        let mid = chip_absorb_all_lanes(16, &ins_a);

        // Block B: the intermediate state, the top pubkey lane, the four stake limbs, three zeros.
        let mut ins_b = [BabyBear::new(0); 16];
        ins_b[..8].copy_from_slice(&mid);
        ins_b[8] = f(e.voter[8]);
        for i in 0..RUNGS {
            ins_b[9 + i] = f(stk[i]);
        }
        let root_out = chip_absorb_all_lanes(16, &ins_b);

        // The u64 limb addition, with the three boolean carries the AIR pins.
        let mut new_acc = [0u32; RUNGS];
        let mut carry = 0u32;
        let mut carries = [0u32; RUNGS - 1];
        for i in 0..RUNGS {
            let s = acc[i] + stk[i] + carry;
            new_acc[i] = s & 0xFFFF;
            carry = s >> 16;
            if i < RUNGS - 1 {
                carries[i] = carry;
            }
        }
        assert_eq!(
            carry, 0,
            "the running total overflowed a u64 — no honest fill exists"
        );

        let mut row = vec![0i64; SOL_LC_WIDTH];
        for j in 0..8 {
            row[ROOT_IN_0 + j] = st[j].as_u32() as i64;
            row[MID_0 + j] = mid[j].as_u32() as i64;
            row[ROOT_OUT_0 + j] = root_out[j].as_u32() as i64;
        }
        for j in 0..9 {
            row[VOTER_0 + j] = e.voter[j] as i64;
        }
        for i in 0..RUNGS {
            row[STAKE_0 + i] = stk[i] as i64;
            row[ACC_0 + i] = new_acc[i] as i64;
        }
        for i in 0..RUNGS - 1 {
            row[CARRY_0 + i] = carries[i] as i64;
        }
        row[ED_OK] = u.ed_ok as i64;
        row[ROOTED_OK] = u.rooted_ok as i64;
        row[AUTH_OK] = u.auth_ok as i64;
        row[ROOTED_STK_0..ROOTED_STK_0 + RUNGS].copy_from_slice(&rooted_l);
        row[QDIFF_0..QDIFF_0 + RUNGS + 1].copy_from_slice(&q.diff);
        row[QDIFF_CARRY_0..QDIFF_CARRY_0 + RUNGS].copy_from_slice(&q.carry);
        row[TPOS_0..TPOS_0 + RUNGS + 1].copy_from_slice(&t.diff);
        row[TPOS_CARRY_0..TPOS_CARRY_0 + RUNGS].copy_from_slice(&t.carry);
        for (i, l) in u.bank_root.iter().enumerate() {
            row[BANK_ROOT_0 + i] = *l as i64;
        }
        row[SLOT_COL] = u.slot as i64;
        rows.push(row);

        st = root_out;
        acc = new_acc;
    }
    rows
}

/// The eight-lane anchor root this trace publishes — the LAST row's `ROOT_OUT`.
fn anchor_root_of(cells: &[Vec<i64>]) -> [i64; ANCHOR_LANES] {
    let last = cells.last().expect("a trace has rows");
    let mut out = [0i64; ANCHOR_LANES];
    out.copy_from_slice(&last[ROOT_OUT_0..ROOT_OUT_0 + ANCHOR_LANES]);
    out
}

/// The twenty-two published anchors, in PI order: EIGHT fold root lanes (`.last`), nine bank-root
/// limbs, the slot, and the four accumulator limbs (`.last`) — the derived denominator.
fn pis_from(cells: &[Vec<i64>], u: &Update) -> Vec<BabyBear> {
    let last = cells.last().expect("a trace has rows");
    let mut pis = vec![BabyBear::new(0); SOL_PI_COUNT];
    for j in 0..ANCHOR_LANES {
        pis[PI_ANCHOR_ROOT_0 + j] = felt(last[ROOT_OUT_0 + j]);
    }
    for (i, l) in u.bank_root.iter().enumerate() {
        pis[PI_BANK_ROOT_0 + i] = BabyBear::new(*l);
    }
    pis[PI_SLOT] = BabyBear::new(u.slot);
    for i in 0..RUNGS {
        pis[PI_TOTAL_STK_0 + i] = felt(last[ACC_0 + i]);
    }
    pis
}

fn pis_of(u: &Update) -> Vec<BabyBear> {
    pis_from(&trace_cells(u), u)
}

/// Set one column on EVERY row. ⚑ The quorum block is constant down the trace, so a forgery of it is
/// a forgery of the whole column; and the per-limb range lookups fire on every row, so a forger who
/// touched only the last row would be caught by a different tooth than the one under test.
fn set_col(cells: &mut [Vec<i64>], col: usize, v: i64) {
    for row in cells.iter_mut() {
        row[col] = v;
    }
}

/// Add `d` to one column on EVERY row.
fn bump_col(cells: &mut [Vec<i64>], col: usize, d: i64) {
    for row in cells.iter_mut() {
        row[col] += d;
    }
}

fn trace_of(cells: &[Vec<i64>]) -> Vec<Vec<BabyBear>> {
    cells
        .iter()
        .map(|r| r.iter().map(|&v| felt(v)).collect())
        .collect()
}

/// PROVE and VERIFY, both legs, exactly as a deployed consumer would.
fn prove_and_verify(
    d: &EffectVmDescriptor2,
    cells: &[Vec<i64>],
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
fn must_prove(what: &str, u: &Update) {
    must_prove_under(what, &desc(), u);
}

fn must_prove_under(what: &str, d: &EffectVmDescriptor2, u: &Update) {
    let cells = trace_cells(u);
    let pis = pis_from(&cells, u);
    refusal::must_accept(what, || prove_and_verify(d, &cells, &pis));
}

/// A RANGE refusal: the prover's layout filler has no honest completion for a wire outside its
/// declared interval. An `Err` in EVERY profile — never a panic, never debug-only.
fn must_refuse_out_of_range(
    what: &str,
    d: &EffectVmDescriptor2,
    cells: &[Vec<i64>],
    pis: &[BabyBear],
) -> String {
    let e: String = refusal::must_refuse(what, || prove_and_verify(d, cells, pis));
    assert!(
        e.contains("range wire"),
        "{what}: expected the RANGE tooth (`row R: range wire N value V >= 2^b`), got: {e}"
    );
    e
}

/// An ALGEBRAIC refusal: some emitted gate does not vanish. Under `cargo test` this is p3's
/// `constraints not satisfied on row N`; under `--release` it is the deployed verifier's
/// `OodEvaluationMismatch`. The load-bearing half is the NEGATIVE clause — a tooth whose subject is
/// a specific gate must not be satisfied by the lookup bus failing instead.
fn must_refuse_violated_gate(
    what: &str,
    d: &EffectVmDescriptor2,
    cells: &[Vec<i64>],
    pis: &[BabyBear],
) -> String {
    let r = refusal::must_refuse_or_unsat_panic(what, || prove_and_verify(d, cells, pis));
    let reason = r.reason();
    refusal::assert_violated_constraint_not_bus(what, &reason);
    reason
}

/// Mainnet-beta's ACTIVE stake, measured live 2026-08-03 via `getVoteAccounts` on
/// `api.mainnet-beta.solana.com` (689 current + 14 delinquent vote accounts, epoch 1011):
/// `432.650M SOL = 2^58.586`. **214,899,670 × the BabyBear modulus.**
const LIVE_ACTIVE_STAKE: u64 = 432_650_183_925_625_587;

/// ⚑ The EXACT-2/3 point at that total: `3 · 288_433_455_950_417_058 = 865_300_367_851_251_174`
/// is `2 · LIVE_ACTIVE_STAKE` on the nose. It was the accepting anchor under the shipped non-strict
/// rule; under agave's STRICT `>` it is a **REFUSAL**.
const EXACT_TWO_THIRDS: u64 = 288_433_455_950_417_058;

/// The SMALLEST rooted stake satisfying agave's STRICT `3·rooted > 2·total` at that total —
/// **one lamport** above the exact-2/3 point, out of 4.3e17.
const MIN_QUORUM: u64 = 288_433_455_950_417_059;

/// The quorum chain's `γ`. ⚑ `1` = STRICT (`3·rooted ≥ 2·total + 1`).
const QUORUM_GAMMA: i64 = 1;

/// The emptiness floor's `γ` — `total − 1 ≥ 0`.
const FLOOR_GAMMA: i64 = 1;

/// Mainnet-beta's total SUPPLY at the same sample (`getSupply`): `2^59.13`.
const LIVE_TOTAL_SUPPLY: u64 = 631_503_420_149_974_995;

/// The measured live slot at the same sample.
const LIVE_SLOT: u32 = 436_909_708;

/// `LightClientSolanaAir.solMaxScaleCells`, transcribed — the LAST row at live scale.
///
/// ⚠ **THE TWENTY-FOUR CHIP-CHAIN CELLS ARE ZERO IN THE LEAN ROW AND ARE NOT ZERO HERE.**
/// `ROOT_IN`, `MID` and `ROOT_OUT` are the deployed Poseidon2 chip's running images, and nothing in
/// `LightClientSolanaAir` models Poseidon2 (`LightClientSolStakeFoldAir` §4 carries it as an OPAQUE
/// `List ℤ → Digest8`). So `the_honest_fill_reproduces_the_lean_row` compares the FIFTY-FIVE cells
/// Lean genuinely models, and asserts separately that the other twenty-four are what the deployed
/// permutation produced. Claiming "the same 79 numbers" would be false for twenty-four of them.
const LEAN_MAX_SCALE_CELLS: [i64; SOL_LC_WIDTH] = [
    // ROOT_IN 0..7 — the chip's running image, NOT modelled in Lean
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0, //
    // VOTER 0..8
    11,
    22,
    33,
    44,
    55,
    66,
    77,
    88,
    99, //
    // STAKE 0..3 = 432650183925625587 (live active stake)
    62195,
    52452,
    5388,
    1537, //
    // MID 0..7 — the chip's image, NOT modelled in Lean
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0, //
    // ROOT_OUT 0..7 — the chip's image, NOT modelled in Lean
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    0, //
    // ACC 0..3 = the DENOMINATOR, and PI 18..21
    62195,
    52452,
    5388,
    1537, //
    // CARRY 0..2
    0,
    0,
    0, //
    // ED_OK, ROOTED_OK, AUTH_OK
    1,
    1,
    1, //
    // ROOTED_STK limbs = 288433455950417059 (minimal STRICT quorum)
    19619,
    13123,
    47283,
    1024, //
    // QDIFF limbs = 3·R − 2·T − 1 = 2
    2,
    0,
    0,
    0,
    0, //
    // QDIFF carries, offset (honest carries −1, −1, +2, 0)
    127,
    127,
    130,
    128, //
    // TPOS limbs = T − 1
    62194,
    52452,
    5388,
    1537,
    0, //
    // TPOS carries, offset
    128,
    128,
    128,
    128, //
    // BANK_ROOT limbs 0..8
    1,
    2,
    3,
    4,
    5,
    6,
    7,
    8,
    9, //
    // SLOT_COL
    436_909_708,
];

/// The columns Lean does NOT model — the chip's running images.
const CHIP_CHAIN_COLS: [std::ops::Range<usize>; 3] = [
    ROOT_IN_0..ROOT_IN_0 + 8,
    MID_0..MID_0 + 8,
    ROOT_OUT_0..ROOT_OUT_0 + 8,
];

fn is_chip_chain(col: usize) -> bool {
    CHIP_CHAIN_COLS.iter().any(|r| r.contains(&col))
}

// ═══════════════════════════════════════════════════════════════════════════════════════════
// The served object
// ═══════════════════════════════════════════════════════════════════════════════════════════

/// The descriptor this tree serves is the one the Lean module declares — width, PI count,
/// constraint count, and all four declared limb widths.
#[test]
fn the_served_descriptor_is_the_lean_emitted_one() {
    let d = desc();
    assert_eq!(d.name, SOL_LC_VERIFY_DESCRIPTOR);
    assert_eq!(
        d.trace_width, SOL_LC_WIDTH,
        "⚑ 49 → 79: the stake-table fold's 44 columns absorbed, the nine .first anchor-root limbs \
         deleted, the four dedicated total-stake columns deleted (the accumulator IS the \
         denominator) and STAKE_TABLE_OK deleted"
    );
    assert_eq!(
        d.public_input_count, SOL_PI_COUNT,
        "⚑ 23 → 22: nine .first anchor-root limbs replaced by EIGHT .last fold output lanes"
    );
    // 41 lookups + 22 boundary gates + 18 window gates + 22 pi_bindings = 103
    // (`LightClientSolanaAir.sol_shape_pins`).
    assert_eq!(d.constraints.len(), 103);
    assert_eq!(
        d.tables.len(),
        4,
        "⚑ the fold's range_w29 / range_w24 join range_w16 and range_w8"
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
    // file's constants. A constant compared against its own definition is decoration.
    let served_limb_bits = bits_of(TID_TALLY_LIMB);
    assert_eq!(served_limb_bits, SOL_LIMB_BITS);
    assert_eq!(bits_of(TID_TALLY_CARRY), SOL_CARRY_BITS);
    assert_eq!(bits_of(TID_LANE), SOL_LANE_BITS);
    assert_eq!(bits_of(TID_TOP_LANE), SOL_TOP_LANE_BITS);
    assert!(
        served_limb_bits <= 29 && bits_of(TID_LANE) <= 29,
        "no declared width may reach the wrap-free ceiling — at 30 the interval leaks and at 31 it \
         contains the whole field"
    );

    // ⚑ The felt-wide `range` table is GONE (`sol_range_table_is_not_declared`).
    assert!(
        d.tables.iter().all(|t| t.id != TID_FELT_RANGE),
        "⚑ the shared felt-wide range table must NOT be declared — it is where the 128-bit vacuity \
         lived, and both of its lookups are limbed chains now"
    );

    // ⚑ THE ANCHOR PINS ARE ON THE LAST ROW. This is the whole pass, read off the served bytes: a
    // pin that drifted back to `first` would publish a PREFIX of the fold, i.e. a root and a total
    // for a table that is not the one committed.
    let last_pins: Vec<(usize, usize)> = d
        .constraints
        .iter()
        .filter_map(|c| match c {
            VmConstraint2::Base(VmConstraint::PiBinding { row, col, pi_index })
                if *row == VmRow::Last =>
            {
                Some((*col, *pi_index))
            }
            _ => None,
        })
        .collect();
    assert_eq!(
        last_pins.len(),
        ANCHOR_LANES + RUNGS,
        "⚑ TWELVE last-row pins: the eight fold root lanes and the four accumulator limbs \
         (`LightClientSolanaAir.sol_pin_rows`)"
    );
    for j in 0..ANCHOR_LANES {
        assert!(
            last_pins.contains(&(ROOT_OUT_0 + j, PI_ANCHOR_ROOT_0 + j)),
            "root lane {j} must be pinned from ROOT_OUT on the LAST row"
        );
    }
    for i in 0..RUNGS {
        assert!(
            last_pins.contains(&(ACC_0 + i, PI_TOTAL_STK_0 + i)),
            "denominator limb {i} must be pinned from the ACCUMULATOR on the LAST row"
        );
    }

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

/// The Rust filler and the Lean row are the same FIFTY-FIVE numbers — every cell but the
/// twenty-four the deployed Poseidon2 chip produces. Lean hand-writes them (`solMaxScaleCells`) and
/// `decide`s what they denote; Rust derives them from the TABLE through the fold and `fill_chain`.
#[test]
fn the_honest_fill_reproduces_the_lean_row() {
    let u = honest(LIVE_ACTIVE_STAKE, MIN_QUORUM);
    let cells = trace_cells(&u);
    let last = cells.last().unwrap();
    assert_eq!(last.len(), SOL_LC_WIDTH);

    let mut modelled = 0usize;
    for col in 0..SOL_LC_WIDTH {
        if is_chip_chain(col) {
            continue;
        }
        modelled += 1;
        assert_eq!(
            last[col], LEAN_MAX_SCALE_CELLS[col],
            "col {col} differs from LightClientSolanaAir.solMaxScaleCells"
        );
    }
    assert_eq!(
        modelled,
        SOL_LC_WIDTH - 24,
        "fifty-five cells are Lean-modelled; the other twenty-four are the chip's running image"
    );

    // …and the twenty-four that are NOT compared are genuinely the permutation's, not zeros the
    // filler forgot: the last row's ROOT_IN is the previous row's ROOT_OUT, by the continuity gate.
    let prev = &cells[cells.len() - 2];
    for j in 0..8 {
        assert_eq!(
            last[ROOT_IN_0 + j],
            prev[ROOT_OUT_0 + j],
            "the fold's state continuity must hold on the wire, lane {j}"
        );
    }
    assert!(
        (0..8).any(|j| last[ROOT_OUT_0 + j] != 0),
        "the published anchor root must not be all zeros — that would mean the chip never ran"
    );

    // ⚑ THE DENOMINATOR IS THE ACCUMULATOR: the four published limbs recompose to the table's sum.
    let mut acc = [0i64; RUNGS];
    acc.copy_from_slice(&last[ACC_0..ACC_0 + RUNGS]);
    assert_eq!(limb_value(&acc), LIVE_ACTIVE_STAKE as i128);
    assert_eq!(u.total_stk(), LIVE_ACTIVE_STAKE);

    // …and the fills really recompose (`LimbTally.chain_recomposes`).
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
    assert!(
        3 * EXACT_TWO_THIRDS as i128 >= 2 * LIVE_ACTIVE_STAKE as i128,
        "non-strict ACCEPTS it"
    );
    assert!(
        !(3 * EXACT_TWO_THIRDS as i128 > 2 * LIVE_ACTIVE_STAKE as i128),
        "strict REFUSES it"
    );

    // ⚑ And the quorum carries are NOT trivial: `[127, 127, 130, 128]` is `[−1, −1, +2, 0]`.
    assert_eq!(q.carry, [127, 127, 130, 128]);
    assert!(q.carry.iter().any(|&c| c > CARRY_OFF) && q.carry.iter().any(|&c| c < CARRY_OFF));
}

// ═══════════════════════════════════════════════════════════════════════════════════════════
// ⚑⚑ THE MEASUREMENT — a prover has run this descriptor
// ═══════════════════════════════════════════════════════════════════════════════════════════

/// ⚑⚑ **THE DELIVERABLE: MAINNET-BETA'S LIVE ACTIVE STAKE PROVES AND VERIFIES ON THE DEPLOYED RUST
/// PROVER, WITH ITS STAKE TABLE FOLDED INSIDE THE SAME PROOF.**
#[test]
fn the_live_mainnet_beta_active_stake_proves() {
    let u = honest(LIVE_ACTIVE_STAKE, MIN_QUORUM);
    assert!(3 * u.rooted_stk as i128 > 2 * u.total_stk() as i128);

    let t0 = std::time::Instant::now();
    must_prove(
        "⚑ mainnet-beta's live active stake at the minimal STRICT quorum",
        &u,
    );
    let dt = t0.elapsed();
    let root = anchor_root_of(&trace_cells(&u));
    eprintln!(
        "⚑ SOLANA LIVE ACTIVE STAKE: total={} rooted={} slot={} PROVED AND VERIFIED in {:?} \
         ({TRACE_ROWS} trace rows, {SOL_LC_WIDTH} columns, {FOLD_WIDTH} of them the fold)\n   \
         derived anchor root lanes = {root:?}",
        u.total_stk(),
        u.rooted_stk,
        u.slot,
        dt
    );
}

/// ⚑ **AND AT THE PROTOCOL CEILING.** Mainnet-beta's TOTAL SUPPLY bounds any stake table that can
/// ever exist. A stake table at the whole supply, with its minimal quorum, proves.
#[test]
fn a_stake_table_at_the_whole_supply_proves() {
    let total = LIVE_TOTAL_SUPPLY;
    // ⚑ ceil((2T+1)/3), the minimal STRICT quorum (agave's `>`), not ceil(2T/3).
    let rooted = (2 * total as u128 + 1).div_ceil(3) as u64;
    assert!(3 * rooted as u128 > 2 * total as u128);
    assert!(!(3 * ((rooted - 1) as u128) > 2 * total as u128));

    let u = honest(total, rooted);
    let cells = trace_cells(&u);
    let q = fill_chain(3, limbs4(rooted), 2, limbs4(total), QUORUM_GAMMA);
    assert!(
        q.carry.iter().any(|&c| c != CARRY_OFF),
        "the carry chain must do real work at the supply ceiling; carries = {:?}",
        q.carry
    );
    assert_eq!(
        cells.last().unwrap()[TOTAL_STK_0..TOTAL_STK_0 + RUNGS],
        limbs4(total)[..]
    );

    let t0 = std::time::Instant::now();
    must_prove("⚑ a stake table at mainnet-beta's TOTAL SUPPLY", &u);
    eprintln!(
        "⚑ SUPPLY CEILING: total={total} rooted={rooted} PROVED AND VERIFIED in {:?}\n   total \
         limbs {:?}\n   qdiff limbs {:?}\n   offset carries {:?} (offset {CARRY_OFF})",
        t0.elapsed(),
        limbs4(total),
        q.diff,
        q.carry
    );
}

/// ⚑ **A REAL MULTI-MEMBER TABLE PROVES** — 703 vote accounts is the live count, and this proves the
/// shape at the committed height with several distinct members carrying distinct stakes, so the
/// accumulator's carry chain and the root chain both do work across rows rather than on one row.
#[test]
fn a_multi_member_stake_table_proves() {
    let entries = vec![
        Entry {
            voter: PK_A,
            stake: 200_000_000_000_000_000,
        },
        Entry {
            voter: PK_B,
            stake: 132_650_183_925_625_587,
        },
        Entry {
            voter: PK_C,
            stake: 100_000_000_000_000_000,
        },
    ];
    let u = honest_table(entries, MIN_QUORUM);
    assert_eq!(
        u.total_stk(),
        LIVE_ACTIVE_STAKE,
        "the three members must sum to the live active stake"
    );
    let cells = trace_cells(&u);
    // The accumulator really ticks: three distinct running totals before the padding rows.
    let running: Vec<i128> = cells
        .iter()
        .map(|r| {
            let mut a = [0i64; RUNGS];
            a.copy_from_slice(&r[ACC_0..ACC_0 + RUNGS]);
            limb_value(&a)
        })
        .collect();
    assert_eq!(running[0], 200_000_000_000_000_000);
    assert_eq!(running[2], LIVE_ACTIVE_STAKE as i128);
    assert_eq!(*running.last().unwrap(), LIVE_ACTIVE_STAKE as i128);
    must_prove(
        "⚑ a three-member stake table summing to live active stake",
        &u,
    );
    eprintln!(
        "⚑ MULTI-MEMBER TABLE PROVED: running accumulator {:?}",
        running
    );
}

/// ⚑⚑ **THE EXACT-2/3 BOUNDARY IS REFUSED — the strictness repair, at the smallest scale there is.**
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
    let cells = trace_cells(&u);
    let pis = pis_from(&cells, &u);
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
    set_col(&mut forged, QDIFF_0 + RUNGS, 0);
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
    must_prove("agave's STRICT >2/3 boundary (rooted 3 of total 3)", &u);
}

// ═══════════════════════════════════════════════════════════════════════════════════════════
// ⚑ TOOTH 1 — the sub-quorum, one lamport out of 4.3e17
// ═══════════════════════════════════════════════════════════════════════════════════════════

/// ⚑⚑ **ONE LAMPORT BELOW THE MINIMAL STRICT QUORUM IS REFUSED, AT LIVE SCALE — and that value is
/// the EXACT-2/3 POINT, which PROVED before the strictness repair.**
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
        !(3 * (u.rooted_stk as i128) > 2 * u.total_stk() as i128),
        "the exact-2/3 point must not finalize under agave's STRICT rule"
    );
    assert!(
        3 * (u.rooted_stk as i128) >= 2 * u.total_stk() as i128,
        "…and it DID under the non-strict rule this descriptor shipped"
    );

    let q = fill_chain(
        3,
        limbs4(u.rooted_stk),
        2,
        limbs4(u.total_stk()),
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
    let cells = trace_cells(&u);
    let pis = pis_from(&cells, &u);
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
    set_col(&mut forged, QDIFF_0 + RUNGS, 0);
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
/// differing in exactly one integer: the tally-limb table's declared width, moved from 16 to 32.
#[test]
fn the_sub_quorum_is_admitted_when_the_limb_table_is_vacuous() {
    // (the vacuity of VACUOUS_BITS is pinned at the top of this file by a `const _` assert)
    let u = honest(LIVE_ACTIVE_STAKE, MIN_QUORUM - 1);
    must_prove_under(
        "⚑ the SAME sub-quorum at a VACUOUS tally-limb width",
        &desc_with_limb_range_width(VACUOUS_BITS),
        &u,
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
/// ⚑ Now the empty table is genuinely EMPTY: every row is the canonical ZERO ENTRY, so the fold's
/// accumulator reaches 0 by adding up nothing rather than by a prover writing four zeros.
#[test]
fn the_empty_stake_table_is_refused_by_both_teeth() {
    let u = honest_table(vec![], 0);
    assert_eq!(u.total_stk(), 0);
    let cells = trace_cells(&u);
    let d = desc();
    let pis = pis_from(&cells, &u);

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

    // ⚑ …and the SHIPPED non-strict quorum admitted exactly this row.
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
    set_col(&mut q_forged, QDIFF_0 + RUNGS, 0);
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
    set_col(&mut both_forged, TPOS_0 + RUNGS, 0);
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
#[test]
fn with_the_emptiness_floor_disarmed_the_strict_quorum_still_refuses_the_empty_table() {
    let u = honest_table(vec![], 0);
    let d = desc();
    let cells = trace_cells(&u);
    let pis = pis_from(&cells, &u);

    let mut floor_disarmed = cells.clone();
    set_col(&mut floor_disarmed, TPOS_0 + RUNGS, 0);

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

/// ⚑ **AND THE CONTROL, ON THE FLOOR.** The empty stake table at a VACUOUS 32-bit limb width PROVES.
/// A block signed by nobody, accepted by the deployed prover, at the width this descriptor shipped.
#[test]
fn the_empty_stake_table_is_admitted_when_the_limb_table_is_vacuous() {
    must_prove_under(
        "⚑ the EMPTY stake table at a VACUOUS tally-limb width",
        &desc_with_limb_range_width(VACUOUS_BITS),
        &honest_table(vec![], 0),
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
#[test]
fn a_forged_difference_limb_is_refused_on_both_chains() {
    let u = honest(LIVE_ACTIVE_STAKE, MIN_QUORUM);
    let honest_cells = trace_cells(&u);
    let pis = pis_from(&honest_cells, &u);
    let d = desc();
    must_prove("the honest live-scale pole", &u);

    for (chain, base) in [
        ("QDIFF (quorum)", QDIFF_0),
        ("TPOS (empty-set floor)", TPOS_0),
    ] {
        for i in 0..=RUNGS {
            let mut forged = honest_cells.clone();
            bump_col(&mut forged, base + i, 1);
            assert!(
                forged.last().unwrap()[base + i] < (1 << SOL_LIMB_BITS),
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
/// ⚠ Worth saying what this does NOT show. `LimbTally.chain_recomposes` holds for **any** integer
/// carries whatsoever. The carry range lookups exist ONLY for the mod-`p` ↔ ℤ bridge. So this tooth
/// measures that the CHAIN pins the carries to the operands — not that the carry range check is
/// load-bearing for soundness. It is not.
#[test]
fn a_forged_carry_is_refused_on_both_chains() {
    let u = honest(LIVE_ACTIVE_STAKE, MIN_QUORUM);
    let honest_cells = trace_cells(&u);
    let pis = pis_from(&honest_cells, &u);
    let d = desc();

    for (chain, base) in [
        ("QDIFF (quorum)", QDIFF_CARRY_0),
        ("TPOS (empty-set floor)", TPOS_CARRY_0),
    ] {
        for i in 0..RUNGS {
            let mut forged = honest_cells.clone();
            bump_col(&mut forged, base + i, 1);
            assert!(
                forged.last().unwrap()[base + i] < (1 << SOL_CARRY_BITS),
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

/// ⚑⚑ **A RE-SPELT DENOMINATOR IS REFUSED — and there is now a THIRD gate standing there.**
///
/// The denominator columns ARE the fold's accumulator, so a forger who shrinks one to manufacture a
/// quorum breaks (a) the quorum chain, (b) the emptiness floor — which reads the same four columns —
/// and (c) the fold's own `accStep` identity, which says those columns are the running sum of the
/// exhibited stake limbs. There is no second, unchecked copy of the total to disagree with, and now
/// there is no unchecked FIRST copy either.
///
/// ⚠ The forgery is applied to the LAST ROW ONLY, and that is deliberate: the accumulator is a
/// per-row running total, so shrinking the whole column takes row 0's zero to `p − 1` and the RANGE
/// tooth fires first — a refusal, but not the one this test is about. Moving only the published row
/// keeps every wire in range and leaves the algebra as the only thing standing.
#[test]
fn a_re_spelt_denominator_is_refused() {
    let u = honest(LIVE_ACTIVE_STAKE, MIN_QUORUM);
    let honest_cells = trace_cells(&u);
    let pis = pis_from(&honest_cells, &u);
    let d = desc();
    let last = honest_cells.len() - 1;
    for i in 0..RUNGS {
        let mut forged = honest_cells.clone();
        forged[last][TOTAL_STK_0 + i] -= 1;
        assert!(
            forged[last][TOTAL_STK_0 + i] >= 0
                && forged[last][TOTAL_STK_0 + i] < (1 << SOL_LIMB_BITS),
            "the shrunk limb must stay INSIDE the declared 16-bit interval, so the range tooth is \
             not what catches it"
        );
        let reason = must_refuse_violated_gate(
            &format!("⚑ a shrunk denominator limb {i} (col {})", TOTAL_STK_0 + i),
            &d,
            &forged,
            &pis,
        );
        eprintln!("⚑ shrunk denominator limb {i}: {reason}");
    }
}

// ═══════════════════════════════════════════════════════════════════════════════════════════
// ⚑⚑ THE SWAPPED STAKE TABLE — the forgery this pass exists to refuse
// ═══════════════════════════════════════════════════════════════════════════════════════════

/// A stake universe the FORGER prefers: 1% of mainnet-beta's real active stake. A cartel holding
/// 4.3M SOL cannot clear 2/3 of 432.6M — but it clears 2/3 of a table it gets to pick.
const FORGED_TOTAL: u64 = LIVE_ACTIVE_STAKE / 100;

/// The minimal STRICT quorum of the forged universe (`3·R > 2·T`).
const FORGED_QUORUM: u64 = (2 * FORGED_TOTAL) / 3 + 1;

/// ⚑⚑ **WHAT MAKES THE FORGERY A FORGERY — AT BUILD TIME.** Two facts, and if either failed the
/// test below would be measuring something else entirely: the shrunk universe must CLEAR agave's
/// strict 2/3 on its own terms (otherwise the prover refuses it for the ordinary reason and the
/// tooth proves nothing about the anchor), and it must NOT clear 2/3 of the real active stake
/// (otherwise it is a legitimate quorum, not a forgery). Both are integer arithmetic over
/// constants — including a floor division whose off-by-one is exactly the kind of thing that
/// silently makes `FORGED_QUORUM` one short — so the obligation is discharged against the BUILD.
const THE_SHRUNK_UNIVERSE_IS_A_FORGERY: () = {
    assert!(
        2 * FORGED_TOTAL < 3 * FORGED_QUORUM,
        "the forged tally must clear agave's STRICT 2/3 in its own universe"
    );
    assert!(
        3 * FORGED_QUORUM < 2 * LIVE_ACTIVE_STAKE,
        "…and must NOT clear 2/3 of the REAL active stake — otherwise it is not a forgery"
    );
};
const _: () = THE_SHRUNK_UNIVERSE_IS_A_FORGERY;

/// ⚑⚑ **THE SHRUNK STAKE UNIVERSE PROVES ON ITS OWN TERMS — and that is the whole attack.**
#[test]
fn a_swapped_stake_table_is_arithmetically_perfect() {
    let forged = honest(FORGED_TOTAL, FORGED_QUORUM);
    // (both premises are const-asserted at `FORGED_QUORUM`'s definition — a build obligation)
    let cells = trace_cells(&forged);
    prove_and_verify(&desc(), &cells, &pis_from(&cells, &forged))
        .expect("the shrunk stake universe satisfies every arithmetic gate in the descriptor");
    eprintln!(
        "⚑ shrunk stake universe PROVES on its own terms: total {FORGED_TOTAL} (1% of \
         {LIVE_ACTIVE_STAKE}), rooted {FORGED_QUORUM}"
    );
}

/// ⚑⚑ **AND IT IS REFUSED AGAINST THE LIGHT CLIENT'S ANCHOR.**
#[test]
fn a_swapped_stake_table_is_refused_against_the_pinned_denominator() {
    let forged = honest(FORGED_TOTAL, FORGED_QUORUM);
    let honest_client = honest(LIVE_ACTIVE_STAKE, MIN_QUORUM);
    let client_cells = trace_cells(&honest_client);
    let pis = pis_from(&client_cells, &honest_client);
    let forged_cells = trace_cells(&forged);

    // The forger claims the SAME block: only the stake universe differs.
    assert_eq!(
        pis[PI_BANK_ROOT_0..=PI_SLOT],
        pis_from(&forged_cells, &forged)[PI_BANK_ROOT_0..=PI_SLOT],
        "bank root and slot must be identical — the swap is of the TABLE, not the block"
    );
    let reason = must_refuse_violated_gate(
        "⚑ a shrunk stake universe against the light client's pinned anchor",
        &desc(),
        &forged_cells,
        &pis,
    );
    eprintln!("⚑ SHRUNK STAKE UNIVERSE REFUSED: {reason}");
}

/// The honest table: A holds 60% of the live stake, B holds 40%.
fn honest_pair() -> Vec<Entry> {
    vec![
        Entry {
            voter: PK_A,
            stake: 259_590_110_355_375_352,
        },
        Entry {
            voter: PK_B,
            stake: 173_060_073_570_250_235,
        },
    ]
}

/// ⚑ THE FORGERY: the SAME two validators, the SAME total, the shares SWAPPED. B — a minority
/// holder under the honest table — now claims the majority share.
fn same_tally_swap() -> Vec<Entry> {
    vec![
        Entry {
            voter: PK_A,
            stake: 173_060_073_570_250_235,
        },
        Entry {
            voter: PK_B,
            stake: 259_590_110_355_375_352,
        },
    ]
}

/// ⚑⚑ **THE CONTROL. THE SAME-TALLY SWAP IS ARITHMETICALLY PERFECT.**
///
/// The forged table proves against its OWN root: every range lookup, every boolean carry, every
/// accumulator gate, both chip absorbs and the whole quorum chain are satisfied. Its published
/// denominator is **bit-identical** to the honest one — the four felts are the same four felts. The
/// forgery is not caught by arithmetic, which is what makes the next test mean something.
///
/// ⚠ This is the exact row the previous pass named as OUTSIDE its scope: *"a swap to a different
/// validator set with the SAME total active stake is NOT refused by this."*
#[test]
fn a_same_tally_swap_is_arithmetically_perfect() {
    let honest_u = honest_table(honest_pair(), MIN_QUORUM);
    let forged_u = honest_table(same_tally_swap(), MIN_QUORUM);
    assert_eq!(
        honest_u.total_stk(),
        LIVE_ACTIVE_STAKE,
        "the pair must sum to the live active stake"
    );
    assert_eq!(
        honest_u.total_stk(),
        forged_u.total_stk(),
        "the swap must preserve the denominator — otherwise the denominator pin already refuses it \
         and this rung proves nothing new"
    );

    let hc = trace_cells(&honest_u);
    let fc = trace_cells(&forged_u);
    let hp = pis_from(&hc, &honest_u);
    let fp = pis_from(&fc, &forged_u);

    // ⚑ THE PUBLISHED DENOMINATOR IS BIT-IDENTICAL…
    assert_eq!(
        hp[PI_TOTAL_STK_0..PI_TOTAL_STK_0 + RUNGS],
        fp[PI_TOTAL_STK_0..PI_TOTAL_STK_0 + RUNGS],
        "the four denominator felts must be the same four felts"
    );
    // …and the eight-lane commitment is NOT.
    assert_ne!(
        anchor_root_of(&hc),
        anchor_root_of(&fc),
        "the eight-lane Poseidon2 commitment must move; if it did not, the fold would be blind to \
         exactly the forgery it exists to catch"
    );

    prove_and_verify(&desc(), &fc, &fp)
        .expect("the same-tally swap satisfies every arithmetic gate in the descriptor");
    eprintln!(
        "⚑ SAME-TALLY SWAP PROVES on its own root: denominator {:?} identical, anchor root {:?} \
         vs {:?}",
        &hp[PI_TOTAL_STK_0..PI_TOTAL_STK_0 + RUNGS],
        anchor_root_of(&hc),
        anchor_root_of(&fc)
    );
}

/// ⚑⚑⚑ **THE DELIVERABLE. A SWAPPED VALIDATOR SET WITH A BIT-IDENTICAL PUBLISHED DENOMINATOR IS
/// REFUSED.**
///
/// The light client supplies its governance-pinned anchor root in `PI[0..7]` and the denominator it
/// believes in `PI[18..21]`. The forger's table clears the denominator — the four felts are
/// bit-identical, asserted above — and the LAST-row root pins do not vanish.
///
/// ⚠ **PROVED BEFORE, REFUSED AFTER**, and the "before" is the test directly above: nothing about
/// the tally arithmetic changed. What changed is that the light client's trust anchor became the
/// IMAGE of the rows instead of nine columns nothing reads.
#[test]
fn a_same_tally_swap_is_refused_against_the_pinned_anchor_root() {
    let honest_u = honest_table(honest_pair(), MIN_QUORUM);
    let forged_u = honest_table(same_tally_swap(), MIN_QUORUM);
    let hc = trace_cells(&honest_u);
    let fc = trace_cells(&forged_u);
    let pinned = pis_from(&hc, &honest_u);

    assert_ne!(
        hc, fc,
        "the two traces must differ, or there is nothing to refuse"
    );
    assert_eq!(
        pinned[PI_TOTAL_STK_0..PI_TOTAL_STK_0 + RUNGS],
        pis_from(&fc, &forged_u)[PI_TOTAL_STK_0..PI_TOTAL_STK_0 + RUNGS],
        "the published denominator is the same object in both proofs"
    );

    let reason = must_refuse_violated_gate(
        "⚑⚑ same-tally swap vs the light client's pinned anchor root",
        &desc(),
        &fc,
        &pinned,
    );
    eprintln!("⚑⚑ SAME-TALLY SWAP REFUSED AGAINST THE PINNED ANCHOR ROOT: {reason}");
}

/// A REORDERING: the same two members, the same lamports each, listed the other way round. Same
/// multiset, same tally — and the fold is order-sensitive by construction, so the root moves.
#[test]
fn a_reordered_stake_table_is_refused() {
    let honest_u = honest_table(honest_pair(), MIN_QUORUM);
    let mut reordered = honest_pair();
    reordered.reverse();
    let reordered_u = honest_table(reordered, MIN_QUORUM);
    assert_eq!(reordered_u.total_stk(), honest_u.total_stk());

    let pinned = pis_of(&honest_u);
    let reason = must_refuse_violated_gate(
        "⚑ a reordered stake table vs the pinned anchor root",
        &desc(),
        &trace_cells(&reordered_u),
        &pinned,
    );
    eprintln!("⚑ REORDERED STAKE TABLE REFUSED: {reason}");
}

/// ⚑ AN EXTRA MEMBER AT ZERO STAKE. The tally is untouched — the padding rows it displaces are
/// themselves zero entries — and the root still moves, because the message FRAME moved. This is the
/// case a tally-only pin is structurally blind to.
#[test]
fn an_extra_zero_stake_validator_is_refused() {
    let honest_u = honest_table(honest_pair(), MIN_QUORUM);
    let mut padded = honest_pair();
    padded.push(Entry {
        voter: PK_C,
        stake: 0,
    });
    let padded_u = honest_table(padded, MIN_QUORUM);
    assert_eq!(
        padded_u.total_stk(),
        honest_u.total_stk(),
        "a zero-stake member preserves the tally"
    );

    let reason = must_refuse_violated_gate(
        "⚑ an extra zero-stake validator vs the pinned anchor root",
        &desc(),
        &trace_cells(&padded_u),
        &pis_of(&honest_u),
    );
    eprintln!("⚑ EXTRA ZERO-STAKE VALIDATOR REFUSED: {reason}");
}

// ═══════════════════════════════════════════════════════════════════════════════════════════
// The anchor, carrier and addressing teeth
// ═══════════════════════════════════════════════════════════════════════════════════════════

/// ⚑ **AN ANCHOR-ROOT LANE THAT DISAGREES WITH ITS PUBLIC INPUT IS REFUSED — all eight.** The light
/// client's pinned lane is moved, one at a time, so a partial binding (seven of eight pinned) cannot
/// pass unnoticed.
#[test]
fn an_anchor_root_lane_that_disagrees_with_its_public_input_is_refused() {
    let u = honest(LIVE_ACTIVE_STAKE, MIN_QUORUM);
    let cells = trace_cells(&u);
    let d = desc();
    for j in 0..ANCHOR_LANES {
        let mut pis = pis_from(&cells, &u);
        pis[PI_ANCHOR_ROOT_0 + j] += BabyBear::new(1);
        let reason = must_refuse_violated_gate(
            &format!("a pinned WS anchor-root lane {j} disagreeing with the derived root"),
            &d,
            &cells,
            &pis,
        );
        eprintln!("⚑ forged anchor-root PI lane {j}: {reason}");
    }
}

/// ⚑⚑ **MEASURED, NOT ASSUMED: CHIP OUTPUT LANES 1..7 ARE WELD-OWNED, SO ONLY `out0` IS
/// PRODUCER-FORGEABLE.**
///
/// `descriptor_ir2::fill_chip_lanes` requires a chip lookup's lane slots (tuple indices
/// `CHIP_RATE + 2 + j`, i.e. output lanes 1..7) to be bare `Var` columns and **writes the genuine
/// permutation lanes into them** before proving. `out0` (tuple index `CHIP_RATE + 1`) is explicitly
/// NOT in that set — *"the producer's hash chain owns it"*.
///
/// So a tamper on lanes 1..7 is OVERWRITTEN and the resulting proof is a proof about the CORRECTED
/// trace, which is why this test asserts ACCEPTANCE there; and a tamper on `out0` is REFUSED. Both
/// poles, so the acceptance reads as "this column is not the producer's" and not as "the chip is
/// blind".
///
/// ⚠ The consequence that matters here: `ROOT_OUT` lanes 1..7 are weld-owned, so the LAST-row PI
/// pins on them compare the GENUINE lanes against the light client's anchor. That is what makes
/// `a_same_tally_swap_is_refused_against_the_pinned_anchor_root` a refusal of the FOLD and not of a
/// number the prover happened to write.
#[test]
fn chip_output_lanes_1_to_7_are_weld_owned_not_producer_owned() {
    let u = honest(LIVE_ACTIVE_STAKE, MIN_QUORUM);
    let honest_cells = trace_cells(&u);
    let pis = pis_from(&honest_cells, &u);
    let d = desc();

    let mut tampered = honest_cells.clone();
    tampered[0][MID_0 + 3] += 1;
    assert_ne!(
        tampered[0][MID_0 + 3],
        honest_cells[0][MID_0 + 3],
        "the tamper must actually change the submitted cell"
    );
    refusal::must_accept("tampered chip lane 3 (weld-owned)", || {
        prove_and_verify(&d, &tampered, &pis)
    });

    let mut out0_tampered = honest_cells.clone();
    out0_tampered[0][MID_0] += 1;
    refusal::must_refuse_or_unsat_panic("tampered chip out0 (producer-owned)", || {
        prove_and_verify(&d, &out0_tampered, &pis)
    });
    eprintln!(
        "⚑ chip lane 3 tamper ACCEPTED (weld rewrote it); out0 tamper REFUSED — only out0 is \
         producer-forgeable"
    );
}

/// ⚑⚑⚑ **THE ANCHOR'S OWN `out0`, FORGED, WITH THE PUBLIC INPUT MOVED TO MATCH — AND STILL
/// REFUSED.**
///
/// Every other anchor tooth in this file moves a PI away from the trace and is caught by a
/// **pin**. That is a check on the light client's side of the seam, and it says nothing about
/// whether the root the prover published is the IMAGE of the rows or a number it chose. This one
/// removes the pin from the argument entirely: the forger writes its own value into the last row's
/// `ROOT_OUT` lane 0 and **publishes that value**, so `PI[0]` and the trace agree and every
/// `pi_binding` is satisfied.
///
/// The last row is the one row where this is even worth attempting. `rootContinuity` is a
/// `.transition` window gate, so it does not fire there — the forged lane feeds no successor and
/// disturbs no continuity. And lane 0 is the one output lane `descriptor_ir2::fill_chip_lanes` does
/// NOT rewrite (*"the producer's hash chain owns it"*), so unlike lanes 1..7 the forgery actually
/// reaches the prover. What is left holding the anchor down is **the chip lookup and nothing else**.
///
/// ⚠ This refusal is expected on the LOOKUP BUS, not as a violated gate, so it is asserted with the
/// weaker `must_refuse_or_unsat_panic` and the reason is printed rather than pattern-matched. Naming
/// the tooth honestly is the point: `2^123.63` (birthday over `8 · 30.906891 = 247.26` bits) is the
/// number that governs a forged root, and it is a property of the chip's image, not of a pin.
#[test]
fn a_forged_anchor_out0_with_a_matching_public_input_is_refused() {
    let u = honest(LIVE_ACTIVE_STAKE, MIN_QUORUM);
    let honest_cells = trace_cells(&u);
    let d = desc();

    // The honest pole, so the refusal below is not vacuous.
    refusal::must_accept("the honest fill, before the anchor out0 forgery", || {
        prove_and_verify(&d, &honest_cells, &pis_from(&honest_cells, &u))
    });

    let mut forged = honest_cells.clone();
    let last = forged.len() - 1;
    forged[last][ROOT_OUT_0] += 1;

    // ⚑ The forger PUBLISHES the root it wrote — `pis_from` reads the last row, so the pin agrees.
    let self_consistent = pis_from(&forged, &u);
    assert_eq!(
        self_consistent[PI_ANCHOR_ROOT_0],
        felt(forged[last][ROOT_OUT_0]),
        "the published anchor must be the forged value, or the PIN is doing the work and this test \
         is the one above"
    );
    assert_ne!(
        self_consistent[PI_ANCHOR_ROOT_0],
        pis_from(&honest_cells, &u)[PI_ANCHOR_ROOT_0],
        "the forged anchor must differ from the honest one"
    );
    // …and the denominator is untouched, so nothing else moved.
    assert_eq!(
        self_consistent[PI_TOTAL_STK_0..PI_TOTAL_STK_0 + RUNGS],
        pis_from(&honest_cells, &u)[PI_TOTAL_STK_0..PI_TOTAL_STK_0 + RUNGS],
        "the forgery is of the ROOT alone"
    );

    let r = refusal::must_refuse_or_unsat_panic(
        "⚑⚑ a forged anchor-root out0 published as its own public input",
        || prove_and_verify(&d, &forged, &self_consistent),
    );
    eprintln!(
        "⚑⚑ FORGED ANCHOR out0 REFUSED WITH ITS PIN SATISFIED: {}",
        r.reason()
    );
}

/// ⚑ **A DENOMINATOR LIMB THAT DISAGREES WITH ITS PUBLIC INPUT IS REFUSED** — the pin itself, one
/// limb at a time, so a partial binding (three of four pinned) cannot pass unnoticed.
#[test]
fn a_total_stake_limb_that_disagrees_with_its_public_input_is_refused() {
    let u = honest(LIVE_ACTIVE_STAKE, MIN_QUORUM);
    let cells = trace_cells(&u);
    let d = desc();
    for i in 0..RUNGS {
        let mut pis = pis_from(&cells, &u);
        pis[PI_TOTAL_STK_0 + i] += BabyBear::new(1);
        let reason = must_refuse_violated_gate(
            &format!("a published total-stake limb {i} disagreeing with the trace"),
            &d,
            &cells,
            &pis,
        );
        eprintln!("⚑ forged denominator PI {i}: {reason}");
    }
}

/// A forged CARRIER or logic bit — the ed25519 batch-verify result, the rooted flag, or the
/// authorized-voter binding, cleared to `0` — is refused by its own gate.
///
/// ⚑ There were FOUR. `STAKE_TABLE_OK` is gone: the fold computes what it asserted.
///
/// ⚠ `ED_OK` is a witnessed bit, not in-AIR ed25519. What the AIR enforces is that a prover claiming
/// acceptance must ASSERT it; the crypto soundness behind it is consumed one layer up, inside
/// `sol_no_forgery`.
#[test]
fn a_cleared_carrier_or_logic_bit_is_refused() {
    for (name, col) in [
        ("ED_OK (aggregate ed25519 verify)", ED_OK),
        ("ROOTED_OK (tower root reaches the slot)", ROOTED_OK),
        ("AUTH_OK (authorized-voter binding)", AUTH_OK),
    ] {
        let u = honest(LIVE_ACTIVE_STAKE, MIN_QUORUM);
        let honest_cells = trace_cells(&u);
        let pis = pis_from(&honest_cells, &u);
        let mut cells = honest_cells.clone();
        assert_eq!(cells.last().unwrap()[col], 1, "the honest carrier is set");
        set_col(&mut cells, col, 0);
        let reason =
            must_refuse_violated_gate(&format!("a cleared carrier {name}"), &desc(), &cells, &pis);
        eprintln!("cleared carrier {name}: {reason}");
    }
}

/// A forged PUBLIC ANCHOR: a bank-root limb on the wire disagreeing with the published PI. The nine
/// `.piBinding` pins are the addressing layer — they say WHICH full 256-bit bank hash the proof is
/// about — and a proof whose trace disagrees with its own public statement must not verify.
#[test]
fn a_bank_root_limb_that_disagrees_with_its_public_input_is_refused() {
    let u = honest(LIVE_ACTIVE_STAKE, MIN_QUORUM);
    let honest_cells = trace_cells(&u);
    let pis = pis_from(&honest_cells, &u);
    let d = desc();
    for i in 0..BANK_ROOT_LIMBS {
        let mut cells = honest_cells.clone();
        bump_col(&mut cells, BANK_ROOT_0 + i, 1);
        let reason = must_refuse_violated_gate(
            &format!("a bank-root limb {i} disagreeing with its PI pin"),
            &d,
            &cells,
            &pis,
        );
        eprintln!("forged bank-root limb {i}: {reason}");
    }
}

/// A replayed proof pointed at a DIFFERENT slot is refused: the slot rides `PI[17]` and the trace
/// column must agree with it.
#[test]
fn a_slot_that_disagrees_with_its_public_input_is_refused() {
    let u = honest(LIVE_ACTIVE_STAKE, MIN_QUORUM);
    let honest_cells = trace_cells(&u);
    let pis = pis_from(&honest_cells, &u);
    let mut cells = honest_cells.clone();
    bump_col(&mut cells, SLOT_COL, 1);
    let reason = must_refuse_violated_gate(
        "a rooted slot disagreeing with its PI pin",
        &desc(),
        &cells,
        &pis,
    );
    eprintln!("forged slot: {reason}");
}

/// ⚑ **A NON-BOOLEAN ACCUMULATOR CARRY IS REFUSED.** The `.all`-scoped boolean pin fires on EVERY
/// row including the last, which is exactly where an unbooleanised carry would hide the published
/// total.
#[test]
fn a_non_boolean_accumulator_carry_is_refused() {
    let u = honest(LIVE_ACTIVE_STAKE, MIN_QUORUM);
    let honest_cells = trace_cells(&u);
    let pis = pis_from(&honest_cells, &u);
    let mut cells = honest_cells.clone();
    let last = cells.len() - 1;
    cells[last][CARRY_0] = 2;
    let reason = must_refuse_violated_gate(
        "a non-boolean accumulator carry on the LAST row",
        &desc(),
        &cells,
        &pis,
    );
    eprintln!("⚑ non-boolean accumulator carry: {reason}");
}

// ═══════════════════════════════════════════════════════════════════════════════════════════
// ⚑ THE SECOND DEFECT — CLOSED 2026-08-03: the over-wide width is REFUSED AT DESCRIPTOR LOAD
// ═══════════════════════════════════════════════════════════════════════════════════════════

/// The served descriptor's own JSON bytes, so a width substitution below is done to the REAL wire
/// object rather than to a hand-typed stand-in.
const SOLANA_LC_JSON: &str =
    include_str!("../descriptors/by-name/dregg-solana-lightclient-verify-v1.json");

/// ⚑⚑ **THE WIDTH THAT SHIPPED IS NOW REFUSED AT THE DOOR.**
///
///  1. **The declaration is REFUSED AT LOAD.** `parse_vm_descriptor2` rejects a range table at or
///     above `VACUOUS_RANGE_BITS = 31`, naming the reason.
///  2. **The mask is gone.** The filler's bound is now total (`value_fits_bits`), so a descriptor
///     constructed IN MEMORY at a vacuous width behaves the way its denotation says: it admits
///     everything, including the honest row.
#[test]
fn the_shipped_128_bit_width_refuses_even_an_honest_update() {
    // ── 1. LOAD REFUSES the width, on the real served bytes with one integer moved.
    let served = SOLANA_LC_JSON;
    assert!(
        parse_vm_descriptor2(served).is_ok(),
        "the SERVED descriptor must still load — its declared widths are 29, 24, 16 and 8"
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
    let u = honest(LIVE_ACTIVE_STAKE, MIN_QUORUM);
    must_prove("the honest live-scale u at the declared limb widths", &u);
    must_prove_under(
        "⚑ the SAME honest u at an in-memory bits=128 — vacuous, therefore ADMITTED",
        &desc_with_limb_range_width(SHIPPED_SOL_BITS),
        &u,
    );
    eprintln!(
        "⚑ dregg-solana-lightclient-verify::v1: the honest u now PROVES at an in-memory bits=128 \
         (vacuous, admits everything) instead of being refused by a masked comparison — and \
         bits=128 can no longer be LOADED at all"
    );
}
