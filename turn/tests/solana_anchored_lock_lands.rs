//! ⚑⚑⚑ **THE SOLANA MINT PATH SPENDS A STARK — both polarities, through the deployed verifier.**
//!
//! `dregg_turn::executor::solana_head_verifier` is the consumer that makes
//! `dregg-solana-lightclient-verify::v1` gate something. Until it existed, the descriptor was
//! proven only from `circuit/tests/` and the value-bearing decision was
//! `bridge/src/solana_provenance.rs:697` — one Rust line,
//! `voted.saturating_mul(3) >= total.saturating_mul(2) && total > 0`.
//!
//! This file drives the real producer (the trace shape
//! `circuit/tests/solana_lightclient_proves.rs` exhibits), the real prover, and the real
//! `WitnessedPredicateVerifier`. Every refusal below is the deployed verifier's, not a helper's.
//!
//! ⚠ **PROFILE — RUN IN RELEASE.** plonky3's ALGEBRAIC refusals are `#[cfg(debug_assertions)]`
//! panics under `cargo test` and clean `Err(OodEvaluationMismatch)` under `--release`. The STARK
//! polarity pair is `#[cfg(not(debug_assertions))]` for exactly that reason; the weld/pin/absence
//! refusals are profile-independent and always run.
//!
//!     cargo nextest run --release -p dregg-turn --test solana_anchored_lock_lands

use dregg_cell::predicate::{PredicateInput, WitnessedPredicateError, WitnessedPredicateVerifier};
use dregg_circuit::BabyBear;
use dregg_circuit::descriptor_by_name::descriptor_by_name;
use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, MemBoundaryWitness, chip_absorb_all_lanes, prove_vm_descriptor2,
};
use dregg_circuit::heap_root::HeapLeaf;
use dregg_turn::executor::solana_head_verifier::{
    SOL_LC_VERIFY_DESCRIPTOR, SolanaAnchoredLockStarkVerifier, SolanaGovernanceAnchor,
    SolanaLockProofWire, key_lanes_u32, solana_lock_commitment,
};

// ════════════════════════════════════════════════════════════════════════════════════════════
// The trace shape — transcribed from `circuit/tests/solana_lightclient_proves.rs`, which is the
// file that owns it. Column literals are `LightClientSolanaAir`'s.
// ════════════════════════════════════════════════════════════════════════════════════════════

const ROOT_IN_0: usize = 0;
const VOTER_0: usize = 8;
const STAKE_0: usize = 17;
const MID_0: usize = 21;
const ROOT_OUT_0: usize = 29;
const ACC_0: usize = 37;
const CARRY_0: usize = 41;
const ED_OK: usize = 44;
const ROOTED_OK: usize = 45;
const AUTH_OK: usize = 46;
const ROOTED_STK_0: usize = 47;
const QDIFF_0: usize = 51;
const QDIFF_CARRY_0: usize = 56;
const TPOS_0: usize = 60;
const TPOS_CARRY_0: usize = 65;
const BANK_ROOT_0: usize = 69;
const BANK_ROOT_LIMBS: usize = 9;
const SLOT_COL: usize = 78;
const SOL_LC_WIDTH: usize = 79;
const SOL_PI_COUNT: usize = 22;

const ANCHOR_LANES: usize = 8;
const PI_ANCHOR_ROOT_0: usize = 0;
const PI_BANK_ROOT_0: usize = 8;
const PI_SLOT: usize = 17;
const PI_TOTAL_STK_0: usize = 18;

const SOL_LIMB_BITS: usize = 16;
const CARRY_OFF: i64 = 128;
const RUNGS: usize = 4;
const TRACE_ROWS: usize = 8;
const P: i64 = 2_013_265_921;
const FOLD_TAG: u32 = 0x5353_5446;

/// `LightClientSolanaAir` ships the STRICT quorum: `3·rooted > 2·total`.
const QUORUM_GAMMA: i64 = 1;
const FLOOR_GAMMA: i64 = 1;

/// Mainnet-beta's ACTIVE stake, measured live 2026-08-03 (the same figure the circuit suite pins).
const LIVE_ACTIVE_STAKE: u64 = 432_650_183_925_625_587;
/// ⚑ `3 · this == 2 · LIVE_ACTIVE_STAKE`, exactly. The Rust gate ADMITS this point (`>=`); the AIR
/// REFUSES it. This is the divergence the whole lane is about.
const EXACT_TWO_THIRDS: u64 = 288_433_455_950_417_058;
/// One lamport above it — the smallest quorum the AIR admits.
const MIN_QUORUM: u64 = 288_433_455_950_417_059;
const LIVE_SLOT: u32 = 436_909_708;

fn felt(v: i64) -> BabyBear {
    BabyBear::new(v.rem_euclid(P) as u32)
}
fn f(v: u32) -> BabyBear {
    BabyBear::new(v)
}

fn desc() -> EffectVmDescriptor2 {
    descriptor_by_name(SOL_LC_VERIFY_DESCRIPTOR)
        .unwrap_or_else(|| panic!("{SOL_LC_VERIFY_DESCRIPTOR} must dispatch"))
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
struct Entry {
    voter: [u32; 9],
    stake: u64,
}
const ZERO_ENTRY: Entry = Entry {
    voter: [0; 9],
    stake: 0,
};
const PK_A: [u32; 9] = [11, 22, 33, 44, 55, 66, 77, 88, 99];

struct ChainFill {
    diff: [i64; RUNGS + 1],
    carry: [i64; RUNGS],
}

fn limbs4(v: u64) -> [i64; RUNGS] {
    std::array::from_fn(|i| ((v >> (SOL_LIMB_BITS * i)) & 0xFFFF) as i64)
}
fn limbs4_u32(v: u64) -> [u32; RUNGS] {
    std::array::from_fn(|i| ((v >> (SOL_LIMB_BITS * i)) & 0xFFFF) as u32)
}

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
    diff[RUNGS] = c;
    ChainFill { diff, carry }
}

#[derive(Clone)]
struct Update {
    entries: Vec<Entry>,
    rooted_stk: u64,
    bank_root: [u32; BANK_ROOT_LIMBS],
    slot: u32,
}

impl Update {
    fn total_stk(&self) -> u64 {
        self.entries.iter().map(|e| e.stake).sum()
    }
}

/// An honest update at a chosen total, with the bank-root limbs set to the `Faithful9` lanes of a
/// real 32-byte bank hash — the encoding the CONSUMER requires (`check_public_input_weld`).
fn honest(total_stk: u64, rooted_stk: u64, bank_hash: &[u8; 32]) -> Update {
    let mut entries = vec![ZERO_ENTRY; TRACE_ROWS - 1];
    entries.push(Entry {
        voter: PK_A,
        stake: total_stk,
    });
    Update {
        entries,
        rooted_stk,
        bank_root: key_lanes_u32(bank_hash),
        slot: LIVE_SLOT,
    }
}

fn trace_cells(u: &Update) -> Vec<Vec<i64>> {
    let total = u.total_stk();
    let total_l = limbs4(total);
    let rooted_l = limbs4(u.rooted_stk);
    let q = fill_chain(3, rooted_l, 2, total_l, QUORUM_GAMMA);
    let t = fill_chain(1, total_l, 0, total_l, FLOOR_GAMMA);

    let mut st = [BabyBear::new(0); 8];
    st[0] = f(FOLD_TAG);
    let mut acc = [0u32; RUNGS];
    let mut rows: Vec<Vec<i64>> = Vec::with_capacity(TRACE_ROWS);

    for r in 0..TRACE_ROWS {
        let e = u.entries.get(r).copied().unwrap_or(ZERO_ENTRY);
        let stk = limbs4_u32(e.stake);

        let mut ins_a = [BabyBear::new(0); 16];
        ins_a[..8].copy_from_slice(&st);
        for j in 0..8 {
            ins_a[8 + j] = f(e.voter[j]);
        }
        let mid = chip_absorb_all_lanes(16, &ins_a);

        let mut ins_b = [BabyBear::new(0); 16];
        ins_b[..8].copy_from_slice(&mid);
        ins_b[8] = f(e.voter[8]);
        for i in 0..RUNGS {
            ins_b[9 + i] = f(stk[i]);
        }
        let root_out = chip_absorb_all_lanes(16, &ins_b);

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
        assert_eq!(carry, 0, "the running total overflowed a u64");

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
        row[ED_OK] = 1;
        row[ROOTED_OK] = 1;
        row[AUTH_OK] = 1;
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

/// The eight-lane anchor root a trace publishes — the value governance must have pinned.
fn lane_root_of(cells: &[Vec<i64>]) -> [u32; ANCHOR_LANES] {
    let last = cells.last().expect("a trace has rows");
    std::array::from_fn(|j| felt(last[ROOT_OUT_0 + j]).as_u32())
}

const TEST_BANK_HASH: [u8; 32] = [
    0x9a, 0x1f, 0x33, 0x07, 0xc4, 0x52, 0xbe, 0x11, 0x88, 0x2d, 0x6e, 0xf0, 0x4b, 0x93, 0x25, 0xa7,
    0x60, 0xd8, 0x17, 0x3c, 0xe5, 0x0b, 0x74, 0x9f, 0x21, 0xaa, 0x58, 0x66, 0xcd, 0x02, 0xef, 0x40,
];
const TEST_EPOCH: u64 = 1011;

/// A 32-byte `PredicateInput::Slot` carrying the recorded slot in its low four bytes.
fn slot_input(slot: u32) -> [u8; 32] {
    let mut s = [0u8; 32];
    s[..4].copy_from_slice(&slot.to_le_bytes());
    s
}

/// The whole honest bundle: a proven trace, its PIs, the governance pin it publishes, and a wire.
struct Bundle {
    wire: SolanaLockProofWire,
    pinned: SolanaGovernanceAnchor,
    commitment: [u8; 32],
    slot: u32,
}

fn honest_bundle(total: u64, rooted: u64) -> Bundle {
    let u = honest(total, rooted, &TEST_BANK_HASH);
    let cells = trace_cells(&u);
    let pis = pis_from(&cells, &u);
    let trace: Vec<Vec<BabyBear>> = cells
        .iter()
        .map(|r| r.iter().map(|&v| felt(v)).collect())
        .collect();
    let mem = MemBoundaryWitness::default();
    let heaps: Vec<Vec<HeapLeaf>> = vec![];
    let proof = prove_vm_descriptor2(&desc(), &trace, &pis, &mem, &heaps).expect(
        "the honest fill must prove — an honest pole that fails makes every refusal vacuous",
    );
    let pinned = SolanaGovernanceAnchor {
        epoch: TEST_EPOCH,
        stake_table_lane_root: lane_root_of(&cells),
    };
    let commitment = solana_lock_commitment(&pinned.stake_table_lane_root, u.slot);
    Bundle {
        wire: SolanaLockProofWire {
            public_inputs: pis.iter().map(|p| p.as_u32()).collect(),
            proof,
            anchor_epoch: TEST_EPOCH,
            rotation_steps: 0,
            bank_hash: TEST_BANK_HASH,
        },
        pinned,
        commitment,
        slot: u.slot,
    }
}

fn run(v: &SolanaAnchoredLockStarkVerifier, b: &Bundle) -> Result<(), WitnessedPredicateError> {
    let s = slot_input(b.slot);
    let bytes = postcard::to_allocvec(&b.wire).expect("wire serialises");
    v.verify(&b.commitment, &PredicateInput::Slot(&s), &bytes)
}

fn reason(e: WitnessedPredicateError) -> String {
    match e {
        WitnessedPredicateError::Rejected { reason, .. } => reason,
        other => panic!("expected a Rejected, got {other:?}"),
    }
}

// ════════════════════════════════════════════════════════════════════════════════════════════
// ⚑ ABSENCE IS REJECT — exhibited, and BEFORE the blob is decoded.
// ════════════════════════════════════════════════════════════════════════════════════════════

/// ⚑⚑⚑ **REFUSAL 0.** A node with no governance-pinned lane root refuses every lock, and refuses
/// it on GARBAGE bytes — which is how we exhibit that the refusal precedes the decode. A verifier
/// that decoded first would report a codec error here instead.
#[test]
fn an_unpinned_node_refuses_before_the_blob_is_decoded() {
    let v = SolanaAnchoredLockStarkVerifier::unwired();
    assert!(!v.is_anchor_pinned());
    let s = slot_input(LIVE_SLOT);
    let e = reason(
        v.verify(
            &[7u8; 32],
            &PredicateInput::Slot(&s),
            b"not a postcard blob at all",
        )
        .expect_err("an unpinned node must REFUSE"),
    );
    assert!(
        e.contains("no governance-pinned Solana stake-table lane root is installed"),
        "the refusal must name the ABSENT capability, not the blob; got: {e}"
    );
    assert!(
        !e.contains("did not decode"),
        "refusal 0 must precede the decode — a codec error here means the order slipped; got: {e}"
    );
}

/// The absence refusal is not vacuous: the SAME garbage bytes reach the decoder once a pin exists,
/// so the test above is discriminating the capability and not the input.
#[test]
fn a_pinned_node_reaches_the_decoder_on_the_same_bytes() {
    let v = SolanaAnchoredLockStarkVerifier::with_pinned_anchor(SolanaGovernanceAnchor {
        epoch: TEST_EPOCH,
        stake_table_lane_root: [1, 2, 3, 4, 5, 6, 7, 8],
    });
    let s = slot_input(LIVE_SLOT);
    let e = reason(
        v.verify(
            &[7u8; 32],
            &PredicateInput::Slot(&s),
            b"not a postcard blob at all",
        )
        .expect_err("garbage must still be refused"),
    );
    assert!(
        e.contains("did not decode"),
        "with a pin installed the SAME bytes must reach the codec; got: {e}"
    );
}

// The program pin's own polarity pair lives beside the pin, in
// `turn/src/executor/solana_head_verifier.rs`'s `mod tests` — it needs no prover, and keeping one
// copy is the point. What this file adds is that the pin is spent on the path a real proof takes.

// ════════════════════════════════════════════════════════════════════════════════════════════
// ⚑ THE WELD — every public input tied to something the prover does not choose.
// ════════════════════════════════════════════════════════════════════════════════════════════

/// ⚑⚑⚑ **THE HONEST POLE.** A real trace, a real prover, the real verifier: `Ok(())`. Everything
/// below is vacuous without this.
#[test]
fn an_honest_anchored_lock_proves_and_verifies() {
    let b = honest_bundle(LIVE_ACTIVE_STAKE, MIN_QUORUM);
    let v = SolanaAnchoredLockStarkVerifier::with_pinned_anchor(b.pinned);
    run(&v, &b).expect("the honest anchored lock must verify through the deployed consumer");
}

/// ⚑⚑⚑ **THE FORGERY THE SURVEY NAMES: a stake table that satisfies every in-circuit check and is
/// not the finalized chain's.** The proof is perfectly honest — it proves a real quorum over a real
/// table. What refuses it is the governance pin, and nothing else could: the quorum is a fact about
/// SOME table, and this is the check that makes it THE table.
#[test]
fn a_quorum_over_a_table_governance_did_not_pin_is_refused() {
    let b = honest_bundle(LIVE_ACTIVE_STAKE, MIN_QUORUM);
    let mut pinned = b.pinned;
    let before = pinned.stake_table_lane_root[3];
    pinned.stake_table_lane_root[3] = before.wrapping_add(1) % (P as u32);
    // ⚑ THE FALSIFIER MOVED, and it moved a NON-ZERO lane: a tamper into an equal value refuses
    // nothing, and bumping a zero would be testing the filler rather than the weld.
    assert_ne!(
        pinned.stake_table_lane_root[3], before,
        "the forgery must actually move a value"
    );
    assert_ne!(
        before, 0,
        "and it must move a lane that was not already zero"
    );
    let commitment = solana_lock_commitment(&pinned.stake_table_lane_root, b.slot);
    let b2 = Bundle {
        wire: b.wire,
        pinned,
        commitment,
        slot: b.slot,
    };
    let v = SolanaAnchoredLockStarkVerifier::with_pinned_anchor(pinned);
    let e = reason(run(&v, &b2).expect_err("a table governance did not pin must be REFUSED"));
    assert!(
        e.contains("governance-pinned lane root"),
        "the refusal must name the GOVERNANCE PIN — the gate under test — and not the STARK or the \
         commitment; got: {e}"
    );
    assert!(
        !e.contains("STARK rejected"),
        "the weld must refuse BEFORE the verification is spent; got: {e}"
    );
}

/// ⚑ A bank-root limb that is not the recorded bank hash's lane is refused, and by the bank-root
/// weld specifically.
#[test]
fn a_bank_root_limb_that_is_not_the_recorded_hash_is_refused() {
    let mut b = honest_bundle(LIVE_ACTIVE_STAKE, MIN_QUORUM);
    let before = b.wire.public_inputs[PI_BANK_ROOT_0 + 2];
    b.wire.public_inputs[PI_BANK_ROOT_0 + 2] = before.wrapping_add(1) % (P as u32);
    assert_ne!(b.wire.public_inputs[PI_BANK_ROOT_0 + 2], before);
    assert_ne!(before, 0, "the moved limb must not have been zero");
    let v = SolanaAnchoredLockStarkVerifier::with_pinned_anchor(b.pinned);
    let e = reason(
        run(&v, &b)
            .expect_err("a published bank root that is not the observed one must be REFUSED"),
    );
    assert!(
        e.contains("bank-root limb"),
        "the refusal must name the bank-root weld; got: {e}"
    );
}

/// ⚑ A proof for a different slot than the turn is recording is refused.
#[test]
fn a_proof_for_another_slot_is_refused() {
    let mut b = honest_bundle(LIVE_ACTIVE_STAKE, MIN_QUORUM);
    let before = b.wire.public_inputs[PI_SLOT];
    b.wire.public_inputs[PI_SLOT] = before - 1;
    assert_ne!(b.wire.public_inputs[PI_SLOT], before);
    let v = SolanaAnchoredLockStarkVerifier::with_pinned_anchor(b.pinned);
    let e = reason(run(&v, &b).expect_err("a proof about another slot must be REFUSED"));
    assert!(
        e.contains("rooted slot"),
        "the refusal must name the slot weld; got: {e}"
    );
}

/// ⚑⚑ **THE ROTATION REFUSAL — the named residual, refused rather than trusted.**
/// `solana_trustless.rs:587` walks `provenance.rotation` in hand-written Rust and nothing proves
/// that chain. A wire that declares a rotation is refused outright.
#[test]
fn a_rotated_anchor_is_refused_rather_than_trusted_to_the_rust_chain() {
    let mut b = honest_bundle(LIVE_ACTIVE_STAKE, MIN_QUORUM);
    b.wire.rotation_steps = 1;
    let v = SolanaAnchoredLockStarkVerifier::with_pinned_anchor(b.pinned);
    let e = reason(run(&v, &b).expect_err("a rotated anchor must be REFUSED"));
    assert!(
        e.contains("epoch-rotation step"),
        "the refusal must name the rotation residual; got: {e}"
    );
}

/// ⚑ A proof under an epoch this node did not attest is refused.
#[test]
fn a_proof_under_another_governance_epoch_is_refused() {
    let mut b = honest_bundle(LIVE_ACTIVE_STAKE, MIN_QUORUM);
    b.wire.anchor_epoch = TEST_EPOCH + 1;
    let v = SolanaAnchoredLockStarkVerifier::with_pinned_anchor(b.pinned);
    let e = reason(run(&v, &b).expect_err("a foreign epoch must be REFUSED"));
    assert!(
        e.contains("governance anchor epoch"),
        "the refusal must name the epoch weld; got: {e}"
    );
}

// ════════════════════════════════════════════════════════════════════════════════════════════
// ⚑⚑⚑ THE DIVERGENCE — the point the Rust gate MINTS and this one REFUSES.
// ════════════════════════════════════════════════════════════════════════════════════════════

/// ⚑⚑⚑ **THE WHOLE LANE, IN ONE PAIR.** `bridge/src/solana_provenance.rs:697` is
/// `voted.saturating_mul(3) >= total.saturating_mul(2)` — NON-STRICT, so a cluster sitting exactly
/// on two thirds MINTS. The AIR ships `γ = 1`, the strict `3·rooted > 2·total`, and the prover has
/// no honest fill at the exact point: the top difference limb comes out NEGATIVE.
///
/// This test asserts BOTH halves, so it cannot pass by the boundary having moved.
#[test]
fn the_exact_two_thirds_point_mints_in_rust_and_has_no_honest_fill_here() {
    // The Rust gate's own arithmetic, transcribed: it ADMITS.
    assert!(
        (EXACT_TWO_THIRDS as u128).saturating_mul(3)
            >= (LIVE_ACTIVE_STAKE as u128).saturating_mul(2),
        "the exact point must satisfy the deployed Rust super-majority — if this fails the \
         divergence this lane reports has moved"
    );
    assert_eq!(
        (EXACT_TWO_THIRDS as u128) * 3,
        (LIVE_ACTIVE_STAKE as u128) * 2,
        "and it must be EXACTLY the boundary, not merely above it"
    );

    // The AIR's own arithmetic: the strict chain has no non-negative fill.
    let total_l = limbs4(LIVE_ACTIVE_STAKE);
    let exact_l = limbs4(EXACT_TWO_THIRDS);
    let refused = fill_chain(3, exact_l, 2, total_l, QUORUM_GAMMA);
    assert!(
        refused.diff[RUNGS] < 0,
        "the strict quorum must leave a NEGATIVE top difference limb at the exact point — that \
         negativity IS the refusal; got {}",
        refused.diff[RUNGS]
    );

    // One lamport more and the fill exists. This is the non-vacuity control: the chain is not
    // simply always negative.
    let min_l = limbs4(MIN_QUORUM);
    let admitted = fill_chain(3, min_l, 2, total_l, QUORUM_GAMMA);
    assert!(
        admitted.diff[RUNGS] >= 0,
        "one lamport above the boundary must have an honest fill; got {}",
        admitted.diff[RUNGS]
    );
}

/// ⚑⚑ **AND THE DEPLOYED PROVER AGREES.** The pair above is arithmetic; this is the served
/// descriptor refusing the exact point through the real prover. Release-only: the range tooth that
/// fires here is an `Err` in both profiles, but the surrounding algebra is a debug panic.
#[test]
fn the_deployed_prover_refuses_the_exact_two_thirds_point() {
    let u = honest(LIVE_ACTIVE_STAKE, EXACT_TWO_THIRDS, &TEST_BANK_HASH);
    let cells = trace_cells(&u);
    let pis = pis_from(&cells, &u);
    let trace: Vec<Vec<BabyBear>> = cells
        .iter()
        .map(|r| r.iter().map(|&v| felt(v)).collect())
        .collect();
    let mem = MemBoundaryWitness::default();
    let heaps: Vec<Vec<HeapLeaf>> = vec![];
    let e = prove_vm_descriptor2(&desc(), &trace, &pis, &mem, &heaps)
        .err()
        .expect(
            "the exact two-thirds point must have NO honest proof under the shipped strict gate",
        );
    let e = format!("{e}");
    assert!(
        e.contains("range wire"),
        "the refusal must be the limb RANGE tooth on the negative top difference limb — the gate \
         under test — and not an unrelated bus failure; got: {e}"
    );
}
