//! ⚑ **BOTH POLARITIES ON THE EMITTED OBJECT, AND THE LANDING.**
//!
//! `dregg-mina-lightclient-verify::v1` is the Lean-COMPILED Mina anchored-head verify AIR
//! (`metatheory/Dregg2/Circuit/Emit/LightClientMinaAir.lean` — `EffectLower.lowerAir` of the
//! `EffectAir` source `minaHeadAir`; there is no hand-written `VmConstraint2` in its module). This
//! file proves and verifies it, and exhibits the refusals ON THE DESCRIPTOR ITSELF rather than on a
//! model of it.
//!
//! ⚑ Measured 2026-08-02: **no peer-chain lightclient verify AIR in this tree had ever been proved
//! in Rust.** `dregg-{eth,tm,solana,midnight}-lightclient-verify::v1` are `include_str!`'d and
//! name-dispatched, and `grep -rl lightclient-verify --include=*.rs` returns only
//! `descriptor_by_name.rs` and this Mina work. "Producible by a node" was a claim about DISPATCH.
//! This is the first prove/verify round trip of one.
//!
//! # What each test establishes
//!
//! * `an_honest_anchored_head_proves_and_verifies` — the POSITIVE polarity. Anchor pinned at
//!   height 400,000; 300 exhibited, linked, proof-carrying blocks; settlement submitted at 400,010;
//!   Samasika `k = 290` met exactly. Proves, verifies, and the recorded head binds.
//! * `a_forged_blockchain_length_is_refused_by_the_descriptor` — ⚑ the tooth. Five blocks exhibited
//!   but 400,300 published, with every other column filled to match the lie. G2/G3/G4/G5 all hold
//!   on that row; **G1 (`BLOCK_LEN = ANCHOR_H + SEG_LEN`) refuses it**, and it is refused by the
//!   AIR, not by an executor comparison.
//! * `a_losing_fork_is_refused_by_the_descriptor` — 285 blocks against a `k = 290` requirement:
//!   `DEPTH_SLACK = −5`, which in the field is `p − 5 = 2013265916`, far outside `[0, 2^24)`. The
//!   range tooth has no satisfying row. ⚑ This is the shallower branch of a real disagreement
//!   refused by the descriptor.
//! * `a_bent_proof_word_is_refused_by_the_descriptor` — the Pickles carrier at `0`.
//! * `the_observer_arithmetic_is_refused_by_the_descriptor` — the deployed observer's own accepting
//!   input (`Dregg2.Bridge.LightClientMina.witnessedDepth_unbounded_without_anchor_bound`: anchor
//!   1000, submitted 0, ONE block "witnessing" depth 1001). `ANCH_SLACK = −1000`.
//! * `the_landing_refuses_a_head_the_turn_did_not_prove` — the executor-side binding: a VERIFYING
//!   proof of head A does not license recording head B.
//!
//! ⚠ Scope, said plainly: `LINK_OK` / `PICKLES_OK` / `CANON_OK` are witnessed carriers on the
//! undischarged IPA/FRI floor, and the dregg-side STARK inherits the undischarged FRI floor. This
//! is an ANCHORED SEGMENT, not fork choice. Not "machine-checked", not "Mina-valid".

use dregg_circuit::BabyBear;
use dregg_circuit::descriptor_by_name::descriptor_by_name;
use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, MemBoundaryWitness, prove_vm_descriptor2, verify_vm_descriptor2,
};
use dregg_circuit::heap_root::HeapLeaf;
use dregg_turn::executor::mina_head_verifier::{
    MINA_LC_PI_COUNT, MINA_LC_VERIFY_DESCRIPTOR, PI_ANCHOR_STATE_BASE, PI_BLOCK_LEN, PI_REQ_DEPTH,
    PI_TIP_STATE_BASE, check_head_binding, key_lanes_u32,
};

// Trace column layout — pinned to `LightClientMinaAir`'s Lean `def`s.
const SEG_LEN: usize = 0;
const ANCHOR_H: usize = 1;
const SUBMIT_H: usize = 2;
const WIT_DEPTH: usize = 3;
const REQ_DEPTH: usize = 4;
const SEG_SLACK: usize = 5;
const ANCH_SLACK: usize = 6;
const DEPTH_SLACK: usize = 7;
const LINK_OK: usize = 8;
const PICKLES_OK: usize = 9;
const CANON_OK: usize = 10;
const BLOCK_LEN: usize = 11;
const ANCHOR_STATE_0: usize = 12;
const TIP_STATE_0: usize = 21;
const MINA_LC_WIDTH: usize = 30;

const TRACE_ROWS: usize = 8;

fn desc() -> EffectVmDescriptor2 {
    descriptor_by_name(MINA_LC_VERIFY_DESCRIPTOR).unwrap_or_else(|| {
        panic!(
            "{MINA_LC_VERIFY_DESCRIPTOR} must dispatch: the Lean-compiled descriptor is routed \
             through EmitByName.lean and included by circuit/src/descriptor_by_name.rs"
        )
    })
}

/// The witness columns of one logical row. Everything above `BLOCK_LEN` is filled from the two
/// 32-byte hashes by `row`.
#[derive(Clone, Copy)]
struct Head {
    seg_len: u32,
    anchor_h: u32,
    submit_h: u32,
    wit_depth: i64,
    req_depth: u32,
    block_len: u32,
    link_ok: u32,
    pickles_ok: u32,
    canon_ok: u32,
}

/// An HONEST head: every derived column computed, never claimed.
fn honest(seg_len: u32, anchor_h: u32, submit_h: u32, req_depth: u32) -> Head {
    let block_len = anchor_h + seg_len;
    Head {
        seg_len,
        anchor_h,
        submit_h,
        wit_depth: block_len as i64 - submit_h as i64,
        req_depth,
        block_len,
        link_ok: 1,
        pickles_ok: 1,
        canon_ok: 1,
    }
}

/// Field-encode a possibly-negative slack: in BabyBear a negative value IS `p − k`, which is the
/// element the range tooth must refuse.
fn felt(v: i64) -> BabyBear {
    let p = 2013265921i64;
    BabyBear::new(v.rem_euclid(p) as u32)
}

/// The `TRACE_ROWS`-row trace (every row identical: the descriptor's gates are single-row and its
/// pins are first-row, so replication is the FRI padding shape) plus the twenty public inputs.
fn trace_and_pis(
    h: Head,
    anchor: &[u8; 32],
    tip: &[u8; 32],
) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    let anchor_lanes = key_lanes_u32(anchor);
    let tip_lanes = key_lanes_u32(tip);

    let mut r = vec![BabyBear::new(0); MINA_LC_WIDTH];
    r[SEG_LEN] = BabyBear::new(h.seg_len);
    r[ANCHOR_H] = BabyBear::new(h.anchor_h);
    r[SUBMIT_H] = BabyBear::new(h.submit_h);
    r[WIT_DEPTH] = felt(h.wit_depth);
    r[REQ_DEPTH] = BabyBear::new(h.req_depth);
    // The three slacks, each the genuine difference the gate identity forces.
    r[SEG_SLACK] = felt(h.seg_len as i64 - 1);
    r[ANCH_SLACK] = felt(h.submit_h as i64 - h.anchor_h as i64);
    r[DEPTH_SLACK] = felt(h.wit_depth - h.req_depth as i64);
    r[LINK_OK] = BabyBear::new(h.link_ok);
    r[PICKLES_OK] = BabyBear::new(h.pickles_ok);
    r[CANON_OK] = BabyBear::new(h.canon_ok);
    r[BLOCK_LEN] = BabyBear::new(h.block_len);
    for i in 0..9 {
        r[ANCHOR_STATE_0 + i] = BabyBear::new(anchor_lanes[i]);
        r[TIP_STATE_0 + i] = BabyBear::new(tip_lanes[i]);
    }

    let mut pis = vec![BabyBear::new(0); MINA_LC_PI_COUNT];
    for i in 0..9 {
        pis[PI_ANCHOR_STATE_BASE + i] = BabyBear::new(anchor_lanes[i]);
        pis[PI_TIP_STATE_BASE + i] = BabyBear::new(tip_lanes[i]);
    }
    pis[PI_BLOCK_LEN] = BabyBear::new(h.block_len);
    pis[PI_REQ_DEPTH] = BabyBear::new(h.req_depth);

    (vec![r; TRACE_ROWS], pis)
}

/// `Ok(())` iff the descriptor ACCEPTS this witness — prove AND verify.
///
/// ⚑ **A REFUSAL HAS THREE SHAPES HERE, AND ALL THREE ARE REFUSALS.** Measured 2026-08-03 on this
/// descriptor:
///
/// * an `Err` from the prover — how the RANGE teeth refuse (`row 0: range wire 7 value 2013265916
///   >= 2^24`, which is `p − 5`: the wrapped negative slack, verbatim);
/// * a PANIC out of plonky3's `check_constraints.rs:133` (`constraints not satisfied on row 0:
///   failed constraints = [#0]`) — how the ALGEBRAIC gates refuse in a debug build, where the
///   prover's own constraint check is a debug assertion;
/// * an `Err` from the verifier — the deployed leg.
///
/// So this helper does exactly what the production consumer does: `mina_head_verifier.rs`'s refusal
/// 4 runs prove/verify under `catch_unwind` precisely so a malformed or forged witness is a
/// fail-closed REJECTION and never a panic unwinding through the executor. A test that let a panic
/// escape would report the descriptor's refusal as a test failure — which is what the first run of
/// this file did, and the descriptor was right both times.
fn descriptor_accepts(h: Head, anchor: &[u8; 32], tip: &[u8; 32]) -> Result<(), String> {
    let d = desc();
    let (trace, pis) = trace_and_pis(h, anchor, tip);
    let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let mem = MemBoundaryWitness::default();
        let heaps: Vec<Vec<HeapLeaf>> = vec![];
        let proof = prove_vm_descriptor2(&d, &trace, &pis, &mem, &heaps)
            .map_err(|e| format!("prover refused: {e}"))?;
        verify_vm_descriptor2(&d, &proof, &pis).map_err(|e| format!("verifier refused: {e:?}"))
    }));
    match outcome {
        Ok(r) => r,
        Err(_) => Err(
            "prover/verifier PANICKED — plonky3's debug constraint check fired, i.e. an emitted \
             gate is unsatisfied on this row. The deployed consumer catches this the same way."
                .to_string(),
        ),
    }
}

/// Quieten the default panic printer for the refusal cases: a refusal that arrives as a panic is
/// expected here, and its backtrace is noise. Restored by the guard's `Drop`.
struct QuietPanics(Option<Box<dyn Fn(&std::panic::PanicHookInfo<'_>) + Sync + Send + 'static>>);

impl QuietPanics {
    fn new() -> Self {
        let prev = std::panic::take_hook();
        std::panic::set_hook(Box::new(|_| {}));
        Self(Some(prev))
    }
}

impl Drop for QuietPanics {
    fn drop(&mut self) {
        if let Some(h) = self.0.take() {
            std::panic::set_hook(h);
        }
    }
}

const ANCHOR: [u8; 32] = [0x5au8; 32];
const TIP: [u8; 32] = [0x17u8; 32];

/// The descriptor this tree serves is the one the Lean module declares.
#[test]
fn the_served_descriptor_is_the_lean_compiled_one() {
    let d = desc();
    assert_eq!(d.name, MINA_LC_VERIFY_DESCRIPTOR);
    assert_eq!(d.trace_width, MINA_LC_WIDTH);
    assert_eq!(d.public_input_count, MINA_LC_PI_COUNT);
    // 8 gates + 3 range lookups + 20 PI pins, one per source leg.
    assert_eq!(d.constraints.len(), 31);
    assert_eq!(d.tables.len(), 1);
}

/// ⚑ POSITIVE POLARITY. A genuinely verified anchored head PROVES and VERIFIES, and its recorded
/// head binds at the executor. Without this every refusal below is satisfied by a descriptor that
/// refuses everything.
#[test]
fn an_honest_anchored_head_proves_and_verifies() {
    let h = honest(300, 400_000, 400_010, 290);
    assert_eq!(h.block_len, 400_300);
    assert_eq!(h.wit_depth, 290);
    descriptor_accepts(h, &ANCHOR, &TIP).expect("an honest anchored head must prove and verify");

    let (_, pis) = trace_and_pis(h, &ANCHOR, &TIP);
    let raw: Vec<u32> = pis.iter().map(|f| f.as_u32()).collect();
    check_head_binding(&ANCHOR, &TIP, &raw).expect("the recorded head must bind");
}

/// ⚑ THE TOOTH. Five blocks exhibited, 400,300 published — every other column filled to match the
/// lie, so G2/G3/G4/G5 ALL HOLD. G1 alone refuses it, in the AIR.
///
/// This is the `mina-tip` wound in circuit form: a peer reply read at 1,544 of 61,193 bytes left
/// `blockchain_length` standing because it is the one field a liar sets for free. Here it is
/// DERIVED from the pinned anchor plus the exhibited segment, so it is not settable.
#[test]
fn a_forged_blockchain_length_is_refused_by_the_descriptor() {
    let _quiet = QuietPanics::new();
    let mut h = honest(5, 400_000, 400_010, 290);
    h.block_len = 400_300; // the lie
    h.wit_depth = 290; // …and the depth columns dressed to match it
    let err = descriptor_accepts(h, &ANCHOR, &TIP)
        .expect_err("a forged blockchain_length must be REFUSED by the descriptor");
    eprintln!("forged blockchain_length refused: {err}");
}

/// ⚑ THE LOSING FORK. 285 exhibited blocks against a `k = 290` requirement: `DEPTH_SLACK = −5`,
/// which in the field is `p − 5 = 2013265916`, far outside the declared `[0, 2^24)`. The range
/// lookup has no satisfying row.
#[test]
fn a_losing_fork_is_refused_by_the_descriptor() {
    let _quiet = QuietPanics::new();
    let h = honest(295, 400_000, 400_010, 290);
    assert_eq!(h.wit_depth, 285, "the shallower fork witnesses only 285");
    let err = descriptor_accepts(h, &ANCHOR, &TIP)
        .expect_err("a fork five blocks short of k must be REFUSED by the descriptor");
    eprintln!("losing fork refused: {err}");
}

/// ⚑ A BENT PROOF WORD: the Pickles carrier at `0`, every other column honest.
#[test]
fn a_bent_proof_word_is_refused_by_the_descriptor() {
    let _quiet = QuietPanics::new();
    let mut h = honest(300, 400_000, 400_010, 290);
    h.pickles_ok = 0;
    let err = descriptor_accepts(h, &ANCHOR, &TIP)
        .expect_err("a block whose Wrap proof does not verify must be REFUSED");
    eprintln!("bent proof word refused: {err}");
}

/// ⚑ THE DEPLOYED OBSERVER'S OWN ACCEPTING INPUT. Anchor at 1000, settlement submitted at 0, ONE
/// exhibited block: `tip_height.saturating_sub(submitted_height)` reports depth 1001 and
/// `mina_observer::observe_settlement` finalizes. Here `ANCH_SLACK = 0 − 1000 = −1000` is the field
/// element `p − 1000`, outside `[0, 2^24)`.
#[test]
fn the_observer_arithmetic_is_refused_by_the_descriptor() {
    let _quiet = QuietPanics::new();
    let h = honest(1, 1000, 0, 290);
    assert_eq!(
        h.wit_depth, 1001,
        "the observer's arithmetic 'witnesses' 1001"
    );
    let err = descriptor_accepts(h, &ANCHOR, &TIP)
        .expect_err("an unanchored depth claim must be REFUSED by the descriptor");
    eprintln!("observer arithmetic refused: {err}");
}

/// ⚑ THE LANDING, at the executor seam: a proof of head A that genuinely VERIFIES does not license
/// recording head B. The descriptor cannot see this — its tip lanes are consistent with themselves
/// — so the binding lives where the state write does.
#[test]
fn the_landing_refuses_a_head_the_turn_did_not_prove() {
    let h = honest(300, 400_000, 400_010, 290);
    descriptor_accepts(h, &ANCHOR, &TIP).expect("the proof of head A verifies");

    let (_, pis) = trace_and_pis(h, &ANCHOR, &TIP);
    let raw: Vec<u32> = pis.iter().map(|f| f.as_u32()).collect();
    let other_head = [0x18u8; 32];
    let err = check_head_binding(&ANCHOR, &other_head, &raw)
        .expect_err("recording a head the proof did not verify must be REFUSED");
    assert!(err.contains("different head"), "{err}");

    let other_anchor = [0x5bu8; 32];
    let err = check_head_binding(&other_anchor, &TIP, &raw)
        .expect_err("a head under a different pinned anchor must be REFUSED");
    assert!(err.contains("anchored somewhere else"), "{err}");
}
