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
//! * `the_anchor_substitution_is_refused_by_the_descriptor` — ⚑ **THE CANONICALITY RUNG
//!   (2026-08-03).** The pinned anchor is the real devnet genesis hash PLUS ONE PASTA MODULUS,
//!   which chains to the identical tip state hash. `CANON_OK` still reads `1`; the descriptor
//!   refuses it anyway, on the 22-bit TOP-LANE lookup at column 20.
//! * `the_forged_anchor_passes_the_encoder_and_fails_the_field` — and the refusal is the FIELD
//!   canonicality tooth, not a malformed-nonet accident: lane 8 of the forgery is below the
//!   `Faithful9` `2^24` ceiling and above the Pasta `2^22` one.
//!
//! ⚠ Scope, said plainly. `LINK_OK` and `PICKLES_OK` remain witnessed carriers on the undischarged
//! IPA/FRI floor. `CANON_OK` is DERIVED for the two `Fp` elements this descriptor publishes — the
//! anchor and the tip — by eighteen lookups on the lane columns it already carried; the PER-BLOCK
//! canonicality `LightClientMina.canonOk` quantifies over is not, because a single-row descriptor
//! has no per-block columns. The dregg-side STARK inherits the undischarged FRI floor. This is an
//! ANCHORED SEGMENT, not fork choice. Not "machine-checked", not "Mina-valid".

use dregg_circuit::BabyBear;
use dregg_circuit::descriptor_by_name::descriptor_by_name;
use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, MemBoundaryWitness, prove_vm_descriptor2, verify_vm_descriptor2,
};
use dregg_circuit::heap_root::HeapLeaf;
use dregg_turn::executor::mina_head_verifier::{
    MINA_LC_PI_COUNT, MINA_LC_VERIFY_DESCRIPTOR, PI_ANCHOR_H, PI_ANCHOR_STATE_BASE, PI_BLOCK_LEN,
    PI_CONJ_COMMIT_BASE, PI_REQ_DEPTH, PI_SUB_COMMIT_BASE, PI_TIP_STATE_BASE, check_head_binding,
    key_lanes_u32,
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
const PICKLES_OPENING_WITNESSED: usize = 9;
const CANON_OK: usize = 10;
const BLOCK_LEN: usize = 11;
const ANCHOR_STATE_0: usize = 12;
const TIP_STATE_0: usize = 21;
/// ⚑ 49, not 30. `7a4b8ab00` split `PICKLES_OK` into `PICKLES_WITNESSED` + `WRAP_FS_PROVED` and
/// added the recursion carrier's two nine-lane blocks; this file kept building 30-wide rows, so
/// every prove in it died as *"base row 0 width 30 is short of the PRODUCER-OWNED width 49"* — a
/// SHAPE fault, which is neither pole. Both polarities in this file were dead from that morning.
/// ⚑ 77 since 2026-08-06's FINALIZE-CONJUNCTION rung (was 58, was 49, was 30). Every widening of this descriptor has cost
/// this file a red, and each time the red was a SHAPE fault — "base row 0 width N is short of the
/// PRODUCER-OWNED width M" — which is neither pole. That is the failure this constant exists to make
/// loud: a stale width here does not weaken a test, it silently stops both polarities from running.
const MINA_LC_WIDTH: usize = 77;

/// ⚑⚑ The FINALIZE-CONJUNCTION carrier (`LightClientMinaAir.FINALIZE_XI_B_PROVED`, col 58) and its
/// two nine-lane blocks. Added 2026-08-06; this is what `PICKLES_WITNESSED` became.
const FINALIZE_XI_B_PROVED: usize = 58;
const CONJ_VK_0: usize = 59;
const CONJ_PI_0: usize = 68;

/// `LightClientMinaAir.CONJ_VK_LANES` — the nine `Faithful9` lanes of
/// `dregg-mina-wrap-conjunction::v1`'s semantic fingerprint. NOT the prover's to choose: the emitted
/// `proof_bind` forces the row's `CONJ_VK` block to these literals under the guard.
const CONJ_VK_LANES: [u32; 9] = [
    447620828, 118399956, 332150941, 529607877, 314255522, 98355104, 173079149, 176046258, 561245,
];

/// `LightClientMinaAir.CONJ_PI_LANES` — ⚠ **NINE ZEROS, and labelled so in Lean too.** Not forced by
/// any gate: `CONJ_PI` is PI-bound with `bound := none`. What refuses a wrong one is
/// `mina_head_verifier::check_conjunction_binding`, at the consumer. Kept identical to the Lean
/// honest row so `decide` and the deployed prover see ONE object.
const CONJ_PI_LANES: [u32; 9] = [0; 9];
/// ⚑ The recursion carrier (col 30) and its two nine-lane blocks (31..40 program, 40..49 declared
/// commitment) — `LightClientMinaAir.WRAP_FS_PROVED` / `SUB_VK` / `SUB_PI`.
const WRAP_FS_PROVED: usize = 30;
const SUB_VK_0: usize = 31;
const SUB_PI_0: usize = 40;
/// ⚑⚑ The SEGMENT seam's attested program lanes (`LightClientMinaAir.LINK_VK`), cols 49..57 — the
/// nine columns `LINK_OK` guards. Before 2026-08-05 `LINK_OK` was a bare `= 1`; it is now the guard
/// of a `proof_bind` whose declared commitment is the row's nine PUBLISHED `TIP_STATE` columns.
const LINK_VK_0: usize = 49;
/// The nine `Faithful9` lanes of `dregg-mina-lightclient-link::v1`'s semantic fingerprint — the
/// value the descriptor's second `vk_pin` forces under `LINK_OK = 1`. Recomputed from that
/// descriptor's own bytes by `circuit/tests/mina_transcript_carrier_binding.rs` and by `dregg-turn`
/// at verify time (`check_subproof_program_pin` at `HEAD_LINK_GUARD_COL`).
const LINK_VK_LANES: [u32; 9] = [
    233430738, 4032640, 246608840, 175841926, 90073704, 22259745, 113829679, 206352694, 3987074,
];
/// The nine `Faithful9` lanes of `dregg-pasta-fq-chainlink::v1`'s semantic fingerprint — the value
/// the descriptor's `vk_pin` forces under `WRAP_FS_PROVED = 1`. Recomputed from that descriptor's
/// own bytes by `circuit/tests/mina_transcript_carrier_binding.rs`, and by `dregg-turn` itself at
/// verify time (`check_subproof_program_pin`); a literal here so a drift is a red, not a silence.
const CHAINLINK_VK_LANES: [u32; 9] = [
    40589529, 494773874, 527776693, 373808410, 118028044, 372824034, 512521559, 25478361, 4577485,
];
/// The nine lanes of the digest of that sub-proof's 256 public inputs on the block-539508 instance's
/// 46th and last link — PI-bound at slots 20..28.
const CHAINLINK_PI_LANES: [u32; 9] = [
    76470648, 44150818, 361910605, 443692671, 242143308, 490185822, 240590146, 360276303, 4019771,
];

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
/// pins are first-row, so replication is the FRI padding shape) plus the thirty public inputs.
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
    r[PICKLES_OPENING_WITNESSED] = BabyBear::new(h.pickles_ok);
    r[CANON_OK] = BabyBear::new(h.canon_ok);
    r[BLOCK_LEN] = BabyBear::new(h.block_len);
    for i in 0..9 {
        r[ANCHOR_STATE_0 + i] = BabyBear::new(anchor_lanes[i]);
        r[TIP_STATE_0 + i] = BabyBear::new(tip_lanes[i]);
        // ⚑ The recursion carrier's two blocks. `SUB_VK` is NOT the prover's to choose: the emitted
        // `proof_bind` forces it to the chainlink fingerprint under the guard below.
        r[SUB_VK_0 + i] = BabyBear::new(CHAINLINK_VK_LANES[i]);
        r[SUB_PI_0 + i] = BabyBear::new(CHAINLINK_PI_LANES[i]);
        // ⚑ …and the SEGMENT seam's program lanes, forced the same way under `LINK_OK`.
        r[LINK_VK_0 + i] = BabyBear::new(LINK_VK_LANES[i]);
        // ⚑⚑ …and the FINALIZE-CONJUNCTION seam's, forced under `FINALIZE_XI_B_PROVED` — the third
        // bind, and the one that retired `PICKLES_WITNESSED` on 2026-08-06.
        r[CONJ_VK_0 + i] = BabyBear::new(CONJ_VK_LANES[i]);
        r[CONJ_PI_0 + i] = BabyBear::new(CONJ_PI_LANES[i]);
    }
    r[WRAP_FS_PROVED] = BabyBear::new(1);
    r[FINALIZE_XI_B_PROVED] = BabyBear::new(1);

    let mut pis = vec![BabyBear::new(0); MINA_LC_PI_COUNT];
    for i in 0..9 {
        pis[PI_ANCHOR_STATE_BASE + i] = BabyBear::new(anchor_lanes[i]);
        pis[PI_TIP_STATE_BASE + i] = BabyBear::new(tip_lanes[i]);
        pis[PI_SUB_COMMIT_BASE + i] = BabyBear::new(CHAINLINK_PI_LANES[i]);
        pis[PI_CONJ_COMMIT_BASE + i] = BabyBear::new(CONJ_PI_LANES[i]);
    }
    pis[PI_BLOCK_LEN] = BabyBear::new(h.block_len);
    pis[PI_REQ_DEPTH] = BabyBear::new(h.req_depth);
    // ⚑ The anchor height, PUBLISHED since `adf5aa892` — read off the row, never asserted beside it.
    pis[PI_ANCHOR_H] = BabyBear::new(h.anchor_h);

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

/// ⚑ **THE ANCHOR IS A REAL MINA STATE HASH, NOT A FILL BYTE.** Devnet genesis
/// `3NL93SipJfAMNDBRfQ8Uo8LPovC74mnJZfZYB5SK7mTtkL72dsPx`, as `Fp` element
/// `9114416221768123787477325283664893678899335531281108607736543138013422200977` in 32 LITTLE-ENDIAN
/// bytes (`LightClientMinaHashFold.DEVNET_GENESIS_STATE_HASH`; the same decode
/// `bridge/src/mina_observer.rs::decode_state_hash` performs).
///
/// It used to be `[0x5a; 32]`, and the canonicality rung (2026-08-03) REFUSED that — correctly. A
/// 32-byte fill pattern is not a Pasta field element: `0x5a5a…5a`'s ninth `Faithful9` lane is
/// 5,921,370, above the `2^22` ceiling that makes the nonet's value `< 2^254 < p`. The fixture was
/// asserting that the descriptor accepts a "state hash" Mina could never have produced.
const ANCHOR: [u8; 32] = [
    0x91, 0xa8, 0xea, 0xb2, 0x14, 0xc0, 0xe9, 0xec, 0xe2, 0xa7, 0x7b, 0x0c, 0xe5, 0x5c, 0xbe, 0x90,
    0x3f, 0x6b, 0x4c, 0xef, 0x3b, 0x3a, 0x7a, 0x95, 0xd2, 0xed, 0xd9, 0x18, 0xa7, 0x93, 0x26, 0x14,
];

/// Devnet block **539508**'s state hash `3NLmVB6Fs3dm4kXNkgwheHXzJXNpCCwEDe76RpTVeBTNujm12zNk` — the
/// block whose Wrap proof o1-labs' own `kimchi::verifier::verify` accepts (`MinaRealBlockGate`).
const TIP: [u8; 32] = [
    0xe4, 0x68, 0xd8, 0x48, 0xac, 0x5d, 0x04, 0x1c, 0xb3, 0x5c, 0x4f, 0xcf, 0x04, 0x16, 0xd7, 0xce,
    0xe1, 0xf9, 0xc5, 0xa1, 0x80, 0x7c, 0x7e, 0xf3, 0x02, 0xdd, 0xd7, 0x0b, 0xcb, 0x72, 0xe3, 0x39,
];

/// ⚑ **THE ANCHOR SUBSTITUTION: the SAME devnet genesis anchor plus ONE PASTA MODULUS.**
///
/// Poseidon's `absorbAt` enters every input through `(state + x) % p`, so a segment presented under
/// `A + p` chains to the IDENTICAL tip state hash as one under `A`
/// (`LightClientMinaHashFold.stateChain_anchor_shift_collides`, proved structurally). The
/// governance-pinned weak-subjectivity anchor therefore does not, by itself, pin the history.
///
/// This value is a perfectly legal `Faithful9` nonet — its ninth lane is 5,514,899, BELOW the
/// encoder's own `2^24` ceiling — so the 32-byte-string canonicity gate admits it and so did the
/// witnessed `CANON_OK` bit. It is refused by the descriptor's 22-bit TOP-LANE table and by nothing
/// else. Lean twin: `LightClientMinaAir.shifted_anchor_old_admits_new_rejects`.
const SHIFTED_ANCHOR: [u8; 32] = [
    0x92, 0xa8, 0xea, 0xb2, 0x01, 0xf1, 0x16, 0x86, 0xfe, 0xa0, 0xc8, 0x15, 0xe1, 0xf5, 0x04, 0xb3,
    0x3f, 0x6b, 0x4c, 0xef, 0x3b, 0x3a, 0x7a, 0x95, 0xd2, 0xed, 0xd9, 0x18, 0xa7, 0x93, 0x26, 0x54,
];

/// The descriptor this tree serves is the one the Lean module declares.
#[test]
fn the_served_descriptor_is_the_lean_compiled_one() {
    let d = desc();
    assert_eq!(d.name, MINA_LC_VERIFY_DESCRIPTOR);
    assert_eq!(d.trace_width, MINA_LC_WIDTH);
    assert_eq!(d.public_input_count, MINA_LC_PI_COUNT);
    // 8 gates + 3 slack lookups + ⚑ the `REQ_DEPTH` lookup + 16 lane lookups (two `.limbs` legs)
    // + 2 top-lane lookups + 20 PI pins = 50, from 36 source legs (`minaHeadAir_leg_count`,
    // `minaLcVerifyDesc_constraint_count`).
    //
    // ⚑ **49 -> 50, 2026-08-03.** `REQ_DEPTH` was PI-pinned and otherwise FREE — it carried no
    // range lookup at all, so a prover could put a negative required depth on the wire, satisfy
    // G5's `DEPTH_SLACK + REQ_DEPTH = WIT_DEPTH` with a non-negative slack, and drive `WIT_DEPTH`
    // — and therefore `BLOCK_LEN - SUBMIT_H` — negative. A settlement submitted ABOVE the verified
    // tip satisfied every emitted constraint; the only thing that caught it was a verifier reading
    // `PI[19]` and comparing it to 290 by hand, which is a convention and not a check. One lookup
    // on the table already declared closes it (`minaLcAir_forces_submit_within_the_segment`).
    //
    // ⚑ **50 -> 62, 2026-08-05, in two steps that this pin did not follow.** `7a4b8ab00` split
    // `PICKLES_OK` and added the recursion seam: the `WRAP_FS_PROVED = 1` gate, ONE nine-lane
    // `proof_bind`, and nine `SUB_PI` pins (+11). `adf5aa892` published the weak-subjectivity
    // anchor's height and added its pin (+1). Byte source:
    // `LightClientMinaAir.minaLcVerifyDesc_constraint_count`, which carries 62 as a proved `rfl`.
    //
    // ⚑⚑ **62 -> 63, 2026-08-05 SECOND PASS — the SEGMENT seam.** ONE more `proof_bind`, guarded by
    // `LINK_OK` (col 8), pinned to `dregg-mina-lightclient-link::v1`'s fingerprint, with its `commit`
    // vector the row's nine PUBLISHED `TIP_STATE` columns. Nine more trace columns (49..57) and
    // **zero more public inputs**: the tip block was already published, and what changed is that a
    // constraint now names it.
    //
    // ⚑⚑⚑ **63 -> 74, 2026-08-06 — the FINALIZE-CONJUNCTION seam, and the retirement of
    // `PICKLES_WITNESSED`.** The carrier gate on col 58, ONE more nine-lane `proof_bind` pinned to
    // `dregg-mina-wrap-conjunction::v1`'s fingerprint, and NINE more `pi_binding`s — this seam
    // commits to a DIFFERENT object (the conjunction sub-proof's 160 public inputs), so unlike the
    // segment seam it could not re-use a published block and the PI count moved 30 -> 39.
    assert_eq!(d.constraints.len(), 74);
    // ⚑ And BOTH seams are present and distinguishable BY GUARD COLUMN — never by list position.
    let binds: Vec<_> = d
        .constraints
        .iter()
        .filter_map(|c| match c {
            dregg_circuit::descriptor_ir2::VmConstraint2::ProofBind(p) => Some(p),
            _ => None,
        })
        .collect();
    assert_eq!(
        binds.len(),
        3,
        "the chainlink seam, the segment seam and ⚑ the finalize-conjunction seam"
    );
    let guards: Vec<usize> = binds
        .iter()
        .map(|b| match b.guard {
            dregg_circuit::lean_descriptor_air::LeanExpr::Var(c) => c,
            _ => panic!("a seam guard must be a column"),
        })
        .collect();
    assert!(guards.contains(&WRAP_FS_PROVED) && guards.contains(&LINK_OK));
    // `range` at 24 bits (the slack teeth), `range_w29` (wire 98, the sixteen low lanes),
    // `range_w22` (wire 91, the two TOP lanes — the canonicality tooth).
    assert_eq!(d.tables.len(), 3);
    let widths: Vec<usize> = d
        .tables
        .iter()
        .map(|t| match t.sem {
            dregg_circuit::descriptor_ir2::TableSem::Range { bits } => bits,
            _ => panic!("every table of this descriptor is a range table"),
        })
        .collect();
    assert_eq!(widths, vec![24, 29, 22]);
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

/// ⚑⚑ **THE ANCHOR SUBSTITUTION IS REFUSED BY THE DESCRIPTOR — the canonicality rung, on the
/// deployed prover.**
///
/// Every column is the honest row's; the ONLY difference is that the pinned weak-subjectivity
/// anchor is the real devnet genesis hash plus one Pasta modulus, which chains to the identical tip
/// state hash. `CANON_OK` still reads `1` — a prover simply sets it, and before 2026-08-03 nothing
/// in the circuit disagreed. The 22-bit top-lane lookup on column 20 (`ANCHOR_STATE 8`) has no
/// satisfying table row: 5,514,899 >= 2^22.
///
/// ⚑ This is the carrier stopping being a witness, measured end to end: the same forged input the
/// witnessed boolean waved through is now refused by an emitted constraint.
#[test]
fn the_anchor_substitution_is_refused_by_the_descriptor() {
    let _quiet = QuietPanics::new();
    let h = honest(300, 400_000, 400_010, 290);
    assert_eq!(
        h.canon_ok, 1,
        "the forger sets the canonicality carrier to 1 — that is the whole point"
    );
    // The honest anchor is accepted with everything else identical.
    descriptor_accepts(h, &ANCHOR, &TIP)
        .expect("the genuine devnet genesis anchor must still be ACCEPTED");
    let err = descriptor_accepts(h, &SHIFTED_ANCHOR, &TIP)
        .expect_err("the +p anchor alias must be REFUSED by the descriptor, not by an executor");
    assert!(
        err.contains("wire 20"),
        "the refusal must come from the TOP-LANE table on the anchor's ninth lane, got: {err}"
    );
    eprintln!("anchor substitution refused: {err}");
}

/// The forged anchor is a LEGAL nine-lane encoding — so the refusal above is the field-canonicality
/// tooth doing work the 32-byte-string encoder gate cannot do. Lane 8 of the shifted anchor sits
/// below the encoder's `2^24` ceiling and above the Pasta `2^22` one; the honest anchor's sits below
/// both. Without this, "the shifted anchor is refused" could be a malformed-nonet accident.
#[test]
fn the_forged_anchor_passes_the_encoder_and_fails_the_field() {
    let honest_lanes = key_lanes_u32(&ANCHOR);
    let forged_lanes = key_lanes_u32(&SHIFTED_ANCHOR);
    assert!(forged_lanes[8] < (1 << 24), "a legal Faithful9 nonet");
    assert!(
        forged_lanes[8] >= (1 << 22),
        "not a canonical Pasta element"
    );
    assert!(honest_lanes[8] < (1 << 22), "the real anchor is canonical");
    // …and the low lanes are unremarkable in both, so nothing else distinguishes them.
    for i in 0..8 {
        assert!(honest_lanes[i] < (1 << 29) && forged_lanes[i] < (1 << 29));
    }
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
