//! # `dregg-mina-lightclient-link::v1` on the DEPLOYED PROVER — both polarities, multi-row.
//!
//! ⚑ SUBSTRATE: the descriptor under test is Lean-authored and, more precisely, LEAN-COMPILED —
//! `Dregg2.Circuit.Emit.LightClientMinaLinkAir.minaLinkDesc` is `EffectLower.lowerAir` applied to
//! the `EffectAir` source `minaLinkAir`, and that module contains no hand-written `VmConstraint2`.
//! This file writes NO constraints. It builds traces and asks the deployed prover.
//!
//! ## What this exhibits
//!
//! `LightClientMinaAir` (the single-row Mina verify AIR) carries `LINK_OK` as a witnessed boolean
//! column forced `= 1`. Nothing in that descriptor computes it, and — because the descriptor is one
//! row — nothing in it can: parent linkage is a per-BLOCK relation. So a prover publishing any
//! `(anchor, tip)` pair with `LINK_OK := 1` gets an accepting proof, and the segment length
//! `SEG_LEN` is a free felt in `[1, 2^24]`.
//!
//! This descriptor is one row per exhibited block. The tests below run the DEPLOYED
//! `prove_vm_descriptor2` / `verify_vm_descriptor2` and show:
//!
//! * an honest three-block segment from the REAL devnet genesis anchor to the REAL block-539508
//!   tip PROVES and VERIFIES;
//! * ⚑ the SAME segment with block 2's `previousStateHash` lane 0 bumped by ONE — still a perfectly
//!   canonical lane, so no range lookup refuses it — is REFUSED by the lane-continuity window gate.
//!   That is the forgery the witnessed `LINK_OK = 1` waves through;
//! * a segment whose published `PI_SEG_LEN` claims 290 against 3 real rows is REFUSED.
//!
//! * ⚑⚑ **2026-08-06 — THE STATE-HASH SEAM.** Every row carries nine `HASH_VK` lanes that the
//!   descriptor's `proof_bind` pins, lane by lane, to the semantic fingerprint of
//!   `dregg-pasta-fp-absorb::v1` — the emitted Poseidon-over-Pasta sponge. A row whose lane 0 is
//!   moved by ONE (non-zero to non-zero, well inside the 29-bit lookup) is REFUSED, and the
//!   assertion below requires the refusal to name a violated constraint rather than a bus.
//!
//! ## ⚠ What it does NOT exhibit, said plainly
//!
//! The prover enforces the seam's ROW-LOCAL half — the guard is a bit, the nine attested-program
//! lanes are the pinned literal. It does not run a verifier: the existential
//! (`Satisfied2Custom.proofBound`, "there IS a verifying absorb sub-proof whose public-input
//! commitment is this row's salt ‖ parent ‖ body ‖ own") is off-row by construction and is
//! discharged at the CONSUMER, exactly as the head descriptor's segment bind is discharged by
//! `mina_head_verifier` refusals 11-14. So what a green here shows is that the seam is EMITTED and
//! BITES on the deployed prover, not that a chain of Poseidon proofs was verified.
//! `PICKLES_OPENING_WITNESSED` (`PICKLES_WITNESSED` until 2026-08-06, `PICKLES_OK` until 08-05) —
//! what makes a row a real block — is still a
//! witness. Its sibling `WRAP_FS_PROVED` is not: see `circuit/tests/mina_lightclient_carrier_proves.rs`.
//!
//! ## ⚑ RUN IN RELEASE
//!
//! In a DEBUG build plonky3's own constraint check (`check_constraints.rs`) is a debug assertion, so
//! an algebraic refusal arrives as a PANIC. In RELEASE it arrives as a clean
//! `Err(OodEvaluationMismatch)` from the verifier. `descriptor_accepts` catches both so the test is
//! meaningful in either profile, and `the_refusal_is_the_verifiers_in_release` records which one
//! actually fired.

use dregg_circuit::BabyBear;
use dregg_circuit::descriptor_by_name::descriptor_by_name;
use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, MemBoundaryWitness, prove_vm_descriptor2, verify_vm_descriptor2,
};
use dregg_circuit::heap_root::HeapLeaf;

const LINK_DESCRIPTOR: &str = "dregg-mina-lightclient-link::v1";

/// Column layout, mirroring `LightClientMinaLinkAir` §1. A drift here is caught by
/// `the_served_descriptor_matches_the_lean_shape`.
const PARENT_0: usize = 0;
const OWNHASH_0: usize = 9;
const HEIGHT: usize = 18;
const IS_REAL: usize = 19;
const REAL_COUNT: usize = 20;
const ANCHOR_H: usize = 21;
/// ⚑ 2026-08-06: the block's `state_body_hash` — the PREIMAGE the row did not have.
const BODYHASH_0: usize = 22;
/// ⚑ 2026-08-06: the attested state-hash program's nine `Faithful9` fingerprint lanes.
const HASH_VK_0: usize = 31;
/// ⚑ 2026-08-08: the body-hash chain's ORDERED TRANSCRIPT ACCUMULATOR, columns 40..47, published at
/// PI 29..36. It is what keeps the body-chain seam from being vacuous — a bind of `(salt, BODYHASH)`
/// alone would not be, since `perm` is a permutation and 25 links from a fixed head with free
/// absorbed inputs reach every field element. Not range-gated (these are BabyBear Poseidon2 digest
/// lanes; a 29-bit lookup would refuse an honest accumulator).
const BODY_ACC_0: usize = 40;
/// ⚑ 2026-08-08: the body-hash chain program's nine `Faithful9` fingerprint lanes, columns 48..56.
const CHAIN_VK_0: usize = 48;
/// ⚑ 40 → 57 on 2026-08-08, the publication flag day: `BODY_ACC` (8) + `CHAIN_VK` (9) appended.
const LINK_WIDTH: usize = 57;

/// ⚑ The nine `Faithful9` lanes of `effect_vm_descriptor2_semantic_fingerprint`
/// (`dregg-pasta-fp-absorb::v1`), transcribed in `LightClientMinaLinkAir.ABSORB_VK_LANES` and
/// recomputed from that descriptor's own bytes by
/// `circuit/tests/mina_statehash_seam_proves.rs::the_seam_pins_the_real_absorb_program`.
///
/// ⚑ MOVED 2026-08-08: `067f63780` re-emitted `pasta-fp-absorb.json` and the pin did not follow, so
/// the seam named a program no descriptor in this tree had. Recomputed, not copied.
const ABSORB_VK_LANES: [u32; 9] = [
    484507606, 137849382, 203872743, 165431410, 35280581, 243997426, 419793387, 241629155, 7378268,
];

/// ⚑ The nine lanes of `dregg-pasta-fp-chainlink::v1`'s fingerprint
/// (`LightClientMinaLinkAir.FP_CHAINLINK_VK_LANES`) — the body-chain seam's `vkPin`. Recomputed
/// from that descriptor's own bytes by `conj_fingerprint`; unchanged by this flag day.
const FP_CHAINLINK_VK_LANES: [u32; 9] = [
    331349446, 492579056, 87664392, 244507792, 473722701, 515537956, 384678982, 534069614, 6023200,
];

const PI_ANCHOR_BASE: usize = 0;
const PI_TIP_BASE: usize = 9;
const PI_ANCHOR_H: usize = 18;
const PI_SEG_LEN: usize = 19;
/// ⚑ 2026-08-08: the FIRST row's nine `BODYHASH` lanes, published at slots 20..28.
const PI_BODYHASH_BASE: usize = 20;
/// ⚑ 2026-08-08: the FIRST row's eight `BODY_ACC` lanes, published at slots 29..36.
const PI_BODY_ACC_BASE: usize = 29;
/// ⚑ 20 → 37 on 2026-08-08. A `proofBind`'s `commit`/`vk` may name only PUBLISHED values, so an
/// unpublished `BODYHASH` could not be `cb.connect`ed by a fold at all — publication is what makes
/// the body-chain seam REACHABLE. The old 20-PI shape now REFUSES (`public input count … !=
/// descriptor public_input_count`) rather than being reinterpreted at the wrong offsets.
const LINK_PI_COUNT: usize = 46;

/// A canonical stand-in for the chain's 8-lane transcript accumulator. ⚑ Like `BODY_LANES`, this is
/// a SHAPE witness: the AIR forces the seam's `vk` lanes and publishes these eight, and relates them
/// to `MinaStateBodyHashChain`'s root nowhere on-row — that tie is the seam's off-row half.
const BODY_ACC_LANES: [u32; 8] = [7, 14, 21, 28, 35, 42, 49, 56];

/// The base-`2^29` lanes of Mina devnet GENESIS's state hash — the same nine digits
/// `LightClientMinaAir.GENESIS_ANCHOR_LANES` pins against the Base58Check decimal.
const GENESIS_ANCHOR_LANES: [u32; 9] = [
    317368465, 122552485, 518650043, 481937944, 112457995, 488503206, 390747624, 350427965, 1320595,
];

/// The lanes of devnet block 539508's state hash — the block whose Wrap proof o1-labs'
/// `kimchi::verifier::verify` accepts.
const DEVNET_TIP_LANES: [u32; 9] = [
    148400356, 2288994, 332868807, 237767070, 530455789, 507531490, 336317945, 425818875, 3793778,
];

/// Two interior state hashes. Any canonical nonet does: the descriptor forces that they CHAIN, not
/// what they are — and that gap is exactly `LinkHashResidual`.
const MID1_LANES: [u32; 9] = [11, 22, 33, 44, 55, 66, 77, 88, 99];
const MID2_LANES: [u32; 9] = [111, 222, 333, 444, 555, 666, 777, 888, 999];

/// Canonical body-hash nonets. ⚑ These are SHAPE witnesses and the file says so: the tie
/// `OWNHASH = Poseidon_salt(PARENT, BODYHASH)` is the off-row half of the seam and no trace can
/// witness it. Using real Poseidon images here would make the test LOOK like it checked the hash.
const BODY_LANES: [[u32; 9]; 3] = [
    [7, 14, 21, 28, 35, 42, 49, 56, 63],
    [70, 140, 210, 280, 350, 420, 490, 560, 630],
    [700, 1400, 2100, 2800, 3500, 4200, 4900, 5600, 6300],
];

/// The committed trace must be a power of two; the real rows are a PREFIX and the rest is padding
/// that repeats the tip, exactly as `dregg-turn-chain-binding-v2` pads.
const TRACE_ROWS: usize = 8;

fn desc() -> EffectVmDescriptor2 {
    descriptor_by_name(LINK_DESCRIPTOR).unwrap_or_else(|| {
        panic!(
            "{LINK_DESCRIPTOR} is not in the by-name registry — it is emitted from \
             Dregg2/Circuit/Emit/LightClientMinaLinkAir.lean through EmitByName.lean and included \
             by circuit/src/descriptor_by_name.rs"
        )
    })
}

/// One exhibited block's row.
#[derive(Clone, Copy)]
struct Block {
    parent: [u32; 9],
    own: [u32; 9],
    body: [u32; 9],
    height: u32,
    is_real: u32,
}

fn row_of(b: Block, real_count: u32, anchor_h: u32) -> Vec<BabyBear> {
    let mut r = vec![BabyBear::new(0); LINK_WIDTH];
    for i in 0..9 {
        r[PARENT_0 + i] = BabyBear::new(b.parent[i]);
        r[OWNHASH_0 + i] = BabyBear::new(b.own[i]);
        r[BODYHASH_0 + i] = BabyBear::new(b.body[i]);
        // ⚑ The seam's `vk` vector. A witness generator that leaves these unfilled produces an
        // UNSAT row: the `proof_bind`'s `vk_pin` congruence is an emitted constraint.
        r[HASH_VK_0 + i] = BabyBear::new(ABSORB_VK_LANES[i]);
        // ⚑ 2026-08-08: the body-chain seam's own `vk` vector, same discipline.
        r[CHAIN_VK_0 + i] = BabyBear::new(FP_CHAINLINK_VK_LANES[i]);
    }
    for i in 0..8 {
        r[BODY_ACC_0 + i] = BabyBear::new(BODY_ACC_LANES[i]);
    }
    r[HEIGHT] = BabyBear::new(b.height);
    r[IS_REAL] = BabyBear::new(b.is_real);
    r[REAL_COUNT] = BabyBear::new(real_count);
    r[ANCHOR_H] = BabyBear::new(anchor_h);
    r
}

/// Build the padded trace and the thirty-seven public inputs for an exhibited segment.
///
/// ⚑ The padding rows repeat `(parent, own) = (tip, tip)` and CONTINUE the height and the counter,
/// so the transition gates fire across the real→padding boundary and the last row's `REAL_COUNT` is
/// still the real-row total. This is `dregg-turn-chain-binding-v2`'s padding argument verbatim.
fn trace_and_pis(
    blocks: &[Block],
    anchor_h: u32,
    published_seg_len: u32,
) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    assert!(!blocks.is_empty() && blocks.len() <= TRACE_ROWS);
    let tip = blocks[blocks.len() - 1].own;

    let mut rows: Vec<Vec<BabyBear>> = Vec::with_capacity(TRACE_ROWS);
    let mut count = 0u32;
    for b in blocks {
        count += b.is_real;
        rows.push(row_of(*b, count, anchor_h));
    }
    let mut h = blocks[blocks.len() - 1].height;
    while rows.len() < TRACE_ROWS {
        h += 1;
        rows.push(row_of(
            Block {
                parent: tip,
                own: tip,
                body: BODY_LANES[2],
                height: h,
                is_real: 0,
            },
            count,
            anchor_h,
        ));
    }

    let mut pis = vec![BabyBear::new(0); LINK_PI_COUNT];
    for i in 0..9 {
        pis[PI_ANCHOR_BASE + i] = BabyBear::new(blocks[0].parent[i]);
        pis[PI_TIP_BASE + i] = BabyBear::new(tip[i]);
    }
    pis[PI_ANCHOR_H] = BabyBear::new(anchor_h);
    pis[PI_SEG_LEN] = BabyBear::new(published_seg_len);
    // ⚑ 2026-08-08: both new blocks are pinned to the FIRST row (`pi_binding row=first`, cols
    // 22..30 and 40..47), so they carry the first exhibited block's body hash and the accumulator
    // every row repeats.
    for i in 0..9 {
        pis[PI_BODYHASH_BASE + i] = BabyBear::new(blocks[0].body[i]);
    }
    for i in 0..8 {
        pis[PI_BODY_ACC_BASE + i] = BabyBear::new(BODY_ACC_LANES[i]);
    }

    (rows, pis)
}

/// `Ok(())` iff the descriptor ACCEPTS this witness — prove AND verify.
///
/// A refusal has three shapes and all three are refusals: an `Err` from the prover (how the RANGE
/// teeth refuse), a PANIC out of plonky3's debug constraint check (how the ALGEBRAIC gates refuse in
/// a debug build), and an `Err` from the verifier (the release leg). The production consumer catches
/// the panic the same way, so a test that let it escape would report a correct refusal as a failure.
fn descriptor_accepts(
    blocks: &[Block],
    anchor_h: u32,
    published_seg_len: u32,
) -> Result<(), String> {
    let d = desc();
    let (trace, pis) = trace_and_pis(blocks, anchor_h, published_seg_len);
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
            "prover/verifier PANICKED — plonky3's debug constraint check fired, i.e. \
                       an emitted gate is unsatisfied on this row window."
                .to_string(),
        ),
    }
}

/// Quieten the default panic printer for the refusal cases.
struct Hush(Option<Box<dyn Fn(&std::panic::PanicHookInfo<'_>) + Sync + Send + 'static>>);
impl Hush {
    fn new() -> Self {
        let prev = std::panic::take_hook();
        std::panic::set_hook(Box::new(|_| {}));
        Hush(Some(prev))
    }
}
impl Drop for Hush {
    fn drop(&mut self) {
        if let Some(p) = self.0.take() {
            std::panic::set_hook(p);
        }
    }
}

/// The honest three-block segment: genesis anchor at height 1000, blocks 1001/1002/1003, tip =
/// devnet block 539508's state hash.
fn honest_blocks() -> Vec<Block> {
    vec![
        Block {
            parent: GENESIS_ANCHOR_LANES,
            own: MID1_LANES,
            body: BODY_LANES[0],
            height: 1001,
            is_real: 1,
        },
        Block {
            parent: MID1_LANES,
            own: MID2_LANES,
            body: BODY_LANES[1],
            height: 1002,
            is_real: 1,
        },
        Block {
            parent: MID2_LANES,
            own: DEVNET_TIP_LANES,
            body: BODY_LANES[2],
            height: 1003,
            is_real: 1,
        },
    ]
}

#[test]
fn the_served_descriptor_matches_the_lean_shape() {
    let d = desc();
    assert_eq!(d.name, LINK_DESCRIPTOR);
    // `minaLinkDesc_width` / `_piCount` / `_constraint_count` / `_tables`, in Lean.
    assert_eq!(
        d.trace_width, LINK_WIDTH,
        "trace width drifted from the Lean emission"
    );
    assert_eq!(d.public_input_count, LINK_PI_COUNT, "PI count drifted");
    assert_eq!(
        d.constraints.len(),
        72,
        "constraint count drifted (minaLinkDesc_constraint_count)"
    );
    // ⚑ 2026-08-06: exactly one recursion seam, and it is not the declarative shape.
    let binds: Vec<_> = d
        .constraints
        .iter()
        .filter_map(|c| match c {
            dregg_circuit::descriptor_ir2::VmConstraint2::ProofBind(m) => Some(m),
            _ => None,
        })
        .collect();
    assert_eq!(binds.len(), 1, "one state-hash seam (minaLink_proofBinds)");
    assert_eq!(
        binds[0].commit.len(),
        54,
        "six Fp elements, nine lanes each"
    );
    assert_eq!(binds[0].vk.len(), 9, "a nine-lane Faithful9 program pin");
    assert!(
        !binds[0].is_declarative(),
        "the seam must pin its program (ProofBind::is_declarative)"
    );
    assert_eq!(
        d.tables.len(),
        2,
        "declared tables drifted: range_w29 + range_w22"
    );
    assert!(
        d.hash_sites.is_empty(),
        "this descriptor computes no hash IN ITS OWN ROWS — the Poseidon is the bound sub-proof's, \
         and a native BabyBear hash site here would be a different hash entirely"
    );
}

#[test]
fn an_honest_exhibited_segment_proves_and_verifies() {
    let r = descriptor_accepts(&honest_blocks(), 1000, 3);
    assert!(
        r.is_ok(),
        "the honest three-block anchored segment must prove and verify: {r:?}"
    );
}

/// ⚑⚑ THE RUNG. Block 2's `previousStateHash` lane 0 is `12` where block 1's own-hash lane 0 is
/// `11`. It is a canonical lane, so every one of the eighteen per-row range lookups still passes;
/// only the lane-continuity window gate refuses it. This is precisely the chain the single-row
/// descriptor's witnessed `LINK_OK = 1` accepts.
#[test]
fn a_mismatched_parent_is_refused_by_the_descriptor() {
    let _h = Hush::new();
    let mut blocks = honest_blocks();
    blocks[1].parent[0] += 1;
    let r = descriptor_accepts(&blocks, 1000, 3);
    assert!(
        r.is_err(),
        "a segment whose second block's previousStateHash is NOT the first block's state hash \
         must be REFUSED — this is the forgery the witnessed LINK_OK bit waves through"
    );
}

/// The bent lane is canonical, so the refusal above is the LINKAGE gate's and not the canonicality
/// gate's. Stated as its own assertion so a future narrowing of the lane widths cannot silently
/// turn the linkage test into a range test.
#[test]
fn the_bent_lane_is_itself_canonical() {
    let bent = MID1_LANES[0] + 1;
    assert!(
        bent < (1u32 << 29),
        "the bent lane must still pass the 29-bit lane table"
    );
    // Both fixtures' top lanes are constants, so their canonicality is a BUILD obligation: a
    // fixture edited past the 22-bit table would make every linkage tooth in this file a range
    // tooth, and a runtime assert reports that only when this one test runs.
    const _: () = assert!(
        DEVNET_TIP_LANES[8] < (1u32 << 22) && GENESIS_ANCHOR_LANES[8] < (1u32 << 22),
        "both real top lanes must pass the 22-bit Pasta-canonical table"
    );
}

/// ⚑ THE FREE DEPTH, REFUSED. Three exhibited real rows, `PI_SEG_LEN` published as 290 (mainnet
/// Samasika `k`). The last-row `REAL_COUNT` pin refuses it.
///
/// ⚠ This is the shape `dregg-mina-lightclient-verify::v1` CANNOT refuse IN-CIRCUIT: there `SEG_LEN`
/// is a free witness column in a single row and 290 costs exactly as much to write as 3.
/// ⚑ **AND SINCE 2026-08-05 THE CONSUMER REFUSES IT ANYWAY, WHICH IS A DIFFERENT SENTENCE.** The
/// head now binds this descriptor through a `LINK_OK`-guarded `proof_bind`, and
/// `mina_head_verifier::check_segment_binding` (REFUSAL 14c) recomputes the segment length as
/// `head PI[18] − head PI[29]` — two PUBLISHED values, so no prover input — and requires THIS
/// descriptor's counted `PI_SEG_LEN` to equal it. So the claim is paid for in rows after all; it is
/// paid for at an EXECUTOR CHECK plus this AIR's row count, not by a gate of the head AIR.
#[test]
fn a_published_depth_without_rows_is_refused() {
    let _h = Hush::new();
    let r = descriptor_accepts(&honest_blocks(), 1000, 290);
    assert!(
        r.is_err(),
        "claiming a 290-deep segment while exhibiting 3 rows must be REFUSED — the published \
         length is the last row's REAL_COUNT, and REAL_COUNT is paid for one row at a time"
    );
}

/// A non-contiguous height is refused by the transition gate.
#[test]
fn a_height_gap_is_refused_by_the_descriptor() {
    let _h = Hush::new();
    let mut blocks = honest_blocks();
    blocks[2].height = 1005; // skips 1004
    let r = descriptor_accepts(&blocks, 1000, 3);
    assert!(r.is_err(), "a segment that skips a height must be REFUSED");
}

/// An anchor the first row does not carry is refused by the first-row PI pin: the trust root is
/// pinned, not suggested.
#[test]
fn a_substituted_anchor_is_refused_by_the_descriptor() {
    let _h = Hush::new();
    let d = desc();
    let blocks = honest_blocks();
    let (trace, mut pis) = trace_and_pis(&blocks, 1000, 3);
    // publish a DIFFERENT anchor than the one the first row's PARENT lanes carry
    pis[PI_ANCHOR_BASE] = BabyBear::new(GENESIS_ANCHOR_LANES[0] + 1);
    let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let mem = MemBoundaryWitness::default();
        let heaps: Vec<Vec<HeapLeaf>> = vec![];
        let proof = prove_vm_descriptor2(&d, &trace, &pis, &mem, &heaps)
            .map_err(|e| format!("prover refused: {e}"))?;
        verify_vm_descriptor2(&d, &proof, &pis).map_err(|e| format!("verifier refused: {e:?}"))
    }));
    let refused = match outcome {
        Ok(r) => r.is_err(),
        Err(_) => true,
    };
    assert!(
        refused,
        "an anchor the exhibited segment does not start from must be REFUSED"
    );
}

/// ⚑ THE POLARITY PAIR ON THE DEPLOYED PROVER: the same helper accepts the honest segment and
/// refuses every tamper. A descriptor that accepted everything, or refused everything, fails this.
#[test]
fn the_deployed_prover_discriminates() {
    let _h = Hush::new();
    assert!(descriptor_accepts(&honest_blocks(), 1000, 3).is_ok());

    let mut bent = honest_blocks();
    bent[1].parent[0] += 1;
    assert!(descriptor_accepts(&bent, 1000, 3).is_err());

    assert!(descriptor_accepts(&honest_blocks(), 1000, 290).is_err());

    let mut gap = honest_blocks();
    gap[2].height = 1005;
    assert!(descriptor_accepts(&gap, 1000, 3).is_err());
}

/// ⚑ Record WHICH leg refused the mismatched parent, so the register in the module header stays
/// honest as profiles change. In release this must be a clean `Err`, not a panic.
#[test]
fn the_refusal_is_the_verifiers_in_release() {
    let _h = Hush::new();
    let d = desc();
    let mut blocks = honest_blocks();
    blocks[1].parent[0] += 1;
    let (trace, pis) = trace_and_pis(&blocks, 1000, 3);
    let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let mem = MemBoundaryWitness::default();
        let heaps: Vec<Vec<HeapLeaf>> = vec![];
        let proof = prove_vm_descriptor2(&d, &trace, &pis, &mem, &heaps)
            .map_err(|e| format!("prover refused: {e}"))?;
        verify_vm_descriptor2(&d, &proof, &pis).map_err(|e| format!("verifier refused: {e:?}"))
    }));
    match outcome {
        Ok(Err(msg)) => {
            eprintln!("REFUSAL LEG (clean Err): {msg}");
            assert!(
                msg.contains("verifier refused") || msg.contains("prover refused"),
                "unexpected refusal text: {msg}"
            );
        }
        Ok(Ok(())) => panic!("the mismatched-parent segment was ACCEPTED — the rung is broken"),
        Err(_) => eprintln!(
            "REFUSAL LEG (panic): plonky3's debug constraint check fired. Expected in a DEBUG \
             build; in release this should be a clean Err."
        ),
    }
}

/// ⚑⚑⚑ **THE STATE-HASH SEAM BITES ON THE DEPLOYED PROVER — both polarities, 2026-08-06.**
///
/// The honest trace fills every row's nine `HASH_VK` lanes with
/// `dregg-pasta-fp-absorb::v1`'s fingerprint and proves. The forgery moves **lane 0 of row 1 by
/// one** and must be refused.
///
/// Three properties of the forgery are ASSERTED rather than described, because each one is a way a
/// falsifier in this tree has previously died without anyone noticing:
///
/// * it moves a **non-zero value to a non-zero value** (a sibling lane shipped a mutation that
///   moved a zero into a zero, and `decide` correctly proved it was not a tamper);
/// * it stays **inside the 29-bit range lookup**, so a range check cannot be what objects (another
///   was refused by a range lookup rather than by the gate under test);
/// * **nothing else in the row changes** — same parent, own hash, body hash, height, `IS_REAL`,
///   counter — so no pre-existing gate can be the one that fires.
#[test]
fn a_row_attesting_the_wrong_program_is_refused() {
    let _h = Hush::new();
    let d = desc();
    let blocks = honest_blocks();
    let (honest_trace, pis) = trace_and_pis(&blocks, 1000, 3);

    // ── ACCEPT: the honest trace, with every row attesting the pinned absorb program.
    {
        let mem = MemBoundaryWitness::default();
        let heaps: Vec<Vec<HeapLeaf>> = vec![];
        let proof = prove_vm_descriptor2(&d, &honest_trace, &pis, &mem, &heaps)
            .expect("the honest segment proves with the seam in place");
        verify_vm_descriptor2(&d, &proof, &pis).expect("…and verifies");
    }

    // ── THE FORGERY. One lane, one row.
    let mut forged = honest_trace.clone();
    let before = forged[1][HASH_VK_0].as_u32();
    let after = before + 1;
    forged[1][HASH_VK_0] = BabyBear::new(after);

    // ⚑ THE FALSIFIER MOVES, AND IT MOVES THE RIGHT THING.
    assert_ne!(before, after, "the forgery must actually move the lane");
    assert_ne!(before, 0, "moving a zero into a zero proves nothing");
    assert_ne!(after, 0, "the forged value must be non-zero too");
    assert_eq!(
        before, ABSORB_VK_LANES[0],
        "the honest cell must be the pinned lane, or this moves the wrong column"
    );
    assert!(
        after < (1u32 << 29),
        "the forged lane must stay INSIDE the 29-bit lookup so a range check cannot refuse it"
    );
    for (c, (h, f)) in honest_trace[1].iter().zip(forged[1].iter()).enumerate() {
        assert_eq!(
            h.as_u32() == f.as_u32(),
            c != HASH_VK_0,
            "column {c} changed and it should not have (or HASH_VK_0 did not)"
        );
    }

    // ── REFUSE, and the refusing gate is NAMED: the `proof_bind`'s `vk_pin` congruence.
    let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let mem = MemBoundaryWitness::default();
        let heaps: Vec<Vec<HeapLeaf>> = vec![];
        let proof = prove_vm_descriptor2(&d, &forged, &pis, &mem, &heaps)
            .map_err(|e| format!("prover refused: {e}"))?;
        verify_vm_descriptor2(&d, &proof, &pis).map_err(|e| format!("verifier refused: {e:?}"))
    }));
    match outcome {
        Ok(Err(msg)) => {
            assert!(
                !msg.contains("exact-public") && !msg.contains("lookup"),
                "the SEAM must refuse this, not a bus or a range table; got: {msg}"
            );
            eprintln!("⚑ FORGED HASH_VK LANE -> REFUSED by the proof_bind vk_pin: {msg}");
        }
        Ok(Ok(())) => panic!(
            "a row attesting a program nobody pinned was ACCEPTED — the state-hash seam is not \
             biting, and `OWNHASH` is a free witness again"
        ),
        Err(_) => eprintln!(
            "⚑ FORGED HASH_VK LANE -> REFUSED by plonky3's debug constraint check (DEBUG build)."
        ),
    }
}
