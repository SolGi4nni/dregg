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
//! ## ⚠ What it does NOT exhibit, said plainly
//!
//! Nothing here forces a row's `OWNHASH` nonet to BE the Poseidon-over-Pasta hash of that block's
//! state row (`LightClientMinaLinkAir.LinkHashResidual`). A prover free to choose `OWNHASH` can
//! fabricate a consistent chain of any length between any two `Fp` elements. What this removes is
//! the freedom to be INCONSISTENT and the freedom to claim a depth without committing rows for it.
//! `PICKLES_WITNESSED` (`PICKLES_OK` until 2026-08-05) — what makes a row a real block — is still a
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
const LINK_WIDTH: usize = 22;

const PI_ANCHOR_BASE: usize = 0;
const PI_TIP_BASE: usize = 9;
const PI_ANCHOR_H: usize = 18;
const PI_SEG_LEN: usize = 19;
const LINK_PI_COUNT: usize = 20;

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
    height: u32,
    is_real: u32,
}

fn row_of(b: Block, real_count: u32, anchor_h: u32) -> Vec<BabyBear> {
    let mut r = vec![BabyBear::new(0); LINK_WIDTH];
    for i in 0..9 {
        r[PARENT_0 + i] = BabyBear::new(b.parent[i]);
        r[OWNHASH_0 + i] = BabyBear::new(b.own[i]);
    }
    r[HEIGHT] = BabyBear::new(b.height);
    r[IS_REAL] = BabyBear::new(b.is_real);
    r[REAL_COUNT] = BabyBear::new(real_count);
    r[ANCHOR_H] = BabyBear::new(anchor_h);
    r
}

/// Build the padded trace and the twenty public inputs for an exhibited segment.
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
            height: 1001,
            is_real: 1,
        },
        Block {
            parent: MID1_LANES,
            own: MID2_LANES,
            height: 1002,
            is_real: 1,
        },
        Block {
            parent: MID2_LANES,
            own: DEVNET_TIP_LANES,
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
        53,
        "constraint count drifted (minaLinkDesc_constraint_count)"
    );
    assert_eq!(
        d.tables.len(),
        2,
        "declared tables drifted: range_w29 + range_w22"
    );
    assert!(
        d.hash_sites.is_empty(),
        "this descriptor computes no hash — that is the residual"
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
    assert!(
        DEVNET_TIP_LANES[8] < (1u32 << 22) && GENESIS_ANCHOR_LANES[8] < (1u32 << 22),
        "both real top lanes must pass the 22-bit Pasta-canonical table"
    );
}

/// ⚑ THE FREE DEPTH, REFUSED. Three exhibited real rows, `PI_SEG_LEN` published as 290 (mainnet
/// Samasika `k`). The last-row `REAL_COUNT` pin refuses it.
///
/// ⚠ This is the shape `dregg-mina-lightclient-verify::v1` CANNOT refuse: there `SEG_LEN` is a free
/// witness column in a single row and 290 costs exactly as much to write as 3.
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
