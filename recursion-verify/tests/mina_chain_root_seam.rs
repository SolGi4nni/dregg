//! ⚑⚑⚑ **THE NODE/VERIFIER SEAM, DRIVEN END TO END ON A REAL FOLD ROOT.**
//!
//! `dregg_turn::executor::mina_head_verifier` refuses every Mina anchored head until a host
//! injects a [`MinaChainRootBackend`]. This file IS that host — the same ~40 lines
//! `node/src/mina_chain_root_backend.rs` installs — and it drives the whole path over proofs it
//! mints itself:
//!
//! ```text
//!   fold  →  postcard bytes  →  decode  →  recursion_vk_fingerprint  →  verify STARK
//!         →  read chain claim  →  dregg-turn's check_chain_root_binding
//! ```
//!
//! ## ⚑⚑ THE ANCHOR THIS FILE PRINTS ROTATED ON 2026-08-08
//!
//! The phase-2 chain tower was switched to the two-engine shape: a leaf VERIFIES its IR-v2 child at
//! the descriptor engine (bit for bit the acceptance decision it always made) and MINTS at the
//! recursion engine, `log_blowup 3 / 38 queries`, which every fold and the root verify then run
//! at. The fold circuit that verifies a 38-query child is a **different circuit**, so **every
//! `recursion_vk_fingerprint` this file prints is a new value** and an operator's
//! `DREGG_MINA_CHAIN_ROOT_VK` from before that date refuses every root — fail-closed, which is the
//! correct direction. §1 and §1b are unaffected: they are about PI bytes, not proofs.
//!
//! ## ⚑ RELEASE, DELIBERATELY
//!
//! Algebraic refusals are `debug_assert` panics in debug and clean `Err(..)` in release, so a
//! refusal test that passes only in debug tests the assertion rather than the gate. Same reason
//! `mina_phase2_chain_fold.rs` says so.
//!
//! ## PREREQUISITE — the witnesses
//!
//! §2 onward need links 0..3 of the Lean-emitted chain (~150 MB, NOT tracked; ~4 minutes):
//!
//! ```text
//! cd metatheory && lake build mina_chain_emit
//! ./.lake/build/bin/mina_chain_emit ../circuit/tests/fixtures/pasta-fq-chainlink 4
//! ```
//!
//! §1 needs NO witnesses at all: the 46 PI vectors are tracked, and §1 is the claim the whole
//! weld rests on.
//!
//! Run: `cargo test -p dregg-recursion-verify --release --test mina_chain_root_seam -- --nocapture`

use std::path::PathBuf;

use dregg_circuit::field::BabyBear;
use dregg_circuit_prove::fold_vk_pin::FoldVkPins;
use dregg_circuit_prove::mina_phase2_chain_leaf::{
    CHAIN_LINKS, CHAIN_PI_COUNT, OUT_PI_LO, STATE_WIDTH, chain_inner_config, fold_chain_links,
    prove_chain_link_leaf,
};
use dregg_recursion_verify::chain_root::{chain_root_config, read_chain_claim_from_proof};
use dregg_recursion_verify::verify::{
    RecursionVk, decode_recursive_batch_proof, recursion_vk_fingerprint,
    verify_recursive_batch_proof_with_config,
};
use dregg_turn::executor::{
    MinaChainRootBackend, MinaChainRootClaim, check_chain_root_binding,
    mina_head_verifier::{
        CHAINLINK_OUT_LANES_LO, CHAINLINK_OUT_LANES_WIDTH, MINA_CHAINLINK_PI_COUNT,
    },
};

/// The 46 Lean-emitted chain-link public-input vectors, one line per link, in chain order.
const CHAIN_PIS_ALL: &str = include_str!("../../circuit/tests/fixtures/pasta-fq-chainlink-pis.txt");
/// The SEVEN-block `dregg-pasta-fq-wraplink::v1` instance's 224 public inputs. ⚑ Since 2026-08-05
/// this is NOT the sub-proof a Mina anchored head presents — the head verifier binds the eight-block
/// chainlink, whose link-45 line lives in [`CHAIN_PIS_ALL`]. It is kept here as an INDEPENDENT
/// second emission of the same closing squeeze, so §1's agreement is a two-source fact and not a
/// slice of one file compared against another slice of itself.
const WRAPLINK_PIS: &str = include_str!("../../circuit/tests/fixtures/pasta-fq-wraplink-pis.txt");
/// The seven-block layout's PI offset for its FIRST published outgoing lane (`in(3) ‖ absorbed(2) ‖
/// out(2)`), and the width it publishes: TWO lanes where the chainlink publishes three.
const WRAPLINK_OUT_LANES_LO: usize = 5 * 32;
const WRAPLINK_OUT_LANES_WIDTH: usize = 2 * 32;

// ════════════════════════════════════════════════════════════════════════════════════════════
// The backend a host injects. Byte-for-byte the body of `node/src/mina_chain_root_backend.rs`;
// duplicated HERE only so the seam is exercisable without the node's whole dependency graph.
// ════════════════════════════════════════════════════════════════════════════════════════════

#[derive(Debug, Clone, Copy)]
struct TestRootBackend {
    pinned: RecursionVk,
}

impl MinaChainRootBackend for TestRootBackend {
    fn pinned_root_vk(&self) -> [u8; 32] {
        self.pinned.0
    }

    // This suite exercises the PHASE-2 seam only; the body-fold anchor is deliberately unset
    // (all-zero), so any accidental body-root dispatch through this backend is REFUSED at
    // `check_body_chain_binding` 16a rather than silently accepted against a test pin.
    fn pinned_body_root_vk(&self) -> [u8; 32] {
        [0u8; 32]
    }

    fn verify_chain_root(
        &self,
        proof_bytes: &[u8],
    ) -> Result<([u8; 32], MinaChainRootClaim), String> {
        let proof = decode_recursive_batch_proof(proof_bytes)?;
        let measured = recursion_vk_fingerprint(&proof);
        verify_recursive_batch_proof_with_config(&proof, &chain_root_config())?;
        let claim = read_chain_claim_from_proof(&proof)
            .ok_or_else(|| "root verifies but publishes no chain claim".to_string())?;
        Ok((
            measured.0,
            MinaChainRootClaim {
                in_state: claim.in_state.iter().map(|v| v.as_u32()).collect(),
                out_state: claim.out_state.iter().map(|v| v.as_u32()).collect(),
                transcript_acc: claim.transcript_acc.iter().map(|v| v.as_u32()).collect(),
            },
        ))
    }
}

// ── fixtures ────────────────────────────────────────────────────────────────────────────────

fn all_link_pis() -> Vec<Vec<BabyBear>> {
    let pis: Vec<Vec<BabyBear>> = CHAIN_PIS_ALL
        .lines()
        .filter(|l| !l.trim().is_empty())
        .map(|l| {
            l.split_whitespace()
                .map(|c| BabyBear::new(c.parse::<u32>().expect("PI is a u32 decimal")))
                .collect()
        })
        .collect();
    assert_eq!(pis.len(), CHAIN_LINKS);
    assert!(pis.iter().all(|p| p.len() == CHAIN_PI_COUNT));
    pis
}

fn wraplink_pis() -> Vec<u32> {
    let pis: Vec<u32> = WRAPLINK_PIS
        .split_whitespace()
        .map(|c| c.parse::<u32>().expect("PI is a u32 decimal"))
        .collect();
    assert_eq!(pis.len(), 7 * 32, "seven 32-limb pin blocks");
    pis
}

fn witness_dir() -> PathBuf {
    std::env::var("DREGG_CHAINLINK_WITNESS_DIR")
        .map(PathBuf::from)
        .unwrap_or_else(|_| {
            PathBuf::from(env!("CARGO_MANIFEST_DIR"))
                .join("../circuit/tests/fixtures/pasta-fq-chainlink")
        })
}

/// Read link `j`'s Lean-emitted 2048x469 trace. Fails LOUDLY with the emit command rather than
/// skipping: a test that quietly does nothing when its input is absent is not a gate.
fn link_trace(j: usize) -> Vec<Vec<BabyBear>> {
    let path = witness_dir().join(format!("link-{j}-trace.txt"));
    let text = std::fs::read_to_string(&path).unwrap_or_else(|e| {
        panic!(
            "chain-link witness {} missing ({e}).\n\
             Emit it first (COMPILED — the interpreter costs 9m20s per link):\n  \
             cd metatheory && lake build mina_chain_emit \\\n    \
             && ./.lake/build/bin/mina_chain_emit ../circuit/tests/fixtures/pasta-fq-chainlink 4",
            path.display()
        )
    });
    let t: Vec<Vec<BabyBear>> = text
        .lines()
        .filter(|l| !l.trim().is_empty())
        .map(|l| {
            l.split_whitespace()
                .map(|c| BabyBear::new(c.parse::<u32>().expect("cell is a u32 decimal")))
                .collect()
        })
        .collect();
    assert_eq!(t.len(), 2048);
    t
}

/// Link 45's public inputs — the sub-proof a Mina anchored head presents since 2026-08-05.
fn chainlink_pis() -> Vec<u32> {
    all_link_pis()[CHAIN_LINKS - 1]
        .iter()
        .map(|v| v.as_u32())
        .collect()
}

/// The 256 sub-proof PIs with the WHOLE outgoing block replaced by `out`'s 96 limbs — the chainlink
/// instance a root over links `0..=k` would close, for a `k` that is not 45.
///
/// ⚑ 96, not 64. Under the seven-block wraplink this rewrote two of three sponge lanes and the third
/// was neither written here nor compared by `check_chain_root_binding`, so a `k != 45` root and the
/// honest one were indistinguishable in a third of the state.
fn sub_pis_landing_on(out: &[u32]) -> Vec<u32> {
    let mut pis = chainlink_pis();
    pis[CHAINLINK_OUT_LANES_LO..][..CHAINLINK_OUT_LANES_WIDTH]
        .copy_from_slice(&out[..CHAINLINK_OUT_LANES_WIDTH]);
    pis
}

// ════════════════════════════════════════════════════════════════════════════════════════════
// §1 — THE WELD'S EXPECTATION, ON THE TRACKED FIXTURES. Cheap, unconditional, and the reason
//      the expensive tests below are about anything.
// ════════════════════════════════════════════════════════════════════════════════════════════

/// ⚑⚑ **THE 46-LINK CHAIN LANDS EXACTLY WHERE THE PRESENTED SUB-PROOF LANDS — ALL THREE LANES.**
///
/// `dregg-turn`'s refusal 10 requires a root's 96 outgoing limbs to BE the Fq-transcript sub-proof's
/// pinned outgoing block. Since 2026-08-05 that sub-proof is the EIGHT-block chainlink and the
/// requirement is a whole-sponge-state identity; the offsets are checked here so a layout drift
/// (`OUT_PI_LO` vs `CHAINLINK_OUT_LANES_LO`) is a named red rather than a silent mis-slice.
///
/// ⚑ **AND THE SEVEN-BLOCK SIBLING STILL CORROBORATES, ON THE TWO LANES IT PUBLISHES.** That is the
/// half of this test with independent-source content: `MinaPhase2Chain`'s link 45 and
/// `MinaBlockFqTranscript`'s wrap link are separate emissions of the same closing squeeze of the
/// same block, and they agree limb for limb on lanes 0 and 1. ⚑ **The third lane has no second
/// source — because the wraplink never published it. That is the whole reason this rung was
/// re-pointed:** under the old binding, `claim.out_state[64..96]` was compared against nothing.
///
/// ⚑ AND THE CHAIN STARTS AT (0,0,0), which is refusal 9's expectation. Without both halves the
/// weld would be a check that can never pass on honest input — the other way to be vacuous.
#[test]
fn the_chains_last_link_lands_on_the_presented_sub_proofs_pins() {
    let chain = all_link_pis();
    let wrap = wraplink_pis();
    let sub = chainlink_pis();
    let last = &chain[CHAIN_LINKS - 1];

    let chain_out: Vec<u32> = last[OUT_PI_LO..OUT_PI_LO + STATE_WIDTH]
        .iter()
        .map(|v| v.as_u32())
        .collect();

    // The identity the weld rests on: the consumer's outgoing-block offsets ARE the leaf's.
    assert_eq!(
        (CHAINLINK_OUT_LANES_LO, CHAINLINK_OUT_LANES_WIDTH),
        (OUT_PI_LO, STATE_WIDTH),
        "the consumer reads the sub-proof's outgoing block at different offsets than the leaf \
         publishes it — one of the two layouts moved"
    );
    assert_eq!(sub.len(), MINA_CHAINLINK_PI_COUNT);
    assert_eq!(
        &chain_out[..],
        &sub[CHAINLINK_OUT_LANES_LO..][..CHAINLINK_OUT_LANES_WIDTH],
        "link 45's outgoing state is not what the presented sub-proof pins"
    );

    // ⚑ THE INDEPENDENT SOURCE: the seven-block emission agrees on the two lanes it publishes.
    assert_eq!(
        &chain_out[..WRAPLINK_OUT_LANES_WIDTH],
        &wrap[WRAPLINK_OUT_LANES_LO..][..WRAPLINK_OUT_LANES_WIDTH],
        "link 45's outgoing lanes 0/1 are not the seven-block wrap link's pinned outgoing pair — \
         two independent emissions of the same squeeze disagree"
    );

    assert!(
        chain[0][..STATE_WIDTH].iter().all(|v| v.as_u32() == 0),
        "the chain must start from a FRESH Kimchi sponge (refusal 9's expectation)"
    );
    // Non-vacuity: the state is not all-zero, so the equalities above are checking something — and
    // say it about the THIRD lane specifically, which is the one the re-point bought.
    assert!(
        chain_out[..WRAPLINK_OUT_LANES_WIDTH]
            .iter()
            .any(|v| *v != 0),
        "the outgoing pair is all-zero; the equality is checking nothing"
    );
    assert!(
        chain_out[WRAPLINK_OUT_LANES_WIDTH..]
            .iter()
            .any(|v| *v != 0),
        "the THIRD outgoing lane is all-zero; the lane this re-point added to the weld would be \
         checking nothing"
    );
    println!(
        "\n§1 ⚑⚑ link 45's outgoing state == the presented sub-proof's pinned block \
         ({CHAINLINK_OUT_LANES_WIDTH} limbs, all three lanes); the seven-block sibling \
         corroborates on {WRAPLINK_OUT_LANES_WIDTH}; link 0 starts at (0,0,0)."
    );
}

/// ⚑ And the weld's expectation is DISCRIMINATING: a root that landed one limb away is refused.
/// Pure, no fold — so the negative pole is exercised on every machine, not only where 150 MB of
/// witnesses live.
#[test]
fn a_root_landing_one_limb_away_is_refused_without_any_fold() {
    let chain = all_link_pis();
    let out: Vec<u32> = chain[CHAIN_LINKS - 1][OUT_PI_LO..OUT_PI_LO + STATE_WIDTH]
        .iter()
        .map(|v| v.as_u32())
        .collect();
    let claim = MinaChainRootClaim {
        in_state: vec![0u32; STATE_WIDTH],
        out_state: out.clone(),
        transcript_acc: vec![0u32; 8],
    };
    let sub = chainlink_pis();
    check_chain_root_binding(&[1u8; 32], &[1u8; 32], &claim, &sub)
        .expect("the honest pair must BIND");

    let mut bent = claim.clone();
    bent.out_state[3] = bent.out_state[3].wrapping_add(1);
    let err = check_chain_root_binding(&[1u8; 32], &[1u8; 32], &bent, &sub).unwrap_err();
    assert!(err.contains("does not LAND ON"), "{err}");
    println!("\n§1b ⚑ one bent limb REFUSED by the weld: {err}");
}

// ════════════════════════════════════════════════════════════════════════════════════════════
// §2 — A REAL ROOT, THROUGH THE WHOLE SEAM.
// ════════════════════════════════════════════════════════════════════════════════════════════

/// ⚑⚑⚑ **THE NODE'S PATH, ON A ROOT NOBODY HANDED IT: BOTH POLARITIES.**
///
/// Folds links 0..1 for real, serialises the root to the bytes a wire would carry, and runs the
/// injected-backend path a node runs. Then:
///
/// * **HONEST** — decoded, fingerprinted, STARK-verified, claim read, and `check_chain_root_binding`
///   BINDS against a sub-proof pinned to that root's own outgoing pair.
/// * **REFUSED (wrong circuit)** — the SAME root against a different pinned anchor is refused
///   by `dregg-turn`, naming the substitution. This is the refusal that makes
///   `recursion_vk_fingerprint` the root's identity.
/// * **REFUSED (bent bytes)** — a root whose serialised bytes were altered does not survive the
///   backend at all: the refusal is the DECODE or the STARK, never a claim read off a proof
///   nobody checked.
#[test]
fn a_real_fold_root_passes_the_nodes_path_and_a_wrong_anchor_does_not() {
    let pis = all_link_pis();
    // ⚑ TWO ENGINES: a leaf verifies its IR-v2 child at the inner engine and mints at the
    // recursion engine, so the fold — and the node's own verify — run at `chain_root_config()`.
    let inner = chain_inner_config();
    let fold_cfg = chain_root_config();

    let t0 = std::time::Instant::now();
    let l0 = prove_chain_link_leaf(&link_trace(0), &pis[0], &inner).expect("link 0 leaf");
    let l1 = prove_chain_link_leaf(&link_trace(1), &pis[1], &inner).expect("link 1 leaf");
    let root = fold_chain_links(
        &l0,
        &l1,
        &FoldVkPins::tracked(&l0, &l1).expect("both children carry a preprocessed commitment"),
        &fold_cfg,
    )
    .expect("links 0..1 fold");
    let fold_ms = t0.elapsed().as_millis();

    // The wire: a root travels as postcard bytes because `dregg-turn` does not link the type.
    let bytes = postcard::to_allocvec(&root.0).expect("a root serialises");

    // ⚑ THE ANCHOR IS EXTRACTED FROM AN HONEST FOLD — the setup party's job, done here.
    let anchor = recursion_vk_fingerprint(&root.0);
    let backend = TestRootBackend { pinned: anchor };

    // ── HONEST.
    let (measured, claim) = backend
        .verify_chain_root(&bytes)
        .expect("an honest root must verify through the node's path");
    assert_eq!(measured, anchor.0);
    assert_eq!(claim.in_state.len(), STATE_WIDTH);
    let sub = sub_pis_landing_on(&claim.out_state);
    check_chain_root_binding(&backend.pinned_root_vk(), &measured, &claim, &sub)
        .expect("an honest root that lands on the presented sub-proof must BIND");

    // ── REFUSED: the same root, a different pinned circuit.
    let mut other = anchor.0;
    other[0] ^= 0xFF;
    let err = check_chain_root_binding(&other, &measured, &claim, &sub).unwrap_err();
    assert!(err.contains("DIFFERENT circuit"), "{err}");

    // ── REFUSED: bent bytes never reach the claim.
    let mut bent = bytes.clone();
    let n = bent.len();
    bent[n / 2] ^= 0x5A;
    let bent_err = backend
        .verify_chain_root(&bent)
        .err()
        .expect("a bent root must be REFUSED by the backend");

    println!("\n§2 ⚑⚑⚑ A REAL FOLD ROOT THROUGH THE NODE'S PATH ({fold_ms} ms to mint)");
    println!("  wire bytes      : {}", bytes.len());
    println!("  RecursionVk     : {}", anchor.to_hex());
    println!("  claim           : in(96) ‖ out(96) ‖ acc(8), in-state fresh sponge");
    println!("  wrong anchor    : REFUSED — {err}");
    println!("  bent root bytes : REFUSED — {bent_err}");
}

/// ⚑ **`RecursionVk` DETERMINISM, THROUGH THE VERIFY CRATE.** Two honest folds of the same two
/// links mint the SAME fingerprint. This is the light client's distributed trust anchor and the
/// property that makes an operator-pinned `DREGG_MINA_CHAIN_ROOT_VK` reproducible at all; the
/// extraction of the fingerprint into this crate must not have moved it.
#[test]
fn the_extracted_fingerprint_is_still_deterministic() {
    let pis = all_link_pis();
    // ⚑ TWO ENGINES: a leaf verifies its IR-v2 child at the inner engine and mints at the
    // recursion engine, so the fold — and the node's own verify — run at `chain_root_config()`.
    let inner = chain_inner_config();
    let fold_cfg = chain_root_config();
    let build = || {
        let l0 = prove_chain_link_leaf(&link_trace(0), &pis[0], &inner).expect("link 0 leaf");
        let l1 = prove_chain_link_leaf(&link_trace(1), &pis[1], &inner).expect("link 1 leaf");
        fold_chain_links(
            &l0,
            &l1,
            &FoldVkPins::tracked(&l0, &l1).expect("both children carry a preprocessed commitment"),
            &fold_cfg,
        )
        .expect("links 0..1 fold")
    };
    let a = build();
    let b = build();
    assert_eq!(
        recursion_vk_fingerprint(&a.0),
        recursion_vk_fingerprint(&b.0),
        "two honest folds of the SAME chain minted different RecursionVk fingerprints — the \
         operator's pinned anchor is not reproducible"
    );
    println!(
        "\n§2b ⚑ RecursionVk STABLE across two honest folds: {}",
        recursion_vk_fingerprint(&a.0).to_hex()
    );
}

/// ⚑⚑⚑ **THE WHOLE 46-LINK ROOT, WELDED TO THE DEPLOYED SUB-PROOF'S OWN PINS.**
///
/// The full weld: fold all 46 links, then require the root to bind against the DEPLOYED
/// `pasta-fq-chainlink::v1` link-45 public inputs unmodified — no `sub_pis_landing_on` rewrite. What that
/// says, read end to end: *the sponge state the head's sub-proof consumes is the output of a
/// 46-link chain that started at (0,0,0) and absorbed block 539508's ordered tape* — the residual
/// this module's header narrows, exercised rather than described.
///
/// `#[ignore]`d for wall clock (§5 of `mina_phase2_chain_fold.rs` measured 1037 s for the same
/// tree). Needs ALL 46 witnesses. Run with:
/// `cargo test -p dregg-recursion-verify --release --test mina_chain_root_seam -- --ignored --nocapture`
#[test]
#[ignore = "the whole 46-link chain: ~17 min and all 46 witnesses. Explicit --ignored."]
fn the_whole_chain_root_binds_to_the_deployed_sub_proof() {
    let pis = all_link_pis();
    // ⚑ TWO ENGINES: a leaf verifies its IR-v2 child at the inner engine and mints at the
    // recursion engine, so the fold — and the node's own verify — run at `chain_root_config()`.
    let inner = chain_inner_config();
    let fold_cfg = chain_root_config();
    let t_all = std::time::Instant::now();

    let mut acc = prove_chain_link_leaf(&link_trace(0), &pis[0], &inner).expect("link 0 leaf");
    for j in 1..CHAIN_LINKS {
        let leaf = prove_chain_link_leaf(&link_trace(j), &pis[j], &inner)
            .unwrap_or_else(|e| panic!("link {j} leaf: {e}"));
        acc = fold_chain_links(
            &acc,
            &leaf,
            &FoldVkPins::tracked(&acc, &leaf)
                .unwrap_or_else(|e| panic!("fold at link {j} has an unpinnable child: {e}")),
            &fold_cfg,
        )
        .unwrap_or_else(|e| panic!("fold at link {j}: {e}"));
        println!(
            "  link {j:>2}/46 folded (elapsed {:.1} min)",
            t_all.elapsed().as_secs_f64() / 60.0
        );
    }

    let bytes = postcard::to_allocvec(&acc.0).expect("a root serialises");
    let anchor = recursion_vk_fingerprint(&acc.0);
    let backend = TestRootBackend { pinned: anchor };
    let (measured, claim) = backend
        .verify_chain_root(&bytes)
        .expect("the 46-link root must verify through the node's path");

    // ⚑ THE DEPLOYED SUB-PROOF'S OWN PINS, UNMODIFIED.
    check_chain_root_binding(&anchor.0, &measured, &claim, &chainlink_pis())
        .expect("the whole-chain root must BIND to the deployed wrap link's pins");

    println!("\n═══ ⚑⚑⚑ THE WHOLE PHASE-2 CHAIN ROOT, CONSUMED BY THE NODE'S PATH ═══");
    println!(
        "  46 leaves + 45 folds in {:.1} min",
        t_all.elapsed().as_secs_f64() / 60.0
    );
    println!("  RecursionVk : {}", anchor.to_hex());
    println!(
        "  pin it with : DREGG_MINA_CHAIN_ROOT_VK={}",
        anchor.to_hex()
    );
}
