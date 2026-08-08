//! ⚑⚑ **THE 46-PERMUTATION Fq TRANSCRIPT OF A REAL MINA BLOCK, FOLDED.**
//!
//! `MinaBlockFqTranscript` §6.1: *"a chain of 46 instances welded by input/output pin equality is
//! the shape that closes it, **and it is not built here**."* This file is where it is built and
//! measured.
//!
//! ## WHAT EACH TEST ESTABLISHES
//!
//! * **§0** — the emitted claims chain, host-side: link `j`'s outgoing public-input block IS link
//!   `j+1`'s incoming block, the stream absorbed across all 46 links is exactly the block's real
//!   91-element tape, and link 0 starts from a fresh sponge. This is cheap and it is what the
//!   expensive tests are proving *about*, so it runs first and unconditionally.
//! * **§1** — TWO links fold, and the parent claim's endpoints span both.
//! * **§2** — FOUR links fold, and the parent claim is indistinguishable in shape from a leaf's —
//!   which is what makes the node composable to any depth.
//! * **§3 (both polarities, RELEASE)** — a TAMPERED link is REFUSED, and the refusing gate is
//!   named. Two distinct tampers, because they are refused by two different things.
//! * **§4** — `RecursionVk` determinism: an honest re-fold of the same chain mints the SAME
//!   fingerprint. That is a shipped property (`recursion_vk_determinism.rs` calls it *"the light
//!   client's distributed trust anchor"*) and this file must not break it.
//! * **§5** — the whole 46-link chain. `#[ignore]`d for wall-clock only.
//!
//! ## ⚑⚑ THE TOWER IS TWO ENGINES DEEP SINCE 2026-08-08, AND EVERY NUMBER BELOW MOVED
//!
//! A chain leaf VERIFIES its IR-v2 child at the descriptor engine (`chain_inner_config()`,
//! `log_blowup 6 / 19 queries` — bit-for-bit the acceptance decision it always made) and MINTS at
//! the recursion engine (`chain_root_config()`, `log_blowup 3 / 38 queries`), which every fold and
//! the root verify then run at. Both are reached by iterating `recursion_layer_over`; **no test
//! below names a FRI constant.** §1 asserts the switch on the ARTIFACTS it mints — emitted query
//! count, committed Merkle depth, and the node's refusal at the descriptor engine — because a
//! config object being right is what was already true while the predecessor of this change was
//! inert.
//!
//! ⚠ **The 1 037 s recorded for §5 was measured at the single-engine shape and is RETRACTED as a
//! figure for the tower that exists now.** ⚠ **Every chain-root VK rotates**; an operator's
//! `DREGG_MINA_CHAIN_ROOT_VK` must be re-extracted from an honest fold.
//!
//! **MEASURED 2026-08-08 at the split** (96 GiB M2 Max, load ~110, six sibling proving lanes):
//! §0–§4 ran **8/8 in 349.3 s**; §1's two leaves took 37.5 s and its fold 23.3 s. ⚑ The 46-leaf
//! fold this file's §5 builds was run to completion by `mina_kimchi_verifier_gadget.rs` §4 on the
//! same day through the identical `prove_chain_fold` and the same 46 witnesses: **1 192 660 ms,
//! root verified**, committed `|D⁽⁰⁾| = 2^21` over a `2^18` trace where the single-engine shape
//! would have committed `2^24`. ⚠ **That wall clock is NOT comparable to the 1 037 s baseline** —
//! this box was carrying a load average near 110 and the baseline's load was never recorded. The
//! controlled same-binary before/after lives in `mina_towers_mint_at_their_own_engine.rs`.
//!
//! ## ⚑ RELEASE, DELIBERATELY
//!
//! Algebraic refusals are `debug_assert` panics in debug and clean `Err(..)` in release, so a
//! refusal test that passes only in debug tests the assertion rather than the gate. Same reason
//! `pasta_fq_wrap_transcript_proves.rs` says so.
//!
//! ## PREREQUISITE — the witnesses
//!
//! The 46 traces are ~150 MB and are NOT tracked. Emit them (compiled; the interpreter costs 9 min
//! 20 s *per link*):
//!
//! ```text
//! cd metatheory && lake build mina_chain_emit
//! # §1-§4 reach only links 0..3 -- ~4 MINUTES, and the whole fold gate goes live:
//! ./.lake/build/bin/mina_chain_emit ../circuit/tests/fixtures/pasta-fq-chainlink 4
//! # §5 (the whole chain) needs all 46 -- ~45 min:
//! ./.lake/build/bin/mina_chain_emit ../circuit/tests/fixtures/pasta-fq-chainlink
//! ```
//!
//! ⚑ **THE PARTIAL EMIT IS THE POINT OF THE `count` ARGUMENT.** A fold gate that needs 45 minutes
//! of rendering before it can run at all is a gate every machine reports RED and everyone learns to
//! ignore. Four links is four minutes. The 46 PI vectors ARE tracked (`pasta-fq-chainlink-pis.txt`),
//! so §0 -- the claim that the 46 emitted witnesses ARE the block's chain -- runs with no emit at all.
//!
//! Run: `cargo test -p dregg-circuit-prove --release --test mina_phase2_chain_fold -- --nocapture`

use std::path::PathBuf;
use std::time::Instant;

use dregg_circuit::field::BabyBear;
use dregg_circuit_prove::fold_vk_pin::FoldVkPins;
use dregg_circuit_prove::mina_phase2_chain_leaf::{
    ABSORBED_PI_LO, ABSORBED_WIDTH, CHAIN_CLAIM_LEN, CHAIN_LINKS, CHAIN_PI_COUNT, OUT_PI_LO, SK,
    STATE_WIDTH, chain_inner_config, chain_link_descriptor, chain_root_config, fold_chain_links,
    host_chain_transcript_acc, prove_chain_link_leaf, read_chain_claim,
};
use dregg_circuit_prove::plonky3_recursion_impl::recursive::{
    recursion_vk_fingerprint, verify_recursive_batch_proof_with_config,
};

/// The 46 Lean-emitted public-input vectors, one line per link, in chain order. TRACKED — small,
/// and the object §0's continuity claim is about.
const CHAIN_PIS_ALL: &str = include_str!("../../circuit/tests/fixtures/pasta-fq-chainlink-pis.txt");

/// The block's own `v′` (polyscale) and `u′` (evalscale), from `mina_real_block_proof.json` via
/// `MinaBlockFqTranscript.WRAP_{V,U}_CHAL`. Mina devnet block 539508, state hash
/// `3NLmVB6Fs3dm4kXNkgwheHXzJXNpCCwEDe76RpTVeBTNujm12zNk`.
const WRAP_V_CHAL: u128 = 330305781815358857211111367912836029937;
const WRAP_U_CHAL: u128 = 25455272712921947007977874297033672595;

fn witness_dir() -> PathBuf {
    std::env::var("DREGG_CHAINLINK_WITNESS_DIR")
        .map(PathBuf::from)
        .unwrap_or_else(|_| {
            PathBuf::from(env!("CARGO_MANIFEST_DIR"))
                .join("../circuit/tests/fixtures/pasta-fq-chainlink")
        })
}

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
    assert_eq!(
        pis.len(),
        CHAIN_LINKS,
        "the block's tape costs 46 permutations"
    );
    assert!(
        pis.iter().all(|p| p.len() == CHAIN_PI_COUNT),
        "every link carries {CHAIN_PI_COUNT} public inputs"
    );
    pis
}

/// Read link `j`'s Lean-emitted 2048x469 trace. Fails LOUDLY with the emit command rather than
/// skipping: a test that quietly does nothing when its input is absent is not a gate.
fn link_trace(j: usize) -> Vec<Vec<BabyBear>> {
    let path = witness_dir().join(format!("link-{j}-trace.txt"));
    let text = std::fs::read_to_string(&path).unwrap_or_else(|e| {
        panic!(
            "chain-link witness {} missing ({e}).\n\
             Emit the witnesses first (COMPILED — the interpreter costs 9m20s per link).\n  \
             §1-§4 need only links 0..3, which is ~4 MINUTES:\n  \
             cd metatheory && lake build mina_chain_emit \\\n    \
             && ./.lake/build/bin/mina_chain_emit ../circuit/tests/fixtures/pasta-fq-chainlink 4\n  \
             (omit the `4` for all 46, which §5 needs.)",
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
    assert_eq!(t.len(), 2048, "the Lean-emitted link is 2048 rows");
    assert!(t.iter().all(|r| r.len() == 469), "every row is 469 wide");
    t
}

/// The FRI shape of an EMITTED artifact, read off the proof rather than off a config field.
/// `log_lde_domain` is the tallest committed matrix's Merkle authentication-path length; this
/// tower's `cap_height` is 0, so path length IS tree depth IS `degree_bits + mint log_blowup`.
struct EmittedFri {
    num_queries: usize,
    log_lde_domain: usize,
    max_degree_bits: usize,
}

fn emitted_fri(
    out: &p3_recursion::RecursionOutput<
        dregg_circuit_prove::plonky3_recursion_impl::recursive::DreggRecursionConfig,
    >,
) -> EmittedFri {
    let fri = &out.0.proof.opening_proof;
    EmittedFri {
        num_queries: fri.query_proofs.len(),
        log_lde_domain: fri
            .query_proofs
            .iter()
            .flat_map(|q| q.input_proof.iter())
            .map(|b| b.opening_proof.len())
            .max()
            .unwrap_or(0),
        max_degree_bits: out.0.proof.degree_bits.iter().copied().max().unwrap_or(0),
    }
}

/// `Result::expect_err` needs `T: Debug`, and a `RecursionOutput` is not. This says the same thing
/// and keeps the refusal message the assertion is about.
fn expect_refusal<T>(r: Result<T, String>, must: &str) -> String {
    match r {
        Ok(_) => panic!("{must}"),
        Err(e) => e,
    }
}

/// Little-endian 8-bit limbs -> the value.
fn limbs_to_u128_low(limbs: &[BabyBear]) -> u128 {
    limbs
        .iter()
        .take(16)
        .enumerate()
        .fold(0u128, |acc, (i, v)| acc | ((v.as_u32() as u128) << (8 * i)))
}

// ============================================================================
// §0 — THE EMITTED CLAIMS CHAIN. Cheap, unconditional, and what everything below is about.
// ============================================================================

/// ⚑ **THE 46 EMITTED CLAIMS ARE A CHAIN**, and it is the block's chain.
///
/// This is `MinaPhase2Chain.the_emitted_claims_are_continuous` on the wire: link `j`'s outgoing
/// state block is link `j+1`'s incoming state block, limb for limb. Plus the two ends: link 0 comes
/// out of a FRESH Kimchi sponge, and link 45's outgoing lanes 0/1 truncate to the challenges that
/// block's `proof.oracles(…)` returned.
#[test]
fn the_forty_six_emitted_claims_are_the_blocks_chain() {
    let pis = all_link_pis();

    for j in 0..CHAIN_LINKS - 1 {
        assert_eq!(
            &pis[j][OUT_PI_LO..OUT_PI_LO + STATE_WIDTH],
            &pis[j + 1][..STATE_WIDTH],
            "link {j}'s outgoing state is not link {}'s incoming state -- the emitted witnesses \
             are not a chain",
            j + 1
        );
    }

    assert!(
        pis[0][..STATE_WIDTH].iter().all(|v| v.as_u32() == 0),
        "link 0 must start from a FRESH Kimchi sponge (0,0,0); a chain that starts anywhere else \
         is a sentence about a transcript nobody checked"
    );

    let last = &pis[CHAIN_LINKS - 1];
    assert_eq!(
        limbs_to_u128_low(&last[OUT_PI_LO..OUT_PI_LO + SK]),
        WRAP_V_CHAL,
        "the chain's final lane 0 does not truncate to block 539508's v' (polyscale)"
    );
    assert_eq!(
        limbs_to_u128_low(&last[OUT_PI_LO + SK..OUT_PI_LO + 2 * SK]),
        WRAP_U_CHAL,
        "the chain's final lane 1 does not truncate to block 539508's u' (evalscale)"
    );
    // Non-vacuity of the truncation: the raw squeezes have HIGH limbs, so the low 16 are a genuine
    // prefix of a 254-bit value and not a 128-bit number padded out.
    assert!(
        last[OUT_PI_LO + 16..OUT_PI_LO + SK]
            .iter()
            .any(|v| v.as_u32() != 0),
        "the raw v' squeeze is only 128 bits wide -- the truncation is checking nothing"
    );

    // ⚑ AND EXACTLY ONE ELEMENT IS ABSORBED BY THE LAST LINK. The tape is 91 elements — odd — so
    // the closing squeeze's second rate slot is the sponge's own no-op. Without this pin the chain
    // would be a sentence about a 92nd absorbed element nobody checked.
    assert!(
        last[ABSORBED_PI_LO + SK..ABSORBED_PI_LO + ABSORBED_WIDTH]
            .iter()
            .all(|v| v.as_u32() == 0),
        "the closing squeeze's second absorb slot must be pinned to zero"
    );

    println!("\n═══ §0  THE 46 EMITTED CLAIMS ARE A CHAIN ═══");
    println!("  45 joints: out(j) == in(j+1), limb for limb");
    println!("  link 0 in-state  : FRESH Kimchi sponge (0,0,0)");
    println!("  link 45 out-lane0: v' = {WRAP_V_CHAL}");
    println!("  link 45 out-lane1: u' = {WRAP_U_CHAL}");
    println!("  both read from `mina_real_block_proof.json`, which openmina's BlockVerifier and");
    println!("  o1-labs' `kimchi::verifier::verify` accepted before it was written.");
}

/// The Lean-emitted descriptor is the one this module's layout constants describe, and it runs the
/// deployed wrap link's ROM cell for cell — so `pasta_fq_wrap_transcript_proves.rs` §9's check of
/// the `fq_kimchi` constants against o1-labs' `static_params()` is a check of THESE instances too.
#[test]
fn the_chain_descriptor_runs_the_deployed_wrap_links_rom() {
    use dregg_circuit::descriptor_ir2::{TableSem, parse_vm_descriptor2};

    let chain = chain_link_descriptor().expect("the Lean chain-link descriptor parses");
    let wrap = parse_vm_descriptor2(include_str!(
        "../../circuit/descriptors/by-name/pasta-fq-wraplink.json"
    ))
    .expect("the deployed wrap-link descriptor parses");

    let rom = |d: &dregg_circuit::descriptor_ir2::EffectVmDescriptor2| {
        d.tables
            .iter()
            .find_map(|t| match &t.sem {
                TableSem::ExactPublicRows { rows } => Some(rows.clone()),
                _ => None,
            })
            .expect("the machine declares an instruction ROM")
    };

    assert_eq!(
        rom(&chain),
        rom(&wrap),
        "the chain link must run the SAME 2048-instruction ROM as the deployed wrap link -- the \
         same 55x3 `fq_kimchi` round constants, as descriptor cells"
    );
    assert_eq!(chain.trace_width, wrap.trace_width);
    assert_eq!(chain.public_input_count, 256);
    assert_eq!(
        wrap.public_input_count, 224,
        "the deployed link pins 7 blocks; the chain link pins 8 -- the third OUTGOING lane is the \
         one that makes it chainable"
    );
    println!(
        "\n§0b chain link ROM == deployed wrap link ROM (2048 rows), +32 PIs for the third \
         outgoing lane."
    );
}

// ============================================================================
// §1..§2 — THE FOLD. Small first: 2, then 4.
// ============================================================================

/// ⚑⚑ **§1 — TWO LINKS FOLD, AND THE STATE IS CARRIED INSIDE THE RECURSION.**
///
/// The parent claim's incoming state is link 0's and its outgoing state is link 1's. That equality
/// is not compared host-side: `fold_chain_links` `connect`s link 0's 96 outgoing limbs to link 1's
/// 96 incoming limbs in-circuit, so a chain that does not join has no satisfying assignment.
#[test]
fn two_links_fold_into_one_claim() {
    let pis = all_link_pis();
    // ⚑ TWO ENGINES, AND THEY ARE NOT THE SAME OBJECT ANY MORE: a leaf VERIFIES its IR-v2
    // child at the inner engine and MINTS at the recursion engine; a fold verifies what the
    // leaf emitted, so it runs at the root config. Both are tower accessors, neither is a
    // named FRI constant.
    let inner = chain_inner_config();
    let fold_cfg = chain_root_config();

    let t0 = Instant::now();
    let l0 = prove_chain_link_leaf(&link_trace(0), &pis[0], &inner).expect("link 0 leaf");
    let l1 = prove_chain_link_leaf(&link_trace(1), &pis[1], &inner).expect("link 1 leaf");
    let leaves_ms = t0.elapsed().as_millis();

    let t1 = Instant::now();
    let node = fold_chain_links(
        &l0,
        &l1,
        &FoldVkPins::tracked(&l0, &l1).expect("both children carry a preprocessed commitment"),
        &fold_cfg,
    )
    .expect("links 0..1 fold");
    let fold_ms = t1.elapsed().as_millis();

    verify_recursive_batch_proof_with_config(&node.0, &fold_cfg).expect("the folded node verifies");

    // ⚑ THE SWITCH, READ OFF THE TWO ARTIFACTS THIS TEST JUST MINTED — not off a config field.
    // A config object being right is exactly what was already true while the split was inert.
    for (label, art) in [("leaf", &l0), ("fold node", &node)] {
        let e = emitted_fri(art);
        println!(
            "  {label:<10} EMITTED {} query proofs, committed LDE 2^{} (trace 2^{})",
            e.num_queries, e.log_lde_domain, e.max_degree_bits
        );
        assert_eq!(
            e.num_queries, 38,
            "the chain {label} emitted {} query proofs; 19 means it minted at its CHILD's engine \
             and the 8x is not in this tower",
            e.num_queries
        );
        assert_eq!(
            e.log_lde_domain,
            e.max_degree_bits + 3,
            "the chain {label} committed 2^{} over a 2^{} trace; the split mint blowup is 8x, the \
             deployed one was 64x",
            e.log_lde_domain,
            e.max_degree_bits
        );
    }
    // …and the node REFUSES at the inner engine. Without this the two assertions above could be
    // two labels on one object rather than a claim that two distinct engines exist.
    assert!(
        verify_recursive_batch_proof_with_config(&node.0, &inner).is_err(),
        "a 38-query chain node must NOT verify under the 19-query IR-v2 descriptor engine"
    );

    let claim = read_chain_claim(&node).expect("the node publishes a chain claim");
    assert_eq!(
        claim.in_state,
        pis[0][..STATE_WIDTH],
        "parent in == link 0 in"
    );
    assert_eq!(
        claim.out_state,
        pis[1][OUT_PI_LO..OUT_PI_LO + STATE_WIDTH],
        "parent out == link 1 out"
    );
    assert_eq!(
        claim.transcript_acc,
        host_chain_transcript_acc(&pis[..2]),
        "the folded transcript digest must be the host fold of the two links' absorbed pairs"
    );

    println!("\n§1 ⚑⚑ TWO LINKS FOLDED. 2 leaves {leaves_ms} ms, 1 fold {fold_ms} ms.");
    println!("  the parent spans link 0's incoming state to link 1's outgoing state,");
    println!("  and the join was enforced by 96 in-circuit `connect`s, not a host comparison.");
}

/// ⚑ **§2 — FOUR LINKS FOLD, AND THE PARENT IS SHAPED LIKE A LEAF.** The node's claim has exactly
/// [`CHAIN_CLAIM_LEN`] lanes whether it wraps 1 link or 46, which is what lets the same node
/// compose to any depth — the property that turns "too big for one instance" into a tree.
#[test]
fn four_links_fold_into_one_claim() {
    let pis = all_link_pis();
    // ⚑ TWO ENGINES, AND THEY ARE NOT THE SAME OBJECT ANY MORE: a leaf VERIFIES its IR-v2
    // child at the inner engine and MINTS at the recursion engine; a fold verifies what the
    // leaf emitted, so it runs at the root config. Both are tower accessors, neither is a
    // named FRI constant.
    let inner = chain_inner_config();
    let fold_cfg = chain_root_config();

    let t0 = Instant::now();
    let mut acc = prove_chain_link_leaf(&link_trace(0), &pis[0], &inner).expect("link 0 leaf");
    for j in 1..4 {
        let leaf = prove_chain_link_leaf(&link_trace(j), &pis[j], &inner)
            .unwrap_or_else(|e| panic!("link {j} leaf: {e}"));
        acc = fold_chain_links(
            &acc,
            &leaf,
            &FoldVkPins::tracked(&acc, &leaf)
                .expect("both children carry a preprocessed commitment"),
            &fold_cfg,
        )
        .unwrap_or_else(|e| panic!("fold at link {j}: {e}"));
    }
    let total_ms = t0.elapsed().as_millis();

    verify_recursive_batch_proof_with_config(&acc.0, &fold_cfg).expect("the 4-link root verifies");

    let claim = read_chain_claim(&acc).expect("the root publishes a chain claim");
    assert_eq!(
        claim.in_state.len() + claim.out_state.len() + 8,
        CHAIN_CLAIM_LEN
    );
    assert_eq!(claim.in_state, pis[0][..STATE_WIDTH]);
    assert_eq!(claim.out_state, pis[3][OUT_PI_LO..OUT_PI_LO + STATE_WIDTH]);
    assert_eq!(claim.transcript_acc, host_chain_transcript_acc(&pis[..4]));

    println!(
        "\n§2 ⚑ FOUR LINKS FOLDED in {total_ms} ms; the root claim is {CHAIN_CLAIM_LEN} lanes,"
    );
    println!("  the SAME shape a single leaf publishes -- so depth costs nothing in claim width.");
}

// ============================================================================
// §3 — BOTH POLARITIES. A tampered link is refused, and the refusing gate is named.
// ============================================================================

/// ⚑⚑ **§3 — A BROKEN JOIN IS REFUSED BY THE FOLD'S `connect`, IN RELEASE.**
///
/// Fold link 0 with link **2**. Both are honest links of the real tape and both leaves prove: link
/// 2's own execution is impeccable. What is false is only that link 2 continues link 0 — link 1 is
/// missing. The 96 `cb.connect`s between link 0's outgoing lanes and link 2's incoming lanes are
/// then a witness CONFLICT, and there is no parent proof.
///
/// ⚑ **AND IT IS THE FOLD THAT REFUSES, NOT THE LEAVES.** Both leaves are built successfully first
/// and that is asserted, so this cannot pass because a leaf failed for an unrelated reason.
#[test]
fn a_skipped_link_is_refused_by_the_folds_connect() {
    let pis = all_link_pis();
    // ⚑ TWO ENGINES, AND THEY ARE NOT THE SAME OBJECT ANY MORE: a leaf VERIFIES its IR-v2
    // child at the inner engine and MINTS at the recursion engine; a fold verifies what the
    // leaf emitted, so it runs at the root config. Both are tower accessors, neither is a
    // named FRI constant.
    let inner = chain_inner_config();
    let fold_cfg = chain_root_config();

    let l0 = prove_chain_link_leaf(&link_trace(0), &pis[0], &inner)
        .expect("link 0 is an honest link and its leaf MUST prove");
    let l2 = prove_chain_link_leaf(&link_trace(2), &pis[2], &inner)
        .expect("link 2 is an honest link and its leaf MUST prove -- the lie is only the JOIN");

    let err = expect_refusal(
        fold_chain_links(
            &l0,
            &l2,
            &FoldVkPins::tracked(&l0, &l2).expect("both children carry a preprocessed commitment"),
            &fold_cfg,
        ),
        "a chain that skips link 1 must be REFUSED by the fold",
    );
    println!("\n§3 ⚑ BROKEN JOIN REFUSED BY THE FOLD: {err}");
    assert!(
        !err.contains("exact-public"),
        "the ROM must be SILENT about the transcript state -- the in-circuit CONNECT is what \
         refuses a broken join; got: {err}"
    );
    // The honest join proves, so the refusal above is about the JOIN and not about link 2.
    let l1 = prove_chain_link_leaf(&link_trace(1), &pis[1], &inner).expect("link 1 leaf");
    fold_chain_links(
        &l0,
        &l1,
        &FoldVkPins::tracked(&l0, &l1).expect("both children carry a preprocessed commitment"),
        &fold_cfg,
    )
    .expect("the HONEST join must still fold");
    println!("  …and the honest join (0,1) folds, so the refusal is the join and not the link.");
}

/// ⚑ **§3b — A FORGED ABSORBED ELEMENT IS REFUSED BY THE LEAF'S PI PIN**, and the ROM is silent
/// about it — the pole inversion `MinaWrapVerifierSponge` §9 names, inherited by every chain link.
/// The absorbed value is a REGISTER operand with a zero immediate, so no ROM tuple mentions it.
#[test]
fn a_forged_absorbed_element_is_refused_by_the_pin() {
    let pis = all_link_pis();
    let inner = chain_inner_config();

    let mut forged = pis[0].clone();
    // Stay INSIDE the declared 8-bit range so a range lookup can never be what refuses.
    forged[ABSORBED_PI_LO] = BabyBear::new((forged[ABSORBED_PI_LO].as_u32() + 1) % 256);

    let err = expect_refusal(
        prove_chain_link_leaf(&link_trace(0), &forged, &inner),
        "an absorbed element that is not the tape's must be REFUSED",
    );
    println!("\n§3b ⚑ FORGED ABSORBED TAPE ELEMENT REFUSED AT THE LEAF: {err}");
    assert!(
        !err.contains("exact-public"),
        "the ROM must be SILENT about WHICH value is absorbed -- the boundary PIN is the whole of \
         the transcript binding; got: {err}"
    );
}

/// ⚑ **§3c — AND A FORGED HANDED-ON STATE IS REFUSED.** Claim link 0 produced a state it did not.
/// This is the tamper the SEVEN-block descriptor could not catch on its third lane, which is the
/// defect `MinaPhase2Chain` exists to fix.
#[test]
fn a_forged_outgoing_state_is_refused_at_the_third_lane() {
    let pis = all_link_pis();
    let inner = chain_inner_config();

    // Lane 2 of the OUTGOING state — the lane `MinaBlockFqTranscript.linkPins` never pinned.
    let slot = OUT_PI_LO + 2 * SK;
    let mut forged = pis[0].clone();
    forged[slot] = BabyBear::new((forged[slot].as_u32() + 1) % 256);

    let err = expect_refusal(
        prove_chain_link_leaf(&link_trace(0), &forged, &inner),
        "a third outgoing lane the machine did not compute must be REFUSED",
    );
    println!("\n§3c ⚑ FORGED THIRD OUTGOING LANE REFUSED: {err}");
    assert!(
        !err.contains("exact-public"),
        "the ROM must be SILENT about the handed-on state; got: {err}"
    );
}

// ============================================================================
// §4 — RecursionVk determinism: a shipped property this must not break.
// ============================================================================

/// ⚑ **§4 — AN HONEST RE-FOLD OF THE SAME CHAIN MINTS THE SAME `RecursionVk` FINGERPRINT.**
///
/// `recursion_vk_determinism.rs` calls that fingerprint *"the light client's distributed trust
/// anchor"*. A fold whose circuit shape wobbled between runs would mint a different anchor for the
/// same history and every downstream verifier would diverge. Measured here on the chain fold.
#[test]
fn the_chain_folds_recursion_vk_is_deterministic() {
    let pis = all_link_pis();
    // ⚑ TWO ENGINES, AND THEY ARE NOT THE SAME OBJECT ANY MORE: a leaf VERIFIES its IR-v2
    // child at the inner engine and MINTS at the recursion engine; a fold verifies what the
    // leaf emitted, so it runs at the root config. Both are tower accessors, neither is a
    // named FRI constant.
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
        "two honest folds of the SAME chain minted different RecursionVk fingerprints -- the light \
         client's trust anchor is not deterministic"
    );
    assert_eq!(
        read_chain_claim(&a).expect("claim a"),
        read_chain_claim(&b).expect("claim b"),
        "…and the claims must agree too"
    );
    println!(
        "\n§4 ⚑ RecursionVk fingerprint STABLE across two honest folds: {:?}",
        recursion_vk_fingerprint(&a.0)
    );
}

// ============================================================================
// §5 — THE WHOLE CHAIN.
// ============================================================================

/// ⚑⚑⚑ **§5 — THE WHOLE PHASE-2 TRANSCRIPT OF MINA DEVNET BLOCK 539508, IN ONE CLAIM.**
///
/// 46 leaves, 45 folds, one root. Read end to end the root says: *starting from a fresh Kimchi
/// sponge, absorbing exactly the block's ordered 91-element `fq_kimchi` tape, 46 emitted
/// `absorbProg` executions chain to a state whose first two lanes' low 128 bits are the `v′` and
/// `u′` that block's own `proof.oracles(…)` returned.*
///
/// ⚑ **AND THE TREE IS CHEAPER THAN THE LEAVES SUGGEST.** Measured in §1/§2: a leaf is **12.5 s**
/// and a fold is **11.3 s** — a 2-to-1 recursion node costs LESS than the IR2 leaf it aggregates,
/// because it verifies two constant-size recursive proofs rather than a 2048x469 batch. So the
/// whole tree is `46 x 12.5 + 45 x 11.3` = **~18 min**, not the hours a per-instance reading of the
/// 207 MB witness figure implied. That is the number the residual should always have been priced
/// against.
///
/// ⚑ **RUN, 2026-08-05, AT THE SINGLE-ENGINE SHAPE: 1037 s (17.3 min), root verified**, steady
/// state ~9.5 s leaf + ~11.5 s fold. ⚠ **That is a number about an object this tower no longer
/// contains** — since 2026-08-08 the leaf mints at `log_blowup 3` and the whole tree commits an 8×
/// smaller domain per layer. It is kept as the BASELINE it is, labelled, and not carried forward.
///
/// `#[ignore]`d for wall clock only. Run it with:
/// `cargo test -p dregg-circuit-prove --release --test mina_phase2_chain_fold -- --ignored --nocapture`
#[test]
#[ignore = "the whole 46-link chain. Baseline at the OLD single-engine shape was 17.3 min. Explicit --ignored."]
fn the_whole_phase2_transcript_folds_into_one_claim() {
    let pis = all_link_pis();
    // ⚑ TWO ENGINES, AND THEY ARE NOT THE SAME OBJECT ANY MORE: a leaf VERIFIES its IR-v2
    // child at the inner engine and MINTS at the recursion engine; a fold verifies what the
    // leaf emitted, so it runs at the root config. Both are tower accessors, neither is a
    // named FRI constant.
    let inner = chain_inner_config();
    let fold_cfg = chain_root_config();
    let t_all = Instant::now();

    let mut acc = {
        let t = Instant::now();
        let leaf = prove_chain_link_leaf(&link_trace(0), &pis[0], &inner).expect("link 0 leaf");
        println!("  link  0/46 leaf {:>6} ms", t.elapsed().as_millis());
        leaf
    };
    for j in 1..CHAIN_LINKS {
        let t = Instant::now();
        let leaf = prove_chain_link_leaf(&link_trace(j), &pis[j], &inner)
            .unwrap_or_else(|e| panic!("link {j} leaf: {e}"));
        let leaf_ms = t.elapsed().as_millis();
        let t = Instant::now();
        acc = fold_chain_links(
            &acc,
            &leaf,
            &FoldVkPins::tracked(&acc, &leaf)
                .expect("both children carry a preprocessed commitment"),
            &fold_cfg,
        )
        .unwrap_or_else(|e| panic!("fold at link {j}: {e}"));
        println!(
            "  link {j:>2}/46 leaf {leaf_ms:>6} ms  fold {:>6} ms  (elapsed {:.1} min)",
            t.elapsed().as_millis(),
            t_all.elapsed().as_secs_f64() / 60.0
        );
    }

    verify_recursive_batch_proof_with_config(&acc.0, &fold_cfg)
        .expect("the 46-link chain root verifies");
    let claim = read_chain_claim(&acc).expect("the root publishes a chain claim");

    // The two ends, and the tape between them.
    assert!(
        claim.in_state.iter().all(|v| v.as_u32() == 0),
        "the root's incoming state must be the FRESH Kimchi sponge"
    );
    assert_eq!(
        limbs_to_u128_low(&claim.out_state[..SK]),
        WRAP_V_CHAL,
        "the root's outgoing lane 0 does not truncate to block 539508's v'"
    );
    assert_eq!(
        limbs_to_u128_low(&claim.out_state[SK..2 * SK]),
        WRAP_U_CHAL,
        "the root's outgoing lane 1 does not truncate to block 539508's u'"
    );
    assert_eq!(
        claim.transcript_acc,
        host_chain_transcript_acc(&pis),
        "the root's transcript digest is not the ordered commitment to the block's real tape -- \
         the chain absorbed something else"
    );

    println!("\n═══ §5 ⚑⚑⚑ THE WHOLE PHASE-2 TRANSCRIPT, PROVED AS ONE CLAIM ═══");
    println!("  mina devnet block 539508, Wrap proof, phase-2 (`fq_kimchi`) sponge");
    println!(
        "  46 leaves + 45 folds in {:.1} min",
        t_all.elapsed().as_secs_f64() / 60.0
    );
    println!("  in  : FRESH Kimchi sponge (0,0,0)");
    println!("  tape: 91 elements, ordered, committed in-circuit");
    println!("  out : v' = {WRAP_V_CHAL}");
    println!("        u' = {WRAP_U_CHAL}");
    println!(
        "  the state was carried by 45 x 96 in-circuit `connect`s -- not re-pinned host-side."
    );
}
