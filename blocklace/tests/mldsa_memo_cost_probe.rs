//! A STOPWATCH for the ML-DSA-65 memo, plus the byte-identity it must not cost.
//!
//! `Block::new` derives an ML-DSA-65 key per block; a [`Blocklace`] authoring through
//! its HELD identity does not. Both paths survive, so this measures them side by side
//! IN ONE PROCESS on identical inputs — no cross-tree comparison, no build skew.
//!
//! # What is asserted and what is only printed
//!
//! The ASSERTIONS are byte-identity: the memoised path and the one-shot path must
//! agree on `creator`, the ed25519 signature and the block `id()`, and each block's
//! PQ half must verify under the enrolled key. Those are exact and cannot flake.
//!
//! The TIMINGS are PRINTED, never asserted. A stopwatch threshold on a shared,
//! co-tenanted build box is a flake generator, and the transferable quantity here is
//! the KEYGEN COUNT — which is structural, and is pinned by the `Arc::ptr_eq`
//! liveness tests in `finality.rs` instead. Read the numbers with:
//!
//! ```text
//! cargo nextest run -p dregg-blocklace --test mldsa_memo_cost_probe --no-capture
//! ```
//!
//! ⚠ The number you get depends on WHICH keygen answered. With the Lean-verified
//! real keygen core installed (`dregg-pq-testkit`, as here) it is the extracted
//! `mldsaKeygenInternal` across the FFI; without one it is the `fips204` crate
//! fallback, which is ~1000× cheaper and would make this probe look pointless. Say
//! which one you measured when you quote it.

use std::time::Instant;

use dregg_blocklace::finality::{Block, Blocklace, Payload};
use dregg_blocklace::signer::HybridBlockSigner;
use ed25519_dalek::SigningKey;

/// Blocks authored per timed sample. Small on purpose: at ~0.5 s per keygen the
/// one-shot arm is the slow one, and this probe must not become a heavy test.
const N: u64 = 8;

fn key() -> SigningKey {
    SigningKey::from_bytes(&[0x5Au8; 32])
}

#[test]
fn per_block_authorship_cost_one_shot_versus_held_identity() {
    // This is an INTEGRATION test, so `dregg-blocklace` is compiled without
    // `cfg(test)` and its two internal install points do not fire. Install the
    // Lean-verified PQ cores here, or `dregg-pq` aborts the process on the first
    // ML-DSA op.
    dregg_pq_testkit::install_or_panic();

    let k = key();
    let enrolled = Block::pq_public_key(&k);

    // ── Arm A: ONE-SHOT. `Block::new` from a bare seed — an ML-DSA keygen per block.
    let t0 = Instant::now();
    let mut one_shot_blocks = Vec::new();
    for seq in 1..=N {
        one_shot_blocks.push(Block::new(&k, seq, Payload::Data(vec![seq as u8]), vec![]));
    }
    let one_shot = t0.elapsed();

    // ── Arm B: HELD IDENTITY. A `Blocklace` derives once at construction; every
    //    block after that is a signature, not a keygen.
    let t1 = Instant::now();
    let mut lace = Blocklace::new(k.clone(), 1);
    let lace_construction = t1.elapsed();
    let t2 = Instant::now();
    let mut held_blocks = Vec::new();
    for seq in 1..=N {
        held_blocks.push(Block::new_signed_by(
            lace.signer(),
            seq,
            Payload::Data(vec![seq as u8]),
            vec![],
        ));
    }
    let held = t2.elapsed();

    // ── The identity accessors: `self_creator()` was a full keygen, now a field read.
    let t3 = Instant::now();
    for _ in 0..N {
        std::hint::black_box(Block::hybrid_id(&k));
    }
    let hybrid_id_one_shot = t3.elapsed();
    let t4 = Instant::now();
    for _ in 0..N {
        std::hint::black_box(lace.self_creator());
    }
    let self_creator_held = t4.elapsed();

    // ── A bare keygen, for scale.
    let t5 = Instant::now();
    std::hint::black_box(HybridBlockSigner::new(k.clone()));
    let one_keygen = t5.elapsed();

    // ── And the full local-authoring path through the lace (signs + inserts).
    let t6 = Instant::now();
    for seq in 1..=N {
        lace.add_block(Payload::Data(vec![seq as u8]));
    }
    let lace_add_block = t6.elapsed();

    println!("── ML-DSA-65 memo cost probe (verified Lean keygen core INSTALLED) ──");
    println!("  one ML-DSA keygen (HybridBlockSigner::new) : {one_keygen:>10.3?}");
    println!("  Blocklace::new (pays the ONE keygen)       : {lace_construction:>10.3?}");
    println!();
    println!(
        "  {N} blocks, Block::new (one-shot, 1 keygen/blk) : {one_shot:>10.3?}  ({:.3?}/blk)",
        one_shot / N as u32
    );
    println!(
        "  {N} blocks, held identity (0 keygens)           : {held:>10.3?}  ({:.3?}/blk)",
        held / N as u32
    );
    println!(
        "  {N} blocks, lace.add_block (sign + insert)      : {lace_add_block:>10.3?}  ({:.3?}/blk)",
        lace_add_block / N as u32
    );
    println!();
    println!("  {N}× Block::hybrid_id (one-shot, 1 keygen)      : {hybrid_id_one_shot:>10.3?}");
    println!("  {N}× lace.self_creator() (field read)           : {self_creator_held:>10.3?}");
    println!("────────────────────────────────────────────────────────────────────");

    // ── THE ASSERTIONS: byte-identity. Never a timing threshold.
    for (i, (a, b)) in one_shot_blocks.iter().zip(held_blocks.iter()).enumerate() {
        assert_eq!(a.creator, b.creator, "block {i}: HYBRID creator differs");
        assert_eq!(a.ed25519, b.ed25519, "block {i}: ed25519 half differs");
        assert_eq!(
            a.signature, b.signature,
            "block {i}: ed25519 signature differs — ed25519 is deterministic, so the SIGNED \
             CONTENT differs"
        );
        assert_eq!(a.id(), b.id(), "block {i}: canonical block id differs");
        assert!(
            a.verify_hybrid(&enrolled).is_ok(),
            "block {i}: one-shot block fails hybrid verification"
        );
        assert!(
            b.verify_hybrid(&enrolled).is_ok(),
            "block {i}: held-identity block fails hybrid verification"
        );
    }
}
