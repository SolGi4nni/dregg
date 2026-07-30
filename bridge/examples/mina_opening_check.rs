//! `mina_opening_check` — **ask dregg, from a real binary, to prove it verified a Mina block.**
//!
//! ```text
//!   cargo run --release -p dregg-bridge --example mina_opening_check --features test-utils
//! ```
//!
//! The `test-utils` feature is what carries the tracked real-devnet-block fixture
//! (`metatheory/fixtures/pickles-extractors/mina_devnet_block.json`, captured 2026-07-28 from
//! `api.minascan.io`) into a non-test build. Everything downstream of the block — the descriptors,
//! the challenge vector, the witness, the prover, the verifier — is the production path.
//!
//! ## Why an example and not only a test
//!
//! This repo has a named class (`minted-uncalled-initializer-class`) where a path reachable only
//! from libtest was believed live and was not, with the FATAL banner swallowed by libtest's output
//! capture. So the ask is exercised from a real `main` too, and it prints its own refusals.
//!
//! ## Substrate, said out loud
//!
//! The AIR is LEAN-AUTHORED: `Dregg2.Circuit.Emit.PastaMsmScalarDerive.deriveRowDesc 15 10922 k 3
//! 256 MinaWrapSrsG.SRS_G`, emitted by `metatheory/EmitPastaDerive.lean`. This driver authors
//! nothing; it calls [`dregg_bridge::mina_observer::MinaObserver::prove_opening_check`].
//!
//! ## What a green run says, and what it does not
//!
//! **Says:** for the 15 IPA challenges of devnet block 539508, four chosen 3-generator slices of
//! Mina's real 32,768-point Wrap SRS fold — under the CANONICAL s-vector those challenges derive,
//! with both operands forced onto `y² = x³ + 5` and combined by the real group law — to the
//! published accumulator values; a STARK proof of that was produced and the deployed verifier
//! accepted it; and the served block was bound to that height by the verified header gate first.
//!
//! **Does not say:** that the whole `⟨s, srs.g⟩` MSM holds (12 of 32,768 generators are bound);
//! that the Wrap proof verifies (this is one leg of one of two IPA statements); or that the
//! FRI/STARK soundness floor under the proof system, or P10 (IPA opening soundness), is
//! discharged. None of those are closed by this run and it must not be read as closing them.

use dregg_bridge::mina_observer::{
    MinaBlock, MinaObserver, MinaObserverConfig, MinaRpc, MinaVerifiedHeaderAnchor,
    MinaZkappAccount, ObserveError, real_devnet_protocol_state_proof,
};
use dregg_bridge::mina_pickles::MinaWrapIndexParams;
use dregg_bridge::solana_relayer::RpcError;

/// The tracked real devnet block: height, and the Base58Check `stateHash` a node served for it.
const DEVNET_539508_B58: &str = "3NLmVB6Fs3dm4kXNkgwheHXzJXNpCCwEDe76RpTVeBTNujm12zNk";
const DEVNET_539508_PARENT_B58: &str = "3NKQvrgBGtHUHkYs9r7hL7cGRJhLDNVGL3zj4b7t9nLTCzfvXHkK";

fn main() {
    println!("── ask: prove the ⟨s, srs.g⟩ opening check for a real Mina devnet block ──\n");

    if !dregg_lean_ffi::mina_state_hash_word_ok_available() {
        eprintln!(
            "REFUSED: the Lean archive does not export the header-binding gate, so the served \
             block cannot be bound to the height whose challenges are pinned. Nothing was \
             decided. Build the archive (scripts/fetch-lean-seed.sh) and re-run."
        );
        std::process::exit(2);
    }

    let block = MinaBlock {
        state_hash: DEVNET_539508_B58.to_string(),
        parent_state_hash: DEVNET_539508_PARENT_B58.to_string(),
        block_height: 539_508,
        protocol_state_proof: real_devnet_protocol_state_proof(),
    };
    println!(
        "block   height {} · stateHash {} · protocolStateProof {} b64 chars",
        block.block_height,
        block.state_hash,
        block.protocol_state_proof.len()
    );

    let config = MinaObserverConfig {
        zkapp_address: String::new(),
        anchor_state_hash: DEVNET_539508_PARENT_B58.to_string(),
        anchor_height: 539_507,
        confirmation_depth: 1,
        wrap_index: MinaWrapIndexParams::DEVNET_BLOCKCHAIN,
        verified_header_anchor: MinaVerifiedHeaderAnchor::devnet_539508(),
    };
    let observer = MinaObserver::new(config, NoRpc);

    let t0 = std::time::Instant::now();
    match observer.prove_opening_check(std::slice::from_ref(&block)) {
        Ok(receipt) => {
            let wall = t0.elapsed();
            println!("\nPROVED AND VERIFIED.\n");
            println!("  {}", receipt.cost_line());
            println!("  observer wall clock: {wall:?}");
            println!("\n  descriptors (LEAN-AUTHORED, sha-pinned):");
            for n in &receipt.descriptor_names {
                println!("    {n}");
            }
            println!(
                "\n  challenge vector sha256 {}\n  provenance: {}",
                receipt.challenges_sha256, receipt.challenge_provenance
            );
            println!(
                "\n  ⚑ scope: 12 of 32,768 SRS generators are bound; this is ONE leg of the IPA \
                 verifier's two statements; the FRI/STARK floor and P10 are undischarged."
            );
        }
        Err(e) => {
            // ⚑ FAIL CLOSED, and the refusal is the product. Nothing here logs-and-proceeds.
            eprintln!("\nREFUSED: {e}");
            let code = match e {
                ObserveError::MinaOpeningChallengesUnavailable { .. }
                | ObserveError::VerifiedGateUnavailable { .. } => 2, // nothing was decided
                _ => 1, // a check ran and said no
            };
            std::process::exit(code);
        }
    }
}

/// The driver does not talk to a node — the block is the tracked fixture — so the transport is a
/// stub that REFUSES rather than a mock that returns plausible data.
struct NoRpc;

impl MinaRpc for NoRpc {
    fn best_chain(&self, _max_length: u32) -> Result<Vec<MinaBlock>, RpcError> {
        Err(RpcError::Transport(
            "this driver runs on a tracked block, not a live endpoint".to_string(),
        ))
    }

    fn zkapp_account(&self, _public_key: &str) -> Result<Option<MinaZkappAccount>, RpcError> {
        Err(RpcError::Transport(
            "this driver runs on a tracked block, not a live endpoint".to_string(),
        ))
    }
}
