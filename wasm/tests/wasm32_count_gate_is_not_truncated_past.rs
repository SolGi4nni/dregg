//! **THE `wasm32` LEG OF THE COUNT-LANE ALIAS CLOSE — measured on the target, not read.**
//!
//! The audit that specified envelope v6 said the count guard MUST sit on the envelope's integer
//! and not on a `usize`, because `wasm/src/bindings_lightclient.rs` ships `verify_history_bytes`
//! to `wasm32`, where a `usize` is **32 bits** — so `env.num_turns as usize` would truncate
//! *before* a `usize`-typed guard could ever see the value. That leg was READ, not measured; the
//! lane did not build for `wasm32`. This file measures it, running as real wasm.
//!
//! Two facts, both about THIS target:
//!
//!   1. `usize` here is 4 bytes, and `(2 + 2^32) as usize == 2` — the truncation is real, so a
//!      guard placed after that cast would have been handed the honest count and passed. This is
//!      why the v6 gate is on the `u32` inside `WholeChainProofBytes::from_postcard`, ahead of
//!      every consumer's conversion.
//!   2. The v6 decode gate actually FIRES on `wasm32`: an envelope carrying a non-canonical count
//!      is refused here, in the browser/node client, exactly as it is natively.
//!
//! Run: `wasm-pack test --node wasm -- --test wasm32_count_gate_is_not_truncated_past`

use dregg_circuit_prove::ivc_turn_chain::{
    SEG_ANCHOR_WIDTH, SEG_DIGEST_WIDTH, WHOLE_CHAIN_PROOF_ENVELOPE_V1, WholeChainProofBytes,
};
use wasm_bindgen_test::*;

// Deliberately NOT `run_in_browser`: this file is about the TARGET's integer widths and the
// decode gate, both of which are identical under node and a browser, and node needs no
// headless-browser driver to be installed for the leg to be measurable.

/// The BabyBear prime `2^31 - 2^27 + 1`.
const P: u32 = 0x7800_0001;

fn shaped_envelope(num_turns: u32) -> WholeChainProofBytes {
    WholeChainProofBytes {
        version: WHOLE_CHAIN_PROOF_ENVELOPE_V1,
        vk_fingerprint_hex: "00".repeat(32),
        root_proof: vec![0xAB; 32],
        binding_proof: vec![0xCD; 16],
        genesis_root: [1u32; SEG_ANCHOR_WIDTH],
        final_root: [2u32; SEG_ANCHOR_WIDTH],
        chain_digest: [3u32; SEG_DIGEST_WIDTH],
        num_turns,
        board_window: None,
    }
}

/// **FACT 1 — the truncation the audit read is real on this target.** A `usize`-typed guard would
/// have seen `2` and waved the forgery through.
#[wasm_bindgen_test]
fn usize_is_32_bits_here_so_a_usize_typed_guard_would_have_been_blind() {
    assert_eq!(
        core::mem::size_of::<usize>(),
        4,
        "this test is only meaningful on a 32-bit-usize target"
    );
    let forged: u64 = 2 + (1u64 << 32);
    assert_eq!(
        forged as usize, 2,
        "the v5 envelope's u64 count truncated to the HONEST count under wasm32 — which is \
         precisely why the v6 guard sits on the u32 at the decode gate and not on a usize"
    );
    // And the number the falsification lane actually measured.
    assert_eq!((2u64 + (1u64 << 32) + u64::from(P)) as usize, 2013265923);
}

/// **FACT 2 — the v6 decode gate fires in the tab.** The light client shipped to `wasm32` refuses
/// a non-canonical count at exactly the same seam it does natively.
#[wasm_bindgen_test]
fn the_v6_decode_gate_refuses_a_non_canonical_count_on_wasm32() {
    // p - 1 is canonical and must still decode: the gate is a bound, not a blanket.
    let ok = shaped_envelope(P - 1);
    let back = WholeChainProofBytes::from_postcard(&ok.to_postcard())
        .expect("a canonical count must decode on wasm32 too");
    assert_eq!(back.num_turns, P - 1);

    for bad in [P, P + 5, 2 + P, 2 + 2 * P, u32::MAX] {
        let bytes = shaped_envelope(bad).to_postcard();
        let r = WholeChainProofBytes::from_postcard(&bytes);
        assert!(
            r.is_err(),
            "REGRESSION on wasm32: num_turns = {bad} (>= p) decoded instead of being refused"
        );
    }
}

/// A v5 artifact refuses to load in the tab too — the flag day is not native-only.
#[wasm_bindgen_test]
fn a_v5_envelope_refuses_to_load_on_wasm32() {
    assert_eq!(WHOLE_CHAIN_PROOF_ENVELOPE_V1, 6);
    let mut v5 = shaped_envelope(2);
    v5.version = 5;
    assert!(
        WholeChainProofBytes::from_postcard(&v5.to_postcard()).is_err(),
        "REGRESSION: a v5 artifact loaded into a v6 wasm reader"
    );
}
