//! **THE COUNT-LANE ALIAS — measured open, then CLOSED. This file is now the REGRESSION TOOTH.**
//!
//! ## What this probe measured when it was written (commit `c80ee7c92`)
//!
//! An audit READ the whole-chain verify path and claimed the count lane aliased on the wire. The
//! probe MEASURED it, against a real 2-turn fold, and the audit was right:
//!
//!   * `WholeChainProofBytes.num_turns` was a `u64`;
//!   * `verify_whole_chain_proof_bytes` passed `env.num_turns as usize`;
//!   * both comparison sites build `BabyBear::new(num_turns as u32)` — the binding-descriptor
//!     scalar tooth and the segment tooth;
//!   * `BabyBear::new` reduces mod p and `as u32` truncates mod 2^32;
//!   * every `num_turns < BABY_BEAR_MODULUS` guard in the file sat on a `turns.len()` PROVER
//!     site — **none on a verify path**.
//!
//! Result: **12/12 admitted.** `n + p`, `n + 2p`, `n + 2^32`, `n + 2^32 + p` each passed all four
//! teeth on the envelope, the blob seam and the in-memory verifier, with no key, no proving and no
//! witness — while the control `n + 1` was refused, so it was attributable to modular aliasing and
//! not a dead tooth.
//!
//! ## The fix (envelope v6) and what this file asserts NOW
//!
//! **The assertions below are DELIBERATELY INVERTED from the confirming form.** They are not
//! edited to match observed behaviour: each one now states the REFUSAL the fix owes, so a
//! regression that re-opens the alias fails here loudly instead of passing quietly.
//!
//!   * `WholeChainProofBytes.num_turns` is a `u32` and the envelope version is **6**. The `2^32`
//!     family is dead BY TYPE — not representable on the wire at all — and
//!     [`wire_u64_shaped_count_is_not_even_decodable`] measures that at the BYTES, not in Rust's
//!     type system.
//!   * `WholeChainProofBytes::from_postcard` refuses `num_turns >= p` — the one decode gate every
//!     wire consumer passes, sitting on the `u32` and not a `usize` (under `wasm32` a `usize` is
//!     32 bits, so an `as usize` would already have truncated).
//!   * `verify_turn_chain_recursive_from_parts_with_board_window` refuses it too, covering the
//!     in-memory verifier and the `pg-dregg` blob seam, which take the count as a bare `usize`
//!     and pass no decode gate.
//!
//! The honest baseline must still be ADMITTED — a guard that refuses everything is not a fix, and
//! the control `n + 1` must still be refused by the segment tooth (not by the new bound), so the
//! measurement stays attributable to the same place it always was.
//!
//! SLOW leg: one real recursion fold (~minutes). Run with:
//!   cargo test -p dregg-circuit-prove --test num_turns_alias_probe -- --ignored --nocapture
//! The FAST legs (decode gate, wire shape) run in the default set and need no fold.

use dregg_circuit::effect_vm::{CellState, Effect};
use dregg_circuit_prove::ivc_turn_chain::{
    FinalizedTurn, SEG_ANCHOR_WIDTH, SEG_DIGEST_WIDTH, TurnChainError,
    WHOLE_CHAIN_PROOF_ENVELOPE_V1, WholeChainProof, WholeChainProofBytes,
    prove_turn_chain_recursive, verify_turn_chain_recursive,
    verify_turn_chain_recursive_from_blobs, verify_whole_chain_proof_bytes,
};
use dregg_circuit_prove::joint_turn_aggregation::DescriptorParticipant;
use dregg_turn_prover::rotation_witness::mint_rotated_participant_leg;

/// The BabyBear prime `2^31 - 2^27 + 1` — the modulus `BabyBear::new` reduces by.
const P: u64 = 0x7800_0001;

fn open_permissions() -> dregg_cell::Permissions {
    use dregg_cell::AuthRequired;
    dregg_cell::Permissions {
        send: AuthRequired::None,
        receive: AuthRequired::None,
        set_state: AuthRequired::None,
        set_permissions: AuthRequired::None,
        set_verification_key: AuthRequired::None,
        increment_nonce: AuthRequired::None,
        delegate: AuthRequired::None,
        access: AuthRequired::None,
    }
}

fn producer_cell(balance: i64, nonce: u64) -> dregg_cell::Cell {
    let mut pk = [0u8; 32];
    pk[0] = 7;
    let mut cell = dregg_cell::Cell::with_balance(pk, [0u8; 32], balance);
    cell.permissions = open_permissions();
    for _ in 0..nonce {
        let _ = cell.state.increment_nonce();
    }
    cell
}

/// The audited Bucket-F rotated mint fixture (verbatim from
/// `recursion_vk_determinism.rs` / `ivc_turn_chain_rotated.rs`).
fn make_turn(balance: u64, nonce: u32, amount: u64) -> FinalizedTurn {
    let state = CellState::new(balance, nonce);
    let effects = vec![Effect::Transfer {
        amount,
        direction: 1,
    }];
    let before_cell = producer_cell(balance as i64, nonce as u64);
    let after_cell = producer_cell((balance as i64) - (amount as i64), nonce as u64);
    let receipt_log: Vec<[u8; 32]> = vec![[1u8; 32], [2u8; 32]];
    let leg = mint_rotated_participant_leg(
        &state,
        &effects,
        &before_cell,
        &after_cell,
        &dregg_circuit::heap_root::empty_heap_root_8(),
        &dregg_circuit::heap_root::empty_heap_root_8(),
        &receipt_log,
        None,
    )
    .expect("rotated leg mints");
    FinalizedTurn::new(DescriptorParticipant::rotated(leg))
}

/// Two continuous transfer turns — the smallest chain the fold accepts.
fn the_chain() -> Vec<FinalizedTurn> {
    vec![make_turn(1000, 0, 7), make_turn(1000 - 7, 1, 7)]
}

// ============================================================================
// FAST LEG 1 — the decode gate, on a hand-built envelope (no fold needed).
// ============================================================================

/// A shape-valid envelope with placeholder proof blobs. The count gate in `from_postcard` runs
/// AFTER the emptiness checks and BEFORE any cryptographic tooth, so a fixture with opaque
/// non-empty blobs measures exactly the gate and nothing else.
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

/// **THE DECODE GATE.** `num_turns >= p` never gets past `from_postcard`, and `p - 1` still does
/// — the bound is exact, not a blanket refusal.
#[test]
fn decode_gate_refuses_a_non_canonical_count_and_admits_p_minus_1() {
    // p - 1 is the largest count the field lane can carry faithfully: it DECODES.
    let ok = shaped_envelope((P - 1) as u32);
    let back = WholeChainProofBytes::from_postcard(&ok.to_postcard())
        .expect("p-1 is a canonical count and must decode (the gate is a bound, not a blanket)");
    assert_eq!(back.num_turns, (P - 1) as u32);

    // p, p+5, and the honest count's own aliases are all REFUSED at decode.
    for bad in [
        P as u32,           // == p: aliases 0
        (P as u32) + 5,     // > p: aliases 5
        (2 + P) as u32,     // the measured forgery: aliases the honest 2-turn count
        (2 + 2 * P) as u32, // and its second multiple
        u32::MAX,           // the top of what the v6 field can hold at all
    ] {
        let bytes = shaped_envelope(bad).to_postcard();
        match WholeChainProofBytes::from_postcard(&bytes) {
            Err(TurnChainError::EnvelopeDecode { reason }) => {
                println!("[decode gate] num_turns = {bad}: REFUSED — {reason}");
                assert!(
                    reason.contains("BabyBear modulus"),
                    "the refusal must name the count bound, got: {reason}"
                );
            }
            other => panic!(
                "REGRESSION: num_turns = {bad} (>= p) decoded instead of being refused: {other:?}"
            ),
        }
    }
}

// ============================================================================
// FAST LEG 2 — "dead by type" measured AT THE WIRE, not in Rust's type system.
// ============================================================================

/// The v5 field layout with the old `u64` count, so a `2^32`-family forgery can actually be
/// SERIALIZED and offered to the decoder. Everything else is v6's exact field order.
#[derive(serde::Serialize)]
struct U64CountShapedEnvelope {
    version: u16,
    vk_fingerprint_hex: String,
    root_proof: Vec<u8>,
    binding_proof: Vec<u8>,
    genesis_root: [u32; SEG_ANCHOR_WIDTH],
    final_root: [u32; SEG_ANCHOR_WIDTH],
    chain_digest: [u32; SEG_DIGEST_WIDTH],
    num_turns: u64,
    board_window: Option<(Vec<u32>, Vec<u32>)>,
}

/// **THE `2^32` FAMILY IS DEAD AT THE BYTES.** "Killed by type" is a claim about Rust; this
/// measures it about the WIRE. Bytes carrying a `u64`-shaped count above `u32::MAX` — exactly what
/// the old envelope admitted — do not decode into a v6 envelope at all.
#[test]
fn wire_u64_shaped_count_is_not_even_decodable() {
    for (label, n) in [
        ("n + 2^32", 2u64 + (1u64 << 32)),
        ("n + 2^32 + p", 2u64 + (1u64 << 32) + P),
        ("u64::MAX", u64::MAX),
    ] {
        let forged = U64CountShapedEnvelope {
            version: WHOLE_CHAIN_PROOF_ENVELOPE_V1,
            vk_fingerprint_hex: "00".repeat(32),
            root_proof: vec![0xAB; 32],
            binding_proof: vec![0xCD; 16],
            genesis_root: [1u32; SEG_ANCHOR_WIDTH],
            final_root: [2u32; SEG_ANCHOR_WIDTH],
            chain_digest: [3u32; SEG_DIGEST_WIDTH],
            num_turns: n,
            board_window: None,
        };
        let bytes = postcard::to_allocvec(&forged).expect("the forged shape encodes");
        let r = WholeChainProofBytes::from_postcard(&bytes);
        println!("[wire] {label} = {n}: {r:?}");
        assert!(
            r.is_err(),
            "REGRESSION: a u64-shaped count {label} = {n} decoded into a v6 envelope"
        );
    }
}

/// **THE FLAG DAY IS FINDABLE.** A v5 artifact (the shape that carried the alias) refuses to load
/// rather than being reinterpreted — it does not silently become a v6 envelope with a truncated
/// count.
#[test]
fn a_v5_envelope_refuses_to_load() {
    assert_eq!(
        WHOLE_CHAIN_PROOF_ENVELOPE_V1, 6,
        "the count-lane alias close is envelope v6"
    );
    let mut v5 = shaped_envelope(2);
    v5.version = 5;
    match WholeChainProofBytes::from_postcard(&v5.to_postcard()) {
        Err(TurnChainError::EnvelopeDecode { reason }) => {
            println!("[flag day] v5 artifact: REFUSED — {reason}");
            assert!(reason.contains("version"), "got: {reason}");
        }
        other => panic!("REGRESSION: a v5 artifact loaded into a v6 reader: {other:?}"),
    }
}

// ============================================================================
// SLOW LEG — the original measurement, against a REAL fold, with every
// assertion inverted to the refusal the fix owes.
// ============================================================================

/// **THE MEASUREMENT, INVERTED.** One honest fold; then the count edited on the wire, with no
/// re-proving and no other change — exactly what a relayer can do. Every representable alias must
/// now be REFUSED, on all three seams (envelope, blob, in-memory), while the honest artifact still
/// verifies and the control still fails for the reason it always did.
#[test]
#[ignore = "SLOW: one real recursion fold (~minutes); run with --ignored --nocapture"]
fn wire_num_turns_aliases_mod_p_and_mod_2_32() {
    let turns = the_chain();
    let honest_n = turns.len() as u32;
    let mut whole: WholeChainProof =
        prove_turn_chain_recursive(&turns).expect("the 2-turn rotated chain folds");
    assert_eq!(whole.num_turns as u32, honest_n);
    let vk = whole.root_vk_fingerprint();

    let bytes = whole.to_bytes();
    let env = WholeChainProofBytes::from_postcard(&bytes).expect("the honest envelope decodes");
    assert_eq!(env.num_turns, honest_n);

    // BASELINE: the honest artifact still verifies over the wire. A bound that refused this would
    // not be a fix, and everything below would be unattributable.
    let baseline = verify_whole_chain_proof_bytes(&bytes, &vk);
    println!("[baseline] num_turns = {honest_n}: {baseline:?}");
    baseline.expect("the honest artifact must verify (else the probe measured nothing)");

    // THE REPRESENTABLE ALIASES. `n + 2^32` and `n + 2^32 + p` are gone from this table because
    // the v6 `u32` cannot hold them — that leg is measured at the bytes by
    // `wire_u64_shaped_count_is_not_even_decodable`, not asserted here.
    let aliases: [(&str, u32); 2] = [
        ("n + p", honest_n + P as u32),
        ("n + 2p", honest_n + 2 * (P as u32)),
    ];

    let mut admitted = Vec::new();
    for (label, n) in aliases {
        let mut bad = env.clone();
        bad.num_turns = n;
        let bad_bytes = bad.to_postcard();
        let r = verify_whole_chain_proof_bytes(&bad_bytes, &vk);
        println!("[envelope] {label} = {n}: {r:?}");
        if r.is_ok() {
            admitted.push(("envelope", label, n));
        }

        // The lower blob seam (`pg-dregg`'s entry) takes the count as a `usize` directly and
        // passes NO decode gate — it is covered by the verifier-core bound, not the envelope one.
        let rb = verify_turn_chain_recursive_from_blobs(
            &bad.root_proof,
            &bad.binding_proof,
            &bad.genesis_root,
            &bad.final_root,
            &bad.chain_digest,
            n as usize,
            &vk.0,
        );
        println!("[blobs]    {label} = {n}: {rb:?}");
        if rb.is_ok() {
            admitted.push(("blobs", label, n));
        }
    }

    // The IN-MEMORY verifier reads a `usize` field with no wire in front of it.
    for (label, n) in aliases {
        let honest = whole.num_turns;
        whole.num_turns = n as usize;
        let r = verify_turn_chain_recursive(&whole, &vk);
        println!("[in-mem]   {label} = {n}: {r:?}");
        if r.is_ok() {
            admitted.push(("in-mem", label, n));
        }
        whole.num_turns = honest;
    }

    // THE CONTROL: `honest_n + 1` is a genuinely different field element, BELOW p, so it sails
    // through the new bound and must be refused by the SEGMENT TOOTH — the same place it was
    // refused before the fix. If it were admitted, the teeth would be dead and nothing above
    // would be attributable to the bound.
    {
        let mut bad = env.clone();
        bad.num_turns = honest_n + 1;
        let r = verify_whole_chain_proof_bytes(&bad.to_postcard(), &vk);
        println!("[control]  n + 1 = {}: {r:?}", honest_n + 1);
        match r {
            Err(TurnChainError::ClaimedPublicsUnattested { ref reason }) => assert!(
                !reason.contains("BabyBear modulus"),
                "the control must still be refused by the SEGMENT TOOTH, not by the new count \
                 bound — otherwise the bound is masking a dead tooth: {reason}"
            ),
            other => panic!(
                "NOT ATTRIBUTABLE: the control n+1 did not fail at the publics tooth: {other:?}"
            ),
        }
    }

    // THE VERDICT, INVERTED. The confirming form of this file asserted `admitted.len() == 4`.
    assert!(
        admitted.is_empty(),
        "REGRESSION — the count-lane alias is OPEN again on {} seam/case pair(s): {:?}. A relayer \
         can inflate a history's length by editing one integer, with no key, no proving and no \
         witness.",
        admitted.len(),
        admitted
    );
    println!(
        "\nADMITTED ALIASES: 0/{} — the alias is CLOSED",
        aliases.len()
    );
}
