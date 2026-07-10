//! TIER-C ADMIT/REFUSE TEETH — a REAL whole-chain IVC proof routed through
//! `pg-dregg`'s SQL-crossable transport and verified by the `tier-c` proof gate.
//!
//! The default (circuit-free) `cargo test` proves only the SAFE direction of the
//! gate: a well-formed-but-placeholder transport attests NOTHING
//! (`attest::well_formed_transport_attests_nothing_fail_closed`). That is correct
//! discipline, but it leaves the ADMIT polarity of the `tier-c` verifier untested —
//! "a genuine proof, packed as `SerializedWholeChainProof`, is ACCEPTED by
//! `verify_serialized_proof`, returning the bound window publics".
//!
//! This file closes that polarity with a REAL fold:
//!
//!   1. build a continuous K-turn finalized chain over real producer witnesses
//!      (the ROTATED leg `mint_rotated_participant_leg` mints — the same recipe the
//!      wasm light-client demo and `circuit/tests/ivc_turn_chain_rotated.rs` use);
//!   2. fold it with `dregg_circuit::ivc_turn_chain::prove_turn_chain_recursive`;
//!   3. project the verify-sufficient subset into `pg-dregg`'s
//!      [`SerializedWholeChainProof`] transport with the SAME mapping the S2
//!      producer documents (`postcard(&whole.root.0)` + `postcard(&whole.binding_proof)`
//!      + `BabyBear → [u8;32]` little-endian publics);
//!   4. drive `pg_dregg::attest::verify_serialized_proof` and assert it ATTESTS the
//!      true publics — then assert two TAMPERS are REFUSED (a relabeled `final_root`
//!      hint bites the carried-publics tooth; a wrong VK anchor bites the VK pin).
//!
//! It is the `pg-dregg`-side dual of the circuit's
//! `whole_chain_proof_bytes_roundtrip_and_tamper` (which already exercises the same
//! real blobs through `verify_turn_chain_recursive_from_blobs` — the exact function
//! `verify_serialized_proof` calls under `tier-c`). Here the boundary under test is
//! `pg-dregg`'s thin wrapper: transport postcard-decode → `le32` publics unpack →
//! `from_blobs`.
//!
//! SLOW: a real recursion fold (~minutes). `#[ignore]` by default; run with
//!   `cargo test --features tier-c --test tier_c_real_proof -- --ignored --nocapture`
//!
//! This whole file compiles ONLY under `--features tier-c` (it needs the circuit /
//! turn / cell crates the gate links); the default `cargo test` skips it and stays
//! postgres- and circuit-free.
#![cfg(feature = "tier-c")]

use dregg_circuit::effect_vm::{CellState, Effect};
use dregg_circuit::field::BabyBear;
use dregg_circuit_prove::ivc_turn_chain::{
    prove_turn_chain_recursive, FinalizedTurn, WholeChainProof,
};
use dregg_circuit_prove::joint_turn_aggregation::DescriptorParticipant;
use dregg_turn::rotation_witness::mint_rotated_participant_leg;

use pg_dregg::attest::{verify_serialized_proof, SerializedWholeChainProof, VkAnchor};

// ---- the real-chain fixtures (the proven recipe from the wasm light-client demo
//      and circuit/tests/ivc_turn_chain_rotated.rs) ----------------------------

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

/// The transfer actor cell at `(balance, nonce)` with open permissions.
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

/// Build a continuous K-turn chain whose ROTATED state-commit roots chain
/// (`new_root[i] == old_root[i+1]` — the temporal tooth). Returns the turns.
fn make_chain(k: usize, step: u64) -> Vec<FinalizedTurn> {
    let start_balance: u64 = step.saturating_mul(k as u64).saturating_add(1_000_000);
    let mut turns: Vec<FinalizedTurn> = Vec::with_capacity(k);
    let mut balance = start_balance;
    // The rotated trace welds balance/nonce from the v1 sub-trace, which BUMPS the
    // nonce by 1 per Transfer row — turn i's after-state `(balance - step, nonce + 1)`
    // IS turn i+1's before-state. Advance BOTH per turn so the roots chain.
    let mut nonce: u32 = 0;
    for _ in 0..k {
        let state = CellState::new(balance, nonce);
        let effects = vec![Effect::Transfer {
            amount: step,
            direction: 1,
        }];
        let before_cell = producer_cell(balance as i64, nonce as u64);
        let after_cell = producer_cell((balance as i64) - (step as i64), nonce as u64);
        let nullifier_root = dregg_circuit::heap_root::empty_heap_root_8();
        let commitments_root = dregg_circuit::heap_root::empty_heap_root_8();
        let receipt_log: Vec<[u8; 32]> = vec![[1u8; 32], [2u8; 32]];
        let leg = mint_rotated_participant_leg(
            &state,
            &effects,
            &before_cell,
            &after_cell,
            &nullifier_root,
            &commitments_root,
            &receipt_log,
            None,
        )
        .expect("rotated leg mint must succeed for an open-permission Transfer");
        turns.push(FinalizedTurn::new(DescriptorParticipant::rotated(leg)));
        balance -= step;
        nonce += 1;
    }
    turns
}

/// Pack a `BabyBear` into the 32-byte little-endian form `pg-dregg`'s transport
/// carries (a field element is one `u32`; the high 28 bytes are zero). This is the
/// inverse of `attest::le32` — the exact mapping the S2 producer applies
/// (`turn_proofs.rs`: `BabyBear → [u8;32]`).
fn bb_to_bytes(b: BabyBear) -> [u8; 32] {
    let mut out = [0u8; 32];
    out[..4].copy_from_slice(&b.as_u32().to_le_bytes());
    out
}

/// Project an upstream 8-felt FAITHFUL-FLOOR state anchor into the single-felt
/// 32-byte form the `pg-dregg` transport carries today. A deployed narrow-leg
/// proof broadcasts its one rotated commit felt across the eight lanes
/// (`WholeChainProof::genesis_root` docs), so the lanes MUST be uniform here —
/// asserted, not truncated: a genuine wide-leg anchor (differing lanes) fails
/// loudly at the named transport-widening follow-up (`attest.rs`) instead of
/// silently dropping lanes.
fn anchor_to_bytes(anchor: [BabyBear; 8]) -> [u8; 32] {
    assert!(
        anchor.iter().all(|l| *l == anchor[0]),
        "narrow-leg anchor lanes must be uniform (the broadcast shape); a genuine \
         wide-leg anchor needs the 8-felt transport widening (the named pg-dregg follow-up)"
    );
    bb_to_bytes(anchor[0])
}

/// Project a real `WholeChainProof` into the `pg-dregg` SQL transport, exactly as
/// the documented `tier-c`/node producer would (`postcard(&root.0)` +
/// `postcard(&binding_proof)` + the `BabyBear → [u8;32]`-packed publics).
fn transport_from_proof(whole: &WholeChainProof) -> SerializedWholeChainProof {
    let root_proof = postcard::to_allocvec(&whole.root.0).expect("root BatchStarkProof encodes");
    let binding_proof = postcard::to_allocvec(&whole.binding_proof).expect("binding Proof encodes");
    SerializedWholeChainProof::new(
        root_proof,
        binding_proof,
        anchor_to_bytes(whole.genesis_root),
        anchor_to_bytes(whole.final_root),
        core::array::from_fn(|i| bb_to_bytes(whole.chain_digest[i])),
        whole.num_turns as u64,
    )
}

#[test]
#[ignore = "SLOW: real recursion fold (~minutes); run with --ignored under --features tier-c"]
fn tier_c_real_proof_attests_and_tamper_is_refused() {
    // ---- produce a REAL whole-chain proof over a 3-turn rotated chain. ----------
    let turns = make_chain(3, 7);
    let whole: WholeChainProof = prove_turn_chain_recursive(&turns)
        .expect("a continuous 3-turn rotated finalized chain must fold recursively");
    // The trust anchor an honest setup mints from a LOCAL fold of this window shape
    // (exactly how the light client gets its config-pinned anchor). The verifier
    // recomputes the fingerprint from the presented root and compares it to THIS.
    let vk: VkAnchor = whole.root_vk_fingerprint().0;

    // ---- (ADMIT) the real proof, packed as the SQL transport, ATTESTS. ----------
    let transport = transport_from_proof(&whole);
    let bytes = transport.to_bytes();
    assert!(!bytes.is_empty(), "the transport bytes must be non-empty");

    let publics = verify_serialized_proof(&bytes, &vk)
        .expect("a REAL whole-chain proof must verify against its own anchor via the tier-c gate");
    // The attested window summary is the proof's bound publics, surfaced for the SRF.
    assert_eq!(publics.genesis_root, anchor_to_bytes(whole.genesis_root));
    assert_eq!(publics.final_root, anchor_to_bytes(whole.final_root));
    assert_eq!(
        publics.chain_digest,
        core::array::from_fn::<_, 8, _>(|i| bb_to_bytes(whole.chain_digest[i]))
    );
    assert_eq!(publics.num_turns, 3);

    // The full range-attest entry attests the matching window and emits tagged rows.
    let req = pg_dregg::attest::AttestRequest {
        proof_bytes: &bytes,
        vk_anchor: vk,
        lo: 0,
        hi: 2, // 3 turns ⇒ ordinals [0, 2]
    };
    let verdict = pg_dregg::attest::attest_range(&req);
    assert!(
        verdict.attested(),
        "the real proof must attest the window [0,2]: {}",
        verdict.reason()
    );

    // ---- (REFUSE 1) a relabeled `final_root` hint — the carried-publics tooth. ---
    // Splice a different final_root into the transport. The binding proof's
    // Fiat–Shamir-bound publics no longer match the claim, so verify refuses.
    {
        let mut bad = transport.clone();
        bad.final_root[0] ^= 0xFF;
        let bad_bytes = bad.to_bytes();
        let r = verify_serialized_proof(&bad_bytes, &vk);
        assert!(
            r.is_err(),
            "a relabeled final_root hint must be refused (the publics tooth), got {r:?}"
        );
    }

    // ---- (REFUSE 2) a wrong VK anchor (a different circuit) — the VK pin. --------
    {
        let mut wrong = vk;
        wrong[0] ^= 0xFF;
        let r = verify_serialized_proof(&bytes, &wrong);
        assert!(
            r.is_err(),
            "a wrong anchor must be refused (the VK pin), got {r:?}"
        );
    }

    // ---- (REFUSE 3) a corrupted root-proof blob — the root batch verify (or the
    //      structural decode) catches it; either way fail-closed, never a false attest.
    {
        let mut bad = transport.clone();
        let mid = bad.root_proof.len() / 2;
        bad.root_proof[mid] ^= 0xFF;
        let bad_bytes = bad.to_bytes();
        let r = verify_serialized_proof(&bad_bytes, &vk);
        assert!(
            r.is_err(),
            "a corrupted root proof must be refused, got {r:?}"
        );
    }
}
