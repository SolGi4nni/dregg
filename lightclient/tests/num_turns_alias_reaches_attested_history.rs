//! **DOES THE COUNT ALIAS REACH `AttestedHistory`? — measured YES, then CLOSED. Now the
//! REGRESSION TOOTH.**
//!
//! ## What this probe measured when it was written (commit `0a1854df0`)
//!
//! `circuit-prove/tests/num_turns_alias_probe.rs` had MEASURED that
//! `verify_whole_chain_proof_bytes` admits an envelope whose `num_turns` has been inflated by any
//! multiple of the BabyBear prime (or of `2^32`), because both comparison sites build
//! `BabyBear::new(num_turns as u32)`.
//!
//! That was a verifier-level fact. This probe closed the last hop: `verify_history_bytes` copies
//! `env.num_turns as usize` into the returned [`dregg_lightclient::AttestedHistory`] with no
//! branch between the teeth and the copy — so the number the light client *reported* was the
//! relayer's, not the fold's, against an `AttestedHistory` doc that reads "every one of
//! `num_turns` finalized turns executed correctly, in order".
//!
//! **Measured: a genuine 2-turn history attested as `num_turns = 6,308,233,219`.**
//!
//! ## What this file asserts NOW
//!
//! **The assertions are DELIBERATELY INVERTED, not edited to match observed behaviour.** Each one
//! states the refusal envelope v6 owes, so a regression re-opens this file loudly.
//!
//! The fix sits in `circuit-prove`, upstream of this crate: `num_turns` is a `u32` (the `2^32`
//! family is unrepresentable) and `WholeChainProofBytes::from_postcard` refuses `>= p`. There is
//! still no branch between the teeth and the copy at `lightclient/src/lib.rs` — and there does not
//! need to be one, because nothing that reaches the copy can carry a non-canonical count. This
//! probe is what holds that reasoning to account.
//!
//! SLOW: one real recursion fold (~minutes). Run with:
//!   cargo test -p dregg-lightclient --test num_turns_alias_reaches_attested_history -- --ignored --nocapture

#![cfg(feature = "prover")]

use dregg_circuit::effect_vm::{CellState, Effect};
use dregg_circuit_prove::ivc_turn_chain::{
    FinalizedTurn, WholeChainProof, WholeChainProofBytes, prove_turn_chain_recursive,
};
use dregg_circuit_prove::joint_turn_aggregation::DescriptorParticipant;
use dregg_lightclient::verify_history_bytes;
use dregg_turn_prover::rotation_witness::mint_rotated_participant_leg;

/// The BabyBear prime `2^31 - 2^27 + 1`.
const P: u32 = 0x7800_0001;

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

fn make_turn(balance: u64, nonce: u32, amount: u64) -> FinalizedTurn {
    let state = CellState::new(balance, nonce);
    let effects = vec![Effect::Transfer {
        amount,
        direction: 1,
    }];
    let leg = mint_rotated_participant_leg(
        &state,
        &effects,
        &producer_cell(balance as i64, nonce as u64),
        &producer_cell((balance as i64) - (amount as i64), nonce as u64),
        &dregg_circuit::heap_root::empty_heap_root_8(),
        &dregg_circuit::heap_root::empty_heap_root_8(),
        &vec![[1u8; 32], [2u8; 32]],
        None,
    )
    .expect("rotated leg mints");
    FinalizedTurn::new(DescriptorParticipant::rotated(leg))
}

/// **THE MEASUREMENT, INVERTED.** The light client must REFUSE an envelope whose count was edited
/// on the wire, so no `AttestedHistory` is ever minted carrying a relayer's number.
#[test]
#[ignore = "SLOW: one real recursion fold (~minutes); run with --ignored --nocapture"]
fn light_client_reports_the_relayers_inflated_count() {
    let turns = vec![make_turn(1000, 0, 7), make_turn(1000 - 7, 1, 7)];
    let whole: WholeChainProof =
        prove_turn_chain_recursive(&turns).expect("the 2-turn rotated chain folds");
    let vk = whole.root_vk_fingerprint();
    let bytes = whole.to_bytes();
    let env = WholeChainProofBytes::from_postcard(&bytes).expect("the honest envelope decodes");

    // The honest artifact must still attest, and at the TRUE count — a fix that refused this, or
    // that reduced the count into range, would be worse than the hole.
    let honest = verify_history_bytes(&bytes, &vk).expect("the honest envelope must attest");
    println!(
        "[baseline] AttestedHistory.num_turns = {}",
        honest.num_turns
    );
    assert_eq!(honest.num_turns, 2);

    // `n + 2^32` and `n + 2^32 + p` are absent from this table because envelope v6's `u32` cannot
    // hold them; that leg is measured at the bytes in
    // `circuit-prove/tests/num_turns_alias_probe.rs::wire_u64_shaped_count_is_not_even_decodable`.
    for (label, n) in [("n + p", 2 + P), ("n + 2p", 2 + 2 * P)] {
        let mut bad = env.clone();
        bad.num_turns = n;
        match verify_history_bytes(&bad.to_postcard(), &vk) {
            Err(e) => println!("[alias] {label} = {n}: REFUSED — {e}"),
            Ok(att) => panic!(
                "REGRESSION: the light client ADMITTED the aliased count {label} = {n} and minted \
                 an AttestedHistory reporting {} turns — a relayer can inflate a history's length \
                 by editing one integer, with no key, no proving and no witness",
                att.num_turns
            ),
        }
    }

    // CONTROL: a non-aliasing edit (below p, so it sails past the new count bound) must still be
    // refused by the segment tooth — else nothing above is attributable.
    let mut bad = env.clone();
    bad.num_turns = 3;
    let r = verify_history_bytes(&bad.to_postcard(), &vk);
    println!(
        "[control] n + 1 = 3: {}",
        if r.is_err() { "REFUSED" } else { "ADMITTED" }
    );
    assert!(
        r.is_err(),
        "NOT ATTRIBUTABLE: even n+1 was admitted — the count tooth is dead for another reason"
    );
}
