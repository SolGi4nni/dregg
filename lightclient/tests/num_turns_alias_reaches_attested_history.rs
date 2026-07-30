//! **FALSIFICATION PROBE — does the count alias reach `AttestedHistory`?**
//!
//! `circuit-prove/tests/num_turns_alias_probe.rs` MEASURED that
//! `verify_whole_chain_proof_bytes` admits an envelope whose `num_turns` has been inflated
//! by any multiple of the BabyBear prime (or of `2^32`), because both comparison sites
//! build `BabyBear::new(num_turns as u32)`.
//!
//! That is a verifier-level fact. This probe closes the last hop: `verify_history_bytes`
//! copies `env.num_turns as usize` into the returned [`AttestedHistory`]
//! (`lightclient/src/lib.rs:245`) with no branch between the teeth and the copy — so the
//! number the light client *reports* is the relayer's, not the fold's. `AttestedHistory`'s
//! own doc (`:131`) reads: "every one of `num_turns` finalized turns executed correctly,
//! in order".
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

/// **THE MEASUREMENT.** The light client accepts an envelope whose count was edited on the
/// wire and reports the edited count as the number of turns it attests.
#[test]
#[ignore = "SLOW: one real recursion fold (~minutes); run with --ignored --nocapture"]
fn light_client_reports_the_relayers_inflated_count() {
    let turns = vec![make_turn(1000, 0, 7), make_turn(1000 - 7, 1, 7)];
    let whole: WholeChainProof =
        prove_turn_chain_recursive(&turns).expect("the 2-turn rotated chain folds");
    let vk = whole.root_vk_fingerprint();
    let bytes = whole.to_bytes();
    let env = WholeChainProofBytes::from_postcard(&bytes).expect("the honest envelope decodes");

    let honest = verify_history_bytes(&bytes, &vk).expect("the honest envelope must attest");
    println!(
        "[baseline] AttestedHistory.num_turns = {}",
        honest.num_turns
    );
    assert_eq!(honest.num_turns, 2);

    for (label, n) in [
        ("n + p", 2 + P),
        ("n + 2^32", 2 + (1u64 << 32)),
        ("n + 2^32 + p", 2 + (1u64 << 32) + P),
    ] {
        let mut bad = env.clone();
        bad.num_turns = n;
        match verify_history_bytes(&bad.to_postcard(), &vk) {
            Ok(att) => {
                println!(
                    "[alias] {label}: envelope claims {n}, AttestedHistory reports {}",
                    att.num_turns
                );
                assert_eq!(
                    att.num_turns as u64, n,
                    "the light client reports the RELAYER's count verbatim"
                );
            }
            Err(e) => panic!(
                "REFUTED: the light client refused the aliased count {label} = {n}: {e:?} — \
                 something on this path bounds the count after all"
            ),
        }
    }

    // CONTROL: a non-aliasing edit must still be refused, else nothing above is attributable.
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
