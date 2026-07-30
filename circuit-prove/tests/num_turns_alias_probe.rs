//! **FALSIFICATION PROBE — can a relayer inflate `num_turns` by editing a `u64`?**
//!
//! An audit READ the whole-chain verify path and claimed the count lane aliases on the
//! wire:
//!
//!   * `WholeChainProofBytes.num_turns` is a `u64` (`ivc_turn_chain.rs:1984`);
//!   * `verify_whole_chain_proof_bytes` passes `env.num_turns as usize` (`:2132`);
//!   * both comparison sites build `BabyBear::new(num_turns as u32)`
//!     (`:5607` — the binding-descriptor scalar tooth, and `:5659` — the segment tooth);
//!   * `BabyBear::new` reduces mod p (`circuit/src/field.rs:114`) and `as u32` truncates;
//!   * every `num_turns < BABY_BEAR_MODULUS` guard in the file sits on a `turns.len()`
//!     PROVER site (`:2590`, `:3018`, `:3429`, `:5249`) — none on a verify path.
//!
//! So `n`, `n + p`, `n + 2p`, and `n + 2^32` should all land on the SAME field element and
//! all four teeth should pass, while `AttestedHistory`/`env.num_turns` reports the
//! inflated one. This probe MEASURES it against a REAL fold: one honest 2-turn chain,
//! then the same artifact with the count edited — no re-proving, which is exactly what a
//! relayer can do.
//!
//! Every case PRINTS its result before asserting, so a REFUTATION (a refusal) is visible
//! in the log and not just a panic.
//!
//! SLOW: one real recursion fold (~minutes). Run with:
//!   cargo test -p dregg-circuit-prove --test num_turns_alias_probe -- --ignored --nocapture

use dregg_circuit::effect_vm::{CellState, Effect};
use dregg_circuit_prove::ivc_turn_chain::{
    FinalizedTurn, WholeChainProof, WholeChainProofBytes, prove_turn_chain_recursive,
    verify_turn_chain_recursive, verify_turn_chain_recursive_from_blobs,
    verify_whole_chain_proof_bytes,
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

/// **THE MEASUREMENT.** One honest fold; then the count edited on the wire, with no
/// re-proving and no other change.
#[test]
#[ignore = "SLOW: one real recursion fold (~minutes); run with --ignored --nocapture"]
fn wire_num_turns_aliases_mod_p_and_mod_2_32() {
    let turns = the_chain();
    let honest_n = turns.len() as u64;
    let mut whole: WholeChainProof =
        prove_turn_chain_recursive(&turns).expect("the 2-turn rotated chain folds");
    assert_eq!(whole.num_turns as u64, honest_n);
    let vk = whole.root_vk_fingerprint();

    let bytes = whole.to_bytes();
    let env = WholeChainProofBytes::from_postcard(&bytes).expect("the honest envelope decodes");
    assert_eq!(env.num_turns, honest_n);

    // BASELINE: the honest artifact verifies over the wire.
    let baseline = verify_whole_chain_proof_bytes(&bytes, &vk);
    println!("[baseline] num_turns = {honest_n}: {baseline:?}");
    baseline.expect("the honest artifact must verify (else the probe measured nothing)");

    // THE FOUR ALIASES. Each is the honest artifact with ONLY the envelope's `u64` count
    // edited — no proving, no other field touched. `BabyBear::new(n as u32)` should map
    // all of them onto the same field element as `honest_n`.
    let aliases: [(&str, u64); 4] = [
        ("n + p", honest_n + P),
        ("n + 2p", honest_n + 2 * P),
        ("n + 2^32", honest_n + (1u64 << 32)),
        ("n + 2^32 + p", honest_n + (1u64 << 32) + P),
    ];

    let mut admitted = Vec::new();
    for (label, n) in aliases {
        let mut bad = env.clone();
        bad.num_turns = n;
        let bad_bytes = bad.to_postcard();
        let r = verify_whole_chain_proof_bytes(&bad_bytes, &vk);
        println!("[envelope] {label} = {n}: {r:?}");
        if r.is_ok() {
            admitted.push((label, n));
        }

        // The lower blob seam (`pg-dregg`'s entry) takes the count as a `usize` directly.
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
    }

    // The IN-MEMORY verifier reads the same `usize` field (`:3105`).
    for (label, n) in aliases {
        let honest = whole.num_turns;
        whole.num_turns = n as usize;
        let r = verify_turn_chain_recursive(&whole, &vk);
        println!("[in-mem]   {label} = {n}: {r:?}");
        whole.num_turns = honest;
    }

    // A CONTROL: `honest_n + 1` is a genuinely different field element and MUST be
    // refused. If this is admitted too, the probe is measuring a dead verifier, not an
    // aliasing hole, and nothing above is attributable.
    {
        let mut bad = env.clone();
        bad.num_turns = honest_n + 1;
        let r = verify_whole_chain_proof_bytes(&bad.to_postcard(), &vk);
        println!("[control]  n + 1 = {}: {r:?}", honest_n + 1);
        assert!(
            r.is_err(),
            "NOT ATTRIBUTABLE: even a non-aliasing count (n+1) was admitted — the count \
             tooth is dead for a reason other than modular aliasing"
        );
    }

    println!(
        "\nADMITTED ALIASES: {}/{} — {:?}",
        admitted.len(),
        aliases.len(),
        admitted
    );

    // THE VERDICT. Written as the audit's prediction so a REFUTATION is loud.
    assert_eq!(
        admitted.len(),
        aliases.len(),
        "REFUTED (wholly or partly): some inflated count was refused on the wire — the \
         verify path does bound the count somewhere the audit did not read"
    );
}
