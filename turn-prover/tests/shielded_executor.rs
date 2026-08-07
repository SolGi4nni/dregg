//! End-to-end shielded transfer through the REAL executor (privacy M2-a), over the
//! **committed shielded accumulator**.
//!
//! ## ⚑ SAY THE SUBSTRATE OUT LOUD
//!
//! Every constraint exercised here is AUTHORED IN LEAN. The spend side is
//! `dregg-shielded-spend-complete-fsi2::v1`
//! (`metatheory/Dregg2/Circuit/Emit/ShieldedSpendCompleteEmit.lean`, 557 columns, 25 PIs
//! `[nullifier] ++ committedRoot[8] ++ wide[16]`); the sidecar is
//! `WideValueBindingEmit.lean`. This file authors no constraint — it builds witnesses, drives the
//! public executor entry, and reads refusals.
//!
//! ## ⚑ FLAG DAY 2026-08-07 — seam #15, closed ON THE DEPLOYED PATH
//!
//! The retired payload carried `merkle_root: u32`, chosen by the prover, compared against nothing.
//! `ShieldedMerkleRootPin.root_substitution_forges` states the theft: build your OWN tree holding a
//! note that was never committed, honestly prove membership at that tree's root `R`, publish `R`.
//! Membership genuinely holds. Nobody checked which tree.
//!
//! The field is gone. `apply_shielded_transfer` reads `note_shielded.root8()` from live executor
//! state and hands it to the verifier as the 8-lane `piCommitted` every spend proof is judged
//! against. `executor_theft_forged_tree_refuses_on_the_deployed_path` is the exhibit, and it is
//! deliberately built so the ONLY difference between accept and refuse is which accumulator the
//! executor holds — the same payload bytes, two executors.
//!
//! The old test in this position was `forged_membership_root_rejects`, which bumped
//! `payload.merkle_root` by one on an already-built payload and watched the STARK fail. Lean names
//! that exactly: `ShieldedMerkleRootPin.mutation_test_is_not_the_pin`. It rejected
//! root-mutation-without-reproof; the attacker never mutates, they PROVE. It is replaced, not
//! renamed.
//!
//! ## What the seven un-ignored tests now cover
//!
//! They were `#[ignore]`d because the deployed path FAILED CLOSED: the retired spend circuit
//! published only a one-felt `value_binding`, so the same-opening join had no ring-side full-`u64`
//! carrier to join against and `ring_wide_bindings` was passed EMPTY. The complete spend PI-pins
//! its own sixteen `cap_node8` lanes, so the join is live and the ignores are gone.

use std::sync::Arc;

use dregg_cell::{
    AuthRequired, Cell, CellId, Ledger, Permissions, ShieldedNoteCommitment, ShieldedNoteSet,
    felt_to_bytes32,
};
use dregg_cell_crypto::value_commitment::{
    BulletproofRangeProof, ValueCommitment, ValueCommitmentBytes, prove_conservation,
    scalar_from_blinding_bytes,
};
use dregg_circuit::exact_nullifier_aafi::TaggedKeyWire;
use dregg_circuit::field::{BABYBEAR_P, BabyBear};
use dregg_circuit_prove::shielded::{
    BINDING_BLIND_LANES, ShieldedSpendCompleteWitness, ShieldedSpendMembership, ShieldedTransfer,
    ShieldedTransferWitness, ShieldedValueLeg, TREE_DEPTH, WideValueBindingProof,
    WideValueBindingWitness, prove_wide_value_binding, wide_transfer_message,
};
use dregg_turn::action::{ShieldedInputPayload, ShieldedLeg, ShieldedTransferPayload};
use dregg_turn::executor::shielded_nullifier_key;
use dregg_turn::{
    Action, Authorization, CallForest, ComputronCosts, DelegationMode, Effect, TurnError,
    TurnExecutor,
    turn::{Turn, TurnResult},
};
use dregg_turn_prover::CircuitShieldedTransferVerifier;

const ASSET: u64 = 1;

// ── executor / turn plumbing (public API only) ───────────────────────────────

fn open_permissions() -> Permissions {
    Permissions {
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

/// An executor with the REAL shielded verifier injected AND its shielded accumulator holding
/// exactly `set` — the production wiring a node performs at startup, plus the committed state a
/// node would have reached by processing the `Shield` mints that created these notes.
///
/// ⚑ The root equality assert is not decoration. The AAFI root is APPEND-ORDER dependent (append
/// rank `r` sits at physical slot `r + 1`), so a harness that seeded the same commitments in a
/// different order would produce a different `root8()` and every test below would refuse for the
/// wrong reason — a refusal that looks exactly like the theft refusal. It is checked here so that
/// can never be mistaken for the tooth.
fn shielded_executor_holding(set: &ShieldedNoteSet) -> TurnExecutor {
    let executor = TurnExecutor::new(ComputronCosts::zero())
        .with_shielded_transfer_verifier(Arc::new(CircuitShieldedTransferVerifier::new()));
    {
        let mut live = executor.note_shielded.lock().unwrap();
        for (commitment, _seq) in set.iter_in_append_order() {
            live.insert(ShieldedNoteCommitment(commitment))
                .expect("seeding the executor's committed accumulator");
        }
    }
    assert_eq!(
        executor.note_shielded.lock().unwrap().root8(),
        set.root8(),
        "the executor's committed accumulator must be the SAME tree the spend proofs fold to; \
         an order mismatch here would refuse every transfer for a reason that mimics the theft"
    );
    executor
}

/// The executor's live shielded accumulator, as a `ShieldedNoteSet` a prover can build membership
/// paths against. Used to prove a SECOND spend after the first transfer grew the tree.
fn live_accumulator(executor: &TurnExecutor) -> ShieldedNoteSet {
    ShieldedNoteSet::from_records(
        executor
            .note_shielded
            .lock()
            .unwrap()
            .iter_in_append_order(),
    )
    .expect("the live accumulator's records reconstruct")
}

fn actor_cell() -> (CellId, Cell) {
    let mut pk = [0u8; 32];
    pk[0] = 0x5A;
    pk[31] = 0xA5;
    let mut cell = Cell::with_balance(pk, [0u8; 32], 0);
    cell.permissions = open_permissions();
    (cell.id(), cell)
}

fn shielded_turn(
    agent: CellId,
    previous_receipt_hash: Option<[u8; 32]>,
    payload: ShieldedTransferPayload,
) -> Turn {
    let mut forest = CallForest::new();
    forest.add_root(Action {
        target: agent,
        method: [0u8; 32],
        args: vec![],
        authorization: Authorization::Unchecked,
        preconditions: Default::default(),
        effects: vec![Effect::ShieldedTransfer { payload }],
        may_delegate: DelegationMode::None,
        commitment_mode: Default::default(),
        balance_change: None,
        witness_blobs: vec![],
    });
    Turn {
        agent,
        nonce: 0,
        call_forest: forest,
        fee: 0,
        memo: None,
        valid_until: None,
        previous_receipt_hash,
        depends_on: vec![],
        conservation_proof: None,
        sovereign_witnesses: std::collections::HashMap::new(),
        execution_proof: None,
        execution_proof_cell: None,
        execution_proof_new_commitment: None,
        custom_program_proofs: None,
        effect_binding_proofs: Vec::new(),
        cross_effect_dependencies: Vec::new(),
        effect_witness_index_map: Vec::new(),
    }
}

/// Drive one shielded transfer through the whole public turn path.
/// `Ok(())` = committed; `Err(reason)` = the executor's genuine refusal.
fn run(executor: &TurnExecutor, payload: ShieldedTransferPayload) -> Result<(), TurnError> {
    run_chained(executor, payload, None).map(|_| ())
}

/// As [`run`], but threads the executor's receipt chain so a SECOND turn on the same executor is
/// accepted by the chain gate. Returns the committed receipt hash to chain onward.
fn run_chained(
    executor: &TurnExecutor,
    payload: ShieldedTransferPayload,
    previous_receipt_hash: Option<[u8; 32]>,
) -> Result<[u8; 32], TurnError> {
    let (agent, cell) = actor_cell();
    let mut ledger = Ledger::new();
    let _ = ledger.insert_cell(cell);
    match executor.execute(
        &shielded_turn(agent, previous_receipt_hash, payload),
        &mut ledger,
    ) {
        TurnResult::Committed { receipt, .. } => Ok(receipt.receipt_hash()),
        TurnResult::Rejected { reason, .. } => Err(reason),
        other => panic!("unexpected turn result: {other:?}"),
    }
}

fn refusal_reason(error: TurnError) -> String {
    match error {
        TurnError::InvalidEffect { reason } => reason,
        other => panic!("expected InvalidEffect, got {other:?}"),
    }
}

// ── shielded witness / payload construction (the real prover, over a REAL accumulator) ──

fn range_proof_bytes(value: u64, blinding: &[u8; 32]) -> Vec<u8> {
    BulletproofRangeProof::prove_range(value, &scalar_from_blinding_bytes(blinding)).proof_bytes
}

/// Distinct canonical single-felt decoy commitments (the shape a `Shield` mint lands).
fn decoys(n: u32, salt: u32) -> Vec<[u8; 32]> {
    (0..n)
        .map(|i| felt_to_bytes32(BabyBear::new(0x0A0A_0000 + salt * 0x1000 + i)))
        .collect()
}

/// Build a complete-spend witness whose note is a GENUINE member of a fresh `ShieldedNoteSet`
/// (populated with `decoys` then the note), and return the witness, the populated set, and the
/// note's committed 32-byte commitment.
///
/// The membership path is the note's REAL authenticated place in that set, so the generated trace
/// folds to the set's `root8()`. This is the honest route the executor drives: a `Shield` mint
/// lands the Poseidon2 note commitment, a spend opens it against the committed accumulator.
fn witness_in_set(
    value: u64,
    asset_type: u64,
    randomness: BabyBear,
    spending_key: [BabyBear; 4],
    decoy_bytes: &[[u8; 32]],
) -> (
    ShieldedSpendCompleteWitness,
    ShieldedNoteSet,
    ShieldedNoteCommitment,
) {
    let binding_blind: [BabyBear; BINDING_BLIND_LANES] =
        core::array::from_fn(|i| BabyBear::new(100 + i as u32));
    // A probe witness (trivial membership) just to derive the note-commitment felt.
    let probe = ShieldedSpendCompleteWitness {
        value,
        asset_type,
        randomness,
        spending_key,
        binding_blind,
        membership: ShieldedSpendMembership {
            positions: [0; TREE_DEPTH],
            siblings: [[[BabyBear::ZERO; 8]; 3]; TREE_DEPTH],
            next_addr: TaggedKeyWire::top(),
        },
    };
    let commitment = ShieldedNoteCommitment(felt_to_bytes32(probe.note_commitment_felt()));

    let mut set = ShieldedNoteSet::new();
    for d in decoy_bytes {
        set.insert(ShieldedNoteCommitment(*d))
            .expect("decoy commitment inserts");
    }
    set.insert(commitment).expect("the spent note is committed");

    let witness = witness_against(&probe, &set, &commitment);
    (witness, set, commitment)
}

/// Re-aim a complete-spend witness at whatever tree `set` currently is — the note's REAL
/// authenticated place in it. Used to re-prove a spend after the accumulator has grown.
fn witness_against(
    base: &ShieldedSpendCompleteWitness,
    set: &ShieldedNoteSet,
    commitment: &ShieldedNoteCommitment,
) -> ShieldedSpendCompleteWitness {
    let path = set
        .membership_path(commitment)
        .expect("the committed note has a membership path");
    ShieldedSpendCompleteWitness {
        membership: ShieldedSpendMembership {
            positions: path.path.positions,
            siblings: path.path.siblings,
            next_addr: path.leaf.next_addr().wire(),
        },
        ..base.clone()
    }
}

/// The wide sidecar for a spend witness. Its `(value, asset, randomness, blind)` are the SAME as
/// the spend's, so the sidecar's sixteen `cap_node8` lanes equal the spend proof's PI-pinned ring
/// carrier and `verify_same_opening` joins them. `override_value` exists so a test can prove a
/// DIFFERENT full-`u64` opening (the `v` / `v+p` alias) and watch the join refuse.
fn sidecar_for(
    w: &ShieldedSpendCompleteWitness,
    override_value: Option<u64>,
) -> WideValueBindingProof {
    prove_wide_value_binding(&WideValueBindingWitness {
        value: override_value.unwrap_or(w.value),
        asset_type: w.asset_type,
        legacy_randomness: w.randomness,
        binding_blind: w.binding_blind,
    })
    .expect("prove the mandatory native-wide input binding")
}

/// Serialize a built circuit `ShieldedTransfer` + its conservation proof into the executor wire
/// payload — exactly what a client would post. There is no root to serialize.
fn to_payload(
    transfer: &ShieldedTransfer,
    sidecars: &[WideValueBindingProof],
    conservation: dregg_cell_crypto::ConservationProof,
) -> ShieldedTransferPayload {
    assert_eq!(transfer.inputs.len(), sidecars.len());
    let leg = |l: &ShieldedValueLeg| ShieldedLeg {
        asset_type: l.asset_type,
        commitment_bytes: l.commitment_bytes,
    };
    ShieldedTransferPayload {
        inputs: transfer
            .inputs
            .iter()
            .zip(sidecars)
            .map(|(ip, wide)| ShieldedInputPayload {
                nullifier: ip.nullifier.as_u32(),
                legacy_value_binding: wide.claim.legacy_binding.as_u32(),
                spend_wide_binding: ip.spend_wide_binding.map(BabyBear::as_u32),
                wide_value_binding: wide.claim.wide_binding.map(BabyBear::as_u32),
                spend_proof: ip.proof_bytes(),
                wide_value_proof: wide.proof_bytes(),
            })
            .collect(),
        input_legs: transfer.input_legs.iter().map(leg).collect(),
        output_legs: transfer.output_legs.iter().map(leg).collect(),
        output_range_proofs: transfer.output_range_proofs.clone(),
        conservation,
    }
}

/// Assemble a one-in/one-out shielded transfer over `set` spending the note `witness` opens.
/// `out_value` is what the OUTPUT leg commits to — equal to the input for a conserving transfer,
/// larger for the inflation pole.
fn build_payload(
    witness: &ShieldedSpendCompleteWitness,
    set: &ShieldedNoteSet,
    in_blinding: [u8; 32],
    out_blinding: [u8; 32],
    out_value: u64,
) -> ShieldedTransferPayload {
    let in_c = ValueCommitment::commit(witness.value, &scalar_from_blinding_bytes(&in_blinding));
    let out_c = ValueCommitment::commit(out_value, &scalar_from_blinding_bytes(&out_blinding));
    let sidecar = sidecar_for(witness, None);

    let transfer = dregg_circuit_prove::shielded::transfer_from_witnesses(
        &[ShieldedTransferWitness {
            spend: witness.clone(),
            leg: ShieldedValueLeg {
                asset_type: ASSET,
                commitment_bytes: in_c.to_bytes().0,
            },
        }],
        vec![ShieldedValueLeg {
            asset_type: ASSET,
            commitment_bytes: out_c.to_bytes().0,
        }],
        vec![range_proof_bytes(out_value, &out_blinding)],
    )
    .expect("prove the shielded transfer's complete-spend side");

    // The conservation transcript absorbs the COMMITTED ROOT the transfer is meant for, so a
    // conservation proof cannot be replayed against a different accumulator state.
    let committed_root = set.root8().limbs();
    let excess =
        scalar_from_blinding_bytes(&in_blinding) - scalar_from_blinding_bytes(&out_blinding);
    let message = wide_transfer_message(&transfer, core::slice::from_ref(&sidecar), committed_root)
        .expect("build the native-wide conservation transcript");
    let conservation = prove_conservation(&[in_c], &[out_c], &excess, &message);
    to_payload(&transfer, &[sidecar], conservation)
}

/// A balanced one-in/one-out shielded transfer over a fresh committed accumulator: the set the
/// executor must hold, the payload, and the spend witness (so a test can re-prove against a grown
/// tree).
fn balanced(
    seed: u32,
) -> (
    ShieldedNoteSet,
    ShieldedTransferPayload,
    ShieldedSpendCompleteWitness,
    ShieldedNoteCommitment,
) {
    let amount = 1_000_000u64;
    let (witness, set, commitment) = witness_in_set(
        amount,
        ASSET,
        BabyBear::new(0xC0FFEE ^ seed),
        core::array::from_fn(|i| BabyBear::new(seed.wrapping_mul(7) + i as u32 + 1)),
        &decoys(2, seed),
    );
    let mut in_blinding = [3u8; 32];
    let mut out_blinding = [7u8; 32];
    in_blinding[..4].copy_from_slice(&seed.to_le_bytes());
    out_blinding[..4].copy_from_slice(&seed.wrapping_mul(3).to_le_bytes());
    let payload = build_payload(&witness, &set, in_blinding, out_blinding, amount);
    (set, payload, witness, commitment)
}

// ═══════════════════════════════════════════════════════════════════════════════
//  ⚑ THE #15 CLOSE — the theft REFUSES on the deployed path
// ═══════════════════════════════════════════════════════════════════════════════

/// **⚑ THE EXECUTOR THEFT KAT — seam #15, on the DEPLOYED path.**
///
/// The Rust exhibit of `ShieldedMerkleRootPin.deployed_admits_but_pin_rejects`: a note that was
/// NEVER committed is spent, and only the missing pin would stop it. Here the pin is present, so
/// it stops it — inside `apply_shielded_transfer`, through the public `execute()` entry.
///
/// The construction is deliberately arranged so that the ONLY variable is which accumulator the
/// executor holds. The SAME payload bytes are submitted to two executors:
///
/// * to an executor whose committed accumulator IS the attacker's tree — **ACCEPTED**. This is the
///   non-vacuity pole and it is the important one: it proves the payload is completely well formed
///   (a genuine membership proof, a genuine nullifier derivation, a live wide join, a conserving
///   Pedersen side, a valid range proof), so nothing about it is malformed and the refusal below
///   cannot be some incidental rejection wearing the pin's clothes.
/// * to an executor holding the REAL accumulator (which has never seen this note) — **REFUSED**,
///   nothing spent, nothing appended.
///
/// Vacuity guards asserted BEFORE the verdict: the forged note is genuinely absent from the real
/// accumulator, and the attacker's root `R` genuinely differs from the real `root8()`. The mutation
/// is CONSTRUCTIVE — the attacker's tree is built, not a mutated copy of the real one — so it
/// cannot decay into a no-op the way a `replacen`-style mutation can.
#[test]
fn executor_theft_forged_tree_refuses_on_the_deployed_path() {
    // ── The REAL committed accumulator: an authorized note plus decoys. ──
    let (real_set, honest_payload, _honest_w, _honest_cm) = balanced(0x1234);

    // ── The ATTACKER's tree: an UNAUTHORIZED note, never committed anywhere real. ──
    let attacker_amount = 999_999_999u64;
    let (forged_w, attacker_set, forged_cm) = witness_in_set(
        attacker_amount,
        ASSET,
        BabyBear::new(0xDEAD),
        [
            BabyBear::new(90),
            BabyBear::new(91),
            BabyBear::new(92),
            BabyBear::new(93),
        ],
        &[],
    );

    // ── VACUITY GUARDS, asserted before any verdict is read. ──
    assert!(
        !real_set.contains(&forged_cm),
        "the forged note must NOT be committed in the real accumulator — otherwise this is not a \
         theft, it is an ordinary spend"
    );
    assert_ne!(
        attacker_set.root8(),
        real_set.root8(),
        "the attacker's tree root R must genuinely differ from the real committed root8(); if \
         these agreed the refusal below would prove nothing"
    );

    // The theft payload: an honest membership proof IN THE ATTACKER'S TREE, with a fully
    // conserving Pedersen side and a valid range proof. Everything a well-formed transfer needs.
    let mut in_blinding = [11u8; 32];
    let mut out_blinding = [13u8; 32];
    in_blinding[..4].copy_from_slice(&0xBAADu32.to_le_bytes());
    out_blinding[..4].copy_from_slice(&0xF00Du32.to_le_bytes());
    let theft_payload = build_payload(
        &forged_w,
        &attacker_set,
        in_blinding,
        out_blinding,
        attacker_amount,
    );

    // ── POLE 1 (NON-VACUITY): an executor whose committed state IS the attacker's tree ACCEPTS
    //    this exact payload. So the payload is well formed in every respect. ──
    let attacker_world = shielded_executor_holding(&attacker_set);
    run(&attacker_world, theft_payload.clone()).expect(
        "the theft payload is a COMPLETELY well-formed transfer — it is admitted by an executor \
         whose accumulator is the tree it proves membership in. Whatever refuses it below refuses \
         it for exactly one reason: the committed root.",
    );

    // ── POLE 2 (THE THEFT DIES): the SAME payload, judged by an executor holding the REAL
    //    accumulator. `piCommitted` is `real_set.root8()`, the fold reached R, and the Lean-emitted
    //    8-lane `rootPins` `.piBinding` has no satisfying assignment. ──
    let real_world = shielded_executor_holding(&real_set);
    let reason = refusal_reason(run(&real_world, theft_payload).expect_err(
        "a spend proving membership in the ATTACKER'S OWN tree must REFUSE once piCommitted is \
         sourced from the executor's note_shielded.root8(). This is seam #15.",
    ));
    assert!(
        reason.contains("STARK") || reason.contains("complete-spend"),
        "the refusal must be the complete-spend proof failing under the executor-committed root, \
         not some earlier structural check: {reason}"
    );
    assert!(
        real_world.note_nullifiers.lock().unwrap().is_empty(),
        "a refused theft spends NOTHING"
    );
    assert_eq!(
        real_world.note_shielded.lock().unwrap().root8(),
        real_set.root8(),
        "a refused theft appends NOTHING — the committed accumulator is untouched"
    );

    // ── And the honest spender, in the same real world, is ADMITTED. The pin refuses the theft
    //    without refusing the legitimate transfer. ──
    let honest_world = shielded_executor_holding(&real_set);
    run(&honest_world, honest_payload)
        .expect("an honest spend of a genuinely committed note must be admitted");
}

/// **The pin is a PIN, not a rejection of everything.** A genuine member of the real accumulator
/// is admitted and its nullifier is consumed — the accept pole of the tooth above, standing alone
/// so a regression that refuses everything cannot masquerade as security.
#[test]
fn valid_shielded_transfer_is_admitted_and_spends_its_nullifier() {
    let (set, payload, _w, _cm) = balanced(11);
    let executor = shielded_executor_holding(&set);
    let nf = shielded_nullifier_key(payload.inputs[0].nullifier);
    assert!(!executor.note_nullifiers.lock().unwrap().contains(&nf));
    run(&executor, payload).expect("a valid shielded transfer must be admitted");
    assert!(
        executor.note_nullifiers.lock().unwrap().contains(&nf),
        "the shielded input's nullifier is now spent in the production set"
    );
}

// ═══════════════════════════════════════════════════════════════════════════════
//  Conservation
// ═══════════════════════════════════════════════════════════════════════════════

/// **A transfer that does not conserve REFUSES.** The output leg commits to MORE than the input
/// (hidden inflation) — the complete-spend membership is genuine, the range proof is valid (the
/// inflated value really is in `[0, 2^64)`), so only the Pedersen conservation gate can catch it.
/// `Σδ ≠ 0` ⇒ refused, and nothing is spent.
#[test]
fn inflating_shielded_transfer_rejects_on_conservation() {
    let amount = 1_000_000u64;
    let (witness, set, _cm) = witness_in_set(
        amount,
        ASSET,
        BabyBear::new(0x5151),
        [
            BabyBear::new(14),
            BabyBear::new(15),
            BabyBear::new(16),
            BabyBear::new(17),
        ],
        &decoys(2, 14),
    );
    let executor = shielded_executor_holding(&set);
    // The output leg commits to the INFLATED value; the prover still uses the blinding excess, so
    // the value imbalance leaves a V-component the Schnorr-on-R proof cannot answer.
    let payload = build_payload(&witness, &set, [3u8; 32], [7u8; 32], 2_000_000);
    let reason = refusal_reason(
        run(&executor, payload).expect_err("an inflating shielded transfer must reject"),
    );
    assert!(
        reason.contains("conservation") || reason.contains("range"),
        "rejection must be the value-conservation gate, got: {reason}"
    );
    assert!(
        executor.note_nullifiers.lock().unwrap().is_empty(),
        "the transfer was refused before the nullifier gate could record"
    );
}

/// **The same-opening JOIN is live, and it bites.** `v` and `v + p` share the one-felt legacy
/// binding but NOT the sixteen `cap_node8` carrier lanes. Splicing an `x + p` sidecar over a
/// transfer whose spend proof pins the `x` carrier is refused by `verify_same_opening` — the
/// `ShieldedWideJoinPin.dark_value_decouples` pole, now reachable because the ring carrier is a
/// public input of the complete-spend proof rather than the empty vector.
#[test]
fn modulus_alias_splice_rejects_at_real_executor_no_mint_entry() {
    let (set, honest_payload, witness, _cm) = balanced(31);

    // The honest transfer is admitted.
    let honest_executor = shielded_executor_holding(&set);
    run(&honest_executor, honest_payload.clone()).expect("the full-width x carrier is admitted");

    // The distinct full-`u64` opening `x + p`. Its compatibility felt is identical by construction.
    let alias = sidecar_for(&witness, Some(witness.value + BABYBEAR_P as u64));
    assert_eq!(
        alias.claim.legacy_binding.as_u32(),
        honest_payload.inputs[0].legacy_value_binding,
        "vacuity guard: x and x+p must genuinely share the retired one-felt binding"
    );
    assert_ne!(
        alias.claim.wide_binding.map(BabyBear::as_u32),
        honest_payload.inputs[0].wide_value_binding,
        "vacuity guard: the native carrier must distinguish x from x+p"
    );

    let mut alias_payload = honest_payload;
    alias_payload.inputs[0].wide_value_binding = alias.claim.wide_binding.map(BabyBear::as_u32);
    alias_payload.inputs[0].wide_value_proof = alias.proof_bytes();
    let alias_executor = shielded_executor_holding(&set);
    let reason = refusal_reason(
        run(&alias_executor, alias_payload)
            .expect_err("an x+p sidecar spliced over an x spend carrier must reject"),
    );
    assert!(
        reason.contains("dark-value decouple") || reason.contains("same-opening"),
        "the splice must die at the routed same-opening join, which is the whole point of the \
         join being live: {reason}"
    );
    assert!(alias_executor.note_nullifiers.lock().unwrap().is_empty());
}

// ═══════════════════════════════════════════════════════════════════════════════
//  Double-spend
// ═══════════════════════════════════════════════════════════════════════════════

/// **A genuine double-spend REFUSES at the nullifier gate.**
///
/// ⚑ This is a stronger test than the one it replaces, and it had to become one. The old version
/// re-presented the IDENTICAL payload; that no longer reaches the nullifier gate, because an
/// accepted transfer APPENDS its output and therefore MOVES `note_shielded.root8()`, so a replayed
/// proof now fails the root pin first. A spend proof is bound to the accumulator SNAPSHOT it was
/// built against — a real property of pinning to live state, and one worth a test rather than an
/// assumption.
///
/// So the attacker does what a real attacker does: after the first transfer lands, they RE-PROVE
/// the same note's spend against the GROWN accumulator, with fresh output blinding. The membership
/// proof is genuine and current, the conservation is genuine — and the nullifier, being derived
/// from the note, is the same. The cross-transfer double-spend gate is what refuses it.
#[test]
fn double_spent_shielded_nullifier_rejects() {
    let (set, first_payload, witness, commitment) = balanced(13);
    let executor = shielded_executor_holding(&set);
    let wire_nullifier = first_payload.inputs[0].nullifier;
    let nf = shielded_nullifier_key(wire_nullifier);

    let first = run_chained(&executor, first_payload, None).expect("first transfer admitted");
    assert!(
        executor.note_nullifiers.lock().unwrap().contains(&nf),
        "the first spend consumed the nullifier"
    );

    // The accumulator has GROWN (the first transfer's output landed). Re-prove against it.
    let grown = live_accumulator(&executor);
    assert_ne!(
        grown.root8(),
        set.root8(),
        "vacuity guard: the accepted transfer must have moved the committed root, or this is just \
         the old replay test wearing a new name"
    );
    let reproved = witness_against(&witness, &grown, &commitment);
    let second_payload = build_payload(&reproved, &grown, [3u8; 32], [0x5Au8; 32], witness.value);
    assert_eq!(
        second_payload.inputs[0].nullifier, wire_nullifier,
        "the re-proved spend of the same note reveals the SAME nullifier — the nullifier is \
         derived from the note, not from the tree it was proven in"
    );

    let reason = refusal_reason(
        run_chained(&executor, second_payload, Some(first))
            .expect_err("a second spend of the same note must reject"),
    );
    assert!(
        reason.contains("double-spend"),
        "rejection must be the double-spend refusal — the re-proved membership is genuine and \
         current, so nothing else should refuse it: {reason}"
    );
}

// ═══════════════════════════════════════════════════════════════════════════════
//  Decoder / fail-closed / unlinkability
// ═══════════════════════════════════════════════════════════════════════════════

/// A non-canonical BabyBear encoding in the SIDECAR's public lanes is refused at the decoder,
/// before any proof work — `x + p` must never be accepted as `x`.
#[test]
fn noncanonical_wide_public_lane_rejects_at_executor_entry() {
    let (set, mut payload, _w, _cm) = balanced(32);
    let executor = shielded_executor_holding(&set);
    payload.inputs[0].wide_value_binding[0] = BABYBEAR_P;
    let reason = refusal_reason(
        run(&executor, payload).expect_err("a noncanonical wide field encoding must reject"),
    );
    assert!(
        reason.contains("not canonical BabyBear"),
        "wide decoder refusal must be explicit: {reason}"
    );
}

/// The same canonicality wall on the RING side — the lanes the complete-spend proof pins. This is a
/// NEW surface (the ring carrier only became wire data at this flag day), so it gets its own tooth
/// rather than borrowing the sidecar's.
#[test]
fn noncanonical_ring_wide_lane_rejects_at_executor_entry() {
    let (set, mut payload, _w, _cm) = balanced(33);
    let executor = shielded_executor_holding(&set);
    payload.inputs[0].spend_wide_binding[3] = BABYBEAR_P;
    let reason = refusal_reason(
        run(&executor, payload).expect_err("a noncanonical ring carrier lane must reject"),
    );
    assert!(
        reason.contains("not canonical BabyBear"),
        "the ring decoder refusal must be explicit: {reason}"
    );
}

/// ⚑ **THE L0.5 TRIPWIRE — what a transfer APPENDS is not what a spend can OPEN.**
///
/// This replaces `shielded_append_is_prover_written_not_ledger_derived`, whose own comment said it
/// "must be rewritten" when the accumulator became load-bearing. It has: `note_shielded.root8()` is
/// now the `piCommitted` every spend is pinned to.
///
/// What lands from a transfer is still the output leg's Ristretto Pedersen commitment, chosen by
/// the prover. The safety argument is an ENCODING argument and this test is where it is checked
/// rather than assumed: a spendable note's address is `felt_to_bytes32(cCM)` — four significant
/// bytes, twenty-eight ZERO — because the complete-spend relation pins `cADDR0`/`cADDR1` and
/// constrains the higher limbs to zero. A valid compressed Ristretto point in that subspace would
/// need 224 zero bits. So a transfer output can pollute the accumulator but can never become a
/// forged spendable note.
///
/// When the L0.5 output relation lands (the wire carries a Poseidon2 note commitment bound to the
/// output leg's hidden value, and GATE 4 appends THAT), this test must be rewritten again — and
/// the rewrite is the tripwire.
#[test]
fn transfer_output_append_is_prover_written_and_cannot_be_opened_by_any_spend() {
    let (set, payload, _w, _cm) = balanced(41);
    let executor = shielded_executor_holding(&set);
    let leg_bytes = payload.output_legs[0].commitment_bytes;
    let before = executor.note_shielded.lock().unwrap().root8();

    run(&executor, payload).expect("a valid shielded transfer must be admitted");

    let live = executor.note_shielded.lock().unwrap();
    assert!(
        live.contains(&ShieldedNoteCommitment(leg_bytes)),
        "GATE 4 appends the PROVER-SUPPLIED wire bytes verbatim"
    );
    assert_ne!(
        live.root8(),
        before,
        "the committed root MOVES — which is exactly why the appended encoding matters now"
    );
    assert!(
        ValueCommitment::from_bytes(&ValueCommitmentBytes(leg_bytes)).is_some(),
        "what landed is a PEDERSEN VALUE commitment (a valid Ristretto point), not the Poseidon2 \
         note commitment hash_fact(v,[a,owner,rand]) the complete-spend relation opens"
    );
    assert!(
        leg_bytes[4..].iter().any(|b| *b != 0),
        "THE SAFETY ARGUMENT, CHECKED: the appended leaf lies OUTSIDE the spendable address \
         subspace (felt_to_bytes32 = 4 significant bytes, 28 zero). No complete-spend proof can \
         open it, so a transfer output cannot become a forged spendable note. If this ever fails, \
         a prover has found a Ristretto encoding with 28 trailing zero bytes and the append is a \
         mint."
    );
}

/// UNLINKABILITY: two independent shielded transfers of the SAME amount produce DIFFERENT
/// nullifiers / commitments / proofs — an observer cannot link sender to receiver on the wire.
#[test]
fn distinct_transfers_are_unlinkable_on_the_wire() {
    let (_sa, a, _wa, _ca) = balanced(21);
    let (_sb, b, _wb, _cb) = balanced(22);
    assert_ne!(
        a.inputs[0].nullifier, b.inputs[0].nullifier,
        "distinct shielded inputs must reveal distinct nullifiers"
    );
    assert_ne!(
        a.output_legs[0].commitment_bytes, b.output_legs[0].commitment_bytes,
        "equal amounts must still commit to distinct (blinded) value commitments"
    );
    assert_ne!(
        a.inputs[0].spend_proof, b.inputs[0].spend_proof,
        "the hidden proofs reveal nothing linking the two transfers"
    );
    assert_ne!(
        a.inputs[0].wide_value_binding, b.inputs[0].wide_value_binding,
        "the native wide carriers retain fresh hidden blinding"
    );
    assert_ne!(
        a.inputs[0].spend_wide_binding, b.inputs[0].spend_wide_binding,
        "so does the ring carrier the spend proof pins"
    );
}

/// ⚑ FAIL-CLOSED CANARY: the ONE payload the injected executor ADMITS is REFUSED by an executor
/// with no verifier injected, with a reason that NAMES the missing verifier — so a verify-only
/// deployment is never mistaken for a bad proof. Both sides in the SAME executable.
#[test]
fn uninjected_executor_refuses_the_very_transfer_the_injected_one_admits() {
    let (set, payload, _w, _cm) = balanced(51);

    // Same payload, verifier injected: ADMITTED.
    let injected = shielded_executor_holding(&set);
    let before = injected.note_shielded.lock().unwrap().len();
    run(&injected, payload.clone()).expect("the injected executor admits this transfer");
    assert_eq!(
        injected.note_shielded.lock().unwrap().len(),
        before + 1,
        "the admitted transfer landed its output note"
    );

    // Same payload, SAME committed state, NOTHING injected: REFUSED, and nothing landed.
    let bare = TurnExecutor::new(ComputronCosts::zero());
    {
        let mut live = bare.note_shielded.lock().unwrap();
        for (c, _) in set.iter_in_append_order() {
            live.insert(ShieldedNoteCommitment(c)).unwrap();
        }
    }
    let reason = refusal_reason(
        run(&bare, payload).expect_err("a verify-only executor must NOT admit a hidden transfer"),
    );
    assert!(
        reason.contains("injected shielded verifier"),
        "the refusal must name the MISSING VERIFIER, not masquerade as a proof failure: {reason}"
    );
    assert!(
        bare.note_nullifiers.lock().unwrap().is_empty(),
        "a fail-closed refusal spends nothing"
    );
    assert_eq!(
        bare.note_shielded.lock().unwrap().root8(),
        set.root8(),
        "a fail-closed refusal appends nothing"
    );
}

/// The seam's OTHER half: the trait never sees the journal. `ShieldedTransferVerifier::verify`
/// takes `&ShieldedTransferPayload` plus the executor-computed `committed_root` and returns
/// `VerifiedShieldedTransfer` — no `&mut LedgerJournal`, no `&Ledger`, no `&TurnExecutor`. This is
/// the compile-time witness that the signature is verify-returns-VALUE.
///
/// ⚑ It is also the witness that the committed root is a PARAMETER: there is nothing in the
/// payload this call could have derived it from.
#[test]
fn the_verifier_trait_is_pure_verification_and_returns_the_state_to_land() {
    let (set, payload, _w, _cm) = balanced(61);
    let expected_commitment = ShieldedNoteCommitment(payload.output_legs[0].commitment_bytes);

    let verified = dregg_turn::ShieldedTransferVerifier::verify(
        &CircuitShieldedTransferVerifier::new(),
        &payload,
        set.root8().limbs(),
    )
    .expect("a balanced transfer verifies under the committed root");

    assert_eq!(
        verified.nullifiers,
        vec![payload.inputs[0].nullifier],
        "the returned nullifiers are the ones the STARK proved"
    );
    assert_eq!(
        verified.output_commitments,
        vec![expected_commitment],
        "the returned commitments are what the core executor appends and journals"
    );

    // And under the EMPTY accumulator's root — a tree that does not hold this note — the same call
    // refuses. The parameter is load-bearing, not decorative.
    assert!(
        dregg_turn::ShieldedTransferVerifier::verify(
            &CircuitShieldedTransferVerifier::new(),
            &payload,
            ShieldedNoteSet::new().root8().limbs(),
        )
        .is_err(),
        "the committed-root parameter must decide acceptance"
    );
    // No ledger, no journal, no executor was involved above.
}
