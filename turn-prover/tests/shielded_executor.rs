//! End-to-end shielded transfer through the REAL executor, over the **committed shielded
//! accumulator**, with the **value link in the AIR**.
//!
//! ## ⚑ SAY THE SUBSTRATE OUT LOUD
//!
//! Every constraint exercised here is AUTHORED IN LEAN. The spend side is
//! `dregg-shielded-spend-complete-fsi2::v1`
//! (`metatheory/Dregg2/Circuit/Emit/ShieldedSpendCompleteEmit.lean`, 557 columns, 25 PIs
//! `[nullifier] ++ committedRoot[8] ++ wide[16]`); the value link is
//! `dregg-shielded-transfer-value-link::v1`
//! (`metatheory/Dregg2/Circuit/Emit/ShieldedTransferValueLinkEmit.lean`, 164 columns, 17 PIs
//! `wide[16] ++ [outCm]`). This file authors no constraint — it builds witnesses, drives the public
//! executor entry, and reads refusals.
//!
//! ## ⚑ FLAG DAY — the VALUE LINK, and the Pedersen leg's deletion
//!
//! Seam #15's lane closed the spend-side theft (a prover-chosen `merkle_root`) and named one
//! residual it did not hide, verbatim:
//!
//! > the Pedersen leg's own `v` is bound to the STARK-side `v` only through this TRANSCRIPT, not by
//! > any circuit equality (`verify_value_link` is test-only). The wide join makes the two proofs
//! > open the same `(value, asset)` **as each other**; it does not make either open the value the
//! > Ristretto commitment holds.
//!
//! So a spender who genuinely owned a note worth `1` published input and output legs committing to
//! `1_000_000`; `verify_full_conservation_bytes` cleared `Σ C_in = Σ C_out` over those legs and
//! nothing compared them to the note. That gap is not closable by a check — BabyBear cannot open a
//! Ristretto point without non-native curve arithmetic in-AIR, and a Ristretto sigma protocol
//! cannot open a Poseidon2 image without the hash in-group (`cell-crypto/src/value_link_zk.rs`
//! records the same finding and names the exit). The Pedersen leg is therefore GONE: no
//! `input_legs`, no `output_legs`, no `output_range_proofs`, no `conservation`, no sidecar fields.
//!
//! What an output publishes is a **Poseidon2 note commitment** plus its value-link proof, and the
//! Lean relation forces that commitment and the spend's sixteen carrier lanes to be functions of
//! ONE canonical 16-bit limb opening. Two consequences this file tests:
//!
//! * [`value_link_divergence_refuses_on_the_deployed_path`] — the NEGATIVE pole. A transfer whose
//!   minted note opens to `v' != v` is CONSTRUCTED (a real link proof, at `v'`, over a real spend
//!   proof at `v`), the divergence is asserted present before any verdict is read, and it REFUSES.
//! * [`honest_transfer_conserves_and_the_minted_note_is_spendable`] — the POSITIVE pole. The
//!   appended leaf IS `hash_fact(v,[a,owner,rand])` for the SAME `v` the spent note held, and a
//!   second transfer spends it. The old L0.5 tripwire (`transfer_output_append_is_prover_written…`)
//!   asserted the opposite — that no spend could ever open a transfer output — and said in its own
//!   docblock that it must be rewritten when the output relation landed. This is that rewrite.

use std::sync::Arc;

use dregg_cell::{
    AuthRequired, Cell, CellId, Ledger, Permissions, ShieldedNoteCommitment, ShieldedNoteSet,
    felt_to_bytes32,
};
use dregg_circuit::exact_nullifier_aafi::TaggedKeyWire;
use dregg_circuit::field::{BABYBEAR_P, BabyBear};
use dregg_circuit::poseidon2::hash_fact;
use dregg_circuit_prove::shielded::{
    BINDING_BLIND_LANES, ShieldedSpendCompleteWitness, ShieldedSpendMembership,
    ShieldedTransferLinkWitness, ShieldedTransferWitness, TREE_DEPTH, prove_shielded_transfer,
    prove_shielded_transfer_link,
};
use dregg_turn::action::{ShieldedInputPayload, ShieldedOutputPayload, ShieldedTransferPayload};
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
/// wrong reason — a refusal that looks exactly like the theft refusal.
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

/// Distinct canonical single-felt decoy commitments (the shape a `Shield` mint lands).
fn decoys(n: u32, salt: u32) -> Vec<[u8; 32]> {
    (0..n)
        .map(|i| felt_to_bytes32(BabyBear::new(0x0A0A_0000 + salt * 0x1000 + i)))
        .collect()
}

/// A recipient: their four-limb spending key and the owner felt the minted note must carry
/// (`hash_fact(key0,[key1,key2,key3])` — the SAME derivation the complete-spend relation's
/// `lkOwnerDerive` performs, which is what makes the minted note spendable by them and nobody
/// else).
fn recipient(seed: u32) -> ([BabyBear; 4], BabyBear) {
    let key: [BabyBear; 4] =
        core::array::from_fn(|i| BabyBear::new(seed.wrapping_mul(31) + i as u32 + 7));
    let owner = hash_fact(key[0], &[key[1], key[2], key[3]]);
    (key, owner)
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

/// Serialize a built circuit `ShieldedTransfer` into the executor wire payload — exactly what a
/// client would post. There is no root to serialize, and no value.
fn to_payload(
    transfer: &dregg_circuit_prove::shielded::ShieldedTransfer,
) -> ShieldedTransferPayload {
    ShieldedTransferPayload {
        inputs: transfer
            .inputs
            .iter()
            .map(|ip| ShieldedInputPayload {
                nullifier: ip.nullifier.as_u32(),
                spend_wide_binding: ip.spend_wide_binding.map(BabyBear::as_u32),
                spend_proof: ip.proof_bytes(),
            })
            .collect(),
        outputs: transfer
            .outputs
            .iter()
            .map(|note_commitment| ShieldedOutputPayload {
                note_commitment: *note_commitment,
            })
            .collect(),
        // ⚑ ONE link proof per TRANSFER (flag day: change outputs).
        link_proof: transfer.link_proof.clone(),
    }
}

/// Assemble the honest one-in/one-out transfer over `set`: spend the note `witness` opens, mint a
/// note of the SAME value to `out_owner`. There is no `out_value` parameter, and that absence IS
/// the close — the Lean relation reads the minted note's value off the spent note's limb columns.
fn build_payload(
    witness: &ShieldedSpendCompleteWitness,
    out_owner: BabyBear,
    out_randomness: BabyBear,
) -> ShieldedTransferPayload {
    let transfer = prove_shielded_transfer(&ShieldedTransferWitness {
        spend: witness.clone(),
        out_owner,
        out_randomness,
    })
    .expect("prove the shielded transfer (complete spend + value link)");
    to_payload(&transfer)
}

/// A balanced one-in/one-out shielded transfer over a fresh committed accumulator: the set the
/// executor must hold, the payload, the spend witness (so a test can re-prove against a grown
/// tree), and the spent note's commitment.
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
    let (_rk, out_owner) = recipient(seed);
    let payload = build_payload(&witness, out_owner, BabyBear::new(0xB10B ^ seed));
    (set, payload, witness, commitment)
}

// ═══════════════════════════════════════════════════════════════════════════════
//  ⚑ THE #15 CLOSE — the forged-tree theft REFUSES on the deployed path
// ═══════════════════════════════════════════════════════════════════════════════

/// **⚑ THE EXECUTOR THEFT KAT — seam #15, on the DEPLOYED path.**
///
/// A note that was NEVER committed is spent, and only the missing pin would stop it. Here the pin
/// is present, so it stops it — inside `apply_shielded_transfer`, through the public `execute()`
/// entry.
///
/// The construction is deliberately arranged so that the ONLY variable is which accumulator the
/// executor holds. The SAME payload bytes are submitted to two executors:
///
/// * to an executor whose committed accumulator IS the attacker's tree — **ACCEPTED**. This is the
///   non-vacuity pole and it is the important one: it proves the payload is completely well formed
///   (a genuine membership proof, a genuine nullifier derivation, a genuine value link), so nothing
///   about it is malformed and the refusal below cannot be some incidental rejection wearing the
///   pin's clothes.
/// * to an executor holding the REAL accumulator (which has never seen this note) — **REFUSED**,
///   nothing spent, nothing appended.
///
/// Vacuity guards asserted BEFORE the verdict: the forged note is genuinely absent from the real
/// accumulator, and the attacker's root `R` genuinely differs from the real `root8()`. The
/// construction is CONSTRUCTIVE — the attacker's tree is built, not a mutated copy of the real one
/// — so it cannot decay into a no-op the way a `replacen`-style mutation can.
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

    // The theft payload: an honest membership proof IN THE ATTACKER'S TREE, with a genuine value
    // link. Everything a well-formed transfer needs.
    let (_rk, thief_owner) = recipient(0xBAAD);
    let theft_payload = build_payload(&forged_w, thief_owner, BabyBear::new(0xF00D));

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
        reason.contains("complete-spend"),
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
//  ⚑ THE VALUE LINK — the residual #15 named, closed, with both poles
// ═══════════════════════════════════════════════════════════════════════════════

/// **⚑ THE NEGATIVE POLE: a minted note worth more than the note it spends REFUSES.**
///
/// This is the theft the residual described, in its post-Pedersen form. Under the retired shape the
/// attacker chose a Ristretto leg worth `1_000_000` for a note worth `1`; conservation cleared over
/// the legs and nothing compared them to the note. Here the attacker's only remaining lever is the
/// value-link proof itself, so they pull it: they prove a **genuine, fully valid** value link at
/// `v' = 1_000_000` and staple it to a **genuine, fully valid** complete-spend proof of a note they
/// really own, worth `v = 1`.
///
/// **The construction is CONSTRUCTIVE, not a mutation.** Both proofs are freshly proven objects,
/// each internally satisfying its own relation — nothing is byte-poked, so this adversary cannot
/// decay into a no-op the way a `replacen`-style mutation can (`minted-a-falsifier-that-stopped-
/// falsifying`). What kills it is that the two objects disagree, and the executor supplies the
/// link's sixteen carrier public inputs FROM THE SPEND PROOF rather than from the link's own claim.
///
/// **The divergence is asserted PRESENT before any verdict is read**: the forged link's carrier
/// differs from the spend's on at least one lane, and its minted commitment differs from the honest
/// one. If either assert ever goes quiet, the adversary has stopped adversing and this test says so
/// instead of going green.
#[test]
fn value_link_divergence_refuses_on_the_deployed_path() {
    let honest_value = 1u64;
    let forged_value = 1_000_000u64;
    let (witness, set, _cm) = witness_in_set(
        honest_value,
        ASSET,
        BabyBear::new(0x5EED),
        core::array::from_fn(|i| BabyBear::new(400 + i as u32)),
        &decoys(2, 0x99),
    );
    let (_rk, out_owner) = recipient(0x99);
    let out_randomness = BabyBear::new(0x1234);

    // The HONEST transfer of that note — proven first, so its parts are available to splice.
    let honest = prove_shielded_transfer(&ShieldedTransferWitness {
        spend: witness.clone(),
        out_owner,
        out_randomness,
    })
    .expect("prove the honest transfer");

    // THE ADVERSARY: a genuine value-link proof, at a DIFFERENT value. Everything else — asset,
    // recipient, randomness — is the honest transfer's, so the ONLY difference is `v`.
    let forged_link = prove_shielded_transfer_link(&ShieldedTransferLinkWitness {
        value: forged_value,
        asset_type: ASSET,
        in_randomness: witness.randomness,
        in_binding_blind: witness.binding_blind,
        out_owner,
        out_randomness,
    })
    .expect("the forged link is a GENUINE proof of its own relation — at the wrong value");

    // ── THE MUTATION, ASSERTED PRESENT (before any verdict). ──
    assert_ne!(
        honest_value, forged_value,
        "the two values must differ, or there is no divergence to refuse"
    );
    assert_ne!(
        forged_link.claim.in_wide_binding, honest.inputs[0].spend_wide_binding,
        "VACUITY GUARD: the forged link must carry a DIFFERENT sixteen-lane carrier than the one \
         the spend proof PI-pins — that difference IS the divergence this test refuses. If these \
         ever agreed, the adversary would be proving the honest statement."
    );
    let forged_cm_bytes = felt_to_bytes32(forged_link.claim.out_note_commitment);
    assert_ne!(
        forged_cm_bytes, honest.outputs[0],
        "VACUITY GUARD: the forged mint must be a DIFFERENT note commitment than the honest one"
    );

    // The theft payload: the honest spend proof, the forged link, the forged mint.
    let theft = ShieldedTransferPayload {
        inputs: vec![ShieldedInputPayload {
            nullifier: honest.inputs[0].nullifier.as_u32(),
            spend_wide_binding: honest.inputs[0].spend_wide_binding.map(BabyBear::as_u32),
            spend_proof: honest.inputs[0].proof_bytes(),
        }],
        outputs: vec![ShieldedOutputPayload {
            note_commitment: forged_cm_bytes,
        }],
        link_proof: forged_link.proof_bytes(),
    };

    // ── NON-VACUITY: the forged link proof is REAL. Verified against ITS OWN public inputs it
    //    passes — so what refuses below is the LINK to the spend, not a malformed proof. ──
    dregg_circuit_prove::shielded::verify_shielded_transfer_link(
        &forged_link.proof_bytes(),
        &forged_link.claim.in_wide_binding,
        forged_link.claim.out_note_commitment,
    )
    .expect(
        "the forged link is a completely valid proof of the value-link relation at v'. It is not \
         malformed; it is about the wrong note. That is what makes this a theft and not a typo.",
    );

    // ── THE VERDICT. ──
    let executor = shielded_executor_holding(&set);
    let reason = refusal_reason(run(&executor, theft).expect_err(
        "a transfer whose minted note opens to a DIFFERENT value than the spent note's carrier \
         binds must REFUSE. This is the residual seam #15 named and did not close.",
    ));
    assert!(
        reason.contains("value link"),
        "the refusal must be the VALUE LINK, named — not an incidental structural rejection \
         wearing its clothes: {reason}"
    );
    assert!(
        executor.note_nullifiers.lock().unwrap().is_empty(),
        "a refused value-link theft spends NOTHING"
    );
    assert_eq!(
        executor.note_shielded.lock().unwrap().root8(),
        set.root8(),
        "a refused value-link theft mints NOTHING — the committed accumulator is untouched"
    );

    // ── AND THE HONEST TRANSFER OF THE SAME NOTE IS ADMITTED, in a fresh world holding the same
    //    committed state. The link refuses the theft without refusing the legitimate transfer. ──
    let honest_world = shielded_executor_holding(&set);
    run(&honest_world, to_payload(&honest))
        .expect("the honest transfer of the same note must be admitted");
}

/// **⚑ THE POSITIVE POLE: the honest transfer conserves, and what it mints is SPENDABLE.**
///
/// Conservation is checked the only way it can be checked once values are hidden: by exhibiting the
/// opening. The minted leaf is asserted equal to `hash_fact(v,[a,owner,rand])` for the SAME `v` the
/// spent note held — recomputed here from an independently constructed
/// `ShieldedSpendCompleteWitness` — and then that note is SPENT, through the same executor, in a
/// second transfer. Value in, same value out, and out again.
///
/// ⚑ This inverts `transfer_output_append_is_prover_written_and_cannot_be_opened_by_any_spend`,
/// whose docblock said it must be rewritten when the output relation landed. Under the retired
/// shape the appended leaf was a Ristretto point, so no spend could ever open it and value entering
/// a transfer output was unrecoverable (the L0.5 liveness gap). It is a Poseidon2 note commitment
/// now, and the second spend below is the proof.
#[test]
fn honest_transfer_conserves_and_the_minted_note_is_spendable() {
    let amount = 4_242u64;
    let (witness, set, _cm) = witness_in_set(
        amount,
        ASSET,
        BabyBear::new(0xAB0DE),
        core::array::from_fn(|i| BabyBear::new(700 + i as u32)),
        &decoys(2, 0x77),
    );
    let (recipient_key, out_owner) = recipient(0x77);
    let out_randomness = BabyBear::new(0x0BEEF);
    let payload = build_payload(&witness, out_owner, out_randomness);

    // ── CONSERVATION, exhibited. The note the recipient will hold, constructed independently from
    //    the value the SPENT note carried. ──
    let minted = ShieldedSpendCompleteWitness {
        value: amount,
        asset_type: ASSET,
        randomness: out_randomness,
        spending_key: recipient_key,
        binding_blind: witness.binding_blind,
        membership: ShieldedSpendMembership {
            positions: [0; TREE_DEPTH],
            siblings: [[[BabyBear::ZERO; 8]; 3]; TREE_DEPTH],
            next_addr: TaggedKeyWire::top(),
        },
    };
    let minted_cm = ShieldedNoteCommitment(felt_to_bytes32(minted.note_commitment_felt()));
    assert_eq!(
        payload.outputs[0].note_commitment, minted_cm.0,
        "THE CONSERVATION STATEMENT: the leaf this transfer mints is the note commitment of a note \
         worth exactly what the spent note was worth. Not `<=`, not `mod p` — the same u64, \
         because the Lean relation read one set of limb columns for both."
    );

    let executor = shielded_executor_holding(&set);
    let first = run_chained(&executor, payload, None).expect("the honest transfer is admitted");
    assert!(
        executor.note_shielded.lock().unwrap().contains(&minted_cm),
        "GATE 4 appended the value-linked Poseidon2 note commitment"
    );

    // ── SPENDABLE: the recipient spends the note they were just paid. ──
    let grown = live_accumulator(&executor);
    let minted_against = witness_against(&minted, &grown, &minted_cm);
    let (_next_key, next_owner) = recipient(0x78);
    let second = build_payload(&minted_against, next_owner, BabyBear::new(0x0F1E));
    assert_ne!(
        second.inputs[0].nullifier, 0,
        "the minted note derives its own nullifier"
    );
    run_chained(&executor, second, Some(first)).expect(
        "the note a transfer MINTED must be spendable by its recipient — this is the L0.5 \
         liveness gap closing, and it is only meaningful because the value it carries was bound",
    );
}

/// **The modulus alias, on the value-link surface.** `v` and `v + p` reduce to the SAME BabyBear
/// felt, so any one-felt binding is blind to the difference. The link's carrier is not one felt: it
/// is sixteen `cap_node8` lanes over the CANONICAL 16-bit limb decomposition, which differs between
/// the two. A link proven at `v + p` therefore carries a different carrier and refuses against the
/// spend's — even though `hash_fact(value mod p, …)` cannot tell them apart.
///
/// Constructive: the alias link is a genuine proof at `v + p`, not a poked byte.
#[test]
fn modulus_alias_output_refuses_against_the_spend_carrier() {
    let value = 5_000u64;
    let (witness, set, _cm) = witness_in_set(
        value,
        ASSET,
        BabyBear::new(0x51DE),
        core::array::from_fn(|i| BabyBear::new(900 + i as u32)),
        &decoys(2, 0x55),
    );
    let (_rk, out_owner) = recipient(0x55);
    let out_randomness = BabyBear::new(0x2222);
    let honest = prove_shielded_transfer(&ShieldedTransferWitness {
        spend: witness.clone(),
        out_owner,
        out_randomness,
    })
    .expect("prove the honest transfer");

    let aliased = value + u64::from(BABYBEAR_P);
    let alias_link = prove_shielded_transfer_link(&ShieldedTransferLinkWitness {
        value: aliased,
        asset_type: ASSET,
        in_randomness: witness.randomness,
        in_binding_blind: witness.binding_blind,
        out_owner,
        out_randomness,
    })
    .expect("the alias link is a genuine proof at v + p");

    // ── THE ALIAS, ASSERTED PRESENT: same felt, different limbs, different carrier. ──
    assert_eq!(
        aliased % u64::from(BABYBEAR_P),
        value % u64::from(BABYBEAR_P),
        "v and v + p must reduce to the SAME felt — that is what makes this an alias"
    );
    assert_eq!(
        felt_to_bytes32(alias_link.claim.out_note_commitment),
        honest.outputs[0],
        "AND THE ONE-FELT SURFACE IS BLIND TO IT: the alias mints the very SAME note commitment, \
         because `hash_fact(value mod p, …)` cannot separate v from v + p. Every narrow binding in \
         this system agrees with the attacker here."
    );
    assert_ne!(
        alias_link.claim.in_wide_binding, honest.inputs[0].spend_wide_binding,
        "VACUITY GUARD: the alias must move the SIXTEEN-LANE carrier even though it does not move \
         the reduced felt — that separation is the whole reason the carrier is wide"
    );

    let theft = ShieldedTransferPayload {
        inputs: vec![ShieldedInputPayload {
            nullifier: honest.inputs[0].nullifier.as_u32(),
            spend_wide_binding: honest.inputs[0].spend_wide_binding.map(BabyBear::as_u32),
            spend_proof: honest.inputs[0].proof_bytes(),
        }],
        outputs: vec![ShieldedOutputPayload {
            note_commitment: felt_to_bytes32(alias_link.claim.out_note_commitment),
        }],
        link_proof: alias_link.proof_bytes(),
    };
    let executor = shielded_executor_holding(&set);
    let reason = refusal_reason(
        run(&executor, theft).expect_err("an x+p link spliced over an x spend must reject"),
    );
    assert!(
        reason.contains("value link"),
        "the alias splice must die at the value link: {reason}"
    );
    assert!(executor.note_nullifiers.lock().unwrap().is_empty());
}

// ═══════════════════════════════════════════════════════════════════════════════
//  Double-spend
// ═══════════════════════════════════════════════════════════════════════════════

/// **A genuine double-spend REFUSES at the nullifier gate.**
///
/// The attacker does what a real attacker does: after the first transfer lands, they RE-PROVE the
/// same note's spend against the GROWN accumulator, with a fresh output. The membership proof is
/// genuine and current, the value link is genuine — and the nullifier, being derived from the note,
/// is the same. The cross-transfer double-spend gate is what refuses it.
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
    let (_rk, other_owner) = recipient(0x13FF);
    let second_payload = build_payload(&reproved, other_owner, BabyBear::new(0x5A5A));
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
//  Decoder / arity / fail-closed / unlinkability
// ═══════════════════════════════════════════════════════════════════════════════

/// A non-canonical BabyBear encoding in the ring carrier's public lanes is refused at the decoder,
/// before any proof work — `x + p` must never be accepted as `x`.
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

/// A minted note commitment OUTSIDE the spendable address subspace is refused before it can be
/// appended. `felt_to_bytes32` is four significant bytes and twenty-eight zero; the complete-spend
/// relation pins `cADDR0`/`cADDR1` and constrains the higher limbs to zero, so a leaf outside that
/// subspace could be appended and never opened again — value in, never out.
#[test]
fn noncanonical_note_commitment_rejects_before_it_can_be_appended() {
    let (set, mut payload, _w, _cm) = balanced(34);
    let executor = shielded_executor_holding(&set);
    payload.outputs[0].note_commitment[31] = 1;
    let reason = refusal_reason(
        run(&executor, payload).expect_err("a non-felt-encoded note commitment must reject"),
    );
    assert!(
        reason.contains("canonical felt encoding"),
        "the refusal must name the encoding: {reason}"
    );
    assert_eq!(
        executor.note_shielded.lock().unwrap().root8(),
        set.root8(),
        "nothing was appended"
    );
}

/// An arity the deployed value-link descriptor does not state REFUSES rather than being admitted
/// without a conservation statement. Today that is anything but one-in/one-out.
#[test]
fn unstated_arity_refuses_rather_than_being_admitted() {
    let (set, mut payload, _w, _cm) = balanced(35);
    let executor = shielded_executor_holding(&set);

    // ⚑ 2026-08-07 — THIS TEST'S BAR MOVED, and the move is the point. `1-in/2-out` used to be the
    // canonical unstated arity; it is now the SPLIT, stated by
    // `dregg-shielded-transfer-value-link-2out::v1` and gated in
    // `circuit-prove/tests/shielded_transfer_split.rs`. The refusal this test guards therefore
    // starts at the first arity the Lean family still does not state.
    let extra = payload.outputs[0].clone();
    payload.outputs.push(extra.clone());
    payload.outputs.push(extra);
    let reason = refusal_reason(
        run(&executor, payload).expect_err("a 1-in/3-out transfer has no stated conservation"),
    );
    assert!(
        reason.contains("not stated by the deployed value-link descriptor"),
        "the refusal must name the missing descriptor, so the next reader knows this is a gap in \
         the Lean family and not a bug: {reason}"
    );
    assert!(
        reason.contains("[1, 2]"),
        "and it must name the arities that ARE stated — a message frozen at the old single arity \
         would be a documented wound rather than a detected one: {reason}"
    );

    // The empty arity refuses too, at the layer where the message is clearest.
    let (set, mut payload, _w, _cm) = balanced(36);
    let executor = shielded_executor_holding(&set);
    payload.outputs.clear();
    let reason = refusal_reason(
        run(&executor, payload).expect_err("a transfer minting nothing has nothing to link"),
    );
    assert!(
        reason.contains("no outputs"),
        "the empty-output refusal must say so: {reason}"
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
        a.outputs[0].note_commitment, b.outputs[0].note_commitment,
        "equal amounts must still mint distinct (blinded) note commitments"
    );
    assert_ne!(
        a.inputs[0].spend_proof, b.inputs[0].spend_proof,
        "the hidden proofs reveal nothing linking the two transfers"
    );
    assert_ne!(
        a.link_proof, b.link_proof,
        "nor do the hidden value-link proofs"
    );
    assert_ne!(
        a.inputs[0].spend_wide_binding, b.inputs[0].spend_wide_binding,
        "the ring carriers retain fresh hidden blinding"
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
        "the admitted transfer landed its minted note"
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
    let expected_commitment = ShieldedNoteCommitment(payload.outputs[0].note_commitment);

    let verified = dregg_turn::ShieldedTransferVerifier::verify(
        &CircuitShieldedTransferVerifier::new(),
        &payload,
        set.root8().limbs(),
    )
    .expect("a valid transfer verifies under the committed root");

    assert_eq!(
        verified.nullifiers,
        vec![payload.inputs[0].nullifier],
        "the returned nullifiers are the ones the STARK proved"
    );
    assert_eq!(
        verified.output_commitments,
        vec![expected_commitment],
        "the returned commitments are what the core executor appends and journals — and they are \
         value-linked Poseidon2 note commitments, not prover-chosen group elements"
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
