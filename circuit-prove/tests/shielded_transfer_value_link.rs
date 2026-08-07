//! Both-polarity gate for the shielded transfer's **VALUE LINK**, at the circuit layer.
//!
//! **SAY THE SUBSTRATE OUT LOUD: the AIR is AUTHORED IN LEAN.** The relation under test is
//! `dregg-shielded-transfer-value-link::v1`
//! (`metatheory/Dregg2/Circuit/Emit/ShieldedTransferValueLinkEmit.lean`, 164 columns, 17 PIs
//! `wide[16] ++ [outCm]`, byte-pinned there by `link_emits_golden`). This file authors no
//! constraint: it builds witnesses, proves, and reads verdicts. These are behaviour tests over the
//! DEPLOYED path — not refinement, not translation validation, not verification.
//!
//! ## What it replaces, and why the old file is gone
//!
//! `shielded_transfer_m2a.rs` tested the Pedersen half end to end: `Σ C_in = Σ C_out` over
//! prover-chosen Ristretto legs, Bulletproof range proofs, and `verify_value_link` — the
//! compatibility bridge that was *exercised only in tests* and never on the deployed path. That
//! mechanism is DELETED (see `circuit-prove/src/shielded/transfer.rs`), so its tests went with it
//! rather than being kept green over an object nothing loads.
//!
//! The residual seam #15's lane named was exactly that gap: *"the Pedersen leg's own `v` is bound to
//! the STARK-side `v` only through this TRANSCRIPT, not by any circuit equality (`verify_value_link`
//! is test-only)."* What stands in its place is a single Lean relation that reads ONE set of
//! canonical 16-bit limb columns for both the spent note's sixteen carrier lanes and the minted
//! note's commitment.

use dregg_cell::{ShieldedNoteCommitment, ShieldedNoteSet, felt_to_bytes32};
use dregg_circuit::exact_nullifier_aafi::TaggedKeyWire;
use dregg_circuit::field::{BABYBEAR_P, BabyBear};
use dregg_circuit::poseidon2::hash_fact;
use dregg_circuit_prove::shielded::{
    BINDING_BLIND_LANES, DEPLOYED_INPUTS, DEPLOYED_OUTPUTS, ShieldedOutput,
    ShieldedSpendCompleteWitness, ShieldedSpendMembership, ShieldedTransferLinkWitness,
    ShieldedTransferWitness, TREE_DEPTH, note_commitment_felt_from_bytes, prove_shielded_transfer,
    prove_shielded_transfer_link, shielded_transfer_value_link_descriptor,
    verify_shielded_transfer_link,
};

fn blind() -> [BabyBear; BINDING_BLIND_LANES] {
    core::array::from_fn(|i| BabyBear::new(0x1000 + (i as u32) * 0x111))
}

fn recipient(seed: u32) -> ([BabyBear; 4], BabyBear) {
    let key: [BabyBear; 4] =
        core::array::from_fn(|i| BabyBear::new(seed.wrapping_mul(37) + i as u32 + 3));
    (key, hash_fact(key[0], &[key[1], key[2], key[3]]))
}

/// A COMPLETE-spend witness over a REAL committed `ShieldedNoteSet`.
fn spend_in_set(
    value: u64,
    asset: u64,
    randomness: BabyBear,
) -> (ShieldedSpendCompleteWitness, ShieldedNoteSet) {
    let probe = ShieldedSpendCompleteWitness {
        value,
        asset_type: asset,
        randomness,
        spending_key: [
            BabyBear::new(11),
            BabyBear::new(13),
            BabyBear::new(17),
            BabyBear::new(19),
        ],
        binding_blind: blind(),
        membership: ShieldedSpendMembership {
            positions: [0; TREE_DEPTH],
            siblings: [[[BabyBear::ZERO; 8]; 3]; TREE_DEPTH],
            next_addr: TaggedKeyWire::top(),
        },
    };
    let commitment = ShieldedNoteCommitment(felt_to_bytes32(probe.note_commitment_felt()));
    let mut set = ShieldedNoteSet::new();
    set.insert(ShieldedNoteCommitment(felt_to_bytes32(BabyBear::new(
        0x0A0A_0001,
    ))))
    .expect("decoy inserts");
    set.insert(commitment).expect("the spent note is committed");
    let path = set
        .membership_path(&commitment)
        .expect("the committed note has a membership path");
    (
        ShieldedSpendCompleteWitness {
            membership: ShieldedSpendMembership {
                positions: path.path.positions,
                siblings: path.path.siblings,
                next_addr: path.leaf.next_addr().wire(),
            },
            ..probe
        },
        set,
    )
}

/// The relation the deployed path loads IS the Lean-emitted one, at the shape the Lean file's named
/// theorems pin. A drift in either direction (Lean moves, or Rust's mirror moves) shows up here.
#[test]
fn the_deployed_value_link_relation_is_the_lean_emitted_one() {
    let desc = shielded_transfer_value_link_descriptor();
    assert_eq!(desc.name, "dregg-shielded-transfer-value-link::v1");
    assert_eq!(
        desc.trace_width, 164,
        "LINK_WIDTH — ShieldedTransferValueLinkEmit.LINK_WIDTH_eq"
    );
    assert_eq!(
        desc.public_input_count, 17,
        "wide[16] ++ [outCm] — ShieldedTransferValueLinkEmit.LINK_PI_COUNT_eq"
    );
    assert_eq!(
        desc.constraints.len(),
        158,
        "128 boolean pins + 8 limb recompositions + 2 reductions + 2 carriers + 1 fact site + 17 \
         pins — ShieldedTransferValueLinkEmit.constraint_census"
    );
}

/// ⚑ **BOTH POLES, at the relation.** The honest link verifies against the public inputs the
/// executor supplies; a link proven at a DIFFERENT value does not — and the divergence is asserted
/// present before either verdict is read.
///
/// Constructive, not a mutation: both proofs are freshly proven objects that each satisfy the
/// relation internally. Nothing is byte-poked, so the adversary cannot decay into a no-op.
#[test]
fn a_link_proven_at_a_different_value_cannot_verify_against_the_spent_carrier() {
    let value = 7u64;
    let forged = 7_000_000u64;
    let asset = 3u64;
    let randomness = BabyBear::new(0x4242);
    let (_key, out_owner) = recipient(5);
    let out_randomness = BabyBear::new(0x9999);

    let honest = prove_shielded_transfer_link(&ShieldedTransferLinkWitness {
        value,
        asset_type: asset,
        in_randomness: randomness,
        in_binding_blind: blind(),
        out_owner,
        out_randomness,
    })
    .expect("the honest link proves");
    let theft = prove_shielded_transfer_link(&ShieldedTransferLinkWitness {
        value: forged,
        asset_type: asset,
        in_randomness: randomness,
        in_binding_blind: blind(),
        out_owner,
        out_randomness,
    })
    .expect("the forged link is a GENUINE proof of the relation — at the wrong value");

    // ── THE DIVERGENCE, ASSERTED PRESENT. ──
    assert_ne!(value, forged);
    assert_ne!(
        honest.claim.in_wide_binding, theft.claim.in_wide_binding,
        "VACUITY GUARD: the two values must produce DIFFERENT sixteen-lane carriers, or there is \
         nothing for the join to separate"
    );
    assert_ne!(
        honest.claim.out_note_commitment, theft.claim.out_note_commitment,
        "VACUITY GUARD: and different minted notes"
    );

    // ── POSITIVE: each proof verifies against its OWN public inputs (neither is malformed). ──
    verify_shielded_transfer_link(
        &honest.proof_bytes(),
        &honest.claim.in_wide_binding,
        honest.claim.out_note_commitment,
    )
    .expect("the honest link verifies");
    verify_shielded_transfer_link(
        &theft.proof_bytes(),
        &theft.claim.in_wide_binding,
        theft.claim.out_note_commitment,
    )
    .expect("the forged link is valid ABOUT ITS OWN STATEMENT — it is about the wrong note");

    // ── NEGATIVE: the forged mint, judged against the carrier of the note actually spent. ──
    assert!(
        verify_shielded_transfer_link(
            &theft.proof_bytes(),
            &honest.claim.in_wide_binding,
            theft.claim.out_note_commitment,
        )
        .is_err(),
        "a minted note that opens to v' != v must NOT verify against the spent note's carrier — \
         this is the residual seam #15 named, refusing"
    );
    // ── And the mirror: the honest proof cannot be re-pointed at a richer mint either. ──
    assert!(
        verify_shielded_transfer_link(
            &honest.proof_bytes(),
            &honest.claim.in_wide_binding,
            theft.claim.out_note_commitment,
        )
        .is_err(),
        "nor can an honest proof be spliced onto a different minted commitment"
    );
}

/// The modulus alias, where it matters. `v` and `v + p` reduce to the SAME felt, so the minted note
/// commitment `hash_fact(value mod p, …)` is IDENTICAL — every narrow binding in the system agrees
/// with the attacker. The sixteen-lane carrier does not: it absorbs the canonical 16-bit limbs.
#[test]
fn the_modulus_alias_moves_the_carrier_but_not_the_minted_commitment() {
    let value = 0x1234_5678_9abc_def0u64;
    let alias = value + u64::from(BABYBEAR_P);
    let asset = 0xfedc_ba98_7654_3210u64;
    let (_key, out_owner) = recipient(9);
    let w = |v: u64| ShieldedTransferLinkWitness {
        value: v,
        asset_type: asset,
        in_randomness: BabyBear::new(0x13579),
        in_binding_blind: blind(),
        out_owner,
        out_randomness: BabyBear::new(0x2468),
    };
    let honest = w(value);
    let aliased = w(alias);
    assert_eq!(
        honest.out_note_commitment_felt(),
        aliased.out_note_commitment_felt(),
        "the one-felt note commitment CANNOT separate v from v + p"
    );
    assert_ne!(
        honest.in_wide_binding(),
        aliased.in_wide_binding(),
        "the sixteen-lane carrier CAN — that separation is why it is wide"
    );
}

/// The transfer object's own gates: the committed root decides, the arity is stated, and a
/// non-canonical minted commitment refuses before it could be appended.
#[test]
fn transfer_gates_root_arity_and_commitment_encoding() {
    let (spend, set) = spend_in_set(500, 1, BabyBear::new(0x777));
    let (_key, out_owner) = recipient(21);
    let mut transfer = prove_shielded_transfer(&ShieldedTransferWitness {
        spend,
        out_owner,
        out_randomness: BabyBear::new(0x321),
    })
    .expect("the honest transfer proves");

    transfer
        .verify(set.root8().limbs())
        .expect("the honest transfer verifies under its own committed root");
    assert!(
        transfer
            .verify(ShieldedNoteSet::new().root8().limbs())
            .is_err(),
        "a spend judged under a foreign committed root must reject (seam #15)"
    );

    // The arity the descriptor states, and the refusal outside it.
    assert_eq!((DEPLOYED_INPUTS, DEPLOYED_OUTPUTS), (1, 1));
    let extra = ShieldedOutput {
        note_commitment: transfer.outputs[0].note_commitment,
        link_proof: transfer.outputs[0].link_proof.clone(),
    };
    transfer.outputs.push(extra);
    let err = transfer
        .verify(set.root8().limbs())
        .expect_err("1-in/2-out has no stated conservation and must refuse");
    assert!(
        err.to_string().contains("not stated by the deployed"),
        "the refusal must name the missing descriptor: {err}"
    );
    transfer.outputs.truncate(1);

    // A minted commitment outside the spendable address subspace refuses before any append.
    let good = transfer.outputs[0].note_commitment;
    assert!(note_commitment_felt_from_bytes(&good).is_ok());
    let mut bad = good;
    bad[31] = 1;
    assert!(
        note_commitment_felt_from_bytes(&bad).is_err(),
        "a leaf outside felt_to_bytes32's four-significant-byte subspace could be appended and \
         never opened again — value in, never out"
    );
}

/// HIDING: two transfers of the SAME value with different blinding produce different proofs and
/// different minted commitments. Nothing about the amount leaks onto the wire.
#[test]
fn equal_value_transfers_do_not_look_alike() {
    let (_k1, owner_a) = recipient(31);
    let (_k2, owner_b) = recipient(32);
    let a = prove_shielded_transfer_link(&ShieldedTransferLinkWitness {
        value: 12_345,
        asset_type: 1,
        in_randomness: BabyBear::new(1),
        in_binding_blind: blind(),
        out_owner: owner_a,
        out_randomness: BabyBear::new(11),
    })
    .expect("a proves");
    let b = prove_shielded_transfer_link(&ShieldedTransferLinkWitness {
        value: 12_345,
        asset_type: 1,
        in_randomness: BabyBear::new(2),
        in_binding_blind: blind(),
        out_owner: owner_b,
        out_randomness: BabyBear::new(22),
    })
    .expect("b proves");
    assert_ne!(a.claim.in_wide_binding, b.claim.in_wide_binding);
    assert_ne!(a.claim.out_note_commitment, b.claim.out_note_commitment);
    assert_ne!(a.proof_bytes(), b.proof_bytes());
}
