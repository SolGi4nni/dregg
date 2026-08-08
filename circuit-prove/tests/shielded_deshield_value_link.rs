//! Both-polarity gate for the shielded **OFF-RAMP**'s value link, at the circuit layer.
//!
//! **SAY THE SUBSTRATE OUT LOUD: the AIR is AUTHORED IN LEAN.** The relation under test is
//! `dregg-shielded-deshield-value-link::v1`
//! (`metatheory/Dregg2/Circuit/Emit/ShieldedDeshieldValueLinkEmit.lean`, 161 columns, 24 PIs
//! `wide[16] ++ vLimb[4] ++ aLimb[4]`, byte-pinned there by `deshield_emits_golden`). This file
//! authors no constraint: it builds witnesses, proves, and reads verdicts. These are behaviour
//! tests over the DEPLOYED path — not refinement, not translation validation, not verification.
//!
//! ## What was missing, and what the poles are
//!
//! Value could ENTER the pool (`Effect::Shield`) and MOVE inside it (`ShieldedTransfer`). It could
//! never LEAVE. The off-ramp's failure mode is the on-ramp's, reflected: a deshield that **credits
//! more cleartext than the note it spends holds**. It is the easier theft of the two, because the
//! credit is a plain `u64` on the wire while the spent note's value is hidden — so "the proof
//! verified" would mean nothing if the credit were merely carried alongside it.

use dregg_cell::{ShieldedNoteCommitment, ShieldedNoteSet, felt_to_bytes32};
use dregg_circuit::exact_nullifier_aafi::TaggedKeyWire;
use dregg_circuit::field::{BABYBEAR_P, BabyBear};
use dregg_circuit_prove::shielded::{
    BINDING_BLIND_LANES, DEPLOYED_DESHIELD_INPUTS, ShieldedDeshieldLinkWitness,
    ShieldedDeshieldWitness, ShieldedSpendCompleteWitness, ShieldedSpendMembership, TREE_DEPTH,
    credit_from_public_limbs, credit_limbs_of, prove_shielded_deshield,
    prove_shielded_deshield_link, shielded_deshield_value_link_descriptor,
    verify_shielded_deshield_link,
};

fn blind() -> [BabyBear; BINDING_BLIND_LANES] {
    core::array::from_fn(|i| BabyBear::new(0x1000 + (i as u32) * 0x111))
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
        0x0B0B_0001,
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
fn the_deployed_deshield_relation_is_the_lean_emitted_one() {
    let desc = shielded_deshield_value_link_descriptor();
    assert_eq!(desc.name, "dregg-shielded-deshield-value-link::v1");
    assert_eq!(
        desc.trace_width, 161,
        "DESHIELD_WIDTH — ShieldedDeshieldValueLinkEmit.DESHIELD_WIDTH_eq"
    );
    assert_eq!(
        desc.public_input_count, 24,
        "wide[16] ++ vLimb[4] ++ aLimb[4] — ShieldedDeshieldValueLinkEmit.DESHIELD_PI_COUNT_eq"
    );
    assert_eq!(
        desc.constraints.len(),
        164,
        "128 boolean pins + 8 limb recompositions + 2 reductions + 2 carriers + 24 pins — \
         ShieldedDeshieldValueLinkEmit.constraint_census"
    );
}

/// ⚑ **THE NEGATIVE POLE, at the relation.** A deshield crediting MORE cleartext than the spent
/// note holds must REFUSE.
///
/// Constructive, not a mutation: both proofs are freshly proven objects that each satisfy the
/// relation internally, over the SAME spent-note randomness and blinds. Nothing is byte-poked, so
/// the adversary cannot decay into a no-op the way a `replacen` of an absent string does.
#[test]
fn a_credit_proven_at_a_different_value_cannot_verify_against_the_spent_carrier() {
    let value = 7u64;
    let inflated = 1_000_000u64;
    let asset = 3u64;
    let randomness = BabyBear::new(0x4242);

    let honest = prove_shielded_deshield_link(&ShieldedDeshieldLinkWitness {
        value,
        asset_type: asset,
        in_randomness: randomness,
        in_binding_blind: blind(),
    })
    .expect("the honest off-ramp link proves");
    let theft = prove_shielded_deshield_link(&ShieldedDeshieldLinkWitness {
        value: inflated,
        asset_type: asset,
        in_randomness: randomness,
        in_binding_blind: blind(),
    })
    .expect("the inflated link is a GENUINE proof of the relation — at the wrong value");

    // ── THE DIVERGENCE, ASSERTED PRESENT, BEFORE ANY VERDICT IS READ. ──
    assert_ne!(value, inflated);
    assert_ne!(
        honest.claim.in_wide_binding, theft.claim.in_wide_binding,
        "VACUITY GUARD: the two values must produce DIFFERENT sixteen-lane carriers, or there is \
         nothing for the join to separate"
    );
    assert_ne!(
        honest.claim.credit_limbs, theft.claim.credit_limbs,
        "VACUITY GUARD: and different published credit limbs"
    );
    assert_eq!(
        honest.claim.credit().expect("honest limbs recompose"),
        (value, asset),
        "the honest proof publishes exactly the value it was proven at"
    );
    assert_eq!(
        theft.claim.credit().expect("theft limbs recompose"),
        (inflated, asset),
        "and the theft publishes the INFLATED one — the attack is genuinely constructed"
    );

    // ── POSITIVE: each proof verifies against its OWN public inputs (neither is malformed). ──
    verify_shielded_deshield_link(
        &honest.proof_bytes(),
        &honest.claim.in_wide_binding,
        value,
        asset,
    )
    .expect("the honest link verifies");
    verify_shielded_deshield_link(
        &theft.proof_bytes(),
        &theft.claim.in_wide_binding,
        inflated,
        asset,
    )
    .expect("the inflated link is valid ABOUT ITS OWN STATEMENT — it is about the wrong note");

    // ── ⚑ NEGATIVE: the inflated credit, judged against the carrier of the note ACTUALLY spent. ──
    assert!(
        verify_shielded_deshield_link(
            &theft.proof_bytes(),
            &honest.claim.in_wide_binding,
            inflated,
            asset,
        )
        .is_err(),
        "a cleartext credit of v' != v must NOT verify against the spent note's carrier — this is \
         the off-ramp's mint, refusing"
    );
    // ── And the mirror: the honest proof cannot be re-pointed at a richer credit either. ──
    assert!(
        verify_shielded_deshield_link(
            &honest.proof_bytes(),
            &honest.claim.in_wide_binding,
            inflated,
            asset,
        )
        .is_err(),
        "nor can an honest proof be spliced onto a larger declared credit"
    );
    // ── The pool must not silently EAT value either: crediting less also refuses. ──
    assert!(
        verify_shielded_deshield_link(
            &honest.proof_bytes(),
            &honest.claim.in_wide_binding,
            value - 1,
            asset,
        )
        .is_err(),
        "a credit SMALLER than the spent note must also refuse — a one-way leak is still a leak"
    );
    // ── And the ASSET half: a note denominated in A cannot fund a credit in A'. ──
    assert!(
        verify_shielded_deshield_link(
            &honest.proof_bytes(),
            &honest.claim.in_wide_binding,
            value,
            asset + 1,
        )
        .is_err(),
        "a credit in a DIFFERENT asset must refuse (Lean substituted_credit_asset_unsat)"
    );
}

/// The modulus alias, at the place it would arrive as free money.
///
/// `v` and `v + p` reduce to the SAME `value mod p` felt. If the public credit rode that reduction,
/// a note worth `v` would fund a credit of `v + p`. It rides the four canonical 16-bit limbs
/// instead, which separate them — and so does the sixteen-lane carrier.
#[test]
fn the_modulus_alias_moves_both_the_carrier_and_the_published_credit_limbs() {
    let value = 0x1234_5678_9abc_def0u64;
    let alias = value + u64::from(BABYBEAR_P);
    let asset = 0xfedc_ba98_7654_3210u64;
    let w = |v: u64| ShieldedDeshieldLinkWitness {
        value: v,
        asset_type: asset,
        in_randomness: BabyBear::new(0x13579),
        in_binding_blind: blind(),
    };
    let honest = w(value);
    let aliased = w(alias);
    assert_ne!(
        honest.in_wide_binding(),
        aliased.in_wide_binding(),
        "the sixteen-lane carrier separates v from v + p — that is why it is wide"
    );
    assert_ne!(
        honest.credit_limbs(),
        aliased.credit_limbs(),
        "and so do the published limbs — which is why the credit is NOT `value mod p`, the one \
         encoding that could not tell these apart"
    );
    // The recomposition is total and exact over the integers on both.
    assert_eq!(
        credit_from_public_limbs(&honest.credit_limbs()).expect("recomposes"),
        (value, asset)
    );
    assert_eq!(
        credit_from_public_limbs(&aliased.credit_limbs()).expect("recomposes"),
        (alias, asset)
    );
    assert_eq!(credit_limbs_of(value, asset), honest.credit_limbs());
}

/// ⚑ **THE POSITIVE POLE, at the object.** An honest deshield verifies under its own committed
/// root, publishes exactly the spent note's value as its cleartext credit, and refuses under a
/// foreign root (seam #15, inherited) or at an unstated arity.
#[test]
fn honest_deshield_credits_the_spent_notes_value_and_refuses_off_root() {
    let value = 500u64;
    let asset = 1u64;
    let (spend, set) = spend_in_set(value, asset, BabyBear::new(0x777));
    let mut deshield = prove_shielded_deshield(&ShieldedDeshieldWitness { spend })
        .expect("the honest deshield proves");

    // The credit is what the note holds — read off the relation's published limbs, not the witness.
    assert_eq!(
        (deshield.credit.value, deshield.credit.asset_type),
        (value, asset),
        "the cleartext credit IS the spent note's value; no prover chose it"
    );

    deshield
        .verify(set.root8().limbs())
        .expect("the honest deshield verifies under its own committed root");
    assert!(
        deshield
            .verify(ShieldedNoteSet::new().root8().limbs())
            .is_err(),
        "a spend judged under a foreign committed root must reject (seam #15)"
    );

    // ⚑ The executor-visible theft, at the object: declare a bigger credit over the SAME proofs.
    let honest_credit = deshield.credit.value;
    deshield.credit.value = honest_credit * 2;
    assert_ne!(
        deshield.credit.value, honest_credit,
        "the mutation is PRESENT: the declared credit is now double the note"
    );
    let err = deshield
        .verify(set.root8().limbs())
        .expect_err("a deshield declaring twice the note's value MUST refuse");
    assert!(
        err.to_string().contains("credit"),
        "the refusal must name the credit link, not masquerade as a spend failure: {err}"
    );
    deshield.credit.value = honest_credit;
    deshield
        .verify(set.root8().limbs())
        .expect("and restoring the honest credit restores acceptance — the gate is not stuck red");

    // The arity the descriptor states, and the refusal outside it.
    assert_eq!(DEPLOYED_DESHIELD_INPUTS, 1);
    deshield.inputs.clear();
    assert!(
        deshield.verify(set.root8().limbs()).is_err(),
        "a deshield with no spent note has nothing to credit against and must refuse"
    );
}

/// HIDING, as far as an off-ramp can hide: two deshields of the SAME value with different blinding
/// produce different carriers and different proofs. The value itself is public — that is what an
/// off-ramp IS — but nothing links the two spends to each other or to their notes.
#[test]
fn equal_value_deshields_do_not_look_alike_beyond_the_value_they_declare() {
    let a = prove_shielded_deshield_link(&ShieldedDeshieldLinkWitness {
        value: 12_345,
        asset_type: 1,
        in_randomness: BabyBear::new(1),
        in_binding_blind: blind(),
    })
    .expect("a proves");
    let b = prove_shielded_deshield_link(&ShieldedDeshieldLinkWitness {
        value: 12_345,
        asset_type: 1,
        in_randomness: BabyBear::new(2),
        in_binding_blind: blind(),
    })
    .expect("b proves");
    assert_ne!(
        a.claim.in_wide_binding, b.claim.in_wide_binding,
        "different blinding ⇒ different carriers, so the two spends are unlinkable"
    );
    assert_eq!(
        a.claim.credit_limbs, b.claim.credit_limbs,
        "the CREDIT is public and equal — an off-ramp reveals the value, and pretending otherwise \
         would be the dishonest claim here"
    );
    assert_ne!(a.proof_bytes(), b.proof_bytes());
}
