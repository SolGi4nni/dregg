//! Fast hostile gate for the PoA signed-envelope boundary.
//!
//! This test intentionally has no happy mint: until a Lean-owned transition
//! verifier consumes the receipt, an otherwise valid issuer signature must
//! still fail closed and leave the asset world empty.
//!
//! Discovery gate:
//! `cargo nextest list -p dreggnet-market --features poa-expedition --test poa_expedition_ingress`
//!
//! Fast execution gate:
//! `cargo nextest run -p dreggnet-market --features poa-expedition --test poa_expedition_ingress`

#![cfg(feature = "poa-expedition")]

use dreggnet_market::poa_expedition::{
    POA_DECK_COUNT, POA_SALVAGE_SLOTS, PoaContributionBounds, PoaContributionClaim,
    PoaExpeditionClaim, PoaExpeditionError, PoaExpeditionPolicy, PoaExpeditionReceipt,
    PoaSalvageMinter,
};
use dungeon_on_dregg::loot::LootVault;
use ed25519_dalek::{Signer as _, SigningKey};

const PLAYER: &str = "poa-expedition:alice";

#[test]
fn signed_poa_envelope_refuses_every_substitution_and_cannot_mint_unjudged() {
    let federation = [0x11; 32];
    let session = [0x12; 32];
    let mission = [0x13; 32];
    let artifact = [0x14; 32];
    let issuer = SigningKey::from_bytes(&[0x15; 32]);
    let mut vault = LootVault::new();
    let player_key = vault.pubkey_of(PLAYER);
    let bounds = PoaContributionBounds {
        intel: 8,
        supplies: 8,
        cohesion: 8,
        influence: 8,
        score: 100,
    };
    let claim = PoaExpeditionClaim::new(
        federation,
        session,
        mission,
        artifact,
        [0x16; 32],
        [0x17; 32],
        [0x18; 32],
        PLAYER,
        player_key,
        1,
        447,
        0,
        PoaContributionClaim {
            intel: 3,
            supplies: 1,
            cohesion: 2,
            influence: 0,
            score: 17,
            relics: vec![447_001],
        },
        [0x19; 32],
    );
    let receipt = PoaExpeditionReceipt::issue(claim.clone(), &issuer);
    let policy = PoaExpeditionPolicy::new(
        federation,
        session,
        mission,
        artifact,
        bounds,
        issuer.verifying_key(),
    );
    let mut minter = PoaSalvageMinter::new(policy);

    let mut exact_message = b"pathofangels.network/run-receipt/v1\0".to_vec();
    exact_message.extend_from_slice(&claim.canonical_fields());
    issuer
        .verifying_key()
        .verify_strict(
            &exact_message,
            &ed25519_dalek::Signature::from_bytes(&receipt.signature),
        )
        .expect("the envelope is exactly the protocol domain plus canonical fields");

    let mut forged = receipt.clone();
    forged.signature[0] ^= 1;
    assert_eq!(
        minter.mint(&mut vault, &forged).unwrap_err(),
        PoaExpeditionError::InvalidSignature
    );

    let mut wrong_domain_message = b"pathofangels.network/wrong-domain/v1\0".to_vec();
    wrong_domain_message.extend_from_slice(&claim.canonical_fields());
    let wrong_domain = PoaExpeditionReceipt {
        claim: claim.clone(),
        signature: issuer.sign(&wrong_domain_message).to_bytes(),
    };
    assert_eq!(
        minter.mint(&mut vault, &wrong_domain).unwrap_err(),
        PoaExpeditionError::InvalidSignature
    );

    for (mutation, expected) in [
        (0, PoaExpeditionError::WrongFederation),
        (1, PoaExpeditionError::WrongSession),
        (2, PoaExpeditionError::WrongMission),
        (3, PoaExpeditionError::WrongArtifact),
        (4, PoaExpeditionError::ContributionOutOfBounds),
        (5, PoaExpeditionError::ContributionOutOfBounds),
        (6, PoaExpeditionError::InvalidStateTransition),
        (7, PoaExpeditionError::WrongVersion),
        (8, PoaExpeditionError::MissingRunReceipt),
        (9, PoaExpeditionError::InvalidStateTransition),
        (10, PoaExpeditionError::InvalidStateTransition),
        (11, PoaExpeditionError::InvalidPlayer),
        (12, PoaExpeditionError::InvalidPlayer),
        (13, PoaExpeditionError::InvalidPlayer),
        (14, PoaExpeditionError::InvalidPlayer),
        (15, PoaExpeditionError::DeckOutOfBounds),
        (16, PoaExpeditionError::SalvageSlotOutOfBounds),
    ] {
        let mut hostile = claim.clone();
        match mutation {
            0 => hostile.federation[0] ^= 1,
            1 => hostile.session[0] ^= 1,
            2 => hostile.mission[0] ^= 1,
            3 => hostile.artifact_digest[0] ^= 1,
            4 => hostile.contribution.score = bounds.score + 1,
            5 => hostile.contribution.relics = vec![447_001, 447_001],
            6 => hostile.post_state = hostile.pre_state,
            7 => hostile.version += 1,
            8 => hostile.run_receipt = [0; 32],
            9 => hostile.pre_state = [0; 32],
            10 => hostile.post_state = [0; 32],
            11 => hostile.player.clear(),
            12 => hostile.player = "x".repeat(129),
            13 => hostile.player_key = [0; 32],
            14 => hostile.counter = 0,
            15 => hostile.deck = POA_DECK_COUNT,
            16 => hostile.salvage_slot = POA_SALVAGE_SLOTS,
            _ => unreachable!(),
        }
        let hostile = PoaExpeditionReceipt::issue(hostile, &issuer);
        assert_eq!(minter.mint(&mut vault, &hostile).unwrap_err(), expected);
    }

    // These replacements remain individually valid admission values. They are
    // refused because the signature binds every field, not because a range
    // check happens to reject the replacement first.
    for substitution in 0..5 {
        let mut altered = claim.clone();
        match substitution {
            0 => altered.run_seed[0] ^= 1,
            1 => altered.player.push_str(":substituted"),
            2 => altered.counter += 1,
            3 => altered.deck += 1,
            4 => altered.salvage_slot += 1,
            _ => unreachable!(),
        }
        let stale_signature = PoaExpeditionReceipt {
            claim: altered,
            signature: receipt.signature,
        };
        assert_eq!(
            minter.mint(&mut vault, &stale_signature).unwrap_err(),
            PoaExpeditionError::InvalidSignature,
        );
    }

    assert_eq!(
        minter.mint(&mut vault, &receipt).unwrap_err(),
        PoaExpeditionError::MissingTransitionVerifier
    );
    assert_eq!(vault.item_count(), 0, "no unjudged receipt can mint");
}
