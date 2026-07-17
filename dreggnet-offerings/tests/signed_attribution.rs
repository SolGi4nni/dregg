//! DRIVEN: the SIGNED-ATTRIBUTION seam end-to-end — a game turn's actor as a VERIFIED public
//! key, every gate exercised in BOTH polarities on the real dungeon substrate:
//!
//! * a signed advance with a real keypair LANDS, attributed to the pubkey identity, recorded
//!   with `Signed` provenance;
//! * a FORGED signature is refused (`BadSignature`) and the session state does not move;
//! * a REPLAYED envelope is refused (`StaleCounter`) and the session state does not move;
//! * the unsigned legacy path is byte-identically alive and records `Asserted`;
//! * a session key bound to pubkey A refuses a play driven under pubkey B, and admits A's own.

use dreggnet_offerings::dungeon::{DungeonOffering, TURN_CHOOSE};
use dreggnet_offerings::session::{
    FreePaymaster, PlayGrant, PlayOutcome, PlayRefusal, PlayScope, open_session_signed,
};
use dreggnet_offerings::signed::TurnSigner;
use dreggnet_offerings::{
    Action, Attribution, DreggIdentity, HostError, Offering, OfferingHost, SessionConfig,
    SessionId, SignedError,
};
use dungeon_on_dregg::{KP_CLAIM_RED, KP_PRESS_ON};

fn choose(arg: usize) -> Action {
    Action::new("move", TURN_CHOOSE, arg as i64, true)
}

fn dungeon_host() -> (OfferingHost, SessionId) {
    let mut host = OfferingHost::new();
    host.register("dungeon", "The Warden's Keep", DungeonOffering::new());
    let id = host.open("dungeon").expect("dungeon opens");
    (host, id)
}

/// A SIGNED advance with a real keypair lands a real committed turn; the actor of record is the
/// VERIFIED pubkey identity (not any frontend string), and the resume log carries the
/// [`Attribution::Signed`] trust level beside it.
#[test]
fn a_signed_advance_lands_attributed_to_the_verified_pubkey() {
    let (mut host, id) = dungeon_host();
    let alice = TurnSigner::from_seed([7u8; 32]);

    let sa = alice.sign("dungeon", &id, 0, choose(KP_PRESS_ON));
    let out = host
        .advance_signed("dungeon", &id, sa)
        .expect("a genuinely signed move is admitted");
    assert!(out.landed(), "the signed move landed a real receipt");

    // The move-log records the VERIFIED identity with Signed provenance.
    let log = host.move_log("dungeon", &id).expect("log exists");
    assert_eq!(log.moves.len(), 1);
    assert_eq!(
        log.moves[0].actor,
        alice.identity(),
        "the actor of record is the verified pubkey identity"
    );
    assert_eq!(
        log.moves[0].attribution,
        Attribution::Signed {
            pubkey_hex: alice.pubkey_hex().to_string()
        },
        "the attribution is visibly Signed"
    );
    // The host's replay ledger consumed counter 0; the signer's next counter is 1.
    assert_eq!(
        host.signed_counter("dungeon", &id, alice.pubkey_hex()),
        Some(0)
    );

    // The next signed turn (counter 1) also lands — a whole session can ride signed turns.
    let sa = alice.sign("dungeon", &id, 1, choose(KP_CLAIM_RED));
    assert!(
        host.advance_signed("dungeon", &id, sa)
            .expect("second signed move admitted")
            .landed()
    );
    assert_eq!(
        host.verify("dungeon", &id).unwrap().turns,
        3,
        "genesis + two"
    );
}

/// A FORGED signature — a different key signs, claiming the victim's pubkey — is
/// [`SignedError::BadSignature`], and the session state DOES NOT MOVE (anti-ghost read-back:
/// commitment and turn count identical before and after, no move logged).
#[test]
fn a_forged_signature_is_refused_and_the_state_does_not_move() {
    let (mut host, id) = dungeon_host();
    let alice = TurnSigner::from_seed([7u8; 32]);
    let mallory = TurnSigner::from_seed([13u8; 32]);

    let before = host.commitment("dungeon", &id).expect("commitment");

    // Mallory signs a perfectly legal move, but claims Alice's public key.
    let mut forged = mallory.sign("dungeon", &id, 0, choose(KP_PRESS_ON));
    forged.actor_pubkey_hex = alice.pubkey_hex().to_string();

    let err = host
        .advance_signed("dungeon", &id, forged)
        .expect_err("a forged signature is refused");
    assert!(
        matches!(err, HostError::Signature(SignedError::BadSignature)),
        "refused as BadSignature: {err}"
    );

    // Anti-ghost: nothing committed, nothing logged, no counter consumed.
    let after = host.commitment("dungeon", &id).expect("commitment");
    assert_eq!(before, after, "the session state did not move");
    assert_eq!(
        host.verify("dungeon", &id).unwrap().turns,
        1,
        "genesis only"
    );
    assert!(host.move_log("dungeon", &id).unwrap().is_empty());
    assert_eq!(
        host.signed_counter("dungeon", &id, alice.pubkey_hex()),
        None
    );

    // Non-vacuous: the SAME move genuinely signed by Alice lands.
    let genuine = alice.sign("dungeon", &id, 0, choose(KP_PRESS_ON));
    assert!(
        host.advance_signed("dungeon", &id, genuine)
            .unwrap()
            .landed()
    );
}

/// A REPLAYED envelope — the identical [`dreggnet_offerings::SignedAction`] presented twice — is
/// [`SignedError::StaleCounter`] the second time, and the state does not move again.
#[test]
fn a_replayed_signed_action_is_stale_and_the_state_does_not_move() {
    let (mut host, id) = dungeon_host();
    let alice = TurnSigner::from_seed([7u8; 32]);

    let sa = alice.sign("dungeon", &id, 0, choose(KP_PRESS_ON));
    assert!(
        host.advance_signed("dungeon", &id, sa.clone())
            .expect("first presentation lands")
            .landed()
    );
    let after_first = host.commitment("dungeon", &id).expect("commitment");

    // The captured envelope, replayed verbatim.
    let err = host
        .advance_signed("dungeon", &id, sa)
        .expect_err("the replay is refused");
    assert!(
        matches!(
            err,
            HostError::Signature(SignedError::StaleCounter {
                presented: 0,
                expected: 1
            })
        ),
        "refused as StaleCounter: {err}"
    );

    // Anti-ghost: exactly one committed turn, once.
    let after_replay = host.commitment("dungeon", &id).expect("commitment");
    assert_eq!(after_first, after_replay, "the replay moved nothing");
    assert_eq!(
        host.verify("dungeon", &id).unwrap().turns,
        2,
        "genesis + one"
    );
    assert_eq!(host.move_log("dungeon", &id).unwrap().len(), 1);
}

/// The UNSIGNED legacy path is untouched: `advance` with a bare string identity still lands
/// exactly as before, and its recorded attribution is honestly [`Attribution::Asserted`].
#[test]
fn the_unsigned_legacy_advance_still_works_and_records_asserted() {
    let (mut host, id) = dungeon_host();
    let actor = DreggIdentity("web:alice".to_string());

    let out = host
        .advance("dungeon", &id, choose(KP_PRESS_ON), actor.clone())
        .expect("the legacy path is alive");
    assert!(out.landed(), "the unsigned move lands exactly as before");

    let log = host.move_log("dungeon", &id).expect("log exists");
    assert_eq!(
        log.moves[0].actor, actor,
        "attributed to the asserted string"
    );
    assert_eq!(
        log.moves[0].attribution,
        Attribution::Asserted {
            label: "web:alice".to_string()
        },
        "the legacy attribution is visibly Asserted, never laundered to Signed"
    );
    assert!(!log.moves[0].attribution.is_signed());
}

/// A session key minted for a SIGNED holder (bound to pubkey A) refuses a play DRIVEN under
/// pubkey B ([`PlayRefusal::WrongHolderKey`], nothing advances, no budget spent), and admits
/// A's own play — both polarities of the binding.
#[test]
fn a_pubkey_bound_session_key_refuses_a_different_driver() {
    let alice = TurnSigner::from_seed([7u8; 32]);
    let bob = TurnSigner::from_seed([8u8; 32]);

    let root = PlayGrant::root(PlayScope::Any, 1_000_000, 100);
    let mut key = open_session_signed(
        &root,
        alice.pubkey_hex(),
        PlayScope::of_offering("dungeon"),
        1_000_000,
        10,
    )
    .expect("a narrowing signed delegation is minted");
    assert_eq!(
        key.holder(),
        &alice.identity(),
        "the holder IS the pubkey identity"
    );
    assert_eq!(key.bound_pubkey_hex(), Some(alice.pubkey_hex()));

    let off = DungeonOffering::new();
    let mut s = off.open(SessionConfig::with_seed(3)).expect("open");
    let free = FreePaymaster;
    let dungeon = PlayScope::of_offering("dungeon").offering_id().unwrap();

    // Bob drives Alice's key: refused, no advance, no budget spent.
    let out = key.play_driven_by(
        bob.pubkey_hex(),
        dungeon,
        &off,
        &mut s,
        choose(KP_PRESS_ON),
        1,
        &free,
    );
    assert!(
        matches!(
            out,
            PlayOutcome::Refused(PlayRefusal::WrongHolderKey { .. })
        ),
        "a different driver is refused: {out:?}"
    );
    assert_eq!(key.turns_taken(), 0, "the refused drive consumed no budget");
    assert_eq!(off.verify(&s).turns, 1, "genesis only — nothing advanced");

    // Alice drives her own key: the move commits (non-vacuous — the binding was the only gate).
    let out = key.play_driven_by(
        alice.pubkey_hex(),
        dungeon,
        &off,
        &mut s,
        choose(KP_PRESS_ON),
        1,
        &free,
    );
    assert!(
        out.committed(),
        "the bound holder's own play lands: {out:?}"
    );
    assert_eq!(key.turns_taken(), 1);

    // An UNBOUND legacy key admits any driver — the additive default is unchanged behavior.
    let mut legacy = dreggnet_offerings::session::open_session(
        &root,
        DreggIdentity("player-legacy".into()),
        PlayScope::of_offering("dungeon"),
        1_000_000,
        10,
    )
    .expect("legacy key");
    assert_eq!(legacy.bound_pubkey_hex(), None);
    let out = legacy.play_driven_by(
        bob.pubkey_hex(),
        dungeon,
        &off,
        &mut s,
        choose(KP_CLAIM_RED),
        1,
        &free,
    );
    assert!(out.committed(), "an unbound key admits any driver: {out:?}");
}
