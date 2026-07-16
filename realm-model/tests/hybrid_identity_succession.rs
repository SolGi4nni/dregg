//! DECISION 2 (ember's DECIDED "recommended") — a hybrid-PQ canonical identity
//! from ONE seed, with SUCCESSION (key rotation) and guardian RECOVERY.
//!
//!   * The identity derives BOTH its ed25519 AND its ML-DSA-65 key from one
//!     32-byte seed (the shipped `turn/src/pq.rs` posture: `ML-DSA.KeyGen(ξ =
//!     seed)`, ctx `dregg-hybrid-turn-v1`). Its durable CELL state NAMES the
//!     current key; the cell id is the stable durable principal.
//!   * ROTATION: a succession SIGNED BY THE OLD KEY advances the current-key
//!     commitment (a succession chain). The identity outlives any single key;
//!     the resolver follows the chain to the current key; surface bindings still
//!     resolve to the SAME id across the rotation (the durable-principal property
//!     survives a key change). A rotation by a non-current, non-guardian key is
//!     REFUSED (the stolen-identity canary).
//!   * RECOVERY: a pre-registered K-of-N guardian set can co-sign a succession
//!     (a lost key is not a lost identity). N-of-M rotates; below threshold fails.
//!   * PQ-HYBRID throughout: every succession is signed by BOTH halves.

use realm_model::identity::{
    HybridKey, SuccessionKind, Surface, SurfaceRef, commit_hybrid, succession_message,
};
use realm_model::{RealmWorld, Refused};

/// A distinct hybrid key from a byte-filled seed (a "new" or "guardian" key).
fn key(seed_byte: u8) -> HybridKey {
    HybridKey::from_seed(&[seed_byte; 32])
}

/// The durable principal survives a key rotation: the OLD key signs a succession,
/// the current key advances, the resolver follows the chain, and both surface
/// bindings still resolve to the SAME canonical id across the rotation.
#[test]
fn identity_rotates_and_the_principal_survives() {
    let mut world = RealmWorld::new();
    let me = world.mint_identity("pip", "seed-pip").unwrap();

    // Two surfaces bind onto the durable identity BEFORE the rotation.
    let discord = SurfaceRef::new(Surface::Discord, "pip#1234");
    let web = SurfaceRef::new(Surface::Web, "sess-cafe");
    world.bind_surface(&me, discord.clone()).unwrap();
    world.bind_surface(&me, web.clone()).unwrap();

    // The birth key is the deterministic hybrid key from the same seed.
    let birth = world.birth_key("seed-pip");
    assert_eq!(
        world.current_key_commit(&me.id).unwrap(),
        birth.commitment(),
        "the cell names the birth key at genesis"
    );
    assert_eq!(world.identity_epoch(&me.id), 1);

    // Rotate to a new key. The OLD (current, birth) key signs the canonical
    // succession message; the gate builds the same message internally.
    let new_key = key(0x11);
    let new_commit = new_key.commitment();
    let epoch = world.identity_epoch(&me.id);
    let current = world.current_key_commit(&me.id).unwrap();
    let msg = succession_message(
        &me.id,
        epoch,
        &current,
        &new_commit,
        SuccessionKind::SelfSigned,
    );
    let sig = birth.sign(&msg).expect("hybrid sign");

    let rec = world
        .rotate_identity(&me.id, new_commit, &sig)
        .expect("rotation signed by the current key is admitted");
    assert_eq!(rec.kind, SuccessionKind::SelfSigned);

    // The current key advanced; the epoch advanced; the id is UNCHANGED.
    assert_eq!(world.current_key_commit(&me.id).unwrap(), new_commit);
    assert_eq!(world.identity_epoch(&me.id), 2);

    // The resolver follows the chain from genesis and reaches the current key.
    assert_eq!(
        world.follow_chain(&me.id),
        Some(new_commit),
        "the succession chain resolves to the current key"
    );

    // THE DURABLE-PRINCIPAL PROPERTY: both surface bindings still resolve to the
    // SAME canonical id across the key change — the identity outlived the key.
    assert_eq!(world.resolve_surface(&discord).unwrap().id, me.id);
    assert_eq!(world.resolve_surface(&web).unwrap().id, me.id);
}

/// The stolen-identity CANARY: a succession signed by a key that is NOT the
/// current key (and not a guardian) is REFUSED — accepting it would be a stolen
/// identity. Also: the OLD key, once rotated away, can no longer succeed.
#[test]
fn rotation_by_a_wrong_key_is_refused() {
    let mut world = RealmWorld::new();
    let me = world.mint_identity("gwen", "seed-gwen").unwrap();
    let birth = world.birth_key("seed-gwen");
    let birth_commit = birth.commitment();

    // A stranger key attempts to seize the identity.
    let thief = key(0x99);
    let thief_target = key(0x9A).commitment();
    let epoch = world.identity_epoch(&me.id);
    let cur = world.current_key_commit(&me.id).unwrap();
    let thief_msg = succession_message(
        &me.id,
        epoch,
        &cur,
        &thief_target,
        SuccessionKind::SelfSigned,
    );
    let thief_sig = thief.sign(&thief_msg).unwrap();

    let refused = world.rotate_identity(&me.id, thief_target, &thief_sig);
    assert!(
        matches!(
            refused,
            Err(Refused::WrongSuccessionKey { got_commit, .. })
                if got_commit == thief.commitment()
        ),
        "a non-current key must not succeed the identity; got {refused:?}"
    );
    // Nothing moved.
    assert_eq!(world.current_key_commit(&me.id).unwrap(), birth_commit);
    assert_eq!(world.identity_epoch(&me.id), 1);

    // A well-formed sig by the birth key over a TAMPERED target (signing one
    // commit, submitting another) also fails — the message binds the target.
    let real_target = key(0x22).commitment();
    let honest_msg = succession_message(
        &me.id,
        epoch,
        &cur,
        &real_target,
        SuccessionKind::SelfSigned,
    );
    let honest_sig = birth.sign(&honest_msg).unwrap();
    let mismatched = world.rotate_identity(&me.id, key(0x23).commitment(), &honest_sig);
    assert!(
        matches!(mismatched, Err(Refused::BadSuccessionSignature { .. })),
        "a signature over a different target must not authorize this succession; got {mismatched:?}"
    );

    // Do a real rotation, then prove the OLD key can no longer succeed.
    world
        .rotate_identity(&me.id, real_target, &honest_sig)
        .expect("legitimate rotation lands");
    let epoch2 = world.identity_epoch(&me.id);
    let cur2 = world.current_key_commit(&me.id).unwrap();
    let stale_msg = succession_message(
        &me.id,
        epoch2,
        &cur2,
        &key(0x24).commitment(),
        SuccessionKind::SelfSigned,
    );
    let stale_sig = birth.sign(&stale_msg).unwrap(); // birth is no longer current
    let stale = world.rotate_identity(&me.id, key(0x24).commitment(), &stale_sig);
    assert!(
        matches!(stale, Err(Refused::WrongSuccessionKey { .. })),
        "the retired key cannot succeed the identity again; got {stale:?}"
    );
}

/// Guardian RECOVERY: a pre-registered K-of-N guardian set co-signs a succession
/// so a lost key is not a lost identity. N-of-M (here 2-of-3) rotates the locked
/// identity; below threshold (1-of-3, and a padded-with-a-non-guardian set) fails.
#[test]
fn guardian_threshold_recovery() {
    let mut world = RealmWorld::new();
    let me = world.mint_identity("rowan", "seed-rowan").unwrap();

    // Register a 2-of-3 guardian set (their key commitments).
    let g1 = key(0xA1);
    let g2 = key(0xA2);
    let g3 = key(0xA3);
    let guardians = [g1.commitment(), g2.commitment(), g3.commitment()];
    world.register_guardians(&me.id, &guardians, 2).unwrap();

    // The owner "loses" the current key. Recovery targets a fresh key.
    let recovered = key(0x33);
    let recovered_commit = recovered.commitment();
    let epoch = world.identity_epoch(&me.id);
    let cur = world.current_key_commit(&me.id).unwrap();
    let rec_msg = succession_message(
        &me.id,
        epoch,
        &cur,
        &recovered_commit,
        SuccessionKind::GuardianRecovery,
    );

    // BELOW threshold: a single guardian co-sign is refused.
    let one = [g1.sign(&rec_msg).unwrap()];
    let short = world.recover_identity(&me.id, recovered_commit, &one);
    assert!(
        matches!(
            short,
            Err(Refused::BelowGuardianThreshold {
                have: 1,
                need: 2,
                ..
            })
        ),
        "1-of-3 must not recover a 2-of-3 identity; got {short:?}"
    );
    assert_eq!(
        world.current_key_commit(&me.id).unwrap(),
        cur,
        "no rotation on a short quorum"
    );

    // A non-guardian padding the set does NOT count toward the threshold.
    let stranger = key(0xEE);
    let padded = [g1.sign(&rec_msg).unwrap(), stranger.sign(&rec_msg).unwrap()];
    let padded_res = world.recover_identity(&me.id, recovered_commit, &padded);
    assert!(
        matches!(
            padded_res,
            Err(Refused::BelowGuardianThreshold {
                have: 1,
                need: 2,
                ..
            })
        ),
        "a non-guardian cannot pad a quorum; got {padded_res:?}"
    );

    // AT threshold: two DISTINCT registered guardians co-sign -> recovery lands.
    let quorum = [g1.sign(&rec_msg).unwrap(), g3.sign(&rec_msg).unwrap()];
    let rec = world
        .recover_identity(&me.id, recovered_commit, &quorum)
        .expect("2-of-3 guardian recovery is admitted");
    assert_eq!(rec.kind, SuccessionKind::GuardianRecovery);
    assert_eq!(
        world.current_key_commit(&me.id).unwrap(),
        recovered_commit,
        "the guardian quorum rotated the locked identity to the recovered key"
    );
    assert_eq!(world.identity_epoch(&me.id), epoch + 1);
    assert_eq!(world.follow_chain(&me.id), Some(recovered_commit));

    // The recovered key is now the current key: it can self-sign a further
    // succession, proving the chain composed correctly through recovery.
    let after = key(0x44);
    let epoch2 = world.identity_epoch(&me.id);
    let cur2 = world.current_key_commit(&me.id).unwrap();
    let msg2 = succession_message(
        &me.id,
        epoch2,
        &cur2,
        &after.commitment(),
        SuccessionKind::SelfSigned,
    );
    let sig2 = recovered.sign(&msg2).unwrap();
    world
        .rotate_identity(&me.id, after.commitment(), &sig2)
        .expect("the recovered key is the live current key");
    assert_eq!(
        world.current_key_commit(&me.id).unwrap(),
        after.commitment()
    );
}

/// A duplicate co-sign by the SAME guardian counts ONCE — two signatures from one
/// guardian do not manufacture a quorum.
#[test]
fn duplicate_guardian_cosign_counts_once() {
    let mut world = RealmWorld::new();
    let me = world.mint_identity("sage", "seed-sage").unwrap();
    let g1 = key(0xB1);
    let g2 = key(0xB2);
    world
        .register_guardians(&me.id, &[g1.commitment(), g2.commitment()], 2)
        .unwrap();

    let target = key(0x55).commitment();
    let epoch = world.identity_epoch(&me.id);
    let cur = world.current_key_commit(&me.id).unwrap();
    let msg = succession_message(
        &me.id,
        epoch,
        &cur,
        &target,
        SuccessionKind::GuardianRecovery,
    );

    // g1 signs twice — must count as ONE distinct guardian, below the 2 floor.
    let doubled = [g1.sign(&msg).unwrap(), g1.sign(&msg).unwrap()];
    let res = world.recover_identity(&me.id, target, &doubled);
    assert!(
        matches!(
            res,
            Err(Refused::BelowGuardianThreshold {
                have: 1,
                need: 2,
                ..
            })
        ),
        "one guardian signing twice is not a 2-quorum; got {res:?}"
    );
}

/// The hybrid signature really is BOTH halves: `commit_hybrid` binds ed25519 AND
/// ML-DSA-65, and a tampered signature fails closed (a quantum-safe succession).
#[test]
fn succession_signature_is_hybrid_and_fail_closed() {
    let k = key(0x77);
    let msg = b"the canonical succession message both halves cover";
    let mut sig = k.sign(msg).expect("hybrid sign");
    assert!(sig.verify(msg), "a well-formed hybrid signature verifies");

    // The commitment binds both public keys.
    assert_eq!(
        sig.signer_commitment(),
        commit_hybrid(&sig.ed_pk, &sig.ml_pk)
    );

    // Corrupt the ML-DSA (PQ) half: the whole hybrid check fails closed.
    let saved = sig.ml_sig.clone();
    sig.ml_sig[0] ^= 0xff;
    assert!(!sig.verify(msg), "a broken PQ half fails the hybrid check");
    sig.ml_sig = saved;

    // Corrupt the ed25519 (classical) half: likewise fails closed.
    sig.ed_sig[0] ^= 0xff;
    assert!(
        !sig.verify(msg),
        "a broken classical half fails the hybrid check"
    );
}
