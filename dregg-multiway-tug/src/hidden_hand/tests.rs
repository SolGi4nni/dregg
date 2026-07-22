//! Phase 2 — the zk hidden-hand, DRIVEN.
//!
//! The membership tooth runs through the REAL cell evaluator + registry
//! ([`super::check_play`]); the committed roots + phase machine run on a real
//! embedded executor ([`super::HiddenHandLedger`]). Every assertion is
//! non-vacuous: the legal play commits, the fabricated card is refused.

use super::*;
use crate::reference::Player;

/// A deterministic six-card hand: distinct card ids across guilds, distinct nonces.
fn sample_hand() -> Vec<(u64, u64)> {
    vec![
        (0, 1001),
        (1, 1002),
        (3, 1003),
        (7, 1004),
        (12, 1005),
        (18, 1006),
    ]
}

// ---------------------------------------------------------------------------
// The Merkle-committed hand.
// ---------------------------------------------------------------------------

#[test]
fn deal_commits_hand_as_a_merkle_root() {
    let tree = HandTree::commit(sample_hand());
    // The root is a real Poseidon2 commitment (non-trivial), and stable.
    let r1 = tree.root_bytes();
    let r2 = HandTree::commit(sample_hand()).root_bytes();
    assert_eq!(r1, r2, "the hand commitment is deterministic");
    assert_ne!(r1, [0u8; 32], "the committed root is non-trivial");

    // A different hand commits to a different root (binding).
    let mut other = sample_hand();
    other[0] = (2, 1001);
    assert_ne!(
        HandTree::commit(other).root_bytes(),
        r1,
        "a different hand => a different committed root"
    );
}

// ---------------------------------------------------------------------------
// The membership-proven legal play (executor-checked) — revealing nothing else.
// ---------------------------------------------------------------------------

#[test]
fn legal_play_verifies_membership_through_the_real_evaluator() {
    let hand = sample_hand();
    let tree = HandTree::commit(hand.clone());

    // Every dealt card is a provably-legal play, verified through the REAL cell
    // evaluator + the REAL WitnessedPredicateRegistry.
    for &(card, _) in &hand {
        let proof = tree.prove_play(card).expect("a dealt card can be proven");
        check_play(&proof).unwrap_or_else(|e| panic!("legal play of card {card} refused: {e}"));
    }
}

#[test]
fn legal_play_reveals_only_the_played_card() {
    let hand = sample_hand();
    let tree = HandTree::commit(hand.clone());
    let played = 7u64;
    let proof = tree.prove_play(played).expect("dealt");

    // The proof's whole public content is the played card + hashes.
    assert_eq!(proof.card_id, played);

    // The other cards' identities NEVER appear in the clear in the proof wire bytes:
    // the leaves are blinded commitments, the path carries only sibling *hashes*.
    let mut wire = proof.opening_bytes();
    wire.extend_from_slice(&proof.path_bytes());
    for &(other, other_nonce) in &hand {
        if other == played {
            continue;
        }
        // Neither the other card id nor its nonce is recoverable in the clear.
        assert!(
            !contains_subsequence(&wire, &other.to_le_bytes()),
            "other card id {other} leaked into the play proof bytes"
        );
        assert!(
            !contains_subsequence(&wire, &other_nonce.to_le_bytes()),
            "other card nonce {other_nonce} leaked into the play proof bytes"
        );
        // And a naive unblinded guess never equals a real (blinded) leaf.
        let sib_leaf = card_leaf(other, other_nonce);
        assert_ne!(
            sib_leaf,
            card_leaf(other, 0),
            "the per-card nonce blinds the leaf"
        );
    }
}

// ---------------------------------------------------------------------------
// A fabricated card is REFUSED (the tooth is non-vacuous).
// ---------------------------------------------------------------------------

#[test]
fn fabricated_card_is_refused_but_legal_play_commits() {
    let tree = HandTree::commit(sample_hand());
    // A real, legal play commits.
    let legal = tree.prove_play(12).expect("dealt");
    assert!(check_play(&legal).is_ok(), "the legal play must commit");

    // (a) A card that was never dealt — fabricated id, borrowing a real path shape.
    let fabricated = PlayProof {
        card_id: 99,
        nonce: 4242,
        path: legal.path.clone(),
        root: legal.root,
    };
    assert!(
        check_play(&fabricated).is_err(),
        "a fabricated card (never dealt) must be refused"
    );

    // (b) A real dealt card with the WRONG opening nonce — cannot forge the leaf.
    let wrong_nonce = PlayProof {
        nonce: legal.nonce.wrapping_add(1),
        ..legal.clone()
    };
    assert!(
        check_play(&wrong_nonce).is_err(),
        "a wrong opening nonce must be refused"
    );

    // (c) A tampered authentication path — a flipped sibling breaks the walk.
    let mut tampered = legal.clone();
    tampered.path[0].siblings[0] = dregg_circuit::field::BabyBear::ZERO;
    assert!(
        check_play(&tampered).is_err(),
        "a tampered membership path must be refused"
    );

    // (d) The SAME proof against a DIFFERENT committed root — a swapped commitment.
    let mut wrong_root = legal.clone();
    wrong_root.root[0] ^= 0x01;
    assert!(
        check_play(&wrong_root).is_err(),
        "a proof against a swapped root must be refused"
    );

    // (e) The full u64 opening is bound. The old one-felt encoding aliased values that differed
    // by the BabyBear modulus; the staged 30/30/4-bit encoding must refuse both aliases.
    let card_alias = PlayProof {
        card_id: legal.card_id + dregg_circuit::field::BABYBEAR_P as u64,
        ..legal.clone()
    };
    assert!(
        check_play(&card_alias).is_err(),
        "a card id that aliases in one BabyBear lane must still be refused"
    );
    let nonce_alias = PlayProof {
        nonce: legal.nonce + dregg_circuit::field::BABYBEAR_P as u64,
        ..legal.clone()
    };
    assert!(
        check_play(&nonce_alias).is_err(),
        "a nonce that aliases in one BabyBear lane must still be refused"
    );

    // (f) The root's 32-byte wire form is canonical, not merely its low field lane.
    let mut noncanonical_root = legal.clone();
    noncanonical_root.root[31] = 1;
    assert!(
        check_play(&noncanonical_root).is_err(),
        "non-zero high root bytes must not alias the canonical commitment"
    );
}

// ---------------------------------------------------------------------------
// The remaining-hand root updates — no double-play of a committed card.
// ---------------------------------------------------------------------------

#[test]
fn played_card_cannot_be_replayed_against_the_updated_root() {
    let hand = sample_hand();
    let tree = HandTree::commit(hand.clone());
    let played = 3u64;

    // The play is legal against the current root.
    let proof = tree.prove_play(played).expect("dealt");
    assert!(check_play(&proof).is_ok());

    // The remaining hand is recommitted with the card removed.
    let remaining = tree.without(played);
    assert_ne!(
        remaining.root_bytes(),
        tree.root_bytes(),
        "playing a card updates the committed remaining root"
    );

    // The played card can no longer even produce a proof under the remaining root.
    assert!(
        remaining.prove_play(played).is_none(),
        "a played card is no longer a member of the remaining hand"
    );

    // And a proof carrying the old path but the NEW remaining root is refused.
    let replay = PlayProof {
        root: remaining.root_bytes(),
        ..proof.clone()
    };
    assert!(
        check_play(&replay).is_err(),
        "a replay of the played card against the updated root is refused"
    );

    // A still-held card IS provable under the remaining root (non-vacuous).
    let still_held = remaining.prove_play(7).expect("7 is still held");
    assert!(
        check_play(&still_held).is_ok(),
        "a still-held card remains a legal play"
    );
}

// ---------------------------------------------------------------------------
// The blind Gift/Competition pick + the concealed Secret — commit → reveal.
// ---------------------------------------------------------------------------

#[test]
fn blind_pick_is_a_binding_commit_reveal() {
    // The opponent's concealed choice (which cards they keep).
    let payload = vec![4u8, 5u8]; // guilds kept
    let nonce = 0xC0FFEE;
    let seal = BlindPick::compute_seal(Player::B, &payload, nonce);

    let mut pick = BlindPick::commit(Player::B, seal);

    // Fog: before reveal, a peeker sees only the seal — the pick is unreadable.
    assert_eq!(pick.peek(), Some(seal));
    assert!(
        pick.bound_payload().is_none(),
        "the pick is concealed before reveal"
    );

    // A reveal before the commit phase closes is refused (phase gate).
    assert_eq!(
        pick.reveal(&payload, nonce),
        Err(BlindPickError::NotRevealPhase)
    );

    pick.close_commit().unwrap();

    // A post-reveal SWAP (a different payload / a peek-then-switch) is refused.
    assert_eq!(
        pick.reveal(&[9u8], nonce),
        Err(BlindPickError::SealMismatch),
        "a swapped pick does not open the committed seal"
    );
    assert_eq!(
        pick.reveal(&payload, nonce.wrapping_add(1)),
        Err(BlindPickError::SealMismatch),
        "a swapped nonce does not open the committed seal"
    );

    // The honest reveal binds.
    pick.reveal(&payload, nonce)
        .expect("the honest reveal binds");
    assert_eq!(pick.phase, PickPhase::Bound);
    assert_eq!(pick.bound_payload(), Some(payload.as_slice()));
    // Once bound, no further peek / reveal.
    assert_eq!(pick.peek(), None);
    assert_eq!(
        pick.reveal(&payload, nonce),
        Err(BlindPickError::AlreadyBound)
    );
}

#[test]
fn secret_card_rides_the_same_commit_reveal() {
    // The concealed Secret card (a single guild), the owner's own commit.
    let secret = vec![6u8];
    let nonce = 777;
    let seal = BlindPick::compute_seal(Player::A, &secret, nonce);
    let mut pick = BlindPick::commit(Player::A, seal);
    pick.close_commit().unwrap();
    // A guess at the secret is refused; the true secret binds.
    assert_eq!(
        pick.reveal(&[0u8], nonce),
        Err(BlindPickError::SealMismatch)
    );
    pick.reveal(&secret, nonce).unwrap();
    assert_eq!(pick.bound_payload(), Some(secret.as_slice()));
}

// ---------------------------------------------------------------------------
// The committed roots + phase machine on the real WorldCell (executor teeth).
// ---------------------------------------------------------------------------

#[test]
fn ledger_commits_the_deal_and_freezes_the_hand_root() {
    let a = HandTree::commit(sample_hand());
    let mut b_cards = sample_hand();
    b_cards[0] = (2, 2001);
    let b = HandTree::commit(b_cards);

    let mut ledger = HiddenHandLedger::deploy(7).expect("deploy");
    ledger.deal(a.root(), b.root()).expect("the deal commits");
    assert_eq!(ledger.read("a_hand_root"), a.root().as_u32() as u64);
    assert_eq!(ledger.read("phase"), PHASE_DEAL);

    let proof = a.prove_play(3).expect("dealt card");
    let remaining = a.without(3);
    let mut legal_next = ledger.state();
    legal_next.a_rem_root = root_to_u64(remaining.root());
    legal_next.a_played += 1;
    legal_next.generation += 1;
    legal_next.phase = PHASE_PLAY;

    // A turn that tries to SWAP the committed hand root is refused (WriteOnce).
    let mut swap = legal_next;
    swap.a_hand_root ^= 0x1234; // change the frozen root
    assert!(
        ledger
            .commit_raw_play(Player::A, &[proof.clone()], &swap)
            .is_err(),
        "swapping the committed hand root must be refused"
    );

    // A phase REWIND is refused (Monotonic).
    let mut rewind = legal_next;
    rewind.phase = 0; // below DEAL
    assert!(
        ledger
            .commit_raw_play(Player::A, &[proof], &rewind)
            .is_err(),
        "rewinding the phase must be refused"
    );
}

#[test]
fn ledger_play_advances_generation_and_writes_remaining_root() {
    let a = HandTree::commit(sample_hand());
    let b = HandTree::commit(sample_hand());
    let mut ledger = HiddenHandLedger::deploy(9).expect("deploy");
    ledger.deal(a.root(), b.root()).expect("deal");

    let gen0 = ledger.read("gen");
    let proof = a.prove_play(3).expect("dealt card");
    let remaining = a.without(3);
    ledger
        .play(Player::A, &[proof], remaining.root())
        .expect("play commits");
    assert_eq!(
        ledger.read("gen"),
        gen0 + 1,
        "the play advances the generation"
    );
    assert_eq!(ledger.read("a_played"), 1);
    assert_eq!(ledger.read("a_rem_root"), remaining.root().as_u32() as u64);
    assert_eq!(
        ledger.read("a_hand_root"),
        a.root().as_u32() as u64,
        "the committed root is unchanged"
    );

    // A stale generation under `play` is refused (StrictMonotonic).
    let mut stale = ledger.state();
    // do NOT advance gen
    let proof2 = a.prove_play(7).expect("another pinned-inventory member");
    stale.a_played += 1;
    stale.a_rem_root = root_to_u64(a.without(3).without(7).root());
    assert!(
        ledger
            .commit_raw_play(Player::A, &[proof2], &stale)
            .is_err(),
        "a non-advancing generation must be refused"
    );
}

#[test]
fn ledger_requires_witnesses_on_the_actual_executor_path() {
    let a = HandTree::commit(sample_hand());
    let b = HandTree::commit(sample_hand());
    let mut ledger = HiddenHandLedger::deploy(10).expect("deploy");
    ledger.deal(a.root(), b.root()).expect("deal");

    let proof = a.prove_play(3).expect("dealt card");
    let remaining = a.without(3);
    let before = ledger.state();
    let mut claimed = before;
    claimed.a_rem_root = root_to_u64(remaining.root());
    claimed.a_played += 1;
    claimed.generation += 1;
    claimed.phase = PHASE_PLAY;

    assert!(
        ledger
            .commit_raw(&witnessed_play_method(Player::A, 1), &claimed)
            .is_err(),
        "the witnessed method without opening/path blobs must fail closed"
    );
    assert_eq!(
        ledger.state(),
        before,
        "a refusal cannot advance the mirror"
    );
    assert_eq!(
        ledger.read("gen"),
        before.generation,
        "a refusal cannot advance committed state"
    );

    // A real executor refusal burns a runtime nonce. The next honestly witnessed action must
    // still be re-signed at the live nonce and land (anti-ghost + restart of the receipt chain).
    ledger
        .play(Player::A, &[proof], remaining.root())
        .expect("the witnessed retry lands");
    assert_eq!(ledger.read("a_played"), 1);
}

#[test]
fn ledger_refuses_forged_tampered_and_wrong_root_proofs_without_a_ghost_step() {
    let a = HandTree::commit(sample_hand());
    let mut b_cards = sample_hand();
    b_cards[0] = (2, 2001);
    let b = HandTree::commit(b_cards);
    let mut ledger = HiddenHandLedger::deploy(12).expect("deploy");
    ledger.deal(a.root(), b.root()).expect("deal");
    let legal = a.prove_play(7).expect("dealt card");
    let remaining = a.without(7);
    let before = ledger.state();

    let mut wrong_root = legal.clone();
    wrong_root.root = b.root_bytes();
    assert!(
        ledger
            .play(Player::A, &[wrong_root], remaining.root())
            .is_err(),
        "a proof bound to the other inventory root is refused"
    );

    let fabricated = PlayProof {
        card_id: 99,
        ..legal.clone()
    };
    assert!(
        ledger
            .play(Player::A, &[fabricated], remaining.root())
            .is_err(),
        "a fabricated opening reaches the executor and fails Merkle membership"
    );

    let mut tampered = legal.clone();
    let sibling = &mut tampered.path[0].siblings[0];
    *sibling = if *sibling == BabyBear::ZERO {
        BabyBear::ONE
    } else {
        BabyBear::ZERO
    };
    assert!(
        ledger
            .play(Player::A, &[tampered], remaining.root())
            .is_err(),
        "a tampered path reaches the executor and fails Merkle membership"
    );

    assert_eq!(ledger.state(), before);
    assert_eq!(ledger.read("gen"), before.generation);
    ledger
        .play(Player::A, &[legal], remaining.root())
        .expect("a legal proof still lands after hostile refusals");
}

#[test]
fn ledger_rejects_duplicate_proofs_within_and_across_actions() {
    let a = HandTree::commit(sample_hand());
    let b = HandTree::commit(sample_hand());
    let mut ledger = HiddenHandLedger::deploy(14).expect("deploy");
    ledger.deal(a.root(), b.root()).expect("deal");
    let proof = a.prove_play(12).expect("dealt card");
    let remaining = a.without(12);

    assert!(
        ledger
            .play(Player::A, &[proof.clone(), proof.clone()], remaining.root(),)
            .is_err(),
        "one action cannot count the same membership witness twice"
    );
    assert_eq!(ledger.read("a_played"), 0);

    ledger
        .play(Player::A, &[proof.clone()], remaining.root())
        .expect("first consumption lands");
    let after = ledger.state();
    assert!(
        ledger.play(Player::A, &[proof], remaining.root()).is_err(),
        "a static-root membership proof cannot be replayed after consumption"
    );
    assert_eq!(ledger.state(), after);
    assert_eq!(ledger.read("a_played"), 1);
}

#[test]
fn ledger_freezes_a_committed_pick_seal() {
    let a = HandTree::commit(sample_hand());
    let b = HandTree::commit(sample_hand());
    let mut ledger = HiddenHandLedger::deploy(11).expect("deploy");
    ledger.deal(a.root(), b.root()).expect("deal");

    let seal = BlindPick::compute_seal(Player::B, &[4u8, 5u8], 42);
    ledger
        .commit_pick(Player::B, &seal, false)
        .expect("the pick seal commits");
    assert_eq!(ledger.read("b_pick_seal"), seal_to_u64(&seal));
    assert_eq!(ledger.read("phase"), PHASE_PICK);

    // Committing a DIFFERENT seal onto the already-committed slot is refused
    // (WriteOnce) — the executor-level post-reveal swap tooth.
    let seal2 = BlindPick::compute_seal(Player::B, &[0u8], 43);
    let mut swap = ledger.state();
    swap.b_pick_seal = seal_to_u64(&seal2);
    swap.generation += 1;
    assert!(
        ledger.commit_raw(COMMIT_PICK, &swap).is_err(),
        "swapping a committed pick seal must be refused"
    );
}

// ---------------------------------------------------------------------------
// The full hidden-hand round — deal, membership-proven play, blind pick — all
// on the real executor.
// ---------------------------------------------------------------------------

#[test]
fn full_hidden_hand_round_drives_the_executor() {
    let full_a = HandTree::commit(sample_hand());
    let mut a = full_a.clone();
    let b = HandTree::commit(sample_hand());
    let mut ledger = HiddenHandLedger::deploy(13).expect("deploy");
    ledger.deal(a.root(), b.root()).expect("deal");

    // A plays two cards: each membership-proven, each committing the remaining root.
    for card in [0u64, 18u64] {
        let proof = full_a
            .prove_play(card)
            .expect("held in the pinned inventory");
        check_play(&proof).expect("the play is a legal member of the committed hand");
        a = a.without(card);
        ledger
            .play(Player::A, &[proof], a.root())
            .expect("the play commits");
    }
    assert_eq!(ledger.read("a_played"), 2);

    // The blind Gift pick: B commits, then reveals — bound on the executor.
    let payload = vec![4u8, 5u8];
    let nonce = 9;
    let seal = BlindPick::compute_seal(Player::B, &payload, nonce);
    let mut pick = BlindPick::commit(Player::B, seal);
    ledger.commit_pick(Player::B, &seal, false).expect("commit");
    pick.close_commit().unwrap();
    pick.reveal(&payload, nonce)
        .expect("the honest reveal binds");
    ledger
        .reveal_pick(Player::B)
        .expect("the reveal turn commits");
    assert_eq!(pick.bound_payload(), Some(payload.as_slice()));
}

// ---------------------------------------------------------------------------

/// Whether `haystack` contains `needle` as a contiguous subsequence.
fn contains_subsequence(haystack: &[u8], needle: &[u8]) -> bool {
    if needle.is_empty() || needle.len() > haystack.len() {
        return false;
    }
    haystack.windows(needle.len()).any(|w| w == needle)
}
