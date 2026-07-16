//! Adversarial tests against the blocklace (Lean
//! `Authority/Blocklace::equivocation_detectable / observer_detects` and the
//! `finality.rs` byzantine-repelling tooth).
//!
//! Adversary models:
//!  - a Byzantine *creator* who forks their own strand (should be detected),
//!  - a *forger* who tries to inject a block as another creator (bad sig),
//!  - a *framer* who tries to make an HONEST creator look like an equivocator
//!    via signature malleability (the subtle one — block id binds the sig).
//!
//! IDENTITY MODEL (post PQ hybrid-identity sweep). `Block::creator` is NO LONGER
//! the ed25519 verify key: it is the HYBRID id `H(ed25519_pk ‖ ml_dsa_pk)`
//! (`dregg_types::hybrid_id_commitment`, = `Block::hybrid_id(&signing_key)`).
//! The classical verify key is carried separately in `Block::ed25519`, and it is
//! `ed25519` — not `creator` — that `verify_signature` parses as the verifying
//! key. `creator` is the identity LABEL keying tips / equivocators / roster.
//! Consequently every "is this creator flagged?" assertion below keys on the
//! hybrid id, and every hand-built adversarial block must set BOTH halves.
//!
//! PATH SCOPE. These tests drive `Blocklace::receive_block`, the ed25519-only
//! reception (local DAG reconstruction + equivocation bookkeeping). It verifies
//! the classical half ONLY; it does not consult the PQ roster and does not run
//! the `creator == H(ed25519 ‖ enrolled_ml_dsa)` commitment gate. That gate lives
//! in `Block::verify_hybrid`, reached on the live wire via
//! `receive_block_pinned`. Attack 2b drives `verify_hybrid` directly for exactly
//! the forgery variant the ed25519-only path cannot refuse.

use dregg_blocklace::finality::{Block, BlockError, Blocklace, Payload};
use ed25519_dalek::ed25519::signature::Signer as _;
use ed25519_dalek::SigningKey as DalekKey;

fn dalek_key(seed: u8) -> DalekKey {
    DalekKey::from_bytes(&[seed; 32])
}

/// Reconstruct the block signing content (mirrors finality.rs::signing_content
/// for the Ack/Data payloads used here). Domain-separated, payload hashed.
/// `creator` is the HYBRID id (`Block::hybrid_id`) — the signed bytes commit to
/// the hybrid identity, not to the bare ed25519 key.
fn signing_content(creator: &[u8; 32], seq: u64, payload: &Payload, preds: &[[u8; 32]]) -> Vec<u8> {
    let mut buf = Vec::new();
    buf.extend_from_slice(b"dregg-blocklace-v1");
    buf.extend_from_slice(creator);
    buf.extend_from_slice(&seq.to_le_bytes());
    let payload_bytes = match payload {
        Payload::Ack => vec![0x02u8],
        Payload::Data(d) => {
            let mut v = vec![0x05u8];
            v.extend_from_slice(&(d.len() as u32).to_le_bytes());
            v.extend_from_slice(d);
            v
        }
        _ => panic!("only Ack/Data used in this harness"),
    };
    let h = blake3::hash(&payload_bytes);
    buf.extend_from_slice(h.as_bytes());
    for p in preds {
        buf.extend_from_slice(p);
    }
    buf
}

// ===========================================================================
// ATTACK 1 — Byzantine creator forks their OWN strand (equivocation).
// Lean claims: detectable as an incomparable pair; tip evicted.
// ===========================================================================

#[test]
fn attack_byzantine_self_fork_is_detected_and_evicted() {
    let me = dalek_key(1);
    // The identity label the lace keys equivocation bookkeeping by: the hybrid
    // id, NOT `me.verifying_key()`.
    let me_id = Block::hybrid_id(&me);
    let mut lace = Blocklace::new_simple(me.clone());

    // Genesis-ish: a seq-0 block with no predecessors.
    let b0 = Block::new(&me, 0, Payload::Ack, vec![]);
    lace.receive_block(b0.clone()).expect("b0 ok");

    // Two DISTINCT seq-1 blocks both extending b0 with different payloads.
    // (Same creator, same seq, mutually non-preceding ⇒ a fork.)
    let fork_a = Block::new(&me, 1, Payload::Data(vec![0xAA]), vec![b0.id()]);
    let fork_b = Block::new(&me, 1, Payload::Data(vec![0xBB]), vec![b0.id()]);

    lace.receive_block(fork_a).expect("first arm accepted");
    let r = lace.receive_block(fork_b);
    // EVIDENCE: the second arm is flagged as equivocation.
    match r {
        Err(BlockError::Equivocation { creator, seq, .. }) => {
            assert_eq!(
                creator, me_id,
                "equivocation must be attributed to the hybrid id"
            );
            assert_eq!(seq, 1, "the fork is at seq 1");
        }
        other => panic!("expected Equivocation, got {other:?}"),
    }
    assert!(lace.is_equivocator(&me_id));
    // The tip is EVICTED — the equivocator no longer has a live strand head.
    assert!(
        !lace.tips().contains_key(&me_id),
        "equivocator's tip must be evicted"
    );
    eprintln!("[BL ATTACK 1] self-fork: DEFENDED (detected + flagged)");
}

// ===========================================================================
// ATTACK 2 — forge a block as a DIFFERENT creator (no private key).
// Lean/Rust claim: verify_signature rejects.
// ===========================================================================

#[test]
fn attack_forge_block_for_other_creator_is_rejected() {
    let me = dalek_key(2);
    let victim = dalek_key(3);
    // Everything the forger legitimately knows about the victim: their PUBLIC
    // ed25519 key and their PUBLIC hybrid id. No secrets.
    let victim_ed = victim.verifying_key().to_bytes();
    let victim_id = Block::hybrid_id(&victim);
    let mut lace = Blocklace::new_simple(me.clone());

    // Impersonate the victim wholesale: claim their hybrid id AND carry their
    // real ed25519 key, but sign with OUR key (we do not have theirs).
    //
    // This block PASSES every identity check — `creator` genuinely recomputes as
    // `H(victim_ed ‖ victim_ml_dsa)`, and `ed25519` genuinely is the victim's key
    // — so nothing but the SIGNATURE can refuse it. That is the point: the test
    // must fail on the signature, not incidentally on an id mismatch.
    let content = signing_content(&victim_id, 0, &Payload::Ack, &[]);
    let sig = me.sign(&content).to_bytes();
    let forged = Block {
        creator: victim_id,
        ed25519: victim_ed,
        seq: 0,
        payload: Payload::Ack,
        predecessors: vec![],
        signature: sig,
        pq_signature: Vec::new(),
    };

    // NON-VACUITY: the forgery must be well-formed everywhere EXCEPT the sig.
    // If these ever drift, the test below would "pass" for the wrong reason.
    assert_eq!(
        forged.creator,
        Block::hybrid_id_from_parts(&forged.ed25519, &Block::pq_public_key(&victim)),
        "forged block must carry a WELL-FORMED victim identity: the id gate must \
         not be what rejects it"
    );
    // NON-VACUITY: the very same block, signed by the VICTIM instead of us, is
    // ACCEPTED. So the only thing standing between the forger and injection is
    // possession of the victim's key — exactly the property under test.
    {
        let honest = Block {
            signature: victim.sign(&content).to_bytes(),
            ..forged.clone()
        };
        Blocklace::new_simple(me.clone())
            .receive_block(honest)
            .expect("the same block signed by the VICTIM must be accepted");
    }

    let r = lace.receive_block(forged);
    match r {
        Err(BlockError::InvalidSignature { creator, seq }) => {
            assert_eq!(creator, victim_id);
            assert_eq!(seq, 0);
        }
        other => panic!("expected InvalidSignature, got {other:?}"),
    }
    eprintln!("[BL ATTACK 2] cross-creator forgery: DEFENDED (sig rejected)");
}

// ===========================================================================
// ATTACK 2b — the forgery variant the CLASSICAL half alone cannot refuse:
// claim the victim's hybrid id but carry OUR OWN ed25519 key and a signature
// that genuinely verifies under it. `verify_signature` parses `self.ed25519`,
// so the classical check is SATISFIED — only the hybrid COMMITMENT GATE
// (`creator == H(ed25519 ‖ enrolled_ml_dsa)`) refuses this block.
//
// This is the attack that motivates the hybrid id existing at all, so it must
// be tested against the check that actually defends it: `verify_hybrid`.
// ===========================================================================

#[test]
fn attack_forge_under_victim_id_with_own_key_fails_commitment_gate() {
    let me = dalek_key(2);
    let victim = dalek_key(3);
    let victim_id = Block::hybrid_id(&victim);
    let victim_pq = Block::pq_public_key(&victim);

    // Our own key, victim's identity label.
    let content = signing_content(&victim_id, 0, &Payload::Ack, &[]);
    let forged = Block {
        creator: victim_id,
        ed25519: me.verifying_key().to_bytes(),
        seq: 0,
        payload: Payload::Ack,
        predecessors: vec![],
        signature: me.sign(&content).to_bytes(),
        pq_signature: Vec::new(),
    };

    // NON-VACUITY: the CLASSICAL half really does verify. The block is refused
    // by the commitment gate, not by a broken signature.
    forged
        .verify_signature()
        .expect("classical half MUST verify — otherwise this is not the 2b attack");

    // The gate: `victim_id` does not commit to OUR ed25519 key.
    match forged.verify_hybrid(&victim_pq) {
        Err(BlockError::BadPqSignature { creator, seq }) => {
            assert_eq!(creator, victim_id);
            assert_eq!(seq, 0);
        }
        other => panic!("expected BadPqSignature from the commitment gate, got {other:?}"),
    }

    // NON-VACUITY / DISCRIMINATION: prove it was the GATE that refused, not a
    // later check. The same block shape whose id DOES commit to its carried
    // ed25519 key (our own identity, our own enrolled PQ key) gets PAST the gate
    // and is refused one check later, by the missing-PQ sentinel. So
    // `BadPqSignature` above is reachable ONLY from the commitment gate: with
    // `pq_signature` empty, the ML-DSA verification branch is never reached.
    {
        let me_id = Block::hybrid_id(&me);
        let content = signing_content(&me_id, 0, &Payload::Ack, &[]);
        let own = Block {
            creator: me_id,
            ed25519: me.verifying_key().to_bytes(),
            seq: 0,
            payload: Payload::Ack,
            predecessors: vec![],
            signature: me.sign(&content).to_bytes(),
            pq_signature: Vec::new(),
        };
        assert!(
            matches!(
                own.verify_hybrid(&Block::pq_public_key(&me)),
                Err(BlockError::UnsignedPq { .. })
            ),
            "a well-committed id must PASS the gate and fall through to the \
             missing-PQ check — otherwise the gate is not what refuses 2b"
        );
    }
    eprintln!("[BL ATTACK 2b] id-substitution forgery: DEFENDED (hybrid commitment gate)");
}

// ===========================================================================
// ATTACK 3 — FRAMING via signature malleability. The block id binds the
// signature bytes: id = blake3(content || signature). If a non-canonical
// re-encoding of an honest block's signature still VERIFIES, it yields a NEW
// id with the SAME (creator, seq, preds) but is incomparable to the original
// → detect_equivocation would flag the HONEST creator as an equivocator and
// evict them. We probe whether dalek v2 accepts a malleated signature.
//
// Outcome interpretation:
//  - If the malleated sig is REJECTED -> DEFENDED (dalek v2 strictness saves us).
//  - If ACCEPTED and the honest creator gets evicted -> FINDING (framing works).
// ===========================================================================

#[test]
fn probe_signature_malleability_framing() {
    let honest = dalek_key(4);
    let honest_id = Block::hybrid_id(&honest);
    let mut lace = Blocklace::new_simple(honest.clone());

    let b0 = Block::new(&honest, 0, Payload::Ack, vec![]);
    lace.receive_block(b0.clone()).expect("b0 ok");

    let b1 = Block::new(&honest, 1, Payload::Data(vec![1, 2, 3]), vec![b0.id()]);
    lace.receive_block(b1.clone()).expect("honest b1 ok");

    // Malleate: add the ed25519 group order L to the S scalar (upper 32 bytes).
    // L = 2^252 + 27742317777372353535851937790883648493 (little-endian).
    const L: [u8; 32] = [
        0xed, 0xd3, 0xf5, 0x5c, 0x1a, 0x63, 0x12, 0x58, 0xd6, 0x9c, 0xf7, 0xa2, 0xde, 0xf9, 0xde,
        0x14, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x10,
    ];
    // NON-VACUITY: the honest strand really is live and unflagged before the
    // framing attempt, so a later `!framed_out` means the attack was REFUSED —
    // not that the creator was never tracked in the first place.
    assert!(!lace.is_equivocator(&honest_id));
    assert_eq!(lace.tips().get(&honest_id), Some(&b1.id()));

    let mut mal = b1.signature;
    // s' = s + L  (mod 2^256, little-endian add with carry).
    let mut carry = 0u16;
    for i in 0..32 {
        let v = mal[32 + i] as u16 + L[i] as u16 + carry;
        mal[32 + i] = (v & 0xff) as u8;
        carry = v >> 8;
    }

    // The framer only ever has the HONEST block, so they carry its identity
    // halves and its PQ signature verbatim; the ONLY thing they touch is the
    // ed25519 S scalar. (The malleated sig changes `id()`, so b1's PQ half no
    // longer matches — irrelevant on the ed25519-only `receive_block` path, and
    // an independent reason `receive_block_pinned` would refuse it.)
    let framed = Block {
        creator: b1.creator,
        ed25519: b1.ed25519,
        seq: 1,
        payload: b1.payload.clone(),
        predecessors: b1.predecessors.clone(),
        signature: mal,
        pq_signature: b1.pq_signature.clone(),
    };

    // First: does the malleated block even verify?
    let verifies = framed.verify_signature().is_ok();
    // Then: feed it to the lace and see if the honest creator is framed.
    let r = lace.receive_block(framed);
    let framed_out = lace.is_equivocator(&honest_id);

    eprintln!(
        "[BL ATTACK 3 / PROBE] malleated-sig verifies={} receive_block={:?} honest_framed={}",
        verifies, r, framed_out
    );
    // Assert the SAFE outcome so this test FAILS loudly if framing ever works.
    assert!(
        !framed_out,
        "FINDING: honest creator framed as equivocator via signature malleability"
    );
    // And the honest strand head is UNDISTURBED — no tip eviction.
    assert_eq!(
        lace.tips().get(&honest_id),
        Some(&b1.id()),
        "honest creator's tip must survive the framing attempt"
    );
}

// ===========================================================================
// ATTACK 4 — replay the SAME honest block twice (idempotency / no self-frame).
// Re-receiving an identical block must be a no-op, NOT a self-equivocation.
// ===========================================================================

#[test]
fn attack_replay_same_block_is_idempotent_not_equivocation() {
    let me = dalek_key(5);
    let me_id = Block::hybrid_id(&me);
    let mut lace = Blocklace::new_simple(me.clone());
    let b0 = Block::new(&me, 0, Payload::Ack, vec![]);
    lace.receive_block(b0.clone()).expect("first ok");
    // Replay identical block: same id, already present -> Ok, no equivocation.
    lace.receive_block(b0.clone()).expect("replay ok");
    assert!(!lace.is_equivocator(&me_id));
    assert_eq!(lace.len(), 1, "replay must not duplicate the block");
    eprintln!("[BL ATTACK 4] identical replay: DEFENDED (idempotent)");
}
