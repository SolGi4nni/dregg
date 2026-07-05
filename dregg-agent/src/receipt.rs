//! The ONE product-wide receipt contract.
//!
//! The kernel already has the right primitive twice over: the `TurnReceipt`
//! chain (`breadstuffs/turn/src/turn.rs`, `Receipt.lean`'s
//! `chain_tamper_evident`) and the `BridgeReceipt` envelope
//! (`breadstuffs/cell-crypto/src/note_bridge.rs`). Both are **append-only,
//! prev-hash-chained, signature-bearing records a non-witness can verify**.
//! That is the discipline; everything above the kernel must speak it too.
//!
//! Above the kernel the product surfaces had drifted into ~10 distinct
//! "receipt" notions, most of them post-hoc log structs (a `seq`, a
//! `content_root`, an owner — nothing chained, nothing signed, nothing a
//! third party can re-witness). ember's re-grounding: **a deploy / publish /
//! bind / put IS a turn, so the kernel receipt is already the receipt.** Each
//! product "receipt" is therefore either:
//!
//! 1. **a typed VIEW** over a turn receipt — it carries the turn-receipt hash
//!    plus its typed fields (e.g. a `DeployReceipt` is a view over the
//!    `PublishReceipt` of the publish turn it ran), or
//! 2. **a genuinely-offchain owned-state transition made REAL** — signed and
//!    prev-hash-chained here, exactly like a `BridgeReceipt`, so a client can
//!    verify a publish/bind/put without trusting the host.
//!
//! This crate is the shared vocabulary for both. A [`ReceiptBody`] is the
//! typed "what happened"; a [`ReceiptAttestation`] lifts it into the
//! discipline (prev-hash link + ed25519 signature, optionally naming the
//! kernel turn receipt it is a view of); [`ReceiptChain`] is the producer-side
//! sealer (a registry owns one); and [`verify_chain`] is the non-witness
//! verifier. See `docs/RECEIPT-CONTRACT.md` (breadstuffs) for the contract in
//! prose.

use ed25519_dalek::{Signature, Signer, SigningKey, Verifier, VerifyingKey};
use serde::{Deserialize, Serialize};
use std::sync::Mutex;

/// Domain separator for the canonical receipt hash (the thing that is signed
/// and chained). Bumping this is a receipt-format epoch.
pub const RECEIPT_DOMAIN: &[u8] = b"dregg-receipt-v1";

/// The chained, signed attestation that lifts a typed [`ReceiptBody`] into the
/// kernel receipt discipline.
///
/// - `prev_receipt_hash` makes the producer's stream **append-only and
///   tamper-evident** (the same role as `TurnReceipt::previous_receipt_hash`
///   and `BridgeReceiptEnvelope::previous_phase_receipt_hash`).
/// - `turn_receipt_hash`, when present, names the **kernel turn receipt this
///   record is a typed VIEW of** — the re-grounding's "a publish/bind IS a
///   turn" made explicit. `None` for an owned-state transition that is itself
///   the root authority (the producer's signature below carries it).
/// - `signer` + `signature` make it **re-witnessable**: anyone holding the
///   producer's public key can verify the record without having been present.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReceiptAttestation {
    /// BLAKE3 receipt-hash of the previous receipt in this producer's chain;
    /// `None` only for the genesis receipt.
    pub prev_receipt_hash: Option<[u8; 32]>,
    /// The kernel `TurnReceipt`/`BridgeReceipt` hash this record is a view of,
    /// when it is a projection of a turn rather than a root owned-state step.
    pub turn_receipt_hash: Option<[u8; 32]>,
    /// The producing authority's ed25519 public key (32 bytes).
    pub signer: [u8; 32],
    /// ed25519 signature over [`receipt_hash`] (64 bytes).
    pub signature: Vec<u8>,
}

/// A typed receipt body that can be lifted into the contract.
///
/// Implementors are the product receipts (`PublishReceipt`, `BindReceipt`,
/// `BucketReceipt`, `PutReceipt`, `DeleteReceipt`, …). They expose their
/// canonical field hash, their chain position, and — once sealed — their
/// attestation.
pub trait ReceiptBody {
    /// Canonical, domain-separated hash of the typed "what happened" fields.
    /// Must NOT include the attestation (the attestation signs over this).
    fn body_hash(&self) -> [u8; 32];

    /// The producer-monotonic sequence number (the chain position).
    fn seq(&self) -> u64;

    /// The attestation, present once the receipt has been sealed into a chain.
    /// `None` for a bare, unsigned local projection.
    fn attestation(&self) -> Option<&ReceiptAttestation>;

    /// The canonical receipt hash of this (sealed) receipt — the value the
    /// *next* receipt in the chain links back to. `None` if unsealed.
    fn receipt_hash(&self) -> Option<[u8; 32]> {
        let att = self.attestation()?;
        Some(receipt_hash(
            &self.body_hash(),
            self.seq(),
            att.prev_receipt_hash.as_ref(),
            att.turn_receipt_hash.as_ref(),
        ))
    }
}

/// A domain-separated, length-prefixed hasher for building a
/// [`ReceiptBody::body_hash`] — so a product crate can hash its typed fields
/// canonically without depending on blake3 directly. Length-prefixing each
/// field makes the concatenation unambiguous (no separator-collision).
pub struct BodyHasher(blake3::Hasher);

impl BodyHasher {
    /// A fresh hasher seeded with a per-receipt-kind domain (e.g. `b"publish-receipt-v1"`).
    pub fn new(domain: &[u8]) -> BodyHasher {
        let mut h = blake3::Hasher::new();
        h.update(domain);
        BodyHasher(h)
    }
    /// Absorb a variable-length field (length-prefixed).
    pub fn field(&mut self, bytes: &[u8]) -> &mut BodyHasher {
        self.0.update(&(bytes.len() as u64).to_le_bytes());
        self.0.update(bytes);
        self
    }
    /// Absorb a `u64`.
    pub fn u64(&mut self, v: u64) -> &mut BodyHasher {
        self.0.update(&v.to_le_bytes());
        self
    }
    /// Absorb a `bool`.
    pub fn bool(&mut self, v: bool) -> &mut BodyHasher {
        self.0.update(&[v as u8]);
        self
    }
    /// The 32-byte body hash.
    pub fn finalize(&self) -> [u8; 32] {
        *self.0.finalize().as_bytes()
    }
}

/// The canonical receipt hash: what a producer signs and what the next receipt
/// chains to. Domain-separated; binds the body, the sequence, the prev link,
/// and any turn-receipt view link.
pub fn receipt_hash(
    body_hash: &[u8; 32],
    seq: u64,
    prev_receipt_hash: Option<&[u8; 32]>,
    turn_receipt_hash: Option<&[u8; 32]>,
) -> [u8; 32] {
    let mut h = blake3::Hasher::new();
    h.update(RECEIPT_DOMAIN);
    h.update(body_hash);
    h.update(&seq.to_le_bytes());
    match prev_receipt_hash {
        Some(p) => {
            h.update(&[1u8]);
            h.update(p);
        }
        None => {
            h.update(&[0u8]);
        }
    };
    match turn_receipt_hash {
        Some(t) => {
            h.update(&[1u8]);
            h.update(t);
        }
        None => {
            h.update(&[0u8]);
        }
    };
    *h.finalize().as_bytes()
}

/// A producer's signing identity. Deterministic from a 32-byte secret seed —
/// a real producer configures a persistent secret; tests use a fixed seed.
#[derive(Clone)]
pub struct ReceiptSigner {
    key: SigningKey,
}

impl ReceiptSigner {
    /// A signer from a 32-byte secret seed (deterministic).
    pub fn from_seed(seed: [u8; 32]) -> ReceiptSigner {
        ReceiptSigner {
            key: SigningKey::from_bytes(&seed),
        }
    }

    /// The public key that verifies this signer's receipts.
    pub fn public(&self) -> [u8; 32] {
        self.key.verifying_key().to_bytes()
    }

    /// Sign a raw, already-domain-separated message digest directly (NOT a chain
    /// receipt) — the low-level seam a co-signing protocol uses when several
    /// independent signers each attest the *same* fact (e.g. a federation quorum
    /// over a QA result). The caller owns the domain separation of `msg`; verify
    /// with [`verify_signature`] under this signer's [`public`](Self::public) key.
    pub fn sign_raw(&self, msg: &[u8]) -> Vec<u8> {
        let sig: Signature = self.key.sign(msg);
        sig.to_bytes().to_vec()
    }

    /// Produce the attestation for a body, given the chain's current head and
    /// an optional turn-receipt view link. Returns the attestation and the
    /// resulting receipt hash (the new chain head).
    pub fn attest(
        &self,
        body_hash: &[u8; 32],
        seq: u64,
        prev_receipt_hash: Option<[u8; 32]>,
        turn_receipt_hash: Option<[u8; 32]>,
    ) -> (ReceiptAttestation, [u8; 32]) {
        let rh = receipt_hash(
            body_hash,
            seq,
            prev_receipt_hash.as_ref(),
            turn_receipt_hash.as_ref(),
        );
        let sig: Signature = self.key.sign(&rh);
        let att = ReceiptAttestation {
            prev_receipt_hash,
            turn_receipt_hash,
            signer: self.public(),
            signature: sig.to_bytes().to_vec(),
        };
        (att, rh)
    }
}

/// Verify a raw ed25519 signature `sig` over `msg` under `signer`'s public key.
/// The non-witness companion to [`ReceiptSigner::sign_raw`]: `true` iff `signer`
/// produced `sig` over exactly `msg`. A tampered message, a wrong signer, or a
/// malformed key/signature all return `false` (fail-closed). Used to re-witness
/// each independent co-signer in a multi-sig quorum over a shared fact.
pub fn verify_signature(signer: &[u8; 32], msg: &[u8], sig: &[u8]) -> bool {
    let Ok(vk) = VerifyingKey::from_bytes(signer) else {
        return false;
    };
    let Ok(sig) = Signature::from_slice(sig) else {
        return false;
    };
    vk.verify(msg, &sig).is_ok()
}

/// The producer-side chain: a [`ReceiptSigner`] plus the moving chain head.
/// A registry that emits receipts owns one; each emit [`seal`](ReceiptChain::seal)s
/// the next body, advancing the head so the stream is append-only.
pub struct ReceiptChain {
    signer: ReceiptSigner,
    head: Mutex<Option<[u8; 32]>>,
}

impl ReceiptChain {
    /// A fresh chain (empty head) signing under `signer`.
    pub fn new(signer: ReceiptSigner) -> ReceiptChain {
        ReceiptChain {
            signer,
            head: Mutex::new(None),
        }
    }

    /// A fresh chain from a secret seed.
    pub fn from_seed(seed: [u8; 32]) -> ReceiptChain {
        ReceiptChain::new(ReceiptSigner::from_seed(seed))
    }

    /// **Resume** a chain under `seed` with its head already advanced to `head` — the
    /// tip of a PERSISTED chain, so a cold-woken session's next [`seal`](ReceiptChain::seal)
    /// links to the persisted tip rather than an empty head (a fork). `head == None`
    /// is exactly [`from_seed`](ReceiptChain::from_seed). The seed re-derives the SAME
    /// signer, so the resumed chain re-signs under the persisted key.
    pub fn resume(seed: [u8; 32], head: Option<[u8; 32]>) -> ReceiptChain {
        ReceiptChain {
            signer: ReceiptSigner::from_seed(seed),
            head: Mutex::new(head),
        }
    }

    /// The public key non-witnesses verify this chain's receipts under.
    pub fn signer_public(&self) -> [u8; 32] {
        self.signer.public()
    }

    /// Seal a body into the chain: link it to the current head, sign it, and
    /// advance the head. `turn_receipt_hash` names the kernel turn receipt this
    /// record is a view of (or `None` for a root owned-state transition).
    pub fn seal(
        &self,
        body_hash: [u8; 32],
        seq: u64,
        turn_receipt_hash: Option<[u8; 32]>,
    ) -> ReceiptAttestation {
        let mut head = self.head.lock().expect("receipt chain head poisoned");
        let (att, rh) = self
            .signer
            .attest(&body_hash, seq, *head, turn_receipt_hash);
        *head = Some(rh);
        att
    }
}

/// Why a receipt chain failed to verify.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ChainError {
    /// A receipt carried no attestation — a bare log struct, not a receipt.
    Unsigned { seq: u64 },
    /// The signature did not verify under the named signer (forged/tampered).
    BadSignature { seq: u64 },
    /// `prev_receipt_hash` did not equal the previous receipt's hash — the
    /// stream was reordered, spliced, or had a record removed.
    BrokenLink { seq: u64 },
    /// Sequence numbers did not strictly increase.
    NonMonotonic { seq: u64 },
    /// Two adjacent receipts were signed by different keys (no single
    /// producer authority over the stream).
    SignerChanged { seq: u64 },
}

/// Verify a producer's receipt chain end-to-end: every receipt is signed by
/// the same key, signatures verify, sequences strictly increase, and each
/// `prev_receipt_hash` links to the prior receipt's hash. This is the
/// non-witness check — it needs only the receipts and the signer's public key
/// (carried in each attestation).
///
/// An empty slice verifies vacuously.
pub fn verify_chain<R: ReceiptBody>(receipts: &[R]) -> Result<(), ChainError> {
    verify_chain_from(receipts, None)
}

/// As [`verify_chain`], but for a **sub-chain** that does not start at genesis:
/// the first receipt's `prev_receipt_hash` must equal `initial_prev` (e.g. the
/// hash of a `create` receipt that precedes a run of `put`s in the same
/// producer chain). `verify_chain(rs) == verify_chain_from(rs, None)`.
pub fn verify_chain_from<R: ReceiptBody>(
    receipts: &[R],
    initial_prev: Option<[u8; 32]>,
) -> Result<(), ChainError> {
    let mut expected_prev: Option<[u8; 32]> = initial_prev;
    let mut last_seq: Option<u64> = None;
    let mut signer: Option<[u8; 32]> = None;

    for r in receipts {
        let att = r
            .attestation()
            .ok_or(ChainError::Unsigned { seq: r.seq() })?;

        if let Some(ls) = last_seq {
            if r.seq() <= ls {
                return Err(ChainError::NonMonotonic { seq: r.seq() });
            }
        }
        match signer {
            None => signer = Some(att.signer),
            Some(s) if s != att.signer => return Err(ChainError::SignerChanged { seq: r.seq() }),
            _ => {}
        }
        if att.prev_receipt_hash != expected_prev {
            return Err(ChainError::BrokenLink { seq: r.seq() });
        }

        let rh = receipt_hash(
            &r.body_hash(),
            r.seq(),
            att.prev_receipt_hash.as_ref(),
            att.turn_receipt_hash.as_ref(),
        );
        let vk = VerifyingKey::from_bytes(&att.signer)
            .map_err(|_| ChainError::BadSignature { seq: r.seq() })?;
        let sig = Signature::from_slice(&att.signature)
            .map_err(|_| ChainError::BadSignature { seq: r.seq() })?;
        vk.verify(&rh, &sig)
            .map_err(|_| ChainError::BadSignature { seq: r.seq() })?;

        expected_prev = Some(rh);
        last_seq = Some(r.seq());
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A minimal body for exercising the contract in isolation.
    #[derive(Clone, Debug)]
    struct DummyBody {
        seq: u64,
        payload: String,
        attest: Option<ReceiptAttestation>,
    }

    impl ReceiptBody for DummyBody {
        fn body_hash(&self) -> [u8; 32] {
            let mut h = blake3::Hasher::new();
            h.update(b"dummy-body-v1");
            h.update(&self.seq.to_le_bytes());
            h.update(self.payload.as_bytes());
            *h.finalize().as_bytes()
        }
        fn seq(&self) -> u64 {
            self.seq
        }
        fn attestation(&self) -> Option<&ReceiptAttestation> {
            self.attest.as_ref()
        }
    }

    fn chain_of(n: u64) -> (Vec<DummyBody>, ReceiptChain) {
        let chain = ReceiptChain::from_seed([7u8; 32]);
        let mut out = Vec::new();
        for i in 0..n {
            let mut b = DummyBody {
                seq: i,
                payload: format!("op-{i}"),
                attest: None,
            };
            b.attest = Some(chain.seal(b.body_hash(), b.seq(), None));
            out.push(b);
        }
        (out, chain)
    }

    #[test]
    fn a_sealed_chain_verifies() {
        let (receipts, _) = chain_of(5);
        assert_eq!(verify_chain(&receipts), Ok(()));
        // The genesis links to nothing; the rest link forward.
        assert!(
            receipts[0]
                .attestation()
                .unwrap()
                .prev_receipt_hash
                .is_none()
        );
        assert_eq!(
            receipts[1].attestation().unwrap().prev_receipt_hash,
            receipts[0].receipt_hash()
        );
    }

    #[test]
    fn an_unsigned_body_is_not_a_receipt() {
        let b = DummyBody {
            seq: 0,
            payload: "x".into(),
            attest: None,
        };
        assert_eq!(verify_chain(&[b]), Err(ChainError::Unsigned { seq: 0 }));
    }

    #[test]
    fn tampering_the_body_breaks_the_signature() {
        let (mut receipts, _) = chain_of(3);
        // Forge the payload after sealing: body_hash changes, signature no longer matches.
        receipts[1].payload = "tampered".into();
        assert_eq!(
            verify_chain(&receipts),
            Err(ChainError::BadSignature { seq: 1 })
        );
    }

    #[test]
    fn removing_a_receipt_breaks_the_link() {
        let (mut receipts, _) = chain_of(4);
        receipts.remove(2); // splice out the middle — prev links no longer match
        assert_eq!(
            verify_chain(&receipts),
            Err(ChainError::BrokenLink { seq: 3 })
        );
    }

    #[test]
    fn a_foreign_signer_cannot_extend_the_chain() {
        let (mut receipts, _) = chain_of(2);
        // A different producer seals a record that links to the real head but
        // signs with its own key — caught as a signer change.
        let foreign = ReceiptChain::from_seed([9u8; 32]);
        let mut b = DummyBody {
            seq: 2,
            payload: "evil".into(),
            attest: None,
        };
        // Manually link to the real head so only the signer differs.
        let prev = receipts[1].receipt_hash();
        let (att, _) = ReceiptSigner::from_seed([9u8; 32]).attest(&b.body_hash(), 2, prev, None);
        let _ = &foreign;
        b.attest = Some(att);
        receipts.push(b);
        assert_eq!(
            verify_chain(&receipts),
            Err(ChainError::SignerChanged { seq: 2 })
        );
    }

    #[test]
    fn turn_receipt_view_is_bound() {
        // A receipt that is a typed VIEW of a kernel turn receipt binds that
        // turn-receipt hash into its own hash — tampering the link is caught.
        let chain = ReceiptChain::from_seed([3u8; 32]);
        let turn_hash = [42u8; 32];
        let mut b = DummyBody {
            seq: 0,
            payload: "view".into(),
            attest: None,
        };
        b.attest = Some(chain.seal(b.body_hash(), 0, Some(turn_hash)));
        assert_eq!(verify_chain(std::slice::from_ref(&b)), Ok(()));
        assert_eq!(b.attestation().unwrap().turn_receipt_hash, Some(turn_hash));

        // Swap the claimed turn link → the bound hash no longer matches the signature.
        let mut tampered = b.clone();
        tampered.attest.as_mut().unwrap().turn_receipt_hash = Some([0u8; 32]);
        assert_eq!(
            verify_chain(std::slice::from_ref(&tampered)),
            Err(ChainError::BadSignature { seq: 0 })
        );
    }
}
