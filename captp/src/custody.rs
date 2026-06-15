//! Store-and-forward CUSTODY ACCOUNTABILITY: a signed receipt makes a relay that
//! ACCEPTED custody and then DROPPED a message convictable, while an honest relay
//! (one that delivered or refunded) is provably safe.
//!
//! # The gap this closes
//!
//! [`crate::store_forward`] proves the relay is a delay/drop channel that cannot read,
//! forge, or re-address a box (X25519 + ChaCha20-Poly1305 AEAD). But the relay's whole
//! sanctioned power is to **drop** ([`crate::store_forward::MessageRelay::expire`],
//! [`crate::store_forward::MessageRelay::drain`]'s reorder) — and a drop produced **no
//! evidence**: the relay signed NOTHING. `QueuedMessage` carried no relay commitment;
//! `StoreForwardClient.acknowledge` only mutated the *sender's* own local bookkeeping.
//! So a dropped message could not be proven *against the relay*, and nothing proved an
//! honest relay could not be slashed by a fabricated dispute. Accountability — "a
//! dropped message is convictable, an honest relay is safe" — was the missing calculus.
//!
//! This module is the Rust realization of the verified Lean model
//! `Dregg2.Exec.Custody` (`metatheory/Dregg2/Exec/CustodyReceipt.lean`). The
//! structures mirror it field-for-field; the two headline theorems
//! (`accepted_and_dropped_is_convictable`, `honest_relay_not_slashable`) are the
//! both-polarity teeth in the test module below.
//!
//! # The §8 seam, DISCHARGED here
//!
//! In the Lean model the receipt carries `sig : Bool` — the *carrier* for "the relay's
//! Ed25519 signature over the receipt preimage verifies" — and unforgeability is the
//! named obligation `receiptUnforgeable` routed to the crypto portal. This module is
//! exactly that portal: the receipt carries a real [`Signature`], and
//! [`CustodyReceipt::well_formed`] checks it against the relay's [`PublicKey`] over the
//! canonical, domain-separated preimage. `sig = true` becomes "verify_strict succeeds";
//! the EUF-CMA unforgeability of Ed25519 (only the relay's key can produce a verifying
//! signature) is supplied by `ed25519-dalek`, the vetted crate — never re-proved.
//!
//! # The adjudicator reads the CELL, not the disputant
//!
//! Per `CustodyReceipt.lean` §7.5: the verdict is a pure function of the inbox cell's own
//! authenticated state — a sticky DELIVERY-WITNESS bit ("was THIS box, by its
//! `content_hash`, dequeued toward the recipient?") plus a refund bit — never the
//! disputant's claim. A malicious disputant cannot manufacture a conviction by lying about
//! the outcome, and an honest disputant need not be believed. [`adjudicate_from_inbox`] is
//! the realizable decision procedure the dispute path runs against the inbox cell.
//!
//! The witness bit (not root equality) is what makes the verdict robust to OVERSHOOT /
//! prefix-reorg: an inbox whose `MerkleQueue` head root advanced PAST the promised
//! `new_root` (a later box, a reorg, a late block) STILL acquits a relay that delivered,
//! because delivery is a sticky content-addressed fact, not "the live root equals a past
//! promise". See [`InboxState`] for why bare `root == new_root` silently dropped this.

use dregg_types::{PublicKey, Signature, SigningKey, sign};
use serde::{Deserialize, Serialize};

use crate::FederationId;

// =============================================================================
// §1 — The signed CustodyReceipt and the custody outcome
// =============================================================================

/// Domain-separation tag for the custody-receipt signing preimage. Bump on any
/// wire-format change to the preimage. Distinct tag ⇒ a receipt signature can never be
/// replayed as a handoff cert or any other signed object (cross-protocol confusion).
pub const CUSTODY_RECEIPT_DOMAIN: &[u8] = b"dregg-custody-receipt-v1";

/// **`CustodyReceipt`** — the relay's SIGNED promise of custody, returned when it accepts
/// a box for store-and-forward. Mirrors `Dregg2.Exec.Custody.CustodyReceipt`. It binds:
///
///   * `relay`        — the operator identity that signed it (the party held accountable);
///   * `content_hash` — the content-address of the box the relay accepted (binds the
///     receipt to a specific message; a receipt for a different `content_hash` does not
///     cover this box);
///   * `inbox_owner`  — the destination the box is held FOR (binds custody to the right
///     inbox);
///   * `old_root` / `new_root` — the inbox-root transition the relay PROMISES to effect
///     on delivery (`old_root` = the inbox root at accept time, `new_root` = the root
///     after the box is appended);
///   * `accept_by`    — the deadline height: the relay must DELIVER or REFUND by this
///     height, else it has DROPPED (the accept-or-refund-by clause);
///   * `signature`    — the §8 carrier MADE REAL: the relay's Ed25519 signature over the
///     domain-separated preimage. In the Lean model this is the `sig : Bool` carrier;
///     here it is the actual signature, verified by [`Self::well_formed`].
///
/// The relay's [`PublicKey`] is *not* stored inline — it is `relay` interpreted as a key
/// ([`Self::relay_pubkey`]): a `FederationId` in the unified lace model is the operator's
/// committee commitment / pubkey. This is what makes a valid conviction bind exactly the
/// signer (`conviction_binds_the_signer`).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CustodyReceipt {
    /// The operator identity that signed this receipt (the accountable party).
    pub relay: FederationId,
    /// Content-address of the accepted box (BLAKE3 of the ciphertext envelope).
    pub content_hash: [u8; 32],
    /// The inbox owner the box is held FOR.
    pub inbox_owner: FederationId,
    /// The inbox root at accept time (the transition's source).
    pub old_root: [u8; 32],
    /// The inbox root the relay PROMISES to effect on delivery (the transition's target).
    pub new_root: [u8; 32],
    /// Deadline height: deliver or refund by here, else dropped.
    pub accept_by: u64,
    /// §8 carrier: the relay's Ed25519 signature over [`Self::signing_preimage`].
    pub signature: Signature,
}

impl CustodyReceipt {
    /// The canonical, domain-separated preimage the relay signs. Includes every binding
    /// field EXCEPT the signature itself, so two receipts differing in any bound field
    /// produce distinct preimages (and thus distinct signatures — no field can be swapped
    /// post-hoc without invalidating the signature).
    pub fn signing_preimage(
        relay: &FederationId,
        content_hash: &[u8; 32],
        inbox_owner: &FederationId,
        old_root: &[u8; 32],
        new_root: &[u8; 32],
        accept_by: u64,
    ) -> Vec<u8> {
        let mut msg = Vec::with_capacity(CUSTODY_RECEIPT_DOMAIN.len() + 32 * 4 + 32 + 8);
        msg.extend_from_slice(CUSTODY_RECEIPT_DOMAIN);
        msg.extend_from_slice(&relay.0);
        msg.extend_from_slice(content_hash);
        msg.extend_from_slice(&inbox_owner.0);
        msg.extend_from_slice(old_root);
        msg.extend_from_slice(new_root);
        msg.extend_from_slice(&accept_by.to_le_bytes());
        msg
    }

    /// The preimage for THIS receipt's bound fields.
    fn preimage(&self) -> Vec<u8> {
        Self::signing_preimage(
            &self.relay,
            &self.content_hash,
            &self.inbox_owner,
            &self.old_root,
            &self.new_root,
            self.accept_by,
        )
    }

    /// **The relay signs a custody receipt** — the object `POST /relay/send` (or
    /// [`crate::store_forward::MessageRelay::accept_custody`]) returns. The relay's
    /// `SigningKey` produces an Ed25519 signature over the canonical preimage; the
    /// `relay` id MUST be the public key matching `relay_key` (else the receipt will not
    /// be well-formed and convicts nobody — exactly the binding the model demands).
    pub fn sign(
        relay: FederationId,
        relay_key: &SigningKey,
        content_hash: [u8; 32],
        inbox_owner: FederationId,
        old_root: [u8; 32],
        new_root: [u8; 32],
        accept_by: u64,
    ) -> Self {
        let preimage = Self::signing_preimage(
            &relay,
            &content_hash,
            &inbox_owner,
            &old_root,
            &new_root,
            accept_by,
        );
        let signature = sign(relay_key, &preimage);
        Self {
            relay,
            content_hash,
            inbox_owner,
            old_root,
            new_root,
            accept_by,
            signature,
        }
    }

    /// The relay identity interpreted as an Ed25519 public key (the unified-lace
    /// equivalence: a `FederationId` IS the operator's pubkey/committee commitment).
    pub fn relay_pubkey(&self) -> PublicKey {
        PublicKey(self.relay.0)
    }

    /// **`sig` made real** — the §8 carrier: does the relay's signature over the canonical
    /// preimage verify against the `relay` public key? This is the discharge of the Lean
    /// `sig : Bool` and the `receiptUnforgeable` obligation: only the holder of the
    /// `relay` secret key can make this return `true` (Ed25519 EUF-CMA, by `ed25519-dalek`
    /// `verify_strict`). A forged receipt (no relay key) yields `false`.
    pub fn sig_verifies(&self) -> bool {
        self.relay_pubkey().verify(&self.preimage(), &self.signature)
    }
}

/// **`CustodyOutcome`** — what the relay actually DID with the accepted box, observed
/// at/after the deadline. Mirrors `Dregg2.Exec.Custody.CustodyOutcome`: two honest fates,
/// one dishonest.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum CustodyOutcome {
    /// The recipient drained the box and the inbox root advanced to `root` (HONEST iff
    /// `root` is the promised `new_root`); the recipient's drain witnesses delivery.
    Delivered {
        /// The inbox root after delivery (the cell's authenticated head).
        root: [u8; 32],
    },
    /// The relay returned the fee and released custody before the deadline. HONEST: the
    /// accept-OR-refund-by half — it could not deliver but did not silently keep custody.
    Refunded,
    /// The deadline passed with the box neither delivered nor refunded. DISHONEST: the
    /// relay took custody (and the fee) and silently lost the message.
    Dropped,
}

impl CustodyOutcome {
    /// **`outcome_honest`** — the relay HONORED the receipt: delivered the box to the
    /// PROMISED root, or refunded before the deadline. `Dropped` is dishonest; a
    /// `Delivered` to the WRONG root is also dishonest (the relay effected a different
    /// inbox transition than it signed for — caught here, not papered over). Mirrors
    /// `outcomeHonest`.
    pub fn is_honest_for(&self, receipt: &CustodyReceipt) -> bool {
        match self {
            CustodyOutcome::Delivered { root } => *root == receipt.new_root,
            CustodyOutcome::Refunded => true,
            CustodyOutcome::Dropped => false,
        }
    }
}

// =============================================================================
// §2 — EvidenceOfDrop: the conviction object, and the adjudicator's verdict
// =============================================================================

/// **`EvidenceOfDrop`** — the conviction object submitted by the inbox owner against a
/// relay (the `POST /relay/dispute` body). Mirrors `Dregg2.Exec.Custody.EvidenceOfDrop`:
///
///   * `receipt`         — the relay's OWN signed [`CustodyReceipt`] (binds the dispute to
///     a specific relay, content, owner, and promised transition);
///   * `claimed_outcome` — the outcome the disputant CLAIMS holds at the deadline. NOTE:
///     this is the disputant's *assertion*; the realizable adjudicator
///     ([`adjudicate_from_inbox`]) does NOT trust it — it reads the inbox cell. Carried so
///     a dispute is self-describing and to prove the claim is inert
///     (`disputant_claim_irrelevant`);
///   * `at_height`       — the height the dispute is raised at (must be ≥ `accept_by`:
///     the deadline must have PASSED for a non-delivery to be a drop, not pending custody).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct EvidenceOfDrop {
    /// The relay's own signed receipt (the binding to a specific accountable party).
    pub receipt: CustodyReceipt,
    /// The outcome the disputant claims (an assertion; the cell read overrides it).
    pub claimed_outcome: CustodyOutcome,
    /// The height the dispute is raised at (must be ≥ `receipt.accept_by`).
    pub at_height: u64,
}

impl EvidenceOfDrop {
    /// **`well_formed`** — the evidence is admissible: the receipt's signature verifies
    /// (binding it to `receipt.relay`) AND the dispute is raised at or after the deadline
    /// (`at_height ≥ accept_by`, so the relay has actually defaulted). A forged receipt or
    /// a premature dispute is NOT admissible — the two non-malleability gates. Mirrors
    /// `wellFormed`.
    pub fn well_formed(&self) -> bool {
        self.receipt.sig_verifies() && self.at_height >= self.receipt.accept_by
    }

    /// **`adjudicate`** — the verdict given the TRUE custody outcome (what the relay
    /// actually did, established by the inbox cell's authenticated state — see
    /// [`true_outcome_from_inbox`]). Returns `slash` (`true`) IFF the evidence is
    /// well-formed AND the true outcome is `Dropped`; otherwise `acquit`. It does NOT take
    /// the disputant's `claimed_outcome` on faith. Mirrors `adjudicate`.
    pub fn adjudicate(&self, true_outcome: CustodyOutcome) -> bool {
        self.well_formed() && matches!(true_outcome, CustodyOutcome::Dropped)
    }

    /// **`evidence_of_drop`** — the canonical evidence the inbox owner assembles from a
    /// relay's receipt once the deadline has passed (`at_height = accept_by`, the earliest
    /// admissible height), claiming the box was `Dropped`. Mirrors `evidenceOfDrop`.
    pub fn from_receipt(receipt: CustodyReceipt) -> Self {
        let at_height = receipt.accept_by;
        Self {
            receipt,
            claimed_outcome: CustodyOutcome::Dropped,
            at_height,
        }
    }
}

// =============================================================================
// §7.5 — The REALIZABLE adjudicator: the true outcome is DERIVED from the inbox's
// authenticated monotone root, not TAKEN from the disputant
// =============================================================================

/// **`InboxState`** — exactly what the adjudication path READS to establish the true
/// custody outcome. Two authenticated bits PLUS the live root:
///
///   * `delivered_witness` — **the DELIVERY-WITNESS bit: "was THIS box delivered?"** Set by
///     the inbox cell when the box bound by the receipt (its `content_hash`) leaves the
///     queue toward the recipient — concretely, a [`crate::store_forward`] / `MerkleQueue`
///     dequeue whose `entry.content_hash == receipt.content_hash`. This is the realizable,
///     content-address-HONEST signal of delivery, and it is **STICKY**: once the box has been
///     delivered the cell records it permanently, so no later root movement un-witnesses it.
///   * `refund_recorded`  — the relay recorded a refund before the deadline (the
///     accept-OR-refund-by other half), an authenticated cell event.
///   * `root`             — the inbox's authenticated MONOTONE root at the dispute height
///     (the `CapInbox` / queue head root, which only ever advances). Carried for the
///     `Delivered { root }` outcome and for diagnostics — the verdict reads the WITNESS bit,
///     never bare root equality (see below).
///
/// Mirrors `Dregg2.Exec.Custody.InboxState` field-for-field.
///
/// # Why the witness bit and NOT root equality (the overshoot/reorg fidelity gap, CLOSED)
///
/// The earlier realization derived delivery from `root == new_root`. That is more honest than
/// the Lean `Nat` `>=` for an opaque content-address — but it SILENTLY DROPS the
/// overshoot/prefix-reorg robustness the Lean model proves: an inbox whose authenticated root
/// advanced PAST the promised `new_root` (a later box enqueued/dequeued, a reorg, a late
/// block) no longer EQUALS `new_root`, so it read as [`CustodyOutcome::Dropped`] — a FALSE
/// conviction of a relay that actually delivered, the exact OPPOSITE of the Lean verdict
/// (`overshoot_acquits`, `monotone_root_no_erased_delivery` / `sticky_witness_no_erased_delivery`).
/// The explicit sticky witness bit is the fix: it answers "was this box delivered?" (a fact
/// that stays true once set), not "does the live root equal a past promise?" (a fact that any
/// subsequent activity breaks). With it, Lean and this adjudicator AGREE on overshoot — neither
/// false-convicts a delivered relay. Construct the bit content-address-honestly from the actual
/// delivery event via [`Self::from_dequeue`].
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct InboxState {
    /// THE DELIVERY-WITNESS bit: the cell recorded that THIS box (`receipt.content_hash`) was
    /// delivered to the recipient (dequeued from the inbox). STICKY: never retracted once set.
    pub delivered_witness: bool,
    /// The relay recorded a refund before the deadline (an authenticated cell event).
    pub refund_recorded: bool,
    /// The inbox's authenticated root at the dispute height. MONOTONE: once it reaches a
    /// value it never retreats (the cursor discipline of the FIFO inbox). Carried for the
    /// `Delivered { root }` outcome; the verdict reads `delivered_witness`, not this.
    pub root: [u8; 32],
}

impl InboxState {
    /// **The content-address-HONEST witness constructor.** Build the inbox state the
    /// adjudicator reads from the AUTHENTICATED delivery evidence: the set of dequeue events
    /// the inbox emitted (each carrying the `content_hash` of the box it removed from the
    /// queue head — see [`crate::store_forward`] / the storage `DequeueProof`), the live
    /// inbox `root`, and whether a refund was recorded. The witness bit is set IFF some
    /// dequeue carried THIS receipt's `content_hash` — i.e. the box bound by the receipt
    /// actually left the queue toward the recipient. This is sticky and ORDER-FREE: it holds
    /// regardless of how the root subsequently moved (overshoot/reorg robust), exactly as the
    /// Lean `deliveredOf` reads the witness bit and not root equality.
    ///
    /// `delivered_content_hashes` is the cell's authenticated record of "boxes that left this
    /// inbox toward the recipient" (the `content_hash` field of each `DequeueProof.entry`). An
    /// honest inbox accumulates it append-only; the membership test is therefore the sticky
    /// witness.
    pub fn from_dequeue(
        receipt: &CustodyReceipt,
        delivered_content_hashes: &[[u8; 32]],
        root: [u8; 32],
        refund_recorded: bool,
    ) -> Self {
        let delivered_witness = delivered_content_hashes.contains(&receipt.content_hash);
        Self {
            delivered_witness,
            refund_recorded,
            root,
        }
    }

    /// **`delivered_of`** — the realizable delivery-witness bit READ from the cell: was THIS
    /// box delivered? The single source of truth the verdict consults. Mirrors the Lean
    /// `deliveredOf`. Order-free and sticky — the content-address-honest replacement for the
    /// brittle `root == new_root` equality (which the overshoot case broke). The `_receipt`
    /// argument is the box identity the bit is recorded against (set by [`Self::from_dequeue`]
    /// keyed on `receipt.content_hash`); the stored bit already pertains to this receipt.
    pub fn delivered_of(&self, _receipt: &CustodyReceipt) -> bool {
        self.delivered_witness
    }

    /// **`true_outcome_from_inbox`** — the custody outcome DERIVED from this authenticated
    /// inbox state for `receipt`. NOT the disputant's claim: a verified fact read off the
    /// cell. Mirrors `trueOutcomeFromInbox`:
    ///
    ///   * the DELIVERY-WITNESS bit is set for this box → `Delivered { root }` (the box left
    ///     the queue toward the recipient; STICKY, so this survives any later root movement,
    ///     including overshoot) (HONEST);
    ///   * else if a refund was recorded → `Refunded` (HONEST);
    ///   * else → `Dropped` (the deadline passed, the box was never delivered, no refund —
    ///     established WITHOUT trusting anyone's word, and WITHOUT the brittle root equality
    ///     that broke on overshoot).
    pub fn true_outcome(&self, receipt: &CustodyReceipt) -> CustodyOutcome {
        if self.delivered_of(receipt) {
            CustodyOutcome::Delivered { root: self.root }
        } else if self.refund_recorded {
            CustodyOutcome::Refunded
        } else {
            CustodyOutcome::Dropped
        }
    }
}

/// **`adjudicate_from_inbox`** — the REALIZABLE adjudicator the dispute path runs: it
/// derives the true outcome from the inbox's authenticated state and feeds it to
/// [`EvidenceOfDrop::adjudicate`]. No disputant claim is consulted. Returns `slash`
/// (`true`) IFF the dispute is well-formed AND the authenticated root fell short of the
/// promise AND no refund was recorded. Mirrors `adjudicateFromInbox` and is governed by
/// the `conviction_iff_root_short` keystone. This is the function `POST /relay/dispute`
/// evaluates against the inbox cell's root.
pub fn adjudicate_from_inbox(evidence: &EvidenceOfDrop, inbox: &InboxState) -> bool {
    let true_outcome = inbox.true_outcome(&evidence.receipt);
    evidence.adjudicate(true_outcome)
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_types::generate_keypair;

    // A relay identity whose FederationId IS its Ed25519 public key (unified-lace
    // equivalence). We construct a real keypair and use the public key bytes as the id.
    fn relay_identity() -> (FederationId, SigningKey) {
        let (sk, pk) = generate_keypair();
        (FederationId(pk.0), sk)
    }

    fn owner() -> FederationId {
        FederationId([0x03; 32])
    }

    fn h(byte: u8) -> [u8; 32] {
        [byte; 32]
    }

    /// Build the demo receipt of `CustodyReceipt.lean` §7: relay accepts box `0xAB..`,
    /// for the owner, promising the root to advance `old → new` by deadline 500.
    fn demo_receipt() -> (CustodyReceipt, SigningKey) {
        let (relay, sk) = relay_identity();
        let r = CustodyReceipt::sign(
            relay,
            &sk,
            h(0xAB), // content_hash
            owner(),
            h(0x64), // old_root
            h(0x8E), // new_root (the promised transition target)
            500,     // accept_by
        );
        (r, sk)
    }

    /// A DELIVERED inbox built content-address-honestly: the receipt's box `content_hash` is
    /// among the dequeued (delivered) hashes, so [`InboxState::from_dequeue`] sets the witness
    /// bit. `root` is the live head root (may equal `new_root`, or OVERSHOOT it).
    fn delivered_inbox(receipt: &CustodyReceipt, root: [u8; 32]) -> InboxState {
        InboxState::from_dequeue(receipt, &[receipt.content_hash], root, false)
    }

    /// A DROPPED inbox: NO dequeue carried the receipt's box `content_hash` (witness unset),
    /// no refund. `root` short of the promise (or anywhere — the verdict reads the witness).
    fn dropped_inbox(receipt: &CustodyReceipt, root: [u8; 32]) -> InboxState {
        InboxState::from_dequeue(receipt, &[], root, false)
    }

    /// A REFUNDED inbox: box not delivered, but a refund WAS recorded.
    fn refunded_inbox(receipt: &CustodyReceipt, root: [u8; 32]) -> InboxState {
        InboxState::from_dequeue(receipt, &[], root, true)
    }

    // ── §3 KEYSTONE (a): an accepted-and-dropped relay is CONVICTABLE ──────────────

    #[test]
    fn accepted_and_dropped_is_convictable() {
        // Mirrors theorem `accepted_and_dropped_is_convictable`: a relay that signed a
        // valid receipt and DROPPED is convictable by its OWN signature.
        let (r, _sk) = demo_receipt();
        assert!(r.sig_verifies(), "the relay's real signature must verify");

        let evidence = EvidenceOfDrop::from_receipt(r);
        assert!(evidence.well_formed(), "own signature + deadline reached");
        assert!(
            evidence.adjudicate(CustodyOutcome::Dropped),
            "verdict on a true drop must be SLASH"
        );
    }

    // ── §4 KEYSTONE (b): an HONEST relay is NOT slashable (no false conviction) ─────

    #[test]
    fn honest_relay_not_slashable() {
        // Mirrors theorem `honest_relay_not_slashable`: if the relay HONORED the receipt
        // (delivered to the promised root, or refunded), NO claim convicts it — the
        // adjudicator decides on the verified TRUE outcome, not the disputant's claim.
        let (r, _sk) = demo_receipt();
        let new_root = r.new_root;
        let evidence = EvidenceOfDrop::from_receipt(r);

        // Honest delivery to the promised root: acquit even on the disputant's drop-claim.
        let delivered = CustodyOutcome::Delivered { root: new_root };
        assert!(delivered.is_honest_for(&evidence.receipt));
        assert!(
            !evidence.adjudicate(delivered),
            "an honestly-delivered relay must be ACQUITTED"
        );

        // Honest refund: acquit.
        assert!(CustodyOutcome::Refunded.is_honest_for(&evidence.receipt));
        assert!(
            !evidence.adjudicate(CustodyOutcome::Refunded),
            "an honestly-refunded relay must be ACQUITTED"
        );
    }

    #[test]
    fn wrong_root_delivery_is_not_honest() {
        // Mirrors the §7 #guard `outcomeHonest demoReceipt (.delivered 999) == false`:
        // the relay effected a DIFFERENT inbox transition than it signed for ⇒ dishonest.
        let (r, _sk) = demo_receipt();
        let wrong = CustodyOutcome::Delivered { root: h(0xFF) };
        assert!(
            !wrong.is_honest_for(&r),
            "delivery to the wrong root is NOT honest (caught, not excused)"
        );
    }

    // ── §5 non-malleability / binding teeth ────────────────────────────────────────

    #[test]
    fn forged_receipt_no_conviction() {
        // Mirrors `forged_receipt_no_conviction`: a receipt fabricated WITHOUT the relay's
        // key convicts nobody. We forge by signing the preimage with the WRONG key (an
        // attacker who does not hold the relay's secret) — `verify_strict` against the
        // relay's pubkey then fails, so the evidence is not well-formed.
        let (r, _sk) = demo_receipt();
        let (attacker_sk, _attacker_pk) = generate_keypair();
        let bad_sig = sign(&attacker_sk, &r.preimage());
        let forged = CustodyReceipt {
            signature: bad_sig,
            ..r
        };
        assert!(
            !forged.sig_verifies(),
            "a signature by a non-relay key must NOT verify against the relay pubkey"
        );
        let evidence = EvidenceOfDrop::from_receipt(forged);
        assert!(!evidence.well_formed());
        assert!(
            !evidence.adjudicate(CustodyOutcome::Dropped),
            "a forged receipt convicts nobody even on a true drop"
        );
    }

    #[test]
    fn tampered_field_breaks_signature() {
        // Sharper than the Lean Bool model: a relay-signed receipt whose bound field is
        // mutated post-hoc no longer verifies (the preimage covers every field). This is
        // the real-crypto strengthening of the `sig : Bool` carrier.
        let (r, _sk) = demo_receipt();
        assert!(r.sig_verifies());
        // Swap the promised new_root while keeping the original signature.
        let tampered = CustodyReceipt {
            new_root: h(0x99),
            ..r.clone()
        };
        assert!(
            !tampered.sig_verifies(),
            "mutating a bound field must invalidate the relay's signature"
        );
        // Swapping the content_hash likewise.
        let tampered2 = CustodyReceipt {
            content_hash: h(0x11),
            ..r
        };
        assert!(!tampered2.sig_verifies());
    }

    #[test]
    fn premature_dispute_inadmissible() {
        // Mirrors `premature_dispute_inadmissible`: a drop-claim raised BEFORE the deadline
        // (height < accept_by) is inadmissible — the relay has not yet defaulted.
        let (r, _sk) = demo_receipt();
        let accept_by = r.accept_by;
        let early = EvidenceOfDrop {
            receipt: r,
            claimed_outcome: CustodyOutcome::Dropped,
            at_height: accept_by - 1,
        };
        assert!(!early.well_formed(), "a premature dispute is not well-formed");
        assert!(!early.adjudicate(CustodyOutcome::Dropped));
    }

    #[test]
    fn conviction_binds_the_signer() {
        // Mirrors `conviction_binds_the_signer` under the `receiptUnforgeable` seam: a
        // well-formed conviction can only be against the relay that signed. The relay
        // pubkey recovered from a verifying receipt IS the accountable party, and no other
        // identity could have produced a verifying signature (Ed25519 EUF-CMA).
        let (r, _sk) = demo_receipt();
        let evidence = EvidenceOfDrop::from_receipt(r.clone());
        assert!(evidence.well_formed());
        // The signer named in the receipt is exactly the relay whose pubkey verifies it.
        assert_eq!(evidence.receipt.relay.0, evidence.receipt.relay_pubkey().0);
        // A DIFFERENT relay id (different pubkey) on the same signature does not verify —
        // the conviction cannot be re-pointed at an innocent party.
        let (other_id, _other_sk) = relay_identity();
        let mispointed = CustodyReceipt {
            relay: other_id,
            ..r
        };
        assert!(
            !mispointed.sig_verifies(),
            "a receipt cannot be re-pointed at an innocent relay"
        );
    }

    // ── §7.5 the REALIZABLE adjudicator: verdict from the inbox cell, claim inert ───

    #[test]
    fn conviction_from_inbox_when_not_delivered() {
        // Mirrors `conviction_iff_not_delivered` (slash direction) + the §7.5(d) #guard
        // `adjudicateFromInbox (evidenceOfDrop demoReceipt) droppedInbox == true`: the box
        // was NOT delivered (witness unset) and no refund ⇒ the realizable adjudicator
        // SLASHES — established from the cell, NOT the disputant.
        let (r, _sk) = demo_receipt();
        let new_root = r.new_root;
        let evidence = EvidenceOfDrop::from_receipt(r);
        // Dropped inbox: no dequeue carried the box (witness false), root short, no refund.
        let dropped = dropped_inbox(&evidence.receipt, h(0x64));
        assert!(!dropped.delivered_of(&evidence.receipt));
        assert_eq!(
            dropped.true_outcome(&evidence.receipt),
            CustodyOutcome::Dropped
        );
        assert!(
            adjudicate_from_inbox(&evidence, &dropped),
            "a genuine drop (not delivered, no refund) convicts from the cell"
        );
        // Sanity: the promised root differs from the dropped root.
        assert_ne!(new_root, dropped.root);
    }

    #[test]
    fn acquit_from_inbox_when_delivered_or_refunded() {
        // Mirrors `honest_relay_not_slashable_from_inbox` + the §7.5(d) acquit #guards: if
        // the box was delivered (witness set) OR a refund was recorded, the realizable
        // adjudicator ACQUITS for ANY evidence, regardless of the claim.
        let (r, _sk) = demo_receipt();
        let new_root = r.new_root;
        let evidence = EvidenceOfDrop::from_receipt(r);

        // Delivered inbox: the box's content_hash was dequeued (witness set); root at promise.
        let delivered = delivered_inbox(&evidence.receipt, new_root);
        assert!(delivered.delivered_of(&evidence.receipt));
        assert!(matches!(
            delivered.true_outcome(&evidence.receipt),
            CustodyOutcome::Delivered { .. }
        ));
        assert!(
            !adjudicate_from_inbox(&evidence, &delivered),
            "delivery witnessed in the cell ⇒ acquit even on the drop-claim"
        );

        // Refunded inbox: box not delivered, but refund recorded.
        let refunded = refunded_inbox(&evidence.receipt, h(0x64));
        assert_eq!(
            refunded.true_outcome(&evidence.receipt),
            CustodyOutcome::Refunded
        );
        assert!(
            !adjudicate_from_inbox(&evidence, &refunded),
            "a recorded refund ⇒ acquit (accept-or-refund-by half, read off the cell)"
        );
    }

    #[test]
    fn disputant_claim_irrelevant() {
        // Mirrors `disputant_claim_irrelevant`: the verdict does NOT depend on the
        // disputant's claimed_outcome AT ALL — two evidences with the same receipt + height
        // but arbitrarily different claims adjudicate identically against the same inbox.
        let (r, _sk) = demo_receipt();
        let dropped = dropped_inbox(&r, h(0x64));
        let claim_drop = EvidenceOfDrop {
            receipt: r.clone(),
            claimed_outcome: CustodyOutcome::Dropped,
            at_height: 500,
        };
        let claim_delivered = EvidenceOfDrop {
            receipt: r.clone(),
            claimed_outcome: CustodyOutcome::Delivered { root: h(0xFF) },
            at_height: 500,
        };
        let claim_refunded = EvidenceOfDrop {
            receipt: r,
            claimed_outcome: CustodyOutcome::Refunded,
            at_height: 500,
        };
        // All three adjudicate identically against the genuine-drop inbox (all convict).
        let v1 = adjudicate_from_inbox(&claim_drop, &dropped);
        let v2 = adjudicate_from_inbox(&claim_delivered, &dropped);
        let v3 = adjudicate_from_inbox(&claim_refunded, &dropped);
        assert_eq!(v1, v2);
        assert_eq!(v2, v3);
        assert!(v1, "the cell shows a drop ⇒ all convict regardless of the claim");
    }

    #[test]
    fn forged_receipt_acquits_even_against_drop_inbox() {
        // Mirrors the §7.5(d) #guard: a forged receipt convicts nobody even against a
        // genuine-drop inbox (the §5 binding tooth composes with the cell-read adjudicator).
        let (r, _sk) = demo_receipt();
        let (attacker_sk, _pk) = generate_keypair();
        let forged = CustodyReceipt {
            signature: sign(&attacker_sk, &r.preimage()),
            ..r
        };
        let evidence = EvidenceOfDrop::from_receipt(forged);
        let dropped = dropped_inbox(&evidence.receipt, h(0x64));
        assert!(
            !adjudicate_from_inbox(&evidence, &dropped),
            "not well-formed ⇒ acquit regardless of the cell"
        );
    }

    #[test]
    fn full_lifecycle_honest_custody_then_deliver() {
        // End-to-end: an HONEST custody+deliver verifies (the recipient drained, the root
        // reached the promise) — the headline scenario named in the recovered keystone.
        let (relay, relay_sk) = relay_identity();
        let promised_root = h(0x8E);
        // 1. Relay accepts custody and signs a receipt.
        let receipt = CustodyReceipt::sign(
            relay,
            &relay_sk,
            h(0xAB),
            owner(),
            h(0x64),
            promised_root,
            500,
        );
        assert!(receipt.sig_verifies());
        // 2. Recipient comes online; the box is dequeued — the witness bit is set, root at promise.
        let inbox = delivered_inbox(&receipt, promised_root);
        // 3. Even if SOMEONE files a drop dispute, the cell shows delivery ⇒ acquit.
        let dispute = EvidenceOfDrop::from_receipt(receipt);
        assert!(
            !adjudicate_from_inbox(&dispute, &inbox),
            "honest custody+deliver: relay is provably safe"
        );
    }

    #[test]
    fn full_lifecycle_accepted_then_withheld_is_at_fault() {
        // End-to-end: a relay that ACCEPTED-but-WITHHELD is provably at fault — the other
        // headline scenario. The relay signed (it accepted), the deadline passed, the root
        // never reached the promise, no refund ⇒ the cell-read adjudicator convicts.
        let (relay, relay_sk) = relay_identity();
        let promised_root = h(0x8E);
        let receipt = CustodyReceipt::sign(
            relay,
            &relay_sk,
            h(0xAB),
            owner(),
            h(0x64),
            promised_root,
            500,
        );
        // Deadline passed; box never dequeued (the relay withheld), no refund.
        let inbox = dropped_inbox(&receipt, h(0x64));
        let dispute = EvidenceOfDrop::from_receipt(receipt);
        assert!(dispute.well_formed());
        assert!(
            adjudicate_from_inbox(&dispute, &inbox),
            "accepted-then-withheld: the relay is provably at fault"
        );
    }

    // ── §7.5(c) THE OVERSHOOT/REORG TOOTH: the gap this change closes ──────────────

    #[test]
    fn overshoot_does_not_convict_a_delivered_relay() {
        // THE MISSING TEST (the fidelity gap, now a tooth): a relay that DELIVERED and whose
        // inbox root then GREW PAST the promised new_root (a later message / reorg / late
        // block) is NOT convictable. Under the old strict `root == new_root` realization this
        // FALSE-CONVICTED (the live root no longer equals the promise ⇒ read as Dropped); the
        // sticky delivery-witness bit fixes it. Mirrors the Lean `overshoot_acquits` +
        // `#guard adjudicateFromInbox (evidenceOfDrop demoReceipt) overshotInbox == false`.
        let (r, _sk) = demo_receipt();
        let new_root = r.new_root; // h(0x8E)
        let overshot_root = h(0x99); // a DIFFERENT root: later activity advanced past the promise
        assert_ne!(
            overshot_root, new_root,
            "the overshoot root must differ from the promise (that's the whole point)"
        );

        // The box WAS delivered (its content_hash is among the dequeued), but the live root
        // overshot the promise. Built content-address-honestly via from_dequeue.
        let overshot = delivered_inbox(&r, overshot_root);
        assert!(
            overshot.delivered_of(&r),
            "the box was dequeued ⇒ the witness bit holds regardless of the live root"
        );
        // The realizable outcome is Delivered (to the live, overshot root), NOT Dropped.
        assert!(matches!(
            overshot.true_outcome(&r),
            CustodyOutcome::Delivered { .. }
        ));

        let evidence = EvidenceOfDrop::from_receipt(r);
        assert!(
            evidence.well_formed(),
            "the dispute is well-formed (own signature + deadline) — so only the cell saves the relay"
        );
        assert!(
            !adjudicate_from_inbox(&evidence, &overshot),
            "OVERSHOOT MUST ACQUIT: a delivered relay is not convicted when the root grew past the promise"
        );

        // The CONTRAST that pins the bug being fixed: the OLD strict-equality predicate
        // (root == new_root) would have read this overshoot inbox as NOT delivered (and hence
        // convicted), because the live root no longer equals the promise. The witness bit does
        // not — this asserts the precise divergence the fix removes.
        assert_ne!(
            overshot.root, new_root,
            "bare equality FAILS on overshoot (root != new_root)…"
        );
        assert!(
            !adjudicate_from_inbox(&evidence, &overshot),
            "…yet the witness-bit adjudicator ACQUITS — the false conviction is gone"
        );
    }

    #[test]
    fn overshoot_still_convicts_a_genuine_drop() {
        // THE DUAL POLARITY (so the fix is not vacuously always-acquit): if the root grew by
        // UNRELATED activity but THIS box was never delivered (witness unset) and no refund,
        // the relay is STILL convicted. Overshoot robustness must not become a drop loophole.
        // Mirrors the Lean `drop_conviction_survives_root_growth`.
        let (r, _sk) = demo_receipt();
        let grown_unrelated_root = h(0x99); // root advanced — but NOT by delivering this box
        // No dequeue carried THIS box's content_hash ⇒ witness unset; no refund.
        let still_dropped = dropped_inbox(&r, grown_unrelated_root);
        assert!(
            !still_dropped.delivered_of(&r),
            "unrelated root growth does NOT witness THIS box's delivery"
        );
        assert_eq!(
            still_dropped.true_outcome(&r),
            CustodyOutcome::Dropped,
            "not delivered + no refund ⇒ Dropped, even though the root moved"
        );
        let evidence = EvidenceOfDrop::from_receipt(r);
        assert!(
            adjudicate_from_inbox(&evidence, &still_dropped),
            "a genuine drop stays convictable even as the root grows (no escape via unrelated activity)"
        );
    }

    #[test]
    fn from_dequeue_witness_is_content_addressed() {
        // The witness bit is keyed on the BOX's content_hash, order-free: a dequeue of a
        // DIFFERENT box does not witness THIS receipt's delivery (no cross-box false acquit),
        // while a dequeue carrying this box's hash does — regardless of the live root.
        let (r, _sk) = demo_receipt();
        let other_box = h(0x77); // some other box that was delivered

        // Only the other box was dequeued ⇒ THIS receipt's witness is unset ⇒ convictable.
        let not_ours = InboxState::from_dequeue(&r, &[other_box], h(0x12), false);
        assert!(!not_ours.delivered_of(&r));
        let evidence = EvidenceOfDrop::from_receipt(r.clone());
        assert!(
            adjudicate_from_inbox(&evidence, &not_ours),
            "another box's delivery must NOT acquit this relay (content-addressed witness)"
        );

        // Our box AND others were dequeued ⇒ witness set ⇒ acquitted, root irrelevant.
        let ours_among_many =
            InboxState::from_dequeue(&r, &[other_box, r.content_hash, h(0x55)], h(0x12), false);
        assert!(ours_among_many.delivered_of(&r));
        assert!(
            !adjudicate_from_inbox(&evidence, &ours_among_many),
            "this box's delivery (anywhere in the dequeued set) acquits, regardless of the live root"
        );
    }
}
