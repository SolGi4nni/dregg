//! The adjudication court — ORGANS §5 composed (CONSENSUS-FLEX §7 items 1–2).
//!
//! # The court rule: WITNESS-FIRST
//!
//! Where either party can exhibit a verifying witness, **the exhibit decides**
//! — no tribunal, no vote, no jury (the Lawvere adjudication result ORGANS §5
//! cites). Equivocation IS certifiable: the wire value
//! [`dregg_blocklace::evidence::EvidenceOfEquivocation`] carries two signed
//! conflicting headers and verifies with two Ed25519 checks and three
//! equalities. This module supplies the two missing welds in dependency order:
//!
//! 1. **The predicate atom** ([`EquivocationEvidenceVerifier`], CONSENSUS-FLEX
//!    §7 item 2): a `Custom { vk_hash }` [`WitnessedPredicateVerifier`] — the
//!    `witnessed(vk)`-style atom — so a turn can carry the exhibit in its
//!    `witness_blobs` and any cell program / authorization / precondition can
//!    gate on `validEquivocation(ev, strandKey)`. Fail-closed on malformed
//!    evidence.
//! 2. **The slash pipe** ([`EquivocationCourt`]): verified evidence drives
//!    [`AdmissionRegistry::slash`] with the obligation-factory discipline —
//!    no-double-resolve (an order-insensitive evidence digest is BURNED on
//!    resolution, the trustline draw-digest pattern), and a refusal changes
//!    no state. Executing the slash as an ordinary conserved MOVE from the
//!    bonded cell is the node-side half (`node/src/equivocation_court_service.rs`),
//!    which calls down into this court for the registry + digest legs.
//!
//! Jury selection exists ONLY for the non-certifiable residue: equivocation
//! never reaches a jury. [`seed_council`] is the one call site demonstrating
//! the randomness organ ([`crate::beacon::select_jury`]) seeds a council
//! selection deterministically; the full tribunal flow is a later organ wave.

use std::collections::BTreeSet;
use std::sync::Arc;

use dregg_blocklace::evidence::EvidenceOfEquivocation;
use dregg_cell::predicate::{
    PredicateInput, WitnessedPredicateError, WitnessedPredicateKind, WitnessedPredicateRegistry,
    WitnessedPredicateVerifier, canonical_predicate_vk,
};

use crate::admission::{AdmissionRegistry, EquivocationEvidence, StrandId};

// =============================================================================
// The predicate atom (CONSENSUS-FLEX §7 item 2)
// =============================================================================

/// The canonical "program bytes" the court atom's vk_hash commits to — the
/// VK-as-re-execution-recipe discipline (`cell/src/predicate.rs`): the name +
/// version of the verification rule. Re-key this string iff the rule or the
/// evidence codec changes.
pub const EQUIVOCATION_PREDICATE_PROGRAM: &[u8] =
    b"dregg-court:valid-equivocation:blocklace-evidence-v1";

/// The `Custom { vk_hash }` key the court atom registers under.
pub fn equivocation_predicate_vk() -> [u8; 32] {
    canonical_predicate_vk(EQUIVOCATION_PREDICATE_PROGRAM)
}

/// **The verification Pred atom** — `validEquivocation(ev, strandKey)`.
///
/// Dispatch shape (the `WitnessedPredicateRegistry` machinery the executor
/// already runs, `turn/src/executor/execute_tree.rs`):
///
/// * `commitment` = the ACCUSED strand key (32 bytes) — the predicate is
///   "this is a valid equivocation BY this strand", so a bond cell's program
///   can pin the commitment to its owner's key at birth.
/// * `proof_bytes` = the wire-encoded [`EvidenceOfEquivocation`] (rides the
///   action's `witness_blobs` at the declared `proof_witness_index`).
/// * `input` = the 32-byte order-insensitive evidence DIGEST (via
///   `InputRef::Witness` or a slot) — binds the turn to THIS exhibit, which
///   is also the no-double-resolve burn key.
///
/// Fail-closed: malformed bytes, forged/invalid signatures, slot or content
/// mismatches, a creator other than the committed strand, and a digest other
/// than the exhibit's all REJECT.
pub struct EquivocationEvidenceVerifier;

impl WitnessedPredicateVerifier for EquivocationEvidenceVerifier {
    fn name(&self) -> &'static str {
        "valid-equivocation"
    }

    fn kind(&self) -> WitnessedPredicateKind {
        WitnessedPredicateKind::Custom {
            vk_hash: equivocation_predicate_vk(),
        }
    }

    fn verify(
        &self,
        commitment: &[u8; 32],
        input: &PredicateInput<'_>,
        proof_bytes: &[u8],
    ) -> Result<(), WitnessedPredicateError> {
        let reject = |reason: String| WitnessedPredicateError::Rejected {
            kind_name: "valid-equivocation",
            reason,
        };
        let ev = EvidenceOfEquivocation::from_bytes(proof_bytes)
            .ok_or_else(|| reject("malformed evidence bytes".into()))?;
        // The cryptographic core: both signatures valid, same author, same
        // slot, conflicting content.
        ev.verify().map_err(|e| reject(e.to_string()))?;
        // The accusation must name the committed strand.
        if &ev.creator != commitment {
            return Err(reject(
                "evidence does not accuse the committed strand key".into(),
            ));
        }
        // The input binds the turn to THIS exhibit (its burn digest).
        let bound: [u8; 32] = match input {
            PredicateInput::Slot(s) => **s,
            PredicateInput::Bytes(b) => (*b)
                .try_into()
                .map_err(|_| reject("evidence-digest input must be exactly 32 bytes".into()))?,
            other => {
                return Err(WitnessedPredicateError::InputShapeMismatch {
                    kind_name: "valid-equivocation",
                    expected: "Slot or Bytes (the 32-byte evidence digest)",
                    actual: match other {
                        PredicateInput::PublicInput(_) => "PublicInput",
                        PredicateInput::Sender(_) => "Sender",
                        PredicateInput::SigningMessage(_) => "SigningMessage",
                        _ => "unexpected",
                    },
                });
            }
        };
        if bound != ev.digest() {
            return Err(reject(
                "input digest does not match the exhibited evidence".into(),
            ));
        }
        Ok(())
    }
}

/// Install the court atom into a [`WitnessedPredicateRegistry`] under its
/// canonical vk_hash. Hosts call this where they build the executor registry.
pub fn register_equivocation_court(registry: &mut WitnessedPredicateRegistry) {
    registry.register_custom(
        equivocation_predicate_vk(),
        Arc::new(EquivocationEvidenceVerifier),
    );
}

// =============================================================================
// The court (evidence → slash, no-double-resolve)
// =============================================================================

/// A successful witness-first resolution.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CourtVerdict {
    /// The slashed strand.
    pub strand: StrandId,
    /// The burned evidence digest (the no-double-resolve key).
    pub digest: [u8; 32],
    /// The bond value the registry slash burned.
    pub burned: u64,
}

/// Every way the court refuses to act. A refusal changes NO state.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CourtRefusal {
    /// The exhibit does not verify (malformed / forged / not a same-slot
    /// conflicting pair). Detail carries the evidence error.
    BadEvidence(String),
    /// This evidence digest was already resolved — the same fork must not
    /// slash twice (re-submission in either block order refuses here).
    AlreadyResolved,
    /// The accused strand holds no bond in the registry — nothing at stake.
    /// NOT burned: evidence never expires, so a bond posted later by an
    /// exposed equivocator is still slashable by the same exhibit.
    NothingAtStake,
}

impl std::fmt::Display for CourtRefusal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CourtRefusal::BadEvidence(d) => write!(f, "exhibit does not verify: {d}"),
            CourtRefusal::AlreadyResolved => {
                write!(f, "evidence digest already resolved (no-double-resolve)")
            }
            CourtRefusal::NothingAtStake => write!(f, "accused strand holds no bond"),
        }
    }
}

/// The witness-first equivocation court: verified exhibits drive the
/// admission registry's slash exactly once each.
#[derive(Clone, Debug, Default)]
pub struct EquivocationCourt {
    /// Burned evidence digests (resolved forks). The forever anti-replay
    /// set, exactly the trustline draw-digest registry's shape.
    resolved: BTreeSet<[u8; 32]>,
}

impl EquivocationCourt {
    /// A fresh court with nothing resolved.
    pub fn new() -> Self {
        Self::default()
    }

    /// WITNESS-FIRST step 1: decode + cryptographically verify an exhibit.
    /// Pure — no state read or written. Fail-closed on malformed bytes.
    pub fn verify_exhibit(bytes: &[u8]) -> Result<EvidenceOfEquivocation, CourtRefusal> {
        let ev = EvidenceOfEquivocation::from_bytes(bytes)
            .ok_or_else(|| CourtRefusal::BadEvidence("malformed evidence bytes".into()))?;
        ev.verify()
            .map_err(|e| CourtRefusal::BadEvidence(e.to_string()))?;
        Ok(ev)
    }

    /// Whether this evidence digest has already been resolved.
    pub fn is_resolved(&self, digest: &[u8; 32]) -> bool {
        self.resolved.contains(digest)
    }

    /// WITNESS-FIRST step 2: the exhibit decides — slash the accused
    /// strand's bond in `registry` and burn the evidence digest.
    ///
    /// Re-verifies the exhibit (fail-closed even if the caller skipped
    /// [`Self::verify_exhibit`]); refuses double-resolution and unbonded
    /// strands. The digest burns ONLY on a successful slash, so a refusal
    /// leaves court + registry exactly as they were.
    pub fn resolve(
        &mut self,
        registry: &mut AdmissionRegistry,
        ev: &EvidenceOfEquivocation,
    ) -> Result<CourtVerdict, CourtRefusal> {
        ev.verify()
            .map_err(|e| CourtRefusal::BadEvidence(e.to_string()))?;
        let digest = ev.digest();
        if self.is_resolved(&digest) {
            return Err(CourtRefusal::AlreadyResolved);
        }
        let strand = dregg_types::PublicKey(ev.creator);
        if registry.bond_amount(&strand) == 0 {
            return Err(CourtRefusal::NothingAtStake);
        }
        let (id_a, id_b) = ev.block_ids();
        let admission_ev = EquivocationEvidence {
            creator: strand,
            sequence: ev.header_a.seq,
            existing: id_a.0,
            conflicting: id_b.0,
        };
        let burned = registry
            .slash(&admission_ev)
            // unreachable given ev.verify() (distinct content ⇒ distinct ids),
            // but the court never assumes — refuse, burn nothing.
            .ok_or_else(|| CourtRefusal::BadEvidence("registry refused the fork proof".into()))?;
        self.resolved.insert(digest);
        Ok(CourtVerdict {
            strand,
            digest,
            burned,
        })
    }

    /// One-shot convenience: verify wire bytes and resolve.
    pub fn adjudicate(
        &mut self,
        registry: &mut AdmissionRegistry,
        evidence_bytes: &[u8],
    ) -> Result<CourtVerdict, CourtRefusal> {
        let ev = Self::verify_exhibit(evidence_bytes)?;
        self.resolve(registry, &ev)
    }
}

// =============================================================================
// Jury seeding (the non-certifiable residue ONLY)
// =============================================================================

/// Seed a council selection from a beacon output — the ONE call site wiring
/// the randomness organ ([`crate::beacon::select_jury`]) to adjudication.
///
/// `randomness` is a verified beacon output (`crate::beacon::beacon_at`);
/// `pool` is the candidate-juror strand list; `council_size` the seats.
/// Deterministic given the beacon output (every node derives the SAME
/// council); `None` iff `council_size > pool.len()`.
///
/// COURT RULE (ORGANS §5): this exists for the NON-certifiable residue.
/// Equivocation is certifiable, so it is decided by the exhibit
/// ([`EquivocationCourt`]) and NEVER reaches a council.
pub fn seed_council(
    randomness: &[u8; 32],
    pool: &[StrandId],
    council_size: usize,
) -> Option<Vec<StrandId>> {
    let indices = crate::beacon::select_jury(randomness, pool.len(), council_size)?;
    Some(indices.into_iter().map(|i| pool[i]).collect())
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::admission::Bond;
    use dregg_blocklace::finality::{Block, Payload};
    use dregg_cell::predicate::{InputRef, WitnessedPredicate};
    use ed25519_dalek::SigningKey;

    /// A signing key whose pubkey doubles as the strand id, plus the matching
    /// `dregg_types::SigningKey` for posting bonds (the admission registry
    /// signs bonds with the typed key; the blocklace signs blocks with the
    /// dalek key — SAME seed, same Ed25519 keypair, same public key).
    fn strand(seed: u8) -> (SigningKey, dregg_types::SigningKey, StrandId) {
        let dalek = SigningKey::from_bytes(&[seed; 32]);
        let typed = dregg_types::SigningKey::from_bytes(&[seed; 32]);
        let pk = typed.public_key();
        assert_eq!(
            pk.as_bytes(),
            &dalek.verifying_key().to_bytes(),
            "the two key types must agree on the public key"
        );
        (dalek, typed, pk)
    }

    fn fork_evidence(dalek: &SigningKey, seq: u64) -> EvidenceOfEquivocation {
        let a = Block::new(dalek, seq, Payload::Data(b"story A".to_vec()), vec![]);
        let b = Block::new(dalek, seq, Payload::Data(b"story B".to_vec()), vec![]);
        EvidenceOfEquivocation::from_blocks(&a, &b).expect("real fork certifies")
    }

    /// Registry with one bonded strand (bond 250 ≥ min_bond 100) and no seeds.
    fn bonded_registry(typed: &dregg_types::SigningKey) -> AdmissionRegistry {
        let mut reg = AdmissionRegistry::new([], 2, 100);
        assert!(reg.add_bond(Bond::post(typed, 250)));
        reg
    }

    #[test]
    fn valid_evidence_slashes_exactly_once() {
        let (dalek, typed, pk) = strand(41);
        let mut reg = bonded_registry(&typed);
        assert!(reg.admitted(&pk), "bonded strand starts admitted");
        let ev = fork_evidence(&dalek, 7);
        let mut court = EquivocationCourt::new();

        // The exhibit decides: slash fires, whole bond burns, admission falls.
        let verdict = court
            .adjudicate(&mut reg, &ev.to_bytes())
            .expect("valid evidence slashes");
        assert_eq!(verdict.burned, 250, "the WHOLE bond burns");
        assert_eq!(verdict.strand, pk);
        assert!(!reg.admitted(&pk), "slashed strand loses admission");
        assert!(court.is_resolved(&verdict.digest));

        // Re-submission refuses (no-double-resolve) and changes nothing.
        assert_eq!(
            court.adjudicate(&mut reg, &ev.to_bytes()),
            Err(CourtRefusal::AlreadyResolved)
        );
        // … in EITHER block order (the digest is order-insensitive).
        let flipped = EvidenceOfEquivocation {
            creator: ev.creator,
            hybrid_id: ev.hybrid_id,
            header_a: ev.header_b.clone(),
            header_b: ev.header_a.clone(),
        };
        assert_eq!(
            court.adjudicate(&mut reg, &flipped.to_bytes()),
            Err(CourtRefusal::AlreadyResolved),
            "the same fork re-presented in flipped order must not resolve again"
        );
    }

    #[test]
    fn forged_evidence_refuses_with_no_state_change() {
        let (dalek, typed, pk) = strand(43);
        let mut reg = bonded_registry(&typed);
        let mut court = EquivocationCourt::new();

        // Forge: a different key signs "the strand's" second header.
        let attacker = SigningKey::from_bytes(&[99u8; 32]);
        let a = Block::new(&dalek, 3, Payload::Data(b"x".to_vec()), vec![]);
        let mut b = Block::new(&attacker, 3, Payload::Data(b"y".to_vec()), vec![]);
        b.creator = a.creator; // claim the victim authored it; sig won't verify.
        let forged = EvidenceOfEquivocation {
            creator: a.ed25519,
            hybrid_id: a.creator,
            header_a: dregg_blocklace::evidence::EvidenceHeader::from_block(&a),
            header_b: dregg_blocklace::evidence::EvidenceHeader::from_block(&b),
        };
        let refusal = court.adjudicate(&mut reg, &forged.to_bytes());
        assert!(
            matches!(refusal, Err(CourtRefusal::BadEvidence(_))),
            "forged exhibit refuses: {refusal:?}"
        );
        assert_eq!(reg.bond_amount(&pk), 250, "bond untouched");
        assert!(reg.admitted(&pk), "admission untouched");
        assert!(!court.is_resolved(&forged.digest()), "nothing burned");
    }

    #[test]
    fn same_payload_and_different_positions_refuse() {
        let (dalek, typed, pk) = strand(47);
        let mut reg = bonded_registry(&typed);
        let mut court = EquivocationCourt::new();

        // Same payload (identical content, re-presented): not a fork.
        let a = Block::new(&dalek, 5, Payload::Data(b"same".to_vec()), vec![]);
        let same = EvidenceOfEquivocation {
            creator: a.ed25519,
            hybrid_id: a.creator,
            header_a: dregg_blocklace::evidence::EvidenceHeader::from_block(&a),
            header_b: dregg_blocklace::evidence::EvidenceHeader::from_block(&a.clone()),
        };
        assert!(matches!(
            court.adjudicate(&mut reg, &same.to_bytes()),
            Err(CourtRefusal::BadEvidence(_))
        ));

        // Different positions: plain chain extension, not same-slot-certifiable.
        let p1 = Block::new(&dalek, 1, Payload::Data(b"x".to_vec()), vec![]);
        let p2 = Block::new(&dalek, 2, Payload::Data(b"y".to_vec()), vec![]);
        let diff = EvidenceOfEquivocation {
            creator: p1.ed25519,
            hybrid_id: p1.creator,
            header_a: dregg_blocklace::evidence::EvidenceHeader::from_block(&p1),
            header_b: dregg_blocklace::evidence::EvidenceHeader::from_block(&p2),
        };
        assert!(matches!(
            court.adjudicate(&mut reg, &diff.to_bytes()),
            Err(CourtRefusal::BadEvidence(_))
        ));

        // Malformed bytes fail decode, fail-closed.
        assert!(matches!(
            court.adjudicate(&mut reg, b"garbage"),
            Err(CourtRefusal::BadEvidence(_))
        ));

        assert_eq!(reg.bond_amount(&pk), 250, "no refusal touched the bond");
        assert!(reg.admitted(&pk));
    }

    #[test]
    fn unbonded_strand_is_nothing_at_stake_and_slashable_later() {
        let (dalek, typed, pk) = strand(53);
        let mut reg = AdmissionRegistry::new([], 2, 100); // no bond posted
        let mut court = EquivocationCourt::new();
        let ev = fork_evidence(&dalek, 1);

        assert_eq!(
            court.adjudicate(&mut reg, &ev.to_bytes()),
            Err(CourtRefusal::NothingAtStake)
        );
        assert!(!court.is_resolved(&ev.digest()), "refusal burns nothing");

        // Evidence never expires: bond posted later, same exhibit slashes.
        assert!(reg.add_bond(Bond::post(&typed, 100)));
        let verdict = court.adjudicate(&mut reg, &ev.to_bytes()).unwrap();
        assert_eq!(verdict.burned, 100);
        assert!(!reg.admitted(&pk));
    }

    /// THE PREDICATE ATOM through the real registry machinery: a
    /// `WitnessedPredicate::custom` keyed on the court vk dispatches to the
    /// verifier; accept and every reject leg behave.
    #[test]
    fn predicate_atom_dispatches_through_witnessed_registry() {
        let (dalek, _typed, _pk) = strand(59);
        let ev = fork_evidence(&dalek, 9);
        let evidence_bytes = ev.to_bytes();
        let digest = ev.digest();

        let mut registry = WitnessedPredicateRegistry::empty();
        register_equivocation_court(&mut registry);

        let wp = WitnessedPredicate::custom(
            equivocation_predicate_vk(),
            ev.creator,                     // commitment = the accused strand
            InputRef::Witness { index: 0 }, // input = the evidence digest
            1,                              // proof = the evidence bytes
        );

        // ACCEPT: right commitment, right digest, real evidence.
        registry
            .verify(&wp, &PredicateInput::Bytes(&digest), &evidence_bytes)
            .expect("valid exhibit accepted");

        // REJECT: digest not matching the exhibit.
        let wrong_digest = [0xABu8; 32];
        assert!(
            registry
                .verify(&wp, &PredicateInput::Bytes(&wrong_digest), &evidence_bytes)
                .is_err()
        );

        // REJECT: commitment naming a different strand.
        let other = WitnessedPredicate::custom(
            equivocation_predicate_vk(),
            [0x11u8; 32],
            InputRef::Witness { index: 0 },
            1,
        );
        assert!(
            registry
                .verify(&other, &PredicateInput::Bytes(&digest), &evidence_bytes)
                .is_err()
        );

        // REJECT: garbage proof bytes (fail-closed on malformed evidence).
        assert!(
            registry
                .verify(&wp, &PredicateInput::Bytes(&digest), b"garbage")
                .is_err()
        );

        // REJECT: wrong input shape.
        assert!(matches!(
            registry.verify(&wp, &PredicateInput::PublicInput(&[1, 2]), &evidence_bytes),
            Err(WitnessedPredicateError::InputShapeMismatch { .. })
        ));
    }

    /// The jury-seed call site is deterministic given a beacon output and
    /// draws distinct members.
    #[test]
    fn council_seed_is_deterministic_given_beacon_output() {
        let pool: Vec<StrandId> = (0u8..7)
            .map(|i| dregg_types::SigningKey::from_bytes(&[i + 1; 32]).public_key())
            .collect();
        let randomness = *blake3::hash(b"beacon output, epoch 3 height 9").as_bytes();

        let council_1 = seed_council(&randomness, &pool, 3).expect("3 of 7 selects");
        let council_2 = seed_council(&randomness, &pool, 3).expect("replay selects");
        assert_eq!(council_1, council_2, "same beacon output ⇒ same council");
        assert_eq!(council_1.len(), 3);
        let distinct: std::collections::BTreeSet<_> =
            council_1.iter().map(|p| *p.as_bytes()).collect();
        assert_eq!(distinct.len(), 3, "council members are distinct");

        // A different beacon output draws a different council (w.h.p. for
        // this fixed fixture — pinned, not probabilistic, by these inputs).
        let other = *blake3::hash(b"beacon output, epoch 3 height 10").as_bytes();
        assert_ne!(seed_council(&other, &pool, 3).unwrap(), council_1);

        // Refuses an over-large council.
        assert!(seed_council(&randomness, &pool, 8).is_none());
    }
}
