//! Strand admission — the HYBRID (stake-OR-vouch) Sybil-admission gate (closes red-team F-4).
//!
//! # The finding (F-4)
//!
//! A strand is just a keypair (`captp/src/lib.rs::StrandId = [u8; 32]`): minting a fresh strand
//! costs nothing, so an adversary can spin up unlimited free strands and flood the lace. Plain
//! Secure-Scuttlebutt leans on the human follow-graph for admission; dregg needs a real admission
//! gate or a Sybil swarm can saturate the federation.
//!
//! # The mechanism (HYBRID stake-OR-vouch)
//!
//! A strand is *admitted* to the federation — its blocks may anchor finality and it may
//! participate — iff EITHER
//!
//!   (a) **VOUCH path**: it is vouched-for by ≥ `vouch_threshold` DISTINCT already-admitted members
//!       (a web-of-trust / follow-graph attestation; the threshold is a federation parameter), OR
//!   (b) **STAKE path**: it is backed by a slashable BOND of value ≥ `min_bond` (value bonded in the
//!       in-kernel asset model, slashable on equivocation / misbehavior).
//!
//! Social path for the trusted, economic path for newcomers. Genesis `seeds` are the bootstrap
//! trust root (admitted by construction), exactly as the constitution's initial participant set.
//!
//! This is the faithful Rust mirror of the verified Lean model
//! `Dregg2.Distributed.StrandAdmission` (`metatheory/Dregg2/Distributed/StrandAdmission.lean`):
//! `admitted = is_seed ∨ vouched_to_threshold ∨ has_valid_bond`, with the vouch graph ROOTED (only
//! seeds + bonded strands' vouches count, so a ring of fresh Sybils cannot bootstrap itself in),
//! and a slash-on-equivocation path that burns the whole bond.
//!
//! # This is NOT the constitution
//!
//! [`crate::epoch`] / the blocklace constitution model the self-amending *participant set* +
//! supermajority threshold — governance over an ALREADY-recognized member set. F-4 is the layer
//! BELOW: WHICH keypairs are even eligible to be participants. This module is the NEW gate IN FRONT;
//! the participant set is then drawn from the admitted strands.

use std::collections::BTreeSet;

use dregg_types::{PublicKey, Signature};

/// A strand identity: an Ed25519 public key (`captp::StrandId` / `blocklace::NodeKey` = `[u8; 32]`,
/// here carried as the typed [`PublicKey`] so we can verify attestation signatures against it).
pub type StrandId = PublicKey;

/// Domain separator for a vouch attestation signature (the §8 crypto binding made real).
const VOUCH_DOMAIN: &[u8] = b"dregg-strand-vouch-v1";
/// Domain separator for a bond-posting signature.
const BOND_DOMAIN: &[u8] = b"dregg-strand-bond-v1";

// =============================================================================
// Vouch
// =============================================================================

/// A vouch: voucher `voucher` attests (web-of-trust / follow-graph edge) for candidate strand
/// `candidate`. The `signature` is the voucher's Ed25519 signature over the canonical vouch message
/// — so a vouch cannot be forged in the voucher's name. A vouch counts toward admission only if the
/// voucher is itself ADMITTED (rooted: a seed or bonded) AND the signature verifies.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Vouch {
    /// The vouching member (must be admitted/rooted for the vouch to count).
    pub voucher: StrandId,
    /// The candidate strand being vouched for.
    pub candidate: StrandId,
    /// The voucher's Ed25519 signature over [`Vouch::signing_message`].
    pub signature: Signature,
}

impl Vouch {
    /// The canonical message a voucher signs: domain ‖ voucher ‖ candidate.
    pub fn signing_message(voucher: &StrandId, candidate: &StrandId) -> Vec<u8> {
        let mut m = Vec::with_capacity(VOUCH_DOMAIN.len() + 64);
        m.extend_from_slice(VOUCH_DOMAIN);
        m.extend_from_slice(voucher.as_bytes());
        m.extend_from_slice(candidate.as_bytes());
        m
    }

    /// Build a signed vouch from the voucher's signing key.
    pub fn create(voucher_sk: &dregg_types::SigningKey, candidate: StrandId) -> Self {
        let voucher = voucher_sk.public_key();
        let msg = Self::signing_message(&voucher, &candidate);
        let signature = dregg_types::sign(voucher_sk, &msg);
        Self {
            voucher,
            candidate,
            signature,
        }
    }

    /// Verify the voucher's signature on this vouch (the §8 crypto binding, made real with
    /// `ed25519-dalek`). A vouch whose signature does not verify is not a valid attestation.
    pub fn verify_sig(&self) -> bool {
        let msg = Self::signing_message(&self.voucher, &self.candidate);
        self.voucher.verify(&msg, &self.signature)
    }
}

// =============================================================================
// Bond
// =============================================================================

/// A slashable bond: strand `owner` has posted `amount` value units (in the in-kernel asset model)
/// as a slashable stake. The `signature` binds the bond to the owner. Slashable on equivocation: a
/// fork proof burns the whole bond (see [`AdmissionRegistry::slash`]).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Bond {
    /// The strand that posted the stake.
    pub owner: StrandId,
    /// The bonded value (slashable). Admits via the stake path iff `amount >= min_bond`.
    pub amount: u64,
    /// The owner's Ed25519 signature over [`Bond::signing_message`].
    pub signature: Signature,
}

impl Bond {
    /// The canonical message a bond owner signs: domain ‖ owner ‖ amount (LE).
    pub fn signing_message(owner: &StrandId, amount: u64) -> Vec<u8> {
        let mut m = Vec::with_capacity(BOND_DOMAIN.len() + 40);
        m.extend_from_slice(BOND_DOMAIN);
        m.extend_from_slice(owner.as_bytes());
        m.extend_from_slice(&amount.to_le_bytes());
        m
    }

    /// Post a signed bond from the owner's signing key.
    pub fn post(owner_sk: &dregg_types::SigningKey, amount: u64) -> Self {
        let owner = owner_sk.public_key();
        let msg = Self::signing_message(&owner, amount);
        let signature = dregg_types::sign(owner_sk, &msg);
        Self {
            owner,
            amount,
            signature,
        }
    }

    /// Verify the owner's signature on this bond.
    pub fn verify_sig(&self) -> bool {
        let msg = Self::signing_message(&self.owner, self.amount);
        self.owner.verify(&msg, &self.signature)
    }
}

// =============================================================================
// Equivocation evidence (the slash trigger)
// =============================================================================

/// Evidence that a strand equivocated: two distinct blocks at the same `(creator, sequence)`. This
/// is value-faithful to `blocklace::EquivocationProof` (read-only; we do not depend on the blocklace
/// crate, and must not edit it) and to the Lean `Authority.Blocklace.Equivocation` proof object —
/// the fork witness is its own warrant to slash, no vote required.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EquivocationEvidence {
    /// The equivocating strand.
    pub creator: StrandId,
    /// The sequence number at which the fork occurred.
    pub sequence: u64,
    /// The block already present at `(creator, sequence)`.
    pub existing: [u8; 32],
    /// The conflicting block presented at the same `(creator, sequence)`.
    pub conflicting: [u8; 32],
}

impl EquivocationEvidence {
    /// A well-formed equivocation names the SAME creator at the SAME sequence with two DISTINCT
    /// block ids — the attributable, detectable fork. A malformed "proof" (same block id, or no
    /// fork) is not grounds to slash.
    pub fn is_valid(&self) -> bool {
        self.existing != self.conflicting
    }
}

// =============================================================================
// AdmissionRegistry — the gate
// =============================================================================

/// The federation's admission registry + parameters: the hybrid stake-OR-vouch Sybil gate.
///
/// Mirrors the Lean `AdmissionState`: `seeds` (bootstrap trust root), `vouch_threshold` (= Lean
/// `N`), `min_bond` (= Lean `minBond`), the vouch attestations and posted bonds.
#[derive(Clone, Debug, Default)]
pub struct AdmissionRegistry {
    /// Genesis / bootstrap members, admitted by construction (the trust root the vouch graph roots
    /// from). Stored as a set for O(log n) membership.
    seeds: BTreeSet<[u8; 32]>,
    /// The VOUCH threshold: a candidate needs ≥ this many distinct admitted-member vouches.
    vouch_threshold: usize,
    /// The STAKE floor: a bond of ≥ this many value units admits via the stake path.
    min_bond: u64,
    /// The follow-graph vouch attestations.
    vouches: Vec<Vouch>,
    /// The posted slashable bonds.
    bonds: Vec<Bond>,
}

impl AdmissionRegistry {
    /// A fresh registry with the given seeds, vouch threshold, and bond floor.
    pub fn new(
        seeds: impl IntoIterator<Item = StrandId>,
        vouch_threshold: usize,
        min_bond: u64,
    ) -> Self {
        Self {
            seeds: seeds.into_iter().map(|s| *s.as_bytes()).collect(),
            vouch_threshold,
            min_bond,
            vouches: Vec::new(),
            bonds: Vec::new(),
        }
    }

    /// The vouch threshold parameter (= Lean `N`).
    pub fn vouch_threshold(&self) -> usize {
        self.vouch_threshold
    }

    /// The minimum slashable bond parameter (= Lean `minBond`).
    pub fn min_bond(&self) -> u64 {
        self.min_bond
    }

    /// Register a vouch (rejected silently if its signature does not verify — only authentic
    /// attestations enter the graph).
    pub fn add_vouch(&mut self, vouch: Vouch) -> bool {
        if !vouch.verify_sig() {
            return false;
        }
        self.vouches.push(vouch);
        true
    }

    /// Post a bond (rejected silently if its signature does not verify).
    pub fn add_bond(&mut self, bond: Bond) -> bool {
        if !bond.verify_sig() {
            return false;
        }
        self.bonds.push(bond);
        true
    }

    /// `is_seed strand` — `strand` is a bootstrap member, admitted by construction.
    pub fn is_seed(&self, strand: &StrandId) -> bool {
        self.seeds.contains(strand.as_bytes())
    }

    /// `has_valid_bond strand` — the STAKE path: `strand` posted a bond of value ≥ `min_bond`.
    pub fn has_valid_bond(&self, strand: &StrandId) -> bool {
        self.bonds
            .iter()
            .any(|b| &b.owner == strand && b.amount >= self.min_bond)
    }

    /// `is_root strand` — admitted WITHOUT needing a vouch (seed or bonded). The vouch graph roots
    /// from this set; only rooted members' vouches count, so a ring of fresh Sybils cannot
    /// bootstrap itself into admission.
    pub fn is_root(&self, strand: &StrandId) -> bool {
        self.is_seed(strand) || self.has_valid_bond(strand)
    }

    /// `bond_amount strand` — the maximum bond `strand` has posted (`0` if unbonded). The slashable
    /// amount.
    pub fn bond_amount(&self, strand: &StrandId) -> u64 {
        self.bonds
            .iter()
            .filter(|b| &b.owner == strand)
            .map(|b| b.amount)
            .max()
            .unwrap_or(0)
    }

    /// The DISTINCT set of vouchers attesting for `candidate` whose own admission is ROOTED (seed or
    /// bonded) AND whose signature verifies. The root gate is the anti-Sybil tooth; the dedup means
    /// one voucher cannot be double-counted (mirrors Lean `distinctVouchersFor`).
    pub fn distinct_vouchers_for(&self, candidate: &StrandId) -> Vec<StrandId> {
        let mut seen: BTreeSet<[u8; 32]> = BTreeSet::new();
        let mut out = Vec::new();
        for v in &self.vouches {
            if &v.candidate == candidate && self.is_root(&v.voucher) && v.verify_sig() {
                if seen.insert(*v.voucher.as_bytes()) {
                    out.push(v.voucher);
                }
            }
        }
        out
    }

    /// `vouched_by strand` — how many distinct rooted-admitted members vouch for `strand`.
    pub fn vouched_by(&self, strand: &StrandId) -> usize {
        self.distinct_vouchers_for(strand).len()
    }

    /// `vouched_to_threshold strand` — the VOUCH path fires: ≥ `vouch_threshold` distinct rooted
    /// vouches.
    pub fn vouched_to_threshold(&self, strand: &StrandId) -> bool {
        self.vouched_by(strand) >= self.vouch_threshold
    }

    /// The PURE-RUST hybrid admission gate — the DIFFERENTIAL SIBLING of the verified Lean rule.
    ///
    /// `admitted = is_seed ∨ vouched_to_threshold ∨ has_valid_bond` — the exact Lean
    /// `StrandAdmission.admitted`. This is `dreggrs`'s Rust heritage gate: it is kept as the
    /// differential reference (Lean == Rust on the same registry) and as the fallback when the Lean
    /// archive is not linked. [`Self::admitted`] prefers the VERIFIED Lean export when available.
    pub fn admitted_rust(&self, strand: &StrandId) -> bool {
        self.is_seed(strand) || self.vouched_to_threshold(strand) || self.has_valid_bond(strand)
    }

    /// **THE HYBRID ADMISSION GATE (F-4).** A strand is admitted iff it is a seed, OR it is bonded
    /// (stake path), OR it is vouched to threshold by rooted members (vouch path).
    ///
    /// When built with `--features lean-admission` AND the Lean archive exports `dregg_strand_admit`,
    /// this routes the verdict through the VERIFIED Lean rule
    /// `Dregg2.Distributed.StrandAdmission.admitted` (the `dregg_strand_admit` export): the F-4 gate
    /// the federation runs IS the verified gate, carried by the Lean theorem `strand_admit_eq_admitted`
    /// (the export's `"1"`/`"0"` is definitionally the verified `admitted`). When the archive is
    /// absent (marshal-only / wasm build) it FAILS BACK to the pure-Rust [`Self::admitted_rust`] — so
    /// the gate is never broken, only un-verified. The Rust path remains the differential sibling.
    pub fn admitted(&self, strand: &StrandId) -> bool {
        #[cfg(feature = "lean-admission")]
        {
            if let Some(verdict) = self.lean_admitted(strand) {
                return verdict;
            }
            // archive missing the export ⇒ fall through to the Rust gate (never break the live path).
        }
        self.admitted_rust(strand)
    }

    /// Query the VERIFIED Lean strand-admission gate for `strand`. Interns the registry's `[u8;32]`
    /// pubkeys to the small `AuthorId` indices the Lean wire uses (the same interning discipline the
    /// finality gate applies), builds the wire `StrandAdmission.encodeAdmitWire` mirrors, calls the
    /// `dregg_strand_admit` export, and decodes the `"1"`/`"0"` verdict. Returns `None` when the
    /// archive lacks the export (so [`Self::admitted`] falls back to the Rust gate); a malformed wire
    /// (`ERR`) decodes fail-closed to `Some(false)` — the verified rule's "not admitted".
    #[cfg(feature = "lean-admission")]
    fn lean_admitted(&self, strand: &StrandId) -> Option<bool> {
        if !dregg_lean_ffi::strand_admit_available() {
            return None;
        }
        // Intern every pubkey that appears (seeds, vouchers, candidates, bond owners, the query) to a
        // stable, injective small index — the abstract `AuthorId` the Lean rule reasons over.
        let mut ids: std::collections::HashMap<[u8; 32], u64> = std::collections::HashMap::new();
        let intern = |pk: &[u8; 32], ids: &mut std::collections::HashMap<[u8; 32], u64>| -> u64 {
            let next = ids.len() as u64;
            *ids.entry(*pk).or_insert(next)
        };
        // Seeds first (deterministic order), then vouchers/candidates, then bond owners, then query —
        // the exact set the wire carries; interning is by first appearance, injective by construction.
        let seeds: Vec<u64> = self.seeds.iter().map(|s| intern(s, &mut ids)).collect();
        let vouches: Vec<(u64, u64)> = self
            .vouches
            .iter()
            .filter(|v| v.verify_sig())
            .map(|v| {
                let vc = intern(v.voucher.as_bytes(), &mut ids);
                let cn = intern(v.candidate.as_bytes(), &mut ids);
                (vc, cn)
            })
            .collect();
        let bonds: Vec<(u64, u64)> = self
            .bonds
            .iter()
            .filter(|b| b.verify_sig())
            .map(|b| {
                let ow = intern(b.owner.as_bytes(), &mut ids);
                (ow, b.amount)
            })
            .collect();
        let q = intern(strand.as_bytes(), &mut ids);

        let join_pairs = |ps: &[(u64, u64)]| -> String {
            ps.iter()
                .map(|(a, b)| format!("{a}:{b}"))
                .collect::<Vec<_>>()
                .join(",")
        };
        let wire = format!(
            "N={n};m={m};S={s};V={v};Bo={bo};q={q}",
            n = self.vouch_threshold,
            m = self.min_bond,
            s = seeds
                .iter()
                .map(|i| i.to_string())
                .collect::<Vec<_>>()
                .join(","),
            v = join_pairs(&vouches),
            bo = join_pairs(&bonds),
            q = q,
        );

        match dregg_lean_ffi::verified_admits(&wire) {
            Ok(b) => Some(b), // the verified verdict (ERR ⇒ fail-closed false inside verified_admits).
            Err(_) => None,   // archive lacks the export ⇒ fall back to the Rust gate.
        }
    }

    /// **SLASH** `strand`'s bond on a valid equivocation proof: remove all of its bonds (burning the
    /// staked value) and return the amount burned. The fork proof is the only authorization (no
    /// vote — the equivocation is its own warrant, exactly `MembershipSafety.autoEvict`'s
    /// discipline). Returns `None` if the evidence is malformed (no real fork).
    ///
    /// After a slash the strand no longer has a valid bond, so its stake-path admission is revoked;
    /// a slashed newcomer with no seed/vouch standing falls out of admission entirely (the hybrid
    /// gate is an OR — slashing kills only the path the bond bought).
    pub fn slash(&mut self, evidence: &EquivocationEvidence) -> Option<u64> {
        if !evidence.is_valid() {
            return None;
        }
        let strand = &evidence.creator;
        let burned = self.bond_amount(strand);
        self.bonds.retain(|b| &b.owner != strand);
        Some(burned)
    }

    /// Draw the admitted participant set from a candidate strand list — the gate IN FRONT of the
    /// constitution / finality: only admitted strands are eligible to participate. The node passes
    /// THIS set (not the raw keypair list) to `ordering::tau`, so an unadmitted Sybil's blocks
    /// cannot anchor finality (mirrors the Lean `finalLeaderAtAdmitted` gate on
    /// `BlocklaceFinality.finalLeaderAt`).
    pub fn admitted_participants(&self, candidates: &[StrandId]) -> Vec<StrandId> {
        candidates
            .iter()
            .copied()
            .filter(|s| self.admitted(s))
            .collect()
    }

    /// Is `strand` eligible to have its blocks finalized? The finalization-side restatement of the
    /// gate: an unadmitted strand is finality-inert.
    pub fn is_finalizable(&self, strand: &StrandId) -> bool {
        self.admitted(strand)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_types::generate_keypair;

    /// A small fixture: seeds {a, b}, vouch threshold 2, min bond 100.
    fn fixture() -> (
        AdmissionRegistry,
        dregg_types::SigningKey,
        PublicKey,
        dregg_types::SigningKey,
        PublicKey,
    ) {
        let (sk_a, a) = generate_keypair();
        let (sk_b, b) = generate_keypair();
        let reg = AdmissionRegistry::new([a, b], 2, 100);
        (reg, sk_a, a, sk_b, b)
    }

    #[test]
    fn seeds_are_admitted() {
        let (reg, _, a, _, b) = fixture();
        assert!(reg.admitted(&a));
        assert!(reg.admitted(&b));
        assert!(reg.is_finalizable(&a));
    }

    #[test]
    fn fresh_sybil_is_rejected() {
        // F-4: a fresh keypair with no vouch and no bond is NOT admitted.
        let (reg, _, _, _, _) = fixture();
        let (_, sybil) = generate_keypair();
        assert!(!reg.admitted(&sybil));
        assert!(!reg.is_finalizable(&sybil));
    }

    #[test]
    fn vouch_path_admits_at_threshold_not_below() {
        let (mut reg, sk_a, _a, sk_b, _b) = fixture();
        let (_, cand) = generate_keypair();
        // one seed vouch: below threshold (need 2) ⇒ still rejected.
        assert!(reg.add_vouch(Vouch::create(&sk_a, cand)));
        assert_eq!(reg.vouched_by(&cand), 1);
        assert!(!reg.admitted(&cand));
        // second distinct seed vouch ⇒ reaches threshold ⇒ admitted.
        assert!(reg.add_vouch(Vouch::create(&sk_b, cand)));
        assert_eq!(reg.vouched_by(&cand), 2);
        assert!(reg.admitted(&cand));
    }

    #[test]
    fn duplicate_voucher_counts_once() {
        let (mut reg, sk_a, _a, _, _) = fixture();
        let (_, cand) = generate_keypair();
        // same seed vouches twice ⇒ deduped to one distinct voucher (no double-count to threshold).
        assert!(reg.add_vouch(Vouch::create(&sk_a, cand)));
        assert!(reg.add_vouch(Vouch::create(&sk_a, cand)));
        assert_eq!(reg.vouched_by(&cand), 1);
        assert!(!reg.admitted(&cand));
    }

    #[test]
    fn ring_of_unrooted_sybils_cannot_bootstrap() {
        // THE RING ATTACK: a clutch of fresh Sybils vouch for each other. None is rooted (no seed,
        // no bond), so none of their vouches count — the ring cannot bootstrap itself into
        // admission.
        let (mut reg, _, _, _, _) = fixture();
        let (sk_s1, s1) = generate_keypair();
        let (sk_s2, s2) = generate_keypair();
        let (_, victim) = generate_keypair();
        // s1, s2 each vouch for `victim` (and for each other) — but s1, s2 are not rooted.
        reg.add_vouch(Vouch::create(&sk_s1, victim));
        reg.add_vouch(Vouch::create(&sk_s2, victim));
        reg.add_vouch(Vouch::create(&sk_s1, s2));
        reg.add_vouch(Vouch::create(&sk_s2, s1));
        assert_eq!(
            reg.vouched_by(&victim),
            0,
            "unrooted vouchers must not count"
        );
        assert!(!reg.admitted(&victim));
        assert!(!reg.admitted(&s1));
        assert!(!reg.admitted(&s2));
    }

    #[test]
    fn stake_path_admits_at_floor_not_below() {
        let (mut reg, _, _, _, _) = fixture();
        let (sk_new, newcomer) = generate_keypair();
        // a 50-unit bond is below the 100 floor ⇒ not admitted.
        assert!(reg.add_bond(Bond::post(&sk_new, 50)));
        assert!(!reg.has_valid_bond(&newcomer));
        assert!(!reg.admitted(&newcomer));
        // a 100-unit bond clears the floor ⇒ admitted via the stake path (no social standing needed).
        assert!(reg.add_bond(Bond::post(&sk_new, 100)));
        assert!(reg.has_valid_bond(&newcomer));
        assert!(reg.admitted(&newcomer));
    }

    #[test]
    fn bonded_equivocator_is_slashed_and_loses_admission() {
        let (mut reg, _, _, _, _) = fixture();
        let (sk_new, newcomer) = generate_keypair();
        reg.add_bond(Bond::post(&sk_new, 250));
        assert!(reg.admitted(&newcomer));
        assert_eq!(reg.bond_amount(&newcomer), 250);
        // a valid equivocation proof ⇒ the WHOLE bond is burned, admission revoked.
        let ev = EquivocationEvidence {
            creator: newcomer,
            sequence: 7,
            existing: [1u8; 32],
            conflicting: [2u8; 32],
        };
        let burned = reg.slash(&ev).expect("valid equivocation slashes");
        assert_eq!(burned, 250, "slash burns the whole bond");
        assert!(!reg.has_valid_bond(&newcomer));
        assert!(
            !reg.admitted(&newcomer),
            "slashed newcomer falls out of admission"
        );
    }

    #[test]
    fn malformed_equivocation_does_not_slash() {
        let (mut reg, _, _, _, _) = fixture();
        let (sk_new, newcomer) = generate_keypair();
        reg.add_bond(Bond::post(&sk_new, 100));
        // same block id for existing and conflicting ⇒ no real fork ⇒ no slash.
        let bogus = EquivocationEvidence {
            creator: newcomer,
            sequence: 3,
            existing: [9u8; 32],
            conflicting: [9u8; 32],
        };
        assert!(reg.slash(&bogus).is_none());
        assert!(
            reg.admitted(&newcomer),
            "an unproven fork must not slash a member"
        );
    }

    #[test]
    fn forged_vouch_signature_is_rejected() {
        // The §8 crypto binding made real: a vouch whose signature was made by the WRONG key (i.e.
        // an attacker forging a seed's vouch for itself) does not verify and is rejected.
        let (mut reg, _sk_a, a, _, _) = fixture();
        let (sk_attacker, _attacker) = generate_keypair();
        let (_, candidate) = generate_keypair();
        // attacker signs a vouch but CLAIMS it is from seed `a`.
        let msg = Vouch::signing_message(&a, &candidate);
        let forged = Vouch {
            voucher: a,
            candidate,
            signature: dregg_types::sign(&sk_attacker, &msg),
        };
        assert!(!forged.verify_sig(), "a forged vouch must not verify");
        assert!(!reg.add_vouch(forged), "a forged vouch must be rejected");
        assert_eq!(reg.vouched_by(&candidate), 0);
        assert!(!reg.admitted(&candidate));
    }

    #[test]
    fn forged_bond_signature_is_rejected() {
        let (mut reg, _, _, _, _) = fixture();
        let (sk_attacker, _) = generate_keypair();
        let (_, victim) = generate_keypair();
        // attacker posts a bond in the victim's name — signature is the attacker's, so it fails.
        let msg = Bond::signing_message(&victim, 1000);
        let forged = Bond {
            owner: victim,
            amount: 1000,
            signature: dregg_types::sign(&sk_attacker, &msg),
        };
        assert!(!forged.verify_sig());
        assert!(!reg.add_bond(forged));
        assert!(!reg.has_valid_bond(&victim));
    }

    /// THE F-4 CLOSURE DIFFERENTIAL: a Sybil strand cannot get its blocks finalized.
    ///
    /// `admitted_participants` is the set the node hands to `ordering::tau`. A Sybil is filtered
    /// OUT, so it never appears as a participant / leader candidate — its blocks reach no finality.
    /// A vouched strand and a bonded strand ARE admitted; a bonded equivocator is slashed out.
    #[test]
    fn f4_sybil_not_finalizable_differential() {
        let (mut reg, sk_a, a, sk_b, b) = fixture();
        // a vouched newcomer (2 seed vouches), a bonded newcomer, a fresh Sybil, a bonded equivocator.
        let (_, vouched) = generate_keypair();
        reg.add_vouch(Vouch::create(&sk_a, vouched));
        reg.add_vouch(Vouch::create(&sk_b, vouched));
        let (sk_bonded, bonded) = generate_keypair();
        reg.add_bond(Bond::post(&sk_bonded, 100));
        let (_, sybil) = generate_keypair();
        let (sk_equiv, equiv) = generate_keypair();
        reg.add_bond(Bond::post(&sk_equiv, 100));

        let candidates = vec![a, b, vouched, bonded, sybil, equiv];
        let admitted = reg.admitted_participants(&candidates);

        // seeds + vouched + bonded + equiv (still bonded) are admitted; the Sybil is NOT.
        assert!(admitted.contains(&a) && admitted.contains(&b));
        assert!(admitted.contains(&vouched), "vouched strand admitted");
        assert!(admitted.contains(&bonded), "bonded strand admitted");
        assert!(admitted.contains(&equiv));
        assert!(
            !admitted.contains(&sybil),
            "F-4: the Sybil strand is NOT admitted/finalizable"
        );
        assert!(!reg.is_finalizable(&sybil));

        // now the equivocator forks — it is slashed and drops out of the admitted participant set.
        let ev = EquivocationEvidence {
            creator: equiv,
            sequence: 1,
            existing: [3u8; 32],
            conflicting: [4u8; 32],
        };
        assert_eq!(reg.slash(&ev), Some(100));
        let admitted_after = reg.admitted_participants(&candidates);
        assert!(
            !admitted_after.contains(&equiv),
            "a slashed bonded equivocator drops out of the finalizable set"
        );
        // and the Sybil is STILL not finalizable — the gate holds.
        assert!(!admitted_after.contains(&sybil));
    }

    /// Golden-vector cross-check against the Lean `fedDemo` model: same parameters (N = 2,
    /// minBond = 100), same admit/reject verdicts on the same strand roles. This is the
    /// model⟺crate differential for the admission gate (the Lean `#guard`s on `fedDemo` assert the
    /// matching verdicts).
    #[test]
    fn lean_feddemo_differential() {
        // seeds {s1, s2}, N = 2, minBond = 100 (= Lean `fedDemo`).
        let (sk_s1, s1) = generate_keypair();
        let (sk_s2, s2) = generate_keypair();
        let mut reg = AdmissionRegistry::new([s1, s2], 2, 100);
        let (_, three) = generate_keypair(); // Lean strand 3: vouched by both seeds.
        let (sk_four, four) = generate_keypair(); // strand 4: bonded at floor.
        let (sk_five, five) = generate_keypair(); // strand 5: bonded below floor.
        let (_, six) = generate_keypair(); // strand 6: fresh Sybil.
        reg.add_vouch(Vouch::create(&sk_s1, three));
        reg.add_vouch(Vouch::create(&sk_s2, three));
        reg.add_bond(Bond::post(&sk_four, 100));
        reg.add_bond(Bond::post(&sk_five, 50));

        // Lean `#guard admitted fedDemo k`: 1,2,3,4 admitted; 5,6 rejected.
        assert!(reg.admitted(&s1)); // fedDemo 1
        assert!(reg.admitted(&s2)); // fedDemo 2
        assert_eq!(reg.vouched_by(&three), 2);
        assert!(reg.admitted(&three)); // fedDemo 3
        assert!(reg.admitted(&four)); // fedDemo 4
        assert!(!reg.admitted(&five)); // fedDemo 5 (below floor)
        assert!(!reg.admitted(&six)); // fedDemo 6 (Sybil)
        // slash on strand 4 burns 100 (= Lean `(slash fedDemo 4).2 == 100`).
        let ev = EquivocationEvidence {
            creator: four,
            sequence: 0,
            existing: [1u8; 32],
            conflicting: [2u8; 32],
        };
        assert_eq!(reg.slash(&ev), Some(100));
        assert!(!reg.admitted(&four)); // = Lean `admitted (slash fedDemo 4).1 4 == false`
    }

    /// THE LIVE F-4 LEAN-BACKED GATE DIFFERENTIAL — when the verified Lean archive is linked
    /// (`--features lean-admission` + the `dregg_strand_admit` export present), the Lean-backed
    /// `admitted` AGREES with the pure-Rust `admitted_rust` on every strand role of the `fedDemo`
    /// fixture. This is the runtime proof that routing the gate through the verified rule is
    /// transparent for the modelled cases — `admitted` IS `admitted_rust` IS the verified Lean
    /// `StrandAdmission.admitted`. Self-skips when the archive lacks the export (then `admitted`
    /// already falls back to `admitted_rust`, so they are trivially equal).
    #[cfg(feature = "lean-admission")]
    #[test]
    fn lean_backed_gate_agrees_with_rust_gate() {
        let (sk_s1, s1) = generate_keypair();
        let (sk_s2, s2) = generate_keypair();
        let mut reg = AdmissionRegistry::new([s1, s2], 2, 100);
        let (_, three) = generate_keypair(); // vouched by both seeds
        let (sk_four, four) = generate_keypair(); // bonded at floor
        let (sk_five, five) = generate_keypair(); // bonded below floor
        let (_, six) = generate_keypair(); // fresh Sybil
        reg.add_vouch(Vouch::create(&sk_s1, three));
        reg.add_vouch(Vouch::create(&sk_s2, three));
        reg.add_bond(Bond::post(&sk_four, 100));
        reg.add_bond(Bond::post(&sk_five, 50));

        if !dregg_lean_ffi::strand_admit_available() {
            eprintln!("SKIP: Lean strand-admit export not linked — admitted() == admitted_rust()");
        }
        for s in [&s1, &s2, &three, &four, &five, &six] {
            assert_eq!(
                reg.admitted(s),
                reg.admitted_rust(s),
                "Lean-backed admitted() must agree with the Rust differential sibling"
            );
        }
        // And the verdicts are the F-4 expected ones (= Lean `fedDemo`).
        assert!(reg.admitted(&s1) && reg.admitted(&s2));
        assert!(reg.admitted(&three) && reg.admitted(&four));
        assert!(!reg.admitted(&five) && !reg.admitted(&six));
    }
}
