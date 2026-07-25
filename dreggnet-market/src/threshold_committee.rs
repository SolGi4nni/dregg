//! ONE n-of-n threshold committee, shared by every market that needs one.
//!
//! [`oracle_pit`](crate::oracle_pit) and [`dark_pool_offering`](crate::dark_pool_offering) each
//! grew their own near-identical wrapper around the frozen [`fhegg_fhe::threshold`] primitives
//! (`KeygenSession` → `ThresholdParty` ×n → `KeygenCoordinator::finish` → `RelinKeySession` →
//! `generate_relinearization_key`). This module is the single object; the two callers differ only
//! in the parameters named on [`CommitteeCeremony`].
//!
//! # What this type does and does not give you
//!
//! It gives you: an `n`-of-`n` BFV collective public key whose secret exists nowhere as a whole,
//! a full-quorum opening path that runs every party's `partial_decrypt` at the Lean-pinned
//! smudging floor and feeds them to the real [`combine`], and the multiparty relinearization key
//! the wrap-guarded `ct×ct` multiply needs.
//!
//! It does NOT give you a distributed deployment. Every [`ThresholdParty`] here lives in this
//! process. What survives that co-location is the *reconstruction* property — `combine` needs
//! every party's mask and nothing short of the real set reproduces the plaintext (see
//! [`ThresholdCommittee::combine_shares`] for the exact strength of each refusal). What does NOT
//! survive it is any claim about transport, availability, or an adversary with process memory:
//! one process holding all `n` shares is one compromise away from all of them, whatever the
//! combiner does.
//!
//! # The two refusals a caller must not conflate
//!
//! [`combine`] refuses a SHORT share set on a roster/arity check — that is *structural*, and it
//! says nothing about what `n-1` custodians could compute. The *cryptographic* content is that a
//! FULL-arity set containing a share the coalition forged (structurally well-formed to the
//! combiner) still does not reconstruct the plaintext, because the reconstruction only cancels
//! the key when every real mask is present. Both are exercised below, under names that say which
//! is which, and neither is described in the other's words.

use std::sync::OnceLock;
use std::time::Duration;

use fhe::bfv::{Ciphertext, Encoding, Plaintext, RelinearizationKey};
use fhe_traits::{FheEncoder, FheEncrypter, Serialize as FheSerialize};
use fhegg_fhe::bfv_lean::LeanCiphertext;
use fhegg_fhe::bfv_mul::{BoundedCiphertext, MulEngine};
use fhegg_fhe::threshold::relin::{RelinKeySession, generate_relinearization_key_verified};
use fhegg_fhe::threshold::{
    BfvParams, CollectivePublicKey, DecryptShare, KeygenCoordinator, KeygenSession,
    MIN_SMUDGE_BITS, ThresholdParty, combine,
};

/// The smallest roster that can carry a no-single-viewer claim at all.
///
/// Both callers used to enforce this in their own outer constructor while their `ceremony`
/// happily stood up a 1-of-1 "committee" — a key one party holds outright. The guard lives on the
/// ceremony now, so it cannot be bypassed by a new caller that forgets it.
pub const MIN_COMMITTEE_PARTIES: usize = 2;

/// Why a committee could not be stood up, or could not open something.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CommitteeError {
    /// The roster is too small to have a no-single-viewer property, or a party index / custody
    /// root was refused.
    Roster(String),
    /// Collective key generation failed.
    Keygen(String),
    /// The multiparty relinearization ceremony failed.
    Relin(String),
    /// The relinearization key was produced but the wrap-guarded multiply engine refused it.
    MulEngine(String),
    /// A plaintext could not be encoded, or a value could not be encrypted to the collective key.
    Encoding(String),
    /// A partial decryption or the n-of-n combine failed.
    Opening(String),
}

impl std::fmt::Display for CommitteeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Roster(why) => write!(f, "the committee roster was refused: {why}"),
            Self::Keygen(why) => write!(f, "the n-of-n key ceremony failed: {why}"),
            Self::Relin(why) => write!(f, "the relinearization ceremony failed: {why}"),
            Self::MulEngine(why) => write!(f, "the multiply engine refused the relin key: {why}"),
            Self::Encoding(why) => write!(f, "a plaintext could not be encoded: {why}"),
            Self::Opening(why) => write!(f, "the threshold opening failed: {why}"),
        }
    }
}

impl std::error::Error for CommitteeError {}

/// Where each party's secret share comes from.
///
/// This is the one parameter with real security content, and the two callers genuinely want
/// different values — so it is named, not defaulted.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PartySeeding {
    /// Every party samples its own share from OS randomness ([`ThresholdParty::join`]), and the
    /// public CRP seed is OS-random too.
    ///
    /// Nothing reconstructs a share afterwards — not even the caller. Pick this when the
    /// committee is born fresh with the market it serves and nobody needs to replay it.
    OsRandom,
    /// Every party's share is derived from ONE 32-byte `root` ([`ThresholdParty::join_seeded`]),
    /// so the whole committee is reproducible for audit.
    ///
    /// **Say this out loud when you pick it:** deriving all `n` custody roots from one value
    /// inside one process is a *shared dealer*, which is exactly what `join_seeded`'s own doc
    /// tells a deployment not to do. Whoever knows `root` holds every share and can decrypt
    /// unilaterally — the n-of-n property of such a committee is worth exactly the secrecy of
    /// `root` and no more. It buys reproducibility, and it costs the threshold property against
    /// anyone who learns the root.
    ///
    /// `crp_domain` and `party_domain` are blake3 derive-key domains, so two different markets
    /// standing up on the same `root` still get unrelated key material.
    FromRoot {
        /// The single 32-byte value the entire committee is derived from. An all-zero root is
        /// refused (`join_seeded` refuses it too; refusing here names the misconfiguration
        /// before `n` party joins have run).
        root: [u8; 32],
        /// blake3 derive-key domain for the public CRP seed.
        crp_domain: &'static str,
        /// blake3 derive-key domain for each party's custody root.
        party_domain: &'static str,
    },
}

/// When the multiparty relinearization ceremony is paid for.
///
/// It is the same ceremony and the same key either way — [`ThresholdCommittee`] caches it — so
/// this names only WHICH call blocks, never what comes out.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RelinSchedule {
    /// Run it inside [`CommitteeCeremony::run`]. Pick this when the caller needs
    /// `&RelinearizationKey` immediately (a pool that encrypts its genesis reserves under a
    /// multiply-capable house) and when the cost belongs to a genesis event either way.
    AtGenesis,
    /// Run it the first time [`ThresholdCommittee::relin_key`] or
    /// [`ThresholdCommittee::mul_engine`] is called, then cache it. Pick this when the linear
    /// path (quotes, positions) needs no relin key at all and a committee that never reaches a
    /// `ct×ct` multiply should never pay for one.
    OnFirstUse,
}

/// The full parameter set of one committee ceremony. Every field is something the two market
/// callers genuinely disagree about; nothing here is a knob invented for symmetry.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CommitteeCeremony {
    /// Roster size. This is an n-of-n key: `n_parties` is both the roster and the quorum.
    pub n_parties: usize,
    /// Where the secret shares come from — read [`PartySeeding`] before choosing.
    pub seeding: PartySeeding,
    /// Public entropy for the relinearization CRP. PUBLIC by construction: `RelinKeySession`
    /// domain-separates it and binds it to the keygen session AND the collective public key
    /// before expansion, so a constant here still yields a per-committee CRP.
    pub relin_entropy: [u8; 32],
    /// The relinearization ceremony's liveness deadline. Not a security parameter: a party that
    /// misses it fails the ceremony, it does not weaken the key.
    pub relin_timeout: Duration,
    /// When to pay for the relinearization ceremony.
    pub relin_schedule: RelinSchedule,
}

impl CommitteeCeremony {
    /// Run the ceremony: the public keygen session, every party's join, the aggregated collective
    /// key, and — under [`RelinSchedule::AtGenesis`] — the multiparty relinearization key.
    pub fn run(self) -> Result<ThresholdCommittee, CommitteeError> {
        if self.n_parties < MIN_COMMITTEE_PARTIES {
            return Err(CommitteeError::Roster(format!(
                "a no-single-viewer committee needs at least {MIN_COMMITTEE_PARTIES} parties, \
                 got {}",
                self.n_parties
            )));
        }
        let params = BfvParams::fold_set();

        let keygen = match &self.seeding {
            PartySeeding::OsRandom => KeygenSession::random(self.n_parties),
            PartySeeding::FromRoot {
                root, crp_domain, ..
            } => {
                if root.iter().all(|byte| *byte == 0) {
                    return Err(CommitteeError::Roster(
                        "an all-zero custody root is a deployment misconfiguration".to_string(),
                    ));
                }
                KeygenSession::from_seed(self.n_parties, blake3::derive_key(crp_domain, root))
            }
        }
        .map_err(|e| CommitteeError::Keygen(format!("{e:?}")))?;

        let mut coordinator = KeygenCoordinator::new(keygen.clone(), params.clone());
        let mut parties = Vec::with_capacity(self.n_parties);
        for index in 0..self.n_parties {
            let (party, contribution) = match &self.seeding {
                PartySeeding::OsRandom => ThresholdParty::join(&keygen, index, &params),
                PartySeeding::FromRoot {
                    root, party_domain, ..
                } => {
                    let mut material = Vec::with_capacity(40);
                    material.extend_from_slice(root);
                    material.extend_from_slice(&(index as u64).to_le_bytes());
                    let party_root = blake3::derive_key(party_domain, &material);
                    ThresholdParty::join_seeded(&keygen, index, &params, &party_root)
                }
            }
            .map_err(|e| CommitteeError::Keygen(format!("{e:?}")))?;
            coordinator
                .accept(contribution)
                .map_err(|e| CommitteeError::Keygen(format!("{e:?}")))?;
            parties.push(party);
        }
        let collective = coordinator
            .finish()
            .map_err(|e| CommitteeError::Keygen(format!("{e:?}")))?;

        // Build 5 Tier-0: the collective key must round-trip (encrypt → full-quorum decrypt) before use —
        // a corrupt key from a malformed party contribution (aggregation checks no c0 well-formedness) is
        // refused fail-closed here, never cached. Detection, not attribution (the per-share ZK proof is
        // the full Build 5). Bounded one-time cost at committee genesis.
        fhegg_fhe::threshold::collective_key_acceptance_gate(&collective, &params, &parties, 4)
            .map_err(|e| {
                CommitteeError::Keygen(format!("collective key acceptance gate: {e:?}"))
            })?;

        let committee = ThresholdCommittee {
            params,
            keygen,
            collective,
            parties,
            relin_entropy: self.relin_entropy,
            relin_timeout: self.relin_timeout,
            relin: OnceLock::new(),
        };
        if self.relin_schedule == RelinSchedule::AtGenesis {
            committee.relin_key()?;
        }
        Ok(committee)
    }
}

/// **AN n-OF-n THRESHOLD COMMITTEE.** `n` parties jointly hold a BFV secret key that exists
/// nowhere as a whole; anything encrypted to [`collective`](Self::collective) opens only when
/// every party contributes a [`DecryptShare`].
///
/// The parties run in one process. Read this module's header for exactly which part of the
/// threshold claim survives that and which part does not.
pub struct ThresholdCommittee {
    params: BfvParams,
    keygen: KeygenSession,
    collective: CollectivePublicKey,
    parties: Vec<ThresholdParty>,
    relin_entropy: [u8; 32],
    relin_timeout: Duration,
    /// Cached because the ceremony is the expensive part and the key is a pure function of
    /// (keygen session, collective key, entropy, roster) — running it twice yields the same key at
    /// several hundred milliseconds a go.
    relin: OnceLock<RelinearizationKey>,
}

impl ThresholdCommittee {
    /// Roster size, which for an n-of-n key is also the quorum: every party must agree to open
    /// anything.
    pub fn n_parties(&self) -> usize {
        self.keygen.n_parties()
    }

    /// The BFV parameter set every share and ciphertext is bound to.
    pub fn params(&self) -> &BfvParams {
        &self.params
    }

    /// The plaintext modulus every wrap guard is checked against.
    pub fn plaintext_modulus(&self) -> u64 {
        self.params.plaintext_modulus()
    }

    /// The collective public key. Encrypting to it needs no secret and no quorum.
    pub fn collective(&self) -> &CollectivePublicKey {
        &self.collective
    }

    /// A short public fingerprint of the collective key everything is encrypted to.
    pub fn collective_key_digest(&self) -> [u8; 32] {
        *blake3::hash(&self.collective.pk.to_bytes()).as_bytes()
    }

    /// The multiparty relinearization key, running the ceremony on first call and caching it.
    ///
    /// Under [`RelinSchedule::AtGenesis`] this is already warm and the call is free.
    pub fn relin_key(&self) -> Result<&RelinearizationKey, CommitteeError> {
        if let Some(relin) = self.relin.get() {
            return Ok(relin);
        }
        let session = RelinKeySession::from_public_entropy(
            &self.keygen,
            &self.collective,
            self.relin_entropy,
            self.relin_timeout,
        )
        .map_err(|e| CommitteeError::Relin(format!("session: {e}")))?;
        // Build 4: the VERIFIED generator runs the mandatory acceptance gate (fresh trial products must
        // decrypt to the exact product under the quorum) before returning — a silently-corrupt relin key
        // (malformed party contribution) is refused fail-closed, never cached.
        let relin = generate_relinearization_key_verified(
            &session,
            &self.params,
            &self.collective,
            &self.parties,
        )
        .map_err(|e| CommitteeError::Relin(e.to_string()))?;
        // A racing caller may have won; either key is the same object, so keep whichever landed.
        let _ = self.relin.set(relin);
        self.relin.get().ok_or_else(|| {
            CommitteeError::Relin("the relin cache did not accept a key".to_string())
        })
    }

    /// The wrap-guarded `ct×ct` multiply engine, over the committee's relinearization key.
    pub fn mul_engine(&self) -> Result<MulEngine, CommitteeError> {
        let relin = self.relin_key()?;
        MulEngine::new(relin, self.params.arc())
            .map_err(|e| CommitteeError::MulEngine(format!("{e:?}")))
    }

    /// Encrypt one value into SIMD slot 0 under the collective key. No secret and no quorum is
    /// involved: anyone holding the public key can do this.
    pub fn encrypt(&self, value: u64) -> Result<Ciphertext, CommitteeError> {
        let pt = self.plaintext(value)?;
        let mut rng = rand_09::rng();
        self.collective
            .pk
            .try_encrypt(&pt, &mut rng)
            .map_err(|e| CommitteeError::Encoding(format!("collective encrypt: {e}")))
    }

    /// A bare SIMD plaintext, for the plaintext-multiply weights the linear paths use.
    pub fn plaintext(&self, value: u64) -> Result<Plaintext, CommitteeError> {
        Plaintext::try_encode(&[value], Encoding::simd(), self.params.arc())
            .map_err(|e| CommitteeError::Encoding(format!("encode: {e}")))
    }

    fn lean(&self, ct: &Ciphertext, plain_bound: u64) -> Result<LeanCiphertext, CommitteeError> {
        LeanCiphertext::from_fhe_bytes(
            &ct.to_bytes(),
            self.params.moduli(),
            self.params.degree(),
            plain_bound,
        )
        .map_err(|e| CommitteeError::Opening(format!("Lean boundary: {e:?}")))
    }

    /// Every custodian's public decryption share for `ct` — the exact wire objects a distributed
    /// deployment broadcasts. Producing them reveals nothing on its own.
    ///
    /// Public because it is what a real deployment ships, and because an adversarial test needs
    /// to be able to hand a short or forged coalition to the real combiner.
    pub fn shares(&self, ct: &BoundedCiphertext) -> Result<Vec<DecryptShare>, CommitteeError> {
        self.shares_of(&ct.ct, ct.plain_bound)
    }

    /// [`shares`](Self::shares) for a raw ciphertext whose plaintext bound the caller tracks
    /// itself.
    pub fn shares_of(
        &self,
        ct: &Ciphertext,
        plain_bound: u64,
    ) -> Result<Vec<DecryptShare>, CommitteeError> {
        let lean = self.lean(ct, plain_bound)?;
        self.parties
            .iter()
            .map(|party| {
                party
                    .partial_decrypt(&lean, MIN_SMUDGE_BITS)
                    .map_err(|e| CommitteeError::Opening(format!("partial decrypt: {e:?}")))
            })
            .collect()
    }

    /// Push a share set through the real n-of-n [`combine`] and return SIMD slot 0.
    ///
    /// TWO DIFFERENT STRENGTHS OF REFUSAL LIVE BEHIND THIS CALL, and a caller that blurs them is
    /// claiming something it has not shown:
    ///
    /// * a SHORT, duplicated, mismatched or under-smudged set is refused by `combine`'s roster,
    ///   parameter and smudge checks. Those are STRUCTURAL — arity and well-formedness. A short
    ///   set being refused is not evidence about what `n-1` custodians could compute, because
    ///   `n-1` custodians would not hand the combiner `n-1` shares; they would fabricate an
    ///   `n`-th;
    /// * a FULL-arity set carrying a fabricated share passes every one of those structural checks
    ///   and still does not reconstruct the plaintext, because the sum of masks only cancels the
    ///   key when each real mask is present. THAT is the cryptographic content, and it is the one
    ///   worth citing.
    pub fn combine_shares(&self, shares: &[DecryptShare]) -> Result<u64, CommitteeError> {
        let slots =
            combine(shares, &self.params).map_err(|e| CommitteeError::Opening(format!("{e:?}")))?;
        slots
            .first()
            .copied()
            .ok_or_else(|| CommitteeError::Opening("combine returned no slots".to_string()))
    }

    /// Open one raw ciphertext under the full quorum (the only kind an n-of-n key has).
    pub fn open(&self, ct: &Ciphertext, plain_bound: u64) -> Result<u64, CommitteeError> {
        let shares = self.shares_of(ct, plain_bound)?;
        self.combine_shares(&shares)
    }

    /// Open one bound-carrying ciphertext under the full quorum.
    pub fn open_bounded(&self, ct: &BoundedCiphertext) -> Result<u64, CommitteeError> {
        self.open(&ct.ct, ct.plain_bound)
    }
}

#[cfg(test)]
mod tests {
    use std::time::Instant;

    use super::*;

    const AUDIT_ROOT: [u8; 32] = [0x5c; 32];

    fn spec(n: usize, seeding: PartySeeding) -> CommitteeCeremony {
        CommitteeCeremony {
            n_parties: n,
            seeding,
            relin_entropy: *b"dreggnet-market-committee-test--",
            relin_timeout: Duration::from_secs(120),
            relin_schedule: RelinSchedule::OnFirstUse,
        }
    }

    fn from_root(n: usize) -> CommitteeCeremony {
        spec(
            n,
            PartySeeding::FromRoot {
                root: AUDIT_ROOT,
                crp_domain: "dregg-committee-test-crp-v1",
                party_domain: "dregg-committee-test-party-v1",
            },
        )
    }

    /// The no-single-viewer floor is a property of the CEREMONY now, not of whichever outer
    /// constructor remembered to check it. A 1-of-1 "committee" is a key one party holds
    /// outright, and both former wrappers would have built one.
    #[test]
    fn a_one_party_committee_is_refused_by_the_ceremony_itself() {
        assert!(matches!(from_root(1).run(), Err(CommitteeError::Roster(_))));
        assert!(matches!(
            spec(0, PartySeeding::OsRandom).run(),
            Err(CommitteeError::Roster(_))
        ));
        assert!(matches!(
            spec(1, PartySeeding::OsRandom).run(),
            Err(CommitteeError::Roster(_))
        ));
    }

    /// An all-zero custody root is a deployment misconfiguration, and it is named before `n`
    /// party joins have run rather than by the `n`-th `join_seeded`.
    #[test]
    fn an_all_zero_custody_root_is_refused_before_any_party_joins() {
        let zeroed = spec(
            2,
            PartySeeding::FromRoot {
                root: [0u8; 32],
                crp_domain: "dregg-committee-test-crp-v1",
                party_domain: "dregg-committee-test-party-v1",
            },
        );
        assert!(matches!(zeroed.run(), Err(CommitteeError::Roster(_))));
    }

    /// STRUCTURAL, and labelled as such: `combine` refuses a short set on its roster/arity check.
    /// This says nothing about what `n-1` custodians could compute — see the test below for that.
    #[test]
    fn a_short_share_set_is_refused_by_the_structural_arity_check() {
        const N: usize = 3;
        let committee = from_root(N).run().expect("ceremony");
        let ct = committee
            .encrypt(1_234)
            .expect("encrypt under the collective key");
        let bounded = BoundedCiphertext::new(ct, 4_096);

        let shares = committee.shares(&bounded).expect("every custodian's share");
        assert_eq!(shares.len(), N);
        assert_eq!(
            committee
                .combine_shares(&shares)
                .expect("full quorum opens"),
            1_234
        );
        assert!(committee.combine_shares(&shares[..N - 1]).is_err());
        assert!(committee.combine_shares(&[]).is_err());
    }

    /// CRYPTOGRAPHIC, and this is the one worth citing: an `n-1` coalition FORGES the missing
    /// custodian's share by re-labelling one of their own. The forgery is structurally
    /// well-formed — it round-trips through `DecryptShare::from_wire_bytes`, carries the right
    /// ciphertext, roster, smudge and parameters, and clears every check the previous test's
    /// refusal came from — and it still does not recover the plaintext.
    #[test]
    fn an_n_minus_one_coalition_forging_the_missing_share_does_not_recover_the_plaintext() {
        const N: usize = 3;
        let committee = from_root(N).run().expect("ceremony");
        let ct = committee
            .encrypt(4_242)
            .expect("encrypt under the collective key");
        let bounded = BoundedCiphertext::new(ct, 8_192);

        let shares = committee.shares(&bounded).expect("every custodian's share");
        let honest = committee
            .combine_shares(&shares)
            .expect("full quorum opens");
        assert_eq!(honest, 4_242);

        // Parties 0 and 1 fabricate party 2's share by re-labelling party 0's. The wire layout is
        // magic(8) then the party index as u64 LE.
        let mut bytes = shares[0].to_wire_bytes();
        bytes[8..16].copy_from_slice(&((N - 1) as u64).to_le_bytes());
        let fake = DecryptShare::from_wire_bytes(&bytes, committee.params())
            .expect("a re-labelled share is structurally well-formed");
        assert_eq!(fake.party(), N - 1, "the forgery claims the missing seat");
        assert_eq!(fake.n_parties(), N);
        assert!(fake.smudge_bits() >= MIN_SMUDGE_BITS);

        let coalition = vec![shares[0].clone(), shares[1].clone(), fake];
        assert_eq!(
            coalition.len(),
            N,
            "the coalition hands the combiner a FULL-arity set, so the arity check cannot be \
             what refuses it"
        );
        // THE COMBINER ACCEPTS THIS SET. That is the point, and it is asserted rather than
        // tolerated: if the forgery were refused, this test would be a second structural check
        // wearing a cryptographic name, and the no-single-viewer claim would rest on arity alone.
        // It is not refused — every structural check passes — and the reconstruction still
        // returns garbage, because the masks only cancel the key when each real one is present.
        let forged = committee.combine_shares(&coalition).expect(
            "the combiner must ACCEPT a full-arity forged set — if it refuses, this test proves \
             nothing beyond the arity check above",
        );
        assert_ne!(
            forged, honest,
            "an n-1 coalition forging the missing share RECOVERED the plaintext — the n-of-n \
             reconstruction is not doing its job"
        );
    }

    /// WHERE THE CEREMONY COST LIVES. The relinearization key is a pure function of the ceremony,
    /// so a second call must hand back the SAME key rather than re-run it. The pit wrapper this
    /// replaced re-ran the entire n-of-n relin ceremony on every `mul_engine()` call; a caller
    /// that reached for the engine twice paid twice for an identical key.
    ///
    /// The margin is deliberately enormous (a cached call under a hundredth of the ceremony) so a
    /// loaded build box cannot flake it. The printed numbers are the actual measurement — this is
    /// the answer to "how much does a committee cost, and on which call".
    #[test]
    fn the_relin_ceremony_runs_once_and_is_cached() {
        for n in [2usize, 3] {
            let start = Instant::now();
            let committee = from_root(n).run().expect("ceremony");
            let keygen = start.elapsed();

            let start = Instant::now();
            let first = committee.relin_key().expect("relin ceremony") as *const RelinearizationKey;
            let relin = start.elapsed();

            let start = Instant::now();
            let second = committee.relin_key().expect("cached relin") as *const RelinearizationKey;
            let cached = start.elapsed();

            println!(
                "{n}-of-{n} committee @ degree {}: keygen {keygen:?} + relin ceremony {relin:?} \
                 = {:?} total; cached relin {cached:?}",
                committee.params().degree(),
                keygen + relin
            );
            assert_eq!(first, second, "the relin key was regenerated, not cached");
            assert!(
                cached * 100 < relin,
                "a second relin_key() cost {cached:?} against a {relin:?} ceremony — the key is \
                 being regenerated per call"
            );
            committee.mul_engine().expect("the multiply engine builds");
        }
    }

    /// A committee seeded from a root is byte-for-byte reproducible; one seeded from OS
    /// randomness is not. Both are real modes and the choice is the caller's.
    #[test]
    fn a_rooted_committee_reproduces_and_an_os_random_one_does_not() {
        let a = from_root(2).run().expect("ceremony");
        let b = from_root(2).run().expect("ceremony");
        assert_eq!(a.collective_key_digest(), b.collective_key_digest());

        let fresh_a = spec(2, PartySeeding::OsRandom).run().expect("ceremony");
        let fresh_b = spec(2, PartySeeding::OsRandom).run().expect("ceremony");
        assert_ne!(
            fresh_a.collective_key_digest(),
            fresh_b.collective_key_digest()
        );

        // And a different domain over the SAME root is a different committee, so two markets
        // cannot collide on one operator's root.
        let other_domain = spec(
            2,
            PartySeeding::FromRoot {
                root: AUDIT_ROOT,
                crp_domain: "dregg-committee-test-crp-v2",
                party_domain: "dregg-committee-test-party-v1",
            },
        )
        .run()
        .expect("ceremony");
        assert_ne!(
            a.collective_key_digest(),
            other_domain.collective_key_digest()
        );
    }
}
