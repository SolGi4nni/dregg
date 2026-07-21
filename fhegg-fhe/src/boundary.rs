//! MASKED DECRYPT-TO-SHARES — the BFV-to-MPC value-channel seam.
//!
//! ## The seam this closes
//!
//! The output-boundary MPC PoC (`crate::mpc`) measured the crossing at
//! milliseconds, but its input step — "the threshold-BFV partial-decrypt-INTO-
//! shares" — was MODELLED by sharing the true decrypted coefficients
//! (`share_int` on cleartext). Between the BFV-encrypted folded curves and the
//! secret-shared MPC crossing there was still one un-built protocol step.
//!
//! ## The construction: mask, THEN decrypt (one-time pad over `Z_t`)
//!
//! A dedicated "partial-decrypt-into-shares" primitive is not needed. Additive
//! homomorphism already gives it, composed from pieces the stack HAS:
//!
//!   1. Each party `i` samples a uniform mask vector `r_i ∈ Z_t^K`, encrypts it,
//!      and homomorphically adds `Enc(r_i)` to the folded curve ciphertext:
//!      `ct' = ct ⊞ Enc(r_0) ⊞ … ⊞ Enc(r_{n-1})` — n more carry-free adds on a
//!      noise budget sized for millions.
//!   2. The selected BFV custodians emit smudged decrypt shares over `ct'`. The
//!      legacy [`ThresholdParty`](crate::threshold::ThresholdParty) path is
//!      n-of-n; [`crate::threshold::quorum::QuorumParty`] provides strict `t < n`
//!      Shamir opening, and its authenticated combiner binds each share to a
//!      configured Ed25519 custody identity. The coordinator combines only the
//!      expected framed roster. What opens is
//!      `y = (m + Σ r_i) mod t` — **a one-time-padded value**,
//!      uniform on `Z_t` and EXACTLY independent of the curve `m` for any view
//!      missing at least one honest party's mask (proven by enumeration in
//!      `pad_is_exact_and_secret_independent`). Decrypting it does not reveal a
//!      curve coefficient to that view.
//!   3. The mod-t additive shares of `m` are then LOCAL: party 0 takes
//!      `σ_0 = (y − r_0) mod t`, party `i>0` takes `σ_i = (−r_i) mod t`, so
//!      `Σ σ_i ≡ m (mod t)` — each party's share is a function of its own mask
//!      (plus the public `y`), no interaction.
//!   4. One boundary bridge (`a2b_mod_t`) converts the mod-t arithmetic shares
//!      to boolean shares — a secret-shared exact integer sum of the n shares
//!      (`secure_add`, width `w = ⌈log₂ n·t⌉`) followed by `n−1` oblivious
//!      conditional subtractions of the public `t` — and the UNCHANGED
//!      Beaver-triple crossing (`mpc_crossing`) runs and reveals only `(p*,V*)`.
//!
//! [`MaskedDecryptSession`], [`MaskedBoundaryParty`], and
//! [`MaskedDecryptCoordinator`] are the production-shaped composition: a party
//! retains both its threshold secret and its plaintext mask, while only an
//! [`EncryptedMaskContribution`] and a framed threshold decrypt share cross the
//! coordinator. [`masked_decrypt_to_shares`] and [`masked_boundary_clear`] are
//! retained as legacy single-key benchmarks/oracles; they are not the deployment
//! entry point.
//!
//! ## Honest scope (stated like the sibling PoCs)
//!
//! - **REAL:** the value-channel algebra and its composition with the real
//!   party-owned threshold API. The mask is an exact one-time pad over `Z_t`
//!   (enumeration-proven); the opened `y` carries zero information about the
//!   curve; the mod-t share algebra and the `a2b_mod_t` bridge are real MPC on
//!   real shares; the crossing is the unchanged measured protocol; correctness
//!   is KAT-checked against direct decryption and the plaintext reference.
//! - **Process-shaped, not a network protocol:** the integration tooth uses
//!   channels and party threads, but this module does not authenticate session
//!   nonces, public-key contributions, or mask contributions. The legacy
//!   opening methods also leave decrypt shares unauthenticated;
//!   [`ThresholdMaskedCiphertext::open_authenticated_quorum_framed`] verifies
//!   the quorum module's DKG/session/ciphertext/roster-bound Ed25519 envelopes.
//!   The verified setup path now binds salted bivariate-row commitments and
//!   genuine pairwise row-consistency checks into those envelopes. Public
//!   `-a*s+e` coefficient images also force the hidden VSS constants to the
//!   actual fhe.rs public-key share. It still does not prove their hidden
//!   ternary/CBD ranges, or that a malicious party formed its public BFV
//!   decrypt share with in-range smudge. This layer also lacks full crash recovery or persistent
//!   secret-storage/replay policy. The Shamir path tolerates `n-t` absent
//!   custodians after all-dealer DKG, with in-memory exact-session and
//!   exact-target replay teeth. The threshold module's Lean-pinned smudging
//!   floor closes the named decryption-noise channel for the honest-party model;
//!   the remaining malicious-robustness seam is the lattice shortness/range and
//!   decrypt-share proof, not row consistency or the BFV public-key equation.
//! - **Now composed at the next boundary:** locally derived mod-t shares can
//!   enter [`crate::mpc_party::transport::CrossingPartyMachine`], whose peer
//!   ingress is encrypted and whose gate/output frames are session-bound and
//!   signed. [`crate::mpc_party::transport::verify_public_crossing_transcript`]
//!   reconstructs the reveal-only transcript from the exact authenticated
//!   frame set before computation signatures are issued. This closes the
//!   previously missing transport composition; it does not prove malicious
//!   input-share or Beaver-triple formation.

use std::sync::Arc;
use std::time::{Duration, Instant};

use fhe::bfv::{BfvParameters, Ciphertext, Encoding, Plaintext, PublicKey, SecretKey};
use fhe_traits::{
    DeserializeParametrized, FheDecoder, FheDecrypter, FheEncoder, FheEncrypter,
    Serialize as FheSerialize,
};
use rand::Rng;
use rand_09::rngs::StdRng as StdRng09;
use rand_09::SeedableRng as SeedableRng09;

use crate::additive::{bfv_fold_encrypted, BfvFoldedBook};
use crate::bfv_lean::LeanCiphertext;
use crate::mpc::{
    const_int, geq, mpc_crossing, secure_add, select_int, share_int, triples_needed, Crossing,
    SharedInt, Transcript, TriplePool,
};
use crate::threshold::quorum::{
    self, AuthenticatedOpeningAudit, AuthenticatedQuorumCombiner, QuorumDecryptShare, QuorumError,
    QuorumOpeningSession,
};
use crate::threshold::{self, BfvParams, CollectivePublicKey, DecryptShare, ThresholdError};
use crate::Order;

/// Bits needed to hold `x` (`⌈log₂(x+1)⌉`, min 1).
fn bits_for(x: u64) -> usize {
    (64 - x.leading_zeros() as usize).max(1)
}

/// The mod-t share vector of ONE slot: `shares[i]` is party `i`'s additive share,
/// `Σ_i shares[i] ≡ m (mod t)`.
pub type ModTShares = Vec<u64>;

/// Fail-closed errors for the party-owned masked-decrypt composition.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BoundaryError {
    InvalidParty { party: usize, n_parties: usize },
    InvalidLiveSlots { have: usize, degree: usize },
    QuorumTooSmall { have: usize, need: usize },
    DuplicateParty { party: usize },
    SessionMismatch,
    ParamMismatch,
    MalformedWire,
    Crypto,
    Threshold(ThresholdError),
    Quorum(QuorumError),
}

impl From<ThresholdError> for BoundaryError {
    fn from(value: ThresholdError) -> Self {
        Self::Threshold(value)
    }
}

impl From<QuorumError> for BoundaryError {
    fn from(value: QuorumError) -> Self {
        Self::Quorum(value)
    }
}

pub type BoundaryResult<T> = std::result::Result<T, BoundaryError>;

/// Public context binding one mask/decrypt round to one exact ciphertext.
///
/// The nonce is an unauthenticated replay-domain tag, not a signature or a
/// randomness beacon. Hosts must authenticate it together with the target
/// ciphertext and party roster.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MaskedDecryptSession {
    nonce: [u8; 32],
    n_parties: usize,
    live_slots: usize,
    target: LeanCiphertext,
}

impl MaskedDecryptSession {
    /// Create a fresh public session around the ciphertext to be masked.
    pub fn random(
        n_parties: usize,
        live_slots: usize,
        target: LeanCiphertext,
        params: &BfvParams,
    ) -> BoundaryResult<Self> {
        let mut nonce = [0u8; 32];
        rand_09::RngCore::fill_bytes(&mut rand_09::rng(), &mut nonce);
        Self::from_public(nonce, n_parties, live_slots, target, params)
    }

    /// Reconstruct the session from public transport state.
    pub fn from_public(
        nonce: [u8; 32],
        n_parties: usize,
        live_slots: usize,
        target: LeanCiphertext,
        params: &BfvParams,
    ) -> BoundaryResult<Self> {
        if n_parties == 0 {
            return Err(BoundaryError::QuorumTooSmall { have: 0, need: 1 });
        }
        if live_slots == 0 || live_slots > params.degree() {
            return Err(BoundaryError::InvalidLiveSlots {
                have: live_slots,
                degree: params.degree(),
            });
        }
        if target.moduli != params.moduli()
            || target.degree != params.degree()
            || target.polys.len() != 2
        {
            return Err(BoundaryError::ParamMismatch);
        }
        Ciphertext::from_bytes(&target.to_fhe_bytes(), params.arc())
            .map_err(|_| BoundaryError::MalformedWire)?;
        Ok(Self {
            nonce,
            n_parties,
            live_slots,
            target,
        })
    }

    pub fn nonce(&self) -> [u8; 32] {
        self.nonce
    }

    pub fn n_parties(&self) -> usize {
        self.n_parties
    }

    pub fn live_slots(&self) -> usize {
        self.live_slots
    }

    pub fn target(&self) -> &LeanCiphertext {
        &self.target
    }
}

/// The only mask-phase message a party sends to the coordinator.
///
/// It contains the exact public session context and `Enc(r_i)`, never `r_i`.
/// The framing below is strict but deliberately unauthenticated.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EncryptedMaskContribution {
    session: MaskedDecryptSession,
    party: usize,
    encrypted_mask: LeanCiphertext,
}

impl EncryptedMaskContribution {
    pub fn party(&self) -> usize {
        self.party
    }

    pub fn session(&self) -> &MaskedDecryptSession {
        &self.session
    }

    pub fn encrypted_mask(&self) -> &LeanCiphertext {
        &self.encrypted_mask
    }

    /// Strict public-message framing. Authentication is a host responsibility.
    pub fn to_wire_bytes(&self) -> Vec<u8> {
        let target = self.session.target.to_fhe_bytes();
        let mask = self.encrypted_mask.to_fhe_bytes();
        let mut out = Vec::with_capacity(96 + target.len() + mask.len());
        out.extend_from_slice(b"FHBMv001");
        out.extend_from_slice(&(self.party as u64).to_le_bytes());
        out.extend_from_slice(&(self.session.n_parties as u64).to_le_bytes());
        out.extend_from_slice(&(self.session.live_slots as u64).to_le_bytes());
        out.extend_from_slice(&self.session.nonce);
        out.extend_from_slice(&self.session.target.plain_bound.to_le_bytes());
        out.extend_from_slice(&(target.len() as u64).to_le_bytes());
        out.extend_from_slice(&target);
        out.extend_from_slice(&(mask.len() as u64).to_le_bytes());
        out.extend_from_slice(&mask);
        out
    }

    pub fn from_wire_bytes(bytes: &[u8], params: &BfvParams) -> BoundaryResult<Self> {
        let mut i = 0usize;
        if take_boundary_wire::<8>(bytes, &mut i)? != *b"FHBMv001" {
            return Err(BoundaryError::MalformedWire);
        }
        let party = boundary_wire_usize(bytes, &mut i)?;
        let n_parties = boundary_wire_usize(bytes, &mut i)?;
        let live_slots = boundary_wire_usize(bytes, &mut i)?;
        let nonce = take_boundary_wire::<32>(bytes, &mut i)?;
        let target_bound = u64::from_le_bytes(take_boundary_wire::<8>(bytes, &mut i)?);
        let target_len = boundary_wire_usize(bytes, &mut i)?;
        let target_bytes = take_boundary_slice(bytes, &mut i, target_len)?;
        let target = LeanCiphertext::from_fhe_bytes(
            target_bytes,
            params.moduli(),
            params.degree(),
            target_bound,
        )
        .map_err(|_| BoundaryError::MalformedWire)?;
        let session =
            MaskedDecryptSession::from_public(nonce, n_parties, live_slots, target, params)?;
        if party >= n_parties {
            return Err(BoundaryError::InvalidParty { party, n_parties });
        }
        let mask_len = boundary_wire_usize(bytes, &mut i)?;
        let mask_bytes = take_boundary_slice(bytes, &mut i, mask_len)?;
        if i != bytes.len() {
            return Err(BoundaryError::MalformedWire);
        }
        let encrypted_mask = LeanCiphertext::from_fhe_bytes(
            mask_bytes,
            params.moduli(),
            params.degree(),
            params.plaintext_modulus() - 1,
        )
        .map_err(|_| BoundaryError::MalformedWire)?;
        Ok(Self {
            session,
            party,
            encrypted_mask,
        })
    }
}

/// Party-local mask custody for one round. This intentionally has no `Clone`,
/// serialization, or mask accessor.
pub struct MaskedBoundaryParty {
    session: MaskedDecryptSession,
    party: usize,
    mask: Vec<u64>,
}

impl MaskedBoundaryParty {
    /// Independently sample and retain `r_i`, emitting only `Enc(r_i)`.
    pub fn prepare(
        session: &MaskedDecryptSession,
        party: usize,
        params: &BfvParams,
        public_key: &CollectivePublicKey,
    ) -> BoundaryResult<(Self, EncryptedMaskContribution)> {
        if party >= session.n_parties {
            return Err(BoundaryError::InvalidParty {
                party,
                n_parties: session.n_parties,
            });
        }
        let t = params.plaintext_modulus();
        let mut rng = rand_09::rng();
        let mask = (0..session.live_slots)
            .map(|_| rand_09::Rng::random_range(&mut rng, 0..t))
            .collect::<Vec<_>>();
        let mut padded_mask = vec![0u64; params.degree()];
        padded_mask[..session.live_slots].copy_from_slice(&mask);
        let plaintext = Plaintext::try_encode(&padded_mask, Encoding::simd(), params.arc())
            .map_err(|_| BoundaryError::Crypto)?;
        let ciphertext = public_key
            .pk
            .try_encrypt(&plaintext, &mut rng)
            .map_err(|_| BoundaryError::Crypto)?;
        let encrypted_mask = LeanCiphertext::from_fhe_bytes(
            &ciphertext.to_bytes(),
            params.moduli(),
            params.degree(),
            t - 1,
        )
        .map_err(|_| BoundaryError::MalformedWire)?;
        let state = Self {
            session: session.clone(),
            party,
            mask,
        };
        let contribution = EncryptedMaskContribution {
            session: session.clone(),
            party,
            encrypted_mask,
        };
        Ok((state, contribution))
    }

    pub fn party(&self) -> usize {
        self.party
    }

    /// Locally derive this party's row of mod-t shares from the public padded
    /// opening. The mask itself never leaves this object.
    pub fn derive_mod_t_share(&self, opening: &MaskedOpening) -> BoundaryResult<Vec<u64>> {
        if opening.session != self.session {
            return Err(BoundaryError::SessionMismatch);
        }
        let t = opening.plaintext_modulus;
        Ok(opening
            .y
            .iter()
            .zip(self.mask.iter())
            .map(|(&y, &r)| {
                if self.party == 0 {
                    (y + t - r) % t
                } else {
                    (t - r) % t
                }
            })
            .collect())
    }
}

/// Coordinator for the public mask contributions. It cannot accept a plaintext
/// mask or a [`MaskedBoundaryParty`].
pub struct MaskedDecryptCoordinator {
    session: MaskedDecryptSession,
    params: BfvParams,
    contributions: Vec<EncryptedMaskContribution>,
}

impl MaskedDecryptCoordinator {
    pub fn new(session: MaskedDecryptSession, params: BfvParams) -> Self {
        Self {
            session,
            params,
            contributions: Vec::new(),
        }
    }

    pub fn accept(&mut self, contribution: EncryptedMaskContribution) -> BoundaryResult<()> {
        if contribution.session != self.session {
            return Err(BoundaryError::SessionMismatch);
        }
        if self
            .contributions
            .iter()
            .any(|existing| existing.party == contribution.party)
        {
            return Err(BoundaryError::DuplicateParty {
                party: contribution.party,
            });
        }
        self.contributions.push(contribution);
        Ok(())
    }

    /// Homomorphically add the exact target and every public encrypted mask.
    ///
    /// This intentionally uses BFV's native modular add instead of the fold
    /// wrap gate: modulo-t wrap is the one-time-pad construction here, not an
    /// aggregate overflow. The resulting declaration is therefore `[0,t)`.
    pub fn finish(self) -> BoundaryResult<ThresholdMaskedCiphertext> {
        if self.contributions.len() < self.session.n_parties {
            return Err(BoundaryError::QuorumTooSmall {
                have: self.contributions.len(),
                need: self.session.n_parties,
            });
        }
        if self.contributions.len() > self.session.n_parties {
            return Err(BoundaryError::ParamMismatch);
        }
        let mut aggregate =
            Ciphertext::from_bytes(&self.session.target.to_fhe_bytes(), self.params.arc())
                .map_err(|_| BoundaryError::MalformedWire)?;
        for contribution in &self.contributions {
            let encrypted_mask = Ciphertext::from_bytes(
                &contribution.encrypted_mask.to_fhe_bytes(),
                self.params.arc(),
            )
            .map_err(|_| BoundaryError::MalformedWire)?;
            aggregate += &encrypted_mask;
        }
        let ciphertext = LeanCiphertext::from_fhe_bytes(
            &aggregate.to_bytes(),
            self.params.moduli(),
            self.params.degree(),
            self.params.plaintext_modulus() - 1,
        )
        .map_err(|_| BoundaryError::MalformedWire)?;
        Ok(ThresholdMaskedCiphertext {
            session: self.session,
            ciphertext,
        })
    }
}

/// The coordinator's masked aggregate, ready for party-owned threshold shares.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ThresholdMaskedCiphertext {
    session: MaskedDecryptSession,
    ciphertext: LeanCiphertext,
}

impl ThresholdMaskedCiphertext {
    pub fn ciphertext(&self) -> &LeanCiphertext {
        &self.ciphertext
    }

    pub fn session(&self) -> &MaskedDecryptSession {
        &self.session
    }

    /// Parse and combine only framed public decrypt-share messages. Full-quorum,
    /// duplicate-party, smudging, and exact-ciphertext checks are delegated to
    /// the threshold module's fail-closed combine gate.
    pub fn open_framed(
        &self,
        framed_shares: &[Vec<u8>],
        params: &BfvParams,
    ) -> BoundaryResult<MaskedOpening> {
        if framed_shares.len() < self.session.n_parties {
            return Err(BoundaryError::QuorumTooSmall {
                have: framed_shares.len(),
                need: self.session.n_parties,
            });
        }
        if framed_shares.len() > self.session.n_parties {
            return Err(BoundaryError::ParamMismatch);
        }
        let shares = framed_shares
            .iter()
            .map(|wire| DecryptShare::from_wire_bytes(wire, params))
            .collect::<std::result::Result<Vec<_>, _>>()?;
        if shares
            .iter()
            .any(|share| share.ciphertext() != &self.ciphertext)
        {
            return Err(BoundaryError::SessionMismatch);
        }
        let y = threshold::combine(&shares, params)?;
        Ok(MaskedOpening {
            session: self.session.clone(),
            y: y[..self.session.live_slots].to_vec(),
            plaintext_modulus: params.plaintext_modulus(),
        })
    }

    /// Open the same one-time-padded value through a crash-tolerant `t < n`
    /// custody roster.
    ///
    /// The quorum nonce must be the masked-decrypt nonce, and every framed
    /// share must target this exact masked ciphertext.  The caller supplies the
    /// expected roster rather than trusting metadata chosen by the first share.
    /// Construction/combination refusals occur before a [`MaskedOpening`] exists.
    pub fn open_quorum_framed(
        &self,
        expected: &QuorumOpeningSession,
        framed_shares: &[Vec<u8>],
        params: &BfvParams,
    ) -> BoundaryResult<MaskedOpening> {
        if expected.nonce() != self.session.nonce {
            return Err(BoundaryError::SessionMismatch);
        }
        if framed_shares.len() < expected.parties().len() {
            return Err(BoundaryError::QuorumTooSmall {
                have: framed_shares.len(),
                need: expected.parties().len(),
            });
        }
        if framed_shares.len() > expected.parties().len() {
            return Err(BoundaryError::ParamMismatch);
        }
        let shares = framed_shares
            .iter()
            .map(|wire| QuorumDecryptShare::from_wire_bytes(wire, params))
            .collect::<std::result::Result<Vec<_>, _>>()?;
        if shares
            .iter()
            .any(|share| share.ciphertext() != &self.ciphertext)
        {
            return Err(BoundaryError::SessionMismatch);
        }
        let y = quorum::combine_quorum(&shares, expected, params)?;
        Ok(MaskedOpening {
            session: self.session.clone(),
            y: y[..self.session.live_slots].to_vec(),
            plaintext_modulus: params.plaintext_modulus(),
        })
    }

    /// Open through canonical DKG/session/ciphertext/roster-bound signed
    /// decryption-share envelopes.
    ///
    /// This authenticates each configured custodian, binds the accepted
    /// bivariate-VSS setup transcript when the verified constructor was used,
    /// and refuses coordinator replay in memory.  The VSS transcript proves
    /// setup-row consistency and the exact BFV `p0 = -a*s+e` equation. It does
    /// not yet prove the hidden ternary/CBD ranges or that an authenticated
    /// custodian formed `h = c1*s_i +` in-range smudge. Those require the
    /// remaining lattice short-witness/range proofs.
    pub fn open_authenticated_quorum_framed(
        &self,
        combiner: &mut AuthenticatedQuorumCombiner,
        expected: &QuorumOpeningSession,
        framed_shares: &[Vec<u8>],
        params: &BfvParams,
    ) -> BoundaryResult<MaskedOpening> {
        self.open_authenticated_quorum_framed_with_audit(combiner, expected, framed_shares, params)
            .map(|(opening, _audit)| opening)
    }

    /// Authenticated opening plus a digest-only custody transcript commitment
    /// suitable for binding into an outer receipt without disclosing shares.
    pub fn open_authenticated_quorum_framed_with_audit(
        &self,
        combiner: &mut AuthenticatedQuorumCombiner,
        expected: &QuorumOpeningSession,
        framed_shares: &[Vec<u8>],
        params: &BfvParams,
    ) -> BoundaryResult<(MaskedOpening, AuthenticatedOpeningAudit)> {
        if expected.nonce() != self.session.nonce {
            return Err(BoundaryError::SessionMismatch);
        }
        let (y, audit) = combiner.combine_framed_with_audit(
            expected,
            &self.ciphertext,
            framed_shares,
            params,
        )?;
        Ok((
            MaskedOpening {
                session: self.session.clone(),
                y: y[..self.session.live_slots].to_vec(),
                plaintext_modulus: params.plaintext_modulus(),
            },
            audit,
        ))
    }
}

/// The only value opened by threshold decryption: `m + Σr_i (mod t)`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MaskedOpening {
    session: MaskedDecryptSession,
    y: Vec<u64>,
    plaintext_modulus: u64,
}

impl MaskedOpening {
    pub fn values(&self) -> &[u64] {
        &self.y
    }

    pub fn session(&self) -> &MaskedDecryptSession {
        &self.session
    }
}

fn take_boundary_wire<const N: usize>(bytes: &[u8], i: &mut usize) -> BoundaryResult<[u8; N]> {
    let end = i
        .checked_add(N)
        .filter(|&end| end <= bytes.len())
        .ok_or(BoundaryError::MalformedWire)?;
    let out = bytes[*i..end]
        .try_into()
        .map_err(|_| BoundaryError::MalformedWire)?;
    *i = end;
    Ok(out)
}

fn boundary_wire_usize(bytes: &[u8], i: &mut usize) -> BoundaryResult<usize> {
    usize::try_from(u64::from_le_bytes(take_boundary_wire::<8>(bytes, i)?))
        .map_err(|_| BoundaryError::MalformedWire)
}

fn take_boundary_slice<'a>(bytes: &'a [u8], i: &mut usize, len: usize) -> BoundaryResult<&'a [u8]> {
    let end = i
        .checked_add(len)
        .filter(|&end| end <= bytes.len())
        .ok_or(BoundaryError::MalformedWire)?;
    let out = &bytes[*i..end];
    *i = end;
    Ok(out)
}

/// Sample the parties' masks: `masks[i][j]` = party `i`'s uniform `Z_t` mask for
/// slot `j`. Each party samples its own row locally (the PoC uses one rng).
pub fn sample_masks<R: Rng>(n: usize, k: usize, t: u64, rng: &mut R) -> Vec<Vec<u64>> {
    (0..n)
        .map(|_| (0..k).map(|_| rng.gen_range(0..t)).collect())
        .collect()
}

/// The LOCAL share derivation of step 3: given the public masked opening `y` and
/// its own mask row, each party derives its mod-t share of the true slot values.
/// `σ_0 = (y − r_0) mod t`, `σ_i = (−r_i) mod t` for `i > 0`; `Σ σ ≡ m (mod t)`.
pub fn shares_from_masked_opening(y: &[u64], masks: &[Vec<u64>], t: u64) -> Vec<ModTShares> {
    let n = masks.len();
    (0..y.len())
        .map(|j| {
            (0..n)
                .map(|i| {
                    if i == 0 {
                        (y[j] + t - masks[0][j] % t) % t
                    } else {
                        (t - masks[i][j] % t) % t
                    }
                })
                .collect()
        })
        .collect()
}

/// Legacy single-key benchmark result: the padded opening, reconstructed
/// in-process mod-t shares, and phase timings.
pub struct MaskedDecrypt {
    /// The opened masked plaintext `y[j] = (m[j] + Σ_i r_i[j]) mod t` for the K
    /// live slots — a one-time-padded value, safe to publish.
    pub y: Vec<u64>,
    /// Per-slot mod-t additive shares of the TRUE values: `sigma[j][i]`.
    pub sigma: Vec<ModTShares>,
    /// Wall time for the parties to encrypt their masks + the homomorphic adds.
    pub mask: Duration,
    /// Wall time for the legacy single-key decrypt. The production-shaped path
    /// uses [`ThresholdMaskedCiphertext::open_framed`] instead.
    pub decrypt: Duration,
}

/// Legacy benchmark/oracle for steps 1–3 using one in-process secret key.
///
/// It opens only the padded value, but does not model threshold key custody.
/// New protocol callers use [`MaskedBoundaryParty`] and
/// [`MaskedDecryptCoordinator`].
pub fn masked_decrypt_to_shares<R: Rng>(
    ct: &Ciphertext,
    k: usize,
    n: usize,
    params: &Arc<BfvParameters>,
    pk: &PublicKey,
    sk: &SecretKey,
    rng_bfv: &mut StdRng09,
    rng: &mut R,
) -> MaskedDecrypt {
    let t = params.plaintext();

    // (1) Each party encrypts its uniform Z_t mask and adds it homomorphically.
    let t0 = Instant::now();
    let masks = sample_masks(n, k, t, rng);
    let mut ct_masked = ct.clone();
    for row in &masks {
        let pt = Plaintext::try_encode(row, Encoding::simd(), params).expect("mask encode");
        let enc: Ciphertext = pk.try_encrypt(&pt, rng_bfv).expect("mask encrypt");
        ct_masked += &enc;
    }
    let mask_dt = t0.elapsed();

    // (2) Decrypt the MASKED ciphertext. The opened value is one-time-padded —
    //     uniform on Z_t, independent of the curve — so this opening is safe.
    let t0 = Instant::now();
    let pt = sk.try_decrypt(&ct_masked).expect("masked decrypt");
    let y_full = Vec::<u64>::try_decode(&pt, Encoding::simd()).expect("masked decode");
    let y: Vec<u64> = y_full[..k].to_vec();
    let decrypt_dt = t0.elapsed();

    // (3) LOCAL mod-t share derivation from (public y, own mask).
    let sigma = shares_from_masked_opening(&y, &masks, t);

    MaskedDecrypt {
        y,
        sigma,
        mask: mask_dt,
        decrypt: decrypt_dt,
    }
}

/// Step 4 — the mod-t ARITHMETIC → BOOLEAN bridge. The n mod-t shares of one
/// slot are summed EXACTLY (secret-shared ripple adders at width `w = ⌈log₂ n·t⌉`,
/// no wrap), then reduced `mod t` by `n−1` oblivious conditional subtractions
/// (`[acc ≥ t]` → subtract, via `geq` + `select_int`; the comparison bit is never
/// opened). The result is truncated to `b_out` bits — exact, because the true
/// value `m < 2^b_out ≤ t` and boolean sharing is bitwise. Feeds `mpc_crossing`
/// unchanged.
pub fn a2b_mod_t<R: Rng>(
    sigma: &ModTShares,
    t: u64,
    b_out: usize,
    pool: &mut TriplePool,
    tr: &mut Transcript,
    rng: &mut R,
) -> SharedInt {
    let n = sigma.len();
    let w = bits_for(n as u64 * (t - 1));
    assert!(w < 63, "share-sum width {w} out of range");
    assert!(b_out <= w);

    // Exact integer sum of the n shares (each party boolean-shares its own).
    let mut acc = share_int(sigma[0], w, n, rng);
    for &s in &sigma[1..] {
        let xi = share_int(s, w, n, rng);
        acc = secure_add(&acc, &xi, pool, tr);
    }

    // Reduce mod t: up to n−1 conditional subtractions, each oblivious.
    let t_const = const_int(t, w, n);
    let neg_t = const_int((1u64 << w) - t, w, n); // two's-complement −t at width w
    for _ in 0..n - 1 {
        let ge = geq(&acc, &t_const, pool, tr);
        let sub = secure_add(&acc, &neg_t, pool, tr);
        acc = select_int(&ge, &sub, &acc, pool, tr);
    }

    // acc now boolean-shares m < t exactly; keep the low b_out bits (bitwise
    // sharing truncates locally and exactly; the high bits are zero for m < 2^b_out).
    acc.truncate(b_out);
    acc
}

/// Beaver triples one masked-boundary clear consumes: `2K` slots × [`n−1` exact
/// adds + `n−1` × (geq + subtract-add + select)] + the crossing itself.
pub fn triples_needed_boundary(k: usize, b: usize, t: u64, n: usize) -> usize {
    let w = bits_for(n as u64 * (t - 1));
    let per_slot = (n - 1) * (w - 1) + (n - 1) * (3 * w + (w - 1) + w);
    2 * k * per_slot + triples_needed(k, b) + w
}

/// One legacy in-process masked-boundary benchmark, with per-phase timings.
pub struct BoundaryRun {
    pub cross: Crossing,
    pub transcript: Transcript,
    pub fold: Duration,
    pub encrypt: Duration,
    pub mask: Duration,
    pub decrypt: Duration,
    pub a2b: Duration,
    pub crossing: Duration,
    pub triples_used: usize,
    pub a2b_and_gates: usize,
}

/// Legacy single-key end-to-end oracle: carry-free BFV fold → homomorphic
/// masking → open the padded value → local mod-t shares → a2b bridge →
/// Beaver-triple crossing → reveal `(p*,V*)`.
///
/// This remains useful for timing/algebra parity, but its `BfvFoldedBook` owns a
/// joint secret key. The production-shaped custody path begins at
/// [`MaskedDecryptSession`] and is exercised by the channel integration test.
pub fn masked_boundary_clear<R: Rng>(
    orders: &[Order],
    k: usize,
    b: usize,
    n: usize,
    params: &Arc<BfvParameters>,
    rng: &mut R,
) -> BoundaryRun {
    let t = params.plaintext();
    let mut rng_bfv = StdRng09::seed_from_u64(0xB0_04_DA_47);

    // (a) the carry-free additive fold (curves stay encrypted).
    let folded: BfvFoldedBook = bfv_fold_encrypted(orders, k, params);

    // (b) masked decrypt-to-shares for demand and supply.
    let d_md = masked_decrypt_to_shares(
        &folded.d_ct,
        k,
        n,
        params,
        &folded.pk,
        &folded.sk,
        &mut rng_bfv,
        rng,
    );
    let s_md = masked_decrypt_to_shares(
        &folded.s_ct,
        k,
        n,
        params,
        &folded.pk,
        &folded.sk,
        &mut rng_bfv,
        rng,
    );

    // (c) the mod-t → boolean bridge, per slot (slots are independent — the
    //     AND-depth, hence network rounds, does not grow with K).
    let mut pool = TriplePool::generate(triples_needed_boundary(k, b, t, n), n, rng);
    let mut tr = Transcript::default();
    let t0 = Instant::now();
    let d_shared: Vec<SharedInt> = d_md
        .sigma
        .iter()
        .map(|s| a2b_mod_t(s, t, b, &mut pool, &mut tr, rng))
        .collect();
    let s_shared: Vec<SharedInt> = s_md
        .sigma
        .iter()
        .map(|s| a2b_mod_t(s, t, b, &mut pool, &mut tr, rng))
        .collect();
    let a2b_dt = t0.elapsed();
    let a2b_ands = tr.and_gates;
    // Depth: ⌈log₂ n⌉ adds of width w + (n−1) sequential conditional subtracts
    // (each a w-deep geq + 1-deep select), shared across all 2K independent slots.
    let w = bits_for(n as u64 * (t - 1));
    tr.rounds += w * n.next_power_of_two().trailing_zeros().max(1) as usize + (n - 1) * (3 * w + 1);

    // (d) the unchanged Beaver-triple crossing — reveals ONLY (p*, V*).
    let t0 = Instant::now();
    let cross = mpc_crossing(&d_shared, &s_shared, &mut pool, &mut tr);
    let crossing_dt = t0.elapsed();

    BoundaryRun {
        cross,
        fold: folded.timing.fold,
        encrypt: folded.timing.encrypt,
        mask: d_md.mask + s_md.mask,
        decrypt: d_md.decrypt + s_md.decrypt,
        a2b: a2b_dt,
        crossing: crossing_dt,
        triples_used: pool.consumed(),
        a2b_and_gates: a2b_ands,
        transcript: tr,
    }
}

/// EXACT pad histogram: enumerate the FULL mask space of one slot at a toy `t`
/// and return the distribution of the opened `y` for a given secret `m`, as seen
/// by a coalition that already knows the masks of `known` parties. If the
/// histograms for two different secrets are IDENTICAL, the opening carries zero
/// information about the secret — the one-time-pad property, proven not sampled.
pub fn masked_opening_histogram(
    m: u64,
    t: u64,
    n: usize,
    known: &[usize],
) -> std::collections::BTreeMap<(Vec<u64>, u64), u64> {
    let mut hist: std::collections::BTreeMap<(Vec<u64>, u64), u64> =
        std::collections::BTreeMap::new();
    let total = (t as u128).pow(n as u32);
    for idx in 0..total {
        let mut rem = idx;
        let mut masks = vec![0u64; n];
        for s in masks.iter_mut() {
            *s = (rem % t as u128) as u64;
            rem /= t as u128;
        }
        let y = masks.iter().fold(m % t, |a, &r| (a + r) % t);
        let view: Vec<u64> = known.iter().map(|&i| masks[i]).collect();
        *hist.entry((view, y)).or_insert(0) += 1;
    }
    hist
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::additive::pick_params;
    use crate::{reference_clear, Side};
    use rand::rngs::StdRng;
    use rand::SeedableRng;

    /// The pad is EXACT: over the full mask space, the (coalition-view, opened-y)
    /// histogram is identical for two different secrets — even when all but one
    /// party's masks are known. Enumeration, not sampling.
    #[test]
    fn pad_is_exact_and_secret_independent() {
        let (t, n) = (17u64, 3usize);
        for known in [vec![], vec![0usize], vec![0, 2]] {
            let h_a = masked_opening_histogram(0, t, n, &known);
            let h_b = masked_opening_histogram(13, t, n, &known);
            assert_eq!(h_a, h_b, "masked opening depends on the secret");
        }
    }

    /// Share algebra: Σσ ≡ m (mod t) for every slot, on real masks.
    #[test]
    fn shares_reconstruct_mod_t() {
        let mut rng = StdRng::seed_from_u64(2);
        let (t, n, k) = (1_032_193u64, 4usize, 8usize);
        let m: Vec<u64> = (0..k as u64).map(|j| j * 977 % 65_536).collect();
        let masks = sample_masks(n, k, t, &mut rng);
        let y: Vec<u64> = (0..k)
            .map(|j| masks.iter().fold(m[j], |a, r| (a + r[j]) % t))
            .collect();
        let sigma = shares_from_masked_opening(&y, &masks, t);
        for j in 0..k {
            let rec = sigma[j].iter().fold(0u64, |a, &s| (a + s) % t);
            assert_eq!(rec, m[j], "slot {j} share reconstruction");
        }
    }

    /// The a2b bridge: random mod-t splits of random values open to the value.
    #[test]
    fn a2b_mod_t_roundtrips() {
        let mut rng = StdRng::seed_from_u64(3);
        let (t, n, b) = (1_032_193u64, 4usize, 16usize);
        let mut pool = TriplePool::generate(64 * triples_needed_boundary(1, b, t, n), n, &mut rng);
        let mut tr = Transcript::default();
        for &m in &[0u64, 1, 2, 65_535, 40_000, 12_345] {
            // random mod-t split of m
            let mut sigma: ModTShares = (0..n - 1).map(|_| rng.gen_range(0..t)).collect();
            let partial = sigma.iter().fold(0u64, |a, &s| (a + s) % t);
            sigma.push((m + t - partial) % t);
            let shared = a2b_mod_t(&sigma, t, b, &mut pool, &mut tr, &mut rng);
            assert_eq!(crate::mpc::open_int(&shared), m, "a2b_mod_t({m})");
        }
    }

    /// KAT vs DIRECT decryption: on real BFV-folded curves, the masked path's
    /// reconstructed shares equal what decrypting the curve directly yields —
    /// the protocol replaces the decryption without changing the value.
    #[test]
    fn masked_decrypt_matches_direct_decrypt() {
        use fhe_traits::{FheDecoder, FheDecrypter};
        let mut rng = StdRng::seed_from_u64(4);
        let params = pick_params(20);
        let t = params.plaintext();
        let (k, n) = (16usize, 3usize);
        let book: Vec<Order> = (0..24)
            .map(|i| Order {
                side: if i % 2 == 0 { Side::Bid } else { Side::Ask },
                limit: (i * 3) % k,
                qty: 1 + (i as u16 % 5),
            })
            .collect();
        let folded = bfv_fold_encrypted(&book, k, &params);
        // Direct decryption is the legacy test oracle, never the deployment path.
        let pt = folded.sk.try_decrypt(&folded.d_ct).expect("direct");
        let direct = Vec::<u64>::try_decode(&pt, Encoding::simd()).expect("decode");
        // the masked path:
        let mut rng_bfv = StdRng09::seed_from_u64(99);
        let md = masked_decrypt_to_shares(
            &folded.d_ct,
            k,
            n,
            &params,
            &folded.pk,
            &folded.sk,
            &mut rng_bfv,
            &mut rng,
        );
        for j in 0..k {
            let rec = md.sigma[j].iter().fold(0u64, |a, &s| (a + s) % t);
            assert_eq!(rec, direct[j], "slot {j}: shares ≠ direct decryption");
        }
    }

    /// The full pipeline KAT: fold → mask → decrypt-masked → shares → a2b →
    /// crossing equals the plaintext reference (correctness preserved end-to-end).
    #[test]
    fn masked_boundary_matches_plaintext_reference() {
        let mut rng = StdRng::seed_from_u64(5);
        let params = pick_params(20);
        for &(nn, k, n) in &[(48usize, 32usize, 3usize), (64, 24, 4)] {
            let book: Vec<Order> = (0..nn)
                .map(|i| Order {
                    side: if i % 2 == 0 { Side::Bid } else { Side::Ask },
                    limit: (i * 7) % k,
                    qty: 1 + (i as u16 % 6),
                })
                .collect();
            let reference = reference_clear(&book, k);
            let run = masked_boundary_clear(&book, k, 16, n, &params, &mut rng);
            assert_eq!(run.cross.p_star, reference.p_star, "N={nn} K={k} n={n}");
            assert_eq!(
                run.cross.v_star as u32, reference.v_star,
                "N={nn} K={k} n={n}"
            );
            assert!(run.transcript.is_reveal_only(k, 16));
        }
    }
}
