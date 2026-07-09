//! A **hybrid** (classical + post-quantum) session key-exchange, so a recorded
//! session is not *harvest-now-decrypt-later* (HNDL) vulnerable: an adversary
//! who records the handshake today and acquires a quantum computer later still
//! cannot recover the session key.
//!
//! The classical transport seals each frame with X25519 ECDH → HKDF-SHA256 →
//! ChaCha20-Poly1305. That protects against a *classical* adversary but not a
//! future quantum one, because X25519 (a discrete-log problem) falls to Shor's
//! algorithm. This module adds the missing half: a session KEM whose derived
//! key depends on **both** an X25519 secret **and** an ML-KEM-768 (FIPS 203)
//! secret.
//!
//! ## The combiner (the load-bearing correctness point)
//!
//! We follow the published **X-Wing** / TLS **X25519MLKEM768** hybrid-KEM
//! construction: derive one classical secret `ss_x25519` and one post-quantum
//! secret `ss_mlkem`, then feed **both, concatenated, plus the full public
//! transcript** through a single KDF:
//!
//! ```text
//! session_key = HKDF-SHA256(
//!     salt = DOMAIN,
//!     ikm  = ss_x25519 ‖ ss_mlkem,
//!     info = DOMAIN ‖ transcript )
//! ```
//!
//! This is a **concatenation KDF, never XOR**: with XOR an adversary who learns
//! one secret could cancel it and forge agreement on the other; with a
//! collision-resistant KDF over the *concatenation* the output depends jointly
//! and inextricably on both. Consequently breaking X25519 alone (quantum) does
//! not recover the key — `ss_mlkem` still protects it — and breaking ML-KEM
//! alone does not either — `ss_x25519` protects it. That two-sided dependence is
//! exactly what the `hybrid_dependence_*` tests pin.
//!
//! The `transcript` binds the derived key to the exact public handshake material
//! (both X25519 public keys, the ML-KEM encapsulation key, and the ML-KEM
//! ciphertext), so an active attacker cannot substitute ephemeral material
//! without changing the key — the same transcript binding X-Wing performs over
//! `ct_X ‖ pk_X`.
//!
//! ## Shape
//!
//! One round trip. The **responder** publishes a [`HybridOffer`] (its X25519
//! ephemeral public key + its ML-KEM encapsulation key) and keeps the matching
//! [`HybridResponder`] secrets. The **initiator** consumes the offer with
//! [`initiate`], producing a [`HybridInitiatorMessage`] (its X25519 ephemeral
//! public key + the ML-KEM ciphertext) and *its* copy of the session key. The
//! responder feeds that message to [`HybridResponder::finish`] to derive the
//! *same* session key. Confidentiality only: this is a KEM, there is no enroll /
//! pin / signature here (peer authentication rides the existing identity/handoff
//! layer).
//!
//! ## `kem` traits
//!
//! ml-kem 0.2.3 re-exports the `Encapsulate`/`Decapsulate` traits its encaps /
//! decaps are built on via its own `ml_kem::kem` module, so this module imports
//! them from `ml_kem::kem` and never names the pinned pre-release `kem` crate.

use hkdf::Hkdf;
use ml_kem::kem::{Decapsulate, Encapsulate};
use ml_kem::{Ciphertext, Encoded, EncodedSizeUser, KemCore, MlKem768};
use sha2::Sha256;
use x25519_dalek::{PublicKey, StaticSecret};
use zeroize::Zeroize;

type Ek = <MlKem768 as KemCore>::EncapsulationKey;
type Dk = <MlKem768 as KemCore>::DecapsulationKey;

/// HKDF domain-separation / version tag for the hybrid combiner. Bump on any
/// change to the transcript layout or combiner. Kept byte-identical to captp's
/// original inline value so the derived key is unchanged across the lift.
const HYBRID_DOMAIN: &[u8] = b"dregg-captp-hybrid-kem-x25519-mlkem768-v1";

/// Errors from the hybrid handshake (all are malformed-wire faults; the KEM
/// itself does not fail on well-formed input).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum HybridError {
    /// The ML-KEM encapsulation key in an offer was the wrong length / malformed.
    BadEncapKey,
    /// The ML-KEM ciphertext in an initiator message was the wrong length /
    /// malformed.
    BadCiphertext,
    /// ML-KEM encapsulation failed (RNG fault).
    Encapsulation,
}

impl std::fmt::Display for HybridError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            HybridError::BadEncapKey => write!(f, "malformed ML-KEM encapsulation key"),
            HybridError::BadCiphertext => write!(f, "malformed ML-KEM ciphertext"),
            HybridError::Encapsulation => write!(f, "ML-KEM encapsulation failed"),
        }
    }
}

impl std::error::Error for HybridError {}

/// An OS-backed CSPRNG adapter exposing the `rand_core` 0.6 `CryptoRngCore` that
/// `ml-kem` / `x25519-dalek` require, sourced from `getrandom`. Every call reads
/// fresh OS entropy (no reseed state to compromise).
struct OsCsprng;

impl rand_core::RngCore for OsCsprng {
    fn next_u32(&mut self) -> u32 {
        let mut b = [0u8; 4];
        self.fill_bytes(&mut b);
        u32::from_le_bytes(b)
    }
    fn next_u64(&mut self) -> u64 {
        let mut b = [0u8; 8];
        self.fill_bytes(&mut b);
        u64::from_le_bytes(b)
    }
    fn fill_bytes(&mut self, dest: &mut [u8]) {
        getrandom::fill(dest).expect("getrandom failed");
    }
    fn try_fill_bytes(&mut self, dest: &mut [u8]) -> Result<(), rand_core::Error> {
        self.fill_bytes(dest);
        Ok(())
    }
}

impl rand_core::CryptoRng for OsCsprng {}

/// The responder's public offer: its X25519 ephemeral public key and its
/// ML-KEM-768 encapsulation key. Sent to the initiator to open a hybrid
/// handshake.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HybridOffer {
    /// X25519 ephemeral public key (classical half).
    pub x25519_pk: [u8; 32],
    /// ML-KEM-768 encapsulation key bytes (post-quantum half, 1184 B).
    pub mlkem_ek: Vec<u8>,
}

/// The initiator's reply: its X25519 ephemeral public key and the ML-KEM
/// ciphertext encapsulated to the responder's encapsulation key.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HybridInitiatorMessage {
    /// X25519 ephemeral public key (classical half).
    pub x25519_pk: [u8; 32],
    /// ML-KEM-768 ciphertext (post-quantum half, 1088 B).
    pub mlkem_ct: Vec<u8>,
}

/// Responder-side secret state kept between publishing a [`HybridOffer`] and
/// calling [`finish`](HybridResponder::finish). Holds the X25519 secret, the
/// ML-KEM decapsulation key, and a copy of the public offer material needed to
/// reconstruct the transcript.
pub struct HybridResponder {
    x25519_sk: StaticSecret,
    x25519_pk: [u8; 32],
    mlkem_dk: Dk,
    mlkem_ek_bytes: Vec<u8>,
}

/// Build the concatenation-KDF transcript: the exact public handshake bytes, in
/// a fixed order both sides agree on.
fn transcript(offer_x25519: &[u8; 32], ek: &[u8], msg_x25519: &[u8; 32], ct: &[u8]) -> Vec<u8> {
    let mut t = Vec::with_capacity(32 + ek.len() + 32 + ct.len());
    t.extend_from_slice(offer_x25519);
    t.extend_from_slice(ek);
    t.extend_from_slice(msg_x25519);
    t.extend_from_slice(ct);
    t
}

/// The load-bearing combiner: HKDF-SHA256 over `ss_x25519 ‖ ss_mlkem`
/// (concatenation, never XOR) with the transcript as HKDF `info`. See the module
/// docs.
pub fn combine(ss_x25519: &[u8; 32], ss_mlkem: &[u8; 32], transcript: &[u8]) -> [u8; 32] {
    let mut ikm = Vec::with_capacity(64);
    ikm.extend_from_slice(ss_x25519);
    ikm.extend_from_slice(ss_mlkem);

    let hk = Hkdf::<Sha256>::new(Some(HYBRID_DOMAIN), &ikm);
    let mut info = Vec::with_capacity(HYBRID_DOMAIN.len() + transcript.len());
    info.extend_from_slice(HYBRID_DOMAIN);
    info.extend_from_slice(transcript);

    let mut key = [0u8; 32];
    hk.expand(&info, &mut key)
        .expect("HKDF-SHA256 expand of 32 bytes never fails");
    ikm.zeroize();
    key
}

fn shared_to_array(ss: ml_kem::SharedKey<MlKem768>) -> [u8; 32] {
    let mut out = [0u8; 32];
    out.copy_from_slice(ss.as_slice());
    out
}

/// Responder step 1: mint a fresh hybrid offer and keep the matching secret
/// state. The returned [`HybridOffer`] is sent to the initiator; the
/// [`HybridResponder`] is retained for [`finish`](HybridResponder::finish).
pub fn responder_offer() -> (HybridOffer, HybridResponder) {
    let mut rng = OsCsprng;

    // Classical half: fresh X25519 ephemeral keypair.
    let x25519_sk = StaticSecret::random_from_rng(&mut rng);
    let x25519_pk = PublicKey::from(&x25519_sk).to_bytes();

    // Post-quantum half: fresh ML-KEM-768 keypair.
    let (mlkem_dk, mlkem_ek) = MlKem768::generate(&mut rng);
    let mlkem_ek_bytes = mlkem_ek.as_bytes().to_vec();

    let offer = HybridOffer {
        x25519_pk,
        mlkem_ek: mlkem_ek_bytes.clone(),
    };
    let responder = HybridResponder {
        x25519_sk,
        x25519_pk,
        mlkem_dk,
        mlkem_ek_bytes,
    };
    (offer, responder)
}

/// Initiator step: consume a responder's [`HybridOffer`], deriving the session
/// key and the [`HybridInitiatorMessage`] to send back.
///
/// Fails only if the offer's ML-KEM encapsulation key is malformed.
pub fn initiate(offer: &HybridOffer) -> Result<(HybridInitiatorMessage, [u8; 32]), HybridError> {
    let mut rng = OsCsprng;

    // Classical half: our ephemeral X25519 + DH against the offer's pk.
    let x25519_sk = StaticSecret::random_from_rng(&mut rng);
    let x25519_pk = PublicKey::from(&x25519_sk).to_bytes();
    let ss_x25519 = x25519_sk
        .diffie_hellman(&PublicKey::from(offer.x25519_pk))
        .to_bytes();

    // Post-quantum half: encapsulate to the offer's ML-KEM key.
    let ek_encoded =
        Encoded::<Ek>::try_from(offer.mlkem_ek.as_slice()).map_err(|_| HybridError::BadEncapKey)?;
    let ek = Ek::from_bytes(&ek_encoded);
    let (ct, ss_mlkem) = ek
        .encapsulate(&mut rng)
        .map_err(|_| HybridError::Encapsulation)?;
    let ss_mlkem = shared_to_array(ss_mlkem);
    let ct_bytes = ct.as_slice().to_vec();

    let t = transcript(&offer.x25519_pk, &offer.mlkem_ek, &x25519_pk, &ct_bytes);
    let session_key = combine(&ss_x25519, &ss_mlkem, &t);

    Ok((
        HybridInitiatorMessage {
            x25519_pk,
            mlkem_ct: ct_bytes,
        },
        session_key,
    ))
}

impl HybridResponder {
    /// Responder step 2: consume the initiator's message and derive the session
    /// key — identical to the initiator's when the handshake is faithful.
    ///
    /// Fails only if the ML-KEM ciphertext is malformed.
    pub fn finish(&self, msg: &HybridInitiatorMessage) -> Result<[u8; 32], HybridError> {
        // Classical half: DH of our secret against the initiator's pk.
        let ss_x25519 = self
            .x25519_sk
            .diffie_hellman(&PublicKey::from(msg.x25519_pk))
            .to_bytes();

        // Post-quantum half: decapsulate the ciphertext with our dk.
        let ct = Ciphertext::<MlKem768>::try_from(msg.mlkem_ct.as_slice())
            .map_err(|_| HybridError::BadCiphertext)?;
        let ss_mlkem = shared_to_array(
            self.mlkem_dk
                .decapsulate(&ct)
                .map_err(|_| HybridError::BadCiphertext)?,
        );

        let t = transcript(
            &self.x25519_pk,
            &self.mlkem_ek_bytes,
            &msg.x25519_pk,
            &msg.mlkem_ct,
        );
        Ok(combine(&ss_x25519, &ss_mlkem, &t))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// KEM correctness: both parties derive the SAME session key from the hybrid
    /// handshake (X25519 + ML-KEM-768 round trip).
    #[test]
    fn hybrid_roundtrip_same_key() {
        let (offer, responder) = responder_offer();
        // Offer carries both halves at their FIPS-203 / X25519 sizes.
        assert_eq!(offer.x25519_pk.len(), 32);
        assert_eq!(offer.mlkem_ek.len(), 1184); // ML-KEM-768 encapsulation key

        let (msg, initiator_key) = initiate(&offer).expect("initiate");
        assert_eq!(msg.mlkem_ct.len(), 1088); // ML-KEM-768 ciphertext

        let responder_key = responder.finish(&msg).expect("finish");
        assert_eq!(
            initiator_key, responder_key,
            "both sides must agree on the hybrid session key"
        );
    }

    /// HYBRID-DEPENDENCE: the derived session key depends on BOTH secrets.
    /// Zeroing or replacing either secret alone changes the key, and the
    /// transcript binds in too. This pins the concatenation-KDF combiner:
    /// neither half can be cancelled.
    #[test]
    fn hybrid_dependence_on_both_secrets() {
        let ss_x = [0x11u8; 32];
        let ss_m = [0x22u8; 32];
        let t = b"fixed-transcript";

        let key = combine(&ss_x, &ss_m, t);

        assert_ne!(
            key,
            combine(&ss_x, &[0u8; 32], t),
            "zeroing the ML-KEM secret must change the key"
        );
        assert_ne!(
            key,
            combine(&ss_x, &[0x33u8; 32], t),
            "replacing the ML-KEM secret must change the key"
        );
        assert_ne!(
            key,
            combine(&[0u8; 32], &ss_m, t),
            "zeroing the X25519 secret must change the key"
        );
        assert_ne!(
            key,
            combine(&[0x44u8; 32], &ss_m, t),
            "replacing the X25519 secret must change the key"
        );
        assert_ne!(
            key,
            combine(&ss_x, &ss_m, b"other-transcript"),
            "the transcript must bind into the key"
        );
    }

    /// End-to-end: a ciphertext tampered in flight makes the responder derive a
    /// DIFFERENT key than the initiator — the ML-KEM half genuinely participates.
    #[test]
    fn hybrid_tampered_ciphertext_diverges() {
        let (offer, responder) = responder_offer();
        let (mut msg, initiator_key) = initiate(&offer).expect("initiate");

        msg.mlkem_ct[500] ^= 0xff;
        let responder_key = responder.finish(&msg).expect("finish still succeeds");
        assert_ne!(
            initiator_key, responder_key,
            "tampering the PQ ciphertext must break key agreement"
        );
    }

    /// Malformed post-quantum material is rejected, not silently accepted.
    #[test]
    fn hybrid_rejects_malformed_material() {
        let (mut offer, _responder) = responder_offer();
        offer.mlkem_ek.truncate(10);
        assert_eq!(initiate(&offer).unwrap_err(), HybridError::BadEncapKey);

        let (offer, responder) = responder_offer();
        let (mut msg, _k) = initiate(&offer).unwrap();
        msg.mlkem_ct.truncate(10);
        assert_eq!(
            responder.finish(&msg).unwrap_err(),
            HybridError::BadCiphertext
        );
    }
}
