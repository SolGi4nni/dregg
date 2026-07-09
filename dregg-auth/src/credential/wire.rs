//! Wire format: **postcard, versioned by prefix, base64url for headers**.
//!
//! The byte form is [postcard](https://docs.rs/postcard) (compact, canonical
//! for a fixed schema — the property the signed digests rely on). The string
//! form is the version prefix plus base64url (no padding) of the postcard
//! bytes, safe for HTTP headers / CLI args / env vars:
//!
//! * credential: `dga1_<base64url>`
//! * discharge:  `dgd1_<base64url>`
//!
//! The prefix IS the version: a breaking schema change bumps it (`dga2_`), and
//! a decoder never guesses — an unknown prefix is an error, not a fallback.
//! The golden-vector discipline applies to any binding (sdk-py/sdk-ts wrap
//! this exact byte schema; vectors in `tests/`).
//!
//! A decoded credential is structurally validated (signature lengths, a
//! non-empty chain, the carried proof key matching the tail block) before it
//! is handed back; cryptographic validity is still — always — decided by
//! [`Credential::verify`].

use base64::Engine;
use base64::engine::general_purpose::URL_SAFE_NO_PAD;
use ed25519_dalek::SigningKey;
use serde::{Deserialize, Serialize};

use super::caveat::Caveat;
use super::chain::{Block, Credential, Discharge};
use super::pred::Pred;

/// Version prefix of an encoded credential.
pub const CREDENTIAL_PREFIX: &str = "dga1_";
/// Version prefix of an encoded discharge.
pub const DISCHARGE_PREFIX: &str = "dgd1_";

/// A credential or discharge failed to decode.
#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error)]
pub enum WireError {
    /// The string does not carry a known version prefix.
    #[error("unknown wire prefix (expected `{expected}`)")]
    Prefix {
        /// The prefix this decoder accepts.
        expected: &'static str,
    },
    /// The payload is not valid base64url.
    #[error("payload is not base64url: {0}")]
    Base64(String),
    /// The bytes do not parse as the versioned postcard schema.
    #[error("payload does not match the v1 schema: {0}")]
    Schema(String),
    /// The structure is schema-valid but internally inconsistent.
    #[error("malformed credential: {0}")]
    Malformed(&'static str),
}

#[derive(Serialize, Deserialize)]
struct BlockWire {
    caveats: Vec<Caveat>,
    next_pub: [u8; 32],
    /// The next block's ML-DSA-65 public key (FIPS 204 = 1952 bytes; length
    /// checked on decode). The PQ half of the carried attenuation key.
    next_pub_ml_dsa: Vec<u8>,
    /// 64 ed25519 signature bytes (postcard byte-seq; length checked on decode).
    sig: Vec<u8>,
    /// The ML-DSA-65 signature over the same block digest (length checked on
    /// decode). A missing/short PQ half fails structurally — fail-closed.
    sig_ml_dsa: Vec<u8>,
}

#[derive(Serialize, Deserialize)]
struct CredentialWire {
    nonce: [u8; 32],
    blocks: Vec<BlockWire>,
    /// The tail (proof-of-possession / attenuation) key seed — what makes the
    /// encoded form a BEARER credential.
    proof_seed: [u8; 32],
}

#[derive(Serialize, Deserialize)]
struct DischargeWire {
    caveat_id: Vec<u8>,
    caveats: Vec<Pred>,
    binding: Option<[u8; 32]>,
    /// 64 signature bytes.
    sig: Vec<u8>,
}

fn sig64(v: &[u8]) -> Result<[u8; 64], WireError> {
    v.try_into()
        .map_err(|_| WireError::Malformed("signature is not 64 bytes"))
}

/// Structural fail-closed check on a block's PQ half: the carried ML-DSA public
/// key and signature must be exactly the FIPS 204 lengths. A missing or
/// truncated PQ half is rejected here, before any cryptographic check.
fn check_pq_lengths(next_pub_ml_dsa: &[u8], sig_ml_dsa: &[u8]) -> Result<(), WireError> {
    use super::pq::{ML_DSA_PK_LEN, ML_DSA_SIG_LEN};
    if next_pub_ml_dsa.len() != ML_DSA_PK_LEN {
        return Err(WireError::Malformed(
            "block ML-DSA public key is not the FIPS 204 length (missing/truncated PQ half)",
        ));
    }
    if sig_ml_dsa.len() != ML_DSA_SIG_LEN {
        return Err(WireError::Malformed(
            "block ML-DSA signature is not the FIPS 204 length (missing/truncated PQ half)",
        ));
    }
    Ok(())
}

impl Credential {
    /// Encode to the `dga1_…` string form. **Bearer**: the string carries the
    /// tail key, i.e. both the right to present and the right to attenuate
    /// further — transmit it like the capability it is.
    pub fn encode(&self) -> String {
        let wire = CredentialWire {
            nonce: self.nonce,
            blocks: self
                .blocks
                .iter()
                .map(|b| BlockWire {
                    caveats: b.caveats.clone(),
                    next_pub: b.next_pub,
                    next_pub_ml_dsa: b.next_pub_ml_dsa.clone(),
                    sig: b.sig.to_vec(),
                    sig_ml_dsa: b.sig_ml_dsa.clone(),
                })
                .collect(),
            proof_seed: self.proof.to_bytes(),
        };
        let bytes = postcard::to_stdvec(&wire).expect("credential encoding is total");
        format!("{CREDENTIAL_PREFIX}{}", URL_SAFE_NO_PAD.encode(bytes))
    }

    /// Decode from the `dga1_…` string form. Structural validation only —
    /// authorization is decided by [`Credential::verify`].
    pub fn decode(s: &str) -> Result<Credential, WireError> {
        let body = s
            .trim()
            .strip_prefix(CREDENTIAL_PREFIX)
            .ok_or(WireError::Prefix {
                expected: CREDENTIAL_PREFIX,
            })?;
        let bytes = URL_SAFE_NO_PAD
            .decode(body)
            .map_err(|e| WireError::Base64(e.to_string()))?;
        let wire: CredentialWire =
            postcard::from_bytes(&bytes).map_err(|e| WireError::Schema(e.to_string()))?;
        if wire.blocks.is_empty() {
            return Err(WireError::Malformed("a credential has at least one block"));
        }
        let blocks = wire
            .blocks
            .iter()
            .map(|b| {
                check_pq_lengths(&b.next_pub_ml_dsa, &b.sig_ml_dsa)?;
                Ok(Block {
                    caveats: b.caveats.clone(),
                    next_pub: b.next_pub,
                    next_pub_ml_dsa: b.next_pub_ml_dsa.clone(),
                    sig: sig64(&b.sig)?,
                    sig_ml_dsa: b.sig_ml_dsa.clone(),
                })
            })
            .collect::<Result<Vec<_>, WireError>>()?;
        let proof = SigningKey::from_bytes(&wire.proof_seed);
        let tail_pub = blocks.last().expect("non-empty checked above").next_pub;
        if proof.verifying_key().to_bytes() != tail_pub {
            return Err(WireError::Malformed(
                "carried proof key does not match the tail block (stripped or reassembled chain)",
            ));
        }
        Ok(Credential {
            nonce: wire.nonce,
            blocks,
            proof,
        })
    }
}

impl Discharge {
    /// Encode to the `dgd1_…` string form.
    pub fn encode(&self) -> String {
        let wire = DischargeWire {
            caveat_id: self.caveat_id.clone(),
            caveats: self.caveats.clone(),
            binding: self.binding,
            sig: self.sig.to_vec(),
        };
        let bytes = postcard::to_stdvec(&wire).expect("discharge encoding is total");
        format!("{DISCHARGE_PREFIX}{}", URL_SAFE_NO_PAD.encode(bytes))
    }

    /// Decode from the `dgd1_…` string form.
    pub fn decode(s: &str) -> Result<Discharge, WireError> {
        let body = s
            .trim()
            .strip_prefix(DISCHARGE_PREFIX)
            .ok_or(WireError::Prefix {
                expected: DISCHARGE_PREFIX,
            })?;
        let bytes = URL_SAFE_NO_PAD
            .decode(body)
            .map_err(|e| WireError::Base64(e.to_string()))?;
        let wire: DischargeWire =
            postcard::from_bytes(&bytes).map_err(|e| WireError::Schema(e.to_string()))?;
        Ok(Discharge::from_parts(
            wire.caveat_id,
            wire.caveats,
            wire.binding,
            sig64(&wire.sig)?,
        ))
    }
}
