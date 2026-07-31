//! **THE EXTERNAL HISTORY ENVELOPE** — the JSON transport a node/relayer serializes a
//! [`crate::WholeChainProof`] into, and a remote verifier (a browser tab, an indexer, a
//! relay) reads.
//!
//! # Why it lives HERE and not in `wasm/`
//!
//! It used to live in `wasm/src/bindings_lightclient.rs`, and the native producer
//! (`lightclient/src/bin/produce_history_envelope.rs`) hand-printed the same JSON with
//! `println!` — a SECOND shape of the same wire format, agreeing by inspection only.
//! Worse, `wasm/` is **excluded from the workspace** (`Cargo.toml`'s `exclude`), so no
//! test of that type ever ran in a workspace green pass. A wire format whose only
//! guard sits in a crate the gates never build is an unguarded wire format.
//!
//! The type is now defined once, here, in the crate that defines what verifying a
//! history MEANS; the wasm bindings and the native producer both use it, and the
//! falsifiers in `lightclient/tests/` run on every `cargo test --workspace`.
//!
//! # What the envelope may carry: only values a verify consumes
//!
//! Through v1 the envelope also carried `genesis_root`, `final_root`, `chain_digest`
//! and `num_turns`. **They were never an argument to any verify.** The verify path
//! passes only `proof_bytes_b64` to [`crate::verify_history_bytes`], and the publics
//! tooth 2 re-attests are the INNER
//! [`dregg_circuit_prove::ivc_turn_chain::WholeChainProofBytes`] publics — a different
//! copy, never compared to the outer one. A producer could set the outer four to
//! anything; the wasm success path happened to render the inner (verified) values, but
//! every OTHER reader of the JSON — an indexer, a relay, a summary rendered before
//! verifying, and the verifier's own refusal arms — was reading unbound producer input
//! and presenting it as a fact about a history.
//!
//! Per greenfield doctrine the second shape is **deleted**, not cross-checked: two
//! shapes that agree today are two shapes that will disagree later. The verified
//! publics are read off the [`crate::AttestedHistory`] a successful verify returns, and
//! nowhere else.
//!
//! `#[serde(deny_unknown_fields)]` makes the deletion enforced at the wire: a v1
//! artifact still carrying those four **refuses to parse** rather than being read with
//! them silently dropped.

use serde::{Deserialize, Serialize};

use crate::{FinalityCert, SignedVote};
use dregg_circuit::field::BabyBear;
use dregg_circuit_prove::ivc_turn_chain::SEG_ANCHOR_WIDTH;

/// The OUTER envelope format version.
///
/// **v2 (2026-07-30)** deleted the four carried publics (`genesis_root` /
/// `final_root` / `chain_digest` / `num_turns`), which were transported and never
/// checked against anything. Combined with `deny_unknown_fields` on
/// [`ExternalHistoryEnvelope`], a v1 artifact now refuses to load twice over — the
/// version pin and the unknown field.
///
/// **Flag day.** Every produced artifact re-emits: `site/light-client/history.json`
/// (regenerate with the `produce_history_envelope` bin), any `deos-view`
/// `ServerSupplied` envelope, and any envelope JSON pasted in a doc. No VK rotation
/// and no re-proving: the proof bytes are byte-identical, only the wrapper changed.
///
/// Independent of the INNER [`dregg_circuit_prove::ivc_turn_chain::WholeChainProofBytes`]
/// version, which is what fail-closes a *proof layout* change.
pub const EXTERNAL_HISTORY_ENVELOPE_VERSION: u32 = 2;

/// The versioned wire envelope. `proof_bytes_b64` is the base64 of the circuit's inner
/// versioned byte envelope, which carries the verify-sufficient subset of the proof
/// (the root `BatchStarkProof`, the binding `Proof`, the publics) — everything the
/// recursion verify reads and nothing of the prover-only `root.1`.
///
/// `vk_fingerprint_hex` rides as the producer's **claim**, never trusted from here: the
/// verifier compares it to its OWN configured anchor for a precise diagnostic, and the
/// real verify re-pins the anchor from the proof bytes regardless.
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ExternalHistoryEnvelope {
    /// Envelope format version. Must equal [`EXTERNAL_HISTORY_ENVELOPE_VERSION`].
    pub version: u32,
    /// The producer's CLAIMED root-circuit VK fingerprint (64 hex chars). NEVER trusted
    /// from the envelope.
    pub vk_fingerprint_hex: String,
    /// Base64 of the proof's inner versioned byte envelope. An empty value fails closed
    /// at verify (there is nothing to cryptographically check).
    #[serde(default)]
    pub proof_bytes_b64: String,
    /// **LC-3 — the finality certificate (artifact side).** The producer's BFT finality
    /// cert over the head root. `None` for a legs-1+2-only envelope, which the finalized
    /// verify then refuses as un-finalized. The verifier checks these votes against its
    /// OWN configured committee (a separate argument, never read from here), so a
    /// fabricated cert by foreign keys is rejected.
    #[serde(default)]
    pub finality_cert: Option<FinalityCertJson>,
}

impl ExternalHistoryEnvelope {
    /// Build the envelope for a proof's wire bytes and its claimed fingerprint. The ONE
    /// constructor — the native producer bin and the wasm producer both go through it,
    /// so there is no second place a field could be filled differently.
    pub fn new(vk_fingerprint_hex: String, proof_bytes_b64: String) -> Self {
        Self {
            version: EXTERNAL_HISTORY_ENVELOPE_VERSION,
            vk_fingerprint_hex,
            proof_bytes_b64,
            finality_cert: None,
        }
    }

    /// Reject an envelope this build does not speak, by version. Returns the precise
    /// refusal naming what changed, so a stale artifact is diagnosable rather than
    /// mysterious.
    pub fn check_version(&self) -> Result<(), String> {
        if self.version == EXTERNAL_HISTORY_ENVELOPE_VERSION {
            return Ok(());
        }
        Err(format!(
            "unsupported envelope version {} (this client speaks \
             v{EXTERNAL_HISTORY_ENVELOPE_VERSION}). v1 carried four publics that were never \
             checked against anything; they are DELETED, and a v1 artifact is refused rather \
             than read with them silently dropped. Re-emit the envelope from the same fold — \
             no re-proving, no VK rotation.",
            self.version
        ))
    }
}

/// A finality certificate as it rides in the [`ExternalHistoryEnvelope`]. The verifier
/// reconstructs a [`FinalityCert`] from it and checks it against the client's CONFIG
/// committee — the keys here are the producer's claim, never trusted on their own.
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct FinalityCertJson {
    /// The ratifying votes.
    pub votes: Vec<FinalityVoteJson>,
    /// The group size the producer claims the supermajority was taken over — DIAGNOSTIC
    /// ONLY. The verifier anchors the threshold to its OWN committee size, never this.
    pub participant_count: usize,
    /// The FULL 8-felt wide head state root the cert claims a quorum finalized. Must
    /// equal the aggregate's byte-verified 8-felt final anchor for the seam to bind —
    /// ALL lanes are compared and ALL lanes are inside each vote's signed message (a
    /// lane-0-only `u32` here was the ~31-bit finality-substitution hole).
    pub finalized_root: [u32; SEG_ANCHOR_WIDTH],
}

/// One ratification vote in a [`FinalityCertJson`].
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct FinalityVoteJson {
    /// The validator's Ed25519 verifying key (64 hex chars / 32 bytes).
    pub validator_hex: String,
    /// The Ed25519 signature over `finality_signing_message(finalized_root,
    /// participant_count)` (128 hex chars / 64 bytes).
    pub signature_hex: String,
    /// The voter's ML-DSA-65 public key (FIPS 204, 1952 bytes → 3904 hex chars), carried
    /// SELF-CONTAINED so the post-quantum half is re-verifiable with no committee PQ-key
    /// history. `#[serde(default)]` so a legacy classical-only vote still parses; it then
    /// reconstructs an empty PQ half, which the hybrid gate REJECTS (fail-closed — never
    /// a silent ed25519-only accept).
    #[serde(default)]
    pub ml_dsa_pubkey_hex: String,
    /// The ML-DSA-65 signature over the SAME message the Ed25519 half signs, bound to
    /// [`crate::HYBRID_PQ_CTX`]. `#[serde(default)]`; a missing/empty half fails closed.
    #[serde(default)]
    pub pq_signature_hex: String,
}

impl FinalityCertJson {
    /// Reconstruct a verifiable [`FinalityCert`] from the wire form (hex-decoding each
    /// vote). A present-but-malformed hex string is a hard error, never a silent drop;
    /// an ABSENT PQ half decodes to an empty `Vec`, which the hybrid gate rejects.
    pub fn reconstruct(&self) -> Result<FinalityCert, String> {
        let mut votes = Vec::with_capacity(self.votes.len());
        for v in &self.votes {
            votes.push(SignedVote {
                validator: parse_hex32(&v.validator_hex)
                    .map_err(|e| format!("validator key: {e}"))?,
                signature: parse_hex64(&v.signature_hex).map_err(|e| format!("signature: {e}"))?,
                ml_dsa_pubkey: parse_hex_var(&v.ml_dsa_pubkey_hex)
                    .map_err(|e| format!("ml-dsa pk: {e}"))?,
                pq_signature: parse_hex_var(&v.pq_signature_hex)
                    .map_err(|e| format!("pq sig: {e}"))?,
            });
        }
        Ok(FinalityCert {
            votes,
            participant_count: self.participant_count,
            finalized_root: core::array::from_fn(|i| BabyBear::new(self.finalized_root[i])),
        })
    }
}

/// Parse a 64-char hex string into a `[u8; 32]` — the one hex→anchor decoder every
/// config-anchor entry point shares. Rejects wrong length / non-hex with a precise
/// message, so a fat-fingered anchor is a clear error and never a silent zero-fill (a
/// zero anchor would be a real fingerprint a forger could target).
pub fn parse_hex32(s: &str) -> Result<[u8; 32], String> {
    let s = s.trim();
    let s = s.strip_prefix("0x").unwrap_or(s);
    if s.len() != 64 {
        return Err(format!("expected 64 hex chars (32 bytes), got {}", s.len()));
    }
    let mut out = [0u8; 32];
    for (i, byte) in out.iter_mut().enumerate() {
        let hi = hex_nibble(s.as_bytes()[2 * i])?;
        let lo = hex_nibble(s.as_bytes()[2 * i + 1])?;
        *byte = (hi << 4) | lo;
    }
    Ok(out)
}

/// Parse a 128-char hex string into a `[u8; 64]` (an Ed25519 signature).
pub fn parse_hex64(s: &str) -> Result<[u8; 64], String> {
    let s = s.trim();
    let s = s.strip_prefix("0x").unwrap_or(s);
    if s.len() != 128 {
        return Err(format!(
            "expected 128 hex chars (64 bytes), got {}",
            s.len()
        ));
    }
    let mut out = [0u8; 64];
    for (i, byte) in out.iter_mut().enumerate() {
        let hi = hex_nibble(s.as_bytes()[2 * i])?;
        let lo = hex_nibble(s.as_bytes()[2 * i + 1])?;
        *byte = (hi << 4) | lo;
    }
    Ok(out)
}

/// Decode a variable-length hex string (optional `0x` prefix) to bytes. An EMPTY string
/// decodes to an empty `Vec` — the "PQ half absent" sentinel the hybrid gate rejects
/// fail-closed. An odd length or a non-hex character is a hard error, never a silent
/// truncation.
pub fn parse_hex_var(s: &str) -> Result<Vec<u8>, String> {
    let s = s.trim();
    let s = s.strip_prefix("0x").unwrap_or(s);
    if s.is_empty() {
        return Ok(Vec::new());
    }
    if s.len() % 2 != 0 {
        return Err(format!(
            "expected an even number of hex chars, got {}",
            s.len()
        ));
    }
    let mut out = Vec::with_capacity(s.len() / 2);
    for pair in s.as_bytes().chunks_exact(2) {
        out.push((hex_nibble(pair[0])? << 4) | hex_nibble(pair[1])?);
    }
    Ok(out)
}

/// Hex-encode bytes (lowercase) — the inverse of [`parse_hex_var`].
pub fn to_hex(bytes: &[u8]) -> String {
    use core::fmt::Write as _;
    let mut s = String::with_capacity(bytes.len() * 2);
    for b in bytes {
        let _ = write!(s, "{b:02x}");
    }
    s
}

fn hex_nibble(c: u8) -> Result<u8, String> {
    match c {
        b'0'..=b'9' => Ok(c - b'0'),
        b'a'..=b'f' => Ok(c - b'a' + 10),
        b'A'..=b'F' => Ok(c - b'A' + 10),
        other => Err(format!("non-hex character '{}'", other as char)),
    }
}
