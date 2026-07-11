//! gnark witness export — ETH-NATIVE-WRAP milestone 1 (Rust → gnark JSON).
//!
//! A **pure-serialization** exporter that projects a verify-sufficient
//! [`WholeChainProofBytes`] envelope plus a caller-held [`RecursionVk`] trust
//! anchor into the JSON witness file the gnark wrap circuit (`chain/gnark/`)
//! consumes, and a **Fiat-Shamir transcript fixture** emitter so the Go side
//! can validate its Poseidon2 duplex sponge byte-for-byte against the exact
//! challenger the Rust verifier runs
//! ([`DuplexChallenger`]`<BabyBear, Poseidon2BabyBear<16>, 16, 8>` — the
//! `Challenger` type of `plonky3_recursion_impl::recursive`).
//!
//! ## The 25-lane public-input contract (pinned)
//!
//! Both EVM lanes (this exporter and the gnark circuit / Solidity ABI) MUST
//! agree exactly:
//!
//! ```text
//! order  = genesis_root[0..8] ++ final_root[0..8] ++ num_turns ++ chain_digest[0..8]
//! len    = 25
//! domain = every value is a CANONICAL BabyBear residue, i.e. < 0x78000001
//! ABI    = (uint32[8] genesisRoot, uint32[8] finalRoot, uint32 numTurns, uint32[8] chainDigest)
//! ```
//!
//! This is byte-identical to the host segment tooth's expected vector
//! (`verify_turn_chain_recursive_from_parts`, `ivc_turn_chain.rs`): the tooth
//! builds `[genesis_root8, final_root8, BabyBear::new(num_turns as u32),
//! chain_digest8]` and compares it against the root's `expose_claim` table.
//!
//! ## Fail-closed validation
//!
//! The exporter REFUSES (never clamps, never reduces):
//! - an envelope whose `version` is not [`WHOLE_CHAIN_PROOF_ENVELOPE_V1`],
//! - any lane `>= 2013265921` (`0x78000001`, the BabyBear modulus) in
//!   `genesis_root` / `final_root` / `chain_digest`,
//! - a `num_turns` that is not itself a canonical BabyBear residue (this is
//!   STRICTER than "fits u32": the host tooth embeds the count as a single
//!   BabyBear lane via `BabyBear::new(num_turns as u32)`, so a count `>= p`
//!   would silently wrap in the field — refused here instead),
//! - an empty `root_proof` (nothing for the gnark circuit to verify).
//!
//! ## Dependency note
//!
//! JSON is emitted by hand (this crate deliberately has no `serde_json` in
//! its non-dev dependency set). Every emitted string is machine-generated
//! (`[0-9a-f]` hex or decimal digits) so no JSON escaping is ever required;
//! the teeth test parses the output with real `serde_json` (a dev-dep) to
//! prove it is well-formed.

use core::fmt;

use p3_baby_bear::{BabyBear as P3BabyBear, Poseidon2BabyBear, default_babybear_poseidon2_16};
use p3_challenger::{CanObserve, CanSample, DuplexChallenger};
use p3_field::{PrimeCharacteristicRing, PrimeField32};

use crate::ivc_turn_chain::{
    SEG_ANCHOR_WIDTH, SEG_DIGEST_WIDTH, WHOLE_CHAIN_PROOF_ENVELOPE_V1, WholeChainProofBytes,
};
use crate::plonky3_recursion_impl::recursive::RecursionVk;

/// The BabyBear prime modulus `p = 2^31 - 2^27 + 1 = 2013265921`. A public-input
/// lane is canonical iff it is strictly below this. (The teeth test pins this
/// constant against `P3BabyBear::ORDER_U32` so it can never drift from the field.)
pub const BABYBEAR_MODULUS: u32 = 0x7800_0001;

/// The pinned public-input vector length:
/// `genesis_root(8) ++ final_root(8) ++ num_turns(1) ++ chain_digest(8)`.
pub const GNARK_PUBLIC_INPUT_LEN: usize = 2 * SEG_ANCHOR_WIDTH + 1 + SEG_DIGEST_WIDTH;

/// The version tag of the emitted gnark witness JSON format itself (bumped on
/// any layout change of the JSON, independent of the wire envelope version).
pub const GNARK_WITNESS_FORMAT_VERSION: u32 = 1;

/// A fail-closed export refusal. Every variant is a REJECT — the exporter
/// never clamps, reduces, or truncates a value into range.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum GnarkWitnessExportError {
    /// The envelope's wire version is not the one this exporter understands.
    UnsupportedEnvelopeVersion { found: u16, expected: u16 },
    /// A public-input lane is not a canonical BabyBear residue (`>= p`).
    NonCanonicalLane {
        field: &'static str,
        index: usize,
        value: u32,
    },
    /// `num_turns` is not a canonical BabyBear residue. The host tooth embeds
    /// the count as ONE BabyBear lane, so `num_turns >= p` (which includes
    /// everything above `u32::MAX`) would wrap in-field; refused instead.
    NumTurnsNotCanonical { value: u64 },
    /// The envelope carries no root proof bytes — nothing to wrap.
    EmptyRootProof,
}

impl fmt::Display for GnarkWitnessExportError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::UnsupportedEnvelopeVersion { found, expected } => write!(
                f,
                "unsupported WholeChainProofBytes envelope version {found} (exporter understands {expected})"
            ),
            Self::NonCanonicalLane {
                field,
                index,
                value,
            } => write!(
                f,
                "non-canonical BabyBear lane {field}[{index}] = {value} (must be < {BABYBEAR_MODULUS})"
            ),
            Self::NumTurnsNotCanonical { value } => write!(
                f,
                "num_turns = {value} is not a canonical BabyBear residue (must be < {BABYBEAR_MODULUS}); refusing to wrap"
            ),
            Self::EmptyRootProof => write!(f, "envelope carries an empty root_proof"),
        }
    }
}

impl std::error::Error for GnarkWitnessExportError {}

/// Validate the envelope's public lanes and assemble the pinned 25-lane
/// public-input vector: `genesis_root ++ final_root ++ num_turns ++ chain_digest`.
///
/// Fail-closed: any non-canonical lane (>= [`BABYBEAR_MODULUS`]) or
/// non-canonical `num_turns` is an error, never clamped.
pub fn gnark_public_input_vector(
    env: &WholeChainProofBytes,
) -> Result<[u32; GNARK_PUBLIC_INPUT_LEN], GnarkWitnessExportError> {
    fn check_lanes(field: &'static str, lanes: &[u32]) -> Result<(), GnarkWitnessExportError> {
        for (index, &value) in lanes.iter().enumerate() {
            if value >= BABYBEAR_MODULUS {
                return Err(GnarkWitnessExportError::NonCanonicalLane {
                    field,
                    index,
                    value,
                });
            }
        }
        Ok(())
    }

    check_lanes("genesis_root", &env.genesis_root)?;
    check_lanes("final_root", &env.final_root)?;
    check_lanes("chain_digest", &env.chain_digest)?;
    if env.num_turns >= BABYBEAR_MODULUS as u64 {
        return Err(GnarkWitnessExportError::NumTurnsNotCanonical {
            value: env.num_turns,
        });
    }

    let mut v = [0u32; GNARK_PUBLIC_INPUT_LEN];
    v[..SEG_ANCHOR_WIDTH].copy_from_slice(&env.genesis_root);
    v[SEG_ANCHOR_WIDTH..2 * SEG_ANCHOR_WIDTH].copy_from_slice(&env.final_root);
    v[2 * SEG_ANCHOR_WIDTH] = env.num_turns as u32;
    v[2 * SEG_ANCHOR_WIDTH + 1..].copy_from_slice(&env.chain_digest);
    Ok(v)
}

/// Export a [`WholeChainProofBytes`] envelope + the caller-held [`RecursionVk`]
/// anchor as the gnark witness JSON document.
///
/// Layout (all keys always present, in this order):
///
/// ```json
/// {
///   "version": 1,                      // GNARK_WITNESS_FORMAT_VERSION
///   "envelope_version": 3,             // the wire envelope version (v3)
///   "vk_anchor_hex": "…64 hex…",       // the caller-held TRUSTED anchor
///   "claimed_vk_fingerprint_hex": "…", // the envelope's untrusted claim (diagnostic only)
///   "publics": {
///     "genesis_root": [8 × u32],
///     "final_root":   [8 × u32],
///     "num_turns":    u32,
///     "chain_digest": [8 × u32]
///   },
///   "public_input_vector": [25 decimal strings],  // the pinned order
///   "root_proof_hex": "…"              // postcard bytes of the root BatchStarkProof
/// }
/// ```
///
/// `public_input_vector` is emitted as DECIMAL STRINGS (not JSON numbers) so
/// the Go side can feed them to `big.Int.SetString` without any float-parsing
/// hazard; `publics.*` carries the same values as plain u32 numbers for
/// human/diagnostic use. The two are generated from one validated vector, so
/// they cannot disagree.
pub fn export_gnark_witness_json(
    env: &WholeChainProofBytes,
    vk_anchor: &RecursionVk,
) -> Result<String, GnarkWitnessExportError> {
    if env.version != WHOLE_CHAIN_PROOF_ENVELOPE_V1 {
        return Err(GnarkWitnessExportError::UnsupportedEnvelopeVersion {
            found: env.version,
            expected: WHOLE_CHAIN_PROOF_ENVELOPE_V1,
        });
    }
    if env.root_proof.is_empty() {
        return Err(GnarkWitnessExportError::EmptyRootProof);
    }
    let vector = gnark_public_input_vector(env)?;

    let mut out = String::with_capacity(env.root_proof.len() * 2 + 4096);
    out.push_str("{\n");
    out.push_str(&format!("  \"version\": {GNARK_WITNESS_FORMAT_VERSION},\n"));
    out.push_str(&format!("  \"envelope_version\": {},\n", env.version));
    out.push_str(&format!(
        "  \"vk_anchor_hex\": \"{}\",\n",
        vk_anchor.to_hex()
    ));
    // The envelope's own claimed fingerprint is NEVER trusted (the verifier
    // recomputes it from root_proof); carried for the mismatch diagnostic only.
    // It is producer-controlled text, so it is emitted defensively: hex chars
    // only, anything else replaced (never interpolated raw into JSON).
    let claimed: String = env
        .vk_fingerprint_hex
        .chars()
        .map(|c| if c.is_ascii_hexdigit() { c } else { '?' })
        .collect();
    out.push_str(&format!(
        "  \"claimed_vk_fingerprint_hex\": \"{claimed}\",\n"
    ));
    out.push_str("  \"publics\": {\n");
    out.push_str(&format!(
        "    \"genesis_root\": {},\n",
        json_u32_array(&env.genesis_root)
    ));
    out.push_str(&format!(
        "    \"final_root\": {},\n",
        json_u32_array(&env.final_root)
    ));
    out.push_str(&format!("    \"num_turns\": {},\n", env.num_turns as u32));
    out.push_str(&format!(
        "    \"chain_digest\": {}\n",
        json_u32_array(&env.chain_digest)
    ));
    out.push_str("  },\n");
    out.push_str(&format!(
        "  \"public_input_vector\": {},\n",
        json_decimal_string_array(&vector)
    ));
    out.push_str(&format!(
        "  \"root_proof_hex\": \"{}\"\n",
        hex_encode(&env.root_proof)
    ));
    out.push_str("}\n");
    Ok(out)
}

// ============================================================================
// Fiat-Shamir transcript fixture (chain/gnark/fixtures/transcript_w16.json)
// ============================================================================

/// Number of base-field elements absorbed by the fixture protocol: the byte
/// values `0..16` (i.e. `0, 1, …, 15`), each lifted to a BabyBear element.
/// 16 = 2 × RATE, so the observe phase performs EXACTLY two duplexing
/// permutations.
pub const TRANSCRIPT_FIXTURE_ABSORB_COUNT: usize = 16;

/// Number of base-field challenges squeezed by the fixture protocol.
pub const TRANSCRIPT_FIXTURE_SQUEEZE_COUNT: usize = 8;

/// The deterministic transcript fixture: the exact absorb/squeeze run of the
/// verifier's challenger, with the final sponge state exposed for lane-level
/// diagnostics on the Go side.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TranscriptFixtureW16 {
    /// The absorbed inputs, as canonical residues (here simply `0..=15`).
    pub absorbed: [u32; TRANSCRIPT_FIXTURE_ABSORB_COUNT],
    /// The 8 squeezed challenges, canonical residues, in sample order.
    pub challenges: [u32; TRANSCRIPT_FIXTURE_SQUEEZE_COUNT],
    /// The full 16-lane sponge state after the final permutation. Because the
    /// squeeze pops from the END of the rate-prefix output buffer,
    /// `challenges[i] == final_sponge_state[RATE - 1 - i]`.
    pub final_sponge_state: [u32; 16],
}

/// Run the fixture protocol on the REAL verifier challenger
/// (`DuplexChallenger<BabyBear, Poseidon2BabyBear<16>, WIDTH=16, RATE=8>` built
/// over `default_babybear_poseidon2_16()` — imported, not re-implemented).
///
/// Protocol (documented identically in the emitted JSON):
/// 1. Fresh challenger: `sponge_state = [0; 16]`, empty input/output buffers.
/// 2. `observe(BabyBear::from(b))` for `b = 0, 1, …, 15`. Each observe pushes
///    into the input buffer; when the buffer holds RATE=8 elements a duplexing
///    fires: the buffered 8 OVERWRITE `state[0..8]` (capacity `state[8..16]`
///    untouched), the Poseidon2 width-16 permutation is applied, and the
///    output buffer is refilled with `state[0..8]`. 16 observes ⇒ exactly two
///    permutations.
/// 3. `sample()` × 8 (base-field). Each sample POPS FROM THE END of the output
///    buffer, so `challenges[0] = state[7]`, `challenges[1] = state[6]`, …,
///    `challenges[7] = state[0]` (state = post-second-permutation). No third
///    permutation fires.
pub fn transcript_fixture_w16() -> TranscriptFixtureW16 {
    let perm = default_babybear_poseidon2_16();
    let mut challenger: DuplexChallenger<P3BabyBear, Poseidon2BabyBear<16>, 16, 8> =
        DuplexChallenger::new(perm);

    let mut absorbed = [0u32; TRANSCRIPT_FIXTURE_ABSORB_COUNT];
    for (b, slot) in absorbed.iter_mut().enumerate() {
        *slot = b as u32;
        challenger.observe(P3BabyBear::from_u8(b as u8));
    }

    let mut challenges = [0u32; TRANSCRIPT_FIXTURE_SQUEEZE_COUNT];
    for c in challenges.iter_mut() {
        let sampled: P3BabyBear = challenger.sample();
        *c = sampled.as_canonical_u32();
    }

    let final_sponge_state = challenger.sponge_state.map(|x| x.as_canonical_u32());

    TranscriptFixtureW16 {
        absorbed,
        challenges,
        final_sponge_state,
    }
}

/// Render [`transcript_fixture_w16`] as the `transcript_w16.json` fixture
/// document (deterministic, byte-stable output).
pub fn transcript_fixture_w16_json() -> String {
    let fx = transcript_fixture_w16();
    let mut out = String::with_capacity(4096);
    out.push_str("{\n");
    out.push_str("  \"description\": \"Fiat-Shamir transcript fixture: the EXACT challenger the dregg Rust verifier uses (p3_challenger::DuplexChallenger<BabyBear, Poseidon2BabyBear<16>, WIDTH=16, RATE=8> over Plonky3 default_babybear_poseidon2_16). Protocol: (1) fresh challenger, sponge_state = [0; 16]; (2) observe the byte values 0..16 as field elements, in order - each observe buffers one input, and when 8 are buffered a duplexing fires: the 8 buffered inputs OVERWRITE state[0..8] (capacity state[8..16] untouched), the Poseidon2 width-16 permutation is applied, and the output buffer becomes state[0..8]; 16 observes = exactly two permutations; (3) sample 8 base-field challenges - each sample POPS FROM THE END of the output buffer, so challenges[i] = final_sponge_state[7 - i]; no third permutation fires. All values are canonical decimal residues below the modulus.\",\n");
    out.push_str("  \"field\": \"BabyBear\",\n");
    out.push_str(&format!("  \"modulus\": \"{BABYBEAR_MODULUS}\",\n"));
    out.push_str(
        "  \"permutation\": \"Poseidon2 width-16 (Plonky3 default_babybear_poseidon2_16, workspace-pinned rev 82cfad73cd734d37a0d51953094f970c531817ec)\",\n",
    );
    out.push_str("  \"width\": 16,\n");
    out.push_str("  \"rate\": 8,\n");
    out.push_str(&format!(
        "  \"absorbed\": {},\n",
        json_decimal_string_array(&fx.absorbed)
    ));
    out.push_str(&format!(
        "  \"challenges\": {},\n",
        json_decimal_string_array(&fx.challenges)
    ));
    out.push_str(&format!(
        "  \"final_sponge_state\": {}\n",
        json_decimal_string_array(&fx.final_sponge_state)
    ));
    out.push_str("}\n");
    out
}

// ============================================================================
// Tiny dependency-free emit helpers (values are digits/hex only — no escaping)
// ============================================================================

fn json_u32_array(vals: &[u32]) -> String {
    let body: Vec<String> = vals.iter().map(|v| v.to_string()).collect();
    format!("[{}]", body.join(", "))
}

fn json_decimal_string_array(vals: &[u32]) -> String {
    let body: Vec<String> = vals.iter().map(|v| format!("\"{v}\"")).collect();
    format!("[{}]", body.join(", "))
}

fn hex_encode(bytes: &[u8]) -> String {
    let mut s = String::with_capacity(bytes.len() * 2);
    for b in bytes {
        s.push_str(&format!("{b:02x}"));
    }
    s
}
