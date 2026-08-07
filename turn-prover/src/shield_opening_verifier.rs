//! The production [`ShieldOpeningVerifier`] — the MINT half of the shielded
//! on-ramp ([`dregg_turn::action::Effect::Shield`]), over `dregg-circuit-prove`.
//!
//! This is the PROVER half of the seam described in `dregg_turn::shielded_verifier`.
//! It is deliberately VERIFY-RETURNS-VALUE: it receives the wire public fields plus
//! the proof bytes, reconstructs the shield-opening claim, runs the relation, and
//! returns the proven `(value, asset, note_commitment)`. It has no access to the
//! `LedgerJournal`, the `Ledger`, or the `TurnExecutor` — the core `apply_shield`
//! path performs (and journals) the debit and the accumulator append.
//!
//! **The AIR is AUTHORED IN LEAN.** This crate only CALLS
//! `dregg_circuit_prove::shielded::shield_opening::verify_shield_opening`, which
//! reads the byte-pinned Lean golden `dregg-shielded-shield::v1`
//! (`metatheory/Dregg2/Circuit/Emit/ShieldedShieldDescriptor.lean`, proven
//! `shield_opening_binds_public_value` / `shield_value_decouple_unsat`). It authors
//! no constraint. Nothing here is `#[cfg]`'d: this crate IS the prover, so a shape
//! change in `dregg-circuit-prove` or in `dregg_turn::action` is a compile error
//! HERE, at the source.

use dregg_circuit::field::{BABYBEAR_P, BabyBear};
use dregg_circuit_prove::shielded::shield_opening::{
    ShieldOpeningClaim, ShieldOpeningError, ShieldOpeningProof, verify_shield_opening,
};
use dregg_turn::error::TurnError;
use dregg_turn::shielded_verifier::{ShieldOpeningVerifier, VerifiedShieldOpening};

/// The real shield-opening verifier. Inject with
/// [`dregg_turn::executor::TurnExecutor::set_shield_opening_verifier`].
#[derive(Clone, Copy, Debug, Default)]
pub struct CircuitShieldOpeningVerifier;

impl CircuitShieldOpeningVerifier {
    pub const fn new() -> Self {
        Self
    }
}

fn invalid(reason: String) -> TurnError {
    TurnError::InvalidEffect { reason }
}

/// The u64 → BabyBear canonical narrowing for a public on-ramp value/asset. The
/// shield-opening relation represents value and asset as SINGLE BabyBear lanes, so
/// the on-ramp is (today) bounded to canonical field values. A `>= p` value is a
/// non-canonical public field and REJECTS — the wide-value on-ramp is the follow-up
/// pass, never a silent truncation here.
fn canonical_felt(v: u64, what: &str) -> Result<BabyBear, TurnError> {
    if v >= BABYBEAR_P as u64 {
        return Err(invalid(format!(
            "shield {what}={v} is not a canonical BabyBear field value (>= p); the on-ramp \
             represents it as one lane — the wide-value on-ramp is the follow-up pass"
        )));
    }
    Ok(BabyBear::new(v as u32))
}

/// Recover the note-commitment felt from its canonical `cell::felt_to_bytes32`
/// encoding: the low 4 bytes are the felt (canonical `< p`), the high 28 MUST be
/// zero. A non-canonical encoding rejects rather than silently truncating.
fn commitment_felt(bytes: [u8; 32]) -> Result<BabyBear, TurnError> {
    if bytes[4..].iter().any(|&b| b != 0) {
        return Err(invalid(
            "shield note_commitment is not a canonical single-felt encoding (high bytes nonzero)"
                .into(),
        ));
    }
    let raw = u32::from_le_bytes([bytes[0], bytes[1], bytes[2], bytes[3]]);
    if raw >= BABYBEAR_P {
        return Err(invalid(
            "shield note_commitment low lane is not a canonical BabyBear field value".into(),
        ));
    }
    Ok(BabyBear::new(raw))
}

impl ShieldOpeningVerifier for CircuitShieldOpeningVerifier {
    fn verify(
        &self,
        value: u64,
        asset_type: u64,
        note_commitment: [u8; 32],
        shield_proof: &[u8],
    ) -> Result<VerifiedShieldOpening, TurnError> {
        // Reconstruct the PUBLIC claim from the wire fields — never from anything
        // embedded in the proof bytes. A claim decoupled from the proof rejects
        // inside `verify_shield_opening` (the `.piBinding`s force the proven cells,
        // Lean `shield_value_decouple_unsat`), which is exactly the mint-worth-more
        // refusal `apply_shield` relies on.
        let claim = ShieldOpeningClaim {
            value: canonical_felt(value, "value")?,
            asset: canonical_felt(asset_type, "asset_type")?,
            note_commitment: commitment_felt(note_commitment)?,
        };

        // Deserialize the hiding IR-v2 batch proof (postcard — the same
        // `Ir2BatchProof` wire form the `wide_value_binding` sidecar uses).
        let proof = ShieldOpeningProof {
            claim,
            proof: postcard::from_bytes(shield_proof)
                .map_err(|e| invalid(format!("shield-opening proof malformed: {e}")))?,
        };

        verify_shield_opening(&proof).map_err(|e| match e {
            ShieldOpeningError::StatementRejected { reason } => {
                invalid(format!("shield-opening statement rejected: {reason}"))
            }
            ShieldOpeningError::VerifyFailed { reason } => {
                invalid(format!("shield-opening verification failed: {reason}"))
            }
            ShieldOpeningError::ProveFailed { reason } => invalid(format!(
                "shield-opening prove-path error surfaced at verify: {reason}"
            )),
        })?;

        // Both gates passed. Return the PROVEN public data — equal to the wire
        // fields, since the claim was reconstructed from them and verify accepted.
        Ok(VerifiedShieldOpening {
            value,
            asset_type,
            note_commitment,
        })
    }
}
