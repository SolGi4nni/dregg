//! Real selective-disclosure proofs for `/credential verify` — wiring the SDK's
//! `AgentCipherclerk::prove_predicate_unlinkable` (`sdk/src/privacy.rs:413`).
//!
//! The bot previously emitted `cryptographic_proof: null` for a verify request
//! (the toy finding in `docs/MATURATION-LEDGER.md` Theme 5). This module closes
//! that: it parses a predicate string (`"age>=18"`), reads the subject's attribute
//! value out of their held credential, reconstructs the subject's REAL
//! [`AgentCipherclerk`] from the bot's custodial seed, and produces a genuine
//! **unlinkable predicate STARK proof** — the same circuit the SDK's own tests
//! exercise.
//!
//! ## Why the bot may prove on the subject's behalf
//!
//! The bot is a **custodial** front: every Discord user's cclerk is deterministic
//! from `BLAKE3_derive_key("dregg-discord-bot-v1", bot_secret || discord_id)` (see
//! `cipherclerk.rs`). So the bot holds the subject's key material and can act as
//! their holder to generate a selective-disclosure proof — exactly as a
//! self-custody holder would on their own device. The proof is **unlinkable**: a
//! fresh blinding factor per call means two proofs about the same attribute do not
//! correlate (the `prove_predicate_unlinkable` guarantee).
//!
//! ## What the proof shows / hides
//!
//! - **shows the verifier:** that the subject's attribute satisfies the predicate
//!   (e.g. `age >= 18`) + the blinded fact commitment (unique per proof).
//! - **hides:** the actual attribute value, which credential produced it, and any
//!   correlation with other proofs.

use dregg_circuit::{BabyBear, PredicateType};
use dregg_sdk::AgentCipherclerk;
use dregg_sdk::privacy::UnlinkablePredicateProof;
use zeroize::Zeroizing;

/// A parsed predicate over a credential attribute, e.g. `age >= 18`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ParsedPredicate {
    /// The attribute name (e.g. `"age"`, `"balance"`).
    pub attribute: String,
    /// The comparator.
    pub predicate_type: PredicateType,
    /// The threshold the attribute is compared against.
    pub threshold: u32,
}

/// Why a predicate string could not be parsed into a [`ParsedPredicate`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PredicateParseError {
    /// No comparator (`>=`, `<=`, `>`, `<`, `!=`) was found in the string.
    NoComparator,
    /// The attribute name (left of the comparator) was empty.
    EmptyAttribute,
    /// The threshold (right of the comparator) was not a non-negative integer.
    BadThreshold(String),
    /// The comparator is not one the predicate circuit supports (e.g. `==`, which
    /// has no `PredicateType` — only `Gte`/`Lte`/`Gt`/`Lt`/`Neq` exist).
    UnsupportedComparator(String),
}

impl std::fmt::Display for PredicateParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PredicateParseError::NoComparator => write!(
                f,
                "no comparator found — use one of `>=`, `<=`, `>`, `<`, `!=` (e.g. `age>=18`)"
            ),
            PredicateParseError::EmptyAttribute => {
                write!(f, "the attribute name (left of the comparator) is empty")
            }
            PredicateParseError::BadThreshold(s) => {
                write!(f, "the threshold `{s}` is not a non-negative integer")
            }
            PredicateParseError::UnsupportedComparator(c) => write!(
                f,
                "the comparator `{c}` is not supported by the predicate circuit \
                 (supported: `>=`, `<=`, `>`, `<`, `!=`)"
            ),
        }
    }
}

impl std::error::Error for PredicateParseError {}

/// Parse a predicate string like `"age>=18"` (or `"age >= 18"`) into its
/// attribute, comparator, and threshold.
///
/// The comparator search is order-sensitive: two-char comparators (`>=`, `<=`,
/// `!=`) are tried before the one-char ones (`>`, `<`), so `age>=18` parses as
/// `Gte(18)`, not `Gt(=18)`. `==` is rejected ([`PredicateParseError::UnsupportedComparator`])
/// because the predicate circuit has no equality `PredicateType` (only `Neq`).
pub fn parse_predicate(input: &str) -> Result<ParsedPredicate, PredicateParseError> {
    // Two-char comparators first (so `>=` wins over `>`).
    const TWO: &[(&str, PredicateType)] = &[
        (">=", PredicateType::Gte),
        ("<=", PredicateType::Lte),
        ("!=", PredicateType::Neq),
    ];
    const ONE: &[(&str, PredicateType)] = &[(">", PredicateType::Gt), ("<", PredicateType::Lt)];

    // Reject `==` explicitly with a precise error (it has no PredicateType).
    if input.contains("==") {
        return Err(PredicateParseError::UnsupportedComparator("==".to_string()));
    }

    for (op, ty) in TWO.iter().chain(ONE.iter()) {
        if let Some(idx) = input.find(op) {
            let attribute = input[..idx].trim().to_string();
            let rhs = input[idx + op.len()..].trim();
            if attribute.is_empty() {
                return Err(PredicateParseError::EmptyAttribute);
            }
            let threshold = rhs
                .parse::<u32>()
                .map_err(|_| PredicateParseError::BadThreshold(rhs.to_string()))?;
            return Ok(ParsedPredicate {
                attribute,
                predicate_type: *ty,
                threshold,
            });
        }
    }
    Err(PredicateParseError::NoComparator)
}

/// Extract the integer value of `attribute` from a credential's `attributes_json`
/// (e.g. `{"age": 25}` → `25`). Accepts a JSON number or a numeric string value.
/// Returns `None` if the attribute is absent or non-numeric.
pub fn attribute_value(attributes_json: &str, attribute: &str) -> Option<u32> {
    let value: serde_json::Value = serde_json::from_str(attributes_json).ok()?;
    let field = value.get(attribute)?;
    if let Some(n) = field.as_u64() {
        return u32::try_from(n).ok();
    }
    // Tolerate a string-encoded number (e.g. `{"age": "25"}`).
    field.as_str().and_then(|s| s.trim().parse::<u32>().ok())
}

/// Why generating a real selective-disclosure proof failed.
#[derive(Debug)]
pub enum ProofError {
    /// The predicate string could not be parsed.
    Parse(PredicateParseError),
    /// The credential's `attributes_json` has no numeric value for the predicate's
    /// attribute (so there is nothing to prove the predicate about).
    AttributeMissing {
        /// The attribute the predicate referenced.
        attribute: String,
    },
    /// The SDK refused to produce the proof — most commonly because the predicate
    /// is FALSE for the subject's value (e.g. proving `age>=21` when `age=18`): the
    /// circuit is sound, so a false statement is unprovable. Carries the SDK error.
    Sdk(dregg_sdk::SdkError),
}

impl std::fmt::Display for ProofError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ProofError::Parse(e) => write!(f, "predicate parse failed: {e}"),
            ProofError::AttributeMissing { attribute } => write!(
                f,
                "the matched credential has no numeric `{attribute}` attribute to prove the predicate about"
            ),
            ProofError::Sdk(e) => write!(
                f,
                "selective-disclosure proof generation refused (the predicate may be FALSE for the subject's attribute, which is unprovable): {e}"
            ),
        }
    }
}

impl std::error::Error for ProofError {}

/// A generated selective-disclosure proof, ready to render in a Discord embed +
/// persist as the (no-longer-null) presentation cryptographic material.
#[derive(Debug)]
pub struct GeneratedProof {
    /// The parsed predicate this proof attests.
    pub predicate: ParsedPredicate,
    /// The REAL unlinkable predicate proof (STARK-backed, freshly blinded).
    pub proof: UnlinkablePredicateProof,
}

impl GeneratedProof {
    /// The blinded fact commitment as hex (unique per proof — the unlinkability
    /// witness; rendered in the embed so two proofs are visibly distinct).
    pub fn blinded_commitment_hex(&self) -> String {
        babybear_hex(self.proof.blinded_fact_commitment)
    }

    /// A compact, non-secret JSON description of the proof for the presentation
    /// store — replaces the old `cryptographic_proof: null` with a REAL artifact
    /// summary (the blinded commitment + the predicate + the proof type). The full
    /// STARK proof is large + binary; this is the durable receipt that a real proof
    /// WAS produced, with the public commitment a verifier re-binds.
    pub fn presentation_json(&self, subject_cell: &str) -> String {
        serde_json::json!({
            "type": "unlinkable_predicate_proof",
            "predicate": format!(
                "{} {} {}",
                self.predicate.attribute,
                comparator_str(self.predicate.predicate_type),
                self.predicate.threshold
            ),
            "subject_cell": subject_cell,
            "blinded_fact_commitment": self.blinded_commitment_hex(),
            "proof_system": "BabyBear STARK (prove_predicate_unlinkable)",
            "unlinkable": true,
            "cryptographic_proof": "present"
        })
        .to_string()
    }
}

/// **Generate a REAL selective-disclosure proof** that the subject (whose
/// custodial seed is `subject_seed`) satisfies `predicate_str` about a credential
/// whose attributes are `attributes_json`.
///
/// Reconstructs the subject's REAL [`AgentCipherclerk`] from their seed (the
/// custodial holder), mints a root token over the predicate's attribute service,
/// reads the attribute's value from the credential, and calls
/// [`AgentCipherclerk::prove_predicate_unlinkable`] — the genuine STARK circuit.
/// The proof is fresh-blinded (unlinkable across calls).
///
/// Refuses (`Parse`) on a malformed predicate, (`AttributeMissing`) if the
/// credential has no numeric value for the attribute, and (`Sdk`) if the SDK
/// declines — most commonly because the predicate is FALSE for the value (a sound
/// circuit cannot prove a false statement).
pub fn generate_predicate_proof(
    subject_seed: &[u8; 32],
    predicate_str: &str,
    attributes_json: &str,
) -> Result<GeneratedProof, ProofError> {
    let predicate = parse_predicate(predicate_str).map_err(ProofError::Parse)?;

    let value = attribute_value(attributes_json, &predicate.attribute).ok_or(
        ProofError::AttributeMissing {
            attribute: predicate.attribute.clone(),
        },
    )?;

    // Reconstruct the subject's REAL cipherclerk from the custodial seed (same
    // identity the bot derives for the subject elsewhere). Wrap in `Zeroizing` so
    // the temporary key copy is wiped after `from_key_bytes` consumes it.
    let secret = Zeroizing::new(*subject_seed);
    let mut cclerk = AgentCipherclerk::from_key_bytes(secret);

    // Mint a root token over a service named for the attribute (the holder's token
    // the predicate proof is generated against).
    let service = format!("identity:{}", predicate.attribute);
    let root_key = *subject_seed; // the holder's own root key material
    let token = cclerk.mint_token(&root_key, &service);

    let proof = cclerk
        .prove_predicate_unlinkable(
            &token,
            &predicate.attribute,
            value,
            predicate.predicate_type,
            BabyBear::new(predicate.threshold),
        )
        .map_err(ProofError::Sdk)?;

    Ok(GeneratedProof { predicate, proof })
}

// ── helpers ──────────────────────────────────────────────────────────────────

/// The comparator string for a [`PredicateType`] (for display / the JSON receipt).
fn comparator_str(ty: PredicateType) -> &'static str {
    match ty {
        PredicateType::Gte | PredicateType::InRangeLow => ">=",
        PredicateType::Lte | PredicateType::InRangeHigh => "<=",
        PredicateType::Gt => ">",
        PredicateType::Lt => "<",
        PredicateType::Neq => "!=",
    }
}

/// Hex of a [`BabyBear`] field element (its canonical u32, big-endian).
fn babybear_hex(b: BabyBear) -> String {
    hex::encode(b.as_u32().to_be_bytes())
}

#[cfg(test)]
mod tests {
    use super::*;

    // ── predicate parsing ──

    #[test]
    fn parses_common_comparators() {
        assert_eq!(
            parse_predicate("age>=18").unwrap(),
            ParsedPredicate {
                attribute: "age".into(),
                predicate_type: PredicateType::Gte,
                threshold: 18
            }
        );
        // whitespace-tolerant; two-char wins over one-char.
        assert_eq!(
            parse_predicate("balance <= 1000").unwrap(),
            ParsedPredicate {
                attribute: "balance".into(),
                predicate_type: PredicateType::Lte,
                threshold: 1000
            }
        );
        assert_eq!(
            parse_predicate("score>5").unwrap().predicate_type,
            PredicateType::Gt
        );
        assert_eq!(
            parse_predicate("rank<3").unwrap().predicate_type,
            PredicateType::Lt
        );
        assert_eq!(
            parse_predicate("tier!=0").unwrap().predicate_type,
            PredicateType::Neq
        );
    }

    #[test]
    fn ge_beats_gt_in_parse_order() {
        // `age>=18` must parse as Gte(18), NOT Gt with a `=18` threshold.
        let p = parse_predicate("age>=18").unwrap();
        assert_eq!(p.predicate_type, PredicateType::Gte);
        assert_eq!(p.threshold, 18);
    }

    #[test]
    fn rejects_malformed_predicates() {
        assert_eq!(
            parse_predicate("age").unwrap_err(),
            PredicateParseError::NoComparator
        );
        assert_eq!(
            parse_predicate(">=18").unwrap_err(),
            PredicateParseError::EmptyAttribute
        );
        assert!(matches!(
            parse_predicate("age>=abc").unwrap_err(),
            PredicateParseError::BadThreshold(_)
        ));
        // `==` is explicitly unsupported (no equality PredicateType).
        assert!(matches!(
            parse_predicate("age==18").unwrap_err(),
            PredicateParseError::UnsupportedComparator(_)
        ));
    }

    // ── attribute extraction ──

    #[test]
    fn extracts_numeric_attribute_value() {
        assert_eq!(attribute_value(r#"{"age": 25}"#, "age"), Some(25));
        // string-encoded number tolerated.
        assert_eq!(attribute_value(r#"{"age": "25"}"#, "age"), Some(25));
        // absent / non-numeric → None.
        assert_eq!(attribute_value(r#"{"age": 25}"#, "height"), None);
        assert_eq!(attribute_value(r#"{"name": "alice"}"#, "name"), None);
        assert_eq!(attribute_value("not json", "age"), None);
    }

    // ── the REAL proof: a TRUE predicate proves, a FALSE one is unprovable ──

    #[test]
    fn generates_a_real_unlinkable_proof_for_a_true_predicate() {
        // age=25, predicate age>=18 (TRUE): a genuine STARK proof is produced, with a
        // blinded fact commitment. This wires `prove_predicate_unlinkable` end to end
        // (the toy finding's fix) — no null proof.
        let seed = [0xABu8; 32];
        let proof_gen = generate_predicate_proof(&seed, "age>=18", r#"{"age": 25}"#)
            .expect("a TRUE predicate over a real cipherclerk produces a real proof");
        assert_eq!(proof_gen.predicate.attribute, "age");
        assert_eq!(proof_gen.predicate.threshold, 18);
        // The blinded commitment is non-empty (a real artifact, not null).
        assert!(!proof_gen.blinded_commitment_hex().is_empty());
        // The presentation JSON carries the REAL proof material, not `null`.
        let json = proof_gen.presentation_json("deadbeef");
        assert!(json.contains("unlinkable_predicate_proof"));
        assert!(json.contains("\"cryptographic_proof\":\"present\""));
        assert!(!json.contains("null"));
    }

    #[test]
    fn two_proofs_for_the_same_predicate_are_unlinkable() {
        // Fresh blinding per call → two proofs of the SAME fact have DIFFERENT
        // blinded commitments (the unlinkability guarantee, surfaced in the embed).
        let seed = [0x11u8; 32];
        let a = generate_predicate_proof(&seed, "balance>=1000", r#"{"balance": 5000}"#).unwrap();
        let b = generate_predicate_proof(&seed, "balance>=1000", r#"{"balance": 5000}"#).unwrap();
        assert_ne!(
            a.blinded_commitment_hex(),
            b.blinded_commitment_hex(),
            "two proofs of the same fact must have different blinded commitments (unlinkable)"
        );
    }

    #[test]
    fn a_false_predicate_is_unprovable() {
        // age=16, predicate age>=18 (FALSE): the sound circuit refuses — Err(Sdk),
        // NOT a fabricated proof. This is the soundness tooth.
        let seed = [0xCDu8; 32];
        let r = generate_predicate_proof(&seed, "age>=18", r#"{"age": 16}"#);
        assert!(
            matches!(r, Err(ProofError::Sdk(_))),
            "a false predicate must be unprovable, got {r:?}"
        );
    }

    #[test]
    fn a_missing_attribute_is_reported() {
        let seed = [0x22u8; 32];
        let r = generate_predicate_proof(&seed, "age>=18", r#"{"height": 180}"#);
        assert!(matches!(r, Err(ProofError::AttributeMissing { .. })));
    }
}
