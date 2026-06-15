//! `facet`: the human-friendly capability-FACET surface for DreggDL grants.
//!
//! A `[[grant]]`'s authority over its target is restricted by an **effect
//! facet** — a bitmask (`dregg_cell::EffectMask`) of which effect KINDS the cap
//! permits (the E-language "restricted object view"). The raw mask is a `u32`,
//! which is hostile to a human author and to a diagnostic that wants to *name*
//! the over-granting edge. This module is the readable layer over it:
//!
//!   * [`parse_facet`] — a friendly facet string → the `EffectMask` the lowering
//!     puts on the [`dregg_cell::CapabilityRef`]. Accepts a NAMED facet
//!     (`"transfer-only"`), a `|`/`+`/`,`-joined list of effect-kind names
//!     (`"transfer|emit_event"`), or a raw decimal/hex mask (`"6"` / `"0x6"`).
//!   * [`describe_facet`] — an `EffectMask` → a human description
//!     (`"transfer-only {Transfer}"`), used by the enriched no-amplification /
//!     refinement diagnostics so a rejected over-grant reads as *what it widened*,
//!     not a hex constant.
//!
//! The named facets and the effect-kind names are exactly the
//! `dregg_cell::facet` vocabulary (`FACET_*` / `EFFECT_*`), so a DreggDL facet
//! and a Rust-SDK facet denote the same authority.

use dregg_cell::{
    EffectMask, EFFECT_ALL, EFFECT_ATTENUATE_CAPABILITY, EFFECT_BRIDGE_OPS, EFFECT_BURN,
    EFFECT_CAPTP_OPS, EFFECT_CREATE_CELL, EFFECT_DELEGATION_OPS, EFFECT_EMIT_EVENT,
    EFFECT_ESCROW_OPS, EFFECT_GRANT_CAPABILITY, EFFECT_INCREMENT_NONCE, EFFECT_INTRODUCE,
    EFFECT_LIFECYCLE_OPS, EFFECT_NOTE_CREATE, EFFECT_NOTE_SPEND, EFFECT_OBLIGATION_OPS,
    EFFECT_QUEUE_OPS, EFFECT_REFUSAL, EFFECT_REVOKE_CAPABILITY, EFFECT_SEAL_OPS, EFFECT_SET_FIELD,
    EFFECT_SET_PERMISSIONS, EFFECT_SET_VERIFICATION_KEY, EFFECT_SOVEREIGN_OPS, EFFECT_TRANSFER,
    FACET_ADMIN, FACET_DELEGATOR, FACET_READ_ONLY, FACET_STATE_WRITER, FACET_TRANSFER_ONLY,
};

/// An error parsing a facet string — names the offending token + the surface
/// row, and lists what was expected so the author can self-correct.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
#[error(
    "bad facet `{value}` in {site}: token `{token}` is not a named facet, an effect kind, or a \
     decimal/hex mask. Named facets: read-only | transfer-only | state-writer | admin | delegator \
     | all. Effect kinds (combine with `|`): {kinds}"
)]
pub struct FacetParseError {
    /// Where in the surface the bad facet sits (e.g. ``grant[3].facet``).
    pub site: String,
    /// The whole offending facet value.
    pub value: String,
    /// The specific token that did not resolve.
    pub token: String,
    /// The comma list of recognized effect-kind names (for the hint).
    pub kinds: String,
}

/// The (name → bit) table of effect KINDS — the `dregg_cell::EFFECT_*`
/// vocabulary, in the same order as the bit layout. Both the canonical name and
/// a couple of natural aliases resolve. This is the list a DreggDL author draws
/// from when writing `facet = "set_field|emit_event"`.
pub const EFFECT_KIND_NAMES: &[(&str, EffectMask)] = &[
    ("set_field", EFFECT_SET_FIELD),
    ("setfield", EFFECT_SET_FIELD),
    ("transfer", EFFECT_TRANSFER),
    ("grant_capability", EFFECT_GRANT_CAPABILITY),
    ("grant", EFFECT_GRANT_CAPABILITY),
    ("revoke_capability", EFFECT_REVOKE_CAPABILITY),
    ("revoke", EFFECT_REVOKE_CAPABILITY),
    ("emit_event", EFFECT_EMIT_EVENT),
    ("emit", EFFECT_EMIT_EVENT),
    ("increment_nonce", EFFECT_INCREMENT_NONCE),
    ("create_cell", EFFECT_CREATE_CELL),
    ("set_permissions", EFFECT_SET_PERMISSIONS),
    ("set_verification_key", EFFECT_SET_VERIFICATION_KEY),
    ("note_spend", EFFECT_NOTE_SPEND),
    ("note_create", EFFECT_NOTE_CREATE),
    ("seal_ops", EFFECT_SEAL_OPS),
    ("bridge_ops", EFFECT_BRIDGE_OPS),
    ("introduce", EFFECT_INTRODUCE),
    ("obligation_ops", EFFECT_OBLIGATION_OPS),
    ("escrow_ops", EFFECT_ESCROW_OPS),
    ("delegation_ops", EFFECT_DELEGATION_OPS),
    ("sovereign_ops", EFFECT_SOVEREIGN_OPS),
    ("queue_ops", EFFECT_QUEUE_OPS),
    ("captp_ops", EFFECT_CAPTP_OPS),
    ("refusal", EFFECT_REFUSAL),
    ("lifecycle_ops", EFFECT_LIFECYCLE_OPS),
    ("burn", EFFECT_BURN),
    ("attenuate_capability", EFFECT_ATTENUATE_CAPABILITY),
];

/// The (name → mask) table of NAMED facets — the `dregg_cell::FACET_*` bundles,
/// plus `all`/`unrestricted` for the top mask. A named facet is the preferred
/// surface (`facet = "transfer-only"` reads as intent).
const NAMED_FACETS: &[(&str, EffectMask)] = &[
    ("read-only", FACET_READ_ONLY),
    ("read_only", FACET_READ_ONLY),
    ("readonly", FACET_READ_ONLY),
    ("transfer-only", FACET_TRANSFER_ONLY),
    ("transfer_only", FACET_TRANSFER_ONLY),
    ("state-writer", FACET_STATE_WRITER),
    ("state_writer", FACET_STATE_WRITER),
    ("admin", FACET_ADMIN),
    ("delegator", FACET_DELEGATOR),
    ("all", EFFECT_ALL),
    ("unrestricted", EFFECT_ALL),
    ("top", EFFECT_ALL),
];

fn kinds_hint() -> String {
    // The canonical names only (skip the aliases) for a tidy hint.
    let mut seen = std::collections::BTreeSet::new();
    let mut out: Vec<&str> = Vec::new();
    for (name, bit) in EFFECT_KIND_NAMES {
        if seen.insert(*bit) {
            out.push(name);
        }
    }
    out.join(", ")
}

/// Resolve ONE token (a named facet, an effect kind, or a decimal/hex literal)
/// to its mask bits.
fn parse_token(site: &str, value: &str, token: &str) -> Result<EffectMask, FacetParseError> {
    let t = token.trim().to_ascii_lowercase();
    if t.is_empty() {
        return Ok(0);
    }
    // (1) a named facet bundle.
    if let Some((_, m)) = NAMED_FACETS.iter().find(|(n, _)| *n == t) {
        return Ok(*m);
    }
    // (2) an effect-kind name.
    if let Some((_, m)) = EFFECT_KIND_NAMES.iter().find(|(n, _)| *n == t) {
        return Ok(*m);
    }
    // (3) a raw mask: hex (0x…) or decimal.
    let parsed = if let Some(hex) = t.strip_prefix("0x") {
        u32::from_str_radix(hex, 16).ok()
    } else {
        t.parse::<u32>().ok()
    };
    if let Some(m) = parsed {
        return Ok(m);
    }
    Err(FacetParseError {
        site: site.to_string(),
        value: value.to_string(),
        token: token.to_string(),
        kinds: kinds_hint(),
    })
}

/// Parse a friendly facet string into the `EffectMask` the lowering puts on a
/// `CapabilityRef.allowed_effects`. A single named facet, OR a `|`/`+`/`,`-joined
/// union of effect kinds / named facets / literals. The union is the bitwise OR
/// (a facet that permits `transfer` AND `emit_event` is `transfer|emit_event`).
///
/// Returns the combined mask. `parse_facet("all")` == `EFFECT_ALL`; the CALLER
/// decides whether `EFFECT_ALL` should become `Some(EFFECT_ALL)` (an explicit
/// top-but-faceted cap) or `None` (the unrestricted cap) — see
/// [`facet_to_allowed_effects`].
pub fn parse_facet(site: &str, s: &str) -> Result<EffectMask, FacetParseError> {
    let mut mask: EffectMask = 0;
    for token in s.split(['|', '+', ',']) {
        if token.trim().is_empty() {
            continue;
        }
        mask |= parse_token(site, s, token)?;
    }
    Ok(mask)
}

/// Lower a friendly facet string to the `allowed_effects: Option<EffectMask>` a
/// `CapabilityRef` carries. `"all"`/`"unrestricted"` lower to `None` (the
/// genuine unrestricted top — the cap that `cap_attenuates` treats as `⊤`),
/// matching the executor's `None == unrestricted` reading; everything else is a
/// concrete `Some(mask)`. An empty/whitespace facet is `None`.
pub fn facet_to_allowed_effects(
    site: &str,
    s: &str,
) -> Result<Option<EffectMask>, FacetParseError> {
    if s.trim().is_empty() {
        return Ok(None);
    }
    let m = parse_facet(site, s)?;
    // The whole-top mask is the unrestricted cap; represent it as `None` so the
    // attenuation lattice treats it as ⊤ (and a `None` parent dominates it).
    if m == EFFECT_ALL {
        Ok(None)
    } else {
        Ok(Some(m))
    }
}

/// The reverse of [`facet_to_allowed_effects`] for HUMAN diagnostics: an
/// `allowed_effects` value → a readable facet description. `None` →
/// `"unrestricted (all effect kinds)"`; a mask that exactly equals a named facet
/// → that name plus its kinds; otherwise the `{Kind, Kind, …}` list. `Some(0)`
/// is the explicit deny-all (`{} (deny-all)`), per the `dregg_cell` P2-1 reading.
pub fn describe_allowed_effects(mask: Option<EffectMask>) -> String {
    match mask {
        None => "unrestricted (all effect kinds)".to_string(),
        Some(0) => "{} (deny-all — no effect kind permitted)".to_string(),
        Some(m) => describe_facet(m),
    }
}

/// A human description of a concrete (non-`None`) `EffectMask`: the matching
/// named facet (if exact) followed by the braced kind list — e.g.
/// `"transfer-only {Transfer}"` or `"{SetField, EmitEvent}"`.
pub fn describe_facet(mask: EffectMask) -> String {
    let kinds = describe_kinds(mask);
    // Is this exactly a named facet? (use the canonical spelling)
    let named = NAMED_FACETS
        .iter()
        .filter(|(n, m)| *m == mask && !n.contains('_')) // prefer hyphen spelling
        .map(|(n, _)| *n)
        .next()
        .or_else(|| {
            NAMED_FACETS
                .iter()
                .find(|(_, m)| *m == mask)
                .map(|(n, _)| *n)
        });
    match named {
        Some(name) => format!("{name} {{{kinds}}}"),
        None => format!("{{{kinds}}}"),
    }
}

/// The `{Kind, Kind, …}`-inner list of which effect kinds a mask permits (the
/// human face of the bits). Uses the canonical CamelCase kind labels.
pub fn describe_kinds(mask: EffectMask) -> String {
    const LABELS: &[(EffectMask, &str)] = &[
        (EFFECT_SET_FIELD, "SetField"),
        (EFFECT_TRANSFER, "Transfer"),
        (EFFECT_GRANT_CAPABILITY, "GrantCapability"),
        (EFFECT_REVOKE_CAPABILITY, "RevokeCapability"),
        (EFFECT_EMIT_EVENT, "EmitEvent"),
        (EFFECT_INCREMENT_NONCE, "IncrementNonce"),
        (EFFECT_CREATE_CELL, "CreateCell"),
        (EFFECT_SET_PERMISSIONS, "SetPermissions"),
        (EFFECT_SET_VERIFICATION_KEY, "SetVerificationKey"),
        (EFFECT_NOTE_SPEND, "NoteSpend"),
        (EFFECT_NOTE_CREATE, "NoteCreate"),
        (EFFECT_SEAL_OPS, "SealOps"),
        (EFFECT_BRIDGE_OPS, "BridgeOps"),
        (EFFECT_INTRODUCE, "Introduce"),
        (EFFECT_OBLIGATION_OPS, "ObligationOps"),
        (EFFECT_ESCROW_OPS, "EscrowOps"),
        (EFFECT_DELEGATION_OPS, "DelegationOps"),
        (EFFECT_SOVEREIGN_OPS, "SovereignOps"),
        (EFFECT_QUEUE_OPS, "QueueOps"),
        (EFFECT_CAPTP_OPS, "CapTpOps"),
        (EFFECT_REFUSAL, "Refusal"),
        (EFFECT_LIFECYCLE_OPS, "LifecycleOps"),
        (EFFECT_BURN, "Burn"),
        (EFFECT_ATTENUATE_CAPABILITY, "AttenuateCapability"),
    ];
    let mut out: Vec<&str> = Vec::new();
    for (bit, label) in LABELS {
        if mask & bit != 0 {
            out.push(label);
        }
    }
    if out.is_empty() {
        return String::new();
    }
    out.join(", ")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn named_facets_resolve() {
        assert_eq!(parse_facet("t", "transfer-only").unwrap(), FACET_TRANSFER_ONLY);
        assert_eq!(parse_facet("t", "read-only").unwrap(), FACET_READ_ONLY);
        assert_eq!(parse_facet("t", "state-writer").unwrap(), FACET_STATE_WRITER);
        assert_eq!(parse_facet("t", "delegator").unwrap(), FACET_DELEGATOR);
        assert_eq!(parse_facet("t", "all").unwrap(), EFFECT_ALL);
    }

    #[test]
    fn kind_unions_resolve() {
        assert_eq!(
            parse_facet("t", "transfer|emit_event").unwrap(),
            EFFECT_TRANSFER | EFFECT_EMIT_EVENT
        );
        // alternative separators + whitespace + aliases.
        assert_eq!(
            parse_facet("t", "set_field + emit").unwrap(),
            EFFECT_SET_FIELD | EFFECT_EMIT_EVENT
        );
        assert_eq!(
            parse_facet("t", "transfer, grant").unwrap(),
            EFFECT_TRANSFER | EFFECT_GRANT_CAPABILITY
        );
    }

    #[test]
    fn raw_masks_resolve() {
        assert_eq!(parse_facet("t", "2").unwrap(), EFFECT_TRANSFER); // 1<<1
        assert_eq!(parse_facet("t", "0x6").unwrap(), EFFECT_TRANSFER | EFFECT_GRANT_CAPABILITY);
    }

    #[test]
    fn top_facet_lowers_to_none() {
        assert_eq!(facet_to_allowed_effects("t", "all").unwrap(), None);
        assert_eq!(facet_to_allowed_effects("t", "").unwrap(), None);
        assert_eq!(
            facet_to_allowed_effects("t", "transfer-only").unwrap(),
            Some(FACET_TRANSFER_ONLY)
        );
    }

    #[test]
    fn bad_token_errors_with_hint() {
        let e = parse_facet("grant[2].facet", "transfer|frobnicate").unwrap_err();
        assert_eq!(e.token, "frobnicate");
        assert!(e.to_string().contains("grant[2].facet"));
        assert!(e.to_string().contains("transfer")); // the kinds hint lists transfer
    }

    #[test]
    fn describe_round_trips_intent() {
        assert_eq!(describe_allowed_effects(None), "unrestricted (all effect kinds)");
        assert_eq!(describe_facet(FACET_TRANSFER_ONLY), "transfer-only {Transfer}");
        assert_eq!(
            describe_facet(EFFECT_SET_FIELD | EFFECT_EMIT_EVENT),
            "state-writer {SetField, EmitEvent}"
        );
        assert!(describe_allowed_effects(Some(0)).contains("deny-all"));
    }
}
