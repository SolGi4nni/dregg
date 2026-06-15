//! `diagnose`: turn a raw [`dregg_userspace_verify::Assurance`] over a lowered
//! DreggDL forest into **enriched, spec-named diagnostics**.
//!
//! `dregg-userspace-verify` already locates a finding precisely — the
//! `node_path` + `effect_index` of the offending grant, and a message naming the
//! granting cell's hex prefix + the cap shape. That is correct but terse: it
//! names cells by `a1b2c3…` and facets by `Some(2)`. This module RE-WALKS the
//! lowered forest at the finding's locus to recover the actual
//! `Effect::GrantCapability { from, to, cap }` (and, for an amplification, the
//! PARENT cap it failed to attenuate), then renders the finding the way a human
//! reads a deploy:
//!
//! > `over-grant: operator → sub grants custody over `deal` with facet
//! >  unrestricted (all effect kinds), but operator was only handed
//! >  transfer-only {Transfer} for `deal` — the re-delegation WIDENS
//! >  {GrantCapability,…} beyond what it holds.`
//!
//! It names: the **edge** (`from → to`), the **target** (by spec name), the
//! **granted facet** (human), and the **parent facet** the grant exceeded — the
//! "exact over-granting edge" the deploy lane asks for. The enrichment is purely
//! additive: the underlying [`Finding`] / [`Locus`] are unchanged.

use dregg_cell::CapabilityRef;
use dregg_turn::action::Effect;
use dregg_turn::{CallForest, CallTree};
use dregg_userspace_verify::{Assurance, Finding, Locus};

use crate::facet::describe_allowed_effects;
use crate::lower::Lowered;

/// An enriched explanation of ONE finding: the original located finding, plus a
/// spec-named, facet-described human rendering and (for an amplification) the
/// resolved edge + parent.
#[derive(Clone, Debug)]
pub struct ExplainedFinding {
    /// The underlying located finding (guarantee + locus + raw message).
    pub finding: Finding,
    /// The enriched human message (spec names + human facets + the parent cap
    /// for an amplification). Falls back to the raw message when the finding is
    /// not a resolvable grant edge.
    pub explanation: String,
    /// For a non-amplification finding, the granting cell's spec label, if the
    /// locus resolved to a grant effect.
    pub from_label: Option<String>,
    /// For a non-amplification finding, the recipient cell's spec label.
    pub to_label: Option<String>,
    /// For a non-amplification finding, the target cell's spec label.
    pub target_label: Option<String>,
}

/// The enriched diagnostics over a whole assurance: one [`ExplainedFinding`] per
/// raw finding, in the assurance's order.
#[derive(Clone, Debug)]
pub struct DeployDiagnostics {
    pub findings: Vec<ExplainedFinding>,
}

impl DeployDiagnostics {
    /// `true` iff there are no findings (the clean case).
    pub fn is_clean(&self) -> bool {
        self.findings.is_empty()
    }
    /// The enriched explanation lines, one per finding (for printing).
    pub fn lines(&self) -> Vec<String> {
        self.findings.iter().map(|e| e.explanation.clone()).collect()
    }
}

/// Walk a forest to the node at `node_path` (forest root index, then child
/// indices), returning the `CallTree` there.
fn node_at<'a>(forest: &'a CallForest, node_path: &[usize]) -> Option<&'a CallTree> {
    let (&first, rest) = node_path.split_first()?;
    let mut cur = forest.roots.get(first)?;
    for &i in rest {
        cur = cur.children.get(i)?;
    }
    Some(cur)
}

/// Recover the `GrantCapability` effect a no-amplification finding points at.
fn grant_at<'a>(forest: &'a CallForest, locus: &Locus) -> Option<&'a Effect> {
    let node = node_at(forest, &locus.node_path)?;
    let ei = locus.effect_index?;
    node.action.effects.get(ei)
}

/// Find the PARENT cap an amplifying grant failed to attenuate: walk the path
/// from the forest root down to (but not including) the offending node,
/// collecting every `GrantCapability` whose recipient `to` is the offending
/// grant's `from` and whose target matches — the cap(s) the chain handed the
/// grantor for this target. Returns the first such parent cap (the one the
/// checker compared against).
fn parent_cap_for<'a>(
    forest: &'a CallForest,
    node_path: &[usize],
    grantor: &dregg_types::CellId,
    target: &dregg_types::CellId,
) -> Option<&'a CapabilityRef> {
    // Re-derive the ancestor scope exactly as `check_no_amplification` does:
    // caps granted TO `grantor` for `target` by any strict ancestor on the path.
    if node_path.is_empty() {
        return None;
    }
    let mut cur_path: Vec<usize> = Vec::new();
    let mut found: Option<&CapabilityRef> = None;
    // Visit each strict prefix of node_path (the ancestors of the offending node).
    for &step in &node_path[..node_path.len() - 1] {
        cur_path.push(step);
        if let Some(node) = node_at(forest, &cur_path) {
            for eff in &node.action.effects {
                if let Effect::GrantCapability { to, cap, .. } = eff {
                    if to == grantor && &cap.target == target {
                        found = Some(cap);
                    }
                }
            }
        }
    }
    found
}

/// Render ONE finding with spec names + human facets. For a no-amplification
/// finding whose locus resolves to a grant edge, this is the rich form; for
/// everything else (conservation, ring, well-formedness, or an unresolvable
/// locus) it passes the raw message through with the located guarantee prefix.
fn explain_one(lowered: &Lowered, finding: &Finding) -> ExplainedFinding {
    let forest = &lowered.forest;
    if let Some(Effect::GrantCapability { from, to, cap }) = grant_at(forest, &finding.locus) {
        let from_label = lowered.label_cell(from);
        let to_label = lowered.label_cell(to);
        let target_label = lowered.label_cell(&cap.target);
        let granted = describe_allowed_effects(cap.allowed_effects);

        let explanation = if finding.guarantee.starts_with('A') {
            // An amplification: name the parent cap it exceeded.
            match parent_cap_for(forest, &finding.locus.node_path, from, &cap.target) {
                Some(parent) => {
                    let held = describe_allowed_effects(parent.allowed_effects);
                    format!(
                        "OVER-GRANT at {loc}: `{from_label}` → `{to_label}` grants a capability \
                         over `{target_label}` (slot {slot}, facet {granted}, expiry {exp}) — but \
                         `{from_label}` was only handed facet {held} for `{target_label}` earlier \
                         in this deployment. The re-delegation WIDENS authority it does not hold \
                         (it must be ⊆ the parent cap). Narrow `{to_label}`'s facet to within \
                         {held}, or grant `{from_label}` the wider cap first.",
                        loc = finding.locus,
                        slot = cap.slot,
                        exp = expiry_str(cap.expires_at),
                    )
                }
                None => format!(
                    "OVER-GRANT at {loc}: `{from_label}` → `{to_label}` grants a capability over \
                     `{target_label}` (facet {granted}) that is not an attenuation of any cap the \
                     deployment handed `{from_label}` for that target. {raw}",
                    loc = finding.locus,
                    raw = finding.message,
                ),
            }
        } else {
            // A non-A finding that still located a grant effect — pass through
            // with the named edge for context.
            format!(
                "{g} at {loc}: `{from_label}` → `{to_label}` over `{target_label}` (facet \
                 {granted}). {raw}",
                g = finding.guarantee,
                loc = finding.locus,
                raw = finding.message,
            )
        };

        return ExplainedFinding {
            finding: finding.clone(),
            explanation,
            from_label: Some(from_label),
            to_label: Some(to_label),
            target_label: Some(target_label),
        };
    }

    // Non-grant finding (conservation asset column, ring, well-formedness): the
    // raw message already names the asset/locus; prefix the guarantee.
    ExplainedFinding {
        finding: finding.clone(),
        explanation: format!(
            "{g} at {loc}: {raw}",
            g = finding.guarantee,
            loc = finding.locus,
            raw = finding.message
        ),
        from_label: None,
        to_label: None,
        target_label: None,
    }
}

fn expiry_str(e: Option<u64>) -> String {
    match e {
        None => "never".to_string(),
        Some(h) => format!("height {h}"),
    }
}

/// **Enrich a single finding** against a lowered deployment.
pub fn explain_finding(lowered: &Lowered, finding: &Finding) -> ExplainedFinding {
    explain_one(lowered, finding)
}

/// **Enrich a whole assurance** against a lowered deployment: every finding,
/// spec-named and facet-described, in the assurance's flattened order.
pub fn explain_assurance(lowered: &Lowered, assurance: &Assurance) -> DeployDiagnostics {
    let findings = assurance
        .all_findings()
        .iter()
        .map(|f| explain_one(lowered, f))
        .collect();
    DeployDiagnostics { findings }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parse_toml;

    const OVERGRANT: &str = r#"
[federation]
id = "auto"

[[factory]]
ref = "f"

[[cell]]
name = "deal"
factory = "f"
[[cell]]
name = "operator"
factory = "f"
[[cell]]
name = "sub"
factory = "f"

# operator is handed a TRANSFER-ONLY facet over deal.
[[grant]]
from = "deal"
to   = "operator"
permissions = "signature"
target = "deal"
facet = "transfer-only"

# operator re-delegates UNRESTRICTED over deal — a widening.
[[grant]]
from = "operator"
to   = "sub"
permissions = "signature"
target = "deal"
"#;

    #[test]
    fn overgrant_diagnostic_names_the_edge_target_and_both_facets() {
        let dep = parse_toml(OVERGRANT).unwrap();
        let lowered = Lowered::from_deployment(&dep).unwrap();
        let assurance = dregg_userspace_verify::analyze(&lowered.forest, false);
        assert!(!assurance.no_amplification.is_pass(), "the spec amplifies");

        let diag = explain_assurance(&lowered, &assurance);
        assert!(!diag.is_clean());
        let amp = diag
            .findings
            .iter()
            .find(|e| e.finding.guarantee.starts_with('A'))
            .expect("there is an amplification finding");

        // Names the EDGE by spec name.
        assert_eq!(amp.from_label.as_deref(), Some("operator"));
        assert_eq!(amp.to_label.as_deref(), Some("sub"));
        // Names the TARGET by spec name.
        assert_eq!(amp.target_label.as_deref(), Some("deal"));
        // The human message names both facets in words, not hex.
        let m = &amp.explanation;
        assert!(m.contains("operator"), "names grantor: {m}");
        assert!(m.contains("sub"), "names recipient: {m}");
        assert!(m.contains("deal"), "names target: {m}");
        assert!(m.contains("unrestricted"), "describes the granted (wider) facet: {m}");
        assert!(m.contains("transfer-only"), "describes the parent (held) facet: {m}");
        assert!(m.contains("WIDENS"), "calls it a widening: {m}");
    }

    #[test]
    fn clean_spec_has_no_findings() {
        const ESCROW: &str = include_str!("../examples/escrow.dregg.toml");
        let dep = parse_toml(ESCROW).unwrap();
        let lowered = Lowered::from_deployment(&dep).unwrap();
        let assurance = dregg_userspace_verify::analyze(&lowered.forest, false);
        let diag = explain_assurance(&lowered, &assurance);
        assert!(diag.is_clean(), "a valid deploy has no findings: {:?}", diag.lines());
    }
}
