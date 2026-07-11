//! `gate`: the **tier-1 deploy gate** — a proof-carrying permit-or-refuse over a
//! DreggDL deployment spec.
//!
//! This is the code behind the deploy-gate microsite (`docs/deos/
//! DEPLOY-GATE-DESIGN.md`). The gate takes a DreggDL deployment spec, runs the
//! existing **structural assurance** ([`crate::check_deployment`] over the
//! lowered `dregg_turn::CallForest`), then applies a configurable **gate
//! policy** over the lowered capability graph, and returns either a
//! proof-carrying [`GateDecision::Permit`] (carrying the [`DeployVerdict`] as
//! evidence) or a [`GateDecision::Refuse`] with the offending locus.
//!
//! ## FAIL-CLOSED (the Nomad-law default)
//!
//! A [`GateDecision::Permit`] is returned **only** when *all* of the following
//! hold:
//!   1. the spec parses and lowers,
//!   2. the spec is non-empty (an empty/zero spec — nothing to deploy — is
//!      refused, never permitted),
//!   3. the structural assurance passes (A · B · well-formedness · ring), and
//!   4. *every* policy predicate passes.
//!
//! A parse error, an empty spec, a structural failure, OR a policy violation all
//! [`GateDecision::Refuse`]. There is no path from a malformed or dangerous spec
//! to a permit.
//!
//! ## The tiers (name all three; do not blur them)
//!
//! This module is **TIER 1 ONLY**: a contract expressed *as* a DreggDL
//! capability layout, whose authority structure is checkable off one file and is
//! therefore *provable*. The two other tiers named in the design note are
//! deliberately **NOT built here**:
//!
//!   * **Tier 2 — arbitrary foreign bytecode (heuristic, permanently
//!     incomplete).** A contract you cannot express as a cap-layout falls back
//!     to heuristic analysis (bytecode/template allow-listing, simulation-based
//!     honeypot checks). By Rice's theorem this is necessary-not-sufficient;
//!     it is a followup, not this lane.
//!   * **The on-chain permit hook.** The adapter-shaped integration that makes a
//!     target chain's deploy path *require* a valid dregg permit (the same
//!     plug-not-socket shape as the Hyperlane ISM / LayerZero DVN) is a followup.
//!
//! ## What the policy layer is FOR (and what it deliberately leans on)
//!
//! The structural tier already refuses whole rug-classes *structurally*:
//! **hidden or amplifying authority** is refused by guarantee A
//! ([`dregg_userspace_verify::check_no_amplification`]) and **value-from-nothing**
//! is refused by guarantee B ([`dregg_userspace_verify::check_conservation`]) —
//! before a single policy predicate runs. The policy layer is for
//! **DISCLOSED-but-dangerous** authority: authority that is structurally valid
//! (it attenuates, it conserves) yet is a rug by construction — a live,
//! un-renounced mint key; a pooled-asset withdraw cap handed to an unbounded
//! holder. Those pass the structural checks and are caught here.

use dregg_cell::permissions::AuthRequired;
use dregg_cell::{CapabilityRef, EFFECT_MINT, EffectMask, is_effect_permitted};
use dregg_turn::CallForest;
use dregg_turn::action::Effect;
use dregg_types::CellId;
use dregg_userspace_verify::{Assurance, cap_attenuates};

use crate::facet::describe_allowed_effects;
use crate::lower::Lowered;
use crate::schema::Deployment;
use crate::{DeployVerdict, check_deployment, parse_toml};

/// The all-zeros `CellId` — the burn/null recipient. A capability granted to it
/// has **no live holder** (nothing can ever exercise the recipient's c-list),
/// so a mint authority sent here is renounced. This is the dregg analog of the
/// on-chain "transfer ownership to `0x0`" renunciation idiom.
const BURN: CellId = CellId([0u8; 32]);

// ════════════════════════════════════════════════════════════════════════════
//  the gate
// ════════════════════════════════════════════════════════════════════════════

/// The tier-1 deploy gate: a policy plus the `evaluate` entry that turns a
/// DreggDL spec into a proof-carrying permit or a refusal.
#[derive(Clone, Debug)]
pub struct DeployGate {
    /// The configured policy applied on top of the structural assurance.
    pub policy: GatePolicy,
}

impl DeployGate {
    /// Build a gate from a policy.
    pub fn new(policy: GatePolicy) -> Self {
        DeployGate { policy }
    }

    /// Evaluate a DreggDL **TOML spec** end-to-end: parse → lower → the
    /// structural tier → the policy predicates. FAIL-CLOSED: any failure at any
    /// stage is a [`GateDecision::Refuse`].
    pub fn evaluate(&self, spec_text: &str) -> GateDecision {
        let dep = match parse_toml(spec_text) {
            Ok(d) => d,
            Err(e) => {
                // A malformed spec never permits (Nomad-law).
                return GateDecision::Refuse {
                    reason: RefuseReason::Parse(e.to_string()),
                };
            }
        };
        self.evaluate_deployment(&dep)
    }

    /// Evaluate an already-parsed [`Deployment`]. Same pipeline as
    /// [`Self::evaluate`], minus the text parse.
    pub fn evaluate_deployment(&self, dep: &Deployment) -> GateDecision {
        // ── lower (the artifact the structural + policy tiers both read) ──
        let lowered = match Lowered::from_deployment(dep) {
            Ok(l) => l,
            Err(e) => {
                return GateDecision::Refuse {
                    reason: RefuseReason::Parse(e.to_string()),
                };
            }
        };

        // ── Nomad-law: an empty/zero spec (nothing declared) is REFUSED, never
        //    permitted. An empty forest passes every structural check vacuously,
        //    so without this guard a `""` spec would slip through as a permit. ──
        if lowered.forest.roots.is_empty() {
            return GateDecision::Refuse {
                reason: RefuseReason::EmptySpec,
            };
        }

        // ── the STRUCTURAL tier (A · B · well-formedness · ring). Any failure is
        //    an immediate refuse carrying the assurance with the offending
        //    locus. This is `check_deployment` — the real API, not a mirror. ──
        let verdict = match check_deployment(dep, self.policy.as_ring) {
            Ok(v) => v,
            Err(e) => {
                return GateDecision::Refuse {
                    reason: RefuseReason::Parse(e.to_string()),
                };
            }
        };
        if !verdict.pass() {
            return GateDecision::Refuse {
                reason: RefuseReason::Structural {
                    assurance: verdict.assurance,
                },
            };
        }

        // ── the POLICY tier: every predicate over the lowered cap graph must
        //    pass. First violation refuses. ──
        let ctx = PolicyCtx {
            lowered: &lowered,
            verdict: &verdict,
        };
        for pred in &self.policy.predicates {
            if let Err(finding) = pred.check(&ctx) {
                return GateDecision::Refuse {
                    reason: RefuseReason::Policy(finding),
                };
            }
        }

        // Structural PASSED and every policy predicate PASSED: permit, carrying
        // the DeployVerdict as the proof-carrying evidence.
        GateDecision::Permit { verdict }
    }
}

/// The gate's decision: a proof-carrying permit, or a refusal with a reason.
#[derive(Clone, Debug)]
pub enum GateDecision {
    /// The deployment is permitted. Carries the [`DeployVerdict`] — the static
    /// assurance over the whole authority layout + the resolved ids — as the
    /// evidence a chain (or an auditor) re-checks.
    Permit { verdict: DeployVerdict },
    /// The deployment is refused, with the reason (parse / empty / structural /
    /// policy) and the offending locus.
    Refuse { reason: RefuseReason },
}

impl GateDecision {
    /// `true` iff this is a [`GateDecision::Permit`].
    pub fn is_permit(&self) -> bool {
        matches!(self, GateDecision::Permit { .. })
    }
    /// `true` iff this is a [`GateDecision::Refuse`].
    pub fn is_refuse(&self) -> bool {
        matches!(self, GateDecision::Refuse { .. })
    }
    /// The carried verdict on a permit (`None` on a refusal).
    pub fn verdict(&self) -> Option<&DeployVerdict> {
        match self {
            GateDecision::Permit { verdict } => Some(verdict),
            GateDecision::Refuse { .. } => None,
        }
    }
}

/// Why a deployment was refused.
#[derive(Clone, Debug)]
pub enum RefuseReason {
    /// The spec did not parse or lower (a malformed spec — fail-closed).
    Parse(String),
    /// The spec is empty/zero — nothing to deploy (the Nomad-law fail-closed
    /// default; an empty forest is refused, never permitted).
    EmptySpec,
    /// The structural tier failed (guarantee A / B / well-formedness / ring).
    /// Carries the [`Assurance`] whose findings name the precise offending locus
    /// (which node, which effect, which asset).
    Structural { assurance: Assurance },
    /// A policy predicate was violated. Carries the located finding.
    Policy(PolicyFinding),
}

impl std::fmt::Display for RefuseReason {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            RefuseReason::Parse(m) => write!(f, "REFUSE (parse): {m}"),
            RefuseReason::EmptySpec => {
                write!(f, "REFUSE (empty spec): nothing to deploy (fail-closed)")
            }
            RefuseReason::Structural { assurance } => {
                write!(f, "REFUSE (structural):")?;
                for finding in assurance.all_findings() {
                    write!(
                        f,
                        "\n  [{}] {} — {}",
                        finding.guarantee, finding.locus, finding.message
                    )?;
                }
                Ok(())
            }
            RefuseReason::Policy(p) => write!(f, "REFUSE (policy): {p}"),
        }
    }
}

/// One policy-tier finding: which predicate refused, where (a human label for
/// the offending grant edge / cell), and why.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PolicyFinding {
    /// The predicate that refused (e.g. `"NoLiveMintAuthority"`).
    pub predicate: String,
    /// A human label for the offending locus (e.g. `"grant issuer → operator"`).
    pub locus: String,
    /// Why the predicate refused.
    pub message: String,
}

impl std::fmt::Display for PolicyFinding {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} at {}: {}", self.predicate, self.locus, self.message)
    }
}

// ════════════════════════════════════════════════════════════════════════════
//  the policy
// ════════════════════════════════════════════════════════════════════════════

/// A configurable, composable set of tier-1 policy predicates over the lowered
/// capability graph. Composable = an ordered `Vec` of [`Predicate`]s; the gate
/// refuses on the first that fails.
#[derive(Clone, Debug, Default)]
pub struct GatePolicy {
    /// Run the ring-balance structural check too (for a spec that declares a
    /// settlement ring as bare funding transfers). Forwarded to
    /// [`crate::check_deployment`]'s `as_ring`.
    pub as_ring: bool,
    /// The ordered policy predicates.
    pub predicates: Vec<Predicate>,
}

impl GatePolicy {
    /// The permissive default: structural-only (no policy predicates). Still
    /// fail-closes on parse / empty / structural failure.
    pub fn structural_only() -> Self {
        GatePolicy::default()
    }

    /// A representative **fair-launch** policy for the microsite: no live
    /// un-renounced mint authority (mint must be renounced or held by a declared
    /// governance holder), reliance on the structural non-amplification check,
    /// and a requirement that the pooled-asset withdraw/transfer cap be
    /// attenuated to a permitted operator set.
    pub fn fair_launch(
        governance_holders: Vec<String>,
        pool: &str,
        operators: Vec<String>,
    ) -> Self {
        GatePolicy {
            as_ring: false,
            predicates: vec![
                Predicate::NoLiveMintAuthority { governance_holders },
                Predicate::NoUndisclosedAmplifyingGrant,
                Predicate::RequireDangerousCapAttenuation {
                    label: "pooled-asset withdraw".to_string(),
                    // withdraw/transfer over a pooled asset is the dangerous kind.
                    dangerous_effects: dregg_cell::EFFECT_TRANSFER,
                    pooled_target: Some(pool.to_string()),
                    permitted_holders: operators,
                    // the granted cap may carry at most transfer authority …
                    ceiling_effects: Some(dregg_cell::EFFECT_TRANSFER),
                    // … and no wider expiry than the ceiling (None = no bound).
                    ceiling_expiry: None,
                },
            ],
        }
    }
}

/// The context a predicate reads: the lowered deployment (the cap graph + the
/// name↔id resolution) and the structural verdict.
pub struct PolicyCtx<'a> {
    pub lowered: &'a Lowered,
    pub verdict: &'a DeployVerdict,
}

/// A tier-1 policy predicate over the lowered capability graph. Each variant is
/// grounded in the REAL cap types (`dregg_cell::CapabilityRef`,
/// `dregg_cell::EFFECT_*`, `AuthRequired`) — it inspects the actual lowered
/// caps, never invented ones.
#[derive(Clone, Debug)]
pub enum Predicate {
    /// **NoLiveMintAuthority** — refuse the un-renounced-mint rug.
    ///
    /// REFUSAL CONDITION: a lowered `Effect::GrantCapability { to, cap, .. }`
    /// whose `cap` permits `dregg_cell::EFFECT_MINT` (bit `1 << 26` — the
    /// cap-gated SUPPLY ENTRY; `cell/src/facet.rs:108`), determined by the real
    /// `dregg_cell::is_effect_permitted(cap.allowed_effects, EFFECT_MINT)` — so
    /// an **unrestricted** cap (`allowed_effects == None`, which permits every
    /// effect *including* mint) counts — is REFUSED **unless** it is one of:
    ///   * **renounced** — `cap.permissions == AuthRequired::Impossible` (the cap
    ///     is permanently un-exercisable → no live holder;
    ///     `cell/src/permissions.rs:15`), OR the recipient is the burn/null
    ///     `CellId([0; 32])` (no live holder);
    ///   * **held by governance** — the recipient resolves to a name in
    ///     `governance_holders` (a disclosed, permitted, e.g. time-locked,
    ///     holder).
    ///
    /// Otherwise it is a live mint key held by a non-governance cell — the rug —
    /// and is refused.
    NoLiveMintAuthority {
        /// Cell names permitted to hold a LIVE (exercisable) mint authority
        /// (e.g. a time-locked governance multisig). Empty = the strict
        /// fair-launch reading: mint must be renounced, full stop.
        governance_holders: Vec<String>,
    },

    /// **NoUndisclosedAmplifyingGrant** — hidden/amplifying authority is refused
    /// **structurally**, and the gate RELIES on that; this predicate does not
    /// duplicate the walk.
    ///
    /// The structural tier ([`dregg_userspace_verify::check_no_amplification`],
    /// guarantee A) already refuses any grant that confers wider authority than
    /// the delegation chain handed it — *before* the policy tier runs. This
    /// predicate is a defensive re-assertion of that reliance: it refuses iff the
    /// carried structural non-amplification verdict is not a pass (which the gate
    /// has already acted on, so in practice it never fires here). It exists to
    /// make the reliance EXPLICIT in the policy, and to document that the policy
    /// tier's job is DISCLOSED-but-dangerous authority, not hidden amplification.
    ///
    /// REFUSAL CONDITION: `verdict.assurance.no_amplification` is not `Pass`.
    NoUndisclosedAmplifyingGrant,

    /// **RequireDangerousCapAttenuation** — a named dangerous capability must be
    /// attenuated to a permitted holder set.
    ///
    /// REFUSAL CONDITION: for each lowered `Effect::GrantCapability { to, cap,
    /// .. }` whose `cap` permits any bit in `dangerous_effects` (via the real
    /// `is_effect_permitted`) AND (when `pooled_target` is set) reaches that
    /// target cell, the grant is REFUSED if EITHER:
    ///   * the recipient does not resolve to a name in `permitted_holders`, OR
    ///   * the granted cap is not an attenuation of the policy ceiling —
    ///     `dregg_userspace_verify::cap_attenuates(cap, &ceiling)` is false,
    ///     where `ceiling` is the granted cap with its facet clamped to
    ///     `ceiling_effects` and its expiry clamped to `ceiling_expiry`. This
    ///     uses the REAL attenuation lattice: the granted facet must be `⊆`
    ///     `ceiling_effects` and the granted expiry `≤` `ceiling_expiry` (a
    ///     timelock ceiling).
    RequireDangerousCapAttenuation {
        /// A human label for the dangerous capability (for the finding).
        label: String,
        /// The effect bit(s) that make a cap "dangerous" (e.g.
        /// `dregg_cell::EFFECT_TRANSFER` for withdraw/transfer authority).
        dangerous_effects: EffectMask,
        /// Restrict the check to caps whose `target` resolves to this cell name
        /// (the pooled asset). `None` = any target.
        pooled_target: Option<String>,
        /// Cell names permitted to hold the dangerous cap.
        permitted_holders: Vec<String>,
        /// The widest facet a granted dangerous cap may carry (`None` = top /
        /// unrestricted allowed). The granted facet must be `⊆` this.
        ceiling_effects: Option<EffectMask>,
        /// The latest expiry a granted dangerous cap may carry (`None` = no
        /// bound). A `Some(h)` ceiling is a timelock: a cap with no expiry (or a
        /// later one) fails to attenuate it.
        ceiling_expiry: Option<u64>,
    },
}

impl Predicate {
    /// The predicate's name (for findings).
    pub fn name(&self) -> &'static str {
        match self {
            Predicate::NoLiveMintAuthority { .. } => "NoLiveMintAuthority",
            Predicate::NoUndisclosedAmplifyingGrant => "NoUndisclosedAmplifyingGrant",
            Predicate::RequireDangerousCapAttenuation { .. } => "RequireDangerousCapAttenuation",
        }
    }

    /// Check this predicate over the lowered cap graph. `Ok(())` on pass, `Err`
    /// with the located finding on the first violation.
    pub fn check(&self, ctx: &PolicyCtx<'_>) -> Result<(), PolicyFinding> {
        match self {
            Predicate::NoLiveMintAuthority { governance_holders } => {
                check_no_live_mint(ctx.lowered, governance_holders)
            }
            Predicate::NoUndisclosedAmplifyingGrant => check_relies_on_structural_a(ctx.verdict),
            Predicate::RequireDangerousCapAttenuation {
                label,
                dangerous_effects,
                pooled_target,
                permitted_holders,
                ceiling_effects,
                ceiling_expiry,
            } => check_dangerous_attenuation(
                ctx.lowered,
                label,
                *dangerous_effects,
                pooled_target.as_deref(),
                permitted_holders,
                *ceiling_effects,
                *ceiling_expiry,
            ),
        }
    }
}

// ─── predicate implementations ──────────────────────────────────────────────

/// Collect every lowered grant edge `(from, to, cap)` across the forest
/// (recursing into nested re-delegations via `all_effects`).
fn grant_edges(forest: &CallForest) -> Vec<(&CellId, &CellId, &CapabilityRef)> {
    let mut out = Vec::new();
    for root in &forest.roots {
        for eff in root.all_effects() {
            if let Effect::GrantCapability { from, to, cap } = eff {
                out.push((from, to, cap));
            }
        }
    }
    out
}

/// Resolve a set of cell NAMES to their lowered `CellId`s (names that do not
/// resolve are dropped — a permitted-holder set built from an unknown name is
/// simply smaller, which fails closed).
fn resolve_names(lowered: &Lowered, names: &[String]) -> std::collections::BTreeSet<CellId> {
    names
        .iter()
        .filter_map(|n| lowered.cell_ids.get(n).copied())
        .collect()
}

fn check_no_live_mint(
    lowered: &Lowered,
    governance_holders: &[String],
) -> Result<(), PolicyFinding> {
    let gov = resolve_names(lowered, governance_holders);
    for (from, to, cap) in grant_edges(&lowered.forest) {
        // Does this cap permit minting? `is_effect_permitted(None, _) == true`,
        // so an UNRESTRICTED cap counts as mint-capable (it can mint).
        if !is_effect_permitted(cap.allowed_effects, EFFECT_MINT) {
            continue;
        }
        // Renounced: permanently un-exercisable, or sent to the burn address.
        let renounced = cap.permissions == AuthRequired::Impossible || *to == BURN;
        if renounced {
            continue;
        }
        // Held by a declared governance holder → disclosed & permitted.
        if gov.contains(to) {
            continue;
        }
        // A live mint key held by a non-governance, non-renounced cell — the rug.
        return Err(PolicyFinding {
            predicate: "NoLiveMintAuthority".to_string(),
            locus: format!(
                "grant {} → {}",
                lowered.label_cell(from),
                lowered.label_cell(to)
            ),
            message: format!(
                "grant confers LIVE mint authority to `{}`: the cap facet {} permits \
                 Effect::Mint (dregg_cell::EFFECT_MINT, bit 1<<26 — the cap-gated supply \
                 entry), yet it is NOT renounced (permissions != Impossible and recipient \
                 is not the burn address) and `{}` is not a declared governance holder. \
                 This is the un-renounced-mint rug.",
                lowered.label_cell(to),
                describe_allowed_effects(cap.allowed_effects),
                lowered.label_cell(to),
            ),
        });
    }
    Ok(())
}

fn check_relies_on_structural_a(verdict: &DeployVerdict) -> Result<(), PolicyFinding> {
    if verdict.assurance.no_amplification.is_pass() {
        Ok(())
    } else {
        // Defensive: the structural tier already refuses this before the policy
        // runs, so this path is unreachable through the gate — but it makes the
        // reliance explicit rather than silent.
        Err(PolicyFinding {
            predicate: "NoUndisclosedAmplifyingGrant".to_string(),
            locus: "<forest>".to_string(),
            message: "hidden/amplifying authority is refused STRUCTURALLY (guarantee A, \
                      check_no_amplification); the structural non-amplification verdict did \
                      not pass"
                .to_string(),
        })
    }
}

#[allow(clippy::too_many_arguments)]
fn check_dangerous_attenuation(
    lowered: &Lowered,
    label: &str,
    dangerous_effects: EffectMask,
    pooled_target: Option<&str>,
    permitted_holders: &[String],
    ceiling_effects: Option<EffectMask>,
    ceiling_expiry: Option<u64>,
) -> Result<(), PolicyFinding> {
    let permitted = resolve_names(lowered, permitted_holders);
    let target_id = pooled_target.and_then(|t| lowered.cell_ids.get(t).copied());

    for (from, to, cap) in grant_edges(&lowered.forest) {
        // Only caps that carry the dangerous authority are in scope.
        if !is_effect_permitted(cap.allowed_effects, dangerous_effects) {
            continue;
        }
        // Restrict to caps reaching the pooled target (when configured).
        if let Some(tid) = target_id
            && cap.target != tid
        {
            continue;
        }

        let locus = format!(
            "grant {} → {} (target {})",
            lowered.label_cell(from),
            lowered.label_cell(to),
            lowered.label_cell(&cap.target),
        );

        // (1) recipient must be a permitted holder.
        if !permitted.contains(to) {
            return Err(PolicyFinding {
                predicate: "RequireDangerousCapAttenuation".to_string(),
                locus,
                message: format!(
                    "the dangerous `{label}` cap (facet {}) is granted to `{}`, which is not \
                     in the permitted holder set — refuse.",
                    describe_allowed_effects(cap.allowed_effects),
                    lowered.label_cell(to),
                ),
            });
        }

        // (2) the granted cap must attenuate the policy ceiling. The ceiling is
        // the granted cap with its facet + expiry clamped to the policy bound;
        // `cap_attenuates` (the REAL lattice) checks facet ⊆ and expiry ≤.
        let ceiling = CapabilityRef {
            allowed_effects: ceiling_effects,
            expires_at: ceiling_expiry,
            ..cap.clone()
        };
        if !cap_attenuates(cap, &ceiling) {
            return Err(PolicyFinding {
                predicate: "RequireDangerousCapAttenuation".to_string(),
                locus,
                message: format!(
                    "the dangerous `{label}` cap (facet {}, expiry {:?}) is WIDER than the \
                     permitted ceiling (facet {}, expiry {:?}) — it does not attenuate it. \
                     Refuse.",
                    describe_allowed_effects(cap.allowed_effects),
                    cap.expires_at,
                    describe_allowed_effects(ceiling_effects),
                    ceiling_expiry,
                ),
            });
        }
    }
    Ok(())
}

// ════════════════════════════════════════════════════════════════════════════
//  tests — both polarities, default-run
// ════════════════════════════════════════════════════════════════════════════

#[cfg(test)]
mod tests {
    use super::*;

    const MINT_BIT: u32 = 1 << 26; // dregg_cell::EFFECT_MINT

    /// A CLEAN tier-1 spec: an issuer mints only into a governance holder, and
    /// the pooled-asset transfer cap is attenuated to a permitted operator. It
    /// passes structural AND every fair-launch policy predicate.
    fn clean_spec() -> String {
        format!(
            r#"
[federation]
id = "auto"

[[factory]]
ref = "f"

[[cell]]
name = "issuer"
factory = "f"
[[cell]]
name = "pool"
factory = "f"
[[cell]]
name = "gov"
factory = "f"
[[cell]]
name = "operator"
factory = "f"

# mint authority held by the governance holder — disclosed & permitted.
[[grant]]
from = "issuer"
to   = "gov"
permissions = "signature"
target = "issuer"
allowed_effects = {MINT_BIT}

# pooled-asset transfer cap, transfer-only, to the permitted operator.
[[grant]]
from = "pool"
to   = "operator"
permissions = "signature"
target = "pool"
allowed_effects = 2
"#
        )
    }

    fn fair_launch_gate() -> DeployGate {
        DeployGate::new(GatePolicy::fair_launch(
            vec!["gov".to_string()],
            "pool",
            vec!["operator".to_string()],
        ))
    }

    // ── (a) a clean spec PERMITS, carrying a DeployVerdict ──
    #[test]
    fn clean_spec_permits_with_a_verdict() {
        let decision = fair_launch_gate().evaluate(&clean_spec());
        assert!(
            decision.is_permit(),
            "a clean fair-launch spec must permit; got: {decision:?}"
        );
        let verdict = decision.verdict().expect("permit carries a verdict");
        assert!(verdict.pass(), "the carried verdict is a passing assurance");
        assert_eq!(
            verdict.cells.len(),
            4,
            "four cells resolved in the evidence"
        );
    }

    // ── (b) an AMPLIFYING spec REFUSES (structural A) ──
    #[test]
    fn amplifying_spec_refuses_structurally() {
        // operator is handed a transfer-only facet over `deal`, then re-delegates
        // an UNRESTRICTED cap over the same target — an in-forest amplification.
        let dl = r#"
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
[[grant]]
from = "deal"
to   = "operator"
permissions = "signature"
target = "deal"
allowed_effects = 2
[[grant]]
from = "operator"
to   = "sub"
permissions = "signature"
target = "deal"
"#;
        let decision = fair_launch_gate().evaluate(dl);
        let GateDecision::Refuse {
            reason: RefuseReason::Structural { assurance },
        } = decision
        else {
            panic!("an amplifying spec must refuse structurally; got: {decision:?}");
        };
        assert!(
            !assurance.no_amplification.is_pass(),
            "refused on the non-amplification (A) check"
        );
    }

    // ── (c) a NON-CONSERVING spec REFUSES (structural B family) ──
    #[test]
    fn non_conserving_spec_refuses_structurally() {
        // The DreggDL surface emits only self-netting Transfers, so the
        // conservation failure it CAN express is a ring imbalance — the intent-
        // ring specialization of guarantee B (an un-closed ring: a→b, b→c, no
        // c→a). Under a ring-mode policy the gate refuses it structurally.
        let dl = r#"
[federation]
id = "auto"
[[factory]]
ref = "f"
[[cell]]
name = "a"
factory = "f"
[[cell]]
name = "b"
factory = "f"
[[cell]]
name = "c"
factory = "f"
[[fund]]
from = "a"
to   = "b"
amount = 10
[[fund]]
from = "b"
to   = "c"
amount = 10
"#;
        let gate = DeployGate::new(GatePolicy {
            as_ring: true,
            predicates: vec![],
        });
        let decision = gate.evaluate(dl);
        let GateDecision::Refuse {
            reason: RefuseReason::Structural { assurance },
        } = decision
        else {
            panic!("an un-closed ring must refuse structurally; got: {decision:?}");
        };
        assert!(
            !assurance.ring_balance.is_pass(),
            "refused on the ring-balance (B-family) check"
        );
    }

    // ── (d) THE DISCRIMINATOR: NoLiveMintAuthority bites AND permits clean ──
    #[test]
    fn no_live_mint_authority_bites_and_permits() {
        // A live un-renounced mint granted to `operator` (not governance, not
        // renounced) — the rug.
        let rug = format!(
            r#"
[federation]
id = "auto"
[[factory]]
ref = "f"
[[cell]]
name = "issuer"
factory = "f"
[[cell]]
name = "operator"
factory = "f"
[[grant]]
from = "issuer"
to   = "operator"
permissions = "signature"
target = "issuer"
allowed_effects = {MINT_BIT}
"#
        );
        // No governance holder permitted → the rug must be refused by policy.
        let strict = DeployGate::new(GatePolicy {
            as_ring: false,
            predicates: vec![Predicate::NoLiveMintAuthority {
                governance_holders: vec![],
            }],
        });
        let decision = strict.evaluate(&rug);
        let GateDecision::Refuse {
            reason: RefuseReason::Policy(finding),
        } = &decision
        else {
            panic!("a live un-renounced mint must be refused by policy; got: {decision:?}");
        };
        assert_eq!(finding.predicate, "NoLiveMintAuthority");
        assert!(
            finding.message.contains("mint"),
            "the finding names the mint authority: {finding}"
        );

        // The SAME spec, but the mint is RENOUNCED (permissions = impossible →
        // permanently un-exercisable, no live holder). Now it permits — proving
        // the policy is non-vacuous: it bites the rug AND lets the clean one pass.
        let renounced = rug.replace(
            r#"permissions = "signature""#,
            r#"permissions = "impossible""#,
        );
        let decision = strict.evaluate(&renounced);
        assert!(
            decision.is_permit(),
            "a RENOUNCED mint (permissions=impossible) must permit; got: {decision:?}"
        );

        // And the SAME rug spec PERMITS when `operator` IS a declared governance
        // holder (a disclosed, permitted holder).
        let gov_gate = DeployGate::new(GatePolicy {
            as_ring: false,
            predicates: vec![Predicate::NoLiveMintAuthority {
                governance_holders: vec!["operator".to_string()],
            }],
        });
        assert!(
            gov_gate.evaluate(&rug).is_permit(),
            "a mint held by a declared governance holder must permit"
        );
    }

    // ── the sneaky variant: an UNRESTRICTED grant permits mint too ──
    #[test]
    fn unrestricted_grant_is_treated_as_live_mint() {
        // No allowed_effects = unrestricted (None) = permits EVERY effect,
        // including mint. NoLiveMintAuthority must catch it even though "mint" is
        // never named in the spec.
        let dl = r#"
[federation]
id = "auto"
[[factory]]
ref = "f"
[[cell]]
name = "issuer"
factory = "f"
[[cell]]
name = "operator"
factory = "f"
[[grant]]
from = "issuer"
to   = "operator"
permissions = "signature"
target = "issuer"
"#;
        let strict = DeployGate::new(GatePolicy {
            as_ring: false,
            predicates: vec![Predicate::NoLiveMintAuthority {
                governance_holders: vec![],
            }],
        });
        assert!(
            strict.evaluate(dl).is_refuse(),
            "an unrestricted live grant confers mint authority and must be refused"
        );
    }

    // ── RequireDangerousCapAttenuation bites AND permits ──
    #[test]
    fn dangerous_cap_attenuation_bites_and_permits() {
        let base = r#"
[federation]
id = "auto"
[[factory]]
ref = "f"
[[cell]]
name = "pool"
factory = "f"
[[cell]]
name = "operator"
factory = "f"
[[cell]]
name = "attacker"
factory = "f"
"#;
        let pred = Predicate::RequireDangerousCapAttenuation {
            label: "pooled-asset withdraw".to_string(),
            dangerous_effects: dregg_cell::EFFECT_TRANSFER,
            pooled_target: Some("pool".to_string()),
            permitted_holders: vec!["operator".to_string()],
            ceiling_effects: Some(dregg_cell::EFFECT_TRANSFER),
            ceiling_expiry: None,
        };
        let gate = DeployGate::new(GatePolicy {
            as_ring: false,
            predicates: vec![pred.clone()],
        });

        // BITE (wrong holder): transfer cap over pool granted to `attacker`.
        let to_attacker = format!(
            "{base}\n[[grant]]\nfrom = \"pool\"\nto = \"attacker\"\ntarget = \"pool\"\nallowed_effects = 2\n"
        );
        let d = gate.evaluate(&to_attacker);
        assert!(
            d.is_refuse(),
            "a dangerous cap to a non-permitted holder must refuse: {d:?}"
        );

        // BITE (too wide): UNRESTRICTED cap over pool to the permitted operator —
        // wider than the transfer-only ceiling, so it does not attenuate.
        let too_wide =
            format!("{base}\n[[grant]]\nfrom = \"pool\"\nto = \"operator\"\ntarget = \"pool\"\n");
        // NoLiveMint is NOT in this policy, so only the attenuation predicate acts.
        assert!(
            gate.evaluate(&too_wide).is_refuse(),
            "an unrestricted (wider-than-ceiling) dangerous cap must refuse"
        );

        // PERMIT: transfer-only cap over pool to the permitted operator.
        let clean = format!(
            "{base}\n[[grant]]\nfrom = \"pool\"\nto = \"operator\"\ntarget = \"pool\"\nallowed_effects = 2\n"
        );
        assert!(
            gate.evaluate(&clean).is_permit(),
            "a transfer-only cap to the permitted operator must permit"
        );
    }

    // ── (e) THE NOMAD-LAW: empty / malformed / zero specs REFUSE ──
    #[test]
    fn empty_and_malformed_specs_refuse() {
        let gate = fair_launch_gate();

        // A wholly empty spec ("") must REFUSE (never permit) — fail-closed. The
        // `[federation]` block is a required field, so the bare empty string is
        // caught at parse; either way it never permits.
        let d = gate.evaluate("");
        assert!(
            d.is_refuse(),
            "an empty spec must refuse (Nomad-law); got: {d:?}"
        );

        // A well-formed spec with a federation but NOTHING to deploy (no cells)
        // lowers to an empty forest — the EmptySpec fail-closed path. Without the
        // guard this would slip through as a vacuous permit.
        let zero = "[federation]\nid = \"auto\"\n";
        let d = gate.evaluate(zero);
        assert!(
            matches!(
                d,
                GateDecision::Refuse {
                    reason: RefuseReason::EmptySpec
                }
            ),
            "a zero (no-cells) spec must refuse via EmptySpec; got: {d:?}"
        );

        // A malformed spec (bad TOML) → Parse refuse, never permit.
        let malformed = "[federation\nid = ";
        let d = gate.evaluate(malformed);
        assert!(
            matches!(
                d,
                GateDecision::Refuse {
                    reason: RefuseReason::Parse(_)
                }
            ),
            "a malformed spec must refuse on parse; got: {d:?}"
        );
    }

    // ── the gate never permits what check_deployment refuses (fail-closed) ──
    #[test]
    fn structural_only_gate_still_fail_closes() {
        // With no policy predicates the gate is structural-only, but an amplifying
        // spec is still refused.
        let dl = r#"
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
[[grant]]
from = "deal"
to   = "operator"
target = "deal"
allowed_effects = 2
[[grant]]
from = "operator"
to   = "sub"
target = "deal"
"#;
        let gate = DeployGate::new(GatePolicy::structural_only());
        assert!(gate.evaluate(dl).is_refuse());
    }
}
