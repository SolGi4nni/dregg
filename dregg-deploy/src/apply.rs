//! `apply`: lower a DreggDL doc → the per-root **turn sequence** + the
//! **receipt-chain shape**, gated by the static pre-submission check.
//!
//! [`crate::check`] answers *"is this declared authority layout sound?"* over
//! the lowered forest. `apply` is the next step: it turns that lowered forest
//! into the **ordered sequence of `dregg_turn::Turn`s an operator submits** —
//! one turn per root effect-group (births, then funds, then grant trees), in
//! dependency order — and links them into a **receipt chain** the way the live
//! executor will: each turn's [`dregg_turn::Turn::previous_receipt_hash`]
//! points at the prior turn's receipt, so the whole deployment is one causal
//! strand.
//!
//! ## The gate (the load-bearing property)
//!
//! [`plan_apply`] runs the **static assurance first** and **refuses to emit any
//! turn** if it fails. An over-grant — a re-delegation that amplifies the cap
//! it was handed, caught by `dregg-userspace-verify::check_no_amplification` as
//! an in-forest capability amplification — is therefore rejected *before* a
//! single turn is built, before any gas is spent. The plan you get back is
//! exactly the plan that passed the check; there is no path from an amplifying
//! DreggDL to a submittable turn sequence through this function.
//!
//! ```text
//!   Deployment ──lower──▶ CallForest ──analyze──▶ Assurance
//!                                                     │
//!                                          pass? ─────┤── no ─▶ ApplyError::Refused
//!                                                     │              (carries the findings)
//!                                                    yes
//!                                                     ▼
//!                          per-root Turn sequence + receipt-chain shape
//!                          (deploy → birth → fund → grant, chained)
//! ```
//!
//! ## What the receipt chain here IS and is NOT
//!
//! The chain this module computes is the **shape** — the deterministic
//! `previous_receipt_hash` links between the turns, plus a [`ProjectedReceipt`]
//! per turn. The projection is split HONESTLY into two halves:
//!
//!   * the **artifact-known** half (turn hash, forest hash, effects hash, agent,
//!     federation, action count, the chain link) — plain values, computed off
//!     the turn alone at plan time;
//!   * the **executor-filled** half (pre/post-state commitments, computrons,
//!     timestamp, executor signature) — typed [`DeferredField::Deferred`] until
//!     the live submit fills them. These are **not zeroed-and-pretended**: a
//!     reader cannot mistake a planned receipt for a live one with an all-zero
//!     post-state (the maturation-ledger Theme-3 disposition).
//!
//! The `chain_link_hash` the next turn points at is still a pure function of the
//! artifact (the unknown fields enter the *digest* as their zero placeholders, as
//! a chain SHAPE must), so the plan is a self-consistent receipt chain at plan
//! time. What the projection gives an operator is the causal skeleton: *which*
//! turn chains to *which*, computed off the artifact alone, so the submitted
//! chain can be checked link-for-link against this plan. A mismatch between the
//! projected chain and the executor's returned receipts is a deviation an auditor
//! can see without trusting the node. When the turns are actually submitted, the
//! SDK swaps each `DeferredField::Deferred` to `Filled(..)` from the executor's
//! response — the plan becomes a live receipt chain in place.

use dregg_turn::CallForest;
use dregg_turn::turn::{Turn, TurnReceipt};
use dregg_types::CellId;

use crate::lower::{LowerError, Lowered};
use crate::schema::Deployment;
use dregg_userspace_verify::Assurance;

/// A receipt field whose value is **knowable only at submit time**, from the
/// live executor — NOT at plan time off the artifact. This is the honest type
/// for the deploy receipt's dynamic half: the planner cannot compute a
/// post-state commitment / a computron count / a wall-clock timestamp / an
/// executor signature without RUNNING the turn, so rather than silently writing
/// a zero (which reads as "the post-state is all-zeros"), the [`ProjectedReceipt`]
/// carries these as `Deferred` and the operator (or the SDK) fills them from the
/// executor's response when the turn is actually submitted.
///
/// `Deferred` is the plan-time state; `Filled(v)` is what the submit path swaps
/// in. The receipt-chain SHAPE (`previous_receipt_hash` links) does not depend on
/// these — it is computed off the artifact-only fields — so the plan is a
/// self-consistent chain whether or not the deferred fields are filled yet.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DeferredField<T> {
    /// Not yet knowable at plan time — the live executor fills it at submit.
    Deferred,
    /// Filled in from the executor's receipt at submit time.
    Filled(T),
}

impl<T> DeferredField<T> {
    /// `true` while the field is still deferred (the plan-time state).
    pub fn is_deferred(&self) -> bool {
        matches!(self, DeferredField::Deferred)
    }
    /// The filled value, if the submit path has supplied it.
    pub fn filled(&self) -> Option<&T> {
        match self {
            DeferredField::Deferred => None,
            DeferredField::Filled(v) => Some(v),
        }
    }
}

/// The **projected receipt** for a planned turn: the receipt fields split
/// HONESTLY into the two halves the deploy boundary distinguishes
/// (`dregg_userspace_verify::boundary`):
///
///   * the **artifact-known** half — computable off the turn alone at plan time
///     (turn hash, forest hash, effects hash, agent, federation, action count,
///     the `previous_receipt_hash` chain link). These are plain values.
///   * the **executor-filled** half — knowable ONLY by running the turn against
///     live state ([`DeferredField::Deferred`] until submit): the pre/post-state
///     commitments, the computrons charged, the wall-clock timestamp, the
///     executor's signature, and the finality. These are NOT zeroed-and-pretended;
///     they are typed as deferred so the shape can't be mistaken for a live
///     receipt.
///
/// This replaces the prior "build a `TurnReceipt` with the dynamic fields zeroed"
/// projection with one that *says* which fields are deferred. The
/// `chain_link_hash` is the same deterministic chain-shape digest the next turn
/// points at (it is a function of the artifact-known fields + the zeroed dynamic
/// placeholders, as the chain shape must be), so the receipt chain is unchanged;
/// what changes is that the shape is now legible.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProjectedReceipt {
    // ── artifact-known (plan-time) ──
    /// The turn's content hash (`Turn::hash`).
    pub turn_hash: [u8; 32],
    /// The single-root call-forest hash.
    pub forest_hash: [u8; 32],
    /// The deterministic digest over every effect in the turn.
    pub effects_hash: [u8; 32],
    /// The agent (target cell) this turn runs as.
    pub agent: CellId,
    /// The federation the deployment binds to.
    pub federation_id: [u8; 32],
    /// The number of actions in the turn.
    pub action_count: usize,
    /// The chain link: the prior turn's `chain_link_hash` (`None` for the first).
    pub previous_receipt_hash: Option<[u8; 32]>,
    /// The chain-shape digest the NEXT turn's `previous_receipt_hash` points at —
    /// the same value [`PlannedTurn::projected_receipt_hash`] exposes. A function
    /// of the artifact (the dynamic fields enter as their zero placeholders, as a
    /// chain SHAPE must), so the plan is a self-consistent chain at plan time.
    pub chain_link_hash: [u8; 32],

    // ── executor-filled (deferred to submit) ──
    /// The committed PRE-state hash — filled by the executor at submit.
    pub pre_state_hash: DeferredField<[u8; 32]>,
    /// The committed POST-state hash — filled by the executor at submit. This is
    /// the field whose silent zero the maturation ledger flagged
    /// (`apply.rs` Theme 3); it is now explicitly `Deferred`.
    pub post_state_hash: DeferredField<[u8; 32]>,
    /// The computrons the executor charged — filled at submit.
    pub computrons_used: DeferredField<u64>,
    /// The wall-clock timestamp the executor stamped — filled at submit.
    pub timestamp: DeferredField<i64>,
    /// The executor's signature over the real receipt hash — filled at submit.
    pub executor_signature: DeferredField<Vec<u8>>,
}

impl ProjectedReceipt {
    /// `true` iff every executor-filled field is still `Deferred` — the
    /// plan-time state (no live executor has run this turn yet). A submitted plan
    /// flips these to `Filled` from the executor's response.
    pub fn is_fully_deferred(&self) -> bool {
        self.pre_state_hash.is_deferred()
            && self.post_state_hash.is_deferred()
            && self.computrons_used.is_deferred()
            && self.timestamp.is_deferred()
            && self.executor_signature.is_deferred()
    }
}

/// Errors from [`plan_apply`].
#[derive(Debug, thiserror::Error)]
pub enum ApplyError {
    /// Lowering / name-resolution failed (an unknown name, a bad hex, a
    /// duplicate) — the deployment is malformed before the static check even
    /// runs.
    #[error(transparent)]
    Lower(#[from] LowerError),
    /// The static pre-submission check **refused** the deployment: the declared
    /// authority layout does not conserve, amplifies a capability, or is
    /// ill-formed. No turn sequence is produced. The carried [`Assurance`]
    /// names the precise locus (which node, which effect, which asset / grant
    /// edge) — e.g. an over-grant surfaces as a `no_amplification` finding whose
    /// message contains `amplifies`.
    #[error("deployment refused by the static pre-submission check: {0} finding(s) over the declared authority layout (run `dregg-deploy check` for the loci)", .assurance.all_findings().len())]
    Refused { assurance: Box<Assurance> },
}

/// One turn in the applied deployment plan: the submittable [`Turn`] plus the
/// **projected** receipt hash the executor's receipt for it should match, and a
/// human label of which deployment phase it came from.
#[derive(Clone, Debug)]
pub struct PlannedTurn {
    /// The submittable turn (a single-root call forest, signed and submitted by
    /// the SDK at apply time; the placeholder authorization the lowering put on
    /// the action is re-signed with the real key before submission).
    pub turn: Turn,
    /// The phase tag — `"birth"`, `"fund"`, or `"grant"` — for human-readable
    /// plan output.
    pub phase: &'static str,
    /// The agent (target cell) this turn runs as — the `from` of the root
    /// effect. The receipt chain is keyed per cell, but a deployment is one
    /// operator's causal strand, so we chain across the whole sequence.
    pub agent: CellId,
    /// The turn's own content hash ([`Turn::hash`]) — the stable id the
    /// `previous_receipt_hash` of the *next* turn would point at if receipts
    /// were content-addressed by turn. Exposed so the caller can audit the
    /// chain links.
    pub turn_hash: [u8; 32],
    /// The **projected** receipt hash: what
    /// [`TurnReceipt::receipt_hash`] would yield for this turn IF it committed
    /// against the projected (artifact-only) fields. The next turn's
    /// `previous_receipt_hash` is set to exactly this value, so the plan is a
    /// self-consistent receipt chain. NOT an executor receipt (no post-state
    /// commitment) — the chain *shape*, checkable off the artifact. (Equal to
    /// `projected_receipt.chain_link_hash`.)
    pub projected_receipt_hash: [u8; 32],
    /// The HONEST projected receipt SHAPE: the artifact-known fields as plain
    /// values, the executor-filled fields (post-state commitment, computrons,
    /// timestamp, signature) typed [`DeferredField::Deferred`] — not silently
    /// zeroed. The submit path swaps the deferred fields to `Filled` from the
    /// executor's response; the chain link does not depend on them. This is the
    /// maturation-ledger Theme-3 disposition: the planned receipt no longer reads
    /// as a live receipt with an all-zero post-state.
    pub projected_receipt: ProjectedReceipt,
}

/// The applied deployment: the ordered, receipt-chained turn sequence that a
/// PASSING DreggDL lowers to, plus the assurance that gated it.
#[derive(Clone, Debug)]
pub struct AppliedPlan {
    /// The federation this deployment binds to (bound at signing time by the
    /// SDK; all-zeros for an `"auto"` deployment).
    pub federation_id: dregg_types::FederationId,
    /// The static assurance that **passed** — every plan returned by
    /// [`plan_apply`] carries a passing assurance by construction (a failing one
    /// is returned as [`ApplyError::Refused`] instead).
    pub assurance: Assurance,
    /// The ordered turn sequence (one per root effect-group), each chained to
    /// the previous via `previous_receipt_hash`. Submitting these in order, each
    /// re-signed with the operator's key, instantiates the whole deployment.
    pub turns: Vec<PlannedTurn>,
}

impl AppliedPlan {
    /// The number of turns in the plan (= the number of root effect-groups).
    pub fn len(&self) -> usize {
        self.turns.len()
    }
    /// `true` iff the plan has no turns (an empty deployment).
    pub fn is_empty(&self) -> bool {
        self.turns.is_empty()
    }
    /// Verify the receipt-chain shape is internally consistent: the first turn
    /// has no predecessor, and each subsequent turn's `previous_receipt_hash`
    /// equals the prior turn's `projected_receipt_hash`. This is the invariant
    /// [`plan_apply`] establishes; re-checking it is what an auditor does to a
    /// plan they were handed.
    pub fn chain_is_linked(&self) -> bool {
        let mut prev: Option<[u8; 32]> = None;
        for pt in &self.turns {
            if pt.turn.previous_receipt_hash != prev {
                return false;
            }
            prev = Some(pt.projected_receipt_hash);
        }
        true
    }

    /// `true` iff EVERY turn's projected receipt is still fully deferred — the
    /// honest plan-time state: no live executor has run any turn, so the
    /// post-state commitments / computrons / timestamps / signatures are
    /// [`DeferredField::Deferred`], not zeroed. A submitted plan flips these to
    /// `Filled` from the executor's responses. This is the witness that the
    /// planned chain is a SHAPE, not a forged live receipt chain.
    pub fn receipts_are_planned_shape(&self) -> bool {
        self.turns
            .iter()
            .all(|pt| pt.projected_receipt.is_fully_deferred())
    }
}

/// THE APPLY FLOW: lower a [`Deployment`] → run the static check as the GATE →
/// emit the per-root turn sequence with the receipt-chain shape.
///
/// On a PASS, returns the [`AppliedPlan`]: one [`Turn`] per root effect-group of
/// the lowered forest (births, then funds, then grant trees, in dependency
/// order), chained so each turn's `previous_receipt_hash` is the prior turn's
/// projected receipt hash.
///
/// On a FAIL — including an over-grant caught as in-forest capability
/// amplification — returns [`ApplyError::Refused`] **without producing any
/// turn**. This is the whole point: the static check refuses non-conserving /
/// amplifying specs up front, so an operator never pays to submit a deployment
/// the executor would reject.
///
/// `as_ring`: also gate on the ring-balance check (for a settlement-ring
/// deployment declared as bare funding transfers).
pub fn plan_apply(dep: &Deployment, as_ring: bool) -> Result<AppliedPlan, ApplyError> {
    // (1) lower — name resolution + the checkable forest.
    let lowered = Lowered::from_deployment(dep)?;

    // (2) THE GATE: run the static assurance over the whole declared authority
    // layout. Refuse to emit anything if it does not pass.
    let assurance = dregg_userspace_verify::analyze(&lowered.forest, as_ring);
    if !assurance.pass() {
        return Err(ApplyError::Refused {
            assurance: Box::new(assurance),
        });
    }

    // (3) emit the per-root turn sequence + the receipt-chain shape.
    let turns = build_turn_sequence(&lowered);

    Ok(AppliedPlan {
        federation_id: lowered.federation_id,
        assurance,
        turns,
    })
}

/// [`plan_apply`] from DreggDL TOML text.
pub fn plan_apply_toml(text: &str, as_ring: bool) -> Result<AppliedPlan, crate::DeployError> {
    let dep = crate::parse_toml(text)?;
    Ok(plan_apply(&dep, as_ring)?)
}

/// Build the [`AppliedPlan`] from an already-lowered deployment **without the
/// static gate** — the per-root turn sequence + receipt-chain shape only. The
/// `assurance` is computed (non-ring) and attached but is NOT enforced.
///
/// This is the constructor for callers that want to run the **behavioral**
/// refinement gate ([`crate::refines_upgrade`] / [`crate::refines_intent`]) over
/// a deployment whose STATIC gate verdict they handle separately — e.g. to show
/// both gates' verdicts on the same over-granting spec. It does NOT bypass
/// safety: nothing is submitted, and the attached `assurance` records the (here
/// possibly failing) static verdict for inspection. Prefer [`plan_apply`] when
/// you want the gate to refuse a failing spec up front.
pub fn plan_from_lowered(lowered: &Lowered) -> AppliedPlan {
    let assurance = dregg_userspace_verify::analyze(&lowered.forest, false);
    let turns = build_turn_sequence(lowered);
    AppliedPlan {
        federation_id: lowered.federation_id,
        assurance,
        turns,
    }
}

/// Split the lowered single-turn-wide forest into one [`Turn`] per root and
/// chain them. The lowered forest already orders roots births → funds → grants
/// and nests re-delegations under their parent grant; we preserve that order
/// and that nesting (each root tree, with its children, becomes one turn).
fn build_turn_sequence(lowered: &Lowered) -> Vec<PlannedTurn> {
    let fed = lowered.federation_id.0;
    let mut out: Vec<PlannedTurn> = Vec::with_capacity(lowered.forest.roots.len());
    let mut prev_receipt: Option<[u8; 32]> = None;

    for (i, root) in lowered.forest.roots.iter().enumerate() {
        let agent = root.action.target;
        let phase = phase_of(&root.action.method);

        // One single-root forest carrying this root tree (children = nested
        // re-delegations) verbatim, so the per-turn forest hash binds the whole
        // sub-tree the checker walked.
        let mut call_forest = CallForest {
            roots: vec![root.clone()],
            forest_hash: [0u8; 32],
        };
        call_forest.forest_hash = call_forest.compute_hash();

        // The turn. nonce = the root's position in the deployment sequence (a
        // deterministic, monotone-per-agent placeholder; the SDK re-stamps the
        // real nonce from the live c-list at submit time). Authorization lives
        // on the action inside the forest, re-signed by the SDK.
        let turn = Turn {
            agent,
            nonce: i as u64,
            call_forest,
            fee: 0,
            memo: Some(format!("dregg-deploy:{phase}")),
            valid_until: None,
            previous_receipt_hash: prev_receipt,
            depends_on: prev_turn_hash(&out).map(|h| vec![h]).unwrap_or_default(),
            conservation_proof: None,
            sovereign_witnesses: Default::default(),
            execution_proof: None,
            execution_proof_cell: None,
            execution_proof_new_commitment: None,
            custom_program_proofs: None,
            effect_binding_proofs: Vec::new(),
            cross_effect_dependencies: Vec::new(),
            effect_witness_index_map: Vec::new(),
        };

        let turn_hash = turn.hash();
        let projected_receipt = project_receipt(&turn, agent, fed, prev_receipt);
        let projected_receipt_hash = projected_receipt.chain_link_hash;

        out.push(PlannedTurn {
            turn,
            phase,
            agent,
            turn_hash,
            projected_receipt_hash,
            projected_receipt,
        });
        prev_receipt = Some(projected_receipt_hash);
    }
    out
}

/// The previous turn's content hash, for the `depends_on` causal edge.
fn prev_turn_hash(out: &[PlannedTurn]) -> Option<[u8; 32]> {
    out.last().map(|pt| pt.turn_hash)
}

/// Project the [`ProjectedReceipt`] for a planned turn off the artifact alone.
///
/// The artifact-known half (turn hash, forest hash, effects hash, agent,
/// federation, action count, the chain link) is computed directly. The
/// executor-filled half (pre/post-state commitments, computrons, timestamp,
/// executor signature) is typed [`DeferredField::Deferred`] — it is knowable
/// only by running the turn against live state at submit time.
///
/// The `chain_link_hash` IS the deterministic chain-shape digest the next turn
/// points at: it is the `receipt_hash` of a `TurnReceipt` whose dynamic fields
/// take their ZERO placeholders (a chain SHAPE must be a pure function of the
/// artifact, so the unknown fields enter as zero), and whose artifact fields are
/// the real ones. So the link is unchanged from the prior projection — but the
/// shape is no longer a `TurnReceipt` masquerading as live; the zero only enters
/// the *link digest*, never a field a reader could mistake for a real commitment.
///
/// The honest boundary: see module docs + `dregg_userspace_verify::boundary`.
fn project_receipt(
    turn: &Turn,
    agent: CellId,
    federation_id: [u8; 32],
    previous_receipt_hash: Option<[u8; 32]>,
) -> ProjectedReceipt {
    let forest_hash = turn.call_forest.compute_hash();
    let effects_hash = effects_hash(&turn.call_forest);
    let action_count = turn.call_forest.action_count();
    // The chain-shape digest: the artifact fields are real, the dynamic fields
    // are their zero placeholders (a chain SHAPE is a pure function of the
    // artifact — the executor's real receipt rehashes with the live fields and
    // is checked link-for-link against THIS shape at submit).
    let chain_link_hash = TurnReceipt {
        turn_hash: turn.hash(),
        forest_hash,
        pre_state_hash: [0u8; 32],
        post_state_hash: [0u8; 32],
        timestamp: 0,
        effects_hash,
        computrons_used: 0,
        action_count,
        previous_receipt_hash,
        agent,
        federation_id,
        routing_directives: Vec::new(),
        introduction_exports: Vec::new(),
        derivation_records: Vec::new(),
        emitted_events: Vec::new(),
        executor_signature: None,
        finality: Default::default(),
        was_encrypted: false,
        was_burn: false,
        consumed_capabilities: Vec::new(),
    }
    .receipt_hash();

    ProjectedReceipt {
        turn_hash: turn.hash(),
        forest_hash,
        effects_hash,
        agent,
        federation_id,
        action_count,
        previous_receipt_hash,
        chain_link_hash,
        // The executor-filled half: deferred until the live submit, NOT zeroed.
        pre_state_hash: DeferredField::Deferred,
        post_state_hash: DeferredField::Deferred,
        computrons_used: DeferredField::Deferred,
        timestamp: DeferredField::Deferred,
        executor_signature: DeferredField::Deferred,
    }
}

/// A deterministic digest of every effect in the forest (the artifact-only
/// `effects_hash` projection: a BLAKE3 over each effect's serialized form, in
/// DFS order). Binds the receipt-chain shape to the actual effects, so a turn
/// whose effects were tampered projects a different chain. Uses `serde_json`
/// (already a dep) for the stable per-effect serialization — `Effect` is a
/// fixed serde shape, so the bytes are deterministic for a given effect.
fn effects_hash(forest: &CallForest) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new();
    hasher.update(b"dregg-deploy-effects-v1:");
    for eff in forest.total_effects() {
        if let Ok(bytes) = serde_json::to_vec(eff) {
            hasher.update(&(bytes.len() as u64).to_le_bytes());
            hasher.update(&bytes);
        }
    }
    *hasher.finalize().as_bytes()
}

/// Map the lowered action method symbol back to a human phase tag.
fn phase_of(method: &dregg_turn::action::Symbol) -> &'static str {
    let want_create = dregg_turn::action::symbol("deploy.create_cell");
    let want_fund = dregg_turn::action::symbol("deploy.fund");
    let want_grant = dregg_turn::action::symbol("deploy.grant");
    if *method == want_create {
        "birth"
    } else if *method == want_fund {
        "fund"
    } else if *method == want_grant {
        "grant"
    } else {
        "other"
    }
}
