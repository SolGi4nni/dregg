//! # starbridge-polis — governance cells + agent-orchestration mandates
//!
//! The polis layer: the userspace that makes the verified kernel a livable
//! place. Three cell families, all built the same way as the settlement
//! blueprints (`cell/src/blueprint.rs`, the frozen reference pattern):
//! per-charter **content-addressed [`FactoryDescriptor`]s** whose
//! `state_constraints` ARE the enforced state machines. The executor
//! re-evaluates the installed program on EVERY turn that touches the cell
//! (`turn/src/executor/execute_tree.rs`); the negative e2e tests in
//! `sdk/tests/polis_*_e2e.rs` hand the executor well-signed turns and assert
//! it rejects with `TurnError::ProgramViolation`.
//!
//! | family | module | machine |
//! |--------|--------|---------|
//! | council proposal | [`council`] | DRAFT → PROPOSED → {REJECTED, APPROVED → EXECUTED}, M-of-N gated |
//! | constitution | [`constitution`] | UNINIT → ACTIVE → SUPERSEDED, params pinned for life |
//! | amendment proposal | [`council`] (amendment variant) | council machine + cooling-period `TemporalGate` on ENACT |
//! | worker mandate | [`mandate`] | UNINIT → ACTIVE → REVOKED, slice/scope pinned, REVOKED inert |
//!
//! ## The polis design in one paragraph
//!
//! A **council** is a factory: its membership + threshold are content-addressed
//! into the `factory_vk`, and each proposal is one cell born from it. A
//! **constitution** is a per-version cell whose parameters are pinned literals
//! — changes are *impossible* on the cell itself; an **amendment** is a
//! council-style proposal cell that stages the successor constitution's
//! descriptor hash, requires M-of-N approval, and whose ENACT transition is
//! gated by a `TemporalGate` cooling period baked into the amendment's own
//! descriptor. Enactment births the successor constitution cell and steps the
//! old one to SUPERSEDED (terminal, inert) with the successor hash recorded.
//! The receipt chain of that ceremony IS the forward certification. A
//! **worker mandate** is a per-worker cell whose budget slice is its own
//! funded balance (conservation is the kernel move law — overspend simply
//! cannot commit) and whose tool-scope is a pinned literal; revocation steps
//! it to a terminal state with no outgoing transition row, so every
//! subsequent touch is rejected.
//!
//! Two principles run through all of it:
//!
//! * **Adoption is attenuation** — joining the polis means running under a
//!   program someone can recompute. Every charter, constitution, and mandate
//!   is content-addressed: the `factory_vk` IS the governance terms, so "is
//!   this council the constitutional one?" is a hash check, not a trust
//!   relation.
//! * **Governance must be legible** — what the executor enforces, anyone can
//!   READ back out of the ledger. [`council::inspect_council`] decodes a
//!   proposal cell's machine from its 8 slots (pure; works on a node read, a
//!   receipt's post-state, or a light-client proof) and is the shared
//!   decoder behind the CLI (`dregg polis council`) and the Discord
//!   `/council-status` surface.
//!
//! ## Expressibility gaps (documented, NOT shimmed — dregg4 guard-algebra feed)
//!
//! The `StateConstraint` grammar evaluates over the 8 field slots of the ONE
//! touched cell's post-state (+ old state + block height). The following legs
//! of the polis semantics are therefore **not program-enforced**; each is
//! listed with what carries it instead:
//!
//! 1. **Member ↔ approval-slot sender binding.** The program cannot see which
//!    key signed the turn (no per-slot sender predicate; `SenderAuthorized`
//!    is whole-cell and witness-blob-driven, and would also gate the
//!    operator's own propose/execute turns). What IS enforced: each approval
//!    is a distinct slot, bounded to {0,1}, monotone (no un-approve), and
//!    gated on a staged proposal — so the approval COUNT is over distinct
//!    member slots by construction, and double-approving one slot cannot
//!    reach the threshold. WHO may flip slot *i* is carried by capability
//!    possession (only cap holders can drive the cell at all) + operator
//!    discipline; receipts record the signer for audit.
//! 2. **Cross-cell reads.** A proposal/amendment cell cannot read the
//!    constitution cell's parameters. The honest pattern (used here):
//!    constitutional parameters are COPIED into dependent descriptors at
//!    build time by the SDK builders (`dregg_sdk::polis`), and an amendment
//!    REISSUES the constitution as a new per-version cell — the parameters
//!    are content-addressed, so a builder that lies about them produces a
//!    visibly different `factory_vk`.
//! 3. **The executed action matching the staged hash.** The proposal stages a
//!    32-byte action hash; the program cannot interpret that hash as a set of
//!    effects, so "the execute turn performs exactly the proposed action" is
//!    carried by the SDK builder (the execute turn carries the action effects
//!    in the SAME turn as the EXECUTED step, so the receipt binds them) and
//!    by verifiers recomputing the hash from the receipt.
//! 4. **Supersede only after an enacted amendment.** The constitution cell
//!    cannot verify the amendment cell reached ENACTED (cross-cell). What IS
//!    enforced on the constitution: parameters can never change, supersede
//!    happens at most once, requires a nonzero successor hash, and the
//!    superseded cell is terminally inert. The ceremony ordering is carried
//!    by the receipt chain (amendment ENACT receipt precedes the supersede
//!    receipt) — the forward certification.
//! 5. **Worker slice as a numeric cap.** The cell `balance` is sealed from
//!    `StateConstraint` (not one of the 8 slots), so "spent ≤ slice" is not a
//!    program predicate; it is the kernel conservation law: the worker is
//!    funded with EXACTLY its slice, and a spend exceeding the remaining
//!    balance cannot commit. The pinned `SLICE` slot publishes the slice for
//!    audit; it is not the enforcement.
//! 6. **Tool-scope semantics.** The mandate's tool scope is a pinned 32-byte
//!    commitment (e.g. the hash of the allowed tool list). The program cannot
//!    decode which "tool" a turn used; per-tool gating lives at the MCP
//!    capability layer (`node/src/mcp.rs`). The cell publishes the scope so
//!    every spend receipt is traceable to the mandate's published terms.
//! 7. **Slot budget.** With 8 constraint-visible slots, a council cell
//!    supports at most [`council::MAX_MEMBERS`] (= 3) members
//!    (state + proposal hash + approved flag + 3 approval slots + membership
//!    commitment + reserved). Larger councils need the dregg4 grammar
//!    (dynamic member sets / map-slot constraints).

#![forbid(unsafe_code)]

use dregg_cell::factory::{CapTarget, CapTemplate, ChildVkStrategy, FactoryDescriptor};
use dregg_cell::permissions::AuthRequired;
use dregg_cell::program::{CellProgram, SimpleStateConstraint, StateConstraint, field_from_u64};
use dregg_cell::state::{FIELD_ZERO, FieldElement};
use dregg_cell::{CellId, CellMode};

/// Lifecycle state-code slot — slot 0 in every polis cell family.
pub const STATE_SLOT: u8 = 0;

// =============================================================================
// Errors
// =============================================================================

/// A charter / parameter set the polis blueprints refuse to publish
/// (fail-closed at build).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PolisError {
    /// A council charter with no members cannot gate anything.
    NoMembers,
    /// More members than the 8-slot grammar can hold (see module docs, gap 7).
    TooManyMembers { got: usize, max: usize },
    /// Threshold must satisfy `1 <= threshold <= members.len()`.
    ThresholdOutOfRange { threshold: u64, members: usize },
    /// Duplicate member ids would let one member fill two approval slots.
    DuplicateMember,
    /// Member index out of range for this charter.
    BadMemberIndex { index: usize, members: usize },
    /// An amendment must stage a nonzero successor-constitution hash (a zero
    /// hash is indistinguishable from the unstaged slot).
    ZeroAmendmentHash,
    /// Constitution version must be >= 1 (0 is the unborn slot value).
    ZeroVersion,
    /// Constitution council threshold parameter must be >= 1.
    ZeroThresholdParam,
    /// A proposal treasury exceeding the constitutional cap. Enforced
    /// fail-closed at descriptor build by the SDK's constitution-governed
    /// builders (the balance is sealed from `StateConstraint` — lib docs
    /// gap 5 — so the cap is a builder gate, not a program gate; documented,
    /// not shimmed).
    EndowmentExceedsTreasuryCap { endowment: u64, cap: u64 },
    /// A worker mandate with a zero budget slice can do nothing; rejected so
    /// a forgotten slice fails loudly at build, not silently at spend.
    ZeroSlice,
    /// The tool-scope commitment must be nonzero (a zero scope is
    /// indistinguishable from the unborn slot).
    ZeroToolScope,
}

impl std::fmt::Display for PolisError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PolisError::NoMembers => write!(f, "council charter must list at least one member"),
            PolisError::TooManyMembers { got, max } => {
                write!(f, "council charter lists {got} members; slot grammar holds at most {max}")
            }
            PolisError::ThresholdOutOfRange { threshold, members } => write!(
                f,
                "threshold {threshold} out of range for {members} members (need 1 <= M <= N)"
            ),
            PolisError::DuplicateMember => write!(f, "council members must be distinct"),
            PolisError::BadMemberIndex { index, members } => {
                write!(f, "member index {index} out of range ({members} members)")
            }
            PolisError::ZeroAmendmentHash => {
                write!(f, "amendment must stage a nonzero successor-constitution hash")
            }
            PolisError::ZeroVersion => write!(f, "constitution version must be >= 1"),
            PolisError::ZeroThresholdParam => {
                write!(f, "constitution council-threshold parameter must be >= 1")
            }
            PolisError::EndowmentExceedsTreasuryCap { endowment, cap } => write!(
                f,
                "proposal endowment {endowment} exceeds the constitutional treasury cap {cap}"
            ),
            PolisError::ZeroSlice => write!(f, "worker mandate slice must be nonzero"),
            PolisError::ZeroToolScope => {
                write!(f, "worker mandate tool-scope commitment must be nonzero")
            }
        }
    }
}

impl std::error::Error for PolisError {}

// =============================================================================
// Shared constraint helpers (the blueprint.rs idioms)
// =============================================================================

/// `state == code` as a [`SimpleStateConstraint`] (big-endian u64 encoding).
fn state_is(code: u64) -> SimpleStateConstraint {
    SimpleStateConstraint::FieldEquals {
        index: STATE_SLOT,
        value: field_from_u64(code),
    }
}

/// Pin `slot` to `lit` whenever the cell has left its birth state (state 0):
/// `AnyOf[ state == 0, slot == lit ]`. Once the cell is activated/proposed,
/// the term can never differ from the descriptor's published literal.
fn pin_term(slot: u8, lit: FieldElement) -> StateConstraint {
    StateConstraint::AnyOf {
        variants: vec![
            state_is(0),
            SimpleStateConstraint::FieldEquals { index: slot, value: lit },
        ],
    }
}

/// `state == gate_state ⇒ consequent`, encoded as `AnyOf[¬(state==gate), consequent]`.
fn when_state(gate_state: u64, consequent: SimpleStateConstraint) -> StateConstraint {
    StateConstraint::AnyOf {
        variants: vec![
            SimpleStateConstraint::Not(Box::new(state_is(gate_state))),
            consequent,
        ],
    }
}

/// A slot that is pinned to zero for the cell's whole life (reserved slots,
/// non-member approval slots). Rejects ANY write.
fn pinned_zero(slot: u8) -> StateConstraint {
    StateConstraint::FieldEquals {
        index: slot,
        value: FIELD_ZERO,
    }
}

/// Build a per-charter descriptor around a constraint set, content-addressed
/// over the constraints (which bake every charter term as literals) under a
/// family domain tag. Two distinct charters get distinct factories; the same
/// charter is re-derivable by any party.
fn polis_descriptor(
    domain_tag: &str,
    constraints: Vec<StateConstraint>,
    creation_budget: Option<u64>,
) -> FactoryDescriptor {
    let program = CellProgram::Predicate(constraints.clone());
    let child_vk = dregg_cell::factory::canonical_program_vk(&program);
    let mut hasher = blake3::Hasher::new_derive_key(domain_tag);
    let encoded = postcard::to_allocvec(&constraints).unwrap_or_default();
    hasher.update(&(encoded.len() as u64).to_le_bytes());
    hasher.update(&encoded);
    let factory_vk = *hasher.finalize().as_bytes();
    FactoryDescriptor {
        factory_vk,
        child_program_vk: Some(child_vk),
        child_vk_strategy: Some(ChildVkStrategy::Fixed(Some(child_vk))),
        allowed_cap_templates: vec![CapTemplate {
            target: CapTarget::SelfCell,
            max_permissions: AuthRequired::Signature,
            attenuatable: true,
        }],
        field_constraints: vec![],
        state_constraints: constraints,
        default_mode: CellMode::Hosted,
        creation_budget,
    }
}

/// Encode a cell identity as a 32-byte pinned-term field (matches
/// `dregg_sdk::factories::party_field`).
pub fn party_field(cell: CellId) -> FieldElement {
    *cell.as_bytes()
}

// =============================================================================
// Council — M-of-N proposal cells
// =============================================================================

pub mod council {
    //! The council proposal cell: M-of-N member approval over a staged
    //! action hash.
    //!
    //! ## Slot schema
    //!
    //! | slot | name | constraint teeth |
    //! |------|------|------------------|
    //! | 0 | STATE | `AllowedTransitions` (the machine below) + `BoundedBy(PROPOSAL_HASH)` |
    //! | 1 | PROPOSAL_HASH | `WriteOnce` (one proposal per cell) |
    //! | 2 | APPROVED_FLAG | `{0,1}`, monotone, arming requires `Σ approvals >= M` (`AffineLe`) |
    //! | 3..3+N | approval slot per member | `{0,1}`, monotone, requires staged proposal |
    //! | 3+N..6 | non-member approval slots | pinned zero (a "non-member approval" cannot exist) |
    //! | 6 | MEMBERS_COMMIT | pinned to `blake3(threshold ‖ members)` once proposed |
    //! | 7 | reserved | pinned zero |
    //!
    //! ## The machine (enforced by `AllowedTransitions`; terminal states have
    //! no outgoing row, so REJECTED/EXECUTED cells are inert — no double
    //! execute, not even a transfer in)
    //!
    //! ```text
    //!   DRAFT(0, birth) ──propose (stages hash)──▶ PROPOSED(1)
    //!                                                │  │
    //!                              reject ◀──────────┘  └────▶ APPROVED(3)   [requires flag=1 ⇒ Σ approvals >= M]
    //!                                │                            │
    //!                                ▼                            ▼
    //!                          REJECTED(2) [terminal]       EXECUTED(4) [terminal]
    //! ```
    //!
    //! ## The threshold gate, precisely
    //!
    //! `AffineLe { M·flag − Σ approvalᵢ <= 0 }` makes arming the flag demand
    //! `Σ approvals >= M` in the same post-state; `APPROVED`/`EXECUTED` each
    //! require `flag == 1` (full 32-byte equality); approvals and the flag are
    //! monotone, so once armed the inequality stays satisfied — the gate is
    //! an inductive invariant, not a one-shot check. Approval slots are
    //! distinct per member, so the count is over DISTINCT approvers by
    //! construction (double-approving one slot is idempotent).

    use super::*;

    /// Maximum members an 8-slot council cell supports (see lib docs, gap 7).
    pub const MAX_MEMBERS: usize = 3;

    /// Slot 1 — the staged action hash (write-once; one proposal per cell).
    /// For amendment cells this is the successor constitution's descriptor
    /// hash, additionally pinned to the descriptor literal.
    pub const PROPOSAL_HASH_SLOT: u8 = 1;
    /// Slot 2 — the threshold-certification flag (`{0,1}`, monotone; arming
    /// it is the `Σ approvals >= M` gate).
    pub const APPROVED_FLAG_SLOT: u8 = 2;
    /// Slots 3..6 — one approval bit per member, in charter order.
    pub const FIRST_APPROVAL_SLOT: u8 = 3;
    /// Slot 6 — the published membership commitment (pinned literal).
    pub const MEMBERS_COMMIT_SLOT: u8 = 6;
    /// Slot 7 — reserved, pinned zero.
    pub const RESERVED_SLOT: u8 = 7;

    /// Birth state of a factory-born proposal cell.
    pub const STATE_DRAFT: u64 = 0;
    /// A proposal hash is staged; approvals are open.
    pub const STATE_PROPOSED: u64 = 1;
    /// Terminal: the council declined. Inert.
    pub const STATE_REJECTED: u64 = 2;
    /// Threshold certified (`flag == 1`, `Σ approvals >= M`).
    pub const STATE_APPROVED: u64 = 3;
    /// Terminal: the proposed action was executed (its effects ride in the
    /// same turn as this step). Inert — no double execute.
    pub const STATE_EXECUTED: u64 = 4;

    /// A council charter: the published membership + threshold. Identifies
    /// the council — the factory vk is content-addressed over it.
    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct CouncilCharter {
        /// Member cells, in slot order (member `i` approves via slot
        /// `FIRST_APPROVAL_SLOT + i`). At most [`MAX_MEMBERS`].
        pub members: Vec<CellId>,
        /// Approvals required to certify (`1 <= threshold <= members.len()`).
        pub threshold: u64,
    }

    impl CouncilCharter {
        /// Fail-closed validation (see [`PolisError`]).
        pub fn validate(&self) -> Result<(), PolisError> {
            if self.members.is_empty() {
                return Err(PolisError::NoMembers);
            }
            if self.members.len() > MAX_MEMBERS {
                return Err(PolisError::TooManyMembers {
                    got: self.members.len(),
                    max: MAX_MEMBERS,
                });
            }
            if self.threshold == 0 || self.threshold > self.members.len() as u64 {
                return Err(PolisError::ThresholdOutOfRange {
                    threshold: self.threshold,
                    members: self.members.len(),
                });
            }
            for (i, m) in self.members.iter().enumerate() {
                if self.members[..i].contains(m) {
                    return Err(PolisError::DuplicateMember);
                }
            }
            Ok(())
        }

        /// The approval slot for member `index` (charter order).
        pub fn approval_slot(&self, index: usize) -> Result<u8, PolisError> {
            if index >= self.members.len() {
                return Err(PolisError::BadMemberIndex {
                    index,
                    members: self.members.len(),
                });
            }
            Ok(FIRST_APPROVAL_SLOT + index as u8)
        }

        /// The published membership commitment:
        /// `blake3("dregg-polis:council-members v1", threshold ‖ memberᵢ…)`.
        /// Pinned into [`MEMBERS_COMMIT_SLOT`] once the cell leaves DRAFT, so
        /// the cell itself publishes which membership gates it.
        pub fn members_commitment(&self) -> FieldElement {
            let mut hasher = blake3::Hasher::new_derive_key("dregg-polis:council-members v1");
            hasher.update(&self.threshold.to_be_bytes());
            hasher.update(&(self.members.len() as u64).to_be_bytes());
            for m in &self.members {
                hasher.update(m.as_bytes());
            }
            *hasher.finalize().as_bytes()
        }
    }

    /// The shared council/amendment constraint generator. `enact_not_before`
    /// is the amendment variant's cooling gate: entering EXECUTED is
    /// additionally gated on `block_height >= h`. `pinned_proposal_hash`
    /// pins the staged hash to a descriptor literal (amendments publish
    /// WHICH successor they stage; plain councils stage per-proposal).
    pub(crate) fn machine_constraints(
        charter: &CouncilCharter,
        pinned_proposal_hash: Option<FieldElement>,
        enact_not_before: Option<u64>,
    ) -> Vec<StateConstraint> {
        let n = charter.members.len();
        let m = charter.threshold;
        let mut cs = vec![
            // ── the state machine; terminal states have NO outgoing row ──
            StateConstraint::AllowedTransitions {
                slot_index: STATE_SLOT,
                allowed: vec![
                    (field_from_u64(STATE_DRAFT), field_from_u64(STATE_DRAFT)),
                    (field_from_u64(STATE_DRAFT), field_from_u64(STATE_PROPOSED)),
                    (field_from_u64(STATE_PROPOSED), field_from_u64(STATE_PROPOSED)),
                    (field_from_u64(STATE_PROPOSED), field_from_u64(STATE_REJECTED)),
                    (field_from_u64(STATE_PROPOSED), field_from_u64(STATE_APPROVED)),
                    (field_from_u64(STATE_APPROVED), field_from_u64(STATE_APPROVED)),
                    (field_from_u64(STATE_APPROVED), field_from_u64(STATE_EXECUTED)),
                ],
            },
            // ── one proposal per cell; any state step requires a staged hash ──
            StateConstraint::WriteOnce { index: PROPOSAL_HASH_SLOT },
            StateConstraint::BoundedBy {
                index: STATE_SLOT,
                witness_index: PROPOSAL_HASH_SLOT,
            },
            // ── membership publication (pinned once out of DRAFT) ──
            pin_term(MEMBERS_COMMIT_SLOT, charter.members_commitment()),
            // ── the certification flag: a monotone bit, armable only with a
            //    staged proposal ──
            StateConstraint::MemberOf { index: APPROVED_FLAG_SLOT, set: vec![0, 1] },
            StateConstraint::Monotonic { index: APPROVED_FLAG_SLOT },
            StateConstraint::BoundedBy {
                index: APPROVED_FLAG_SLOT,
                witness_index: PROPOSAL_HASH_SLOT,
            },
            // ── THE THRESHOLD GATE: M·flag − Σ approvals <= 0 ──
            StateConstraint::AffineLe {
                terms: std::iter::once((m as i64, APPROVED_FLAG_SLOT))
                    .chain((0..n).map(|i| (-1i64, FIRST_APPROVAL_SLOT + i as u8)))
                    .collect(),
                c: 0,
            },
            // ── APPROVED / EXECUTED demand the certified flag ──
            when_state(
                STATE_APPROVED,
                SimpleStateConstraint::FieldEquals {
                    index: APPROVED_FLAG_SLOT,
                    value: field_from_u64(1),
                },
            ),
            when_state(
                STATE_EXECUTED,
                SimpleStateConstraint::FieldEquals {
                    index: APPROVED_FLAG_SLOT,
                    value: field_from_u64(1),
                },
            ),
        ];
        // ── per-member approval bits: {0,1}, monotone (no un-approve),
        //    admitted only with a staged proposal ──
        for i in 0..n {
            let slot = FIRST_APPROVAL_SLOT + i as u8;
            cs.push(StateConstraint::MemberOf { index: slot, set: vec![0, 1] });
            cs.push(StateConstraint::Monotonic { index: slot });
            cs.push(StateConstraint::BoundedBy {
                index: slot,
                witness_index: PROPOSAL_HASH_SLOT,
            });
        }
        // ── non-member approval slots are pinned zero: an approval outside
        //    the charter's membership CANNOT exist ──
        for i in n..MAX_MEMBERS {
            cs.push(pinned_zero(FIRST_APPROVAL_SLOT + i as u8));
        }
        cs.push(pinned_zero(RESERVED_SLOT));
        // ── amendment variant: pin the staged hash + the cooling period ──
        if let Some(hash) = pinned_proposal_hash {
            cs.push(pin_term(PROPOSAL_HASH_SLOT, hash));
        }
        if let Some(h) = enact_not_before {
            cs.push(when_state(
                STATE_EXECUTED,
                SimpleStateConstraint::TemporalGate {
                    not_before: Some(h),
                    not_after: None,
                },
            ));
        }
        cs
    }

    /// The council proposal constraint set (see the module docs for the
    /// machine and the threshold gate).
    pub fn council_state_constraints(
        charter: &CouncilCharter,
    ) -> Result<Vec<StateConstraint>, PolisError> {
        charter.validate()?;
        Ok(machine_constraints(charter, None, None))
    }

    /// The `CellProgram` installed on every proposal cell of this council.
    pub fn council_cell_program(charter: &CouncilCharter) -> Result<CellProgram, PolisError> {
        Ok(CellProgram::Predicate(council_state_constraints(charter)?))
    }

    /// **The council factory (per-charter, content-addressed).** Each
    /// proposal is one cell born from this factory; the membership +
    /// threshold are baked into every proposal cell's program for life.
    /// Unbounded creation budget: a council may consider many proposals.
    pub fn council_factory_descriptor(
        charter: &CouncilCharter,
    ) -> Result<FactoryDescriptor, PolisError> {
        Ok(polis_descriptor(
            "dregg-polis:council-factory v1",
            council_state_constraints(charter)?,
            None,
        ))
    }

    /// The terms of one constitutional amendment: the council that must
    /// certify it, the successor constitution it stages, and the absolute
    /// height before which enactment is forbidden (the cooling period; the
    /// SDK builder derives it as `propose_height + constitution.amendment_delay`
    /// and content-addressing makes the chosen gate auditable).
    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct AmendmentTerms {
        /// The certifying council.
        pub charter: CouncilCharter,
        /// The successor constitution's `FactoryDescriptor::hash()` — pinned
        /// into [`PROPOSAL_HASH_SLOT`] as a descriptor literal, so the
        /// amendment cell publishes exactly which constitution it enacts.
        pub new_constitution_hash: FieldElement,
        /// ENACT (the EXECUTED transition) is admitted only at
        /// `block_height >= enact_not_before` (`TemporalGate`).
        pub enact_not_before: u64,
    }

    /// The amendment-proposal constraint set: the council machine + the
    /// pinned successor hash + the cooling-period gate on ENACT.
    pub fn amendment_state_constraints(
        terms: &AmendmentTerms,
    ) -> Result<Vec<StateConstraint>, PolisError> {
        terms.charter.validate()?;
        if terms.new_constitution_hash == FIELD_ZERO {
            return Err(PolisError::ZeroAmendmentHash);
        }
        Ok(machine_constraints(
            &terms.charter,
            Some(terms.new_constitution_hash),
            Some(terms.enact_not_before),
        ))
    }

    /// The `CellProgram` installed on the amendment proposal cell.
    pub fn amendment_cell_program(terms: &AmendmentTerms) -> Result<CellProgram, PolisError> {
        Ok(CellProgram::Predicate(amendment_state_constraints(terms)?))
    }

    /// **The amendment factory (per-amendment, content-addressed).** Births
    /// exactly ONE amendment proposal cell; the cooling gate and the staged
    /// successor hash are part of its content address.
    pub fn amendment_factory_descriptor(
        terms: &AmendmentTerms,
    ) -> Result<FactoryDescriptor, PolisError> {
        Ok(polis_descriptor(
            "dregg-polis:amendment-factory v1",
            amendment_state_constraints(terms)?,
            Some(1),
        ))
    }

    // -------------------------------------------------------------------------
    // Legibility — read the machine back out of the ledger
    // -------------------------------------------------------------------------

    /// One proposal-cell lifecycle state, decoded.
    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub enum ProposalState {
        /// Birth state; nothing staged yet.
        Draft,
        /// A proposal is staged; approvals are open.
        Proposed,
        /// Terminal: declined.
        Rejected,
        /// Threshold certified.
        Approved,
        /// Terminal: executed exactly once.
        Executed,
        /// Not a value this machine emits (a foreign or corrupted cell).
        Unknown(u64),
    }

    /// A council proposal cell, made legible: the decoded machine state, the
    /// staged hash, and per-member approvals in charter order. Governance the
    /// polis can READ is governance the polis can trust — this is the shared
    /// decoder for every inspection surface (CLI, bots, verifiers), pure over
    /// the cell's 8 field slots.
    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct CouncilStatus {
        /// Decoded lifecycle state.
        pub state: ProposalState,
        /// The staged action hash (zero = nothing staged).
        pub proposal_hash: FieldElement,
        /// Whether the membership commitment slot matches the charter
        /// (false on DRAFT cells — published at propose — or foreign cells).
        pub members_commit_matches: bool,
        /// Per-member approval bits, charter order.
        pub approvals: Vec<bool>,
        /// `approvals.iter().filter(|a| **a).count()` — distinct approvers.
        pub approval_count: u64,
        /// The charter threshold, for display alongside the count.
        pub threshold: u64,
        /// Whether the threshold-certification flag is armed.
        pub certified: bool,
    }

    /// Decode a proposal cell's fields against its charter. Pure — callers
    /// fetch the 8 slots from any ledger view (a node query, a receipt's
    /// post-state witness, a light-client proof) and render.
    pub fn inspect_council(charter: &CouncilCharter, fields: &[FieldElement; 8]) -> CouncilStatus {
        let to_u64 = |f: &FieldElement| {
            let mut b = [0u8; 8];
            b.copy_from_slice(&f[24..32]);
            u64::from_be_bytes(b)
        };
        let state = match to_u64(&fields[STATE_SLOT as usize]) {
            STATE_DRAFT => ProposalState::Draft,
            STATE_PROPOSED => ProposalState::Proposed,
            STATE_REJECTED => ProposalState::Rejected,
            STATE_APPROVED => ProposalState::Approved,
            STATE_EXECUTED => ProposalState::Executed,
            other => ProposalState::Unknown(other),
        };
        let approvals: Vec<bool> = (0..charter.members.len())
            .map(|i| to_u64(&fields[(FIRST_APPROVAL_SLOT + i as u8) as usize]) == 1)
            .collect();
        let approval_count = approvals.iter().filter(|a| **a).count() as u64;
        CouncilStatus {
            state,
            proposal_hash: fields[PROPOSAL_HASH_SLOT as usize],
            members_commit_matches: fields[MEMBERS_COMMIT_SLOT as usize]
                == charter.members_commitment(),
            approvals,
            approval_count,
            threshold: charter.threshold,
            certified: to_u64(&fields[APPROVED_FLAG_SLOT as usize]) == 1,
        }
    }
}

// =============================================================================
// Constitution — parameters-as-pinned-program, per-version cells
// =============================================================================

pub mod constitution {
    //! The constitution cell: the polis's constitutional parameters as a
    //! per-version cell whose program FORBIDS parameter changes outright.
    //!
    //! ## Slot schema
    //!
    //! | slot | name | constraint teeth |
    //! |------|------|------------------|
    //! | 0 | STATE | `AllowedTransitions` UNINIT→ACTIVE→SUPERSEDED, SUPERSEDED terminal |
    //! | 1 | VERSION | pinned literal |
    //! | 2 | COUNCIL_THRESHOLD | pinned literal |
    //! | 3 | AMENDMENT_DELAY | pinned literal (blocks of cooling before enact) |
    //! | 4 | TREASURY_CAP | pinned literal |
    //! | 5 | SUCCESSOR_HASH | `WriteOnce`; zero while ACTIVE; nonzero at SUPERSEDED |
    //! | 6,7 | reserved | pinned zero |
    //!
    //! Amendment is REISSUE, not mutation: parameters are immutable for the
    //! cell's whole life (the strongest expressible form of "no changes
    //! except via the amendment flow" — changes on THIS cell are impossible;
    //! the amendment flow births the successor cell and steps this one to
    //! SUPERSEDED exactly once, recording the successor's descriptor hash).
    //! Dependent cells receive the parameters at descriptor-build time from
    //! the SDK builders; an amendment reissues dependent descriptors (see
    //! lib docs, gap 2).

    use super::*;

    /// Slot 1 — the constitution version (>= 1; pinned).
    pub const VERSION_SLOT: u8 = 1;
    /// Slot 2 — the council threshold parameter (pinned).
    pub const COUNCIL_THRESHOLD_SLOT: u8 = 2;
    /// Slot 3 — the amendment cooling delay in blocks (pinned).
    pub const AMENDMENT_DELAY_SLOT: u8 = 3;
    /// Slot 4 — the treasury cap parameter (pinned).
    pub const TREASURY_CAP_SLOT: u8 = 4;
    /// Slot 5 — the successor constitution's descriptor hash (write-once;
    /// must be zero while ACTIVE and nonzero at SUPERSEDED).
    pub const SUCCESSOR_HASH_SLOT: u8 = 5;
    /// Slots 6, 7 — reserved, pinned zero.
    pub const RESERVED_SLOTS: [u8; 2] = [6, 7];

    /// Birth state (all slots zero; parameters not yet written).
    pub const STATE_UNINIT: u64 = 0;
    /// The constitution is in force; parameters pinned.
    pub const STATE_ACTIVE: u64 = 1;
    /// Terminal: superseded by the successor recorded in
    /// [`SUCCESSOR_HASH_SLOT`]. Inert.
    pub const STATE_SUPERSEDED: u64 = 2;

    /// The constitutional parameters of one constitution version.
    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct ConstitutionParams {
        /// Version number, >= 1 (v0 is the unborn slot value).
        pub version: u64,
        /// How many council approvals certify a proposal/amendment.
        pub council_threshold: u64,
        /// Cooling period in blocks between proposing an amendment and
        /// enacting it.
        pub amendment_delay: u64,
        /// Treasury spending cap parameter (published for dependent
        /// descriptors; see lib docs gap 2).
        pub treasury_cap: u64,
    }

    /// The constitution constraint set (see module docs).
    pub fn constitution_state_constraints(
        params: &ConstitutionParams,
    ) -> Result<Vec<StateConstraint>, PolisError> {
        if params.version == 0 {
            return Err(PolisError::ZeroVersion);
        }
        if params.council_threshold == 0 {
            return Err(PolisError::ZeroThresholdParam);
        }
        let mut cs = vec![
            StateConstraint::AllowedTransitions {
                slot_index: STATE_SLOT,
                allowed: vec![
                    (field_from_u64(STATE_UNINIT), field_from_u64(STATE_UNINIT)),
                    (field_from_u64(STATE_UNINIT), field_from_u64(STATE_ACTIVE)),
                    (field_from_u64(STATE_ACTIVE), field_from_u64(STATE_ACTIVE)),
                    (field_from_u64(STATE_ACTIVE), field_from_u64(STATE_SUPERSEDED)),
                ],
            },
            // ── the constitutional parameters: pinned for life ──
            pin_term(VERSION_SLOT, field_from_u64(params.version)),
            pin_term(COUNCIL_THRESHOLD_SLOT, field_from_u64(params.council_threshold)),
            pin_term(AMENDMENT_DELAY_SLOT, field_from_u64(params.amendment_delay)),
            pin_term(TREASURY_CAP_SLOT, field_from_u64(params.treasury_cap)),
            // ── supersession provenance: written exactly once, only at the
            //    supersede step ──
            StateConstraint::WriteOnce { index: SUCCESSOR_HASH_SLOT },
            when_state(
                STATE_ACTIVE,
                SimpleStateConstraint::FieldEquals {
                    index: SUCCESSOR_HASH_SLOT,
                    value: FIELD_ZERO,
                },
            ),
            when_state(
                STATE_SUPERSEDED,
                SimpleStateConstraint::Not(Box::new(SimpleStateConstraint::FieldEquals {
                    index: SUCCESSOR_HASH_SLOT,
                    value: FIELD_ZERO,
                })),
            ),
        ];
        for s in RESERVED_SLOTS {
            cs.push(pinned_zero(s));
        }
        Ok(cs)
    }

    /// The `CellProgram` installed on this constitution version's cell.
    pub fn constitution_cell_program(
        params: &ConstitutionParams,
    ) -> Result<CellProgram, PolisError> {
        Ok(CellProgram::Predicate(constitution_state_constraints(params)?))
    }

    /// **The constitution factory (per-version, content-addressed).** Births
    /// exactly ONE cell; its `FactoryDescriptor::hash()` is the value an
    /// amendment stages and the superseded predecessor records.
    pub fn constitution_factory_descriptor(
        params: &ConstitutionParams,
    ) -> Result<FactoryDescriptor, PolisError> {
        Ok(polis_descriptor(
            "dregg-polis:constitution-factory v1",
            constitution_state_constraints(params)?,
            Some(1),
        ))
    }
}

// =============================================================================
// Worker mandate — budgeted delegation
// =============================================================================

pub mod mandate {
    //! The worker mandate cell: an orchestrator's budgeted, revocable,
    //! tool-scoped delegation to one worker.
    //!
    //! ## Slot schema
    //!
    //! | slot | name | constraint teeth |
    //! |------|------|------------------|
    //! | 0 | STATE | UNINIT→ACTIVE→REVOKED; REVOKED terminal (inert: ANY further touch rejected) |
    //! | 1 | SLICE | pinned literal — the published budget slice |
    //! | 2 | TOOL_SCOPE | pinned literal — the mandate's tool-scope commitment |
    //! | 3 | ORCHESTRATOR | pinned literal — the delegating cell's id |
    //! | 4 | WORKER_TAG | pinned literal — per-worker identity tag |
    //! | 5..7 | reserved | pinned zero |
    //!
    //! The budget slice is the worker cell's own funded BALANCE: the
    //! orchestrator funds exactly `slice` in, so a spend exceeding the
    //! remaining slice cannot commit (kernel conservation — see lib docs,
    //! gap 5). Revocation (`ACTIVE → REVOKED`) leaves the cell with no
    //! outgoing transition row, so a revoked worker's spends are rejected by
    //! the program; any residual balance is recoverable only by... nobody —
    //! it is burned with the cell's inertness, so orchestrators should drain
    //! before revoking or accept the burn (the revoke turn itself may carry
    //! the recovery `Transfer`, since the program evaluates the whole turn's
    //! post-state and the (ACTIVE, REVOKED) row admits it).

    use super::*;

    /// Slot 1 — the published budget slice (pinned).
    pub const SLICE_SLOT: u8 = 1;
    /// Slot 2 — the tool-scope commitment (pinned; e.g. blake3 of the
    /// allowed tool list — see [`tool_scope_commitment`]).
    pub const TOOL_SCOPE_SLOT: u8 = 2;
    /// Slot 3 — the delegating orchestrator's cell id (pinned).
    pub const ORCHESTRATOR_SLOT: u8 = 3;
    /// Slot 4 — the per-worker tag (pinned). Distinguishes two workers with
    /// otherwise identical terms: each mandate is content-addressed PER
    /// WORKER, so a receipt resolves to THIS worker's mandate, not to "some
    /// worker with the same slice and scope".
    pub const WORKER_TAG_SLOT: u8 = 4;
    /// Slots 5..7 — reserved, pinned zero.
    pub const RESERVED_SLOTS: [u8; 3] = [5, 6, 7];

    /// Birth state (mandate terms not yet written).
    pub const STATE_UNINIT: u64 = 0;
    /// The mandate is live: the worker may spend against its slice.
    pub const STATE_ACTIVE: u64 = 1;
    /// Terminal: revoked by the orchestrator. Inert — every further touch
    /// (spend, re-activate, transfer in) is rejected.
    pub const STATE_REVOKED: u64 = 2;

    /// The published terms of one worker mandate.
    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct WorkerMandate {
        /// The delegating orchestrator cell.
        pub orchestrator: CellId,
        /// The budget slice (must be nonzero); funded into the worker cell's
        /// own balance — the slice IS the balance.
        pub slice: u64,
        /// The tool-scope commitment (must be nonzero); see
        /// [`tool_scope_commitment`].
        pub tool_scope: FieldElement,
        /// Per-worker tag (any value, e.g. a worker index or a name hash) —
        /// makes this mandate's content address unique to ONE worker even
        /// when slices and scopes coincide.
        pub worker_tag: FieldElement,
    }

    /// Hash a tool list into the pinned scope commitment:
    /// `blake3("dregg-polis:tool-scope v1", toolᵢ…)`.
    pub fn tool_scope_commitment(tools: &[&str]) -> FieldElement {
        let mut hasher = blake3::Hasher::new_derive_key("dregg-polis:tool-scope v1");
        hasher.update(&(tools.len() as u64).to_be_bytes());
        for t in tools {
            hasher.update(&(t.len() as u64).to_be_bytes());
            hasher.update(t.as_bytes());
        }
        *hasher.finalize().as_bytes()
    }

    /// The worker-mandate constraint set (see module docs).
    pub fn worker_state_constraints(
        mandate: &WorkerMandate,
    ) -> Result<Vec<StateConstraint>, PolisError> {
        if mandate.slice == 0 {
            return Err(PolisError::ZeroSlice);
        }
        if mandate.tool_scope == FIELD_ZERO {
            return Err(PolisError::ZeroToolScope);
        }
        let mut cs = vec![
            StateConstraint::AllowedTransitions {
                slot_index: STATE_SLOT,
                allowed: vec![
                    (field_from_u64(STATE_UNINIT), field_from_u64(STATE_UNINIT)),
                    (field_from_u64(STATE_UNINIT), field_from_u64(STATE_ACTIVE)),
                    (field_from_u64(STATE_ACTIVE), field_from_u64(STATE_ACTIVE)),
                    (field_from_u64(STATE_ACTIVE), field_from_u64(STATE_REVOKED)),
                ],
            },
            pin_term(SLICE_SLOT, field_from_u64(mandate.slice)),
            pin_term(TOOL_SCOPE_SLOT, mandate.tool_scope),
            pin_term(ORCHESTRATOR_SLOT, party_field(mandate.orchestrator)),
            pin_term(WORKER_TAG_SLOT, mandate.worker_tag),
        ];
        for s in RESERVED_SLOTS {
            cs.push(pinned_zero(s));
        }
        Ok(cs)
    }

    /// The `CellProgram` installed on the worker mandate cell.
    pub fn worker_cell_program(mandate: &WorkerMandate) -> Result<CellProgram, PolisError> {
        Ok(CellProgram::Predicate(worker_state_constraints(mandate)?))
    }

    /// **The worker-mandate factory (per-worker, content-addressed).** Births
    /// exactly ONE worker cell; the orchestrator, slice, and tool scope are
    /// its content address — every receipt on the worker cell is traceable to
    /// these published mandate terms.
    pub fn worker_factory_descriptor(
        mandate: &WorkerMandate,
    ) -> Result<FactoryDescriptor, PolisError> {
        Ok(polis_descriptor(
            "dregg-polis:worker-mandate-factory v1",
            worker_state_constraints(mandate)?,
            Some(1),
        ))
    }
}

// =============================================================================
// Program-level tests (executor-independent; the e2e half runs on the real
// TurnExecutor in `sdk/tests/polis_governance_e2e.rs` +
// `sdk/tests/polis_orchestration_e2e.rs`)
// =============================================================================

#[cfg(test)]
mod tests {
    use super::council::*;
    use super::constitution::*;
    use super::mandate::*;
    use super::*;
    use dregg_cell::preconditions::EvalContext;
    use dregg_cell::program::{ProgramError, TransitionMeta, WitnessBundle};
    use dregg_cell::state::CellState;

    fn ctx_at(height: u64) -> EvalContext {
        EvalContext {
            block_height: height,
            timestamp: 0,
            current_epoch: 0,
            sender: None,
            sender_epoch_count: 0,
            revealed_preimage: None,
        }
    }

    fn eval(
        program: &CellProgram,
        new: &CellState,
        old: Option<&CellState>,
        height: u64,
    ) -> Result<(), ProgramError> {
        program.evaluate_full(
            new,
            old,
            Some(&ctx_at(height)),
            &TransitionMeta::wildcard(),
            &WitnessBundle::empty(),
        )
    }

    fn charter_2of3() -> CouncilCharter {
        CouncilCharter {
            members: vec![
                CellId::from_bytes([0x11; 32]),
                CellId::from_bytes([0x22; 32]),
                CellId::from_bytes([0x33; 32]),
            ],
            threshold: 2,
        }
    }

    /// Post-propose state: hash staged, membership commitment published.
    fn proposed_state(charter: &CouncilCharter, hash: FieldElement) -> CellState {
        let mut s = CellState::new(0);
        s.fields[STATE_SLOT as usize] = field_from_u64(STATE_PROPOSED);
        s.fields[PROPOSAL_HASH_SLOT as usize] = hash;
        s.fields[MEMBERS_COMMIT_SLOT as usize] = charter.members_commitment();
        s
    }

    #[test]
    fn charter_validation_fail_closed() {
        let mut c = charter_2of3();
        c.threshold = 4;
        assert_eq!(
            council_state_constraints(&c),
            Err(PolisError::ThresholdOutOfRange { threshold: 4, members: 3 })
        );
        c.threshold = 0;
        assert!(council_state_constraints(&c).is_err());
        c = charter_2of3();
        c.members[2] = c.members[0];
        assert_eq!(council_state_constraints(&c), Err(PolisError::DuplicateMember));
        c = charter_2of3();
        c.members.push(CellId::from_bytes([0x44; 32]));
        assert!(matches!(
            council_state_constraints(&c),
            Err(PolisError::TooManyMembers { got: 4, max: 3 })
        ));
    }

    #[test]
    fn council_birth_and_propose_pass() {
        let c = charter_2of3();
        let p = council_cell_program(&c).unwrap();
        let born = CellState::new(0);
        assert!(eval(&p, &born, None, 0).is_ok(), "all-zero birth must pass");
        let proposed = proposed_state(&c, field_from_u64(0xAC7A));
        assert!(eval(&p, &proposed, Some(&born), 0).is_ok(), "propose must pass");
    }

    #[test]
    fn council_approve_before_propose_rejected() {
        let c = charter_2of3();
        let p = council_cell_program(&c).unwrap();
        let born = CellState::new(0);
        let mut bad = born.clone();
        bad.fields[FIRST_APPROVAL_SLOT as usize] = field_from_u64(1);
        assert!(eval(&p, &bad, Some(&born), 0).is_err(), "BoundedBy must bite");
    }

    #[test]
    fn council_threshold_gates_flag() {
        let c = charter_2of3();
        let p = council_cell_program(&c).unwrap();
        let proposed = proposed_state(&c, field_from_u64(7));
        // One approval (M = 2): arming the flag must be rejected.
        let mut one = proposed.clone();
        one.fields[FIRST_APPROVAL_SLOT as usize] = field_from_u64(1);
        assert!(eval(&p, &one, Some(&proposed), 0).is_ok());
        let mut armed_early = one.clone();
        armed_early.fields[APPROVED_FLAG_SLOT as usize] = field_from_u64(1);
        assert!(eval(&p, &armed_early, Some(&one), 0).is_err(), "1 < M=2 must reject");
        // Second approval, then arming passes; APPROVED requires the flag.
        let mut two = one.clone();
        two.fields[(FIRST_APPROVAL_SLOT + 1) as usize] = field_from_u64(1);
        let mut armed = two.clone();
        armed.fields[APPROVED_FLAG_SLOT as usize] = field_from_u64(1);
        armed.fields[STATE_SLOT as usize] = field_from_u64(STATE_APPROVED);
        assert!(eval(&p, &armed, Some(&two), 0).is_ok(), "2 >= M=2 must pass");
        // APPROVED without the flag: rejected.
        let mut no_flag = two.clone();
        no_flag.fields[STATE_SLOT as usize] = field_from_u64(STATE_APPROVED);
        assert!(eval(&p, &no_flag, Some(&two), 0).is_err());
    }

    #[test]
    fn council_double_approve_one_slot_does_not_reach_threshold() {
        // The structural distinct-approver property: one member approving
        // "twice" is the same slot at 1 — the affine count cannot reach 2.
        let c = charter_2of3();
        let p = council_cell_program(&c).unwrap();
        let proposed = proposed_state(&c, field_from_u64(7));
        let mut one = proposed.clone();
        one.fields[FIRST_APPROVAL_SLOT as usize] = field_from_u64(1);
        // "Approve again" — the slot is already 1; the post-state is identical.
        let again = one.clone();
        assert!(eval(&p, &again, Some(&one), 0).is_ok());
        let mut armed = again.clone();
        armed.fields[APPROVED_FLAG_SLOT as usize] = field_from_u64(1);
        assert!(eval(&p, &armed, Some(&again), 0).is_err(), "still 1 distinct approver");
    }

    #[test]
    fn council_unapprove_rejected() {
        let c = charter_2of3();
        let p = council_cell_program(&c).unwrap();
        let proposed = proposed_state(&c, field_from_u64(7));
        let mut one = proposed.clone();
        one.fields[FIRST_APPROVAL_SLOT as usize] = field_from_u64(1);
        let mut retracted = one.clone();
        retracted.fields[FIRST_APPROVAL_SLOT as usize] = FIELD_ZERO;
        assert!(eval(&p, &retracted, Some(&one), 0).is_err(), "Monotonic must bite");
    }

    #[test]
    fn council_non_member_slot_pinned() {
        let c = CouncilCharter { members: charter_2of3().members[..2].to_vec(), threshold: 2 };
        let p = council_cell_program(&c).unwrap();
        let proposed = proposed_state(&c, field_from_u64(7));
        let mut bad = proposed.clone();
        bad.fields[(FIRST_APPROVAL_SLOT + 2) as usize] = field_from_u64(1); // 3rd slot, 2-member charter
        assert!(eval(&p, &bad, Some(&proposed), 0).is_err(), "non-member slot is pinned zero");
    }

    #[test]
    fn council_proposal_hash_write_once() {
        let c = charter_2of3();
        let p = council_cell_program(&c).unwrap();
        let proposed = proposed_state(&c, field_from_u64(7));
        let mut swapped = proposed.clone();
        swapped.fields[PROPOSAL_HASH_SLOT as usize] = field_from_u64(8);
        assert!(eval(&p, &swapped, Some(&proposed), 0).is_err(), "WriteOnce must bite");
    }

    #[test]
    fn council_terminal_states_inert() {
        let c = charter_2of3();
        let p = council_cell_program(&c).unwrap();
        let mut executed = proposed_state(&c, field_from_u64(7));
        executed.fields[FIRST_APPROVAL_SLOT as usize] = field_from_u64(1);
        executed.fields[(FIRST_APPROVAL_SLOT + 1) as usize] = field_from_u64(1);
        executed.fields[APPROVED_FLAG_SLOT as usize] = field_from_u64(1);
        executed.fields[STATE_SLOT as usize] = field_from_u64(STATE_EXECUTED);
        // Self-touch and any further step: rejected (no transition row).
        assert!(eval(&p, &executed, Some(&executed), 0).is_err());
        let mut re_exec = executed.clone();
        re_exec.fields[STATE_SLOT as usize] = field_from_u64(STATE_APPROVED);
        assert!(eval(&p, &re_exec, Some(&executed), 0).is_err());
        // REJECTED likewise.
        let mut rejected = proposed_state(&c, field_from_u64(7));
        rejected.fields[STATE_SLOT as usize] = field_from_u64(STATE_REJECTED);
        assert!(eval(&p, &rejected, Some(&rejected), 0).is_err());
    }

    #[test]
    fn amendment_cooling_gate() {
        let terms = AmendmentTerms {
            charter: charter_2of3(),
            new_constitution_hash: field_from_u64(0xC0457),
            enact_not_before: 500,
        };
        let p = amendment_cell_program(&terms).unwrap();
        let mut certified = proposed_state(&terms.charter, terms.new_constitution_hash);
        certified.fields[FIRST_APPROVAL_SLOT as usize] = field_from_u64(1);
        certified.fields[(FIRST_APPROVAL_SLOT + 1) as usize] = field_from_u64(1);
        certified.fields[APPROVED_FLAG_SLOT as usize] = field_from_u64(1);
        certified.fields[STATE_SLOT as usize] = field_from_u64(STATE_APPROVED);
        let mut enacted = certified.clone();
        enacted.fields[STATE_SLOT as usize] = field_from_u64(STATE_EXECUTED);
        assert!(eval(&p, &enacted, Some(&certified), 499).is_err(), "height 499 < 500");
        assert!(eval(&p, &enacted, Some(&certified), 500).is_ok(), "height 500 >= 500");
    }

    #[test]
    fn amendment_pins_staged_hash() {
        let terms = AmendmentTerms {
            charter: charter_2of3(),
            new_constitution_hash: field_from_u64(0xC0457),
            enact_not_before: 0,
        };
        let p = amendment_cell_program(&terms).unwrap();
        let born = CellState::new(0);
        let wrong = proposed_state(&terms.charter, field_from_u64(0xBAD));
        assert!(eval(&p, &wrong, Some(&born), 0).is_err(), "staging a different hash rejected");
        let right = proposed_state(&terms.charter, terms.new_constitution_hash);
        assert!(eval(&p, &right, Some(&born), 0).is_ok());
        // Zero hash rejected at build.
        let mut z = terms.clone();
        z.new_constitution_hash = FIELD_ZERO;
        assert_eq!(amendment_state_constraints(&z), Err(PolisError::ZeroAmendmentHash));
    }

    fn params_v1() -> ConstitutionParams {
        ConstitutionParams {
            version: 1,
            council_threshold: 2,
            amendment_delay: 50,
            treasury_cap: 1_000,
        }
    }

    fn active_constitution(params: &ConstitutionParams) -> CellState {
        let mut s = CellState::new(0);
        s.fields[STATE_SLOT as usize] = field_from_u64(constitution::STATE_ACTIVE);
        s.fields[VERSION_SLOT as usize] = field_from_u64(params.version);
        s.fields[COUNCIL_THRESHOLD_SLOT as usize] = field_from_u64(params.council_threshold);
        s.fields[AMENDMENT_DELAY_SLOT as usize] = field_from_u64(params.amendment_delay);
        s.fields[TREASURY_CAP_SLOT as usize] = field_from_u64(params.treasury_cap);
        s
    }

    #[test]
    fn constitution_params_pinned_for_life() {
        let params = params_v1();
        let p = constitution_cell_program(&params).unwrap();
        let born = CellState::new(0);
        let active = active_constitution(&params);
        assert!(eval(&p, &active, Some(&born), 0).is_ok(), "activate writes the params");
        // ANY parameter edit on the active cell is rejected.
        for slot in [VERSION_SLOT, COUNCIL_THRESHOLD_SLOT, AMENDMENT_DELAY_SLOT, TREASURY_CAP_SLOT] {
            let mut bad = active.clone();
            bad.fields[slot as usize] = field_from_u64(9_999);
            assert!(eval(&p, &bad, Some(&active), 0).is_err(), "param slot {slot} must be pinned");
        }
    }

    #[test]
    fn constitution_supersede_requires_successor_and_is_terminal() {
        let params = params_v1();
        let p = constitution_cell_program(&params).unwrap();
        let active = active_constitution(&params);
        // Supersede without a successor hash: rejected.
        let mut anon = active.clone();
        anon.fields[STATE_SLOT as usize] = field_from_u64(constitution::STATE_SUPERSEDED);
        assert!(eval(&p, &anon, Some(&active), 0).is_err());
        // Successor hash while still ACTIVE: rejected.
        let mut early = active.clone();
        early.fields[SUCCESSOR_HASH_SLOT as usize] = field_from_u64(0xDEED);
        assert!(eval(&p, &early, Some(&active), 0).is_err());
        // Proper supersede: passes; then the cell is inert.
        let mut superseded = active.clone();
        superseded.fields[SUCCESSOR_HASH_SLOT as usize] = field_from_u64(0xDEED);
        superseded.fields[STATE_SLOT as usize] = field_from_u64(constitution::STATE_SUPERSEDED);
        assert!(eval(&p, &superseded, Some(&active), 0).is_ok());
        assert!(eval(&p, &superseded, Some(&superseded), 0).is_err(), "terminal: inert");
        let mut resurrect = superseded.clone();
        resurrect.fields[STATE_SLOT as usize] = field_from_u64(constitution::STATE_ACTIVE);
        assert!(eval(&p, &resurrect, Some(&superseded), 0).is_err());
    }

    #[test]
    fn worker_mandate_machine() {
        let m = WorkerMandate {
            orchestrator: CellId::from_bytes([0xAA; 32]),
            slice: 30,
            tool_scope: tool_scope_commitment(&["search", "fetch"]),
            worker_tag: field_from_u64(1),
        };
        let p = worker_cell_program(&m).unwrap();
        let born = CellState::new(0);
        let mut active = born.clone();
        active.fields[STATE_SLOT as usize] = field_from_u64(mandate::STATE_ACTIVE);
        active.fields[SLICE_SLOT as usize] = field_from_u64(m.slice);
        active.fields[TOOL_SCOPE_SLOT as usize] = m.tool_scope;
        active.fields[ORCHESTRATOR_SLOT as usize] = party_field(m.orchestrator);
        active.fields[WORKER_TAG_SLOT as usize] = m.worker_tag;
        assert!(eval(&p, &active, Some(&born), 0).is_ok());
        // Scope / slice rewrites rejected.
        let mut bad = active.clone();
        bad.fields[TOOL_SCOPE_SLOT as usize] = field_from_u64(0xEEEE);
        assert!(eval(&p, &bad, Some(&active), 0).is_err(), "tool scope pinned");
        let mut inflated = active.clone();
        inflated.fields[SLICE_SLOT as usize] = field_from_u64(9_999);
        assert!(eval(&p, &inflated, Some(&active), 0).is_err(), "slice pinned");
        // Revoke, then inert (no re-activate, no touch).
        let mut revoked = active.clone();
        revoked.fields[STATE_SLOT as usize] = field_from_u64(mandate::STATE_REVOKED);
        assert!(eval(&p, &revoked, Some(&active), 0).is_ok());
        assert!(eval(&p, &revoked, Some(&revoked), 0).is_err());
        let mut reactivated = revoked.clone();
        reactivated.fields[STATE_SLOT as usize] = field_from_u64(mandate::STATE_ACTIVE);
        assert!(eval(&p, &reactivated, Some(&revoked), 0).is_err());
        // Build-time fail-closed.
        assert_eq!(
            worker_state_constraints(&WorkerMandate { slice: 0, ..m.clone() }),
            Err(PolisError::ZeroSlice)
        );
        assert_eq!(
            worker_state_constraints(&WorkerMandate { tool_scope: FIELD_ZERO, ..m }),
            Err(PolisError::ZeroToolScope)
        );
    }

    #[test]
    fn descriptors_are_content_addressed() {
        let a = council_factory_descriptor(&charter_2of3()).unwrap();
        let b = council_factory_descriptor(&charter_2of3()).unwrap();
        assert_eq!(a.factory_vk, b.factory_vk, "same charter → same factory");
        assert_eq!(a.hash(), b.hash());
        let mut c2 = charter_2of3();
        c2.threshold = 3;
        let c = council_factory_descriptor(&c2).unwrap();
        assert_ne!(a.factory_vk, c.factory_vk, "different threshold → different factory");
        // Amendment vs council with identical members: domain tags separate.
        let amend = amendment_factory_descriptor(&AmendmentTerms {
            charter: charter_2of3(),
            new_constitution_hash: field_from_u64(1),
            enact_not_before: 0,
        })
        .unwrap();
        assert_ne!(a.factory_vk, amend.factory_vk);
        // Constitution params are content-addressed too.
        let v1 = constitution_factory_descriptor(&params_v1()).unwrap();
        let mut p2 = params_v1();
        p2.version = 2;
        p2.council_threshold = 3;
        let v2 = constitution_factory_descriptor(&p2).unwrap();
        assert_ne!(v1.hash(), v2.hash());
    }
}
