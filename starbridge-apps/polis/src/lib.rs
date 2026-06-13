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
//!   proposal cell's machine from its 16 slots (pure; works on a node read, a
//!   receipt's post-state, or a light-client proof) and is the shared
//!   decoder behind the CLI (`dregg polis council`) and the Discord
//!   `/council-status` surface.
//!
//! ## Expressibility gaps (documented, NOT shimmed — dregg4 guard-algebra feed)
//!
//! The `StateConstraint` grammar evaluates over the 16 field slots of the ONE
//! touched cell's post-state (+ old state + block height). The following legs
//! of the polis semantics are therefore **not program-enforced**; each is
//! listed with what carries it instead:
//!
//! 1. **Member ↔ approval-slot sender binding — DISSOLVED** (turn-context
//!    atoms, `docs/CELL-PROGRAM-LANGUAGE.md` §3). A charter built with
//!    [`council::CouncilCharter::with_member_keys`] installs, per member,
//!    `AnyOf[Immutable{approval_slot_i}, SenderIs{member_keys[i]}]`: slot
//!    *i* flips only in a turn whose SENDER is member *i*. A stolen/shared
//!    capability no longer suffices to flip another member's slot, and the
//!    operator cannot relay approvals (the e2e
//!    `approval_slots_are_actor_bound` is the executor-level tooth).
//!    Charters without published keys keep the legacy carry: capability
//!    possession + operator discipline, receipts recording the signer.
//!    What is enforced either way: each approval is a distinct slot,
//!    bounded to {0,1}, monotone (no un-approve), and gated on a staged
//!    proposal — the approval COUNT is over distinct member slots by
//!    construction.
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
//! 5. **Worker slice as a numeric cap.** "Spent ≤ slice" is the kernel
//!    conservation law: the worker is funded with EXACTLY its slice, and a
//!    spend exceeding the remaining balance cannot commit. The pinned
//!    `SLICE` slot publishes the slice for audit; it is not the enforcement.
//!    (The balance is no longer sealed from the grammar — `BalanceGte` /
//!    `BalanceLte` atoms exist (`docs/CELL-PROGRAM-LANGUAGE.md` §3) for
//!    programs that want explicit floors/drain teeth; the mandate keeps
//!    conservation as its enforcement because it is already exact.)
//! 6. **Tool-scope semantics.** The mandate's tool scope is a pinned 32-byte
//!    commitment (e.g. the hash of the allowed tool list). The program cannot
//!    decode which "tool" a turn used; per-tool gating lives at the MCP
//!    capability layer (`node/src/mcp.rs`). The cell publishes the scope so
//!    every spend receipt is traceable to the mandate's published terms.
//! 7. **Slot budget.** With 16 constraint-visible slots, a council cell
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
    /// More members than the 16-slot grammar can hold (see module docs, gap 7).
    TooManyMembers { got: usize, max: usize },
    /// Threshold must satisfy `1 <= threshold <= members.len()`.
    ThresholdOutOfRange { threshold: u64, members: usize },
    /// Duplicate member ids (or duplicate member keys) would let one
    /// member fill two approval slots.
    DuplicateMember,
    /// An actor-bound charter must publish exactly one signing key per
    /// member (charter order).
    MemberKeyCountMismatch { keys: usize, members: usize },
    /// A zero member key can never match a real turn sender — that member
    /// could never approve; rejected at build (fail-closed).
    ZeroMemberKey { index: usize },
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
    /// builders (a build gate; a `BalanceLte { max: treasury_cap }`
    /// program tooth is now expressible — `docs/CELL-PROGRAM-LANGUAGE.md`
    /// §3 — and is the natural descriptor evolution).
    EndowmentExceedsTreasuryCap { endowment: u64, cap: u64 },
    /// A worker mandate with a zero budget slice can do nothing; rejected so
    /// a forgotten slice fails loudly at build, not silently at spend.
    ZeroSlice,
    /// The tool-scope commitment must be nonzero (a zero scope is
    /// indistinguishable from the unborn slot).
    ZeroToolScope,
    /// An identity charter must carry a nonzero rotation cooling period —
    /// the recovery-cooling composition is load-bearing (a zero window
    /// would let a preimage-holding thief rotate instantly and invisibly).
    ZeroCoolingPeriod,
}

impl std::fmt::Display for PolisError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PolisError::NoMembers => write!(f, "council charter must list at least one member"),
            PolisError::TooManyMembers { got, max } => {
                write!(
                    f,
                    "council charter lists {got} members; slot grammar holds at most {max}"
                )
            }
            PolisError::ThresholdOutOfRange { threshold, members } => write!(
                f,
                "threshold {threshold} out of range for {members} members (need 1 <= M <= N)"
            ),
            PolisError::DuplicateMember => write!(f, "council members must be distinct"),
            PolisError::MemberKeyCountMismatch { keys, members } => write!(
                f,
                "actor-bound charter publishes {keys} member keys for {members} members"
            ),
            PolisError::ZeroMemberKey { index } => {
                write!(f, "member {index} has the all-zero signing key")
            }
            PolisError::BadMemberIndex { index, members } => {
                write!(f, "member index {index} out of range ({members} members)")
            }
            PolisError::ZeroAmendmentHash => {
                write!(
                    f,
                    "amendment must stage a nonzero successor-constitution hash"
                )
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
            PolisError::ZeroCoolingPeriod => {
                write!(
                    f,
                    "identity charter rotation cooling period must be >= 1 block"
                )
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
            SimpleStateConstraint::FieldEquals {
                index: slot,
                value: lit,
            },
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
        /// **Actor-bound approvals** (dissolves expressibility gap 1):
        /// when present, member `i`'s signing key — and the program gains,
        /// per member, the slot caveat
        /// `AnyOf[Immutable{approval_slot_i}, SenderIs{member_keys[i]}]`:
        /// approval slot `i` can only ever be flipped by a turn whose
        /// SENDER is member `i`. Capability possession alone no longer
        /// suffices; the operator cannot relay approvals. Must be the same
        /// length as `members` (charter order). `None` = the legacy
        /// capability-possession charter (gap 1 documented, not enforced).
        pub member_keys: Option<Vec<[u8; 32]>>,
    }

    impl CouncilCharter {
        /// An unbound (legacy) charter: membership + threshold only.
        pub fn new(members: Vec<CellId>, threshold: u64) -> Self {
            Self {
                members,
                threshold,
                member_keys: None,
            }
        }

        /// An actor-bound charter: approval slot `i` is flippable only by
        /// the sender holding `member_keys[i]`.
        pub fn with_member_keys(
            members: Vec<CellId>,
            threshold: u64,
            member_keys: Vec<[u8; 32]>,
        ) -> Self {
            Self {
                members,
                threshold,
                member_keys: Some(member_keys),
            }
        }

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
            if let Some(keys) = &self.member_keys {
                if keys.len() != self.members.len() {
                    return Err(PolisError::MemberKeyCountMismatch {
                        keys: keys.len(),
                        members: self.members.len(),
                    });
                }
                for (i, k) in keys.iter().enumerate() {
                    if *k == [0u8; 32] {
                        // A zero key can never match a real sender; that
                        // member could never approve. Fail loudly at build.
                        return Err(PolisError::ZeroMemberKey { index: i });
                    }
                    if keys[..i].contains(k) {
                        return Err(PolisError::DuplicateMember);
                    }
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
        /// `blake3("dregg-polis:council-members v1", threshold ‖ memberᵢ…)`
        /// for unbound charters; actor-bound charters commit under the v2
        /// domain and additionally bind every member signing key, so an
        /// actor-bound and an unbound charter over the same cells can
        /// never alias. Pinned into [`MEMBERS_COMMIT_SLOT`] once the cell
        /// leaves DRAFT, so the cell itself publishes which membership
        /// (and which keys) gate it.
        pub fn members_commitment(&self) -> FieldElement {
            match &self.member_keys {
                None => {
                    let mut hasher =
                        blake3::Hasher::new_derive_key("dregg-polis:council-members v1");
                    hasher.update(&self.threshold.to_be_bytes());
                    hasher.update(&(self.members.len() as u64).to_be_bytes());
                    for m in &self.members {
                        hasher.update(m.as_bytes());
                    }
                    *hasher.finalize().as_bytes()
                }
                Some(keys) => {
                    let mut hasher = blake3::Hasher::new_derive_key(
                        "dregg-polis:council-members v2 actor-bound",
                    );
                    hasher.update(&self.threshold.to_be_bytes());
                    hasher.update(&(self.members.len() as u64).to_be_bytes());
                    for m in &self.members {
                        hasher.update(m.as_bytes());
                    }
                    for k in keys {
                        hasher.update(k);
                    }
                    *hasher.finalize().as_bytes()
                }
            }
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
                    (
                        field_from_u64(STATE_PROPOSED),
                        field_from_u64(STATE_PROPOSED),
                    ),
                    (
                        field_from_u64(STATE_PROPOSED),
                        field_from_u64(STATE_REJECTED),
                    ),
                    (
                        field_from_u64(STATE_PROPOSED),
                        field_from_u64(STATE_APPROVED),
                    ),
                    (
                        field_from_u64(STATE_APPROVED),
                        field_from_u64(STATE_APPROVED),
                    ),
                    (
                        field_from_u64(STATE_APPROVED),
                        field_from_u64(STATE_EXECUTED),
                    ),
                ],
            },
            // ── one proposal per cell; any state step requires a staged hash ──
            StateConstraint::WriteOnce {
                index: PROPOSAL_HASH_SLOT,
            },
            StateConstraint::BoundedBy {
                index: STATE_SLOT,
                witness_index: PROPOSAL_HASH_SLOT,
            },
            // ── membership publication (pinned once out of DRAFT) ──
            pin_term(MEMBERS_COMMIT_SLOT, charter.members_commitment()),
            // ── the certification flag: a monotone bit, armable only with a
            //    staged proposal ──
            StateConstraint::MemberOf {
                index: APPROVED_FLAG_SLOT,
                set: vec![0, 1],
            },
            StateConstraint::Monotonic {
                index: APPROVED_FLAG_SLOT,
            },
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
            cs.push(StateConstraint::MemberOf {
                index: slot,
                set: vec![0, 1],
            });
            cs.push(StateConstraint::Monotonic { index: slot });
            cs.push(StateConstraint::BoundedBy {
                index: slot,
                witness_index: PROPOSAL_HASH_SLOT,
            });
        }
        // ── actor-bound approvals (gap 1 DISSOLVED when keys are
        //    published): approval slot i may change ONLY in a turn whose
        //    sender is member i's key. `Immutable` admits every turn that
        //    leaves the slot alone (propose / certify / execute / other
        //    members' approvals); flipping the slot demands the bound
        //    sender. Capability possession alone can no longer flip
        //    another member's slot. ──
        if let Some(keys) = &charter.member_keys {
            for (i, key) in keys.iter().enumerate() {
                cs.push(StateConstraint::AnyOf {
                    variants: vec![
                        SimpleStateConstraint::Immutable {
                            index: FIRST_APPROVAL_SLOT + i as u8,
                        },
                        SimpleStateConstraint::SenderIs { pk: *key },
                    ],
                });
            }
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
    /// the cell's 16 field slots.
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
    pub fn inspect_council(charter: &CouncilCharter, fields: &[FieldElement; 16]) -> CouncilStatus {
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
                    (
                        field_from_u64(STATE_ACTIVE),
                        field_from_u64(STATE_SUPERSEDED),
                    ),
                ],
            },
            // ── the constitutional parameters: pinned for life ──
            pin_term(VERSION_SLOT, field_from_u64(params.version)),
            pin_term(
                COUNCIL_THRESHOLD_SLOT,
                field_from_u64(params.council_threshold),
            ),
            pin_term(AMENDMENT_DELAY_SLOT, field_from_u64(params.amendment_delay)),
            pin_term(TREASURY_CAP_SLOT, field_from_u64(params.treasury_cap)),
            // ── supersession provenance: written exactly once, only at the
            //    supersede step ──
            StateConstraint::WriteOnce {
                index: SUCCESSOR_HASH_SLOT,
            },
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
        Ok(CellProgram::Predicate(constitution_state_constraints(
            params,
        )?))
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
// Identity — the person as a governance cell, with KERI-shaped pre-rotation
// =============================================================================

pub mod identity {
    //! The identity cell: a person's identity as a small governance cell
    //! (`docs/REFINEMENT-DESIGN.md` Decision 2 — devices are council
    //! members, recovery is amendment-with-cooling) carrying the
    //! **pre-rotation register** (`docs/ORGANS.md` "Identity rider"; kernel
    //! semantics proven in `metatheory/Dregg2/Apps/PreRotation.lean`).
    //!
    //! ## Pre-rotation in one line
    //!
    //! Every key-state event commits to the digest of the NEXT, unexposed
    //! key set; rotation must exhibit the preimage — so compromising the
    //! CURRENT signing keys does not suffice to rotate
    //! (`rotate_compromise_resistant`), and the public commitment stream
    //! pins the entire key history (`rotChain_pinned_by_commitments`).
    //!
    //! ## Slot schema
    //!
    //! | slot | name | constraint teeth |
    //! |------|------|------------------|
    //! | 0 | STATE | `AllowedTransitions` UNINIT→ACTIVE→{ACTIVE, RETIRED}; RETIRED terminal/inert |
    //! | 1 | NEXT_KEYS_DIGEST | `KeyRotationGate` (the register; rotation = preimage exhibit + fresh re-commit) |
    //! | 2 | CURRENT_KEYS_COMMIT | written ONLY by the gate (`new == exhibited preimage`); nonzero while ACTIVE |
    //! | 3 | LAST_ROTATED_AT | the cooling anchor; stamped to the rotation height by the gate |
    //! | 4 | COUNCIL_COMMIT | pinned to the device/recovery council's `members_commitment()` |
    //! | 5..7 | reserved | pinned zero |
    //!
    //! ## The rotate verb (the `KeyRotationGate`, executor-enforced)
    //!
    //! A turn that moves any rotation register is admitted ONLY when it
    //! carries a `Preimage32` witness `K` with `blake3(K) ==
    //! old[NEXT_KEYS_DIGEST]` (the preimage EXHIBIT against the PRE-state
    //! register), installs `new[CURRENT_KEYS_COMMIT] == K`, re-commits a
    //! fresh nonzero `new[NEXT_KEYS_DIGEST]` in the SAME turn (the forward
    //! chain), and waits out the cooling window
    //! (`old[LAST_ROTATED_AT] + cooling_period <= height`, stamping
    //! `new[LAST_ROTATED_AT] = height`). The guard never reads the current
    //! key commitment — current-key theft contributes nothing
    //! (`rotate_current_keys_irrelevant`, the `rfl` theorem).
    //!
    //! ## Cooling / recovery composition
    //!
    //! Per-cell cooling is INSIDE the gate (the Lean `rotateWriteCooled`
    //! production shape): even a preimage-holding rotation waits in the
    //! open, visible to the council — pre-rotation removes the attacker's
    //! ABILITY, cooling removes their SPEED/STEALTH; the composition
    //! strictly dominates either alone (`cooling_blocks_admitted_preimage`
    //! / `preimage_blocks_cooled_rotation`). The council-certified recovery
    //! ceremony composes ON TOP via the existing amendment machinery: a
    //! rotation proposal is an [`super::council`] amendment-variant cell
    //! staging the rotation's hash with its own `TemporalGate`, whose ENACT
    //! turn carries the rotate effects — and the identity cell's gate STILL
    //! demands the preimage (recovery is empowered, never amplified).
    //!
    //! ## Genesis
    //!
    //! A factory-born identity cell mints empty (all-zero registers — the
    //! polis bootstrap shape). The genesis turn (UNINIT → ACTIVE) installs
    //! the FIRST pre-commitment without a preimage (nothing was committed
    //! yet — KERI `icp`): the birth key-set commitment, the first
    //! next-keys digest, and the pinned council commitment, all in one
    //! turn. While ACTIVE both key registers are nonzero — the chain can
    //! never be nulled.
    //!
    //! ## Key history
    //!
    //! The receipt stream over slots 1/2 IS the key-event log: each
    //! rotation receipt shows the exhibited commitment (slot 2) equal to
    //! the preimage of the PREVIOUS receipt's slot 1, and publishes the
    //! next link. This is the KERI KEL shape the ORGANS export lane
    //! serializes.

    use super::council::CouncilCharter;
    use super::*;
    use dregg_cell::program::HashKind;

    /// Slot 1 — the `next_keys_digest` register: the commitment to the
    /// NEXT, unexposed key set (KERI `n`).
    pub const NEXT_KEYS_DIGEST_SLOT: u8 = 1;
    /// Slot 2 — the installed (current) key-set commitment (KERI `k`,
    /// as its 32-byte commitment).
    pub const CURRENT_KEYS_COMMIT_SLOT: u8 = 2;
    /// Slot 3 — the height of the last rotation event (cooling anchor).
    pub const LAST_ROTATED_AT_SLOT: u8 = 3;
    /// Slot 4 — the device/recovery council's published membership
    /// commitment (pinned literal).
    pub const COUNCIL_COMMIT_SLOT: u8 = 4;
    /// Slots 5..7 — reserved, pinned zero.
    pub const RESERVED_SLOTS: [u8; 3] = [5, 6, 7];

    /// Birth state (factory-born; registers all zero).
    pub const STATE_UNINIT: u64 = 0;
    /// The identity is live: registers populated, rotations admitted
    /// through the gate.
    pub const STATE_ACTIVE: u64 = 1;
    /// Terminal: the identity is retired. Inert — no transition row out,
    /// so no further rotation (or any touch) can commit.
    pub const STATE_RETIRED: u64 = 2;

    /// The published terms of one identity cell: the device/recovery
    /// council and the rotation cooling window. Content-addressed into the
    /// factory vk — "is this identity governed by THESE devices under THIS
    /// cooling window?" is a hash check.
    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct IdentityCharter {
        /// The governing council: devices (and/or recovery friends) with
        /// their threshold — [`CouncilCharter`], reused verbatim. Its
        /// commitment is pinned into [`COUNCIL_COMMIT_SLOT`].
        pub council: CouncilCharter,
        /// Blocks a rotation must wait after the previous rotation (the
        /// recovery cooling window; must be >= 1).
        pub cooling_period: u64,
    }

    impl IdentityCharter {
        /// Fail-closed validation.
        pub fn validate(&self) -> Result<(), PolisError> {
            self.council.validate()?;
            if self.cooling_period == 0 {
                return Err(PolisError::ZeroCoolingPeriod);
            }
            Ok(())
        }
    }

    /// Commit a key set (ordered Ed25519 public keys) to its 32-byte
    /// commitment — the value the `Preimage32` witness presents at
    /// rotation and [`CURRENT_KEYS_COMMIT_SLOT`] installs.
    pub fn key_set_commitment(keys: &[[u8; 32]]) -> FieldElement {
        let mut hasher = blake3::Hasher::new_derive_key("dregg-polis:identity-keyset v1");
        hasher.update(&(keys.len() as u64).to_be_bytes());
        for k in keys {
            hasher.update(k);
        }
        *hasher.finalize().as_bytes()
    }

    /// The `next_keys_digest` register value for a key-set commitment:
    /// plain `blake3(commitment)` — EXACTLY the digest the gate's
    /// `HashKind::Blake3` recomputes from the exhibited preimage.
    pub fn next_keys_digest(key_set_commit: &FieldElement) -> FieldElement {
        *blake3::hash(key_set_commit).as_bytes()
    }

    /// The identity constraint set (see module docs).
    pub fn identity_state_constraints(
        charter: &IdentityCharter,
    ) -> Result<Vec<StateConstraint>, PolisError> {
        charter.validate()?;
        let mut cs = vec![
            // ── the lifecycle; RETIRED has NO outgoing row (inert) ──
            StateConstraint::AllowedTransitions {
                slot_index: STATE_SLOT,
                allowed: vec![
                    (field_from_u64(STATE_UNINIT), field_from_u64(STATE_UNINIT)),
                    (field_from_u64(STATE_UNINIT), field_from_u64(STATE_ACTIVE)),
                    (field_from_u64(STATE_ACTIVE), field_from_u64(STATE_ACTIVE)),
                    (field_from_u64(STATE_ACTIVE), field_from_u64(STATE_RETIRED)),
                ],
            },
            // ── THE PRE-ROTATION GATE (the rotate verb as a guarded
            //    write; cooling conjoined — the `rotateWriteCooled`
            //    production shape) ──
            StateConstraint::KeyRotationGate {
                digest_slot: NEXT_KEYS_DIGEST_SLOT,
                current_slot: CURRENT_KEYS_COMMIT_SLOT,
                last_rotated_slot: LAST_ROTATED_AT_SLOT,
                cooling_period: charter.cooling_period,
                hash_kind: HashKind::Blake3,
            },
            // ── an ACTIVE identity always carries a live pre-commitment
            //    and a published current key set: genesis must install
            //    both; no rotation can null the chain ──
            when_state(
                STATE_ACTIVE,
                SimpleStateConstraint::Not(Box::new(SimpleStateConstraint::FieldEquals {
                    index: NEXT_KEYS_DIGEST_SLOT,
                    value: FIELD_ZERO,
                })),
            ),
            when_state(
                STATE_ACTIVE,
                SimpleStateConstraint::Not(Box::new(SimpleStateConstraint::FieldEquals {
                    index: CURRENT_KEYS_COMMIT_SLOT,
                    value: FIELD_ZERO,
                })),
            ),
            // ── council publication (pinned once out of UNINIT) ──
            pin_term(COUNCIL_COMMIT_SLOT, charter.council.members_commitment()),
        ];
        for s in RESERVED_SLOTS {
            cs.push(pinned_zero(s));
        }
        Ok(cs)
    }

    /// The `CellProgram` installed on the identity cell.
    pub fn identity_cell_program(charter: &IdentityCharter) -> Result<CellProgram, PolisError> {
        Ok(CellProgram::Predicate(identity_state_constraints(
            charter,
        )?))
    }

    /// **The identity factory (per-charter, content-addressed).** Births
    /// exactly ONE identity cell; the council commitment and the cooling
    /// window are its content address.
    pub fn identity_factory_descriptor(
        charter: &IdentityCharter,
    ) -> Result<FactoryDescriptor, PolisError> {
        Ok(polis_descriptor(
            "dregg-polis:identity-factory v1",
            identity_state_constraints(charter)?,
            Some(1),
        ))
    }

    // -------------------------------------------------------------------------
    // Legibility — read the key state back out of the ledger
    // -------------------------------------------------------------------------

    /// One identity-cell lifecycle state, decoded.
    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub enum IdentityState {
        /// Birth state; registers not yet populated.
        Uninit,
        /// Live: registers populated, rotations gated.
        Active,
        /// Terminal: retired, inert.
        Retired,
        /// Not a value this machine emits.
        Unknown(u64),
    }

    /// An identity cell, made legible: the decoded key state. Pure over
    /// the 16 field slots (a node read, a receipt post-state, or a
    /// light-client proof).
    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct IdentityStatus {
        /// Decoded lifecycle state.
        pub state: IdentityState,
        /// The committed next-keys digest (the unexposed pre-commitment).
        pub next_keys_digest: FieldElement,
        /// The installed (current) key-set commitment.
        pub current_keys_commit: FieldElement,
        /// Height of the last rotation event (the cooling anchor).
        pub last_rotated_at: u64,
        /// Whether the council-commitment slot matches the charter.
        pub council_commit_matches: bool,
    }

    /// Decode an identity cell's fields against its charter.
    pub fn inspect_identity(
        charter: &IdentityCharter,
        fields: &[FieldElement; 16],
    ) -> IdentityStatus {
        let to_u64 = |f: &FieldElement| {
            let mut b = [0u8; 8];
            b.copy_from_slice(&f[24..32]);
            u64::from_be_bytes(b)
        };
        let state = match to_u64(&fields[STATE_SLOT as usize]) {
            STATE_UNINIT => IdentityState::Uninit,
            STATE_ACTIVE => IdentityState::Active,
            STATE_RETIRED => IdentityState::Retired,
            other => IdentityState::Unknown(other),
        };
        IdentityStatus {
            state,
            next_keys_digest: fields[NEXT_KEYS_DIGEST_SLOT as usize],
            current_keys_commit: fields[CURRENT_KEYS_COMMIT_SLOT as usize],
            last_rotated_at: to_u64(&fields[LAST_ROTATED_AT_SLOT as usize]),
            council_commit_matches: fields[COUNCIL_COMMIT_SLOT as usize]
                == charter.council.members_commitment(),
        }
    }
}

// =============================================================================
// Program-level tests (executor-independent; the e2e half runs on the real
// TurnExecutor in `sdk/tests/polis_governance_e2e.rs` +
// `sdk/tests/polis_orchestration_e2e.rs`)
// =============================================================================

#[cfg(test)]
mod tests {
    use super::constitution::*;
    use super::council::*;
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
        CouncilCharter::new(
            vec![
                CellId::from_bytes([0x11; 32]),
                CellId::from_bytes([0x22; 32]),
                CellId::from_bytes([0x33; 32]),
            ],
            2,
        )
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
            Err(PolisError::ThresholdOutOfRange {
                threshold: 4,
                members: 3
            })
        );
        c.threshold = 0;
        assert!(council_state_constraints(&c).is_err());
        c = charter_2of3();
        c.members[2] = c.members[0];
        assert_eq!(
            council_state_constraints(&c),
            Err(PolisError::DuplicateMember)
        );
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
        assert!(
            eval(&p, &proposed, Some(&born), 0).is_ok(),
            "propose must pass"
        );
    }

    #[test]
    fn council_approve_before_propose_rejected() {
        let c = charter_2of3();
        let p = council_cell_program(&c).unwrap();
        let born = CellState::new(0);
        let mut bad = born.clone();
        bad.fields[FIRST_APPROVAL_SLOT as usize] = field_from_u64(1);
        assert!(
            eval(&p, &bad, Some(&born), 0).is_err(),
            "BoundedBy must bite"
        );
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
        assert!(
            eval(&p, &armed_early, Some(&one), 0).is_err(),
            "1 < M=2 must reject"
        );
        // Second approval, then arming passes; APPROVED requires the flag.
        let mut two = one.clone();
        two.fields[(FIRST_APPROVAL_SLOT + 1) as usize] = field_from_u64(1);
        let mut armed = two.clone();
        armed.fields[APPROVED_FLAG_SLOT as usize] = field_from_u64(1);
        armed.fields[STATE_SLOT as usize] = field_from_u64(STATE_APPROVED);
        assert!(
            eval(&p, &armed, Some(&two), 0).is_ok(),
            "2 >= M=2 must pass"
        );
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
        assert!(
            eval(&p, &armed, Some(&again), 0).is_err(),
            "still 1 distinct approver"
        );
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
        assert!(
            eval(&p, &retracted, Some(&one), 0).is_err(),
            "Monotonic must bite"
        );
    }

    #[test]
    fn council_non_member_slot_pinned() {
        let c = CouncilCharter::new(charter_2of3().members[..2].to_vec(), 2);
        let p = council_cell_program(&c).unwrap();
        let proposed = proposed_state(&c, field_from_u64(7));
        let mut bad = proposed.clone();
        bad.fields[(FIRST_APPROVAL_SLOT + 2) as usize] = field_from_u64(1); // 3rd slot, 2-member charter
        assert!(
            eval(&p, &bad, Some(&proposed), 0).is_err(),
            "non-member slot is pinned zero"
        );
    }

    /// Actor-bound approvals (gap 1 dissolved): with published member
    /// keys, approval slot i flips ONLY when the turn sender is member i.
    #[test]
    fn council_approval_slots_are_actor_bound() {
        let key_a = [0xA1u8; 32];
        let key_b = [0xB2u8; 32];
        let c = CouncilCharter::with_member_keys(
            vec![
                CellId::from_bytes([0x11; 32]),
                CellId::from_bytes([0x22; 32]),
            ],
            2,
            vec![key_a, key_b],
        );
        let p = council_cell_program(&c).unwrap();
        let proposed = proposed_state(&c, field_from_u64(7));

        let eval_as = |new: &CellState, old: &CellState, sender: [u8; 32]| {
            let ctx = EvalContext {
                sender: Some(sender),
                ..ctx_at(0)
            };
            p.evaluate_full(
                new,
                Some(old),
                Some(&ctx),
                &TransitionMeta::wildcard(),
                &WitnessBundle::empty(),
            )
        };

        // Member A flips A's slot: admitted.
        let mut a_approves = proposed.clone();
        a_approves.fields[FIRST_APPROVAL_SLOT as usize] = field_from_u64(1);
        assert!(eval_as(&a_approves, &proposed, key_a).is_ok());
        // Member B flips A's slot (a member with a real capability, the
        // wrong identity): rejected.
        assert!(
            eval_as(&a_approves, &proposed, key_b).is_err(),
            "B cannot flip A's approval slot"
        );
        // A non-member key flips B's slot: rejected.
        let mut b_approves = proposed.clone();
        b_approves.fields[(FIRST_APPROVAL_SLOT + 1) as usize] = field_from_u64(1);
        assert!(eval_as(&b_approves, &proposed, [0xEE; 32]).is_err());
        // Member B flips B's slot: admitted.
        assert!(eval_as(&b_approves, &proposed, key_b).is_ok());
        // A turn not touching approval slots (e.g. the certify step after
        // both approvals) is admitted regardless of sender identity.
        let mut both = proposed.clone();
        both.fields[FIRST_APPROVAL_SLOT as usize] = field_from_u64(1);
        both.fields[(FIRST_APPROVAL_SLOT + 1) as usize] = field_from_u64(1);
        let mut certified = both.clone();
        certified.fields[APPROVED_FLAG_SLOT as usize] = field_from_u64(1);
        certified.fields[STATE_SLOT as usize] = field_from_u64(STATE_APPROVED);
        assert!(eval_as(&certified, &both, [0xEE; 32]).is_ok());

        // Build-time fail-closed teeth.
        assert_eq!(
            CouncilCharter::with_member_keys(c.members.clone(), 2, vec![key_a])
                .validate()
                .unwrap_err(),
            PolisError::MemberKeyCountMismatch {
                keys: 1,
                members: 2
            }
        );
        assert_eq!(
            CouncilCharter::with_member_keys(c.members.clone(), 2, vec![key_a, [0u8; 32]])
                .validate()
                .unwrap_err(),
            PolisError::ZeroMemberKey { index: 1 }
        );
        assert_eq!(
            CouncilCharter::with_member_keys(c.members.clone(), 2, vec![key_a, key_a])
                .validate()
                .unwrap_err(),
            PolisError::DuplicateMember
        );
        // Bound and unbound charters over the same cells never alias.
        assert_ne!(
            c.members_commitment(),
            CouncilCharter::new(c.members.clone(), 2).members_commitment()
        );
    }

    #[test]
    fn council_proposal_hash_write_once() {
        let c = charter_2of3();
        let p = council_cell_program(&c).unwrap();
        let proposed = proposed_state(&c, field_from_u64(7));
        let mut swapped = proposed.clone();
        swapped.fields[PROPOSAL_HASH_SLOT as usize] = field_from_u64(8);
        assert!(
            eval(&p, &swapped, Some(&proposed), 0).is_err(),
            "WriteOnce must bite"
        );
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
        assert!(
            eval(&p, &enacted, Some(&certified), 499).is_err(),
            "height 499 < 500"
        );
        assert!(
            eval(&p, &enacted, Some(&certified), 500).is_ok(),
            "height 500 >= 500"
        );
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
        assert!(
            eval(&p, &wrong, Some(&born), 0).is_err(),
            "staging a different hash rejected"
        );
        let right = proposed_state(&terms.charter, terms.new_constitution_hash);
        assert!(eval(&p, &right, Some(&born), 0).is_ok());
        // Zero hash rejected at build.
        let mut z = terms.clone();
        z.new_constitution_hash = FIELD_ZERO;
        assert_eq!(
            amendment_state_constraints(&z),
            Err(PolisError::ZeroAmendmentHash)
        );
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
        assert!(
            eval(&p, &active, Some(&born), 0).is_ok(),
            "activate writes the params"
        );
        // ANY parameter edit on the active cell is rejected.
        for slot in [
            VERSION_SLOT,
            COUNCIL_THRESHOLD_SLOT,
            AMENDMENT_DELAY_SLOT,
            TREASURY_CAP_SLOT,
        ] {
            let mut bad = active.clone();
            bad.fields[slot as usize] = field_from_u64(9_999);
            assert!(
                eval(&p, &bad, Some(&active), 0).is_err(),
                "param slot {slot} must be pinned"
            );
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
        assert!(
            eval(&p, &superseded, Some(&superseded), 0).is_err(),
            "terminal: inert"
        );
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
        assert!(
            eval(&p, &bad, Some(&active), 0).is_err(),
            "tool scope pinned"
        );
        let mut inflated = active.clone();
        inflated.fields[SLICE_SLOT as usize] = field_from_u64(9_999);
        assert!(
            eval(&p, &inflated, Some(&active), 0).is_err(),
            "slice pinned"
        );
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
            worker_state_constraints(&WorkerMandate {
                slice: 0,
                ..m.clone()
            }),
            Err(PolisError::ZeroSlice)
        );
        assert_eq!(
            worker_state_constraints(&WorkerMandate {
                tool_scope: FIELD_ZERO,
                ..m
            }),
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
        assert_ne!(
            a.factory_vk, c.factory_vk,
            "different threshold → different factory"
        );
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

// =============================================================================
// Identity pre-rotation program-level tests (executor-independent; the e2e
// half runs on the real TurnExecutor in `sdk/tests/identity_prerotation_e2e.rs`)
// =============================================================================

#[cfg(test)]
mod identity_tests {
    use super::council::CouncilCharter;
    use super::identity::*;
    use super::*;
    use dregg_cell::preconditions::EvalContext;
    use dregg_cell::program::{ProgramError, TransitionMeta, WitnessBlobView, WitnessBundle, WitnessKindTag};
    use dregg_cell::state::CellState;

    fn devices_2of2() -> CouncilCharter {
        CouncilCharter::new(
            vec![
                CellId::from_bytes([0xD1; 32]),
                CellId::from_bytes([0xD2; 32]),
            ],
            2,
        )
    }

    fn charter() -> IdentityCharter {
        IdentityCharter {
            council: devices_2of2(),
            cooling_period: 50,
        }
    }

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

    /// Evaluate with an exhibited `Preimage32` witness (the rotate-verb shape).
    fn eval_revealing(
        program: &CellProgram,
        new: &CellState,
        old: Option<&CellState>,
        height: u64,
        preimage: Option<[u8; 32]>,
    ) -> Result<(), ProgramError> {
        let blobs: Vec<WitnessBlobView<'_>> = Vec::new();
        let stored;
        let blobs = match &preimage {
            Some(p) => {
                stored = p.to_vec();
                vec![WitnessBlobView {
                    kind: WitnessKindTag::Preimage32,
                    bytes: &stored,
                }]
            }
            None => blobs,
        };
        program.evaluate_full(
            new,
            old,
            Some(&ctx_at(height)),
            &TransitionMeta::wildcard(),
            &WitnessBundle {
                blobs: &blobs,
                registry: None,
            },
        )
    }

    /// The genesis (KERI `icp`) post-state: birth keys + first pre-commitment.
    fn genesis_state(
        ch: &IdentityCharter,
        birth_commit: FieldElement,
        first_digest: FieldElement,
    ) -> CellState {
        let mut s = CellState::new(0);
        s.fields[STATE_SLOT as usize] = field_from_u64(STATE_ACTIVE);
        s.fields[NEXT_KEYS_DIGEST_SLOT as usize] = first_digest;
        s.fields[CURRENT_KEYS_COMMIT_SLOT as usize] = birth_commit;
        s.fields[COUNCIL_COMMIT_SLOT as usize] = ch.council.members_commitment();
        s
    }

    /// Key generations: G0 (birth), G1 (pre-committed at genesis), G2.
    fn generations() -> ([u8; 32], [u8; 32], [u8; 32]) {
        let g0 = key_set_commitment(&[[0x10; 32], [0x11; 32]]);
        let g1 = key_set_commitment(&[[0x20; 32], [0x21; 32]]);
        let g2 = key_set_commitment(&[[0x30; 32], [0x31; 32]]);
        (g0, g1, g2)
    }

    /// The post-state of an honest rotation to `new_commit` at `height`.
    fn rotated(
        base: &CellState,
        new_commit: FieldElement,
        fresh_digest: FieldElement,
        height: u64,
    ) -> CellState {
        let mut s = base.clone();
        s.fields[NEXT_KEYS_DIGEST_SLOT as usize] = fresh_digest;
        s.fields[CURRENT_KEYS_COMMIT_SLOT as usize] = new_commit;
        s.fields[LAST_ROTATED_AT_SLOT as usize] = field_from_u64(height);
        s
    }

    #[test]
    fn genesis_installs_first_precommitment() {
        let ch = charter();
        let p = identity_cell_program(&ch).unwrap();
        let born = CellState::new(0);
        let (g0, g1, _) = generations();
        let active = genesis_state(&ch, g0, next_keys_digest(&g1));
        assert!(
            eval_revealing(&p, &active, Some(&born), 0, None).is_ok(),
            "genesis (no preimage — nothing committed yet) must commit"
        );
        // ACTIVE without a pre-commitment: refused (the chain must start).
        let mut chainless = active.clone();
        chainless.fields[NEXT_KEYS_DIGEST_SLOT as usize] = FIELD_ZERO;
        assert!(
            eval_revealing(&p, &chainless, Some(&born), 0, None).is_err(),
            "ACTIVE demands a live next-keys digest"
        );
        // ACTIVE without a current key commitment: refused.
        let mut keyless = active.clone();
        keyless.fields[CURRENT_KEYS_COMMIT_SLOT as usize] = FIELD_ZERO;
        assert!(eval_revealing(&p, &keyless, Some(&born), 0, None).is_err());
        // Council commitment is pinned: a wrong commitment is refused.
        let mut usurped = active.clone();
        usurped.fields[COUNCIL_COMMIT_SLOT as usize] = field_from_u64(0xBAD);
        assert!(eval_revealing(&p, &usurped, Some(&born), 0, None).is_err());
    }

    #[test]
    fn honest_rotation_exhibits_preimage_and_chains() {
        let ch = charter();
        let p = identity_cell_program(&ch).unwrap();
        let (g0, g1, g2) = generations();
        let active = genesis_state(&ch, g0, next_keys_digest(&g1));
        // Cooled (height 100 >= 0 + 50), exhibiting G1 (the committed
        // preimage), installing it, committing G2's digest.
        let post = rotated(&active, g1, next_keys_digest(&g2), 100);
        assert!(
            eval_revealing(&p, &post, Some(&active), 100, Some(g1)).is_ok(),
            "honest rotation must commit"
        );
        // The register now holds the FRESH commitment — the next link.
        assert_eq!(
            post.fields[NEXT_KEYS_DIGEST_SLOT as usize],
            next_keys_digest(&g2)
        );
    }

    #[test]
    fn forged_key_set_refused() {
        // COMPROMISE RESISTANCE: presenting ANY key set other than the
        // pre-committed one is refused — an admitted forgery would BE a
        // blake3 collision (`rotate_compromise_resistant`).
        let ch = charter();
        let p = identity_cell_program(&ch).unwrap();
        let (g0, g1, g2) = generations();
        let active = genesis_state(&ch, g0, next_keys_digest(&g1));
        let forged = key_set_commitment(&[[0xEE; 32]]);
        let post = rotated(&active, forged, next_keys_digest(&g2), 100);
        assert!(
            eval_revealing(&p, &post, Some(&active), 100, Some(forged)).is_err(),
            "wrong preimage must be refused"
        );
    }

    #[test]
    fn rotation_without_preimage_refused_even_with_current_keys() {
        // THE TOOTH: a turn that moves the key registers WITHOUT exhibiting
        // the preimage is refused — even though it is (at the executor
        // level) signed by the CURRENT keys. Current keys do not occur in
        // the guard (`rotate_current_keys_irrelevant`): exfiltrating every
        // signing key gains exactly nothing toward rotating.
        let ch = charter();
        let p = identity_cell_program(&ch).unwrap();
        let (g0, g1, g2) = generations();
        let active = genesis_state(&ch, g0, next_keys_digest(&g1));
        let post = rotated(&active, g1, next_keys_digest(&g2), 100);
        assert!(
            matches!(
                eval_revealing(&p, &post, Some(&active), 100, None),
                Err(ProgramError::PreimageWitnessMissing)
            ),
            "no preimage exhibited ⇒ refused, regardless of signatures"
        );
    }

    #[test]
    fn install_must_match_exhibited_preimage() {
        // The exhibit and the install are the SAME value: revealing the
        // right preimage but installing a different current commitment is
        // refused (`rotate_installs`).
        let ch = charter();
        let p = identity_cell_program(&ch).unwrap();
        let (g0, g1, g2) = generations();
        let active = genesis_state(&ch, g0, next_keys_digest(&g1));
        let mut post = rotated(&active, g1, next_keys_digest(&g2), 100);
        post.fields[CURRENT_KEYS_COMMIT_SLOT as usize] = key_set_commitment(&[[0xEE; 32]]);
        assert!(eval_revealing(&p, &post, Some(&active), 100, Some(g1)).is_err());
    }

    #[test]
    fn rotation_must_recommit_fresh_digest() {
        // The chain never ends: zeroing the register is refused even with
        // the right preimage.
        let ch = charter();
        let p = identity_cell_program(&ch).unwrap();
        let (g0, g1, _) = generations();
        let active = genesis_state(&ch, g0, next_keys_digest(&g1));
        let post = rotated(&active, g1, FIELD_ZERO, 100);
        assert!(eval_revealing(&p, &post, Some(&active), 100, Some(g1)).is_err());
    }

    #[test]
    fn cooling_blocks_admitted_preimage() {
        // STRICT DOMINATION, one direction: an event the bare preimage
        // gate would admit (the right preimage, honestly installed) is
        // STILL refused inside the cooling window — slow and visible.
        let ch = charter(); // cooling_period = 50
        let p = identity_cell_program(&ch).unwrap();
        let (g0, g1, g2) = generations();
        let mut active = genesis_state(&ch, g0, next_keys_digest(&g1));
        active.fields[LAST_ROTATED_AT_SLOT as usize] = field_from_u64(100);
        // Inside the window (100 + 50 > 149): refused.
        let inside = rotated(&active, g1, next_keys_digest(&g2), 149);
        assert!(
            eval_revealing(&p, &inside, Some(&active), 149, Some(g1)).is_err(),
            "preimage-holding rotation still waits out the window"
        );
        // At the boundary (100 + 50 <= 150): admitted (no over-tightening).
        let at = rotated(&active, g1, next_keys_digest(&g2), 150);
        assert!(eval_revealing(&p, &at, Some(&active), 150, Some(g1)).is_ok());
        // Cooled but FORGED: still refused — cooling alone would have
        // admitted the patient attacker (`preimage_blocks_cooled_rotation`).
        let forged = key_set_commitment(&[[0xEE; 32]]);
        let cooled_forged = rotated(&active, forged, next_keys_digest(&g2), 150);
        assert!(eval_revealing(&p, &cooled_forged, Some(&active), 150, Some(forged)).is_err());
    }

    #[test]
    fn rotation_stamps_its_height() {
        let ch = charter();
        let p = identity_cell_program(&ch).unwrap();
        let (g0, g1, g2) = generations();
        let active = genesis_state(&ch, g0, next_keys_digest(&g1));
        // Stamping a height other than the execution height: refused
        // (back/future-dating the cooling anchor would warp the window).
        let post = rotated(&active, g1, next_keys_digest(&g2), 90);
        assert!(eval_revealing(&p, &post, Some(&active), 100, Some(g1)).is_err());
    }

    #[test]
    fn chain_pinned_by_commitments() {
        // THE FORWARD CHAIN: two admitted rotations replay link-for-link;
        // the commitment stream reconstructs the key history, and a forged
        // first link kills the chain (`rotChain_pinned_by_commitments`).
        let ch = charter();
        let p = identity_cell_program(&ch).unwrap();
        let (g0, g1, g2) = generations();
        let g3 = key_set_commitment(&[[0x40; 32], [0x41; 32]]);
        let active = genesis_state(&ch, g0, next_keys_digest(&g1));
        // Link 1: G0 → G1 at height 100.
        let s1 = rotated(&active, g1, next_keys_digest(&g2), 100);
        assert!(eval_revealing(&p, &s1, Some(&active), 100, Some(g1)).is_ok());
        // Link 2: G1 → G2 at height 200 (cooled past 100 + 50).
        let s2 = rotated(&s1, g2, next_keys_digest(&g3), 200);
        assert!(eval_revealing(&p, &s2, Some(&s1), 200, Some(g2)).is_ok());
        // Reconstruct: each installed commitment is the preimage of the
        // PREVIOUS state's register — the receipt stream IS the KEL.
        assert_eq!(
            next_keys_digest(&s1.fields[CURRENT_KEYS_COMMIT_SLOT as usize]),
            active.fields[NEXT_KEYS_DIGEST_SLOT as usize]
        );
        assert_eq!(
            next_keys_digest(&s2.fields[CURRENT_KEYS_COMMIT_SLOT as usize]),
            s1.fields[NEXT_KEYS_DIGEST_SLOT as usize]
        );
        // A stale-generation replay (exhibiting G1 again after G1 was
        // exposed) no longer matches the advanced register: refused.
        let replay = rotated(&s2, g1, next_keys_digest(&g3), 300);
        assert!(eval_revealing(&p, &replay, Some(&s2), 300, Some(g1)).is_err());
    }

    #[test]
    fn retired_identity_is_inert() {
        let ch = charter();
        let p = identity_cell_program(&ch).unwrap();
        let (g0, g1, g2) = generations();
        let active = genesis_state(&ch, g0, next_keys_digest(&g1));
        let mut retired = active.clone();
        retired.fields[STATE_SLOT as usize] = field_from_u64(STATE_RETIRED);
        assert!(eval_revealing(&p, &retired, Some(&active), 0, None).is_ok());
        // No rotation can commit on a retired identity (no transition row).
        let post = rotated(&retired, g1, next_keys_digest(&g2), 100);
        assert!(eval_revealing(&p, &post, Some(&retired), 100, Some(g1)).is_err());
    }

    #[test]
    fn charter_fail_closed_and_content_addressed() {
        let mut ch = charter();
        ch.cooling_period = 0;
        assert_eq!(
            identity_state_constraints(&ch),
            Err(PolisError::ZeroCoolingPeriod)
        );
        let a = identity_factory_descriptor(&charter()).unwrap();
        let b = identity_factory_descriptor(&charter()).unwrap();
        assert_eq!(a.factory_vk, b.factory_vk);
        let mut longer = charter();
        longer.cooling_period = 100;
        let c = identity_factory_descriptor(&longer).unwrap();
        assert_ne!(
            a.factory_vk, c.factory_vk,
            "the cooling window is part of the identity's content address"
        );
    }

    #[test]
    fn inspect_identity_decodes() {
        let ch = charter();
        let (g0, g1, _) = generations();
        let mut active = genesis_state(&ch, g0, next_keys_digest(&g1));
        active.fields[LAST_ROTATED_AT_SLOT as usize] = field_from_u64(123);
        let status = inspect_identity(&ch, &active.fields);
        assert_eq!(status.state, IdentityState::Active);
        assert_eq!(status.next_keys_digest, next_keys_digest(&g1));
        assert_eq!(status.current_keys_commit, g0);
        assert_eq!(status.last_rotated_at, 123);
        assert!(status.council_commit_matches);
    }
}
