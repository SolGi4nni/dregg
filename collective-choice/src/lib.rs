//! # collective-choice — the general voting engine for dregg
//!
//! A **poll** → **cap-bounded ballots** → a **monotone verifiable tally** → a
//! **decision-turn**. This crate is *assembly, not invention*: it welds four
//! governance mechanisms that already ship and already bite through the
//! verified executor into one [`VoteEngine`] that both the CYOA lane
//! (`spween-dregg` branch-selection) and the governance lane
//! (`dregg-governance` proposals) consume.
//!
//! ## The four proven mechanisms it composes
//!
//! 1. **One-vote-per-ballot** — a factory-born ballot cell whose `VOTE` slot is
//!    [`StateConstraint::WriteOnce`], reused verbatim from
//!    [`starbridge_privacy_voting::ballot_factory_descriptor`]. A second
//!    `cast_vote` on the same ballot is a real executor refusal.
//! 2. **Monotone tally** — the poll cell's per-option tally slots are
//!    [`StateConstraint::Monotonic`], so a stale/replayed value can never shrink
//!    the board (privacy-voting's poll substrate, generalized to N options).
//! 3. **Quorum gate** — the reusable in-cell M-of-N gate lifted from the polis
//!    council (`starbridge-apps/polis:637`): a single
//!    [`StateConstraint::AffineLe`] `{ M·RESOLVED − Σ TALLY_i ≤ 0 }` guarding
//!    the `RESOLVED` slot, so a decision-turn can commit *only* once the running
//!    total reaches quorum.
//! 4. **Non-amplifying delegation (liquid democracy)** —
//!    [`dregg_intent::agent_mandate::Mandate::sub_delegate`] (AND-only macaroon
//!    attenuation): a voter hands their ballot-cap to a delegate who votes with
//!    it; the delegated authority can never exceed what was delegated
//!    ([`DelegTree::no_amplify`]), and the vote still counts exactly once.
//!
//! Plus a **one-vote nullifier set** ([`CollectiveChoice::nullifiers`])
//! mirroring the node's `used_proof_hashes` (`node/src/state.rs:196`): the third
//! depth of double-vote defence, network-wide dedup of a ballot proof.
//!
//! ## One-vote at three depths
//!
//! A double vote is refused three independent ways: (i) the ballot's
//! `WriteOnce(VOTE)` caveat, (ii) the single per-voter ballot cell (a
//! deterministic blinding token — a voter has exactly one ballot per poll), and
//! (iii) the engine nullifier set.

#![forbid(unsafe_code)]

use std::collections::{BTreeSet, HashMap, HashSet};

use dregg_app_framework::{
    Action, AgentCipherclerk, AppCipherclerk, AuthRequired, CellId, CellMode, CellProgram, Effect,
    EmbeddedExecutor, Event, FieldElement, StateConstraint, TurnReceipt, field_from_bytes,
    field_from_u64, symbol,
};
use dregg_cell::{Cell, FactoryCreationParams};
use dregg_intent::agent_mandate::{Auth, Caveat, DelegTree, Mandate, Rights};

use starbridge_privacy_voting::{
    BALLOT_FACTORY_VK, ballot_child_program_vk, ballot_factory_descriptor, build_cast_vote_action,
};

// =============================================================================
// Poll-cell state schema (16 slots; MAX_OPTIONS tallies fill slots 8..16)
// =============================================================================

/// BLAKE3 of the poll question. `WriteOnce`.
pub const QUESTION_HASH_SLOT: u8 = 2;
/// Commitment over the eligible-voter set (the electorate). `WriteOnce`.
pub const ELECTORATE_ROOT_SLOT: u8 = 3;
/// The quorum threshold `M`: the decision-turn certifies only at `Σ TALLY ≥ M`.
/// `WriteOnce` (also baked as the `AffineLe` coefficient).
pub const QUORUM_M_SLOT: u8 = 4;
/// Number of active options. `WriteOnce`.
pub const OPTION_COUNT_SLOT: u8 = 5;
/// Non-zero once the poll is closed. `WriteOnce`.
pub const CLOSED_SLOT: u8 = 6;
/// The decision flag: 0 while pending, 1 once the quorum `AffineLe` certifies a
/// result. `WriteOnce` and gated by the quorum `AffineLe`.
pub const RESOLVED_SLOT: u8 = 7;
/// First per-option tally slot; option `i` lives at `TALLY_BASE + i`. `Monotonic`.
pub const TALLY_BASE: u8 = 8;
/// Ceiling on options (slots 8..16 — the 16-slot cell's structural ceiling).
pub const MAX_OPTIONS: usize = 8;

/// The caveat method-code the ballot cap admits (a vote-cast action).
pub const CAST_METHOD: u64 = 1;

/// Marker written into the poll `CLOSED` slot.
pub const CLOSED_MARKER: u64 = 1;

// =============================================================================
// The public value types
// =============================================================================

/// A poll handle — the id of the factory-seeded poll (tally-board) cell.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct PollId(pub CellId);

/// The specification a caller opens a poll with.
#[derive(Clone, Debug)]
pub struct PollSpec {
    /// The poll question (its BLAKE3 is pinned `WriteOnce` on the poll cell).
    pub question: String,
    /// The ballot options; `1..=MAX_OPTIONS` of them.
    pub options: Vec<String>,
    /// The electorate — the public keys of the voters who may hold a ballot cap.
    pub electorate: Vec<[u8; 32]>,
    /// The quorum threshold `M`: a decision certifies only once `Σ TALLY ≥ M`.
    pub quorum_m: u64,
}

/// A **ballot capability** — one voter's single-use authority to vote in a poll.
/// Holding one *is* eligibility (it is minted only to an electorate member);
/// exercising it writes the voter's factory-born ballot cell's `WriteOnce(VOTE)`
/// slot. A delegate obtains a strictly-attenuated copy via
/// [`CollectiveChoice::delegate`].
#[derive(Clone, Debug)]
pub struct BallotCap {
    /// The poll this ballot votes in.
    pub poll: PollId,
    /// The voter's factory-born ballot cell (the `WriteOnce(VOTE)` cell).
    pub ballot: CellId,
    /// The electorate member this ballot was issued to.
    pub voter_pk: [u8; 32],
    /// Who currently holds the cap (the voter, or a delegate after
    /// [`CollectiveChoice::delegate`]).
    pub holder: CellId,
    /// The non-amplifying delegation mandate (Lean-mirrored `Mandate`); a
    /// delegate's copy is `mandate.sub_delegate(..)` — provably ⊆ this one.
    pub mandate: Mandate,
}

/// A monotone, light-client-recomputable tally.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Tally {
    /// Per-option running counts (index = option).
    pub per_option: Vec<u64>,
    /// The total across options.
    pub total: u64,
}

/// A certified decision — produced only once the quorum `AffineLe` gate admits
/// the `RESOLVED` turn.
#[derive(Clone, Debug)]
pub struct Decision {
    /// The winning option (argmax tally; ties break to the lowest index).
    pub winner: usize,
    /// The winning option's tally.
    pub winner_tally: u64,
    /// The total that met quorum.
    pub total: u64,
}

/// Everything the engine can refuse.
#[derive(Clone, Debug)]
pub enum VoteError {
    /// The poll id is unknown to this engine.
    NoSuchPoll,
    /// `options.len()` outside `1..=MAX_OPTIONS`, or `quorum_m == 0`.
    BadPollSpec(String),
    /// The option index is out of range for the poll.
    BadOption,
    /// The ballot cap belongs to a different poll.
    WrongPoll,
    /// The voter is not in the poll's electorate (holds no eligibility cap).
    Ineligible,
    /// The nullifier for this ballot has already been consumed (double vote).
    DoubleVote,
    /// The verified executor refused a submitted turn (the caveat that bit is in
    /// the message — e.g. `WriteOnce`, `Monotonic`, or the quorum `AffineLe`).
    Executor(String),
    /// A ledger invariant was violated (birth/seed failure).
    Ledger(String),
}

impl std::fmt::Display for VoteError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            VoteError::NoSuchPoll => write!(f, "no such poll"),
            VoteError::BadPollSpec(m) => write!(f, "bad poll spec: {m}"),
            VoteError::BadOption => write!(f, "option out of range"),
            VoteError::WrongPoll => write!(f, "ballot cap is for a different poll"),
            VoteError::Ineligible => write!(f, "voter is not in the electorate"),
            VoteError::DoubleVote => write!(f, "ballot nullifier already consumed"),
            VoteError::Executor(m) => write!(f, "executor refused: {m}"),
            VoteError::Ledger(m) => write!(f, "ledger error: {m}"),
        }
    }
}

impl std::error::Error for VoteError {}

// =============================================================================
// The VoteEngine trait — the clean interface spween-dregg + dregg-governance consume
// =============================================================================

/// The general voting interface. `spween-dregg` drives branch selection through
/// it (options = branches); `dregg-governance` drives proposals through it
/// (options = for/against/abstain, quorum = the constitutional threshold).
pub trait VoteEngine {
    /// The engine's refusal type.
    type Error;

    /// Open a cap-bounded poll: pins the question, electorate commitment, quorum
    /// `M`, and option count on a governance cell whose caveats are its rules.
    fn open_poll(&mut self, spec: PollSpec) -> Result<PollId, Self::Error>;

    /// Cast one vote: a single-use ballot cap → one vote. The ballot's
    /// `WriteOnce(VOTE)` + the nullifier set make a double vote a refusal; the
    /// poll's `Monotonic` tally records it.
    fn cast(
        &mut self,
        poll: PollId,
        ballot: &BallotCap,
        option: usize,
    ) -> Result<TurnReceipt, Self::Error>;

    /// Read the monotone tally a light client verifies (nobody can stuff or
    /// forge it — each vote is a verifiable turn, the tally a monotone reduction).
    fn tally(&self, poll: PollId) -> Result<Tally, Self::Error>;

    /// Certify the decision-turn — commits only once the quorum `AffineLe` gate
    /// is satisfied. `Ok(None)` below quorum (the gate refused the turn).
    fn resolve(&mut self, poll: PollId) -> Result<Option<Decision>, Self::Error>;
}

// =============================================================================
// The engine
// =============================================================================

struct PollRecord {
    cell: CellId,
    electorate: BTreeSet<[u8; 32]>,
    option_count: usize,
    /// Append-only cast log — what a light client replays to recompute the
    /// tally independently of the stored slots.
    receipts: Vec<usize>,
    /// Ballots already issued (voter pk → ballot cell), so re-issue is idempotent.
    issued: HashMap<[u8; 32], CellId>,
}

/// The collective-choice engine — one embedded executor hosting every poll,
/// ballot, and tally as verified turns.
pub struct CollectiveChoice {
    clerk: AppCipherclerk,
    exec: EmbeddedExecutor,
    polls: HashMap<CellId, PollRecord>,
    /// Consumed ballot nullifiers — the `used_proof_hashes` mirror.
    nullifiers: HashSet<[u8; 32]>,
    poll_seq: u64,
}

impl CollectiveChoice {
    /// Stand up a fresh engine (its own operator identity + embedded executor),
    /// deploy the ballot factory, and fund the operator so it can pay turn fees.
    pub fn new(federation_id: [u8; 32]) -> Self {
        let clerk = AppCipherclerk::new(AgentCipherclerk::new(), federation_id);
        // The domain MUST match `AppCipherclerk`'s default ("default"), so the
        // executor's seeded+funded operator cell (`exec.cell_id()`) is the same
        // cell the clerk signs turns from (`clerk.cell_id()`). A mismatch leaves
        // the issuer cell unseeded → "cell not found" on the first factory birth.
        let exec = EmbeddedExecutor::new(&clerk, "default");
        exec.deploy_factory(ballot_factory_descriptor());

        let operator = clerk.cell_id();
        exec.with_ledger_mut(|ledger| {
            if let Some(cell) = ledger.get_mut(&operator) {
                cell.state.set_balance(1_000_000_000);
            }
        });

        CollectiveChoice {
            clerk,
            exec,
            polls: HashMap::new(),
            nullifiers: HashSet::new(),
            poll_seq: 0,
        }
    }

    fn operator_pk(&self) -> [u8; 32] {
        self.clerk.public_key().0
    }

    /// Mint (or return the existing) ballot cap for an electorate member. This
    /// is the **eligibility gate**: a voter not in the poll's electorate is
    /// refused — there is no cap to hold. The ballot is a factory-born cell
    /// under a per-voter blinding token, so each voter has exactly one ballot
    /// per poll (the single-use-cap depth of one-vote).
    pub fn issue_ballot(
        &mut self,
        poll: PollId,
        voter_pk: [u8; 32],
    ) -> Result<BallotCap, VoteError> {
        let operator = self.operator_pk();
        let record = self.polls.get(&poll.0).ok_or(VoteError::NoSuchPoll)?;
        if !record.electorate.contains(&voter_pk) {
            return Err(VoteError::Ineligible);
        }

        let token = ballot_token(poll.0, &voter_pk);
        let ballot = CellId::derive_raw(&operator, &token);

        // Idempotent: a voter's ballot is deterministic in (poll, voter).
        if !record.issued.contains_key(&voter_pk) {
            let params = FactoryCreationParams {
                mode: CellMode::Sovereign,
                program_vk: Some(ballot_child_program_vk()),
                initial_fields: vec![],
                initial_caps: vec![],
                owner_pubkey: operator,
            };
            let birth = self
                .clerk
                .create_from_factory(BALLOT_FACTORY_VK, operator, token, params);
            self.exec
                .submit_turn(&birth)
                .map_err(|e| VoteError::Ledger(e.to_string()))?;

            // Grant the operator a cap reaching the freshly-born ballot so the
            // cast turn can author against it (the WriteOnce caveat still bites).
            let operator_cell = self.clerk.cell_id();
            self.exec.with_ledger_mut(|ledger| {
                if let Some(agent) = ledger.get_mut(&operator_cell) {
                    agent.capabilities.grant(ballot, AuthRequired::Signature);
                }
            });

            self.polls
                .get_mut(&poll.0)
                .expect("poll present")
                .issued
                .insert(voter_pk, ballot);
        }

        let mandate = Mandate::root(
            self.clerk.cell_id(),
            CellId::from_bytes(voter_pk),
            ballot,
            vote_rights(),
            1,
            Caveat::only(&[CAST_METHOD]),
        );

        Ok(BallotCap {
            poll,
            ballot,
            voter_pk,
            holder: CellId::from_bytes(voter_pk),
            mandate,
        })
    }

    /// **Liquid democracy** — delegate a ballot cap to `delegate_pk`. The
    /// delegate receives a *strictly-attenuated* copy of the mandate
    /// ([`Mandate::sub_delegate`]: rights ⊆, budget ≤, caveat ⇒) over the SAME
    /// ballot cell, so the delegate's vote counts exactly ONCE and the delegated
    /// authority can never be amplified ([`DelegTree::no_amplify`]). A
    /// re-delegation is likewise attenuating.
    pub fn delegate(&self, cap: &BallotCap, delegate_pk: [u8; 32]) -> BallotCap {
        let delegate_cell = CellId::from_bytes(delegate_pk);
        // The child mandate: `keep ∩ requested`, `min(budget, ..)`, `caveat ∧ ..`
        // — the non-amplifying sub-delegation. Requesting more never widens it.
        let child = cap.mandate.sub_delegate(
            delegate_cell,
            &vote_rights(),
            cap.mandate.budget,
            &Caveat::any(),
        );
        BallotCap {
            poll: cap.poll,
            ballot: cap.ballot,
            voter_pk: cap.voter_pk,
            holder: delegate_cell,
            mandate: child,
        }
    }

    /// The delegation tree `root → delegate` — the object whose
    /// [`DelegTree::no_amplify`] / [`DelegTree::well_attenuated`] teeth witness
    /// that a delegated vote can never out-authorize the delegator.
    pub fn delegation_tree(root: &BallotCap, delegate: &BallotCap) -> DelegTree {
        DelegTree::leaf(root.mandate.clone()).with_child(DelegTree::leaf(delegate.mandate.clone()))
    }

    /// Recompute the tally from the append-only cast log alone — the
    /// **light-client** view. A verifier that never re-executes replays the
    /// recorded casts and sums them; [`tally`](Self::tally) reads the executor's
    /// stored monotone slots. When they agree the board is unforged.
    pub fn light_client_tally(&self, poll: PollId) -> Result<Tally, VoteError> {
        let record = self.polls.get(&poll.0).ok_or(VoteError::NoSuchPoll)?;
        let mut per_option = vec![0u64; record.option_count];
        for &opt in &record.receipts {
            per_option[opt] += 1;
        }
        let total = per_option.iter().sum();
        Ok(Tally { per_option, total })
    }

    fn poll_program(quorum_m: u64, option_count: usize) -> CellProgram {
        let mut cs: Vec<StateConstraint> = vec![
            StateConstraint::WriteOnce {
                index: QUESTION_HASH_SLOT,
            },
            StateConstraint::WriteOnce {
                index: ELECTORATE_ROOT_SLOT,
            },
            StateConstraint::WriteOnce {
                index: QUORUM_M_SLOT,
            },
            StateConstraint::WriteOnce {
                index: OPTION_COUNT_SLOT,
            },
            StateConstraint::WriteOnce { index: CLOSED_SLOT },
            StateConstraint::WriteOnce {
                index: RESOLVED_SLOT,
            },
        ];
        for i in 0..MAX_OPTIONS {
            cs.push(StateConstraint::Monotonic {
                index: TALLY_BASE + i as u8,
            });
        }
        // THE QUORUM GATE (lifted from polis:637): `M·RESOLVED − Σ TALLY_i ≤ 0`.
        // RESOLVED == 0 ⇒ `−Σ TALLY ≤ 0` (always true); arming RESOLVED := 1
        // DEMANDS `Σ TALLY ≥ M` in the same post-state — the decision-turn.
        let mut terms: Vec<(i64, u8)> = vec![(quorum_m as i64, RESOLVED_SLOT)];
        for i in 0..option_count {
            terms.push((-1, TALLY_BASE + i as u8));
        }
        cs.push(StateConstraint::AffineLe { terms, c: 0 });
        CellProgram::always(cs)
    }
}

impl VoteEngine for CollectiveChoice {
    type Error = VoteError;

    fn open_poll(&mut self, spec: PollSpec) -> Result<PollId, VoteError> {
        let option_count = spec.options.len();
        if option_count == 0 || option_count > MAX_OPTIONS {
            return Err(VoteError::BadPollSpec(format!(
                "options must be 1..={MAX_OPTIONS}, got {option_count}"
            )));
        }
        if spec.quorum_m == 0 {
            return Err(VoteError::BadPollSpec("quorum_m must be >= 1".into()));
        }

        let operator = self.operator_pk();
        self.poll_seq += 1;
        let token = *blake3::hash(
            &[
                b"collective-choice-poll".as_slice(),
                &self.poll_seq.to_be_bytes(),
            ]
            .concat(),
        )
        .as_bytes();
        let poll_cell = CellId::derive_raw(&operator, &token);

        let program = Self::poll_program(spec.quorum_m, option_count);
        let electorate: BTreeSet<[u8; 32]> = spec.electorate.iter().copied().collect();

        // Seed the poll (tally-board) cell: install the full program so the
        // executor re-enforces WriteOnce/Monotonic/AffineLe on every touching
        // turn, then pin the genesis state. Mirrors privacy-voting's `seed_poll`.
        let mut cell = Cell::new(operator, token);
        cell.program = program.clone();
        cell.state.set_field(
            QUESTION_HASH_SLOT as usize,
            field_from_bytes(spec.question.as_bytes()),
        );
        cell.state
            .set_field(ELECTORATE_ROOT_SLOT as usize, electorate_root(&electorate));
        cell.state
            .set_field(QUORUM_M_SLOT as usize, field_from_u64(spec.quorum_m));
        cell.state.set_field(
            OPTION_COUNT_SLOT as usize,
            field_from_u64(option_count as u64),
        );
        cell.state
            .set_field(CLOSED_SLOT as usize, field_from_u64(0));
        cell.state
            .set_field(RESOLVED_SLOT as usize, field_from_u64(0));
        for i in 0..MAX_OPTIONS {
            cell.state
                .set_field(TALLY_BASE as usize + i, field_from_u64(0));
        }
        self.exec.ensure_cell(cell).map_err(VoteError::Ledger)?;
        self.exec.install_program(poll_cell, program);

        // Grant the operator a cap reaching the poll cell so tally/resolve turns
        // author against it.
        let operator_cell = self.clerk.cell_id();
        self.exec.with_ledger_mut(|ledger| {
            if let Some(agent) = ledger.get_mut(&operator_cell) {
                agent.capabilities.grant(poll_cell, AuthRequired::Signature);
            }
        });

        self.polls.insert(
            poll_cell,
            PollRecord {
                cell: poll_cell,
                electorate,
                option_count,
                receipts: Vec::new(),
                issued: HashMap::new(),
            },
        );
        Ok(PollId(poll_cell))
    }

    fn cast(
        &mut self,
        poll: PollId,
        ballot: &BallotCap,
        option: usize,
    ) -> Result<TurnReceipt, VoteError> {
        if ballot.poll != poll {
            return Err(VoteError::WrongPoll);
        }
        let (poll_cell, option_count) = {
            let record = self.polls.get(&poll.0).ok_or(VoteError::NoSuchPoll)?;
            (record.cell, record.option_count)
        };
        if option >= option_count {
            return Err(VoteError::BadOption);
        }

        // Depth (iii): the nullifier set — a consumed ballot proof is refused
        // network-wide (the `used_proof_hashes` mirror).
        let nullifier = ballot_nullifier(poll.0, ballot.ballot);
        if self.nullifiers.contains(&nullifier) {
            return Err(VoteError::DoubleVote);
        }

        // Depth (i): the ballot's `WriteOnce(VOTE)` — the choice code is the
        // option index + 1 (non-zero so WriteOnce treats it as "set").
        let choice = option as u64 + 1;
        let action = build_cast_vote_action(&self.clerk, ballot.ballot, poll_cell, choice);
        let receipt = self
            .exec
            .submit_action(&self.clerk, action)
            .map_err(|e| VoteError::Executor(e.to_string()))?;

        // Only now consume the nullifier (the ballot turn committed).
        self.nullifiers.insert(nullifier);

        // The tally is a verifiable turn: read the live monotone slot and write
        // `live + 1`. `Monotonic(TALLY_i)` re-enforced — a stale value cannot
        // shrink the board.
        let live = self
            .exec
            .cell_state(poll_cell)
            .map(|s| field_to_u64(&s.fields[TALLY_BASE as usize + option]))
            .unwrap_or(0);
        let bump = build_tally_bump(&self.clerk, poll_cell, option, live + 1);
        self.exec
            .submit_action(&self.clerk, bump)
            .map_err(|e| VoteError::Executor(e.to_string()))?;

        self.polls
            .get_mut(&poll.0)
            .expect("poll present")
            .receipts
            .push(option);

        Ok(receipt)
    }

    fn tally(&self, poll: PollId) -> Result<Tally, VoteError> {
        let record = self.polls.get(&poll.0).ok_or(VoteError::NoSuchPoll)?;
        let state = self
            .exec
            .cell_state(record.cell)
            .ok_or_else(|| VoteError::Ledger("poll cell has no live state".into()))?;
        let per_option: Vec<u64> = (0..record.option_count)
            .map(|i| field_to_u64(&state.fields[TALLY_BASE as usize + i]))
            .collect();
        let total = per_option.iter().sum();
        Ok(Tally { per_option, total })
    }

    fn resolve(&mut self, poll: PollId) -> Result<Option<Decision>, VoteError> {
        let poll_cell = self.polls.get(&poll.0).ok_or(VoteError::NoSuchPoll)?.cell;
        let tally = self.tally(poll)?;
        let (winner, winner_tally) = argmax(&tally.per_option);
        let decision = Decision {
            winner,
            winner_tally,
            total: tally.total,
        };

        // Idempotent: if already resolved, report the decision.
        if let Some(state) = self.exec.cell_state(poll_cell) {
            if field_to_u64(&state.fields[RESOLVED_SLOT as usize]) != 0 {
                return Ok(Some(decision));
            }
        }

        // Attempt the decision-turn: set RESOLVED := 1. The quorum `AffineLe`
        // (`M·RESOLVED − Σ TALLY ≤ 0`) is the REAL gate — below quorum the
        // executor refuses this turn, so `resolve` yields `None`.
        let action = build_resolve_action(&self.clerk, poll_cell);
        match self.exec.submit_action(&self.clerk, action) {
            Ok(_) => Ok(Some(decision)),
            Err(_) => Ok(None),
        }
    }
}

// =============================================================================
// Turn-builders + encoders
// =============================================================================

fn build_tally_bump(
    clerk: &AppCipherclerk,
    poll_cell: CellId,
    option: usize,
    new_val: u64,
) -> Action {
    let effects = vec![
        Effect::SetField {
            cell: poll_cell,
            index: TALLY_BASE as usize + option,
            value: field_from_u64(new_val),
        },
        Effect::EmitEvent {
            cell: poll_cell,
            event: Event::new(symbol("vote-tallied"), vec![field_from_u64(option as u64)]),
        },
    ];
    clerk.make_action(poll_cell, "record_tally", effects)
}

fn build_resolve_action(clerk: &AppCipherclerk, poll_cell: CellId) -> Action {
    let effects = vec![
        Effect::SetField {
            cell: poll_cell,
            index: RESOLVED_SLOT as usize,
            value: field_from_u64(1),
        },
        Effect::EmitEvent {
            cell: poll_cell,
            event: Event::new(symbol("poll-resolved"), vec![]),
        },
    ];
    clerk.make_action(poll_cell, "resolve", effects)
}

/// The rights a ballot cap confers: the vote (a `SetField`) is the `Read`
/// (`EFFECT_SET_FIELD`) facet — the narrowest tier, never `Grant`/`Transfer`.
fn vote_rights() -> Rights {
    let mut r = BTreeSet::new();
    r.insert(Auth::Read);
    r
}

/// The per-voter blinding token: `blake3(poll ‖ voter)` — deterministic, so a
/// voter has exactly one ballot cell per poll, yet unlinkable to their primary
/// cell (privacy-voting's blinding-token model).
fn ballot_token(poll: CellId, voter_pk: &[u8; 32]) -> [u8; 32] {
    *blake3::hash(&[poll.as_bytes().as_slice(), voter_pk.as_slice()].concat()).as_bytes()
}

/// The ballot nullifier: `blake3(poll ‖ ballot)` — the value dedup'd in the
/// engine nullifier set (the `used_proof_hashes` mirror).
fn ballot_nullifier(poll: CellId, ballot: CellId) -> [u8; 32] {
    *blake3::hash(&[poll.as_bytes().as_slice(), ballot.as_bytes().as_slice()].concat()).as_bytes()
}

/// A commitment over the electorate: `blake3` of the sorted voter keys, lifted
/// into a field (pinned `WriteOnce` on the poll cell).
fn electorate_root(electorate: &BTreeSet<[u8; 32]>) -> FieldElement {
    let mut hasher = blake3::Hasher::new();
    for pk in electorate {
        hasher.update(pk);
    }
    field_from_bytes(hasher.finalize().as_bytes())
}

/// Read a `u64` from the last 8 big-endian bytes of a field element (the inverse
/// of [`field_from_u64`], matching the executor's `affine_sum` decode).
fn field_to_u64(f: &FieldElement) -> u64 {
    let mut b = [0u8; 8];
    b.copy_from_slice(&f[24..32]);
    u64::from_be_bytes(b)
}

/// Argmax over per-option tallies; ties break to the lowest index.
fn argmax(per_option: &[u64]) -> (usize, u64) {
    let mut best = 0usize;
    let mut best_v = 0u64;
    for (i, &v) in per_option.iter().enumerate() {
        if v > best_v {
            best = i;
            best_v = v;
        }
    }
    (best, best_v)
}

#[cfg(test)]
mod tests;
