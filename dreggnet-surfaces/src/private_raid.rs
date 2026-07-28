//! A proof-assigned, capability-authorized tactical raid Offering.
//!
//! This composes two already-real organs instead of inventing a raid state machine:
//!
//! - [`RaidAssignmentSession`] verifies the existing Lean-emitted HidingFri receipt for
//!   a private 4x4 suitability/admissibility matrix and yields one public optimal role
//!   permutation; and
//! - [`PartyOffering`] forms those four authenticated identities into its real
//!   capability-seated [`dreggnet_party::Party`], then drives signed target ballots and
//!   transactional party+Arena contributions. The verified assignment also mints one
//!   context-bound tactical sigil per role. A player must burn the sigil assigned to
//!   their proof seat through a real capability-bearing cell before contributing.
//!
//! The proof arrives through the generic durable binary-operation seam (web owning-file
//! upload) or a bounded sequence of ordinary text turns (Discord/Telegram), both ending
//! at the same canonical decoder and HidingFri verifier. Until it lands, no ordinary
//! party action is available. Afterwards each public proof seat may claim
//! only the corresponding real capability role, burn that role's sigil, and spend the
//! resulting tactical authorization in the shared encounter. A substituted actor or role
//! is refused before lobby progress; after launch a forged teammate tactic still reaches
//! the party executor and is refused by the missing capability before the Arena changes.
//! A fixed-roster deployment may additionally install an fhIR exact-QP allocation claim.
//! Its verified one-hot coordinate is mapped through this exact authenticated roster to
//! the member's proof-assigned party role; accepting any other actor or role reaches a
//! capability-backed allocation cell and is refused by the executor.
//!
//! ## Honest binding boundary
//!
//! The current private-assignment statement publishes seat numbers, not player identity
//! keys. This Offering context-binds the exact ordered identity roster, hosted seed, and
//! canonical proof receipt into one operation id and rechecks that interpretation on
//! restart. That is a fail-closed **host/replay binding**, not an executor-level
//! `ObservedFieldEquals` between the proof receipt and party cells. The proof operation,
//! lobby audit cell, proof-sigil world, party world, and tactical Arena remain separately
//! verified records; no cross-world atomicity is claimed. A sigil burn is a durable
//! prerequisite action, not half of the later party/Arena transaction. The Tier-1 proof
//! producer still sees the private
//! matrix, while players and hosts see the public assigned roles.
//!
//! ## Who sees what, and when — this is NOT a hidden-information offering
//!
//! The name says "private" about the OPTIMIZER'S INPUTS, never about its output, and the
//! surface is deliberately **viewer-invariant in its state tree**:
//!
//! - **Before the proof lands** there is nothing per-seat to see. Every viewer reads the
//!   same awaiting-proof section: the expected proof session, how many receipt bytes have
//!   been assembled, and [`ASSIGN_DISCLOSURE`].
//! - **After the proof lands** every viewer — an assigned seat, a teammate, a spectator
//!   holding no seat, an anonymous reader — reads the SAME four `(seat, identity, role)`
//!   rows, because `roles[4]` is a *public input* of the HidingFri statement. Anyone
//!   holding the receipt recomputes it against the pinned verifier key; fogging it would
//!   hide nothing and would only make the page lie about what it knows.
//! - **What is actually secret** never enters this crate: the 4x4 suitability scores, the
//!   independent admissibility matrix, the blinding, and the aggregate score stay with the
//!   Tier-1 producer. `RaidAssignmentReceipt` is documented to carry none of them, and the
//!   rendered `input root` is a *commitment* to them.
//!
//! So [`Offering::hidden_information`] is **`false`**, declared explicitly on both
//! offerings rather than inherited, and a shared surface (a Telegram group's one editable
//! message, a Discord channel post, a projector) may paint this offering in full. The only
//! per-viewer projection is the ACTION SET — which seat may claim, burn, or spend — the
//! "dims cap-gated affordances" case that the trait documents as `false`. Every action
//! label names only public material (a role name, a short identity), so the
//! button-label class of fog leak has no purchase here.
//! `tests/private_raid.rs::the_state_tree_is_one_public_statement_for_every_viewer`
//! is the tooth: it fails if a future change makes the state tree viewer-dependent.
//! The underlying descriptor's documented finite modular-to-integer bridge from emitted
//! AIR facts to the exact `OptimalLex` relation is still a named proof gate; this module
//! consumes the existing verifier at its current assurance level and does not promote it.

use std::collections::BTreeSet;

use deos_view::ViewNode;
use dregg_app_framework::{
    CellId, CellProgram, FieldElement, StateConstraint, TurnReceipt, field_from_u64,
};
use dreggnet_offerings::player_name::display_name_of;
use dreggnet_offerings::refusal::belongs_to_another_player;
use dreggnet_offerings::{
    Action, BinaryOperationDescriptor, BinaryOperationError, BinaryOperationReceipt,
    BinaryOperationReplayMaterial, CollectiveDecision, DreggIdentity, Offering, OfferingError,
    Outcome, RunCost, SessionConfig, Surface, VerifyReport,
};
use dreggnet_party::Role;
use dungeon_on_dregg::private_raid::{
    RaidAssignmentReceipt, RaidAssignmentSession, RaidPartyAssignment, RaidRole,
};
use fhir::{Compiled, VerifiedRosterAllocationClaim, verify_zero_kkt_roster_allocation_claim};
use starbridge_v2::world::{CommitOutcome, World, make_open_cell, set_field};

use crate::party::{PartyOffering, PartySession, TURN_CLAIM};
use crate::{action_menu, pill, row, section, text};

/// Suggested catalog key. Registration is deliberately left to the shared-catalog lane.
pub const KEY: &str = "private-raid";
/// Generic binary-operation name for one proof-assignment receipt.
pub const ASSIGN_OPERATION: &str = "party.private-raid-assignment.v1";
/// Exact wire type emitted by the existing private raid producer.
pub const ASSIGN_MEDIA_TYPE: &str = "application/vnd.dregg.private-raid-assignment.v1+postcard";
/// Same bounded receipt ceiling as the existing dungeon consumer.
pub const MAX_ASSIGNMENT_BYTES: usize = 8 * 1024 * 1024;
/// Disclosure rendered by every generic operation adapter.
pub const ASSIGN_DISCLOSURE: &str = "HidingFri checks a public four-seat role permutation against the existing private-assignment AIR for one producer-private 4x4 matrix; the intended relation is admissible, globally score-optimal, and deterministically tie-broken, while its documented finite modular-to-integer OptimalLex bridge remains a proof gate. The producer sees the scores and admissibility bits; the host retains the public statement, verifier identity, and opaque proof. Seat numbers are interpreted against this raid's ordered authenticated roster by a replay-checked host binding, not by an ObservedFieldEquals cross-cell tooth.";
/// Public lobby verb used by the catalog-ready wrapper. The first four distinct
/// authenticated actors establish proof seats 0..3 in exact replay order.
pub const TURN_JOIN_RAID: &str = "join-private-raid";
/// Append one lowercase-hex proof receipt chunk through the ordinary text-action seam.
/// This is the chat-native counterpart of [`ASSIGN_OPERATION`]: Discord text modals
/// and Telegram armed replies already carry this exact [`Action`] shape, while web
/// keeps its more efficient owning-file upload.
pub const TURN_STREAM_ASSIGNMENT: &str = "stream-private-raid-assignment";
/// Verify and install the receipt assembled by [`TURN_STREAM_ASSIGNMENT`].
pub const TURN_FINALIZE_ASSIGNMENT: &str = "finalize-private-raid-assignment";
/// Burn the proof-assigned role's tactical sigil (`arg = Role::index()`).
/// The executor, not the host, decides whether this seat holds the requested sigil cap.
pub const TURN_PRIME_TACTIC: &str = "prime-private-raid-tactic";
/// Accept the fhIR-selected member in their proof-assigned party role.
/// The requested role is `arg = Role::index()`; actor and role authority are
/// both decided by the allocation world's capabilities.
pub const TURN_ACCEPT_FHIR_ALLOCATION: &str = "accept-fhir-raid-allocation";
/// Maximum raw bytes in one chat-native proof chunk. Its lowercase hex wire is
/// 240 characters, fitting the standing Discord text-modal ceiling of 300.
pub const MAX_STREAM_CHUNK_BYTES: usize = 120;
/// Chat-native proof assembly is deliberately smaller than the 8 MiB owning-file
/// operation. The current width-299 HidingFRI receipt is about 304 KiB, so the
/// bounded chat route admits up to 512 KiB with room for stable encoding-size
/// variation; larger future proof families must use web/Activity/Mini-App upload
/// rather than an unbounded message journal.
pub const MAX_STREAM_ASSIGNMENT_BYTES: usize = 512 * 1024;
/// Derived hard ceiling on executor turns spent assembling one chat proof.
pub const MAX_STREAM_CHUNKS: usize =
    (MAX_STREAM_ASSIGNMENT_BYTES + MAX_STREAM_CHUNK_BYTES - 1) / MAX_STREAM_CHUNK_BYTES;

const BABYBEAR_P_MINUS_ONE: u64 = 2_013_265_920;
const HOSTED_LOBBY_REVISION_SLOT: usize = 0;
const HOSTED_LOBBY_ROOT_BASE: usize = 1;
const SIGIL_SPENT_SLOT: usize = 0;
const SIGIL_CONTEXT_BASE: usize = 1;
const SIGIL_ROLE_SLOT: usize = 5;
const FHIR_ALLOCATION_SPENT_SLOT: usize = 0;
const FHIR_ALLOCATION_CONTEXT_BASE: usize = 1;
const FHIR_ALLOCATION_MEMBER_SLOT: usize = 5;
const FHIR_ALLOCATION_ROLE_SLOT: usize = 6;
const UPLOAD_REVISION_SLOT: usize = 0;
const UPLOAD_LENGTH_SLOT: usize = 1;
const UPLOAD_ROOT_BASE: usize = 2;
const UPLOAD_SEALED_SLOT: usize = 6;

/// Decode the canonical big-endian [`field_from_u64`] representation used by
/// the executor's integer constraints.
fn field_to_u64(field: &FieldElement) -> u64 {
    let mut bytes = [0u8; 8];
    bytes.copy_from_slice(&field[24..32]);
    u64::from_be_bytes(bytes)
}

/// Match the private raid's canonical nonzero BabyBear session derivation.
pub fn proof_session_for_seed(seed: u64) -> u32 {
    ((seed % BABYBEAR_P_MINUS_ONE) + 1) as u32
}

#[derive(Clone, Debug)]
struct TacticStep {
    actor: String,
    role: Role,
    receipt_hash: [u8; 32],
}

/// Executor-backed one-shot permissions minted from one verified assignment.
///
/// Each proof role owns a separate sigil cell. Each public seat is represented by
/// an agent cell holding exactly one capability: the sigil selected for that seat
/// by the verified permutation. The role cells carry the full assignment operation
/// receipt id as four immutable u64 limbs plus their role tag. Burning a sigil is a
/// genuine turn from the seat agent onto the requested role cell.
struct ProofTactics {
    world: World,
    agents: [CellId; 4],
    sigils: [CellId; 4],
    context_limbs: [u64; 4],
    history: Vec<TacticStep>,
}

impl ProofTactics {
    fn new(assignment: RaidPartyAssignment, receipt_id: [u8; 32]) -> Result<Self, String> {
        let context_limbs = receipt_limbs(receipt_id);
        let mut world = World::new();
        let mut sigils = Vec::with_capacity(4);
        for role in Role::ALL {
            let mut cell = make_open_cell(0xC0 + role.index() as u8, 0);
            for (index, limb) in context_limbs.iter().copied().enumerate() {
                cell.state.fields[SIGIL_CONTEXT_BASE + index] = field_from_u64(limb);
            }
            cell.state.fields[SIGIL_ROLE_SLOT] = field_from_u64(role.index() as u64 + 1);
            let mut constraints = vec![
                StateConstraint::FieldDelta {
                    index: SIGIL_SPENT_SLOT as u8,
                    delta: field_from_u64(1),
                },
                StateConstraint::FieldEquals {
                    index: SIGIL_SPENT_SLOT as u8,
                    value: field_from_u64(1),
                },
                StateConstraint::WriteOnce {
                    index: SIGIL_SPENT_SLOT as u8,
                },
            ];
            for (index, limb) in context_limbs.iter().copied().enumerate() {
                constraints.push(StateConstraint::WriteOnce {
                    index: (SIGIL_CONTEXT_BASE + index) as u8,
                });
                constraints.push(StateConstraint::FieldEquals {
                    index: (SIGIL_CONTEXT_BASE + index) as u8,
                    value: field_from_u64(limb),
                });
            }
            constraints.push(StateConstraint::WriteOnce {
                index: SIGIL_ROLE_SLOT as u8,
            });
            constraints.push(StateConstraint::FieldEquals {
                index: SIGIL_ROLE_SLOT as u8,
                value: field_from_u64(role.index() as u64 + 1),
            });
            cell.program = CellProgram::Predicate(constraints);
            sigils.push(world.genesis_install(cell));
        }
        let sigils: [CellId; 4] = sigils
            .try_into()
            .map_err(|_| "private raid did not install four tactical sigils".to_string())?;

        let mut agents = Vec::with_capacity(4);
        for seat in 0..4 {
            let assigned = assignment
                .role_for_seat(seat)
                .ok_or_else(|| format!("private assignment omitted public seat {seat}"))?;
            let role = capability_role(assigned);
            let (agent, _) =
                world.genesis_cell_with_cap(0xD0 + seat as u8, 0, sigils[role.index()]);
            agents.push(agent);
        }
        let agents = agents
            .try_into()
            .map_err(|_| "private raid did not install four tactical agents".to_string())?;
        Ok(Self {
            world,
            agents,
            sigils,
            context_limbs,
            history: Vec::with_capacity(4),
        })
    }

    fn turns(&self) -> usize {
        self.history.len()
    }

    fn is_primed(&self, role: Role) -> bool {
        self.world
            .ledger()
            .get(&self.sigils[role.index()])
            .is_some_and(|cell| field_to_u64(&cell.state.fields[SIGIL_SPENT_SLOT]) == 1)
    }

    fn prime(
        &mut self,
        seat: usize,
        actor: &DreggIdentity,
        requested: Role,
    ) -> Result<TurnReceipt, String> {
        let Some(agent) = self.agents.get(seat).copied() else {
            return Err("tactical sigil actor has no public proof seat".to_string());
        };
        let target = self.sigils[requested.index()];
        let turn = self.world.turn(
            agent,
            vec![set_field(target, SIGIL_SPENT_SLOT, field_from_u64(1))],
        );
        let receipt = match self.world.commit_turn(turn) {
            CommitOutcome::Committed { receipt, .. } => *receipt,
            CommitOutcome::Rejected { reason, .. } => {
                return Err(format!("proof-assigned tactical sigil refused: {reason}"));
            }
            CommitOutcome::Queued { .. } => {
                return Err("proof-assigned tactical world is suspended".to_string());
            }
        };
        self.history.push(TacticStep {
            actor: actor.0.clone(),
            role: requested,
            receipt_hash: receipt.turn_hash,
        });
        Ok(receipt)
    }

    fn verify(
        &self,
        roster: &[String; 4],
        assignment: RaidPartyAssignment,
        receipt_id: [u8; 32],
    ) -> Result<(), String> {
        if self.history.len() > 4 {
            return Err("more tactical sigils landed than the four-role kit contains".to_string());
        }
        let expected_limbs = receipt_limbs(receipt_id);
        if self.context_limbs != expected_limbs {
            return Err("tactical sigil context differs from the proof operation".to_string());
        }
        for role in Role::ALL {
            let Some(cell) = self.world.ledger().get(&self.sigils[role.index()]) else {
                return Err(format!("{} tactical sigil cell is absent", role.name()));
            };
            let spent = field_to_u64(&cell.state.fields[SIGIL_SPENT_SLOT]);
            if spent > 1 {
                return Err(format!(
                    "{} tactical sigil has a non-bit spent value",
                    role.name()
                ));
            }
            for (index, expected) in expected_limbs.iter().copied().enumerate() {
                if field_to_u64(&cell.state.fields[SIGIL_CONTEXT_BASE + index]) != expected {
                    return Err(format!("{} tactical sigil lost proof context", role.name()));
                }
            }
            if field_to_u64(&cell.state.fields[SIGIL_ROLE_SLOT]) != role.index() as u64 + 1 {
                return Err(format!("{} tactical sigil changed role tag", role.name()));
            }
        }
        if Role::ALL
            .into_iter()
            .filter(|role| self.is_primed(*role))
            .count()
            != self.history.len()
        {
            return Err("tactical sigil cells and burn journal disagree".to_string());
        }
        for step in &self.history {
            if step.receipt_hash == [0u8; 32]
                || !self
                    .world
                    .receipts()
                    .iter()
                    .any(|receipt| receipt.turn_hash == step.receipt_hash)
            {
                return Err("tactical sigil burn lacks its complete executor receipt".to_string());
            }
        }

        // Re-drive the application journal against fresh role cells and capabilities.
        // Cell ids and turn hashes are process-local, so compare exact semantic bits;
        // every live receipt was independently checked against this world's provenance.
        let mut replay = Self::new(assignment, receipt_id)?;
        for (index, step) in self.history.iter().enumerate() {
            let seat = roster
                .iter()
                .position(|identity| identity == &step.actor)
                .ok_or_else(|| format!("tactical burn {index} actor left the proof roster"))?;
            replay
                .prime(seat, &DreggIdentity(step.actor.clone()), step.role)
                .map_err(|reason| format!("tactical burn {index} refused on replay: {reason}"))?;
        }
        for role in Role::ALL {
            if replay.is_primed(role) != self.is_primed(role) {
                return Err(format!("{} tactical sigil changed on replay", role.name()));
            }
        }
        Ok(())
    }
}

/// Deployment-pinned fhIR policy and hostile canonical optimizer artifact.
///
/// Construction immediately verifies the exact-QP claim. The same bytes are
/// nevertheless retained so session verification and restart replay can rerun
/// the complete hostile-wire boundary instead of trusting the cached winner.
#[derive(Clone, Debug)]
struct FhirRaidAllocationPolicy {
    compiled: Compiled,
    wire: Vec<u8>,
    program_digest: [u8; 32],
    expected_commitment: [u8; 32],
}

impl FhirRaidAllocationPolicy {
    fn new(
        roster: &[String; 4],
        compiled: Compiled,
        wire: Vec<u8>,
        expected_commitment: Option<[u8; 32]>,
    ) -> Result<Self, String> {
        let roster_ids = fhir_roster_ids(roster)?;
        let claim = verify_zero_kkt_roster_allocation_claim(&compiled, &wire, &roster_ids)
            .map_err(|error| format!("fhIR raid allocation refused: {error}"))?;
        if let Some(expected) = expected_commitment
            && claim.commitment() != expected
        {
            return Err(
                "fhIR raid allocation differs from the deployment's roster/objective claim"
                    .to_string(),
            );
        }
        Ok(Self {
            compiled,
            wire,
            program_digest: claim.program_digest(),
            expected_commitment: claim.commitment(),
        })
    }

    fn verify_for_roster(
        &self,
        roster: &[String; 4],
    ) -> Result<VerifiedRosterAllocationClaim, String> {
        let roster_ids = fhir_roster_ids(roster)?;
        let claim =
            verify_zero_kkt_roster_allocation_claim(&self.compiled, &self.wire, &roster_ids)
                .map_err(|error| format!("fhIR raid allocation refused on replay: {error}"))?;
        if claim.program_digest() != self.program_digest
            || claim.commitment() != self.expected_commitment
        {
            return Err(
                "fhIR raid allocation changed its program, roster, winner, or exact objective"
                    .to_string(),
            );
        }
        Ok(claim)
    }

    fn same_deployment(&self, other: &Self) -> bool {
        self.program_digest == other.program_digest
            && self.expected_commitment == other.expected_commitment
            && self.wire == other.wire
    }
}

#[derive(Clone, Debug)]
struct FhirAllocationStep {
    actor: String,
    role: Role,
    receipt_hash: [u8; 32],
}

/// Executor-backed acceptance of the optimizer-selected real party member and role.
///
/// Four role cells exist, but the selected seat's agent holds exactly one cap: the
/// cell for the role that the independently verified private assignment gave that
/// member. Wrong actors and wrong roles therefore reach the executor and fail its
/// capability check rather than being accepted by a host-side comparison.
struct FhirRaidAllocationGate {
    world: World,
    agents: [CellId; 4],
    role_cells: [CellId; 4],
    context_limbs: [u64; 4],
    selected_seat: usize,
    selected_roster_id: u64,
    selected_role: Role,
    history: Vec<FhirAllocationStep>,
}

impl FhirRaidAllocationGate {
    fn new(
        policy: &FhirRaidAllocationPolicy,
        roster: &[String; 4],
        assignment: RaidPartyAssignment,
        assignment_receipt_id: [u8; 32],
    ) -> Result<Self, String> {
        let claim = policy.verify_for_roster(roster)?;
        let selected_seat = claim.winner_index();
        let selected_role = assignment
            .role_for_seat(selected_seat)
            .map(capability_role)
            .ok_or_else(|| {
                format!("private role assignment omitted fhIR winner seat {selected_seat}")
            })?;
        let selected_roster_id = claim.winner();
        let context_limbs = fhir_allocation_context(
            policy.expected_commitment,
            assignment_receipt_id,
            roster,
            selected_seat,
            selected_role,
        );

        let mut world = World::new();
        let mut role_cells = Vec::with_capacity(4);
        for role in Role::ALL {
            let mut cell = make_open_cell(0xA0 + role.index() as u8, 0);
            for (index, limb) in context_limbs.iter().copied().enumerate() {
                cell.state.fields[FHIR_ALLOCATION_CONTEXT_BASE + index] = field_from_u64(limb);
            }
            cell.state.fields[FHIR_ALLOCATION_MEMBER_SLOT] = field_from_u64(selected_roster_id);
            cell.state.fields[FHIR_ALLOCATION_ROLE_SLOT] = field_from_u64(role.index() as u64 + 1);
            let mut constraints = vec![
                StateConstraint::FieldDelta {
                    index: FHIR_ALLOCATION_SPENT_SLOT as u8,
                    delta: field_from_u64(1),
                },
                StateConstraint::FieldEquals {
                    index: FHIR_ALLOCATION_SPENT_SLOT as u8,
                    value: field_from_u64(1),
                },
                StateConstraint::WriteOnce {
                    index: FHIR_ALLOCATION_SPENT_SLOT as u8,
                },
            ];
            for (index, limb) in context_limbs.iter().copied().enumerate() {
                constraints.push(StateConstraint::WriteOnce {
                    index: (FHIR_ALLOCATION_CONTEXT_BASE + index) as u8,
                });
                constraints.push(StateConstraint::FieldEquals {
                    index: (FHIR_ALLOCATION_CONTEXT_BASE + index) as u8,
                    value: field_from_u64(limb),
                });
            }
            constraints.extend([
                StateConstraint::WriteOnce {
                    index: FHIR_ALLOCATION_MEMBER_SLOT as u8,
                },
                StateConstraint::FieldEquals {
                    index: FHIR_ALLOCATION_MEMBER_SLOT as u8,
                    value: field_from_u64(selected_roster_id),
                },
                StateConstraint::WriteOnce {
                    index: FHIR_ALLOCATION_ROLE_SLOT as u8,
                },
                StateConstraint::FieldEquals {
                    index: FHIR_ALLOCATION_ROLE_SLOT as u8,
                    value: field_from_u64(role.index() as u64 + 1),
                },
            ]);
            cell.program = CellProgram::Predicate(constraints);
            role_cells.push(world.genesis_install(cell));
        }
        let role_cells: [CellId; 4] = role_cells
            .try_into()
            .map_err(|_| "fhIR raid allocation did not install four role cells".to_string())?;

        let mut agents = Vec::with_capacity(4);
        for seat in 0..4 {
            let agent = if seat == selected_seat {
                world
                    .genesis_cell_with_cap(0xB0 + seat as u8, 0, role_cells[selected_role.index()])
                    .0
            } else {
                world.genesis_cell(0xB0 + seat as u8, 0)
            };
            agents.push(agent);
        }
        let agents = agents
            .try_into()
            .map_err(|_| "fhIR raid allocation did not install four seat agents".to_string())?;
        Ok(Self {
            world,
            agents,
            role_cells,
            context_limbs,
            selected_seat,
            selected_roster_id,
            selected_role,
            history: Vec::with_capacity(1),
        })
    }

    fn turns(&self) -> usize {
        self.history.len()
    }

    fn landed(&self) -> bool {
        !self.history.is_empty()
    }

    fn selected_seat(&self) -> usize {
        self.selected_seat
    }

    fn selected_role(&self) -> Role {
        self.selected_role
    }

    fn is_spent(&self, role: Role) -> bool {
        self.world
            .ledger()
            .get(&self.role_cells[role.index()])
            .is_some_and(|cell| field_to_u64(&cell.state.fields[FHIR_ALLOCATION_SPENT_SLOT]) == 1)
    }

    fn accept(
        &mut self,
        seat: usize,
        actor: &DreggIdentity,
        requested_role: Role,
    ) -> Result<TurnReceipt, String> {
        let Some(agent) = self.agents.get(seat).copied() else {
            return Err("fhIR allocation actor has no public raid seat".to_string());
        };
        let target = self.role_cells[requested_role.index()];
        let turn = self.world.turn(
            agent,
            vec![set_field(
                target,
                FHIR_ALLOCATION_SPENT_SLOT,
                field_from_u64(1),
            )],
        );
        let receipt = match self.world.commit_turn(turn) {
            CommitOutcome::Committed { receipt, .. } => *receipt,
            CommitOutcome::Rejected { reason, .. } => {
                return Err(format!("fhIR raid allocation executor refused: {reason}"));
            }
            CommitOutcome::Queued { .. } => {
                return Err("fhIR raid allocation world is suspended".to_string());
            }
        };
        self.history.push(FhirAllocationStep {
            actor: actor.0.clone(),
            role: requested_role,
            receipt_hash: receipt.turn_hash,
        });
        Ok(receipt)
    }

    fn verify(
        &self,
        policy: &FhirRaidAllocationPolicy,
        roster: &[String; 4],
        assignment: RaidPartyAssignment,
        assignment_receipt_id: [u8; 32],
    ) -> Result<(), String> {
        if self.history.len() > 1 {
            return Err("fhIR raid allocation landed more than once".to_string());
        }
        let expected = Self::new(policy, roster, assignment, assignment_receipt_id)?;
        if self.context_limbs != expected.context_limbs
            || self.selected_seat != expected.selected_seat
            || self.selected_roster_id != expected.selected_roster_id
            || self.selected_role != expected.selected_role
        {
            return Err(
                "fhIR raid allocation changed roster, objective winner, actor, or role".to_string(),
            );
        }
        for role in Role::ALL {
            let Some(cell) = self.world.ledger().get(&self.role_cells[role.index()]) else {
                return Err(format!("fhIR {} allocation cell is absent", role.name()));
            };
            for (index, expected_limb) in self.context_limbs.iter().copied().enumerate() {
                if field_to_u64(&cell.state.fields[FHIR_ALLOCATION_CONTEXT_BASE + index])
                    != expected_limb
                {
                    return Err(format!(
                        "fhIR {} allocation cell lost claim context",
                        role.name()
                    ));
                }
            }
            if field_to_u64(&cell.state.fields[FHIR_ALLOCATION_MEMBER_SLOT])
                != self.selected_roster_id
                || field_to_u64(&cell.state.fields[FHIR_ALLOCATION_ROLE_SLOT])
                    != role.index() as u64 + 1
            {
                return Err(format!(
                    "fhIR {} allocation cell changed member/role binding",
                    role.name()
                ));
            }
        }
        if Role::ALL
            .into_iter()
            .filter(|role| self.is_spent(*role))
            .count()
            != self.history.len()
        {
            return Err("fhIR allocation cells and acceptance journal disagree".to_string());
        }
        for step in &self.history {
            if step.actor != roster[self.selected_seat]
                || step.role != self.selected_role
                || step.receipt_hash == [0u8; 32]
                || !self
                    .world
                    .receipts()
                    .iter()
                    .any(|receipt| receipt.turn_hash == step.receipt_hash)
            {
                return Err(
                    "fhIR allocation acceptance lost its selected actor/role receipt".to_string(),
                );
            }
        }

        let mut replay = expected;
        for step in &self.history {
            replay
                .accept(
                    self.selected_seat,
                    &DreggIdentity(step.actor.clone()),
                    step.role,
                )
                .map_err(|reason| format!("fhIR allocation refused on replay: {reason}"))?;
        }
        for role in Role::ALL {
            if replay.is_spent(role) != self.is_spent(role) {
                return Err(format!(
                    "fhIR {} allocation acceptance changed on replay",
                    role.name()
                ));
            }
        }
        Ok(())
    }
}

#[derive(Clone, Debug)]
struct ProofUploadStep {
    actor: String,
    bytes: Vec<u8>,
    receipt_hash: [u8; 32],
}

/// Executor-audited assembly buffer for frontends whose native affordance is text,
/// not an owning byte upload. The proof remains opaque: the adapter carries lowercase
/// hex, while only the finalizer decodes and invokes the same HidingFri verifier as the
/// binary-operation path.
struct ProofUpload {
    world: World,
    agent: CellId,
    cell: CellId,
    bytes: Vec<u8>,
    hasher: blake3::Hasher,
    history: Vec<ProofUploadStep>,
    final_receipt_hash: Option<[u8; 32]>,
}

impl ProofUpload {
    fn new() -> Self {
        let mut world = World::new();
        let mut cell = make_open_cell(0xE5, 0);
        cell.program = CellProgram::Predicate(vec![
            StateConstraint::FieldDelta {
                index: UPLOAD_REVISION_SLOT as u8,
                delta: field_from_u64(1),
            },
            StateConstraint::Monotonic {
                index: UPLOAD_LENGTH_SLOT as u8,
            },
            StateConstraint::WriteOnce {
                index: UPLOAD_SEALED_SLOT as u8,
            },
        ]);
        let cell = world.genesis_install(cell);
        let (agent, _) = world.genesis_cell_with_cap(0xE6, 0, cell);
        Self {
            world,
            agent,
            cell,
            bytes: Vec::new(),
            hasher: proof_stream_hasher(),
            history: Vec::new(),
            final_receipt_hash: None,
        }
    }

    fn turns(&self) -> usize {
        self.history.len() + usize::from(self.final_receipt_hash.is_some())
    }

    fn is_pristine(&self) -> bool {
        self.history.is_empty() && self.bytes.is_empty() && self.final_receipt_hash.is_none()
    }

    fn is_sealed(&self) -> bool {
        self.final_receipt_hash.is_some()
    }

    fn next_chunk(&self) -> i64 {
        i64::try_from(self.history.len()).expect("proof chunk count fits i64")
    }

    fn effects(
        &self,
        next_len: usize,
        digest: [u8; 32],
        sealed: bool,
    ) -> Vec<dregg_app_framework::Effect> {
        let mut effects = vec![
            set_field(
                self.cell,
                UPLOAD_REVISION_SLOT,
                field_from_u64((self.turns() + 1) as u64),
            ),
            set_field(
                self.cell,
                UPLOAD_LENGTH_SLOT,
                field_from_u64(next_len as u64),
            ),
            set_field(
                self.cell,
                UPLOAD_SEALED_SLOT,
                field_from_u64(if sealed { 1 } else { 0 }),
            ),
        ];
        for (index, limb) in receipt_limbs(digest).into_iter().enumerate() {
            effects.push(set_field(
                self.cell,
                UPLOAD_ROOT_BASE + index,
                field_from_u64(limb),
            ));
        }
        effects
    }

    fn commit(&mut self, effects: Vec<dregg_app_framework::Effect>) -> Result<TurnReceipt, String> {
        let turn = self.world.turn(self.agent, effects);
        match self.world.commit_turn(turn) {
            CommitOutcome::Committed { receipt, .. } => Ok(*receipt),
            CommitOutcome::Rejected { reason, .. } => {
                Err(format!("private proof upload audit cell refused: {reason}"))
            }
            CommitOutcome::Queued { .. } => {
                Err("private proof upload audit world is suspended".to_string())
            }
        }
    }

    fn append(
        &mut self,
        actor: &DreggIdentity,
        chunk_index: i64,
        encoded: &str,
    ) -> Result<TurnReceipt, String> {
        if self.is_sealed() {
            return Err("private proof upload is already sealed".to_string());
        }
        if chunk_index != self.next_chunk() {
            return Err(format!(
                "private proof chunk index mismatch: expected {}, received {chunk_index}",
                self.next_chunk()
            ));
        }
        if self.history.len() >= MAX_STREAM_CHUNKS {
            return Err(format!(
                "private proof upload exhausted its {MAX_STREAM_CHUNKS}-chunk chat budget; use the owning-file uploader"
            ));
        }
        let chunk = decode_lower_hex(encoded)?;
        if chunk.is_empty() || chunk.len() > MAX_STREAM_CHUNK_BYTES {
            return Err(format!(
                "private proof chunk contains {} bytes; expected 1..={MAX_STREAM_CHUNK_BYTES}",
                chunk.len()
            ));
        }
        let Some(next_len) = self.bytes.len().checked_add(chunk.len()) else {
            return Err("private proof upload length overflow".to_string());
        };
        if next_len > MAX_STREAM_ASSIGNMENT_BYTES {
            return Err(format!(
                "private chat proof would contain {next_len} bytes; maximum is {MAX_STREAM_ASSIGNMENT_BYTES}; use the owning-file uploader"
            ));
        }
        let mut next_hasher = self.hasher.clone();
        next_hasher.update(&chunk);
        let digest = *next_hasher.finalize().as_bytes();
        let receipt = self.commit(self.effects(next_len, digest, false))?;
        self.bytes.extend_from_slice(&chunk);
        self.hasher = next_hasher;
        self.history.push(ProofUploadStep {
            actor: actor.0.clone(),
            bytes: chunk,
            receipt_hash: receipt.turn_hash,
        });
        Ok(receipt)
    }

    fn seal(&mut self) -> Result<TurnReceipt, String> {
        if self.is_sealed() {
            return Err("private proof upload is already sealed".to_string());
        }
        if self.bytes.is_empty() {
            return Err("private proof upload contains no receipt bytes".to_string());
        }
        let effects = self.effects(self.bytes.len(), *self.hasher.finalize().as_bytes(), true);
        let receipt = self.commit(effects)?;
        self.final_receipt_hash = Some(receipt.turn_hash);
        Ok(receipt)
    }

    fn verify(&self, leader: &str) -> Result<(), String> {
        if self.bytes.len() > MAX_STREAM_ASSIGNMENT_BYTES || self.history.len() > MAX_STREAM_CHUNKS
        {
            return Err("private chat proof upload exceeds its declared budget".to_string());
        }
        if self.history.iter().any(|step| step.actor != leader) {
            return Err("a private proof chunk was not submitted by public seat 0".to_string());
        }
        let joined = self
            .history
            .iter()
            .flat_map(|step| step.bytes.iter().copied())
            .collect::<Vec<_>>();
        if joined != self.bytes {
            return Err("private proof chunks do not reconstruct the retained receipt".to_string());
        }
        let mut expected_hasher = proof_stream_hasher();
        expected_hasher.update(&self.bytes);
        if self.hasher.finalize() != expected_hasher.finalize() {
            return Err("private proof upload incremental digest changed".to_string());
        }
        let Some(cell) = self.world.ledger().get(&self.cell) else {
            return Err("private proof upload audit cell is absent".to_string());
        };
        if field_to_u64(&cell.state.fields[UPLOAD_REVISION_SLOT]) != self.turns() as u64
            || field_to_u64(&cell.state.fields[UPLOAD_LENGTH_SLOT]) != self.bytes.len() as u64
            || field_to_u64(&cell.state.fields[UPLOAD_SEALED_SLOT])
                != if self.is_sealed() { 1 } else { 0 }
        {
            return Err("private proof upload journal and audit counters disagree".to_string());
        }
        if self.turns() > 0 {
            let expected_root = receipt_limbs(*expected_hasher.finalize().as_bytes());
            for (index, limb) in expected_root.into_iter().enumerate() {
                if field_to_u64(&cell.state.fields[UPLOAD_ROOT_BASE + index]) != limb {
                    return Err("private proof upload audit root changed".to_string());
                }
            }
        }
        for step in &self.history {
            if step.receipt_hash == [0u8; 32]
                || !self
                    .world
                    .receipts()
                    .iter()
                    .any(|receipt| receipt.turn_hash == step.receipt_hash)
            {
                return Err("private proof chunk lacks its executor receipt".to_string());
            }
        }
        if let Some(final_hash) = self.final_receipt_hash
            && (final_hash == [0u8; 32]
                || !self
                    .world
                    .receipts()
                    .iter()
                    .any(|receipt| receipt.turn_hash == final_hash))
        {
            return Err("private proof finalizer lacks its executor receipt".to_string());
        }

        let mut replay = Self::new();
        for (index, step) in self.history.iter().enumerate() {
            replay
                .append(
                    &DreggIdentity(step.actor.clone()),
                    index as i64,
                    &encode_lower_hex(&step.bytes),
                )
                .map_err(|reason| {
                    format!("private proof chunk {index} refused on replay: {reason}")
                })?;
        }
        if self.is_sealed() {
            replay
                .seal()
                .map_err(|reason| format!("private proof finalizer refused on replay: {reason}"))?;
        }
        if replay.bytes != self.bytes || replay.is_sealed() != self.is_sealed() {
            return Err("private proof upload changed on replay".to_string());
        }
        Ok(())
    }
}

struct PreparedAssignment {
    gate: RaidAssignmentSession,
    assignment: RaidPartyAssignment,
    actor: DreggIdentity,
    canonical: Vec<u8>,
    receipt_id: [u8; 32],
    tactics: ProofTactics,
    fhir_allocation: Option<FhirRaidAllocationGate>,
}

/// One hosted raid. An owning-file assignment operation is durable independently of
/// the ordinary action log; the chat-native chunk path is itself a sequence of audited,
/// replayed ordinary actions. [`PartyOffering`] owns every later formation/combat action.
pub struct ProofAssignedRaidSession {
    seed: u64,
    expected_proof_session: u32,
    roster: [String; 4],
    assignment_gate: RaidAssignmentSession,
    assignment_actor: Option<DreggIdentity>,
    canonical_receipt: Option<Vec<u8>>,
    assignment_receipt_id: Option<[u8; 32]>,
    proof_upload: ProofUpload,
    tactics: Option<ProofTactics>,
    fhir_allocation_policy: Option<FhirRaidAllocationPolicy>,
    fhir_allocation: Option<FhirRaidAllocationGate>,
    party: PartySession,
}

impl ProofAssignedRaidSession {
    pub fn assignment(&self) -> Option<RaidPartyAssignment> {
        self.assignment_gate.assignment().copied()
    }

    pub fn assignment_receipt_id(&self) -> Option<[u8; 32]> {
        self.assignment_receipt_id
    }

    pub fn turns(&self) -> usize {
        self.proof_upload.turns()
            + self.party.turns()
            + self.tactics.as_ref().map(ProofTactics::turns).unwrap_or(0)
            + self
                .fhir_allocation
                .as_ref()
                .map(FhirRaidAllocationGate::turns)
                .unwrap_or(0)
    }

    pub fn launched(&self) -> bool {
        self.party.launched()
    }

    pub fn target(&self) -> Option<u8> {
        self.party.target()
    }

    pub fn role_of(&self, actor: &str) -> Option<Role> {
        self.party.role_of(actor)
    }

    /// The exact authenticated roster member selected by the verified fhIR
    /// optimum, when this deployment carries an optimizer allocation policy.
    pub fn fhir_selected_actor(&self) -> Option<&str> {
        let gate = self.fhir_allocation.as_ref()?;
        Some(&self.roster[gate.selected_seat()])
    }

    /// That selected member's independently proof-assigned real party role.
    pub fn fhir_selected_role(&self) -> Option<Role> {
        self.fhir_allocation
            .as_ref()
            .map(FhirRaidAllocationGate::selected_role)
    }

    /// Whether the selected member/role pair has landed through its executor cell.
    pub fn fhir_allocation_landed(&self) -> bool {
        self.fhir_allocation
            .as_ref()
            .is_some_and(FhirRaidAllocationGate::landed)
    }

    fn seat_of(&self, actor: &str) -> Option<usize> {
        self.roster.iter().position(|identity| identity == actor)
    }

    fn assigned_role_for(&self, actor: &str) -> Option<Role> {
        let seat = self.seat_of(actor)?;
        self.assignment()?.role_for_seat(seat).map(capability_role)
    }

    /// Whether this actor has burned the one-shot sigil selected by the proof.
    pub fn tactic_primed_for(&self, actor: &str) -> bool {
        let Some(role) = self.assigned_role_for(actor) else {
            return false;
        };
        self.tactics
            .as_ref()
            .is_some_and(|tactics| tactics.is_primed(role))
    }

    /// Raw receipt bytes assembled through ordinary text actions. This is public
    /// transport state (the opaque proof was already chosen for durable retention),
    /// never the private score/admissibility witness.
    pub fn streamed_assignment_bytes(&self) -> usize {
        self.proof_upload.bytes.len()
    }

    pub fn streamed_assignment_chunks(&self) -> usize {
        self.proof_upload.history.len()
    }
}

/// A raid scenario over one exact ordered public roster.
#[derive(Clone, Debug)]
pub struct ProofAssignedRaidOffering {
    roster: [String; 4],
    fhir_allocation_policy: Option<FhirRaidAllocationPolicy>,
}

impl ProofAssignedRaidOffering {
    /// Construct a scenario whose public proof seats are interpreted in this exact order.
    pub fn new(roster: [String; 4]) -> Result<Self, String> {
        validate_roster(&roster)?;
        Ok(Self {
            roster,
            fhir_allocation_policy: None,
        })
    }

    /// Construct a fixed-roster raid with an exact-QP allocation deployment.
    ///
    /// `wire` is verified immediately, then again during session verification
    /// and replay. Its one-hot winner indexes this exact authenticated roster;
    /// after the private role proof lands, that member's real party role becomes
    /// the only executor-spendable allocation cell.
    pub fn with_fhir_allocation(
        roster: [String; 4],
        compiled: Compiled,
        wire: Vec<u8>,
    ) -> Result<Self, String> {
        validate_roster(&roster)?;
        let policy = FhirRaidAllocationPolicy::new(&roster, compiled, wire, None)?;
        Ok(Self {
            roster,
            fhir_allocation_policy: Some(policy),
        })
    }

    /// As [`Self::with_fhir_allocation`], while requiring the verified claim to
    /// equal a deployment-precommitted program/roster/winner/objective digest.
    pub fn with_precommitted_fhir_allocation(
        roster: [String; 4],
        compiled: Compiled,
        wire: Vec<u8>,
        expected_commitment: [u8; 32],
    ) -> Result<Self, String> {
        validate_roster(&roster)?;
        let policy =
            FhirRaidAllocationPolicy::new(&roster, compiled, wire, Some(expected_commitment))?;
        Ok(Self {
            roster,
            fhir_allocation_policy: Some(policy),
        })
    }

    pub fn roster(&self) -> &[String; 4] {
        &self.roster
    }

    pub fn fhir_allocation_commitment(&self) -> Option<[u8; 32]> {
        self.fhir_allocation_policy
            .as_ref()
            .map(|policy| policy.expected_commitment)
    }

    fn decode_receipt(
        session: &ProofAssignedRaidSession,
        payload: &[u8],
    ) -> Result<(RaidAssignmentReceipt, Vec<u8>), BinaryOperationError> {
        if payload.len() > MAX_ASSIGNMENT_BYTES {
            return Err(BinaryOperationError::Malformed(format!(
                "private raid receipt is {} bytes; maximum is {MAX_ASSIGNMENT_BYTES}",
                payload.len()
            )));
        }
        let receipt = RaidAssignmentReceipt::from_postcard(payload)
            .map_err(|error| BinaryOperationError::Malformed(error.to_string()))?;
        let canonical = receipt
            .to_postcard()
            .map_err(|error| BinaryOperationError::Malformed(error.to_string()))?;
        if canonical != payload {
            return Err(BinaryOperationError::Malformed(
                "private raid receipt is not canonically encoded".to_string(),
            ));
        }
        if receipt.statement().session != session.expected_proof_session {
            return Err(BinaryOperationError::Refused(format!(
                "private raid proof session mismatch: expected {}, claimed {}",
                session.expected_proof_session,
                receipt.statement().session
            )));
        }
        Ok((receipt, canonical))
    }

    fn receipt_id(
        seed: u64,
        roster: &[String; 4],
        actor: &DreggIdentity,
        canonical: &[u8],
    ) -> [u8; 32] {
        let mut hash = blake3::Hasher::new_derive_key("dregg-proof-assigned-tactical-raid-v1");
        hash.update(&seed.to_le_bytes());
        for identity in roster {
            hash.update(&(identity.len() as u64).to_le_bytes());
            hash.update(identity.as_bytes());
        }
        hash.update(&(actor.0.len() as u64).to_le_bytes());
        hash.update(actor.0.as_bytes());
        hash.update(canonical);
        *hash.finalize().as_bytes()
    }

    fn prepare_assignment(
        &self,
        session: &ProofAssignedRaidSession,
        payload: &[u8],
        actor: DreggIdentity,
    ) -> Result<PreparedAssignment, BinaryOperationError> {
        if actor.as_str() != session.roster[0] {
            // The binary-operation twin of the two `advance` gates above — one condition, one
            // sentence, and seat 0's key stays out of it.
            return Err(BinaryOperationError::Refused(belongs_to_another_player(
                "raid's proof upload",
            )));
        }
        let (receipt, canonical) = Self::decode_receipt(session, payload)?;
        let mut gate = session.assignment_gate.clone();
        let assignment = gate
            .accept(&receipt)
            .map_err(|error| BinaryOperationError::Refused(error.to_string()))?;
        let receipt_id = Self::receipt_id(session.seed, &session.roster, &actor, &canonical);
        let tactics =
            ProofTactics::new(assignment, receipt_id).map_err(BinaryOperationError::Refused)?;
        let fhir_allocation = session
            .fhir_allocation_policy
            .as_ref()
            .map(|policy| {
                FhirRaidAllocationGate::new(policy, &session.roster, assignment, receipt_id)
            })
            .transpose()
            .map_err(BinaryOperationError::Refused)?;
        Ok(PreparedAssignment {
            gate,
            assignment,
            actor,
            canonical,
            receipt_id,
            tactics,
            fhir_allocation,
        })
    }

    fn install_assignment(session: &mut ProofAssignedRaidSession, prepared: PreparedAssignment) {
        session.assignment_gate = prepared.gate;
        session.assignment_actor = Some(prepared.actor);
        session.canonical_receipt = Some(prepared.canonical);
        session.assignment_receipt_id = Some(prepared.receipt_id);
        session.tactics = Some(prepared.tactics);
        session.fhir_allocation = prepared.fhir_allocation;
    }

    fn proof_stream_actions(session: &ProofAssignedRaidSession) -> Vec<Action> {
        let mut actions = Vec::with_capacity(2);
        if session.proof_upload.history.len() < MAX_STREAM_CHUNKS
            && session.proof_upload.bytes.len() < MAX_STREAM_ASSIGNMENT_BYTES
        {
            actions.push(
                Action::new(
                    format!(
                        "Append proof chunk {} / {} (lowercase hex, up to {} bytes)",
                        session.proof_upload.next_chunk(),
                        MAX_STREAM_CHUNKS,
                        MAX_STREAM_CHUNK_BYTES
                    ),
                    TURN_STREAM_ASSIGNMENT,
                    session.proof_upload.next_chunk(),
                    true,
                )
                .taking_text(),
            );
        }
        if !session.proof_upload.bytes.is_empty() {
            actions.push(Action::new(
                format!(
                    "Seal and verify {} proof bytes",
                    session.proof_upload.bytes.len()
                ),
                TURN_FINALIZE_ASSIGNMENT,
                session.proof_upload.next_chunk(),
                true,
            ));
        }
        actions
    }

    fn assigned_claim(
        &self,
        session: &ProofAssignedRaidSession,
        input: &Action,
        actor: &DreggIdentity,
    ) -> Result<(), String> {
        let Some(expected) = session.assigned_role_for(actor.as_str()) else {
            return Err(belongs_to_another_player("raid"));
        };
        // NOT the wrong-player condition — an ORDERING one, and the difference matters to the reader:
        // the raid IS theirs, they are simply early. Its own sentence, and still no key in it (naming
        // seat 0's 64-char hex told a waiting player nothing about who to wait for).
        if session.party.seat_count() == 0 && actor.as_str() != session.roster[0] {
            return Err(
                "The player who opened this raid has to take their seat before anyone else can \
                 claim one. Nothing was changed. Wait for them to claim, then claim yours."
                    .to_string(),
            );
        }
        if input.arg != expected.index() as i64 {
            // The player's own key was echoed back at them here, which reads as an accusation. What
            // they need is the role the proof gave them and the press that claims it.
            return Err(format!(
                "The proof assigned you the {} role, and that is the only one you can claim. \
                 Nothing was changed. Claim {} instead.",
                expected.name(),
                expected.name()
            ));
        }
        Ok(())
    }

    fn actions_for_viewer(
        &self,
        session: &ProofAssignedRaidSession,
        viewer: &DreggIdentity,
    ) -> Vec<Action> {
        if session.assignment().is_none() {
            return if viewer.as_str() == session.roster[0] {
                Self::proof_stream_actions(session)
            } else {
                Vec::new()
            };
        }
        let Some(assigned) = session.assigned_role_for(viewer.as_str()) else {
            return Vec::new();
        };
        if session.party.seat_count() == 0 && viewer.as_str() != session.roster[0] {
            return Vec::new();
        }
        let mut actions = PartyOffering::new().actions_for(&session.party, viewer);
        actions.retain(|action| action.turn != TURN_CLAIM || action.arg == assigned.index() as i64);
        for action in &mut actions {
            if action.turn == TURN_CLAIM {
                action.label = format!("Claim proof-assigned {}", assigned.name());
            } else if action.turn == crate::party::TURN_ACT {
                action.label = format!("Spend primed {} tactic", assigned.name());
            }
        }
        let holds_assignment = session.party.role_of(viewer.as_str()) == Some(assigned);
        let primed = session.tactic_primed_for(viewer.as_str());
        if !primed {
            actions.retain(|action| action.turn != crate::party::TURN_ACT);
            if holds_assignment {
                actions.push(Action::new(
                    format!("Burn proof-assigned {} sigil", assigned.name()),
                    TURN_PRIME_TACTIC,
                    assigned.index() as i64,
                    true,
                ));
            }
        }
        if let Some(allocation) = session.fhir_allocation.as_ref()
            && !allocation.landed()
            && allocation.selected_seat() == session.seat_of(viewer.as_str()).unwrap_or(usize::MAX)
            && session.party.role_of(viewer.as_str()) == Some(allocation.selected_role())
        {
            actions.push(Action::new(
                format!(
                    "Accept fhIR-selected {} allocation",
                    allocation.selected_role().name()
                ),
                TURN_ACCEPT_FHIR_ALLOCATION,
                allocation.selected_role().index() as i64,
                true,
            ));
        }
        actions
    }

    fn shared_party_actions(session: &ProofAssignedRaidSession) -> Vec<Action> {
        let mut actions = PartyOffering::new().actions(&session.party);
        let mut any_primed = false;
        for identity in &session.roster {
            let Some(role) = session.assigned_role_for(identity) else {
                continue;
            };
            if session.tactic_primed_for(identity) {
                any_primed = true;
            } else if session.party.role_of(identity) == Some(role) {
                actions.push(Action::new(
                    format!("Burn proof-assigned {} sigil", role.name()),
                    TURN_PRIME_TACTIC,
                    role.index() as i64,
                    true,
                ));
            }
        }
        if !any_primed {
            actions.retain(|action| action.turn != crate::party::TURN_ACT);
        }
        if let Some(allocation) = session.fhir_allocation.as_ref()
            && !allocation.landed()
        {
            let actor = &session.roster[allocation.selected_seat()];
            if session.party.role_of(actor) == Some(allocation.selected_role()) {
                actions.push(Action::new(
                    format!(
                        "{} accepts fhIR-selected {} allocation",
                        display_name_of(actor),
                        allocation.selected_role().name()
                    ),
                    TURN_ACCEPT_FHIR_ALLOCATION,
                    allocation.selected_role().index() as i64,
                    true,
                ));
            }
        }
        actions
    }

    fn proof_section(&self, session: &ProofAssignedRaidSession) -> ViewNode {
        let Some(assignment) = session.assignment() else {
            return section(
                "Shielded role assignment",
                "warn",
                vec![
                    pill("AWAITING HIDING PROOF", "warn"),
                    text(format!(
                        "expected proof session {} · {} receipt bytes assembled · no party claim may land before verification",
                        session.expected_proof_session,
                        session.proof_upload.bytes.len(),
                    )),
                    text(format!(
                        "Web uses the owning byte uploader (up to {MAX_ASSIGNMENT_BYTES} bytes). Discord and Telegram may stream lowercase-hex chunks of at most {MAX_STREAM_CHUNK_BYTES} bytes through the ordinary replayed text-action seam, bounded to {MAX_STREAM_ASSIGNMENT_BYTES} bytes / {MAX_STREAM_CHUNKS} chunks, then seal them into the same verifier."
                    )),
                    text(ASSIGN_DISCLOSURE),
                ],
            );
        };
        let mut rows = vec![row(vec![
            text("Seat"),
            text("Authenticated identity"),
            // NOT "private optimizer result". The optimizer's INPUTS are private; its
            // OUTPUT is `roles[4]`, a public input of the statement every viewer can
            // re-verify. Naming this column "private" claimed a secrecy this offering
            // does not have and cost a reviewer a leak investigation.
            text("Proof-assigned role (public)"),
            text("Real party capability"),
            text("Claim"),
            text("Tactical sigil"),
        ])];
        for seat in 0..4 {
            let raid_role = assignment
                .role_for_seat(seat)
                .expect("verified assignment has four seats");
            let capability = capability_role(raid_role);
            let identity = &session.roster[seat];
            rows.push(row(vec![
                text(seat.to_string()),
                text(display_name_of(identity)),
                pill(raid_role_name(raid_role), "genuine"),
                pill(capability.name(), "accent"),
                text(if session.party.role_of(identity) == Some(capability) {
                    "committed"
                } else {
                    "pending"
                }),
                pill(
                    if session.tactic_primed_for(identity) {
                        "burned / tactic armed"
                    } else {
                        "unspent"
                    },
                    if session.tactic_primed_for(identity) {
                        "good"
                    } else {
                        "warn"
                    },
                ),
            ]));
        }
        let receipt = session
            .assignment_receipt_id
            .map(|id| hex_prefix(&id))
            .unwrap_or_else(|| "missing".to_string());
        section(
            "Shielded role assignment",
            "genuine",
            vec![
                pill("HIDING PROOF VERIFIED", "good"),
                text(format!(
                    "proof session {} · receipt {} · public input root {}",
                    assignment.session(),
                    receipt,
                    hex_felts(assignment.input_root()),
                )),
                ViewNode::Table(rows),
                text(
                    "Each public result mints one receipt-context-bound sigil cell. The assigned seat holds its only capability; burning it is a WriteOnce + FieldDelta(+1) executor turn and gates that seat's Arena contribution. Roster/role interpretation remains a replay-checked host binding, not an ObservedFieldEquals transition from the proof receipt.",
                ),
                // The honest boundary, said on the surface rather than only in a doc
                // comment: this table is not a fogged hand, it is the STATEMENT, and it
                // is the same table for a seat, a teammate, a spectator and a stranger.
                text(
                    "WHAT IS SECRET AND WHAT IS NOT: this table is the proof's PUBLIC STATEMENT, so every viewer (seated, teammate, spectator, or anonymous) reads the same four roles, and must, because anyone can recompute them from the receipt against the pinned verifier key. The private half never reaches this host at all: the 4x4 suitability scores, the admissibility matrix, the blinding, and the aggregate score stay with the Tier-1 producer, and the input root above is a commitment to them, not a window into them. This offering therefore declares no hidden information, and a shared chat may paint it in full.",
                ),
            ],
        )
    }

    fn fhir_allocation_section(&self, session: &ProofAssignedRaidSession) -> Option<ViewNode> {
        session.fhir_allocation_policy.as_ref()?;
        let Some(allocation) = session.fhir_allocation.as_ref() else {
            return Some(section(
                "Exact-QP party allocation",
                "warn",
                vec![
                    pill("AWAITING ROLE PROOF", "warn"),
                    text(
                        "The fhIR optimizer claim is verified and roster/objective-bound; its selected member's real role is fixed only when the private role proof lands.",
                    ),
                ],
            ));
        };
        let actor = &session.roster[allocation.selected_seat()];
        Some(section(
            "Exact-QP party allocation",
            if allocation.landed() {
                "genuine"
            } else {
                "accent"
            },
            vec![
                pill("FHQPB001 EXACT OPTIMUM VERIFIED", "good"),
                text(format!(
                    "selected {} in the real {} role · {}",
                    display_name_of(actor),
                    allocation.selected_role().name(),
                    if allocation.landed() {
                        "executor allocation landed"
                    } else {
                        "awaiting selected actor/role acceptance"
                    }
                )),
                text(
                    "Replay reruns full QP binding, exact-zero KKT, one-hot, ordered-roster, and exact-objective checks; the selected actor holds only the selected role cell's capability.",
                ),
            ],
        ))
    }

    fn render_inner(
        &self,
        session: &ProofAssignedRaidSession,
        viewer: Option<&DreggIdentity>,
    ) -> Surface {
        let mut children = vec![self.proof_section(session)];
        if let Some(allocation) = self.fhir_allocation_section(session) {
            children.push(allocation);
        }
        if session.assignment().is_some() {
            let inner = match viewer {
                Some(viewer) => PartyOffering::new().render_for(&session.party, viewer),
                None => PartyOffering::new().render(&session.party),
            };
            // PartyOffering cannot know the proof-sigil prerequisite, so its own
            // action menu would expose an unprimed TURN_ACT and omit the burn.
            // Keep its state projection, then paint this wrapper's exact action set.
            children.push(without_direct_actions(inner.0));
        }
        let actions = match (session.assignment(), viewer) {
            // The pre-assignment affordance wants an OPAQUE PROOF CHUNK, not prose.
            // `MenuItem` now preserves `Action::wants_text` (a text field on the web,
            // free-text routing in chat), but a text box cannot carry a proof: web
            // paints the owning binary-operation uploader and chat adapters paint
            // `AudienceProjection.actions` beside the tree. Still no dead web button here.
            (None, _) => Vec::new(),
            (Some(_), Some(viewer)) => self.actions_for_viewer(session, viewer),
            (Some(_), None) => self.actions(session),
        };
        if !actions.is_empty() {
            children.push(crate::menu(action_menu(actions)));
        }
        Surface(section(
            "The Ash Gate Raid · prove, muster, choose, fight",
            "accent",
            children,
        ))
    }

    fn verify_assignment(&self, session: &ProofAssignedRaidSession) -> Result<(), String> {
        if session.seed % BABYBEAR_P_MINUS_ONE + 1 != u64::from(session.expected_proof_session) {
            return Err("hosted seed and expected proof session diverge".to_string());
        }
        if session.roster != self.roster {
            return Err("session roster differs from the offering's public seat order".to_string());
        }
        match (
            self.fhir_allocation_policy.as_ref(),
            session.fhir_allocation_policy.as_ref(),
        ) {
            (None, None) => {}
            (Some(expected), Some(actual)) if expected.same_deployment(actual) => {
                actual.verify_for_roster(&session.roster)?;
            }
            (Some(_), Some(_)) => {
                return Err(
                    "session fhIR allocation differs from the offering deployment".to_string(),
                );
            }
            _ => {
                return Err(
                    "session and offering disagree about the fhIR allocation policy".to_string(),
                );
            }
        }
        session.proof_upload.verify(&session.roster[0])?;
        let accepted = session.assignment();
        match (
            accepted,
            session.assignment_actor.as_ref(),
            session.canonical_receipt.as_ref(),
            session.assignment_receipt_id,
            session.tactics.as_ref(),
        ) {
            (None, None, None, None, None) => {
                if session.party.turns() != 0 || session.party.seat_count() != 0 {
                    return Err("party progressed before a private assignment landed".to_string());
                }
                if session.proof_upload.is_sealed() {
                    return Err("proof upload sealed without installing its assignment".to_string());
                }
                if session.fhir_allocation.is_some() {
                    return Err(
                        "fhIR member/role gate exists before the private role proof".to_string()
                    );
                }
            }
            (Some(expected), Some(actor), Some(canonical), Some(receipt_id), Some(tactics)) => {
                if actor.as_str() != session.roster[0] {
                    return Err("private assignment was not submitted by public seat 0".to_string());
                }
                let (receipt, reencoded) =
                    Self::decode_receipt(session, canonical).map_err(|error| error.to_string())?;
                if &reencoded != canonical {
                    return Err("stored private assignment is not canonical".to_string());
                }
                let mut replay = RaidAssignmentSession::new(session.expected_proof_session)
                    .map_err(|error| error.to_string())?;
                let reproduced = replay.accept(&receipt).map_err(|error| error.to_string())?;
                if reproduced != expected {
                    return Err("private assignment changed under proof replay".to_string());
                }
                let reproduced_id =
                    Self::receipt_id(session.seed, &session.roster, actor, canonical);
                if receipt_id != reproduced_id {
                    return Err("private assignment roster/context binding changed".to_string());
                }
                if session.proof_upload.is_sealed() {
                    if session.proof_upload.bytes.as_slice() != canonical.as_slice() {
                        return Err(
                            "streamed proof bytes differ from the installed canonical receipt"
                                .to_string(),
                        );
                    }
                } else if !session.proof_upload.is_pristine() {
                    return Err(
                        "binary proof operation landed beside an unfinished chat upload"
                            .to_string(),
                    );
                }

                let mut claimed = 0usize;
                for (seat, identity) in session.roster.iter().enumerate() {
                    let expected_role = capability_role(
                        expected
                            .role_for_seat(seat)
                            .ok_or_else(|| "assignment omitted a public seat".to_string())?,
                    );
                    if let Some(actual) = session.party.role_of(identity) {
                        claimed += 1;
                        if actual != expected_role {
                            return Err(format!(
                                "{} holds {}, but its proof seat was assigned {}",
                                identity,
                                actual.name(),
                                expected_role.name()
                            ));
                        }
                    }
                }
                if claimed != session.party.seat_count() {
                    return Err(
                        "party contains an identity outside the proof-bound roster".to_string()
                    );
                }
                for step in &tactics.history {
                    if session.party.role_of(&step.actor) != Some(step.role) {
                        return Err(format!(
                            "{} burned a {} sigil without holding that proof-assigned party capability",
                            step.actor,
                            step.role.name()
                        ));
                    }
                }
                tactics.verify(&session.roster, expected, receipt_id)?;
                match (
                    session.fhir_allocation_policy.as_ref(),
                    session.fhir_allocation.as_ref(),
                ) {
                    (None, None) => {}
                    (Some(policy), Some(allocation)) => {
                        for step in &allocation.history {
                            if session.party.role_of(&step.actor) != Some(step.role) {
                                return Err(format!(
                                    "{} accepted fhIR allocation as {}, but holds no such real party role",
                                    step.actor,
                                    step.role.name()
                                ));
                            }
                        }
                        allocation.verify(policy, &session.roster, expected, receipt_id)?;
                    }
                    _ => {
                        return Err(
                            "fhIR allocation policy and executor gate lifecycle disagree"
                                .to_string(),
                        );
                    }
                }
            }
            _ => return Err("private assignment lifecycle fields disagree".to_string()),
        }
        Ok(())
    }
}

impl Offering for ProofAssignedRaidOffering {
    type Session = ProofAssignedRaidSession;

    fn open(&self, cfg: SessionConfig) -> Result<Self::Session, OfferingError> {
        let seed = cfg.seed.unwrap_or(1);
        let expected_proof_session = proof_session_for_seed(seed);
        Ok(ProofAssignedRaidSession {
            seed,
            expected_proof_session,
            roster: self.roster.clone(),
            assignment_gate: RaidAssignmentSession::new(expected_proof_session)
                .map_err(|error| OfferingError::Deploy(error.to_string()))?,
            assignment_actor: None,
            canonical_receipt: None,
            assignment_receipt_id: None,
            proof_upload: ProofUpload::new(),
            tactics: None,
            fhir_allocation_policy: self.fhir_allocation_policy.clone(),
            fhir_allocation: None,
            party: PartyOffering::new().open(cfg)?,
        })
    }

    fn actions(&self, session: &Self::Session) -> Vec<Action> {
        if session.assignment().is_none() {
            Self::proof_stream_actions(session)
        } else {
            Self::shared_party_actions(session)
        }
    }

    fn actions_for(&self, session: &Self::Session, viewer: &DreggIdentity) -> Vec<Action> {
        self.actions_for_viewer(session, viewer)
    }

    fn advance(&self, session: &mut Self::Session, input: Action, actor: DreggIdentity) -> Outcome {
        if input.turn == TURN_STREAM_ASSIGNMENT {
            if session.assignment().is_some() {
                return Outcome::Refused("the hiding assignment is already filled".to_string());
            }
            if actor.as_str() != session.roster[0] {
                // ⚑ THE SEAT-0 KEY IS NOT PRINTED. This only fires when the presser is NOT seat 0,
                // so naming seat 0's 64-char hex told the reader nothing they could use — and the
                // real cause is nearly always that they are signed in as a different account than
                // the one that opened the raid. Same shared sentence as every other wrong-player
                // refusal in the product.
                return Outcome::Refused(belongs_to_another_player("raid's proof upload"));
            }
            let Some(encoded) = input.text.as_deref() else {
                return Outcome::Refused(
                    "a streamed private proof chunk requires lowercase-hex text".to_string(),
                );
            };
            return match session.proof_upload.append(&actor, input.arg, encoded) {
                Ok(receipt) => Outcome::Landed {
                    receipt,
                    ended: false,
                },
                Err(reason) => Outcome::Refused(reason),
            };
        }
        if input.turn == TURN_FINALIZE_ASSIGNMENT {
            if session.assignment().is_some() {
                return Outcome::Refused("the hiding assignment is already filled".to_string());
            }
            if actor.as_str() != session.roster[0] {
                // The sibling of the stream gate above — one condition, one sentence.
                return Outcome::Refused(belongs_to_another_player("raid's proof upload"));
            }
            if input.text.is_some() || input.arg != session.proof_upload.next_chunk() {
                return Outcome::Refused(
                    "private proof finalizer does not match the current chunk journal".to_string(),
                );
            }
            let prepared =
                match self.prepare_assignment(session, &session.proof_upload.bytes, actor) {
                    Ok(prepared) => prepared,
                    Err(error) => return Outcome::Refused(error.to_string()),
                };
            // The expensive verifier and all proof-derived cells are prepared first.
            // Once the audit seal commits, installing those infallible owned values is
            // the only remaining step, so a refusal cannot strand a sealed half-state.
            let receipt = match session.proof_upload.seal() {
                Ok(receipt) => receipt,
                Err(reason) => return Outcome::Refused(reason),
            };
            Self::install_assignment(session, prepared);
            return Outcome::Landed {
                receipt,
                ended: false,
            };
        }
        if session.assignment().is_none() {
            return Outcome::Refused(
                "the hiding assignment must verify before the party can progress".to_string(),
            );
        }
        let Some(seat) = session.seat_of(actor.as_str()) else {
            // ⚑ THE PRESSER'S OWN KEY IS NOT PRINTED EITHER. Echoing the 64-char hex of the identity
            // that is not on the roster reads as an accusation and carries no next step; the shared
            // sentence names the likely cause (a second device, a second account) and the one thing
            // they can do about it.
            return Outcome::Refused(belongs_to_another_player("raid"));
        };
        if input.turn == TURN_CLAIM
            && let Err(reason) = self.assigned_claim(session, &input, &actor)
        {
            return Outcome::Refused(reason);
        }
        if input.turn == TURN_ACCEPT_FHIR_ALLOCATION {
            if input.text.is_some() {
                return Outcome::Refused(
                    "an fhIR raid allocation acceptance has no free-text payload".to_string(),
                );
            }
            let Some(requested_role) = role_from_arg(input.arg) else {
                return Outcome::Refused("no such fhIR-selected party role".to_string());
            };
            if session.party.role_of(actor.as_str()).is_none() {
                return Outcome::Refused(
                    "claim a proof-assigned real party role before accepting its fhIR allocation"
                        .to_string(),
                );
            }
            let Some(allocation) = session.fhir_allocation.as_mut() else {
                return Outcome::Refused(
                    "this raid deployment carries no verified fhIR allocation".to_string(),
                );
            };
            return match allocation.accept(seat, &actor, requested_role) {
                Ok(receipt) => Outcome::Landed {
                    receipt,
                    ended: false,
                },
                Err(reason) => Outcome::Refused(reason),
            };
        }
        if input.turn == TURN_PRIME_TACTIC {
            if input.text.is_some() {
                return Outcome::Refused(
                    "a tactical sigil burn has no free-text payload".to_string(),
                );
            }
            let Some(requested) = role_from_arg(input.arg) else {
                return Outcome::Refused("no such proof-assigned tactical sigil".to_string());
            };
            let Some(expected) = session.assigned_role_for(actor.as_str()) else {
                return Outcome::Refused("actor has no verified raid assignment".to_string());
            };
            if session.party.role_of(actor.as_str()) != Some(expected) {
                return Outcome::Refused(
                    "claim the exact proof-assigned party capability before burning its sigil"
                        .to_string(),
                );
            }
            let Some(tactics) = session.tactics.as_mut() else {
                return Outcome::Refused("the verified assignment minted no tactics".to_string());
            };
            return match tactics.prime(seat, &actor, requested) {
                Ok(receipt) => Outcome::Landed {
                    receipt,
                    ended: false,
                },
                Err(reason) => Outcome::Refused(reason),
            };
        }
        if input.turn == crate::party::TURN_ACT && !session.tactic_primed_for(actor.as_str()) {
            return Outcome::Refused(
                "burn this seat's proof-assigned tactical sigil before contributing".to_string(),
            );
        }
        PartyOffering::new().advance(&mut session.party, input, actor)
    }

    fn advance_collective(
        &self,
        session: &mut Self::Session,
        input: Action,
        decision: CollectiveDecision,
    ) -> Outcome {
        if matches!(
            input.turn.as_str(),
            TURN_CLAIM
                | TURN_PRIME_TACTIC
                | TURN_ACCEPT_FHIR_ALLOCATION
                | TURN_STREAM_ASSIGNMENT
                | TURN_FINALIZE_ASSIGNMENT
        ) {
            return Outcome::Refused(
                "proof-assigned capability and sigil actions must come from their own identity"
                    .to_string(),
            );
        }
        if session.assignment().is_none() || session.seat_of(decision.carrier.as_str()).is_none() {
            return Outcome::Refused(
                "collective carrier is not in an assigned live raid".to_string(),
            );
        }
        if input.turn == crate::party::TURN_ACT
            && !session.tactic_primed_for(decision.carrier.as_str())
        {
            return Outcome::Refused(
                "collective carrier has not burned its proof-assigned tactical sigil".to_string(),
            );
        }
        PartyOffering::new().advance_collective(&mut session.party, input, decision)
    }

    fn verify(&self, session: &Self::Session) -> VerifyReport {
        if let Err(error) = self.verify_assignment(session) {
            return VerifyReport::broken(session.turns(), error);
        }
        let party = PartyOffering::new().verify(&session.party);
        if !party.verified {
            return VerifyReport::broken(
                session.turns(),
                format!("capability/tactical replay failed: {}", party.detail),
            );
        }
        VerifyReport::ok(session.turns())
    }

    fn render(&self, session: &Self::Session) -> Surface {
        self.render_inner(session, None)
    }

    fn render_for(&self, session: &Self::Session, viewer: &DreggIdentity) -> Surface {
        self.render_inner(session, Some(viewer))
    }

    /// **Declared `false`, not inherited** — see the module's "Who sees what, and when".
    /// The verified `roles[4]` permutation is a PUBLIC INPUT of the HidingFri statement, so
    /// the state tree is the same for every viewer by design; the only per-viewer
    /// projection is which affordance is offered, and no label carries private material.
    /// The private half (scores, admissibility, blinding, aggregate) never reaches this
    /// host. A shared chat may therefore paint this surface in full.
    fn hidden_information(&self) -> bool {
        false
    }

    fn binary_operations(&self, session: &Self::Session) -> Vec<BinaryOperationDescriptor> {
        if session.assignment().is_some() || !session.proof_upload.is_pristine() {
            return Vec::new();
        }
        vec![BinaryOperationDescriptor {
            name: ASSIGN_OPERATION.to_string(),
            title: "Verify shielded raid-role assignment".to_string(),
            input_media_type: ASSIGN_MEDIA_TYPE.to_string(),
            max_input_bytes: MAX_ASSIGNMENT_BYTES,
            disclosure: ASSIGN_DISCLOSURE.to_string(),
        }]
    }

    fn binary_operation_replay_material(
        &self,
        session: &Self::Session,
        name: &str,
        payload: &[u8],
    ) -> Result<Option<BinaryOperationReplayMaterial>, BinaryOperationError> {
        if name != ASSIGN_OPERATION {
            return Err(BinaryOperationError::UnknownOperation(name.to_string()));
        }
        let (_, canonical) = Self::decode_receipt(session, payload)?;
        Ok(Some(BinaryOperationReplayMaterial::new(
            canonical,
            "Retains the public raid statement, canonical verifier identity, public assigned roles, and opaque HidingFri proof; no suitability scores, admissibility matrix, blindings, or witness.",
        )))
    }

    fn invoke_binary_operation(
        &self,
        session: &mut Self::Session,
        name: &str,
        payload: &[u8],
        actor: DreggIdentity,
    ) -> Result<BinaryOperationReceipt, BinaryOperationError> {
        if name != ASSIGN_OPERATION {
            return Err(BinaryOperationError::UnknownOperation(name.to_string()));
        }
        if !session.proof_upload.is_pristine() {
            return Err(BinaryOperationError::Refused(format!(
                "discarding or replacing {} streamed proof bytes is not allowed",
                session.proof_upload.bytes.len()
            )));
        }
        // Stage the proof slot and every proof-derived capability cell off to the
        // side. A deployment refusal must not leave an accepted proof without the
        // corresponding spendable tactical authority.
        let prepared = self.prepare_assignment(session, payload, actor)?;
        let assignment = prepared.assignment;
        let receipt_id = prepared.receipt_id;
        Self::install_assignment(session, prepared);
        Ok(BinaryOperationReceipt {
            operation: ASSIGN_OPERATION.to_string(),
            receipt_id,
            public_fields: vec![
                ("proofSession".to_string(), assignment.session().to_string()),
                ("inputRoot".to_string(), hex_felts(assignment.input_root())),
                (
                    "roles".to_string(),
                    assignment
                        .roles()
                        .into_iter()
                        .map(raid_role_name)
                        .collect::<Vec<_>>()
                        .join(","),
                ),
            ],
        })
    }

    fn price(&self, input: &Action) -> RunCost {
        PartyOffering::new().price(input)
    }
}

/// Catalog-ready private raid: the first four distinct authenticated actors form the
/// exact public proof roster, then the existing fixed-roster offering takes over.
///
/// The lobby is deliberately small and deterministic. Each accepted join emits a
/// context-bound receipt hash and is retained by the generic host move journal. On
/// replay, the same actors in the same order reconstruct the same fixed-roster raid
/// before the proof operation is re-applied. No nickname, frontend-local seat map, or
/// ambient channel membership enters the proof interpretation.
#[derive(Clone, Copy, Debug, Default)]
pub struct HostedProofAssignedRaidOffering;

pub struct HostedProofAssignedRaidSession {
    seed: u64,
    roster: Vec<String>,
    lobby_receipts: Vec<[u8; 32]>,
    lobby_world: World,
    lobby_agent: dregg_app_framework::CellId,
    lobby_cell: dregg_app_framework::CellId,
    raid: Option<ProofAssignedRaidSession>,
}

impl HostedProofAssignedRaidSession {
    /// Exact public proof-seat roster in landed join order.
    pub fn roster(&self) -> &[String] {
        &self.roster
    }

    /// Verified public assignment, once the binary proof operation has landed.
    pub fn assignment(&self) -> Option<RaidPartyAssignment> {
        self.raid.as_ref()?.assignment()
    }

    /// Real party capability held by `actor`, once claimed.
    pub fn role_of(&self, actor: &str) -> Option<Role> {
        self.raid.as_ref()?.role_of(actor)
    }

    /// Number of opaque receipt bytes assembled through chat-native text turns.
    pub fn streamed_assignment_bytes(&self) -> usize {
        self.raid
            .as_ref()
            .map(ProofAssignedRaidSession::streamed_assignment_bytes)
            .unwrap_or(0)
    }

    pub fn streamed_assignment_chunks(&self) -> usize {
        self.raid
            .as_ref()
            .map(ProofAssignedRaidSession::streamed_assignment_chunks)
            .unwrap_or(0)
    }

    /// Whether `actor` has consumed the proof-selected one-shot tactical sigil.
    pub fn tactic_primed_for(&self, actor: &str) -> bool {
        self.raid
            .as_ref()
            .is_some_and(|raid| raid.tactic_primed_for(actor))
    }

    pub fn launched(&self) -> bool {
        self.raid
            .as_ref()
            .is_some_and(ProofAssignedRaidSession::launched)
    }

    pub fn target(&self) -> Option<u8> {
        self.raid.as_ref()?.target()
    }
}

impl HostedProofAssignedRaidOffering {
    pub fn new() -> Self {
        Self
    }

    fn join_action() -> Action {
        Action::new("Join the next public proof seat", TURN_JOIN_RAID, 0, true)
    }

    fn join_receipt(seed: u64, roster: &[String]) -> [u8; 32] {
        let mut hash = blake3::Hasher::new_derive_key("dregg-private-raid-public-lobby-v1");
        hash.update(&seed.to_le_bytes());
        hash.update(&(roster.len() as u64).to_le_bytes());
        for identity in roster {
            hash.update(&(identity.len() as u64).to_le_bytes());
            hash.update(identity.as_bytes());
        }
        *hash.finalize().as_bytes()
    }

    fn commit_lobby_join(
        session: &mut HostedProofAssignedRaidSession,
        next_roster: &[String],
    ) -> Result<dregg_app_framework::TurnReceipt, String> {
        let root = Self::join_receipt(session.seed, next_roster);
        let mut effects = vec![set_field(
            session.lobby_cell,
            HOSTED_LOBBY_REVISION_SLOT,
            field_from_u64(next_roster.len() as u64),
        )];
        for (index, chunk) in root.chunks_exact(8).enumerate() {
            effects.push(set_field(
                session.lobby_cell,
                HOSTED_LOBBY_ROOT_BASE + index,
                field_from_u64(u64::from_le_bytes(
                    chunk.try_into().expect("eight-byte roster-root limb"),
                )),
            ));
        }
        let turn = session.lobby_world.turn(session.lobby_agent, effects);
        match session.lobby_world.commit_turn(turn) {
            CommitOutcome::Committed { receipt, .. } => Ok(*receipt),
            CommitOutcome::Rejected { reason, .. } => {
                Err(format!("private-raid lobby audit cell refused: {reason}"))
            }
            CommitOutcome::Queued { .. } => {
                Err("private-raid lobby audit world is suspended".to_string())
            }
        }
    }

    fn audit_matches(session: &HostedProofAssignedRaidSession) -> bool {
        let Some(cell) = session.lobby_world.ledger().get(&session.lobby_cell) else {
            return false;
        };
        if field_to_u64(&cell.state.fields[HOSTED_LOBBY_REVISION_SLOT])
            != session.roster.len() as u64
        {
            return false;
        }
        let root = if session.roster.is_empty() {
            [0u8; 32]
        } else {
            Self::join_receipt(session.seed, &session.roster)
        };
        for (index, chunk) in root.chunks_exact(8).enumerate() {
            let expected =
                u64::from_le_bytes(chunk.try_into().expect("eight-byte roster-root limb"));
            if field_to_u64(&cell.state.fields[HOSTED_LOBBY_ROOT_BASE + index]) != expected {
                return false;
            }
        }
        true
    }

    fn lobby_surface(
        session: &HostedProofAssignedRaidSession,
        viewer: Option<&DreggIdentity>,
    ) -> Surface {
        let mut seats = vec![row(vec![
            text("Proof seat"),
            text("Authenticated identity"),
        ])];
        for seat in 0..4 {
            seats.push(row(vec![
                text(seat.to_string()),
                match session.roster.get(seat) {
                    Some(identity) => pill(display_name_of(identity), "genuine"),
                    None => pill("open", "warn"),
                },
            ]));
        }
        let mut children = vec![
            pill(
                format!("{} / 4 PUBLIC SEATS", session.roster.len()),
                if session.roster.len() == 4 {
                    "good"
                } else {
                    "warn"
                },
            ),
            text(
                "The first four distinct authenticated actors become proof seats 0–3. This exact order is replayed and context-bound to the later hiding receipt.",
            ),
            ViewNode::Table(seats),
        ];
        if session.roster.len() < 4
            && viewer
                .map(|who| !session.roster.iter().any(|seat| seat == who.as_str()))
                .unwrap_or(true)
        {
            children.push(crate::menu(action_menu(vec![Self::join_action()])));
        }
        Surface(section(
            "The Ash Gate Raid · muster the proof roster",
            "accent",
            children,
        ))
    }

    fn verify_lobby(session: &HostedProofAssignedRaidSession) -> Result<(), String> {
        if session.roster.len() > 4 || session.lobby_receipts.len() != session.roster.len() {
            return Err("private raid lobby lengths disagree".to_string());
        }
        let mut seen = BTreeSet::new();
        for (index, identity) in session.roster.iter().enumerate() {
            if identity.is_empty() || identity.len() > 256 || !seen.insert(identity.as_str()) {
                return Err(format!("invalid or duplicate public raid seat {index}"));
            }
        }
        if !Self::audit_matches(session) {
            return Err("public raid roster diverges from its committed audit cell".to_string());
        }
        let live_receipts = session.lobby_world.receipts();
        if live_receipts.len() != session.lobby_receipts.len() {
            return Err("public raid lobby receipt journal length changed".to_string());
        }
        for (index, receipt) in live_receipts.iter().enumerate() {
            if receipt.turn_hash != session.lobby_receipts[index] {
                return Err(format!(
                    "public raid seat {index} lost its retained executor receipt"
                ));
            }
            let expected_previous = index
                .checked_sub(1)
                .map(|previous| live_receipts[previous].receipt_hash());
            if receipt.previous_receipt_hash != expected_previous {
                return Err(format!(
                    "public raid seat {index} broke the retained receipt chain"
                ));
            }
            if receipt.timestamp != session.lobby_world.timestamp() {
                return Err(format!(
                    "public raid seat {index} changed its pinned audit timestamp"
                ));
            }
        }
        let offering = Self::new();
        let mut replay = offering
            .open(SessionConfig::with_seed(session.seed))
            .map_err(|error| error.to_string())?;
        for (index, identity) in session.roster.iter().enumerate() {
            let outcome = offering.advance(
                &mut replay,
                Action::new("replay raid join", TURN_JOIN_RAID, 0, true),
                DreggIdentity(identity.clone()),
            );
            let Outcome::Landed { receipt, .. } = outcome else {
                return Err(format!("public raid seat {index} refused on replay"));
            };
            // `World::new` pins its wall clock. That timestamp is correctly
            // folded into each receipt hash, and therefore into the next turn's
            // causal head: raw turn hashes after seat zero cannot be identical
            // when verification runs in a later second. The retained journal
            // above checks the exact original hashes and their receipt-hash
            // linkage. Replay compares every timestamp-independent transition
            // commitment, so it still proves the same real audit turns.
            let live = &live_receipts[index];
            if receipt.forest_hash != live.forest_hash
                || receipt.pre_state_hash != live.pre_state_hash
                || receipt.post_state_hash != live.post_state_hash
                || receipt.effects_hash != live.effects_hash
                || receipt.computrons_used != live.computrons_used
                || receipt.action_count != live.action_count
                || receipt.agent != live.agent
                || receipt.federation_id != live.federation_id
            {
                return Err(format!(
                    "public raid seat {index} audit transition changed on replay"
                ));
            }
        }
        match (&session.raid, session.roster.len()) {
            (None, 0..=3) => Ok(()),
            (Some(raid), 4) if raid.roster.as_slice() == session.roster.as_slice() => Ok(()),
            (Some(_), 4) => Err("live raid roster differs from the replayed lobby".to_string()),
            (None, 4) => Err("complete raid lobby did not instantiate its proof gate".to_string()),
            (None, 5..) => Err("raid lobby exceeded four public seats".to_string()),
            (Some(_), _) => Err("raid instantiated before four public seats landed".to_string()),
        }
    }
}

impl Offering for HostedProofAssignedRaidOffering {
    type Session = HostedProofAssignedRaidSession;

    fn open(&self, cfg: SessionConfig) -> Result<Self::Session, OfferingError> {
        let seed = cfg.seed.unwrap_or(1);
        let mut lobby_world = World::new();
        let lobby_cell = lobby_world.genesis_cell(0xE3, 0);
        if !lobby_world.set_cell_program(
            &lobby_cell,
            CellProgram::Predicate(vec![StateConstraint::FieldDelta {
                index: HOSTED_LOBBY_REVISION_SLOT as u8,
                delta: field_from_u64(1),
            }]),
        ) {
            return Err(OfferingError::Deploy(
                "could not install the private-raid lobby audit program".to_string(),
            ));
        }
        let (lobby_agent, _) = lobby_world.genesis_cell_with_cap(0xE4, 0, lobby_cell);
        Ok(HostedProofAssignedRaidSession {
            seed,
            roster: Vec::with_capacity(4),
            lobby_receipts: Vec::with_capacity(4),
            lobby_world,
            lobby_agent,
            lobby_cell,
            raid: None,
        })
    }

    fn actions(&self, session: &Self::Session) -> Vec<Action> {
        match &session.raid {
            Some(raid) => ProofAssignedRaidOffering::new(raid.roster.clone())
                .expect("a live raid has a validated roster")
                .actions(raid),
            None if session.roster.len() < 4 => vec![Self::join_action()],
            None => Vec::new(),
        }
    }

    fn actions_for(&self, session: &Self::Session, viewer: &DreggIdentity) -> Vec<Action> {
        match &session.raid {
            Some(raid) => ProofAssignedRaidOffering::new(raid.roster.clone())
                .expect("a live raid has a validated roster")
                .actions_for(raid, viewer),
            None if session.roster.len() < 4
                && !session.roster.iter().any(|seat| seat == viewer.as_str()) =>
            {
                vec![Self::join_action()]
            }
            None => Vec::new(),
        }
    }

    fn advance(&self, session: &mut Self::Session, input: Action, actor: DreggIdentity) -> Outcome {
        if let Some(raid) = &mut session.raid {
            let offering = ProofAssignedRaidOffering::new(raid.roster.clone())
                .expect("a live raid has a validated roster");
            return offering.advance(raid, input, actor);
        }
        if input.turn != TURN_JOIN_RAID || input.arg != 0 || input.text.is_some() {
            return Outcome::Refused(
                "four public actors must join before the hiding assignment can land".to_string(),
            );
        }
        if actor.as_str().is_empty() || actor.as_str().len() > 256 {
            return Outcome::Refused("raid identities must contain 1..=256 bytes".to_string());
        }
        if session.roster.iter().any(|seat| seat == actor.as_str()) {
            return Outcome::Refused(
                "this identity already occupies a public proof seat".to_string(),
            );
        }
        if session.roster.len() == 4 {
            return Outcome::Refused("all four public proof seats are occupied".to_string());
        }
        let mut next_roster = session.roster.clone();
        next_roster.push(actor.0);
        // Prepare the fixed proof/party organ before committing the fourth lobby
        // turn. A deploy refusal must leave both roster and audit cell untouched.
        let prepared_raid = if next_roster.len() == 4 {
            let roster: [String; 4] = next_roster
                .clone()
                .try_into()
                .expect("the fourth candidate yields four exact seats");
            let offering = ProofAssignedRaidOffering::new(roster)
                .expect("the lobby already rejected empty and duplicate identities");
            match offering.open(SessionConfig::with_seed(session.seed)) {
                Ok(raid) => Some(raid),
                Err(error) => {
                    return Outcome::Refused(format!(
                        "private raid proof/party organ refused before roster lock: {error}"
                    ));
                }
            }
        } else {
            None
        };
        let receipt = match Self::commit_lobby_join(session, &next_roster) {
            Ok(receipt) => receipt,
            Err(reason) => return Outcome::Refused(reason),
        };
        session.roster = next_roster;
        session.lobby_receipts.push(receipt.turn_hash);
        session.raid = prepared_raid;
        Outcome::Landed {
            receipt,
            ended: false,
        }
    }

    fn advance_collective(
        &self,
        session: &mut Self::Session,
        input: Action,
        decision: CollectiveDecision,
    ) -> Outcome {
        let Some(raid) = &mut session.raid else {
            return Outcome::Refused(
                "public proof seats are individual identity claims, not a collective ballot"
                    .to_string(),
            );
        };
        let offering = ProofAssignedRaidOffering::new(raid.roster.clone())
            .expect("a live raid has a validated roster");
        offering.advance_collective(raid, input, decision)
    }

    fn verify(&self, session: &Self::Session) -> VerifyReport {
        if let Err(error) = Self::verify_lobby(session) {
            return VerifyReport::broken(session.lobby_receipts.len(), error);
        }
        let Some(raid) = &session.raid else {
            return VerifyReport::ok(session.lobby_receipts.len());
        };
        let offering = ProofAssignedRaidOffering::new(raid.roster.clone())
            .expect("a live raid has a validated roster");
        let report = offering.verify(raid);
        if report.verified {
            VerifyReport::ok(session.lobby_receipts.len() + report.turns)
        } else {
            VerifyReport::broken(
                session.lobby_receipts.len() + report.turns,
                format!("proof-assigned raid failed: {}", report.detail),
            )
        }
    }

    fn render(&self, session: &Self::Session) -> Surface {
        match &session.raid {
            Some(raid) => ProofAssignedRaidOffering::new(raid.roster.clone())
                .expect("a live raid has a validated roster")
                .render(raid),
            None => Self::lobby_surface(session, None),
        }
    }

    fn render_for(&self, session: &Self::Session, viewer: &DreggIdentity) -> Surface {
        match &session.raid {
            Some(raid) => ProofAssignedRaidOffering::new(raid.roster.clone())
                .expect("a live raid has a validated roster")
                .render_for(raid, viewer),
            None => Self::lobby_surface(session, Some(viewer)),
        }
    }

    /// **Declared `false`, not inherited** — it must agree with the fixed-roster offering
    /// this delegates every live render to (see
    /// [`ProofAssignedRaidOffering::hidden_information`]). The lobby it renders before the
    /// raid forms is public too: a join is a public turn, and the seat order it establishes
    /// is exactly what the proof statement's `session` is derived from.
    fn hidden_information(&self) -> bool {
        false
    }

    fn binary_operations(&self, session: &Self::Session) -> Vec<BinaryOperationDescriptor> {
        match &session.raid {
            Some(raid) => ProofAssignedRaidOffering::new(raid.roster.clone())
                .expect("a live raid has a validated roster")
                .binary_operations(raid),
            None => Vec::new(),
        }
    }

    fn binary_operation_replay_material(
        &self,
        session: &Self::Session,
        name: &str,
        payload: &[u8],
    ) -> Result<Option<BinaryOperationReplayMaterial>, BinaryOperationError> {
        let Some(raid) = &session.raid else {
            return Err(BinaryOperationError::Refused(
                "four public proof seats must land before assignment upload".to_string(),
            ));
        };
        ProofAssignedRaidOffering::new(raid.roster.clone())
            .expect("a live raid has a validated roster")
            .binary_operation_replay_material(raid, name, payload)
    }

    fn invoke_binary_operation(
        &self,
        session: &mut Self::Session,
        name: &str,
        payload: &[u8],
        actor: DreggIdentity,
    ) -> Result<BinaryOperationReceipt, BinaryOperationError> {
        let Some(raid) = &mut session.raid else {
            return Err(BinaryOperationError::Refused(
                "four public proof seats must land before assignment upload".to_string(),
            ));
        };
        ProofAssignedRaidOffering::new(raid.roster.clone())
            .expect("a live raid has a validated roster")
            .invoke_binary_operation(raid, name, payload, actor)
    }

    fn price(&self, input: &Action) -> RunCost {
        if input.turn == TURN_JOIN_RAID {
            RunCost::free()
        } else {
            PartyOffering::new().price(input)
        }
    }
}

/// Deterministically project the fixed authenticated roster into the nonzero,
/// distinct `u64` identities consumed by fhIR's roster-allocation claim.
/// Full strings remain bound by the surrounding allocation context and replay.
pub fn fhir_raid_roster_ids(roster: &[String; 4]) -> Result<[u64; 4], String> {
    validate_roster(roster)?;
    let mut ids = [0u64; 4];
    let mut seen = BTreeSet::new();
    for (seat, identity) in roster.iter().enumerate() {
        let mut hash = blake3::Hasher::new_derive_key("dregg-fhir-raid-roster-identity-v1");
        hash.update(&(identity.len() as u64).to_le_bytes());
        hash.update(identity.as_bytes());
        let id = u64::from_le_bytes(
            hash.finalize().as_bytes()[..8]
                .try_into()
                .expect("BLAKE3 output contains an eight-byte identity limb"),
        );
        if id == 0 {
            return Err(format!(
                "raid identity at seat {seat} maps to the reserved zero fhIR identity"
            ));
        }
        if !seen.insert(id) {
            return Err(format!(
                "raid identities collide at seat {seat} in the fhIR u64 roster image"
            ));
        }
        ids[seat] = id;
    }
    Ok(ids)
}

fn fhir_roster_ids(roster: &[String; 4]) -> Result<[u64; 4], String> {
    fhir_raid_roster_ids(roster)
}

fn fhir_allocation_context(
    claim_commitment: [u8; 32],
    assignment_receipt_id: [u8; 32],
    roster: &[String; 4],
    selected_seat: usize,
    selected_role: Role,
) -> [u64; 4] {
    let mut hash = blake3::Hasher::new_derive_key("dregg-fhir-private-raid-allocation-v1");
    hash.update(&claim_commitment);
    hash.update(&assignment_receipt_id);
    for identity in roster {
        hash.update(&(identity.len() as u64).to_le_bytes());
        hash.update(identity.as_bytes());
    }
    hash.update(&(selected_seat as u64).to_le_bytes());
    hash.update(&(selected_role.index() as u64).to_le_bytes());
    receipt_limbs(*hash.finalize().as_bytes())
}

fn validate_roster(roster: &[String; 4]) -> Result<(), String> {
    let mut seen = BTreeSet::new();
    for identity in roster {
        if identity.is_empty() || identity.len() > 256 {
            return Err("raid identities must contain 1..=256 bytes".to_string());
        }
        if !seen.insert(identity.as_str()) {
            return Err(format!(
                "raid identity {identity:?} occupies two public seats"
            ));
        }
    }
    Ok(())
}

fn capability_role(role: RaidRole) -> Role {
    match role {
        RaidRole::Bulwark => Role::Tank,
        RaidRole::Striker => Role::Mage,
        RaidRole::Mender => Role::Healer,
        RaidRole::Pathfinder => Role::Scout,
    }
}

fn role_from_arg(arg: i64) -> Option<Role> {
    usize::try_from(arg)
        .ok()
        .and_then(|index| Role::ALL.get(index).copied())
}

fn receipt_limbs(receipt_id: [u8; 32]) -> [u64; 4] {
    std::array::from_fn(|index| {
        let start = index * 8;
        u64::from_le_bytes(
            receipt_id[start..start + 8]
                .try_into()
                .expect("one assignment-receipt limb"),
        )
    })
}

fn proof_stream_hasher() -> blake3::Hasher {
    blake3::Hasher::new_derive_key("dregg-private-raid-chat-proof-stream-v1")
}

/// The one naming of a public raid role lives on [`RaidRole`] itself, so this surface, the
/// dungeon's raid muster, and native Descent's campaign card cannot drift apart.
fn raid_role_name(role: RaidRole) -> &'static str {
    role.name()
}

fn encode_lower_hex(bytes: &[u8]) -> String {
    let mut out = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        use std::fmt::Write as _;
        write!(&mut out, "{byte:02x}").expect("writing to a String is infallible");
    }
    out
}

fn decode_lower_hex(encoded: &str) -> Result<Vec<u8>, String> {
    if encoded.len() % 2 != 0 {
        return Err("private proof chunk must contain an even number of hex digits".to_string());
    }
    let mut bytes = Vec::with_capacity(encoded.len() / 2);
    for pair in encoded.as_bytes().chunks_exact(2) {
        let digit = |byte: u8| match byte {
            b'0'..=b'9' => Some(byte - b'0'),
            b'a'..=b'f' => Some(byte - b'a' + 10),
            _ => None,
        };
        let Some(hi) = digit(pair[0]) else {
            return Err("private proof chunks use canonical lowercase hex only".to_string());
        };
        let Some(lo) = digit(pair[1]) else {
            return Err("private proof chunks use canonical lowercase hex only".to_string());
        };
        bytes.push((hi << 4) | lo);
    }
    Ok(bytes)
}

fn hex_prefix(bytes: &[u8; 32]) -> String {
    bytes[..4]
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect()
}

/// Render a felt-limb public digest as one canonical lowercase-hex string.
///
/// The AIR's public roots are `[u32; 8]` limbs, and a `Debug` dump of that array
/// (`[1234567, 89, …]`) reads as an internals spill rather than a commitment a
/// viewer can compare against another copy of the same statement. Every digest a
/// player is shown is this shape.
fn hex_felts(felts: [u32; 8]) -> String {
    felts
        .into_iter()
        .map(|felt| format!("{felt:08x}"))
        .collect()
}

fn without_direct_actions(view: ViewNode) -> ViewNode {
    match view {
        ViewNode::Section {
            title,
            tag,
            mut children,
        } => {
            children.retain(
                |child| !matches!(child, ViewNode::Section { title, .. } if title == "Actions"),
            );
            ViewNode::Section {
                title,
                tag,
                children,
            }
        }
        other => other,
    }
}
