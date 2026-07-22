#![cfg(feature = "private-raid-assignment")]

//! Executor-atomic proof-assigned raid cut prototype.
//!
//! This is deliberately an isolated integration test rather than production wiring.
//! It establishes the strongest claim the existing public APIs support without moving
//! ownership between the current `ProofAssignedRaidSession`, `Party`, and `Arena` types:
//!
//! - the real HidingFri assignment receipt is checked by a registered `Custom { vk_hash }`
//!   witnessed predicate inside the executor;
//! - that verified role is carried through a one-shot sigil cell into the same role/focus
//!   cell predicates used by `dreggnet-party`;
//! - a real `combat::Arena` cell, with its complete compiled program and exact
//!   dice-bound transition, shares its action with a Party-observing admission gate; and
//! - all four roots execute as one call forest, so stripping the final Arena observation
//!   rolls the proof, sigil, party, focus, admission-gate, and Arena mutations back together.
//!
//! Honest boundary: the Party role/focus cells below reproduce the public executor
//! semantics of `dreggnet-party` rather than importing its privately-owned `World`; doing
//! the literal type-level cut needs the production ownership/API changes recorded at the
//! bottom of this file. The Arena cell and private-assignment proof are the real organs.
//! The companion gate is necessary because the current executor discovers
//! `ObservedFieldEquals` only in `CellProgram::Predicate`, while Arena correctly uses
//! method-dispatched `CellProgram::Cases`; no claim is made beyond that executor seam.
//! In particular, later sibling roots observe earlier roots because this embedded executor
//! walks the forest sequentially over one journaled ledger image. That is executor-local
//! atomicity/current-state authority, not a claim of distributed consensus finality.
//! “Atomic” here names the forest effects: the executor intentionally keeps its phase-one
//! agent nonce/fee accounting when a forest rejects, so the RED case asserts that boundary.

use std::sync::{Arc, OnceLock};

use dregg_app_framework::{DreggEngine, EngineConfig, Event, field_from_u64, symbol};
use dregg_cell::predicate::{
    InputRef, PredicateInput, WitnessedPredicate, WitnessedPredicateError, WitnessedPredicateKind,
    WitnessedPredicateRegistry, WitnessedPredicateVerifier, canonical_predicate_vk,
};
use dregg_cell::{AuthRequired, Cell, CellId, CellProgram, StateConstraint};
use dregg_turn::action::{Effect, WitnessBlob};
use dregg_turn::{CallForest, ComputronCosts, Turn};
use dungeon_on_dregg::combat::{Arena, DICE_TOPIC, WARDEN, is_hero};
use dungeon_on_dregg::private_raid::{
    RaidAssignmentReceipt, RaidAssignmentSession, RaidRole, prove_private_assignment,
};
use starbridge_v2::world::{bare_action, bare_turn, make_open_cell, open_permissions, set_field};

const SEAT: usize = 0;
const PROOF_LANDED: usize = 0;
const PROOF_ROLE: usize = 1;
const SIGIL_SPENT: usize = 0;
const SIGIL_ROLE: usize = 1;
const PARTY_CONTRIBUTED: usize = 0;
const PARTY_ROLE: usize = 1;
const FOCUS_SPENT: usize = 0;
const FOCUS_BUDGET: usize = 1;
const ARENA_GATE_OPEN: usize = 0;
const ARENA_GATE_ROLE: usize = 1;
const PARTY_FOCUS_COST: u64 = 15;
const PARTY_FOCUS_BUDGET: u64 = 40;

fn field_to_u64(value: &[u8; 32]) -> u64 {
    u64::from_be_bytes(value[24..].try_into().expect("eight-byte u64 lane"))
}

fn capability_role_tag(role: RaidRole) -> u64 {
    // Same public mapping as dreggnet-surfaces::private_raid::capability_role,
    // encoded as dreggnet-party's canonical Role::index() + 1.
    match role {
        RaidRole::Bulwark => 1,    // Tank
        RaidRole::Pathfinder => 2, // Scout
        RaidRole::Striker => 3,    // Mage
        RaidRole::Mender => 4,     // Healer
    }
}

fn statement_commitment(receipt: &RaidAssignmentReceipt) -> [u8; 32] {
    let mut hash = blake3::Hasher::new_derive_key("dregg.private-raid.atomic-statement.v1");
    hash.update(&receipt.verifier_key());
    for public in receipt.statement().as_u32_vec() {
        hash.update(&public.to_le_bytes());
    }
    *hash.finalize().as_bytes()
}

fn role_predicate_vk(receipt: &RaidAssignmentReceipt, seat: usize) -> [u8; 32] {
    let mut recipe = b"private-raid-assignment/verified-party-role/v1".to_vec();
    recipe.extend_from_slice(&receipt.verifier_key());
    recipe.extend_from_slice(&receipt.statement().session.to_le_bytes());
    recipe.extend_from_slice(&(seat as u64).to_le_bytes());
    canonical_predicate_vk(&recipe)
}

#[derive(Clone)]
struct PrivateRaidRoleVerifier {
    vk_hash: [u8; 32],
    statement: [u8; 32],
    session: u32,
    seat: usize,
}

impl PrivateRaidRoleVerifier {
    fn reject(reason: impl Into<String>) -> WitnessedPredicateError {
        WitnessedPredicateError::Rejected {
            kind_name: "PrivateRaidAssignedRole",
            reason: reason.into(),
        }
    }
}

impl WitnessedPredicateVerifier for PrivateRaidRoleVerifier {
    fn name(&self) -> &'static str {
        "private-raid-assigned-role-v1"
    }

    fn kind(&self) -> WitnessedPredicateKind {
        WitnessedPredicateKind::Custom {
            vk_hash: self.vk_hash,
        }
    }

    fn verify(
        &self,
        commitment: &[u8; 32],
        input: &PredicateInput<'_>,
        proof_bytes: &[u8],
    ) -> Result<(), WitnessedPredicateError> {
        if commitment != &self.statement {
            return Err(Self::reject(
                "statement commitment differs from the installed recipe",
            ));
        }
        let PredicateInput::Slot(role_field) = input else {
            return Err(WitnessedPredicateError::InputShapeMismatch {
                kind_name: "PrivateRaidAssignedRole",
                expected: "Slot",
                actual: "non-Slot",
            });
        };
        let receipt = RaidAssignmentReceipt::from_postcard(proof_bytes)
            .map_err(|error| Self::reject(error.to_string()))?;
        if receipt
            .to_postcard()
            .map_err(|error| Self::reject(error.to_string()))?
            != proof_bytes
        {
            return Err(Self::reject(
                "assignment receipt is not canonically encoded",
            ));
        }
        if statement_commitment(&receipt) != self.statement {
            return Err(Self::reject("proof carries a different public statement"));
        }
        let mut gate = RaidAssignmentSession::new(self.session)
            .map_err(|error| Self::reject(error.to_string()))?;
        let assignment = gate
            .accept(&receipt)
            .map_err(|error| Self::reject(error.to_string()))?;
        let assigned = assignment
            .role_for_seat(self.seat)
            .ok_or_else(|| Self::reject("verified assignment omitted the requested seat"))?;
        let expected = capability_role_tag(assigned);
        if field_to_u64(role_field) != expected {
            return Err(Self::reject(format!(
                "proof assigned party-role tag {expected}, cell attempted {}",
                field_to_u64(role_field)
            )));
        }
        Ok(())
    }
}

fn scores() -> [[u8; 4]; 4] {
    [[3, 2, 0, 0], [3, 0, 1, 0], [0, 0, 3, 1], [0, 1, 0, 3]]
}

fn arena_seed() -> u8 {
    static SEED: OnceLock<u8> = OnceLock::new();
    *SEED.get_or_init(|| {
        (0..=u8::MAX)
            .find(|seed| {
                let arena = Arena::deploy(*seed);
                // Seat zero's fixed fixture assignment is Striker -> Mage -> tag 3.
                // Pick a genuine hero-first initiative whose next actor is combatant 3,
                // so the Arena's real `active` register can carry the observed role tag.
                is_hero(arena.active()) && arena.order.get(1) == Some(&3)
            })
            .expect("some deterministic Arena initiative begins hero -> combatant 3")
    })
}

fn proof_bytes() -> &'static [u8] {
    static PROOF: OnceLock<Vec<u8>> = OnceLock::new();
    PROOF.get_or_init(|| {
        prove_private_assignment(
            u32::from(arena_seed()) + 1,
            scores(),
            [
                [false, true, true, true],
                [true, true, true, true],
                [true, true, true, true],
                [true, true, true, true],
            ],
        )
        .expect("the existing HidingFri assignment proves")
        .to_postcard()
        .expect("the assignment receipt has a canonical wire image")
    })
}

fn observed(
    local_field: usize,
    source: CellId,
    source_field: usize,
    at_root: [u8; 32],
    proof_witness_index: usize,
) -> StateConstraint {
    StateConstraint::ObservedFieldEquals {
        local_field: local_field as u8,
        source_cell: *source.as_bytes(),
        source_field: source_field as u8,
        at_root,
        proof_witness_index,
    }
}

fn root_witness(root: [u8; 32]) -> WitnessBlob {
    // ObservedFieldEquals resolves the authoritative value from the executor's
    // finalized-root channel; the indexed MerklePath blob is the required opening
    // carrier and its absence is fail-closed.
    WitnessBlob::merkle_path(root.to_vec())
}

fn set_post(cell: &Cell, writes: &[(usize, [u8; 32])]) -> Cell {
    let mut post = cell.clone();
    for (index, value) in writes {
        assert!(post.state.set_field(*index, *value));
    }
    post
}

fn arena_effects(before: &Cell, after: &Cell, hit: &dungeon_on_dregg::combat::Hit) -> Vec<Effect> {
    let mut effects = Vec::new();
    for index in 0..before.state.fields.len() {
        if before.state.fields[index] != after.state.fields[index] {
            effects.push(set_field(after.id(), index, after.state.fields[index]));
        }
    }
    for (&key, &value) in &after.state.fields_map {
        if before.state.fields_map.get(&key) != Some(&value) {
            effects.push(set_field(after.id(), key as usize, value));
        }
    }
    effects.push(Effect::EmitEvent {
        cell: after.id(),
        event: Event::new(
            symbol(DICE_TOPIC),
            vec![
                *hit.draw.request.event_id().as_bytes(),
                hit.draw.evidence.draw_transcript_commitment,
                field_from_u64(hit.draw.roll),
                field_from_u64(hit.draw.damage),
                field_from_u64(hit.draw.guarded as u64),
            ],
        ),
    });
    effects
}

struct AtomicRaidHarness {
    engine: DreggEngine,
    turn: Turn,
    agent: CellId,
    proof: CellId,
    sigil: CellId,
    party: CellId,
    focus: CellId,
    arena: CellId,
    arena_gate: CellId,
    arena_active_slot: usize,
    arena_stunned_slot: usize,
    assigned_role_tag: u64,
}

impl AtomicRaidHarness {
    fn new() -> Self {
        let receipt = RaidAssignmentReceipt::from_postcard(proof_bytes())
            .expect("fixture receipt decodes canonically");
        // Staging reads only the canonical PUBLIC statement. It deliberately does
        // not call the HidingFri verifier; that acceptance happens inside the first
        // forest root through `PrivateRaidRoleVerifier`.
        let assigned_role_tag = capability_role_tag(
            RaidRole::try_from(receipt.statement().roles[SEAT])
                .expect("canonical statement carries a role permutation"),
        );
        assert_eq!(
            assigned_role_tag, 3,
            "fixture seat zero is the Mage capability"
        );

        let statement = statement_commitment(&receipt);
        let vk_hash = role_predicate_vk(&receipt, SEAT);

        let mut proof_cell = make_open_cell(0xF1, 0);
        proof_cell.program = CellProgram::Predicate(vec![
            StateConstraint::FieldDelta {
                index: PROOF_LANDED as u8,
                delta: field_from_u64(1),
            },
            StateConstraint::FieldEquals {
                index: PROOF_LANDED as u8,
                value: field_from_u64(1),
            },
            StateConstraint::WriteOnce {
                index: PROOF_LANDED as u8,
            },
            StateConstraint::WriteOnce {
                index: PROOF_ROLE as u8,
            },
            StateConstraint::Witnessed {
                wp: WitnessedPredicate {
                    kind: WitnessedPredicateKind::Custom { vk_hash },
                    commitment: statement,
                    input_ref: InputRef::Slot {
                        index: PROOF_ROLE as u8,
                    },
                    proof_witness_index: 0,
                },
            },
        ]);
        let proof_id = proof_cell.id();
        let proof_post = set_post(
            &proof_cell,
            &[
                (PROOF_LANDED, field_from_u64(1)),
                (PROOF_ROLE, field_from_u64(assigned_role_tag)),
            ],
        );
        let proof_post_root = proof_post.state_commitment();

        let mut sigil_cell = make_open_cell(0xF2, 0);
        sigil_cell.program = CellProgram::Predicate(vec![
            StateConstraint::FieldDelta {
                index: SIGIL_SPENT as u8,
                delta: field_from_u64(1),
            },
            StateConstraint::WriteOnce {
                index: SIGIL_SPENT as u8,
            },
            StateConstraint::WriteOnce {
                index: SIGIL_ROLE as u8,
            },
            observed(SIGIL_SPENT, proof_id, PROOF_LANDED, proof_post_root, 0),
            observed(SIGIL_ROLE, proof_id, PROOF_ROLE, proof_post_root, 1),
        ]);
        let sigil_id = sigil_cell.id();
        let sigil_post = set_post(
            &sigil_cell,
            &[
                (SIGIL_SPENT, field_from_u64(1)),
                (SIGIL_ROLE, field_from_u64(assigned_role_tag)),
            ],
        );
        let sigil_post_root = sigil_post.state_commitment();

        // This is the exact dreggnet-party Mage role-cell + focus-pool predicate
        // shape, extended with the two proof-sigil observations the cut needs.
        let mut party_cell = make_open_cell(0xF3, 0);
        party_cell.program = CellProgram::Predicate(vec![
            StateConstraint::WriteOnce {
                index: PARTY_CONTRIBUTED as u8,
            },
            StateConstraint::WriteOnce {
                index: PARTY_ROLE as u8,
            },
            observed(PARTY_CONTRIBUTED, sigil_id, SIGIL_SPENT, sigil_post_root, 0),
            observed(PARTY_ROLE, sigil_id, SIGIL_ROLE, sigil_post_root, 1),
        ]);
        let party_id = party_cell.id();
        let party_post = set_post(
            &party_cell,
            &[
                (PARTY_CONTRIBUTED, field_from_u64(1)),
                (PARTY_ROLE, field_from_u64(assigned_role_tag)),
            ],
        );
        let party_post_root = party_post.state_commitment();

        let mut focus_cell = make_open_cell(0xF4, 0);
        focus_cell.state.fields[FOCUS_BUDGET] = field_from_u64(PARTY_FOCUS_BUDGET);
        focus_cell.program = CellProgram::Predicate(vec![StateConstraint::FieldLteField {
            left_index: FOCUS_SPENT as u8,
            right_index: FOCUS_BUDGET as u8,
        }]);
        let focus_id = focus_cell.id();

        // Stage a real Arena heavy transition in its native executor, then reconstruct
        // its exact post-state deltas and dice event in the joined ledger. The original
        // full compiled Arena program below re-checks those effects at admission.
        let mut staged_arena = Arena::deploy(arena_seed());
        let attacker = staged_arena.active();
        assert!(is_hero(attacker));
        let mut arena_cell = staged_arena
            .world
            .cell_snapshot()
            .expect("deployed Arena exposes its real cell");
        let arena_before_native = arena_cell.clone();
        let hit = staged_arena
            .heavy(attacker, WARDEN)
            .expect("the staged real Arena heavy strike lands");
        let arena_after_native = staged_arena
            .world
            .cell_snapshot()
            .expect("landed Arena exposes its exact post cell");
        let arena_active_slot = staged_arena
            .story()
            .var_key("active")
            .expect("Arena layout names active") as usize;
        let arena_stunned_slot = staged_arena
            .story()
            .var_key(&format!("st{WARDEN}"))
            .expect("Arena layout names target stun") as usize;
        assert_eq!(
            field_to_u64(&arena_after_native.state.fields[arena_active_slot]),
            assigned_role_tag,
            "chosen initiative makes real Arena active carry the assigned role tag"
        );
        assert_eq!(
            field_to_u64(&arena_after_native.state.fields[arena_stunned_slot]),
            1,
            "a real heavy strike stuns the target"
        );

        let arena_id = arena_cell.id();

        // Keep Arena's complete method-dispatched `Cases` program byte-for-byte.
        // The current executor's finalized-root-authority builder only discovers
        // `ObservedFieldEquals` in `Predicate` programs, so a companion one-shot
        // admission cell carries the Party observation and is mutated by the SAME
        // action as the Arena. A missing observation therefore rejects after both
        // Arena and gate effects have entered the journal, and rolls them back with
        // the preceding proof/sigil/Party roots.
        let mut arena_gate_cell = make_open_cell(0xF5, 0);
        arena_gate_cell.program = CellProgram::Predicate(vec![
            StateConstraint::FieldEquals {
                index: ARENA_GATE_OPEN as u8,
                value: field_from_u64(1),
            },
            StateConstraint::WriteOnce {
                index: ARENA_GATE_OPEN as u8,
            },
            StateConstraint::WriteOnce {
                index: ARENA_GATE_ROLE as u8,
            },
            observed(
                ARENA_GATE_OPEN,
                party_id,
                PARTY_CONTRIBUTED,
                party_post_root,
                0,
            ),
            observed(ARENA_GATE_ROLE, party_id, PARTY_ROLE, party_post_root, 1),
        ]);
        let arena_gate_id = arena_gate_cell.id();

        // `WorldCell` normally signs this cell's action. The joined embedded fixture
        // uses the same single-custody `Unchecked` convention as starbridge `World`;
        // capability reach and all cell programs remain load-bearing.
        arena_cell.permissions = open_permissions();

        let mut agent_cell = make_open_cell(0xF0, 0);
        let agent = agent_cell.id();
        for target in [
            proof_id,
            sigil_id,
            party_id,
            focus_id,
            arena_id,
            arena_gate_id,
        ] {
            agent_cell
                .capabilities
                .grant(target, AuthRequired::None)
                .expect("prototype agent c-list has room");
        }

        let mut config = EngineConfig::for_testing();
        config.costs = ComputronCosts::zero();
        let mut engine = DreggEngine::new(config);
        for cell in [
            proof_cell,
            sigil_cell,
            party_cell,
            focus_cell,
            arena_cell,
            arena_gate_cell,
            agent_cell,
        ] {
            engine
                .ledger_mut()
                .insert_cell(cell)
                .expect("prototype cells have disjoint identities");
        }
        let mut registry = WitnessedPredicateRegistry::default_builtins();
        registry.register_custom(
            vk_hash,
            Arc::new(PrivateRaidRoleVerifier {
                vk_hash,
                statement,
                session: receipt.statement().session,
                seat: SEAT,
            }),
        );
        engine.executor_mut().set_witnessed_registry(registry);

        let mut proof_action = bare_action(
            proof_id,
            vec![
                set_field(proof_id, PROOF_LANDED, field_from_u64(1)),
                set_field(proof_id, PROOF_ROLE, field_from_u64(assigned_role_tag)),
            ],
        );
        proof_action
            .witness_blobs
            .push(WitnessBlob::proof(proof_bytes().to_vec()));

        let mut sigil_action = bare_action(
            sigil_id,
            vec![
                set_field(sigil_id, SIGIL_SPENT, field_from_u64(1)),
                set_field(sigil_id, SIGIL_ROLE, field_from_u64(assigned_role_tag)),
            ],
        );
        sigil_action.witness_blobs =
            vec![root_witness(proof_post_root), root_witness(proof_post_root)];

        let mut party_action = bare_action(
            party_id,
            vec![
                set_field(party_id, PARTY_CONTRIBUTED, field_from_u64(1)),
                set_field(party_id, PARTY_ROLE, field_from_u64(assigned_role_tag)),
                set_field(focus_id, FOCUS_SPENT, field_from_u64(PARTY_FOCUS_COST)),
            ],
        );
        party_action.witness_blobs =
            vec![root_witness(sigil_post_root), root_witness(sigil_post_root)];

        let mut arena_effects = arena_effects(&arena_before_native, &arena_after_native, &hit);
        arena_effects.extend([
            set_field(arena_gate_id, ARENA_GATE_OPEN, field_from_u64(1)),
            set_field(
                arena_gate_id,
                ARENA_GATE_ROLE,
                field_from_u64(assigned_role_tag),
            ),
        ]);
        let mut arena_action = bare_action(arena_id, arena_effects);
        arena_action.method = symbol(&format!("hvy/{attacker}/{WARDEN}"));
        arena_action.witness_blobs =
            vec![root_witness(party_post_root), root_witness(party_post_root)];

        let mut forest = CallForest::new();
        forest.add_root(proof_action);
        forest.add_root(sigil_action);
        forest.add_root(party_action);
        forest.add_root(arena_action);
        let mut turn = bare_turn(agent, 0, Vec::new());
        turn.call_forest = forest;

        Self {
            engine,
            turn,
            agent,
            proof: proof_id,
            sigil: sigil_id,
            party: party_id,
            focus: focus_id,
            arena: arena_id,
            arena_gate: arena_gate_id,
            arena_active_slot,
            arena_stunned_slot,
            assigned_role_tag,
        }
    }

    fn commitments(&self) -> Vec<[u8; 32]> {
        [
            self.proof,
            self.sigil,
            self.party,
            self.focus,
            self.arena_gate,
            self.arena,
        ]
        .into_iter()
        .map(|id| {
            self.engine
                .ledger()
                .get(&id)
                .expect("prototype cell remains present")
                .state_commitment()
        })
        .collect()
    }

    fn read(&self, cell: CellId, index: usize) -> u64 {
        field_to_u64(
            &self
                .engine
                .ledger()
                .get(&cell)
                .expect("prototype cell remains present")
                .state
                .fields[index],
        )
    }
}

#[test]
fn real_proof_sigil_party_and_arena_commit_as_one_four_root_forest() {
    let mut raid = AtomicRaidHarness::new();

    // RED tooth: the very last Arena predicate is stripped. By the time this
    // refuses, the proof has verified, the sigil and Party cells have mutated,
    // and the real Arena effects have been applied to the journal. None publish.
    let before = raid.commitments();
    let agent_nonce_before = raid
        .engine
        .ledger()
        .get(&raid.agent)
        .expect("agent remains present")
        .state
        .nonce();
    let mut stripped_tail = raid.turn.clone();
    stripped_tail
        .call_forest
        .roots
        .last_mut()
        .expect("Arena is the fourth root")
        .action
        .witness_blobs
        .pop();
    assert!(
        raid.engine.execute_turn(&stripped_tail).is_err(),
        "stripping the final Party->Arena observation must reject"
    );
    assert_eq!(
        raid.commitments(),
        before,
        "late Arena refusal rolls proof, sigil, Party, focus, and Arena back"
    );
    assert_eq!(
        raid.engine
            .ledger()
            .get(&raid.agent)
            .expect("agent remains present")
            .state
            .nonce(),
        agent_nonce_before + 1,
        "executor phase-one nonce accounting is intentionally outside forest rollback"
    );

    // Retry the exact honest forest at the executor's advanced actor nonce; it yields
    // one receipt covering four actions.
    raid.turn.nonce = raid
        .engine
        .ledger()
        .get(&raid.agent)
        .expect("agent remains present")
        .state
        .nonce();
    let receipt = raid
        .engine
        .execute_turn(&raid.turn)
        .expect("the exact proof-assigned forest commits");
    assert_eq!(receipt.action_count, 4);
    assert_eq!(raid.read(raid.proof, PROOF_LANDED), 1);
    assert_eq!(raid.read(raid.proof, PROOF_ROLE), raid.assigned_role_tag);
    assert_eq!(raid.read(raid.sigil, SIGIL_SPENT), 1);
    assert_eq!(raid.read(raid.sigil, SIGIL_ROLE), raid.assigned_role_tag);
    assert_eq!(raid.read(raid.party, PARTY_CONTRIBUTED), 1);
    assert_eq!(raid.read(raid.party, PARTY_ROLE), raid.assigned_role_tag);
    assert_eq!(raid.read(raid.focus, FOCUS_SPENT), PARTY_FOCUS_COST);
    assert_eq!(raid.read(raid.arena_gate, ARENA_GATE_OPEN), 1);
    assert_eq!(
        raid.read(raid.arena_gate, ARENA_GATE_ROLE),
        raid.assigned_role_tag
    );
    assert_eq!(
        raid.read(raid.arena, raid.arena_active_slot),
        raid.assigned_role_tag
    );
    assert_eq!(raid.read(raid.arena, raid.arena_stunned_slot), 1);
}

#[test]
fn custom_vk_refuses_a_non_receipt_without_leaking_any_raid_prefix() {
    let mut raid = AtomicRaidHarness::new();
    let before = raid.commitments();
    raid.turn.call_forest.roots[0].action.witness_blobs[0] =
        WitnessBlob::proof(b"not-a-private-raid-receipt".to_vec());
    assert!(raid.engine.execute_turn(&raid.turn).is_err());
    assert_eq!(raid.commitments(), before);
}

// Production cut plan (kept beside the executable spec so it cannot drift):
//
// 1. Give `Party` and `Arena` ownership-neutral deployment descriptors that install
//    their cells into a caller-supplied `World`/ledger and return public handles. Today
//    each constructor privately creates its own executor, which is the primary blocker.
// 2. Register `PrivateRaidRoleVerifier` (or its production equivalent) at host startup.
//    Its custom VK recipe must commit to the underlying HidingFri VK, fixed rule,
//    expected session, seat, and seat->Party-role interpretation.
// 3. Materialize the accepted proof statement in a proof-result cell. Each role sigil
//    observes its exact seat-role field at the proof cell's post root; the selected Party
//    role cell observes the spent sigil. Until executor authority discovery covers
//    `CellProgram::Cases`, install a Predicate admission gate that observes the Party
//    role/contribution and is changed by the same action as Arena; do not flatten or replace
//    Arena's full method-dispatched program merely to make the observation discoverable.
// 4. Build those actions in dependency order as sibling roots of one `CallForest` and
//    submit exactly one `Turn`. Do not retain the current pre-burn host boolean as authority.
// 5. Persist/replay the single `TurnReceipt`; retire the separate sigil receipt and the
//    detached Party+Arena transaction only after restart/substitution tests reproduce the
//    same forest and all pre-existing Party/Arena hostile teeth remain green.
