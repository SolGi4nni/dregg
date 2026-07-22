//! Relic resonance as an executor-owned Dungeon mechanic.
//!
//! The authored fork is deliberately small: taking one of two relics fixes an oath,
//! the oath fixes the guardian encounter, and that consequence fixes which relic may
//! awaken and which ending may land. Every branch fact is cell state and every edge is
//! a [`StateConstraint`] on the real executor; callers receive no host-side bypass.
//!
//! With `private-raid-assignment`, `AtomicRaidNarratedResonance` exposes the composed
//! cut. Its culminating turn is one real two-root `CallForest`: root one verifies and
//! materializes a HidingFri raid assignment through a custom witnessed predicate; root
//! two awakens the relic, binds the narration event, and changes a companion gate that
//! observes the proof root's exact post-state. The executor walks both roots over one
//! journal and publishes one receipt or neither root. This is executor-local atomicity,
//! not a claim that separately hosted `WorldCell` owners magically share a federation.

use std::sync::Arc;

use dregg_app_framework::{
    CellProgram, StateConstraint, TransitionCase, TransitionGuard, field_from_u64, symbol,
};
use spween::{Choice, PassageContent, Scene};
use spween_dregg::{
    CompiledStory, PASSAGE_ENDED, PASSAGE_SLOT, WorldCell, WorldError, choice_method,
    compile_scene, parse,
};

/// The authored Reliquary of Two Oaths scene.
pub const RELIQUARY_SOURCE: &str = r#"---
id: reliquary-of-two-oaths
title: The Reliquary of Two Oaths
weight: 1
---

=== reliquary

Two relics wait beneath the sleeping guardian: a sunblade wrapped in white linen and
a thorn crown resting in a bowl of old coins. The oath you take will wake the stone.

* [Lift the Sunblade and swear to free the valley]
  ~ oath = 1
  -> reliquary

* [Wear the Thorn Crown and claim the buried court]
  ~ oath = 2
  -> reliquary

* [Break the guardian's chains with the Sunblade]
  ~ guardian_defeated = 1
  ~ mercy = 1
  -> aftermath

* [Command the guardian to kneel to the Thorn Crown]
  ~ guardian_defeated = 1
  ~ curse = 1
  ~ tribute = 13
  -> aftermath

=== aftermath

The guardian is still. Dawn reaches the valley above; below, thirteen sealed coffers
wait around an empty throne. The relic in your hands remembers which promise you made.

* [Let the freed guardian kindle the Sunblade]
  ~ relic_awakened = 1
  -> aftermath

* [Feed thirteen seals of tribute to the Thorn Crown]
  ~ relic_awakened = 2
  -> aftermath

* [Carry the Sunblade home and free the valley]
  ~ village_saved = 1
  -> END

* [Descend crowned and claim the burial tribute]
  ~ vault_claimed = 1
  -> END
"#;

pub const ROOM_RELIQUARY: &str = "reliquary";
pub const ROOM_AFTERMATH: &str = "aftermath";

pub const TAKE_SUNBLADE: usize = 0;
pub const TAKE_THORN_CROWN: usize = 1;
pub const FREE_GUARDIAN: usize = 2;
pub const COMMAND_GUARDIAN: usize = 3;
pub const AWAKEN_SUNBLADE: usize = 0;
pub const AWAKEN_THORN_CROWN: usize = 1;
pub const SAVE_VALLEY: usize = 2;
pub const CLAIM_TRIBUTE: usize = 3;

/// Parse the static authored relic scene.
pub fn relic_scene() -> Scene {
    parse(RELIQUARY_SOURCE, "reliquary-of-two-oaths.scene")
        .expect("the embedded relic-resonance scene is valid")
}

/// Resolve one authored choice by its stable room-local index.
pub fn relic_choice(scene: &Scene, room: &str, index: usize) -> Option<Choice> {
    scene
        .passages
        .iter()
        .find(|passage| passage.name.as_str() == room)?
        .content
        .iter()
        .filter_map(|content| match content {
            PassageContent::Choice(choice) => Some(choice.clone()),
            _ => None,
        })
        .nth(index)
}

fn slot(story: &CompiledStory, name: &str) -> u8 {
    let key = *story
        .var_slots
        .get(name)
        .unwrap_or_else(|| panic!("relic-resonance story has `{name}` state"));
    u8::try_from(key).expect("the relic-resonance vars fit the register plane")
}

fn append_method_teeth(
    program: &mut CellProgram,
    method: &str,
    constraints: impl IntoIterator<Item = StateConstraint>,
) {
    let wanted = symbol(method);
    let CellProgram::Cases(cases) = program else {
        panic!("compiled relic-resonance story uses method cases");
    };
    let case = cases
        .iter_mut()
        .find(
            |case| matches!(&case.guard, TransitionGuard::MethodIs { method } if *method == wanted),
        )
        .unwrap_or_else(|| panic!("compiled relic choice method `{method}` exists"));
    case.constraints.extend(constraints);
}

fn confine_slot(program: &mut CellProgram, slot: u8, writers: &[&str]) {
    let writers: Vec<_> = writers.iter().map(|method| symbol(method)).collect();
    let CellProgram::Cases(cases) = program else {
        panic!("compiled relic-resonance story uses method cases");
    };
    for case in cases {
        let TransitionGuard::MethodIs { method } = &case.guard else {
            continue;
        };
        if !writers.contains(method) {
            case.constraints
                .push(StateConstraint::Immutable { index: slot });
        }
    }
}

fn eq(index: u8, value: u64) -> StateConstraint {
    StateConstraint::FieldEquals {
        index,
        value: field_from_u64(value),
    }
}

fn delta(index: u8, value: u64) -> StateConstraint {
    StateConstraint::FieldDelta {
        index,
        delta: field_from_u64(value),
    }
}

fn method(room: &str, index: usize) -> String {
    choice_method(room, index)
}

/// Compile the scene and install the oath, resonance, ending, and confinement teeth.
pub fn compile_relic_resonance() -> CompiledStory {
    let mut story = compile_scene(&relic_scene()).expect("the embedded relic scene compiles");

    let oath = slot(&story, "oath");
    let guardian = slot(&story, "guardian_defeated");
    let mercy = slot(&story, "mercy");
    let curse = slot(&story, "curse");
    let tribute = slot(&story, "tribute");
    let awakened = slot(&story, "relic_awakened");
    let village = slot(&story, "village_saved");
    let vault = slot(&story, "vault_claimed");

    let take_sunblade = method(ROOM_RELIQUARY, TAKE_SUNBLADE);
    let take_crown = method(ROOM_RELIQUARY, TAKE_THORN_CROWN);
    let free_guardian = method(ROOM_RELIQUARY, FREE_GUARDIAN);
    let command_guardian = method(ROOM_RELIQUARY, COMMAND_GUARDIAN);
    let awaken_sunblade = method(ROOM_AFTERMATH, AWAKEN_SUNBLADE);
    let awaken_crown = method(ROOM_AFTERMATH, AWAKEN_THORN_CROWN);
    let save_valley = method(ROOM_AFTERMATH, SAVE_VALLEY);
    let claim_tribute = method(ROOM_AFTERMATH, CLAIM_TRIBUTE);

    let reliquary = story.passage_index[ROOM_RELIQUARY] as u64;
    let aftermath = story.passage_index[ROOM_AFTERMATH] as u64;

    append_method_teeth(
        &mut story.program,
        &take_sunblade,
        [
            eq(oath, 1),
            delta(oath, 1),
            StateConstraint::WriteOnce { index: oath },
            eq(PASSAGE_SLOT as u8, reliquary),
        ],
    );
    append_method_teeth(
        &mut story.program,
        &take_crown,
        [
            eq(oath, 2),
            delta(oath, 2),
            StateConstraint::WriteOnce { index: oath },
            eq(PASSAGE_SLOT as u8, reliquary),
        ],
    );

    append_method_teeth(
        &mut story.program,
        &free_guardian,
        [
            eq(oath, 1),
            eq(guardian, 1),
            delta(guardian, 1),
            eq(mercy, 1),
            delta(mercy, 1),
            eq(PASSAGE_SLOT as u8, aftermath),
        ],
    );
    append_method_teeth(
        &mut story.program,
        &command_guardian,
        [
            eq(oath, 2),
            eq(guardian, 1),
            delta(guardian, 1),
            eq(curse, 1),
            delta(curse, 1),
            eq(tribute, 13),
            delta(tribute, 13),
            eq(PASSAGE_SLOT as u8, aftermath),
        ],
    );

    let aftermath_loop = || StateConstraint::AllowedTransitions {
        slot_index: PASSAGE_SLOT as u8,
        allowed: vec![(field_from_u64(aftermath), field_from_u64(aftermath))],
    };
    append_method_teeth(
        &mut story.program,
        &awaken_sunblade,
        [
            eq(oath, 1),
            eq(guardian, 1),
            eq(mercy, 1),
            eq(awakened, 1),
            delta(awakened, 1),
            StateConstraint::WriteOnce { index: awakened },
            aftermath_loop(),
        ],
    );
    append_method_teeth(
        &mut story.program,
        &awaken_crown,
        [
            eq(oath, 2),
            eq(guardian, 1),
            eq(curse, 1),
            eq(tribute, 13),
            eq(awakened, 2),
            delta(awakened, 2),
            StateConstraint::WriteOnce { index: awakened },
            aftermath_loop(),
        ],
    );

    append_method_teeth(
        &mut story.program,
        &save_valley,
        [
            eq(oath, 1),
            eq(guardian, 1),
            eq(mercy, 1),
            eq(awakened, 1),
            eq(village, 1),
            delta(village, 1),
            eq(PASSAGE_SLOT as u8, PASSAGE_ENDED),
        ],
    );
    append_method_teeth(
        &mut story.program,
        &claim_tribute,
        [
            eq(oath, 2),
            eq(guardian, 1),
            eq(curse, 1),
            eq(tribute, 13),
            eq(awakened, 2),
            eq(vault, 1),
            delta(vault, 1),
            eq(PASSAGE_SLOT as u8, PASSAGE_ENDED),
        ],
    );

    confine_slot(&mut story.program, oath, &[&take_sunblade, &take_crown]);
    confine_slot(
        &mut story.program,
        guardian,
        &[&free_guardian, &command_guardian],
    );
    confine_slot(&mut story.program, mercy, &[&free_guardian]);
    confine_slot(&mut story.program, curse, &[&command_guardian]);
    confine_slot(&mut story.program, tribute, &[&command_guardian]);
    confine_slot(
        &mut story.program,
        awakened,
        &[&awaken_sunblade, &awaken_crown],
    );
    confine_slot(&mut story.program, village, &[&save_valley]);
    confine_slot(&mut story.program, vault, &[&claim_tribute]);

    let CellProgram::Cases(cases) = &mut story.program else {
        unreachable!();
    };
    cases.push(TransitionCase {
        guard: TransitionGuard::SlotChanged { index: oath },
        constraints: vec![
            StateConstraint::MemberOf {
                index: oath,
                set: vec![1, 2],
            },
            StateConstraint::WriteOnce { index: oath },
        ],
    });
    cases.push(TransitionCase {
        guard: TransitionGuard::SlotChanged { index: awakened },
        constraints: vec![
            StateConstraint::MemberOf {
                index: awakened,
                set: vec![1, 2],
            },
            StateConstraint::WriteOnce { index: awakened },
        ],
    });

    story
}

/// Deploy the production relic-resonance cell.
pub fn deploy_relic_resonance(seed: u8) -> Result<WorldCell, WorldError> {
    WorldCell::deploy_compiled(Arc::new(compile_relic_resonance()), seed)
}

#[cfg(feature = "private-raid-assignment")]
mod atomic_raid_narration {
    use std::collections::BTreeMap;
    use std::sync::Arc;

    use dregg_app_framework::{
        DreggEngine, EngineConfig, Event, FieldElement, TurnReceipt, field_from_u64, symbol,
    };
    use dregg_cell::predicate::{
        InputRef, PredicateInput, WitnessedPredicate, WitnessedPredicateError,
        WitnessedPredicateKind, WitnessedPredicateRegistry, WitnessedPredicateVerifier,
        canonical_predicate_vk,
    };
    use dregg_cell::{AuthRequired, Cell, CellId, CellProgram, StateConstraint};
    use dregg_turn::action::{Action, Effect, WitnessBlob};
    use dregg_turn::{CallForest, ComputronCosts, Turn};
    use spween_dregg::{
        GENESIS_DONE_EXT_KEY, GENESIS_METHOD, PASSAGE_ENDED, PASSAGE_SLOT, choice_method,
        value_to_field, value_to_u64,
    };
    use starbridge_v2::world::{bare_action, bare_turn, make_open_cell, open_permissions};

    use crate::narrator::{NARRATION_TOPIC, Narrated, narration_commitment};
    use crate::private_raid::{RAID_SEATS, RaidAssignmentReceipt, RaidAssignmentSession, RaidRole};

    use super::{
        AWAKEN_SUNBLADE, FREE_GUARDIAN, ROOM_AFTERMATH, ROOM_RELIQUARY, TAKE_SUNBLADE,
        compile_relic_resonance, deploy_relic_resonance, relic_choice, relic_scene,
    };

    const PROOF_LANDED: usize = 0;
    const PROOF_ROLE: usize = 1;
    const GATE_LANDED: usize = 0;
    const GATE_ROLE: usize = 1;
    const MENDER_TAG: u64 = 3;

    fn field_to_u64(value: &[u8; 32]) -> u64 {
        u64::from_be_bytes(value[24..].try_into().expect("eight-byte u64 lane"))
    }

    fn role_tag(role: RaidRole) -> u64 {
        role as u64 + 1
    }

    /// Commitment installed in the proof cell's witnessed predicate.
    pub fn raid_statement_commitment(receipt: &RaidAssignmentReceipt) -> [u8; 32] {
        let mut hash = blake3::Hasher::new_derive_key(
            "dregg.dungeon.relic-resonance.private-raid-statement.v1",
        );
        hash.update(&receipt.verifier_key());
        for public in receipt.statement().as_u32_vec() {
            hash.update(&public.to_le_bytes());
        }
        *hash.finalize().as_bytes()
    }

    fn role_predicate_vk(receipt: &RaidAssignmentReceipt, seat: usize) -> [u8; 32] {
        let mut recipe = b"dungeon/relic-resonance/private-raid-role/v1".to_vec();
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
                kind_name: "DungeonRelicPrivateRaidRole",
                reason: reason.into(),
            }
        }
    }

    impl WitnessedPredicateVerifier for PrivateRaidRoleVerifier {
        fn name(&self) -> &'static str {
            "dungeon-relic-private-raid-role-v1"
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
                return Err(Self::reject("installed raid statement changed"));
            }
            let PredicateInput::Slot(role_field) = input else {
                return Err(WitnessedPredicateError::InputShapeMismatch {
                    kind_name: "DungeonRelicPrivateRaidRole",
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
                return Err(Self::reject("raid receipt is not canonically encoded"));
            }
            if raid_statement_commitment(&receipt) != self.statement {
                return Err(Self::reject("proof carries another public statement"));
            }
            let mut gate = RaidAssignmentSession::new(self.session)
                .map_err(|error| Self::reject(error.to_string()))?;
            let assignment = gate
                .accept(&receipt)
                .map_err(|error| Self::reject(error.to_string()))?;
            let assigned = assignment
                .role_for_seat(self.seat)
                .ok_or_else(|| Self::reject("verified assignment omitted the requested seat"))?;
            let expected = role_tag(assigned);
            if field_to_u64(role_field) != expected {
                return Err(Self::reject(format!(
                    "proof assigned role tag {expected}, action attempted {}",
                    field_to_u64(role_field)
                )));
            }
            Ok(())
        }
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
        WitnessBlob::merkle_path(root.to_vec())
    }

    fn set_field(cell: CellId, index: u64, value: FieldElement) -> Effect {
        Effect::SetField { cell, index, value }
    }

    fn set_post(cell: &Cell, writes: &[(usize, FieldElement)]) -> Cell {
        let mut post = cell.clone();
        for (index, value) in writes {
            assert!(post.state.set_field(*index, *value));
        }
        post
    }

    /// An opaque, session-bound forest ready for atomic submission.
    pub struct PreparedNarratedResonance {
        turn: Turn,
        narration_commit: FieldElement,
        narrated: Narrated,
    }

    impl PreparedNarratedResonance {
        /// Inspect the immutable executor turn before submission.
        pub fn turn(&self) -> &Turn {
            &self.turn
        }

        /// The narration commitment carried by the resonance root's event.
        pub const fn narration_commitment(&self) -> FieldElement {
            self.narration_commit
        }
    }

    /// The one receipt produced by the proof-root + narrated-resonance-root forest.
    #[derive(Clone, Debug)]
    pub struct AtomicNarratedResonanceReceipt {
        /// The executor's single receipt over both forest roots.
        pub receipt: TurnReceipt,
        /// The typed command and prose resolved by the resonance root.
        pub narrated: Narrated,
        /// The narration event's committed field.
        pub narration_commitment: FieldElement,
        /// The proof root's installed public-statement commitment.
        pub raid_statement_commitment: FieldElement,
        /// The seat whose verified Mender allocation authorized resonance.
        pub assigned_seat: usize,
    }

    /// One shared executor carrying the relic, proof-result, and observation-gate cells.
    pub struct AtomicRaidNarratedResonance {
        engine: DreggEngine,
        agent: CellId,
        relic: CellId,
        proof: CellId,
        gate: CellId,
        proof_post_root: [u8; 32],
        receipt_bytes: Vec<u8>,
        statement_commitment: [u8; 32],
        seat: usize,
        story: Arc<spween_dregg::CompiledStory>,
        receipts: Vec<TurnReceipt>,
    }

    impl AtomicRaidNarratedResonance {
        /// Assemble a joined executor image. The proof is not accepted here: only its
        /// public statement is staged. Acceptance happens inside the forest's first root.
        pub fn new(seed: u8, receipt: RaidAssignmentReceipt, seat: usize) -> Result<Self, String> {
            if seat >= RAID_SEATS {
                return Err(format!("raid seat {seat} is outside the four-seat party"));
            }
            let receipt_bytes = receipt.to_postcard().map_err(|error| error.to_string())?;
            let statement_commitment = raid_statement_commitment(&receipt);
            let vk_hash = role_predicate_vk(&receipt, seat);

            let mut proof_cell = make_open_cell(0xD1, 0);
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
                        commitment: statement_commitment,
                        input_ref: InputRef::Slot {
                            index: PROOF_ROLE as u8,
                        },
                        proof_witness_index: 0,
                    },
                },
            ]);
            let proof = proof_cell.id();
            let proof_post = set_post(
                &proof_cell,
                &[
                    (PROOF_LANDED, field_from_u64(1)),
                    (PROOF_ROLE, field_from_u64(MENDER_TAG)),
                ],
            );
            let proof_post_root = proof_post.state_commitment();

            let mut gate_cell = make_open_cell(0xD2, 0);
            gate_cell.program = CellProgram::Predicate(vec![
                StateConstraint::FieldEquals {
                    index: GATE_LANDED as u8,
                    value: field_from_u64(1),
                },
                StateConstraint::FieldEquals {
                    index: GATE_ROLE as u8,
                    value: field_from_u64(MENDER_TAG),
                },
                StateConstraint::WriteOnce {
                    index: GATE_LANDED as u8,
                },
                StateConstraint::WriteOnce {
                    index: GATE_ROLE as u8,
                },
                observed(GATE_LANDED, proof, PROOF_LANDED, proof_post_root, 0),
                observed(GATE_ROLE, proof, PROOF_ROLE, proof_post_root, 1),
            ]);
            let gate = gate_cell.id();

            let relic_world = deploy_relic_resonance(seed).map_err(|error| error.to_string())?;
            let mut relic_cell = relic_world
                .cell_snapshot()
                .ok_or_else(|| "deployed relic cell is absent".to_string())?;
            let relic = relic_cell.id();
            relic_cell.permissions = open_permissions();

            let mut agent_cell = make_open_cell(0xD0, 0);
            let agent = agent_cell.id();
            for target in [relic, proof, gate] {
                agent_cell
                    .capabilities
                    .grant(target, AuthRequired::None)
                    .ok_or_else(|| "composed relic capability list overflowed".to_string())?;
            }

            let mut config = EngineConfig::for_testing();
            config.costs = ComputronCosts::zero();
            let mut engine = DreggEngine::new(config);
            for cell in [proof_cell, gate_cell, relic_cell, agent_cell] {
                engine
                    .ledger_mut()
                    .insert_cell(cell)
                    .map_err(|error| format!("cannot insert composed relic cell: {error:?}"))?;
            }
            let mut registry = WitnessedPredicateRegistry::default_builtins();
            registry.register_custom(
                vk_hash,
                Arc::new(PrivateRaidRoleVerifier {
                    vk_hash,
                    statement: statement_commitment,
                    session: receipt.statement().session,
                    seat,
                }),
            );
            engine.executor_mut().set_witnessed_registry(registry);

            let mut joined = Self {
                engine,
                agent,
                relic,
                proof,
                gate,
                proof_post_root,
                receipt_bytes,
                statement_commitment,
                seat,
                story: Arc::new(compile_relic_resonance()),
                receipts: Vec::new(),
            };
            joined.commit_genesis()?;
            Ok(joined)
        }

        fn read_cell_field(&self, cell: CellId, index: usize) -> u64 {
            self.engine
                .ledger()
                .get(&cell)
                .and_then(|cell| cell.state.fields.get(index))
                .map(field_to_u64)
                .unwrap_or(0)
        }

        /// Read one committed relic-story variable by name.
        pub fn read_relic_var(&self, name: &str) -> u64 {
            let Some(key) = self.story.var_key(name) else {
                return 0;
            };
            self.engine
                .ledger()
                .get(&self.relic)
                .and_then(|cell| cell.state.get_field_ext(key))
                .map(|value| field_to_u64(&value))
                .unwrap_or(0)
        }

        /// Whether the proof-result root has materialized its one-shot result.
        pub fn proof_landed(&self) -> bool {
            self.read_cell_field(self.proof, PROOF_LANDED) == 1
        }

        /// Whether the resonance root observed and consumed the proof result.
        pub fn resonance_gate_landed(&self) -> bool {
            self.read_cell_field(self.gate, GATE_LANDED) == 1
        }

        /// The committed receipt chain, beginning with the one-shot scene genesis.
        pub fn receipts(&self) -> &[TurnReceipt] {
            &self.receipts
        }

        fn lower_choice(&self, room: &str, index: usize) -> Result<Vec<Effect>, String> {
            let scene = relic_scene();
            let choice = relic_choice(&scene, room, index)
                .ok_or_else(|| format!("unknown relic choice {room}/{index}"))?;
            let relic_cell = self
                .engine
                .ledger()
                .get(&self.relic)
                .ok_or_else(|| "joined relic cell is absent".to_string())?;
            let mut local: BTreeMap<u64, u64> = BTreeMap::new();
            let mut effects = Vec::new();
            for effect in &choice.effects {
                match effect {
                    spween::Effect::Set(set) => {
                        if let Some(key) = self.story.var_key(set.var.as_str()) {
                            let value = value_to_u64(&set.value);
                            local.insert(key, value);
                            effects.push(set_field(self.relic, key, field_from_u64(value)));
                        }
                    }
                    spween::Effect::Modify(modify) => {
                        if let Some(key) = self.story.var_key(modify.var.as_str()) {
                            let current = local.get(&key).copied().unwrap_or_else(|| {
                                relic_cell
                                    .state
                                    .get_field_ext(key)
                                    .map(|value| field_to_u64(&value))
                                    .unwrap_or(0)
                            });
                            let value = (current as i64 + modify.delta).max(0) as u64;
                            local.insert(key, value);
                            effects.push(set_field(self.relic, key, field_from_u64(value)));
                        }
                    }
                    spween::Effect::Call(call) => {
                        let args = call.args.iter().map(value_to_field).collect();
                        effects.push(Effect::EmitEvent {
                            cell: self.relic,
                            event: Event::new(symbol(&call.name), args),
                        });
                    }
                }
            }
            let passage = match &choice.target {
                Some(target) if target.is_end => PASSAGE_ENDED,
                Some(target) => *self
                    .story
                    .passage_index
                    .get(target.target.as_str())
                    .ok_or_else(|| format!("unknown relic target `{}`", target.target))?
                    as u64,
                None => PASSAGE_ENDED,
            };
            effects.push(set_field(
                self.relic,
                PASSAGE_SLOT as u64,
                field_from_u64(passage),
            ));
            Ok(effects)
        }

        fn current_nonce(&self) -> u64 {
            self.engine
                .ledger()
                .get(&self.agent)
                .expect("composed relic agent remains present")
                .state
                .nonce()
        }

        fn turn_from_roots(&self, roots: impl IntoIterator<Item = Action>) -> Turn {
            let mut forest = CallForest::new();
            for root in roots {
                forest.add_root(root);
            }
            let mut turn = bare_turn(self.agent, self.current_nonce(), Vec::new());
            turn.call_forest = forest;
            turn.previous_receipt_hash = self.receipts.last().map(TurnReceipt::receipt_hash);
            turn
        }

        fn commit_choice(&mut self, room: &str, index: usize) -> Result<TurnReceipt, String> {
            let effects = self.lower_choice(room, index)?;
            let mut action = bare_action(self.relic, effects);
            action.method = symbol(&choice_method(room, index));
            let turn = self.turn_from_roots([action]);
            let receipt = self
                .engine
                .execute_turn(&turn)
                .map_err(|error| error.to_string())?;
            self.receipts.push(receipt.clone());
            Ok(receipt)
        }

        fn commit_genesis(&mut self) -> Result<TurnReceipt, String> {
            let passage = self.story.passage_index[ROOM_RELIQUARY] as u64;
            let effects = vec![
                set_field(self.relic, PASSAGE_SLOT as u64, field_from_u64(passage)),
                set_field(self.relic, GENESIS_DONE_EXT_KEY, field_from_u64(1)),
            ];
            let mut action = bare_action(self.relic, effects);
            action.method = symbol(GENESIS_METHOD);
            let turn = self.turn_from_roots([action]);
            let receipt = self
                .engine
                .execute_turn(&turn)
                .map_err(|error| error.to_string())?;
            self.receipts.push(receipt.clone());
            Ok(receipt)
        }

        /// Commit the Sunblade oath as one ordinary receipt.
        pub fn take_sunblade(&mut self) -> Result<TurnReceipt, String> {
            self.commit_choice(ROOM_RELIQUARY, TAKE_SUNBLADE)
        }

        /// Commit the oath-selected mercy encounter as one ordinary receipt.
        pub fn free_guardian(&mut self) -> Result<TurnReceipt, String> {
            self.commit_choice(ROOM_RELIQUARY, FREE_GUARDIAN)
        }

        /// Build the exact two-root forest without mutating the executor.
        pub fn prepare_narrated_resonance(
            &self,
            narrated: &Narrated,
        ) -> Result<PreparedNarratedResonance, String> {
            if narrated.command.room != ROOM_AFTERMATH || narrated.command.choice != AWAKEN_SUNBLADE
            {
                return Err(
                    "the composed narrator must name the Sunblade awakening in aftermath"
                        .to_string(),
                );
            }
            if narrated.narration.trim().is_empty() {
                return Err("the composed narrated resonance has empty prose".to_string());
            }
            if narrated.narration.contains("{{") {
                return Err(
                    "the composed narrated resonance carries a refused `{{` delimiter".to_string(),
                );
            }

            let mut proof_action = bare_action(
                self.proof,
                vec![
                    set_field(self.proof, PROOF_LANDED as u64, field_from_u64(1)),
                    set_field(self.proof, PROOF_ROLE as u64, field_from_u64(MENDER_TAG)),
                ],
            );
            proof_action
                .witness_blobs
                .push(WitnessBlob::proof(self.receipt_bytes.clone()));

            let narration_commit = narration_commitment(&narrated.narration);
            let mut resonance_effects = self.lower_choice(ROOM_AFTERMATH, AWAKEN_SUNBLADE)?;
            resonance_effects.extend([
                set_field(self.gate, GATE_LANDED as u64, field_from_u64(1)),
                set_field(self.gate, GATE_ROLE as u64, field_from_u64(MENDER_TAG)),
                Effect::EmitEvent {
                    cell: self.relic,
                    event: Event::new(symbol(NARRATION_TOPIC), vec![narration_commit]),
                },
            ]);
            let mut resonance_action = bare_action(self.relic, resonance_effects);
            resonance_action.method = symbol(&choice_method(ROOM_AFTERMATH, AWAKEN_SUNBLADE));
            resonance_action.witness_blobs = vec![
                root_witness(self.proof_post_root),
                root_witness(self.proof_post_root),
            ];

            Ok(PreparedNarratedResonance {
                turn: self.turn_from_roots([proof_action, resonance_action]),
                narration_commit,
                narrated: narrated.clone(),
            })
        }

        /// Execute the prepared proof + narration + resonance forest atomically.
        pub fn commit_narrated_resonance(
            &mut self,
            prepared: PreparedNarratedResonance,
        ) -> Result<AtomicNarratedResonanceReceipt, String> {
            let receipt = self
                .engine
                .execute_turn(&prepared.turn)
                .map_err(|error| error.to_string())?;
            self.receipts.push(receipt.clone());
            Ok(AtomicNarratedResonanceReceipt {
                receipt,
                narrated: prepared.narrated,
                narration_commitment: prepared.narration_commit,
                raid_statement_commitment: self.statement_commitment,
                assigned_seat: self.seat,
            })
        }

        /// Prepare and atomically commit the narrated awakening forest.
        pub fn awaken_with_private_raid_narration(
            &mut self,
            narrated: &Narrated,
        ) -> Result<AtomicNarratedResonanceReceipt, String> {
            let prepared = self.prepare_narrated_resonance(narrated)?;
            self.commit_narrated_resonance(prepared)
        }
    }
}

#[cfg(feature = "private-raid-assignment")]
pub use atomic_raid_narration::{
    AtomicNarratedResonanceReceipt, AtomicRaidNarratedResonance, PreparedNarratedResonance,
    raid_statement_commitment,
};
