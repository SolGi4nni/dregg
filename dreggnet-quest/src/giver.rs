//! # `giver` — the CROSS-CELL quest-giver: a grant that READS the quest cell.
//!
//! [`crate`]'s turn-in reward is a SAME-CELL gate — the `reward` slot lives on the quest
//! cell, opened by a [`FieldGte`](dregg_app_framework::StateConstraint::FieldGte) on that
//! cell's own committed progress. This module closes the other half the roadmap names: a
//! **quest-giver whose grant reads the quest cell**, a real cross-cell
//! [`StateConstraint::ObservedFieldEquals`] — "the giver hands over its reward BECAUSE the
//! objective was completed on ANOTHER cell." It re-homes [`dungeon_on_dregg::multicell`]'s
//! proven cross-cell gate onto a quest turn-in.
//!
//! ## The two cells share ONE executor ledger
//!
//! | cell | role | program (executor teeth) |
//! |------|------|--------------------------|
//! | [`QUEST`](QuestGiverWorld::quest) | the quest-state cell | authored [`CellProgram::Cases`] — ordered `WriteOnce`/`FieldDelta` step-flags + a `FieldGte(steps_done, N)` + `WriteOnce(reward)` turn-in (the [`crate`] teeth, authored directly in the [`dungeon_on_dregg::meta`] pattern so the cell can live on a shared ledger) |
//! | [`GIVER`](QuestGiverWorld::giver) | the quest-giver's grant | [`CellProgram::Predicate`]`([ObservedFieldEquals])` — the cross-cell gate |
//!
//! The giver cell carries ONE tooth: an [`StateConstraint::ObservedFieldEquals`] naming the
//! QUEST cell + its `reward` slot at the quest cell's **post-turn-in finalized root**
//! ([`QuestGiverWorld::grant_root`]). On every turn touching the giver, the verified
//! executor rebuilds a finalized-root authority from the COMMITTED LEDGER and admits the
//! grant IFF the quest cell's live commitment IS the grant root (the errand was turned in)
//! AND the giver's local grant value equals the quest cell's committed `reward`, with the
//! Merkle-open witness present. So:
//!
//! * **before the errand is turned in** the quest cell's commitment is not the grant root
//!   ⇒ the authority has no binding ⇒ the grant REFUSES (fail-closed);
//! * **after the player really completes + turns in the quest** the quest cell IS at the
//!   grant root ⇒ the authority binds `reward -> 1` ⇒ the giver grant COMMITS;
//! * a **forged grant** — granting before the turn-in, or with a value diverging from the
//!   quest's real reward, or with the witness stripped — is REFUSED. The authority is
//!   rebuilt from the LIVE ledger, never the submitter's claim.
//!
//! ## Honest scope — the finality source
//!
//! As in [`dungeon_on_dregg::multicell`]: in this in-process world the executor's
//! "finalized view" of the quest cell is its CURRENT committed state (turns commit
//! synchronously). The gate is genuinely executor-enforced ACROSS cells and fails closed;
//! the witness blob is STRUCTURALLY required (its absence refuses), and the host recomputes
//! the genuine `(cell, commitment, field, value)` from its own committed ledger. A
//! PRODUCTION finality source (a cross-node finalized-root channel / the recursive light
//! client) is the named add — it would furnish the quest cell's root from an independently
//! finalized chain, so the giver could gate on a quest cell on a DIFFERENT node's ledger.

use dregg_app_framework::{
    AgentCipherclerk, AppCipherclerk, AuthRequired, CellId, CellProgram, Effect, EmbeddedExecutor,
    FieldElement, StateConstraint, TransitionCase, TransitionGuard, TurnReceipt, field_from_u64,
    symbol,
};
use dregg_cell::{Cell, Permissions};
use dregg_turn::action::{WitnessBlob, WitnessKind};

use crate::{NUM_STEPS, REWARD_VALUE, TURN_IN_THRESHOLD};

/// The quest cell's `step_k` flag slot (slots `1..=NUM_STEPS`).
fn step_slot(k: usize) -> u8 {
    k as u8
}
/// The quest cell's `steps_done` counter slot (past the step flags).
const STEPS_DONE_SLOT: u8 = (NUM_STEPS + 1) as u8;
/// The quest cell's `reward` slot — the completion marker the giver reads cross-cell.
pub const REWARD_SLOT: u8 = (NUM_STEPS + 2) as u8;
/// The giver cell's `granted` slot — the cross-cell gated write.
pub const GRANTED_SLOT: u8 = 0;

/// The federation the world's turns commit under (a fixed demo federation id).
const FEDERATION: [u8; 32] = [0x0F; 32];
/// A FIXED driver seed — so the dry-run that pins the grant root ([`finalized_turnin_root`])
/// and the real world share ONE driver identity (hence the quest cell's post-turn-in
/// commitment matches between them).
const DRIVER_SEED: [u8; 64] = [0x1F; 64];

/// Stable cell seeds (a re-deploy reproduces the same cell identities).
const QUEST_SEED: u8 = 0x71;
const GIVER_SEED: u8 = 0x72;

/// The method that lights quest step `k` (`1..=NUM_STEPS`).
fn light_method(k: usize) -> String {
    format!("quest/light/{k}")
}
/// The method that turns in the quest (opens the `reward`).
fn turn_in_method() -> String {
    "quest/turn_in".to_string()
}
/// The method the giver grant presents (writes `granted`).
fn grant_method() -> String {
    "giver/grant".to_string()
}

/// A cell whose permissions gate nothing (the cross-cell GATE + the cap are the
/// load-bearing teeth, as in [`dungeon_on_dregg::multicell`]).
fn open_permissions() -> Permissions {
    Permissions {
        send: AuthRequired::None,
        receive: AuthRequired::None,
        set_state: AuthRequired::None,
        set_permissions: AuthRequired::None,
        set_verification_key: AuthRequired::None,
        increment_nonce: AuthRequired::None,
        delegate: AuthRequired::None,
        access: AuthRequired::None,
    }
}

/// Build an open world cell with `program` installed, deterministic in `seed`.
fn world_cell(seed: u8, program: CellProgram) -> Cell {
    let mut pk = [0u8; 32];
    pk[0] = seed;
    pk[31] = seed.wrapping_mul(37);
    let mut cell = Cell::with_balance(pk, [0u8; 32], 0);
    cell.permissions = open_permissions();
    cell.program = program;
    cell
}

/// **The quest-state cell's program** — the [`crate`] quest teeth, authored directly (the
/// [`dungeon_on_dregg::meta`] `meta_hero_story` pattern) so the cell can live on a shared
/// executor ledger alongside the giver: ordered `WriteOnce`/`FieldDelta` step-flags with a
/// `BoundedBy` order gate, and a `FieldGte(steps_done, N)` + `WriteOnce(reward)` turn-in.
fn quest_program() -> CellProgram {
    let mut cases: Vec<TransitionCase> = Vec::new();
    for k in 1..=NUM_STEPS {
        let mut constraints = vec![
            StateConstraint::WriteOnce {
                index: step_slot(k),
            },
            StateConstraint::FieldDelta {
                index: step_slot(k),
                delta: field_from_u64(1),
            },
            StateConstraint::FieldDelta {
                index: STEPS_DONE_SLOT,
                delta: field_from_u64(1),
            },
        ];
        if k > 1 {
            constraints.push(StateConstraint::BoundedBy {
                index: step_slot(k),
                witness_index: step_slot(k - 1),
            });
        }
        cases.push(TransitionCase {
            guard: TransitionGuard::MethodIs {
                method: symbol(&light_method(k)),
            },
            constraints,
        });
    }
    cases.push(TransitionCase {
        guard: TransitionGuard::MethodIs {
            method: symbol(&turn_in_method()),
        },
        constraints: vec![
            StateConstraint::FieldGte {
                index: STEPS_DONE_SLOT,
                value: field_from_u64(TURN_IN_THRESHOLD),
            },
            StateConstraint::FieldEquals {
                index: REWARD_SLOT,
                value: field_from_u64(REWARD_VALUE),
            },
            StateConstraint::WriteOnce { index: REWARD_SLOT },
        ],
    });
    CellProgram::Cases(cases)
}

/// Assemble the two-cell world on a fresh executor, granting the driver caps to both cells.
/// `grant_root` installs the giver's cross-cell gate at that finalized quest root; `None`
/// leaves the giver ungated (used by the dry-run that computes the root).
fn assemble(grant_root: Option<[u8; 32]>) -> (EmbeddedExecutor, AppCipherclerk, CellId, CellId) {
    let cclerk = AppCipherclerk::new(AgentCipherclerk::from_seed(DRIVER_SEED), FEDERATION);
    let exec = EmbeddedExecutor::new(&cclerk, "default");
    let driver = cclerk.cell_id();

    let quest = world_cell(QUEST_SEED, quest_program());
    let quest_id = quest.id();

    let giver_program = match grant_root {
        Some(at_root) => CellProgram::Predicate(vec![StateConstraint::ObservedFieldEquals {
            local_field: GRANTED_SLOT,
            source_cell: *quest_id.as_bytes(),
            source_field: REWARD_SLOT,
            at_root,
            proof_witness_index: 0,
        }]),
        None => CellProgram::None,
    };
    let giver = world_cell(GIVER_SEED, giver_program);
    let giver_id = giver.id();

    exec.ensure_cell(quest).expect("quest cell inserts");
    exec.ensure_cell(giver).expect("giver cell inserts");

    exec.with_ledger_mut(|ledger| {
        if let Some(agent) = ledger.get_mut(&driver) {
            agent.capabilities.grant(quest_id, AuthRequired::None);
            agent.capabilities.grant(giver_id, AuthRequired::None);
        }
    });

    (exec, cclerk, quest_id, giver_id)
}

/// A `SetField` effect on `cell`'s slot `index`.
fn set_field(cell: CellId, index: usize, value: FieldElement) -> Effect {
    Effect::SetField { cell, index, value }
}

/// Build, sign (over the attached witness blobs), wrap, and submit one turn — the real
/// cap-bounded turn the [`EmbeddedExecutor`] admits IFF every cap AND the touched cell's
/// program admit it. Returns the receipt or the refusal reason.
fn issue(
    exec: &EmbeddedExecutor,
    cclerk: &AppCipherclerk,
    target: CellId,
    method: &str,
    effects: Vec<Effect>,
    witness_blobs: Vec<WitnessBlob>,
) -> Result<TurnReceipt, String> {
    let mut action = cclerk.make_action(target, method, effects);
    action.witness_blobs = witness_blobs;
    let action = cclerk.sign_action(action);
    let turn = cclerk.make_turn(action);
    exec.submit_turn(&turn).map_err(|e| e.to_string())
}

/// The Merkle-open witness of the quest cell's finalized state the gated grant carries.
/// Referenced by the giver's `ObservedFieldEquals { proof_witness_index: 0 }`; its ABSENCE
/// fails the gate closed.
fn peer_finalized_witness(at_root: [u8; 32]) -> WitnessBlob {
    WitnessBlob::new(WitnessKind::MerklePath, at_root.to_vec())
}

/// Drive the quest cell START -> TURN-IN on `exec` (light every ward in order, then turn
/// in). The exact sequence the dry-run and the real completion share, so the quest cell
/// reaches the byte-identical post-turn-in commitment in both.
fn complete_quest(exec: &EmbeddedExecutor, cclerk: &AppCipherclerk, quest: CellId) {
    for k in 1..=NUM_STEPS {
        // step_k = 1, steps_done += 1 (read the running committed value).
        let steps_done = read_slot(exec, quest, STEPS_DONE_SLOT as usize);
        issue(
            exec,
            cclerk,
            quest,
            &light_method(k),
            vec![
                set_field(quest, step_slot(k) as usize, field_from_u64(1)),
                set_field(
                    quest,
                    STEPS_DONE_SLOT as usize,
                    field_from_u64(steps_done + 1),
                ),
            ],
            vec![],
        )
        .unwrap_or_else(|e| panic!("lighting quest ward {k} commits: {e}"));
    }
    issue(
        exec,
        cclerk,
        quest,
        &turn_in_method(),
        vec![set_field(
            quest,
            REWARD_SLOT as usize,
            field_from_u64(REWARD_VALUE),
        )],
        vec![],
    )
    .expect("the quest turn-in commits");
}

/// Read `slot` of `cell` off the committed ledger (`0` if absent) — decoded with the
/// canonical [`spween_dregg::field_to_u64`] (last-8-bytes big-endian), the inverse of the
/// [`field_from_u64`] the writes use.
fn read_slot(exec: &EmbeddedExecutor, cell: CellId, slot: usize) -> u64 {
    exec.cell_state(cell)
        .map(|s| spween_dregg::field_to_u64(&s.fields[slot]))
        .unwrap_or(0)
}

/// Compute the quest cell's **post-turn-in finalized commitment** — the finalized peer root
/// the giver's cross-cell gate pins. A throwaway world drives the quest to a turn-in and
/// reads the resulting committed state commitment. Deterministic: the real world's quest
/// cell reaches the byte-identical commitment after the same completion.
fn finalized_turnin_root() -> [u8; 32] {
    let (exec, cclerk, quest, _giver) = assemble(None);
    complete_quest(&exec, &cclerk, quest);
    exec.with_ledger_mut(|ledger| {
        ledger
            .get(&quest)
            .expect("quest present after turn-in")
            .state_commitment()
    })
}

/// A live two-cell quest-giver world: the shared executor ledger, the quest cell + the
/// giver cell, and the finalized quest root the giver's cross-cell grant pins.
pub struct QuestGiverWorld {
    exec: EmbeddedExecutor,
    cclerk: AppCipherclerk,
    quest: CellId,
    giver: CellId,
    grant_root: [u8; 32],
}

impl QuestGiverWorld {
    /// Deploy the world: assemble the quest + giver cells and install the giver's cross-cell
    /// grant pinned at the quest cell's post-turn-in finalized commitment.
    pub fn deploy() -> QuestGiverWorld {
        let grant_root = finalized_turnin_root();
        let (exec, cclerk, quest, giver) = assemble(Some(grant_root));
        QuestGiverWorld {
            exec,
            cclerk,
            quest,
            giver,
            grant_root,
        }
    }

    /// The quest-state cell id.
    pub fn quest(&self) -> CellId {
        self.quest
    }
    /// The quest-giver's grant cell id.
    pub fn giver(&self) -> CellId {
        self.giver
    }
    /// The finalized quest root the giver's cross-cell grant pins.
    pub fn grant_root(&self) -> [u8; 32] {
        self.grant_root
    }

    /// Read a cell's slot off the committed ledger.
    pub fn read(&self, cell: CellId, slot: usize) -> u64 {
        read_slot(&self.exec, cell, slot)
    }
    /// The quest cell's live committed state commitment (its finalized root right now).
    pub fn quest_root(&self) -> [u8; 32] {
        self.exec
            .with_ledger_mut(|l| l.get(&self.quest).map(|c| c.state_commitment()))
            .unwrap_or([0u8; 32])
    }

    /// Drive the whole quest to a turn-in on the quest cell (light every ward in order, then
    /// turn in). After this the quest cell is AT [`Self::grant_root`] and the giver grant can
    /// open.
    pub fn complete_the_quest(&self) {
        complete_quest(&self.exec, &self.cclerk, self.quest);
    }

    /// Drive only the first `n` steps of the quest (a partial, un-turned-in run) — for the
    /// non-vacuous "the grant is refused before the objective is done" leg.
    pub fn light_wards(&self, n: usize) {
        for k in 1..=n {
            let steps_done = self.read(self.quest, STEPS_DONE_SLOT as usize);
            issue(
                &self.exec,
                &self.cclerk,
                self.quest,
                &light_method(k),
                vec![
                    set_field(self.quest, step_slot(k) as usize, field_from_u64(1)),
                    set_field(
                        self.quest,
                        STEPS_DONE_SLOT as usize,
                        field_from_u64(steps_done + 1),
                    ),
                ],
                vec![],
            )
            .unwrap_or_else(|e| panic!("lighting ward {k} commits: {e}"));
        }
    }

    /// Attempt the quest-giver's grant — the CROSS-CELL gated action. Writes `grant_value`
    /// into the giver's `granted` slot, carrying the witness iff `with_witness`. The executor
    /// admits IFF the giver's `ObservedFieldEquals` passes: the quest cell is AT the grant
    /// root (turned in) AND `grant_value == quest.reward` AND the witness is present.
    pub fn grant(
        &self,
        grant_value: FieldElement,
        with_witness: bool,
    ) -> Result<TurnReceipt, String> {
        let blobs = if with_witness {
            vec![peer_finalized_witness(self.grant_root)]
        } else {
            vec![]
        };
        issue(
            &self.exec,
            &self.cclerk,
            self.giver,
            &grant_method(),
            vec![set_field(self.giver, GRANTED_SLOT as usize, grant_value)],
            blobs,
        )
    }

    /// The HONEST grant: value == the quest cell's reward (`1`), witness attached — what
    /// commits once the quest is really turned in.
    pub fn grant_honest(&self) -> Result<TurnReceipt, String> {
        self.grant(field_from_u64(REWARD_VALUE), true)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The giver's grant is a REAL cross-cell predicate on the giver cell: a `Predicate`
    /// program carrying exactly one `ObservedFieldEquals` naming the PEER quest cell + its
    /// `reward` slot at the finalized grant root. Proof it is a kernel predicate, not a host
    /// `if` — the giver reads the quest cell, not a self-reported flag.
    #[test]
    fn grant_is_a_real_cross_cell_observed_field_equals_on_the_quest() {
        let world = QuestGiverWorld::deploy();
        let program = world
            .exec
            .with_ledger_mut(|l| l.get(&world.giver).map(|c| c.program.clone()))
            .expect("giver cell present");
        let CellProgram::Predicate(constraints) = program else {
            panic!("the giver's program is a Predicate carrying the cross-cell grant");
        };
        let found = constraints.iter().any(|c| {
            matches!(
                c,
                StateConstraint::ObservedFieldEquals { source_cell, source_field, at_root, .. }
                    if *source_cell == *world.quest.as_bytes()
                        && *source_field == REWARD_SLOT
                        && *at_root == world.grant_root()
            )
        });
        assert!(
            found,
            "the giver gates on the PEER quest cell's reward at the finalized turn-in root; got {constraints:?}"
        );
        assert_ne!(world.quest(), world.giver(), "two genuinely distinct cells");
    }

    /// THE HARD GATE, refusal leg: the giver's grant is attempted BEFORE the quest is turned
    /// in. The quest cell's live commitment is not the grant root, so the executor's
    /// finalized-root authority has NO binding ⇒ the cross-cell read fails closed. A real
    /// executor refusal ACROSS cells; nothing commits (anti-ghost).
    #[test]
    fn grant_refused_until_the_quest_is_turned_in() {
        let world = QuestGiverWorld::deploy();

        // Only two of three wards lit — the errand is NOT turned in.
        world.light_wards(2);
        assert_eq!(
            world.read(world.quest(), REWARD_SLOT as usize),
            0,
            "no reward"
        );
        assert_ne!(
            world.quest_root(),
            world.grant_root(),
            "the quest is not at the turn-in root yet"
        );

        let refused = world.grant_honest();
        assert!(
            refused.is_err(),
            "the cross-cell grant must refuse before the quest is turned in, got {refused:?}"
        );
        assert_eq!(
            world.read(world.giver(), GRANTED_SLOT as usize),
            0,
            "anti-ghost: the giver granted nothing"
        );
    }

    /// THE HARD GATE, commit leg: complete + turn in the quest (real turns on the quest
    /// cell), then the giver grant COMMITS — its admission read the PEER quest cell's reward.
    /// A real cross-cell receipt whose admission depended on ANOTHER cell's completed state.
    #[test]
    fn grant_commits_after_the_quest_is_turned_in() {
        let world = QuestGiverWorld::deploy();
        world.complete_the_quest();
        assert_eq!(
            world.read(world.quest(), REWARD_SLOT as usize),
            REWARD_VALUE,
            "the quest is turned in (reward set)"
        );
        assert_eq!(
            world.quest_root(),
            world.grant_root(),
            "the quest cell is now AT the finalized turn-in root"
        );

        let granted = world
            .grant_honest()
            .expect("with the quest turned in + the witness, the giver grant opens");
        assert_eq!(
            world.read(world.giver(), GRANTED_SLOT as usize),
            REWARD_VALUE,
            "the giver handed over its reward, matching the quest's committed reward"
        );
        assert_ne!(granted.turn_hash, [0u8; 32], "a genuine committed grant");
    }

    /// FORGE 1 — a stripped witness. The quest is turned in (peer condition met), but the
    /// grant OMITS the Merkle-open witness. The gate fails closed.
    #[test]
    fn forged_grant_without_witness_fails_closed() {
        let world = QuestGiverWorld::deploy();
        world.complete_the_quest();
        let refused = world.grant(field_from_u64(REWARD_VALUE), false);
        assert!(
            refused.is_err(),
            "a stripped-witness cross-cell grant must fail closed, got {refused:?}"
        );
        assert_eq!(
            world.read(world.giver(), GRANTED_SLOT as usize),
            0,
            "nothing granted"
        );
    }

    /// FORGE 2 — a divergent value. The quest is turned in and the witness is attached, but
    /// the grant writes a value that does NOT match the quest cell's real reward. The
    /// `ObservedFieldEquals` mismatch tooth refuses — the local grant cannot diverge from the
    /// peer's finalized reward.
    #[test]
    fn forged_grant_with_divergent_value_is_refused() {
        let world = QuestGiverWorld::deploy();
        world.complete_the_quest();
        let refused = world.grant(field_from_u64(REWARD_VALUE + 41), true);
        assert!(
            refused.is_err(),
            "a divergent cross-cell grant value must be refused, got {refused:?}"
        );
        assert_eq!(
            world.read(world.giver(), GRANTED_SLOT as usize),
            0,
            "nothing granted"
        );
    }
}
