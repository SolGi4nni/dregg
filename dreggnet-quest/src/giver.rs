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
    let reward_gate = vec![
        StateConstraint::FieldGte {
            index: STEPS_DONE_SLOT,
            value: field_from_u64(TURN_IN_THRESHOLD),
        },
        StateConstraint::FieldEquals {
            index: REWARD_SLOT,
            value: field_from_u64(REWARD_VALUE),
        },
        StateConstraint::WriteOnce { index: REWARD_SLOT },
    ];
    // THE SLOT-BOUND REWARD GATE — the tooth that makes the steps-done floor real.
    //
    // The `turn_in` `MethodIs` case gates only turns that PRESENT the turn-in method. But the
    // executor is open: a client can staple `SetField(reward, 1)` onto ANY other method's turn (a
    // legitimate `light_method(k)`), where no `turn_in` case matches, this cell has no `Always`
    // invariant on `reward`, and `reward` is still zero — so the reward lands with NO steps-done
    // floor. `SlotChanged{reward}` binds the floor to the WRITE; the evaluator runs EVERY matching
    // case (`cell/src/program/eval.rs:104-120`), so it composes with the authoring method's
    // constraints. `SlotChanged` is NOT method-dispatching, so default-deny is unaffected.
    cases.push(TransitionCase {
        guard: TransitionGuard::SlotChanged { index: REWARD_SLOT },
        constraints: reward_gate.clone(),
    });
    cases.push(TransitionCase {
        guard: TransitionGuard::MethodIs {
            method: symbol(&turn_in_method()),
        },
        constraints: reward_gate,
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
    Effect::SetField {
        cell,
        index: index as u64,
        value,
    }
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

// ── The FACTION-gated quest-giver: the giver opens on the REAL faction cell ─────────
//
// The reconciliation the saga names: the quest-giver's start opens ONLY when the player's
// standing with the Embers clears the faction threshold — read off dreggnet-faction's REAL
// committed faction cell through its CANONICAL SHARED READER
// ([`dreggnet_faction::standing::read_standing`] / [`FactionStanding::content_available`]),
// NOT a locally re-authored mirror. The standing is itself kernel-enforced, un-fakeable
// committed cell state on dreggnet-faction's own [`WorldCell`]: a `Monotonic` `rep_embers`
// ratchet (standing is never un-earned), a `FieldGte(rep_embers, `[`REP_THRESHOLD`]`)`-gated
// `WriteOnce(embers_quest)` trial, and a `WriteOnce(embers_betrayed)` betrayal seal. The
// giver consumes that standing as its gate, with every slot resolved BY NAME
// (`rep_embers` / `embers_quest` / `embers_betrayed`, via the roster's `rep_var` etc.), so
// the gate can never be pointed at the wrong slot — the SILENT-INVERSION hazard a hardcoded
// index carries (alphabetical slot 1 is `embers_quest`, slot 2 `embers_betrayed`, not `rep`)
// is structurally excluded.
//
// ## Honest scope — where the un-fakeability lives
//
// dreggnet-faction's [`WorldCell`] encapsulates its own executor, so the giver cannot pin an
// in-executor cross-cell [`ObservedFieldEquals`](dregg_app_framework::StateConstraint::ObservedFieldEquals)
// against it (that needs both cells on ONE ledger, which the `WorldCell` boundary precludes).
// The gate is therefore a HOST read of the real committed faction cell via the canonical
// reader — but the standing it reads is un-fakeable KERNEL state: you cannot reach
// `rep_embers >= REP_THRESHOLD` without real `Monotonic`-ratcheted pledge turns the faction
// executor admits, and a betrayal permanently seals the content. This is exactly the consumer
// pattern [`dreggnet_faction::standing`] was built for (its doc names `dreggnet-quest` as the
// gap this closes) — the giver reads GENUINE standing, never a self-reported flag and never a
// re-guessed slot. The previous cross-cell predicate gated at the kernel but against a
// FABRICATED faction cell; this gates on the REAL one.

use dreggnet_faction::standing::read_standing;
use dreggnet_faction::{
    FactionDef, FactionLines, FactionStanding, REP_THRESHOLD, ROOM_HALL as FACTION_HALL, Roster,
};
use spween::{Choice, Scene};
use spween_dregg::WorldCell;

/// The value the giver's `granted` slot lands at once the quest-start opens — the
/// content-availability marker (kept as the public marker the composing crates read).
pub const EMBER_QUEST_VALUE: u64 = 1;

/// The Embers' stable roster key — the faction whose standing gates the Descent quest-start.
/// Names the slot family (`rep_embers`, `embers_quest`, `embers_betrayed`) the reader resolves.
const FACTION_KEY: &str = "embers";
/// A fixed seed for the deterministic faction world (re-deploy reproduces identity + hashes).
const FACTION_SEED: u8 = 0x73;
/// The giver cell seed (distinct from the quest / quest-giver seeds).
const FGIVER_SEED: u8 = 0x74;

/// Assemble the giver-only executor: one open giver cell whose `granted` write is a real
/// committed turn (the FACTION gate is the host `content_available()` read, documented above —
/// the giver cell itself is ungated at the executor, so the standing read is the sole gate).
fn assemble_giver_only() -> (EmbeddedExecutor, AppCipherclerk, CellId) {
    let cclerk = AppCipherclerk::new(AgentCipherclerk::from_seed(DRIVER_SEED), FEDERATION);
    let exec = EmbeddedExecutor::new(&cclerk, "default");
    let driver = cclerk.cell_id();

    let giver = world_cell(FGIVER_SEED, CellProgram::None);
    let giver_id = giver.id();
    exec.ensure_cell(giver).expect("giver cell inserts");

    exec.with_ledger_mut(|ledger| {
        if let Some(agent) = ledger.get_mut(&driver) {
            agent.capabilities.grant(giver_id, AuthRequired::None);
        }
    });

    (exec, cclerk, giver_id)
}

/// A live **faction-gated quest-giver** world: the REAL dreggnet-faction cell (its standing
/// kernel-enforced) + a giver cell whose grant opens ONLY once the player's Ember standing is
/// available, read off the real cell via the canonical shared reader (every slot by NAME).
pub struct FactionGatedGiverWorld {
    /// The REAL dreggnet-faction cell — `rep_embers` / `embers_quest` / `embers_betrayed` are
    /// kernel-enforced committed state here; the player earns standing through faction's own
    /// pledge/trial flow ([`Self::pledge`] / [`Self::undertake_trial`]).
    faction: WorldCell,
    /// The canonical Ashenmoor roster (names, threshold, the `rep_var`/`quest_var` slot naming
    /// the reader resolves by).
    roster: Roster,
    /// The generated faction scene — to name a [`Choice`] when driving a real faction turn.
    scene: Scene,
    /// The giver cell's executor (its `granted` write is a real committed turn).
    exec: EmbeddedExecutor,
    cclerk: AppCipherclerk,
    giver: CellId,
}

impl FactionGatedGiverWorld {
    /// Deploy the world: the REAL faction cell (deterministic in [`FACTION_SEED`]) + the giver
    /// cell. The faction begins unaligned (rep 0), so the quest-start is deployed CLOSED.
    pub fn deploy() -> FactionGatedGiverWorld {
        let roster = Roster::ashenmoor();
        let faction = roster.deploy(FACTION_SEED);
        let scene = roster.scene();
        let (exec, cclerk, giver) = assemble_giver_only();
        FactionGatedGiverWorld {
            faction,
            roster,
            scene,
            exec,
            cclerk,
            giver,
        }
    }

    /// The Embers' [`FactionDef`] (its threshold + slot naming) — the reader's coordinate.
    fn def(&self) -> &FactionDef {
        self.roster
            .faction(FACTION_KEY)
            .expect("the Embers are in the Ashenmoor roster")
    }
    /// The Embers' hall line block (pledge / trial / betray … indices).
    fn lines(&self) -> FactionLines {
        self.roster.lines(FACTION_KEY)
    }
    /// Name a `Choice` in the faction hall for a direct-executor turn.
    fn faction_choice(&self, index: usize) -> Choice {
        dungeon_on_dregg::choice_at(&self.scene, FACTION_HALL, index)
    }

    /// **The player's REAL Ember standing**, read off the committed faction cell through
    /// dreggnet-faction's canonical shared reader — every slot resolved BY NAME (`rep_embers`,
    /// `embers_quest`, `embers_betrayed`). The typed projection the gate reads.
    pub fn standing(&self) -> FactionStanding {
        read_standing(&self.faction, self.def())
    }

    /// The faction cell id.
    pub fn faction_cell(&self) -> CellId {
        self.faction.cell_id()
    }
    /// The quest-giver's grant cell id.
    pub fn giver(&self) -> CellId {
        self.giver
    }
    /// Read the giver cell's committed slot off the ledger (the composing crates read
    /// `read(giver(), GRANTED_SLOT)` to observe whether the quest-start has opened).
    pub fn read(&self, cell: CellId, slot: usize) -> u64 {
        read_slot(&self.exec, cell, slot)
    }

    /// Drive ONE real Ember pledge on the faction cell (`rep_embers += 1`, `Monotonic`). Below
    /// the threshold the content is not yet available — the non-vacuous refusal leg.
    pub fn pledge(&self) -> Result<(), String> {
        let ln = self.lines().pledge;
        self.faction
            .apply_choice(FACTION_HALL, ln, &self.faction_choice(ln))
            .map(|_| ())
            .map_err(|e| e.to_string())
    }

    /// Attempt the real Ember trial (`embers_quest = 1`) — gated `FieldGte(rep_embers,
    /// REP_THRESHOLD)` on the faction cell. Refused below the threshold, commits once it clears.
    pub fn undertake_trial(&self) -> Result<(), String> {
        let ln = self.lines().trial;
        self.faction
            .apply_choice(FACTION_HALL, ln, &self.faction_choice(ln))
            .map(|_| ())
            .map_err(|e| e.to_string())
    }

    /// Betray the Embers (`embers_betrayed = 1`, a `WriteOnce` seal on the faction cell) — for
    /// the anti-inversion leg: a betrayer's standing is NOT available whatever the flag's slot.
    pub fn betray(&self) -> Result<(), String> {
        let ln = self.lines().betray;
        self.faction
            .apply_choice(FACTION_HALL, ln, &self.faction_choice(ln))
            .map(|_| ())
            .map_err(|e| e.to_string())
    }

    /// Earn Ember standing to the threshold on the REAL faction cell: pledge [`REP_THRESHOLD`]
    /// times (each a `Monotonic` `+1`) then undertake the trial. After this the content is
    /// available and the giver can open.
    pub fn earn_standing(&self) {
        for _ in 0..REP_THRESHOLD {
            self.pledge().expect("a real Ember pledge commits");
        }
        self.undertake_trial()
            .expect("the Ember trial commits once rep clears the threshold");
    }

    /// **THE FACTION GATE** — the quest-giver opens the Descent-quest start IFF the player's REAL
    /// Ember standing is available ([`FactionStanding::content_available`] = `rep_embers >=
    /// REP_THRESHOLD` AND never betrayed), read off the committed faction cell via the canonical
    /// reader. When it opens the giver commits a real `granted` write; when it is closed the
    /// grant fails and nothing commits (anti-ghost).
    pub fn grant(&self, grant_value: FieldElement) -> Result<TurnReceipt, String> {
        let standing = self.standing();
        if !standing.content_available() {
            return Err(format!(
                "the quest-start is refused: Ember standing not available (rep {} < {}, betrayed {})",
                standing.rep, standing.threshold, standing.betrayed
            ));
        }
        issue(
            &self.exec,
            &self.cclerk,
            self.giver,
            &grant_method(),
            vec![set_field(self.giver, GRANTED_SLOT as usize, grant_value)],
            vec![],
        )
    }

    /// The HONEST grant: value == the faction content-availability marker (`1`) — what commits
    /// once real Ember standing is earned.
    pub fn grant_honest(&self) -> Result<TurnReceipt, String> {
        self.grant(field_from_u64(EMBER_QUEST_VALUE))
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

    // ── The FACTION-GATED giver: opens on the REAL, name-resolved Ember standing ──

    /// THE FACTION -> QUEST GATE, threshold both ways (non-vacuous, resolved BY NAME): a player
    /// BELOW the rep threshold is REFUSED the quest-start; a player who earns REAL Ember rep to
    /// the threshold — through dreggnet-faction's OWN pledge flow, a `Monotonic`-ratcheted turn
    /// the faction executor admits — is GRANTED it. The standing is asserted off the real faction
    /// cell via [`read_standing`], every slot resolved by name (no hardcoded index, no mirror).
    #[test]
    fn faction_gate_opens_only_at_real_rep_threshold() {
        let world = FactionGatedGiverWorld::deploy();

        // Fresh: rep 0 (read off the real cell by name), nothing available.
        assert_eq!(world.standing().rep, 0, "you arrive unaffiliated");
        assert!(!world.standing().content_available(), "no standing yet");
        assert!(
            world.grant_honest().is_err(),
            "a no-rep player's quest-start is refused"
        );
        assert_eq!(
            world.read(world.giver(), GRANTED_SLOT as usize),
            0,
            "anti-ghost: nothing granted"
        );

        // One real pledge — rep 1, still BELOW REP_THRESHOLD (2): still refused.
        world.pledge().expect("a real Ember pledge commits");
        assert_eq!(
            world.standing().rep,
            1,
            "rep_embers read by name off the real cell"
        );
        assert!(
            world.grant_honest().is_err(),
            "still below the threshold — the start stays closed"
        );
        assert_eq!(
            world.read(world.giver(), GRANTED_SLOT as usize),
            0,
            "anti-ghost: still nothing granted"
        );

        // Second real pledge — rep 2 == REP_THRESHOLD: the content is available, the start opens.
        world.pledge().expect("the second pledge commits");
        assert_eq!(
            world.standing().rep,
            REP_THRESHOLD,
            "rep at the threshold (by name)"
        );
        assert!(
            world.standing().content_available(),
            "standing now available"
        );
        world
            .grant_honest()
            .expect("the quest-start opens on REAL earned Ember standing");
        assert_eq!(
            world.read(world.giver(), GRANTED_SLOT as usize),
            EMBER_QUEST_VALUE,
            "the Descent-quest is started, matching the faction's committed standing"
        );
    }

    /// THE ANTI-INVERSION LEG: a player who BETRAYED the Embers (`embers_betrayed` set) but holds
    /// LOW rep is REFUSED the quest-start — proving the gate reads the REP slot (`rep_embers`),
    /// not the betrayal/unlock flag. A naive repoint of the old hardcoded indices at the real cell
    /// would read `embers_betrayed` (alphabetical slot 2) as the open-signal and OPEN for a
    /// betrayer; the name-resolved gate (`content_available()` = rep >= threshold AND not betrayed)
    /// REFUSES. Every slot is read by NAME off the real committed faction cell.
    #[test]
    fn faction_gate_refuses_a_betrayer_the_gate_is_not_inverted() {
        let world = FactionGatedGiverWorld::deploy();

        // Betray with no rep: embers_betrayed = 1 (a WriteOnce seal), rep_embers still 0.
        world
            .betray()
            .expect("betraying the Embers commits a WriteOnce seal on the real cell");
        let st = world.standing();
        assert!(
            st.betrayed,
            "the betrayal is remembered on the real cell (by name)"
        );
        assert_eq!(
            st.rep, 0,
            "rep_embers is still zero — the betrayal flag is NOT rep"
        );
        assert!(
            !st.content_available(),
            "a betrayer's content is not available"
        );
        assert!(
            world.grant_honest().is_err(),
            "a betrayer's quest-start is REFUSED — the gate is not inverted onto the betrayal flag"
        );
        assert_eq!(
            world.read(world.giver(), GRANTED_SLOT as usize),
            0,
            "anti-ghost: the betrayer started nothing"
        );
    }

    /// THE BETRAYAL SEAL bites even at QUALIFYING rep: a player who earns rep to the threshold AND
    /// THEN betrays is STILL refused. The gate is not merely `rep_embers >= threshold` (which now
    /// holds) — it honours the `WriteOnce` betrayal seal the real faction cell carries. A sharper
    /// proof the READ is the real cell's `content_available`, not a bare rep read nor an inverted
    /// flag: the ONLY difference from the granted case is the committed betrayal on the real cell.
    #[test]
    fn faction_gate_refuses_a_high_rep_betrayer() {
        let world = FactionGatedGiverWorld::deploy();
        world.pledge().expect("pledge 1");
        world.pledge().expect("pledge 2");
        assert_eq!(world.standing().rep, REP_THRESHOLD, "rep at the threshold");
        assert!(
            world.standing().content_available(),
            "available BEFORE the betrayal (the non-vacuous baseline)"
        );

        world.betray().expect("betray the Embers");
        let st = world.standing();
        assert!(
            st.betrayed && st.rep >= st.threshold,
            "high rep AND betrayed — the seal must still bite"
        );
        assert!(
            !st.content_available(),
            "the betrayal seal closes the content despite qualifying rep"
        );
        assert!(
            world.grant_honest().is_err(),
            "a high-rep betrayer's quest-start is still refused"
        );
        assert_eq!(
            world.read(world.giver(), GRANTED_SLOT as usize),
            0,
            "anti-ghost: nothing granted"
        );
    }

    /// The giver consumes dreggnet-faction's CANONICAL SHARED READER over the REAL faction cell:
    /// after earning standing through the real pledge + trial flow, [`read_standing`] reports the
    /// standing (rep at the threshold, trial unlocked, never betrayed) resolved BY NAME, and the
    /// quest-start is open. Proof the mirror is gone — the standing comes off dreggnet-faction's
    /// own committed cell, not a re-authored program.
    #[test]
    fn earned_standing_opens_the_start_via_the_canonical_reader() {
        let world = FactionGatedGiverWorld::deploy();
        world.earn_standing();

        let st = world.standing();
        assert_eq!(st.rep, REP_THRESHOLD, "rep_embers earned (by name)");
        assert!(
            st.unlocked,
            "embers_quest unlocked by the REAL trial turn (by name)"
        );
        assert!(!st.betrayed, "not betrayed");
        assert!(st.content_available(), "the canonical gate is open");

        world
            .grant_honest()
            .expect("earning real Ember standing opens the quest-giver");
        assert_eq!(
            world.read(world.giver(), GRANTED_SLOT as usize),
            EMBER_QUEST_VALUE,
            "the quest-start is open on genuine, name-resolved faction standing"
        );
    }

    /// THE SLOT-BOUND REWARD TOOTH (the falsifier for a real cell-layer hole): a `reward` write
    /// STAPLED onto a DIFFERENT method's turn cannot mint the reward without the steps-done floor.
    ///
    /// Before the `SlotChanged{reward}` case existed, the turn-in floor lived ONLY on the `turn_in`
    /// case, and (no `Always`, `reward` still zero) a `SetField(reward, 1)` stapled onto a
    /// legitimate `light_method(1)` turn landed the reward with `steps_done == 1 < TURN_IN_THRESHOLD`.
    #[test]
    fn a_stapled_reward_cannot_ride_a_ward_lighting_turn() {
        let world = QuestGiverWorld::deploy();
        let staple = issue(
            &world.exec,
            &world.cclerk,
            world.quest,
            &light_method(1),
            vec![
                set_field(world.quest, step_slot(1) as usize, field_from_u64(1)),
                set_field(world.quest, STEPS_DONE_SLOT as usize, field_from_u64(1)),
                set_field(
                    world.quest,
                    REWARD_SLOT as usize,
                    field_from_u64(REWARD_VALUE),
                ),
            ],
            vec![],
        );
        assert!(
            staple.is_err(),
            "a reward stapled onto a ward-lighting turn must be REFUSED (steps_done 1 < {TURN_IN_THRESHOLD}); got {staple:?}"
        );
        assert_eq!(
            world.read(world.quest(), REWARD_SLOT as usize),
            0,
            "anti-ghost: no forged reward landed"
        );
        // THE GATE IS A FLOOR, NOT A BAN: the honest completion still turns in the reward.
        world.complete_the_quest();
        assert_eq!(
            world.read(world.quest(), REWARD_SLOT as usize),
            REWARD_VALUE,
            "a legitimately-completed quest still mints the reward"
        );
    }
}
