//! # `multicell` — a universe as a GRAPH of real cells, with a real CROSS-CELL gate
//!
//! The committed single-cell dungeon ([`crate`] root) proved single-cell mechanics
//! and named its ceiling precisely: every `StateConstraint` is checked against the
//! action's OWN target cell, so "room B opens because item A — living on a SEPARATE
//! cell — was taken" could not be a kernel predicate. It could only be host-side
//! sequencing (a client `if`), which is exactly the LARP the rebuild exists to kill.
//!
//! This module closes that ceiling on the real substrate. The world is a GRAPH of
//! real cells sharing ONE [`EmbeddedExecutor`] ledger:
//!
//! | cell | role | program (executor teeth) |
//! |------|------|--------------------------|
//! | [`SHORE`](World::shore) | room A — where the lantern lies | `None` (a room a player enters) |
//! | [`LANTERN`](World::lantern) | the ITEM — its OWN cell | `WriteOnce(OWNER)` — first-grabber-wins |
//! | [`STAIR`](World::stair) | room B — the GATED room | `Predicate([ObservedFieldEquals])` — the cross-cell gate |
//!
//! ## The cross-cell gate is a real executor predicate (not a host `if`)
//!
//! Room B's cell carries a [`CellProgram::Predicate`] with ONE tooth:
//! [`StateConstraint::ObservedFieldEquals`] naming the PEER cell (the lantern) and
//! its OWNER slot, at a finalized root [`World::gate_root`]. On every turn touching
//! room B, the verified executor:
//!
//! 1. builds a host [`FinalizedRootAuthority`] from the COMMITTED LEDGER — for the
//!    lantern's genuine current commitment it binds `(lantern, commitment, OWNER) ->
//!    owner_value` ([`build_finalized_root_authority`], `turn/src/executor/execute_tree.rs`);
//! 2. evaluates room B's `ObservedFieldEquals`: it admits IFF the authority confirms
//!    room B's declared `at_root` is the lantern's genuine finalized commitment AND
//!    `new[DOOR] == lantern.OWNER`, with the Merkle-open witness present at the
//!    bound `proof_witness_index`.
//!
//! The gate names item-A's **post-take finalized commitment** as its `at_root`
//! ([`World::gate_root`], computed once by [`finalized_take_root`]). So:
//!
//! * **before the lantern is taken** the lantern's live commitment is its genesis
//!   root, NOT the gate root ⇒ the authority has no binding for the gate root ⇒ the
//!   gate REFUSES (fail-closed; the peer condition is not met);
//! * **after a real `take` turn on the lantern's own cell** the lantern's live
//!   commitment IS the gate root ⇒ the authority binds `OWNER -> tag` ⇒ a room-B turn
//!   that sets `DOOR = tag` (with the witness attached) COMMITS;
//! * a **forged claim** — opening the door when the lantern is NOT at the gate root
//!   (never taken), or with a DOOR value diverging from the lantern's real owner, or
//!   with the witness stripped — is REFUSED. The authority is rebuilt from the LIVE
//!   ledger, never from the submitter's claim, so a self-fabricated cross-cell read
//!   cannot pass.
//!
//! ## Honest scope — the finality source
//!
//! In this in-process world the executor's "finalized view" of a peer cell is its
//! CURRENT committed ledger state (turns commit synchronously, so a peer's present
//! committed state IS finalized — the `monotone_terminal` already-committed fact the
//! atom may read for free). The gate is genuinely executor-enforced ACROSS cells and
//! fails closed. The Merkle-open witness blob is STRUCTURALLY required (its absence
//! refuses), but in the embedded host its bytes are not cryptographically re-opened
//! against `at_root` — the host instead RECOMPUTES the genuine `(cell, commitment,
//! field, value)` from its own committed ledger (exactly what a verifier does). A
//! PRODUCTION finality source (a cross-node finalized-root channel / the recursive
//! light client) adds one thing this test harness does not: it would furnish the peer
//! root from an INDEPENDENTLY finalized chain and verify the Merkle-open against it,
//! so a room-B cell could gate on a peer that lives on a DIFFERENT node's ledger. The
//! cross-cell PREDICATE, the fail-closed authority, and the ledger-recomputed value
//! are real here; the multi-NODE finalized-root transport is the named add.

use dregg_app_framework::{
    AgentCipherclerk, AppCipherclerk, AuthRequired, CellId, CellProgram, Effect, EmbeddedExecutor,
    FieldElement, StateConstraint, TurnReceipt,
};
use dregg_cell::{Cell, Permissions};
use dregg_turn::action::{WitnessBlob, WitnessKind};

/// The item's OWNER slot — a `take` stamps the taker's identity here (write-once).
pub const OWNER_SLOT: u8 = 0;
/// Room B's DOOR slot — the gated write, admitted only against the peer condition.
pub const DOOR_SLOT: u8 = 0;
/// Room A's PRESENCE slot — a player entering marks their presence (an ungated turn).
pub const PRESENCE_SLOT: usize = 0;

/// The federation the world's turns commit under (a fixed demo federation id).
const FEDERATION: [u8; 32] = [0x0D; 32];

/// A FIXED driver seed — so the dry-run that pins the finalized gate root
/// ([`finalized_take_root`]) and the real world share ONE driver identity. Without
/// this the driver's `actor_tag` (hence the lantern's post-take commitment) would
/// differ between the two, and the pinned gate root would never match the live one.
const DRIVER_SEED: [u8; 64] = [0x1D; 64];

/// A cell whose permissions gate nothing (every op `AuthRequired::None`) — the
/// room/item cells the driver acts on. The cross-cell AUTHORITY (does the driver
/// hold a cap to the target?) and the cross-cell GATE (`ObservedFieldEquals`) are the
/// load-bearing teeth; the per-cell permissions are opened so the gate, not a
/// signature-permission mismatch, is what a test observes.
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

/// The 32-byte identity a `take`/`open` write stamps — derived from the actor's cell
/// id so a genuine claim is distinguishable from an untouched (all-zero) slot and two
/// distinct actors write distinct, colliding values.
pub fn actor_tag(actor: CellId) -> FieldElement {
    let mut tag = [0u8; 32];
    let bytes = actor.as_bytes();
    let n = bytes.len().min(32);
    tag[..n].copy_from_slice(&bytes[..n]);
    tag[31] ^= 0x9D; // salt the low byte so the tag can never be the empty reading.
    tag
}

// ── Cell seeds (stable, so a re-deploy reproduces the same cell identities) ────────
const SHORE_SEED: u8 = 0x51;
const LANTERN_SEED: u8 = 0x52;
const STAIR_SEED: u8 = 0x53;
const SOURCE_FIELD: u8 = OWNER_SLOT; // room B reads the lantern's OWNER slot.

/// Assemble the world's cells on a fresh executor and grant the driver caps to reach
/// every cell. `gate_root` installs room B's cross-cell gate at that finalized peer
/// root; `None` leaves room B ungated (used by the dry-run that computes the root).
fn assemble(
    gate_root: Option<[u8; 32]>,
) -> (
    EmbeddedExecutor,
    AppCipherclerk,
    CellId,
    CellId,
    CellId,
    CellId,
) {
    let cclerk = AppCipherclerk::new(AgentCipherclerk::from_seed(DRIVER_SEED), FEDERATION);
    let exec = EmbeddedExecutor::new(&cclerk, "default");
    let driver = cclerk.cell_id();

    // Room A (the shore, where the lantern lies) — a plain room a player enters.
    let shore = world_cell(SHORE_SEED, CellProgram::None);
    // The ITEM — its OWN cell. Its OWNER slot is WRITE-ONCE: the first grabber wins,
    // a second conflicting claim is refused by the lantern's own kernel tooth.
    let lantern = world_cell(
        LANTERN_SEED,
        CellProgram::Predicate(vec![StateConstraint::WriteOnce { index: OWNER_SLOT }]),
    );
    // Room B (the gated stair). If we know the peer's finalized root, install the
    // CROSS-CELL gate: room B's DOOR may be written only to match the lantern's
    // finalized OWNER value, and only once the lantern actually reached `gate_root`.
    let stair_program = match gate_root {
        Some(at_root) => CellProgram::Predicate(vec![StateConstraint::ObservedFieldEquals {
            local_field: DOOR_SLOT,
            source_cell: *lantern.id().as_bytes(),
            source_field: SOURCE_FIELD,
            at_root,
            proof_witness_index: 0,
        }]),
        None => CellProgram::None,
    };
    let stair = world_cell(STAIR_SEED, stair_program);

    let shore_id = shore.id();
    let lantern_id = lantern.id();
    let stair_id = stair.id();

    exec.ensure_cell(shore).expect("shore cell inserts");
    exec.ensure_cell(lantern).expect("lantern cell inserts");
    exec.ensure_cell(stair).expect("stair cell inserts");

    // The driver's mandate: caps reaching every room/item (like the mud-dregg player
    // grants). Without a cap the executor refuses a move with `CapabilityNotHeld`; the
    // cross-cell GATE is a SEPARATE, additional tooth on top of the cap.
    exec.with_ledger_mut(|ledger| {
        if let Some(agent) = ledger.get_mut(&driver) {
            agent.capabilities.grant(shore_id, AuthRequired::None);
            agent.capabilities.grant(lantern_id, AuthRequired::None);
            agent.capabilities.grant(stair_id, AuthRequired::None);
        }
    });

    (exec, cclerk, driver, shore_id, lantern_id, stair_id)
}

/// Compute the lantern's **post-take finalized commitment** — the finalized peer root
/// room B's cross-cell gate pins. A throwaway world takes the lantern with a real
/// turn and reads the resulting committed state commitment. Deterministic: the real
/// world's lantern reaches the byte-identical commitment after the same `take`, so
/// pinning this value is pinning "the lantern, finalized, as-taken-by-this-driver".
///
/// This is the only piece the embedded harness precomputes; a production finality
/// source would instead surface this root from the committed chain / light client.
fn finalized_take_root() -> [u8; 32] {
    let (exec, cclerk, driver, _shore, lantern, _stair) = assemble(None);
    let tag = actor_tag(driver);
    issue(
        &exec,
        &cclerk,
        driver,
        lantern,
        "take",
        vec![set_field(lantern, OWNER_SLOT as usize, tag)],
        vec![],
    )
    .expect("the dry-run take commits");
    exec.with_ledger_mut(|ledger| {
        ledger
            .get(&lantern)
            .expect("lantern present after take")
            .state_commitment()
    })
}

/// A `SetField` effect on `cell`'s slot `index`.
fn set_field(cell: CellId, index: usize, value: FieldElement) -> Effect {
    Effect::SetField { cell, index, value }
}

/// Build, sign (over the attached witness blobs), wrap, and submit one turn — a real
/// cap-bounded turn the [`EmbeddedExecutor`] admits IFF every cap AND every touched
/// cell's program admits it. Returns the real [`TurnReceipt`] or the executor's
/// refusal reason (never a silent partial apply).
fn issue(
    exec: &EmbeddedExecutor,
    cclerk: &AppCipherclerk,
    _driver: CellId,
    target: CellId,
    method: &str,
    effects: Vec<Effect>,
    witness_blobs: Vec<WitnessBlob>,
) -> Result<TurnReceipt, String> {
    let mut action = cclerk.make_action(target, method, effects);
    action.witness_blobs = witness_blobs;
    // Re-sign AFTER attaching the witness (the signature covers `Action::hash`, which
    // covers `witness_blobs` — a witness bolted on post-signing would be a bad sig).
    let action = cclerk.sign_action(action);
    let turn = cclerk.make_turn(action);
    exec.submit_turn(&turn).map_err(|e| e.to_string())
}

/// The Merkle-open witness of item-A's finalized state that the gated room-B turn
/// carries. Referenced by room B's `ObservedFieldEquals { proof_witness_index: 0 }`;
/// its ABSENCE fails the gate closed (a stripped proof cannot open the cross-cell
/// read). In the embedded host the host authority recomputes the genuine value from
/// the committed ledger, so the blob is the structural anti-strip carrier; a
/// production finalized-root channel verifies its bytes against the peer root.
pub fn peer_finalized_witness(at_root: [u8; 32]) -> WitnessBlob {
    WitnessBlob::new(WitnessKind::MerklePath, at_root.to_vec())
}

/// A live multi-cell world: the shared executor ledger + the graph of cell ids + the
/// finalized peer root room B's cross-cell gate pins.
pub struct World {
    exec: EmbeddedExecutor,
    cclerk: AppCipherclerk,
    driver: CellId,
    shore: CellId,
    lantern: CellId,
    stair: CellId,
    gate_root: [u8; 32],
}

impl World {
    /// Deploy the world: assemble the cell graph and install room B's cross-cell gate
    /// pinned at the lantern's post-take finalized commitment.
    pub fn deploy() -> World {
        let gate_root = finalized_take_root();
        let (exec, cclerk, driver, shore, lantern, stair) = assemble(Some(gate_root));
        World {
            exec,
            cclerk,
            driver,
            shore,
            lantern,
            stair,
            gate_root,
        }
    }

    /// The acting player (the turn agent) cell id.
    pub fn driver(&self) -> CellId {
        self.driver
    }
    /// Room A (the shore) cell id.
    pub fn shore(&self) -> CellId {
        self.shore
    }
    /// The item (lantern) cell id — its OWN cell.
    pub fn lantern(&self) -> CellId {
        self.lantern
    }
    /// Room B (the gated stair) cell id.
    pub fn stair(&self) -> CellId {
        self.stair
    }
    /// The finalized peer root room B's cross-cell gate pins.
    pub fn gate_root(&self) -> [u8; 32] {
        self.gate_root
    }
    /// The identity a `take`/`open` write stamps for this driver.
    pub fn tag(&self) -> FieldElement {
        actor_tag(self.driver)
    }

    /// Read a cell's slot from the committed ledger (`None` if the cell is absent).
    pub fn read(&self, cell: CellId, slot: usize) -> Option<FieldElement> {
        self.exec.cell_state(cell).map(|s| s.fields[slot])
    }
    /// The lantern's live committed state commitment (its finalized root right now).
    pub fn lantern_root(&self) -> [u8; 32] {
        self.exec
            .with_ledger_mut(|l| l.get(&self.lantern).map(|c| c.state_commitment()))
            .unwrap_or([0u8; 32])
    }

    /// Enter room A (the shore) — an ungated turn marking the driver's presence. A
    /// real cap-bounded turn on room A's OWN cell.
    pub fn enter_shore(&self) -> Result<TurnReceipt, String> {
        let tag = self.tag();
        issue(
            &self.exec,
            &self.cclerk,
            self.driver,
            self.shore,
            "enter",
            vec![set_field(self.shore, PRESENCE_SLOT, tag)],
            vec![],
        )
    }

    /// Take the lantern — a real turn on the ITEM's OWN cell, stamping the driver's
    /// identity into its WRITE-ONCE owner slot. This is the peer state room B's gate
    /// observes; after it, the lantern's finalized commitment IS [`Self::gate_root`].
    pub fn take_lantern(&self) -> Result<TurnReceipt, String> {
        let tag = self.tag();
        issue(
            &self.exec,
            &self.cclerk,
            self.driver,
            self.lantern,
            "take",
            vec![set_field(self.lantern, OWNER_SLOT as usize, tag)],
            vec![],
        )
    }

    /// A rival's conflicting claim on the lantern — a SECOND, distinct owner value.
    /// The lantern's own `WriteOnce` tooth refuses it (first-grabber-wins): a per-cell
    /// executor refusal on the item's OWN cell. (Genuinely-CONCURRENT divergent
    /// claims are merged settlement-soundly by `starbridge_v2::branch_stitch_session`
    /// — the mud-dregg precedent — where a contested `take` is a real `#`-conflict;
    /// this drives the serialized WriteOnce tooth, the primitive that conflict rides.)
    pub fn rival_take_lantern(&self) -> Result<TurnReceipt, String> {
        let mut rival_tag = self.tag();
        rival_tag[0] ^= 0xFF; // a DIFFERENT owner value — a rival's distinct claim.
        issue(
            &self.exec,
            &self.cclerk,
            self.driver,
            self.lantern,
            "take",
            vec![set_field(self.lantern, OWNER_SLOT as usize, rival_tag)],
            vec![],
        )
    }

    /// Attempt to open room B's gated stair — the CROSS-CELL gated action. Writes
    /// `door_value` into room B's DOOR slot, carrying `witness` iff `with_witness`.
    /// The executor admits IFF room B's `ObservedFieldEquals` passes: the lantern is
    /// AT the gate root AND `door_value == lantern.OWNER` AND the witness is present.
    pub fn open_stair(
        &self,
        door_value: FieldElement,
        with_witness: bool,
    ) -> Result<TurnReceipt, String> {
        let blobs = if with_witness {
            vec![peer_finalized_witness(self.gate_root)]
        } else {
            vec![]
        };
        issue(
            &self.exec,
            &self.cclerk,
            self.driver,
            self.stair,
            "open",
            vec![set_field(self.stair, DOOR_SLOT as usize, door_value)],
            blobs,
        )
    }

    /// The HONEST open: door value == the lantern's owner tag, witness attached. This
    /// is what commits once the lantern is really taken.
    pub fn open_stair_honest(&self) -> Result<TurnReceipt, String> {
        self.open_stair(self.tag(), true)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The gate is a REAL cross-cell predicate on room B's cell: a `Predicate` program
    /// carrying exactly one `ObservedFieldEquals` naming the PEER (lantern) cell + its
    /// OWNER slot at the finalized gate root. Proof it is a kernel predicate, not a
    /// host `if`.
    #[test]
    fn gate_is_a_real_cross_cell_observed_field_equals_on_the_peer() {
        let world = World::deploy();
        let program = world
            .exec
            .with_ledger_mut(|l| l.get(&world.stair).map(|c| c.program.clone()))
            .expect("stair cell present");
        let CellProgram::Predicate(constraints) = program else {
            panic!("room B's program is a Predicate carrying the cross-cell gate");
        };
        let found = constraints.iter().any(|c| {
            matches!(
                c,
                StateConstraint::ObservedFieldEquals { source_cell, source_field, at_root, .. }
                    if *source_cell == *world.lantern.as_bytes()
                        && *source_field == SOURCE_FIELD
                        && *at_root == world.gate_root()
            )
        });
        assert!(
            found,
            "room B gates on the PEER lantern cell's OWNER at the finalized root; got {constraints:?}"
        );
        // The three cells are genuinely distinct real cells (a graph, not one cell).
        assert_ne!(world.shore(), world.lantern());
        assert_ne!(world.lantern(), world.stair());
        assert_ne!(world.shore(), world.stair());
    }

    /// THE HARD GATE, refusal leg: room B's stair is opened BEFORE the lantern is
    /// taken. The lantern's live commitment is its genesis root, not the gate root, so
    /// the executor's finalized-root authority has NO binding for the gate root ⇒ the
    /// cross-cell read fails closed. A real executor refusal ACROSS cells; nothing
    /// commits (anti-ghost: room B's DOOR stays empty).
    #[test]
    fn cross_cell_gate_refuses_until_peer_item_is_taken() {
        let world = World::deploy();
        world
            .enter_shore()
            .expect("entering room A is ungated and commits");

        // The lantern is NOT taken — its owner slot is empty, its live root is genesis.
        assert_eq!(
            world.read(world.lantern(), OWNER_SLOT as usize),
            Some([0u8; 32])
        );
        assert_ne!(
            world.lantern_root(),
            world.gate_root(),
            "lantern is not at the gate root yet"
        );

        // Drive the cross-cell gated open with the honest value + witness — REFUSED,
        // because the peer condition (lantern taken → at the gate root) is not met.
        let refused = world.open_stair_honest();
        assert!(
            refused.is_err(),
            "the cross-cell gate must refuse before the peer item is taken, got {refused:?}"
        );

        // Anti-ghost: the refused cross-cell turn committed NOTHING on room B.
        assert_eq!(
            world.read(world.stair(), DOOR_SLOT as usize),
            Some([0u8; 32]),
            "room B's door did not open (anti-ghost)"
        );
    }

    /// THE HARD GATE, commit leg: take the lantern on its OWN cell (a real turn), then
    /// open room B's stair. Now the lantern's live commitment IS the gate root, the
    /// authority binds OWNER -> tag, and the room-B turn setting DOOR == tag COMMITS.
    /// A real cross-cell TurnReceipt whose admission depended on ANOTHER cell's state.
    #[test]
    fn cross_cell_gate_commits_after_peer_item_is_taken_with_witness() {
        let world = World::deploy();
        world.enter_shore().expect("enter room A");

        let take = world
            .take_lantern()
            .expect("taking the lantern on its own cell commits");
        assert_eq!(
            world.read(world.lantern(), OWNER_SLOT as usize),
            Some(world.tag())
        );
        assert_eq!(
            world.lantern_root(),
            world.gate_root(),
            "the lantern is now AT the finalized gate root"
        );

        // The cross-cell gated open now commits — its admission read the PEER cell.
        let open = world
            .open_stair_honest()
            .expect("with the peer item taken + the witness, the gate opens");
        assert_eq!(
            world.read(world.stair(), DOOR_SLOT as usize),
            Some(world.tag()),
            "room B's door opened to the lantern's owner"
        );

        // Real receipts on DISTINCT cells (a cross-cell chain, not one serial writer).
        assert_ne!(take.turn_hash, [0u8; 32]);
        assert_ne!(open.turn_hash, [0u8; 32]);
        assert_ne!(take.turn_hash, open.turn_hash);
    }

    /// FORGE 1 — a stripped witness. After the lantern is taken, the peer condition IS
    /// met, but the gated open OMITS the Merkle-open witness at `proof_witness_index`.
    /// The gate fails closed: a stripped proof cannot open the cross-cell read.
    #[test]
    fn forged_open_without_witness_fails_closed() {
        let world = World::deploy();
        world.take_lantern().expect("take the lantern");
        assert_eq!(world.lantern_root(), world.gate_root());

        let refused = world.open_stair(world.tag(), false); // honest value, NO witness.
        assert!(
            refused.is_err(),
            "a stripped-witness cross-cell open must fail closed, got {refused:?}"
        );
        assert_eq!(
            world.read(world.stair(), DOOR_SLOT as usize),
            Some([0u8; 32]),
            "door stayed shut"
        );
    }

    /// FORGE 2 — a divergent value. The lantern is taken (peer condition met) and the
    /// witness is attached, but the open tries to write a DOOR value that does NOT
    /// match the lantern's real owner. The `ObservedFieldEquals` mismatch tooth refuses
    /// — the local field cannot diverge from the peer's finalized value.
    #[test]
    fn forged_open_with_divergent_value_is_refused() {
        let world = World::deploy();
        world.take_lantern().expect("take the lantern");

        let mut wrong = world.tag();
        wrong[1] ^= 0xAA; // a value the lantern's owner slot never holds.
        let refused = world.open_stair(wrong, true); // witness present, WRONG value.
        assert!(
            refused.is_err(),
            "a divergent cross-cell value must be refused, got {refused:?}"
        );
        assert_eq!(
            world.read(world.stair(), DOOR_SLOT as usize),
            Some([0u8; 32]),
            "door stayed shut"
        );
    }

    /// The item cell's OWN first-grabber tooth: the lantern's `WriteOnce` OWNER slot
    /// admits the first take (0 -> tag) and REFUSES a second, conflicting claim
    /// (tag -> rival) — a real per-cell executor refusal on the item's own cell. The
    /// multiplayer contested resource, serialized; genuinely-concurrent divergent
    /// claims merge via `branch_stitch_session` (named in `rival_take_lantern`).
    #[test]
    fn item_writeonce_first_grabber_wins() {
        let world = World::deploy();
        let first = world
            .take_lantern()
            .expect("the first grabber's take commits");
        assert_ne!(first.turn_hash, [0u8; 32]);
        assert_eq!(
            world.read(world.lantern(), OWNER_SLOT as usize),
            Some(world.tag())
        );

        let refused = world.rival_take_lantern();
        assert!(
            refused.is_err(),
            "a rival's conflicting claim is refused by WriteOnce, got {refused:?}"
        );
        assert_eq!(
            world.read(world.lantern(), OWNER_SLOT as usize),
            Some(world.tag()),
            "anti-ghost: the lantern still belongs to the first grabber"
        );
    }
}
