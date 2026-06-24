//! # mud — a rich, GM-coordinated living MUD as pure deos substance.
//!
//! A MUD has always had a *server somewhere* with godlike authority over the world —
//! it spawns rooms, moves NPCs, levels characters, opens dungeon instances. Here that
//! server is the **gamemaster cell**: a sovereign principal that holds BROAD caps over
//! every game cell, and players are cap-CONSTRAINED principals that hold NARROW caps
//! (their own character, the rooms they can reach). The asymmetry is the point — and
//! unlike every prior MUD, the GM's omnipotence is *explicit and accountable*: every
//! GM orchestration is a real cap-gated verified turn leaving a [`TurnReceipt`].
//!
//! Nothing here is bespoke gameplay code in the executor. The MUD *is* cells + caps +
//! turns:
//!
//!   - **The map** is the ocap graph of room-cells. A room is a cell; an *exit* is a
//!     capability edge from one room to another. Who can navigate where = the
//!     reachability closure of a principal's c-list ([`Frustum`]/`OcapGraph`). Moving
//!     a character is granting it the cap to the destination room — a verified turn.
//!   - **Characters** are player cells. Stats (HP, XP, LEVEL, ATTACK) live in the
//!     cell's state field slots.
//!   - **Leveling** is a gated turn: when XP crosses the threshold, a LEVEL-UP turn
//!     mutates the character cell. A player can grind XP (act on its own character);
//!     it CANNOT set its level arbitrarily — that is a GM-authority field.
//!   - **Reactions** are the GM coordinating the world's response: a player acts, and
//!     the GM fires a *reactive* turn on an NPC/environment cell (the transition-shape
//!     follow-up the reactive affordance models). The NPC reacts because the GM holds
//!     the broad cap; the player could not have fired that turn.
//!   - **Instances** are membrane forks: a party enters a dungeon → the world is forked
//!     (a cap-bounded snapshot loaded onto a fresh engine) so the party plays its own
//!     copy. Multiple parties = multiple independent instances of the same dungeon,
//!     stitchable back by replaying their receipts onto the shared world.
//!
//! THE CAP TOOTH is the SAME one [`crate::applet::Applet::fire`] commits: an
//! affordance carries the `AuthRequired` it needs; a fire is refused in-band unless the
//! actor's HELD authority satisfies it via [`dregg_cell::is_attenuation`]. The GM holds
//! a distinct `Custom` floor (the GM authority); a player holds only a narrow
//! `Signature`, incomparable to that floor — so a player firing a GM-only affordance is
//! refused with nothing committed. (The underlying ledger permissions are OPEN — the
//! single-custody embedded-world pattern `crate::applet` uses — so the MUD's authority
//! model lives entirely in the affordance-level floors.)

use std::collections::BTreeMap;

use dregg_cell::state::{FieldElement, STATE_SLOTS};
use dregg_cell::{AuthRequired, Cell};
use dregg_sdk::embed::{DreggEngine, EngineConfig};
use dregg_turn::builder::{ActionBuilder, TurnBuilder};
use dregg_turn::TurnReceipt;
use dregg_types::CellId;

use deos_reflect::frustum::Frustum;
use deos_reflect::graph::OcapGraph;

// ─────────────────────────────────────────────────────────────────────────────
// Character stat layout — which cell state slot holds which stat. (A character is
// a cell; its stats are field slots. Public so a reflective crawl can read them.)
// ─────────────────────────────────────────────────────────────────────────────

/// HP — the player may spend/restore it on its own character.
pub const SLOT_HP: usize = 0;
/// XP — accumulated by the player acting in the world (player-writable, grind).
pub const SLOT_XP: usize = 1;
/// LEVEL — a GM-authority stat. A player cannot set it directly; it only rises via the
/// gated level-up turn when XP crosses the threshold.
pub const SLOT_LEVEL: usize = 2;
/// ATTACK — derived from level; bumped by the level-up turn.
pub const SLOT_ATTACK: usize = 3;
/// Current room (audit witness of location; the authoritative location is reachability).
pub const SLOT_LOCATION: usize = 4;

/// NPC mood/aggression slot (on an NPC cell): rises when the GM fires a reaction.
pub const SLOT_NPC_AGGRO: usize = 0;

/// XP needed per level (level N requires `N * XP_PER_LEVEL`).
pub const XP_PER_LEVEL: u64 = 100;

// ─────────────────────────────────────────────────────────────────────────────
// Encoding — stats are u64 scalars packed little-endian into a 32-byte field.
// ─────────────────────────────────────────────────────────────────────────────

fn pack_u64(v: u64) -> FieldElement {
    let mut fe = [0u8; 32];
    fe[..8].copy_from_slice(&v.to_le_bytes());
    fe
}

fn unpack_u64(fe: &FieldElement) -> u64 {
    let mut b = [0u8; 8];
    b.copy_from_slice(&fe[..8]);
    u64::from_le_bytes(b)
}

// ─────────────────────────────────────────────────────────────────────────────
// Authority — the GM-vs-player asymmetry, expressed in `AuthRequired`.
// ─────────────────────────────────────────────────────────────────────────────

/// The GM's authority floor: a distinct `Custom { vk_hash }` that ONLY the GM holds.
/// `is_attenuation` (`is_narrower_or_equal`) makes a different `Custom` (or a plain
/// `Signature`/`Proof`) INCOMPARABLE to this — so a player holding `Signature` over its
/// own character can never satisfy a GM-floored affordance. This is the structural core
/// of "the GM is omnipotent in its world; a player is not."
fn gm_floor() -> AuthRequired {
    // A fixed, distinct vk_hash that ONLY the GM principal carries (a constant, not a
    // hash — the GM-floor identity just has to be a unique `Custom` value incomparable
    // to a player's `Signature`). Exactly 32 bytes.
    AuthRequired::Custom {
        vk_hash: *b"deos-mud:gamemaster-floor-v1::xx",
    }
}

/// A player's authority over its OWN character: a signature. Incomparable to the GM
/// floor, so player-only affordances admit it while GM-only ones refuse it.
fn player_floor() -> AuthRequired {
    AuthRequired::Signature
}

/// In-band cap tooth — the SAME check `Applet::fire` runs. `held` must be
/// narrower-or-equal to `required` (`is_attenuation`). The GM holds the broadest
/// authority (the GM floor itself); a player holds only its narrow `Signature`.
fn cap_admits(held: &AuthRequired, required: &AuthRequired) -> bool {
    dregg_cell::is_attenuation(held, required)
}

// ─────────────────────────────────────────────────────────────────────────────
// The world.
// ─────────────────────────────────────────────────────────────────────────────

/// Why a MUD action was refused (mirrors `FireError`, MUD-flavoured).
#[derive(Debug, PartialEq, Eq)]
pub enum MudError {
    /// The actor's held authority does not satisfy the affordance's floor (the cap
    /// tooth refused — nothing committed). The defining player-vs-GM refusal.
    Unauthorized(String),
    /// The actor cannot reach the destination room (no capability edge / exit).
    NoSuchExit,
    /// A game precondition failed (e.g. level-up fired below the XP threshold).
    Precondition(String),
    /// The embedded executor rejected the (authorized) turn.
    Executor(String),
    /// A named cell is not in the world.
    UnknownCell(String),
}

impl std::fmt::Display for MudError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            MudError::Unauthorized(a) => write!(f, "'{a}' refused by the cap-gate (narrow caps)"),
            MudError::NoSuchExit => write!(f, "no exit / unreachable room"),
            MudError::Precondition(p) => write!(f, "precondition failed: {p}"),
            MudError::Executor(e) => write!(f, "executor rejected the turn: {e}"),
            MudError::UnknownCell(c) => write!(f, "unknown cell '{c}'"),
        }
    }
}
impl std::error::Error for MudError {}

/// A handle (the GM's bookkeeping of who-is-what; the *authority* lives on the ledger).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Kind {
    Gamemaster,
    Room,
    Character,
    Npc,
    Item,
}

/// The MUD world: an embedded verified executor whose ledger holds every game cell, a
/// GM principal with broad caps, and a name→cell directory. Every mutation is a real
/// cap-gated turn leaving a [`TurnReceipt`].
pub struct MudWorld {
    engine: DreggEngine,
    /// The gamemaster cell — the privileged server.
    gm: CellId,
    /// name → (cell id, kind). The GM's directory of the world.
    dir: BTreeMap<String, (CellId, Kind)>,
    /// Reverse: cell id → name (for legible reports).
    names: BTreeMap<CellId, String>,
    /// The receipt tape — every committed turn, GM or player, in order.
    receipts: Vec<TurnReceipt>,
    prev_receipt: Option<[u8; 32]>,
    /// A monotonically increasing per-cell key counter, so successive cells get
    /// distinct ids (content-addressed on public_key).
    seq: u64,
}

impl MudWorld {
    /// Boot a fresh world with a single GM principal holding the broadest authority.
    pub fn new() -> Self {
        let mut engine = DreggEngine::new(EngineConfig::for_testing());
        // Symbolic witness (the local drive path): the state transition fully applies
        // and every gate runs; only the publishable Merkle commitment is deferred. SAME
        // as `crate::applet::Applet`'s default.
        engine
            .executor()
            .set_witness_mode(dregg_turn::collapse::WitnessMode::Symbolic);
        let gm = mk_cell(&mut engine, 0, 1_000_000);
        let mut dir = BTreeMap::new();
        let mut names = BTreeMap::new();
        dir.insert("gm".to_string(), (gm, Kind::Gamemaster));
        names.insert(gm, "gm".to_string());
        MudWorld {
            engine,
            gm,
            dir,
            names,
            receipts: Vec::new(),
            prev_receipt: None,
            seq: 1,
        }
    }

    /// The gamemaster cell id.
    pub fn gm(&self) -> CellId {
        self.gm
    }

    /// Look up a named cell.
    pub fn cell(&self, name: &str) -> Option<CellId> {
        self.dir.get(name).map(|(id, _)| *id)
    }

    /// The receipt tape (every committed turn).
    pub fn receipts(&self) -> &[TurnReceipt] {
        &self.receipts
    }

    /// How many verified turns have committed.
    pub fn receipt_count(&self) -> usize {
        self.receipts.len()
    }

    /// The live ledger (the world the reflective crawl walks).
    pub fn ledger(&self) -> &dregg_cell::Ledger {
        self.engine.ledger()
    }

    /// Read a character/NPC stat slot off the live ledger.
    pub fn stat(&self, cell: CellId, slot: usize) -> u64 {
        self.engine
            .ledger()
            .get(&cell)
            .map(|c| unpack_u64(&c.state.fields[slot]))
            .unwrap_or(0)
    }

    /// The reachability frustum for a viewer — the rooms/cells it can navigate to (the
    /// map AS SEEN BY that principal, bounded by its c-list).
    pub fn reach(&self, viewer: CellId) -> Frustum<'_> {
        Frustum::project(self.engine.ledger(), viewer)
    }

    /// The full ocap topology of the world (the whole map, GM's-eye view).
    pub fn ocap_graph(&self) -> OcapGraph {
        OcapGraph::build(self.engine.ledger())
    }

    // ── GM SUPERPOWERS — each requires the GM floor; a player cannot fire any of these.

    /// **GM: spawn a room.** A new room-cell on the ledger. Returns the room id.
    pub fn gm_spawn_room(&mut self, actor: AuthRequired, name: &str) -> Result<CellId, MudError> {
        self.gm_spawn(actor, name, Kind::Room, 0)
    }

    /// **GM: spawn an NPC.** A new NPC-cell, GM-controlled.
    pub fn gm_spawn_npc(&mut self, actor: AuthRequired, name: &str) -> Result<CellId, MudError> {
        self.gm_spawn(actor, name, Kind::Npc, 0)
    }

    /// **GM: spawn a player character.** The character cell gets a starting HP; the
    /// PLAYER will act on it with narrow `Signature` authority, while the GM keeps the
    /// broad cap (it can level them, move them, etc.).
    pub fn gm_spawn_character(
        &mut self,
        actor: AuthRequired,
        name: &str,
        start_hp: u64,
    ) -> Result<CellId, MudError> {
        let id = self.gm_spawn(actor, name, Kind::Character, start_hp)?;
        // seed LEVEL 1 / ATTACK 1 on the character (GM-floored set-field turns).
        self.gm_set_stat(gm_floor(), id, SLOT_LEVEL, 1)?;
        self.gm_set_stat(gm_floor(), id, SLOT_ATTACK, 1)?;
        Ok(id)
    }

    fn gm_spawn(
        &mut self,
        actor: AuthRequired,
        name: &str,
        kind: Kind,
        start_hp: u64,
    ) -> Result<CellId, MudError> {
        // CAP TOOTH: spawning is a GM superpower.
        if !cap_admits(&actor, &gm_floor()) {
            return Err(MudError::Unauthorized(format!("spawn:{name}")));
        }
        let id = mk_cell(&mut self.engine, self.seq, 1_000_000);
        self.seq += 1;
        self.dir.insert(name.to_string(), (id, kind));
        self.names.insert(id, name.to_string());
        // The spawn is RECEIPTED: the GM commits an init turn on the new cell (seed HP +
        // bump nonce). Blame = GM.
        if start_hp > 0 {
            self.commit_set_fields(id, &[(SLOT_HP, start_hp)])?;
        } else {
            self.commit_set_fields(id, &[])?; // still leave a receipt (bump nonce).
        }
        Ok(id)
    }

    /// **GM: link two rooms by an exit** — grant `from` a capability to `to`. The map
    /// edge IS the cap edge: after this, a principal that can reach `from` can reach
    /// `to`. A GM superpower (reshaping the map).
    pub fn gm_link_rooms(
        &mut self,
        actor: AuthRequired,
        from: CellId,
        to: CellId,
    ) -> Result<(), MudError> {
        if !cap_admits(&actor, &gm_floor()) {
            return Err(MudError::Unauthorized("link_rooms".into()));
        }
        self.engine
            .ledger_mut()
            .get_mut(&from)
            .ok_or_else(|| MudError::UnknownCell("from".into()))?
            .capabilities
            .grant(to, AuthRequired::None);
        self.commit_set_fields(from, &[])?; // receipt: GM reshaped the map.
        Ok(())
    }

    /// **GM: grant a player navigation into a room** — give the character a cap to the
    /// room (so the player can reach/enter it). A GM superpower; this is how a player's
    /// reachable map GROWS.
    pub fn gm_admit_to_room(
        &mut self,
        actor: AuthRequired,
        character: CellId,
        room: CellId,
    ) -> Result<(), MudError> {
        if !cap_admits(&actor, &gm_floor()) {
            return Err(MudError::Unauthorized("admit_to_room".into()));
        }
        self.engine
            .ledger_mut()
            .get_mut(&character)
            .ok_or_else(|| MudError::UnknownCell("character".into()))?
            .capabilities
            .grant(room, AuthRequired::None);
        self.commit_set_fields(character, &[])?;
        Ok(())
    }

    /// **GM: set a character/NPC stat arbitrarily** — the godlike write (level, attack,
    /// aggro, anything). A GM superpower; a player can NEVER do this on the LEVEL slot.
    pub fn gm_set_stat(
        &mut self,
        actor: AuthRequired,
        cell: CellId,
        slot: usize,
        value: u64,
    ) -> Result<(), MudError> {
        if !cap_admits(&actor, &gm_floor()) {
            return Err(MudError::Unauthorized(format!("set_stat[{slot}]")));
        }
        self.commit_set_fields(cell, &[(slot, value)])
    }

    /// **GM: fire a REACTION** — the world's response to a player action. The GM
    /// commits a turn on an NPC/environment cell (here: raise the NPC's aggression by
    /// `amount`). This is the reactive affordance the GM coordinates: a player acted,
    /// and the GM fires the transition-shape follow-up. A player could not fire this
    /// (it is GM-floored and acts on a cell the player has no write-cap over).
    pub fn gm_react(
        &mut self,
        actor: AuthRequired,
        npc: CellId,
        amount: u64,
    ) -> Result<(), MudError> {
        if !cap_admits(&actor, &gm_floor()) {
            return Err(MudError::Unauthorized("react".into()));
        }
        let cur = self.stat(npc, SLOT_NPC_AGGRO);
        self.commit_set_fields(npc, &[(SLOT_NPC_AGGRO, cur + amount)])
    }

    // ── PLAYER ACTIONS — gated by the narrow player floor + game preconditions.

    /// **Player: gain XP** on its OWN character. Admitted by the player's narrow
    /// authority (a player may grind XP on the character it holds the signature for).
    pub fn player_gain_xp(
        &mut self,
        actor: AuthRequired,
        character: CellId,
        xp: u64,
    ) -> Result<(), MudError> {
        if !cap_admits(&actor, &player_floor()) {
            return Err(MudError::Unauthorized("gain_xp".into()));
        }
        let cur = self.stat(character, SLOT_XP);
        self.commit_set_fields(character, &[(SLOT_XP, cur + xp)])
    }

    /// **Player: attempt to set their own LEVEL** — REFUSED. The LEVEL slot is a
    /// GM-authority stat; a player's narrow authority cannot satisfy the GM floor.
    /// This is the explicit "a player cannot level themselves arbitrarily" tooth.
    pub fn player_set_level(
        &mut self,
        actor: AuthRequired,
        character: CellId,
        level: u64,
    ) -> Result<(), MudError> {
        if !cap_admits(&actor, &gm_floor()) {
            return Err(MudError::Unauthorized("set_level".into()));
        }
        self.commit_set_fields(character, &[(SLOT_LEVEL, level)])
    }

    /// **Player: move** to an adjacent room — a cap-gated navigation. The move is
    /// admitted only if the player can REACH the destination (there is an exit / cap
    /// edge from somewhere in its reachable map). Refused with `NoSuchExit` otherwise.
    pub fn player_move(
        &mut self,
        actor: AuthRequired,
        character: CellId,
        to: CellId,
    ) -> Result<(), MudError> {
        if !cap_admits(&actor, &player_floor()) {
            return Err(MudError::Unauthorized("move".into()));
        }
        // The MAP TOOTH: the character must be able to reach the room through its
        // c-list closure (the exits it actually holds). Unreachable = no exit.
        let frustum = Frustum::project(self.engine.ledger(), character);
        if !frustum.can_observe(&to) {
            return Err(MudError::NoSuchExit);
        }
        // Record the move as a receipted turn on the character (its location witness).
        let loc = u64::from_le_bytes(to.as_bytes()[..8].try_into().unwrap());
        self.commit_set_fields(character, &[(SLOT_LOCATION, loc)])
    }

    // ── LEVELING — a GATED turn (the GM/server applies it when XP crosses threshold).

    /// **Level-up** — a gated turn. Requires the GM floor (the server applies it) AND
    /// the XP precondition (`XP >= level * XP_PER_LEVEL`). On success the character's
    /// LEVEL and ATTACK rise. A below-threshold fire is refused (`Precondition`).
    pub fn level_up(&mut self, actor: AuthRequired, character: CellId) -> Result<u64, MudError> {
        if !cap_admits(&actor, &gm_floor()) {
            return Err(MudError::Unauthorized("level_up".into()));
        }
        let level = self.stat(character, SLOT_LEVEL);
        let xp = self.stat(character, SLOT_XP);
        let need = level * XP_PER_LEVEL;
        if xp < need {
            return Err(MudError::Precondition(format!(
                "XP {xp} < {need} needed for level {}",
                level + 1
            )));
        }
        let new_level = level + 1;
        let new_attack = self.stat(character, SLOT_ATTACK) + 2;
        self.commit_set_fields(
            character,
            &[(SLOT_LEVEL, new_level), (SLOT_ATTACK, new_attack)],
        )?;
        Ok(new_level)
    }

    // ── INSTANCES — membrane forks of the whole world for a party.

    /// **Open a dungeon instance** — a membrane fork: snapshot the live world and load
    /// it onto a FRESH engine. The party plays in its own copy; mutations there do not
    /// touch the shared world. Multiple parties = multiple `Instance`s of the same
    /// dungeon. A GM superpower (the server opens the instance), so GM-floored.
    pub fn open_instance(&self, actor: AuthRequired) -> Result<Instance, MudError> {
        if !cap_admits(&actor, &gm_floor()) {
            return Err(MudError::Unauthorized("open_instance".into()));
        }
        let snap = self
            .engine
            .state_snapshot()
            .map_err(|e| MudError::Executor(e.to_string()))?;
        let mut engine = DreggEngine::new(EngineConfig::for_testing());
        engine
            .executor()
            .set_witness_mode(dregg_turn::collapse::WitnessMode::Symbolic);
        engine
            .load_state(&snap)
            .map_err(|e| MudError::Executor(e.to_string()))?;
        Ok(Instance {
            world: MudWorld {
                engine,
                gm: self.gm,
                dir: self.dir.clone(),
                names: self.names.clone(),
                receipts: Vec::new(),
                prev_receipt: None,
                seq: self.seq,
            },
        })
    }

    // ── the receipted-turn primitive every mutation funnels through.

    /// Commit a set-fields turn on `cell` and append the receipt. (The single on-ledger
    /// write path — the SAME shape `Applet::fire` builds: an unchecked action carrying
    /// the writes + a nonce bump, executed on the embedded verified executor. The cap
    /// tooth already ran in-band at the affordance boundary above.)
    fn commit_set_fields(&mut self, cell: CellId, writes: &[(usize, u64)]) -> Result<(), MudError> {
        let nonce = self
            .engine
            .ledger()
            .get(&cell)
            .map(|c| c.state.nonce())
            .ok_or_else(|| MudError::UnknownCell("turn-cell".into()))?;
        let mut action = ActionBuilder::new_unchecked_for_tests(cell, "mud", cell);
        for (slot, value) in writes {
            action = action.effect_set_field(cell, *slot, pack_u64(*value));
        }
        let action = action.effect_increment_nonce(cell).build();
        let mut tb = TurnBuilder::new(cell, nonce);
        tb.set_fee(10_000);
        if let Some(prev) = self.prev_receipt {
            tb.set_previous_receipt_hash(prev);
        }
        tb.add_action(action);
        let turn = tb.build();
        let receipt = self
            .engine
            .execute_turn(&turn)
            .map_err(|e| MudError::Executor(e.to_string()))?;
        let rh = receipt.receipt_hash();
        self.prev_receipt = Some(rh);
        self.receipts.push(receipt);
        Ok(())
    }
}

impl Default for MudWorld {
    fn default() -> Self {
        Self::new()
    }
}

/// A dungeon instance — a cap-bounded membrane fork of the world. Drive it like the
/// shared world; its turns are independent (its own receipt tape). Stitch back by
/// replaying the instance's effects onto the shared world.
pub struct Instance {
    world: MudWorld,
}

impl Instance {
    /// The world inside the instance (drive it like the shared one).
    pub fn world(&mut self) -> &mut MudWorld {
        &mut self.world
    }

    /// Read a stat inside the instance.
    pub fn stat(&self, cell: CellId, slot: usize) -> u64 {
        self.world.stat(cell, slot)
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Cell minting — a real cell on the embedded ledger.
// ─────────────────────────────────────────────────────────────────────────────

/// Mint a real cell onto the engine ledger with a distinct content-addressed id
/// (`seq` salts the public key) and an initial balance (computrons to pay turn fees).
///
/// The cell carries OPEN ledger permissions — the SAME "single-custody embedded world"
/// pattern [`crate::applet::Applet`] uses: the GM-vs-player authority asymmetry is
/// enforced at the AFFORDANCE boundary (the in-band [`cap_admits`] cap tooth), and the
/// executor then commits the already-authorized write.
fn mk_cell(engine: &mut DreggEngine, seq: u64, balance: i64) -> CellId {
    let mut pk = [0u8; 32];
    pk[..8].copy_from_slice(&seq.to_le_bytes());
    pk[8] = MU_TAG;
    let token = [0x11u8; 32];
    let mut cell = Cell::with_balance(pk, token, balance);
    cell.permissions = open_permissions();
    let id = cell.id();
    engine
        .ledger_mut()
        .insert_cell(cell)
        .expect("seed mud cell onto embedded ledger");
    debug_assert!(STATE_SLOTS >= 5, "mud uses slots 0..4");
    id
}

/// Open ledger permissions (single-custody embedded world) — mirrors `crate::applet`'s
/// seed. The MUD authority gate is the affordance-level cap tooth.
fn open_permissions() -> dregg_cell::Permissions {
    dregg_cell::Permissions {
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

/// A nonzero tag byte so a mud public key never collides with the all-zero default.
const MU_TAG: u8 = 0x6d; // 'm'

#[cfg(test)]
mod tests {
    use super::*;

    /// THE LIVING-WORLD ARC: boot a world, the GM builds a map + characters, a player
    /// moves + grinds XP + LEVELS UP, an NPC REACTS, a party opens a dungeon INSTANCE —
    /// and the GM-vs-player cap asymmetry is enforced at every step, all receipted.
    #[test]
    fn mud_living_world_arc() {
        let mut w = MudWorld::new();
        let gm = gm_floor();
        let player = player_floor();

        // ── THE MAP: the GM (broad caps) spawns three rooms and links them by exits.
        let tavern = w.gm_spawn_room(gm.clone(), "tavern").unwrap();
        let road = w.gm_spawn_room(gm.clone(), "road").unwrap();
        let cave = w.gm_spawn_room(gm.clone(), "cave").unwrap();
        w.gm_link_rooms(gm.clone(), tavern, road).unwrap();
        w.gm_link_rooms(gm.clone(), road, cave).unwrap();

        // A PLAYER cannot spawn a room (narrow caps) — refused, nothing committed.
        let before = w.receipt_count();
        let denied = w.gm_spawn_room(player.clone(), "secret-vault");
        assert!(matches!(denied, Err(MudError::Unauthorized(_))));
        assert_eq!(w.receipt_count(), before, "a refused spawn commits no turn");

        // ── CHARACTER + NPC: the GM spawns a player character and a goblin NPC.
        let hero = w.gm_spawn_character(gm.clone(), "hero", 30).unwrap();
        let goblin = w.gm_spawn_npc(gm.clone(), "goblin").unwrap();
        assert_eq!(w.stat(hero, SLOT_LEVEL), 1, "hero starts at level 1");
        assert_eq!(w.stat(hero, SLOT_HP), 30);

        // ── THE PLAYER'S MAP: the GM admits the hero into the tavern. Now the hero can
        //    reach tavern→road→cave through the cap-edge exits (the map is the ocap
        //    graph). Before admission the hero cannot reach the tavern.
        assert!(
            !w.reach(hero).can_observe(&tavern),
            "before admission the hero cannot reach the tavern"
        );
        w.gm_admit_to_room(gm.clone(), hero, tavern).unwrap();
        let reach = w.reach(hero);
        assert!(reach.can_observe(&tavern), "hero can reach the tavern");
        assert!(reach.can_observe(&road), "...and the road (exit)");
        assert!(reach.can_observe(&cave), "...and the cave (transitive exit)");

        // ── PLAYER MOVES: the hero walks tavern→road→cave (cap-gated navigation).
        w.player_move(player.clone(), hero, road).unwrap();
        w.player_move(player.clone(), hero, cave).unwrap();
        // Moving to an UNREACHABLE room is refused (no exit).
        let orphan = w.gm_spawn_room(gm.clone(), "void").unwrap();
        assert_eq!(
            w.player_move(player.clone(), hero, orphan),
            Err(MudError::NoSuchExit),
            "no cap edge to the void = no exit"
        );

        // ── XP GRIND: the player gains XP on its own character (narrow authority OK).
        w.player_gain_xp(player.clone(), hero, 60).unwrap();
        w.player_gain_xp(player.clone(), hero, 50).unwrap();
        assert_eq!(w.stat(hero, SLOT_XP), 110);

        // A PLAYER CANNOT set their own LEVEL (it is GM-authority) — refused.
        let cheat = w.player_set_level(player.clone(), hero, 99);
        assert!(matches!(cheat, Err(MudError::Unauthorized(_))));
        assert_eq!(w.stat(hero, SLOT_LEVEL), 1, "the cheat changed nothing");

        // ── LEVEL UP: a GATED turn. (level 1 needs 1*100 = 100 XP; the hero has 110.)
        let lvl = w.level_up(gm.clone(), hero).unwrap();
        assert_eq!(lvl, 2, "hero is now level 2");
        assert_eq!(w.stat(hero, SLOT_LEVEL), 2);
        assert_eq!(w.stat(hero, SLOT_ATTACK), 3, "attack rose with the level");
        // A second level-up now needs 2*100 = 200 XP; the hero has 110 → refused.
        assert!(matches!(
            w.level_up(gm.clone(), hero),
            Err(MudError::Precondition(_))
        ));

        // ── REACTION: the player acted; the GM fires the goblin's reactive turn (its
        //    aggression rises). A player CANNOT fire this (GM-floored + no write-cap).
        assert_eq!(w.stat(goblin, SLOT_NPC_AGGRO), 0);
        let player_react = w.gm_react(player.clone(), goblin, 5);
        assert!(matches!(player_react, Err(MudError::Unauthorized(_))));
        w.gm_react(gm.clone(), goblin, 5).unwrap();
        assert_eq!(w.stat(goblin, SLOT_NPC_AGGRO), 5, "the goblin reacted");

        // ── EVERY orchestration left a receipt; each carries a distinct hash.
        let shared_turns = w.receipt_count();
        assert!(
            shared_turns >= 10,
            "the living world is a chain of {shared_turns} verified turns"
        );
        let hashes: std::collections::BTreeSet<_> =
            w.receipts().iter().map(|r| r.receipt_hash()).collect();
        assert_eq!(
            hashes.len(),
            shared_turns,
            "every turn left a distinct receipt"
        );

        // ── INSTANCE: a party opens a dungeon — a membrane fork of the whole world.
        //    A PLAYER cannot open an instance (GM superpower).
        assert!(matches!(
            w.open_instance(player.clone()),
            Err(MudError::Unauthorized(_))
        ));
        let mut inst_a = w.open_instance(gm.clone()).unwrap();
        let mut inst_b = w.open_instance(gm.clone()).unwrap();

        // Inside instance A, the GM buffs the goblin; instance B and the shared world
        // are UNAFFECTED (independent forks).
        inst_a.world().gm_react(gm.clone(), goblin, 50).unwrap();
        assert_eq!(inst_a.stat(goblin, SLOT_NPC_AGGRO), 55, "instance A diverged");
        assert_eq!(inst_b.stat(goblin, SLOT_NPC_AGGRO), 5, "instance B is its own copy");
        assert_eq!(w.stat(goblin, SLOT_NPC_AGGRO), 5, "the shared world is untouched");

        // The instance carries the SAME hero: it can level independently.
        inst_b.world().gm_set_stat(gm.clone(), hero, SLOT_XP, 200).unwrap();
        let inst_lvl = inst_b.world().level_up(gm.clone(), hero).unwrap();
        assert_eq!(inst_lvl, 3, "instance B leveled the hero independently");
        assert_eq!(w.stat(hero, SLOT_LEVEL), 2, "shared-world hero is still level 2");
    }

    /// The cap asymmetry in isolation: a player CANNOT satisfy the GM floor.
    #[test]
    fn mud_cap_asymmetry() {
        let gm = gm_floor();
        let player = player_floor();
        // GM authority satisfies the GM floor (it IS the floor).
        assert!(cap_admits(&gm, &gm_floor()));
        // The load-bearing fact: a PLAYER cannot satisfy the GM floor.
        assert!(
            !cap_admits(&player, &gm_floor()),
            "a player CANNOT reach GM authority"
        );
        // A player satisfies its own player floor.
        assert!(cap_admits(&player, &player_floor()));
    }

    /// Leveling is genuinely gated on the XP precondition (non-vacuous: refuses below
    /// threshold AND succeeds at/above it).
    #[test]
    fn mud_leveling_is_gated() {
        let mut w = MudWorld::new();
        let gm = gm_floor();
        let player = player_floor();
        let hero = w.gm_spawn_character(gm.clone(), "hero", 20).unwrap();

        // Below threshold → refused.
        w.player_gain_xp(player.clone(), hero, 50).unwrap();
        assert!(matches!(
            w.level_up(gm.clone(), hero),
            Err(MudError::Precondition(_))
        ));
        assert_eq!(w.stat(hero, SLOT_LEVEL), 1);

        // Cross the threshold → succeeds.
        w.player_gain_xp(player.clone(), hero, 50).unwrap();
        assert_eq!(w.level_up(gm.clone(), hero).unwrap(), 2);
    }
}
