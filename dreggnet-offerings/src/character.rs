//! # `character` — a PERSISTENT, LEVELING character bound to a player's identity.
//!
//! The dungeon (offering #0) is one-shot: [`DungeonOffering::open`](crate::dungeon::DungeonOffering::open)
//! deploys a FRESH, identically-seeded world-cell each run — the *identity* persists (a stable
//! [`DreggIdentity`]) but the *character* does not. `dungeon-on-dregg`'s [`progression`] module
//! already holds a PROVEN character sheet — XP / level / class / abilities as real gated cell
//! state on the real executor (a level-up is a `FieldGte(xp, threshold(L))`-gated turn; a class
//! ability is `FieldEquals(class, .)`-gated; class is `WriteOnce`) — but it was STANDALONE. This
//! module WIRES it into the dungeon flow, keyed by the player's identity, so a character carries
//! and LEVELS across runs.
//!
//! ## The seam (load / save)
//!
//! A [`CharacterStore`] is the load/save seam: a returning player's [`CharacterSheet`] is LOADED
//! on [`open`](AdventurerOffering::open) (a new player starts fresh) and SAVED on
//! [`save`](AdventurerOffering::save). [`InMemoryCharacterStore`] is the in-process impl the tests
//! drive; the **durable sqlite store is the bot's — a NAMED follow-up**, not built here. The
//! character CELL is deployed fresh + seeded from the loaded sheet each run (the identity gives
//! the deterministic cell *identity*; the sheet gives the carried *state*).
//!
//! ## The teeth stay REAL (nothing here is app bookkeeping)
//!
//! - **XP is EARNED from real run outcomes.** Bloodying the gate-warden and seizing the hoard are
//!   real dungeon turns the executor admits; iff such a move LANDS, the session grants XP to the
//!   character cell via [`progression::gain_xp`] — itself a real `StrictMonotonic(xp)`-gated turn.
//!   A dungeon move the executor REFUSES (a killing blow past the HP floor) grants NOTHING (the
//!   anti-ghost binding: no real outcome, no XP).
//! - **A forged XP grant is REFUSED.** XP moves ONLY through the sanctioned `GAIN_XP_METHOD`; a
//!   grant presented under any other method is a real executor refusal (the cell program is
//!   default-deny: an unknown method on a `Cases` program with dispatch cases is
//!   `NoTransitionCaseMatched`). See [`Character::hero_cell`] + the driven anti-cheat test.
//! - **Level-up is the existing `FieldGte(xp, threshold)` gate.** A returning low-XP character
//!   cannot level — the CARRIED xp is exactly what the kernel predicate reads (non-vacuous across
//!   the run boundary).
//!
//! ## Honest scope
//!
//! - The [`CharacterStore`] seam is in-memory here; the durable **bot-owned sqlite store is a
//!   named follow-up**. The character sheet is a plain value ([`CharacterSheet`]) the durable store
//!   will persist by identity — the seam is exactly the boundary it plugs into.
//! - XP is granted for two outcomes (bloodying the warden, seizing the hoard); the grant is a
//!   SESSION-level binding of a real character-cell turn to a real dungeon-cell turn (two cells,
//!   two turns). The dungeon's own `verify_by_replay` chain is untouched.
//! - A fuller RPG (inventory persistence, reputation, cross-universe character, a recorded +
//!   replay-verified character-turn chain) builds ON this seam — named, not built here.

use std::collections::HashMap;

use deos_view::ViewNode;
use dregg_app_framework::TurnReceipt;
use spween_dregg::{Value, WorldCell, WorldError};

use dungeon_on_dregg::meta::{self, deploy_meta_hero};
use dungeon_on_dregg::progression::{self, MAGE, ROGUE, WARRIOR, xp_threshold};
use dungeon_on_dregg::{KP_SEIZE, KP_TRADE_BLOWS, ROOM_GATEHALL, ROOM_SANCTUM};

use crate::dungeon::{DungeonOffering, DungeonSession};
use crate::{
    Action, DreggIdentity, Offering, OfferingError, Outcome, SessionConfig, Surface, VerifyReport,
};

// ── The persistable character sheet ──────────────────────────────────────────────

/// **A persistable snapshot of a character** — the four progression slots as a plain value the
/// [`CharacterStore`] carries across runs, keyed by [`DreggIdentity`]. [`Default`] is a FRESH
/// character (all zero): the natural "a new player starts fresh" state a store returns for an
/// unknown identity.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct CharacterSheet {
    /// Earned experience (the `xp` slot). Monotone; the level-up gate reads it.
    pub xp: u64,
    /// Character level (the `level` slot). Advanced only through the XP-gated per-level turns.
    pub level: u64,
    /// Class id (the `class` slot): `0` = unchosen, else [`WARRIOR`]/[`MAGE`]/[`ROGUE`]. `WriteOnce`.
    pub class: u64,
    /// The class-ability counter (the `abilities_used` slot).
    pub abilities_used: u64,
    /// The HARDCORE death flag (the `dead` slot): `1` once the character has perished.
    /// `WriteOnce`-final on the cell, so a saved `dead` character LOADS dead and stays
    /// dead across runs (a resurrection is refused) — the no-death-streak / survived
    /// leaderboard leans on this un-forgeable, un-undoable fact. A non-hardcore character
    /// never sets it (stays `0`).
    pub dead: u64,
    /// The META-CURRENCY (the `echoes` slot): the roguelite retention loop's accrual. A run that
    /// ENDS IN DEATH grants echoes tied to the depth reached ([`dungeon_on_dregg::meta`]); the slot
    /// is `Monotonic` (it only accrues) and a grant is gated `FieldEquals(dead, 1)` — earned ONLY on
    /// a real death. Carries across runs by identity (this is what makes death ADVANCE you).
    pub echoes: u64,
    /// The persistent UNLOCK (the `boon` slot): bought with enough accrued [`echoes`](Self::echoes)
    /// via a real `FieldGte(echoes, price)` + `WriteOnce(boon)` turn. A modest permanent starting
    /// nudge a NEXT run starts holding (carried across runs by identity).
    pub boon: u64,
}

impl CharacterSheet {
    /// The class name for a render/label (`"unclassed"` when unchosen).
    pub fn class_name(&self) -> &'static str {
        match self.class {
            WARRIOR => "Warrior",
            MAGE => "Mage",
            ROGUE => "Rogue",
            _ => "unclassed",
        }
    }
}

// ── The load/save seam ───────────────────────────────────────────────────────────

/// **The character persistence seam** — load a player's [`CharacterSheet`] on session open, save
/// it back when the run checkpoints. Keyed by [`DreggIdentity`] (the same stable cryptographic
/// identity the frontend derives). An unknown identity LOADS a [`CharacterSheet::default`] (a
/// fresh character). [`InMemoryCharacterStore`] is the in-process impl for tests; the durable
/// bot-owned sqlite store is a NAMED follow-up that implements this same trait.
pub trait CharacterStore {
    /// Load `who`'s persisted character (a fresh [`CharacterSheet::default`] for an unknown player).
    fn load(&self, who: &DreggIdentity) -> CharacterSheet;
    /// Persist `who`'s character sheet (the carried state a later [`load`](CharacterStore::load) returns).
    fn save(&mut self, who: &DreggIdentity, sheet: CharacterSheet);
}

/// The in-process [`CharacterStore`] the tests drive — a map from identity to sheet. The durable
/// (sqlite / redb / pg-dregg) store is the bot's, a named follow-up implementing the same trait.
#[derive(Debug, Default)]
pub struct InMemoryCharacterStore {
    sheets: HashMap<DreggIdentity, CharacterSheet>,
}

impl InMemoryCharacterStore {
    /// A fresh, empty store (every identity is a new player until saved).
    pub fn new() -> Self {
        InMemoryCharacterStore {
            sheets: HashMap::new(),
        }
    }

    /// Whether a character has ever been persisted for `who` (a returning player).
    pub fn has(&self, who: &DreggIdentity) -> bool {
        self.sheets.contains_key(who)
    }
}

impl CharacterStore for InMemoryCharacterStore {
    fn load(&self, who: &DreggIdentity) -> CharacterSheet {
        self.sheets.get(who).copied().unwrap_or_default()
    }

    fn save(&mut self, who: &DreggIdentity, sheet: CharacterSheet) {
        self.sheets.insert(who.clone(), sheet);
    }
}

// ── The live character (the progression cell, seeded from the loaded sheet) ───────

/// Derive a **stable per-identity deploy seed** for the character cell (1..=251): the SAME player
/// always deploys the SAME character-cell identity, so re-deploy + re-seed reproduces the same
/// character (the identity gives the cell *identity*; the [`CharacterStore`] gives the *state*).
fn hero_seed(who: &DreggIdentity) -> u8 {
    (blake3::hash(who.0.as_bytes()).as_bytes()[0] % 251) + 1
}

/// **A live character bound to a player for one run** — the [`progression`] hero world-cell,
/// deployed under the player's stable seed and SEEDED from the loaded [`CharacterSheet`]. Its
/// progression turns (grant XP, level up, use a class ability) are REAL gated turns the executor
/// admits move-for-move; [`sheet`](Character::sheet) snapshots the live cell back to a persistable
/// value the [`CharacterStore`] saves.
pub struct Character {
    who: DreggIdentity,
    world: WorldCell,
}

impl Character {
    /// Deploy the character cell for `who` and seed it from `sheet` (the loaded/carried state). A
    /// FRESH character (level 0) is brought to the natural starting level 1 via the real free
    /// level-up turn (`xp_threshold(1) == 0`); a returning character keeps its carried level.
    ///
    /// `pub` so a sibling offering (e.g. [`crate::daily_descent`]) can bind the SAME persistent
    /// character to its own run, exactly as [`AdventurerOffering`] does for the Keep.
    pub fn open(who: DreggIdentity, sheet: CharacterSheet) -> Character {
        // The META-augmented hero cell: carries `echoes` / `boon` (meta-progression) alongside the
        // xp / level / class / abilities / dead progression slots, all on ONE persistent cell.
        let mut world = deploy_meta_hero(hero_seed(&who));
        // Seed the four progression slots to the carried values (genesis setup, not a turn —
        // exactly how the Keep seeds hp=50; the in-run progression turns are the gated ones).
        world.seed_var("xp", Value::Int(sheet.xp as i64));
        world.seed_var("level", Value::Int(sheet.level as i64));
        if sheet.class != 0 {
            world.seed_var("class", Value::Int(sheet.class as i64));
        }
        world.seed_var("abilities_used", Value::Int(sheet.abilities_used as i64));
        // Carry the HARDCORE death flag: a saved-dead character LOADS dead (and stays dead).
        if sheet.dead != 0 {
            world.seed_var("dead", Value::Int(sheet.dead as i64));
        }
        // Carry the META-PROGRESSION: accrued echoes + a claimed boon carry across runs by identity,
        // so a next run STARTS with the earned unlock — death advances you.
        world.seed_var("echoes", Value::Int(sheet.echoes as i64));
        if sheet.boon != 0 {
            world.seed_var("boon", Value::Int(sheet.boon as i64));
        }

        // A fresh adventurer begins at level 1 — a REAL free level-up turn (threshold(1) == 0).
        // (A carried-dead character keeps its level; the level-up case is alive-gated anyway.)
        if world.read_var("level") == 0 {
            let _ = progression::level_up(&world);
        }
        Character { who, world }
    }

    /// This character's owner identity.
    pub fn who(&self) -> &DreggIdentity {
        &self.who
    }

    /// The underlying [`progression`] hero world-cell (for render/introspection and the driven
    /// forged-XP anti-cheat: a grant under a non-sanctioned method is a real executor refusal).
    pub fn hero_cell(&self) -> &WorldCell {
        &self.world
    }

    /// Snapshot the live cell into a persistable [`CharacterSheet`] — what [`CharacterStore::save`]
    /// carries to the next run.
    pub fn sheet(&self) -> CharacterSheet {
        CharacterSheet {
            xp: self.world.read_var("xp"),
            level: self.world.read_var("level"),
            class: self.world.read_var("class"),
            abilities_used: self.world.read_var("abilities_used"),
            dead: self.world.read_var("dead"),
            echoes: self.world.read_var("echoes"),
            boon: self.world.read_var("boon"),
        }
    }

    /// Current earned XP.
    pub fn xp(&self) -> u64 {
        self.world.read_var("xp")
    }
    /// Current level.
    pub fn level(&self) -> u64 {
        self.world.read_var("level")
    }
    /// Current class id (`0` = unchosen).
    pub fn class(&self) -> u64 {
        self.world.read_var("class")
    }

    /// **Choose the character's class** — the one-time `WriteOnce` creation move (real turn). A
    /// returning character that already has a class is refused (the class carries over, frozen).
    pub fn choose_class(&self, class_id: u64) -> Result<TurnReceipt, WorldError> {
        progression::choose_class(&self.world, class_id)
    }

    /// **Grant earned XP** — the SANCTIONED grant (a real `StrictMonotonic(xp)`-gated turn under
    /// `GAIN_XP_METHOD`). The session calls this only when a real qualifying dungeon outcome LANDS.
    pub fn grant_xp(&self, amount: u64) -> Result<TurnReceipt, WorldError> {
        progression::gain_xp(&self.world, amount)
    }

    /// **Level up by one** — the existing `FieldGte(xp, threshold(next))`-gated turn. Without the
    /// earned (possibly CARRIED-from-a-prior-run) XP the executor REFUSES it and nothing commits.
    pub fn level_up(&self) -> Result<TurnReceipt, WorldError> {
        progression::level_up(&self.world)
    }

    /// **Use a class-locked ability** — the `FieldEquals(class, class_id)`-gated turn (admitted
    /// only in the matching class; a returning character's carried class unlocks its ability).
    pub fn use_ability(&self, class_id: u64) -> Result<TurnReceipt, WorldError> {
        progression::use_ability(&self.world, class_id)
    }

    /// **HARDCORE death** — a real committed turn setting the `WriteOnce`-final `dead` flag.
    /// A hardcore run that ends in defeat (e.g. downed in [`dungeon_on_dregg::bloodgate`])
    /// fires this. Once dead the character earns nothing and cannot be resurrected — the
    /// no-cheat leaderboard's un-forgeable "survived / no-death streak" fact.
    pub fn perish(&self) -> Result<TurnReceipt, WorldError> {
        progression::perish(&self.world)
    }

    /// Whether the character is (hardcore-)dead — the committed `dead` flag is set.
    pub fn is_dead(&self) -> bool {
        progression::is_dead(&self.world)
    }

    /// **Attempt a resurrection** — refused on a dead character (the `WriteOnce(dead)` tooth
    /// bars the 1→0 change). The non-vacuous proof that hardcore death is FINAL.
    pub fn attempt_resurrect(&self) -> Result<TurnReceipt, WorldError> {
        progression::attempt_resurrect(&self.world)
    }

    // ── Meta-progression-on-death (the roguelite retention loop) ──────────────────

    /// Current accrued META-CURRENCY (the carried `echoes` slot).
    pub fn echoes(&self) -> u64 {
        meta::echoes(&self.world)
    }

    /// Whether the persistent UNLOCK has been claimed (the carried `boon` slot is set) — what a
    /// next run starts holding.
    pub fn has_boon(&self) -> bool {
        meta::has_boon(&self.world)
    }

    /// **Grant the meta-currency for a death at `depth`** — the sanctioned accrual (a real turn
    /// gated `FieldEquals(dead, 1)` + `StrictMonotonic(echoes)`). The offering calls this ONLY when
    /// a hardcore run has truly ended in death; a grant on a living character is a real executor
    /// refusal (a won / unfinished run advances you no echoes). A deeper death grants more.
    pub fn grant_echoes(&self, depth: u64) -> Result<TurnReceipt, WorldError> {
        meta::grant_echoes(&self.world, depth)
    }

    /// **Claim the persistent unlock** — the `FieldGte(echoes, price)` + `WriteOnce(boon)`-gated
    /// turn. Without enough accrued (possibly carried) echoes the executor REFUSES it; once claimed,
    /// the boon persists on the sheet and a next run starts holding it.
    pub fn claim_boon(&self) -> Result<TurnReceipt, WorldError> {
        meta::claim_boon(&self.world)
    }
}

// ── The XP reward binding (real dungeon outcomes → earned XP) ─────────────────────

/// XP earned for **bloodying the gate-warden** (one landed trade-blows turn).
pub const XP_BLOODY_WARDEN: u64 = 40;
/// XP earned for **seizing the hoard** (the landed run-ending seize turn).
pub const XP_SEIZE_HOARD: u64 = 120;

/// The XP a just-LANDED dungeon move earns, by `(room, choice_index)`. `None` for a move with no
/// reward. Only real, executor-admitted outcomes reach here (the caller grants iff the move landed).
fn xp_reward(room: &str, choice_index: usize) -> Option<u64> {
    match (room, choice_index) {
        (ROOM_GATEHALL, i) if i == KP_TRADE_BLOWS => Some(XP_BLOODY_WARDEN),
        (ROOM_SANCTUM, i) if i == KP_SEIZE => Some(XP_SEIZE_HOARD),
        _ => None,
    }
}

// ── The adventure session + the character-bound offering ──────────────────────────

/// **A character-bound dungeon run** — the one-shot [`DungeonSession`] plus the player's live
/// persistent [`Character`]. Advancing the dungeon EARNS the character XP on real outcomes; the
/// character's level/class carry across runs through the [`CharacterStore`].
pub struct AdventureSession {
    /// The player driving this run (the actor every dungeon turn is attributed to).
    who: DreggIdentity,
    /// The underlying one-shot dungeon session (the Keep world-cell + its playthrough).
    dungeon: DungeonSession,
    /// The live persistent character (the progression cell, seeded from the loaded sheet).
    character: Character,
}

impl AdventureSession {
    /// The player driving this run.
    pub fn who(&self) -> &DreggIdentity {
        &self.who
    }
    /// The live persistent character (level/XP/class getters, the hero cell).
    pub fn character(&self) -> &Character {
        &self.character
    }
    /// The underlying one-shot dungeon session.
    pub fn dungeon(&self) -> &DungeonSession {
        &self.dungeon
    }
    /// The character's current persistable sheet (what a save would carry forward).
    pub fn sheet(&self) -> CharacterSheet {
        self.character.sheet()
    }
}

/// **The character-bound dungeon offering** — wraps offering #0 ([`DungeonOffering`]) with a
/// persistent [`Character`] bound to each player's [`DreggIdentity`] through a [`CharacterStore`].
/// [`open`](Self::open) LOADS the returning player's character (or a fresh one); [`advance`](Self::advance)
/// runs a real dungeon turn AND, iff it lands a qualifying outcome, grants earned XP via a real
/// gated character turn; [`save`](Self::save) persists the carried character. Additive: the
/// underlying [`DungeonOffering`] and its sessions are untouched.
pub struct AdventurerOffering<S: CharacterStore> {
    dungeon: DungeonOffering,
    store: S,
}

impl<S: CharacterStore> AdventurerOffering<S> {
    /// A character-bound offering over `store` (free-tier dungeon).
    pub fn new(store: S) -> Self {
        AdventurerOffering {
            dungeon: DungeonOffering::new(),
            store,
        }
    }

    /// A character-bound offering over an explicit [`DungeonOffering`] (e.g. a paid tier) + `store`.
    pub fn with_offering(dungeon: DungeonOffering, store: S) -> Self {
        AdventurerOffering { dungeon, store }
    }

    /// Borrow the underlying [`CharacterStore`] (e.g. to check whether a player is returning).
    pub fn store(&self) -> &S {
        &self.store
    }

    /// **Open a run for `who`** — LOAD their persisted character (a fresh one for a new player),
    /// deploy the dungeon session + the seeded character cell. A returning player RESUMES their
    /// carried level/XP/class; a new player starts fresh (level 1, no class).
    pub fn open(
        &self,
        who: DreggIdentity,
        cfg: SessionConfig,
    ) -> Result<AdventureSession, OfferingError> {
        let sheet = self.store.load(&who);
        let dungeon = self.dungeon.open(cfg)?;
        let character = Character::open(who.clone(), sheet);
        Ok(AdventureSession {
            who,
            dungeon,
            character,
        })
    }

    /// **Advance the dungeon by one real turn; earn XP on a real outcome.** Resolves `input` on the
    /// dungeon substrate (attributed to the run's player); iff it LANDS a qualifying outcome
    /// (bloodying the warden, seizing the hoard), grants the earned XP to the character via a real
    /// gated turn. A refused dungeon move earns NOTHING (the anti-ghost binding: no real outcome,
    /// no XP). Returns the dungeon move's [`Outcome`] (the character grant is a side effect the
    /// render reflects).
    pub fn advance(&self, session: &mut AdventureSession, input: Action) -> Outcome {
        // Capture the room + choice BEFORE the move (the dungeon advances past it on a land).
        let room = session.dungeon.current_passage_name();
        let choice_index = if input.arg >= 0 {
            Some(input.arg as usize)
        } else {
            None
        };

        let out = self
            .dungeon
            .advance(&mut session.dungeon, input, session.who.clone());

        if out.landed() {
            if let (Some(room), Some(ci)) = (room, choice_index) {
                if let Some(xp) = xp_reward(&room, ci) {
                    // A real qualifying outcome landed → grant the earned XP as a real gated turn.
                    let _ = session.character.grant_xp(xp);
                }
            }
        }
        out
    }

    /// **Level the character up by one** — the existing `FieldGte(xp, threshold)`-gated turn.
    /// Refused without the earned (possibly carried) XP.
    pub fn level_up(&self, session: &AdventureSession) -> Result<TurnReceipt, WorldError> {
        session.character.level_up()
    }

    /// **Choose the character's class** (the one-time `WriteOnce` creation move).
    pub fn choose_class(
        &self,
        session: &AdventureSession,
        class_id: u64,
    ) -> Result<TurnReceipt, WorldError> {
        session.character.choose_class(class_id)
    }

    /// **Save the run's character back to the store** — the carried level/XP/class the next
    /// [`open`](Self::open) for the same identity RESUMES.
    pub fn save(&mut self, session: &AdventureSession) {
        self.store.save(&session.who, session.character.sheet());
    }

    /// **Re-verify the dungeon's committed chain by replay** (delegates to the underlying
    /// [`DungeonOffering`] — the character binding does not touch the dungeon's verify chain).
    pub fn verify(&self, session: &AdventureSession) -> VerifyReport {
        self.dungeon.verify(&session.dungeon)
    }

    /// **Render the run as a deos affordance [`Surface`]** — a Character panel (level / XP / class /
    /// next-level floor) atop the dungeon room render. A returning session reflects the carried
    /// character.
    pub fn render(&self, session: &AdventureSession) -> Surface {
        let c = session.character.sheet();
        let next = c.level + 1;
        let to_next = xp_threshold(next);
        let xp_line = if to_next == u64::MAX {
            format!("XP {} · level {} (max)", c.xp, c.level)
        } else {
            format!(
                "XP {} · level {} · next level at {}",
                c.xp, c.level, to_next
            )
        };

        let character_panel = ViewNode::Section {
            title: format!("{} — {}", short_name(&session.who), c.class_name()),
            tag: "genuine".to_string(),
            children: vec![ViewNode::Text(xp_line)],
        };

        // The dungeon's own room render (prose + party state + affordances), nested beneath.
        let Surface(room) = self.dungeon.render(&session.dungeon);

        Surface(ViewNode::Section {
            title: "Adventure".to_string(),
            tag: "accent".to_string(),
            children: vec![character_panel, room],
        })
    }
}

/// A short display handle for an identity (the first 8 chars of the opaque key) — for a render
/// title, not an authority (the executor signs with the world cap, not this label).
fn short_name(who: &DreggIdentity) -> String {
    let s = who.as_str();
    if s.len() > 8 {
        format!("{}…", &s[..8])
    } else {
        s.to_string()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_app_framework::{Effect, field_from_u64};
    use dungeon_on_dregg::{KP_CLAIM_RED, KP_DESCEND, KP_PRESS_ON};

    fn choose(arg: usize) -> Action {
        Action::new("move", crate::dungeon::TURN_CHOOSE, arg as i64, true)
    }

    /// Drive the winning line that EARNS XP: two blows bloody the gate-warden (+40 each), then
    /// press on, claim the crown, descend, and seize the hoard (+120). Returns the session with
    /// the earned XP on the (persistent) character cell.
    fn play_earning_run<S: CharacterStore>(
        off: &AdventurerOffering<S>,
        session: &mut AdventureSession,
    ) {
        // gatehall — bloody the warden twice (hp 50→30→10); each landed blow earns XP.
        assert!(off.advance(session, choose(KP_TRADE_BLOWS)).landed());
        assert!(off.advance(session, choose(KP_TRADE_BLOWS)).landed());
        assert!(off.advance(session, choose(KP_PRESS_ON)).landed());
        // hall — claim the crown (no XP), descend.
        assert!(off.advance(session, choose(KP_CLAIM_RED)).landed());
        assert!(off.advance(session, choose(KP_DESCEND)).landed());
        // sanctum — seize the hoard (+120 XP), ending the run.
        assert!(off.advance(session, choose(KP_SEIZE)).landed());
    }

    /// A NEW player starts fresh (level 1, no class); a full earning run grants XP on real landed
    /// outcomes; the totals match the reward table (2 blows + the hoard).
    #[test]
    fn new_player_starts_fresh_and_earns_xp_on_real_outcomes() {
        let off = AdventurerOffering::new(InMemoryCharacterStore::new());
        let who = DreggIdentity("player-alice-key".to_string());
        let mut s = off
            .open(who.clone(), SessionConfig::with_seed(3))
            .expect("open");

        // Fresh: level 1 (the free starting level-up), no class, no XP.
        assert_eq!(
            s.character().level(),
            1,
            "a new adventurer begins at level 1"
        );
        assert_eq!(s.character().xp(), 0, "fresh: no XP");
        assert_eq!(s.character().class(), 0, "fresh: unclassed");

        off.choose_class(&s, WARRIOR).expect("choose a class");
        assert_eq!(s.character().class(), WARRIOR);

        play_earning_run(&off, &mut s);

        // Two bloodied blows + the hoard = 40 + 40 + 120.
        assert_eq!(
            s.character().xp(),
            2 * XP_BLOODY_WARDEN + XP_SEIZE_HOARD,
            "XP earned from real landed outcomes only"
        );
        assert!(off.verify(&s).verified, "the dungeon chain re-verifies");
    }

    /// A dungeon move the executor REFUSES earns NO XP (the anti-ghost binding: no real outcome,
    /// no XP). The killing third blow (hp 10 − 20) is a real refusal; the character's XP is
    /// unchanged across it. Non-vacuous: the two survivable blows before it DID earn.
    #[test]
    fn a_refused_dungeon_move_earns_no_xp() {
        let off = AdventurerOffering::new(InMemoryCharacterStore::new());
        let who = DreggIdentity("player-bob-key".to_string());
        let mut s = off.open(who, SessionConfig::with_seed(7)).expect("open");

        assert!(off.advance(&mut s, choose(KP_TRADE_BLOWS)).landed()); // hp 50→30, +40
        assert!(off.advance(&mut s, choose(KP_TRADE_BLOWS)).landed()); // hp 30→10, +40
        let earned_before = s.character().xp();
        assert_eq!(earned_before, 2 * XP_BLOODY_WARDEN);

        // The killing blow (10 − 20 ≤ 0) is a REAL executor refusal → NO XP granted.
        let out = off.advance(&mut s, choose(KP_TRADE_BLOWS));
        assert!(!out.landed(), "the killing blow is refused, got {out:?}");
        assert_eq!(
            s.character().xp(),
            earned_before,
            "a refused outcome earns no XP (anti-ghost)"
        );
    }

    /// A FORGED XP grant is REFUSED. XP moves ONLY through the sanctioned `GAIN_XP_METHOD`; a
    /// grant presented under any other method is a real executor refusal (default-deny). Non-
    /// vacuous: the SAME XP-slot write via the sanctioned `grant_xp` commits.
    #[test]
    fn a_forged_xp_grant_is_refused() {
        let off = AdventurerOffering::new(InMemoryCharacterStore::new());
        let who = DreggIdentity("player-cheater-key".to_string());
        let s = off.open(who, SessionConfig::with_seed(5)).expect("open");

        let cell = s.character().hero_cell().cell_id();
        // Forge: write the XP slot to a huge value under a NON-sanctioned method → refused.
        let forged = s.character().hero_cell().apply_raw(
            "cheat/inject_xp",
            vec![Effect::SetField {
                cell,
                index: progression::XP_SLOT as usize,
                value: field_from_u64(9_999),
            }],
        );
        assert!(
            matches!(forged, Err(WorldError::Refused(_))),
            "a forged XP grant (unknown method) is refused, got {forged:?}"
        );
        assert_eq!(s.character().xp(), 0, "anti-ghost: no forged XP committed");

        // The SAME XP-slot write via the sanctioned grant commits — non-vacuous.
        s.character()
            .grant_xp(60)
            .expect("the sanctioned grant commits");
        assert_eq!(s.character().xp(), 60);
    }

    /// Level-up is the existing `FieldGte(xp, threshold)` gate. After the earning run the character
    /// has 200 XP: leveling to 2 (needs 100) commits; leveling to 3 (needs 250) is a real refusal.
    #[test]
    fn level_up_is_xp_gated_premature_refused() {
        let off = AdventurerOffering::new(InMemoryCharacterStore::new());
        let who = DreggIdentity("player-dana-key".to_string());
        let mut s = off.open(who, SessionConfig::with_seed(9)).expect("open");
        off.choose_class(&s, ROGUE).expect("class");
        play_earning_run(&off, &mut s);
        assert_eq!(s.character().xp(), 200);
        assert_eq!(s.character().level(), 1);

        off.level_up(&s).expect("level 2 (xp 200 >= 100)");
        assert_eq!(s.character().level(), 2);

        // Premature: level 3 needs xp >= 250; with 200 it is a REAL refusal.
        let premature = off.level_up(&s);
        assert!(
            matches!(premature, Err(WorldError::Refused(_))),
            "a premature level-up is refused, got {premature:?}"
        );
        assert_eq!(s.character().level(), 2, "anti-ghost: still level 2");
    }

    /// THE CROSS-RUN CARRY: the SAME identity resumes its carried character across the run
    /// boundary (level/XP/class persist via the store seam); a DIFFERENT identity gets a fresh one.
    #[test]
    fn character_carries_across_runs_by_identity() {
        let mut off = AdventurerOffering::new(InMemoryCharacterStore::new());
        let alice = DreggIdentity("player-alice-key".to_string());

        // ── Run 1: fresh Mage earns 200 XP and levels to 2, then saves. ──
        {
            let mut s = off
                .open(alice.clone(), SessionConfig::with_seed(3))
                .expect("open run 1");
            assert!(!off.store().has(&alice), "alice is a new player");
            off.choose_class(&s, MAGE).expect("class");
            play_earning_run(&off, &mut s);
            off.level_up(&s).expect("level 2");
            assert_eq!(s.character().level(), 2);
            assert_eq!(s.character().xp(), 200);
            off.save(&s);
        }
        assert!(off.store().has(&alice), "alice's character is persisted");

        // ── Run 2: the SAME identity RESUMES the carried character. ──
        {
            let s = off
                .open(alice.clone(), SessionConfig::with_seed(42))
                .expect("open run 2");
            assert_eq!(
                s.character().level(),
                2,
                "carried level across the run boundary"
            );
            assert_eq!(
                s.character().xp(),
                200,
                "carried XP across the run boundary"
            );
            assert_eq!(
                s.character().class(),
                MAGE,
                "carried class across the run boundary"
            );

            // The carried class unlocks its ability (FieldEquals(class, MAGE)) — a returning perk.
            s.character()
                .use_ability(MAGE)
                .expect("the carried Mage casts its ability");

            // A re-class is refused (WriteOnce carried) — the class is frozen across runs.
            assert!(
                matches!(
                    s.character().choose_class(WARRIOR),
                    Err(WorldError::Refused(_))
                ),
                "a carried class cannot be re-chosen"
            );

            // Earn more and cross the level-3 floor the carried XP could not reach alone.
            s.character().grant_xp(60).expect("earn 60 more (200→260)");
            off.level_up(&s)
                .expect("level 3 (xp 260 >= 250) — carried XP made this reachable");
            assert_eq!(s.character().level(), 3);
        }

        // ── A DIFFERENT identity is a fresh character. ──
        {
            let bob = DreggIdentity("player-bob-key".to_string());
            let s = off
                .open(bob, SessionConfig::with_seed(3))
                .expect("open bob");
            assert_eq!(s.character().level(), 1, "a different identity is fresh");
            assert_eq!(s.character().xp(), 0);
            assert_eq!(s.character().class(), 0);
        }
    }

    /// HARDCORE MODE: a character's death is WriteOnce-FINAL and PERSISTS across the run
    /// boundary. A hardcore run that ends in defeat perishes the character (a real
    /// committed death); a resurrection is refused; a dead character earns nothing; and a
    /// save/load carries the death forward — a re-opened dead character LOADS dead and
    /// stays dead. This is the un-forgeable fact a no-death-streak leaderboard proves.
    #[test]
    fn hardcore_death_is_writeonce_final_and_persists_across_runs() {
        let mut off = AdventurerOffering::new(InMemoryCharacterStore::new());
        let who = DreggIdentity("player-hardcore-key".to_string());

        // ── Run 1: earn, then die in defeat; the death is final within the run. ──
        {
            let mut s = off
                .open(who.clone(), SessionConfig::with_seed(3))
                .expect("open");
            off.choose_class(&s, WARRIOR).expect("class");
            assert!(off.advance(&mut s, choose(KP_TRADE_BLOWS)).landed()); // earn 40 XP
            assert_eq!(s.character().xp(), XP_BLOODY_WARDEN);
            assert!(!s.character().is_dead(), "alive so far");

            // The hardcore run is LOST → the character perishes (a real committed death).
            s.character().perish().expect("the death turn commits");
            assert!(s.character().is_dead(), "the character is dead");

            // Resurrection refused; a dead character earns nothing.
            assert!(
                matches!(
                    s.character().attempt_resurrect(),
                    Err(WorldError::Refused(_))
                ),
                "resurrecting a dead hardcore character is refused"
            );
            assert!(
                matches!(s.character().grant_xp(1000), Err(WorldError::Refused(_))),
                "a dead character earns no XP"
            );
            assert_eq!(s.character().xp(), XP_BLOODY_WARDEN, "XP frozen at death");
            off.save(&s); // persist the death.
        }

        // ── Run 2: the SAME identity LOADS dead — the death carried across the boundary. ──
        {
            let s = off
                .open(who.clone(), SessionConfig::with_seed(9))
                .expect("reopen");
            assert!(
                s.character().is_dead(),
                "a saved-dead hardcore character loads dead — the no-death streak is broken forever"
            );
            assert!(
                matches!(
                    s.character().attempt_resurrect(),
                    Err(WorldError::Refused(_))
                ),
                "still un-resurrectable after the run boundary"
            );
            assert!(
                matches!(s.character().grant_xp(50), Err(WorldError::Refused(_))),
                "a carried-dead character still earns nothing"
            );
        }
    }

    /// META-PROGRESSION-ON-DEATH: a LOST run advances you. A hardcore run that ends in a deep death
    /// banks the meta-currency (a real gated grant, tied to depth), buys a persistent unlock, and
    /// SAVES — and a NEXT run for the same identity STARTS with the earned unlock (echoes + boon
    /// carry via the store). Non-vacuous + executor-refereed: a LIVING character earns no echoes (a
    /// won / unfinished run grants none), a claim without enough echoes is refused, and a forged
    /// grant (unknown method) is refused — the teeth bite.
    #[test]
    fn meta_progression_on_death_grants_a_persistent_unlock_the_next_run_carries() {
        let mut off = AdventurerOffering::new(InMemoryCharacterStore::new());
        let who = DreggIdentity("player-fallen-key".to_string());

        // ── Run 1: a hardcore run LOST deep — perish, bank echoes, buy the boon, save. ──
        {
            let s = off
                .open(who.clone(), SessionConfig::with_seed(3))
                .expect("open run 1");
            off.choose_class(&s, WARRIOR).expect("class");
            assert_eq!(s.character().echoes(), 0, "fresh: no echoes");
            assert!(!s.character().has_boon(), "fresh: no unlock");

            // A LIVING character (a won / unfinished run) earns NO echoes — the grant needs a death.
            assert!(
                matches!(s.character().grant_echoes(6), Err(WorldError::Refused(_))),
                "a living character earns no echoes (a won/unfinished run advances none)"
            );
            // A claim with no accrued echoes is refused (unlock-without-currency).
            assert!(
                matches!(s.character().claim_boon(), Err(WorldError::Refused(_))),
                "a boon claim without the echoes is refused"
            );
            // A forged grant under an unknown method is a real executor refusal (default-deny).
            let cell = s.character().hero_cell().cell_id();
            let forged = s.character().hero_cell().apply_raw(
                "cheat/inject_echoes",
                vec![Effect::SetField {
                    cell,
                    index: dungeon_on_dregg::meta::ECHOES_SLOT as usize,
                    value: field_from_u64(9_999),
                }],
            );
            assert!(
                matches!(forged, Err(WorldError::Refused(_))),
                "a forged echoes grant is refused, got {forged:?}"
            );
            assert_eq!(s.character().echoes(), 0, "anti-ghost: no forged echoes");

            // The run ENDS IN DEATH → perish, then bank echoes for the depth reached (deep = enough).
            s.character().perish().expect("the death commits");
            s.character()
                .grant_echoes(6)
                .expect("a real death funds the echoes grant");
            let banked = s.character().echoes();
            assert!(
                banked >= dungeon_on_dregg::meta::BOON_PRICE,
                "a deep death banks over the boon price: {banked}"
            );

            // The accrued echoes BUY the persistent unlock.
            s.character()
                .claim_boon()
                .expect("enough echoes buys the boon");
            assert!(s.character().has_boon(), "the boon is claimed");

            off.save(&s); // persist echoes + boon (and the death).
        }

        // ── Run 2: the SAME identity RESUMES — a next run STARTS with the earned unlock. ──
        {
            let s = off
                .open(who.clone(), SessionConfig::with_seed(9))
                .expect("open run 2");
            assert!(
                s.character().echoes() >= dungeon_on_dregg::meta::BOON_PRICE,
                "carried echoes across the run boundary: {}",
                s.character().echoes()
            );
            assert!(
                s.character().has_boon(),
                "the NEXT run starts with the earned unlock (the boon carried by identity)"
            );
        }

        // ── A DIFFERENT identity is a fresh character with no meta-progression. ──
        {
            let stranger = DreggIdentity("player-stranger-key".to_string());
            let s = off
                .open(stranger, SessionConfig::with_seed(3))
                .expect("open stranger");
            assert_eq!(
                s.character().echoes(),
                0,
                "a different identity has no echoes"
            );
            assert!(!s.character().has_boon(), "and no carried unlock");
        }
    }

    /// A DEEPER death banks strictly MORE meta-currency (the depth-scaled grant, driven end-to-end):
    /// two identities perish, the one who died deeper carries more echoes across the run boundary.
    #[test]
    fn a_deeper_death_carries_more_meta_currency() {
        let mut off = AdventurerOffering::new(InMemoryCharacterStore::new());
        let shallow = DreggIdentity("player-shallow-key".to_string());
        let deep = DreggIdentity("player-deep-key".to_string());

        for (who, depth) in [(&shallow, 2u64), (&deep, 7u64)] {
            let s = off
                .open(who.clone(), SessionConfig::with_seed(3))
                .expect("open");
            s.character().perish().expect("death");
            s.character().grant_echoes(depth).expect("grant on death");
            off.save(&s);
        }

        let shallow_carry = off
            .open(shallow, SessionConfig::with_seed(1))
            .expect("reopen shallow")
            .character()
            .echoes();
        let deep_carry = off
            .open(deep, SessionConfig::with_seed(1))
            .expect("reopen deep")
            .character()
            .echoes();
        assert!(
            deep_carry > shallow_carry,
            "a deeper death carries more meta-currency: deep {deep_carry} > shallow {shallow_carry}"
        );
    }

    /// The render reflects the (carried) character: level / XP / class appear in the surface.
    #[test]
    fn render_shows_the_character() {
        let mut off = AdventurerOffering::new(InMemoryCharacterStore::new());
        let who = DreggIdentity("player-echo-key".to_string());
        {
            let mut s = off
                .open(who.clone(), SessionConfig::with_seed(3))
                .expect("open");
            off.choose_class(&s, WARRIOR).expect("class");
            play_earning_run(&off, &mut s);
            off.level_up(&s).expect("level 2");
            off.save(&s);
        }
        let s = off.open(who, SessionConfig::with_seed(3)).expect("reopen");
        let surface = off.render(&s);
        let text = format!("{:?}", surface.view());
        assert!(
            text.contains("Warrior"),
            "render shows the carried class: {text}"
        );
        assert!(
            text.contains("level 2"),
            "render shows the carried level: {text}"
        );
        assert!(
            text.contains("XP 200"),
            "render shows the carried XP: {text}"
        );
    }
}
