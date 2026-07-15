//! # `dreggnet-adventure` — THE DESCENT, integrated: the flagship as ONE coherent,
//! **reusable** verifiable RPG loop over the feature systems.
//!
//! `dreggnet-saga` proved the eight feature crates COMPOSE — but over a *synthetic* errand
//! universe built for the proof, and only inside a `#[cfg(test)]` driver. This crate goes one
//! level up on two axes at once:
//!
//! * it drives the REAL [`dreggnet_offerings::daily_descent::DailyDescentOffering`] — the
//!   beacon-seeded permadeath run, the persistent hardcore
//!   [`Character`](dreggnet_offerings::character::Character), the no-cheat board — as the game
//!   that exercises every feature system, its ONE run object handed off object-identically;
//! * it exposes that loop as a REUSABLE library API, not a test. [`Adventure::daily`] +
//!   [`Adventure::play`] play the whole honest loop through the real layers and return an
//!   [`AdventureReport`] a consumer (a web front, a CLI, another crate) can render. The driven
//!   `#[cfg(test)]` module now *exercises the public API* and the non-vacuous refusal legs; it
//!   is no longer the only way to reach the loop.
//!
//! ## The loop (each `->` a real committed handoff on the shared substrate)
//!
//! **BEFORE the run — the loadout + the gate:**
//! 1. a **party** musters ([`dreggnet_party`]) — four seated roles, each cap = its mandate;
//! 2. the player equips **gear** ([`dreggnet_gear::Loadout`]) and brings a **companion**
//!    ([`dreggnet_companion::CompanionRoost`]) — the run LOADOUT, both owned assets keyed to
//!    the ONE [`PlayerIdentity`]; the gear ability + level-N companion buff aid the run
//!    CROSS-CELL (each a real `ObservedFieldEquals`, refused without the loadout, non-vacuous);
//! 3. a **faction**-gated, **Completion**-gated quest ([`CompletionGatedQuest`]) posts the
//!    Descent-quest: its START opens ONLY on real Ember standing (the faction rep cell's
//!    cross-cell gate), and its TURN-IN accepts ONLY the run's verified [`Completion`] bound to
//!    THIS day's [`Universe`] — a dedicated Completion-gated giver, not a bare re-verify.
//!
//! **THE RUN — the actual DailyDescentOffering:**
//! 4. the day's beacon-seeded permadeath world is opened + driven to the WIN on the real
//!    executor ([`drive_descent_to_win`]) — every move a real committed turn;
//! 5. the run's loot drops as owned **assets** ([`dungeon_on_dregg::loot`] — a real fair draw
//!    bound to the run's committed day-seed).
//!
//! **AFTER — progression out (all off the ONE run object):**
//! 6. the run's single [`ugc_dregg::Completion`] **earns a CHEEVO** ([`dreggnet_cheevo`]),
//!    **sums into the GUILD** ([`dreggnet_guild`]), and **turns in the QUEST** — the SAME
//!    `&universe` + `&completion` into all three; a forged run earns none, sums into none,
//!    turns in none;
//! 7. the run's loot is **forged** ([`dreggnet_craft`]) into an item and **traded**
//!    ([`dreggnet_trade`]) to a buyer — the SAME crafted note-cell craft -> trade -> buyer;
//! 8. a **season champion** ([`dregg_season`]) — the verified win enters the season-scoped
//!    no-cheat board and, ranking top-N, earns the hall-of-fame champion cheevo.
//!
//! ## The object-identity spine (the whole point)
//!
//! ONE object flows the whole way, never re-derived: **the run** (one `Completion`/`Universe`
//! the cheevo anchors, the guild counts, the quest turns in on, the season ranks); **the item**
//! (one `AssetId` note-cell minted as loot, forged, and traded in ONE ledger); **the player**
//! (one [`PlayerIdentity`] that is the party seat's ed25519 ballot key, the gear owner, the
//! companion owner, the guild member, and the Descent player at once).
//!
//! ## Honest scope — wired vs. named reconciliations
//!
//! WIRED + DRIVEN, and now reachable through the public [`Adventure`] API (not only under
//! `cargo test`): the faction-gated + Completion-gated quest, the real DailyDescentOffering run
//! driven to the win, the gear ability + companion buff aiding cross-cell, the ONE Completion
//! earning the cheevo + summing the guild + turning in the quest, the looted note crafting +
//! trading as the SAME note-cell, the season champion cheevo, and the ONE identity across seat
//! / gear / companion / guild.
//!
//! NAMED RECONCILIATIONS (deliberate, additive follow-ups — require cross-crate change, so not
//! built here; see the crate's `remaining`):
//! * **The aid cells vs. the literal Descent world-cell.** The gear ability and the companion
//!   buff each host their OWN run-aid cell (the [`multicell`](dungeon_on_dregg::multicell)
//!   cross-cell pattern the two crates ship), gated on the equipped gear / the level-N
//!   companion. Binding those gates onto the ONE `DailyDescentOffering` world-cell (a single
//!   shared executor for run + gear + companion) needs an executor handle
//!   `dreggnet-offerings` does not yet expose — a `dreggnet-gear` / `dreggnet-companion` /
//!   `dreggnet-offerings` reconciliation. The cross-cell PREDICATE is real here.
//! * **The tavern front, kept light.** `dreggnet-tavern` pulls `dregg-node`/deos-host (mozjs),
//!   is async, and needs an `_exit(0)` to dodge a SpiderMonkey teardown SIGSEGV — pulling that
//!   elephant into this synchronous loop would make the green gate heavy + flaky. Presence +
//!   party-up are proven in `dreggnet-tavern`'s own e2e; the prelude here is the light
//!   [`dreggnet_party`] muster. Named, deliberately not pulled.

use dreggnet_offerings::Outcome;
use dreggnet_offerings::character::InMemoryCharacterStore;
use dreggnet_offerings::daily_descent::{
    CORRIDOR_ON, DailyDescentOffering, DailyRun, GATE_HEAL, GATE_MEASURED, GATE_PRESS, HOARD_FORCE,
    HOARD_SEIZE, KEY_TAKE,
};
use procgen_dregg::CommittedSeed;

use dregg_types::PublicKey;
use dungeon_on_dregg::collective::Custodian;
use ugc_dregg::{Completion, Universe, UniverseId, verify_completion};

pub use dreggnet_offerings::DreggIdentity;

// ─────────────────────────────────────────────────────────────────────────────
// The ONE canonical player identity — folded in from `dreggnet-saga` (this crate no
// longer depends on saga; the two weaves overlapped only on this adapter).
// ─────────────────────────────────────────────────────────────────────────────

/// A single canonical player identity the feature crates all key on — the adapter that
/// unifies the three key representations the loop meets:
///
/// * the **party seat**'s ed25519 CUSTODY key ([`dungeon_on_dregg::collective::Custodian`],
///   its ballot identity in [`dreggnet_party`]);
/// * the **guild member** handle ([`DreggIdentity`], what [`dreggnet_guild`] admits and counts
///   clears for, and the [`DailyDescentOffering`] key the run opens under);
/// * the **asset holder** label ([`dreggnet_asset::AssetWorld`]'s per-label holder key, shared
///   by gear / companion / craft / trade / cheevo).
///
/// A small adapter, not a redesign: all three already derive from one `name`, so ONE
/// `PlayerIdentity` yields the seat key, the member, AND the holder — the same actor present
/// across the crates by a single object, not three look-alikes stitched by convention. (A
/// production deployment mints the custody secret in the seat's own device; the demo derivation
/// is deterministic so the loop reproduces stable identities.)
///
/// Reused VERBATIM from the shape `dreggnet-saga` proved (reconciliation #3), folded in here so
/// the flagship loop no longer carries the saga dependency.
#[derive(Clone, Debug)]
pub struct PlayerIdentity {
    name: String,
}

impl PlayerIdentity {
    /// The canonical player named `name` (the single derivation input the three
    /// representations share).
    pub fn new(name: impl Into<String>) -> Self {
        PlayerIdentity { name: name.into() }
    }

    /// The player's canonical name (the derivation input).
    pub fn name(&self) -> &str {
        &self.name
    }

    /// The **asset-layer holder label** — the key [`dreggnet_asset::AssetWorld`] (and thus
    /// gear / companion / craft / trade) mints, transfers, and owns notes under.
    pub fn holder_label(&self) -> &str {
        &self.name
    }

    /// The **guild member handle** — what [`dreggnet_guild`] admits and records clears for, and
    /// the identity a [`DailyDescentOffering`] run opens under.
    pub fn guild_member(&self) -> DreggIdentity {
        DreggIdentity(self.name.clone())
    }

    /// The **party seat's custody keypair** — the ed25519 identity a [`dreggnet_party`] seat
    /// signs its ballots with.
    pub fn custodian(&self) -> Custodian {
        Custodian::demo(self.name.as_str())
    }

    /// The party seat's electorate PUBLIC key (its ballot identity) — the same key
    /// [`dreggnet_party::Seat::electorate_seat`] carries for a seat of this name.
    pub fn seat_pk(&self) -> PublicKey {
        self.custodian().public_key()
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// The day-seed + the raw run driver (reusable building blocks).
// ─────────────────────────────────────────────────────────────────────────────

/// **Today's Descent day-seed** — a fixed committed seed standing in for a verified drand
/// day (the beacon-fetch is `dreggnet_offerings`' own named client seam). The day's world is a
/// pure function of it, so the loop reproduces a stable, winnable descent.
pub fn today_seed() -> CommittedSeed {
    CommittedSeed::from_bytes([0x7D; 32])
}

/// **A fresh hardcore Descent offering** over an in-memory character store — the real
/// flagship offering (permadeath ON; a fall PERISHES the persistent character). The loop
/// plays entirely `Local` (private + fast); settling to a node is the offering's own opt-in.
pub fn descent_offering() -> DailyDescentOffering<InMemoryCharacterStore> {
    DailyDescentOffering::new(InMemoryCharacterStore::new())
}

/// **Drive the day's descent to the WIN** — the real player loop, each step a real committed
/// [`DailyDescentOffering::advance`] turn on the day's world-cell. It reads the committed
/// narrative vars (`warden_hp` / `hp` / `heals_used`) and plays the honest survival line: fell
/// the warden with measured blows (binding wounds with the one field-dressing when a blow
/// would otherwise strand the run), press past the felled warden, take the key, press through
/// the beacon-drawn corridors, force the key-gated hoard-door, and seize the hoard (the win).
/// Every move is executor-refereed; a refusal aborts with the executor's own reason (no LARP).
pub fn drive_descent_to_win(
    offering: &DailyDescentOffering<InMemoryCharacterStore>,
    run: &mut DailyRun,
) -> Result<(), String> {
    // A bound on turns so a mis-driven run fails loud instead of looping forever.
    for _ in 0..64 {
        let Some(room) = run.current_room() else {
            return Ok(()); // the run has ended.
        };
        let choice = if room == "gate" {
            let warden = run.read_var("warden_hp");
            let hp = run.read_var("hp");
            let heals = run.read_var("heals_used");
            if warden == 0 {
                GATE_PRESS
            } else if hp >= 16 && (hp - 15 >= 16 || warden <= 15) {
                // Safe measured blow: either we can keep fighting, or this one fells the warden.
                GATE_MEASURED
            } else if heals == 0 {
                // A blow would strand us below the floor and the warden still stands — bind wounds.
                GATE_HEAL
            } else if hp >= 16 {
                GATE_MEASURED
            } else {
                return Err(format!(
                    "stranded at the warden (hp {hp}, warden {warden}, heals {heals})"
                ));
            }
        } else if room == "keyroom" {
            KEY_TAKE
        } else if room.starts_with("corridor") {
            CORRIDOR_ON
        } else if room == "hoardgate" {
            HOARD_FORCE
        } else if room == "hoard" {
            HOARD_SEIZE
        } else {
            return Err(format!("unexpected room `{room}`"));
        };

        match offering.advance(run, choice) {
            Outcome::Landed { ended, .. } => {
                if ended {
                    return Ok(());
                }
            }
            Outcome::Refused(why) => {
                return Err(format!("move refused at `{room}` (choice {choice}): {why}"));
            }
        }
    }
    Err("the descent did not end within the turn bound".to_string())
}

/// **A run-bound loot seed** — domain-separated over the run's committed day-seed and its
/// final committed fingerprint, so the run's loot drops are provably THIS run's (a different
/// day / a different run draws different loot). Used both as the fair-draw context for the
/// [`dungeon_on_dregg::loot`] vault and as the mint seed of the forge's material drops.
pub fn loot_seed(run: &DailyRun, idx: u64) -> Vec<u8> {
    let mut h = blake3::Hasher::new_derive_key("dreggnet-adventure/loot-drop/v1");
    h.update(run.day().seed.as_bytes());
    h.update(&run.final_commitment());
    h.update(&idx.to_le_bytes());
    h.finalize().as_bytes().to_vec()
}

/// **Open + drive a full winning Descent run for `who`** — the shared entry the API and the
/// after-run handoffs reuse. Returns the offering (owning the character store) and the WON run,
/// or the executor's own reason if the run could not open or be driven to the win. Non-panicking
/// (a reusable library entry, unlike a test's `expect`).
pub fn play_a_winning_descent(
    who: &PlayerIdentity,
) -> Result<(DailyDescentOffering<InMemoryCharacterStore>, DailyRun), String> {
    let offering = descent_offering();
    let mut run = offering
        .open_from_seed(who.guild_member(), today_seed())
        .map_err(|e| format!("the day's descent did not open: {e:?}"))?;
    drive_descent_to_win(&offering, &mut run)?;
    if !run.is_won() {
        return Err("the driven run did not reach the hoard (the win)".to_string());
    }
    if run.is_dead() {
        return Err("a survived win perished the character (permadeath tripped)".to_string());
    }
    Ok((offering, run))
}

/// **Build the ONE run object the after-run handoffs share** — the day's [`Universe`] and the
/// run's single [`Completion`], authored + played by the one identity. Re-verifies the run's own
/// committed chain and asserts the completion is bound to THIS day's universe (object identity)
/// before handing it off. Non-panicking.
pub fn run_object(
    offering: &DailyDescentOffering<InMemoryCharacterStore>,
    run: &DailyRun,
    who: &PlayerIdentity,
) -> Result<(Universe, Completion), String> {
    if !offering.verify(run).verified {
        return Err("the won run's committed chain did not re-verify".to_string());
    }
    let universe = run
        .day()
        .universe(who.name())
        .map_err(|e| format!("the day did not publish as a universe: {e:?}"))?;
    let completion = offering
        .completion(run, who.name(), who.name())
        .map_err(|e| format!("the won run did not build its completion: {e:?}"))?;
    if completion.universe != universe.id() {
        return Err("the completion is not bound to THIS day's universe".to_string());
    }
    Ok((universe, completion))
}

// ─────────────────────────────────────────────────────────────────────────────
// A dedicated Completion-gated quest giver (closes the "quest turn-in re-verifies
// rather than a dedicated Completion-gated giver" gap, within this crate).
// ─────────────────────────────────────────────────────────────────────────────

/// **The Descent-quest as a dedicated, doubly-gated giver.** It composes two real gates around
/// the one run:
///
/// * the **START** is [`dreggnet_quest::giver::FactionGatedGiverWorld`] — a real cross-cell
///   `ObservedFieldEquals` on a faction-standing cell. A player with no Ember standing is
///   REFUSED the start ([`start`](Self::start) fails closed); earning rep opens it.
/// * the **TURN-IN** ([`turn_in`](Self::turn_in)) gates directly on an arbitrary
///   [`Completion`]: it accepts ONLY once the quest is STARTED, ONLY a completion whose
///   `universe` matches the day this quest was posted against (object identity), and ONLY a
///   completion the shared [`verify_completion`] no-cheat gate re-executes to the win. A forged
///   run, a run for the wrong day, or a not-yet-started quest all fail closed, and the quest can
///   be turned in at most once.
///
/// Unlike a bare `verify_completion` at the call-site, this is a stateful giver whose turn-in is
/// the gate — the object the cheevo + guild also consume, but here bound to a posted quest with
/// its own admission rules.
pub struct CompletionGatedQuest {
    giver: dreggnet_quest::giver::FactionGatedGiverWorld,
    /// The day's universe id this quest was posted against — the turn-in's object-identity pin.
    universe_id: UniverseId,
    turned_in: bool,
}

impl CompletionGatedQuest {
    /// Post the Descent-quest bound to the day's `universe` — the run this quest turns in on.
    /// The START stays faction-gated (deployed closed); the TURN-IN is pinned to this universe.
    pub fn post(universe: &Universe) -> Self {
        CompletionGatedQuest {
            giver: dreggnet_quest::giver::FactionGatedGiverWorld::deploy(),
            universe_id: universe.id(),
            turned_in: false,
        }
    }

    /// Whether the quest's START has opened (real faction standing granted the Descent-quest).
    pub fn is_started(&self) -> bool {
        self.giver.read(
            self.giver.giver(),
            dreggnet_quest::giver::GRANTED_SLOT as usize,
        ) == dreggnet_quest::giver::EMBER_QUEST_VALUE
    }

    /// Whether the quest has been turned in.
    pub fn is_turned_in(&self) -> bool {
        self.turned_in
    }

    /// Earn real Ember faction standing (committed pledge + trial turns) so the START can open.
    pub fn earn_standing(&self) {
        self.giver.earn_standing();
    }

    /// Attempt to START the Descent-quest — the faction-gated cross-cell grant. Fails closed for
    /// a player with no Ember standing; commits once [`earn_standing`](Self::earn_standing) has
    /// put real rep on the ledger.
    pub fn start(&self) -> Result<(), String> {
        self.giver.grant_honest().map(|_| ())
    }

    /// Turn the Descent-quest in on a [`Completion`]. Fails closed unless the quest is STARTED,
    /// the completion is bound to the posted day's universe, and the shared no-cheat gate
    /// re-executes it to the win. Returns the verified turns-to-win. Idempotent-refusing: a
    /// second turn-in is refused.
    pub fn turn_in(
        &mut self,
        universe: &Universe,
        completion: &Completion,
    ) -> Result<usize, String> {
        if !self.is_started() {
            return Err("the Descent-quest has not been started (faction gate)".to_string());
        }
        if self.turned_in {
            return Err("the Descent-quest has already been turned in".to_string());
        }
        if universe.id() != self.universe_id {
            return Err("the universe is not the day this quest was posted against".to_string());
        }
        if completion.universe != self.universe_id {
            return Err("the completion is not bound to this quest's day".to_string());
        }
        let turns = verify_completion(universe, completion)
            .map_err(|e| format!("the turned-in completion failed the no-cheat gate: {e:?}"))?;
        self.turned_in = true;
        Ok(turns)
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// The reusable top-level loop: Adventure -> AdventureReport.
// ─────────────────────────────────────────────────────────────────────────────

/// An error in one phase of the driven adventure, carrying the phase and the layer's own reason.
#[derive(Clone, Debug)]
pub struct AdventureError {
    /// Which phase of the loop failed (a stable label a UI can key on).
    pub phase: &'static str,
    /// The underlying layer's own reason.
    pub reason: String,
}

impl std::fmt::Display for AdventureError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "adventure phase `{}`: {}", self.phase, self.reason)
    }
}

impl std::error::Error for AdventureError {}

impl AdventureError {
    fn at(phase: &'static str, reason: impl Into<String>) -> Self {
        AdventureError {
            phase,
            reason: reason.into(),
        }
    }
}

/// A structured record of one played adventure — the object a consumer (a web front, a CLI,
/// another crate) renders. Every field is a fact the real layers committed to during
/// [`Adventure::play`]; nothing here is a claim the loop did not drive.
#[derive(Clone, Debug)]
pub struct AdventureReport {
    /// The canonical player name that threaded the whole loop.
    pub hero: String,
    /// The seated party roles the run mustered.
    pub party_seats: usize,
    /// The party's committed loot split (per seat), a standing ledger fact.
    pub loot_split: Vec<u64>,
    /// The equipped gear ability fired cross-cell (armed BECAUSE the gear is owned + equipped).
    pub gear_aid_fired: bool,
    /// The companion's level at the run, and the buff value it aided the run with.
    pub companion_level: u64,
    pub companion_buff: u64,
    /// The Descent-quest's faction-gated START opened (only on earned rep).
    pub quest_started: bool,
    /// The run reached the hoard (the win) without perishing the character.
    pub run_won: bool,
    /// The XP the persistent hardcore character earned on the run.
    pub xp: u64,
    /// The day's universe id — the object-identity anchor the whole after-run spine shares.
    pub universe_id: [u8; 32],
    /// The ONE run's verified turns-to-win — agreed by cheevo, guild, and quest turn-in.
    pub turns_to_win: usize,
    /// The verified run earned the depth cheevo (soulbound, re-verifiable).
    pub cheevo_earned: bool,
    /// The guild's aggregate after summing exactly this one verified clear.
    pub guild_clears: usize,
    pub guild_turns: usize,
    /// The Descent-quest turned in on the SAME verified completion.
    pub quest_turned_in: bool,
    /// The crafted relic's content-addressed note id (loot -> craft -> trade, the SAME note).
    pub relic_id: [u8; 32],
    /// The relic's provenance-lineage length after the trade (mint -> escrow -> buyer == 3).
    pub relic_lineage_len: usize,
    /// The player the relic was traded to.
    pub relic_buyer: String,
    /// The verified win placed top-N and earned the season hall-of-fame champion cheevo.
    pub season_champion: bool,
}

impl AdventureReport {
    /// A compact human-readable rendering of the played loop — the lines a text UI (a CLI, a log,
    /// a web front's fallback view) prints. Present tense, what-happened, no boast.
    pub fn summary_lines(&self) -> Vec<String> {
        vec![
            format!(
                "{} mustered a party of {} and split the loot {:?}.",
                self.hero, self.party_seats, self.loot_split
            ),
            format!(
                "Loadout: gear ability {} cross-cell; a level-{} companion aided the run for {}.",
                if self.gear_aid_fired {
                    "fired"
                } else {
                    "did not fire"
                },
                self.companion_level,
                self.companion_buff
            ),
            format!(
                "The Descent-quest {}; the run {} for {} XP in {} verified turns.",
                if self.quest_started {
                    "started (faction rep earned)"
                } else {
                    "stayed locked"
                },
                if self.run_won { "was won" } else { "was lost" },
                self.xp,
                self.turns_to_win
            ),
            format!(
                "One completion: cheevo {}, guild {} clear(s)/{} turns, quest turn-in {}.",
                if self.cheevo_earned {
                    "earned"
                } else {
                    "missed"
                },
                self.guild_clears,
                self.guild_turns,
                if self.quest_turned_in {
                    "accepted"
                } else {
                    "refused"
                }
            ),
            format!(
                "The loot forged a relic and traded to {} (lineage length {}).",
                self.relic_buyer, self.relic_lineage_len
            ),
            format!(
                "Season: {}.",
                if self.season_champion {
                    "hall-of-fame champion"
                } else {
                    "did not place"
                }
            ),
        ]
    }
}

/// **The reusable flagship loop.** Construct with [`Adventure::daily`] (today's Descent for a
/// player) and drive with [`Adventure::play`] — it plays the whole honest loop through the real
/// layers and returns an [`AdventureReport`]. This is the entry a front-end mounts: no test
/// harness, no `expect`, one call.
pub struct Adventure {
    hero: PlayerIdentity,
    seed: CommittedSeed,
}

impl Adventure {
    /// Today's Descent for `hero` — the fixed committed day-seed, the real hardcore offering.
    pub fn daily(hero: PlayerIdentity) -> Self {
        Adventure {
            hero,
            seed: today_seed(),
        }
    }

    /// The Descent for `hero` on an explicit committed day-seed (a chosen day / a test fixture).
    pub fn on_seed(hero: PlayerIdentity, seed: CommittedSeed) -> Self {
        Adventure { hero, seed }
    }

    /// The player threading the loop.
    pub fn hero(&self) -> &PlayerIdentity {
        &self.hero
    }

    /// Play the whole honest loop end-to-end through the real layers, returning the
    /// [`AdventureReport`]. Each phase is a real committed handoff; a phase failure returns an
    /// [`AdventureError`] naming the phase and the layer's own reason (no LARP, no panic).
    pub fn play(&self) -> Result<AdventureReport, AdventureError> {
        use dregg_season::{CarryForwardPolicy, Season};
        use dreggnet_asset::AssetId;
        use dreggnet_cheevo::{Achievement, CheevoLedger};
        use dreggnet_companion::{CompanionRoost, roll_hatch};
        use dreggnet_craft::{CraftForge, Recipe, roll_craft};
        use dreggnet_gear::{Armory, Loadout, Rarity as GearRarity, StatBlock};
        use dreggnet_guild::Guild;
        use dreggnet_party::{Party, PartyMove};
        use dreggnet_trade::{LegSpec, TradeSide, TradeWorld};

        /// The Descent-quest's cheevo depth (a winning run presses well past this).
        const DEPTH_CHEEVO_MIN: u64 = 3;
        /// The buff / gear aid require a level-2 companion (a real cross-cell checkpoint).
        const COMPANION_AID_LEVEL: u64 = 2;

        let hero = &self.hero;

        // (1) THE PARTY MUSTERS — four seated roles, each seat capped to its mandate.
        let mut party = Party::muster();
        let party_seats = party.seat_count();
        if !party.act_in_role(0).committed() {
            return Err(AdventureError::at(
                "party",
                "the Tank could not guard the front",
            ));
        }
        if !party.act(1, PartyMove::GuardFront).refused() {
            return Err(AdventureError::at(
                "party",
                "a seat played another seat's role (the mandate cap did not bite)",
            ));
        }
        let split = [40u64, 20, 20, 20];
        if !party.split_loot(&split).committed() {
            return Err(AdventureError::at("party", "the loot split was refused"));
        }

        // (2) THE LOADOUT — equip GEAR (aids the run cross-cell) + bring a level-N COMPANION.
        let mut armory = Armory::new();
        armory.pubkey_of(hero.holder_label());
        let gear = armory.forge(
            hero.holder_label(),
            StatBlock::weapon(GearRarity::Legendary, 12, 0xDE5CE7),
        );
        let mut loadout = Loadout::new(armory, gear, None);
        if loadout.gate.use_ability_honest().is_ok() {
            return Err(AdventureError::at(
                "loadout",
                "the gear aid fired before it was equipped (fail-closed gate did not bite)",
            ));
        }
        loadout
            .equip(hero.holder_label())
            .map_err(|e| AdventureError::at("loadout", format!("the gear did not equip: {e:?}")))?;
        loadout.gate.use_ability_honest().map_err(|e| {
            AdventureError::at("loadout", format!("the equipped gear did not aid: {e:?}"))
        })?;
        let gear_aid_fired = loadout.gate.ability_unlocked();

        let mut roost = CompanionRoost::new();
        roost.pubkey_of(hero.holder_label());
        let comp = roost
            .hatch(
                hero.holder_label(),
                &roll_hatch(&self.seed, "companion:descent-drake", 0),
            )
            .map_err(|e| {
                AdventureError::at("loadout", format!("the companion did not hatch: {e:?}"))
            })?;
        let buff = roost.arm_buff(&comp, COMPANION_AID_LEVEL);
        roost
            .raise_to(&comp, 1)
            .map_err(|e| AdventureError::at("loadout", format!("raise to level 1: {e:?}")))?;
        if roost.attempt_buff(&buff, hero.holder_label(), true).is_ok() {
            return Err(AdventureError::at(
                "loadout",
                "the companion buff fired below the required level (fail-closed gate did not bite)",
            ));
        }
        roost
            .raise_to(&comp, COMPANION_AID_LEVEL)
            .map_err(|e| AdventureError::at("loadout", format!("raise to the aid level: {e:?}")))?;
        roost
            .attempt_buff(&buff, hero.holder_label(), true)
            .map_err(|e| {
                AdventureError::at(
                    "loadout",
                    format!("the level-N companion did not aid: {e:?}"),
                )
            })?;
        let companion_buff = roost.buff_value(&buff);

        // (3+5) THE RUN — the ACTUAL DailyDescentOffering, opened + driven to the win.
        let (offering, mut run) = {
            let offering = descent_offering();
            let mut run = offering
                .open_from_seed(hero.guild_member(), self.seed)
                .map_err(|e| {
                    AdventureError::at("run", format!("the descent did not open: {e:?}"))
                })?;
            drive_descent_to_win(&offering, &mut run)
                .map_err(|reason| AdventureError::at("run", reason))?;
            (offering, run)
        };
        if !run.is_won() || run.is_dead() {
            return Err(AdventureError::at(
                "run",
                "the run did not end in a survived win",
            ));
        }
        let run_won = true;
        let xp = run.character().xp();

        // (4) THE ONE RUN OBJECT — the day's universe + the single completion.
        let (universe, completion) =
            run_object(&offering, &run, hero).map_err(|r| AdventureError::at("run-object", r))?;
        let universe_id: [u8; 32] = *universe.id().as_bytes();

        // (3) THE FACTION- + COMPLETION-GATED QUEST — posted against THIS day; start on rep.
        let mut quest = CompletionGatedQuest::post(&universe);
        if quest.start().is_ok() {
            return Err(AdventureError::at(
                "quest",
                "the faction-locked quest started without earned standing",
            ));
        }
        quest.earn_standing();
        quest
            .start()
            .map_err(|e| AdventureError::at("quest", format!("the started quest refused: {e}")))?;
        let quest_started = quest.is_started();

        // (6) CHEEVO + GUILD + QUEST TURN-IN — all off the SAME &universe + &completion.
        let mut cheevos = CheevoLedger::new();
        let cheevo = cheevos
            .earn(
                &universe,
                &completion,
                Achievement::ReachedDepth {
                    var: "depth".to_string(),
                    min: DEPTH_CHEEVO_MIN,
                },
            )
            .map_err(|e| AdventureError::at("cheevo", format!("the win earned none: {e:?}")))?;
        let mut guild = Guild::form("The Descent Vanguard");
        guild.admit(&hero.guild_member());
        let guild_turns = guild
            .board_mut()
            .record_clear(&hero.guild_member(), &universe, &completion)
            .map_err(|e| AdventureError::at("guild", format!("the clear did not sum: {e:?}")))?;
        let quest_turns = quest
            .turn_in(&universe, &completion)
            .map_err(|e| AdventureError::at("quest", format!("the turn-in refused: {e}")))?;
        if cheevo.turns != guild_turns || quest_turns != guild_turns {
            return Err(AdventureError::at(
                "handoff",
                "cheevo / guild / quest disagreed on the one run's turns",
            ));
        }
        // The cheevo independently re-verifies over the SAME run (soulbound honesty).
        cheevos
            .reverify_run(&cheevo, &universe, &completion)
            .map_err(|e| {
                AdventureError::at("cheevo", format!("the cheevo did not re-verify: {e:?}"))
            })?;

        // (7) THE LOOT -> CRAFT -> TRADE — the SAME note-cell to a buyer.
        const BUYER: &str = "Corvane";
        let mut forge = CraftForge::new();
        let recipe = Recipe::new("forge:descent-relic", 2);
        let m1 = forge.mint_material(hero.holder_label(), &loot_seed(&run, 1));
        let m2 = forge.mint_material(hero.holder_label(), &loot_seed(&run, 2));
        let draw = roll_craft(
            &CommittedSeed::from_bytes(run.final_commitment()),
            &recipe,
            &[m1, m2],
        );
        let relic: AssetId = forge
            .craft(hero.holder_label(), &draw, &recipe)
            .map_err(|e| AdventureError::at("craft", format!("the loot did not forge: {e:?}")))?
            .asset_id;
        let mut market = TradeWorld::with_assets(forge.into_assets());
        market.fund_dregg(BUYER, 100);
        let mut trade = market.open_trade(
            hero.holder_label(),
            LegSpec::Asset(relic),
            BUYER,
            LegSpec::Dregg(50),
        );
        market.deposit(&mut trade, TradeSide::A).map_err(|e| {
            AdventureError::at("trade", format!("the seller deposit failed: {e:?}"))
        })?;
        market
            .deposit(&mut trade, TradeSide::B)
            .map_err(|e| AdventureError::at("trade", format!("the buyer deposit failed: {e:?}")))?;
        market
            .settle(&mut trade)
            .map_err(|e| AdventureError::at("trade", format!("the swap did not settle: {e:?}")))?;
        let prov = market.verify_provenance(relic);
        if !prov.verified {
            return Err(AdventureError::at(
                "trade",
                "the traded relic's lineage did not re-verify",
            ));
        }
        let relic_id: [u8; 32] = relic.0;

        // (8) THE SEASON CHAMPION — the verified win enters the season board + earns the hall.
        let mut season = Season::genesis(
            1,
            dregg_epoch::local_manifest(),
            "the-descent:s1",
            1000,
            CarryForwardPolicy::hall_of_fame(3).with_prestige(),
        );
        season.board.publish(
            run.day()
                .universe(hero.name())
                .map_err(|e| AdventureError::at("season", format!("day universe: {e:?}")))?,
        );
        season
            .board
            .submit(
                offering
                    .completion(&run, hero.name(), hero.name())
                    .map_err(|e| AdventureError::at("season", format!("completion: {e:?}")))?,
            )
            .map_err(|e| {
                AdventureError::at("season", format!("the win did not enter the board: {e:?}"))
            })?;
        cheevos
            .earn_champion(&season, hero.name(), 3)
            .map_err(|e| {
                AdventureError::at("season", format!("the champion cheevo was refused: {e:?}"))
            })?;

        Ok(AdventureReport {
            hero: hero.name().to_string(),
            party_seats,
            loot_split: split.to_vec(),
            gear_aid_fired,
            companion_level: COMPANION_AID_LEVEL,
            companion_buff,
            quest_started,
            run_won,
            xp,
            universe_id,
            turns_to_win: guild_turns,
            cheevo_earned: true,
            guild_clears: guild.stats().verified_clears,
            guild_turns,
            quest_turned_in: quest.is_turned_in(),
            relic_id,
            relic_lineage_len: prov.length,
            relic_buyer: BUYER.to_string(),
            season_champion: true,
        })
    }
}

#[cfg(test)]
mod adventure {
    //! THE DESCENT, integrated — now driven through the REUSABLE public API and its building
    //! blocks. [`the_public_adventure_api_plays_the_whole_loop`] plays the whole loop through
    //! [`Adventure::play`] (the entry a front-end mounts); the remaining tests drive the
    //! individual seams and their non-vacuous refusal legs on the same public surface.
    use super::*;

    use dregg_season::{CarryForwardPolicy, Season};
    use dreggnet_asset::AssetId;
    use dreggnet_cheevo::{Achievement, CheevoError, CheevoLedger};
    use dreggnet_companion::{CompanionRoost, roll_hatch};
    use dreggnet_craft::{CraftForge, Recipe, roll_craft};
    use dreggnet_gear::{Armory, Loadout, Rarity as GearRarity, StatBlock};
    use dreggnet_guild::Guild;
    use dreggnet_party::{Party, PartyMove};
    use dreggnet_quest::giver::{EMBER_QUEST_VALUE, FactionGatedGiverWorld, GRANTED_SLOT};
    use dreggnet_trade::{LegSpec, TradeSide, TradeWorld};
    use dungeon_on_dregg::loot::{LootVault, reverify_drop, roll_drop};
    use ugc_dregg::{Completion, Universe, verify_completion};

    const HERO: &str = "Vael";
    const BUYER: &str = "Corvane";
    const DEPTH_CHEEVO_MIN: u64 = 3;
    const COMPANION_AID_LEVEL: u64 = 2;

    fn hero() -> PlayerIdentity {
        PlayerIdentity::new(HERO)
    }

    /// Test wrapper: the reusable [`play_a_winning_descent`] with the loud `expect` a test wants.
    fn won_descent(
        who: &PlayerIdentity,
    ) -> (DailyDescentOffering<InMemoryCharacterStore>, DailyRun) {
        play_a_winning_descent(who).expect("the descent is driven to a survived win")
    }

    fn one_run_object(
        offering: &DailyDescentOffering<InMemoryCharacterStore>,
        run: &DailyRun,
        who: &PlayerIdentity,
    ) -> (Universe, Completion) {
        run_object(offering, run, who).expect("the ONE run object builds + re-verifies")
    }

    // ── THE PUBLIC API — the whole loop, one call ───────────────────────────────────────

    /// THE REUSABLE ENTRY: [`Adventure::play`] drives the whole honest loop through the real
    /// layers and returns a coherent [`AdventureReport`] — the surface a front-end mounts. Every
    /// reported fact is one the layers committed to; the report's object-identity spine holds.
    #[test]
    fn the_public_adventure_api_plays_the_whole_loop() {
        let report = Adventure::daily(hero())
            .play()
            .expect("the flagship adventure plays end-to-end through the public API");

        assert_eq!(report.hero, HERO);
        assert_eq!(report.party_seats, 4);
        assert_eq!(report.loot_split, vec![40, 20, 20, 20]);
        assert!(report.gear_aid_fired, "the equipped gear aided the run");
        assert_eq!(report.companion_level, COMPANION_AID_LEVEL);
        assert_eq!(report.companion_buff, COMPANION_AID_LEVEL);
        assert!(report.quest_started, "the faction-gated quest opened");
        assert!(report.run_won, "the run was won");
        assert!(report.xp > 0, "the run earned the character real XP");
        assert!(report.turns_to_win > 0);
        assert!(report.cheevo_earned);
        assert_eq!(report.guild_clears, 1, "exactly the one clear entered");
        assert_eq!(report.guild_turns, report.turns_to_win);
        assert!(report.quest_turned_in, "the quest turned in on the win");
        assert_eq!(report.relic_lineage_len, 3, "mint -> escrow -> buyer");
        assert_eq!(report.relic_buyer, BUYER);
        assert!(report.season_champion, "the win placed in the hall-of-fame");

        // The renderable summary a UI prints has one line per phase.
        assert_eq!(report.summary_lines().len(), 6);
    }

    /// The API is a real driver, not a constant: replaying the SAME day is deterministic (the
    /// same universe id), while opening a DIFFERENT committed day is a DIFFERENT run object (a
    /// different universe id). Opening (not a full win) suffices to witness the seed is load-bearing.
    #[test]
    fn the_seed_is_load_bearing_and_the_day_is_deterministic() {
        // Determinism: two plays of today's Descent are the SAME run object.
        let a = Adventure::daily(hero())
            .play()
            .expect("today's Descent plays");
        let b = Adventure::daily(hero())
            .play()
            .expect("today's Descent replays");
        assert_eq!(
            a.universe_id, b.universe_id,
            "the same day is one run object"
        );

        // The seed is load-bearing: a different committed day opens a different universe.
        let offering = descent_offering();
        let today = offering
            .open_from_seed(hero().guild_member(), today_seed())
            .expect("today opens");
        let other = descent_offering()
            .open_from_seed(hero().guild_member(), CommittedSeed::from_bytes([0x5A; 32]))
            .expect("another day opens");
        let today_u = today.day().universe(HERO).expect("today publishes").id();
        let other_u = other.day().universe(HERO).expect("other publishes").id();
        assert_ne!(
            today_u, other_u,
            "a different committed day is a different run object"
        );
    }

    // ── THE DEDICATED COMPLETION-GATED QUEST GIVER (non-vacuous) ─────────────────────────

    /// THE COMPLETION-GATED GIVER: the Descent-quest's START is faction-gated (refused with no
    /// rep, opens once earned) and its TURN-IN gates directly on the run's [`Completion`] — a
    /// not-yet-started quest refuses, a forged run refuses, a wrong-day completion refuses, and
    /// the honest completion turns in exactly once.
    #[test]
    fn the_completion_gated_quest_starts_on_rep_and_turns_in_on_the_run() {
        let hero = hero();
        let (offering, run) = won_descent(&hero);
        let (universe, completion) = one_run_object(&offering, &run, &hero);

        let mut quest = CompletionGatedQuest::post(&universe);

        // START is faction-gated: refused before rep is earned.
        assert!(!quest.is_started());
        assert!(
            quest.start().is_err(),
            "a no-rep player cannot start the Descent-quest"
        );
        // TURN-IN of the honest completion is refused while unstarted (the START gate one up).
        assert!(
            quest.turn_in(&universe, &completion).is_err(),
            "the quest cannot be turned in before it is started"
        );

        // Earn rep -> the SAME start opens.
        quest.earn_standing();
        quest.start().expect("earning rep opens the Descent-quest");
        assert!(quest.is_started());

        // A FORGED run is refused at the turn-in gate (the no-cheat re-execution fails).
        let mut forged = completion.clone();
        forged.play.steps[0].choice_index = GATE_PRESS;
        assert!(
            quest.turn_in(&universe, &forged).is_err(),
            "a forged completion cannot turn the quest in"
        );
        assert!(
            !quest.is_turned_in(),
            "anti-ghost: the quest is not turned in"
        );

        // A WRONG-UNIVERSE turn-in is refused by the object-identity pin: a different author's
        // universe (same day, different name -> different id) does not match the posted quest.
        let other_hero = PlayerIdentity::new("Nyx");
        let (other_off, other_run) =
            play_a_winning_descent(&other_hero).expect("a second player's run plays");
        let (other_universe, _oc) = one_run_object(&other_off, &other_run, &other_hero);
        assert_ne!(
            other_universe.id(),
            universe.id(),
            "a different author is a different id"
        );
        assert!(
            quest.turn_in(&other_universe, &completion).is_err(),
            "a completion presented against the wrong universe is refused"
        );

        // The HONEST completion turns in — exactly once.
        let turns = quest
            .turn_in(&universe, &completion)
            .expect("the honest run turns the Descent-quest in");
        assert!(turns > 0);
        assert!(quest.is_turned_in());
        assert!(
            quest.turn_in(&universe, &completion).is_err(),
            "the quest cannot be turned in twice"
        );
    }

    // ── BEFORE: the faction-gated quest START, on the raw giver (non-vacuous) ────────────

    /// THE FACTION GATE directly on [`FactionGatedGiverWorld`]: a no-rep player is REFUSED the
    /// grant (the faction rep cell's cross-cell gate fails closed); earning real standing opens
    /// the SAME start.
    #[test]
    fn a_faction_locked_player_cannot_start_the_descent_then_can_once_rep_is_earned() {
        let giver = FactionGatedGiverWorld::deploy();
        let refused = giver.grant_honest();
        assert!(
            refused.is_err(),
            "a no-rep grant is refused, got {refused:?}"
        );
        assert_eq!(
            giver.read(giver.giver(), GRANTED_SLOT as usize),
            0,
            "anti-ghost: the quest was not started"
        );
        giver.earn_standing();
        giver
            .grant_honest()
            .expect("earning faction rep opens the Descent-quest start");
        assert_eq!(
            giver.read(giver.giver(), GRANTED_SLOT as usize),
            EMBER_QUEST_VALUE,
            "the Descent-quest is now started"
        );
    }

    // ── THE RUN: the loadout aids it cross-cell (non-vacuous, both legs) ─────────────────

    /// THE EQUIPPED GEAR AIDS THE RUN, cross-cell: refused before the equip, commits after.
    #[test]
    fn the_equipped_gear_ability_aids_the_run_cross_cell() {
        let hero = hero();
        let mut armory = Armory::new();
        armory.pubkey_of(hero.holder_label());
        let gear = armory.forge(
            hero.holder_label(),
            StatBlock::weapon(GearRarity::Legendary, 12, 0xDE5CE7),
        );
        let mut loadout = Loadout::new(armory, gear, None);
        let unarmed = loadout.gate.use_ability_honest();
        assert!(
            unarmed.is_err(),
            "the aid refuses before equip, got {unarmed:?}"
        );
        assert!(
            !loadout.gate.ability_unlocked(),
            "anti-ghost: the aid never fired"
        );
        loadout
            .equip(hero.holder_label())
            .expect("the one identity owns + equips the run gear");
        loadout
            .gate
            .use_ability_honest()
            .expect("the equipped gear aids the run cross-cell");
        assert!(loadout.gate.ability_unlocked());
    }

    /// THE LEVEL-N COMPANION BUFF AIDS THE RUN, cross-cell: refused below level, commits at level.
    #[test]
    fn a_level_n_companion_buff_aids_the_run_cross_cell() {
        let hero = hero();
        let mut roost = CompanionRoost::new();
        roost.pubkey_of(hero.holder_label());
        let draw = roll_hatch(&today_seed(), "companion:descent-drake", 0);
        let comp = roost
            .hatch(hero.holder_label(), &draw)
            .expect("the companion hatches from the run's seed");
        let gate = roost.arm_buff(&comp, COMPANION_AID_LEVEL);
        roost.raise_to(&comp, 1).expect("raise to level 1");
        let below = roost.attempt_buff(&gate, hero.holder_label(), true);
        assert!(
            below.is_err(),
            "the buff refuses below level, got {below:?}"
        );
        assert_eq!(
            roost.buff_value(&gate),
            0,
            "anti-ghost: the buff did not apply"
        );
        roost
            .raise_to(&comp, COMPANION_AID_LEVEL)
            .expect("raise to the required level");
        roost
            .attempt_buff(&gate, hero.holder_label(), true)
            .expect("the level-2 companion aids the run cross-cell");
        assert_eq!(roost.buff_value(&gate), COMPANION_AID_LEVEL);
    }

    // ── THE RUN's loot as owned assets ──────────────────────────────────────────────────

    /// THE RUN'S LOOT DROPS AS OWNED ASSETS: a real fair draw mints an owned note; a forged drop
    /// mints nothing.
    #[test]
    fn the_runs_loot_drops_as_owned_assets() {
        let hero = hero();
        let (_offering, run) = won_descent(&hero);
        let mut vault = LootVault::new();
        let owner_pk = vault.pubkey_of(hero.holder_label());
        let drop = roll_drop(&run.day().seed, "boss:the-warden", 0);
        reverify_drop(&drop).expect("the run's drop is a real fair draw");
        let item = vault
            .claim(hero.holder_label(), &drop)
            .expect("the run's loot drops as an owned asset");
        assert_eq!(
            vault.owner_of(item.asset_id),
            Some(owner_pk),
            "the player owns the loot"
        );
        assert!(
            vault.verify_asset_provenance(item.asset_id).verified,
            "the looted asset's provenance re-verifies"
        );
        let mut forged = drop.clone();
        forged.roll = if forged.roll == 99 { 98 } else { 99 };
        let refused = vault.claim(hero.holder_label(), &forged);
        assert!(
            refused.is_err(),
            "a forged loot claim mints nothing, got {refused:?}"
        );
    }

    // ── AFTER: the ONE Completion -> cheevo + guild + quest (object-identical) ───────────

    /// HANDOFF — the SAME `Completion` earns a CHEEVO, sums into the GUILD, and turns in the
    /// dedicated Completion-gated QUEST. One `&universe` + one `&completion` into all three.
    #[test]
    fn the_one_completion_earns_a_cheevo_sums_the_guild_and_turns_in_the_quest() {
        let hero = hero();
        let (offering, run) = won_descent(&hero);
        let (universe, completion) = one_run_object(&offering, &run, &hero);

        let mut cheevos = CheevoLedger::new();
        let cheevo = cheevos
            .earn(
                &universe,
                &completion,
                Achievement::ReachedDepth {
                    var: "depth".to_string(),
                    min: DEPTH_CHEEVO_MIN,
                },
            )
            .expect("the verified descent earns the depth cheevo");

        let mut guild = Guild::form("The Descent Vanguard");
        let hero_id = hero.guild_member();
        guild.admit(&hero_id);
        let guild_turns = guild
            .board_mut()
            .record_clear(&hero_id, &universe, &completion)
            .expect("the guild sums the same verified clear");

        // The dedicated Completion-gated giver turns in on the SAME object.
        let mut quest = CompletionGatedQuest::post(&universe);
        quest.earn_standing();
        quest.start().expect("the quest starts on earned rep");
        let quest_turns = quest
            .turn_in(&universe, &completion)
            .expect("the Descent-quest turns in on the verified win");

        assert_eq!(cheevo.turns, guild_turns, "cheevo + guild agree on the run");
        assert_eq!(quest_turns, guild_turns, "the quest turn-in agrees");
        assert_eq!(
            cheevo.universe,
            universe.id(),
            "the cheevo anchors THIS day"
        );
        assert_eq!(guild.stats().verified_clears, 1, "exactly one clear");
        assert_eq!(guild.stats().total_turns, guild_turns);
    }

    /// THE REFUSAL LEGS (non-vacuous): a FORGED run earns NO cheevo and sums into NO guild; a
    /// NON-MEMBER cannot inflate the guild; a verified run that MISSES the predicate earns none.
    #[test]
    fn a_forged_run_earns_no_cheevo_and_sums_into_no_guild() {
        let hero = hero();
        let (offering, run) = won_descent(&hero);
        let (universe, honest) = one_run_object(&offering, &run, &hero);

        let mut forged = honest.clone();
        forged.play.steps[0].choice_index = GATE_PRESS;

        let mut cheevos = CheevoLedger::new();
        let earned = cheevos.earn(
            &universe,
            &forged,
            Achievement::ReachedDepth {
                var: "depth".to_string(),
                min: DEPTH_CHEEVO_MIN,
            },
        );
        assert!(
            matches!(earned, Err(CheevoError::RunRejected(_))),
            "a forged descent earns no cheevo, got {earned:?}"
        );

        let mut guild = Guild::form("The Descent Vanguard");
        let hero_id = hero.guild_member();
        guild.admit(&hero_id);
        let summed = guild.board_mut().record_clear(&hero_id, &universe, &forged);
        assert!(
            summed.is_err(),
            "a forged clear cannot inflate the guild, got {summed:?}"
        );
        assert_eq!(
            guild.stats().verified_clears,
            0,
            "anti-ghost: nothing counted"
        );

        let stranger = DreggIdentity("Nyx-the-unenrolled".to_string());
        let refused = guild
            .board_mut()
            .record_clear(&stranger, &universe, &honest);
        assert!(
            refused.is_err(),
            "a non-member cannot inflate the guild, got {refused:?}"
        );

        let unreachable = cheevos.earn(
            &universe,
            &honest,
            Achievement::ReachedDepth {
                var: "depth".to_string(),
                min: 999,
            },
        );
        assert!(
            matches!(unreachable, Err(CheevoError::PredicateNotMet(_))),
            "the run does not reach depth 999, so it earns nothing, got {unreachable:?}"
        );
    }

    // ── AFTER: the looted note crafts + trades as the SAME note-cell ─────────────────────

    /// THE LOOTED NOTE CRAFTS + TRADES AS THE SAME ASSET, in ONE ledger; a non-owner cannot
    /// offer it.
    #[test]
    fn the_looted_note_crafts_and_trades_as_the_same_asset() {
        let hero = hero();
        let (_offering, run) = won_descent(&hero);

        let mut forge = CraftForge::new();
        let recipe = Recipe::new("forge:descent-relic", 2);
        let m1 = forge.mint_material(hero.holder_label(), &loot_seed(&run, 1));
        let m2 = forge.mint_material(hero.holder_label(), &loot_seed(&run, 2));
        let beacon = CommittedSeed::from_bytes(run.final_commitment());
        let draw = roll_craft(&beacon, &recipe, &[m1, m2]);
        let output = forge
            .craft(hero.holder_label(), &draw, &recipe)
            .expect("the run's loot forges into the relic");
        let relic: AssetId = output.asset_id;
        assert!(
            forge.is_destroyed(m1) && forge.is_destroyed(m2),
            "the material drops were spent on-chain (the sink)"
        );

        let mut market = TradeWorld::with_assets(forge.into_assets());
        assert_eq!(
            market.lineage_len(relic),
            1,
            "the traded note IS the craft's origin mint"
        );
        assert_eq!(
            market.current_owner(relic),
            Some(market.pubkey_of(hero.holder_label())),
            "the crafted note is the trade world's own live note (no re-mint)"
        );

        market.fund_dregg(BUYER, 100);
        let mut trade = market.open_trade(
            hero.holder_label(),
            LegSpec::Asset(relic),
            BUYER,
            LegSpec::Dregg(50),
        );
        market
            .deposit(&mut trade, TradeSide::A)
            .expect("the seller deposits the relic");
        market
            .deposit(&mut trade, TradeSide::B)
            .expect("the buyer deposits the value");
        market
            .settle(&mut trade)
            .expect("the swap settles atomically");

        let report = market.verify_provenance(relic);
        assert!(
            report.verified,
            "the traded relic's full lineage re-verifies"
        );
        assert_eq!(report.length, 3, "mint -> escrow -> buyer, not restarted");
        assert_eq!(
            market.current_owner(relic),
            Some(market.pubkey_of(BUYER)),
            "the buyer now owns the identical NOTE the run's loot forged"
        );

        let mut mallory =
            market.open_trade("Mallory", LegSpec::Asset(relic), BUYER, LegSpec::Dregg(1));
        let stolen = market.deposit(&mut mallory, TradeSide::A);
        assert!(
            stolen.is_err(),
            "a non-owner cannot deposit the relic, got {stolen:?}"
        );
    }

    // ── AFTER: a season champion -> the hall-of-fame cheevo ──────────────────────────────

    /// A SEASON CHAMPION -> the dregg-season HALL-OF-FAME; a non-placing player earns nothing.
    #[test]
    fn a_season_champion_earns_the_hall_of_fame_cheevo() {
        let hero = hero();
        let (offering, run) = won_descent(&hero);
        let (_universe, completion) = one_run_object(&offering, &run, &hero);

        let mut season = Season::genesis(
            1,
            dregg_epoch::local_manifest(),
            "the-descent:s1",
            1000,
            CarryForwardPolicy::hall_of_fame(3).with_prestige(),
        );
        let season_universe = run
            .day()
            .universe(hero.name())
            .expect("the day publishes as a universe");
        season.board.publish(season_universe);
        season
            .board
            .submit(completion)
            .expect("the verified win enters the season board");

        let champions = season.champions(3);
        assert!(
            !champions.is_empty(),
            "the verified win placed on the board"
        );
        assert_eq!(champions[0].player, hero.name(), "the hero is the champion");

        let mut cheevos = CheevoLedger::new();
        cheevos
            .earn_champion(&season, hero.name(), 3)
            .expect("the season champion earns the hall-of-fame cheevo");
        let not_champ = cheevos.earn_champion(&season, "Nobody", 3);
        assert!(
            not_champ.is_err(),
            "a non-placing player earns no champion cheevo"
        );
    }

    // ── ONE identity across the crates ──────────────────────────────────────────────────

    /// ONE IDENTITY is the party seat, the gear owner, the companion owner, AND the guild member
    /// — a single [`PlayerIdentity`] (now native to this crate, folded from saga) derives every
    /// representation the loop keys on.
    #[test]
    fn the_one_identity_is_seat_gear_companion_and_guild() {
        let party = Party::muster();
        let hero = PlayerIdentity::new(party.seat(0).name());

        assert_eq!(
            hero.seat_pk(),
            party.seat(0).electorate_seat().pk,
            "the one identity's custody key IS the party seat's ballot identity"
        );

        let mut armory = Armory::new();
        let hero_pk = armory.pubkey_of(hero.holder_label());
        let gear = armory.forge(
            hero.holder_label(),
            StatBlock::weapon(GearRarity::Rare, 8, 0xA1),
        );
        assert_eq!(
            armory.current_owner(&gear),
            Some(hero_pk),
            "the one identity owns its gear"
        );

        let mut roost = CompanionRoost::new();
        let comp = roost
            .hatch(
                hero.holder_label(),
                &roll_hatch(&today_seed(), "companion:fox", 0),
            )
            .expect("the companion hatches");
        assert_eq!(
            roost.owner_of(comp.asset_id),
            Some(hero_pk),
            "the one identity owns its companion (same holder key as its gear)"
        );

        let (offering, run) = won_descent(&hero);
        let (universe, completion) = one_run_object(&offering, &run, &hero);
        let mut guild = Guild::form("The Descent Vanguard");
        guild.admit(&hero.guild_member());
        let turns = guild
            .board_mut()
            .record_clear(&hero.guild_member(), &universe, &completion)
            .expect("the one identity's clear is counted");
        assert!(turns > 0);

        assert_eq!(hero.name(), hero.holder_label());
        assert_eq!(hero.guild_member().as_str(), hero.name());
    }

    // ── THE FULL LOOP through the API + the object-identity spine ────────────────────────

    /// THE FULL INTEGRATED DESCENT LOOP through the public API, with the object-identity spine
    /// asserted directly on the run object the report is built from: one player, one run object,
    /// one item note, cheevo == guild == quest turns, the relic to the buyer, the champion cheevo.
    #[test]
    fn the_full_integrated_descent_loop_runs_end_to_end() {
        let hero = hero();

        // The public API plays the whole loop (party -> loadout -> gated quest -> run ->
        // one Completion -> cheevo + guild + quest -> loot craft + trade -> season champion).
        let report = Adventure::daily(hero.clone())
            .play()
            .expect("the full integrated Descent loop plays through the public API");

        // The object-identity spine, asserted directly: replay the ONE run object and confirm the
        // three after-run consumers agree on it, matching the report the API produced.
        let (offering, run) = won_descent(&hero);
        let (universe, completion) = one_run_object(&offering, &run, &hero);
        assert_eq!(
            universe.id().as_bytes(),
            &report.universe_id,
            "the report is THIS day's run object"
        );

        let cheevo_turns = {
            let mut cheevos = CheevoLedger::new();
            cheevos
                .earn(
                    &universe,
                    &completion,
                    Achievement::ReachedDepth {
                        var: "depth".to_string(),
                        min: DEPTH_CHEEVO_MIN,
                    },
                )
                .expect("the win earns the depth cheevo")
                .turns
        };
        let guild_turns = {
            let mut guild = Guild::form("The Descent Vanguard");
            guild.admit(&hero.guild_member());
            guild
                .board_mut()
                .record_clear(&hero.guild_member(), &universe, &completion)
                .expect("the guild sums the same clear")
        };
        let quest_turns =
            verify_completion(&universe, &completion).expect("the completion re-verifies");
        assert_eq!(
            cheevo_turns, guild_turns,
            "cheevo + guild agree on the one run"
        );
        assert_eq!(quest_turns, guild_turns, "the quest turn-in agrees");
        assert_eq!(
            report.turns_to_win, guild_turns,
            "the report carried the one run's turns"
        );

        // The end state the report claims is coherent.
        assert!(report.gear_aid_fired && report.companion_buff == COMPANION_AID_LEVEL);
        assert_eq!(report.guild_clears, 1);
        assert!(report.quest_turned_in && report.cheevo_earned && report.season_champion);
        assert_eq!(report.relic_lineage_len, 3);
        assert_eq!(report.loot_split[0], 40);
    }
}
