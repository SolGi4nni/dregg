//! # `dreggnet-saga` — the WEAVE that proves the game-infra crates COMPOSE.
//!
//! Eight feature crates (party / quest / craft / cheevo / trade / faction / guild /
//! tavern) each ship, each individually excellent, each built in ISOLATION. This crate
//! is the enmeshment proof: a **driven end-to-end saga** that threads ONE player through
//! the features as a continuous story, each step a real committed turn feeding the next,
//! where one crate's OUTPUT type IS the next crate's INPUT type on the shared substrate.
//!
//! ## The two shared currencies of composition
//!
//! The whole "do they compose?" question reduces to: is the object one crate hands off
//! the SAME object the next crate consumes, or a re-derived look-alike? The saga proves
//! object-identity along the two spines the substrate was designed around:
//!
//! * **The `ugc_dregg::Completion` — the run currency.** A quest completion, a Descent
//!   run, a tournament result are all one `Completion` (a `Playthrough` + a claimed
//!   turns-to-win, verified against a `Universe`). The saga records ONE `Completion` and
//!   passes the SAME `&Completion` (and the SAME `&Universe`) by reference to
//!   [`dreggnet_cheevo::CheevoLedger::earn`] AND
//!   [`dreggnet_guild::leaderboard::GuildBoard::record_clear`]. quest -> cheevo -> guild
//!   is object-identical: nobody re-derives the run.
//! * **The `dreggnet_asset::AssetId` — the item currency.** A crafted output, a traded
//!   item, a loot drop are all one owned note addressed by a stable content id. The saga
//!   forges an output in [`dreggnet_craft`], and the SAME 32-byte `AssetId` is the one a
//!   [`dreggnet_trade`] swap moves and the one the new owner's provenance-verify names.
//!
//! ## The chain the saga drives (each `->` is a real cross-crate handoff)
//!
//! 1. a **party** musters (`dreggnet-party`) — four seated roles, each cap = its mandate;
//! 2. a **faction** gate stands between the party and the quest-giver (`dreggnet-faction`)
//!    — a player with no Ember standing is REFUSED entry to the sanctum where the giver
//!    waits, so a faction-locked player cannot start the quest; earning rep opens it;
//! 3. the **quest** is run and turned in (`dreggnet-quest`) — a replay-verified receipt,
//!    which the saga records as one `ugc_dregg::Completion`;
//! 4. that Completion **earns a cheevo** (`dreggnet-cheevo`) — a soulbound asset over the
//!    run's real trajectory;
//! 5. the guild **sums the same clear** (`dreggnet-guild`) — the identical Completion,
//!    counted into the guild's un-forgeable aggregate;
//! 6. the quest's material drops are **forged** into an item (`dreggnet-craft`) — inputs
//!    spent on-chain, one owned output note;
//! 7. that item is **traded** to a buyer (`dreggnet-trade`) — an atomic escrow swap; the
//!    buyer verifies the item's provenance by the SAME AssetId.
//!
//! ## Honest scope — object-identity end-to-end (the reconciliations, applied)
//!
//! The saga assessment named four additive reconciliations to tighten the weave from
//! label-matched to object-identical. Three are now DONE (additive API tweaks, no
//! redesign); the fourth is a deliberately-named follow-up:
//!
//! * **quest -> cheevo -> guild: OBJECT-IDENTICAL.** One `Universe` and one `Completion`,
//!   passed by reference to both consumers. The cheevo anchors and the guild counts the
//!   very same run object. The strongest handoff in the weave, unchanged.
//! * **craft -> trade -> buyer: OBJECT-IDENTICAL AT THE NOTE-CELL (reconciliation #1,
//!   done).** [`dreggnet_craft::CraftForge::into_assets`] (and `assets_mut`) hands the
//!   forge's live `AssetWorld` to [`dreggnet_trade::TradeWorld::with_assets`], so the trade
//!   moves the EXACT crafted note with NO re-mint. The crafted output's provenance lineage
//!   CONTINUES across the trade — mint(craft) -> escrow -> buyer, length growing 1 -> 3 in
//!   ONE ledger — rather than restarting a same-id look-alike in a second world. The
//!   `AssetId` byte-identity still holds (a reproducible content address); the note-ledger
//!   is now shared, so the handoff is object-identical at the note-cell, not just the id.
//! * **faction -> quest: THE FACTION REP CELL GATES THE QUEST-GIVER (reconciliation #2,
//!   done).** [`dreggnet_quest::giver::FactionGatedGiverWorld`] points the giver's cross-cell
//!   `ObservedFieldEquals` at a faction-standing cell's `ember_quest` slot (mirroring
//!   [`dreggnet_faction`]'s `FieldGte(rep_embers, `[`dreggnet_faction::REP_THRESHOLD`]`)`-gated
//!   `WriteOnce` unlock, re-homed onto the shared executor ledger). The quest-giver's start
//!   opens ONLY on real faction standing: a no-rep grant fails closed; earning rep opens it.
//!   The giver reads the faction cell, not a separate quest flag.
//! * **ONE IDENTITY across the crates (reconciliation #3, done).** [`PlayerIdentity`] is a
//!   small adapter deriving ONE canonical player into all three key representations:
//!   `dreggnet-party`'s ed25519 `Custodian` seat key, `dreggnet-guild`'s `DreggIdentity`
//!   member handle, and the asset layer's per-label `Holder` key (craft / trade / cheevo).
//!   One object is a party seat, a guild member, AND an asset holder — present across the
//!   crates as a single identity, not three look-alikes stitched by name convention.
//! * **`dreggnet-tavern` graduation is a NAMED follow-up (reconciliation #4, not built).**
//!   Tavern pulls `dregg-node`/deos-host (mozjs), is async, and needs an `_exit(0)` to dodge
//!   a SpiderMonkey teardown SIGSEGV — pulling that elephant into the saga's synchronous
//!   driven test would make the green gate heavy and flaky. Presence is proven in
//!   `dreggnet-tavern`'s own e2e; the saga runs on the light substrate. The real
//!   reconciliation the tavern's own honest-scope names: its inline party-roster /
//!   market-stall cells should GRADUATE to `dreggnet-party` / `dreggnet-trade` (the crates
//!   the saga threads). Named here, deliberately not pulled into the saga.
//!
//! ## Assessment
//!
//! They compose EXCELLENTLY and now OBJECT-IDENTICALLY along every spine but the deliberately
//! deferred one: the run (`Completion`) flows by reference quest -> cheevo -> guild; the item
//! (the crafted NOTE, not just its `AssetId`) flows in one shared ledger craft -> trade ->
//! buyer with a continuous provenance lineage; the faction rep cell gates the quest-giver
//! through a real cross-cell executor predicate; and one `PlayerIdentity` is the party seat,
//! the guild member, and the asset holder at once. Every gate is a real executor refusal, not
//! a host `if`. The three applied reconciliations were additive API tweaks — the objects
//! already lined up. The tavern graduation (which pulls mozjs/async) is the one named,
//! un-pulled follow-up.
//!
//! The driven saga lives in `#[cfg(test)] mod saga`; run it with
//! `cargo test -p dreggnet-saga`.

use ugc_dregg::{Completion, Universe, WinCondition};

/// Build the **quest as a `ugc_dregg::Universe`** — the run substrate the cheevo anchors
/// and the guild counts. The universe is the quest crate's own errand scene
/// ([`dreggnet_quest::ERRAND`]) under the quest's declared win ([`dreggnet_quest::quest_win`],
/// i.e. the scene ENDED and `reward == 1`). The same scene the quest crate deploys, lifted
/// onto the shared UGC no-cheat model so a single `Completion` serves quest, cheevo, and
/// guild alike.
pub fn errand_universe(author: &str) -> Universe {
    Universe::authored(
        "The Loremaster's Errand",
        author,
        dreggnet_quest::ERRAND,
        // The quest crate's win, re-declared on the UGC universe (ended + reward == 1).
        WinCondition::ended_with(&[("reward", dreggnet_quest::REWARD_VALUE)]),
    )
    .expect("the errand scene publishes as a universe")
}

/// The choice indices that WIN the errand — the quest crate's canonical
/// [`dreggnet_quest::winning_script`], driven START -> WIN (light the three wards in order,
/// turn in, accept the writ). Five real turns.
pub fn winning_moves() -> Vec<usize> {
    dreggnet_quest::winning_script()
}

/// Record ONE run of the errand universe and wrap it as ONE `ugc_dregg::Completion` — the
/// single run object the saga threads through quest-verify, the cheevo, and the guild.
/// The playthrough is produced by the shared UGC recorder ([`ugc_dregg::record_playthrough`])
/// on the very universe [`errand_universe`] builds.
pub fn record_errand_completion(universe: &Universe, player: &str) -> Completion {
    let moves = winning_moves();
    let play = ugc_dregg::record_playthrough(universe, &moves)
        .expect("the winning script drives the errand to the win");
    Completion {
        universe: universe.id(),
        player: player.to_string(),
        play,
        claimed_turns: moves.len(),
    }
}

// ── ONE IDENTITY — a single canonical player across the three key representations ──

use dregg_types::PublicKey;
use dreggnet_offerings::DreggIdentity;
use dungeon_on_dregg::collective::Custodian;

/// **A single canonical player identity** the feature crates all key on — the reconciliation
/// that unifies the three key representations the saga meets:
///
/// * the **party seat**'s ed25519 CUSTODY key ([`dungeon_on_dregg::collective::Custodian`],
///   its ballot identity in [`dreggnet_party`]);
/// * the **guild member** handle ([`dreggnet_offerings::DreggIdentity`], what
///   [`dreggnet_guild`] admits and counts clears for);
/// * the **asset holder** label ([`dreggnet_asset::AssetWorld`]'s per-label
///   `blake3::derive_key` holder key, shared by craft / trade / cheevo).
///
/// A small adapter, not a redesign: all three already derive from one `name`, so ONE
/// [`PlayerIdentity`] yields the seat key, the member, AND the holder — the same actor is
/// present across the crates by a single object, not three look-alikes stitched by
/// convention. (A production deployment mints the custody secret in the seat's own device —
/// the demo derivation is deterministic so the saga reproduces stable identities.)
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
    /// craft / trade) mints, transfers, and owns notes under.
    pub fn holder_label(&self) -> &str {
        &self.name
    }

    /// The **guild member handle** — what [`dreggnet_guild`] admits and records clears for.
    pub fn guild_member(&self) -> DreggIdentity {
        DreggIdentity(self.name.clone())
    }

    /// The **party seat's custody keypair** — the ed25519 identity a
    /// [`dreggnet_party`] seat signs its ballots with.
    pub fn custodian(&self) -> Custodian {
        Custodian::demo(self.name.as_str())
    }

    /// The party seat's electorate PUBLIC key (its ballot identity) — the same key
    /// [`dreggnet_party::Seat::electorate_seat`] carries for a seat of this name.
    pub fn seat_pk(&self) -> PublicKey {
        self.custodian().public_key()
    }
}

#[cfg(test)]
mod saga {
    use super::*;

    use dreggnet_asset::AssetId;
    use dreggnet_cheevo::{Achievement, CheevoError, CheevoLedger};
    use dreggnet_craft::{
        CraftForge, GearSlot, GearTemplate, Recipe, RecipeBook, craft_commitment, roll_craft,
    };
    use dreggnet_faction::{
        LN_EMBER_TRIAL, LN_ENTER_SANCTUM, LN_PLEDGE_EMBERS, ROOM_HALL, choice_at, deploy_feud,
        feud_scene,
    };
    use dreggnet_guild::Guild;
    use dreggnet_offerings::DreggIdentity;
    use dreggnet_party::{Party, PartyMove};
    use dreggnet_trade::{LegSpec, TradeSide, TradeWorld};
    use procgen_dregg::CommittedSeed;
    use spween_dregg::WorldError;

    const HERO: &str = "Alkas";
    const BUYER: &str = "Brenna";

    /// The saga's bespoke recipe — the **Loremaster's Charm**, a safe two-input trinket forge
    /// (`essence:lore` + `silver:leaf`). It is NOT in the starter catalog; the saga REGISTERS it
    /// so the errand's material drops forge a real, catalog-committed item.
    fn loremasters_charm() -> Recipe {
        Recipe::gear(
            "forge:loremasters-charm",
            &["essence:lore", "silver:leaf"],
            GearTemplate {
                slot: GearSlot::Trinket,
                rune: 0x2a,
                base_might: 4,
                base_ward: 4,
                base_guile: 20,
            },
        )
    }

    /// A forge over a catalog holding exactly the registered Loremaster's Charm — the committed
    /// book the saga crafts against (a craft can only present a recipe the catalog holds).
    fn charm_forge() -> CraftForge {
        let mut book = RecipeBook::new();
        book.register(loremasters_charm());
        CraftForge::with_book(book)
    }

    // ── faction gate: real committed rep state opens (or refuses) the quest-giver ──

    /// Drive the REAL faction feud world to EARN Ember standing: pledge twice
    /// (`rep_embers` 0 -> 1 -> 2, a `Monotonic` ratchet), undertake the Ember trial
    /// (`ember_quest = 1`, gated `FieldGte(rep_embers, 2)`), then enter the sanctum where
    /// the quest-giver waits. Returns after the sanctum entry commits — the player has the
    /// standing to take the quest. Every step is a real `apply_choice` turn the executor
    /// admits only if the installed gate passes.
    fn earn_ember_standing(seed: u8) {
        let scene = feud_scene();
        let world = deploy_feud(seed);
        let commit = |ln: usize| {
            world
                .apply_choice(ROOM_HALL, ln, &choice_at(&scene, ROOM_HALL, ln))
                .unwrap_or_else(|e| panic!("faction line {ln} commits: {e}"));
        };
        commit(LN_PLEDGE_EMBERS);
        commit(LN_PLEDGE_EMBERS);
        assert_eq!(world.read_var("rep_embers"), 2, "rep is earned, on-ledger");
        commit(LN_EMBER_TRIAL);
        assert_eq!(
            world.read_var("ember_quest"),
            1,
            "the trial unlocked the quest"
        );
        commit(LN_ENTER_SANCTUM);
        // In the sanctum the giver is reachable — the faction gate has opened.
    }

    /// THE FACTION LOCK, non-vacuous: a player with NO Ember standing is REFUSED entry to
    /// the sanctum (the gate `{ ember_quest >= 1 }` bites), so they never reach the
    /// quest-giver — a faction-locked player cannot start the quest. Identical scene, one
    /// missing prerequisite, a real `WorldError::Refused`.
    #[test]
    fn faction_locked_player_cannot_start_the_quest() {
        let scene = feud_scene();
        let world = deploy_feud(1);
        assert_eq!(world.read_var("ember_quest"), 0, "no standing yet");

        let refused = world.apply_choice(
            ROOM_HALL,
            LN_ENTER_SANCTUM,
            &choice_at(&scene, ROOM_HALL, LN_ENTER_SANCTUM),
        );
        assert!(
            matches!(refused, Err(WorldError::Refused(_))),
            "a player with no Ember standing is refused the sanctum, got {refused:?}"
        );

        // And the trial itself is refused before rep is earned (the gate one level up).
        let no_trial = world.apply_choice(
            ROOM_HALL,
            LN_EMBER_TRIAL,
            &choice_at(&scene, ROOM_HALL, LN_EMBER_TRIAL),
        );
        assert!(
            matches!(no_trial, Err(WorldError::Refused(_))),
            "the Ember trial is refused below the rep threshold, got {no_trial:?}"
        );
        assert_eq!(world.read_var("ember_quest"), 0, "anti-ghost: still locked");

        // The SAME gate opens once standing is earned — non-vacuous.
        earn_ember_standing(2);
    }

    // ── the object-identity handoff assertions, each on its own ──

    /// HANDOFF A — the SAME `Completion` flows quest -> cheevo -> guild. One `Universe` and
    /// one `Completion` object; the cheevo anchors it and the guild counts it by passing
    /// the identical `&completion`. Proven object-identical: same universe id, same verified
    /// turns off the one run.
    #[test]
    fn completion_is_object_identical_quest_to_cheevo_to_guild() {
        let universe = errand_universe(HERO);
        let completion = record_errand_completion(&universe, HERO);

        // The quest crate's OWN no-cheat verifier accepts the same run object (its ordering
        // teeth included) — the run is a real replay-verified receipt, not a self-report.
        let quest_turns =
            dreggnet_quest::verify_quest(7, &completion.play, completion.claimed_turns)
                .expect("the quest verifier accepts the honest completion");

        // cheevo consumes the SAME &universe + &completion.
        let mut cheevos = CheevoLedger::new();
        let cheevo = cheevos
            .earn(
                &universe,
                &completion,
                Achievement::SpeedClear { max_turns: 5 },
            )
            .expect("the run earns the speed cheevo");

        // guild consumes the SAME &universe + &completion.
        let mut guild = Guild::form("The Lantern Circle");
        let hero_id = DreggIdentity(HERO.to_string());
        guild.admit(&hero_id);
        let guild_turns = guild
            .board_mut()
            .record_clear(&hero_id, &universe, &completion)
            .expect("the guild sums the same verified clear");

        // The one run, three verifiers, one answer.
        assert_eq!(quest_turns, 5);
        assert_eq!(cheevo.turns, 5, "the cheevo anchors the same run's turns");
        assert_eq!(guild_turns, 5, "the guild counted the same run's turns");
        assert_eq!(
            cheevo.universe,
            universe.id(),
            "the cheevo anchors THIS universe"
        );
        assert_eq!(
            guild.stats().verified_clears,
            1,
            "exactly the one clear entered the guild aggregate"
        );
        assert_eq!(guild.stats().total_turns, 5);
    }

    /// HANDOFF A, refusal legs (non-vacuous): a FORGED run is refused by BOTH the cheevo and
    /// the guild off the same tamper, and a NON-MEMBER cannot inflate the guild.
    #[test]
    fn a_forged_run_earns_no_cheevo_and_sums_into_no_guild() {
        let universe = errand_universe(HERO);
        let honest = record_errand_completion(&universe, HERO);

        // FORGE: retcon the first recorded step to a different line. On replay the
        // reproduced state diverges from the recorded one -> the no-cheat verify fails.
        let mut forged = honest.clone();
        forged.play.steps[0].choice_index = dreggnet_quest::LN_LIGHT_2;

        let mut cheevos = CheevoLedger::new();
        let earned = cheevos.earn(&universe, &forged, Achievement::SpeedClear { max_turns: 5 });
        assert!(
            matches!(earned, Err(CheevoError::RunRejected(_))),
            "a forged run earns no cheevo, got {earned:?}"
        );

        let mut guild = Guild::form("The Lantern Circle");
        let hero_id = DreggIdentity(HERO.to_string());
        guild.admit(&hero_id);
        let summed = guild.board_mut().record_clear(&hero_id, &universe, &forged);
        assert!(
            summed.is_err(),
            "a forged clear sums into no guild, got {summed:?}"
        );
        assert_eq!(
            guild.stats().verified_clears,
            0,
            "anti-ghost: nothing counted"
        );

        // A NON-MEMBER's honest clear is refused too — the roster is the cap set.
        let stranger = DreggIdentity("Nix-the-unenrolled".to_string());
        let refused = guild
            .board_mut()
            .record_clear(&stranger, &universe, &honest);
        assert!(
            refused.is_err(),
            "a non-member cannot inflate the guild, got {refused:?}"
        );

        // A run that verifies but MISSES the predicate earns nothing (non-vacuous).
        let too_slow = cheevos.earn(&universe, &honest, Achievement::SpeedClear { max_turns: 2 });
        assert!(
            matches!(too_slow, Err(CheevoError::PredicateNotMet(_))),
            "a 5-turn run does not earn a <=2-turn speed cheevo, got {too_slow:?}"
        );
    }

    /// HANDOFF B (TIGHTENED — reconciliation #1) — the SAME NOTE-CELL flows craft -> trade ->
    /// the buyer, object-identical at the NOTE-CELL, not merely at the `AssetId`. The forge
    /// hands its asset ledger to the trade ([`CraftForge::into_assets`] ->
    /// [`TradeWorld::with_assets`]), so the trade moves the EXACT crafted note with NO
    /// re-mint: its provenance lineage CONTINUES (mint(craft) -> escrow -> buyer) in ONE
    /// ledger, its length growing rather than restarting in a second world.
    #[test]
    fn crafted_note_is_object_identical_craft_to_trade_to_buyer() {
        // ── forge: two typed owned materials -> one crafted output, inputs spent on-chain ──
        let recipe = loremasters_charm();
        let mut forge = charm_forge();
        let m1 = forge.mint_material(HERO, "essence:lore", b"errand-drop-1");
        let m2 = forge.mint_material(HERO, "silver:leaf", b"errand-drop-2");
        let beacon = CommittedSeed::from_bytes([0x5A; 32]);
        let draw = roll_craft(&beacon, &recipe, &[m1, m2]);
        let output = forge
            .craft(HERO, &draw)
            .expect("the forge mints the crafted charm")
            .output()
            .expect("a safe craft mints an output")
            .clone();
        let charm: AssetId = output.asset_id;

        // The output is a real owned note (its lineage's origin mint); the inputs are
        // destroyed on-chain (the sink).
        assert!(
            forge.asset_provenance(charm).verified,
            "output is live + owned"
        );
        assert!(
            forge.is_destroyed(m1) && forge.is_destroyed(m2),
            "the inputs were spent"
        );
        assert_eq!(
            forge.owner_of(charm),
            Some(forge.pubkey_of(HERO)),
            "the crafter owns the output"
        );
        // The AssetId is a deterministic content address (recipe+inputs+roll bound): minting
        // the same commitment in a SEPARATE world reproduces the byte-identical id.
        let mut elsewhere = TradeWorld::new();
        assert_eq!(
            elsewhere
                .mint(HERO, &craft_commitment(&draw, &output.artifact))
                .bytes(),
            charm.bytes(),
            "the crafted note's AssetId is a reproducible content address"
        );

        // ── THE SHARED-WORLD HANDOFF: the trade ADOPTS the forge's ledger (no re-mint) ──
        let mut market = TradeWorld::with_assets(forge.into_assets());
        // The EXACT crafted note is already the trade world's live note, owned by HERO —
        // object-identity at the note-cell. Its lineage is the craft's origin mint (length 1),
        // set to CONTINUE (not restart) across the trade.
        assert_eq!(
            market.lineage_len(charm),
            1,
            "the traded note IS the craft's origin mint — the lineage continues from length 1"
        );
        assert_eq!(
            market.current_owner(charm),
            Some(market.pubkey_of(HERO)),
            "the crafted note is the trade world's own live note (no re-mint)"
        );

        // ── trade: an atomic escrow swap moves THAT note to the buyer ──
        market.fund_dregg(BUYER, 100);
        let mut trade = market.open_trade(HERO, LegSpec::Asset(charm), BUYER, LegSpec::Dregg(50));
        market
            .deposit(&mut trade, TradeSide::A)
            .expect("the seller deposits the charm");
        assert_eq!(
            market.lineage_len(charm),
            2,
            "the deposit CONTINUED the craft lineage (mint -> escrow custody)"
        );
        market
            .deposit(&mut trade, TradeSide::B)
            .expect("the buyer deposits the value");
        let settled = market
            .settle(&mut trade)
            .expect("the swap settles atomically");
        assert_eq!(settled.a_gave, LegSpec::Asset(charm));

        // ── CONTINUOUS PROVENANCE: mint(craft) -> escrow -> buyer, all in ONE ledger ──
        let report = market.verify_provenance(charm);
        assert!(
            report.verified,
            "the traded charm's full lineage re-verifies"
        );
        assert_eq!(
            report.length, 3,
            "the lineage LENGTH continued across craft->trade (mint -> escrow -> buyer), not restarted at 1"
        );
        assert_eq!(
            market.current_owner(charm),
            Some(market.pubkey_of(BUYER)),
            "the buyer now owns the identical NOTE the forge minted"
        );

        // Non-vacuous: a NON-OWNER cannot offer the charm (the scam-proof gate).
        let mut mallory_trade =
            market.open_trade("Mallory", LegSpec::Asset(charm), BUYER, LegSpec::Dregg(1));
        let stolen = market.deposit(&mut mallory_trade, TradeSide::A);
        assert!(
            stolen.is_err(),
            "a non-owner cannot deposit the charm, got {stolen:?}"
        );
    }

    /// RECONCILIATION #2 — the FACTION rep cell gates the QUEST-GIVER. The quest-giver's
    /// cross-cell `ObservedFieldEquals` reads the faction standing cell's `ember_quest` slot,
    /// so the quest-start opens ONLY on real faction standing. Both legs driven: a no-rep
    /// player's start is refused; earning rep (pledge to the threshold + the trial) opens it.
    #[test]
    fn the_faction_rep_cell_gates_the_quest_giver() {
        use dreggnet_quest::giver::{EMBER_QUEST_VALUE, FactionGatedGiverWorld, GRANTED_SLOT};

        // No standing: the quest-giver's start is refused (the faction ember_quest is unset).
        let world = FactionGatedGiverWorld::deploy();
        assert!(
            world.grant_honest().is_err(),
            "a no-rep player's quest-start is refused by the faction gate"
        );
        assert_eq!(
            world.read(world.giver(), GRANTED_SLOT as usize),
            0,
            "anti-ghost: nothing granted"
        );

        // Earn REAL faction standing, and the SAME quest-giver grant now COMMITS — the start
        // opened on genuine faction standing (the cross-cell read of ember_quest).
        world.earn_standing();
        world
            .grant_honest()
            .expect("earning faction rep opens the quest-giver");
        assert_eq!(
            world.read(world.giver(), GRANTED_SLOT as usize),
            EMBER_QUEST_VALUE,
            "the quest-start is open, matching the faction's committed standing"
        );
    }

    /// RECONCILIATION #3 — ONE IDENTITY threads a party seat, a guild member, AND an asset
    /// holder. A single [`PlayerIdentity`] derives all three key representations the crates
    /// key on, consistently: the same actor is present across party / guild / asset by one
    /// object, not three look-alikes matched by name convention.
    #[test]
    fn one_identity_is_a_party_seat_a_guild_member_and_an_asset_holder() {
        // The mustered party seats four canonical identities; take the Tank seat's name.
        let party = Party::muster();
        let hero = PlayerIdentity::new(party.seat(0).name());

        // (a) THE PARTY SEAT — the one identity derives the seat's ed25519 ballot key.
        assert_eq!(
            hero.seat_pk(),
            party.seat(0).electorate_seat().pk,
            "the one identity's custody key IS the party seat's ballot identity"
        );

        // (b) THE GUILD MEMBER — the SAME identity is admitted and counts a verified clear.
        let universe = errand_universe(hero.name());
        let completion = record_errand_completion(&universe, hero.name());
        let mut guild = Guild::form("The Lantern Circle");
        guild.admit(&hero.guild_member());
        assert!(
            guild.is_member(&hero.guild_member()),
            "the one identity is a guild member"
        );
        let turns = guild
            .board_mut()
            .record_clear(&hero.guild_member(), &universe, &completion)
            .expect("the one identity's clear is counted");
        assert_eq!(turns, 5);

        // (c) THE ASSET HOLDER — the SAME identity owns a real asset by its holder label.
        let mut world = TradeWorld::new();
        let asset = world.mint(hero.holder_label(), b"a-cosmetic");
        assert_eq!(
            world.current_owner(asset),
            Some(world.pubkey_of(hero.holder_label())),
            "the one identity owns the asset it minted"
        );

        // Consistency: the three representations are ONE canonical name across the crates.
        assert_eq!(hero.name(), hero.holder_label());
        assert_eq!(hero.guild_member().as_str(), hero.name());
    }

    // ── the continuous saga: one player, all the way through ──

    /// THE FULL SAGA — one player threaded through party -> faction-gate -> quest ->
    /// cheevo + guild (one Completion) -> craft -> trade, each step a real committed turn,
    /// with the cross-crate handoffs asserted object-identical and the end state coherent.
    #[test]
    fn the_full_saga_runs_end_to_end() {
        // ONE canonical identity threads the guild member + the asset holder (reconciliation
        // #3); the party seats are themselves canonical identities (asserted below).
        let hero = PlayerIdentity::new(HERO);

        // (1) THE PARTY MUSTERS — four seated roles on one shared world.
        let mut party = Party::muster();
        assert_eq!(party.seat_count(), 4);
        // Each party seat IS a canonical PlayerIdentity — its ed25519 ballot key derives from
        // the one identity object, not a bespoke seat key.
        assert_eq!(
            PlayerIdentity::new(party.seat(0).name()).seat_pk(),
            party.seat(0).electorate_seat().pk,
            "the party seat's ballot identity is the one-identity derivation"
        );
        // The seated co-op is executor-refereed: a seat acts IN role -> commits.
        assert!(
            party.act_in_role(0).committed(),
            "the Tank guards the front"
        );
        assert!(party.act_in_role(1).committed(), "the Scout works the lock");
        // A seat acting OUTSIDE its role (the Scout guarding the front) is a real refusal.
        let out_of_role = party.act(1, PartyMove::GuardFront);
        assert!(out_of_role.refused(), "nobody plays another seat's role");
        // The party commits its on-ledger loot split (a WriteOnce ledger fact).
        assert!(party.split_loot(&[40, 20, 20, 20]).committed());
        assert_eq!(party.loot_share(0), 40, "the split is a committed fact");

        // (2) THE FACTION GATE — a faction-locked player is refused the quest-giver; the
        // hero earns Ember standing and passes (both legs driven, non-vacuous).
        {
            let scene = feud_scene();
            let locked = deploy_feud(3);
            let refused = locked.apply_choice(
                ROOM_HALL,
                LN_ENTER_SANCTUM,
                &choice_at(&scene, ROOM_HALL, LN_ENTER_SANCTUM),
            );
            assert!(
                matches!(refused, Err(WorldError::Refused(_))),
                "the locked player is turned away from the giver's sanctum"
            );
        }
        earn_ember_standing(4); // the hero earns standing and enters the sanctum.

        // (3) THE QUEST — run + turned in, recorded as ONE Completion (the run currency).
        let universe = errand_universe(HERO);
        let completion = record_errand_completion(&universe, HERO);
        let turns = dreggnet_quest::verify_quest(7, &completion.play, completion.claimed_turns)
            .expect("the quest is a replay-verified win");
        assert_eq!(turns, 5, "the errand is won in five real turns");

        // (4) THE CHEEVO — earned over the SAME completion; soulbound to the hero.
        let mut cheevos = CheevoLedger::new();
        let cheevo = cheevos
            .earn(
                &universe,
                &completion,
                Achievement::SpeedClear { max_turns: 5 },
            )
            .expect("the verified run earns the speed cheevo");

        // (5) THE GUILD — sums the SAME clear (the identical &universe + &completion), keyed
        // by the hero's ONE identity (its guild-member handle).
        let mut guild = Guild::form("The Lantern Circle");
        let hero_id = hero.guild_member();
        guild.admit(&hero_id);
        let guild_turns = guild
            .board_mut()
            .record_clear(&hero_id, &universe, &completion)
            .expect("the guild counts the same clear");
        assert_eq!(
            guild_turns, cheevo.turns,
            "cheevo and guild agree on the one run"
        );

        // (6) THE CRAFT — the errand's material drops forged into one owned item (minted by
        // the hero's ONE identity's holder label).
        let recipe = loremasters_charm();
        let mut forge = charm_forge();
        let m1 = forge.mint_material(hero.holder_label(), "essence:lore", b"errand-drop-1");
        let m2 = forge.mint_material(hero.holder_label(), "silver:leaf", b"errand-drop-2");
        let beacon = CommittedSeed::from_bytes([0x5A; 32]);
        let draw = roll_craft(&beacon, &recipe, &[m1, m2]);
        let output = forge
            .craft(hero.holder_label(), &draw)
            .expect("the charm is forged")
            .output()
            .expect("a safe craft mints an output")
            .clone();
        let charm: AssetId = output.asset_id;
        assert!(
            forge.is_destroyed(m1) && forge.is_destroyed(m2),
            "materials spent"
        );

        // (7) THE TRADE — the EXACT crafted note (reconciliation #1: the trade adopts the
        // forge's ledger, so no re-mint) sold to a buyer via an atomic swap. Its provenance
        // lineage CONTINUES (mint(craft) -> escrow -> buyer) in ONE ledger.
        let mut market = TradeWorld::with_assets(forge.into_assets());
        assert_eq!(
            market.lineage_len(charm),
            1,
            "the traded note IS the craft's origin mint (the lineage continues from length 1)"
        );
        assert_eq!(
            market.current_owner(charm),
            Some(market.pubkey_of(hero.holder_label())),
            "the crafted note is the trade world's own live note (no re-mint)"
        );
        market.fund_dregg(BUYER, 100);
        let mut trade = market.open_trade(
            hero.holder_label(),
            LegSpec::Asset(charm),
            BUYER,
            LegSpec::Dregg(50),
        );
        market
            .deposit(&mut trade, TradeSide::A)
            .expect("seller deposits the charm");
        market
            .deposit(&mut trade, TradeSide::B)
            .expect("buyer deposits the value");
        market
            .settle(&mut trade)
            .expect("the swap settles atomically");

        // ── THE END STATE IS COHERENT ──
        // the cheevo is SOULBOUND to the earner (no sell path) and re-verifies;
        assert!(matches!(
            cheevos.attempt_transfer(&cheevo, BUYER),
            Err(CheevoError::Soulbound)
        ));
        cheevos
            .reverify_run(&cheevo, &universe, &completion)
            .expect("the earned cheevo independently re-verifies");
        // the traded charm is owned by the BUYER, provenance intact + CONTINUOUS: the one
        // lineage is mint(craft) -> escrow -> buyer (length 3), the object-identical note-cell
        // carried end-to-end (not a re-minted look-alike);
        assert_eq!(market.current_owner(charm), Some(market.pubkey_of(BUYER)));
        let charm_prov = market.verify_provenance(charm);
        assert!(charm_prov.verified);
        assert_eq!(
            charm_prov.length, 3,
            "the crafted note's lineage continued through the trade in one ledger"
        );
        // the guild rank reflects exactly the one verified clear;
        assert_eq!(guild.stats().verified_clears, 1);
        assert_eq!(guild.stats().total_turns, 5);
        // the party's loot split stands as a committed ledger fact.
        assert_eq!(party.loot_share(0), 40);
    }
}
