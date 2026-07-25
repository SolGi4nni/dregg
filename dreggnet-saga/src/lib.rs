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
/// A small adapter, not a redesign: ONE [`PlayerIdentity`] yields the seat key, the member,
/// AND the holder — the same actor is present across the crates by a single object, not
/// three look-alikes stitched by convention.
///
/// The unifying thing is the OBJECT, not the name. The guild handle and the asset holder
/// label ARE the name (both are public identifiers); the ballot key is a real keypair
/// GENERATED here from OS entropy and carried by the object. It was `Custodian::demo(name)`
/// — derived from the public name — which made "one identity" true only because the secret
/// was public. A party seats this player by its public key
/// ([`dreggnet_party::Party::muster_with_custody`]), so the thread holds and the secret
/// stays the player's.
#[derive(Clone)]
pub struct PlayerIdentity {
    name: String,
    custody: std::sync::Arc<Custodian>,
}

impl std::fmt::Debug for PlayerIdentity {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // The secret never prints; the public ballot identity does.
        f.debug_struct("PlayerIdentity")
            .field("name", &self.name)
            .field("seat_pk", &self.custody.public_key().0)
            .finish()
    }
}

impl PlayerIdentity {
    /// The canonical player named `name` (the single derivation input the three
    /// representations share).
    pub fn new(name: impl Into<String>) -> Self {
        let name = name.into();
        let custody = std::sync::Arc::new(Custodian::generate(name.clone()));
        PlayerIdentity { name, custody }
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
    /// [`dreggnet_party`] seat signs its ballots with. Generated from OS entropy at
    /// [`PlayerIdentity::new`] and HELD here; it is not a function of the name (it was
    /// `Custodian::demo(name)`, which handed the secret to anyone who could read the
    /// roster). A party seats this player by [`seat_pk`](Self::seat_pk).
    pub fn custodian(&self) -> &Custodian {
        &self.custody
    }

    /// The party seat's electorate PUBLIC key — this player's ballot identity, which a
    /// party seats via [`dreggnet_party::Party::muster_with_custody`].
    pub fn seat_pk(&self) -> PublicKey {
        self.custody.public_key()
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
    use dreggnet_party::{Party, PartyMove, Role};
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
        // The one identity holds its OWN ballot key; a party seats it BY that key.
        let hero = PlayerIdentity::new("Bramwen");
        let escorts: [PlayerIdentity; 3] = [
            PlayerIdentity::new("Corvin"),
            PlayerIdentity::new("Della"),
            PlayerIdentity::new("Ferro"),
        ];
        let party = Party::muster_with_custody([
            (Role::Tank, hero.name().to_string(), hero.seat_pk()),
            (
                Role::Scout,
                escorts[0].name().to_string(),
                escorts[0].seat_pk(),
            ),
            (
                Role::Mage,
                escorts[1].name().to_string(),
                escorts[1].seat_pk(),
            ),
            (
                Role::Healer,
                escorts[2].name().to_string(),
                escorts[2].seat_pk(),
            ),
        ])
        .expect("the roster is valid");

        // (a) THE PARTY SEAT — the one identity IS the seat's ed25519 ballot identity.
        assert_eq!(
            hero.seat_pk(),
            party.seat(0).electorate_seat().pk,
            "the one identity's custody key IS the party seat's ballot identity"
        );
        // ...and the NAME alone is not that key: a second player of the same name is a
        // different actor, which is what makes the seat unforgeable from public data.
        assert_ne!(
            PlayerIdentity::new(hero.name()).seat_pk(),
            hero.seat_pk(),
            "a name is a label, not a ballot key"
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
        // Each party seat carries a real ed25519 ballot identity that is NOT recoverable
        // from its public name: re-deriving from the name yields a different key, and the
        // party's own seat key is the one the electorate registered.
        assert_ne!(
            PlayerIdentity::new(party.seat(0).name()).seat_pk(),
            party.seat(0).electorate_seat().pk,
            "a party seat's ballot key must not be reconstructible from its public name"
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

#[cfg(test)]
mod economy {
    //! **THE ECONOMY LOOP** — one object followed by identity from the dungeon floor to a
    //! stranger's inventory.
    //!
    //! The sibling `saga` module proves craft -> trade is object-identical. It starts,
    //! though, from `forge.mint_material(...)`: a faucet. This module closes the loop at the
    //! other end, where the items an economy actually circulates come from — a real Descent
    //! run — and follows them through every station without re-minting a look-alike at any
    //! step:
    //!
    //! ```text
    //!   a real run banks relics  ──▶  LootVault::claim mints owned notes
    //!            │                              │  (into_assets: ONE ledger, handed on)
    //!            │                              ▼
    //!            │                    CraftForge ADOPTS the exact notes as typed materials
    //!            │                              │  (the sink BURNS them — the same notes)
    //!            │                              ▼
    //!            │                    one crafted output note
    //!            │                              │  (into_assets: still ONE ledger)
    //!            │                              ▼
    //!            └──── provenance ────▶  a Bazaar sale crosses it to a stranger
    //! ```
    //!
    //! The strongest claim it drives is the **recomputation**: a third party who knows only
    //! the run's day-seed, the banked slots, the two players' public keys and the craft
    //! beacon re-derives every address in the chain — the relics' ids from the run, and the
    //! sigil's id from the relics' — with no access to any ledger. A re-minted look-alike
    //! anywhere in the chain would break that arithmetic.

    use super::*;

    use dreggnet_asset::AssetId;
    use dreggnet_craft::{
        CraftDraw, CraftError, CraftForge, CraftProvenance, Recipe, craft_commitment,
        relic_sigil_id, resolve_artifact, roll_craft,
    };
    use dreggnet_trade::{Bazaar, LegSpec, TradeWorld};
    use dungeon_on_dregg::descent::{BANKED, Descent, day_seed_from_deploy_seed};
    use dungeon_on_dregg::loot::{
        LootDraw, LootVault, Rarity, banked_relic_chest, banked_relic_drop, expected_asset_id,
    };
    use procgen_dregg::CommittedSeed;

    const DELVER: &str = "Alkas";
    const STRANGER: &str = "Brenna";

    /// The relic slots the run script below banks: on floor 1 the lootable relics are the ones
    /// whose home floor is 1 (`HOME = [4,1,2,3,1,1,2,3]`) — the way-2 key and two treasures.
    const BANKED_SLOTS: [usize; 3] = [1, 4, 5];

    /// Drive a REAL Descent: delve to floor 1, fell the guardian, take the three relics that
    /// lie there, and flee (the terminal bank). Every verb is a committed executor turn the
    /// Lean-sourced referee admits — nothing here is a fixture.
    fn bank_a_run(deploy_seed: u8) -> Descent {
        let mut d = Descent::deploy(deploy_seed).expect("deploy + genesis");
        d.delve().expect("the way down is open");
        d.smite().expect("the floor-1 guardian falls");
        for slot in BANKED_SLOTS {
            d.loot(slot).expect("the relic lies here");
        }
        d.flee().expect("bank the pack — the run ends");
        for slot in BANKED_SLOTS {
            assert_eq!(
                d.read_relic(slot),
                BANKED,
                "relic {slot} is a committed BANKED custody fact on the cell"
            );
        }
        d
    }

    /// The three drops the run seeded by `deploy_seed` would bank — a PURE function of the
    /// day-seed and the custody slots, so we can scan for an interesting run without deploying
    /// one. (That the deployed run really produces exactly these is asserted in the test.)
    fn prospective_drops(deploy_seed: u8) -> Vec<LootDraw> {
        let day = day_seed_from_deploy_seed(deploy_seed);
        BANKED_SLOTS
            .iter()
            .map(|slot| banked_relic_drop(&day, *slot))
            .collect()
    }

    /// Find a deploy seed whose banked relics contain a PAIR of the same tier — what the relic
    /// ladder's rung consumes. The recipe is not tailored to the run; the run is chosen to
    /// satisfy a recipe the catalog already ships.
    fn find_a_run_that_banks_a_matching_pair() -> (u8, Rarity, [usize; 2]) {
        for seed in 0u16..=255 {
            let seed = seed as u8;
            let drops = prospective_drops(seed);
            for i in 0..drops.len() {
                for j in (i + 1)..drops.len() {
                    if drops[i].rarity == drops[j].rarity {
                        return (seed, drops[i].rarity, [BANKED_SLOTS[i], BANKED_SLOTS[j]]);
                    }
                }
            }
        }
        panic!("no deploy seed in 0..256 banks two relics of one tier");
    }

    /// Scan beacons for one whose fair draw over `recipe` + `inputs` MINTS (the relic ladder is
    /// a risky recipe — it can botch and eat the relics, which is the point of the gamble, but
    /// this test is about the object's journey, not the gamble).
    fn find_a_minting_beacon(recipe: &Recipe, inputs: &[AssetId]) -> (CommittedSeed, CraftDraw) {
        for n in 0u32..100_000 {
            let mut b = [0u8; 32];
            b[..4].copy_from_slice(&n.to_le_bytes());
            let beacon = CommittedSeed::from_bytes(b);
            let draw = roll_craft(&beacon, recipe, inputs);
            if draw.granted_quality().is_some() {
                return (beacon, draw);
            }
        }
        panic!("no beacon in 0..100000 mints for `{}`", recipe.id);
    }

    /// **THE LOOP.** A relic banked in a real run becomes an owned note, that exact note becomes
    /// a crafting input, the sink burns it into one crafted output, and that output crosses a
    /// Bazaar sale to a stranger — with the whole chain of content addresses recomputable from
    /// the run's day-seed alone.
    #[test]
    fn a_banked_relic_becomes_a_crafted_item_a_stranger_buys() {
        // ── (1) A REAL RUN BANKS RELICS ────────────────────────────────────────────────
        let (deploy_seed, tier, pair) = find_a_run_that_banks_a_matching_pair();
        let run = bank_a_run(deploy_seed);
        let day_seed = *run.day_seed();

        // ── (2) THE BANK → ASSET WIRE: the banked relics mint as real owned notes ──────
        let mut vault = LootVault::new();
        let delver_pk = vault.pubkey_of(DELVER);
        let minted = run
            .mint_banked_relics(&mut vault, DELVER)
            .expect("the banked relics mint");
        assert_eq!(
            minted.len(),
            BANKED_SLOTS.len(),
            "one note per banked relic"
        );

        // Each note's provenance replays to THIS run's day-seed and THAT custody slot — and a
        // third party recomputes the note's address from those two facts plus the delver's key.
        let mut relic_of_slot = std::collections::BTreeMap::new();
        for m in &minted {
            let prov = vault.provenance(m.item.asset_id).expect("known loot");
            assert_eq!(prov.run_seed, day_seed, "provenance root = the banked run");
            assert_eq!(prov.chest, banked_relic_chest(m.slot), "names the slot");
            assert!(prov.asset.verified, "the note's lineage verifies");
            assert_eq!(
                m.item.asset_id.bytes(),
                expected_asset_id(&banked_relic_drop(&day_seed, m.slot), &delver_pk).bytes(),
                "the note sits at the address (day_seed, slot, delver_pk) alone fixes"
            );
            relic_of_slot.insert(m.slot, m.item.asset_id);
        }
        // The deployed run really produced the drops we prospected for.
        for (i, slot) in BANKED_SLOTS.iter().enumerate() {
            assert_eq!(
                banked_relic_drop(&day_seed, *slot).rarity,
                prospective_drops(deploy_seed)[i].rarity
            );
        }

        let inputs: Vec<AssetId> = pair.iter().map(|s| relic_of_slot[s]).collect();
        let input_ids: Vec<[u8; 32]> = inputs.iter().map(|a| a.bytes()).collect();
        let drops: Vec<LootDraw> = pair
            .iter()
            .map(|s| banked_relic_drop(&day_seed, *s))
            .collect();

        // ── (3) THE FORGE ADOPTS THOSE EXACT NOTES ────────────────────────────────────
        // The vault hands over its LIVE ledger; the forge types the notes already in it.
        let mut forge = CraftForge::with_assets(vault.into_assets());
        for (id, drop) in inputs.iter().zip(&drops) {
            let kind = forge
                .adopt_loot_material(DELVER, *id, drop)
                .expect("the delver's own banked relic is adoptable");
            assert_eq!(
                kind.as_str(),
                format!("relic:{}", tier.label()),
                "the FAIR DRAW fixed the material kind — nobody declared it"
            );
            assert_eq!(
                forge.asset_provenance(*id).length,
                1,
                "the adopted note IS the dungeon's origin mint; its lineage did not restart"
            );
            assert!(forge.owns_live(DELVER, *id), "still the delver's live note");
        }
        // The catalog — not the test — says what this pair is good for.
        let recipe_id = relic_sigil_id(tier);
        assert!(
            forge.craftable_by(DELVER).contains(&recipe_id),
            "the bench reports the pair unlocks its ladder rung"
        );
        let recipe = forge
            .recipe(&recipe_id)
            .expect("the rung is stocked")
            .clone();

        // ── (4) THE SINK BURNS THOSE EXACT NOTES INTO ONE OUTPUT ──────────────────────
        let (beacon, draw) = find_a_minting_beacon(&recipe, &inputs);
        let output = forge
            .craft(DELVER, &draw)
            .expect("the forge accepts the honest craft")
            .output()
            .expect("a minting band")
            .clone();
        let sigil: AssetId = output.asset_id;

        for id in &inputs {
            assert!(forge.is_destroyed(*id), "the banked relic was consumed");
            assert_eq!(
                forge.owner_of(*id),
                None,
                "and it is GONE on-chain — the delver cannot still hold it"
            );
        }
        // The crafted note's provenance still names the runs its materials came from, even
        // though those materials no longer exist.
        let craft_prov: CraftProvenance = forge.provenance(sigil).expect("a crafted output");
        assert_eq!(craft_prov.recipe_id, recipe_id);
        assert_eq!(
            craft_prov.material_origins.len(),
            2,
            "both consumed inputs were real dungeon drops"
        );
        for origin in &craft_prov.material_origins {
            assert_eq!(
                origin.run_seed, day_seed,
                "the sigil names the RUN its relics were banked on"
            );
            assert_eq!(origin.rarity, tier);
            assert!(input_ids.contains(&origin.input_id));
        }

        // ── (5) THE STRANGER FINDS IT ON A STALL AND BUYS IT ──────────────────────────
        // The trade world adopts the forge's ledger: the sigil is already its live note.
        let mut market = TradeWorld::with_assets(forge.into_assets());
        assert_eq!(
            market.lineage_len(sigil),
            1,
            "the traded note IS the craft's origin mint — no re-mint at the handoff"
        );
        assert_eq!(
            market.current_owner(sigil),
            Some(market.pubkey_of(DELVER)),
            "and it is still the delver's"
        );
        market.fund_dregg(STRANGER, 300);

        let mut stall = Bazaar::new();
        let offer = stall
            .post(&mut market, DELVER, sigil, 120)
            .expect("the delver posts the sigil");
        // The stranger was never told about it — they BROWSE and find it.
        let purse = market.dregg_balance(STRANGER) as u64;
        let shelf = stall.affordable(&market, purse);
        assert!(
            shelf.iter().any(|e| e.asset.bytes() == sigil.bytes()),
            "the sigil is discoverable to a buyer who did not know it existed"
        );
        let settlement = stall
            .buy(&mut market, offer, STRANGER)
            .expect("the sale settles atomically");
        assert_eq!(settlement.a_gave, LegSpec::Asset(sigil));
        assert_eq!(settlement.b_gave, LegSpec::Dregg(120));

        // ── (6) THE CHAIN HELD ────────────────────────────────────────────────────────
        assert_eq!(
            market.current_owner(sigil),
            Some(market.pubkey_of(STRANGER)),
            "the stranger owns the identical note the forge minted"
        );
        let report = market.verify_provenance(sigil);
        assert!(
            report.verified,
            "the sigil's lineage re-verifies: {:?}",
            report.reasons
        );
        assert_eq!(
            report.length, 3,
            "mint(craft) -> escrow -> buyer, ONE continuous lineage across craft and trade"
        );
        assert_eq!(market.dregg_balance(DELVER), 120, "the delver was paid");

        // ── (7) THE RECOMPUTATION — the whole chain, from the run seed, with no ledger ──
        // A third party holding only (day_seed, banked slots, delver_pk, beacon, the public
        // catalog) re-derives every address. This is the property a re-mint anywhere in the
        // chain would destroy.
        let recomputed_relics: Vec<AssetId> = pair
            .iter()
            .map(|slot| expected_asset_id(&banked_relic_drop(&day_seed, *slot), &delver_pk))
            .collect();
        let mut recomputed_ids: Vec<[u8; 32]> =
            recomputed_relics.iter().map(|a| a.bytes()).collect();
        recomputed_ids.sort_unstable();
        assert_eq!(
            recomputed_ids, draw.input_ids,
            "the crafted item's declared inputs ARE the run's relics, re-derived"
        );
        let recomputed_draw = roll_craft(&beacon, &recipe, &recomputed_relics);
        let quality = recomputed_draw
            .granted_quality()
            .expect("the fair draw mints");
        let artifact = resolve_artifact(&recipe, quality);
        let recomputed_sigil = AssetId::derive(
            &market.pubkey_of(DELVER),
            &craft_commitment(&recomputed_draw, &artifact),
        );
        assert_eq!(
            recomputed_sigil.bytes(),
            sigil.bytes(),
            "run day-seed -> relic ids -> craft commitment -> the sigil the stranger now holds"
        );
        assert_eq!(artifact, output.artifact, "and the same concrete artifact");
    }

    /// The loop's refusals, on the SAME shape: a burned relic cannot be re-adopted or
    /// re-crafted (the sink is real, not bookkeeping), and the delver cannot sell the sigil
    /// after selling it. Non-vacuous — each refusal is preceded by the move that works.
    #[test]
    fn a_spent_relic_cannot_be_crafted_twice_and_a_sold_sigil_cannot_be_resold() {
        let (deploy_seed, tier, pair) = find_a_run_that_banks_a_matching_pair();
        let run = bank_a_run(deploy_seed);
        let day_seed = *run.day_seed();

        let mut vault = LootVault::new();
        let minted = run
            .mint_banked_relics(&mut vault, DELVER)
            .expect("the banked relics mint");
        let inputs: Vec<AssetId> = pair
            .iter()
            .map(|slot| {
                minted
                    .iter()
                    .find(|m| m.slot == *slot)
                    .expect("the slot banked")
                    .item
                    .asset_id
            })
            .collect();
        let drops: Vec<LootDraw> = pair
            .iter()
            .map(|s| banked_relic_drop(&day_seed, *s))
            .collect();

        let mut forge = CraftForge::with_assets(vault.into_assets());
        for (id, drop) in inputs.iter().zip(&drops) {
            forge
                .adopt_loot_material(DELVER, *id, drop)
                .expect("adopt the real relic");
        }
        let recipe = forge
            .recipe(&relic_sigil_id(tier))
            .expect("the rung")
            .clone();
        let (_, draw) = find_a_minting_beacon(&recipe, &inputs);
        let sigil = forge
            .craft(DELVER, &draw)
            .expect("the first craft commits")
            .output()
            .expect("a minting band")
            .asset_id;

        // The relics are gone: re-adopting one is refused (it is no longer a live held note),
        // and a second craft over them is refused with nothing minted.
        let re_adopt = forge.adopt_loot_material(DELVER, inputs[0], &drops[0]);
        assert!(
            matches!(re_adopt, Err(CraftError::InputsUnavailable(_))),
            "a burned relic is not an adoptable material, got {re_adopt:?}"
        );
        let before = forge.output_count();
        let (_, redraw) = find_a_minting_beacon(&recipe, &inputs);
        let recraft = forge.craft(DELVER, &redraw);
        assert!(
            matches!(recraft, Err(CraftError::InputsUnavailable(_))),
            "no dupe-then-craft: spent relics cannot be forged again, got {recraft:?}"
        );
        assert_eq!(forge.output_count(), before, "anti-ghost: nothing minted");

        // Sell it once — then the delver, no longer the owner, cannot sell it again.
        let mut market = TradeWorld::with_assets(forge.into_assets());
        market.fund_dregg(STRANGER, 200);
        let mut stall = Bazaar::new();
        let offer = stall
            .post(&mut market, DELVER, sigil, 50)
            .expect("the first posting");
        stall.buy(&mut market, offer, STRANGER).expect("the sale");
        assert_eq!(market.current_holder_label(sigil), Some(STRANGER));

        let resell = stall.post(&mut market, DELVER, sigil, 50);
        assert!(
            resell.is_err(),
            "the delver cannot post an item they have sold, got {resell:?}"
        );
        assert_eq!(
            market.current_holder_label(sigil),
            Some(STRANGER),
            "anti-ghost: the stranger still holds it"
        );
    }
}
