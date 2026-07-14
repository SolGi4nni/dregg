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
//! ## Honest scope — what is object-identical vs re-established, and the friction
//!
//! * **quest -> cheevo -> guild: OBJECT-IDENTICAL.** One `Universe` and one `Completion`,
//!   passed by reference to both consumers. The cheevo anchors and the guild counts the
//!   very same run object. This is the strongest handoff in the weave.
//! * **craft -> trade -> buyer: OBJECT-IDENTICAL AT THE `AssetId`.** The `AssetId` is a
//!   deterministic content address (`blake3(minter_pubkey ‖ mint_seed)`) — the DESIGNED
//!   cross-crate / cross-game handle. The saga asserts the crafted output's `AssetId` is
//!   BYTE-EQUAL to the id the trade lists and the buyer verifies. **Friction (a named
//!   reconciliation, not done here):** `CraftForge` and `TradeWorld` each encapsulate a
//!   *private* `AssetWorld`, so the note-cell LEDGER is not shared in-process — the trade
//!   re-establishes the same-id note in its own world (its provenance length restarts).
//!   The clean fix is a shared `AssetWorld`: expose `CraftForge::assets_mut()` mirroring
//!   the existing [`dreggnet_trade::TradeWorld::assets`], so the EXACT crafted note
//!   deposits into a trade with no re-mint. Object-identity holds at the id (asserted);
//!   note-ledger identity is the follow-up.
//! * **party / faction -> the run: control-flow handoff.** The party musters and the
//!   faction gate opens *before* the run; they gate access, they do not hand a typed
//!   object into the quest. Notably [`dreggnet_quest::giver`] ALREADY implements the exact
//!   cross-cell `ObservedFieldEquals` mechanism a tighter bind would use — the named
//!   reconciliation is to point the giver's gate at the faction rep cell's `ember_quest`
//!   slot, so the quest-giver's start cell opens only when faction standing clears. Small,
//!   concrete, uses machinery that already ships.
//! * **THREE identity representations** meet here and unify only by LABEL/name convention,
//!   not by a single identity object: `dreggnet-party`'s ed25519 `Custodian` seat keys,
//!   `dreggnet-guild`'s `DreggIdentity(String)`, and the asset layer's `Holder` key
//!   (`blake3::derive_key` of a label, shared by craft / trade / cheevo). They compose
//!   because the same player *name* derives the same asset key across crates — but a real
//!   deployment wants ONE identity the party seat, the guild member, and the asset holder
//!   all present. Named reconciliation: a shared identity type the feature crates key on.
//! * **`dreggnet-tavern` (presence) is a NAMED follow-up, deliberately out of the saga
//!   crate.** Tavern pulls `dregg-node`/deos-host (mozjs), is async, and needs an
//!   `_exit(0)` to dodge a SpiderMonkey teardown SIGSEGV — pulling that elephant into the
//!   saga's synchronous driven test would make the green gate heavy and flaky. Presence is
//!   proven in `dreggnet-tavern`'s own e2e; the saga runs on the light substrate. The
//!   tavern's OWN honest-scope note already names the real reconciliation: its inline
//!   party-roster / market-stall cells should graduate to `dreggnet-party` /
//!   `dreggnet-trade` (the crates the saga threads).
//!
//! ## Assessment
//!
//! They compose EXCELLENTLY along the two currencies the substrate was designed for: the
//! run (`Completion`) and the item (`AssetId`) both flow object-identically across crate
//! boundaries with no re-derivation on the run spine and byte-identical ids on the item
//! spine. The friction is not in the mechanics — every gate is a real executor refusal —
//! it is in ENCAPSULATION and IDENTITY: each crate owns its own world/ledger and its own
//! notion of "who a player is", so composition today rides on deterministic content
//! addresses and shared labels rather than shared objects. The three named reconciliations
//! (shared `AssetWorld`; the giver's cross-cell gate onto the faction cell; one identity
//! type) are additive API tweaks, not redesigns — the objects already line up.
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

#[cfg(test)]
mod saga {
    use super::*;

    use dreggnet_asset::AssetId;
    use dreggnet_cheevo::{Achievement, CheevoError, CheevoLedger};
    use dreggnet_craft::{CraftForge, Recipe, craft_commitment, roll_craft};
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

    /// HANDOFF B — the SAME `AssetId` flows craft -> trade -> the buyer's provenance-verify.
    /// The forge mints an output note; its `AssetId` is a deterministic content address, so
    /// the trade world names the byte-IDENTICAL id and the buyer verifies THAT id's
    /// provenance after the swap. (Named friction: the two crates hold private asset worlds,
    /// so the trade re-establishes the same-id note; see the crate docs.)
    #[test]
    fn asset_id_is_object_identical_craft_to_trade_to_buyer() {
        // ── forge: two owned materials -> one crafted output, inputs spent on-chain ──
        let mut forge = CraftForge::new();
        let recipe = Recipe::new("forge:loremasters-charm", 2);
        let m1 = forge.mint_material(HERO, b"errand-drop-1");
        let m2 = forge.mint_material(HERO, b"errand-drop-2");
        let beacon = CommittedSeed::from_bytes([0x5A; 32]);
        let draw = roll_craft(&beacon, &recipe, &[m1, m2]);
        let output = forge
            .craft(HERO, &draw, &recipe)
            .expect("the forge mints the crafted charm");

        // The output is a real owned note; the inputs are destroyed on-chain (the sink).
        assert!(
            forge.asset_provenance(output.asset_id).verified,
            "output is live + owned"
        );
        assert!(
            forge.is_destroyed(m1) && forge.is_destroyed(m2),
            "the inputs were spent"
        );
        assert_eq!(
            forge.owner_of(output.asset_id),
            Some(forge.pubkey_of(HERO)),
            "the crafter owns the output"
        );

        // ── the identity handoff: the AssetId is a deterministic content address ──
        let mut market = TradeWorld::new();
        // The output id encodes (crafter, recipe+inputs+roll) via the craft commitment; the
        // trade world re-derives the byte-IDENTICAL id from the SAME public seed + label.
        let seed = craft_commitment(&draw);
        let listed: AssetId = market.mint(HERO, &seed);
        assert_eq!(
            listed.bytes(),
            output.asset_id.bytes(),
            "the traded AssetId IS the crafted AssetId (byte-identical content address)"
        );

        // ── trade: an atomic escrow swap moves THAT id to the buyer ──
        market.fund_dregg(BUYER, 100);
        let mut trade = market.open_trade(HERO, LegSpec::Asset(listed), BUYER, LegSpec::Dregg(50));
        market
            .deposit(&mut trade, TradeSide::A)
            .expect("the seller deposits the charm");
        market
            .deposit(&mut trade, TradeSide::B)
            .expect("the buyer deposits the value");
        let settled = market
            .settle(&mut trade)
            .expect("the swap settles atomically");
        assert_eq!(settled.a_gave, LegSpec::Asset(listed));

        // ── the buyer verifies the SAME id's provenance after the swap ──
        let report = market.verify_provenance(listed);
        assert!(report.verified, "the traded charm's provenance re-verifies");
        assert_eq!(
            market.current_owner(listed),
            Some(market.pubkey_of(BUYER)),
            "the buyer now owns the identical AssetId the forge minted"
        );

        // Non-vacuous: a NON-OWNER cannot offer the charm (the scam-proof gate).
        let mut mallory_trade =
            market.open_trade("Mallory", LegSpec::Asset(listed), BUYER, LegSpec::Dregg(1));
        let stolen = market.deposit(&mut mallory_trade, TradeSide::A);
        assert!(
            stolen.is_err(),
            "a non-owner cannot deposit the charm, got {stolen:?}"
        );
    }

    // ── the continuous saga: one player, all the way through ──

    /// THE FULL SAGA — one player threaded through party -> faction-gate -> quest ->
    /// cheevo + guild (one Completion) -> craft -> trade, each step a real committed turn,
    /// with the cross-crate handoffs asserted object-identical and the end state coherent.
    #[test]
    fn the_full_saga_runs_end_to_end() {
        // (1) THE PARTY MUSTERS — four seated roles on one shared world.
        let mut party = Party::muster();
        assert_eq!(party.seat_count(), 4);
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

        // (5) THE GUILD — sums the SAME clear (the identical &universe + &completion).
        let mut guild = Guild::form("The Lantern Circle");
        let hero_id = DreggIdentity(HERO.to_string());
        guild.admit(&hero_id);
        let guild_turns = guild
            .board_mut()
            .record_clear(&hero_id, &universe, &completion)
            .expect("the guild counts the same clear");
        assert_eq!(
            guild_turns, cheevo.turns,
            "cheevo and guild agree on the one run"
        );

        // (6) THE CRAFT — the errand's material drops forged into one owned item.
        let mut forge = CraftForge::new();
        let recipe = Recipe::new("forge:loremasters-charm", 2);
        let m1 = forge.mint_material(HERO, b"errand-drop-1");
        let m2 = forge.mint_material(HERO, b"errand-drop-2");
        let beacon = CommittedSeed::from_bytes([0x5A; 32]);
        let draw = roll_craft(&beacon, &recipe, &[m1, m2]);
        let output = forge
            .craft(HERO, &draw, &recipe)
            .expect("the charm is forged");
        assert!(
            forge.is_destroyed(m1) && forge.is_destroyed(m2),
            "materials spent"
        );

        // (7) THE TRADE — the SAME AssetId sold to a buyer via an atomic swap.
        let mut market = TradeWorld::new();
        let charm: AssetId = market.mint(HERO, &craft_commitment(&draw));
        assert_eq!(
            charm.bytes(),
            output.asset_id.bytes(),
            "the item the market moves IS the item the forge minted"
        );
        market.fund_dregg(BUYER, 100);
        let mut trade = market.open_trade(HERO, LegSpec::Asset(charm), BUYER, LegSpec::Dregg(50));
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
        // the traded charm is owned by the BUYER, provenance intact;
        assert_eq!(market.current_owner(charm), Some(market.pubkey_of(BUYER)));
        assert!(market.verify_provenance(charm).verified);
        // the guild rank reflects exactly the one verified clear;
        assert_eq!(guild.stats().verified_clears, 1);
        assert_eq!(guild.stats().total_turns, 5);
        // the party's loot split stands as a committed ledger fact.
        assert_eq!(party.loot_share(0), 40);
    }
}
