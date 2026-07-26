//! ⚑ THE CANARY — the OFFERING layer's banked relics are real owned notes that replay to the run.
//!
//! `dungeon-on-dregg` closed the bank → asset wire ([`Descent::mint_banked_relics`]) and
//! `dreggnet-market` proved a banked note crosses a Dark Bazaar auction. The OFFERING layer —
//! the one every live surface (web, Telegram, WeChat, Discord, the campaign) actually plays
//! through — computed `NativeDescentCompletion::banked_relics` and minted NOTHING: the daily
//! descent produced an index list, not an asset.
//!
//! This battery drives the closed offering wire, through the generic `Offering` seam only:
//!
//! * the session deploys on the day's REAL verified drand beacon
//!   ([`NativeDescentOffering::on_beacon`], fail-closed on a forged reveal), so the run's
//!   provenance root is unpredictable-until-revealed and distinct per day;
//! * a settled run's BANKED custody relics mint into the session's own [`LootVault`], and the
//!   completion carries the real [`AssetId`]s;
//! * ⚑ each note's provenance REPLAYS to THAT RUN: re-deriving `banked_relic_drop(run
//!   day-seed, banked slot)` and claiming it for the same player re-mints the byte-identical
//!   id, and the exact-record verifier re-mints the whole completion on every `verify`;
//! * a run that banks NOTHING mints nothing;
//! * the minted note is owner-gate transferable and its live note world (`into_assets()`) is the
//!   same [`AssetWorld`](dreggnet_asset::AssetWorld) the market path adopts — the full Dark
//!   Bazaar crossing itself is proven by `dreggnet-market/tests/banked_relic_bazaar.rs`, so this
//!   battery stays free of the prover-heavy market stack.

use dreggnet_asset::AssetWorld;
use dreggnet_offerings::native_descent::{
    NativeDescentBankedNote, NativeDescentCompletion, NativeDescentOffering, NativeDescentRecord,
    NativeDescentSession, native_descent_run_day_seed,
};
use dreggnet_offerings::{
    DreggIdentity, Offering, Outcome, RecordVerify, SessionConfig, VerifyReport,
};
use dungeon_on_dregg::descent::{
    ASCEND, BANKED, DELVE, FLEE, LOOT, RELICS, SMITE, day_seed_from_deploy_seed,
};
use dungeon_on_dregg::loot::{LootError, LootVault, banked_relic_chest, banked_relic_drop};
use procgen_dregg::CommittedSeed;
use procgen_dregg::beacon::DailyBeacon;

/// A REAL, PUBLISHED drand `quicknet` round — the same vector the daily-descent driven test
/// pins as "today's beacon". The BLS pairing check against the pinned group key is what makes
/// the derived day-seed unpredictable-until-revealed.
const DRAND_QUICKNET_ROUND: u64 = 1_000_000;
const DRAND_QUICKNET_SIG_HEX: &str = "83ad29e4c409f9470fc2ef02f90214df49e02b441a1a241a82d622d9f608ef98fd8b11a029f1bee9d9e83b45088abe72";

/// The player: the actor every driven move is attributed to, and the vault identity the banked
/// notes are minted to.
const PLAYER: &str = "descent-player:alice";
/// The session seed. `Offering::open` normalizes it to `seed % 251 + 1`.
const SESSION_SEED: u64 = 0x5A;
const NORMALIZED_SEED: u8 = ((SESSION_SEED % 251) + 1) as u8;

/// **The one relic slot that is a WORLD-INVARIANT, not a day-fact.** Way `w`'s key is relic
/// `w - 1`, and the draw guarantees a key is minted above the door it opens
/// (`homes (keyFor w) < w`), so the way-2 key always lies on floor 1 — on every one of the sixteen
/// maps the committed day-seed can draw. It is the relic two different days can be compared over.
/// `floor_one_mints` re-checks the invariant on the map actually in play, so if the draw ever
/// stops guaranteeing it, this battery says so instead of quietly measuring nothing.
const WAY_TWO_KEY: u64 = 1;

fn todays_beacon() -> DailyBeacon {
    DailyBeacon::quicknet(
        DRAND_QUICKNET_ROUND,
        hex::decode(DRAND_QUICKNET_SIG_HEX).expect("the drand signature decodes"),
    )
}

fn actor(name: &str) -> DreggIdentity {
    DreggIdentity(name.to_string())
}

/// Land one native verb through the generic Offering seam (never `Descent` directly): the
/// affordance the adapter advertises, submitted for `who`, admitted by the real executor.
fn land(
    offering: &NativeDescentOffering,
    session: &mut dreggnet_offerings::native_descent::NativeDescentSession,
    who: &DreggIdentity,
    turn: &str,
    arg: i64,
) {
    let action = offering
        .actions(session)
        .into_iter()
        .find(|action| action.turn == turn && action.arg == arg)
        .unwrap_or_else(|| panic!("missing native affordance {turn}({arg})"));
    assert!(action.enabled, "the driven line expected {turn}({arg})");
    match offering.advance(session, action, who.clone()) {
        Outcome::Landed { .. } => {}
        Outcome::Refused(reason) => panic!("legal {turn}({arg}) was refused: {reason}"),
    }
}

/// **Every relic THIS RUN's drawn map mints on floor 1** — the ground truth the whole battery
/// measures the mint against, read off the session's own `DayWorld`.
///
/// This used to be the literal `[1, 4, 5]` ("the way-2 key and two treasures"), which was a fact
/// about the single hard-coded dungeon that existed before the map became a function of the
/// committed day-seed. These sessions open on a REAL drand beacon, so the day — and with it floor
/// 1's hoard and its guardian's vitality — is not knowable when the test is written. A literal
/// that encodes a world-fact outlives the world.
fn floor_one_mints(session: &NativeDescentSession) -> Vec<u64> {
    let homes = session.day_world().homes;
    let mints: Vec<u64> = (0..RELICS)
        .filter(|&relic| homes[relic] == 1)
        .map(|relic| relic as u64)
        .collect();
    assert!(
        !mints.is_empty(),
        "floor 1 mints nothing on this day ({homes:?}); every floor is supposed to stay live"
    );
    assert!(
        mints.contains(&WAY_TWO_KEY),
        "the way-2 key must lie on floor 1 on every drawn map ({homes:?}); the cross-day \
         comparison in this battery is built on that invariant"
    );
    mints
}

/// Drive a real run that banks FLOOR 1's whole hoard: delve, fell the guardian for however many
/// blows this day prices it at, loot every relic minted here, CLIMB BACK OUT (`flee` demands the
/// mouth — you do not teleport out with the loot), then flee: the terminal bank that ratchets
/// custody to BANKED and settles the run.
fn run_that_banks_floor_one(
    offering: &NativeDescentOffering,
    who: &DreggIdentity,
) -> NativeDescentSession {
    let mut session = offering
        .open(SessionConfig::with_seed(SESSION_SEED))
        .expect("the Lean-authored descent deploys");
    land(offering, &mut session, who, DELVE, 0);
    let hp = session.day_world().guard_hp(1);
    assert!(hp > 0, "floor 1 has no guardian to fell");
    for _ in 0..hp {
        land(offering, &mut session, who, SMITE, 0);
    }
    for relic in floor_one_mints(&session) {
        land(offering, &mut session, who, LOOT, relic as i64);
    }
    land(offering, &mut session, who, ASCEND, 0);
    land(offering, &mut session, who, FLEE, 0);
    session
}

/// ⚑ THE CANARY: a real offering-layer run that banks relics settles with REAL asset notes whose
/// provenance replays to THAT RUN's day-seed and banked slots.
#[test]
fn a_settled_native_descent_mints_banked_relics_whose_provenance_replays_to_the_run() {
    let beacon = todays_beacon();
    let day = beacon.seed().expect("the real drand round verifies");
    let offering = NativeDescentOffering::on_beacon(&beacon).expect("a verified beacon binds");
    let alice = actor(PLAYER);
    let session = run_that_banks_floor_one(&offering, &alice);

    // The run day-seed is the BEACON's, not the deploy seed's — the provenance root could not
    // be pre-computed before the round was revealed.
    let run_day_seed = *session.day_seed();
    assert_eq!(
        run_day_seed,
        native_descent_run_day_seed(&day, NORMALIZED_SEED),
        "the session deployed on the day-bound run seed"
    );
    assert_ne!(
        run_day_seed,
        day_seed_from_deploy_seed(NORMALIZED_SEED),
        "a beacon-bound day does not fall back to the deploy-seed-derived provenance root"
    );

    // The committed custody banked exactly this day's floor-1 hoard, and NOTHING else — the
    // ground truth the mint reads. (Both halves matter: a mint that banked the whole dungeon
    // would satisfy the positive half alone.)
    let banked = floor_one_mints(&session);
    for relic in 0..RELICS {
        let custody = session.game().read_relic(relic);
        if banked.contains(&(relic as u64)) {
            assert_eq!(
                custody, BANKED,
                "relic {relic} lay on floor 1 and was carried out — a committed BANKED custody \
                 entry on the cell"
            );
        } else {
            assert_ne!(
                custody, BANKED,
                "relic {relic} was never touched, so nothing may have banked it"
            );
        }
    }

    let completion = session
        .completion()
        .expect("the terminal flee settles the run");
    assert_eq!(completion.banked_relics, banked);
    assert!(!completion.crowned, "the crown stayed on floor 4");

    // ⚑ THE WIRE: the completion carries REAL notes, one per banked relic, in slot order.
    let minted: Vec<u64> = completion.banked_notes.iter().map(|n| n.relic).collect();
    assert_eq!(
        minted, completion.banked_relics,
        "every banked relic became an owned note, and only those"
    );
    assert_eq!(
        session.loot_vault().item_count(),
        banked.len(),
        "one note per banked relic in the session vault, no more"
    );

    let alice_pk = session
        .loot_vault()
        .owner_of(completion.banked_notes[0].asset_id)
        .expect("a minted note has an owner");
    for note in &completion.banked_notes {
        assert_eq!(note.owner, alice_pk, "the settling player owns every note");
        assert_eq!(
            session.loot_vault().owner_of(note.asset_id),
            Some(alice_pk),
            "the asset layer agrees the player is the owner"
        );

        // Provenance names THE BANKED RELIC: this run's day-seed + this custody slot.
        let prov = session
            .banked_note_provenance(note)
            .expect("the session vault recorded the drop");
        assert_eq!(
            prov.run_seed, run_day_seed,
            "provenance root = the banked run's day-seed"
        );
        assert_eq!(
            prov.chest,
            banked_relic_chest(note.relic as usize),
            "provenance names the banked custody slot, not a manufactured boss draw"
        );
        assert_eq!(prov.rarity, note.rarity, "the tier is the fair draw's");
        assert!(
            prov.asset.verified,
            "the asset-layer lineage re-verifies: {:?}",
            prov.asset.reasons
        );

        // ⚑ IT REPLAYS: re-deriving the banked relic's drop from (run day-seed, banked slot)
        // and minting it fresh for the same player yields the byte-identical AssetId.
        let mut replay = LootVault::new();
        let replayed = replay
            .claim(
                PLAYER,
                &banked_relic_drop(&run_day_seed, note.relic as usize),
            )
            .expect("the banked drop re-derives and mints");
        assert_eq!(
            replayed.asset_id, note.asset_id,
            "the settled note re-derives from the banked run — provenance REPLAYS"
        );
    }

    // A DIFFERENT day mints DIFFERENT notes for THE SAME BANKED RELIC: the provenance root rides
    // the day, so yesterday's record cannot claim today's relic.
    //
    // The comparison used to lean on "the same verb line banks the same relics" — true only while
    // both runs played one hard-coded dungeon. Two days draw two maps and two hoards, so the
    // shared quantity is named instead: the WAY-2 KEY, relic 1, which every drawn map mints on
    // floor 1 (the draw guarantees a key lies above the door it opens, `homes (keyFor w) < w`),
    // and which both runs therefore carry out.
    let other_day = CommittedSeed::from_bytes([0x5D; 32]);
    let other = NativeDescentOffering::on_day(other_day);
    let other_session = run_that_banks_floor_one(&other, &alice);
    let other_completion = other_session
        .completion()
        .expect("the other day settles too");
    let key_note = |completion: &NativeDescentCompletion| {
        completion
            .banked_notes
            .iter()
            .find(|note| note.relic == WAY_TWO_KEY)
            .copied()
            .expect("the way-2 key lies on floor 1 on every drawn map, so every run banks it")
    };
    assert_ne!(
        key_note(other_completion).asset_id,
        key_note(completion).asset_id,
        "the SAME banked relic on a different day is a different note"
    );
    let mine: Vec<_> = completion
        .banked_notes
        .iter()
        .map(|note| note.asset_id)
        .collect();
    assert!(
        other_completion
            .banked_notes
            .iter()
            .all(|note| !mine.contains(&note.asset_id)),
        "a different day's run shares NO note with this one"
    );
}

/// A run that banks NOTHING mints nothing — the mint is driven from the committed custody, not
/// from the fact that a run ended. Non-vacuous against the banking run above.
#[test]
fn a_run_that_banks_nothing_mints_nothing() {
    let offering = NativeDescentOffering::on_beacon(&todays_beacon()).expect("beacon binds");
    let alice = actor(PLAYER);
    let mut session = offering
        .open(SessionConfig::with_seed(SESSION_SEED))
        .expect("deploy");
    // Bank the empty pack on the surface: a real terminal flee with no carried relic.
    land(&offering, &mut session, &alice, FLEE, 0);

    let completion = session.completion().expect("the empty flee still settles");
    assert!(
        completion.banked_relics.is_empty(),
        "nothing was carried, so nothing banked"
    );
    assert!(
        completion.banked_notes.is_empty(),
        "a run that banked nothing minted nothing"
    );
    assert_eq!(
        session.loot_vault().item_count(),
        0,
        "the vault is empty — no ghost note"
    );
    assert!(
        offering.verify(&session).verified,
        "the empty settlement still replays exactly"
    );
    let rendered = format!("{:?}", offering.render(&session));
    assert!(
        rendered.contains("no relics banked"),
        "the surface says so plainly: {rendered}"
    );
}

/// The record's completion — notes included — is RE-MINTED by exact replay, and the record's
/// day-seed is hash-chain bound: re-pointing a record at another day's provenance is refused.
#[test]
fn the_record_re_mints_the_notes_and_a_swapped_day_seed_is_refused() {
    let beacon = todays_beacon();
    let offering = NativeDescentOffering::on_beacon(&beacon).expect("beacon binds");
    let alice = actor(PLAYER);
    let session = run_that_banks_floor_one(&offering, &alice);
    let authentic: NativeDescentRecord = offering.export_record(&session);

    let report: VerifyReport = offering.verify_record(&session, &authentic);
    assert!(
        report.verified,
        "the authentic record re-mints its own notes: {}",
        report.detail
    );

    // A fresh executor + a fresh vault reproduce the settlement exactly, notes and all.
    let resumed = offering
        .resume_record(&authentic)
        .expect("a fresh native executor reproduces the record exactly");
    assert_eq!(resumed.completion(), session.completion());
    assert_eq!(resumed.day_seed(), session.day_seed());
    assert_eq!(
        resumed.loot_vault().item_count(),
        floor_one_mints(&session).len(),
        "the resumed session re-minted the banked relics into its own vault"
    );
    for note in &session.completion().expect("settled").banked_notes {
        assert_eq!(
            resumed
                .banked_note_provenance(note)
                .expect("the resumed vault knows the note")
                .run_seed,
            *session.day_seed(),
            "the re-minted note carries the same banked run's provenance"
        );
    }

    // A record re-pointed at ANOTHER day's provenance no longer recomputes its hash chain.
    let mut swapped = authentic.clone();
    swapped.day_seed = CommittedSeed::from_bytes([0xEE; 32]);
    assert!(
        !offering.verify_record(&session, &swapped).verified,
        "a swapped day-seed must not verify against the live head"
    );
    assert!(
        offering.resume_record(&swapped).is_err(),
        "a swapped day-seed breaks the journal root it was folded into"
    );
}

/// The minted note is a real owned, TRADEABLE asset: the owner-gate refuses a non-owner, the
/// owner's transfer moves it, and the session's LIVE note world (`into_assets()`) is the exact
/// same [`AssetWorld`] the market path adopts — the transferred note's ownership and lineage
/// carry into it un-re-minted. (The full Dark Bazaar auction crossing is proven separately by
/// `dreggnet-market/tests/banked_relic_bazaar.rs`; this keeps the offering battery off the
/// prover-heavy market stack.)
#[test]
fn the_banked_note_is_owner_gated_and_its_world_is_the_market_asset_world() {
    const BUYER: &str = "bazaar-bidder:carol";

    let offering = NativeDescentOffering::on_beacon(&todays_beacon()).expect("beacon binds");
    let alice = actor(PLAYER);
    let session = run_that_banks_floor_one(&offering, &alice);
    assert!(floor_one_mints(&session).contains(&WAY_TWO_KEY));
    let note: NativeDescentBankedNote = session
        .completion()
        .expect("settled")
        .banked_notes
        .iter()
        .find(|note| note.relic == WAY_TWO_KEY)
        .copied()
        .expect("the banked way-2 key minted");

    // Take the session's LIVE vault (no re-mint from display metadata).
    let mut vault = session.into_loot_vault();

    // A NON-OWNER cannot move it — a real cryptographic refusal, anti-ghost.
    let forged = vault.transfer(note.asset_id, "mallory", "eve");
    assert!(
        matches!(forged, Err(LootError::Asset(_))),
        "a non-owner transfer is refused by the owner-gate, got {forged:?}"
    );
    assert_eq!(vault.owner_of(note.asset_id), Some(note.owner));

    // The OWNER's transfer commits — the banked relic changes hands under the asset layer's gate.
    vault
        .transfer(note.asset_id, PLAYER, BUYER)
        .expect("the owner's transfer commits");

    // ⚑ The vault's live note world IS the market's AssetWorld: hand it off un-re-minted and the
    // transferred ownership + lineage carry, exactly as `dreggnet_trade::TradeWorld::with_assets`
    // (the Bazaar's adopter) consumes it.
    let world: AssetWorld = vault.into_assets();
    let buyer_pk = {
        // The buyer's key is stable in this same world; the note's current owner is now theirs.
        let mut w = world;
        let buyer_pk = w.pubkey_of(BUYER);
        assert_eq!(
            w.current_owner(note.asset_id),
            Some(buyer_pk),
            "the banked relic is now the buyer's in the adopted market AssetWorld"
        );
        let prov = w.verify_provenance(note.asset_id);
        assert!(
            prov.verified,
            "post-trade lineage verifies: {:?}",
            prov.reasons
        );
        assert_eq!(prov.length, 2, "mint (the bank) + one transfer");
        buyer_pk
    };
    assert_ne!(
        buyer_pk, note.owner,
        "ownership actually moved off the player"
    );
}

/// A forged beacon opens NO day — the day binding is fail-closed, so a run's provenance root
/// cannot be grafted from a reveal nobody published.
#[test]
fn a_forged_beacon_cannot_bind_a_day() {
    let mut sig = hex::decode(DRAND_QUICKNET_SIG_HEX).expect("decodes");
    sig[0] ^= 0x01;
    let forged = DailyBeacon::quicknet(DRAND_QUICKNET_ROUND, sig);
    assert!(
        NativeDescentOffering::on_beacon(&forged).is_err(),
        "a forged beacon must not bind a day (fail-closed)"
    );
    assert!(NativeDescentOffering::on_beacon(&todays_beacon()).is_ok());
}
