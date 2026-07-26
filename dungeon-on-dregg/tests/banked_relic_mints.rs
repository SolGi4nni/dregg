//! # The BANKED relic IS the traded note — the bank → asset wire, DRIVEN with a canary.
//!
//! Before this wire the Descent's banked custody relic (a real committed executor object) and
//! the asset-minting loot were TWO DISJOINT SYSTEMS: the E2E manufactured its tradeable note with
//! `roll_drop("boss:…")` — a fresh draw — and the relic you actually banked was discarded. This
//! battery drives the closed wire: a real Descent banks specific relics, and
//! [`Descent::mint_banked_relics`] mints EACH banked relic into a real owned
//! [`dreggnet_asset`] note whose [`AssetId`](dreggnet_asset::AssetId) provenance encodes THE
//! BANKED RELIC (the run's committed day-seed + the custody slot) and REPLAYS to the banked run.
//!
//! THE CANARY (`the_banked_relic_is_the_traded_note`): the manufactured-before AssetId (a
//! `roll_drop("boss:…")` draw) and the banked-after AssetId (the banked relic's lineage) are
//! shown side by side — they differ, and the traded note carries the banked relic's chest/seed,
//! not the boss draw's.

use dungeon_on_dregg::descent::{BANKED, BankedRelicMint, Descent, RELICS};
use dungeon_on_dregg::loot::{
    LootVault, banked_relic_chest, banked_relic_drop, reverify_drop, roll_drop,
};
use procgen_dregg::CommittedSeed;

/// Drive a real Descent that banks every relic THIS seed's map mints on floor 1. Returns the
/// banked run and the slots it banked.
///
/// The verb line is all real cap-bounded turns on the Lean-sourced executor: delve to floor 1,
/// fell the guardian, loot each floor-1 relic into the pack, climb back to the mouth, then flee —
/// the terminal bank that ratchets each carried relic's custody to `BANKED` (a real committed
/// cell write).
///
/// ⚑ Every quantity here is read off the day's own `DayWorld`. The line used to be a literal
/// `smite(); loot(1); loot(4); loot(5); flee()`, which was true of the single hard-coded dungeon
/// that predated the day-seeded draw: it assumed a floor-1 guardian of exactly 1 hp and relics
/// 1/4/5 minted on floor 1. It also predated the climb — `flee` now demands `depth == 0`
/// (`Dungeon.toll`), so banking from below is refused outright, which is what all three tests in
/// this file were dying on.
fn run_that_banks_floor_one(seed: u8) -> (Descent, Vec<usize>) {
    let mut d = Descent::deploy(seed).expect("deploy + genesis");
    let world = d.day_world();
    let floor_one: Vec<usize> = (0..RELICS).filter(|&r| world.homes[r] == 1).collect();
    assert!(
        !floor_one.is_empty(),
        "every day mints the way-2 key on floor 1"
    );
    d.delve().expect("way 1 is always open");
    for _ in 0..world.guard_hp(1) {
        d.smite().expect("fell the floor-1 guardian");
    }
    for &relic in &floor_one {
        d.loot(relic).expect("carry a floor-1 relic");
    }
    d.ascend()
        .expect("climb back to the mouth — flee is illegal below");
    d.flee().expect("bank the pack — the run ends");
    (d, floor_one)
}

/// The slots this run banks (custody == BANKED), read off the COMMITTED cell — the ground truth
/// the mint is driven from.
fn banked_slots_on_cell(d: &Descent) -> Vec<usize> {
    (0..RELICS).filter(|&i| d.read_relic(i) == BANKED).collect()
}

/// The wire is driven from the COMMITTED banked custody: exactly the relics the run banked
/// (read back off the cell) are minted, in slot order, once each. A run that banks nothing
/// mints nothing.
#[test]
fn mint_is_driven_from_committed_banked_custody() {
    let (d, floor_one) = run_that_banks_floor_one(0x11);
    assert_eq!(
        banked_slots_on_cell(&d),
        floor_one,
        "the committed cell banked exactly the relics the line looted"
    );

    let mut vault = LootVault::new();
    let minted = d
        .mint_banked_relics(&mut vault, "alice")
        .expect("every banked relic is a fair (day_seed, slot) drop");
    let minted_slots: Vec<usize> = minted.iter().map(|m| m.slot).collect();
    assert_eq!(
        minted_slots,
        banked_slots_on_cell(&d),
        "the mint covers exactly the committed banked relics, in slot order"
    );
    assert_eq!(
        vault.item_count(),
        floor_one.len(),
        "one note per banked relic, no more"
    );

    // A run that banked NOTHING (bank the empty pack) mints nothing — the mint reads custody.
    let mut empty = Descent::deploy(0x22).expect("deploy");
    empty.flee().expect("bank the empty pack");
    assert!(banked_slots_on_cell(&empty).is_empty());
    let mut empty_vault = LootVault::new();
    assert!(
        empty
            .mint_banked_relics(&mut empty_vault, "alice")
            .expect("no banked relics is not an error")
            .is_empty(),
        "a run that banked nothing mints nothing"
    );
    assert_eq!(empty_vault.item_count(), 0);
}

/// ⚑ THE CANARY — the banked relic IS the traded note, with the manufactured-before /
/// banked-after provenance shown side by side.
///
/// * BEFORE (manufactured): the pre-wire E2E minted `roll_drop("boss:the Tide-Warden")` — a fresh
///   draw, its provenance a hand-typed boss on a hand-typed seed, the banked relic DISCARDED.
/// * AFTER (banked): the traded note is minted FROM the banked relic; its provenance is the
///   banked relic's lineage (the run's committed day-seed + the custody slot) and REPLAYS to the
///   banked run.
#[test]
fn the_banked_relic_is_the_traded_note() {
    let (d, floor_one) = run_that_banks_floor_one(0x33);
    let day_seed = *d.day_seed();
    // The way-2 key we banked; the note we take to market. The draw guarantees `homes(keyFor 2)`
    // is floor 1, so relic 1 is banked on every day — asserted, not assumed.
    let banked_slot = 1usize;
    assert!(
        floor_one.contains(&banked_slot),
        "the way-2 key lies on floor 1"
    );

    // ── AFTER: mint the banked relics; the traded note is the banked relic's ──
    let mut vault = LootVault::new();
    let alice_pk = vault.pubkey_of("alice");
    let minted = d
        .mint_banked_relics(&mut vault, "alice")
        .expect("banked relics mint");
    let BankedRelicMint { slot, item } = minted
        .iter()
        .find(|m| m.slot == banked_slot)
        .expect("the banked way-key was minted")
        .clone();
    assert_eq!(slot, banked_slot);
    assert_eq!(
        vault.owner_of(item.asset_id),
        Some(alice_pk),
        "alice owns it"
    );

    // The traded note's provenance encodes THE BANKED RELIC: the run's committed day-seed and the
    // custody slot — not a manufactured boss draw.
    let prov = vault
        .provenance(item.asset_id)
        .expect("provenance recorded");
    assert_eq!(
        prov.run_seed, day_seed,
        "provenance root = the run's day-seed"
    );
    assert_eq!(
        prov.chest,
        banked_relic_chest(banked_slot),
        "provenance names the banked custody slot, not a boss/chest string"
    );
    assert!(
        prov.asset.verified,
        "the asset lineage re-verifies: {:?}",
        prov.asset.reasons
    );

    // REPLAYS TO THE BANKED RUN: the AssetId is a pure function of (day_seed, banked slot, owner).
    // Re-deriving the drop from the banked run's seed + the banked slot and claiming it for the same
    // player into a FRESH vault yields the byte-identical AssetId — a replay of the banked run
    // re-derives this exact tradeable note (the owner is the player who banked the relic).
    let replay_drop = banked_relic_drop(&day_seed, banked_slot);
    reverify_drop(&replay_drop).expect("the banked relic's drop is a real fair draw");
    let mut replay_vault = LootVault::new();
    let replay_item = replay_vault
        .claim("alice", &replay_drop)
        .expect("the re-derived banked drop mints");
    assert_eq!(
        replay_item.asset_id.bytes(),
        item.asset_id.bytes(),
        "the banked relic's AssetId re-derives from (run day-seed, banked slot) — it REPLAYS"
    );

    // Even stronger: re-run the WHOLE descent (same seed + verbs) and re-mint — the banked custody
    // and thus the minted note are identical. The tradeable note is a function of the banked run.
    let (d2, _) = run_that_banks_floor_one(0x33);
    let mut vault2 = LootVault::new();
    let remint = d2
        .mint_banked_relics(&mut vault2, "alice")
        .expect("re-run mints");
    let remint_id = remint
        .iter()
        .find(|m| m.slot == banked_slot)
        .unwrap()
        .item
        .asset_id;
    assert_eq!(
        remint_id.bytes(),
        item.asset_id.bytes(),
        "replaying the banked run re-mints the identical note"
    );

    // ── BEFORE: the manufactured draw the pre-wire E2E traded — the banked relic discarded ──
    // (i) the E2E's exact draw: a hand-typed boss on a hand-typed seed, wholly disconnected.
    let e2e_seed = CommittedSeed::from_bytes([0xD3; 32]);
    let mut e2e_vault = LootVault::new();
    let e2e_item = e2e_vault
        .claim("alice", &roll_drop(&e2e_seed, "boss:the Tide-Warden", 0))
        .expect("the manufactured E2E draw mints");
    assert_ne!(
        e2e_item.asset_id.bytes(),
        item.asset_id.bytes(),
        "the manufactured boss draw is NOT the banked relic's note"
    );
    // (ii) even on the SAME banked-run day-seed, a boss draw ≠ the banked relic's drop: the chest
    //      (a boss string vs the banked custody slot) is what the AssetId content-addresses.
    let manufactured_same_seed = roll_drop(&day_seed, "boss:the Tide-Warden", 0);
    let mut same_seed_vault = LootVault::new();
    let manufactured_item = same_seed_vault
        .claim("alice", &manufactured_same_seed)
        .expect("a boss draw on the run's seed still mints");
    assert_ne!(
        manufactured_item.asset_id.bytes(),
        item.asset_id.bytes(),
        "a boss draw discards the banked relic; the banked-relic drop encodes the custody slot"
    );
    assert_ne!(
        manufactured_same_seed.chest,
        banked_relic_chest(banked_slot),
        "the manufactured chest is a boss string, not the banked custody slot"
    );
}

/// TRADE IT — the buyer holds an AssetId whose provenance REPLAYS to the banked run.
///
/// The banked relic's note is transferred under the asset layer's cryptographic owner-gate (a real
/// trade). After the cross the BUYER holds it, and its provenance still names the banked run: the
/// run's committed day-seed + the banked custody slot, lineage re-verifying post-trade.
#[test]
fn the_traded_banked_note_lands_on_the_buyer_and_provenance_still_replays() {
    let (d, floor_one) = run_that_banks_floor_one(0x44);
    let day_seed = *d.day_seed();
    // A banked floor-1 relic OTHER than the way-2 key — which slot that is depends on the day's
    // map, so take it from the run rather than naming a number that is only right on day 0.
    let banked_slot = *floor_one
        .iter()
        .find(|&&r| r != 1)
        .expect("floor 1 mints more than the way-2 key on this day");

    let mut vault = LootVault::new();
    let alice_pk = vault.pubkey_of("alice");
    let bob_pk = vault.pubkey_of("bob");
    let minted = d
        .mint_banked_relics(&mut vault, "alice")
        .expect("banked relics mint");
    let note = minted
        .iter()
        .find(|m| m.slot == banked_slot)
        .expect("the banked treasure minted")
        .item
        .clone();
    assert_eq!(vault.owner_of(note.asset_id), Some(alice_pk));

    // A NON-OWNER cannot take it — a real cryptographic refusal (anti-ghost: still alice's).
    assert!(
        vault.transfer(note.asset_id, "mallory", "eve").is_err(),
        "a non-owner cannot trade the banked note"
    );
    assert_eq!(vault.owner_of(note.asset_id), Some(alice_pk));

    // The OWNER trades it: it crosses to bob (the buyer).
    vault
        .transfer(note.asset_id, "alice", "bob")
        .expect("the owner's trade crosses the banked note");
    assert_eq!(
        vault.owner_of(note.asset_id),
        Some(bob_pk),
        "the buyer now holds the banked relic's note"
    );

    // The buyer holds an AssetId whose provenance REPLAYS to the banked run.
    let prov = vault
        .provenance(note.asset_id)
        .expect("provenance recorded");
    assert_eq!(
        prov.run_seed, day_seed,
        "provenance root is still the run's day-seed"
    );
    assert_eq!(
        prov.chest,
        banked_relic_chest(banked_slot),
        "still the banked custody slot"
    );
    assert!(
        prov.asset.verified && prov.asset.length == 2,
        "post-trade lineage (mint + one transfer) re-verifies: {:?}",
        prov.asset.reasons
    );
    // The held id re-derives from the banked run — a buyer can replay provenance to the run: the
    // banked drop, claimed fresh, content-addresses to the SAME AssetId the buyer holds.
    let mut fresh = LootVault::new();
    let rederived = fresh
        .claim("alice", &banked_relic_drop(&day_seed, banked_slot))
        .expect("the banked drop re-derives + mints");
    assert_eq!(
        rederived.asset_id.bytes(),
        note.asset_id.bytes(),
        "the buyer's note re-derives from (banked run day-seed, banked slot)"
    );
}
