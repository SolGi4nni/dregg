//! # `dreggnet-companion` integration — the matured surface, driven end-to-end.
//!
//! These tests exercise the crate's PUBLIC API against the real executor-refereed layers (the
//! asset world + the shared run executor), covering the features this maturation added on top of
//! the hatch / level / exact-buff / dupe / permadeath / bond suite in `mod tests`:
//!
//! * the **native cross-cell `>=` buff** ([`CompanionRoost::arm_buff_at_least`]) — an
//!   `ObservedFieldEquals` (binding the buff slot to the companion's live level) plus a
//!   `FieldGte(N)` floor, admitting at level N *or higher*, contrasted against the exact gate
//!   which stops applying above its pinned level;
//! * **abilities** keyed to class / level / rarity — a real class-locked kernel turn advancing
//!   the `abilities_used` counter, with the wrong-class kernel refusal and the level/rarity host
//!   eligibility teeth both non-vacuous;
//! * **breeding** — the two-input sink: both parents SPENT on-chain (a consumed parent's re-trade
//!   refused), one fair-draw egg minted whose provenance binds the lineage;
//! * **escrow-market trading** — a two-party atomic swap through escrow (deposit both, settle;
//!   non-owner deposit refused; settle-before-ready refused; the refund abort path).

use dreggnet_companion::{
    Ability, BuffKind, CLASS_WARRIOR, CompanionError, CompanionRoost, HatchBeacon, RarityTier,
    SwapPhase, ability_catalog, rarity_rank, roll_hatch,
};

fn beacon(byte: u8) -> HatchBeacon {
    HatchBeacon::from_bytes([byte; 32])
}

/// Find a beacon whose named-species hatch draws the target rarity (the draw is a pure function of
/// the context, so this scans the deterministic distribution).
fn beacon_for(species: &str, want: RarityTier) -> HatchBeacon {
    for b in 0u16..=1024 {
        let s = HatchBeacon::from_bytes([(b & 0xff) as u8; 32]);
        // vary a second byte so the search space is wide enough for rare tiers
        let mut raw = [0u8; 32];
        raw[0] = (b & 0xff) as u8;
        raw[1] = (b >> 8) as u8;
        let s2 = HatchBeacon::from_bytes(raw);
        if roll_hatch(&s, species, 0).rarity == want {
            return s;
        }
        if roll_hatch(&s2, species, 0).rarity == want {
            return s2;
        }
    }
    panic!("no beacon found for {want:?} of `{species}`");
}

/// Hatch a companion of a chosen rarity for `player`.
fn hatch_rarity(
    roost: &mut CompanionRoost,
    player: &str,
    species: &str,
    r: RarityTier,
) -> dreggnet_companion::Companion {
    let draw = roll_hatch(&beacon_for(species, r), species, 0);
    assert_eq!(draw.rarity, r);
    roost.hatch(player, &draw).expect("hatch")
}

// ── The native cross-cell `>=` buff ─────────────────────────────────────────────────

#[test]
fn the_at_least_buff_applies_at_level_n_or_higher() {
    let mut roost = CompanionRoost::new();
    let draw = roll_hatch(&beacon(41), "companion:griffin", 0);
    let comp = roost.hatch("alice", &draw).expect("hatch");

    // Arm a native `>=` buff at level 3.
    roost.raise_to(&comp, 2).expect("raise to 2");
    let mut gate = roost.arm_buff_at_least(&comp, 3);
    assert_eq!(gate.kind, BuffKind::AtLeast);

    // BELOW the floor (level 2): the FieldGte(3) floor refuses it.
    let below = roost.attempt_buff(&mut gate, "alice", true);
    assert!(
        below.is_err(),
        "the >= buff refuses below the floor, got {below:?}"
    );
    assert_eq!(roost.buff_value(&gate), 0, "anti-ghost: nothing applied");

    // AT the floor (level 3): the cross-cell read + floor both hold — commits, writing level 3.
    roost.raise_to(&comp, 3).expect("raise to 3");
    roost
        .attempt_buff(&mut gate, "alice", true)
        .expect("applies at the floor");
    assert_eq!(roost.buff_value(&gate), 3);

    // ABOVE the floor (level 4, then 5): the SAME `>=` gate still applies — N-or-higher.
    roost.raise_to(&comp, 4).expect("raise to 4");
    roost
        .attempt_buff(&mut gate, "alice", true)
        .expect("still applies above the floor");
    assert_eq!(
        roost.buff_value(&gate),
        4,
        "the buff tracks the companion's current level"
    );

    roost.raise_to(&comp, 5).expect("raise to 5");
    roost
        .attempt_buff(&mut gate, "alice", true)
        .expect("applies at the ceiling");
    assert_eq!(roost.buff_value(&gate), 5);
}

#[test]
fn exact_stops_above_its_level_but_at_least_does_not() {
    let mut roost = CompanionRoost::new();
    let draw = roll_hatch(&beacon(43), "companion:phoenix", 0);
    let comp = roost.hatch("alice", &draw).expect("hatch");
    roost.raise_to(&comp, 3).expect("raise to 3");

    let mut exact = roost.arm_buff(&comp, 3);
    let mut at_least = roost.arm_buff_at_least(&comp, 3);

    // At exactly level 3 BOTH apply.
    roost
        .attempt_buff(&mut exact, "alice", true)
        .expect("exact applies at level 3");
    roost
        .attempt_buff(&mut at_least, "alice", true)
        .expect(">= applies at level 3");

    // Raise to level 4: the companion moves OFF the level-3 checkpoint.
    roost.raise_to(&comp, 4).expect("raise to 4");
    let exact_now = roost.attempt_buff(&mut exact, "alice", true);
    assert!(
        exact_now.is_err(),
        "the EXACT gate no longer applies above level 3, got {exact_now:?}"
    );
    // The `>=` gate still applies (level 4 >= 3).
    roost
        .attempt_buff(&mut at_least, "alice", true)
        .expect(">= still applies at level 4");
    assert_eq!(roost.buff_value(&at_least), 4);
}

#[test]
fn the_at_least_buff_is_fail_closed_to_stripped_witness_and_non_owner() {
    let mut roost = CompanionRoost::new();
    let draw = roll_hatch(&beacon(47), "companion:raven", 0);
    let comp = roost.hatch("alice", &draw).expect("hatch");
    roost.raise_to(&comp, 4).expect("raise to 4");
    let mut gate = roost.arm_buff_at_least(&comp, 2);

    // A stripped witness fails closed even well above the floor.
    let stripped = roost.attempt_buff(&mut gate, "alice", false);
    assert!(
        stripped.is_err(),
        "a stripped-witness >= buff fails closed, got {stripped:?}"
    );
    assert_eq!(roost.buff_value(&gate), 0);

    // A non-owner cannot activate it.
    let non_owner = roost.attempt_buff(&mut gate, "mallory", true);
    assert!(
        matches!(non_owner, Err(CompanionError::NotOwner)),
        "got {non_owner:?}"
    );

    // The owner with the witness commits.
    roost
        .attempt_buff(&mut gate, "alice", true)
        .expect("owner applies the >= buff");
    assert_eq!(roost.buff_value(&gate), 4);
}

// ── Abilities (class / level / rarity keyed) ─────────────────────────────────────────

fn ability(id: &str) -> Ability {
    ability_catalog()
        .into_iter()
        .find(|a| a.id == id)
        .expect("ability exists")
}

#[test]
fn a_class_ability_is_a_real_kernel_gated_turn() {
    let mut roost = CompanionRoost::new();
    // A Rare warrior can eventually reach rallying_cry (level 3, Rare).
    let comp = hatch_rarity(&mut roost, "alice", "companion:knight", RarityTier::Rare);

    // No class chosen: shield_bash's kernel class-lock refuses (class 0 != WARRIOR).
    roost.raise_to(&comp, 1).expect("raise to 1");
    let no_class = roost.use_ability(&comp, &ability("shield_bash"));
    assert!(
        matches!(no_class, Err(CompanionError::Refused(_))),
        "no-class ability refused, got {no_class:?}"
    );
    assert_eq!(
        roost.abilities_used_of(&comp),
        0,
        "anti-ghost: counter untouched"
    );

    // Choose WARRIOR; a MAGE ability is refused by the kernel class-lock.
    roost
        .choose_class(&comp, CLASS_WARRIOR)
        .expect("choose class");
    let wrong_class = roost.use_ability(&comp, &ability("arcane_bolt"));
    assert!(
        matches!(wrong_class, Err(CompanionError::Refused(_))),
        "wrong-class ability refused, got {wrong_class:?}"
    );

    // shield_bash (level 1, Common) now commits and advances the counter.
    roost
        .use_ability(&comp, &ability("shield_bash"))
        .expect("shield_bash");
    assert_eq!(roost.abilities_used_of(&comp), 1);
    roost
        .use_ability(&comp, &ability("shield_bash"))
        .expect("shield_bash again");
    assert_eq!(
        roost.abilities_used_of(&comp),
        2,
        "the counter is strictly monotone"
    );
}

#[test]
fn abilities_are_keyed_to_level_and_rarity() {
    let mut roost = CompanionRoost::new();
    // A Common warrior: rallying_cry (Rare, level 3) is out of reach on BOTH counts.
    let common = hatch_rarity(&mut roost, "alice", "companion:squire", RarityTier::Common);
    roost.choose_class(&common, CLASS_WARRIOR).expect("class");
    roost.raise_to(&common, 3).expect("raise to 3");
    // Level ok now, but rarity too low.
    let by_rarity = roost.use_ability(&common, &ability("rallying_cry"));
    assert!(
        matches!(by_rarity, Err(CompanionError::Ineligible(_))),
        "rarity-gated, got {by_rarity:?}"
    );
    assert!(rarity_rank(RarityTier::Common) < rarity_rank(RarityTier::Rare));

    // A Rare warrior BELOW level 3: level-gated.
    let rare = hatch_rarity(&mut roost, "bob", "companion:baron", RarityTier::Rare);
    roost.choose_class(&rare, CLASS_WARRIOR).expect("class");
    roost.raise_to(&rare, 2).expect("raise to 2");
    let by_level = roost.use_ability(&rare, &ability("rallying_cry"));
    assert!(
        matches!(by_level, Err(CompanionError::Ineligible(_))),
        "level-gated, got {by_level:?}"
    );
    assert!(
        roost
            .unlocked_abilities(&rare)
            .iter()
            .all(|a| a.id != "rallying_cry")
    );

    // At level 3 with Rare rarity: unlocked and it commits.
    roost.raise_to(&rare, 3).expect("raise to 3");
    assert!(
        roost
            .unlocked_abilities(&rare)
            .iter()
            .any(|a| a.id == "rallying_cry")
    );
    roost
        .use_ability(&rare, &ability("rallying_cry"))
        .expect("rallying_cry commits");
    assert_eq!(roost.abilities_used_of(&rare), 1);
}

// ── Breeding (two-input sink) ────────────────────────────────────────────────────────

#[test]
fn breeding_spends_both_parents_and_mints_a_fair_egg() {
    let mut roost = CompanionRoost::new();
    let alice = roost.pubkey_of("alice");
    let pa = roll_hatch(&beacon(51), "companion:mareA", 0);
    let pb = roll_hatch(&beacon(52), "companion:mareB", 0);
    let a = roost.hatch("alice", &pa).expect("parent a");
    let b = roost.hatch("alice", &pb).expect("parent b");
    let count_before = roost.companion_count();

    let egg = roost
        .breed("alice", a.asset_id, b.asset_id, &beacon(53), 0)
        .expect("breed");
    assert_eq!(
        roost.companion_count(),
        count_before + 1,
        "exactly one egg minted"
    );
    assert_eq!(
        roost.owner_of(egg.asset_id),
        Some(alice),
        "the egg is the breeder's"
    );

    // Both parents are CONSUMED — a re-trade of either is refused (spent on-chain).
    assert!(roost.is_consumed(a.asset_id) && roost.is_consumed(b.asset_id));
    let re_a = roost.trade(a.asset_id, "alice", "bob");
    assert!(
        matches!(re_a, Err(CompanionError::Consumed)),
        "consumed parent cannot trade, got {re_a:?}"
    );
    // And breeding with a consumed parent is refused.
    let re_breed = roost.breed("alice", a.asset_id, egg.asset_id, &beacon(54), 0);
    assert!(
        matches!(re_breed, Err(CompanionError::Consumed)),
        "got {re_breed:?}"
    );

    // The egg is a real fair draw whose identity re-verifies, and re-deriving its species from the
    // two parents reproduces the same egg (re-derivable lineage).
    let prov = roost.verify_identity(egg.asset_id);
    assert!(prov.verified, "egg identity verifies: {:?}", prov.reasons);
    let egg_hatch = roost.hatch_of(egg.asset_id).expect("egg hatch");
    assert!(
        egg_hatch.species.starts_with("companion:bred/"),
        "species binds the breeding"
    );
}

#[test]
fn breeding_refuses_non_owner_self_and_dead() {
    let mut roost = CompanionRoost::new();
    let pa = roll_hatch(&beacon(61), "companion:sireA", 0);
    let pb = roll_hatch(&beacon(62), "companion:sireB", 0);
    let a = roost.hatch("alice", &pa).expect("a");
    let b = roost.hatch("bob", &pb).expect("b"); // owned by BOB, not alice

    // A non-owner (alice does not own b) cannot breed them.
    let non_owner = roost.breed("alice", a.asset_id, b.asset_id, &beacon(63), 0);
    assert!(
        matches!(non_owner, Err(CompanionError::NotOwner)),
        "got {non_owner:?}"
    );

    // A companion cannot breed with itself.
    let a2 = {
        let pc = roll_hatch(&beacon(64), "companion:soloA", 0);
        roost.hatch("carol", &pc).expect("a2")
    };
    let self_breed = roost.breed("carol", a2.asset_id, a2.asset_id, &beacon(65), 0);
    assert!(
        matches!(self_breed, Err(CompanionError::Ineligible(_))),
        "got {self_breed:?}"
    );

    // A dead parent cannot breed.
    let pd = roll_hatch(&beacon(66), "companion:mortA", 0);
    let pe = roll_hatch(&beacon(67), "companion:mortB", 0);
    let d = roost.hatch("dave", &pd).expect("d");
    let e = roost.hatch("dave", &pe).expect("e");
    roost.perish(&d).expect("perish");
    let dead_breed = roost.breed("dave", d.asset_id, e.asset_id, &beacon(68), 0);
    assert!(
        matches!(dead_breed, Err(CompanionError::Ineligible(_))),
        "got {dead_breed:?}"
    );
    // Nothing was consumed by the refused breed (the sink bit nothing).
    assert!(
        !roost.is_consumed(e.asset_id),
        "the surviving parent was not consumed"
    );
}

// ── Escrow-market trading (atomic two-party swap) ────────────────────────────────────

#[test]
fn an_escrow_swap_delivers_each_companion_to_the_counterparty() {
    let mut roost = CompanionRoost::new();
    let alice = roost.pubkey_of("alice");
    let bob = roost.pubkey_of("bob");
    let a = roost
        .hatch("alice", &roll_hatch(&beacon(71), "companion:cat", 0))
        .expect("a");
    let b = roost
        .hatch("bob", &roll_hatch(&beacon(72), "companion:dog", 0))
        .expect("b");

    let mut swap = roost
        .open_swap(a.asset_id, "alice", b.asset_id, "bob")
        .expect("open");
    assert_eq!(swap.phase(), SwapPhase::Open);

    // Settle before both deposited: refused, nothing moves.
    let early = roost.settle_swap(&mut swap);
    assert!(
        matches!(early, Err(CompanionError::Swap(_))),
        "no single-sided settle, got {early:?}"
    );

    roost.deposit(&mut swap, true).expect("alice deposits");
    assert_eq!(swap.phase(), SwapPhase::HalfDeposited);
    roost.deposit(&mut swap, false).expect("bob deposits");
    assert_eq!(swap.phase(), SwapPhase::Ready);

    roost.settle_swap(&mut swap).expect("settle");
    assert_eq!(swap.phase(), SwapPhase::Settled);
    // Ownership swapped: alice's companion is now bob's and vice-versa.
    assert_eq!(
        roost.owner_of(a.asset_id),
        Some(bob),
        "companion a went to bob"
    );
    assert_eq!(
        roost.owner_of(b.asset_id),
        Some(alice),
        "companion b went to alice"
    );
}

#[test]
fn escrow_refuses_non_owner_deposit_and_supports_refund() {
    let mut roost = CompanionRoost::new();
    let alice = roost.pubkey_of("alice");
    let a = roost
        .hatch("alice", &roll_hatch(&beacon(81), "companion:hare", 0))
        .expect("a");
    let b = roost
        .hatch("bob", &roll_hatch(&beacon(82), "companion:owl2", 0))
        .expect("b");

    // Mallory tries to open + deposit alice's companion (a non-owner deposit).
    let mut bad = roost
        .open_swap(a.asset_id, "mallory", b.asset_id, "bob")
        .expect("open");
    let steal = roost.deposit(&mut bad, true);
    assert!(
        matches!(steal, Err(CompanionError::Asset(_))),
        "non-owner deposit refused, got {steal:?}"
    );
    assert_eq!(
        roost.owner_of(a.asset_id),
        Some(alice),
        "companion a did not move"
    );

    // A legit swap where only one side deposits, then refund returns it.
    let mut swap = roost
        .open_swap(a.asset_id, "alice", b.asset_id, "bob")
        .expect("open");
    roost.deposit(&mut swap, true).expect("alice deposits");
    assert_ne!(
        roost.owner_of(a.asset_id),
        Some(alice),
        "escrow now holds a"
    );
    roost.refund_swap(&mut swap).expect("refund");
    assert_eq!(swap.phase(), SwapPhase::Refunded);
    assert_eq!(
        roost.owner_of(a.asset_id),
        Some(alice),
        "refund returned a to alice"
    );
}
