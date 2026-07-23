//! **THE WING RIDES THE BRAID** — the companion game's content on `dregg-braid-hook`, driven on
//! the real roost.
//!
//! Two raised companions attune into a wing whose worth is a *composition* of both: three linear
//! terms plus two KNOTS (`level × level`, `rarity × rarity`). The knots are the point — the
//! kernel's declarative `StateConstraint` vocabulary is linear, so "the pair is worth more than
//! the sum of its members" is not expressible as a buff cell's predicate; it needs the general
//! Custom-VK composition AIR the hook reaches.
//!
//! These are the FAST paths (no proving): the projection is real committed state, the law's
//! nonlinearity is load-bearing, the gates refuse, and the composed outcome lands in the
//! attunement cell's committed octet. The SLOW canary — the honest wing folding through the
//! deployed app-root node and a forged committed octet being refused — is `tests/wing_weld.rs`
//! (feature `prove`).

use dregg_braid_hook::{Comp, Subject};
use dreggnet_companion::wing::{
    CO_BOND, CO_CONSORT_LEVEL, CO_RESONANCE, CO_WARDEN_FATIGUE, CO_WARDEN_LEVEL, P_CLASS, P_LEVEL,
    P_RARITY, P_SPENT, ROLE_CONSORT, ROLE_WARDEN, WING_PARAM_COUNT, braid_identity,
};
use dreggnet_companion::{
    Companion, CompanionError, CompanionRoost, HatchBeacon, rarity_rank, reverify_attunement,
    roll_hatch, wing_law,
};

fn beacon(byte: u8) -> HatchBeacon {
    HatchBeacon::from_bytes([byte; 32])
}

/// Hatch a companion of `species` for `player` off a fixed beacon (whatever rarity the fair draw
/// lands on — the wing law reads the tier it really got).
fn hatch(roost: &mut CompanionRoost, player: &str, species: &str) -> Companion {
    let draw = roll_hatch(&beacon(7), species, 0);
    roost.hatch(player, &draw).expect("a fair hatch mints")
}

/// The wing law, evaluated by hand off the roost's own committed reads — an INDEPENDENT oracle
/// for what the Braid composed (it never looks at the wing's own projection).
fn expected_attunement(roost: &CompanionRoost, warden: &Companion, consort: &Companion) -> i128 {
    let wl = roost.level_of(warden) as i128;
    let cl = roost.level_of(consort) as i128;
    let ws = roost.abilities_used_of(warden) as i128;
    let wr = i128::from(rarity_rank(warden.rarity));
    let cr = i128::from(rarity_rank(consort.rarity));
    CO_WARDEN_LEVEL as i128 * wl
        + CO_CONSORT_LEVEL as i128 * cl
        + CO_WARDEN_FATIGUE as i128 * ws
        + CO_BOND as i128 * wl * cl
        + CO_RESONANCE as i128 * wr * cr
}

// ── The composition is over the game's REAL committed state ─────────────────────────

/// A wing composes from the companions' live committed cells, the composed attunement is the
/// named law's value, and it lands in the attunement cell's committed octet.
#[test]
fn a_wing_composes_from_committed_companion_state() {
    let mut roost = CompanionRoost::new();
    let warden = hatch(&mut roost, "ember", "companion:frostwyrm");
    let consort = hatch(&mut roost, "ember", "companion:emberling");

    // Real XP-gated progression turns — the params the Braid reads are these committed fields.
    roost.raise_to(&warden, 3).expect("the warden raises");
    roost.raise_to(&consort, 2).expect("the consort raises");

    let wing = roost
        .attune_wing("ember", &warden, &consort)
        .expect("two owned, living, fair-hatched companions attune");

    assert_eq!(
        wing.attunement,
        expected_attunement(&roost, &warden, &consort),
        "the Braid's composed outcome must be the wing law over the committed projection"
    );
    assert_eq!(
        reverify_attunement(&wing).expect("the attunement re-derives"),
        wing.attunement,
        "the host-side re-derivation must agree with the carried attunement"
    );
    assert!(
        wing.outcome_welded(),
        "the attunement cell's committed native octet must carry the published outcome_commitment"
    );

    // The projection is the committed state, slot by slot.
    let (w, c) = wing.subjects();
    assert_eq!(w.role, ROLE_WARDEN);
    assert_eq!(c.role, ROLE_CONSORT);
    assert_eq!(w.params.len(), WING_PARAM_COUNT);
    assert_eq!(w.params[P_LEVEL], roost.level_of(&warden) as i64);
    assert_eq!(w.params[P_RARITY], i64::from(rarity_rank(warden.rarity)));
    assert_eq!(w.params[P_CLASS], roost.class_of(&warden) as i64);
    assert_eq!(w.params[P_SPENT], roost.abilities_used_of(&warden) as i64);
    assert_eq!(c.params[P_LEVEL], roost.level_of(&consort) as i64);
    assert_eq!(w.identity, braid_identity(warden.asset_id));
    assert_ne!(
        w.identity, c.identity,
        "the two members must occupy distinct Braid identities"
    );
}

/// **The composition tracks committed progression.** A real level-up turn moves the wing's
/// attunement by EXACTLY the law's delta — the linear term plus the BOND knot's cross-term. If
/// the params were a host-side sheet rather than the cells' committed fields, this would not hold.
#[test]
fn leveling_a_companion_moves_the_wing_attunement() {
    let mut roost = CompanionRoost::new();
    let warden = hatch(&mut roost, "ember", "companion:frostwyrm");
    let consort = hatch(&mut roost, "ember", "companion:emberling");
    roost.raise_to(&warden, 2).expect("the warden raises");
    roost.raise_to(&consort, 3).expect("the consort raises");

    let before = roost
        .attune_wing("ember", &warden, &consort)
        .expect("attunes")
        .attunement;

    // One real XP-gated level-up on the warden's own cell.
    let consort_level = roost.level_of(&consort) as i128;
    roost.raise_to(&warden, 3).expect("the warden levels");

    let after = roost
        .attune_wing("ember", &warden, &consort)
        .expect("re-attunes")
        .attunement;

    assert_eq!(
        after - before,
        CO_WARDEN_LEVEL as i128 + CO_BOND as i128 * consort_level,
        "one warden level must move the attunement by the linear coefficient PLUS the bond knot's \
         cross-term — the nonlinear part is what a linear cell predicate could not have produced"
    );
}

// ── The knots are load-bearing ──────────────────────────────────────────────────────

/// **THE NONLINEARITY CANARY.** Two wings whose members' rarities SUM identically — `(0,3)` and
/// `(1,2)` — but whose PRODUCTS differ compose to DIFFERENT attunements, and the gap is exactly
/// the resonance knot's. Every linear functional of the projections is blind to this difference,
/// so no `AffineEq`/`AffineLe` state constraint could have expressed the wing law.
#[test]
fn the_resonance_knot_separates_wings_no_linear_predicate_can() {
    let subject = |identity: u64, role: u64, level: i64, rarity: i64| Subject {
        identity,
        role,
        params: vec![level, rarity, 0, 0],
    };
    let compose = |wr: i64, cr: i64| {
        Comp {
            subjects: vec![
                subject(11, ROLE_WARDEN, 4, wr),
                subject(22, ROLE_CONSORT, 3, cr),
            ],
            ruleset: wing_law(),
            param_count: WING_PARAM_COUNT,
        }
        .compose()
        .expect("a well-formed wing composition")
        .outcome
    };

    let split = compose(0, 3); // rarity sum 3, product 0
    let matched = compose(1, 2); // rarity sum 3, product 2
    assert_eq!(
        matched - split,
        CO_RESONANCE as i128 * 2,
        "the only difference between these wings is a PRODUCT of two committed values"
    );
    assert_ne!(split, matched);
}

// ── The gates refuse, and nothing is deployed ───────────────────────────────────────

/// A wing is refused for a non-owner, a dead companion, and a self-pairing.
#[test]
fn attuning_refuses_a_non_owner_a_dead_companion_and_a_self_pairing() {
    let mut roost = CompanionRoost::new();
    let warden = hatch(&mut roost, "ember", "companion:frostwyrm");
    let consort = hatch(&mut roost, "ember", "companion:emberling");
    roost.raise_to(&warden, 2).expect("raises");

    // A companion cannot be attuned to itself (one entity would occupy two roles).
    match roost.attune_wing("ember", &warden, &warden) {
        Err(CompanionError::Ineligible(w)) => assert!(w.contains("itself"), "{w}"),
        Err(e) => panic!("a self-pairing must be refused as ineligible, got {e}"),
        Ok(_) => panic!("a self-pairing must be refused"),
    }

    // A non-owner cannot attune another handler's companions.
    match roost.attune_wing("mallory", &warden, &consort) {
        Err(CompanionError::NotOwner) => {}
        Err(e) => panic!("a non-owner attunement must be refused as NotOwner, got {e}"),
        Ok(_) => panic!("a non-owner attunement must be refused"),
    }

    // The owner CAN — the refusals above are the gates, not a broken path.
    roost
        .attune_wing("ember", &warden, &consort)
        .expect("the owner attunes");

    // A dead companion (the `WriteOnce` permadeath flag) cannot fly.
    roost.perish(&consort).expect("hardcore death commits");
    match roost.attune_wing("ember", &warden, &consort) {
        Err(CompanionError::Ineligible(w)) => assert!(w.contains("dead"), "{w}"),
        Err(e) => panic!("a dead companion must be refused as ineligible, got {e}"),
        Ok(_) => panic!("a dead companion must be refused"),
    }
}

/// A fabricated attunement is caught by the law re-derivation (the host-side twin of the AIR's
/// in-circuit outcome re-check).
#[test]
fn a_fabricated_attunement_fails_re_derivation() {
    let mut roost = CompanionRoost::new();
    let warden = hatch(&mut roost, "ember", "companion:frostwyrm");
    let consort = hatch(&mut roost, "ember", "companion:emberling");
    roost.raise_to(&warden, 3).expect("raises");
    roost.raise_to(&consort, 2).expect("raises");

    let mut wing = roost
        .attune_wing("ember", &warden, &consort)
        .expect("attunes");
    reverify_attunement(&wing).expect("the honest attunement re-derives");

    wing.attunement += 1_000; // "my wing is legendary"
    match reverify_attunement(&wing) {
        Err(CompanionError::Forged(w)) => assert!(w.contains("not the law's composition"), "{w}"),
        Err(e) => panic!("a fabricated attunement must be refused as forged, got {e}"),
        Ok(v) => panic!("a fabricated attunement must fail re-derivation, got {v}"),
    }
}

/// Two wings of the same roost land on DISTINCT attunement cells (the seed namespace advances).
#[test]
fn distinct_wings_land_on_distinct_attunement_cells() {
    let mut roost = CompanionRoost::new();
    let a = hatch(&mut roost, "ember", "companion:frostwyrm");
    let b = hatch(&mut roost, "ember", "companion:emberling");
    let c = hatch(&mut roost, "ember", "companion:cinderling");
    roost.raise_to(&a, 2).expect("raises");

    let w1 = roost.attune_wing("ember", &a, &b).expect("attunes");
    let w2 = roost.attune_wing("ember", &a, &c).expect("attunes");
    assert_ne!(
        w1.cell, w2.cell,
        "each wing must get its own attunement cell"
    );
}
