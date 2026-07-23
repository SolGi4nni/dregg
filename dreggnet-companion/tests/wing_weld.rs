//! **THE WING'S ATTUNEMENT IS WELDED — driven through the deployed app-root fold node.**
//!
//! This is the graduation canary: a real in-tree GAME entity — two companions a handler raised on
//! the roost's real XP-gated cells — composes through `dregg-braid-hook` and lands as a turn whose
//! published attunement is tied, in-circuit, to the attunement cell's committed native
//! `fields[0..8]` octet.
//!
//! * **S1, the honest pole (runs FIRST):** a wing whose committed octet equals its composed
//!   attunement FOLDS through `prove_custom_binding_node_app_root_segmented` — the node produces a
//!   root, so the property is visible to a pure light client folding the artifact.
//! * **S2, the bite:** the same wing with ONE lane of the committed octet perturbed — "the roost
//!   wrote attunement X into the cell while the sub-proof composed Y" — has NO satisfying fold.
//!   UNSAT, refused.
//!
//! The honest pole runs first so the refusal is attributable to the app-root connect and not to
//! unrelated breakage.
//!
//! Nothing here authors a constraint: the tie is the deployed app-root atom (whose in-circuit
//! keystone descends from Lean `CustomBindingFromFold`), reached through the hook. The game
//! supplies only the content — which creatures, which law, what the number means.
//!
//! The folds are real recursions (minutes each), so this is `#[ignore]` and needs `prove`:
//!   cargo test -p dreggnet-companion --features prove --test wing_weld -- --ignored --nocapture
#![cfg(feature = "prove")]

use dregg_braid_hook::fold::{fold_composition_app_root, forged_after};
use dreggnet_companion::wing::WING_FOLD_ROWS;
use dreggnet_companion::{CompanionRoost, HatchBeacon, roll_hatch};

/// **THE WING WELD CANARY.** An honest wing folds; a wing whose committed attunement octet
/// disagrees with the composed attunement is refused.
#[test]
#[ignore = "SLOW: real deployed app-root weld recursion folds (~minutes each); run with --ignored"]
fn a_wings_attunement_is_welded_to_its_cell() {
    let mut roost = CompanionRoost::new();
    let draw_w = roll_hatch(
        &HatchBeacon::from_bytes([7u8; 32]),
        "companion:frostwyrm",
        0,
    );
    let draw_c = roll_hatch(
        &HatchBeacon::from_bytes([7u8; 32]),
        "companion:emberling",
        0,
    );
    let warden = roost.hatch("ember", &draw_w).expect("the warden hatches");
    let consort = roost.hatch("ember", &draw_c).expect("the consort hatches");

    // Real XP-gated progression turns — the params the Braid composes are these committed fields.
    roost.raise_to(&warden, 3).expect("the warden raises");
    roost.raise_to(&consort, 2).expect("the consort raises");

    let wing = roost
        .attune_wing("ember", &warden, &consort)
        .expect("two owned, living, fair-hatched companions attune");
    eprintln!(
        "WING: warden lvl {} ({:?}) + consort lvl {} ({:?}) -> attunement {}",
        roost.level_of(&warden),
        warden.rarity,
        roost.level_of(&consort),
        consort.rarity,
        wing.attunement,
    );
    assert!(
        wing.outcome_welded(),
        "sanity: the attunement cell's committed octet carries the published outcome_commitment"
    );

    // S1 — THE HONEST POLE. The forged fold below differs only in one committed lane, so without
    // an accept here the refusal would prove nothing.
    wing.seal().expect(
        "an HONEST wing (committed octet == composed attunement) must FOLD through the deployed \
         app-root node",
    );
    eprintln!("WING WELD: the honest attunement FOLDED through the app-root node.");

    // S2 — THE BITE. The cell claims an attunement the composition did not produce.
    let err = fold_composition_app_root(
        &wing.entity.cell,
        &forged_after(&wing.landed, 0),
        &wing.landed,
        WING_FOLD_ROWS,
    )
    .expect_err(
        "a wing whose committed attunement octet does NOT match the composed attunement must be \
         REFUSED by the app-root weld",
    );
    assert!(
        err.contains("app-root fold refused"),
        "the refusal must come from the app-root fold node (the weld), got: {err}"
    );
    eprintln!("WING WELD: a forged attunement was REFUSED by the app-root fold connect: {err}");
}
