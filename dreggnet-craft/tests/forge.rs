//! THE FORGE, DRIVEN on the real asset layer + the real loot / gear siblings.
//!
//! A craft CONSUMES its typed input materials (provably destroyed on-chain — the first real
//! sink) and, on a minting band, MINTS a new owned output carrying a REAL
//! [`dreggnet_gear::StatBlock`] (or a companion egg) whose id binds the recipe + inputs +
//! band + quality. The outcome band + quality tier are the committed-weight fair draws; a
//! forged craft (a fabricated band/tier), a wrong-kind craft, or an unknown recipe mints
//! NOTHING and spends nothing; a BOTCH is the honest failure that consumes the materials and
//! mints nothing.

use dreggnet_craft::{
    CraftDraw, CraftError, CraftForge, CraftOutcome, CraftQuality, CraftResolution,
    CraftedArtifact, GearSlot, GearTemplate, OutputSpec, Recipe, RecipeBook, roll_craft,
};
use dungeon_on_dregg::loot::{LootDraw, roll_drop};
use procgen_dregg::CommittedSeed;

/// A committed beacon from a 32-bit index (fills the low 4 bytes) — a large scan space for
/// finding a beacon whose deterministic draw hits a target outcome/tier.
fn beacon(n: u32) -> CommittedSeed {
    let mut b = [0u8; 32];
    b[..4].copy_from_slice(&n.to_le_bytes());
    CommittedSeed::from_bytes(b)
}

/// Scan for the first beacon whose craft of `recipe` over `inputs` satisfies `pred`.
fn find_beacon<F>(recipe: &Recipe, inputs: &[dreggnet_craft::AssetId], pred: F) -> CommittedSeed
where
    F: Fn(&CraftDraw) -> bool,
{
    for n in 0u32..200_000 {
        let s = beacon(n);
        if pred(&roll_craft(&s, recipe, inputs)) {
            return s;
        }
    }
    panic!(
        "no beacon in 0..200000 satisfies the predicate for `{}`",
        recipe.id
    );
}

/// The starter greatblade recipe (a SAFE recipe: always succeeds).
fn greatblade(forge: &CraftForge) -> Recipe {
    forge
        .recipe("forge:greatblade")
        .expect("starter recipe")
        .clone()
}

/// A safe craft CONSUMES its typed inputs (provably destroyed) and MINTS a real, equippable
/// gear stat block whose provenance binds the recipe + inputs + band + quality.
#[test]
fn a_safe_craft_consumes_typed_inputs_and_mints_a_real_statblock() {
    let mut forge = CraftForge::new();
    let recipe = greatblade(&forge);
    let smith_pk = forge.pubkey_of("smith");

    // The recipe's exact typed multiset: 2x ore:iron + 1x haft:oak.
    let ore1 = forge.mint_material("smith", "ore:iron", b"ore-1");
    let ore2 = forge.mint_material("smith", "ore:iron", b"ore-2");
    let haft = forge.mint_material("smith", "haft:oak", b"haft-1");
    let inputs = vec![ore1, ore2, haft];

    let draw = roll_craft(&beacon(7), &recipe, &inputs);
    assert_eq!(
        draw.outcome,
        CraftOutcome::Success,
        "a safe recipe always succeeds"
    );

    let res = forge.craft("smith", &draw).expect("a real craft resolves");
    let out = res.output().expect("a safe craft mints").clone();

    assert_eq!(out.owner, smith_pk, "the output is owned by the crafter");
    assert_eq!(forge.owner_of(out.asset_id), Some(smith_pk));

    // THE SINK: every input is provably BURNED on-chain by the owner-signed spend.
    for id in [ore1, ore2, haft] {
        assert!(forge.is_destroyed(id), "the input was consumed");
        assert!(!forge.owns_live("smith", id), "a burned input is not live");
        let ap = forge.asset_provenance(id);
        // The owner-signed sink BURNED the input: the asset layer reports it revoked (its
        // origin spent on-chain, no successor) and it has no live owner.
        assert!(
            ap.revoked,
            "the asset layer reports the input burned on-chain: {:?}",
            ap.reasons
        );
        assert_eq!(forge.owner_of(id), None, "a burned input has no live owner");
    }

    // THE OUTPUT is a REAL gear stat block (the shared dreggnet-gear schema).
    match &out.artifact {
        CraftedArtifact::Gear(block) => {
            assert_eq!(block.slot, GearSlot::Weapon, "greatblade forges a weapon");
            assert_eq!(block.rune, 0x01);
            assert_eq!(
                block.rarity,
                out.quality.gear_rarity(),
                "rarity is the fair tier"
            );
            let pct = out.quality.stat_percent();
            assert_eq!(block.might, 40 * pct / 100, "might scales with the tier");
        }
        other => panic!("greatblade forges gear, got {other:?}"),
    }

    // Provenance binds the fair draw + inputs, and the output lineage re-verifies live.
    let prov = forge.provenance(out.asset_id).expect("provenance recorded");
    assert_eq!(prov.recipe_id, "forge:greatblade");
    assert_eq!(prov.outcome, CraftOutcome::Success);
    let mut want = vec![ore1.bytes(), ore2.bytes(), haft.bytes()];
    want.sort_unstable();
    assert_eq!(prov.input_ids, want, "provenance binds the input ids");
    assert!(
        prov.asset.verified,
        "the output lineage re-verifies: {:?}",
        prov.asset.reasons
    );
    assert_eq!(prov.asset.length, 1, "a fresh output is a length-1 lineage");
    assert_eq!(forge.output_count(), 1);
    assert_eq!(forge.botch_count(), 0);
}

/// A LEGENDARY vs a COMMON craft is the committed-weight fair draw — and a legendary gear
/// block is materially stronger (its stats scale with the fair tier).
#[test]
fn quality_tiers_are_the_committed_weighted_draw() {
    let mut forge = CraftForge::new();
    let recipe = greatblade(&forge);

    let leg_inputs = vec![
        forge.mint_material("smith", "ore:iron", b"L-ore-1"),
        forge.mint_material("smith", "ore:iron", b"L-ore-2"),
        forge.mint_material("smith", "haft:oak", b"L-haft"),
    ];
    let leg_beacon = find_beacon(&recipe, &leg_inputs, |d| d.tier == CraftQuality::Legendary);
    let leg_draw = roll_craft(&leg_beacon, &recipe, &leg_inputs);
    dreggnet_craft::reverify_craft(&leg_draw, &recipe).expect("the legendary is a real draw");

    let com_inputs = vec![
        forge.mint_material("smith", "ore:iron", b"C-ore-1"),
        forge.mint_material("smith", "ore:iron", b"C-ore-2"),
        forge.mint_material("smith", "haft:oak", b"C-haft"),
    ];
    let com_beacon = find_beacon(&recipe, &com_inputs, |d| d.tier == CraftQuality::Common);
    let com_draw = roll_craft(&com_beacon, &recipe, &com_inputs);

    let leg = forge
        .craft("smith", &leg_draw)
        .unwrap()
        .output()
        .unwrap()
        .clone();
    let com = forge
        .craft("smith", &com_draw)
        .unwrap()
        .output()
        .unwrap()
        .clone();

    assert_eq!(
        forge.quality_of(leg.asset_id),
        Some(CraftQuality::Legendary)
    );
    assert_eq!(forge.quality_of(com.asset_id), Some(CraftQuality::Common));
    assert_ne!(
        leg.asset_id.bytes(),
        com.asset_id.bytes(),
        "different tiers, different items"
    );

    let (leg_might, com_might) = match (&leg.artifact, &com.artifact) {
        (CraftedArtifact::Gear(l), CraftedArtifact::Gear(c)) => (l.might, c.might),
        _ => panic!("both forge gear"),
    };
    assert!(
        leg_might > com_might,
        "a legendary is stronger: {leg_might} > {com_might}"
    );
    assert_eq!(leg.artifact.content_digest().len(), 32);
}

/// A FORGED craft — a rewritten quality tier (a fabricated legendary the seed never made) —
/// is REFUSED with NO input spent and NO mint. Non-vacuous: the honest craft then forges.
#[test]
fn a_forged_craft_mints_nothing_and_spends_nothing() {
    let mut forge = CraftForge::new();
    let recipe = greatblade(&forge);
    let a = forge.mint_material("cheat", "ore:iron", b"f-a");
    let b = forge.mint_material("cheat", "ore:iron", b"f-b");
    let c = forge.mint_material("cheat", "haft:oak", b"f-c");
    let inputs = vec![a, b, c];
    let honest = roll_craft(&beacon(3), &recipe, &inputs);

    // Rewrite the tier to a flex the seed never made.
    let mut forged = honest.clone();
    forged.tier = if honest.tier == CraftQuality::Legendary {
        CraftQuality::Common
    } else {
        CraftQuality::Legendary
    };

    let out = forge.craft("cheat", &forged);
    assert!(
        matches!(out, Err(CraftError::Forged(_))),
        "a rewritten tier is refused: {out:?}"
    );
    assert_eq!(forge.output_count(), 0, "no output for the forged craft");
    assert_eq!(
        forge.botch_count(),
        0,
        "a forged craft is not even a botch — it spends nothing"
    );
    assert!(
        !forge.is_destroyed(a) && !forge.is_destroyed(b) && !forge.is_destroyed(c),
        "no input was consumed by the refused forged craft"
    );

    // The HONEST craft over the same inputs still forges (the tooth is not vacuous).
    let item = forge
        .craft("cheat", &honest)
        .unwrap()
        .output()
        .unwrap()
        .clone();
    assert_eq!(
        forge.quality_of(item.asset_id),
        Some(honest.granted_quality().unwrap())
    );
    assert!(forge.is_destroyed(a) && forge.is_destroyed(b) && forge.is_destroyed(c));
    assert_eq!(forge.output_count(), 1);
}

/// Presenting the WRONG typed inputs (right count, wrong kinds) is refused with no spend —
/// the typed sink is real, not a bare count.
#[test]
fn wrong_input_kinds_are_refused() {
    let mut forge = CraftForge::new();
    let recipe = greatblade(&forge); // needs 2x ore:iron + 1x haft:oak

    let a = forge.mint_material("smith", "ore:iron", b"w-a");
    let b = forge.mint_material("smith", "ore:iron", b"w-b");
    let wrong = forge.mint_material("smith", "silver:leaf", b"w-c"); // wrong kind
    let inputs = vec![a, b, wrong];
    let draw = roll_craft(&beacon(1), &recipe, &inputs);

    let out = forge.craft("smith", &draw);
    assert!(
        matches!(out, Err(CraftError::InputKindMismatch(_))),
        "a wrong-kind craft is refused: {out:?}"
    );
    assert_eq!(forge.output_count(), 0, "no output minted");
    assert!(
        !forge.is_destroyed(a) && !forge.is_destroyed(b) && !forge.is_destroyed(wrong),
        "no input consumed by the refused craft"
    );

    // The RIGHT kinds then forge (non-vacuous).
    let haft = forge.mint_material("smith", "haft:oak", b"w-haft");
    let good = roll_craft(&beacon(1), &recipe, &[a, b, haft]);
    assert!(forge.craft("smith", &good).unwrap().is_crafted());
}

/// A craft under a recipe the forge's catalog does not hold is refused (a craft cannot bring
/// its own odds).
#[test]
fn an_unknown_recipe_is_refused() {
    let mut forge = CraftForge::with_book(RecipeBook::new()); // empty catalog
    let phantom = Recipe::gear(
        "forge:phantom",
        &["ore:iron"],
        GearTemplate {
            slot: GearSlot::Weapon,
            rune: 9,
            base_might: 10,
            base_ward: 0,
            base_guile: 0,
        },
    );
    let m = forge.mint_material("p", "ore:iron", b"ph");
    let draw = roll_craft(&beacon(2), &phantom, &[m]);
    let out = forge.craft("p", &draw);
    assert!(
        matches!(out, Err(CraftError::UnknownRecipe(_))),
        "unknown recipe refused: {out:?}"
    );
    assert!(!forge.is_destroyed(m), "no input consumed");
}

/// A BOTCH is the honest failure: the materials ARE consumed (the sink fires) but NO output
/// is minted — distinct from a forged refusal, which spends nothing.
#[test]
fn a_botch_consumes_materials_but_mints_nothing() {
    let mut forge = CraftForge::new();
    let recipe = forge.recipe("forge:relic").expect("risky recipe").clone(); // [20,30,50]

    let inputs = vec![
        forge.mint_material("smith", "ore:star-iron", b"b-1"),
        forge.mint_material("smith", "essence:void", b"b-2"),
        forge.mint_material("smith", "essence:void", b"b-3"),
    ];
    let botch_beacon = find_beacon(&recipe, &inputs, |d| d.outcome == CraftOutcome::Botch);
    let draw = roll_craft(&botch_beacon, &recipe, &inputs);

    let res = forge
        .craft("smith", &draw)
        .expect("a botch is a resolved craft, not an error");
    match res {
        CraftResolution::Botched(receipt) => {
            assert_eq!(receipt.recipe_id, "forge:relic");
            assert_eq!(receipt.consumed.len(), 3);
        }
        CraftResolution::Crafted(_) => panic!("expected a botch"),
    }
    // The sink still fired — the materials are gone — but nothing was minted.
    for id in &inputs {
        assert!(
            forge.is_destroyed(*id),
            "a botch still consumes its materials"
        );
    }
    assert_eq!(forge.output_count(), 0, "a botch mints no output");
    assert_eq!(forge.botch_count(), 1);
}

/// A PARTIAL outcome forges a real output, downgraded one tier from the fair draw.
#[test]
fn a_partial_downgrades_one_tier() {
    let mut forge = CraftForge::new();
    let recipe = forge.recipe("forge:relic").expect("risky recipe").clone();

    let inputs = vec![
        forge.mint_material("smith", "ore:star-iron", b"p-1"),
        forge.mint_material("smith", "essence:void", b"p-2"),
        forge.mint_material("smith", "essence:void", b"p-3"),
    ];
    // A partial whose raw tier is above Common, so the downgrade is observable.
    let bcn = find_beacon(&recipe, &inputs, |d| {
        d.outcome == CraftOutcome::Partial && d.tier != CraftQuality::Common
    });
    let draw = roll_craft(&bcn, &recipe, &inputs);
    let granted = draw.granted_quality().expect("a partial mints");
    assert_eq!(
        granted,
        draw.tier.downgraded(),
        "a partial forges one tier down"
    );

    let out = forge
        .craft("smith", &draw)
        .unwrap()
        .output()
        .unwrap()
        .clone();
    assert_eq!(out.outcome, CraftOutcome::Partial);
    assert_eq!(out.quality, granted);
}

/// A companion-egg recipe forges a real egg output binding the species + the granted shared
/// rarity (the schema dreggnet-companion hatches from).
#[test]
fn a_companion_egg_binds_species_and_rarity() {
    let mut forge = CraftForge::new();
    let recipe = forge
        .recipe("forge:frostwyrm-egg")
        .expect("egg recipe")
        .clone();
    let inputs = vec![
        forge.mint_material("smith", "essence:frost", b"e-1"),
        forge.mint_material("smith", "essence:frost", b"e-2"),
        forge.mint_material("smith", "shell:ancient", b"e-3"),
    ];
    // A success (so it mints an egg, not a botch).
    let bcn = find_beacon(&recipe, &inputs, |d| d.outcome == CraftOutcome::Success);
    let draw = roll_craft(&bcn, &recipe, &inputs);
    let out = forge
        .craft("smith", &draw)
        .unwrap()
        .output()
        .unwrap()
        .clone();
    match &out.artifact {
        CraftedArtifact::CompanionEgg { species, rarity } => {
            assert_eq!(species, "companion:frostwyrm");
            assert_eq!(
                *rarity,
                out.quality.loot_rarity(),
                "the egg hatches at the fair tier"
            );
        }
        other => panic!("the egg recipe forges an egg, got {other:?}"),
    }
}

/// A material can be SOURCED from a real, verified loot drop — and a forged loot draw cannot
/// become a material.
#[test]
fn a_loot_sourced_material_requires_a_verified_drop() {
    let mut forge = CraftForge::new();

    // A genuine drop from a run.
    let run_seed = CommittedSeed::from_bytes([42u8; 32]);
    let drop = roll_drop(&run_seed, "boss:the Tide-Warden", 1);
    let mat = forge
        .mint_loot_material("smith", "ore:iron", &drop)
        .expect("a verified drop mints a material");
    assert_eq!(
        forge.material_kind(mat).map(|k| k.as_str()),
        Some("ore:iron")
    );
    assert!(
        forge.owns_live("smith", mat),
        "the loot-sourced material is a live owned asset"
    );

    // A FORGED drop — a rewritten roll the seed never produced — cannot become a material.
    let mut forged = drop.clone();
    forged.roll = forged.roll.wrapping_add(1);
    let bad = forge.mint_loot_material("smith", "ore:iron", &forged);
    assert!(
        matches!(bad, Err(CraftError::ForgedLoot(_))),
        "a forged drop is refused: {bad:?}"
    );
}

/// A loot-sourced material actually crafts: source the recipe's inputs from real drops, then
/// forge — the whole input side wired to the real economy.
#[test]
fn loot_sourced_inputs_forge_a_real_item() {
    let mut forge = CraftForge::new();
    let recipe = greatblade(&forge);
    let run_seed = CommittedSeed::from_bytes([7u8; 32]);

    let drops: Vec<LootDraw> = (0..3)
        .map(|i| roll_drop(&run_seed, "chest:vault", i))
        .collect();
    let ore1 = forge
        .mint_loot_material("smith", "ore:iron", &drops[0])
        .unwrap();
    let ore2 = forge
        .mint_loot_material("smith", "ore:iron", &drops[1])
        .unwrap();
    let haft = forge
        .mint_loot_material("smith", "haft:oak", &drops[2])
        .unwrap();

    let draw = roll_craft(&beacon(11), &recipe, &[ore1, ore2, haft]);
    let out = forge
        .craft("smith", &draw)
        .unwrap()
        .output()
        .unwrap()
        .clone();
    assert!(
        matches!(out.artifact, CraftedArtifact::Gear(_)),
        "loot-sourced inputs forge gear"
    );
    for id in [ore1, ore2, haft] {
        assert!(
            forge.is_destroyed(id),
            "the loot-sourced input was consumed"
        );
    }
}

/// NO DUPE-THEN-CRAFT: consumed inputs cannot be re-crafted (a spent note cannot be respent),
/// and an un-owned input is refused.
#[test]
fn inputs_cannot_be_reused_or_stolen() {
    let mut forge = CraftForge::new();
    let recipe = greatblade(&forge);

    // An input owned by someone else is refused.
    let a = forge.mint_material("smith", "ore:iron", b"s-a");
    let b = forge.mint_material("smith", "ore:iron", b"s-b");
    let theirs = forge.mint_material("rival", "haft:oak", b"s-c");
    let bad_draw = roll_craft(&beacon(1), &recipe, &[a, b, theirs]);
    let out = forge.craft("smith", &bad_draw);
    assert!(
        matches!(out, Err(CraftError::InputsUnavailable(_))),
        "a craft over an un-owned input is refused: {out:?}"
    );
    assert!(
        !forge.is_destroyed(a),
        "no input consumed by the refused craft"
    );

    // Consume a valid set, then try to re-craft the same (now-destroyed) inputs.
    let haft = forge.mint_material("smith", "haft:oak", b"s-haft");
    let good = roll_craft(&beacon(2), &recipe, &[a, b, haft]);
    forge.craft("smith", &good).unwrap().output().unwrap();
    assert!(forge.is_destroyed(a) && forge.is_destroyed(b) && forge.is_destroyed(haft));

    let redraw = roll_craft(&beacon(9), &recipe, &[a, b, haft]);
    let reuse = forge.craft("smith", &redraw);
    assert!(
        matches!(reuse, Err(CraftError::InputsUnavailable(_))),
        "re-crafting consumed inputs is refused: {reuse:?}"
    );
    assert_eq!(forge.output_count(), 1, "the dupe craft minted nothing");
}

/// The input consume is OWNER-SIGNED: a non-owner cannot craft another player's materials,
/// and the owner-gated burn refuses a non-owner directly — the authorization to consume is an
/// ISA owner-signature gate, not merely a host `owns_live` check. The owner then crafts
/// cleanly, its inputs burned by a real owner-signed spend (non-vacuous).
#[test]
fn the_input_consume_is_owner_signed_a_non_owner_craft_is_refused() {
    let mut forge = CraftForge::new();
    let recipe = greatblade(&forge); // 2x ore:iron + haft:oak

    // HERO owns exactly the greatblade inputs.
    let i1 = forge.mint_material("hero", "ore:iron", b"os-1");
    let i2 = forge.mint_material("hero", "ore:iron", b"os-2");
    let haft = forge.mint_material("hero", "haft:oak", b"os-3");
    let draw = roll_craft(&beacon(7), &recipe, &[i1, i2, haft]);

    // MALLORY (not the owner) tries to craft HERO's materials -> refused, nothing consumed.
    let stolen = forge.craft("mallory", &draw);
    assert!(
        matches!(
            stolen,
            Err(CraftError::InputsUnavailable(_)) | Err(CraftError::Asset(_))
        ),
        "a non-owner craft is refused, got {stolen:?}"
    );
    assert!(
        !forge.is_destroyed(i1) && !forge.is_destroyed(i2) && !forge.is_destroyed(haft),
        "anti-ghost: a refused craft burns nothing"
    );

    // The owner-gated burn refuses a non-owner directly: MALLORY cannot burn HERO's note.
    assert!(
        forge.assets_mut().revoke(i1, "mallory").is_err(),
        "a non-owner cannot burn the note"
    );
    assert!(
        !forge.is_destroyed(i1),
        "the note survived the non-owner burn"
    );

    // The OWNER crafts cleanly: the owner-signed burn commits as a real executor turn and the
    // item mints.
    let out = forge.craft("hero", &draw).expect("the owner crafts");
    assert!(out.is_crafted(), "the owner's craft mints an output");
    assert!(
        forge.is_destroyed(i1) && forge.is_destroyed(i2) && forge.is_destroyed(haft),
        "the owner-signed sink burned every input"
    );
    assert_eq!(forge.owner_of(i1), None, "a burned input has no live owner");
}

/// The starter catalog holds the expected recipes and rejects a degenerate one.
#[test]
fn the_recipe_catalog_is_committed() {
    let forge = CraftForge::new();
    let ids = forge.book().ids();
    assert!(ids.contains(&"forge:greatblade".to_string()));
    assert!(ids.contains(&"forge:relic".to_string()));
    assert!(ids.contains(&"forge:frostwyrm-egg".to_string()));

    let mut book = RecipeBook::new();
    // A degenerate recipe (empty inputs) never enters the catalog.
    let bad = Recipe::risky(
        "forge:bad",
        &[],
        [0, 0, 1],
        [1, 1, 1, 1],
        OutputSpec::CompanionEgg {
            species: "x".to_string(),
        },
    );
    assert!(!book.register(bad), "a degenerate recipe is rejected");
    assert!(book.is_empty());
}
