//! # The reimagined Descent, DRIVEN — the Lean-authored rules on the real executor.
//!
//! Every test here drives the REAL `EmbeddedExecutor` through
//! [`dungeon_on_dregg::descent`]: the installed `CellProgram` is LOADED from the
//! Lean-emitted artifact (`program/dungeon_program.json` — source of truth:
//! `metatheory/Dregg2/Games/DungeonProgram.lean :: dungeonProgram`); there is no
//! hand-rolled Rust tooth anywhere in the path.
//!
//! The battery mirrors the Lean `#guard` battery (same crowned run, same attacks) so
//! the two referees — the Lean `Exec` evaluator the theorems run against, and the
//! deployed Rust executor — are DRIVEN over the same transitions and agree.

use dregg_app_framework::{CellProgram, StateConstraint, TransitionGuard, symbol};
use dregg_cell::program::TransitionMeta;
use dregg_cell::state::CellState;
use dungeon_on_dregg::descent::{
    BANKED, CARRIED, DELVE, Deployment, Descent, FLEE, GENESIS, HARMCAP, LOOT, LUNGE, PROGRAM_JSON,
    SCENE_ID, SMITE, Sim, UNLOCK,
};
use spween_dregg::WorldError;

fn refused(r: Result<dregg_app_framework::TurnReceipt, WorldError>) -> bool {
    matches!(r, Err(WorldError::Refused(_)))
}

/// Materialize the same register + custody representation that `Descent` writes,
/// for a direct evaluator mutation canary.  The real-executor tests below remain
/// the deployment pole; this helper isolates which exact tooth makes the attack
/// flip from admit to refuse.
fn evaluator_state(dep: &Deployment, sim: &Sim) -> CellState {
    let mut state = CellState::new(0);
    for (name, value) in [
        ("depth", sim.depth),
        ("spent", sim.spent),
        ("wounds", sim.wounds),
        ("fate", sim.fate),
        ("pack", sim.pack()),
        ("bank", sim.bank()),
        ("way_2", sim.ways[0]),
        ("way_3", sim.ways[1]),
        ("way_4", sim.ways[2]),
        ("hoard_1", sim.hoard_at(1)),
        ("hoard_2", sim.hoard_at(2)),
        ("hoard_3", sim.hoard_at(3)),
        ("hoard_4", sim.hoard_at(4)),
    ] {
        assert!(state.set_field(
            dep.reg(name) as usize,
            dregg_app_framework::field_from_u64(value)
        ));
    }
    for (i, &custody) in sim.custody.iter().enumerate() {
        assert!(state.set_field_ext(
            dep.relic_key(i),
            dregg_app_framework::field_from_u64(custody),
        ));
    }
    assert!(state.set_field_ext(
        spween_dregg::GENESIS_DONE_EXT_KEY,
        dregg_app_framework::field_from_u64(1),
    ));
    state
}

/// The artifact is the Lean emission: it parses, names OUR scene, and the loaded
/// program is `Cases` with the seven verb arms + eight riders — and the genesis arm
/// carries the spween one-shot sentinel teeth (so the world births + injects the
/// sentinel; a genesis replay is structurally unsatisfiable).
#[test]
fn loaded_program_is_the_lean_object() {
    assert!(PROGRAM_JSON.contains(&format!("\"scene\": \"{SCENE_ID}\"")));
    let dep = dungeon_on_dregg::descent::Deployment::new();
    let program = dep.program();
    let CellProgram::Cases(cases) = &program else {
        panic!("descent program must be Cases");
    };
    assert_eq!(cases.len(), 16, "genesis + 7 verb arms + 8 riders");
    // The genesis arm is MethodIs("genesis") and carries a HeapField tooth on the
    // genesis sentinel (spween keys the sentinel machinery off exactly this shape).
    let genesis = cases
        .iter()
        .find(|c| matches!(c.guard, TransitionGuard::MethodIs { method } if method == symbol(GENESIS)))
        .expect("genesis arm");
    assert!(
        genesis.constraints.iter().any(|c| matches!(
            c,
            StateConstraint::HeapField { key, .. } if *key == spween_dregg::GENESIS_DONE_EXT_KEY
        )),
        "genesis arm carries the one-shot sentinel teeth"
    );
    // At least one rider is a SlotChanged-guarded AllOf (the stapleable-slot fix is
    // deployed structure, not doc prose).
    assert!(
        cases.iter().any(|c| matches!(
            &c.guard,
            TransitionGuard::AllOf(children)
                if children.iter().any(|g| matches!(g, TransitionGuard::SlotChanged { .. }))
        )),
        "the SlotChanged riders are installed"
    );
    let census_teeth: Vec<_> = cases
        .iter()
        .flat_map(|case| &case.constraints)
        .filter_map(|constraint| match constraint {
            StateConstraint::FieldsCountEquals { keys, .. } => Some(keys),
            _ => None,
        })
        .collect();
    assert_eq!(
        census_teeth.len(),
        6,
        "pack, bank, and four hoards each have one exact custody census"
    );
    assert!(
        census_teeth.iter().all(|keys| keys.len() == 8),
        "every census covers all eight relic custody objects"
    );
}

/// THE CROWNED RUN — the same 17-verb script the Lean model proves legal and the Lean
/// `#guard` battery proves admitted — commits end-to-end on the real executor: 18 real
/// receipts (genesis + 17), non-zero and chain-linked, ending banked with the prize
/// and the three keys banked (bank = 4, the `crowned_bank_le_four` bound met with
/// equality) and 2 breath to spare.
#[test]
fn crowned_run_commits_with_real_receipts() {
    let mut d = Descent::deploy(7).expect("deploy + genesis");
    let mut receipts = Vec::new();
    receipts.push(None); // genesis receipt is inside deploy; re-verify via state below.

    let push = |r: Result<dregg_app_framework::TurnReceipt, WorldError>| {
        let r = r.expect("legal verb commits");
        assert_ne!(r.turn_hash, [0u8; 32]);
        Some(r)
    };

    // Floor 1: slay (hp 1), win the key to way 2, exercise it.
    receipts.push(push(d.delve()));
    receipts.push(push(d.smite()));
    receipts.push(push(d.loot(1)));
    receipts.push(push(d.unlock(2)));
    // Floor 2.
    receipts.push(push(d.delve()));
    receipts.push(push(d.smite()));
    receipts.push(push(d.loot(2)));
    receipts.push(push(d.unlock(3)));
    // Floor 3 (guardian hp 2).
    receipts.push(push(d.delve()));
    receipts.push(push(d.smite()));
    receipts.push(push(d.smite()));
    receipts.push(push(d.loot(3)));
    receipts.push(push(d.unlock(4)));
    // Floor 4 — the bottom: THE PRIZE.
    receipts.push(push(d.delve()));
    receipts.push(push(d.smite()));
    receipts.push(push(d.smite()));
    receipts.push(push(d.loot(0)));
    receipts.push(push(d.flee()));

    // The receipt chain links (each pre-state is the predecessor's post-state).
    let committed: Vec<_> = receipts.into_iter().flatten().collect();
    for w in committed.windows(2) {
        assert_eq!(
            w[0].post_state_hash, w[1].pre_state_hash,
            "receipt chain links"
        );
    }

    // The committed world agrees with the model's crowned end-state.
    assert_eq!(d.read_reg("fate"), 1);
    assert_eq!(d.read_reg("bank"), 4, "prize + three keys banked");
    assert_eq!(d.read_reg("pack"), 0);
    assert_eq!(d.read_reg("spent"), 24, "the perfect run costs 24 breath");
    assert_eq!(d.read_reg("depth"), 4);
    assert_eq!(d.read_relic(0), BANKED, "THE PRIZE is banked");
    assert_eq!(d.read_relic(4), 1, "an unlooted treasure stays in the deep");
}

/// A keyless descent is a REAL executor refusal that commits nothing (anti-ghost).
#[test]
fn keyless_descent_is_refused_and_commits_nothing() {
    let mut d = Descent::deploy(3).expect("deploy");
    d.delve().expect("way 1 is always open");
    // The mover itself refuses (way 2 shut) — now FORGE the projection at the raw
    // seam so the EXECUTOR is the referee under test, not the mover.
    let sim = d.sim().clone();
    let mut forged = sim.clone();
    forged.depth = 2;
    forged.wounds = 0;
    forged.spent += 1;
    let effects = d.effects_for(&forged);
    assert!(
        refused(d.commit_raw(DELVE, effects)),
        "keyless descent refused by the Lean-sourced teeth"
    );
    // Anti-ghost: nothing committed.
    assert_eq!(d.read_reg("depth"), 1);
    assert_eq!(d.read_reg("spent"), sim.spent);
}

/// DUPE: a loot-shaped turn that mints a pack relic out of nothing (pack +1 with no
/// hoard debit) breaks the conservation tooth and is refused.
#[test]
fn dupe_relic_is_refused() {
    let mut d = Descent::deploy(3).expect("deploy");
    d.delve().expect("delve");
    d.smite().expect("smite");
    let sim = d.sim().clone();
    let effects = vec![
        d.reg_effect("pack", sim.pack() + 1),
        d.reg_effect("spent", sim.spent + 1),
    ];
    assert!(
        refused(d.commit_raw(LOOT, effects)),
        "a minted relic breaks SumEquals and is refused"
    );
    assert_eq!(d.read_reg("pack"), 0);
}

/// OBJECT/PROJECTION SPLIT: a conservation-consistent counter transition with no
/// custody move used to fit the counter-only rules.  The exact census refuses it
/// and rolls the attempted projection back.
#[test]
fn counter_only_loot_is_refused_and_commits_nothing() {
    let mut d = Descent::deploy(3).expect("deploy");
    d.delve().expect("delve");
    d.smite().expect("slay guardian");
    let sim = d.sim().clone();
    let effects = vec![
        d.reg_effect("pack", 1),
        d.reg_effect("hoard_1", 2),
        d.reg_effect("spent", sim.spent + 1),
    ];
    assert!(
        refused(d.commit_raw(LOOT, effects)),
        "register projections cannot claim a custody move that never happened"
    );
    assert_eq!(d.read_reg("pack"), 0);
    assert_eq!(d.read_reg("hoard_1"), 3);
    assert_eq!(d.read_relic(1), 1);
}

/// TWO-FOR-ONE: both relic transitions satisfy their individual monotonicity and
/// provenance alphabets, while the counters honestly describe only ONE move.
/// Exact object↔projection binding is the only missing semantic tooth, and it
/// rejects the forged batch on the real executor.
#[test]
fn two_relics_behind_one_counter_delta_are_refused() {
    let mut d = Descent::deploy(4).expect("deploy");
    d.delve().expect("delve");
    d.smite().expect("slay guardian");
    let sim = d.sim().clone();
    let effects = vec![
        d.reg_effect("pack", 1),
        d.reg_effect("hoard_1", 2),
        d.reg_effect("spent", sim.spent + 1),
        d.relic_effect(1, CARRIED),
        d.relic_effect(4, CARRIED),
    ];
    assert!(
        refused(d.commit_raw(LOOT, effects)),
        "two custody moves cannot hide behind one pack/hoard delta"
    );
    assert_eq!(d.read_reg("pack"), 0);
    assert_eq!(d.read_relic(1), 1);
    assert_eq!(d.read_relic(4), 1);
}

/// Mutation canary: evaluate the identical forged post-state against (a) the
/// loaded Lean program and (b) a copy with only `FieldsCountEquals` removed.
/// The verdict flips refuse→admit, proving the new aggregate is load-bearing
/// rather than accidentally shadowed by conservation or per-relic ratchets.
#[test]
fn deleting_projection_census_reopens_two_for_one_attack() {
    let dep = Deployment::new();
    let old_sim = Sim::genesis()
        .delve()
        .expect("legal delve")
        .smite()
        .expect("legal smite");
    let mut forged_sim = old_sim.clone();
    forged_sim.spent += 1;
    forged_sim.custody[1] = CARRIED;
    forged_sim.custody[4] = CARRIED;

    let old_state = evaluator_state(&dep, &old_sim);
    let mut forged_state = evaluator_state(&dep, &forged_sim);
    // Lie only in the compact projection: claim one move although two custody
    // objects advanced.  SumEquals and the loot frame still see a valid +1/-1.
    assert!(forged_state.set_field(
        dep.reg("pack") as usize,
        dregg_app_framework::field_from_u64(1),
    ));
    assert!(forged_state.set_field(
        dep.reg("hoard_1") as usize,
        dregg_app_framework::field_from_u64(2),
    ));
    let meta = TransitionMeta::new(symbol(LOOT), 0);

    let strong = dep.program();
    assert!(
        strong
            .evaluate_with_meta(&forged_state, Some(&old_state), None, &meta)
            .is_err(),
        "the Lean-loaded exact census refuses the forgery"
    );

    let mut weakened = strong.clone();
    let CellProgram::Cases(cases) = &mut weakened else {
        panic!("descent program must be Cases");
    };
    for case in cases {
        case.constraints
            .retain(|constraint| !matches!(constraint, StateConstraint::FieldsCountEquals { .. }));
    }
    weakened
        .evaluate_with_meta(&forged_state, Some(&old_state), None, &meta)
        .expect("removing only the census teeth reopens the two-for-one attack");
}

/// KEYLESS WAY: flipping `way_2` without the carried key-relic is refused — the
/// SlotChanged rider demands the exhibited key on EVERY verb.
#[test]
fn keyless_way_flip_is_refused_on_any_verb() {
    let mut d = Descent::deploy(3).expect("deploy");
    d.delve().expect("delve");
    let sim = d.sim().clone();
    for method in [UNLOCK, SMITE, LOOT, DELVE] {
        let effects = vec![
            d.reg_effect("way_2", 1),
            d.reg_effect("spent", sim.spent + 2),
        ];
        assert!(
            refused(d.commit_raw(method, effects)),
            "keyless way flip refused under {method}"
        );
    }
    assert_eq!(d.read_reg("way_2"), 0);
}

/// With the key genuinely CARRIED, the same way-flip is admitted — the rider tooth is
/// a key-exercise gate, not a blanket freeze (the non-vacuity pole of the rider).
#[test]
fn carried_key_opens_the_way() {
    let mut d = Descent::deploy(3).expect("deploy");
    d.delve().expect("delve");
    d.smite().expect("slay guardian 1");
    d.loot(1).expect("win the key to way 2");
    assert_eq!(d.read_relic(1), CARRIED);
    d.unlock(2)
        .expect("exercising the carried key opens the way");
    assert_eq!(d.read_reg("way_2"), 1);
}

/// STAPLE: a loot turn that ALSO descends is refused (the loot frame freezes depth;
/// the depth rider would demand the delve law on top).
#[test]
fn stapled_loot_plus_descend_is_refused() {
    let mut d = Descent::deploy(3).expect("deploy");
    d.delve().expect("delve");
    d.smite().expect("smite");
    let sim = d.sim().clone();
    let mut forged = sim.clone();
    forged.custody[1] = CARRIED; // the legitimate loot half…
    forged.spent += 1;
    forged.depth += 1; // …stapled to a descent.
    let effects = d.effects_for(&forged);
    assert!(refused(d.commit_raw(LOOT, effects)));
    assert_eq!(d.read_reg("depth"), 1);
}

/// TOMB: after banking, EVERY verb is refused (the run is a frozen tomb) — driven
/// twin of the Lean `banked_run_frozen` / `banked_tomb_refuses`.
#[test]
fn banked_tomb_is_frozen() {
    let mut d = Descent::deploy(3).expect("deploy");
    d.delve().expect("delve");
    d.flee().expect("bank the empty pack");
    assert_eq!(d.read_reg("fate"), 1);
    assert!(refused(d.delve()));
    assert!(refused(d.smite()));
    assert!(refused(d.flee()));
    // And a FORGED resurrection (write fate back to 0) is refused: fate transitions
    // are pinned to {0→0, 0→1}.
    let sim = d.sim().clone();
    let effects = vec![
        d.reg_effect("fate", 0),
        d.reg_effect("spent", sim.spent + 1),
    ];
    assert!(refused(d.commit_raw(DELVE, effects)), "no resurrection");
}

/// FAKE FLEE: banking while KEEPING the pack (fate flips but pack stays) is refused —
/// `pack' = 0` is the flee law, re-demanded by the fate rider.
#[test]
fn fake_flee_keeping_the_pack_is_refused() {
    let mut d = Descent::deploy(3).expect("deploy");
    d.delve().expect("delve");
    d.smite().expect("smite");
    d.loot(1).expect("loot the key");
    // ⚑ CLIMB OUT FIRST, so the refusal below is about the PACK and nothing else. Fleeing
    // from floor 1 is now refused by `FieldEquals{depth, 0}` too, and a test that let two
    // teeth answer at once would keep passing if the pack law were deleted.
    d.ascend().expect("the climb home");
    let sim = d.sim().clone();
    assert_eq!(sim.pack(), 1);
    assert_eq!(sim.depth, 0, "standing at the mouth");
    let mut forged = sim.clone();
    forged.fate = 1; // bank…
    forged.spent += 1; // …but never empty the pack (custody stays CARRIED).
    let effects = d.effects_for(&forged);
    assert!(refused(d.commit_raw(FLEE, effects)));
    assert_eq!(d.read_reg("fate"), 0);
    // …and the honest twin: the same turn WITH the pack emptied is admitted.
    let mut honest = sim.clone();
    honest.spent += 1;
    honest.fate = 1;
    for c in honest.custody.iter_mut() {
        if *c == CARRIED {
            *c = BANKED;
        }
    }
    let effects = d.effects_for(&honest);
    assert!(
        d.commit_raw(FLEE, effects).is_ok(),
        "a lawful bank at the mouth still lands — the test above is not vacuous"
    );
}

/// RELIC TELEPORT: moving a relic's custody floor→floor (code 1 → 2) is refused — the
/// provenance ratchet's `memberOf {home, CARRIED, BANKED}` admits no other floor.
#[test]
fn relic_teleport_is_refused() {
    let mut d = Descent::deploy(3).expect("deploy");
    d.delve().expect("delve");
    let sim = d.sim().clone();
    let effects = vec![
        d.relic_effect(4, 2), // treasure minted on floor 1 "moves" to floor 2
        d.reg_effect("hoard_1", sim.hoard_at(1) - 1),
        d.reg_effect("hoard_2", sim.hoard_at(2) + 1),
        d.reg_effect("wounds", sim.wounds + 1),
        d.reg_effect("spent", sim.spent + 2),
    ];
    assert!(refused(d.commit_raw(SMITE, effects)));
    assert_eq!(d.read_relic(4), 1);
}

/// GENESIS REPLAY: re-running the mint after deploy is refused — the sentinel one-shot
/// (`Equals 1 ∧ DeltaEquals 1`) is jointly unsatisfiable from `old = 1`. The universal
/// write-hatch is closed at the root.
#[test]
fn genesis_replay_is_refused() {
    let d = Descent::deploy(3).expect("deploy");
    let effects = d.effects_for(&Sim::genesis());
    assert!(refused(d.commit_raw(GENESIS, effects)));
}

/// UNKNOWN METHOD: a verb outside the six is default-denied even with lawful-looking
/// writes (the riders carry a method disjunct, so they cannot be ridden in from an
/// unknown method) — driven twin of the Lean `unknown_method_refused`.
#[test]
fn unknown_method_is_default_denied() {
    let mut d = Descent::deploy(3).expect("deploy");
    d.delve().expect("delve");
    let sim = d.sim().clone();
    let effects = vec![d.reg_effect("spent", sim.spent + 1)];
    assert!(refused(d.commit_raw("plunder", effects)));
}

/// CAPACITY ATTENUATION, driven: at floor 1 the pack may hold up to 7 (CAP − 1); a
/// forged loot pushing pack past the attenuated bound is refused even with a
/// conservation-consistent hoard debit.
#[test]
fn overpacking_past_attenuated_capacity_is_refused() {
    let mut d = Descent::deploy(3).expect("deploy");
    d.delve().expect("delve");
    d.smite().expect("smite");
    // Legally loot all three floor-1 relics (pack 3, depth 1 — well within CAP).
    d.loot(1).expect("key 2");
    d.loot(4).expect("treasure");
    d.loot(5).expect("treasure");
    let sim = d.sim().clone();
    // Forge: pack jumps to 8 with a "consistent" hoard debit — but 8 + 1 > CAP.
    let mut forged = sim.clone();
    forged.spent += 1;
    let effects: Vec<_> = d.effects_for(&forged).into_iter().collect();
    let mut effects = effects;
    effects.push(d.reg_effect("pack", 8));
    effects.push(d.reg_effect("hoard_2", 0));
    effects.push(d.reg_effect("hoard_3", 0));
    effects.push(d.reg_effect("hoard_4", 0));
    assert!(refused(d.commit_raw(LOOT, effects)));
}

/// THE LIGHT: burning breath past BREATH is refused (fieldLte spent) and every verb
/// must strictly spend (a free verb — spent unchanged — is refused too).
#[test]
fn the_clock_binds() {
    let mut d = Descent::deploy(3).expect("deploy");
    d.delve().expect("delve");
    let sim = d.sim().clone();
    // A free smite (no breath paid) is refused.
    let mut forged = sim.clone();
    forged.wounds += 1;
    let effects = d.effects_for(&forged);
    assert!(refused(d.commit_raw(SMITE, effects)), "no free exertion");
    // A clock jump past BREATH is refused.
    let mut forged = sim.clone();
    forged.wounds += 1;
    forged.spent = 27;
    let effects = d.effects_for(&forged);
    assert!(
        refused(d.commit_raw(SMITE, effects)),
        "the light caps at 26"
    );
}

// =============================================================================
// THE LUNGE — the second blow, driven on the real executor.
// =============================================================================

/// THE TRADE IS REAL, ON THE DEPLOYED TEETH. The same wound, one breath cheaper, and the
/// `harm` register moves — through the loaded artifact (which had to grow a register, a
/// verb arm and an anti-staple rider for this turn to be admissible at all).
#[test]
fn a_lunge_buys_a_breath_and_the_executor_records_the_broken_grip() {
    let mut pressed = Descent::deploy(11).expect("deploy");
    pressed.delve().expect("way 1 is always open");
    pressed.smite().expect("the press");
    assert_eq!(pressed.read_reg("spent"), 3, "delve 1 + press 2");
    assert_eq!(pressed.read_reg("harm"), 0, "the press breaks no grip");

    let mut lunged = Descent::deploy(11).expect("deploy");
    lunged.delve().expect("way 1 is always open");
    lunged.lunge().expect("the lunge");
    assert_eq!(lunged.read_reg("spent"), 2, "delve 1 + lunge 1");
    assert_eq!(lunged.read_reg("wounds"), 1, "the same wound");
    assert_eq!(lunged.read_reg("harm"), 1, "one carry slot forfeit");
    // …and the wound it bought is real: the guardian is slain, so the loot admits.
    lunged
        .loot(1)
        .expect("the key lies here and the guardian is down");
    assert_eq!(lunged.read_reg("pack"), 1);
}

/// ⚑ ANTI-STAPLE, ON THE DEPLOYED TEETH. The `harm` slot cannot be moved under another
/// verb's method to buy the lunge's discount: a `smite`-shaped turn that pays 1 breath
/// and writes `harm += 1` is a REAL executor refusal that commits nothing. This is the
/// standing stapleable-slot falsifier aimed at the new register (`smite` freezes `harm`,
/// and the `harmRider` re-demands the whole lunge law method-independently).
#[test]
fn harm_stapled_onto_a_press_is_refused_and_commits_nothing() {
    let mut d = Descent::deploy(12).expect("deploy");
    d.delve().expect("way 1 is always open");
    let before = d.sim().clone();

    let mut forged = before.clone();
    forged.wounds += 1;
    forged.spent += 1;
    forged.harm += 1;
    let effects = d.effects_for(&forged);
    assert!(
        refused(d.commit_raw(SMITE, effects)),
        "harm stapled onto the press is refused by the Lean-sourced teeth"
    );
    assert_eq!(
        d.read_reg("harm"),
        before.harm,
        "anti-ghost: no grip broken"
    );
    assert_eq!(
        d.read_reg("spent"),
        before.spent,
        "anti-ghost: no breath spent"
    );

    // The honest twin: the SAME write set under `lunge` commits.
    let effects = d.effects_for(&forged);
    d.commit_raw(LUNGE, effects)
        .expect("the honest lunge commits");
    assert_eq!(d.read_reg("harm"), before.harm + 1);
}

/// THE RATCHET RUNS ONE WAY AND HAS A CEILING, ON THE DEPLOYED TEETH.
///
/// The third lunge here is on a FRESH floor (`delve` resets `wounds`, so the guardian
/// tooth is satisfied) and inside capacity (`pack 2 + depth 2 + harm 3 = 7 <= CAP`), so
/// the only thing left to refuse it is the `[0, HARMCAP]` ratchet — this isolates the
/// ceiling rather than re-testing the guardian.
#[test]
fn the_grip_never_heals_and_the_ratchet_has_a_ceiling() {
    // Day 9 is `ghp = [0, 2, 2, 2, 2]`, `homes = [4, 1, 1, 2, 1, 2, 3, 4]` — both way-2
    // keys lie on floor 1 and every guardian takes two blows.
    let mut d = Descent::deploy_on_world(
        5,
        dungeon_on_dregg::descent::day_seed_from_deploy_seed(5),
        9,
    )
    .expect("deploy on day 9");
    d.delve().expect("way 1 is always open");
    d.lunge().expect("first lunge");
    d.lunge().expect("second lunge");
    assert_eq!(d.read_reg("harm"), HARMCAP, "the ratchet is at its ceiling");
    assert_eq!(d.read_reg("wounds"), 2, "the guardian is down");
    d.loot(1).expect("the way-2 key");
    d.loot(2).expect("the way-3 key");
    d.unlock(2).expect("exercise it");
    d.delve().expect("floor 2, a fresh guardian");
    assert_eq!(d.read_reg("wounds"), 0, "wounds reset");
    assert_eq!(
        d.read_reg("harm"),
        HARMCAP,
        "harm does NOT reset — it is run-long"
    );

    // A third lunge would be harm 3. The guardian is fresh and capacity is fine, so the
    // ratchet's ceiling is the only thing refusing it — the mover and the executor agree.
    assert!(d.sim().lunge().is_err(), "the mover refuses a third lunge");
    let before = d.sim().clone();
    let mut over = before.clone();
    over.wounds += 1;
    over.spent += 1;
    over.harm += 1;
    let effects = d.effects_for(&over);
    assert!(
        refused(d.commit_raw(LUNGE, effects)),
        "harm past the ratchet's ceiling is refused"
    );

    // Healing is refused too: `fieldDelta harm 1` is an exact step, not a bound.
    let mut healed = before.clone();
    healed.harm -= 1;
    healed.wounds += 1;
    healed.spent += 1;
    let effects = d.effects_for(&healed);
    assert!(
        refused(d.commit_raw(LUNGE, effects)),
        "a grip that heals is refused"
    );
    assert_eq!(d.read_reg("harm"), HARMCAP, "anti-ghost: the ratchet held");
}

/// ⚑ THE STAKE, DRIVEN: `Dungeon.crowned_full_bank_harmless` says a run that banks the
/// prize AND all three keys took no harm at all. Here is the executor's half of it — the
/// crowned line with ONE breath saved by a lunge on floor 1 cannot take the prize,
/// because at depth 4 capacity is `CAP - FLOORS - harm` and the prize needs all of it.
#[test]
fn one_lunge_forfeits_the_crown() {
    let mut d = Descent::deploy(7).expect("deploy");
    d.delve().expect("floor 1");
    d.lunge().expect("save a breath on the shallow guardian");
    d.loot(1).expect("the way-2 key");
    d.unlock(2).expect("exercise it");
    d.delve().expect("floor 2");
    d.smite().expect("press");
    d.loot(2).expect("the way-3 key");
    d.unlock(3).expect("exercise it");
    d.delve().expect("floor 3");
    d.smite().expect("press");
    d.smite().expect("press");
    d.loot(3).expect("the way-4 key");
    d.unlock(4).expect("exercise it");
    d.delve().expect("the bottom");
    d.smite().expect("press");
    d.smite().expect("press");
    assert_eq!(d.read_reg("pack"), 3, "three keys");
    assert_eq!(d.read_reg("harm"), 1, "one broken grip");
    // pack 3 + 1 + depth 4 + harm 1 = 9 > CAP = 8.
    assert!(
        d.sim().loot(0).is_err(),
        "the prize does not fit beside a broken grip"
    );
    // And the executor refuses the forged projection too.
    let mut forged = d.sim().clone();
    forged.custody[0] = CARRIED;
    forged.spent += 1;
    let effects = d.effects_for(&forged);
    assert!(
        refused(d.commit_raw(LOOT, effects)),
        "the capacity commons refuse the crowned loot at harm = 1"
    );
}
