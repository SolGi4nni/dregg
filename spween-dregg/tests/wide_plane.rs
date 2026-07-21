//! **THE 16-SLOT LIMIT IS NOT REAL** — a scene needing more than 16 story variables
//! compiles, deploys, and keeps every tooth.
//!
//! The compiler used to HARD-FAIL a wide scene (`CompileError::TooManySlots`) while the
//! architecture underneath carried unbounded keys already: `Effect::SetField { index >=
//! STATE_SLOTS }` routes into the cell's committed `fields_map` / `fields_root` (an
//! openable sorted-Poseidon2 root folded into the cell commitment), and that plane is
//! CONSTRAINABLE — `HeapField { key, atom }` and `HeapFieldLteOther` are executor teeth.
//! The knowledge was in-tree; the compiler never learned it. It has now: past the 16
//! registers a var SPILLS to an ext key and its gates lower to the ext-plane twins.
//!
//! These tests DRIVE that, against the real `EmbeddedExecutor`:
//!
//! 1. a >16-variable scene COMPILES and DEPLOYS (was `TooManySlots`);
//! 2. the layout is the deterministic one: 15 registers filled first, the rest spilled,
//!    resolved BY NAME (never by a guessed index);
//! 3. a spilled var ROUND-TRIPS through real turns, and the committed `fields_root`
//!    MOVES when it does;
//! 4. every gate class still BITES on a spilled var — the plain comparison, the
//!    clamp-defeat exact-delta companion, the cross-var relation, and membership — each
//!    driven to a real `WorldError::Refused` with the illegal move committing NOTHING;
//! 5. the `<= 16` path is UNCHANGED (no ext key, no ext tooth, same layout);
//! 6. the heap hatch cannot reach a spilled var (the confinement widened with the story).
//!
//! ## What is honest about a spilled gate
//!
//! An ext-plane tooth is EXECUTOR-enforced, not in-circuit-proven: the slot-caveat PI
//! vector cannot express a heap key, so `HeapField`/`HeapFieldLteOther` are evaluated by
//! the host scalar evaluator (`turn/src/executor/mod.rs` names this boundary rather than
//! hiding it), while a register `FieldGte` DOES project into the AIR. Every refusal
//! below is the real executor refusing a real signed turn — which is what an
//! executor-refereed game runs on — and none of it is a claim of in-circuit proving.

use dregg_app_framework::{
    CellProgram, Effect, StateConstraint, TransitionGuard, field_from_u64, symbol,
};
use dregg_cell::program::HeapAtom;
use spween_dregg::{
    CompiledStory, Driver, GENESIS_DONE_EXT_KEY, HEAP_HATCH_METHOD, SPILL_EXT_BASE, STATE_SLOTS,
    Value, WorldCell, WorldError, choice_method, compile_scene, parse, verify,
};

/// **A scene far wider than the register file.** 15 `r*` vars sort before every `z_*`
/// var, so they fill slots 1..15 exactly and EVERY `z_*` var — plus the membership atom
/// (allocated after the vars) — spills to the ext plane. That makes the interesting
/// gates land on spilled state by construction, without any index being written down.
///
/// The gates, one per class the compiler lowers:
/// * `{ z_seal >= 5 }` — a plain comparison on an untouched spilled var (`d = 0`);
/// * `{ z_gold >= 50 } ~ z_gold -= 50` — the CLAMP-DEFEATED lift, which needs the
///   exact-delta companion or a broke buyer's purse silently clamps to zero and commits;
/// * `{ z_gold >= "$z_price" }` — cross-var, BOTH operands spilled;
/// * `{ r01 >= "$z_price" }` — cross-var ACROSS the planes (a register against an ext key);
/// * `{ relics.sigil }` — a spilled membership atom;
/// * `{ z_weary <= 0 }` on an UNSEEDED var — the plane-parity gate: a register is born
///   present-at-zero and admits this, so a spilled var must too.
const WIDE_VAULT: &str = r#"---
id: wide-vault
title: The Wide Vault
weight: 1
---

=== hall

~ r01 = 40
~ r02 = 2
~ r03 = 3
~ r04 = 4
~ r05 = 5
~ r06 = 6
~ r07 = 7
~ r08 = 8
~ r09 = 9
~ r10 = 10
~ r11 = 11
~ r12 = 12
~ r13 = 13
~ r14 = 14
~ r15 = 15
~ z_price = 30

The vault door is banded with seals.

* [Break the seal] { z_seal >= 5 }
  ~ z_broken = 1
  -> END

* [Buy passage] { z_gold >= 50 }
  ~ z_gold -= 50
  ~ z_bought = 1
  -> END

* [Pay the named toll] { z_gold >= "$z_price" }
  ~ z_paid = 1
  -> END

* [Show the ledger] { r01 >= "$z_price" }
  ~ z_shown = 1
  -> END

* [Present the sigil] { relics.sigil }
  ~ z_sigiled = 1
  -> END

* [Rest, unweary] { z_weary <= 0 }
  ~ z_rested = 1
  -> END
"#;

/// A scene that FITS the register file (3 vars) — the unchanged narrow path.
const NARROW: &str = r#"---
id: narrow
title: The Narrow Door
weight: 1
---

=== gate

The door is stuck.

* [Force it open] { strength >= 4 }
  ~ strength -= 1
  -> END
"#;

fn scene(src: &str, name: &str) -> spween::Scene {
    parse(src, name).expect("scene parses")
}

fn wide() -> spween::Scene {
    scene(WIDE_VAULT, "wide-vault.scene")
}

/// The `idx`-th choice in `passage` (the same order `apply_choice`'s index selects).
fn nth_choice(scene: &spween::Scene, passage: &str, idx: usize) -> spween::Choice {
    let p = scene
        .passages
        .iter()
        .find(|p| p.name.as_str() == passage)
        .expect("passage exists");
    p.content
        .iter()
        .filter_map(|c| match c {
            spween::PassageContent::Choice(ch) => Some(ch),
            _ => None,
        })
        .nth(idx)
        .cloned()
        .expect("choice exists")
}

/// The constraints installed for a choice's gate case, found BY METHOD.
fn case_constraints(story: &CompiledStory, passage: &str, choice: usize) -> Vec<StateConstraint> {
    constraints_for(story, &choice_method(passage, choice))
}

fn constraints_for(story: &CompiledStory, method: &str) -> Vec<StateConstraint> {
    let CellProgram::Cases(cases) = &story.program else {
        panic!("program is Cases");
    };
    let want = symbol(method);
    cases
        .iter()
        .find(|c| matches!(&c.guard, TransitionGuard::MethodIs { method: m } if *m == want))
        .map(|c| c.constraints.clone())
        .expect("a case for the method")
}

// The choice indices in `hall`, named once.
const BREAK_SEAL: usize = 0;
const BUY_PASSAGE: usize = 1;
const PAY_TOLL: usize = 2;
const SHOW_LEDGER: usize = 3;
const PRESENT_SIGIL: usize = 4;
const REST: usize = 5;

// ─────────────────────────────────────────────────────────────────────────────
// 1. It COMPILES — and lays out the two planes deterministically.
// ─────────────────────────────────────────────────────────────────────────────

/// THE headline: the scene that used to be `CompileError::TooManySlots` compiles.
#[test]
fn a_scene_wider_than_the_register_file_compiles() {
    let s = wide();
    let story = compile_scene(&s).expect("a >16-variable scene COMPILES (was TooManySlots)");

    // Genuinely wider than the cell's fixed budget — this is not a scene that squeaked in.
    let named = story.var_slots.len() + story.has_slots.len();
    assert!(
        named > STATE_SLOTS,
        "the scene must name MORE atoms than the register file has slots; named {named}"
    );
    assert!(
        !story.ext_keys().is_empty(),
        "a wide scene spills to the ext plane"
    );
}

/// The layout: the fast fixed registers are filled FIRST (slot 0 the passage, then the
/// 15 alphabetically-earliest atoms), and only the overflow spills. Resolved by name.
#[test]
fn the_first_sixteen_stay_in_registers_and_the_rest_spill() {
    let story = compile_scene(&wide()).expect("compiles");

    // The 15 `r*` vars sort first, so they occupy exactly slots 1..=15 — the whole
    // register file below the passage slot. Cheap plane first.
    let mut registers: Vec<u64> = (1..=15)
        .map(|i| {
            let name = format!("r{i:02}");
            story
                .var_key(&name)
                .unwrap_or_else(|| panic!("{name} has a key"))
        })
        .collect();
    registers.sort_unstable();
    assert_eq!(
        registers,
        (1..=15).collect::<Vec<u64>>(),
        "the 15 earliest vars fill the fixed registers 1..=15"
    );
    for i in 1..=15u64 {
        assert!(
            !story.is_spilled(&format!("r{i:02}")),
            "a register var is not spilled"
        );
    }

    // Everything past the register file spilled to the ext plane, and the ext keys are
    // the contiguous deterministic run from SPILL_EXT_BASE.
    for name in [
        "z_bought", "z_broken", "z_gold", "z_paid", "z_price", "z_seal", "z_weary",
    ] {
        let key = story.var_key(name).unwrap_or_else(|| panic!("{name} key"));
        assert!(story.is_spilled(name), "{name} spilled");
        assert!(
            key >= SPILL_EXT_BASE,
            "{name} spilled to the ext plane; got {key}"
        );
        // The ext plane is what the executor routes on (>= STATE_SLOTS), which is
        // exactly what makes the write land in the committed fields_map.
        assert!(key >= STATE_SLOTS as u64);
    }
    let keys = story.ext_keys();
    let expected: Vec<u64> = (0..keys.len() as u64).map(|i| SPILL_EXT_BASE + i).collect();
    assert_eq!(
        keys, expected,
        "the spill is the contiguous deterministic run from SPILL_EXT_BASE"
    );

    // The membership atom is allocated after the vars, so it spills too.
    let sigil = story.has_key("relics", "sigil").expect("sigil key");
    assert!(sigil >= SPILL_EXT_BASE, "the membership atom spilled");
}

/// **Resolve BY NAME, never by a guessed index.** The name→key mapping is the contract;
/// a hardcoded index that is right for a narrow scene names the WRONG atom in a wide
/// one. This pins the mapping's two directions: every name resolves to a DISTINCT key
/// (no collision, no aliasing), and the key a name resolves to is the key the world
/// actually reads and writes for that name.
#[test]
fn the_name_to_key_mapping_resolves_and_never_collides() {
    let story = compile_scene(&wide()).expect("compiles");

    // Injective: no two names share a key, across BOTH maps and BOTH planes. (A
    // collision would silently alias two story vars onto one field — the failure mode
    // the old `TooManySlots` guard existed to prevent.)
    let mut all: Vec<u64> = story
        .var_slots
        .values()
        .chain(story.has_slots.values())
        .map(|&k| k as u64)
        .collect();
    all.push(spween_dregg::PASSAGE_SLOT as u64);
    let count = all.len();
    all.sort_unstable();
    all.dedup();
    assert_eq!(
        all.len(),
        count,
        "every compiled name (and the passage slot) has its OWN key — no aliasing"
    );

    // An unknown name resolves to nothing rather than to a plausible-looking index.
    assert_eq!(story.var_key("no_such_var"), None);
    assert!(!story.is_spilled("no_such_var"));

    // The mapping is the one the world uses: seed by NAME, read the raw KEY back off
    // the committed cell, and they agree — on the ext plane, where a guessed index
    // would silently read a register instead.
    let mut world = WorldCell::deploy(&wide(), 70).expect("deploy");
    world.seed_var("z_seal", Value::Int(9));
    let seal_key = story.var_key("z_seal").expect("z_seal key");
    assert_eq!(
        world.read_heap(seal_key),
        Some(9),
        "the key the NAME resolves to is the key holding the value"
    );
    assert_eq!(world.read_var("z_seal"), 9, "and the by-name read agrees");
}

// ─────────────────────────────────────────────────────────────────────────────
// 2. The lowering: a spilled var's gates become the ext-plane twins.
// ─────────────────────────────────────────────────────────────────────────────

/// The gate teeth for spilled vars are REAL ext-plane constraints — not a dropped
/// clause, not a handler courtesy. Every gate in the wide scene lowered FULLY.
#[test]
fn spilled_gates_lower_to_ext_plane_teeth() {
    let story = compile_scene(&wide()).expect("compiles");
    let seal = story.var_key("z_seal").expect("z_seal");
    let gold = story.var_key("z_gold").expect("z_gold");
    let price = story.var_key("z_price").expect("z_price");
    let r01 = story.var_key("r01").expect("r01");
    let sigil = story.has_key("relics", "sigil").expect("sigil");

    // `{ z_seal >= 5 }`, untouched by the choice ⇒ a bare HeapField{Gte(5)} — the exact
    // twin of the FieldGte a register var would have gotten, same threshold.
    let brk = case_constraints(&story, "hall", BREAK_SEAL);
    assert!(
        brk.iter().any(|c| matches!(c,
            StateConstraint::HeapField { key, atom: HeapAtom::Gte { value } }
                if *key == seal && *value == field_from_u64(5))),
        "the spilled comparison lowers to HeapField{{Gte}}; got {brk:?}"
    );
    assert!(
        !brk.iter().any(|c| matches!(
            c,
            StateConstraint::HeapField {
                atom: HeapAtom::DeltaEquals { .. },
                ..
            }
        )),
        "an UNTOUCHED spilled var gets no exact-delta companion (the lift is already \
         exact — the register rule, preserved); got {brk:?}"
    );

    // `{ z_gold >= 50 } ~ z_gold -= 50`: the lift collapses to `>= 0` (vacuous under the
    // executor's clamp-at-zero) — so it MUST carry the exact-delta companion, the ext
    // twin of FieldDelta. Without it a broke buyer's purse clamps to 0 and commits.
    let buy = case_constraints(&story, "hall", BUY_PASSAGE);
    assert!(
        buy.iter().any(|c| matches!(c,
            StateConstraint::HeapField { key, atom: HeapAtom::DeltaEquals { d } }
                if *key == gold && *d == -50)),
        "the clamp-defeated spilled gate carries HeapField{{DeltaEquals(-50)}}; got {buy:?}"
    );

    // `{ z_gold >= "$z_price" }`, both spilled ⇒ the cross-KEY relation.
    let toll = case_constraints(&story, "hall", PAY_TOLL);
    assert!(
        toll.iter().any(|c| matches!(c,
            StateConstraint::HeapFieldLteOther { key, other_key, delta }
                if *key == price && *other_key == gold && *delta == 0)),
        "a both-spilled cross-var gate lowers to HeapFieldLteOther; got {toll:?}"
    );

    // `{ r01 >= "$z_price" }` — a REGISTER against an EXT key. `get_field_ext` resolves
    // a key < STATE_SLOTS to the register file, so one tooth spans both planes.
    let ledger = case_constraints(&story, "hall", SHOW_LEDGER);
    assert!(
        ledger.iter().any(|c| matches!(c,
            StateConstraint::HeapFieldLteOther { key, other_key, delta }
                if *key == price && *other_key == r01 && *delta == 0)),
        "a MIXED-plane cross-var gate is one HeapFieldLteOther over both keys; got {ledger:?}"
    );

    // The spilled membership atom.
    let sig = case_constraints(&story, "hall", PRESENT_SIGIL);
    assert!(
        sig.iter().any(|c| matches!(c,
            StateConstraint::HeapField { key, atom: HeapAtom::Equals { value } }
                if *key == sigil && *value == field_from_u64(1))),
        "a spilled membership atom lowers to HeapField{{Equals(1)}}; got {sig:?}"
    );

    // NO tooth was silently dropped: every gate in the wide scene is FULLY lowered to
    // executor constraints, exactly as its register twin would be.
    for (name, idx) in [
        ("break", BREAK_SEAL),
        ("buy", BUY_PASSAGE),
        ("toll", PAY_TOLL),
        ("ledger", SHOW_LEDGER),
        ("sigil", PRESENT_SIGIL),
    ] {
        assert_eq!(
            story.fully_gated.get(&choice_method("hall", idx)),
            Some(&true),
            "the {name} gate lowered FULLY to executor teeth — no handler lean"
        );
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// 3. It DEPLOYS, and a spilled var round-trips through real turns.
// ─────────────────────────────────────────────────────────────────────────────

/// The wide scene deploys onto a real world-cell, and a spilled var round-trips:
/// seed → read; then a real committed TURN writes it and the committed `fields_root`
/// MOVES — the overflow is genuine committed state, folded into the cell commitment,
/// not a side table.
#[test]
fn a_spilled_var_round_trips_through_a_real_turn_and_moves_the_committed_root() {
    let s = wide();
    let story = compile_scene(&s).expect("compiles");
    let mut world = WorldCell::deploy(&s, 71).expect("a wide scene DEPLOYS");

    // Every compiled ext key is BORN present-at-zero, exactly like a register — so a
    // spilled var reads zero rather than absent (an absent key refuses every gate).
    for key in story.ext_keys() {
        assert_eq!(
            world.read_heap(key),
            Some(0),
            "ext key {key} is born present-at-field-zero on deploy"
        );
    }

    // Seed → read, by name, on the ext plane.
    world.seed_var("z_seal", Value::Int(7));
    assert_eq!(world.read_var("z_seal"), 7, "seeded spilled var reads back");

    let root_before = world.fields_root();
    let passage_before = world.read_passage();

    // A real, signed, executor-admitted TURN whose effect writes a spilled var.
    let brk = nth_choice(&s, "hall", BREAK_SEAL);
    let receipt = world
        .apply_choice("hall", BREAK_SEAL, &brk)
        .expect("the eligible spilled-gate choice COMMITS");
    assert_ne!(receipt.turn_hash, [0u8; 32], "a genuine committed turn");

    // Write → read: the effect landed on the ext plane.
    assert_eq!(
        world.read_var("z_broken"),
        1,
        "the turn's effect wrote the spilled var"
    );
    assert_ne!(world.read_passage(), passage_before, "the story advanced");

    // ...and the COMMITTED root moved. `fields_root` is folded into the cell's canonical
    // state commitment, so this is the overflow state being bound by the receipt chain.
    assert_ne!(
        world.fields_root(),
        root_before,
        "writing a spilled var MOVES the committed fields_root"
    );

    // The snapshot fingerprint covers the ext plane: registers, then the ext tail. A
    // registers-only fingerprint would let a wide playthrough diverge in its spilled
    // state and still 'reproduce' on replay.
    let snap = world.snapshot();
    assert_eq!(
        snap.len(),
        STATE_SLOTS + story.ext_keys().len(),
        "the replay fingerprint = 16 registers + every ext key"
    );
    let broken_at = story
        .ext_keys()
        .iter()
        .position(|&k| k == story.var_key("z_broken").unwrap())
        .expect("z_broken is an ext key");
    assert_eq!(
        snap[STATE_SLOTS + broken_at],
        1,
        "the spilled var's value is IN the fingerprint"
    );
}

/// A full wide playthrough re-verifies: the receipt chain links and a fresh,
/// identically-seeded world reproduces the committed state — INCLUDING the ext plane —
/// through the stock `spween::Runtime`.
#[test]
fn a_wide_playthrough_reverifies_through_the_stock_runtime() {
    let s = wide();
    let seed = 72;

    let mut world = WorldCell::deploy(&s, seed).expect("deploy");
    world.seed_var("z_seal", Value::Int(9));
    let mut driver = Driver::start(world, &s).expect("start");
    driver.advance(BREAK_SEAL).expect("break the seal");
    let play = driver.playthrough();
    assert_eq!(play.steps.len(), 1);

    let mut fresh = WorldCell::deploy(&s, seed).expect("redeploy");
    fresh.seed_var("z_seal", Value::Int(9));
    verify(fresh, &s, &play).expect("a wide playthrough re-verifies, ext plane and all");
}

// ─────────────────────────────────────────────────────────────────────────────
// 4. THE TEETH: a gate on a spilled var BITES, non-vacuously.
// ─────────────────────────────────────────────────────────────────────────────

/// **The plain comparison bites.** The illegal move is REFUSED by the real executor
/// exactly as it would be on a register — and the same line COMMITS when eligible, so
/// the refusal is the gate discriminating, not the turn being broken.
#[test]
fn a_gate_on_a_spilled_var_refuses_the_ineligible_move() {
    let s = wide();
    let brk = nth_choice(&s, "hall", BREAK_SEAL);

    // seal = 2 < 5: REFUSED. (A directly-submitted choice-turn — the kernel predicate
    // biting on the ext plane, no runtime involved.)
    let mut weak = WorldCell::deploy(&s, 73).expect("deploy");
    weak.seed_var("z_seal", Value::Int(2));
    let root_before = weak.fields_root();
    let refused = weak.apply_choice("hall", BREAK_SEAL, &brk);
    assert!(
        matches!(refused, Err(WorldError::Refused(_))),
        "an ineligible gate on a SPILLED var is refused in-band; got {refused:?}"
    );
    // Anti-ghost: nothing committed — not the effect, not the passage, not the root.
    assert_eq!(weak.read_var("z_broken"), 0, "the effect did not land");
    assert_eq!(weak.read_var("z_seal"), 2, "the seal is untouched");
    assert_eq!(weak.read_passage(), Some(0), "still in the hall");
    assert_eq!(
        weak.fields_root(),
        root_before,
        "the committed root did not move"
    );

    // seal = 7 >= 5: the SAME choice COMMITS. The gate discriminates.
    let mut strong = WorldCell::deploy(&s, 74).expect("deploy");
    strong.seed_var("z_seal", Value::Int(7));
    strong
        .apply_choice("hall", BREAK_SEAL, &brk)
        .expect("an eligible spilled gate commits");
    assert_eq!(strong.read_var("z_broken"), 1);
}

/// **The clamp companion bites on the ext plane.** `{ z_gold >= 50 } ~ z_gold -= 50`
/// lifts to a VACUOUS `>= 0` — the executor clamps a Modify at zero, so without the
/// exact-delta companion a broke buyer's purse clamps to 0, passes `0 >= 0`, and the
/// goods commit. `HeapField{DeltaEquals(-50)}` sees `0 - 30 != -50` and REFUSES. This is
/// the same tooth `FieldDelta` is on a register — carried across the plane.
#[test]
fn the_clamp_defeat_companion_bites_on_a_spilled_purse() {
    let s = wide();
    let buy = nth_choice(&s, "hall", BUY_PASSAGE);

    // BROKE (gold 30, price 50). Non-vacuity of the companion IS this refusal: the
    // comparison alone admits here.
    let mut broke = WorldCell::deploy(&s, 75).expect("deploy");
    broke.seed_var("z_gold", Value::Int(30));
    let refused = broke.apply_choice("hall", BUY_PASSAGE, &buy);
    assert!(
        matches!(refused, Err(WorldError::Refused(_))),
        "a broke buyer's SPILLED purse is REFUSED, not a clamped commit; got {refused:?}"
    );
    assert_eq!(broke.read_var("z_gold"), 30, "anti-ghost: purse untouched");
    assert_eq!(broke.read_var("z_bought"), 0, "no goods delivered");

    // SOLVENT (gold 80): commits, paying EXACTLY the price.
    let mut rich = WorldCell::deploy(&s, 76).expect("deploy");
    rich.seed_var("z_gold", Value::Int(80));
    rich.apply_choice("hall", BUY_PASSAGE, &buy)
        .expect("a solvent buyer commits");
    assert_eq!(rich.read_var("z_gold"), 30, "paid exactly 50");
    assert_eq!(rich.read_var("z_bought"), 1);

    // The LAST COIN (gold exactly 50) commits to zero — the gate is `>= 50`, not `> 50`.
    let mut exact = WorldCell::deploy(&s, 77).expect("deploy");
    exact.seed_var("z_gold", Value::Int(50));
    exact
        .apply_choice("hall", BUY_PASSAGE, &buy)
        .expect("the last coin commits");
    assert_eq!(exact.read_var("z_gold"), 0);
}

/// **The cross-var relation bites with BOTH operands spilled** — `HeapFieldLteOther`
/// over two ext keys, refusing a buyer below a dynamic price the scene sets at runtime.
#[test]
fn a_cross_var_gate_between_two_spilled_vars_bites() {
    let s = wide();
    let toll = nth_choice(&s, "hall", PAY_TOLL);

    // The scene's entry effect sets `z_price = 30`, so it must be committed before the
    // relation can discriminate — drive the genesis turn, then submit the choice.
    let mut broke = WorldCell::deploy(&s, 78).expect("deploy");
    broke.seed_var("z_gold", Value::Int(10));
    let broke = Driver::start(broke, &s).expect("genesis").finish().0;
    assert_eq!(broke.read_var("z_price"), 30, "the world named its price");
    let refused = broke.apply_choice("hall", PAY_TOLL, &toll);
    assert!(
        matches!(refused, Err(WorldError::Refused(_))),
        "gold 10 < price 30 (both SPILLED) is refused; got {refused:?}"
    );
    assert_eq!(broke.read_var("z_paid"), 0, "anti-ghost");

    // Above the price: the SAME choice commits.
    let mut flush = WorldCell::deploy(&s, 79).expect("deploy");
    flush.seed_var("z_gold", Value::Int(45));
    let flush = Driver::start(flush, &s).expect("genesis").finish().0;
    flush
        .apply_choice("hall", PAY_TOLL, &toll)
        .expect("gold 45 >= price 30 commits");
    assert_eq!(flush.read_var("z_paid"), 1);
}

/// **The MIXED-plane cross-var gate bites**: `{ r01 >= "$z_price" }` compares a fixed
/// REGISTER to a spilled EXT key in one tooth. Driven both ways.
#[test]
fn a_cross_var_gate_across_the_planes_bites() {
    let s = wide();
    let ledger = nth_choice(&s, "hall", SHOW_LEDGER);

    // The scene sets r01 = 40 and z_price = 30 at entry ⇒ 40 >= 30 admits.
    let world = WorldCell::deploy(&s, 80).expect("deploy");
    let world = Driver::start(world, &s).expect("genesis").finish().0;
    assert_eq!(world.read_var("r01"), 40, "the register operand");
    assert_eq!(world.read_var("z_price"), 30, "the spilled operand");
    world
        .apply_choice("hall", SHOW_LEDGER, &ledger)
        .expect("register 40 >= ext 30 commits");
    assert_eq!(world.read_var("z_shown"), 1);

    // Re-seed the SPILLED operand above the register one: the same line is REFUSED. The
    // tooth genuinely reads the ext key — it is not passing on the register alone.
    let dear = WorldCell::deploy(&s, 81).expect("deploy");
    let mut dear = Driver::start(dear, &s).expect("genesis").finish().0;
    dear.seed_var("z_price", Value::Int(99));
    let refused = dear.apply_choice("hall", SHOW_LEDGER, &ledger);
    assert!(
        matches!(refused, Err(WorldError::Refused(_))),
        "register 40 < ext price 99 is refused; got {refused:?}"
    );
    assert_eq!(dear.read_var("z_shown"), 0, "anti-ghost");
}

/// **The spilled membership atom bites**: absent ⇒ refused, seeded ⇒ commits.
#[test]
fn a_spilled_membership_gate_bites() {
    let s = wide();
    let sigil = nth_choice(&s, "hall", PRESENT_SIGIL);

    // No sigil: the atom reads present-at-ZERO (born on deploy) and the Equals(1) tooth
    // REFUSES — the same refusal a register membership atom gives.
    let without = WorldCell::deploy(&s, 82).expect("deploy");
    let refused = without.apply_choice("hall", PRESENT_SIGIL, &sigil);
    assert!(
        matches!(refused, Err(WorldError::Refused(_))),
        "an unheld SPILLED membership atom refuses; got {refused:?}"
    );
    assert_eq!(without.read_var("z_sigiled"), 0, "anti-ghost");

    // Holding it: the same choice commits.
    let mut with = WorldCell::deploy(&s, 83).expect("deploy");
    with.seed_membership("relics", "sigil");
    assert!(with.read_membership("relics", "sigil"));
    with.apply_choice("hall", PRESENT_SIGIL, &sigil)
        .expect("the held membership commits");
    assert_eq!(with.read_var("z_sigiled"), 1);
}

/// **Plane parity on an UNSEEDED var — the gate that must NOT bite.** Every test above
/// drives a refusal; this one drives the opposite direction, where the ext plane's own
/// semantics fight the register's.
///
/// On the heap, **absent ≠ present-zero**: a `HeapField` over a never-written key
/// REFUSES. A register is born present-at-field-zero, so `{ z_weary <= 0 }` on a var
/// nobody ever wrote ADMITS there — and the stock runtime's read model agrees (an
/// unwritten compiled var reads `Int(0)`). Left alone, a spilled var would REFUSE the
/// gate its register twin admits: an honest player blocked, and a play-vs-replay split
/// that fails `verify_by_replay` on a legitimate run. `WorldCell` births every compiled
/// ext key at field-zero on deploy precisely so the two planes agree here.
///
/// So this is the falsifier for the birth: it is a gate that PASSES, and it stops
/// passing the moment the ext plane is allowed to differ from the register plane.
#[test]
fn an_unseeded_spilled_var_reads_zero_exactly_like_a_register() {
    let s = wide();
    let rest = nth_choice(&s, "hall", REST);

    // z_weary is never seeded and never written by any effect — its ONLY existence is
    // that a condition named it. On a register that is field-zero; on the ext plane it
    // would be an absent key (refusing everything) if it were not born.
    let world = WorldCell::deploy(&s, 86).expect("deploy");
    assert_eq!(world.read_var("z_weary"), 0, "an unseeded spilled var is 0");
    world
        .apply_choice("hall", REST, &rest)
        .expect("`{ z_weary <= 0 }` on an unwritten SPILLED var admits, as on a register");
    assert_eq!(world.read_var("z_rested"), 1);

    // And it still DISCRIMINATES — the parity is not "admit everything": a weary
    // traveller is refused.
    let mut weary = WorldCell::deploy(&s, 87).expect("deploy");
    weary.seed_var("z_weary", Value::Int(3));
    let refused = weary.apply_choice("hall", REST, &rest);
    assert!(
        matches!(refused, Err(WorldError::Refused(_))),
        "the parity gate still bites a weary traveller; got {refused:?}"
    );
    assert_eq!(weary.read_var("z_rested"), 0, "anti-ghost");
}

// ─────────────────────────────────────────────────────────────────────────────
// 5. The <= 16 path is UNCHANGED.
// ─────────────────────────────────────────────────────────────────────────────

/// A scene that FITS keeps exactly its old layout and its old teeth: registers only, no
/// ext key, no ext tooth anywhere in the program, and a 16-element snapshot. The wide
/// plane is inert for a narrow scene — it changes only what happens PAST the 16th.
#[test]
fn the_narrow_path_is_unchanged() {
    let s = scene(NARROW, "narrow.scene");
    let story = compile_scene(&s).expect("compiles");

    assert!(story.ext_keys().is_empty(), "a narrow scene spills nothing");
    assert_eq!(
        story.var_key("strength"),
        Some(1),
        "the old layout, exactly"
    );
    assert!(!story.is_spilled("strength"));

    // The gate is the register tooth it always was: FieldGte + the FieldDelta clamp
    // companion (`{strength>=4} ~ strength-=1` lifts to `>= 3`... which stays > 0, so
    // NO companion — the untouched-lift rule, preserved).
    let force = case_constraints(&story, "gate", 0);
    assert!(
        force.iter().any(|c| matches!(c,
            StateConstraint::FieldGte { index, value }
                if *index == 1 && *value == field_from_u64(3))),
        "the register gate lifts to FieldGte(strength, 3); got {force:?}"
    );

    // NOT ONE ext-plane tooth over STORY STATE anywhere in a narrow scene's program —
    // including the heap hatch case, whose confinement is the register freeze alone when
    // nothing spilled. This is the SPILL invariant: nothing spilled ⇒ no story var/
    // membership atom is reached through the heap.
    //
    // The reserved `GENESIS_DONE_EXT_KEY` sentinel is EXCLUDED: it is not story state and
    // not a spill — it is the protocol key that makes `genesis` ONE-SHOT (the `0 → 1`
    // tooth on the genesis case + the `Immutable` freeze on every other case), present on
    // EVERY compiled scene, narrow or wide, and it is what closes the universal
    // post-deploy genesis write-hatch. It costs a narrow scene no REGISTER, does not
    // spill any var (`ext_keys()` stays empty, asserted above), and does not widen
    // `snapshot()` (asserted below) — the wide plane itself remains inert for a narrow
    // scene, which is what this test is about. There is no free register to host the
    // sentinel (a wide scene fills all 16), so the reserved ext key is the one uniform
    // home for it.
    let CellProgram::Cases(cases) = &story.program else {
        panic!("Cases")
    };
    for case in cases {
        for c in &case.constraints {
            let story_ext_tooth = match c {
                StateConstraint::HeapField { key, .. } => *key != GENESIS_DONE_EXT_KEY,
                StateConstraint::HeapFieldLteOther { .. } => true,
                _ => false,
            };
            assert!(
                !story_ext_tooth,
                "a narrow scene emits NO ext-plane constraint over story state; got {c:?}"
            );
        }
    }

    // The state fingerprint is the same 16-element register vector as before.
    let world = WorldCell::deploy(&s, 84).expect("deploy");
    assert_eq!(world.snapshot().len(), STATE_SLOTS);
}

// ─────────────────────────────────────────────────────────────────────────────
// 6. The hatch confinement widened with the story.
// ─────────────────────────────────────────────────────────────────────────────

/// **Spilling must not open a hole.** The heap hatch (`HEAP_HATCH_METHOD`) freezes every
/// REGISTER, which used to confine it completely — no story state lived on the heap. Now
/// some does. Without widening the confinement, a hatch turn (a method any cap-holder
/// can present) could overwrite a wide scene's `z_gold` directly, routing around every
/// gate. It cannot: the compiled ext keys are pinned `Immutable` on that case, while a
/// heap key the story does NOT own stays writable — the hatch keeps its purpose.
#[test]
fn the_heap_hatch_cannot_overwrite_a_spilled_story_var() {
    let s = wide();
    let story = compile_scene(&s).expect("compiles");
    let mut world = WorldCell::deploy(&s, 85).expect("deploy");
    world.seed_var("z_gold", Value::Int(5));
    let cell = world.cell_id();
    let gold = story.var_key("z_gold").expect("z_gold");

    // The hatch case pins every compiled ext key.
    let hatch = constraints_for(&story, HEAP_HATCH_METHOD);
    for key in story.ext_keys() {
        assert!(
            hatch.iter().any(|c| matches!(c,
                StateConstraint::HeapField { key: k, atom: HeapAtom::Immutable } if *k == key)),
            "the hatch case pins ext key {key} Immutable"
        );
    }

    // DRIVEN: a hatch turn minting itself a fortune in the story's own purse is REFUSED.
    let forged = world.apply_raw(
        HEAP_HATCH_METHOD,
        vec![Effect::SetField {
            cell,
            index: gold as u64,
            value: field_from_u64(1_000_000),
        }],
    );
    assert!(
        matches!(forged, Err(WorldError::Refused(_))),
        "the hatch cannot overwrite a SPILLED story var; got {forged:?}"
    );
    assert_eq!(world.read_var("z_gold"), 5, "anti-ghost: the purse holds");

    // The hatch still WORKS for what it is for: an app collection key the story does not
    // own is written freely. (Confinement, not closure.)
    let free_key = STATE_SLOTS as u64 + 3;
    world
        .apply_raw(
            HEAP_HATCH_METHOD,
            vec![Effect::SetField {
                cell,
                index: free_key as u64,
                value: field_from_u64(42),
            }],
        )
        .expect("a key the story does not own is still writable");
    assert_eq!(world.read_heap(free_key), Some(42));
}
