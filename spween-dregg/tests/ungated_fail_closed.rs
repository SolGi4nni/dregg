//! **M09 — `apply_choice` must FAIL-CLOSED on an under-gated choice.**
//!
//! `apply_choice` drives the real `EmbeddedExecutor` as the SOLE referee (the demo
//! service and every offerings/faction/quest caller advertise it that way): an
//! ineligible/forged pick is supposed to be refused in-band by the installed
//! `CellProgram` gate case, nothing committing.
//!
//! That holds ONLY when the choice's gate lowered FULLY to executor teeth
//! (`CompiledStory::fully_gated[method] == Some(true)`). A clause the v0 compiler cannot
//! lift — the canonical case being a gate on a var the SAME choice `Set`s, e.g.
//! `{ gold >= 50 } ~ gold = 0` (the `Delta::Overwritten` bail in `lower_clause`) —
//! installs an EMPTY tooth set and records `fully_gated[method] == Some(false)`. The
//! executor's `MethodIs` case is then satisfied by DISPATCH ALONE, so a turn commits
//! WITHOUT anything on the `apply_choice` path ever evaluating the condition. A
//! fail-OPEN: an under-gated choice commits when the referee should refuse it.
//!
//! These tests DRIVE that against the real executor:
//!
//! 1. THE FAIL-OPEN, CLOSED: an under-gated choice on a FULL purse (the condition itself
//!    is satisfied, so the refusal cannot be the gate biting) is `WorldError::UngatedChoice`
//!    and commits NOTHING. The canary below confirms it committed before the fix.
//! 2. THE LEGIT PATH INTACT: a fully-lowered `{ gold >= 50 } ~ bought = 1` still commits on
//!    a solvent purse and is really refused (`Refused`, the executor tooth) on a broke one.
//! 3. PRECISION: a conditionless choice (map entry ABSENT, trivially/correctly ungated)
//!    still commits — the guard refuses only `Some(false)`, not "no condition".
//! 4. THE HANDLER-ONLY GATE STILL HAS A HOME: the `Driver` path (`select_choice`), the one
//!    path that evaluates a handler-only clause, still admits the eligible move and refuses
//!    the ineligible one for the very same under-gated choice.

use spween_dregg::{Driver, Value, WorldCell, WorldError, choice_method, compile_scene, parse};

/// `{ gold >= 50 } ~ gold = 0`: the choice `Set`s its own gate var, so the pre-state gate
/// is NOT liftable to a post-state predicate — `lower_clause` bails (`Delta::Overwritten`)
/// and the case installs no gold tooth. `fully_gated[c/hall/0] == Some(false)`.
const UNDER_GATED: &str = r#"---
id: under-gated
title: The Trapdoor Purse
weight: 1
---

=== hall

A merchant bars the passage.

* [Buy passage] { gold >= 50 }
  ~ gold = 0
  -> END
"#;

/// The SAME gate, but the effect writes a DIFFERENT var — so `{ gold >= 50 }` lifts to a
/// real `FieldGte(gold, 50)` tooth and `fully_gated[c/hall/0] == Some(true)`.
const FULLY_GATED: &str = r#"---
id: fully-gated
title: The Honest Purse
weight: 1
---

=== hall

A merchant bars the passage.

* [Buy passage] { gold >= 50 }
  ~ bought = 1
  -> END
"#;

/// A choice with NO condition at all — the map entry is ABSENT (the compiler only records
/// `fully_gated` when `condition.is_some()`). Trivially, correctly ungated: nothing to check.
const CONDITIONLESS: &str = r#"---
id: conditionless
title: The Open Door
weight: 1
---

=== hall

The door stands open.

* [Walk through]
  ~ walked = 1
  -> END
"#;

fn scene(src: &str, name: &str) -> spween::Scene {
    parse(src, name).expect("scene parses")
}

/// The `idx`-th choice in `passage` (the order `apply_choice`'s index selects).
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

const BUY: usize = 0;

// ─────────────────────────────────────────────────────────────────────────────
// 0. Ground truth: the compiler DOES record the hazard we are closing.
// ─────────────────────────────────────────────────────────────────────────────

/// The under-gated choice compiles to `fully_gated == Some(false)` and the fully-gated one
/// to `Some(true)` — the discriminator `apply_choice` now consults is really populated.
#[test]
fn the_compiler_marks_the_under_gated_choice() {
    let under = compile_scene(&scene(UNDER_GATED, "under.scene")).expect("compiles");
    assert_eq!(
        under.fully_gated.get(&choice_method("hall", BUY)),
        Some(&false),
        "a gate on a self-`Set` var does NOT lower fully — this is the hazard M09 closes"
    );

    let full = compile_scene(&scene(FULLY_GATED, "full.scene")).expect("compiles");
    assert_eq!(
        full.fully_gated.get(&choice_method("hall", BUY)),
        Some(&true),
        "the same gate over an untouched var lowers FULLY to executor teeth"
    );

    let none = compile_scene(&scene(CONDITIONLESS, "none.scene")).expect("compiles");
    assert_eq!(
        none.fully_gated.get(&choice_method("hall", BUY)),
        None,
        "a conditionless choice records NO fully_gated entry (nothing to check)"
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// 1. THE FAIL-OPEN, CLOSED.
// ─────────────────────────────────────────────────────────────────────────────

/// **The headline.** An under-gated choice, on a FULL purse so the condition itself is
/// satisfied — the refusal therefore CANNOT be the gate biting on a broke buyer; it is the
/// referee refusing to admit a turn whose gate nothing on this path checks.
///
/// CANARY: delete `self.require_fully_gated(&method)?` from `apply_choice` (world.rs) and
/// this turn COMMITS — `read_var("gold") == 0`, the passage advances, the receipt is
/// genuine. That is the exact fail-open. Restore the line and it is refused again.
#[test]
fn an_under_gated_choice_is_refused_even_with_the_condition_satisfied() {
    let s = scene(UNDER_GATED, "under.scene");
    let buy = nth_choice(&s, "hall", BUY);

    let mut world = WorldCell::deploy(&s, 90).expect("deploy");
    world.seed_var("gold", Value::Int(100)); // FULL purse — `gold >= 50` is TRUE.
    let passage_before = world.read_passage();

    let refused = world.apply_choice("hall", BUY, &buy);
    assert!(
        matches!(refused, Err(WorldError::UngatedChoice(_))),
        "an under-gated choice is refused fail-closed, NOT admitted by dispatch alone; \
         got {refused:?}"
    );

    // Anti-ghost: the fail-open would have committed gold=0 and advanced the passage.
    assert_eq!(
        world.read_var("gold"),
        100,
        "nothing committed — the purse is untouched (was emptied by the fail-open)"
    );
    assert_eq!(
        world.read_passage(),
        passage_before,
        "nothing committed — the story did not advance"
    );

    // The certified path is closed identically (it shares the same guard).
    let refused_cert = world.apply_choice_certified("hall", BUY, &buy, [7u8; 32]);
    assert!(
        matches!(refused_cert, Err(WorldError::UngatedChoice(_))),
        "the certified path is fail-closed too; got {refused_cert:?}"
    );
    assert_eq!(world.read_var("gold"), 100, "still untouched");
}

// ─────────────────────────────────────────────────────────────────────────────
// 2. THE LEGIT PATH IS INTACT.
// ─────────────────────────────────────────────────────────────────────────────

/// A FULLY-lowered gate is unaffected: the solvent buyer commits (the guard does not fire),
/// and the broke buyer is refused by the REAL executor tooth (`Refused`, not `UngatedChoice`).
/// So the fix narrows to exactly the `Some(false)` hazard — it does not blanket-refuse gates.
#[test]
fn a_fully_gated_choice_still_commits_and_still_bites() {
    let s = scene(FULLY_GATED, "full.scene");
    let buy = nth_choice(&s, "hall", BUY);

    // Solvent: COMMITS — the guard passes (`Some(true)`), the real tooth admits.
    let mut rich = WorldCell::deploy(&s, 91).expect("deploy");
    rich.seed_var("gold", Value::Int(100));
    rich.apply_choice("hall", BUY, &buy)
        .expect("a fully-gated eligible choice still commits");
    assert_eq!(rich.read_var("bought"), 1, "the effect landed");

    // Broke: REFUSED — by the executor's `FieldGte(gold, 50)` tooth, NOT the M09 guard.
    let mut broke = WorldCell::deploy(&s, 92).expect("deploy");
    broke.seed_var("gold", Value::Int(10));
    let refused = broke.apply_choice("hall", BUY, &buy);
    assert!(
        matches!(refused, Err(WorldError::Refused(_))),
        "a broke buyer is refused by the real executor tooth (Refused), not the M09 guard; \
         got {refused:?}"
    );
    assert_eq!(broke.read_var("bought"), 0, "anti-ghost");
}

/// **Precision.** A conditionless choice (map entry ABSENT) is NOT the hazard and still
/// commits — the guard refuses only `Some(false)`. Without this, the fix would over-refuse
/// every ungated choice in the tree (the `~ key_owner = 1` Set-choices, etc.).
#[test]
fn a_conditionless_choice_still_commits() {
    let s = scene(CONDITIONLESS, "none.scene");
    let walk = nth_choice(&s, "hall", BUY);

    let world = WorldCell::deploy(&s, 93).expect("deploy");
    world
        .apply_choice("hall", BUY, &walk)
        .expect("a conditionless choice still commits (nothing to gate)");
    assert_eq!(world.read_var("walked"), 1, "the effect landed");
}

// ─────────────────────────────────────────────────────────────────────────────
// 3. THE HANDLER-ONLY GATE STILL HAS ITS HOME (the Driver path).
// ─────────────────────────────────────────────────────────────────────────────

/// The refusal is a REROUTE, not a loss: the under-gated gate is still enforced — on the
/// `Driver` path, whose `select_choice` evaluates the condition through the runtime overlay.
/// The eligible move commits there; the ineligible one is refused there. So closing the
/// `apply_choice` fail-open removed a trapdoor without removing the gate.
#[test]
fn the_driver_path_still_enforces_the_handler_only_gate() {
    let s = scene(UNDER_GATED, "under.scene");

    // Eligible (gold 100 >= 50): the Driver ADMITS and commits.
    let mut rich = WorldCell::deploy(&s, 94).expect("deploy");
    rich.seed_var("gold", Value::Int(100));
    let mut driver = Driver::start(rich, &s).expect("genesis");
    driver
        .advance(BUY)
        .expect("the Driver path evaluates the handler-only gate and admits the eligible move");
    let (world, _steps) = driver.finish();
    assert_eq!(
        world.read_var("gold"),
        0,
        "the choice's effect committed via the Driver"
    );

    // Ineligible (gold 10 < 50): the Driver REFUSES — the gate genuinely bites there.
    let mut broke = WorldCell::deploy(&s, 95).expect("deploy");
    broke.seed_var("gold", Value::Int(10));
    let mut driver = Driver::start(broke, &s).expect("genesis");
    let refused = driver.advance(BUY);
    assert!(
        matches!(refused, Err(WorldError::Refused(_))),
        "the handler-only gate bites on the Driver path for a broke buyer; got {refused:?}"
    );
}
