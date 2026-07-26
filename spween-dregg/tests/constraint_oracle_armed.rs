//! THE TOOTH ON THE ORACLE ARMING POINT — a world-cell deploy MUST reach it.
//!
//! # The wound
//!
//! `dregg_cell::program::eval` routes the Lean-evaluated `StateConstraint`/`HeapAtom` subset through
//! an installed constraint oracle and FAILS CLOSED when there is none. That refusal is correct. What
//! was not correct is that on 2026-07-26 **nothing in any binary installed one**, so on a native
//! release build the gate could only ever REFUSE: a player typed `/adventure dungeon start` on the
//! live Discord bot and got `no constraint oracle installed … install it via
//! install_constraint_oracle` — the name of an internal Rust function, shown to a human.
//!
//! # Why it survived a whole day of lanes
//!
//! Four separate lanes hit `no constraint oracle installed` that day (10 `crowd_round`/`overlay` lib
//! tests, `dreggnet-council`, `dreggnet-surfaces` under `--release`) and every one classified it as
//! co-tenant churn or an environment artifact. It looked like noise because the obvious test —
//! "is an oracle installed?" — is legitimately `false` in every DEBUG build: the install is
//! release-gated on purpose, because `dregg-cell` is a pervasive dependency and arming it in debug
//! would re-route every programmed-cell decision in the workspace's suite. So the question everyone
//! could cheaply ask was VACUOUS exactly where everyone runs their tests.
//!
//! # What this test asks instead
//!
//! The bug was *nothing called the installer*, which is a property of the CALL GRAPH — identical in
//! debug and release — not of the target or the linked archive. `dregg-sdk` records the arming point
//! separately for that reason ([`dregg_sdk::deployed_executor_arming_attempted`]: set on every target
//! and every profile, including the ones that deliberately install nothing), and this test asserts
//! that a REAL world-cell deploy reaches it.
//!
//! `WorldCell::deploy` is the derivation point every game surface shares: `discord-bot`,
//! `dreggnet-telegram-bot`, `dreggnet-web-server`, `dregg-drive` and the offering hosts all reach a
//! programmed cell through it (→ `EmbeddedExecutor::new` → `AgentRuntime::new` → the arming point),
//! so ONE tooth here covers all of them. It is not a per-binary install and must not become one —
//! copying an install line into five binaries is what produced the PQ cold-start bug, where 179
//! inline installs lived only in `run_node` and `genesis`/`mcp`/`relay` aborted.
//!
//! # HOW TO MAKE IT GO RED (the house rule: a gate that cannot fail is not a gate)
//!
//! * **In DEBUG, on a laptop, in seconds** — delete the
//!   `ensure_deployed_executor_oracles_installed()` call from `AgentRuntime::new` (and
//!   `::with_ledger`) in `sdk/src/runtime.rs`, i.e. restore the exact state of the tree before
//!   2026-07-26 09:21. `arming_point_is_reached_by_a_real_world_cell_deploy` fails at
//!   "a world-cell deploy MUST reach the arming point". This is the assertion that would have caught
//!   the live break, and it needs no Lean archive and no release build.
//! * **In RELEASE** — `cargo test --release -p spween-dregg --test constraint_oracle_armed` with an
//!   archive that does not export `dregg_constraint_admits` (e.g. a `DREGG_REQUIRE_LEAN=0` build,
//!   which is exactly how the hbox bot was built): the deploy itself fails at
//!   "the genesis turn must COMMIT", because that is precisely what a player experienced.
//! * The final assertion (`fails-closed ⇒ installed`) is the deployed configuration stated as an
//!   implication, so it is vacuous in debug BY DESIGN and load-bearing in release. It is the second
//!   tooth, not the first; the arming-point assertion above is the one that bites everywhere.

use dregg_cell::program::{
    constraint_oracle_installed, constraint_subset_fails_closed_without_oracle,
};
use spween_dregg::{Driver, Scene, Value, WorldCell, parse};

/// A two-passage quest whose first passage carries a GATED choice. The compiler lowers
/// `{ strength >= 5 }` into a real `StateConstraint::FieldGte` on the strength slot — a class-a
/// (PURE) constraint, i.e. squarely inside the Lean-evaluated subset the oracle decides and the
/// no-oracle gate refuses. Driving it is what makes this test exercise the actual break rather than
/// a constraint-free turn.
const QUEST: &str = r#"---
id: oracle-armed
title: Oracle Armed
weight: 1
---

=== door

A heavy door, and you are strong enough for it.

* [Force it open] { strength >= 5 }
  ~ strength -= 1
  -> hall

=== hall

Through, into the great hall.

* [Rest]
  -> END
"#;

fn scene() -> Scene {
    parse(QUEST, "oracle-armed.scene").expect("scene parses")
}

/// ONE test function on purpose. `deployed_executor_arming_attempted()` reads a PROCESS-global flag,
/// so a sibling `#[test]` in this binary deploying a world in parallel would set it and make the
/// "not yet armed" premise below pass for the wrong reason. Keeping the before/after pair inside a
/// single test makes the tooth race-free and its premise checkable.
#[test]
fn arming_point_is_reached_by_a_real_world_cell_deploy() {
    // PREMISE (the anti-vacuity guard). Nothing in this binary has constructed an `AgentRuntime`
    // yet, so the flag must still be false — otherwise the assertion after the deploy proves
    // nothing about the deploy.
    assert!(
        !dregg_sdk::deployed_executor_arming_attempted(),
        "nothing in this test binary has built an AgentRuntime yet, so the arming flag must be \
         false here; if it is already true the assertion below is vacuous and this tooth is asleep"
    );

    let scene = scene();
    let mut world = WorldCell::deploy(&scene, 21).expect("the world-cell deploys");
    world.seed_var("strength", Value::Int(6));

    // ⚑ THE TOOTH. Deploying a world-cell goes `WorldCell::deploy` → `EmbeddedExecutor::new` →
    // `AgentRuntime::new` → the deployed-executor arming point. Every game surface in the tree
    // reaches a programmed cell this way, so this is the one call every binary inherits. Before
    // 2026-07-26 it was reached by NOTHING, in any binary, ever.
    assert!(
        dregg_sdk::deployed_executor_arming_attempted(),
        "a world-cell deploy MUST reach the deployed-executor oracle arming point \
         (`WorldCell::deploy` → `EmbeddedExecutor::new` → `AgentRuntime::new` → \
         `ensure_deployed_executor_oracles_installed`). It does not, which means a native RELEASE \
         build of every game surface — discord-bot, dreggnet-telegram-bot, dreggnet-web-server, \
         dregg-drive — installs no constraint oracle and can only REFUSE every programmed-cell turn"
    );

    // The genesis turn is a real programmed-cell turn (the compiler's one-shot genesis case carries
    // `Equals{1} ∧ DeltaEquals{1}` on the genesis sentinel — Lean-subset teeth), so a build with the
    // fail-closed gate armed and no oracle dies HERE, exactly where the player did.
    let mut driver = Driver::start(world, &scene).expect(
        "the genesis turn must COMMIT — a refusal here is the live break: this build refuses the \
         Lean constraint subset and has no oracle to decide it",
    );

    // And so is a gated choice: `{ strength >= 5 }` lowered to a real `FieldGte` tooth.
    driver
        .advance(0)
        .expect("the gated choice must COMMIT — its `FieldGte` tooth is in the Lean subset");
    // ANTI-GHOST: the turn really committed state, so the assertions above are about a turn the
    // executor admitted rather than one it silently skipped.
    assert_eq!(
        driver.world().read_var("strength"),
        5,
        "the admitted choice's `strength -= 1` must be committed state"
    );

    // THE DEPLOYED CONFIGURATION, as an implication over the ONE source for the gate's predicate
    // (`dregg_cell::program::constraint_subset_fails_closed_without_oracle` — the same `const fn`
    // `eval.rs` branches on, so this cannot describe a gate that has moved). Vacuous in debug by
    // design; load-bearing on the native release build that a box actually runs.
    assert!(
        !constraint_subset_fails_closed_without_oracle() || constraint_oracle_installed(),
        "this build REFUSES the Lean-evaluated constraint subset when no oracle is installed, and \
         no oracle is installed — a gate that can only refuse. Either the linked libdregg_lean.a \
         does not export `dregg_constraint_admits` (a DREGG_REQUIRE_LEAN=0 / stale-archive build, \
         which cannot serve turns and must not be deployed) or the arming point installed nothing"
    );
}
