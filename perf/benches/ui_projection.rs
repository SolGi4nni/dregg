//! Criterion bench: THE deos DESKTOP UI-RENDER MEASURE (gpui-free, whole-system).
//!
//! The gpui cockpit's actual GPU FIRST-PAINT (a real lavapipe/Metal scan-out) is captured on
//! persvati (HORIZONLOG: the gpui cockpit is scanned out of the seL4 ramfb). What is measured
//! HERE — deterministically, on any host, without a GPU or window — is the whole-system cost
//! the cockpit pays to HAVE something to paint:
//!
//!   * `demo_world_seed` — `starbridge_v2::demo_world()`: the FIVE real embedded `commit_turn`s
//!     (through the verified `DreggEngine`) that build the live provenance image the cockpit's
//!     first paint renders. This is the "first-paint DATA" cost — the work behind the cells.
//!   * `demo_genesis_instant` — `demo_genesis()`: the INSTANT genesis half (install anchors,
//!     no turns) — the path the gpui cockpit opens its window on immediately, before seeding.
//!   * `compose_scene` — `Shell::compose_scene(&world)`: the VERIFIED compositor scene the
//!     cockpit routes paint + input through (the §5 region/focus/source-root discipline).
//!   * `compose_paint_list` — `Shell::compose(&world)`: the ordered paint list (back-to-front
//!     z-order + per-surface trusted-path identity chrome) the renderer turns into pixels.
//!   * `affordance_project` — `AffordanceSurface::project_for(&held)`: the per-viewer deos
//!     affordance projection (progressive attenuation — which affordances a held cap reveals).
//!
//! These are the deos "affordance projection cost" + the scene the gpui cockpit renders, exactly
//! as the brief's whole-system option (e) names. All gpui-free and `cargo test`-able.
//!
//! Fixed-size (the demo image is the canonical desktop), so SMOKE == FULL.
//!
//! Run: `cargo bench -p dregg-perf --bench ui_projection`

use criterion::{Criterion, black_box, criterion_group, criterion_main};
use dregg_perf::regime;

use dregg_cell::AuthRequired;
use dregg_turn::action::Effect;
use starbridge_v2::affordance::{AffordanceSurface, CellAffordance};
use starbridge_v2::shell::Shell;
use starbridge_v2::{demo_genesis, demo_world};

fn bench_ui_projection(c: &mut Criterion) {
    let mut group = c.benchmark_group(format!("ui_projection/{}", regime()));
    // The `demo_world_seed` leg runs FIVE real embedded `commit_turn`s through the verified
    // `DreggEngine` (+ the replay-tape re-execution) — seconds-scale; keep the sample count
    // modest. The compose / affordance legs are microseconds-scale but share the group config.
    group.sample_size(10);

    // (1) The first-paint DATA cost: the five real embedded commit_turns the cockpit paints.
    group.bench_function("demo_world_seed", |b| {
        b.iter(|| {
            let (world, anchors) = demo_world();
            black_box((world, anchors));
        });
    });

    // (2) The instant genesis half (no turns) — the immediate window-open image.
    group.bench_function("demo_genesis_instant", |b| {
        b.iter(|| {
            let (world, anchors, seed) = demo_genesis();
            black_box((world, anchors, seed));
        });
    });

    // Build a live world + a shell with two open surfaces (a console + a cell view) — the
    // shape the cockpit composes every frame. `open_*` hand back the REAL firmament window
    // cap (widest `None` rights over the backing surface-cell) — the public surface door.
    let (world, anchors) = demo_world();
    let mut shell = Shell::new();
    let _console = shell.open_console(anchors[0], "console");
    let held = shell.open_cell_view(anchors[2], "user");

    // (3) The verified compositor scene (region/focus/source-root discipline).
    group.bench_function("compose_scene", |b| {
        b.iter(|| {
            let scene = shell.compose_scene(black_box(&world));
            black_box(scene);
        });
    });

    // (4) The ordered paint list (z-order + per-surface trusted-path identity chrome).
    group.bench_function("compose_paint_list", |b| {
        b.iter(|| {
            let scene = shell.compose(black_box(&world));
            black_box(scene);
        });
    });

    // (5) The per-viewer affordance projection (progressive attenuation). A surface declaring
    // a narrow `view` + a wider `admin` affordance, projected for the held window cap (whose
    // widest `None` rights clear both — `authorized_for` is a pure rights-lattice check).
    let backing = anchors[2];
    let surf = AffordanceSurface::new(backing)
        .declare(CellAffordance::new(
            "view",
            AuthRequired::Signature,
            Effect::IncrementNonce { cell: backing },
        ))
        .declare(CellAffordance::new(
            "admin",
            AuthRequired::Either,
            Effect::IncrementNonce { cell: backing },
        ));
    group.bench_function("affordance_project", |b| {
        b.iter(|| {
            let visible = surf.project_for(black_box(&held));
            black_box(visible);
        });
    });

    group.finish();
}

criterion_group!(benches, bench_ui_projection);
criterion_main!(benches);
