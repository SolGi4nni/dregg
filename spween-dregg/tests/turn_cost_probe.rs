//! PER-TURN COST AT THE WORLD BOUNDARY — an explicit measurement, not an inference.
//!
//! `#[ignore]`d, because it is a stopwatch rather than a gate. Run it deliberately:
//!
//! ```text
//! cargo test -p spween-dregg --test turn_cost_probe -- --ignored --nocapture
//! ```
//!
//! It reports CPU time (`getrusage`, so a loaded laptop does not distort it) alongside wall time
//! for the three quantities the ML-DSA latency work turns on:
//!
//!   * **keygen** — one `MlDsaTurnKey::from_ed25519_seed`, the derivation `AgentCipherclerk` used
//!     to run on EVERY hybrid signature and now memoises. That is the caching win, per signature.
//!   * **a Federation world's turn** — signs HYBRID (ed25519 + ML-DSA-65) and the executor verifies
//!     both halves, exactly as every world did before this work. Add one keygen to reconstruct the
//!     pre-cache per-turn cost.
//!   * **a Local world's turn** — signs CLASSICAL. The gap to the Federation leg is what the
//!     post-quantum half costs on a path where it is verified against a key the action carries
//!     about itself (the reasoning is on `WorldCell::make_choice_action`).
//!
//! The numbers only mean something with the verified Lean cores installed, so the probe ASSERTS
//! they are — it can never quietly report the `fips204` crate's speed in place of the deployed
//! object's.

use std::time::Instant;

use spween_dregg::{Driver, Scene, WorldCell, parse};

const SCENE: &str = r#"---
id: probe
title: Probe
weight: 1
---

=== start

A corridor.

* [Step]
  -> start
"#;

/// Process CPU time (user + system) in milliseconds.
fn cpu_ms() -> f64 {
    unsafe {
        let mut ru: libc::rusage = std::mem::zeroed();
        libc::getrusage(libc::RUSAGE_SELF, &mut ru);
        ru.ru_utime.tv_sec as f64 * 1000.0
            + ru.ru_utime.tv_usec as f64 / 1000.0
            + ru.ru_stime.tv_sec as f64 * 1000.0
            + ru.ru_stime.tv_usec as f64 / 1000.0
    }
}

fn install_cores() {
    use dregg_sdk::MlDsaVerifyCoreInstall as V;
    use dregg_sdk::{MlDsaKeygenCoreRealInstall as K, MlDsaSignCoreRealInstall as S};
    let k = dregg_sdk::install_verified_mldsa_keygen_core_real();
    assert!(
        matches!(k, K::Installed | K::AlreadyInstalled),
        "the verified ML-DSA keygen core must be installed or this probe times the wrong object; got {k:?}"
    );
    let s = dregg_sdk::install_verified_mldsa_sign_core_real();
    assert!(
        matches!(s, S::Installed | S::AlreadyInstalled),
        "sign core: {s:?}"
    );
    let v = dregg_sdk::install_verified_mldsa_verify_core();
    assert!(
        matches!(v, V::Installed | V::AlreadyInstalled),
        "verify core: {v:?}"
    );
}

fn drive(world: WorldCell, scene: &Scene, turns: usize, label: &str) {
    let mut driver = Driver::start(world, scene).expect("driver starts");
    // One turn outside the window: it warms the clerk's PQ memo and first-touches the Lean heap.
    driver.advance(0).expect("warm turn");
    let c0 = cpu_ms();
    let w0 = Instant::now();
    for _ in 0..turns {
        driver.advance(0).expect("probe turn");
    }
    let cpu = (cpu_ms() - c0) / turns as f64;
    let wall = w0.elapsed().as_secs_f64() * 1000.0 / turns as f64;
    println!("{label:<36} cpu {cpu:8.1} ms/turn   wall {wall:8.1} ms/turn");
}

#[test]
#[ignore = "a stopwatch, not a gate — run with --ignored"]
fn per_turn_cost() {
    install_cores();
    let scene = parse(SCENE, "probe.scene").expect("scene parses");
    let turns = 6;

    // The removed derivation, timed on its own. (Warm it first: the first call into the Lean core
    // pays module init + first-touch paging that no later signature pays.)
    let _ = dregg_turn::pq::MlDsaTurnKey::from_ed25519_seed(&[0x11; 32]);
    let c0 = cpu_ms();
    let w0 = Instant::now();
    let _ = dregg_turn::pq::MlDsaTurnKey::from_ed25519_seed(&[0x5a; 32]);
    println!(
        "{:<36} cpu {:8.1} ms        wall {:8.1} ms",
        "ML-DSA keygen (was once PER SIGNATURE)",
        cpu_ms() - c0,
        w0.elapsed().as_secs_f64() * 1000.0
    );

    let federated = WorldCell::deploy(&scene, 1)
        .expect("deploy")
        .with_node_target(dregg_node_target::NodeTarget::federation(
            dregg_node_target::StubNode::new(),
        ));
    drive(federated, &scene, turns, "turn, Federation target (hybrid)");

    let local = WorldCell::deploy(&scene, 2).expect("deploy");
    drive(local, &scene, turns, "turn, Local target (classical)");
}
