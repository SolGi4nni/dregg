//! ⚑⚑ **A PORT NAMES ITS COVER, AND THE NAME IS RESOLVED — the registry gate for the 2026-08-10
//! `proof_bind` nullability flag day.**
//!
//! # What was wrong, in one line
//!
//! `ProofBindSpec::bound` was `Option<Vec<LeanExpr>>`, `Ir2Air::eval` reached the commit lanes only
//! under `if let Some(b) = &p.bound`, and **every deployed seam wrote `None`** — so results were
//! stated about columns that appear in no emitted polynomial. Five layers of detection machinery
//! were built around the nullable field; none of them stopped the next `None` from being written,
//! because the type still permitted it.
//!
//! # What the type change buys, and what THIS file adds on top
//!
//! [`CommitBinding`] has two states and no third: `Bound(lanes)` (which emits
//! `guard·(commitᵢ − boundᵢ)` per lane) or `Port(PortCover)` (which emits nothing **and says so
//! with two names**). The type alone makes "binds nothing, names nothing" unconstructible.
//!
//! This file closes the remaining half: **the names are resolved, not just present.** A port name
//! that no registry row carries, or a welder path naming a function that does not exist, is a
//! `null` in a costume — and it is exactly what a lane under deadline would write. So:
//!
//! * a cover naming a **seam** must match the `name` of a `SeamSpec` emitted under
//!   `circuit/descriptors/seams/`;
//! * a cover naming a **welder** (a `crate::module::function` path) must resolve to a `fn` of that
//!   name in that module's source file.
//!
//! ⚠ **Resolution is not coverage.** That `check_body_chain_binding` EXISTS does not make it
//! compare the right lanes; that is the welder's own both-polarity release tests
//! (`mina_head_verifier.rs`'s REFUSAL suites), named at each `WeldCover` declaration in
//! `MinaSeams.lean`. What this gate refuses is the cheaper lie: a port that points at nothing.
//!
//! # The counted wound, said out loud
//!
//! [`OWED_COVERS`] is not zero, and the number is the point. Two ported commit surfaces name a
//! welder that has not been written:
//!
//! * `dregg-mina-lightclient-link::v1`'s **`state-hash-preimage`** — the 54-lane
//!   `salt ‖ PARENT ‖ BODYHASH ‖ OWNHASH` commit vector of `stateHashBindLeg`. `bodyHashWeld`
//!   covers the `BODYHASH` nonet (REFUSAL 16d); **nothing anywhere compares `PARENT` or
//!   `OWNHASH`**, and `mina_head_verifier.rs` says so itself — *"its `OWNHASH` is a free witness"*.
//!   Under `bound := none` that fact lived in a paragraph. It is now a name that fails to resolve.
//! * `dregg-mina-wrap-closing::v1`'s **`delta-absorb-pis`** — the closing fold's `connect`s over
//!   the delta-absorb commit vector, which `mina_wrap_closing_fold.rs` does not expose as a named
//!   function.
//!
//! The literal may only shrink. Writing either welder is what shrinks it; renaming a port to dodge
//! the gate moves the literal the other way and reds this file.

use dregg_circuit::descriptor_ir2::{CommitBinding, VmConstraint2, parse_vm_descriptor2};
use std::collections::BTreeSet;
use std::path::{Path, PathBuf};

/// ⚑ The number of declared port covers that DO NOT resolve. May only shrink. See the module
/// docblock for what each one is and what closes it.
const OWED_COVERS: usize = 2;

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("the circuit crate sits one level below the repo root")
        .to_path_buf()
}

/// Every `SeamSpec` name emitted under `circuit/descriptors/seams/`.
fn registered_seam_names() -> BTreeSet<String> {
    let dir = repo_root().join("circuit/descriptors/seams");
    let mut out = BTreeSet::new();
    let Ok(rd) = std::fs::read_dir(&dir) else {
        panic!("the seam registry directory {dir:?} must exist");
    };
    for e in rd.flatten() {
        let p = e.path();
        if p.extension().and_then(|s| s.to_str()) != Some("json") {
            continue;
        }
        let Ok(text) = std::fs::read_to_string(&p) else {
            continue;
        };
        // The seam JSON carries `"name":"…"` at its top level; `ports.json` is an array of port
        // rows and carries none, which is why it contributes nothing here.
        if let Some(i) = text.find("\"name\":\"") {
            let rest = &text[i + 8..];
            if let Some(j) = rest.find('"') {
                out.insert(rest[..j].to_owned());
            }
        }
    }
    out
}

/// `dregg_turn::executor::mina_head_verifier` → `turn/src/executor/mina_head_verifier.rs`.
fn crate_src_root(krate: &str) -> Option<&'static str> {
    match krate {
        "dregg_turn" => Some("turn/src"),
        "dregg_circuit" => Some("circuit/src"),
        "dregg_circuit_prove" => Some("circuit-prove/src"),
        _ => None,
    }
}

/// Does this cover name resolve? Either a registered seam, or a `crate::module::fn` path whose
/// function is defined in that module's source.
fn resolves(cover: &str, seams: &BTreeSet<String>) -> bool {
    if seams.contains(cover) {
        return true;
    }
    let parts: Vec<&str> = cover.split("::").collect();
    if parts.len() < 2 {
        return false;
    }
    let Some(root) = crate_src_root(parts[0]) else {
        return false;
    };
    let func = parts[parts.len() - 1];
    let module: PathBuf = parts[1..parts.len() - 1].iter().collect();
    let file = repo_root().join(root).join(module).with_extension("rs");
    let Ok(text) = std::fs::read_to_string(&file) else {
        return false;
    };
    text.contains(&format!("fn {func}("))
}

/// Every served descriptor's ported commit halves, as `(descriptor, port, cover)`.
fn declared_ports() -> Vec<(String, String, String)> {
    let dir = repo_root().join("circuit/descriptors");
    let mut out = Vec::new();
    let mut stack = vec![dir];
    while let Some(d) = stack.pop() {
        let Ok(rd) = std::fs::read_dir(&d) else {
            continue;
        };
        for e in rd.flatten() {
            let p = e.path();
            if p.is_dir() {
                stack.push(p);
                continue;
            }
            if p.extension().and_then(|s| s.to_str()) != Some("json") {
                continue;
            }
            let Ok(text) = std::fs::read_to_string(&p) else {
                continue;
            };
            // Only IR-v2 descriptor files parse; the seam/port registry rows and provenance
            // records do not, and are skipped rather than asserted about.
            let Ok(d2) = parse_vm_descriptor2(&text) else {
                continue;
            };
            for c in &d2.constraints {
                if let VmConstraint2::ProofBind(m) = c
                    && let CommitBinding::Port(cover) = &m.bound
                {
                    out.push((d2.name.clone(), cover.port.clone(), cover.seam.clone()));
                }
            }
        }
    }
    out.sort();
    out.dedup();
    out
}

/// ⚑ **THE GATE.** Every ported commit half in every served descriptor names a cover, and the
/// number that fails to resolve is pinned. Both directions bite: an unresolvable NEW cover raises
/// the count, and writing an owed welder lowers it, so the literal must be edited either way.
#[test]
fn every_declared_port_cover_resolves_or_is_counted() {
    let seams = registered_seam_names();
    assert!(
        !seams.is_empty(),
        "the seam registry parsed to zero names — the gate would then pass vacuously"
    );

    let ports = declared_ports();
    assert!(
        !ports.is_empty(),
        "no served descriptor declares a ported commit half; if that is so, the flag day did not \
         land and this gate is measuring nothing"
    );

    let mut owed: Vec<String> = Vec::new();
    for (desc, port, cover) in &ports {
        assert!(
            !port.trim().is_empty() && !cover.trim().is_empty(),
            "{desc}'s port declares an empty name — that is the retired `null` in a costume"
        );
        if !resolves(cover, &seams) {
            owed.push(format!("{desc} :: {port} → {cover}"));
        }
    }
    owed.sort();

    println!("declared port covers: {}", ports.len());
    for (desc, port, cover) in &ports {
        println!("  {desc} :: {port} → {cover}");
    }
    println!(
        "UNRESOLVED covers: {} (pinned at {OWED_COVERS})",
        owed.len()
    );
    for o in &owed {
        println!("  OWED {o}");
    }

    assert_eq!(
        owed.len(),
        OWED_COVERS,
        "the owed-cover count moved. It may only SHRINK, and only by writing the welder a port \
         names — never by renaming the port. Owed now: {owed:#?}"
    );
}

/// ⚑ **THE FALSIFIER — the gate can go red, and moves a non-zero value inside its declared
/// width.** A cover name that resolves today, mutated by one character, stops resolving. Built
/// CONSTRUCTIVELY (the mutation is asserted to have happened before the verdict is read) because a
/// mutation that silently became a no-op is how an adversary dies while its gate stays green.
#[test]
fn a_mutated_cover_name_stops_resolving() {
    let seams = registered_seam_names();
    let ports = declared_ports();

    // Pick a cover that DOES resolve today — the honest pole.
    let live = ports
        .iter()
        .map(|(_, _, c)| c.clone())
        .find(|c| resolves(c, &seams))
        .expect("at least one declared cover must resolve, or the gate proves nothing");

    // …and move it. One character, inside the name, so the mutant is a well-formed name that
    // simply names nothing.
    let mutated = format!("{live}_that_no_one_wrote");
    assert_ne!(mutated, live, "the mutation must actually change the name");
    assert!(
        resolves(&live, &seams),
        "the honest pole must resolve: {live}"
    );
    assert!(
        !resolves(&mutated, &seams),
        "the falsifier moved nothing — a cover that resolves under ANY name is not a resolution"
    );
}
