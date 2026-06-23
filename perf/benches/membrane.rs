//! Criterion bench: THE SHARED-FORK MEMBRANE round-trip — "invite someone to my computer".
//!
//! Times the four legs of the confined-fork membrane (`starbridge-v2/src/shared_fork.rs`,
//! gpui-free over the embedded `World` — the same verified executor the node and the seL4
//! `executor` PD drive):
//!
//!   * `fork`      — `World::fork`: the deep-clone of my live ledger + the genuine executor
//!     into a confined sub-world (the snapshot/rehydrate substrate — committing on the fork
//!     mutates ONLY the fork). This is the membrane's allocation cost; it scales with the
//!     ledger size, so it is the cost the fork-per-guest model is sensitive to.
//!   * `mint`      — `SharedFork::construct`: birth the confined guest's view by GRANTING an
//!     attenuated embedded cap into its fork c-list via a real verified powerbox turn
//!     (`Powerbox::grant` — the two gates `mint_needs_held_factory` + `gen_conferral_is_attenuation`
//!     + the executor backstop). This is the consent/authority typing of the membrane.
//!   * `drive`     — `SharedFork::commit_turn_gated`: the guest drives an EMBEDDED turn through
//!     the fail-closed boundary gate (classify against the boundaries over the same
//!     `touched_cells` the live path uses, then commit locally — an embedded exercise needs
//!     no consent). This is the per-turn cost inside the membrane.
//!   * `stitch`    — `Stitch::settle`: reconcile the branch's doc-graph back into main under the
//!     Settlement-Soundness gate (a conferred cap must be held at the settlement tip), then
//!     take the pushout. The merge-back cost.
//!
//! Plus `roundtrip` — fork → mint → drive → stitch end-to-end, the whole membrane lifecycle.
//!
//! Note (scope): the `drive` consent-gated boundary path (the `ConditionalTurn` consent
//! round-trip) is the rarer, slower leg; the common membrane exercise is the embedded turn
//! timed here. The consent path is exercised by `shared_fork`'s own tests.
//!
//! SMOKE (default): a small demo-seeded world. FULL (`PERF_FULL=1`): same shape (the legs are
//! microsecond-to-low-ms; the fork cost scales with the ledger, which the demo world fixes).
//!
//! Run: `cargo bench -p dregg-perf --bench membrane`

use std::collections::{BTreeSet, HashSet};

use criterion::{BatchSize, Criterion, black_box, criterion_group, criterion_main};
use dregg_cell::{AuthRequired, CellId};
use dregg_perf::regime;
use starbridge_v2::branch_stitch::{Atom, BranchCap, DocGraph, Stitch};
use starbridge_v2::shared_fork::SharedFork;
use starbridge_v2::world::{World, make_open_cell, transfer};

/// A fork world mirroring `shared_fork::tests::fork_world`: an owner principal holding a cap
/// to a `docs` cell, plus a fresh confined `guest` born with an empty c-list. Returns
/// `(world, owner, guest, docs)`.
fn membrane_world() -> (World, CellId, CellId, CellId) {
    let mut w = World::new();
    let docs = w.genesis_cell(0xD0, 1_000_000);
    let guest = w.genesis_cell(0xA9, 0); // confined, empty c-list

    let mut owner_cell = make_open_cell(0x55, 0);
    owner_cell
        .capabilities
        .grant(docs, AuthRequired::None)
        .expect("owner holds docs");
    let owner = w.genesis_install(owner_cell);
    (w, owner, guest, docs)
}

/// Construct the shared fork: grant `docs` as an embedded cap (attenuated to Signature) into
/// the guest's fork c-list. Returns the constructed `SharedFork`.
fn mint(fork: &mut World, owner: CellId, guest: CellId, docs: CellId) -> SharedFork {
    SharedFork::construct(
        fork,
        owner,
        guest,
        &[(docs, AuthRequired::Signature)], // embedded, attenuated from None
        vec![],                             // no studyrefs
        vec![],                             // no networkboundaries (embedded-only drive)
    )
}

/// A small main / branch doc-graph pair + a conferred cap, for the stitch leg. The branch
/// adds an atom and the conferred cap IS held at settlement, so the stitch settles.
fn stitch_inputs(docs: CellId) -> (Stitch, Vec<BranchCap>) {
    // The conferred cap reaches a stable id (the docs cell, as a u64 reach key).
    let target = u64::from_le_bytes(docs.0[..8].try_into().unwrap());
    let mut main = DocGraph::default();
    main.atoms.insert(1, Atom::Alive);
    let mut branch = DocGraph::default();
    branch.atoms.insert(1, Atom::Alive);
    branch.atoms.insert(2, Atom::Alive); // the branch's discovery
    let conferred = vec![BranchCap { target, debit_reach: false }];
    let settlement_held = conferred.clone();
    (
        Stitch {
            main,
            branch,
            conferred,
        },
        settlement_held,
    )
}

fn bench_membrane(c: &mut Criterion) {
    let mut group = c.benchmark_group(format!("membrane/{}", regime()));
    group.sample_size(50);

    // ---- FORK: deep-clone my world into a confined sub-world ----------------
    group.bench_function("fork", |b| {
        let (world, _owner, _guest, _docs) = membrane_world();
        b.iter(|| {
            let fork = world.fork();
            black_box(fork);
        });
    });

    // ---- MINT: construct the fork (grant the embedded cap) ------------------
    group.bench_function("mint", |b| {
        b.iter_batched(
            || {
                let (world, owner, guest, docs) = membrane_world();
                (world.fork(), owner, guest, docs)
            },
            |(mut fork, owner, guest, docs)| {
                let sf = mint(&mut fork, owner, guest, docs);
                debug_assert_eq!(sf.embedded.len(), 1, "docs is embedded");
                black_box((fork, sf));
            },
            BatchSize::SmallInput,
        );
    });

    // ---- DRIVE: the guest commits an embedded turn through the gate ---------
    // The guest, holding the embedded docs cap, drains 1 unit of docs's balance to the owner.
    group.bench_function("drive_embedded", |b| {
        b.iter_batched(
            || {
                let (world, owner, guest, docs) = membrane_world();
                let mut fork = world.fork();
                let sf = mint(&mut fork, owner, guest, docs);
                (fork, sf, owner, docs)
            },
            |(mut fork, sf, owner, docs)| {
                // An embedded exercise (touches no boundary) → commits locally, no consent.
                let turn = fork.turn(sf.guest, vec![transfer(docs, owner, 1)]);
                let mut used: HashSet<[u8; 32]> = HashSet::new();
                let out = sf.commit_turn_gated(&mut fork, owner, turn, None, &[], 0, &mut used);
                black_box(out);
            },
            BatchSize::SmallInput,
        );
    });

    // ---- STITCH: reconcile the branch graph back into main ------------------
    group.bench_function("stitch_settle", |b| {
        let (_w, _owner, _guest, docs) = membrane_world();
        let (stitch, settlement_held) = stitch_inputs(docs);
        b.iter(|| {
            let outcome = stitch.settle(black_box(&settlement_held), None);
            black_box(outcome);
        });
    });

    // ---- ROUNDTRIP: fork → mint → drive → stitch (the whole lifecycle) ------
    group.bench_function("roundtrip", |b| {
        b.iter_batched(
            membrane_world,
            |(world, owner, guest, docs)| {
                let mut fork = world.fork();
                let sf = mint(&mut fork, owner, guest, docs);
                let turn = fork.turn(sf.guest, vec![transfer(docs, owner, 1)]);
                let mut used: HashSet<[u8; 32]> = HashSet::new();
                let _ = sf.commit_turn_gated(&mut fork, owner, turn, None, &[], 0, &mut used);
                let (stitch, held) = stitch_inputs(docs);
                let outcome = stitch.settle(&held, Some(&BTreeSet::from([1u64, 2u64])));
                black_box(outcome);
            },
            BatchSize::SmallInput,
        );
    });

    group.finish();
}

criterion_group!(benches, bench_membrane);
criterion_main!(benches);
