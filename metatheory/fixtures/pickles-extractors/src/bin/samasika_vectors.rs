//! samasika_vectors — DIFFERENTIAL VECTOR EXTRACTOR for Ouroboros Samasika chain selection.
//!
//! This binary drives **openmina's own `mina_core::consensus`** — the functions a running
//! openmina node uses to decide fork choice — over real Mina protocol states, and emits the
//! scalar projections plus openmina's verdicts as a Lean fixture. The Lean
//! (`Dregg2.Bridge.MinaChainSelection`) then checks its `def`s against those verdicts.
//!
//! ⚑ WHY THE EXTRACTOR LIVES HERE AND NOT IN `../mina-rust`: an extractor parked inside a
//! third-party checkout is one `git clean` from gone (the Kimchi extractors were, and that
//! lesson was paid for). The FIXTURES are copied in too, at
//! `metatheory/fixtures/samasika-forks/` — they came from `mina-rust/tests/files/forks/`, are
//! real protocol states, and are what openmina's own `long_range_fork` / `short_range_fork`
//! tests assert against.
//!
//! ## What openmina is and is not authoritative for
//!
//! openmina is a SECOND rendering, not the canonical one. The canonical implementation is the
//! OCaml daemon (`~/dev/mina/src/lib/consensus/proof_of_stake.ml`). Where the two disagree the
//! Lean follows the OCaml, and the disagreement is itself recorded — see
//! `Dregg2.Bridge.MinaChainSelection` §8. Concretely, `mina_core::consensus` is a transcription
//! of the *spec document* (`mina/docs/specs/consensus/README.md` §5.4.12), and that document's
//! §5.4.12 pseudocode is itself inconsistent with its own §5.4.9.
//!
//! So this differential is run in TWO tracks, both emitted:
//!   * `om_*`   — openmina's verdicts (what this binary observes).
//!   * `oc_*`   — the OCaml `Min_window_density.update_min_window_density` semantics,
//!                transcribed here ONLY so the emitted vectors record BOTH numbers side by
//!                side and the divergence is a datum rather than a claim. The Lean's own
//!                `virtualMinWindowDensity` is checked against `oc_*`, its
//!                `relMinWindowDensityOpenmina` against `om_*`.
//!
//! Run:  cargo run --release --bin samasika_vectors

use mina_core::consensus::{
    consensus_take, is_short_range_fork, long_range_fork_take, relative_min_window_density,
    short_range_fork_take,
};
use mina_p2p_messages::v2::{
    ConsensusProofOfStakeDataConsensusStateValueStableV2 as ConsensusState, StateHash,
};
use std::path::{Path, PathBuf};

/// mainnet/devnet consensus constants. Sources, all in `~/dev/mina`:
///   `src/config/mainnet.mlh:15-20` (identical in `src/config/devnet.mlh:15-20`)
///   `src/lib/consensus/constants.ml:239` grace_period_end = grace_period_slots + slots_per_window
const SLOTS_PER_SUB_WINDOW: u32 = 7;
const SUB_WINDOWS_PER_WINDOW: u32 = 11;
const GRACE_PERIOD_SLOTS: u32 = 2160;
const GRACE_PERIOD_END_OCAML: u32 =
    GRACE_PERIOD_SLOTS + SLOTS_PER_SUB_WINDOW * SUB_WINDOWS_PER_WINDOW; // 2237

fn global_slot(c: &ConsensusState) -> u32 {
    c.curr_global_slot_since_hard_fork.slot_number.as_u32()
}

fn slots_per_epoch(c: &ConsensusState) -> u32 {
    c.curr_global_slot_since_hard_fork.slots_per_epoch.as_u32()
}

fn densities(c: &ConsensusState) -> Vec<u32> {
    c.sub_window_densities.iter().map(|d| d.as_u32()).collect()
}

/// The OCaml `Min_window_density.update_min_window_density` with `~incr_window:false`,
/// transcribed from `proof_of_stake.ml:1221-1335`. Returns only the min window density.
fn ocaml_update_mwd(
    prev_global_slot: u32,
    next_global_slot: u32,
    prev_sub: &[u32],
    prev_min: u32,
) -> u32 {
    let prev_gsw = prev_global_slot / SLOTS_PER_SUB_WINDOW;
    let next_gsw = next_global_slot / SLOTS_PER_SUB_WINDOW;
    let prev_rel = prev_gsw % SUB_WINDOWS_PER_WINDOW;
    let next_rel = next_gsw % SUB_WINDOWS_PER_WINDOW;
    let same = prev_gsw == next_gsw;
    let overlapping = prev_gsw + SUB_WINDOWS_PER_WINDOW >= next_gsw;
    let mut cur_density = 0u32;
    for (i, d) in prev_sub.iter().enumerate() {
        let i = i as u32;
        let gt_prev = i > prev_rel;
        let lt_next = i < next_rel;
        let within = if prev_rel < next_rel {
            gt_prev && lt_next
        } else {
            gt_prev || lt_next
        };
        let keep = same || (overlapping && !within);
        if keep {
            cur_density += d;
        }
    }
    if same || next_global_slot < GRACE_PERIOD_END_OCAML {
        prev_min
    } else {
        cur_density.min(prev_min)
    }
}

/// The OCaml `select`'s `virtual_min_window_density` (`proof_of_stake.ml:3048`).
fn ocaml_virtual_mwd(s: &ConsensusState, max_slot: u32) -> u32 {
    if global_slot(s) == max_slot {
        s.min_window_density.as_u32()
    } else {
        ocaml_update_mwd(
            global_slot(s),
            max_slot,
            &densities(s),
            s.min_window_density.as_u32(),
        )
    }
}

/// `is_short_range` per the OCaml (`proof_of_stake.ml:2951`): keyed on `curr_epoch`
/// (= `curr_global_slot / slots_per_epoch`, `global_slot.ml:77`), NOT on `epoch_count`,
/// and with `Slot.succ` applied before `in_seed_update_range`.
fn ocaml_is_short_range(c1: &ConsensusState, c2: &ConsensusState) -> bool {
    let epoch = |c: &ConsensusState| global_slot(c) / slots_per_epoch(c);
    let slot = |c: &ConsensusState| global_slot(c) % slots_per_epoch(c);
    // slot.ml:9 — divides the CONSTANTS' slots_per_epoch. Both fixtures and mainnet carry the
    // same value in the state, so we read it off the state being tested.
    let in_seed_update_range = |c: &ConsensusState, s: u32| {
        let third = slots_per_epoch(c) / 3;
        s < third * 2
    };
    let pred_case = |a: &ConsensusState, b: &ConsensusState| {
        epoch(a) + 1 == epoch(b)
            && !in_seed_update_range(a, slot(a) + 1)
            && a.next_epoch_data.lock_checkpoint == b.staking_epoch_data.lock_checkpoint
    };
    if epoch(c1) == epoch(c2) {
        c1.staking_epoch_data.lock_checkpoint == c2.staking_epoch_data.lock_checkpoint
    } else {
        pred_case(c1, c2) || pred_case(c2, c1)
    }
}

/// The OCaml `select` (`proof_of_stake.ml:2971`), returning `true` for `` `Take ``.
/// The tie-break chain is exactly OCaml's: length, then `Blake2b(last_vrf_output)` compared
/// bytewise (`String.compare` on the raw digest), then the state hash compared as a FIELD
/// ELEMENT (the derived `compare` on `Snark_params.Tick.Field.t`; `StateHash`'s `Ord` here is
/// the same numeric order — `BigInt` holds `field.into_bigint()`).
fn ocaml_select(e: &ConsensusState, c: &ConsensusState, eh: &StateHash, ch: &StateHash) -> bool {
    let vrf_bigger = || {
        let (ev, cv) = (e.last_vrf_output.blake2b(), c.last_vrf_output.blake2b());
        ev < cv || (ev == cv && ch > eh)
    };
    let length_longer = || {
        e.blockchain_length.as_u32() < c.blockchain_length.as_u32()
            || (e.blockchain_length.as_u32() == c.blockchain_length.as_u32() && vrf_bigger())
    };
    if ocaml_is_short_range(e, c) {
        length_longer()
    } else {
        let max_slot = global_slot(e).max(global_slot(c));
        let (de, dc) = (
            ocaml_virtual_mwd(e, max_slot),
            ocaml_virtual_mwd(c, max_slot),
        );
        de < dc || (de == dc && length_longer())
    }
}

fn hash_decimal(h: &StateHash) -> String {
    // `StateHash` derefs to `BigInt`, which holds `field.into_bigint()` — the CANONICAL
    // representation (mina-p2p-messages `src/bigint.rs:100`). `to_decimal` is therefore the
    // numeric value of the field element, which is exactly what the OCaml `compare` on
    // `Snark_params.Tick.Field.t` orders by.
    h.to_decimal()
}

fn ck_decimal(h: &StateHash) -> String {
    hash_decimal(h)
}

fn vrf_hex(c: &ConsensusState) -> String {
    c.last_vrf_output
        .blake2b()
        .iter()
        .map(|b| format!("{b:02x}"))
        .collect()
}

struct Pair {
    name: String,
    tip: ConsensusState,
    cnd: ConsensusState,
    tip_hash: StateHash,
    cnd_hash: StateHash,
    /// `Some(expected)` when the fixture name encodes openmina's own asserted decision.
    fixture_expect: Option<bool>,
    fixture_branch: Option<&'static str>,
}

/// ⚑ The fixture JSONs predate a field rename in `mina-p2p-messages`: they carry
/// `consensus_state.curr_global_slot`, and the current generated type calls it
/// `curr_global_slot_since_hard_fork` (`crates/p2p-messages/src/v2/generated.rs:204`). openmina's
/// OWN `short_range_fork` / `long_range_fork` tests deserialize these same files with
/// `serde_json::from_str::<MinaStateProtocolStateValueStableV2>` and therefore no longer parse
/// them — i.e. the only tests openmina has over its chain-selection code do not currently run.
/// We rename the key and go on; nothing else about the state is touched.
fn fixup(mut cs: serde_json::Value) -> serde_json::Value {
    if let Some(o) = cs.as_object_mut() {
        if let Some(gs) = o.remove("curr_global_slot") {
            o.insert("curr_global_slot_since_hard_fork".into(), gs);
        }
    }
    cs
}

fn load_pair(dir: &Path, prefix: &str, tip: &str, cnd: &str) -> (ConsensusState, ConsensusState) {
    let rd = |suffix: &str| {
        let p: PathBuf = dir.join(format!("{prefix}-{tip}-{cnd}-{suffix}.json"));
        let s = std::fs::read_to_string(&p).unwrap_or_else(|e| panic!("{}: {e}", p.display()));
        let v: serde_json::Value = serde_json::from_str(&s).unwrap();
        // Deserialize the CONSENSUS STATE only. The enclosing `MinaStateProtocolStateValueStableV2`
        // has drifted in ways unrelated to selection (`constants.grace_period_slots` was added),
        // and nothing in chain selection reads those fields.
        let cs = v
            .get("body")
            .and_then(|b| b.get("consensus_state"))
            .cloned()
            .unwrap_or_else(|| panic!("{}: no body.consensus_state", p.display()));
        serde_json::from_value::<ConsensusState>(fixup(cs))
            .unwrap_or_else(|e| panic!("{}: {e}", p.display()))
    };
    (rd("tip"), rd("cnd"))
}

fn main() {
    let dir = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../samasika-forks");
    let dir = dir
        .canonicalize()
        .expect("metatheory/fixtures/samasika-forks");

    // The five real fork fixtures, with the decision openmina's own tests assert
    // (`mina-rust/crates/core/src/consensus.rs:404-440`).
    let specs: Vec<(&str, &str, &str, &'static str, bool)> = vec![
        (
            "long-take-density-92-97",
            "3NLESd9gzU52bDWSXL5uUAYbCojHXSVdeBX4sCMF3V8Ns9D1Sriy",
            "3NLQfKJ4kBagLgmiwyiVw9zbi53tiNy8TNu2ua1jmCyEecgbBJoN",
            "long",
            true,
        ),
        (
            "long-keep-density-161-166",
            "3NKY1kxHMRfjBbjfAA5fsasUCWFF9B7YqYFfNH4JFku6ZCUUXyLG",
            "3NLFoBQ6y3nku79LQqPgKBmuo5Ngnpr7rfZygzdRrcPtz2gewRFC",
            "long",
            false,
        ),
        (
            "short-take-length-60-61",
            "3NLQEb5mXqXCL34rueHrMkUVyWSQ7aYjvi6K98ZdpEnTozef69uR",
            "3NKuw8mvieV9RLpdRmHb4kxg7NWR83TfwzNkVmJCeHUmVWFdUQCp",
            "short",
            true,
        ),
        (
            "short-take-vrf-99-99",
            "3NL4kAA33FRs9K66GvVNupNT94L4shALtYLHJRfmxhdZV8iPg2pi",
            "3NKC9F6mgtvRiHgYxiPBt1P5QDYaPVpD3YWyJhjmJZkNnT7RYitm",
            "short",
            true,
        ),
        (
            "short-keep-vrf-117-117",
            "3NLWvDBFYJ2NXZ1EKMZXHB52zcbVtosHPArn4cGj8pDKkYsTHNnC",
            "3NKLEnUBTAhC95XEdJpLvJPqAUuvkC176tFKyLDcXUcofXXgQUvY",
            "short",
            false,
        ),
    ];

    let mut pairs: Vec<Pair> = Vec::new();
    for (prefix, tip_h, cnd_h, branch, expect) in &specs {
        let (tip, cnd) = load_pair(&dir, prefix, tip_h, cnd_h);
        pairs.push(Pair {
            name: (*prefix).to_string(),
            tip,
            cnd,
            tip_hash: tip_h.parse().unwrap(),
            cnd_hash: cnd_h.parse().unwrap(),
            fixture_expect: Some(*expect),
            fixture_branch: Some(branch),
        });
    }

    // Derived pairs: slide the candidate's global slot forward so the projected-window
    // machinery is actually exercised (the raw fixtures sit at tiny slot deltas). Everything
    // else is untouched, so the comparison stays a comparison of REAL states.
    let base = pairs[0].tip.clone();
    let base_h: StateHash = specs[0].1.parse().unwrap();
    let other_h: StateHash = specs[0].2.parse().unwrap();
    let set_slot = |c: &ConsensusState, s: u32| {
        let mut c = c.clone();
        c.curr_global_slot_since_hard_fork.slot_number =
            mina_p2p_messages::v2::MinaNumbersGlobalSlotSinceHardForkMStableV1::SinceHardFork(
                s.into(),
            );
        c
    };
    for delta in [1u32, 6, 7, 8, 13, 14, 20, 70, 77, 78, 100, 1000, 5000] {
        pairs.push(Pair {
            name: format!("derived-slotdelta-{delta}"),
            tip: base.clone(),
            cnd: set_slot(&pairs[0].cnd, global_slot(&pairs[0].cnd) + delta),
            tip_hash: base_h.clone(),
            cnd_hash: other_h.clone(),
            fixture_expect: None,
            fixture_branch: None,
        });
    }
    // ⚑ The raw fixtures all sit BELOW both grace-period ends (openmina's hardcoded 1440 and the
    // OCaml `grace_period_slots + slots_per_window` = 2237), so the density branch short-circuits
    // to `prev_min_window_density` on every one of them and the projection machinery is never
    // exercised. Lift both states above 2237 and vary the gap: this is the region where the two
    // implementations are actually being asked a question.
    let hi_base = 10_000u32;
    for delta in [
        0u32, 1, 6, 7, 8, 13, 14, 15, 21, 28, 42, 70, 76, 77, 78, 84, 100, 200,
    ] {
        pairs.push(Pair {
            name: format!("derived-hi-10000-{}", hi_base + delta),
            tip: set_slot(&base, hi_base),
            cnd: set_slot(&pairs[0].cnd, hi_base + delta),
            tip_hash: base_h.clone(),
            cnd_hash: other_h.clone(),
            fixture_expect: None,
            fixture_branch: None,
        });
    }
    // ⚑ The SAME pairs with the roles swapped — EXISTING is the state at the HIGHER slot, the
    // CANDIDATE lags. This is the orientation in which the two implementations can return
    // different VERDICTS, not merely different densities: openmina collapses the lagging
    // candidate's window to zero, the OCaml preserves it whenever the gap is under one window.
    for delta in [1u32, 6, 7, 8, 13, 14, 15, 21, 28, 42, 70, 76, 77, 78, 84] {
        pairs.push(Pair {
            name: format!("derived-swapped-{}-10000", hi_base + delta),
            tip: set_slot(&base, hi_base + delta),
            cnd: set_slot(&pairs[0].cnd, hi_base),
            tip_hash: base_h.clone(),
            cnd_hash: other_h.clone(),
            fixture_expect: None,
            fixture_branch: None,
        });
    }
    // Straddling the two grace-period ends: 1440 (openmina's hardcoded constant) and 2237 (the
    // OCaml value, `grace_period_slots 2160 + slots_per_window 77`).
    for (a, b) in [
        (1400u32, 1430u32),
        (1400, 1500),
        (2000, 2100),
        (2200, 2230),
        (2200, 2300),
        (2230, 2240),
    ] {
        pairs.push(Pair {
            name: format!("derived-grace-{a}-{b}"),
            tip: set_slot(&base, a),
            cnd: set_slot(&pairs[0].cnd, b),
            tip_hash: base_h.clone(),
            cnd_hash: other_h.clone(),
            fixture_expect: None,
            fixture_branch: None,
        });
    }

    // ── the Lean fixture ──────────────────────────────────────────────────────────────────────
    let out_lean = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("out/MinaSelectionVectors.lean");
    let mut lean = String::new();
    lean.push_str(
        "/-\n\
         # Dregg2.Bridge.MinaSelectionVectors — GENERATED. Do not hand-edit.\n\n\
         Emitted by `metatheory/fixtures/pickles-extractors/src/bin/samasika_vectors.rs`, which\n\
         drives **openmina's own `mina_core::consensus`** over the real Mina protocol states in\n\
         `metatheory/fixtures/samasika-forks/` (copied from `mina-rust/tests/files/forks/`, the\n\
         fixtures openmina's own `short_range_fork` / `long_range_fork` tests assert against) plus\n\
         slot-shifted derivatives of them. Each row carries the eight fields\n\
         `MinaChainSelection.select` reads for both sides, plus:\n\n\
         * `omShort` / `omRelE` / `omRelC` / `omTake` — what OPENMINA computed;\n\
         * `ocShort` / `ocVmwdE` / `ocVmwdC` / `ocTake` — the OCaml daemon's semantics\n\
         (`proof_of_stake.ml`), transcribed in the same extractor so both numbers come from ONE\n\
         run over ONE state.\n\n\
         `MinaChainSelectionDifferential` checks the Lean `def`s against BOTH columns.\n\
         -/\n\
         import Dregg2.Bridge.MinaChainSelection\n\n\
         set_option autoImplicit false\n\n\
         namespace Dregg2.Bridge.MinaSelectionVectors\n\n\
         open Dregg2.Bridge.MinaChainSelection\n\n\
         /-- One differential row. -/\n\
         structure Vec where\n\
         \x20 /-- Fixture name. -/\n\
         \x20 name : String\n\
         \x20 /-- The EXISTING chain's consensus state. -/\n\
         \x20 e : ConsensusState\n\
         \x20 /-- The CANDIDATE chain's consensus state. -/\n\
         \x20 c : ConsensusState\n\
         \x20 /-- The existing tip's state hash, as a field element. -/\n\
         \x20 eh : Nat\n\
         \x20 /-- The candidate tip's state hash, as a field element. -/\n\
         \x20 ch : Nat\n\
         \x20 /-- OCaml `is_short_range`. -/\n\
         \x20 ocShort : Bool\n\
         \x20 /-- OCaml `virtual_min_window_density` of the existing chain. -/\n\
         \x20 ocVmwdE : Nat\n\
         \x20 /-- OCaml `virtual_min_window_density` of the candidate chain. -/\n\
         \x20 ocVmwdC : Nat\n\
         \x20 /-- OCaml `select` = `Take`. -/\n\
         \x20 ocTake : Bool\n\
         \x20 /-- openmina `is_short_range_fork`. -/\n\
         \x20 omShort : Bool\n\
         \x20 /-- openmina `relative_min_window_density existing candidate`. -/\n\
         \x20 omRelE : Nat\n\
         \x20 /-- openmina `relative_min_window_density candidate existing`. -/\n\
         \x20 omRelC : Nat\n\
         \x20 /-- openmina `consensus_take`. -/\n\
         \x20 omTake : Bool\n\n\
         /-- The extracted vectors. -/\n\
         def vectors : List Vec := [\n",
    );

    // Header. One row per ORDERED pair; the Lean re-reads every column.
    println!("# samasika differential vectors");
    println!("# openmina rev: see metatheory/fixtures/pickles-extractors/README.md");
    println!(
        "# cols: name\tbranch\tfx_expect\tom_short\toc_short\t\
         e_len\te_mwd\te_dens\te_slot\te_spe\te_stakelock\te_nextlock\te_vrf\te_hash\te_epochcount\t\
         c_len\tc_mwd\tc_dens\tc_slot\tc_spe\tc_stakelock\tc_nextlock\tc_vrf\tc_hash\tc_epochcount\t\
         om_relmwd_e\tom_relmwd_c\toc_vmwd_e\toc_vmwd_c\tom_short_take\tom_long_take\tom_take\toc_take"
    );
    for p in &pairs {
        let e = &p.tip;
        let c = &p.cnd;
        let max_slot = global_slot(e).max(global_slot(c));
        let om_short = is_short_range_fork(e, c);
        let oc_short = ocaml_is_short_range(e, c);
        let row = [
            p.name.clone(),
            p.fixture_branch.unwrap_or("-").to_string(),
            p.fixture_expect
                .map(|b| if b { "take" } else { "keep" }.to_string())
                .unwrap_or_else(|| "-".into()),
            om_short.to_string(),
            oc_short.to_string(),
            e.blockchain_length.as_u32().to_string(),
            e.min_window_density.as_u32().to_string(),
            densities(e)
                .iter()
                .map(|d| d.to_string())
                .collect::<Vec<_>>()
                .join(","),
            global_slot(e).to_string(),
            slots_per_epoch(e).to_string(),
            ck_decimal(&e.staking_epoch_data.lock_checkpoint),
            ck_decimal(&e.next_epoch_data.lock_checkpoint),
            vrf_hex(e),
            hash_decimal(&p.tip_hash),
            e.epoch_count.as_u32().to_string(),
            c.blockchain_length.as_u32().to_string(),
            c.min_window_density.as_u32().to_string(),
            densities(c)
                .iter()
                .map(|d| d.to_string())
                .collect::<Vec<_>>()
                .join(","),
            global_slot(c).to_string(),
            slots_per_epoch(c).to_string(),
            ck_decimal(&c.staking_epoch_data.lock_checkpoint),
            ck_decimal(&c.next_epoch_data.lock_checkpoint),
            vrf_hex(c),
            hash_decimal(&p.cnd_hash),
            c.epoch_count.as_u32().to_string(),
            relative_min_window_density(e, c).to_string(),
            relative_min_window_density(c, e).to_string(),
            ocaml_virtual_mwd(e, max_slot).to_string(),
            ocaml_virtual_mwd(c, max_slot).to_string(),
            short_range_fork_take(e, c, &p.tip_hash, &p.cnd_hash)
                .0
                .to_string(),
            long_range_fork_take(e, c, &p.tip_hash, &p.cnd_hash)
                .0
                .to_string(),
            consensus_take(e, c, &p.tip_hash, &p.cnd_hash).to_string(),
            ocaml_select(e, c, &p.tip_hash, &p.cnd_hash).to_string(),
        ];
        println!("{}", row.join("\t"));

        let cs_lean = |s: &ConsensusState, lock: &StateHash, next: &StateHash| {
            format!(
                "{{ mkCS {} {} [{}] [{}] {} {} {} {} with epochCount := {} }}",
                s.blockchain_length.as_u32(),
                s.min_window_density.as_u32(),
                densities(s)
                    .iter()
                    .map(|d| d.to_string())
                    .collect::<Vec<_>>()
                    .join(","),
                s.last_vrf_output
                    .blake2b()
                    .iter()
                    .map(|b| b.to_string())
                    .collect::<Vec<_>>()
                    .join(","),
                global_slot(s),
                slots_per_epoch(s),
                lock.to_decimal(),
                next.to_decimal(),
                s.epoch_count.as_u32()
            )
        };
        lean.push_str(&format!(
            "  ⟨\"{}\",\n   {},\n   {},\n   {}, {}, {}, {}, {}, {}, {}, {}, {}, {}⟩,\n",
            p.name,
            cs_lean(
                e,
                &e.staking_epoch_data.lock_checkpoint,
                &e.next_epoch_data.lock_checkpoint
            ),
            cs_lean(
                c,
                &c.staking_epoch_data.lock_checkpoint,
                &c.next_epoch_data.lock_checkpoint
            ),
            hash_decimal(&p.tip_hash),
            hash_decimal(&p.cnd_hash),
            oc_short,
            ocaml_virtual_mwd(e, max_slot),
            ocaml_virtual_mwd(c, max_slot),
            ocaml_select(e, c, &p.tip_hash, &p.cnd_hash),
            om_short,
            relative_min_window_density(e, c),
            relative_min_window_density(c, e),
            consensus_take(e, c, &p.tip_hash, &p.cnd_hash),
        ));

        // GROUND TRUTH ASSERTS, in Rust, before a number is believed downstream.
        if let (Some(exp), Some(branch)) = (p.fixture_expect, p.fixture_branch) {
            let got = match branch {
                "short" => short_range_fork_take(e, c, &p.tip_hash, &p.cnd_hash).0,
                _ => long_range_fork_take(e, c, &p.tip_hash, &p.cnd_hash).0,
            };
            assert_eq!(got, exp, "fixture {} branch {branch}", p.name);
        }
    }

    lean.push_str("]\n\nend Dregg2.Bridge.MinaSelectionVectors\n");
    std::fs::create_dir_all(out_lean.parent().unwrap()).unwrap();
    std::fs::write(&out_lean, lean).unwrap();
    eprintln!("[emit] {} ({} vectors)", out_lean.display(), pairs.len());

    // A standing, LOUD report of the OCaml-vs-openmina density divergence over these vectors.
    let mut diverged = 0usize;
    for p in &pairs {
        let e = &p.tip;
        let c = &p.cnd;
        let max_slot = global_slot(e).max(global_slot(c));
        if relative_min_window_density(e, c) != ocaml_virtual_mwd(e, max_slot)
            || relative_min_window_density(c, e) != ocaml_virtual_mwd(c, max_slot)
        {
            diverged += 1;
        }
    }
    eprintln!(
        "[divergence] openmina relative_min_window_density != OCaml virtual_min_window_density \
         on {diverged}/{} vectors",
        pairs.len()
    );
    let mut short_diverged = 0usize;
    for p in &pairs {
        if is_short_range_fork(&p.tip, &p.cnd) != ocaml_is_short_range(&p.tip, &p.cnd) {
            short_diverged += 1;
        }
    }
    eprintln!(
        "[divergence] openmina is_short_range_fork != OCaml is_short_range on {short_diverged}/{} vectors",
        pairs.len()
    );
    let mut decision_diverged = 0usize;
    for p in &pairs {
        if consensus_take(&p.tip, &p.cnd, &p.tip_hash, &p.cnd_hash)
            != ocaml_select(&p.tip, &p.cnd, &p.tip_hash, &p.cnd_hash)
        {
            decision_diverged += 1;
            eprintln!("[decision-divergence] {}", p.name);
        }
    }
    eprintln!(
        "[divergence] openmina consensus_take != OCaml select on {decision_diverged}/{} vectors",
        pairs.len()
    );
}
