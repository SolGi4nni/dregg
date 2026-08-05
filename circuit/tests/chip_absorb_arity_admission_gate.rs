//! # THE CHIP-ABSORB ARITY GATE — a Lean emitter cannot ask the chip for an arity it does not admit
//!
//! ## The wound
//!
//! `57105f387` found that the wide **blinded** membership descriptor had been **unprovable from
//! the day it was written**. Its blinding tooth emitted a `TID_P2` lookup at **arity 9**; the chip
//! AIR carries its admitted arities as a degree-7 product over the arity column, and 9 is not a
//! root of it, so **no witness exists** — for that constraint, at that row, ever. Nothing reported
//! this. It surfaced only when somebody tried to prove against the descriptor, which for a staged
//! descriptor may be never.
//!
//! And a second, quieter mode rode along: at arity 9 the deployed witness generator's `seed456`
//! blend is LOW (it is high only at 7, 11 and 16), so lane 4 receives the **arity tag** and lanes
//! 5 and 6 receive **zero** — three of the eight member lanes the emitter handed the chip never
//! entered the preimage at all. An arity that silently discards its inputs is *worse* than one
//! that is refused, because the descriptor looks like it worked.
//!
//! ## What this gate does
//!
//! Three things, in the order that matters.
//!
//! **1. It DERIVES the admitted set by running the chip.** There is no list of admitted arities in
//! this file, and there must never be — a constant re-typed beside its own definition is
//! decoration, not a gate. [`dregg_circuit::descriptor_ir2::chip_air_row_accepts`] builds the
//! honest chip row the DEPLOYED witness generator emits (`chip_absorb_row`, the very function
//! `build_traces` calls) and runs the DEPLOYED `Ir2Air::Chip` constraint evaluator over it. An
//! arity is admitted iff that row satisfies the AIR. The sweep is exhaustive over every arity a
//! chip tuple can carry, and the gate independently refuses an arity outside that range, so there
//! is no gap between "swept" and "decided".
//!
//! **2. It DERIVES the per-lane genuineness map the same way**, by probing the AIR with a unit
//! input in each lane: the AIR's "inputs beyond the arity are ZERO" pins make a non-zero in a
//! pinned lane unsatisfiable, and the probe reports exactly that.
//!
//! **3. It DERIVES the lane-DROP map from a genuinely independent source** — the deployed absorb
//! `chip_absorb_all_lanes`, i.e. the witness generator's own behaviour, with the AIR nowhere in
//! sight. A lane is dropped at an arity iff perturbing it changes no output lane. The two maps are
//! then required to agree in the dangerous direction (`AIR permits ⟹ generator uses`), which is
//! the "two independently-derived sources" the repo's own doctrine asks for, and the descriptor
//! scan uses BOTH: a populated lane must be neither AIR-pinned nor generator-dropped.
//!
//! ⓘ **Say what the drop check does and does not add, at today's chip.** `lane_maps_agree_…`
//! passes, which is exactly the statement that *at every ADMITTED arity, a dropped lane is also a
//! pinned lane* — so on the admitted set the drop check finds nothing the pin check would miss,
//! and that is a property of this chip, not a guarantee. Where it earns its keep is off the
//! admitted set, and that is where the wound was: at arity 9 (and at 8 and 14) it is the check
//! that distinguishes **refused** from **silently discarded**, which are different bugs and want
//! different fixes. It also stands as the tripwire for the day the seeding blend and the pins stop
//! agreeing — the failure mode `lane_maps_agree_…` exists to catch and nothing else would.
//!
//! ## What it scans
//!
//! Every emitted descriptor on disk: `circuit/descriptors/`, its `by-name/` registry, the
//! Lean-emitted trees, the benchmark generators, the mirror-gate canaries, the drift-taxonomy
//! fixtures — discovered by walking the tree rather than by a hand list, so a new registry cannot
//! be born outside the gate. The **staged registry TSVs** carry whole descriptors inside a tab
//! field and are parsed out of it. Descriptors are decoded with the DEPLOYED
//! `parse_vm_descriptor2`, never a second JSON reader.
//!
//! ⚑ **The Lean-authored TABLE AIRs are in scope too, and were NOT until 2026-08-01.**
//! `circuit/descriptors/table-airs/*.json` advertise `"ir": 2` like every other emission, but they
//! are a different object (`"kind": "table_air"`) and `parse_vm_descriptor2` refuses them — so from
//! the moment the first one landed, this gate reported each as *"advertises `ir: 2` and the
//! deployed parser refuses"* and went RED, while auditing NONE of their chip tuples. Both halves
//! were wrong in the same direction: the corpus that had grown was the one the gate stopped
//! reading. They are now decoded with the DEPLOYED `parse_table_air` and their chip-bus
//! interactions run through the SAME admission and lane checks as a descriptor `Lookup` — one
//! implementation, so a table AIR cannot be audited by a laxer copy. That matters most for
//! `dregg-ir2-map-absent-v1`, whose 17 `ir2_p2` queries are the live in-circuit double-spend gate.
//!
//! ⚑ **…AND THE SAME WOUND RECURRED ONE LEVEL DOWN, 2026-08-02.** `ExactPublicTable` emits a
//! FAMILY — a JSON **array** of table-air objects, one per declared tuple arity — and the singleton
//! `parse_table_air` refuses an array at byte 0. So from the hour that artifact landed this gate
//! was RED again, on a parse error, having audited none of the family's tuples: the corpus that had
//! grown was once more the one the gate stopped reading. The array form now routes to the DEPLOYED
//! `parse_table_air_family` and every member is scanned. ⚠ The general lesson is the one
//! `36e80c2db` already paid for on two other tools — *a reader that sniffs a SINGLETON grammar goes
//! blind, not red, the day the emitter learns to emit a family* — and this gate was the third tool
//! with the same sniff and was not fixed with them.
//!
//! ⚠ **One directory is excluded and it is named here**: `circuit/tests/fixtures/
//! chip-arity-gate-redproof/`, which holds the pre-`57105f387` arity-9 descriptor this gate's own
//! red-proof runs against. `redproof_fixture_is_red` asserts the exclusion is not hiding a green:
//! pointed straight at that directory the gate MUST fail.

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};

use dregg_circuit::descriptor_ir2::{
    CHIP_RATE, CHIP_TUPLE_LEN, EffectVmDescriptor2, LookupSpec, TID_P2, TID_P2_NARROW,
    TID_P2_STATE16, VmConstraint2, chip_absorb_all_lanes, chip_air_row_accepts,
    parse_vm_descriptor2, parse_vm_descriptor2_unsound_oversized,
};
use dregg_circuit::field::BabyBear;
use dregg_circuit::lean_descriptor_air::LeanExpr;
use dregg_circuit::plonky3_prover::POSEIDON2_WIDTH;
use dregg_circuit::table_air::TableExpr;
use dregg_circuit::table_air::{BusOp, LeanTableAir, parse_table_air};

// ============================================================================
// §1 — the three maps, each DERIVED
// ============================================================================

/// How far above `CHIP_RATE` the ADMISSION sweep looks. A chip tuple carries `CHIP_RATE` input
/// lanes, so an arity above that is refused structurally (§3) and never reaches the derived set;
/// the sweep runs past it anyway so the gate can *report* that nothing is admitted up there
/// rather than assume it. [`chip_air_row_accepts`] is total on this range — it writes the arity
/// into the tuple's arity column and asks the AIR, and the AIR simply refuses.
const SWEEP_CEILING: u32 = 4 * CHIP_RATE as u32;

/// ⚠ **The GENERATOR sweep stops at `CHIP_RATE`, and this is a domain fact, not a convenience.**
/// [`chip_absorb_all_lanes`] is the deployed witness generator's absorb; it reads at most
/// `CHIP_RATE` input lanes and **asserts** `arity <= CHIP_RATE` (`descriptor_ir2.rs:4523`). Asking
/// it about arity 17 is not a question with a false answer, it is a question outside its domain —
/// and asking anyway is how this gate spent its first day: every one of its six tests aborted at
/// `a = 17` with that assertion, so the gate reported NOTHING, in either direction, including on
/// the descriptor it was written for. A sweep bound that outruns the function under test turns a
/// gate into a panic.
///
/// Nothing is lost by stopping here: §3 refuses `arity > CHIP_RATE` structurally, before any lane
/// is consulted, and `admitted_arity_set_is_derived_from_the_chip` proves the admitted set lies
/// entirely at or below `CHIP_RATE` — so no admitted arity goes un-swept.
const DROP_SWEEP_CEILING: u32 = CHIP_RATE as u32;

/// **The admitted set, derived.** For each candidate arity, hand the deployed AIR the honest
/// all-zero-input chip row at that arity and ask whether its constraints vanish.
fn derive_admitted_arities() -> BTreeSet<u32> {
    let zeros = [BabyBear::ZERO; CHIP_RATE];
    (0..=SWEEP_CEILING)
        .filter(|&a| chip_air_row_accepts(a, &zeros))
        .collect()
}

/// **The AIR's genuine-lane map, derived.** Lane `i` is genuine at arity `a` iff the honest row
/// carrying a non-zero in lane `i` (and nothing else) still satisfies the AIR. Where the AIR pins
/// the lane to zero, it cannot.
fn derive_air_genuine_lanes(a: u32) -> Vec<bool> {
    (0..CHIP_RATE)
        .map(|i| {
            let mut ins = [BabyBear::ZERO; CHIP_RATE];
            ins[i] = BabyBear::ONE;
            chip_air_row_accepts(a, &ins)
        })
        .collect()
}

/// **The witness generator's lane-drop map, derived — and the AIR is not consulted.** Lane `i` is
/// DROPPED at arity `a` iff perturbing it leaves every exposed output lane of the deployed absorb
/// unchanged, i.e. the value the emitter handed the chip never entered the preimage.
///
/// Three independent probe values are used. `chip_absorb_all_lanes` exposes 8 of the 16 lanes of
/// the final permutation state, so a *seeded* lane could in principle collide with the baseline on
/// all eight; three distinct probes puts that at ~2^-744, and the map is cross-checked against the
/// AIR-derived one in [`lane_maps_agree_in_the_dangerous_direction`] regardless.
///
/// ⚠ Defined only on `a <= DROP_SWEEP_CEILING` — see that constant. The guard is a hard refusal
/// rather than a clamp: a caller that walks past the absorb's domain is asking a question the
/// deployed generator does not answer, and it must say so here rather than have the assertion
/// inside `chip_absorb_all_lanes` abort the whole test binary.
fn derive_dropped_lanes(a: u32) -> Vec<bool> {
    assert!(
        a <= DROP_SWEEP_CEILING,
        "the deployed absorb is undefined above arity {DROP_SWEEP_CEILING} (it asserts \
         `arity <= CHIP_RATE`); sweep admission with SWEEP_CEILING, the generator with \
         DROP_SWEEP_CEILING"
    );
    const PROBES: [u32; 3] = [1, 2, 0x0123_4567];
    let baseline = chip_absorb_all_lanes(a as usize, &[BabyBear::ZERO; CHIP_RATE]);
    (0..CHIP_RATE)
        .map(|i| {
            PROBES.iter().all(|&p| {
                let mut ins = [BabyBear::ZERO; CHIP_RATE];
                ins[i] = BabyBear::new(p);
                chip_absorb_all_lanes(a as usize, &ins) == baseline
            })
        })
        .collect()
}

// ============================================================================
// §2 — the descriptor corpus
// ============================================================================

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("crate dir has a parent")
        .to_path_buf()
}

/// Directories the walk never enters: build output, VCS, vendored/third-party trees, and the one
/// deliberate carve-out (this gate's own red-proof fixture, asserted red by `redproof_fixture_is_red`).
const PRUNE: &[&str] = &[
    "target",
    ".git",
    "node_modules",
    ".lake",
    "vendor",
    ".cache",
    "chip-arity-gate-redproof",
];

/// A parsed descriptor plus where it came from, for the report.
struct Found {
    origin: String,
    desc: EffectVmDescriptor2,
}

/// A cheap prefilter so the walk can look at every `.json` in the tree without reading all of it:
/// an IR-v2 descriptor declares `"ir": 2` in its first object.
fn looks_like_ir2(head: &str) -> bool {
    let Some(p) = head.find("\"ir\"") else {
        return false;
    };
    head[p + 4..]
        .trim_start()
        .strip_prefix(':')
        .map(|r| r.trim_start().starts_with('2'))
        .unwrap_or(false)
}

fn read_head(path: &Path, n: usize) -> Option<String> {
    let bytes = std::fs::read(path).ok()?;
    let end = bytes.len().min(n);
    Some(String::from_utf8_lossy(&bytes[..end]).into_owned())
}

/// Walk `root` and collect every emitted descriptor: `.json` files that parse as IR-v2, plus every
/// descriptor embedded in a tab field of a staged registry `.tsv`.
fn collect_descriptors(root: &Path) -> (Vec<Found>, Vec<String>, Vec<FoundTable>) {
    let mut found = Vec::new();
    let mut unparsable = Vec::new();
    let mut tables = Vec::new();
    let mut stack = vec![root.to_path_buf()];
    while let Some(dir) = stack.pop() {
        let Ok(rd) = std::fs::read_dir(&dir) else {
            continue;
        };
        for e in rd.flatten() {
            let p = e.path();
            let name = e.file_name().to_string_lossy().into_owned();
            let Ok(ft) = e.file_type() else { continue };
            if ft.is_dir() {
                if PRUNE.contains(&name.as_str()) || name.starts_with('.') {
                    continue;
                }
                stack.push(p);
            } else if ft.is_file() && name.ends_with(".json") {
                let Some(head) = read_head(&p, 8192) else {
                    continue;
                };
                if !looks_like_ir2(&head) {
                    continue;
                }
                let Ok(text) = std::fs::read_to_string(&p) else {
                    continue;
                };
                // ⚑ A Lean-authored TABLE AIR advertises `"ir": 2` too, and is a DIFFERENT object.
                // Route it to the deployed table decoder rather than letting the descriptor parser
                // refuse it — a refusal here reads as "the gate found something" while actually
                // meaning "the gate stopped reading this corpus".
                if looks_like_table_air(&head) {
                    // ⚑ …and a table AIR may be emitted as a FAMILY — a JSON ARRAY of the same
                    // object, one member per declared tuple arity (`ExactPublicTable`). The
                    // singleton decoder refuses an array at byte 0, which is the identical
                    // "the gate stopped reading this corpus" failure one level down: the gate went
                    // RED naming a parse error while auditing none of the family's chip tuples.
                    // Both forms route to their own DEPLOYED decoder.
                    let parsed = if text.trim_start().starts_with('[') {
                        dregg_circuit::table_air::parse_table_air_family(&text)
                    } else {
                        parse_table_air(&text).map(|t| vec![t])
                    };
                    match parsed {
                        Ok(ts) => tables.extend(ts.into_iter().map(|t| FoundTable {
                            origin: rel(root, &p),
                            table: t,
                        })),
                        Err(e) => unparsable.push(format!("{}: {e}", rel(root, &p))),
                    }
                    continue;
                }
                match parse_ir2_widest(&text) {
                    Ok(desc) => found.push(Found {
                        origin: rel(root, &p),
                        desc,
                    }),
                    // A file that ADVERTISES `"ir": 2` and will not decode is itself a finding —
                    // the gate must not silently narrow its own corpus.
                    Err(e) => unparsable.push(format!("{}: {e}", rel(root, &p))),
                }
            } else if ft.is_file() && name.ends_with(".tsv") {
                let Ok(text) = std::fs::read_to_string(&p) else {
                    continue;
                };
                for (ln, line) in text.lines().enumerate() {
                    for field in line.split('\t') {
                        let f = field.trim();
                        if !f.starts_with('{') || !looks_like_ir2(f) {
                            continue;
                        }
                        match parse_ir2_widest(f) {
                            Ok(desc) => found.push(Found {
                                origin: format!("{}:{}", rel(root, &p), ln + 1),
                                desc,
                            }),
                            Err(e) => unparsable.push(format!("{}:{} {e}", rel(root, &p), ln + 1)),
                        }
                    }
                }
            }
        }
    }
    found.sort_by(|a, b| a.origin.cmp(&b.origin));
    tables.sort_by(|a, b| a.origin.cmp(&b.origin));
    unparsable.sort();
    (found, unparsable, tables)
}

/// Does this JSON head declare the TABLE-AIR wire kind? Matched on the emitted key so a descriptor
/// can never be mistaken for one; `parse_table_air` re-checks it and refuses otherwise.
fn looks_like_table_air(head: &str) -> bool {
    head.contains("\"kind\":\"table_air\"") || head.contains("\"kind\": \"table_air\"")
}

/// A decoded Lean-authored table AIR and where it came from.
struct FoundTable {
    origin: String,
    table: LeanTableAir,
}

/// ⚑ This gate is about CHIP ARITY, not coefficient width, so it must keep the widest corpus:
/// strict first, and on the oversized-constant refusal (2026-08-03) retry through the NAMED
/// unsound entry rather than narrowing itself. The descriptors that need the retry are enumerated
/// and counted in `ir2_oversized_constant_refusal.rs`; a re-emit on the felt-sized encoding
/// (`Dregg2.Circuit.Emit.PastaFieldSound`) removes them.
fn parse_ir2_widest(text: &str) -> Result<EffectVmDescriptor2, String> {
    match parse_vm_descriptor2(text) {
        Err(e) if e.contains("does not fit a BabyBear felt") => {
            parse_vm_descriptor2_unsound_oversized(text)
        }
        other => other,
    }
}

fn rel(root: &Path, p: &Path) -> String {
    p.strip_prefix(root).unwrap_or(p).display().to_string()
}

// ============================================================================
// §3 — the check, per chip lookup
// ============================================================================

/// The input-lane count of a chip tuple on each bus. All three shapes are `[arity, inputs…, …]`,
/// so the lanes live at `tuple[1 ..= lanes]` uniformly.
fn chip_input_lanes(table: usize) -> Option<usize> {
    match table {
        // `[arity, in0..in15, out0..out7]` and `[arity, in0..in15, out0]`.
        TID_P2 | TID_P2_NARROW => Some(CHIP_RATE),
        // `[arity, state16, next_state16]` — the raw full-width permutation relation.
        TID_P2_STATE16 => Some(POSEIDON2_WIDTH),
        _ => None,
    }
}

/// A lane is POPULATED unless the emitter wrote the literal constant zero into it. Fail-closed on
/// purpose: an expression that merely happens to evaluate to zero at run time is still an emitter
/// routing a value into a lane, and a gate that reasons about run-time values is not a gate.
fn populated(e: &LeanExpr) -> bool {
    !matches!(e, LeanExpr::Const(0))
}

/// The input-lane count of a chip tuple on each BUS. The three strings are the deployed `BUS_*`
/// constants (`descriptor_ir2.rs`), read here rather than re-derived: a table AIR names its buses
/// by string because the buses cross-cut the five-table `TableId` roster.
fn chip_input_lanes_for_bus(bus: &str) -> Option<usize> {
    match bus {
        "ir2_p2" | "ir2_p2_narrow" => Some(CHIP_RATE),
        "ir2_p2_state16" => Some(POSEIDON2_WIDTH),
        _ => None,
    }
}

/// One chip-bus tuple, reduced to what §3 actually checks: the arity TAG (iff it is a wire
/// constant), the bus's input-lane count, and per lane whether the emitter routed a value in.
///
/// ⚑ Both corpora reduce to this — a descriptor `Lookup` over `LeanExpr`, and a Lean TABLE AIR
/// interaction over `TableExpr` — so the admission and lane checks have exactly ONE
/// implementation. A second copy for the table AIRs is how one of them ends up laxer.
struct ChipTuple {
    at: String,
    lanes: usize,
    arity: Option<i64>,
    /// Per input lane: whether it is POPULATED, and how it renders in a finding.
    lane: Vec<(bool, String)>,
}

struct Verdict {
    violations: Vec<String>,
    lookups: usize,
    descriptors: usize,
    /// Chip tuples audited on Lean-authored TABLE AIRs (a subset of `lookups`).
    table_lookups: usize,
}

/// The admission + per-lane checks, for ONE chip tuple from either corpus.
fn check_chip_tuple(
    v: &mut Verdict,
    genuine: &[Vec<bool>],
    dropped: &[Vec<bool>],
    admitted: &BTreeSet<u32>,
    t: &ChipTuple,
) {
    v.lookups += 1;
    let at = &t.at;

    // -- The arity must be a wire CONSTANT. The chip's whole domain separation is the arity TAG;
    //    an arity chosen by the witness is not gateable and not separated.
    let Some(c) = t.arity else {
        v.violations.push(format!(
            "{at}: chip lookup arity is a witness expression, not a constant — \
             the chip's domain separation IS the arity tag"
        ));
        return;
    };
    if !(0..=CHIP_RATE as i64).contains(&c) {
        v.violations.push(format!(
            "{at}: arity {c} is outside 0..={CHIP_RATE} — the tuple has only \
             {CHIP_RATE} input lanes to seed"
        ));
        return;
    }
    let a = c as u32;

    // -- 1. ADMISSION. Derived from the AIR, never restated.
    if !admitted.contains(&a) {
        v.violations.push(format!(
            "{at}: arity {a} is NOT ADMITTED by the chip AIR (derived admitted set: \
             {admitted:?}) — this descriptor is UNPROVABLE, no witness exists"
        ));
        // Still report the lane damage below: the two modes are independent findings.
    }

    // -- 2/3. Per-lane: AIR-pinned, and generator-dropped.
    for i in 0..t.lanes {
        let Some((pop, render)) = t.lane.get(i) else {
            break;
        };
        if !pop {
            continue;
        }
        if !genuine[a as usize][i] {
            v.violations.push(format!(
                "{at}: lane in{i} carries {render} but the chip AIR PINS in{i} to zero at \
                 arity {a} — unsatisfiable"
            ));
        }
        if dropped[a as usize][i] {
            v.violations.push(format!(
                "{at}: lane in{i} carries {render} but the deployed absorb DROPS in{i} at \
                 arity {a} — the value never enters the preimage, and the descriptor \
                 looks like it worked"
            ));
        }
    }
}

fn audit(found: &[Found], tables: &[FoundTable], admitted: &BTreeSet<u32>) -> Verdict {
    // Derived once, consulted per lookup. Both are only ever indexed at an arity §3 has already
    // bounded by `CHIP_RATE`, so the generator leg stops at its own domain edge.
    let genuine: Vec<Vec<bool>> = (0..=SWEEP_CEILING).map(derive_air_genuine_lanes).collect();
    let dropped: Vec<Vec<bool>> = (0..=DROP_SWEEP_CEILING).map(derive_dropped_lanes).collect();

    let mut v = Verdict {
        violations: Vec::new(),
        lookups: 0,
        descriptors: found.len(),
        table_lookups: 0,
    };
    for f in found {
        for (ci, k) in f.desc.constraints.iter().enumerate() {
            let VmConstraint2::Lookup(l) = k else {
                continue;
            };
            let Some(lanes) = chip_input_lanes(l.table) else {
                continue;
            };
            let t = ChipTuple {
                at: format!("{} [{}] constraint {ci}", f.origin, f.desc.name),
                lanes,
                arity: match l.tuple.first() {
                    Some(LeanExpr::Const(c)) => Some(*c),
                    _ => None,
                },
                lane: l
                    .tuple
                    .iter()
                    .skip(1)
                    .map(|e| (populated(e), format!("{e:?}")))
                    .collect(),
            };
            check_chip_tuple(&mut v, &genuine, &dropped, admitted, &t);
        }
    }
    // ⚑ The SAME checks over the Lean-authored TABLE AIRs, whose chip absorbs were dark until
    // 2026-08-01 (see the module doc). Their tuples are `TableExpr` rather than `LeanExpr`; only
    // the two leaf predicates differ, and both reduce into the shared `ChipTuple` above.
    for f in tables {
        for (ii, i) in f.table.interactions.iter().enumerate() {
            let Some(lanes) = chip_input_lanes_for_bus(&i.bus) else {
                continue;
            };
            // ⚑ **THE SERVING SIDE IS NOT AN ASK, and conflating them was a real hazard the moment
            // the SERVER became a Lean artifact (2026-08-02, the `Ir2Air::Chip` cutover).**
            //
            // This gate's whole contract is that every *client* names a CONSTANT arity from the
            // admitted set — the chip's domain separation IS the tag, so a witness-controlled arity
            // on a query lets one row answer for two domains. The chip TABLE's own legs are
            // `BusOp::Provide`: it is the one object that serves ALL seven arities from one table,
            // so its tuple's first element is necessarily the `CHIP_ARITY` COLUMN. Auditing it as a
            // client reported two findings that say only "the server is a server".
            //
            // ⚠ It is skipped here and NOT left unchecked: what binds the served arity is the
            // degree-7 membership gate, and `admitted_arity_set_is_derived_from_the_chip` DERIVES
            // the admitted set by probing that gate through the real deployed evaluator — so the
            // set this gate audits every client against comes from the server's own algebra, and
            // `Emit/ChipTableEmit.lean`'s `arity_in_declared_set` proves it admits no eighth root.
            // `the_chip_table_serves_and_does_not_query` below pins the sides.
            if i.op == BusOp::Provide {
                continue;
            }
            v.table_lookups += 1;
            let t = ChipTuple {
                at: format!("{} [{}] interaction {ii}", f.origin, f.table.name),
                lanes,
                arity: match i.tuple.first() {
                    Some(TableExpr::Const(c)) => Some(*c),
                    _ => None,
                },
                lane: i
                    .tuple
                    .iter()
                    .skip(1)
                    .map(|e| (!matches!(e, TableExpr::Const(0)), format!("{e:?}")))
                    .collect(),
            };
            check_chip_tuple(&mut v, &genuine, &dropped, admitted, &t);
        }
    }
    v
}

// ============================================================================
// §4 — the gate
// ============================================================================

#[test]
fn admitted_arity_set_is_derived_from_the_chip() {
    let admitted = derive_admitted_arities();
    println!("chip AIR admitted arities (DERIVED by probing Ir2Air::Chip): {admitted:?}");
    for a in 0..=SWEEP_CEILING {
        if !admitted.contains(&a) {
            continue;
        }
        let g = derive_air_genuine_lanes(a);
        // Sound because the last assertion in this test proves every admitted arity is `<=
        // CHIP_RATE` = `DROP_SWEEP_CEILING`, which is exactly the absorb's domain.
        let d = derive_dropped_lanes(a);
        let air_ok: Vec<usize> = (0..CHIP_RATE).filter(|&i| g[i]).collect();
        let drp: Vec<usize> = (0..CHIP_RATE).filter(|&i| d[i]).collect();
        println!("  arity {a:2}: AIR-genuine lanes {air_ok:?} · absorb-dropped lanes {drp:?}");
    }
    assert!(
        !admitted.is_empty(),
        "the probe found NO admitted arity — the probe is broken, not the chip"
    );
    assert!(
        admitted.len() < (SWEEP_CEILING as usize + 1),
        "the probe admitted EVERY arity — it is not reading the admission constraint"
    );
    // PROSE ↔ MACHINE cross-check, and nothing downstream reads it: `57105f387`'s commit message
    // and `descriptor_ir2.rs`'s chip comment both state {0,2,3,4,7,11,16}. The audit in
    // `every_emitted_descriptor_asks_the_chip_for_an_admitted_arity` consumes the DERIVED set.
    let documented: BTreeSet<u32> = [0, 2, 3, 4, 7, 11, 16].into_iter().collect();
    assert_eq!(
        admitted, documented,
        "the chip AIR's admitted set has MOVED away from what the tree says it is — \
         update the prose (and every emitter), do not widen this assertion"
    );
    // Nothing is admitted above the tuple's own lane count, so §3's structural refusal of
    // `arity > CHIP_RATE` closes no honest door.
    assert!(
        admitted.iter().all(|&a| a <= CHIP_RATE as u32),
        "an arity above CHIP_RATE is admitted — the structural bound in §3 would refuse it"
    );
}

#[test]
fn lane_maps_agree_in_the_dangerous_direction() {
    // Two independently-derived sources: the AIR's zero-pins, and the deployed absorb's behaviour.
    // The DANGEROUS disagreement is a lane the AIR permits and the generator throws away — that is
    // a value an emitter may route, that binds nothing. The reverse (the generator seeds a lane
    // the AIR pins to zero) is inert: the pin means no descriptor can put anything there.
    // The generator's own domain edge — the dangerous disagreement can only be exhibited where the
    // generator runs, and above `CHIP_RATE` the AIR admits nothing anyway.
    let mut bad = Vec::new();
    let mut inert = Vec::new();
    for a in 0..=DROP_SWEEP_CEILING {
        let g = derive_air_genuine_lanes(a);
        let d = derive_dropped_lanes(a);
        for i in 0..CHIP_RATE {
            if g[i] && d[i] {
                bad.push(format!(
                    "arity {a} lane in{i}: AIR permits it, the absorb DROPS it"
                ));
            }
            if !g[i] && !d[i] {
                inert.push((a, i));
            }
        }
    }
    println!(
        "AIR-pinned-but-seeded (inert, the safe direction): {} lane/arity pairs",
        inert.len()
    );
    assert!(bad.is_empty(), "SILENT-DROP HOLE:\n  {}", bad.join("\n  "));
}

/// Files that advertise `"ir": 2` and that the DEPLOYED parser refuses. Each is a stub fixture
/// belonging to a DIFFERENT gate (`scripts/check-mirror-gates.sh`, whose canary trees exist to be
/// mutated), carries no chip lookup, and is not an emitted descriptor. The list is a **RATCHET**:
/// a stale entry — one that has been repaired, deleted, or has grown into a real descriptor — is a
/// FAILURE, so an exemption cannot outlive its reason. Anything not on it is a finding: the gate
/// must never narrow its own corpus quietly.
const UNPARSABLE_EXEMPT: &[(&str, &str)] = &[
    (
        "scripts/mirror-gates/canary/clean/circuit-prove/tests/welded_local_golden.json",
        "mirror-gate canary stub: 4-field toy, no public_input_count, no constraints",
    ),
    (
        "scripts/mirror-gates/canary/clean/circuit/descriptors/by-name/canary.json",
        "mirror-gate canary stub: the clean side of the canary pair",
    ),
    (
        "scripts/mirror-gates/canary/mirrors/G1__drifted_local_golden/circuit-prove/tests/drifted_local_golden.json",
        "mirror-gate canary stub: DELIBERATELY drifted — that is the canary",
    ),
];

/// ⚑ **THE CHIP TABLE IS THE SERVER, and its sides are pinned rather than assumed.** The audit
/// above skips `Provide` legs because a server's arity is necessarily a column; that skip is only
/// sound if the chip's legs really ARE all `Provide` and it queries the absorb buses NOWHERE. A
/// table that queried what it should serve makes the bus unsatisfiable in one direction and vacuous
/// in the other, with no gate involved — invisible to every other check in this file.
#[test]
fn the_chip_table_serves_and_does_not_query() {
    for t in [
        dregg_circuit::table_air::chip_table_air(),
        dregg_circuit::table_air::chip_state16_table_air(),
    ] {
        assert!(!t.interactions.is_empty(), "{}: no bus legs at all", t.name);
        for i in &t.interactions {
            assert_eq!(
                i.op,
                BusOp::Provide,
                "{}: leg on {} is a {:?}; the chip SERVES every one of its buses",
                t.name,
                i.bus,
                i.op
            );
        }
    }
    // …and the legacy chip serves exactly the three buses, on the two absorb ones plus the fact
    // bus, so a dropped leg is visible here and not only in the Lean `#guard`s.
    let chip = dregg_circuit::table_air::chip_table_air();
    assert_eq!(chip.bus_count_op("ir2_p2", BusOp::Provide), 1);
    assert_eq!(chip.bus_count_op("ir2_p2_narrow", BusOp::Provide), 1);
    assert_eq!(chip.bus_count_op("ir2_fact", BusOp::Provide), 1);
    assert_eq!(chip.bus_count_on("ir2_p2_state16"), 0);
    let s16 = dregg_circuit::table_air::chip_state16_table_air();
    assert_eq!(s16.bus_count_op("ir2_p2_state16", BusOp::Provide), 1);
    assert_eq!(s16.bus_count_on("ir2_p2"), 0);
    assert_eq!(s16.bus_count_on("ir2_fact"), 0);
}

#[test]
fn every_emitted_descriptor_asks_the_chip_for_an_admitted_arity() {
    // The walk root is overridable ONLY so the gate's own blindness floor can be demonstrated
    // (`scripts/check-chip-absorb-arity.sh --self-test` points it at an empty directory and
    // requires this test to FAIL). Unset — every real run — it is the repo.
    let root = std::env::var_os("DREGG_CHIP_ARITY_GATE_ROOT")
        .map(PathBuf::from)
        .unwrap_or_else(repo_root);
    let admitted = derive_admitted_arities();
    let (found, unparsable, tables) = collect_descriptors(&root);
    let v = audit(&found, &tables, &admitted);

    println!(
        "scanned {} descriptors + {} Lean table AIRs ({} chip tuples, {} of them on table AIRs) \
         under {}",
        v.descriptors,
        tables.len(),
        v.lookups,
        v.table_lookups,
        root.display()
    );
    let mut hist: std::collections::BTreeMap<(usize, i64), usize> = Default::default();
    for f in &found {
        for k in &f.desc.constraints {
            if let VmConstraint2::Lookup(l) = k
                && chip_input_lanes(l.table).is_some()
                && let Some(LeanExpr::Const(c)) = l.tuple.first()
            {
                *hist.entry((l.table, *c)).or_default() += 1;
            }
        }
    }
    println!("(table, arity) -> lookups: {hist:?}");

    // Everything is reported in ONE verdict — a gate that stops at its first finding measures less
    // than it claims to, and the counts below are what a reader needs.
    let mut report: Vec<String> = Vec::new();

    // A corpus that collapses to nothing is the failure mode this whole file exists to catch, so
    // the gate refuses to report clean on a dead reader.
    if v.descriptors < 100 || v.lookups < 1000 {
        report.push(format!(
            "THE WALK COLLAPSED: {} descriptors, {} chip lookups — a gate that reads nothing \
             reports clean",
            v.descriptors, v.lookups
        ));
    }
    for u in &unparsable {
        let path = u.split(':').next().unwrap_or(u);
        if !UNPARSABLE_EXEMPT.iter().any(|(p, _)| *p == path) {
            report.push(format!(
                "advertises \"ir\": 2 and the deployed parser refuses — {u}"
            ));
        }
    }
    for (p, why) in UNPARSABLE_EXEMPT {
        if !unparsable.iter().any(|u| u.starts_with(p)) {
            report.push(format!(
                "STALE EXEMPTION (ratchet): {p} now parses, is gone, or moved — drop the row \
                 (it was exempt because: {why})"
            ));
        }
    }
    report.extend(v.violations.iter().cloned());

    assert!(
        report.is_empty(),
        "{} finding(s) from the chip-absorb arity gate:\n  {}",
        report.len(),
        report.join("\n  ")
    );
}

// ============================================================================
// §5 — both directions, on the real bug
// ============================================================================

/// The path the gate deliberately excludes from its tree walk. Pointed straight at it, the gate
/// MUST go red — otherwise the exclusion is hiding a green and the walk's clean verdict means
/// nothing.
fn redproof_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/chip-arity-gate-redproof")
}

/// **ANTI-VACUITY: the gate catches the bug that motivated it, at the state it was in.**
///
/// The fixture is the wide blinded membership descriptor **as it stood before `57105f387`**,
/// reconstructed from that commit's parent — specifically from the byte-pinned emitted-wire golden
/// the pre-fix Lean emitter carried for itself
/// (`57105f387^:metatheory/Dregg2/Circuit/Emit/BlindedMembershipWideEmit.lean`, the
/// `#eval repr (emitVmJson2 blindedMembershipWideDesc)` literal). It is not a fixture anybody
/// invented for this test; it is what the emitter emitted.
///
/// The gate must report BOTH modes on it: arity 9 inadmissible, and lanes 4/5/6 dropped.
#[test]
fn redproof_fixture_is_red() {
    let admitted = derive_admitted_arities();
    let (found, unparsable, tables) = collect_descriptors(&redproof_dir());
    assert!(unparsable.is_empty(), "{unparsable:?}");
    assert!(
        tables.is_empty(),
        "the red-proof fixture holds no table AIR"
    );
    assert_eq!(found.len(), 1, "expected exactly the pre-fix golden");
    assert_eq!(
        found[0].desc.name,
        "dregg-blinded-membership-4ary-wide-general::v1"
    );

    let v = audit(&found, &tables, &admitted);
    for s in &v.violations {
        println!("RED · {s}");
    }
    assert!(
        v.violations
            .iter()
            .any(|s| s.contains("arity 9 is NOT ADMITTED")),
        "the gate did not catch the inadmissible arity 9 it exists to catch: {:?}",
        v.violations
    );
    for lane in [4usize, 5, 6] {
        assert!(
            v.violations
                .iter()
                .any(|s| s.contains(&format!("DROPS in{lane} at arity 9"))),
            "the gate did not catch the SILENT DROP of lane in{lane} at arity 9: {:?}",
            v.violations
        );
    }
    // Lanes 0..3 and 7..8 carry the rest of the leaf + the blinding felt; the AIR pins every input
    // lane at an inadmissible arity, so all nine populated lanes are reported.
    assert!(
        v.violations
            .iter()
            .filter(|s| s.contains("PINS in"))
            .count()
            == 9,
        "expected all 9 populated lanes reported as AIR-pinned at arity 9, got {:?}",
        v.violations
    );
}

/// **The GREEN direction, on the SAME descriptor.** `57105f387` re-emitted
/// `dregg-blinded-membership-4ary-wide-general::v1` from Lean at arity 11 (`cur8 ‖ r ‖ 0 ‖ 0`).
/// That descriptor is on disk at HEAD and the gate passes it — so the red above is the defect
/// being detected, not the gate refusing everything it is shown.
#[test]
fn the_corrected_descriptor_is_green() {
    let admitted = derive_admitted_arities();
    let path = repo_root().join("circuit/descriptors/by-name/blinded-membership-4ary-wide.json");
    let text = std::fs::read_to_string(&path).expect("the corrected golden is on disk");
    let desc = parse_vm_descriptor2(&text).expect("it parses");
    assert_eq!(desc.name, "dregg-blinded-membership-4ary-wide-general::v1");
    let found = vec![Found {
        origin: path.display().to_string(),
        desc,
    }];
    let v = audit(&found, &[], &admitted);
    assert!(
        v.violations.is_empty(),
        "the CORRECTED descriptor is red — {:?}",
        v.violations
    );
    assert!(
        v.lookups >= 4,
        "it should carry the fold + the blinding tooth"
    );
}

/// A synthetic tooth for each of the two modes independently, so neither can pass on the other's
/// evidence: an admitted arity with a populated lane the generator drops, and an inadmissible
/// arity with clean lanes.
#[test]
fn each_mode_bites_on_its_own() {
    let admitted = derive_admitted_arities();
    let mk = |arity: i64, populated_lane: usize| {
        let mut tuple = vec![LeanExpr::Const(0); CHIP_TUPLE_LEN];
        tuple[0] = LeanExpr::Const(arity);
        tuple[1 + populated_lane] = LeanExpr::Var(0);
        EffectVmDescriptor2 {
            name: "synthetic".into(),
            trace_width: 1,
            public_input_count: 0,
            challenges: 0,
            tables: Vec::new(),
            constraints: vec![VmConstraint2::Lookup(LookupSpec {
                table: TID_P2,
                tuple,
            })],
            hash_sites: Vec::new(),
            ranges: Vec::new(),
        }
    };

    // MODE A — arity 4 IS admitted, and lane in4 is exactly where the arity tag goes. A populated
    // in4 is both AIR-pinned and generator-dropped.
    let a = audit(
        &[Found {
            origin: "modeA".into(),
            desc: mk(4, 4),
        }],
        &[],
        &admitted,
    );
    for s in &a.violations {
        println!("RED · {s}");
    }
    assert!(a.violations.iter().all(|s| !s.contains("NOT ADMITTED")));
    assert!(
        a.violations
            .iter()
            .any(|s| s.contains("DROPS in4 at arity 4"))
    );

    // MODE B — arity 5 is not admitted at all, lane in0 populated.
    let b = audit(
        &[Found {
            origin: "modeB".into(),
            desc: mk(5, 0),
        }],
        &[],
        &admitted,
    );
    for s in &b.violations {
        println!("RED · {s}");
    }
    assert!(
        b.violations
            .iter()
            .any(|s| s.contains("arity 5 is NOT ADMITTED"))
    );

    // The control: arity 16 with a populated lane in15 is the deployed node8 row, and clean.
    let c = audit(
        &[Found {
            origin: "control".into(),
            desc: mk(16, 15),
        }],
        &[],
        &admitted,
    );
    assert!(
        c.violations.is_empty(),
        "the control went red: {:?}",
        c.violations
    );
}
