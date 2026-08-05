//! # The BUCKETED MSM on the machine — the routing `PastaMsmLayouts` §7.3 called inexpressible,
//! proved in both polarities, in RELEASE.
//!
//! ## Substrate, said out loud (HOUSE LAW #1)
//!
//! **The AIR is Lean-authored.** `dregg-pasta-msm-bucketed-c<c>::v1` is
//! `Dregg2.Circuit.Emit.PastaMsmBucketed.bucketedRowDesc n nbits c MinaWrapSrsG.SRS_G SCAL` — 94
//! constraints, of which the first 45 are `PastaMsmWindowed.windowedRowDesc`'s row template
//! verbatim (`bucketedRowDesc_extends_windowed` proves the prefix in the Lean kernel), so the RCB
//! complete add in every row is the same `PastaCurveComplete.pallasCompleteAdd` the whole cone
//! shares. Nothing in this file authors a constraint, a builder gadget or an `air_accepts`
//! predicate: it reads the descriptor's own manifests, fills trace CELLS, and runs the deployed
//! prover. **When the prover refuses a trace, the WITNESS is wrong.**
//!
//! ## What the layout is, and why it needs no new IR
//!
//! Pippenger's buckets are replaced by a FUSED running sum. Sweeping the digit level `d` from
//! `D = 2^c − 1` down to `0` and keeping `RUN = Σ_{i : d_i ≥ d} g_i`, the identity
//! `Σ_i d_i·g_i = Σ_{d≥1} Σ_{i : d_i ≥ d} g_i` says the buckets never have to exist. So **nothing
//! is ever stored at a witness-dependent address and nothing is ever read back** — which is the
//! whole reason §7.3's `MemOp`/new-constraint-kind pricing does not apply.
//!
//! What IS data-dependent is the ORDER in which generators are consumed, and order is exactly what
//! a permutation quantifies over. `DescriptorIR2.PublicLookupBalanced` demands the trace's lookup
//! log be a `Perm` of the declared manifest — not a `Sublist` — so one exact-public table
//! (`pasta_msm_cover`, the `(window, generator, digit)` grid) forces every generator to be folded
//! exactly once per window at exactly its declared digit. **Three deployed teeth, zero new IR.**
//!
//! ## The instances, and what each is for
//!
//!   * `c = 2`: `n = 27` real Mina SRS generators, `W = 2` windows, `D = 3` levels,
//!     `2·(2 + 27 + 3) = 64` rows × 612 columns.
//!   * `c = 3`: `n = 54` generators, `W = 2`, `D = 7`, `2·(3 + 54 + 7) = 128` rows × 612 columns.
//!   * ⚑ the ξ-AGGREGATE of Mina devnet block 539508: `n = 59`, `nbits = 255`, `c = 2`,
//!     **8 192 rows × 804 columns, 475 constraints** — 612 of those columns the row template, 192
//!     the CHALLENGE BLOCK, and the extra 384 constraints its pins and threads.
//!
//! Heights are powers of two because the deployed prover refuses a non-power-of-two base trace AND
//! a permutation manifest's length IS the trace height. That is a parameter-choice constraint on
//! the emitter, not a property of the layout.
//!
//! ## ⚑ RELEASE, DELIBERATELY
//!
//! Algebraic refusals are `debug_assert` PANICS in debug and clean `Err(..)` in release. A refusal
//! test that passes only in debug is testing the assertion, not the constraint system.
//!
//! ## ⚑ WHICH MECHANISM MUST REFUSE
//!
//! The cone records the trap: a forgery that left the limb width was caught by a RANGE LOOKUP, so
//! the gate under test never ran. Every tamper below names the mechanism that must object, and the
//! forged-`sg` case is deliberately a forgery **the arithmetic cannot see** — a claimed commitment
//! displaced by one generator, which only the PI binding can catch.
//!
//! ## ⚑ AND WHAT THE ξ-AGGREGATE'S 192 WIRE FELTS ARE NOT
//!
//! `scripts/check-descriptor-anchor-inertness.py` scores this descriptor at **192 decorative
//! anchors — 192 of 219 public inputs, the largest row in that census**. It is right, and
//! `the_published_basis_is_not_yet_bound_to_the_declared_digits` at the bottom of this file is that
//! verdict on the deployed prover: the aggregate proves against a basis that is not the block's
//! own. The two teeth above it prove the pin and the thread FIRE; that one shows what they do not
//! reach. Read all three together before citing any of them.
//!
//! Run: `cargo test -p dregg-circuit --release --test pasta_msm_bucketed_prove -- --nocapture`

// ⚑ These descriptors carry 495-bit gate coefficients (the `PastaField` value heads), so they
// parse only through the NAMED unsound entry, exactly as every other `pasta-rcb-*` artifact does.
// The felt-sized replacement encoding is `Dregg2.Circuit.Emit.PastaFieldSound`; nothing in this
// file's subject matter (the ROUTING) depends on which multiply the rows are denominated in, and
// `PastaMsmBucketed` §7.2 says so out loud rather than letting the row counts read as sound ones.
use dregg_circuit::BabyBear;
use dregg_circuit::descriptor_ir2::{
    DreggStarkConfig, EffectVmDescriptor2, MemBoundaryWitness, TableSem, VmConstraint2,
    parse_vm_descriptor2_unsound_oversized, prove_vm_descriptor2, prove_vm_descriptor2_with_config,
    verify_vm_descriptor2, verify_vm_descriptor2_with_config,
};
use dregg_circuit::pasta_msm::{complete_add, on_curve_at, proj_eq_at};
use dregg_circuit::pasta_windowed_witness::{
    NUM_LIMBS, P_PASTA, Pt, Q_PASTA, U256, fill_row_at, read_field,
};
use dregg_circuit::plonky3_prover::create_config_with_fri_full;
use dregg_circuit::refusal::{
    Refusal, assert_violated_constraint_not_bus, must_refuse, must_refuse_or_unsat_panic,
};
use sha2::{Digest, Sha256};
use std::time::Instant;

// ---------------------------------------------------------------------------------------------
// The Lean-emitted artifacts, sha256-pinned so a silent re-emit cannot slide under a green test.
// ---------------------------------------------------------------------------------------------

const C2_JSON: &str = include_str!("fixtures/pasta-msm-bucketed/pasta-msm-bucketed-c2.json");
const C3_JSON: &str = include_str!("fixtures/pasta-msm-bucketed/pasta-msm-bucketed-c3.json");

/// ⚑ The INHERITED row template, emitted into THIS campaign's own fixture directory rather than
/// read from `circuit/descriptors/by-name/`. Same object, but a by-name artifact sits on the
/// descriptor-drift gate's hot path and belongs to every lane at once: on 2026-08-05 a sibling
/// lane's new `challenges` wire field made every committed by-name descriptor refuse to load until
/// re-emitted, and a prefix check that reads one inherits that lane's flag days. Owning the
/// comparand is what `circuit/tests/fixtures/pasta-sg-bound/` already does.
const WINDOWED_JSON: &str = include_str!("fixtures/pasta-msm-bucketed/pasta-rcb-windowed.json");
const WINDOWED_SHA: &str = "7c1326f8c705aad8d9165bc97d7c2926a98b2d7ec0bdc756b85eaa36d8886aad";

/// ⚑ THE VESTA/STEP INSTANCE — the curve the deferred accumulator actually lives on.
const V2_JSON: &str = include_str!("fixtures/pasta-msm-bucketed/pasta-msm-bucketed-vesta-c2.json");
const V2_SHA: &str = "b580a8f199a1acca7607429242342f55741aba43b5c41b18ab679caa0621706e";

/// ⚑ **THE ξ-AGGREGATE OF A REAL MINA BLOCK, on this layout.** Emitted by
/// `EmitCommitStages.lean aggmsm` from `Dregg2.Circuit.Emit.MinaWrapXiAggregateMsm.xiAggMsmDesc` =
/// `bucketedRowDescChal 192 59 255 2 GENS SCAL`. It belongs to the COMMITMENT-STAGES campaign, not
/// to this file's demonstration family, and it lives here because the witness producer above is
/// what fills it. Unlike the three toys it is FULL-WIDTH: `nbits = 255`, 47 real block commitments
/// (+12 inert padding terms), 8 192 rows.
///
/// ⚑ **AND SINCE 2026-08-05 IT IS THE ONLY INSTANCE WITH A CHALLENGE BLOCK**: 192 columns above the
/// row template carrying the six-value squaring basis `(ξ³², ξ¹⁶, ξ⁸, ξ⁴, ξ², ξ)`, pinned to public
/// inputs `27 … 218` on the first row and threaded down the trace. The three toys pass through
/// `bucketedRowDesc`, which did not move, and their SHAs are unchanged.
const XIAGG_JSON: &str = include_str!("../descriptors/by-name/mina-xi-aggregate-msm.json");
const XIAGG_SHA: &str = "79eed980c54cc44f48839345f8758026453e3b7908995636b3f499232b1ec678";
/// The four o1-labs goldens, emitted from the GATE CONSTANTS by `EmitCommitStages.lean goldlimbs`.
/// Line 3 (0-indexed) is `MinaWrapAggregationGate.COMBINED_GOLD`.
const MINA_GOLDS: &str = include_str!("fixtures/mina-commit-golds.txt");

const C2_SHA: &str = "5798a59c1957a2ef19f087540b1d9ec382d15d83d897b9cc75e055317fbe0a53";
const C3_SHA: &str = "535d48f303041185156b41ec91b1ca1fd1ecea166507c89df7704f08b2927ad1";

// ---------------------------------------------------------------------------------------------
// The Lean row layout (`PastaMsmBucketed` §1), restated so a drift in either side reds HERE rather
// than silently addressing a different column.
// ---------------------------------------------------------------------------------------------

const WK: usize = 612;
const PI_COUNT: usize = 27;
const CONSTRAINTS: usize = 91;

const RUNX: usize = 525;
const TOTX: usize = 552;
const GENX: usize = 579;
const ISTERM: usize = 606;
const ISSTEP: usize = 607;
const TIDX: usize = 608;
const WIN: usize = 609;
const GIDX: usize = 610;
const DGT: usize = 611;

/// `PastaMsmBucketed.outPiGates` — the 27 `.last` `piBinding`s on `TOT`, as constraint-LIST
/// indices. `bucketedRowDesc` appends them after the row template, so they are the last `PI_COUNT`
/// of the narrow `CONSTRAINTS`, and `bucketedRowDescChal` only APPENDS
/// (`bucketedRowDescChalOn_extends_the_narrow_descriptor`) — so the same range names them on the
/// widened ξ-aggregate too.
const OUT_PI_GATES: std::ops::Range<usize> = (CONSTRAINTS - PI_COUNT)..CONSTRAINTS;

/// `PastaMsmBucketed.chalPinGates[m]` — the first-row `piBinding` on column `CHB + m`. The pins
/// follow the narrow list.
const fn chal_pin_gate(m: usize) -> usize {
    CONSTRAINTS + m
}

/// `PastaMsmBucketed.chalThreadGates[m]` — `nxt CH_m − CH_m` on the transition. The threads follow
/// all `nc` pins.
const fn chal_thread_gate(nc: usize, m: usize) -> usize {
    CONSTRAINTS + nc + m
}

/// `PastaMsmWindowed.W` — the inherited row template's width, and the base `fill_row` produces.
const WINDOWED_W: usize = 525;

fn sha256_hex(b: &[u8]) -> String {
    let mut h = Sha256::new();
    h.update(b);
    h.finalize().iter().map(|x| format!("{x:02x}")).collect()
}

fn put_field(row: &mut [BabyBear], base: usize, v: &U256) {
    for i in 0..NUM_LIMBS {
        row[base + i] = BabyBear::new(v.limb30(i));
    }
}

fn manifest(desc: &EffectVmDescriptor2, name: &str) -> Vec<Vec<u32>> {
    let t = desc
        .tables
        .iter()
        .find(|t| t.name == name)
        .unwrap_or_else(|| panic!("descriptor declares no table named {name}"));
    match &t.sem {
        TableSem::ExactPublicRows { rows } => rows.clone(),
        other => panic!("table {name} is {other:?}, not an exact-public manifest"),
    }
}

/// A projective point read out of a `pasta_msm_srs` manifest row (`gidx+1` then 27 limbs, in the
/// row layout's `X ‖ Y ‖ Z` block order).
fn pt_of_manifest_row(row: &[u32]) -> Pt {
    let coord = |off: usize| {
        let mut limbs = [0u32; NUM_LIMBS];
        limbs.copy_from_slice(&row[1 + off..1 + off + NUM_LIMBS]);
        U256::from_limbs30(&limbs)
    };
    Pt {
        x: coord(0),
        y: coord(NUM_LIMBS),
        z: coord(2 * NUM_LIMBS),
    }
}

// ---------------------------------------------------------------------------------------------
// THE SHAPE, recovered from the descriptor's OWN manifests.
//
// Nothing here is a parameter this file chose: `n`, `W`, `c` and `D` are read back off the three
// declared tables, so a re-emit at different parameters retargets the witness producer without an
// edit. That is also what makes the trace and the manifest impossible to disagree by accident —
// and it is why every tamper below perturbs one of them AFTER this step.
// ---------------------------------------------------------------------------------------------

struct Shape {
    /// ⚑ The COORDINATE modulus this instance's arithmetic is reduced at — `P_PASTA` for the
    /// Pallas/Wrap leg, `Q_PASTA` for the **Vesta/Step** leg the accumulator actually lives on.
    /// Read off the descriptor NAME, so a witness cannot be filled at the wrong prime for the
    /// gadget the descriptor emitted.
    m: U256,
    rows: usize,
    n: usize,
    windows: usize,
    c: usize,
    levels: usize,
    /// ⚑ The CHALLENGE-BLOCK width in FELTS — `PastaMsmBucketed.chalPinGates`' `nc`. `0` for the
    /// three toy instances; `192` for the ξ-aggregate, which carries the six-value squaring basis
    /// at `SK = 32` eight-bit limbs each. Read off the descriptor's own width, never a constant
    /// this file chose.
    nc: usize,
    /// `gens[i]` — the real Mina SRS generator at absolute index `i`.
    gens: Vec<Pt>,
    /// `digits[w][i]` — the declared digit of term `i` in window `w`.
    digits: Vec<Vec<u32>>,
}

fn shape_of(desc: &EffectVmDescriptor2) -> Shape {
    let m = if desc.name.contains("-vesta-") {
        Q_PASTA
    } else if desc.name.contains("-pallas-") {
        P_PASTA
    } else {
        panic!(
            "descriptor {} names no curve; refusing to guess a modulus",
            desc.name
        )
    };
    let sched = manifest(desc, "pasta_msm_schedule");
    let cover = manifest(desc, "pasta_msm_cover");
    let srs = manifest(desc, "pasta_msm_srs");
    let rows = sched.len();
    assert_eq!(
        cover.len(),
        rows,
        "cover manifest length must be the height"
    );
    assert_eq!(srs.len(), rows, "srs manifest length must be the height");

    let real: Vec<&Vec<u32>> = cover.iter().filter(|r| r[0] != 0).collect();
    let windows = real.iter().map(|r| r[0]).max().expect("a window") as usize;
    let n = real.iter().filter(|r| r[0] == 1).count();
    let c = sched.iter().filter(|r| r[1] == 1 && r[2] == 1).count();
    let levels = rows / windows - c - n;

    let mut gens = vec![Pt::INFINITY; n];
    for r in srs.iter().filter(|r| r[0] != 0) {
        let i = r[0] as usize - 1;
        if i < n {
            gens[i] = pt_of_manifest_row(r);
        }
    }
    let mut digits = vec![vec![0u32; n]; windows];
    for r in &real {
        digits[r[0] as usize - 1][r[1] as usize - 1] = r[2];
    }
    // ⚑ The challenge block is whatever the descriptor declared ABOVE the row template, and the
    // two declarations must agree: `nc` more columns and `nc` more public inputs. A descriptor that
    // widened one and not the other would fill silently and publish nothing (or publish a slot no
    // column feeds), so this is asserted rather than derived from one side.
    assert!(
        desc.trace_width >= WK,
        "trace_width {} is below the row template's {WK}",
        desc.trace_width
    );
    let nc = desc.trace_width - WK;
    assert_eq!(
        desc.public_input_count,
        PI_COUNT + nc,
        "the challenge block widened the trace by {nc} but not the public inputs"
    );
    Shape {
        m,
        rows,
        n,
        windows,
        c,
        levels,
        nc,
        gens,
        digits,
    }
}

// ---------------------------------------------------------------------------------------------
// THE WITNESS PRODUCER. Cells only.
// ---------------------------------------------------------------------------------------------

/// One row's mode.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Mode {
    /// `RUN += gens[gidx]`.
    Term(usize),
    /// `TOT += RUN`.
    Step,
    /// `TOT += TOT`, `RUN := O`.
    Dbl,
}

/// The row schedule: `c` doublings, then the digit sweep `D → 0` with a level fold after each
/// nonzero level. The ONLY data-dependent thing about it is which terms land at which level, which
/// is precisely what `pasta_msm_cover` forces.
fn schedule(sh: &Shape) -> Vec<(usize, Mode)> {
    let mut out = Vec::with_capacity(sh.rows);
    for w in 0..sh.windows {
        for _ in 0..sh.c {
            out.push((w, Mode::Dbl));
        }
        for d in (0..=sh.levels).rev() {
            for i in 0..sh.n {
                if sh.digits[w][i] as usize == d {
                    out.push((w, Mode::Term(i)));
                }
            }
            if d >= 1 {
                out.push((w, Mode::Step));
            }
        }
    }
    assert_eq!(out.len(), sh.rows, "the schedule must be the trace height");
    out
}

/// Build the honest trace and its public inputs: the 27 limbs of the claimed commitment `C`, then
/// the `sh.nc` challenge felts.
///
/// ⚑ **THE CHALLENGE BLOCK IS WRITTEN INTO EVERY ROW, NOT JUST THE FIRST.** `chalPinGates` pins row
/// 0 to the public inputs and `chalThreadGates` demands `nxt CH_m = CH_m` on every transition, so a
/// witness that filled only row 0 is refused by the thread. Filling all rows is what an honest
/// prover does; `a_basis_that_varies_by_row_is_refused` is the tamper that shows the thread is what
/// makes that mandatory rather than customary.
fn honest_trace_with_chal(sh: &Shape, chal: &[BabyBear]) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    assert_eq!(
        chal.len(),
        sh.nc,
        "the challenge block must be exactly the width the descriptor declared"
    );
    let sched = schedule(sh);
    let mut trace = Vec::with_capacity(sh.rows);

    let mut run = Pt::INFINITY;
    let mut tot = Pt::INFINITY;
    let mut dgt: u32 = 0;

    for (idx, (w, mode)) in sched.iter().enumerate() {
        let (acc, src, genp, isterm, isstep, dbl, gidx) = match *mode {
            Mode::Term(i) => (run, sh.gens[i], sh.gens[i], 1u32, 0u32, false, i as u32),
            Mode::Step => (tot, run, Pt::INFINITY, 0, 1, false, 0),
            Mode::Dbl => (tot, tot, Pt::INFINITY, 0, 0, true, 0),
        };

        let mut row = fill_row_at(&sh.m, &acc, &src, true, dbl);
        assert_eq!(row.len(), WINDOWED_W);
        row.resize(WK + sh.nc, BabyBear::new(0));
        row[WK..WK + sh.nc].copy_from_slice(chal);

        put_field(&mut row, RUNX, &run.x);
        put_field(&mut row, RUNX + NUM_LIMBS, &run.y);
        put_field(&mut row, RUNX + 2 * NUM_LIMBS, &run.z);
        put_field(&mut row, TOTX, &tot.x);
        put_field(&mut row, TOTX + NUM_LIMBS, &tot.y);
        put_field(&mut row, TOTX + 2 * NUM_LIMBS, &tot.z);
        if isterm == 1 {
            put_field(&mut row, GENX, &genp.x);
            put_field(&mut row, GENX + NUM_LIMBS, &genp.y);
            put_field(&mut row, GENX + 2 * NUM_LIMBS, &genp.z);
        }
        row[ISTERM] = BabyBear::new(isterm);
        row[ISSTEP] = BabyBear::new(isstep);
        row[TIDX] = BabyBear::new(idx as u32);
        row[WIN] = BabyBear::new(*w as u32);
        row[GIDX] = BabyBear::new(gidx);
        row[DGT] = BabyBear::new(dgt);
        trace.push(row);

        // advance the two threads and the sweep counter exactly as the emitted window gates say.
        let out = complete_add(&sh.m, &acc, &src);
        match *mode {
            Mode::Term(_) => run = out,
            Mode::Step => {
                tot = out;
                dgt -= 1;
            }
            Mode::Dbl => {
                tot = out;
                run = Pt::INFINITY;
                dgt = sh.levels as u32;
            }
        }
    }

    // ⚑ The PI binding reads `TOT` at the LAST row, which is the answer iff the final window ends
    // on a term row (its digit-0 group is non-empty). Asserted rather than assumed: if it ever
    // fails, the descriptor's parameters need a trailing no-op row, and a silent pass here would
    // publish a pre-final total as the commitment.
    assert!(
        matches!(sched.last().map(|s| s.1), Some(Mode::Term(_))),
        "the final window's digit-0 group is empty; the published TOT would be pre-final"
    );
    let last = trace.last().expect("a row");
    let claimed = Pt {
        x: read_field(last, TOTX),
        y: read_field(last, TOTX + NUM_LIMBS),
        z: read_field(last, TOTX + 2 * NUM_LIMBS),
    };
    assert!(proj_eq_at(&sh.m, &claimed, &tot) || claimed == tot);

    let mut pis: Vec<BabyBear> = (0..PI_COUNT).map(|i| last[TOTX + i]).collect();
    pis.extend_from_slice(chal);
    (trace, pis)
}

/// The three toy instances carry no challenge block.
///
/// ⚠ This REFUSES an instance that has one rather than filling it with zeros. A zero basis proves
/// perfectly well — the AIR pins and threads the block, it does not evaluate it — so a silent
/// zero-fill would be a green test about nothing, which is exactly the shape this cone keeps
/// finding.
fn honest_trace(sh: &Shape) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    assert_eq!(
        sh.nc, 0,
        "this instance declares a {}-felt challenge block; fill it with the block's OWN basis \
         through honest_trace_with_chal, never with zeros",
        sh.nc
    );
    honest_trace_with_chal(sh, &[])
}

/// The answer computed OUT of circuit, by plain per-term double-and-add — the oracle the trace is
/// checked against. Deliberately NOT the same algorithm: a bucketing bug that agreed with itself
/// would survive comparing the trace to a second bucketed sum.
fn reference_msm(sh: &Shape) -> Pt {
    let radix = 1u64 << sh.c;
    let mut acc = Pt::INFINITY;
    for i in 0..sh.n {
        let mut s: u64 = 0;
        for w in 0..sh.windows {
            s = s * radix + u64::from(sh.digits[w][i]);
        }
        let mut term = Pt::INFINITY;
        for _ in 0..s {
            term = complete_add(&sh.m, &term, &sh.gens[i]);
        }
        acc = complete_add(&sh.m, &acc, &term);
    }
    acc
}

fn parse(json: &str) -> EffectVmDescriptor2 {
    parse_vm_descriptor2_unsound_oversized(json).expect("the Lean artifact must parse")
}

fn prove_and_verify(
    desc: &EffectVmDescriptor2,
    trace: &[Vec<BabyBear>],
    pis: &[BabyBear],
) -> Result<(), String> {
    let proof = prove_vm_descriptor2(desc, trace, pis, &MemBoundaryWitness::default(), &[])?;
    verify_vm_descriptor2(desc, &proof, pis)
}

// ---------------------------------------------------------------------------------------------
// ⚑ NAMING THE GATE THAT REFUSED — the discriminator the four PI-tampers below need.
//
// Every tooth in this file names the mechanism that must object. Until 2026-08-05 four of them
// asserted that with `must_refuse`, which requires a fail-closed `Err` — and this descriptor
// carries LOOKUPS, so under `cargo test` p3's `#[cfg(debug_assertions)]` constraint check panics
// inside `prove_batch` before the producer's self-verify can return anything. All four were RED
// while the constraint system refused every forgery exactly as documented: `refusal`'s own module
// docblock records the same misrouting costing two teeth ten days in `shielded_ring_clearing_air`.
// `must_refuse_or_unsat_panic` is the helper for a lookup-carrying site, and the panic message is
// STRICTLY MORE informative than the `Err` — it carries the row and the failed constraint set.
// ---------------------------------------------------------------------------------------------

/// The AIR-constraint index p3 reports for the descriptor's `list_index`-th constraint.
///
/// `constraints not satisfied on row N: failed constraints = [#k]` numbers the AIR's constraints,
/// and a `lookup` entry compiles to a BUS operation rather than an AIR constraint — so `#k` names
/// the descriptor's `k`-th NON-LOOKUP constraint. On the ξ-aggregate the three manifests sit at
/// list indices 61/62/63, which is why `chalPinGates[31]` (list index 122) is reported as `#119`.
///
/// ⚑ DERIVED, NOT PINNED. A literal `#119` would be a constant checked against nothing; this reads
/// the Lean-emitted constraint list and meets the DEPLOYED PROVER'S OWN numbering, which is a
/// second, independent source. A widening that inserted a gate moves both sides only if the
/// mapping is real.
fn air_index(desc: &EffectVmDescriptor2, list_index: usize) -> usize {
    assert!(
        list_index < desc.constraints.len(),
        "constraint {list_index} is past the end of {}'s {} constraints",
        desc.name,
        desc.constraints.len()
    );
    assert!(
        !matches!(desc.constraints[list_index], VmConstraint2::Lookup(_)),
        "constraint {list_index} is a LOOKUP; it has no AIR-constraint index"
    );
    desc.constraints[..list_index]
        .iter()
        .filter(|c| !matches!(c, VmConstraint2::Lookup(_)))
        .count()
}

/// ⚑ **THE REFUSAL NAMED THE GATE THIS TOOTH NAMES** — not merely "something objected".
///
/// Two clauses, and they are not the same strength:
///
///  * [`assert_violated_constraint_not_bus`] holds in EVERY profile and is the load-bearing
///    NEGATIVE one. A tooth aimed at a PI pin must not be kept green by `pasta_msm_cover`'s LogUp
///    failing instead — that would mean the manifest, not the pin, is what catches the forgery,
///    and the three routing teeth above would then be testing the same thing four times.
///  * The ROW and the failed-constraint SET are asserted only when p3's debug check is the
///    mechanism, because `--release` refuses with `OodEvaluationMismatch`, which carries neither.
///    Said out loud rather than left as a silent weakening: under `--release` these teeth assert
///    the profile-independent clause and nothing finer.
///
/// `gates` are descriptor constraint-LIST indices. The assertion is that every constraint p3
/// reported is one of them and that at least one fired — i.e. **nothing outside the named gate
/// objected**. Deliberately not set EQUALITY: how many of a 27-limb PI block a given displacement
/// moves is a fact about the forgery's arithmetic, not about the gate, and `assert_ne!` on the
/// tampered vector is where that belongs.
#[track_caller]
fn refused_by_gates(
    what: &str,
    refusal: &Refusal<String>,
    desc: &EffectVmDescriptor2,
    gates: &[usize],
    row: usize,
) -> String {
    let reason = refusal.reason();
    assert_violated_constraint_not_bus(what, &reason);

    let Some(rest) = reason.split("constraints not satisfied on row ").nth(1) else {
        // `--release`: `OodEvaluationMismatch`, already checked above. Nothing finer is available.
        return reason;
    };
    let (got_row, rest) = rest
        .split_once(':')
        .expect("p3 renders `on row N: failed constraints = [...]`");
    assert_eq!(
        got_row.trim().parse::<usize>().expect("a row index"),
        row,
        "{what}: refused on the wrong ROW — the gate this tooth names fires on row {row}: {reason}"
    );
    let list = rest
        .split_once('[')
        .and_then(|(_, r)| r.split_once(']'))
        .expect("p3 renders the failed set in brackets")
        .0;
    let got: Vec<usize> = list
        .split(',')
        .map(|t| {
            t.trim()
                .trim_start_matches('#')
                .parse::<usize>()
                .expect("a constraint index")
        })
        .collect();
    assert!(!got.is_empty(), "{what}: p3 named no failed constraint");

    let want: Vec<usize> = gates.iter().map(|&i| air_index(desc, i)).collect();
    for g in &got {
        assert!(
            want.contains(g),
            "{what}: constraint #{g} objected, and it is NOT one of the gates this tooth names \
             ({want:?}, from descriptor constraints {gates:?}). Something other than the named \
             gate is what catches this forgery: {reason}"
        );
    }
    reason
}

// =============================================================================================
// (a) the artifacts are the ones this test was written against
// =============================================================================================

#[test]
fn lean_artifacts_are_pinned() {
    assert_eq!(
        sha256_hex(WINDOWED_JSON.as_bytes()),
        WINDOWED_SHA,
        "the inherited row template was re-emitted; re-read the Lean and re-pin"
    );
    for (json, want, n, nbits, c, curve) in [
        (C2_JSON, C2_SHA, 27usize, 4usize, 2usize, "pallas"),
        (C3_JSON, C3_SHA, 54, 6, 3, "pallas"),
        (V2_JSON, V2_SHA, 27, 4, 2, "vesta"),
    ] {
        assert_eq!(
            sha256_hex(json.as_bytes()),
            want,
            "descriptor c={c} was re-emitted; re-read the Lean and re-pin"
        );
        let d = parse(json);
        // ⚑ THE CURVE IS IN THE NAME. A descriptor that emitted one curve's gadget under the
        // other's name is a wrong-curve proof no shape check catches, so the name is load-bearing
        // and `shape_of` reads the witness modulus straight off it.
        // ⚑ n AND nbits ARE IN THE NAME TOO, since 2026-08-05. They were not, and
        // `bucketedRowDesc 27 4 2` and the full-width xi-aggregate `bucketedRowDesc 59 255 2`
        // therefore emitted ONE string for two different AIRs. Lean's
        // `the_emitted_family_has_no_two_artifacts_with_one_name` is that as a kernel fact.
        assert_eq!(
            d.name,
            format!("dregg-pasta-msm-bucketed-{curve}-n{n}b{nbits}-c{c}::v1")
        );
        assert_eq!(d.trace_width, WK);
        assert_eq!(d.public_input_count, PI_COUNT);
        assert_eq!(
            d.constraints.len(),
            CONSTRAINTS,
            "42 row-local + 4 mode + 6 select + 6 thread + 3 index + 3 lookup + 27 PI"
        );
        assert_eq!(d.tables.len(), 3, "schedule, cover, srs");
        // ⚑ The prefix claim, checked on the ARTIFACT and not only in the kernel: the first 42
        // constraints are `PastaMsmWindowed.rowGates`, so the curve arithmetic is not re-authored.
        let windowed = parse(WINDOWED_JSON);
        assert_eq!(
            windowed.constraints.len(),
            45,
            "windowedRowDesc = rowGates (42) ++ threadGates (3)"
        );
        // ⚑ Only the PALLAS instance inherits `rowGates` byte for byte — that is the whole point
        // of `rowGatesWith` being a parameter. The Vesta instance's 42 row-local gates are
        // `rowGatesWith vestaCompleteAdd`, reduced at `q`, and MUST differ; asserting equality
        // there would be asserting a wrong-curve proof.
        if curve == "pallas" {
            assert_eq!(
                &d.constraints[..42],
                &windowed.constraints[..42],
                "bucketedRowDesc_extends_rowGates is FALSE of the emitted bytes"
            );
        } else {
            assert_ne!(
                &d.constraints[..42],
                &windowed.constraints[..42],
                "the {curve} instance carries the PALLAS row template — wrong-curve emission"
            );
        }
        // ⚑ …and the REFUTATION, on the bytes: the windowed descriptor's own 3 thread gates are
        // NOT inherited, because they say `nxt ACC = loc OUT` UNCONDITIONALLY and this layout's
        // `ACC` is a SELECT over two accumulators. Asserting the negative is the point — the first
        // draft DID inherit them and the deployed prover refused an HONEST witness at row 8 with
        // `failed constraints = [#42,#43,#44]`, exactly those three.
        assert_ne!(
            &d.constraints[42..45],
            &windowed.constraints[42..45],
            "the unconditional accumulator thread must NOT survive into a bucketed layout"
        );
    }
}

/// ⚑ **THE TWO CURVES EMIT DIFFERENT GATES, on the bytes.** `PastaMsmBucketed` proves
/// `pallas_and_vesta_primes_differ` in the kernel and deliberately stops there: deciding the
/// 42-gate list inequality means evaluating 81 cross-products at 255-bit coefficients, which buys
/// nothing this check does not. Here it is where it is cheap — and it is the assertion that would
/// catch an emitter wired to the wrong `AddGadget`, which is the only way a Vesta-named descriptor
/// could carry Pallas arithmetic.
#[test]
fn the_two_curves_are_not_the_same_air() {
    let p = parse(C2_JSON);
    let v = parse(V2_JSON);
    assert_eq!(p.trace_width, v.trace_width, "same layout");
    assert_eq!(p.constraints.len(), v.constraints.len(), "same shape");
    assert_ne!(
        &p.constraints[..42],
        &v.constraints[..42],
        "the Pallas and Vesta rows reduce at the same prime — one AddGadget is wired wrong"
    );
    // …and everything ABOVE the row template is curve-independent, which is what makes the
    // layout one object rather than two.
    assert_eq!(
        &p.constraints[42..],
        &v.constraints[42..],
        "the routing and threads must not depend on the curve"
    );
}

// =============================================================================================
// (b) the shape the manifests declare is the shape the layout predicts
// =============================================================================================

#[test]
fn the_manifests_declare_the_fused_layout() {
    for (json, c, n) in [
        (C2_JSON, 2usize, 27usize),
        (C3_JSON, 3, 54),
        (V2_JSON, 2, 27),
    ] {
        let sh = shape_of(&parse(json));
        assert_eq!(sh.c, c, "doublings per window must be c");
        assert_eq!(sh.n, n);
        assert_eq!(sh.levels, (1 << c) - 1, "levels must be 2^c - 1");
        // the closed form `PastaMsmBucketed.fusedAdds` computes, on these very parameters.
        assert_eq!(sh.rows, sh.windows * (sh.c + sh.n + sh.levels));
        assert!(
            sh.rows.is_power_of_two(),
            "the prover refuses a ragged height"
        );
        // every declared generator is a real curve point, and distinct from its neighbours.
        for (i, g) in sh.gens.iter().enumerate() {
            assert!(
                on_curve_at(&sh.m, g),
                "SRS generator {i} is off-curve for this descriptor's curve"
            );
        }
        assert_ne!(sh.gens[0], sh.gens[1]);
        // every declared digit is a real c-bit digit (`coverManifest_digits_are_c_bit`).
        for w in 0..sh.windows {
            for i in 0..sh.n {
                assert!((sh.digits[w][i] as usize) <= sh.levels);
            }
        }
    }
}

// =============================================================================================
// (c) ⚑ POLARITY 1 — THE HONEST ACCUMULATOR PROVES, and computes the right point
// =============================================================================================

#[test]
fn the_honest_bucketed_msm_proves_and_verifies() {
    for (json, label) in [
        (C2_JSON, "pallas c=2, n=27"),
        (C3_JSON, "pallas c=3, n=54"),
        (V2_JSON, "VESTA/Step c=2, n=27"),
    ] {
        let desc = parse(json);
        let sh = shape_of(&desc);
        let (trace, pis) = honest_trace(&sh);

        // ⚑ FIRST: the trace computes the MSM. A proof of a trace that sums the wrong thing is a
        // proof of the wrong thing, and the prover would never notice.
        let want = reference_msm(&sh);
        let got = Pt {
            x: read_field(trace.last().unwrap(), TOTX),
            y: read_field(trace.last().unwrap(), TOTX + NUM_LIMBS),
            z: read_field(trace.last().unwrap(), TOTX + 2 * NUM_LIMBS),
        };
        assert!(
            proj_eq_at(&sh.m, &want, &got),
            "[{label}] the bucketed trace disagrees with the term-by-term sum"
        );

        let t0 = Instant::now();
        prove_and_verify(&desc, &trace, &pis).unwrap_or_else(|e| {
            panic!(
                "[{label}] the LEAN-AUTHORED AIR refused an honest witness: {e}\n\
                 (that error is the AIR checking the witness — fix the WITNESS, never the AIR)"
            )
        });
        println!(
            "  [HONEST] {label}: {} rows x {} cols, {} constraints, 3 exact-public manifests \
             -> PROVED + VERIFIED in {:.1} ms",
            sh.rows,
            WK,
            desc.constraints.len(),
            t0.elapsed().as_secs_f64() * 1e3
        );
    }
}

// =============================================================================================
// (d) ⚑ POLARITY 2 — A FORGED `sg` IS REFUSED
//
// The native oracle's case, matched: the claimed commitment is displaced by one generator
// (`C + G`), everything else honest. This is a forgery the ARITHMETIC cannot see — every row still
// adds correctly — so the mechanism that must object is the PI binding, and nothing else.
// =============================================================================================

#[test]
fn a_forged_commitment_is_refused() {
    for (json, label) in [
        (C2_JSON, "pallas c=2"),
        (C3_JSON, "pallas c=3"),
        (V2_JSON, "VESTA/Step c=2"),
    ] {
        let desc = parse(json);
        let sh = shape_of(&desc);
        let (trace, pis) = honest_trace(&sh);

        // `C + G` — the same displacement `mina_accumulator_discharge`'s `forge_commitment` makes.
        let honest = Pt {
            x: read_field(trace.last().unwrap(), TOTX),
            y: read_field(trace.last().unwrap(), TOTX + NUM_LIMBS),
            z: read_field(trace.last().unwrap(), TOTX + 2 * NUM_LIMBS),
        };
        let forged = complete_add(&sh.m, &honest, &sh.gens[0]);
        assert!(
            !proj_eq_at(&sh.m, &honest, &forged),
            "the forgery must move the point"
        );

        let mut bad = vec![BabyBear::new(0); PI_COUNT];
        for i in 0..NUM_LIMBS {
            bad[i] = BabyBear::new(forged.x.limb30(i));
            bad[NUM_LIMBS + i] = BabyBear::new(forged.y.limb30(i));
            bad[2 * NUM_LIMBS + i] = BabyBear::new(forged.z.limb30(i));
        }
        assert_ne!(bad, pis, "the forged PI vector must differ");

        let what = format!("[{label}] a commitment displaced by +G, honest trace");
        let r = must_refuse_or_unsat_panic(&what, || prove_and_verify(&desc, &trace, &bad));
        let reason = refused_by_gates(
            &what,
            &r,
            &desc,
            &OUT_PI_GATES.collect::<Vec<_>>(),
            sh.rows - 1,
        );
        println!("  [FORGED] {label}: claimed C + G -> REFUSED by outPiGates: {reason}");
    }
}

// =============================================================================================
// (e) ⚑ POLARITY 2b — THE ROUTING ITSELF IS THE THING UNDER TEST
//
// Three tampers, each aimed at one leg of the routing, each naming the mechanism that must fire.
// This is the section the whole file exists for: without it, (c) and (d) would demonstrate an MSM
// and say nothing about whether the BUCKET ROUTING is forced.
// =============================================================================================

/// A term row consumes a generator that is real, on-curve, and in the manifest — but at the WRONG
/// SWEEP LEVEL. The arithmetic is untouched (the row still adds a real point to `RUN`); the digit
/// column no longer matches the level. **`pasta_msm_cover` must be the mechanism that refuses**,
/// because nothing else in the descriptor relates a generator index to a digit.
#[test]
fn a_generator_folded_at_the_wrong_level_is_refused() {
    let desc = parse(C2_JSON);
    let sh = shape_of(&desc);
    let (mut trace, pis) = honest_trace(&sh);

    // find a term row and move its declared level, keeping the arithmetic self-consistent.
    let victim = (0..sh.rows)
        .find(|&i| trace[i][ISTERM].as_u32() == 1 && trace[i][DGT].as_u32() > 0)
        .expect("a term row above level 0");
    let was = trace[victim][DGT].as_u32();
    trace[victim][DGT] = BabyBear::new(was - 1);

    let e = must_refuse(
        "a real generator folded one sweep level below its declared digit",
        || prove_and_verify(&desc, &trace, &pis),
    );
    println!(
        "  [ROUTE ] cover-manifest level moved {was} -> {}: REFUSED: {e:?}",
        was - 1
    );
}

/// A term row consumes a DIFFERENT REAL Mina SRS generator than its index names — the substitution
/// `pasta_bound_sg_prove` calls the rung. Both points are on-curve and both are in the manifest, so
/// only the `(gidx, limbs)` pairing can object. **`pasta_msm_srs` must be the mechanism.**
#[test]
fn a_substituted_real_generator_is_refused() {
    let desc = parse(C2_JSON);
    let sh = shape_of(&desc);
    let (mut trace, pis) = honest_trace(&sh);

    let victim = (0..sh.rows)
        .find(|&i| trace[i][ISTERM].as_u32() == 1 && trace[i][GIDX].as_u32() == 0)
        .expect("a term row consuming generator 0");
    let substitute = sh.gens[1];
    assert!(on_curve_at(&sh.m, &substitute) && substitute != sh.gens[0]);
    put_field(&mut trace[victim], GENX, &substitute.x);
    put_field(&mut trace[victim], GENX + NUM_LIMBS, &substitute.y);
    put_field(&mut trace[victim], GENX + 2 * NUM_LIMBS, &substitute.z);

    let e = must_refuse(
        "generator index 0's row carrying the limbs of REAL generator 1",
        || prove_and_verify(&desc, &trace, &pis),
    );
    println!("  [ROUTE ] a real SRS generator at the wrong index: REFUSED: {e:?}");
}

/// A generator is folded TWICE in one window and another is DROPPED — the classic MSM forgery a
/// containment-only lookup would admit and a permutation must not. **`pasta_msm_cover`'s `Perm`
/// (not `Sublist`) is the mechanism**, and this is the single test that distinguishes them.
#[test]
fn a_duplicated_term_and_a_dropped_one_are_refused() {
    let desc = parse(C2_JSON);
    let sh = shape_of(&desc);
    let (mut trace, pis) = honest_trace(&sh);

    // two term rows at the SAME sweep level in the SAME window; point the second at the first's
    // generator, so one index is consumed twice and one not at all. Same level, so the sweep
    // counter and every arithmetic gate stay satisfied — only the multiset moves.
    let mut by_level = std::collections::BTreeMap::<u32, Vec<usize>>::new();
    for i in 0..sh.rows {
        if trace[i][ISTERM].as_u32() == 1 && trace[i][WIN].as_u32() == 0 {
            by_level.entry(trace[i][DGT].as_u32()).or_default().push(i);
        }
    }
    let level_rows = by_level
        .values()
        .max_by_key(|v| v.len())
        .expect("window 0 has term rows")
        .clone();
    assert!(
        level_rows.len() >= 2,
        "need two terms at one level to duplicate one"
    );
    let (keep, drop) = (level_rows[0], level_rows[1]);
    let g = sh.gens[trace[keep][GIDX].as_u32() as usize];
    trace[drop][GIDX] = trace[keep][GIDX];
    put_field(&mut trace[drop], GENX, &g.x);
    put_field(&mut trace[drop], GENX + NUM_LIMBS, &g.y);
    put_field(&mut trace[drop], GENX + 2 * NUM_LIMBS, &g.z);

    let e = must_refuse(
        "one generator folded twice in a window and another dropped",
        || prove_and_verify(&desc, &trace, &pis),
    );
    println!("  [ROUTE ] duplicate + drop (a Sublist would ADMIT this): REFUSED: {e:?}");
}

/// The SCHEDULE is verifier-known, and a prover cannot choose its own window structure: move one
/// row's declared window and the schedule manifest must refuse. **`pasta_msm_schedule`.**
#[test]
fn a_relabelled_window_is_refused() {
    let desc = parse(C2_JSON);
    let sh = shape_of(&desc);
    let (mut trace, pis) = honest_trace(&sh);

    let victim = (0..sh.rows)
        .find(|&i| trace[i][WIN].as_u32() == 0 && trace[i][ISTERM].as_u32() == 1)
        .expect("a window-0 term row");
    trace[victim][WIN] = BabyBear::new(1);

    let e = must_refuse("a window-0 row relabelled as window 1", || {
        prove_and_verify(&desc, &trace, &pis)
    });
    println!("  [ROUTE ] a relabelled window: REFUSED: {e:?}");
}

// =============================================================================================
// (f) ⚑ THE FRI BLOWUP — THIS AIR IS CHIP-FREE, SO lb=2 IS LEGAL FOR IT
//
// `IR2_FRI_LOG_BLOWUP = 6` is GLOBAL and stays global: 39 of the 99 parseable by-name goldens pull
// in the Poseidon2 chip, whose inline degree-7 x⁷ S-box needs a degree-6 quotient that a blowup of
// 4 cannot carry, so they REFUSE at lb=2 (`fri_blowup_global_knob_survey.rs`, and the correction in
// `descriptor_ir2.rs`'s `ir2_config` docblock). **This descriptor declares no chip** — three
// exact-public tables and nothing else — so the question is whether IT survives, and the sweep
// below RUNS it rather than arguing it.
//
// Why it matters more here than anywhere else in the registry: the row ceiling is
// `TWO_ADICITY (27) − log_blowup`, so `2^21` at lb=6 and `2^25` at lb=2 — 16× the reachable trace
// height. And the LDE the prover materialises is `2^log_blowup ×` the trace, so the full-width
// instance's ~3.6 GB of main trace becomes ~14 GB at lb=2 against ~231 GB at lb=6. That is the
// difference between a box and no box, and it is the ONLY lever on this workload that does not
// require a different algorithm.
//
// ⚠ THE SECURITY PARITY LINE IS HELD, NOT TRADED. Each `(lb, q)` below keeps
// `q·lb + query_pow ≥ 130` (conjectured) and `q·lb/2 + query_pow ≥ 73` (proven/Johnson) — the same
// line `ir2_config`'s own docblock names. What moves is prove time, memory and wire; never the
// claimed security.
//
// ⚠ AND THIS LANDS NO GLOBAL CHANGE. `prove_vm_descriptor2_with_config` is `#[doc(hidden)]` and
// labelled measurement-only as POLICY (it is a genuine prover — it self-verifies before returning).
// Shipping a real per-descriptor knob is blocked on something else entirely, recorded at
// `descriptor_ir2.rs`: the recursion path reads `num_queries` from the inner proof structure and
// never pins it against a configured count, which is masked today only because every child runs 19.
// That is the finding, and it is not this lane's to fix.

/// The security-parity rungs, as `pasta_sbox_program_proves.rs` uses them.
const FRI_PARITY: &[(usize, usize)] = &[(6, 19), (3, 39), (2, 57), (1, 114)];

fn config_at(log_blowup: usize, num_queries: usize) -> DreggStarkConfig {
    create_config_with_fri_full(
        log_blowup,
        /* log_final_poly_len */ 0,
        /* max_log_arity */ 3,
        num_queries,
        /* commit_pow */ 0,
        /* query_pow */ 16,
    )
}

#[test]
fn the_chip_free_bucketed_air_reaches_log_blowup_two() {
    let desc = parse(V2_JSON);
    assert!(
        desc.tables.iter().all(|t| t.id > 9),
        "a reserved table id would mean a chip after all"
    );
    let sh = shape_of(&desc);
    let (trace, pis) = honest_trace(&sh);

    // the deployed point must reproduce before any other rung means anything.
    prove_and_verify(&desc, &trace, &pis).expect("cold: the deployed config must prove");

    println!(
        "\n  FRI sweep on dregg-pasta-msm-bucketed-vesta-c2 ({} rows x {} cols, chip-free):",
        sh.rows, WK
    );
    println!(
        "  {:>3} {:>4} {:>6} {:>7} {:>10} {:>10} {:>10}",
        "lb", "q", "conj", "proven", "prove ms", "verify ms", "proof KiB"
    );
    let mut reached_lb2 = false;
    for (lb, q) in FRI_PARITY {
        let cfg = config_at(*lb, *q);
        let t0 = Instant::now();
        let proof = match prove_vm_descriptor2_with_config(
            &desc,
            &trace,
            &pis,
            &MemBoundaryWitness::default(),
            &[],
            &cfg,
        ) {
            Ok(p) => p,
            Err(e) => {
                println!("  {lb:>3} {q:>4}   REFUSED AT PROVE: {e}");
                continue;
            }
        };
        let prove_ms = t0.elapsed().as_secs_f64() * 1e3;
        let t1 = Instant::now();
        let verdict = verify_vm_descriptor2_with_config(&desc, &proof, &pis, &cfg);
        let verify_ms = t1.elapsed().as_secs_f64() * 1e3;
        let kib = postcard::to_allocvec(&proof).expect("serialize").len() as f64 / 1024.0;
        match verdict {
            Ok(()) => {
                println!(
                    "  {lb:>3} {q:>4} {:>6} {:>7} {prove_ms:>10.1} {verify_ms:>10.1} {kib:>10.1}",
                    q * lb + 16,
                    q * lb / 2 + 16
                );
                if *lb == 2 {
                    reached_lb2 = true;
                }
            }
            Err(e) => println!("  {lb:>3} {q:>4}   REFUSED AT VERIFY: {e:?}"),
        }
        // the parity line is a property of the rung, asserted rather than printed and trusted.
        assert!(
            q * lb + 16 >= 130,
            "rung (lb={lb}, q={q}) is below conjectured 130"
        );
        assert!(
            q * lb / 2 + 16 >= 73,
            "rung (lb={lb}, q={q}) is below proven 73"
        );
    }

    // ⚑ THE CLAIM UNDER TEST. A chip-bearing descriptor cannot do this; this one can, and that is
    // what makes the row ceiling 2^25 rather than 2^21 for the full-width instance.
    assert!(
        reached_lb2,
        "the chip-free bucketed AIR did NOT prove+verify at log_blowup = 2 — \
         the 2^25 row ceiling and the ~16x LDE saving are not available and \
         PastaMsmBucketed's headroom paragraph must be retracted"
    );
}

// =============================================================================================
// (h) ⚑ THE ξ-AGGREGATE OF MINA DEVNET BLOCK 539508, SCALED INSIDE THE CIRCUIT
//
// This is the instance the commitment-stages campaign needed and could not get from its own
// machine. `MinaWrapCommitStages.xiAggDesc` folds the same 47 commitments at full term count, but
// its ROM immediates are PRE-SCALED by `MinaWrapGroupGate.smul` — a Lean reference function, not a
// gate — so what it forces is "these 47 hardcoded points, added in this order, give this hardcoded
// point". Here the generators enter UNSCALED and the 47 powers of the block's real ξ enter as
// DIGITS, at the full 255-bit scalar width. `T_COVER`'s permutation makes `ξⁱ·Cᵢ` the trace's work.
//
// ⚠ The anchor is not this file's arithmetic and not the trace's own output: it is
// `MinaWrapAggregationGate.COMBINED_GOLD`, o1-labs' `PolyComm::multi_scalar_mul` output for that
// block, emitted straight off the gate constant. No decimal is transcribed here.
//
// ⚠ `reference_msm` above is NOT usable on this instance — it loops `0..s` unary over the scalar,
// which is fine at `nbits = 4` and impossible at 255. The golden IS the reference.
// =============================================================================================

/// The `COMBINED_GOLD` line of the Lean-emitted golden anchor, as an affine point.
fn mina_combined_gold() -> Pt {
    let line = MINA_GOLDS
        .lines()
        .filter(|l| !l.trim().is_empty())
        .nth(3)
        .expect("the golden anchor carries four points; the xi-aggregate is the fourth");
    let v: Vec<u64> = line
        .split_whitespace()
        .map(|c| c.parse::<u64>().expect("limb is a decimal"))
        .collect();
    assert_eq!(v.len(), 64, "32 x-limbs then 32 y-limbs");
    let field = |l: &[u64]| {
        let mut w = [0u64; 4];
        for (i, b) in l.iter().enumerate() {
            assert!(*b < 256, "limb out of its 8-bit range");
            w[i / 8] |= *b << (8 * (i % 8));
        }
        U256(w)
    };
    Pt {
        x: field(&v[..32]),
        y: field(&v[32..]),
        z: U256::ONE,
    }
}

/// ⚑⚑ **THE SIX-VALUE SQUARING BASIS, READ OUT OF THE SCALAR CHAIN'S OWN PUBLIC INPUTS.**
///
/// This is the whole weld, as data. `dregg-mina-xi-scalar-vector::v2` publishes eight 32-felt
/// blocks — `ξ`, `ξ⁴⁶`, then `ξ³², ξ¹⁶, ξ⁸, ξ⁴, ξ², ξ` — and blocks 2..8 are the basis. The
/// ξ-aggregate is proved with **those felts and no others**, so "the aggregate's challenge is the
/// chain's output" is not an assertion this file makes about two numbers; it is the only basis the
/// aggregate is ever given.
///
/// ⚠ Deliberately NOT a second fixture of its own. A basis emitted twice is a basis that can
/// disagree with itself, and no green would move.
const CHAIN_PIS: &str = include_str!("fixtures/mina-commit-xi-pis.txt");

/// `MinaWrapCommitStages.SK` — the boundary limb width the whole commit-machine cone publishes at.
const SK: usize = 32;
/// The basis occupies blocks 2..8 of the chain's PI vector.
const CHAIN_BASIS_OFF: usize = 2 * SK;
/// Six values at `SK` limbs each.
const NC: usize = 6 * SK;

fn chain_basis() -> Vec<BabyBear> {
    let v: Vec<u32> = CHAIN_PIS
        .split_whitespace()
        .map(|t| t.parse::<u32>().expect("a PI limb is a decimal"))
        .collect();
    assert_eq!(
        v.len(),
        8 * SK,
        "the scalar chain publishes eight 32-felt blocks since 2026-08-05"
    );
    assert!(
        v.iter().all(|l| *l < 256),
        "every published limb is eight bits"
    );
    let basis: Vec<BabyBear> = v[CHAIN_BASIS_OFF..]
        .iter()
        .map(|l| BabyBear::new(*l))
        .collect();
    assert_eq!(basis.len(), NC);
    // ⚑ Six DISTINCT values. A tap that aliased its register would publish six copies of `ξ⁴⁶`,
    // every length check would hold, and the aggregate would prove — so the distinctness is
    // checked here, on the felts, before anything is filled with them.
    for a in 0..6 {
        for b in (a + 1)..6 {
            assert_ne!(
                basis[a * SK..(a + 1) * SK],
                basis[b * SK..(b + 1) * SK],
                "published basis values {a} and {b} are the same 32 felts"
            );
        }
    }
    // …and the last block is `ξ` itself, which is block 0 of the same vector (the chain's
    // first-row input pin). That is the join to `dregg-mina-xi-endo-lift::v1`'s output.
    assert_eq!(
        basis[5 * SK..],
        v[..SK]
            .iter()
            .map(|l| BabyBear::new(*l))
            .collect::<Vec<_>>()[..],
        "the basis tail must be the chain's own input xi"
    );
    basis
}

#[test]
fn the_mina_xi_aggregate_scales_inside_the_circuit() {
    assert_eq!(
        sha256_hex(XIAGG_JSON.as_bytes()),
        XIAGG_SHA,
        "the xi-aggregate descriptor was re-emitted; re-read the Lean and re-pin"
    );
    let desc = parse(XIAGG_JSON);
    assert_eq!(
        desc.name, "dregg-pasta-msm-bucketed-pallas-n59b255-c2-w192::v1",
        "n, nbits and the challenge-block width are in the name"
    );
    let sh = shape_of(&desc);
    assert_eq!(sh.rows, 8192, "128 windows of 64 rows");
    assert_eq!(
        sh.n, 59,
        "47 real block commitments + 12 inert padding terms"
    );
    assert_eq!(sh.windows, 128, "ceil(255/2)");
    assert_eq!(sh.c, 2);
    assert_eq!(sh.levels, 3, "2^c - 1");
    assert_eq!(sh.nc, NC, "the six-value basis at 32 limbs each");
    assert_eq!(desc.public_input_count, PI_COUNT + NC, "27 + 192");
    assert_eq!(desc.trace_width, WK + NC, "612 + 192");
    assert_eq!(
        desc.constraints.len(),
        CONSTRAINTS + 2 * NC,
        "the narrow 91 plus 192 first-row challenge pins and 192 challenge threads"
    );
    assert_eq!(desc.tables.len(), 3, "the widening moved no manifest");

    // ⚑ THE SCALARS ARE FULL-WIDTH. Recompose term 1's declared digits and check it is a real
    // 255-bit scalar and not something that fits in a window or two — this is the difference
    // between "the aggregate scales in-circuit" and "a toy scales in-circuit".
    let mut top = 0usize;
    for w in 0..sh.windows {
        if sh.digits[w][1] != 0 {
            top = (sh.windows - w) * sh.c;
            break;
        }
    }
    assert!(
        top > 250,
        "xi^1 should occupy ~255 bits of declared digits, got {top}"
    );

    let basis = chain_basis();
    let (trace, pis) = honest_trace_with_chal(&sh, &basis);
    assert_eq!(
        &pis[PI_COUNT..],
        &basis[..],
        "the aggregate's wire block IS the scalar chain's published basis, felt for felt"
    );
    let got = Pt {
        x: read_field(trace.last().unwrap(), TOTX),
        y: read_field(trace.last().unwrap(), TOTX + NUM_LIMBS),
        z: read_field(trace.last().unwrap(), TOTX + 2 * NUM_LIMBS),
    };
    let gold = mina_combined_gold();
    assert!(
        on_curve_at(&P_PASTA, &gold),
        "o1-labs' aggregate is a real Pallas point"
    );
    assert!(
        proj_eq_at(&P_PASTA, &got, &gold),
        "the in-circuit accumulation did not reach o1-labs' aggregate for block 539508"
    );

    let t0 = Instant::now();
    prove_and_verify(&desc, &trace, &pis).unwrap_or_else(|e| {
        panic!(
            "the LEAN-AUTHORED AIR refused an honest xi-aggregate witness: {e}\n\
             (fix the WITNESS, never the AIR)"
        )
    });
    println!(
        "\n  [ξ-AGGREGATE] Mina devnet block 539508, 47 commitments at nbits=255, \n\
           {} rows x {} cols ({} of them the six-value basis on the wire), {} constraints \n\
           -> the trace REACHES o1-labs' COMBINED_GOLD, PROVED + VERIFIED in {:.1} ms. \n\
           The scalar multiplication is INSIDE the circuit and the challenge is ON THE WIRE.",
        sh.rows,
        WK + sh.nc,
        sh.nc,
        desc.constraints.len(),
        t0.elapsed().as_secs_f64() * 1e3
    );
}

/// ⚑ …and a forged aggregate is refused. The arithmetic cannot see this one — every row still adds
/// correctly — so the 27 output PI bindings are the only thing that can object. Same displacement,
/// same encoding idiom, as `a_forged_commitment_is_refused` above.
///
/// **REFUSING GATE: the LAST-ROW PI BINDINGS on `TOT`** (`PastaMsmBucketed.outPiGates`).
#[test]
fn a_forged_mina_xi_aggregate_is_refused() {
    let desc = parse(XIAGG_JSON);
    let sh = shape_of(&desc);
    let basis = chain_basis();
    let (trace, pis) = honest_trace_with_chal(&sh, &basis);

    let honest = Pt {
        x: read_field(trace.last().unwrap(), TOTX),
        y: read_field(trace.last().unwrap(), TOTX + NUM_LIMBS),
        z: read_field(trace.last().unwrap(), TOTX + 2 * NUM_LIMBS),
    };
    let forged = complete_add(&P_PASTA, &honest, &sh.gens[0]);
    assert!(
        !proj_eq_at(&P_PASTA, &honest, &forged),
        "the forgery must move the point"
    );

    let mut bad = pis.clone();
    for i in 0..NUM_LIMBS {
        bad[i] = BabyBear::new(forged.x.limb30(i));
        bad[NUM_LIMBS + i] = BabyBear::new(forged.y.limb30(i));
        bad[2 * NUM_LIMBS + i] = BabyBear::new(forged.z.limb30(i));
    }
    assert_ne!(bad, pis, "the forged PI vector must differ");
    assert_eq!(
        bad[PI_COUNT..],
        pis[PI_COUNT..],
        "this tamper moves the OUTPUT and leaves the basis alone"
    );

    let what = "the Mina xi-aggregate claimed as C + G, honest trace";
    let r = must_refuse_or_unsat_panic(what, || prove_and_verify(&desc, &trace, &bad));
    let reason = refused_by_gates(
        what,
        &r,
        &desc,
        &OUT_PI_GATES.collect::<Vec<_>>(),
        sh.rows - 1,
    );
    println!(
        "\n  [FORGED ξ-AGGREGATE] claimed COMBINED_GOLD + G -> REFUSED by outPiGates: {reason}"
    );
}

/// ⚑⚑ **A FORGED BASIS FELT IS REFUSED — the wire block is a CHECK, not a decoration.**
///
/// The whole point of widening the PI surface is that a verifier holding the scalar chain's output
/// can compare it against this aggregate's. That is worth nothing if the aggregate will prove
/// against any 192 felts, so: one felt of the published basis moved by one, trace untouched.
///
/// **REFUSING GATE: `PastaMsmBucketed.chalPinGates` — the FIRST-ROW PI binding** on column
/// `CHB + m`. Nothing else in this AIR reads a challenge column, so if this passed, the block would
/// be 192 free prover scalars.
///
/// ⚠ **The felt moved is READ FIRST.** A sibling in this cone drafted a refutation that moved a row
/// whose digit was zero into an accumulator that was also zero, and `decide` refuted the refutation.
/// A tamper that changes nothing is not a tamper.
#[test]
fn a_forged_basis_felt_is_refused() {
    let desc = parse(XIAGG_JSON);
    let sh = shape_of(&desc);
    let basis = chain_basis();
    let (trace, pis) = honest_trace_with_chal(&sh, &basis);

    // The most significant limb of the head basis value `ξ³²` — block 0, limb 31.
    let slot = PI_COUNT + SK - 1;
    let before = pis[slot];
    let after = before + BabyBear::new(1);
    assert_ne!(before, after, "the moved felt must actually change value");

    let mut bad = pis.clone();
    bad[slot] = after;
    assert_ne!(bad, pis, "the forged PI vector must differ");
    assert_eq!(
        bad[..PI_COUNT],
        pis[..PI_COUNT],
        "this tamper moves the BASIS and leaves the claimed aggregate alone"
    );

    // ⚑ THE GATE, NAMED: `chalPinGates[SK - 1]` — the first-row pin on column `CHB + 31`. Nothing
    // else in this AIR touches that column (the census below measures exactly that), so the
    // assertion that ONLY this constraint objected is the tooth's whole content.
    let what = "the xi-aggregate with one basis felt of xi^32 raised by one";
    let r = must_refuse_or_unsat_panic(what, || prove_and_verify(&desc, &trace, &bad));
    let reason = refused_by_gates(what, &r, &desc, &[chal_pin_gate(SK - 1)], 0);
    println!(
        "\n  [FORGED BASIS FELT] pi[{slot}] {before:?} -> {after:?} \
         -> REFUSED by chalPinGates[{}] on row 0: {reason}",
        SK - 1
    );
}

/// ⚑⚑ **A BASIS THAT VARIES BY ROW IS REFUSED — the pin alone would not have caught this.**
///
/// A PI binding looks at ONE row. Without `chalThreadGates` a prover may pin the honest basis on
/// row 0 and use anything it likes on the other 8 191 — which is precisely the forgery
/// `PastaMsmScalarDerive` §5d exhibits ("a prover using a FRESH CHALLENGE VECTOR PER ROW, which the
/// row-local denotation accepts and the wire gates refuse"). This is that forgery on this layout.
///
/// **REFUSING GATE: `PastaMsmBucketed.chalThreadGates` — `nxt CH_m − CH_m` on the transition.**
///
/// ⚠ The cell moved is READ FIRST, and it is deliberately in a row that is neither the first (which
/// the pin already covers) nor the last.
#[test]
fn a_basis_that_varies_by_row_is_refused() {
    let desc = parse(XIAGG_JSON);
    let sh = shape_of(&desc);
    let basis = chain_basis();
    let (mut trace, pis) = honest_trace_with_chal(&sh, &basis);

    let row = 4096usize;
    let col = WK + SK - 1;
    assert!(row > 0 && row + 1 < sh.rows, "an interior row");
    let before = trace[row][col];
    let after = before + BabyBear::new(1);
    assert_ne!(before, after, "the moved cell must actually change value");
    assert_eq!(
        trace[0][col], before,
        "the honest fill is constant down the column, which is what the thread demands"
    );
    trace[row][col] = after;
    assert_eq!(
        trace[0][col], before,
        "row 0 is untouched, so the PI pin still holds and only the thread can object"
    );

    // ⚑ THE GATE, NAMED: `chalThreadGates[SK - 1]`, and it fires on the TRANSITION INTO the moved
    // row — p3 names the window gate by its LOWER row, so `row - 1`. That the pin (row 0) does NOT
    // also appear in the failed set is what distinguishes this tooth from the one above it.
    let what = "the xi-aggregate with a fresh basis felt on row 4096";
    let r = must_refuse_or_unsat_panic(what, || prove_and_verify(&desc, &trace, &pis));
    let reason = refused_by_gates(what, &r, &desc, &[chal_thread_gate(sh.nc, SK - 1)], row - 1);
    println!(
        "\n  [PER-ROW BASIS] trace[{row}][{col}] {before:?} -> {after:?} \
         (row 0 and the public inputs untouched) -> REFUSED by chalThreadGates[{}]: {reason}",
        SK - 1
    );
}

/// ⚑⚑ **THE 192 WIRE FELTS ARE NOT BOUND TO THE MSM — the census's verdict, EXHIBITED.**
///
/// `scripts/check-descriptor-anchor-inertness.py` scores this descriptor at **192 decorative
/// anchors**: columns `612 … 803` are each touched by exactly two constraints — `chalPinGates`'
/// first-row `piBinding` and `chalThreadGates`' `nxt CH_m − CH_m` — and by nothing that relates
/// them to another column. The two teeth above prove those two constraints FIRE; this one proves
/// what they do NOT reach.
///
/// ⚠ **It is here because the census was measurably wrong about this exact class the day the row
/// was minted.** A `proof_bind` widening made `commit`/`vk`/`bound` lane VECTORS and the walker
/// took only the operands that were themselves an expression dict, so a sibling descriptor scored
/// 18 → 27 decorative with no anchor having changed. The walker is fixed; a graph property that
/// nobody exercises is still a claim about a script. This is the claim on the machine.
///
/// The forgery: the block's own basis with one felt of `ξ³²` moved by one, applied to the trace
/// **and** the public inputs together — so the pin holds, the thread holds, and the only thing
/// left to object would be a gate that READS the basis. The proof is **accepted**, and the
/// aggregate it publishes is bit-for-bit the honest one: o1-labs' `COMBINED_GOLD` for Mina devnet
/// block 539508, reached by a trace that never looked at the basis at all.
///
/// ⚠ **WHAT DOES TIE THE BASIS TODAY IS OUTSIDE THIS AIR.** A batch verifier compares
/// `aggPIs[27 … 218]` against `dregg-mina-xi-scalar-vector::v2`'s published block felt by felt
/// (`MinaWrapXiBasisWeld`), and `chain_basis` above is that comparison in this harness. That weld
/// makes the value non-free **relative to another proof of this block's transcript**; it does not
/// make `T_COVER`'s digits the basis's in-circuit image. The digits are permutation-forced
/// DESCRIPTOR data, so this is not a forgeable-digit hole — it is a 192-felt public statement that
/// this proof does not make.
///
/// ⚑ **THIS TEST IS THE GATE ON THE REPAIR, AND IT IS MEANT TO GO RED.** When the tensor/digit
/// chain lands (`MinaWrapXiAggregateMsm` §4 / `PastaMsmBucketed` §7.3 — ~1 400 constraints,
/// ~2 700 columns, plus the `8 → 30` limb regroup and its range certificates), this call starts
/// REFUSING. Then: invert it to `must_refuse_or_unsat_panic` naming the new gate, and drop this
/// descriptor's row in `scripts/descriptor-anchor-inertness-baseline.txt` from 192 to 0.
#[test]
fn the_published_basis_is_not_yet_bound_to_the_declared_digits() {
    let desc = parse(XIAGG_JSON);
    let sh = shape_of(&desc);
    let honest_basis = chain_basis();

    // ⚠ The felt is READ FIRST and the change is ASSERTED to move it. A sibling in this cone
    // drafted a refutation that moved a zero into a zero and `decide` refuted the refutation.
    let mut wrong_basis = honest_basis.clone();
    let slot = SK - 1; // the most significant limb of the head value `ξ³²`
    let before = wrong_basis[slot];
    let after = before + BabyBear::new(1);
    assert_ne!(before, after, "the moved felt must actually change value");
    wrong_basis[slot] = after;
    assert_ne!(
        wrong_basis, honest_basis,
        "the basis under test must differ from the block's own"
    );

    // ⚠ And the filler must not quietly restore it. `honest_trace_with_chal` copies `chal` verbatim
    // into columns `WK … WK + nc`, so this is checked rather than assumed — two lanes elsewhere
    // today forged a lane the filler rewrites and passed for the wrong reason.
    let (trace, pis) = honest_trace_with_chal(&sh, &wrong_basis);
    assert_eq!(
        &pis[PI_COUNT..],
        &wrong_basis[..],
        "the filler rewrote the challenge block; this tamper would test nothing"
    );
    assert_eq!(
        trace[0][WK + slot],
        after,
        "the forged felt must be the one on the wire"
    );
    assert_eq!(
        trace[sh.rows - 1][WK + slot],
        after,
        "…and down the whole trace, so the thread holds and cannot be what objects"
    );

    prove_and_verify(&desc, &trace, &pis).unwrap_or_else(|e| {
        panic!(
            "the ξ-aggregate REFUSED a basis that is not the block's own: {e}\n\
             ⚑ If that is because the tensor/digit chain landed, this is the GOOD red: invert this \
             test to `must_refuse_or_unsat_panic` naming the new gate, and take this descriptor's \
             row in scripts/descriptor-anchor-inertness-baseline.txt from 192 to 0."
        )
    });

    // …and the accepted proof publishes the HONEST aggregate. The forged basis changed the public
    // statement and changed nothing the proof is about.
    let (honest_trace, honest_pis) = honest_trace_with_chal(&sh, &honest_basis);
    assert_eq!(
        pis[..PI_COUNT],
        honest_pis[..PI_COUNT],
        "the claimed aggregate must be untouched — otherwise the basis DID reach the arithmetic"
    );
    let got = Pt {
        x: read_field(trace.last().unwrap(), TOTX),
        y: read_field(trace.last().unwrap(), TOTX + NUM_LIMBS),
        z: read_field(trace.last().unwrap(), TOTX + 2 * NUM_LIMBS),
    };
    assert!(
        proj_eq_at(&P_PASTA, &got, &mina_combined_gold()),
        "the forged-basis trace still reaches o1-labs' COMBINED_GOLD"
    );
    assert_eq!(
        trace.last().unwrap()[..WK],
        honest_trace.last().unwrap()[..WK],
        "…and every column of the row template is identical: 192 felts moved, the MSM did not"
    );

    println!(
        "\n  [DECORATIVE] a basis that is NOT the block's own (pi[{}] {before:?} -> {after:?}) \n\
           PROVES and VERIFIES, and still publishes o1-labs' COMBINED_GOLD. {} of {} public \n\
           inputs ({:.1}%) are carried by this proof and read by no constraint. \n\
           Baseline row: 192  dregg-pasta-msm-bucketed-pallas-n59b255-c2-w192::v1",
        PI_COUNT + slot,
        NC,
        desc.public_input_count,
        100.0 * NC as f64 / desc.public_input_count as f64
    );
}
