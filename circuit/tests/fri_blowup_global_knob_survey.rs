//! # THE GLOBAL FRI `log_blowup` KNOB, PRICED ACROSS THE DESCRIPTOR REGISTRY — MEASURED.
//!
//! `IR2_FRI_LOG_BLOWUP = 6` (`descriptor_ir2.rs`) is **one knob for all 88 by-name descriptors**:
//! `ir2_config()` is a thread-local built from six `const`s, and both `prove_vm_descriptor2` and
//! `verify_vm_descriptor2` reach it with no per-descriptor input at all. So the justification —
//! `.docs-history-noclaude/PROOF-ECONOMICS.md` §2c, a grid measured on ONE descriptor (transfer) —
//! is a claim about eighty-eight objects supported by a measurement of one.
//!
//! This file measures the OTHER descriptors. It changes no deployed constant.
//!
//! ## What is held fixed
//!
//! The security-PARITY points named in `ir2_config`'s own docblock — `(6,19)`, `(2,57)`, `(1,114)`
//! — all read `q·lb + 16 = 130` conjectured and `q·lb/2 + 16 = 73` proven/Johnson. Two interior
//! rungs, `(4,29)` and `(3,39)`, are added so the curve has a shape. Every row below is at parity
//! on both query ledgers; the axes that move are prover time, PEAK MEMORY, proof BYTES and
//! VERIFIER time.
//!
//! ⚑ The query ledgers are not the only columns. `FriLedger`'s per-fold and commit-phase (`ε_C`)
//! columns both move the OTHER way with `log_blowup` — `ε_C` carries `1/(2ρ^{3/2}) = 2^(3·lb/2−1)`,
//! so a smaller blowup IMPROVES it. Those numbers come from Lean
//! (`circuit-prove/tests/fri_params_soundness_budget.rs`), never from here.
//!
//! ## ⚑ THE PROBE ROW WHOSE TRUE COST IS ALREADY KNOWN
//!
//! The sound Pasta multiply at 8 rows: `3dcefe00a` measured 173.8 ms prove / 18.8 ms verify in
//! release, and the deployed `(6,19)` point at 8192 rows serializes to **431.2 KiB** (measured
//! 2026-08-04 by the sibling `pasta_sound_atom_price_and_fri_repricing.rs::§C2`, one process). Both
//! are ASSERTED here, so a harness measuring something else (debug mode, a cached proof, a
//! different config) REDS instead of producing plausible noise.
//!
//! Run (release only — a debug timing here is meaningless):
//! ```text
//! cargo test -p dregg-circuit --release --test fri_blowup_global_knob_survey -- --nocapture --test-threads=1
//! ```
//! One point per process, for OS-measured peak RSS:
//! ```text
//! DREGG_FRI_ONE_CASE=<label> DREGG_FRI_ONE=<lb>,<q> \
//!   /usr/bin/time -l ./<binary> one_case_one_point_per_process --nocapture
//! ```

use dregg_circuit::BabyBear;
use dregg_circuit::descriptor_by_name::descriptor_by_name;
use dregg_circuit::descriptor_ir2::{
    DreggStarkConfig, EffectVmDescriptor2, MemBoundaryWitness, TableSem, VmConstraint2,
    decomp_cols_pub, parse_vm_descriptor2, parse_vm_descriptor2_unsound_oversized,
    prove_vm_descriptor2_with_config, verify_vm_descriptor2_with_config,
};
use dregg_circuit::plonky3_prover::create_config_with_fri_full;

// ─────────────────────────────────────────────────────────────────────────────
// THE PARITY LADDER
// ─────────────────────────────────────────────────────────────────────────────

/// `(log_blowup, num_queries)` at conjectured-130 / proven-73 parity on the query ledgers.
/// `(6,19)` is `ir2_config`. `(1,114)` is omitted from the default grid only because it is the
/// slowest row to serialize, not because it is unreachable — `pasta_sound_atom_price_and_fri_repricing`
/// proves and verifies it.
const PARITY: &[(usize, usize)] = &[(6, 19), (4, 29), (3, 39), (2, 57)];

/// The deployed knobs, restated so a config built here is byte-identical to `ir2_config()` at
/// `(6, 19)` and differs at every other rung in EXACTLY the two knobs under study.
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

// ─────────────────────────────────────────────────────────────────────────────
// THE MEASURED CASES — every by-name descriptor reachable from an HONEST witness
// generator or a checked-in Lean-emitted fixture, in `dregg-circuit`'s own API.
// ─────────────────────────────────────────────────────────────────────────────

struct Case {
    label: &'static str,
    desc: EffectVmDescriptor2,
    trace: Vec<Vec<BabyBear>>,
    pis: Vec<BabyBear>,
}

const MUL_DESC_JSON: &str = include_str!("../descriptors/by-name/pasta-fpmul-sound.json");
const MUL_TRACE: &str = include_str!("fixtures/pasta-fpmul-sound-trace.txt");
const ADD_DESC_JSON: &str = include_str!("../descriptors/by-name/pasta-fpadd-sound.json");
const ADD_TRACE: &str = include_str!("fixtures/pasta-fpadd-sound-trace.txt");
const RCB_DESC_JSON: &str = include_str!("../descriptors/by-name/pasta-rcb-windowed.json");
const RCB_TRACE_1024: &str = include_str!("fixtures/pasta-rcb-windowed-trace-1024.txt");

fn parse_rows(text: &str, width: usize) -> Vec<Vec<BabyBear>> {
    let rows: Vec<Vec<BabyBear>> = text
        .lines()
        .filter(|l| !l.trim().is_empty())
        .map(|l| {
            l.split_whitespace()
                .map(|t| BabyBear::new(t.parse::<u32>().expect("cell is a u32 decimal")))
                .collect::<Vec<_>>()
        })
        .collect();
    assert!(!rows.is_empty(), "the Lean-emitted fixture is non-empty");
    assert!(
        rows.iter().all(|r| r.len() == width),
        "every fixture row is {width} wide"
    );
    rows
}

/// The two sound Pasta field AIRs are ROW-LOCAL (no `on_transition` leg), so cycling an honest
/// block is a valid witness — the same replication `pasta_sound_atom_price_and_fri_repricing`
/// uses, not a padding trick.
fn cycle_to(base: &[Vec<BabyBear>], n: usize) -> Vec<Vec<BabyBear>> {
    (0..n).map(|i| base[i % base.len()].clone()).collect()
}

fn cases() -> Vec<Case> {
    use dregg_circuit::attested_fact_membership_witness as attested;
    use dregg_circuit::blinded_membership_witness as blinded;
    use dregg_circuit::delegate_descriptor as delegate;
    use dregg_circuit::membership_descriptor_4ary as m4;
    use dregg_circuit::membership_descriptor_general as mg;
    use dregg_circuit::poseidon2_air as p2;
    use dregg_circuit::presentation_descriptor_witness as pres;
    use dregg_circuit::turn_chain_witness as tcb;

    let mut out: Vec<Case> = Vec::new();

    // ── the NARROWEST committed shape in the registry: 3 declared columns + chip lanes.
    {
        let (trace, pis) = p2::poseidon2_hash_witness(BabyBear::new(7), BabyBear::new(11));
        out.push(Case {
            label: "poseidon2-hash-arity2",
            desc: p2::poseidon2_hash_descriptor(),
            trace,
            pis,
        });
    }

    // ── turn-chain binding: 7 columns, NO chip, NO range — a main-table-only descriptor.
    {
        let roots: Vec<BabyBear> = (0..5).map(|i| BabyBear::new(100 + i)).collect();
        let turns: Vec<(BabyBear, BabyBear)> = (0..4).map(|i| (roots[i], roots[i + 1])).collect();
        let (trace, pis) = tcb::turn_chain_binding_witness(&turns).expect("turn-chain witness");
        out.push(Case {
            label: "turn-chain-binding",
            desc: descriptor_by_name(tcb::TURN_CHAIN_BINDING_NAME).expect("dispatch"),
            trace,
            pis,
        });
    }

    // ── blinded membership: 12 columns, THREE chip lookups.
    {
        let sibs: Vec<[BabyBear; 3]> = (0..2)
            .map(|i| core::array::from_fn(|k| BabyBear::new((i * 3 + k + 1) as u32)))
            .collect();
        let (trace, pis) = blinded::blinded_membership_witness(
            BabyBear::new(1001),
            BabyBear::new(0xB11D),
            &sibs,
            &[0, 0],
        )
        .expect("blinded witness");
        out.push(Case {
            label: "blinded-membership",
            desc: descriptor_by_name(blinded::BLINDED_MEMBERSHIP_NAME).expect("dispatch"),
            trace,
            pis,
        });
    }

    // ── depth-general BINARY membership at depth 4: 13 columns, chip.
    {
        let path: Vec<mg::MembershipStep> = (0..4)
            .map(|i| mg::MembershipStep {
                sibling: BabyBear::new(31 + i as u32),
                dir: i % 2 == 1,
            })
            .collect();
        let (trace, pis) =
            mg::membership_witness(BabyBear::new(42), &path).expect("binary membership witness");
        out.push(Case {
            label: "merkle-membership-binary-d4",
            desc: mg::membership_descriptor_of_depth(4),
            trace,
            pis,
        });
    }

    // ── presentation freshness: 23 columns, TWO Range{30} lookups (so a byte table appears).
    {
        let summary = pres::summary_from_fields(
            BabyBear::new(0xFED),
            &core::array::from_fn(|k| BabyBear::new(k as u32 + 1)),
            BabyBear::new(1234),
            BabyBear::new(0x7A6),
            &core::array::from_fn(|k| BabyBear::new(k as u32 + 9)),
        );
        let (trace, pis) =
            pres::presentation_freshness_witness(&summary, BabyBear::new(100), BabyBear::new(500))
                .expect("presentation witness");
        out.push(Case {
            label: "presentation-freshness",
            desc: descriptor_by_name(pres::PRESENTATION_FRESHNESS_NAME).expect("dispatch"),
            trace,
            pis,
        });
    }

    // ── delegate scope binding: 24 columns, PI-binding only — no chip, no range, one table.
    {
        let scope: [BabyBear; delegate::DELEGATE_SCOPE_LIMBS] =
            core::array::from_fn(|i| BabyBear::new(1000 + i as u32));
        let (trace, pis) = delegate::delegate_binding_witness(&scope);
        out.push(Case {
            label: "delegate-scope-v2",
            desc: delegate::delegate_binding_descriptor(),
            trace,
            pis,
        });
    }

    // ── attested-fact membership: 34 columns, three chip lookups.
    {
        let sibs: Vec<[BabyBear; 3]> = (0..2)
            .map(|i| core::array::from_fn(|k| BabyBear::new((i * 3 + k + 5) as u32)))
            .collect();
        let (trace, pis) = attested::attested_fact_membership_witness(
            BabyBear::new(1234),
            BabyBear::new(0x57A7E),
            BabyBear::new(99),
            &sibs,
            &[0, 0],
        )
        .expect("attested witness");
        out.push(Case {
            label: "attested-fact-membership",
            desc: descriptor_by_name(attested::ATTESTED_FACT_MEMBERSHIP_NAME).expect("dispatch"),
            trace,
            pis,
        });
    }

    // ── 4-ARY node8 membership at depth 4: 90 columns, chip-heavy.
    {
        let leaf: m4::Digest8 = core::array::from_fn(|k| BabyBear::new(k as u32 + 1));
        let (sibs, pos, _root) = m4::create_test_witness(leaf, 4);
        let (trace, pis) =
            m4::membership_witness_4ary(leaf, &sibs, &pos).expect("4ary membership witness");
        out.push(Case {
            label: "merkle-membership-4ary-d4",
            desc: m4::membership_descriptor_of_depth_4ary(4),
            trace,
            pis,
        });
    }

    // ── the sound Pasta add: 128 declared → 384 committed, 128 range lookups, at 64 rows.
    {
        let base = parse_rows(ADD_TRACE, 128);
        out.push(Case {
            label: "pasta-fpadd-sound@64",
            desc: parse_vm_descriptor2(ADD_DESC_JSON).expect("fpadd parses"),
            trace: cycle_to(&base, 64),
            pis: vec![],
        });
    }

    // ── the windowed RCB row: 525 declared, ZERO lookups — the WIDE, ONE-TABLE shape.
    {
        let trace = parse_rows(RCB_TRACE_1024, 525);
        assert_eq!(
            trace.len(),
            1024,
            "the Lean-emitted RCB fixture is 1024 rows"
        );
        out.push(Case {
            label: "pasta-rcb-windowed@1024",
            desc: parse_vm_descriptor2_unsound_oversized(RCB_DESC_JSON).expect("rcb parses"),
            trace,
            pis: vec![],
        });
    }

    // ── the sound Pasta multiply: 190 declared → 694 committed, 190 range lookups.
    {
        let base = parse_rows(MUL_TRACE, 190);
        let desc = parse_vm_descriptor2(MUL_DESC_JSON).expect("fpmul parses");
        out.push(Case {
            label: "pasta-fpmul-sound@64",
            desc: desc.clone(),
            trace: cycle_to(&base, 64),
            pis: vec![],
        });
        out.push(Case {
            label: "pasta-fpmul-sound@4096",
            desc,
            trace: cycle_to(&base, 4096),
            pis: vec![],
        });
    }

    out
}

/// The committed MAIN width: declared columns plus the nibble aux block each range lookup adds.
/// Read through the deployed `decomp_cols_pub`, not modelled.
fn committed_main_width(desc: &EffectVmDescriptor2) -> (usize, usize, usize) {
    let mut aux = 0usize;
    let mut nlk = 0usize;
    for c in &desc.constraints {
        if let VmConstraint2::Lookup(l) = c {
            if let Some(bits) =
                desc.tables
                    .iter()
                    .find(|t| t.id == l.table)
                    .and_then(|t| match t.sem {
                        TableSem::Range { bits } => Some(bits),
                        _ => None,
                    })
            {
                aux += decomp_cols_pub(bits);
                nlk += 1;
            }
        }
    }
    (desc.trace_width, desc.trace_width + aux, nlk)
}

// ─────────────────────────────────────────────────────────────────────────────
// §1 — THE MEASURED GRID
// ─────────────────────────────────────────────────────────────────────────────

#[derive(Clone)]
struct Point {
    lb: usize,
    q: usize,
    /// `Err(reason)` when the PROVER refused this rung for this descriptor — the load-bearing
    /// column. A blowup below a table's constraint-degree floor is not a slower point, it is
    /// NOT A POINT, and a sweep that panics on it hides that from the table.
    outcome: Result<(usize, f64, f64), String>,
}

struct Measured {
    label: &'static str,
    committed: usize,
    rows: usize,
    tables: usize,
    /// Range lookups the main layout carries — the second regressor of the §1b predictor.
    range_lookups: usize,
    /// Does this descriptor pull in the Poseidon2 CHIP table? (`TID_P2` / `TID_P2_NARROW` lookup.)
    /// The chip carries the inline degree-7 x⁷ S-box, so it is the table whose degree sets the
    /// descriptor's blowup FLOOR.
    chip: bool,
    points: Vec<Point>,
}

fn has_chip_lookup(desc: &EffectVmDescriptor2) -> bool {
    use dregg_circuit::descriptor_ir2::{TID_P2, TID_P2_NARROW};
    desc.constraints.iter().any(
        |c| matches!(c, VmConstraint2::Lookup(l) if l.table == TID_P2 || l.table == TID_P2_NARROW),
    )
}

fn measure(case: &Case) -> Measured {
    let (_, committed, range_lookups) = committed_main_width(&case.desc);
    let mut points = Vec::new();
    let mut tables = 0usize;
    for &(lb, q) in PARITY {
        let cfg = config_at(lb, q);
        // TWICE, report the SECOND. The first pass at a NEW blowup re-sizes the DFT/Merkle
        // scratch; that allocation is not part of the steady-state cost being compared. An
        // un-warmed sweep of this shape measured the deployed (6,19) point 2.3x slow, which
        // would have manufactured a fake speedup on every other row.
        let mut prove_ms = f64::NAN;
        let mut proof = None;
        let mut refusal = None;
        for _ in 0..2 {
            let t0 = std::time::Instant::now();
            match prove_vm_descriptor2_with_config(
                &case.desc,
                &case.trace,
                &case.pis,
                &MemBoundaryWitness::default(),
                &[],
                &cfg,
            ) {
                Ok(p) => {
                    prove_ms = t0.elapsed().as_secs_f64() * 1000.0;
                    proof = Some(p);
                }
                Err(e) => {
                    refusal = Some(e);
                    break;
                }
            }
        }
        let Some(proof) = proof else {
            points.push(Point {
                lb,
                q,
                outcome: Err(refusal.unwrap_or_else(|| "unknown refusal".into())),
            });
            continue;
        };
        tables = proof.degree_bits.len();
        let t1 = std::time::Instant::now();
        let verified = verify_vm_descriptor2_with_config(&case.desc, &proof, &case.pis, &cfg);
        let verify_ms = t1.elapsed().as_secs_f64() * 1000.0;
        let bytes = postcard::to_allocvec(&proof).expect("serialize").len();
        points.push(Point {
            lb,
            q,
            outcome: match verified {
                Ok(()) => Ok((bytes, prove_ms, verify_ms)),
                Err(e) => Err(format!("VERIFY REFUSED: {e}")),
            },
        });
    }
    Measured {
        label: case.label,
        committed,
        rows: case.trace.len(),
        tables,
        range_lookups,
        chip: has_chip_lookup(&case.desc),
        points,
    }
}

/// ⚑ **THE GRID.** Every provable by-name descriptor at every parity rung, with the probe row
/// asserted so a broken harness reds.
///
/// `#[ignore]` because it is a RELEASE-ONLY MEASUREMENT and its assertions are calibrated in
/// release milliseconds — a debug run of it would take minutes and red on the probe band, which
/// would be a false red about the build profile rather than about the tree. The two STRUCTURAL
/// tests in this file (`the_whole_registry_…`, `the_row_ceiling_…`) carry no timing and stay in
/// the default path. Run this one with:
/// ```text
/// cargo test -p dregg-circuit --release --test fri_blowup_global_knob_survey \
///   -- --ignored --nocapture --test-threads=1
/// ```
#[test]
#[ignore = "release-only measurement (~40 s); its probe assertions are release-calibrated"]
fn every_provable_descriptor_at_every_parity_point() {
    // WARM-UP, and it is not politeness: the first prove in a process pays the rayon pool
    // spin-up, the thread-local config build and a cold allocator. Discarded, never reported.
    {
        let warm = &cases()[0];
        let cfg = config_at(6, 19);
        let p = prove_vm_descriptor2_with_config(
            &warm.desc,
            &warm.trace,
            &warm.pis,
            &MemBoundaryWitness::default(),
            &[],
            &cfg,
        )
        .expect("warm-up proves");
        verify_vm_descriptor2_with_config(&warm.desc, &p, &warm.pis, &cfg)
            .expect("warm-up verifies");
    }

    println!("\n═══ THE GLOBAL FRI KNOB, ACROSS THE REGISTRY (security at parity) ═══");
    println!(
        "{:<28}{:>6}{:>7}{:>4}{:>6}  {:>7}{:>10}{:>10}{:>10}",
        "descriptor", "rows", "commit", "tbl", "chip", "(lb,q)", "bytes", "prove ms", "verify ms"
    );

    let mut all: Vec<Measured> = Vec::new();
    for case in cases() {
        let m = measure(&case);
        for p in &m.points {
            let head = p.lb == PARITY[0].0;
            let (l, r, c, t, k) = if head {
                (
                    m.label.to_string(),
                    m.rows.to_string(),
                    m.committed.to_string(),
                    m.tables.to_string(),
                    if m.chip { "yes" } else { "no" }.to_string(),
                )
            } else {
                Default::default()
            };
            match &p.outcome {
                Ok((bytes, prove_ms, verify_ms)) => println!(
                    "{l:<28}{r:>6}{c:>7}{t:>4}{k:>6}  {:>7}{bytes:>10}{prove_ms:>10.1}{verify_ms:>10.2}",
                    format!("({},{})", p.lb, p.q)
                ),
                Err(e) => println!(
                    "{l:<28}{r:>6}{c:>7}{t:>4}{k:>6}  {:>7}   REFUSED: {e}",
                    format!("({},{})", p.lb, p.q)
                ),
            }
        }
        all.push(m);
    }

    // ── THE TRADE, one line per descriptor: what lb 6→2 costs on the wire and buys on the clock.
    println!("\n═══ (6,19) → (2,57): the trade, per descriptor ═══");
    println!(
        "{:<28}{:>6}{:>8}{:>12}{:>12}{:>10}{:>12}{:>12}",
        "descriptor", "chip", "commit", "bytes@6", "bytes@2", "Δ bytes", "prove x", "verify x"
    );
    for m in &all {
        let a = m.points.iter().find(|p| p.lb == 6).expect("(6,19) row");
        let b = m.points.iter().find(|p| p.lb == 2).expect("(2,57) row");
        let chip = if m.chip { "yes" } else { "no" };
        match (&a.outcome, &b.outcome) {
            (Ok((ab, apm, avm)), Ok((bb, bpm, bvm))) => println!(
                "{:<28}{chip:>6}{:>8}{ab:>12}{bb:>12}{:>+10}{:>11.2}x{:>11.2}x",
                m.label,
                m.committed,
                *bb as i64 - *ab as i64,
                apm / bpm,
                bvm / avm,
            ),
            (Ok((ab, _, _)), Err(_)) => println!(
                "{:<28}{chip:>6}{:>8}{ab:>12}{:>12}   — lb=2 IS NOT A POINT FOR THIS DESCRIPTOR",
                m.label, m.committed, "REFUSED",
            ),
            _ => println!(
                "{:<28}{chip:>6}{:>8}   (6,19) REFUSED",
                m.label, m.committed
            ),
        }
    }

    // ── ⚑ THE BLOWUP FLOOR IS PER-DESCRIPTOR, AND IT IS NOT lb=1.
    println!("\n═══ THE PER-DESCRIPTOR BLOWUP FLOOR (lowest parity rung that PROVES) ═══");
    for m in &all {
        let floor = m
            .points
            .iter()
            .filter(|p| p.outcome.is_ok())
            .map(|p| p.lb)
            .min();
        println!(
            "{:<28}chip={:<5}floor = {}",
            m.label,
            m.chip,
            match floor {
                Some(lb) => format!("log_blowup {lb} (of the rungs tried: {PARITY:?})"),
                None => "NO RUNG PROVED".to_string(),
            }
        );
    }

    // ── THE CALIBRATION. The structural prediction: at parity `q·lb` is fixed, so the only term
    // that moves with `q` is the PER-QUERY opening — one row of every committed matrix plus its
    // Merkle path. So `Δbytes(6→2) ≈ (57−19) · (4·W + c)` for a per-query fixed cost `c` that is a
    // function of the table SET and the Merkle depths, not of the width. Fit `c` on the measured
    // set by least squares through `Δbytes/38 = 4·W + c`, then report the per-descriptor error.
    let fitted: Vec<(&Measured, f64, usize)> = all
        .iter()
        .filter_map(|m| {
            let a = m.points.iter().find(|p| p.lb == 6)?.outcome.as_ref().ok()?;
            let b = m.points.iter().find(|p| p.lb == 2)?.outcome.as_ref().ok()?;
            Some((m, (b.0 as f64 - a.0 as f64) / 38.0, m.range_lookups))
        })
        .collect();
    // TWO regressors, NO intercept: a per-query cost must vanish as the committed columns do.
    // Normal equations for `P = α·W + β·n_lk`.
    let (mut aa, mut ab, mut bb, mut ay, mut by) = (0.0, 0.0, 0.0, 0.0, 0.0);
    for (m, y, nlk) in &fitted {
        let (w, l) = (m.committed as f64, *nlk as f64);
        aa += w * w;
        ab += w * l;
        bb += l * l;
        ay += w * y;
        by += l * y;
    }
    let det = aa * bb - ab * ab;
    let (slope_w, slope_l) = if det.abs() > 1e-9 {
        ((ay * bb - by * ab) / det, (by * aa - ay * ab) / det)
    } else {
        (ay / aa, 0.0)
    };
    println!(
        "\n═══ THE STRUCTURAL PREDICTOR, CALIBRATED ON THIS RUN ═══\n\
         fit  Δbytes(6→2) = 38 · ({slope_w:.3} · W_committed_main + {slope_l:.3} · n_range_lookups)\n\
         frozen in §1b as ({P_PER_COLUMN} , {P_PER_RANGE_LOOKUP}) — a large drift here means the \
         registry census below is priced off a stale fit."
    );
    println!(
        "\n{:<28}{:>8}{:>7}{:>14}{:>14}{:>10}{:>12}",
        "descriptor", "commit", "rng lk", "Δ measured", "Δ predicted", "err %", "err bytes"
    );
    let mut worst = 0.0f64;
    for (m, y, nlk) in &fitted {
        let measured = y * 38.0;
        let predicted =
            38.0 * (P_PER_COLUMN * m.committed as f64 + P_PER_RANGE_LOOKUP * *nlk as f64);
        let err = if measured.abs() > 1.0 {
            (predicted - measured) / measured * 100.0
        } else {
            0.0
        };
        worst = worst.max(err.abs());
        println!(
            "{:<28}{:>8}{:>7}{:>14.0}{:>14.0}{:>9.1}%{:>+12.0}",
            m.label,
            m.committed,
            nlk,
            measured,
            predicted,
            err,
            predicted - measured
        );
    }
    println!(
        "\nworst per-descriptor prediction error: {worst:.1}%  \
         (the frozen §1b coefficients claim ±{P_FIT_WORST_ERR_PCT:.0}%)"
    );
    assert!(
        worst < 120.0,
        "the frozen §1b predictor missed by {worst:.1}% on the set it was fitted to — it is no \
         longer describing this tree and every §1b byte count is decoration. Re-fit \
         P_PER_COLUMN/P_PER_RANGE_LOOKUP from the printed slopes."
    );

    // ── THE PROBE. Two independently-recorded costs, asserted.
    let mul4096 = all
        .iter()
        .find(|m| m.label == "pasta-fpmul-sound@4096")
        .expect("the fpmul probe case is in the grid");
    assert_eq!(
        mul4096.committed, 694,
        "the sound multiply commits 694 columns (190 declared + the nibble aux block over 190 \
         range lookups). A different number means `decomp_cols_pub` or the descriptor moved and \
         every width in this table is denominated in the wrong unit."
    );
    let (mul_bytes, mul_prove_ms, _) = mul4096
        .points
        .iter()
        .find(|p| p.lb == 6)
        .unwrap()
        .outcome
        .as_ref()
        .expect("the deployed (6,19) point must prove on the probe case");
    assert!(
        *mul_bytes > 380 * 1024 && *mul_bytes < 460 * 1024,
        "the 4096-row sound multiply at the DEPLOYED (6,19) serialized to {mul_bytes} B; the \
         recorded 8192-row figure is 431.2 KiB and the 4096-row figure 426.5 KiB (proof size is \
         nearly height-independent at these shapes). Far outside that band means this harness is \
         not measuring the deployed config."
    );
    assert!(
        *mul_prove_ms > 200.0 && *mul_prove_ms < 60_000.0,
        "the 4096-row multiply proved in {mul_prove_ms:.1} ms at (6,19); the recorded release cost \
         is ~3.8 s. Outside that band means debug mode, a cached proof, or a different descriptor \
         — and no row of this table is a measurement."
    );

    // ── THE DIRECTION OF THE TRADE, asserted so a silent inversion cannot pass.
    for (m, y, _) in &fitted {
        assert!(
            *y > 0.0,
            "{}: dropping blowup at parity must GROW the wire (3x the queries, each opening a row \
             of every committed matrix). If that ever inverts, the per-query cost has stopped \
             dominating and §2c's premise needs re-deriving.",
            m.label
        );
    }

    // ── ⚑ AND THE FLOOR IS REAL. At least one CHIP-BEARING descriptor must REFUSE at lb=2:
    // the Poseidon2 chip's inline degree-7 x⁷ S-box needs a quotient degree of 6, and
    // `log_blowup = 2` (blowup 4) cannot carry it. A green sweep in which every descriptor proves
    // at every rung would mean this harness is not exercising the chip at all — and "land lb=2
    // globally" would read as free when it is not expressible.
    let chip_refusals: Vec<&str> = all
        .iter()
        .filter(|m| m.chip && m.points.iter().any(|p| p.lb == 2 && p.outcome.is_err()))
        .map(|m| m.label)
        .collect();
    assert!(
        !chip_refusals.is_empty(),
        "no chip-bearing descriptor refused at (2,57). Either the chip S-box degree dropped (in \
         which case PROOF-ECONOMICS §2c's 'degree-7 chip needs blowup >= 6' clause is stale and \
         the whole lb=2 question reopens) or no case in this grid pulls in the chip table."
    );
    println!(
        "\n⚑ (2,57) is NOT A POINT for these chip-bearing descriptors: {chip_refusals:?}\n  \
         The Poseidon2 chip carries the INLINE degree-7 x^7 S-box; a blowup of 4 cannot carry its \
         quotient. `log_blowup` is therefore NOT a free global knob — it is floored, \
         per-descriptor, by the highest-degree table that descriptor's constraint list pulls in."
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// §1b — THE WHOLE REGISTRY, under the predictor calibrated in §1.
// ─────────────────────────────────────────────────────────────────────────────

/// The no-intercept two-regressor fit from §1's measured set:
/// `per-query bytes ≈ 8.623 · W_committed_main + 43.613 · n_range_lookups`.
/// A per-query cost must vanish as the committed columns vanish, so the fit carries no intercept.
/// §1 re-derives these from the run's own measurements and reports the drift; they are frozen here
/// so §1b can price the descriptors §1 cannot prove.
const P_PER_COLUMN: f64 = 8.623;
const P_PER_RANGE_LOOKUP: f64 = 43.613;
/// Measured worst per-descriptor error of that fit on the §1 set (2026-08-04, release, this box).
/// Quoted with every §1b number so no reader takes a predicted byte count for a measured one.
const P_FIT_WORST_ERR_PCT: f64 = 63.0;

/// ⚑ **THE OTHER 83 DESCRIPTORS.** For every by-name golden: is `(2,57)` even a POINT for it
/// (does its constraint list pull in the degree-7 Poseidon2 chip?), and if so what does the
/// blowup drop cost it on the wire? The chip column is STRUCTURAL and exact — it is read off the
/// same constraint list `Presence::of` reads. The byte column is PREDICTED and carries its
/// calibration error.
#[test]
fn the_whole_registry_priced_under_the_calibrated_predictor() {
    let dir = concat!(env!("CARGO_MANIFEST_DIR"), "/descriptors/by-name");
    let mut files: Vec<_> = std::fs::read_dir(dir)
        .expect("the by-name descriptor directory exists")
        .map(|e| e.expect("dir entry").path())
        .filter(|p| p.extension().is_some_and(|x| x == "json"))
        .collect();
    files.sort();
    assert!(
        files.len() >= 80,
        "the by-name registry has {} goldens; this census is supposed to cover the whole thing",
        files.len()
    );

    println!(
        "\n═══ §1b  THE WHOLE BY-NAME REGISTRY ({} goldens) ═══",
        files.len()
    );
    println!(
        "predicted Δbytes(6,19 → 2,57) = 38 · ({P_PER_COLUMN} · W_committed + \
         {P_PER_RANGE_LOOKUP} · n_range_lookups), calibrated in §1, worst measured error \
         ±{P_FIT_WORST_ERR_PCT:.0}%"
    );
    println!(
        "\n{:<58}{:>7}{:>9}{:>7}{:>6}{:>14}",
        "descriptor", "declrd", "committed", "rng lk", "chip", "pred Δbytes"
    );

    let mut chip_bearing = 0usize;
    let mut unparsed: Vec<String> = Vec::new();
    let mut total_pred = 0f64;
    let mut rows: Vec<(String, usize, usize, usize, bool, f64)> = Vec::new();
    for path in &files {
        let text = std::fs::read_to_string(path).expect("golden reads");
        let name = path
            .file_stem()
            .expect("stem")
            .to_string_lossy()
            .to_string();
        // Strict first; the oversized-constant goldens (the windowed RCB family) only parse
        // through the widened checker, and refusing to census them would hide the widest rows.
        let Ok(desc) =
            parse_vm_descriptor2(&text).or_else(|_| parse_vm_descriptor2_unsound_oversized(&text))
        else {
            unparsed.push(name);
            continue;
        };
        let (declared, committed, nlk) = committed_main_width(&desc);
        let chip = has_chip_lookup(&desc);
        if chip {
            chip_bearing += 1;
        }
        let pred = 38.0 * (P_PER_COLUMN * committed as f64 + P_PER_RANGE_LOOKUP * nlk as f64);
        if !chip {
            total_pred += pred;
        }
        rows.push((name, declared, committed, nlk, chip, pred));
    }
    // Widest first — the descriptors the global knob costs the most.
    rows.sort_by(|a, b| b.5.partial_cmp(&a.5).expect("finite"));
    for (name, declared, committed, nlk, chip, pred) in &rows {
        println!(
            "{name:<58}{declared:>7}{committed:>9}{nlk:>7}{:>6}{:>14}",
            if *chip { "YES" } else { "-" },
            if *chip {
                "n/a (refuses)".to_string()
            } else {
                format!("{:+.0}", pred)
            }
        );
    }
    if !unparsed.is_empty() {
        println!("\n⚠ goldens neither checker parsed (excluded from the census): {unparsed:?}");
    }
    println!(
        "\n{chip_bearing} of {} goldens pull in the Poseidon2 chip table, so (2,57) IS NOT A POINT \
         for them — a global lb=2 would not be a slower/bigger config for those descriptors, it \
         would be an UNPROVABLE one. Predicted total extra wire across the {} chip-FREE goldens: \
         {:.1} MiB per proof-set.",
        rows.len(),
        rows.len() - chip_bearing,
        total_pred / (1024.0 * 1024.0)
    );

    assert!(
        chip_bearing > 0,
        "if no golden pulls in the chip table this whole census is measuring the wrong predicate"
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// §2 — ONE CASE, ONE POINT, ONE PROCESS (so `/usr/bin/time -l` can attribute PEAK RSS)
// ─────────────────────────────────────────────────────────────────────────────

/// Peak memory is the axis an in-process sweep CANNOT measure (the allocator retains the
/// high-water mark of every earlier rung). Driven by `DREGG_FRI_ONE_CASE=<label>` +
/// `DREGG_FRI_ONE=<lb>,<q>`; skipped when unset.
#[test]
fn one_case_one_point_per_process() {
    let (Ok(label), Ok(spec)) = (
        std::env::var("DREGG_FRI_ONE_CASE"),
        std::env::var("DREGG_FRI_ONE"),
    ) else {
        println!(
            "\n§2 skipped (set DREGG_FRI_ONE_CASE=<label> DREGG_FRI_ONE=<lb>,<q> and run under \
             /usr/bin/time -l)"
        );
        return;
    };
    let (lb, q) = spec
        .split_once(',')
        .map(|(a, b)| {
            (
                a.trim().parse::<usize>().expect("lb"),
                b.trim().parse::<usize>().expect("q"),
            )
        })
        .expect("DREGG_FRI_ONE=lb,q");
    let all = cases();
    let case = all.iter().find(|c| c.label == label).unwrap_or_else(|| {
        panic!("no case labelled {label:?}; have {:?}", {
            all.iter().map(|c| c.label).collect::<Vec<_>>()
        })
    });
    let (_, committed, _) = committed_main_width(&case.desc);
    let cfg = config_at(lb, q);
    let t0 = std::time::Instant::now();
    let proof = prove_vm_descriptor2_with_config(
        &case.desc,
        &case.trace,
        &case.pis,
        &MemBoundaryWitness::default(),
        &[],
        &cfg,
    )
    .unwrap_or_else(|e| panic!("{label} at (lb {lb}, q {q}) must prove: {e}"));
    let prove_ms = t0.elapsed().as_secs_f64() * 1000.0;
    let t1 = std::time::Instant::now();
    verify_vm_descriptor2_with_config(&case.desc, &proof, &case.pis, &cfg).expect("verifies");
    let verify_ms = t1.elapsed().as_secs_f64() * 1000.0;
    let bytes = postcard::to_allocvec(&proof).expect("serialize").len();
    println!(
        "\n§2  {label}  lb={lb} q={q}  rows={} committed={committed} tables={}  \
         prove {prove_ms:.1} ms  verify {verify_ms:.2} ms  proof {bytes} B  \
         (peak RSS from /usr/bin/time -l)",
        case.trace.len(),
        proof.degree_bits.len(),
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// §3 — THE ROW CEILING. BabyBear two-adicity is 27, so `log_rows ≤ 27 − log_blowup`.
// ─────────────────────────────────────────────────────────────────────────────

/// ⚑ **THE CEILING IS A `assert!` IN A FIELD, NOT A REFUSAL IN A PROVER.** The whole enforcement
/// chain, read at HEAD:
///
///   1. `p3_baby_bear::BabyBear::TWO_ADICITY = 27` (`baby-bear/src/baby_bear.rs:42`).
///   2. `MontyField31::two_adic_generator(bits)` — `assert!(bits <= Self::TWO_ADICITY)`
///      (`monty-31/src/monty_31.rs:681`). A bare assert; the panic it raises, EXHIBITED below, is
///      `monty_31.rs:681:9: assertion failed: bits <= Self::TWO_ADICITY`.
///   3. `TwoAdicMultiplicativeCoset::new(shift, log_size)` returns **`None`** when
///      `log_size > F::TWO_ADICITY` (`field/src/coset.rs:77-79`), and the PCS's
///      `natural_domain_for_degree` `.unwrap()`s it (`vendor/plonky3-fri-82cfad73/src/two_adic_pcs.rs:377`)
///      — so a TRACE taller than `2^27` panics on the unwrap, before any blowup is applied.
///   4. The LDE is where the blowup enters: `Radix2DitParallel::coset_lde_batch_with_transform`
///      computes `F::two_adic_generator(log_h + added_bits)` at
///      `dft/src/radix_2_dit_parallel.rs:218` — i.e. the real ceiling is `log_h + log_blowup ≤ 27`,
///      giving **2^21 rows at lb=6 and 2^25 rows at lb=2**.
///
/// ⚑ **AND THE ORDERING IS WRONG.** Line 216 is `mat.values.reserve_exact(elems_to_add)` — the
/// FULL LDE buffer is reserved BEFORE line 218's assert. So a trace that crosses the two-adicity
/// ceiling asks the allocator for `W · 2^28 · 4` bytes first and dies of memory, never reaching the
/// check that names the real reason. There is no graceful refusal on this path at any blowup.
///
/// ⚑ **AND THE VERIFIER'S OWN SHAPE CHECK IS BLOWUP-BLIND.** `p3_batch_stark`'s verifier calls
/// `validate_degree_bits(.., pcs.log_max_lde_height())` (`batch-stark/src/verifier/mod.rs:97-101`),
/// and `TwoAdicFriPcs::log_max_lde_height()` returns `Val::TWO_ADICITY` = **27 flat**
/// (`vendor/plonky3-fri-82cfad73/src/two_adic_pcs.rs:380-382`), with no `− log_blowup`. So
/// `InvalidProofShapeError::DegreeBitsTooLarge` fires at `degree_bits > 27` regardless of the
/// configured blowup: the verifier's stated bound is 6 bits looser than the prover's real one at
/// `lb = 6`, and 2 bits looser at `lb = 2`.
///
/// This test EXHIBITS steps 1–3 directly (they are cheap and exact — the same calls the prover
/// makes) and states 4 with its file:line, because reaching 4 through the prover requires the
/// multi-hundred-gigabyte allocation that precedes it.
#[test]
fn the_row_ceiling_is_two_adicity_minus_log_blowup() {
    use p3_baby_bear::BabyBear as P3BabyBear;
    use p3_field::{PrimeCharacteristicRing, TwoAdicField, coset::TwoAdicMultiplicativeCoset};

    assert_eq!(
        P3BabyBear::TWO_ADICITY,
        27,
        "the ceiling every row below is derived from"
    );

    // The exact value `natural_domain_for_degree` unwraps.
    assert!(
        TwoAdicMultiplicativeCoset::new(P3BabyBear::ONE, 27).is_some(),
        "a 2^27 domain is inside the two-adic subgroup"
    );
    assert!(
        TwoAdicMultiplicativeCoset::new(P3BabyBear::ONE, 28).is_none(),
        "a 2^28 domain is NOT constructible; the PCS `.unwrap()`s this `None`"
    );

    // The exact assert the LDE hits at `log_h + log_blowup`.
    let panicked = std::panic::catch_unwind(|| {
        let _ = P3BabyBear::two_adic_generator(28);
    })
    .is_err();
    assert!(
        panicked,
        "`two_adic_generator(28)` must panic — it is the call `coset_lde_batch` makes at \
         `log_h + added_bits`, and it is the ONLY thing standing between a too-tall trace and a \
         silently wrong LDE"
    );
    // …and it is fine at exactly the ceiling, so the assertion above is about 28 and not about
    // `catch_unwind` swallowing something else.
    let _ = P3BabyBear::two_adic_generator(27);

    // The row ceiling each shipped parity point implies, printed so the trade is legible.
    println!("\n═══ §3  THE ROW CEILING (BabyBear two-adicity = 27) ═══");
    println!(
        "{:>3}{:>5}{:>14}{:>18}{:>22}",
        "lb", "q", "max log_rows", "max rows", "LDE bytes/col @ max"
    );
    for &(lb, q) in PARITY {
        let max_log = 27 - lb;
        println!(
            "{lb:>3}{q:>5}{max_log:>14}{:>18}{:>22}",
            1u64 << max_log,
            (1u64 << 27) * 4,
        );
    }
    println!(
        "\nthe LDE is 2^27 field elements per column at EVERY rung (that is what the ceiling \
         means), so the memory cost of the ceiling is identical — what differs is how many TRACE \
         rows fit under it: 2^21 at lb=6, 2^25 at lb=2, a 16x difference in reachable trace height."
    );
}
