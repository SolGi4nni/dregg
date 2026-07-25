//! # `fhegg_clear` — the fhEgg single-phase SHIELDED clearing as a thin JSON CLI (the web wire)
//!
//! ```text
//! echo '<orders-json>' | fhegg_clear
//! ```
//!
//! This is the fhEgg engine's **single-phase clearing** driven by the SAME revealed DrEX orders
//! `drex_clear` reads, but cleared through the CONVEX / CERTIFICATE route rather than the TTC ring
//! matcher:
//!
//!   1. map the batch to a trade-circulation LP: nodes = assets, one capacitated weighted edge per
//!      order `(offerAsset → wantAsset)`, `cap = offerAmount`, `weight = priority` — a member of the
//!      fhEgg convex-clearing family (`fhegg_solver::pdhg`, the volume-max circulation `max wᵀf s.t.
//!      Af=0, 0≤f≤c`);
//!   2. **fast UNTRUSTED search**: `solve_cpu` (PDHG) → `restore_feasibility` — the solver sees the
//!      plaintext batch and clears it MAXIMALLY FAST;
//!   3. emit the **Cert-F primal-dual certificate** `(f, π, s)` (`fhegg_solver::cert::CertF`) — the
//!      LINEAR witness that makes the untrusted solve trustworthy;
//!   4. emit + EVALUATE the Cert-F **AIR** (`fhegg_solver::air::ConstraintSystem` — the exact
//!      `n+4m+1` rows the Lean-verified `Market/CertF.lean` proves sound): the honest certificate is
//!      ACCEPTED; a tampered one (broken conservation) is REJECTED. This is the VERIFIED checker —
//!      the fair-batch gate, in code.
//!
//! Output (stdout): the cleared batch — per-order cleared flow read off the certified circulation,
//! the Cert-F report (cleared weighted volume `wᵀf`, dual `cᵀs`, duality gap, conservation residual,
//! every check), the AIR accept + the tamper reject, and the two clearing tiers (solver-sees vs
//! world-sees-only-the-proof).
//!
//! ## The accuracy budget `ε` — derived or declared, never a literal
//!
//! `gap ≤ ε` is the ε-optimality clause of Cert-F, so `ε` decides what the certificate
//! actually claims. This binary DERIVES it from the program (a fraction of the public
//! bound `Σ_e w_e·c_e ≥ wᵀf`, so the budget moves with the batch), or takes it DECLARED
//! as the prescriptive integer ε of a registered Lean-emitted program at that
//! registration's fixed-point scale:
//!
//! ```text
//! {"orders": [...], "accuracy": {"scale": 100, "integerEpsilon": 2000}}
//! {"orders": [...], "accuracy": {"relative": 0.005}}
//! [...]                                    # bare array: the derived default
//! ```
//!
//! The declared form is the one that makes the STARK wrap reachable: the certificate is
//! then claimed against exactly the budget the registration grants, instead of against a
//! number this binary invented. The output's `accuracy` block reports `ε`, its derivation,
//! the achieved gap, and whether the solve landed inside the budget.
//!
//! ## The single-phase SHIELDED boundary — what is REAL here and what is NAMED
//!
//! Everything above is REAL and runs in this binary: the fair-batch clearing, the Cert-F certificate,
//! and the verified AIR accept/reject (the fairness/soundness gate). What this binary does NOT run is
//! the STARK-ZK wrap that HIDES `(f, π, s)` so the world sees only the proof — that is
//! `circuit-prove/src/cert_f_air.rs::{resolve_registered_scaling, from_solution_json_registered,
//! prove_cert_f, verify_cert_f}`, driven by the `cert_f_prove` binary (a dregg BabyBear+FRI proof
//! over this SAME AIR; the reveal-nothing floor rests on its zero-knowledge). This CLI emits the
//! exact `(f, π, s)` + public `(A, w, c)` that bridge ingests under `solverCert`.
//!
//! That wrap now FIRES for a live batch whose public program is the fixed-point preimage of a
//! REGISTERED Lean-emitted Cert-F program: the batch resolves itself to its registration, and the
//! scale and ε budget are read off the Lean artifact rather than guessed by an operator. A batch of
//! any other shape is refused, naming the Lean artifact it is missing. Shown honestly: in THIS
//! binary the certificate is in the clear, and this binary does not decide admissibility.

use std::io::Read;

use fhegg_solver::air::ConstraintSystem;
use fhegg_solver::book::{map_book, weighted_capacity_bound, AccuracyBudget, BookOrder};
use fhegg_solver::cert::CertF;
use fhegg_solver::pdhg::{restore_feasibility, solve_cpu};

use serde::{Deserialize, Serialize};

/// The batch as posted. Historically a bare array of orders; a batch may now also declare
/// the ACCURACY BUDGET its certificate is claimed against (see [`AccuracyIn`]).
#[derive(Deserialize)]
#[serde(untagged)]
enum BatchIn {
    Bare(Vec<BookOrder>),
    Declared {
        orders: Vec<BookOrder>,
        #[serde(default)]
        accuracy: Option<AccuracyIn>,
    },
}

/// A DECLARED accuracy budget. Either the prescriptive integer `epsilon` of a registered
/// Lean-emitted Cert-F program at its fixed-point `scale` (the form that makes the STARK
/// wrap reachable — the certificate is then claimed against exactly the budget the
/// registration grants), or a `relative` fraction of the program's own weighted-capacity
/// bound. Absent, the relative form is derived at [`AccuracyBudget::DEFAULT_RELATIVE`].
#[derive(Deserialize)]
struct AccuracyIn {
    scale: Option<i64>,
    #[serde(rename = "integerEpsilon")]
    integer_epsilon: Option<i64>,
    relative: Option<f64>,
}

impl AccuracyIn {
    fn budget(&self) -> Result<AccuracyBudget, String> {
        match (self.scale, self.integer_epsilon, self.relative) {
            (Some(scale), Some(integer_epsilon), None) => {
                if scale < 1 {
                    return Err(format!("accuracy.scale must be >= 1, got {scale}"));
                }
                if integer_epsilon < 0 {
                    return Err(format!(
                        "accuracy.integerEpsilon must be >= 0, got {integer_epsilon}"
                    ));
                }
                Ok(AccuracyBudget::Registered {
                    scale,
                    integer_epsilon,
                })
            }
            (None, None, Some(relative)) => {
                if !(relative.is_finite() && relative >= 0.0) {
                    return Err(format!(
                        "accuracy.relative must be a finite non-negative fraction, got {relative}"
                    ));
                }
                Ok(AccuracyBudget::RelativeToWeightedCapacity { relative })
            }
            _ => Err(
                "accuracy must declare EITHER {scale, integerEpsilon} (a registered \
                      Lean-emitted program's prescriptive budget) OR {relative} (a fraction \
                      of the program's own weighted-capacity bound) — never a mix, and never \
                      a bare literal"
                    .to_string(),
            ),
        }
    }
}

/// The accuracy budget as it appears in the output: what `ε` is, and where it came from.
/// A relying party must be able to see whether the certificate's ε-optimality claim rests
/// on a registration or on a batch-relative derivation.
#[derive(Serialize)]
struct AccuracyOut {
    epsilon: f64,
    /// `Σ_e w_e·c_e` — the public upper bound on `wᵀf` the relative form is a fraction of.
    #[serde(rename = "weightedCapacityBound")]
    weighted_capacity_bound: f64,
    /// The achieved gap `cᵀs − wᵀf` this solve actually reached.
    #[serde(rename = "achievedGap")]
    achieved_gap: f64,
    /// How `epsilon` was obtained — "derived: …" or "declared: …". Never a literal.
    derivation: String,
    /// Whether the achieved gap is inside the budget the certificate is claimed against.
    #[serde(rename = "withinBudget")]
    within_budget: bool,
}

#[derive(Serialize)]
struct ClearedOrder {
    trader: String,
    #[serde(rename = "offerAsset")]
    offer_asset: String,
    #[serde(rename = "offerAmount")]
    offer_amount: u64,
    #[serde(rename = "wantAsset")]
    want_asset: String,
    #[serde(rename = "wantMin")]
    want_min: u64,
    priority: u64,
    /// The cleared quantity of this order read off the certified circulation `f`.
    #[serde(rename = "clearedFlow")]
    cleared_flow: f64,
    /// Cleared / rested (a rested order got ~0 flow — no ring closed through it).
    filled: bool,
}

#[derive(Serialize)]
struct CertReportOut {
    /// Cleared weighted volume `wᵀf` (the fair-batch objective).
    #[serde(rename = "clearedVolume")]
    cleared_volume: f64,
    /// Dual objective `cᵀs`.
    #[serde(rename = "dualObjective")]
    dual_objective: f64,
    /// Duality gap `cᵀs − wᵀf` (optimality slack).
    #[serde(rename = "dualityGap")]
    duality_gap: f64,
    /// Conservation residual `‖Af‖_∞` (per-asset supply preserved).
    #[serde(rename = "conservationResidual")]
    conservation_residual: f64,
    conserves: bool,
    #[serde(rename = "primalBoxed")]
    primal_boxed: bool,
    #[serde(rename = "sNonneg")]
    s_nonneg: bool,
    #[serde(rename = "dualFeasible")]
    dual_feasible: bool,
    #[serde(rename = "gapOk")]
    gap_ok: bool,
    valid: bool,
}

#[derive(Serialize)]
struct AirOut {
    constraints: usize,
    terms: usize,
    #[serde(rename = "witnessCells")]
    witness_cells: usize,
    accept: bool,
    violated: Vec<String>,
}

#[derive(Serialize)]
struct TamperOut {
    what: String,
    accept: bool,
    violated: Vec<String>,
}

#[derive(Serialize)]
struct StarkStage {
    status: String,
    #[serde(rename = "revealNothingFloor")]
    reveal_nothing_floor: String,
    #[serde(rename = "wireEntryPoint")]
    wire_entry_point: String,
    hides: Vec<String>,
}

#[derive(Serialize)]
struct Tier {
    tier: String,
    sees: String,
}

#[derive(Serialize)]
struct Cleared {
    engine: String,
    mechanism: String,
    assets: Vec<String>,
    nodes: usize,
    edges: usize,
    iters: usize,
    orders: Vec<ClearedOrder>,
    accuracy: AccuracyOut,
    certificate: CertReportOut,
    air: AirOut,
    tamper: TamperOut,
    #[serde(rename = "starkStage")]
    stark_stage: StarkStage,
    tiers: Vec<Tier>,
    /// The RAW Cert-F certificate `(n_nodes, edges, w, c, f, π, s, ε)` — the exact f64 wire
    /// shape `circuit-prove/src/cert_f_air.rs::from_solution_json` ingests. This is the
    /// SOLVER's plaintext view; it carries the private witness `(f, π, s)`, so it is the
    /// bridge input to the reveal-nothing STARK (`cert_f_prove`) and must NOT be forwarded
    /// to the world — the STARK's public output replaces it. `serve.mjs` holds it server-side
    /// and pipes it to the prover; the world sees only the resulting proof + public inputs.
    #[serde(rename = "solverCert")]
    solver_cert: CertF,
}

fn main() {
    let mut buf = String::new();
    if std::io::stdin().read_to_string(&mut buf).is_err() {
        eprintln!("fhegg_clear: failed to read stdin");
        std::process::exit(2);
    }
    let batch: BatchIn = match serde_json::from_str(&buf) {
        Ok(o) => o,
        Err(e) => {
            eprintln!("fhegg_clear: bad batch JSON: {e}");
            std::process::exit(2);
        }
    };
    let (orders, declared) = match batch {
        BatchIn::Bare(orders) => (orders, None),
        BatchIn::Declared { orders, accuracy } => (orders, accuracy),
    };
    if orders.is_empty() {
        eprintln!("fhegg_clear: empty batch");
        std::process::exit(2);
    }
    // The accuracy budget the certificate will be claimed against: DECLARED by the batch
    // (a registered Lean-emitted program's prescriptive epsilon at its fixed-point scale,
    // or an explicit relative fraction), else DERIVED from the program itself. Never a
    // literal — a bare number is a tolerance of nothing.
    let budget = match declared.as_ref().map(AccuracyIn::budget) {
        Some(Ok(b)) => b,
        Some(Err(e)) => {
            eprintln!("fhegg_clear: bad accuracy declaration: {e}");
            std::process::exit(2);
        }
        None => AccuracyBudget::derived_default(),
    };

    // ---- [1] map the batch to the trade-circulation LP (assets = nodes, orders = edges). ----
    // ONE derivation, shared with the STARK bridge (`fhegg_solver::book::map_book`), so the
    // certificate is about the same public program the prover resolves against.
    let program = map_book(&orders);
    let assets = program.assets;
    let lp = program.lp;

    // ---- [2] fast UNTRUSTED search: PDHG → exact-feasibility restore. ----
    let iters = 4000usize;
    let approx = solve_cpu(&lp, iters);
    let (f_exact, _box_viol) = restore_feasibility(&lp, approx.f.clone());

    // ---- [3] the Cert-F primal-dual certificate (f, π, s) + public (A, w, c). ----
    let epsilon = budget.epsilon_for(&lp);
    let cert = CertF::from_solution(&lp, &f_exact, &approx.y, epsilon);
    let report = cert.check_strict();

    // ---- [4] emit + evaluate the Cert-F AIR (the verified fair-batch gate). ----
    let tol = 1e-7;
    let sys = ConstraintSystem::emit(&cert);
    let air_report = sys.evaluate(&cert, tol);
    let n_terms: usize = sys.constraints.iter().map(|cx| cx.terms.len()).sum();

    // Negative polarity: break conservation on one edge — the AIR must REJECT.
    let mut tampered = cert.clone();
    if !tampered.f.is_empty() {
        tampered.f[0] += 3.0;
    }
    let tamper_report = sys.evaluate(&tampered, tol);

    // Per-order cleared flow (rested if ~0).
    let cleared_orders: Vec<ClearedOrder> = orders
        .iter()
        .enumerate()
        .map(|(e, o)| {
            let flow = *f_exact.get(e).unwrap_or(&0.0);
            ClearedOrder {
                trader: o.trader.clone(),
                offer_asset: o.offer_asset.clone(),
                offer_amount: o.offer_amount,
                want_asset: o.want_asset.clone(),
                want_min: o.want_min,
                priority: if o.priority == 0 { 1 } else { o.priority },
                cleared_flow: (flow * 1e6).round() / 1e6,
                filled: flow > 1e-6,
            }
        })
        .collect();

    let out = Cleared {
        engine: "fhEgg single-phase clearing (fhegg-solver: PDHG circulation + Cert-F)".to_string(),
        mechanism: "volume-max trade circulation  max wᵀf  s.t. Af=0, 0≤f≤c  (the convex clearing family; uniform-price is its linear-utility floor)".to_string(),
        assets: assets.clone(),
        nodes: lp.n_nodes,
        edges: lp.m(),
        iters,
        orders: cleared_orders,
        accuracy: AccuracyOut {
            epsilon,
            weighted_capacity_bound: weighted_capacity_bound(&lp),
            achieved_gap: report.gap,
            derivation: budget.derivation(&lp),
            within_budget: report.gap_ok,
        },
        certificate: CertReportOut {
            cleared_volume: (cert.primal_obj * 1e6).round() / 1e6,
            dual_objective: (cert.dual_obj * 1e6).round() / 1e6,
            duality_gap: (cert.duality_gap * 1e6).round() / 1e6,
            conservation_residual: cert.feas_residual,
            conserves: report.conserves,
            primal_boxed: report.primal_boxed,
            s_nonneg: report.s_nonneg,
            dual_feasible: report.dual_feasible,
            gap_ok: report.gap_ok,
            valid: report.valid,
        },
        air: AirOut {
            constraints: sys.constraints.len(),
            terms: n_terms,
            witness_cells: sys.n_vars,
            accept: air_report.satisfied(),
            violated: air_report
                .violated
                .iter()
                .map(|(l, _)| l.to_string())
                .collect(),
        },
        tamper: TamperOut {
            what: "break conservation: add 3 units to edge 0 with no return leg (Af≠0)".to_string(),
            accept: tamper_report.satisfied(),
            violated: tamper_report
                .violated
                .iter()
                .map(|(l, _)| l.to_string())
                .collect(),
        },
        stark_stage: StarkStage {
            status: "NOT run in this binary — `cert_f_prove` runs it, and it ADMITS this batch only if the batch's fixed-point image is a REGISTERED Lean-emitted Cert-F program. This binary does not and must not decide admissibility.".to_string(),
            reveal_nothing_floor:
                "the world sees only a STARK over this SAME AIR; the reveal-nothing floor rests on its zero-knowledge"
                    .to_string(),
            wire_entry_point:
                "circuit-prove/src/cert_f_air.rs::{resolve_registered_scaling → from_solution_json_registered → prove_cert_f → verify_cert_f}"
                    .to_string(),
            hides: vec![
                "f (the primal flow — who cleared how much)".to_string(),
                "π (the node potentials / dual prices)".to_string(),
                "s (the dual slacks)".to_string(),
            ],
        },
        tiers: vec![
            Tier {
                tier: "solver-sees (Stage-1, untrusted)".to_string(),
                sees: "the plaintext batch — every order, to clear it maximally fast".to_string(),
            },
            Tier {
                tier: "world-sees (the shielded output)".to_string(),
                sees: "only the proof: a fair batch cleared, per-asset conservation held — never who traded what (once the STARK stage is wired)".to_string(),
            },
        ],
        solver_cert: cert,
    };

    match serde_json::to_string(&out) {
        Ok(s) => println!("{s}"),
        Err(e) => {
            eprintln!("fhegg_clear: serialize failed: {e}");
            std::process::exit(1);
        }
    }
}
