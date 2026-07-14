//! # `pricecert_clear` — the DERIVATIVES DESK as a thin JSON CLI (the offerings wire)
//!
//! ```text
//! echo '<params-json>' | pricecert_clear
//! ```
//!
//! A sibling of `fhegg_clear` (the shielded ring-clearing CLI): this drives the
//! Price-Cert derivatives family (`fhegg_solver::pricecert`) as a JSON-in/JSON-out
//! offering the DreggFi menu can click. It runs the SAME library the
//! `pricecert-bench` benchmark exercises — `solve_price_cert` (European / basket /
//! Asian, the state-price LP) and `solve_snell_cert` (American / Bermudan, the
//! Snell-envelope LP) — and emits ONLY the world-visible certificate object: the
//! certified price / option value, the duality gap, every re-checked clause, and
//! the accept/reject polarity. Never the plaintext search, only the CHECKED cert.
//!
//! Input (stdin JSON; empty stdin ⇒ the default American-put demo):
//!   { "kind": "american", "spot":100, "strike":100, "rate":0.05, "vol":0.2,
//!     "expiry":1.0, "steps":256, "isPut":true }
//!   { "kind": "european", "scenarios":64, "instruments":16, "seed":48813 }
//!
//! Output (stdout, one JSON line): engine, mechanism, family member, the params
//! echoed, the certified value, the Price-Cert / Snell report (each Lean clause
//! recomputed from the witness), the certificate `valid` flag, the tier, and the
//! honest NEGATIVE polarity — an arbitrage market is REJECTED (no certificate),
//! a broken value vector fails superharmonicity. verify-not-find, in code.

use std::io::Read;

use fhegg_solver::pricecert::{
    american_put_binomial, solve_price_cert, solve_snell_cert, CertPrice, Market, PriceOutcome,
};

use serde::Deserialize;
use serde_json::json;

#[derive(Deserialize, Default)]
#[serde(default)]
struct Params {
    kind: Option<String>,
    // American / Bermudan (Snell) params.
    spot: Option<f64>,
    strike: Option<f64>,
    rate: Option<f64>,
    vol: Option<f64>,
    expiry: Option<f64>,
    steps: Option<usize>,
    #[serde(rename = "isPut")]
    is_put: Option<bool>,
    // European / basket / Asian (state-price) params.
    scenarios: Option<usize>,
    instruments: Option<usize>,
    seed: Option<u64>,
}

/// A deterministic, CONSISTENT (arbitrage-free) incomplete market — the same
/// construction the `pricecert-bench` uses: nonneg state prices `π*`, a nonneg
/// instrument grid `H`, marks `a = Hπ*` (consistency by construction), a random
/// product payoff `h`. Instrument 0 is a bond (pays 1 everywhere ⇒ Σπ=1).
fn gen_market(n_scenarios: usize, n_instruments: usize, seed: u64) -> Market {
    let mut st = seed.wrapping_mul(0x9E3779B97F4A7C15) | 1;
    let mut next = || {
        st ^= st << 13;
        st ^= st >> 7;
        st ^= st << 17;
        (st >> 11) as f64 / (1u64 << 53) as f64
    };
    let (s, j) = (n_scenarios, n_instruments);
    let mut h_mat = vec![0.0f64; j * s];
    for sc in 0..s {
        h_mat[sc] = 1.0; // instrument-0 (bond) row
    }
    for inst in 1..j {
        for sc in 0..s {
            h_mat[inst * s + sc] = next() * 2.0;
        }
    }
    let pi_star: Vec<f64> = {
        let raw: Vec<f64> = (0..s).map(|_| next()).collect();
        let sum: f64 = raw.iter().sum();
        raw.iter().map(|v| v / sum).collect()
    };
    let a: Vec<f64> = (0..j)
        .map(|inst| (0..s).map(|sc| h_mat[inst * s + sc] * pi_star[sc]).sum())
        .collect();
    let h: Vec<f64> = (0..s).map(|_| next() * 3.0).collect();
    Market {
        n_scenarios: s,
        n_instruments: j,
        h_mat,
        a,
        h,
        epsilon: 1e-6,
    }
}

fn european(p: &Params) -> serde_json::Value {
    let scenarios = p.scenarios.unwrap_or(64).clamp(2, 4096);
    let instruments = p.instruments.unwrap_or(16).clamp(1, scenarios);
    let seed = p.seed.unwrap_or(48813);
    let market = gen_market(scenarios, instruments, seed);

    // POSITIVE polarity: a consistent market ⇒ a tight (π, y) certificate.
    let (cert, report) = match solve_price_cert(&market) {
        PriceOutcome::Certified(c) => {
            let r = c.check();
            (Some(c), Some(r))
        }
        PriceOutcome::Arbitrage => (None, None),
    };

    // NEGATIVE polarity: perturb the bond mark so no consistent π≥0 exists ⇒ the
    // runner returns Arbitrage (no certificate) — the honest reject.
    let mut arb = gen_market(scenarios, instruments, seed);
    if !arb.a.is_empty() {
        arb.a[0] += 100.0; // Σπ must be ~1 (bond row) — an inflated bond mark is inconsistent.
    }
    let arb_rejected = matches!(solve_price_cert(&arb), PriceOutcome::Arbitrage);

    let cert: CertPrice = cert.expect("consistent market is certifiable by construction");
    let report = report.unwrap();
    json!({
        "engine": "fhEgg Price-Cert derivatives desk (fhegg-solver: state-price LP + Cert-F pricing)",
        "family": "European / basket / Asian",
        "mechanism": "max hᵀπ  s.t.  Hπ=a, π≥0  (two-phase simplex, untrusted search); superhedge y=−y' is the LP dual (yᵀH≥h)",
        "kind": "european",
        "params": { "scenarios": scenarios, "instruments": instruments, "seed": seed },
        "certifiedPrice": (cert.primal_price * 1e6).round() / 1e6,
        "superhedgeCost": (cert.dual_cost * 1e6).round() / 1e6,
        "dualityGap": (cert.gap * 1e6).round() / 1e6,
        "certificate": {
            "piNonneg": report.pi_nonneg,
            "consistent": report.consistent,
            "superhedge": report.superhedge,
            "gapOk": report.gap_ok,
            "consistencyResidual": report.consistency_residual,
            "hedgeShortfall": report.hedge_shortfall,
            "valid": report.valid,
        },
        "negativePolarity": {
            "what": "inflate the bond mark a[0] by 100 (Σπ can no longer equal 1 with π≥0 ⇒ arbitrage)",
            "rejected": arb_rejected,
        },
        "tier": "runs OPEN here — the plaintext certificate is shown + re-checked; per fhir the derivative_price_cert product's most-private ADMISSIBLE tier is DARK (small public state-price grid). The shielded STARK wrap is the cert_f_prove lane.",
        "verifyNotFind": "the certificate re-checks π≥0, Hπ=a, yᵀH≥h, gap≤ε from scratch — never trusts the simplex search",
        "lean": "metatheory/Market/PriceCert.lean :: price_cert_certifies",
    })
}

fn american(p: &Params) -> serde_json::Value {
    let spot = p.spot.unwrap_or(100.0);
    let strike = p.strike.unwrap_or(100.0);
    let rate = p.rate.unwrap_or(0.05);
    let vol = p.vol.unwrap_or(0.2);
    let expiry = p.expiry.unwrap_or(1.0);
    let steps = p.steps.unwrap_or(256).clamp(1, 4096);
    let is_put = p.is_put.unwrap_or(true);

    let tree = american_put_binomial(spot, strike, rate, vol, expiry, steps, is_put);
    let cert = solve_snell_cert(&tree, 1e-9);
    let report = cert.check();

    // NEGATIVE polarity: dent the root value below its continuation ⇒ the cert
    // must FAIL superharmonicity (a forged, too-cheap option value is caught).
    let mut forged = cert.clone();
    forged.v[forged.root] -= (spot.abs()).max(1.0);
    let forged_report = forged.check();

    json!({
        "engine": "fhEgg Price-Cert derivatives desk (fhegg-solver: Snell-envelope LP)",
        "family": "American / Bermudan",
        "mechanism": "backward induction on the recombining CRR tree = the exact Snell envelope; the cert checks V≥g (exercise-dominance) + V_n≥d·ΣPV_m (superharmonic) — LP feasibility",
        "kind": "american",
        "params": { "spot": spot, "strike": strike, "rate": rate, "vol": vol, "expiry": expiry, "steps": steps, "isPut": is_put },
        "certifiedValue": (cert.root_value * 1e6).round() / 1e6,
        "nodes": tree.n_nodes,
        "certificate": {
            "dominates": report.dominates,
            "superharmonic": report.superharmonic,
            "dominanceShortfall": report.dominance_shortfall,
            "superharmonicShortfall": report.superharmonic_shortfall,
            "valid": report.valid,
        },
        "negativePolarity": {
            "what": "subtract the spot from the root value V_root (below its continuation ⇒ not superharmonic)",
            "rejected": !forged_report.valid,
        },
        "tier": "runs OPEN here — the certified value + its feasibility proof are shown; per fhir the american_put_price_cert product's most-private ADMISSIBLE tier is SHIELDED (>64-node tree exceeds the Dark FHE envelope).",
        "verifyNotFind": "the certificate re-checks dominance + superharmonicity at every node — never trusts how V was found",
        "lean": "metatheory/Market/PriceCert.lean :: snell_feasible_upper_bound (per-step lemma proved; multi-layer composition = Lean's named residual)",
    })
}

fn main() {
    let mut buf = String::new();
    let _ = std::io::stdin().read_to_string(&mut buf);
    let params: Params = if buf.trim().is_empty() {
        Params::default()
    } else {
        match serde_json::from_str(&buf) {
            Ok(p) => p,
            Err(e) => {
                eprintln!("pricecert_clear: bad params JSON: {e}");
                std::process::exit(2);
            }
        }
    };

    let kind = params
        .kind
        .clone()
        .unwrap_or_else(|| "american".to_string());
    let out = match kind.as_str() {
        "european" | "basket" | "asian" => european(&params),
        "american" | "bermudan" => american(&params),
        other => {
            eprintln!("pricecert_clear: unknown kind '{other}' (want european|american)");
            std::process::exit(2);
        }
    };

    match serde_json::to_string(&out) {
        Ok(s) => println!("{s}"),
        Err(e) => {
            eprintln!("pricecert_clear: serialize failed: {e}");
            std::process::exit(1);
        }
    }
}
