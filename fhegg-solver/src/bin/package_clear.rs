//! # `package_clear` — the PACKAGE (COMBINATORIAL) AUCTION as a thin JSON CLI
//!
//! ```text
//! echo '<auction-json>' | package_clear
//! ```
//!
//! A sibling of `fhegg_clear` / `pricecert_clear`: this drives the all-or-none
//! package-clearing family (`fhegg_solver::package`) as a JSON-in/JSON-out
//! offering the DreggFi menu can click. It runs the SAME `clear_package` the
//! `package-bench` benchmark exercises — a certified-approximation combinatorial
//! clearing — and emits ONLY the world-visible object: the accept/reject
//! decisions, the achieved welfare, the CERTIFIED near-optimality bound `α = W/UB`,
//! and every re-checked clause (indivisibility, capacity, dual feasibility, the
//! weak-duality bound). The exact optimum stays NP-hard; the certificate is the
//! near-optimality WITNESS the buyer verifies.
//!
//! Input (stdin JSON; empty stdin ⇒ the built-in `sample_auction`, optimum 18):
//!   { "items":3, "supply":[1,1,1],
//!     "bids":[ {"value":6,"demand":[1,0,0]}, {"value":12,"demand":[1,1,0]}, ... ] }
//!   { "random": { "items":20, "bids":80, "seed":1 } }   // a deterministic sweep instance
//!
//! Output (stdout, one JSON line): engine, mechanism, the accept decisions, the
//! welfare, the certified upper bound + ratio, the CertPackage report (each clause
//! recomputed from the public program + witness), `valid`, and the tier.

use std::io::Read;

use fhegg_solver::package::{
    clear_package, random_auction, sample_auction, PackageAuction, PackageBid,
};

use serde::Deserialize;
use serde_json::json;

#[derive(Deserialize)]
struct BidIn {
    value: f64,
    demand: Vec<f64>,
}

#[derive(Deserialize)]
struct RandomIn {
    #[serde(default = "def_items")]
    items: usize,
    #[serde(default = "def_bids")]
    bids: usize,
    #[serde(default)]
    seed: u64,
}
fn def_items() -> usize {
    20
}
fn def_bids() -> usize {
    80
}

#[derive(Deserialize, Default)]
#[serde(default)]
struct AuctionIn {
    items: Option<usize>,
    supply: Option<Vec<f64>>,
    bids: Option<Vec<BidIn>>,
    random: Option<RandomIn>,
}

fn build_auction(input: &AuctionIn) -> (PackageAuction, &'static str) {
    if let Some(r) = &input.random {
        let items = r.items.clamp(1, 200);
        let bids = r.bids.clamp(1, 4000);
        return (random_auction(items, bids, r.seed), "random sweep instance");
    }
    match (&input.bids, &input.supply, input.items) {
        (Some(bids), Some(supply), Some(items)) if !bids.is_empty() && supply.len() == items => {
            let auction = PackageAuction {
                n_items: items,
                supply: supply.clone(),
                bids: bids
                    .iter()
                    .map(|b| PackageBid::new(b.value, b.demand.clone()))
                    .collect(),
            };
            (auction, "user-supplied auction")
        }
        _ => (sample_auction(), "built-in sample_auction (optimum 18)"),
    }
}

fn main() {
    let mut buf = String::new();
    let _ = std::io::stdin().read_to_string(&mut buf);
    let input: AuctionIn = if buf.trim().is_empty() {
        AuctionIn::default()
    } else {
        match serde_json::from_str(&buf) {
            Ok(a) => a,
            Err(e) => {
                eprintln!("package_clear: bad auction JSON: {e}");
                std::process::exit(2);
            }
        }
    };

    let (auction, source) = build_auction(&input);
    let (clearing, cert) = clear_package(&auction, 4000);
    let report = cert.check();

    // The accepted bundles (index + value + demand) for the UI to render.
    let accepted: Vec<serde_json::Value> = auction
        .bids
        .iter()
        .enumerate()
        .filter(|(i, _)| *clearing.accept.get(*i).unwrap_or(&0.0) > 0.5)
        .map(|(i, b)| json!({ "bid": i, "value": b.value, "demand": b.demand }))
        .collect();

    let out = json!({
        "engine": "fhEgg package auction (fhegg-solver: certified-approximation all-or-none clearing)",
        "mechanism": "max Σ v_i x_i  s.t.  Σ d_ij x_i ≤ s_j, x∈{0,1}  (indivisible bundles); dual prices y≥0 give the certified bound UB(y)=Σ s_j y_j + Σ (v_i − d_i·y)₊",
        "kind": "package",
        "source": source,
        "items": auction.n_items,
        "bidCount": auction.n_bids(),
        "supply": auction.supply.clone(),
        "accepted": accepted,
        "welfare": (clearing.welfare * 1e6).round() / 1e6,
        "upperBound": (clearing.upper_bound * 1e6).round() / 1e6,
        "certifiedRatio": (report.ratio * 1e6).round() / 1e6,
        "prices": clearing.prices.iter().map(|p| (p * 1e6).round() / 1e6).collect::<Vec<_>>(),
        "certificate": {
            "integral": report.integral,
            "capacityOk": report.capacity_ok,
            "pricesNonneg": report.prices_nonneg,
            "boundSound": report.bound_sound,
            "welfare": report.welfare,
            "upperBound": report.upper_bound,
            "ratio": report.ratio,
            "valid": report.valid,
        },
        "tier": "runs OPEN here — public bundles + verified clearing shown (feasibility ALWAYS proven; near-optimality is a CERTIFIED bound α=W/UB; exact optimum stays NP-hard). Per fhir the package_auction_clearing product's most-private ADMISSIBLE tier is SHIELDED (discrete, certified-approx).",
        "verifyNotFind": "CertPackage::check recomputes integrality (x∈{0,1}), capacity (Σd·x≤s), y≥0, and W≤UB from scratch — the buyer never trusts the solver's search",
        "lean": "metatheory/Market/Package.lean (weak-duality bound); feasibility is the all-or-none analogue of Cert-F",
    });

    match serde_json::to_string(&out) {
        Ok(s) => println!("{s}"),
        Err(e) => {
            eprintln!("package_clear: serialize failed: {e}");
            std::process::exit(1);
        }
    }
}
