//! The provably-independent, provably-sourced AI analyst swarm — a runnable demo.
//!
//!   cargo run --manifest-path confined-swarm/Cargo.toml --example research_swarm
//!
//! One primed confined root forks into N sovereign workers; each is jailed to ONE data
//! source, drives its (modeled) research brain against it, and attaches a zkOracle
//! attestation proving what it read. Then `verify` confirms the killer property: the N
//! reports are provably independent (umem fork isolation — no worker's mind ever touched
//! another's) and provably sourced (each attested to its one source), on a conserved budget.

use confined_swarm::{RecordedBrain, Source, Swarm, SwarmAttestationCarrier};

fn main() {
    let brief = "assess the safety posture of frontier agent deployments";

    // N distinct sources — each a different egress door, each different authentic content.
    let sources = vec![
        Source::new(
            "arxiv",
            "export.arxiv.org:443",
            b"Title: Confinement bounds for agent swarms\nAbstract: sovereign umem forks ..."
                .to_vec(),
        ),
        Source::new(
            "pubmed",
            "eutils.ncbi.nlm.nih.gov:443",
            b"Record: agent-in-the-loop clinical triage\nSummary: n=412 encounters ...".to_vec(),
        ),
        Source::new(
            "sec-edgar",
            "www.sec.gov:443",
            b"Filing 10-K: risk factors include model-driven automation exposure ...".to_vec(),
        ),
    ];
    let n = sources.len();

    let carrier = SwarmAttestationCarrier::default();
    let swarm = Swarm::assemble(brief, sources, 1_000_000, 100_000, &RecordedBrain, &carrier)
        .expect("assemble the swarm");

    println!("== confined research swarm ==");
    println!("brief: {}", swarm.brief());
    println!(
        "one primed root -> {n} sovereign workers (root budget {})\n",
        swarm.root_budget()
    );

    for w in swarm.workers() {
        let attested = w
            .attestation
            .as_ref()
            .map(|att| dregg_zkoracle_prove::verify_zkoracle(att, carrier.config()).is_ok())
            .unwrap_or(false);
        let doors: Vec<&str> = w.session.confinement().doors().collect();
        println!("worker {} [{}]", w.index, w.source.name);
        println!("  jailed to  : {doors:?}  (exactly one door)");
        println!("  budget     : {}", w.budget());
        println!("  attested   : {attested}");
        println!("  report     : {}", w.report);
        println!();
    }

    let v = swarm.verify(&carrier);
    println!("== verdict ==");
    println!("  (a) all reports attested        : {}", v.all_attested);
    println!(
        "  (b) each jailed to one source   : {}",
        v.each_jailed_to_one_source
    );
    println!("  (c) non-colluding (isolation)   : {}", v.non_colluding);
    println!("      common ancestry (one root)  : {}", v.common_ancestry);
    println!(
        "  (d) budget conserved            : {}  ({} <= {})",
        v.budget_conserved, v.total_worker_budget, v.root_budget
    );
    println!(
        "  => ACCEPTED (provably-independent, provably-sourced): {}",
        v.accepted()
    );
    assert!(v.accepted());
}
