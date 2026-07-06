//! The provably-independent, provably-sourced AI analyst swarm — a runnable demo.
//!
//!   cargo run --manifest-path confined-swarm/Cargo.toml --example research_swarm
//!
//! One primed confined root forks into N=5 sovereign workers; each is jailed to ONE data
//! source, drives its (modeled) research brain against it, and attaches a zkOracle attestation
//! proving what it read. Then the demo makes the KILLER PROPERTY visceral:
//!
//!   * a per-worker report card (source, bytes read, digest, budget, attested);
//!   * the NON-COLLUSION PROOF MATRIX — every ordered cross-worker probe of "does worker i's
//!     mind carry worker j's source?" comes back empty (worker A's mind provably never touched
//!     B's — probed, not asserted);
//!   * the four-teeth verdict: attested ∧ jailed-to-one-source ∧ non-colluding ∧
//!     budget-conserved, on one primed root.

use confined_swarm::{RecordedBrain, Source, Swarm, SwarmAttestationCarrier};

fn main() {
    let brief = "assess the safety posture of frontier agent deployments";

    // N=5 distinct sources — each a different egress door, each different authentic content.
    let sources = vec![
        Source::new(
            "arxiv",
            "export.arxiv.org:443",
            b"Title: Confinement bounds for agent swarms\nAbstract: sovereign umem forks bound \
              cross-agent information flow; we prove an isolation lattice over checkpoints."
                .to_vec(),
        ),
        Source::new(
            "pubmed",
            "eutils.ncbi.nlm.nih.gov:443",
            b"Record: agent-in-the-loop clinical triage\nSummary: n=412 encounters; supervised \
              deferral reduced missed red-flags without raising over-referral."
                .to_vec(),
        ),
        Source::new(
            "sec-edgar",
            "www.sec.gov:443",
            b"Filing 10-K: risk factors include model-driven automation exposure and third-party \
              inference dependencies material to operations."
                .to_vec(),
        ),
        Source::new(
            "github",
            "api.github.com:443",
            b"Repo: frontier-evals/harness\nRelease notes: added jailbreak-resistance suite; \
              sandbox escape attempts logged and denied at the egress seam."
                .to_vec(),
        ),
        Source::new(
            "courtlistener",
            "www.courtlistener.com:443",
            b"Opinion: In re Automated Decision Systems\nHolding: an operator remains liable for \
              a deployed model's outputs absent a verifiable neutrality record."
                .to_vec(),
        ),
    ];
    let n = sources.len();

    let carrier = SwarmAttestationCarrier::default();
    // root 1_000_000; five workers @ 100_000 = 500_000 — split, well within the root.
    let swarm = Swarm::assemble(brief, sources, 1_000_000, 100_000, &RecordedBrain, &carrier)
        .expect("assemble the swarm");

    println!("== confined research swarm ==");
    println!("brief: {}", swarm.brief());
    println!(
        "one primed root -> {n} sovereign workers (root budget {}, split {} ways)\n",
        swarm.root_budget(),
        n
    );

    // ── Per-worker report cards (the structured, verifiable report objects). ──
    for card in swarm.report_cards(&carrier) {
        println!("worker {} [{}]", card.worker, card.source_name);
        println!("  jailed to  : {}  (exactly one door)", card.source_door);
        println!("  read       : {} bytes", card.bytes_read);
        println!("  digest     : {}", hex8(&card.source_digest));
        println!("  budget     : {}", card.budget_remaining);
        println!("  attested   : {}", card.attested);
        println!("  report     : {}", card.report);
        println!();
    }

    // ── The non-collusion property, MADE VISCERAL: the cross-contact probe matrix. ──
    // For every ordered pair (observer, subject) we PROBE observer's mind at subject's source
    // key. Every cell is empty (·) — no worker's mind ever carried another's source.
    println!("== non-collusion proof matrix ==");
    println!("cell [i][j] = does worker i's mind carry worker j's source?  (· = never touched)");
    let labels: Vec<String> = swarm
        .workers()
        .iter()
        .map(|w| short(&w.source.name))
        .collect();
    print!("        ");
    for l in &labels {
        print!("{l:>5}");
    }
    println!();
    let contacts = swarm.cross_contacts();
    for (i, w) in swarm.workers().iter().enumerate() {
        print!("  {:>5} ", short(&w.source.name));
        for j in 0..n {
            if i == j {
                print!("{:>5}", "self");
            } else {
                let cell = contacts
                    .iter()
                    .find(|c| c.observer == i && c.subject == j)
                    .expect("cross-contact cell present");
                print!(
                    "{:>5}",
                    if cell.recalled.is_none() {
                        "·"
                    } else {
                        "LEAK"
                    }
                );
            }
        }
        println!();
    }
    // A concrete, named probe drives the point home: worker 0's mind, asked for worker 1's
    // source, returns literally nothing.
    let a = &swarm.workers()[0];
    let b = &swarm.workers()[1];
    println!(
        "\nprobe: worker 0 [{}] mind.recall(source_key of worker 1 [{}]) = {:?}",
        a.source.name,
        b.source.name,
        a.session.recall(b.source_key())
    );
    println!(
        "  => worker 0's mind provably NEVER touched worker 1's source (fully_isolated = {})\n",
        swarm.fully_isolated()
    );

    // ── The four-teeth verdict. ──
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
    assert!(swarm.fully_isolated());
    println!(
        "\n{n} analysts, one root, provably non-colluding — a research swarm only the dregg \
         substrate can build."
    );
}

fn hex8(h: &[u8; 32]) -> String {
    h[..4].iter().map(|b| format!("{b:02x}")).collect()
}

/// A ≤4-char column label.
fn short(name: &str) -> String {
    name.chars().take(4).collect()
}
