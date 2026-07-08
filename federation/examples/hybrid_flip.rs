//! FLIP THE HYBRID QUORUM ON — a live demonstration.
//!
//! Brings up a federation with `HybridPq` ACTIVE (every validator holds an
//! ed25519 AND an ML-DSA-65 key), runs consensus rounds, and shows each block
//! finalizing under a HYBRID quorum certificate — `classical ∧ pq`, both halves
//! verified. A quantum computer that breaks ed25519 still cannot forge finality,
//! because the lattice-based ML-DSA-65 half holds.
//!
//! Run: `cargo run -p dregg-federation --example hybrid_flip`

use dregg_federation::MorpheusFederation;

fn main() {
    println!("╔════════════════════════════════════════════════════════════════╗");
    println!("║  FLIPPING HybridPq ON  —  quantum-safe federation finality      ║");
    println!("╚════════════════════════════════════════════════════════════════╝\n");

    let names = ["alpha", "beta", "gamma", "delta"];
    let mut fed = MorpheusFederation::new_hybrid_pq(&names)
        .expect("hybrid federation constructs (ed25519 + ML-DSA-65 keypair per validator)");

    assert!(fed.config.hybrid_pq, "the HybridPq flag is ON");
    assert!(
        fed.config.hybrid_pq_active(),
        "the hybrid quorum is ACTIVE (every member carries a position-aligned PQ key)"
    );

    let n = fed.config.members.len();
    let t = fed.config.threshold;
    println!("  {n} validators: {}", names.join(", "));
    println!("  quorum: {t}-of-{n}");
    println!("  each validator holds:  ed25519 (32 B pk)  +  ML-DSA-65 (1952 B pk)");
    println!(
        "  HybridPq: ACTIVE ✓   (fail-closed — a missing PQ key REFUSES finality, never a silent downgrade)\n"
    );

    println!("  ── finalizing blocks under the hybrid quorum ──");
    for round in 1..=3usize {
        fed.submit_revocation((round - 1) % n, &format!("token-{round}"));
        let (block, _qc) = fed
            .run_consensus_round()
            .expect("hybrid consensus round finalizes");
        let hqc = fed
            .last_hybrid_qc
            .clone()
            .expect("a hybrid QC was recorded for the finalized block");

        // The whole point: the QC verifies ONLY if BOTH halves do.
        let ok = hqc.verify_with_keys(&fed.config.members, &fed.config.ml_dsa_members);
        assert!(ok, "hybrid QC (classical ∧ pq) must verify");

        let n_ed = hqc.qc.votes.len();
        let n_pq = hqc.pq_sigs.len();
        let ed_bytes = n_ed * 64;
        let pq_bytes: usize = hqc.pq_sigs.iter().map(|(_, s)| s.len()).sum();
        println!(
            "  block {:>2} FINALIZED  │  {n_ed} ed25519 votes ({ed_bytes} B)  +  {n_pq} ML-DSA-65 sigs ({pq_bytes} B)  │  hybrid verify ✓",
            block.height
        );
    }

    println!("\n  ── why this is quantum-safe ──");
    println!("  the classical (ed25519) half falls to Shor; the ML-DSA-65 half (FIPS 204,");
    println!("  lattice) does not. A hybrid QC verifies iff BOTH halves do — so an adversary");
    println!("  who breaks ed25519 ENTIRELY still cannot forge a finalized block.");
    println!("  (proved in Lean: Dregg2.Crypto.HybridQuorum.hybrid_survives_classical_break.)\n");

    println!("  HybridPq is LIVE — every quorum certificate is now quantum-safe. 🔒🐉");
}
