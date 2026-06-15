//! FULL-SYSTEM dregg prover performance report.
//!
//! Times EVERY prove/verify primitive on the real dregg proving stack, end to
//! end, with proof sizes — the numbers the product/polis usability assessment
//! is grounded on. No estimates: each section drives the exact production code
//! path (the audited `prove_*_p3` provers, the descriptor interpreter, the
//! silver/gold aggregation, and the SDK commit-path entry the node calls).
//!
//! Run: `cargo run --release -p dregg-perf --bin perf-report`
//!
//! Sections:
//!   1. EffectVM state-transition proof — hand-AIR (the live default path)
//!   2. EffectVM — descriptor-interpreter (the verified-by-construction cutover)
//!   3. Witness-gen vs prove split (where the time goes inside one EffectVM proof)
//!   4. Sub-proof primitives: Merkle c-list membership (depth scaling)
//!   5. Bespoke `stark` vs audited p3 (the TCB-shrinking cost)
//!   6. Full-turn commit path (`prove_turn_self_sovereign`) — the real node number
//!   7. Silver joint-turn aggregation (N-cell) + per-cell + verify
//!   8. Proof sizes (wire bytes)

use std::time::Instant;

use dregg_circuit::dsl::membership::create_test_witness;
use dregg_circuit::effect_vm::{CellState, Effect, generate_effect_vm_trace, pi};
use dregg_circuit::effect_vm_descriptors::descriptor_for_selector;
use dregg_circuit::field::BabyBear;
use dregg_circuit::lean_descriptor_air::{
    descriptor_recursion_matrix, parse_vm_descriptor, prove_vm_descriptor, verify_vm_descriptor,
};
use dregg_circuit::merkle_air::{
    membership_public_inputs, prove_membership_p3, verify_membership_p3,
};

use dregg_perf::{fmt_bytes, fmt_secs, single_transfer, time_mean};

fn rule() {
    println!("{}", "=".repeat(72));
}

fn section(title: &str) {
    println!();
    rule();
    println!("  {title}");
    rule();
}

fn p3_proof_bytes<T: serde::Serialize>(p: &T) -> usize {
    postcard::to_allocvec(p).map(|v| v.len()).unwrap_or(0)
}

fn main() {
    println!();
    println!("  dregg prover performance report");
    println!("  machine: {}", machine());
    println!("  config: BabyBear, FRI log_blowup=3 (8x LDE), 50 queries, 16 PoW bits");
    println!(
        "  live EffectVM path: rotated IR-v2 descriptor-interpreter (the v1 hand-AIR is retired under recursion)"
    );

    // selector 1 = TRANSFER — the validated descriptor every transfer workload proves against.
    let transfer_desc = descriptor_for_selector(1)
        .map(|json| parse_vm_descriptor(json).expect("parse transfer descriptor"));

    section("1. EffectVM state-transition proof — DESCRIPTOR-INTERPRETER (live path)");
    println!(
        "  {:<22} {:>5} {:>6} {:>13} {:>13} {:>11}",
        "workload", "effs", "rows", "prove", "verify", "proof"
    );
    if let Some(desc) = transfer_desc.as_ref() {
        for (name, st, effs) in effectvm_workloads() {
            let (trace, full_pis) = generate_effect_vm_trace(&st, &effs);
            let rows = trace.len();
            let dpis = full_pis[..desc.public_input_count].to_vec();
            let proof = prove_vm_descriptor(desc, &trace, &dpis).expect("prove");
            verify_vm_descriptor(desc, &proof, &dpis).expect("verify");
            let prove = time_mean(5, || {
                prove_vm_descriptor(desc, &trace, &dpis).expect("prove")
            });
            let verify = time_mean(30, || {
                verify_vm_descriptor(desc, &proof, &dpis).expect("verify")
            });
            println!(
                "  {:<22} {:>5} {:>6} {:>13} {:>13} {:>11}",
                name,
                effs.len(),
                rows,
                fmt_secs(prove),
                fmt_secs(verify),
                fmt_bytes(p3_proof_bytes(&proof))
            );
        }
    } else {
        println!("  (no transfer descriptor registered — skipped)");
    }

    section("2. EffectVM — DESCRIPTOR-INTERPRETER (verified-by-construction cutover)");
    println!(
        "  (the descriptor-interpreter IS the live path — see §1 for its prove/verify/proof numbers;"
    );
    println!(
        "   the v1 hand-AIR baseline this section once compared against is retired under recursion.)"
    );

    section("3. Where the time goes inside ONE EffectVM proof (witness-gen vs prove)");
    if let Some(desc) = transfer_desc.as_ref() {
        let (st, effs) = single_transfer();
        let (base_trace, full_pis) = generate_effect_vm_trace(&st, &effs);
        let dpis = full_pis[..desc.public_input_count].to_vec();
        // (a) witness-gen: building the base trace from state+effects.
        let wgen = time_mean(50, || generate_effect_vm_trace(&st, &effs));
        // (b) descriptor witness extension: base wires -> full descriptor-AIR matrix
        //     (Poseidon2 site-aux + range bits), the surface `prove_vm_descriptor` consumes.
        let hashext = time_mean(50, || {
            descriptor_recursion_matrix(desc, &base_trace).expect("descriptor matrix")
        });
        // (c) total prove (includes (b) internally) and (d) verify.
        let total = time_mean(5, || {
            prove_vm_descriptor(desc, &base_trace, &dpis).expect("prove")
        });
        let proof = prove_vm_descriptor(desc, &base_trace, &dpis).expect("prove");
        let verify = time_mean(30, || {
            verify_vm_descriptor(desc, &proof, &dpis).expect("verify")
        });
        println!("  {:<40} {:>13}", "stage", "time");
        println!(
            "  {:<40} {:>13}",
            "base-trace witness-gen (state->trace)",
            fmt_secs(wgen)
        );
        println!(
            "  {:<40} {:>13}",
            "descriptor matrix extension (aux witness)",
            fmt_secs(hashext)
        );
        println!(
            "  {:<40} {:>13}",
            "STARK prove TOTAL (FRI+commit+aux)",
            fmt_secs(total)
        );
        println!(
            "  {:<40} {:>13}",
            "  of which: LDE+FRI+Merkle (prove - aux)",
            fmt_secs(total - hashext)
        );
        println!("  {:<40} {:>13}", "verify", fmt_secs(verify));
        println!(
            "  => witness-gen is {:.2}% of prove; FRI/commit dominates.",
            (wgen + hashext) / total * 100.0
        );
    } else {
        println!("  (no transfer descriptor registered — skipped)");
    }

    section("4. Sub-proof primitive: Merkle c-list MEMBERSHIP (depth scaling)");
    println!(
        "  {:<14} {:>13} {:>13} {:>11}",
        "depth", "prove", "verify", "proof"
    );
    for depth in [4usize, 8, 16, 32] {
        let leaf = BabyBear::new(42424242);
        let (siblings, positions, _root) = create_test_witness(leaf, depth);
        let pis = membership_public_inputs(leaf, &siblings, &positions).expect("mpis");
        let proof = prove_membership_p3(leaf, &siblings, &positions).expect("mprove");
        verify_membership_p3(&proof, &pis).expect("mverify");
        let prove = time_mean(5, || {
            prove_membership_p3(leaf, &siblings, &positions).expect("mprove")
        });
        let verify = time_mean(30, || verify_membership_p3(&proof, &pis).expect("mverify"));
        println!(
            "  {:<14} {:>13} {:>13} {:>11}",
            depth,
            fmt_secs(prove),
            fmt_secs(verify),
            fmt_bytes(p3_proof_bytes(&proof))
        );
    }

    section("5. Bespoke `stark` vs audited p3 (the TCB-shrinking cost)");
    println!(
        "  (RETIRED under recursion: both legs measured the v1 hand-AIR — the bespoke `stark` over"
    );
    println!(
        "   `EffectVmAir` and the audited `prove_effect_vm_p3`. The live path is the rotated IR-v2"
    );
    println!(
        "   descriptor (§1); the audited multi-table batch verifier is `descriptor_ir2::verify_vm_descriptor2`.)"
    );

    section("6. FULL-TURN COMMIT PATH — the real node number (prove_turn_self_sovereign)");
    {
        use dregg_sdk::{prove_turn_self_sovereign, verify_full_turn};
        let (st, effs) = single_transfer();
        let turn_hash = [7u8; 32];
        let (_t, pis) = generate_effect_vm_trace(&st, &effs);
        let old_commit = pis[pi::OLD_COMMIT];
        let new_commit = pis[pi::NEW_COMMIT];
        let t0 = Instant::now();
        let proof = prove_turn_self_sovereign(&st, &effs, turn_hash).expect("full-turn prove");
        let first = t0.elapsed().as_secs_f64();
        verify_full_turn(&proof, old_commit, new_commit).expect("full-turn verify");
        let prove = time_mean(3, || {
            prove_turn_self_sovereign(&st, &effs, turn_hash).expect("full-turn prove")
        });
        let verify = time_mean(20, || {
            verify_full_turn(&proof, old_commit, new_commit).expect("full-turn verify")
        });
        println!("  {:<34} {:>13}", "stage", "time");
        println!(
            "  {:<34} {:>13}",
            "cold first prove (incl. warm)",
            fmt_secs(first)
        );
        println!("  {:<34} {:>13}", "prove (mean)", fmt_secs(prove));
        println!("  {:<34} {:>13}", "verify (mean)", fmt_secs(verify));
        println!(
            "  {:<34} {:>13}",
            "wire proof size",
            fmt_bytes(proof.proof_bytes.len())
        );
        println!(
            "  components: state_transition={} auth={} membership={} conservation={} non_revocation={}",
            proof.components.has_state_transition,
            proof.components.has_authorization,
            proof.components.has_membership,
            proof.components.has_conservation,
            proof.components.has_non_revocation
        );
        println!("  NOTE: self-sovereign turn = EffectVM sub-proof + PI-binding main proof.");
        println!(
            "        A turn WITH auth+membership sub-proofs adds ~ (§4 membership + derivation) on top."
        );
    }

    section("7. Silver joint-turn AGGREGATION (N-cell private joint turn)");
    println!(
        "  (RETIRED under recursion: the v1 silver aggregation re-verified per-cell `EffectVmAir`"
    );
    println!(
        "   proofs via `prove_joint_turn`. The rotated cohort now carries `DescriptorParticipant`"
    );
    println!(
        "   legs (minted by `dregg_turn::rotation_witness::mint_rotated_participant_leg`), verified"
    );
    println!(
        "   by `joint_turn_aggregation::verify_descriptor_participant`; the recursive fold is"
    );
    println!(
        "   `joint_turn_recursive::prove_joint_turn_recursive_rotated`. Wiring an N-cell rotated"
    );
    println!(
        "   joint bench needs the full per-cell rotation witness set — tracked, not measured here.)"
    );

    println!();
    rule();
    println!("  end of report");
    rule();
    println!();
}

fn effectvm_workloads() -> Vec<(&'static str, CellState, Vec<Effect>)> {
    vec![
        (
            "transfer_1effect",
            CellState::new(1_000_000, 0),
            vec![Effect::Transfer {
                amount: 100,
                direction: 1,
            }],
        ),
        (
            "transfer_4effect",
            CellState::new(1_000_000, 0),
            (0..4)
                .map(|i| Effect::Transfer {
                    amount: 10,
                    direction: (i % 2) as u32,
                })
                .collect(),
        ),
        (
            "transfer_16effect",
            CellState::new(1_000_000, 0),
            (0..16)
                .map(|i| Effect::Transfer {
                    amount: 1,
                    direction: (i % 2) as u32,
                })
                .collect(),
        ),
    ]
}

fn machine() -> String {
    // Best-effort host identity for the report header.
    let model = std::process::Command::new("sysctl")
        .args(["-n", "machdep.cpu.brand_string"])
        .output()
        .ok()
        .and_then(|o| String::from_utf8(o.stdout).ok())
        .map(|s| s.trim().to_string())
        .filter(|s| !s.is_empty())
        .unwrap_or_else(|| std::env::consts::ARCH.to_string());
    format!(
        "{model} ({} logical cores)",
        std::thread::available_parallelism()
            .map(|n| n.get())
            .unwrap_or(0)
    )
}
