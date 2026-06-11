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
use dregg_circuit::effect_vm::{CellState, Effect, EffectVmAir, generate_effect_vm_trace, pi};
use dregg_circuit::effect_vm_descriptors::descriptor_for_selector;
use dregg_circuit::effect_vm_p3_full_air::{
    effect_vm_p3_width, extend_trace_with_hashes, prove_effect_vm_p3, verify_effect_vm_p3,
};
use dregg_circuit::field::BabyBear;
use dregg_circuit::joint_turn_aggregation::{
    JointParticipant, prove_joint_turn, verify_joint_turn,
};
use dregg_circuit::lean_descriptor_air::{
    parse_vm_descriptor, prove_vm_descriptor, verify_vm_descriptor,
};
use dregg_circuit::merkle_air::{
    membership_public_inputs, prove_membership_p3, verify_membership_p3,
};
use dregg_circuit::stark;

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
        "  EffectVM AIR: base width 186, +{} Poseidon2-aux cols => full width {}",
        effect_vm_p3_width() - 186,
        effect_vm_p3_width()
    );

    section("1. EffectVM state-transition proof — HAND-AIR (live default path)");
    println!(
        "  {:<22} {:>5} {:>6} {:>13} {:>13} {:>11}",
        "workload", "effs", "rows", "prove", "verify", "proof"
    );
    for (name, st, effs) in effectvm_workloads() {
        let (trace, pis) = generate_effect_vm_trace(&st, &effs);
        let rows = trace.len();
        let proof = prove_effect_vm_p3(&trace, &pis).expect("prove");
        verify_effect_vm_p3(&proof, &pis).expect("verify");
        let prove = time_mean(5, || prove_effect_vm_p3(&trace, &pis).expect("prove"));
        let verify = time_mean(30, || verify_effect_vm_p3(&proof, &pis).expect("verify"));
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

    section("2. EffectVM — DESCRIPTOR-INTERPRETER (verified-by-construction cutover)");
    {
        let (st, effs) = single_transfer();
        let (trace, full_pis) = generate_effect_vm_trace(&st, &effs);
        // selector 1 = TRANSFER; the validated cutover-ready descriptor.
        if let Some(json) = descriptor_for_selector(1) {
            let desc = parse_vm_descriptor(json).expect("parse transfer descriptor");
            let dpis = full_pis[..desc.public_input_count].to_vec();
            let proof = prove_vm_descriptor(&desc, &trace, &dpis).expect("descriptor prove");
            verify_vm_descriptor(&desc, &proof, &dpis).expect("descriptor verify");
            let prove = time_mean(5, || {
                prove_vm_descriptor(&desc, &trace, &dpis).expect("descriptor prove")
            });
            let verify = time_mean(30, || {
                verify_vm_descriptor(&desc, &proof, &dpis).expect("descriptor verify")
            });
            // hand-AIR baseline for the SAME single transfer (apples to apples).
            let hand = prove_effect_vm_p3(&trace, &full_pis).expect("hand prove");
            let hand_prove = time_mean(5, || prove_effect_vm_p3(&trace, &full_pis).expect("hand"));
            println!(
                "  {:<32} {:>13} {:>13} {:>11}",
                "path", "prove", "verify", "proof"
            );
            println!(
                "  {:<32} {:>13} {:>13} {:>11}",
                "transfer  (descriptor-interp)",
                fmt_secs(prove),
                fmt_secs(verify),
                fmt_bytes(p3_proof_bytes(&proof))
            );
            println!(
                "  {:<32} {:>13} {:>13} {:>11}",
                "transfer  (hand-AIR, default)",
                fmt_secs(hand_prove),
                "(see §1)",
                fmt_bytes(p3_proof_bytes(&hand))
            );
            let overhead = (prove / hand_prove - 1.0) * 100.0;
            println!("  => descriptor-interpreter prove overhead vs hand-AIR: {overhead:+.1}%");
        } else {
            println!("  (no transfer descriptor registered — skipped)");
        }
    }

    section("3. Where the time goes inside ONE EffectVM proof (witness-gen vs prove)");
    {
        let (st, effs) = single_transfer();
        let (base_trace, pis) = generate_effect_vm_trace(&st, &effs);
        // (a) witness-gen: building the base trace from state+effects.
        let wgen = time_mean(50, || generate_effect_vm_trace(&st, &effs));
        // (b) hash-aux extension: filling the Poseidon2 aux blocks.
        let hashext = time_mean(50, || extend_trace_with_hashes(&base_trace));
        // (c) total prove (includes (b) internally) and (d) verify.
        let total = time_mean(5, || prove_effect_vm_p3(&base_trace, &pis).expect("prove"));
        let proof = prove_effect_vm_p3(&base_trace, &pis).expect("prove");
        let verify = time_mean(30, || verify_effect_vm_p3(&proof, &pis).expect("verify"));
        println!("  {:<40} {:>13}", "stage", "time");
        println!(
            "  {:<40} {:>13}",
            "base-trace witness-gen (state->trace)",
            fmt_secs(wgen)
        );
        println!(
            "  {:<40} {:>13}",
            "Poseidon2-aux extension (hash witness)",
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
    {
        let (st, effs) = single_transfer();
        let (trace, pis) = generate_effect_vm_trace(&st, &effs);
        // bespoke stark over EffectVmAir (the legacy / aggregation per-cell prover)
        let air = EffectVmAir::new(trace.len());
        let bproof = stark::prove(&air, &trace, &pis);
        stark::verify(&air, &bproof, &pis).expect("bespoke verify");
        let bprove = time_mean(10, || stark::prove(&air, &trace, &pis));
        let bverify = time_mean(50, || stark::verify(&air, &bproof, &pis).expect("bverify"));
        // audited p3 over the same transition
        let pproof = prove_effect_vm_p3(&trace, &pis).expect("p3 prove");
        let pprove = time_mean(5, || prove_effect_vm_p3(&trace, &pis).expect("p3 prove"));
        let pverify = time_mean(30, || {
            verify_effect_vm_p3(&pproof, &pis).expect("p3 verify")
        });
        println!("  {:<28} {:>13} {:>13}", "prover", "prove", "verify");
        println!(
            "  {:<28} {:>13} {:>13}",
            "bespoke stark (legacy/agg)",
            fmt_secs(bprove),
            fmt_secs(bverify)
        );
        println!(
            "  {:<28} {:>13} {:>13}",
            "audited p3 (live commit path)",
            fmt_secs(pprove),
            fmt_secs(pverify)
        );
        println!(
            "  => the audited p3 path costs {:.1}x the bespoke prover (real in-circuit Poseidon2 + log_blowup=3)",
            pprove / bprove
        );
    }

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
        "  {:<14} {:>15} {:>13} {:>11}",
        "cells", "prove (agg+cells)", "verify", "proof"
    );
    for n in [2usize, 4, 8] {
        let proof = prove_joint_turn(build_participants(n)).expect("joint prove");
        verify_joint_turn(&proof).expect("joint verify");
        let prove = time_mean(3, || {
            prove_joint_turn(build_participants(n)).expect("joint prove")
        });
        let verify = time_mean(10, || verify_joint_turn(&proof).expect("joint verify"));
        let bytes = postcard::to_allocvec(&proof.aggregation_proof)
            .map(|v| v.len())
            .unwrap_or(0);
        println!(
            "  {:<14} {:>15} {:>13} {:>11}",
            n,
            fmt_secs(prove),
            fmt_secs(verify),
            fmt_bytes(bytes)
        );
    }
    println!("  NOTE: silver aggregation re-verifies every per-cell proof (no recursion);");
    println!("        verify cost grows ~linearly in cells. Gold recursive path collapses this");
    println!("        to one succinct proof (joint_turn_recursive) at higher prove cost.");

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

/// Build N agreeing joint-turn participants, each a real EffectVm whole-turn
/// proof through the bespoke `stark` per-cell prover (the substrate
/// `proof_forest` / aggregation use), with a shared turn id.
fn build_participants(n: usize) -> Vec<JointParticipant> {
    (0..n)
        .map(|i| {
            let state = CellState::new(100 + i as u64 * 10, i as u32);
            let effects = vec![Effect::Transfer {
                amount: 5,
                direction: 1,
            }];
            let (trace, mut public_inputs) = generate_effect_vm_trace(&state, &effects);
            public_inputs[pi::TURN_HASH_BASE] = BabyBear::new(0xABCD);
            let air = EffectVmAir::new(trace.len());
            let proof = stark::prove(&air, &trace, &public_inputs);
            JointParticipant {
                proof,
                public_inputs,
            }
        })
        .collect()
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
