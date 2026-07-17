//! **MOCK-PROOF PURGE RATCHET** — no production surface may ride a mock prover, ever again.
//!
//! ember, 2026-07-16: *"we need to get rid of all that mock shit… it gotta get purged. need to be wired
//! to real."* A mock proof/verify surface is the WORST lie this codebase can tell: it reports
//! `"valid"`/`"proved"` for data it never proved. This gate makes the purge PERMANENT — the baseline
//! below only ever SHRINKS.
//!
//! ## What counts as a mock prover (the engines, characterized from source — not from their comments)
//! * `circuit/src/ivc.rs` — WAS the SIMULATED IVC: `prove_ivc` built a hash-chain "proof";
//!   `verify_ivc` only recomputed a BLAKE3 digest over the proof's OWN public data.
//!   **Anyone who could call `prove_ivc` could mint a passing proof for any root walk.** Proof sizes
//!   were fabricated; `create_test_chain` fabricated the data itself. DELETED 2026-07-16 (final cut) —
//!   only the real Poseidon2 hash-chain primitives remain in that file.
//! * `circuit/src/constraint_prover.rs` — says it of itself (:5-8): *"a trace digest … **not** a
//!   cryptographic proof … nothing here is sound against a prover that lies"*; `generate_unchecked`
//!   (:256) skips even the local constraint check.
//!
//! ## The REAL prover (the wiring target)
//! `circuit-prove/src/ivc_turn_chain.rs`: `prove_turn_chain_recursive(&[FinalizedTurn]) -> WholeChainProof`
//! (:1714), verified by `verify_whole_chain_proof_bytes` (:1598) — consumed for real by
//! `lightclient/src/lib.rs`. Per-effect proving is `descriptor_by_name` + `prove_vm_descriptor2`.
//! `preflight/src/checks/derivation_descriptor.rs` is the IN-REPO TEMPLATE for a correct migration
//! (real `prove_vm_descriptor2`/`verify_vm_descriptor2`; it explicitly REFUSES the trace-digest path).
//!
//! ## Why some entries are not one-line swaps (read before "just wiring" one)
//! A `FinalizedTurn` wraps a `DescriptorParticipant` — the rotated turn descriptor, produced at PROVING
//! time. A `TurnReceipt` (what `cclerk.receipt_chain()` retains) is HASHES ONLY. So a mock may exist
//! because the provable data was **discarded at that layer**; wiring real then needs RETENTION/plumbing,
//! not a swap. The plumbing already exists but is uncalled in production:
//! `turn/src/rotation_witness.rs:731 finalized_turn_from_full_turn` re-proves the rotated leg and
//! FAIL-CLOSES unless the leg's anchors equal the served `FullTurnProof`'s proven commits — its context
//! exists exactly once, at `node/src/blocklace_sync.rs::execute_finalized_turn` (:4287), which today
//! persists only the `FullTurnProof`. Persist the `FinalizedTurn` there and the chain becomes provable.
//!
//! ## If this test fails
//! You added a production surface that rides a mock prover. **Do NOT add yourself to the baseline.**
//! Wire it to the real prover above. If the provable data is not at your layer, FAIL CLOSED (return an
//! honest error — `node/src/mcp/handlers_verify.rs::tool_prove_sovereign_turn` :206-212 is the honest
//! pattern) and name the plumbing. A mock that answers "valid" is never acceptable.

use std::path::Path;

fn count_mock_sites(src: &str) -> usize {
    [
        "prove_ivc(",
        "verify_ivc(",
        "create_test_chain(",
        "ConstraintProof",
        "generate_unchecked",
        "simulated_proof_size_bytes",
    ]
    .iter()
    .map(|p| src.matches(p).count())
    .sum()
}

/// Frozen 2026-07-16. Verdicts from the purge map (`wh0frxr57`). **SHRINK ONLY.**
#[rustfmt::skip]
const BASELINE: &[(&str, usize)] = &[
        // ── THE MOCK ENGINES themselves (retire once nothing production rides them) ──
        // 2026-07-16: presentation-IVC surface retired (`IvcPresentationProof` + verify,
        // `IvcBackend`/`IvcBackendProof`/`finalize_with_backend`): 79 -> 70.
        // circuit/src/ivc.rs: PURGED 2026-07-16 (final cut) — the simulated engine ITSELF is
        // DELETED (prove/verify/builder/proof types/IvcAir/create_test_chain, plus its dead
        // riders: cipherclerk's never-enabled `enable_ivc` path, the soundness.rs mock tests,
        // the ivc_attenuation_chain example). 70 -> 0. What remains in ivc.rs are the REAL
        // Poseidon2 hash-chain primitives + the state-transition trace shape, which contain
        // zero mock sites.
        ("circuit/src/constraint_prover.rs", 17),
        // node/src/mcp/handlers_verify.rs: PURGED 2026-07-16 — dregg_compress_history now proves via
        // the REAL prove_turn_chain_recursive over retained FinalizedTurns (plumbed at the node commit
        // path); dregg_compose_proofs retired fail-closed. 3 -> 0.
        // dregg-genesis-snapshot: PURGED 2026-07-16 — the mock "history proof" field was DROPPED
        // (not renamed): the layer holds no per-turn provable data, and the leg was minterable by
        // any forger. Tamper-refusal rests on the voucher/re-addressing consistency checks, and
        // the crate's docs now say exactly what those are NOT.
        // ── WIRE-FEASIBLE (real data trivially available here) ──
        // preflight/src/checks/sovereign.rs: PURGED 2026-07-16 — the ivc_history_compression check
        // now mints REAL rotated turns (rotation_witness) and drives the REAL whole-chain fold
        // (`ivc_turn_chain::prove_turn_chain_recursive` + `verify_whole_chain_proof_bytes`), with
        // forged-chain / tampered-publics / wrong-anchor refusal teeth.
        // preflight/src/checks/{proofs,composition,backends}.rs: PURGED 2026-07-16 (d17cbdfe9) — the
        // promotion gate's IVC checks (ivc, ivc_wrong_root, chain, ivc-recursive) now verify the shared
        // REAL whole-chain fold (`preflight/src/checks/ivc_real.rs`, ONE minter) via
        // `verify_whole_chain_proof_bytes`, each with a refusal tooth (wrong genesis root, relabeled
        // num_turns, tampered chain_digest). proofs 5->0, composition 2->0, backends 2->0.
        // ── HONEST-RETIRE (dead but ARMED: the mock rode wire types / is_valid honored it) ──
        // 2026-07-16 the presentation-IVC path was RETIRED: `PresentationAir::prove_ivc`/
        // `prove_ivc_no_folds`, `BridgePresentationBuilder::prove_ivc`, `IvcPresentationProof`,
        // and the `ivc_proof` wire field are DELETED; `is_valid()` now rests solely on
        // `real_stark_proof`. bridge/src/present.rs: 4 -> 0.
        // circuit/src/multi_step_witness.rs: 3 -> 0 (`prove_authorization` trace-digest leg gone).
        // circuit/src/backends/mod.rs: 2 -> 0 (unimplemented `IvcBackend` trait gone).
        // presentation.rs residual 11 = the sequential `prove()` fold-proof path (constraint
        // proofs inside `PresentationProof`), still exercised by prove()/prove_fast(); retires
        // with the constraint-prover engine itself.
        ("circuit/src/presentation.rs", 11),
        // ── incidental ──
        ("circuit/src/lib.rs", 1),
        ("preflight/src/checks/derivation_descriptor.rs", 1),  // the CORRECT template: names the mock only to REFUSE it.
];

#[test]
fn no_new_production_surface_rides_a_mock_prover() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).parent().unwrap();
    let mut violations = Vec::new();
    let mut stack = vec![root.to_path_buf()];
    while let Some(dir) = stack.pop() {
        let Ok(entries) = std::fs::read_dir(&dir) else {
            continue;
        };
        for e in entries.flatten() {
            let p = e.path();
            let name = e.file_name().to_string_lossy().to_string();
            if p.is_dir() {
                // production source only: skip test/bench/example trees and build output
                if !matches!(
                    name.as_str(),
                    "target" | ".git" | "tests" | "benches" | "examples" | "node_modules"
                ) {
                    stack.push(p);
                }
                continue;
            }
            if p.extension().and_then(|s| s.to_str()) != Some("rs") || name == "tests.rs" {
                continue;
            }
            let Ok(src) = std::fs::read_to_string(&p) else {
                continue;
            };
            let n = count_mock_sites(&src);
            if n == 0 {
                continue;
            }
            let rel = p
                .strip_prefix(root)
                .unwrap()
                .to_string_lossy()
                .replace('\\', "/");
            match BASELINE.iter().find(|(f, _)| *f == rel) {
                None => violations.push(format!(
                    "  NEW production surface rides a MOCK prover: {rel} ({n} sites)\n     -> wire it to `ivc_turn_chain::prove_turn_chain_recursive` / `prove_vm_descriptor2`, or FAIL CLOSED. Do NOT add it to the baseline."
                )),
                Some((_, allowed)) if n > *allowed => violations.push(format!(
                    "  GREW: {rel} ({allowed} -> {n} mock sites)\n     -> the purge only shrinks. Wire it to the real prover."
                )),
                _ => {}
            }
        }
    }
    assert!(
        violations.is_empty(),
        "\n\nMOCK-PROOF PURGE VIOLATED — production must never ride a mock prover.\n\n{}\n\nSee this file's module docs for the real prover + the honest fail-closed pattern.\n",
        violations.join("\n")
    );
}
