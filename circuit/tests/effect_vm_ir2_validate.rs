//! # THE EPOCH FLAG-DAY VALIDATE GATE — does IR-v2 prove+verify a REAL transfer end-to-end?
//!
//! `docs/EPOCH-DESIGN.md` makes hashing a BOUNDARY phenomenon: the per-effect circuit becomes a
//! MULTI-TABLE batch STARK (main + poseidon2-chip + range + memory + map-ops), Lean emits the
//! table/relation grammar (`emitVmJson2`, `"ir":2`), and `descriptor_ir2.rs` assembles it. This
//! file is the GATE the full VK cutover is gated on: it drives ONE real effect — `transfer`, the
//! validated reference — through the IR-v2 interpreter's full assembly + the AUDITED
//! `p3-batch-stark` prover, and asserts:
//!
//!   1. **PROVE** — the graduated v2 transfer descriptor (`graduateV1 transferVmDescriptor`,
//!      byte-exact from `EmitAllJsonV2.lean`, `dregg-effectvm-transfer-ir2.json`) proves over the
//!      SAME 186-column real transfer witness `generate_effect_vm_trace` produces (the witness the
//!      hand-AIR + the v1 descriptor interpreter both consume). Graduation turns the v1 hash sites
//!      into poseidon2-CHIP lookups and the v1 range teeth into RANGE lookups; the multi-table
//!      assembly realizes them as bus interactions. Transfer carries NO mem/map ops, so the memory
//!      boundary + map heaps are EMPTY — the chip+range tables alone exercise the LogUp lever.
//!   2. **VERIFY** — the proof verifies through the INDEPENDENT `verify_vm_descriptor2` (the AIRs
//!      rebuilt from the descriptor alone). The proof is REAL.
//!   3. **ANTI-GHOST** — a tampered post-state (the last-row `state_commit` cell mutated by +1)
//!      makes proving FAIL: the chip table only carries GENUINE Poseidon2 permutation rows, so the
//!      forged digest's chip lookup cannot be served (the chip tooth bites). A forged published
//!      `FINAL_BAL_LO` PI likewise refuses (the last-row balance PI binding tooth).
//!
//! This is the EPOCH analogue of `effect_vm_descriptor_cutover_harness.rs`'s v1 beachhead
//! (`transfer_descriptor_interpreter_is_a_faithful_drop_in_for_the_hand_air`), but against the
//! IR-v2 multi-table interpreter rather than the v1 single-table one.
//!
//! Gated on `recursion` (the feature that compiles `descriptor_ir2`). SLOW (~20min cold compile);
//! run ONCE: `cargo test -p dregg-circuit --features recursion ir2_validate -- --nocapture`.

#![cfg(feature = "prover")]

use dregg_circuit::descriptor_ir2::{
    MemBoundaryWitness, parse_vm_descriptor2, prove_vm_descriptor2, verify_vm_descriptor2,
};
use dregg_circuit::effect_vm::columns::{STATE_AFTER_BASE, state};
use dregg_circuit::effect_vm::{CellState, Effect, generate_effect_vm_trace, pi};
use dregg_circuit::effect_vm_descriptors::descriptor2_for_key;
use dregg_circuit::field::BabyBear;

/// THE GATE: IR-v2 proves+verifies a real transfer end-to-end, with the anti-ghost tooth.
#[test]
fn ir2_validate_transfer_proves_verifies_and_refuses_ghost() {
    // The graduated v2 transfer descriptor (byte-exact from the Lean v2 emit).
    let json = descriptor2_for_key("transferVmDescriptor2")
        .expect("transfer v2 descriptor must be registered");
    let desc = parse_vm_descriptor2(json).expect("transfer v2 descriptor must parse");
    assert_eq!(
        desc.trace_width, 216,
        "graduated transfer = 188 base + 7·4 chip lane cols (Phase B-GATE: 4 hash sites)"
    );
    assert_eq!(desc.tables.len(), 5, "the five EPOCH tables");
    // Transfer is a graduated v1 face: chip + range lookups only, no mem/map ops.
    assert!(
        desc.hash_sites.is_empty() && desc.ranges.is_empty(),
        "graduated transfer carries no legacy v1 carriers"
    );

    // Both transfer directions are part of the validated reference.
    let cases: Vec<(&str, CellState, Vec<Effect>)> = vec![
        (
            "transfer-out",
            CellState::new(100_000, 0),
            vec![Effect::Transfer {
                amount: 50,
                direction: 1,
            }],
        ),
        (
            "transfer-in",
            CellState::new(100_000, 0),
            vec![Effect::Transfer {
                amount: 50,
                direction: 0,
            }],
        ),
    ];

    // Transfer declares no memory ops and no map ops → empty boundary + no witness heaps.
    let mem_boundary = MemBoundaryWitness::default();
    let map_heaps: Vec<Vec<dregg_circuit::heap_root::HeapLeaf>> = vec![];

    let mut proven = 0usize;
    for (label, st, effects) in cases {
        // -- The real 186-col base trace + PIs (the witness the hand-AIR consumes). --
        let (base_trace, pis) = generate_effect_vm_trace(&st, &effects);
        assert_eq!(
            base_trace[0].len(),
            188,
            "[{label}] canonical 188-col EffectVM layout (186 + record-digest + asset-class)"
        );
        let dpis: Vec<BabyBear> = pis[..desc.public_input_count].to_vec();

        // (1) PROVE through the IR-v2 multi-table batch STARK (self-verifies before return).
        let proof = prove_vm_descriptor2(&desc, &base_trace, &dpis, &mem_boundary, &map_heaps)
            .unwrap_or_else(|e| {
                panic!("[{label}] IR-v2 FAILED to prove the honest transfer witness: {e}")
            });

        // (2) VERIFY independently (AIRs rebuilt from the descriptor alone).
        verify_vm_descriptor2(&desc, &proof, &dpis)
            .unwrap_or_else(|e| panic!("[{label}] IR-v2 proof failed independent verify: {e}"));

        eprintln!("[{label}] IR-v2 PROVE+VERIFY: real transfer proved and verified end-to-end.");

        // (3a) ANTI-GHOST — forged published FINAL_BAL_LO PI must REFUSE.
        {
            let mut forged = pis.clone();
            forged[pi::FINAL_BAL_LO] = forged[pi::FINAL_BAL_LO] + BabyBear::new(123);
            let fdpis: Vec<BabyBear> = forged[..desc.public_input_count].to_vec();
            let r = std::panic::catch_unwind(|| {
                prove_vm_descriptor2(&desc, &base_trace, &fdpis, &mem_boundary, &map_heaps)
            });
            let refused = match r {
                Err(_) => true,          // debug prover panicked on the unsatisfiable binding
                Ok(res) => res.is_err(), // or returned a prove/self-verify error
            };
            assert!(
                refused,
                "[{label}] IR-v2 PROVED a forged FINAL_BAL_LO — balance-PI tooth OPEN"
            );
        }

        // (3b) ANTI-GHOST — mutated last-row state_commit cell must REFUSE: the chip table only
        // carries genuine Poseidon2 rows, so the GROUP-4 commit hash-site's chip lookup of the
        // forged digest cannot be served.
        {
            let mut t = base_trace.clone();
            let last = t.len() - 1;
            t[last][STATE_AFTER_BASE + state::STATE_COMMIT] =
                t[last][STATE_AFTER_BASE + state::STATE_COMMIT] + BabyBear::new(1);
            let r = std::panic::catch_unwind(|| {
                prove_vm_descriptor2(&desc, &t, &dpis, &mem_boundary, &map_heaps)
            });
            let refused = match r {
                Err(_) => true,
                Ok(res) => res.is_err(),
            };
            assert!(
                refused,
                "[{label}] IR-v2 PROVED a forged last-row state_commit — chip/commit tooth OPEN"
            );
        }

        eprintln!(
            "[{label}] GATE GREEN: IR-v2 proves+verifies the honest transfer and refuses BOTH the \
             forged-balance and forged-state-commit tampers."
        );
        proven += 1;
    }
    assert_eq!(
        proven, 2,
        "both transfer directions must pass the IR-v2 gate"
    );
}
