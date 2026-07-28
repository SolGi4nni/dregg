//! # THE ≥100-BIT CUTOVER — the config the prover RUNS, measured against the ledger it READS
//!
//! `docs/FRI-SECURE-PARAMETERIZATION.md` §3.1 row **D** proposes `extDeg 4 · logBlowup 2 ·
//! 110 queries · arity 8 · query_pow 16 · commit_pow 28 · |D⁰| = 2^17` as the cheapest ≥100-bit
//! posture that needs **no ember-gated step** — no field change, no VK rotation, no fresh Groth16
//! setup. `Dregg2.Circuit.FriCommitPow.ext4_reaches_100_without_a_field_flag_day` is the Lean
//! witness that the *arithmetic* reaches 100 there.
//!
//! **That theorem is about a number. This file is about a prover.** Its whole reason to exist is
//! that a calculator reading 100 for a config no prover runs is the forbidden fake-green, and the
//! only instrument that can tell the two apart is a real proof at the real knobs.
//!
//! ## What the sweep measures (`--ignored`)
//!
//! Each candidate is handed to `create_recursion_config_with_fri` — the SAME constructor
//! `ir2_leaf_wrap_config()` reaches through — and then made to carry a real deployed workload end
//! to end: mint a rotated `Ir2BatchProof`, verify it natively, wrap it as a `NativeBatchStark`
//! recursion leaf (the in-circuit FRI verifier runs at the same knobs), and verify the wrapped
//! root. A candidate that cannot do all four is REPORTED AS UNRUNNABLE, with the failure text.
//!
//! It reads back the two facts the ledger arithmetic cannot supply and that
//! `docs/FRI-SECURE-PARAMETERIZATION.md` §3 did not model:
//!
//! 1. **the quotient-domain floor** — plonky3 splits `Q(x)` into `2^⌈log₂(deg−1)⌉` chunks and
//!    evaluates the trace on a domain that size (`uni-stark/src/prover.rs:197-208`). The deployed
//!    AIRs carry a degree-7 Poseidon2 S-box, so `log_blowup < 3` puts the quotient domain OUTSIDE
//!    the committed LDE. Whether that is a panic or a slow re-interpolation is a property of the
//!    pinned `p3-fri`, not of the arithmetic — so it is measured, not assumed.
//! 2. **the trace-height feedback loop** — `|D⁰| = max_height · 2^log_blowup`, and the wrap's
//!    `max_height` is the height of the circuit that VERIFIES the child proof in-circuit. That
//!    circuit's size is a function of `num_queries × fold_rounds`. So raising `q` to buy Johnson
//!    bits RAISES `|D⁰|`, which LOWERS the commit branch. §3's rows hold `|D⁰|` fixed while moving
//!    `q` by 5.8×; the `degree_bits` printed here are what actually happens.
//!
//! Run the sweep (SLOW — real recursion proofs, and any `commit_pow > 0` row grinds):
//!   `cargo test -p dregg-circuit-prove --release --test fri_hundred_bit_cutover -- --ignored --nocapture`

use std::time::Instant;

use dregg_cell::{AuthRequired, Cell, Ledger, Permissions};
use dregg_circuit::descriptor_ir2::{
    MemBoundaryWitness, UMemBoundaryWitness, parse_vm_descriptor2, prove_vm_descriptor2_for_config,
    verify_vm_descriptor2_with_config,
};
use dregg_circuit::effect_vm::trace_rotated::{
    RotatedBlockWitness, generate_rotated_effect_vm_trace, transfer_caveat_manifest,
};
use dregg_circuit::effect_vm::{CellState, Effect};
use dregg_circuit::effect_vm_descriptors::V3_STAGED_REGISTRY_TSV;
use dregg_circuit_prove::plonky3_recursion_impl::recursive::{
    DreggRecursionConfig, create_recursion_config_with_fri,
    verify_recursive_batch_proof_with_config,
};
use dregg_turn::rotation_witness as rw;

fn rotated_transfer_json() -> &'static str {
    for line in V3_STAGED_REGISTRY_TSV.lines() {
        let mut it = line.splitn(3, '\t');
        if it.next() == Some("transferVmDescriptor2R24") {
            let _name = it.next();
            return it.next().expect("json column");
        }
    }
    panic!("transferVmDescriptor2R24 not in V3_STAGED_REGISTRY_TSV");
}

fn open_permissions() -> Permissions {
    Permissions {
        send: AuthRequired::None,
        receive: AuthRequired::None,
        set_state: AuthRequired::None,
        set_permissions: AuthRequired::None,
        set_verification_key: AuthRequired::None,
        increment_nonce: AuthRequired::None,
        delegate: AuthRequired::None,
        access: AuthRequired::None,
    }
}

fn producer_cell(balance: i64, nonce: u64) -> Cell {
    let mut pk = [0u8; 32];
    pk[0] = 7;
    let mut cell = Cell::with_balance(pk, [0u8; 32], balance);
    cell.permissions = open_permissions();
    for _ in 0..nonce {
        let _ = cell.state.increment_nonce();
    }
    cell
}

/// One candidate knob set, in the order `create_recursion_config_with_fri` takes them.
#[derive(Clone, Copy)]
struct Candidate {
    label: &'static str,
    log_blowup: usize,
    max_log_arity: usize,
    num_queries: usize,
    commit_pow: usize,
    query_pow: usize,
}

/// What one real end-to-end run at a candidate produced.
struct Ran {
    inner_degree_bits: Vec<usize>,
    wrap_degree_bits: Vec<usize>,
    inner_bytes: usize,
    wrap_bytes: usize,
    prove_inner: f64,
    prove_wrap: f64,
    verify_wrap: f64,
}

/// **THE REAL RUN.** Mint + verify + wrap + verify-wrapped, at exactly these knobs. Returns the
/// failure text rather than panicking, because "this candidate cannot be proven" is the single
/// most important thing this file can report and a panic would take the sweep with it.
fn run_candidate(c: &Candidate) -> Result<Ran, String> {
    let config: DreggRecursionConfig = create_recursion_config_with_fri(
        c.log_blowup,
        0,
        c.max_log_arity,
        c.num_queries,
        c.commit_pow,
        c.query_pow,
    );

    // NOTE: the descriptor's own width is deliberately NOT pinned here. This file measures FRI
    // knobs; a width pin would make it red for a reason that has nothing to do with FRI (it did:
    // the staged registry read 1702 against `GRAD_ROT_WIDTH`'s 1647 on 2026-07-28).
    let desc = parse_vm_descriptor2(rotated_transfer_json()).expect("rotated transfer parses");

    let before_balance: i64 = 100_000;
    let amount: u64 = 50;
    let st = CellState::new(before_balance as u64, 0);
    let effects = vec![Effect::Transfer {
        amount,
        direction: 1,
    }];
    let mut ledger = Ledger::new();
    let before_cell = producer_cell(before_balance, 0);
    let after_cell = producer_cell(before_balance - amount as i64, 0);
    ledger.insert_cell(after_cell).unwrap();
    let nullifier_root = dregg_circuit::heap_root::empty_heap_root_8();
    let commitments_root = dregg_circuit::heap_root::empty_heap_root_8();
    let receipt_log: Vec<[u8; 32]> = vec![[1u8; 32], [2u8; 32]];
    let mk = |c: &Cell| {
        rw::produce(
            c,
            &ledger,
            &nullifier_root,
            &commitments_root,
            &dregg_turn::rotation_witness::empty_revoked_root_8(),
            &receipt_log,
            &Default::default(),
        )
    };
    let before_w = mk(&before_cell);
    let after_w = mk(&producer_cell(before_balance - amount as i64, 0));
    let bridge = |w: &rw::RotationWitness| -> RotatedBlockWitness {
        RotatedBlockWitness::new(w.pre_limbs.clone(), w.iroot).expect("31 pre-iroot limbs")
    };
    let caveat = transfer_caveat_manifest();
    let (trace, dpis) = generate_rotated_effect_vm_trace(
        &st,
        &effects,
        &bridge(&before_w),
        &bridge(&after_w),
        &caveat,
    )
    .map_err(|e| format!("trace generation failed: {e:?}"))?;

    let t0 = Instant::now();
    let proof = prove_vm_descriptor2_for_config(
        &desc,
        &trace,
        &dpis,
        &MemBoundaryWitness::default(),
        &[],
        &UMemBoundaryWitness::default(),
        &config,
    )
    .map_err(|e| format!("inner Ir2BatchProof prove FAILED: {e}"))?;
    let prove_inner = t0.elapsed().as_secs_f64();
    verify_vm_descriptor2_with_config(&desc, &proof, &dpis, &config)
        .map_err(|e| format!("inner proof VERIFY FAILED: {e}"))?;
    let inner_degree_bits = proof.degree_bits.clone();
    let inner_bytes = postcard::to_allocvec(&proof)
        .map_err(|e| format!("inner proof postcard: {e}"))?
        .len();

    let t1 = Instant::now();
    let wrapped = dregg_circuit_prove::ivc_turn_chain::prove_descriptor_leaf_rotated_with_config(
        &desc, &proof, &dpis, &config,
    )
    .map_err(|e| format!("leaf-wrap prove FAILED: {e}"))?;
    let prove_wrap = t1.elapsed().as_secs_f64();

    let t2 = Instant::now();
    verify_recursive_batch_proof_with_config(&wrapped.0, &config)
        .map_err(|e| format!("wrapped root VERIFY FAILED: {e:?}"))?;
    let verify_wrap = t2.elapsed().as_secs_f64();

    let wrap_degree_bits = wrapped.0.proof.degree_bits.clone();
    let wrap_bytes = postcard::to_allocvec(&wrapped.0)
        .map_err(|e| format!("wrap proof postcard: {e}"))?
        .len();

    Ok(Ran {
        inner_degree_bits,
        wrap_degree_bits,
        inner_bytes,
        wrap_bytes,
        prove_inner,
        prove_wrap,
        verify_wrap,
    })
}

/// The candidate ladder. The deployed row is first so every other row reads as a delta from it.
///
/// Rows are chosen to isolate ONE variable at a time against the deployed baseline, because the
/// two unknowns (the quotient-domain floor and the height feedback) are confounded in row D.
const CANDIDATES: &[Candidate] = &[
    Candidate {
        label: "DEPLOYED  lb6 arity2 q19  cpow0  qpow16",
        log_blowup: 6,
        max_log_arity: 1,
        num_queries: 19,
        commit_pow: 0,
        query_pow: 16,
    },
    Candidate {
        label: "E2 arity flip  lb6 arity8 q19  cpow0  qpow16",
        log_blowup: 6,
        max_log_arity: 3,
        num_queries: 19,
        commit_pow: 0,
        query_pow: 16,
    },
    Candidate {
        label: "lb floor probe lb3 arity8 q19  cpow0  qpow16",
        log_blowup: 3,
        max_log_arity: 3,
        num_queries: 19,
        commit_pow: 0,
        query_pow: 16,
    },
    Candidate {
        label: "ROW D blowup   lb2 arity8 q19  cpow0  qpow16",
        log_blowup: 2,
        max_log_arity: 3,
        num_queries: 19,
        commit_pow: 0,
        query_pow: 16,
    },
    Candidate {
        label: "ROW D queries  lb2 arity8 q110 cpow0  qpow16",
        log_blowup: 2,
        max_log_arity: 3,
        num_queries: 110,
        commit_pow: 0,
        query_pow: 16,
    },
    Candidate {
        label: "commit-pow live lb6 arity2 q19 cpow12 qpow16",
        log_blowup: 6,
        max_log_arity: 1,
        num_queries: 19,
        commit_pow: 12,
        query_pow: 16,
    },
];

/// **THE SWEEP.** Prints a runnability + cost table. Asserts nothing about which row wins — the
/// choice of tuple is a decision, and this is the measurement that decision is entitled to.
#[test]
#[ignore = "MEASUREMENT: real recursion proofs at six FRI knob sets. --ignored --nocapture."]
fn candidate_configs_are_runnable_and_measured() {
    println!(
        "\n{:<46} {:>10} {:>22} {:>22} {:>10} {:>10}",
        "candidate", "status", "inner degree_bits", "wrap degree_bits", "wrap KiB", "wrap s"
    );
    let mut any_ok = false;
    for c in CANDIDATES {
        match run_candidate(c) {
            Ok(r) => {
                any_ok = true;
                let inner_max = r.inner_degree_bits.iter().copied().max().unwrap_or(0);
                let wrap_max = r.wrap_degree_bits.iter().copied().max().unwrap_or(0);
                println!(
                    "{:<46} {:>10} {:>22} {:>22} {:>10.1} {:>10.1}",
                    c.label,
                    "RUNS",
                    format!("{:?}", r.inner_degree_bits),
                    format!("{:?}", r.wrap_degree_bits),
                    r.wrap_bytes as f64 / 1024.0,
                    r.prove_wrap
                );
                println!(
                    "      inner |D0| = 2^{}  wrap |D0| = 2^{}   inner {:.1} KiB / {:.1} s   \
                     verify-wrap {:.2} s",
                    inner_max + c.log_blowup,
                    wrap_max + c.log_blowup,
                    r.inner_bytes as f64 / 1024.0,
                    r.prove_inner,
                    r.verify_wrap
                );
            }
            Err(e) => {
                println!("{:<46} {:>10}   {e}", c.label, "UNRUNNABLE");
            }
        }
    }
    assert!(
        any_ok,
        "not one candidate ran — the harness itself is broken, which is not a finding about FRI"
    );
}
