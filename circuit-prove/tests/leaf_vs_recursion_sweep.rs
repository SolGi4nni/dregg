//! # THE IN-CIRCUIT VERIFIER, DECOMPOSED BY REGRESSION — what a wrap actually pays for
//!
//! `notes/recursion-tower-profile.md` §2 measured the identity that makes this question askable:
//! the leaf wrap's in-circuit `poseidon2_perm` op count (38,168) **equals** the child's native
//! verify permutation count (38,168), to the unit. So *the cost of recursion is exactly the cost
//! of expressing the child's verifier as constraints*, and the leaf system should be chosen to
//! minimise **its verifier's in-circuit cost**, not its prover cost.
//!
//! What that note could not do is say **which component of the verifier** the 38,168 is. Its §4b
//! names four channels (per-query Merkle *leaf* hashing `q·Σ⌈w/8⌉`, Merkle *path* compressions
//! `q·depth`, the reduced-opening Horner `q·Σw`, and an `O(1)`-in-`q` OOD evaluation) and asserts
//! in prose that *"most in-circuit permutations are 2-to-1 compressions along `q` paths"* — but
//! it measured only one point, so the split is not determined by anything it printed.
//!
//! ## ⚑ THE INSTRUMENT: a parameter sweep, not a new counter
//!
//! The wrap circuit is built deterministically from the child proof's shape, and
//! `create_recursion_config_split_fri` lets the child be minted at an arbitrary
//! `(log_blowup, log_arity, num_queries)` with the wrap's in-circuit verify engine pointed at the
//! same knobs. A circuit build is ~1.2 s and the op census is exact, so the components can be
//! **separated by regression** instead of by a new counting config (`recursion-tower-profile.md`
//! §0b's monomorphism blocker is thereby side-stepped, not solved):
//!
//! ```text
//!   perms(q, m) = C(m)  +  q · [ L  +  P(m) ]
//!                 ^^^^         ^^^    ^^^^
//!                 |            |      Merkle PATH depth + FRI-round paths — grows with m
//!                 |            per-query LEAF sponge over opened rows — INDEPENDENT of m
//!                 transcript / commitment observation / grind — INDEPENDENT of q
//! ```
//!
//! * fix `m`, vary `q` ⇒ slope is `L + P(m)`, intercept is `C(m)`;
//! * repeat at several `m = log₂(max child LDE height) = log₂(max trace rows) + log_blowup`
//!   ⇒ `P(m)` separates from `L`.
//!
//! Everything printed is an **exact op count**. No wall clock is evidence here (load average was
//! three digits while this ran); the two elapsed times printed are labelled upper bounds.
//!
//! ⚠ **Every point re-mints the child.** `num_queries` and the folding arity are read from the
//! child proof's *structure* in-circuit (`recursion-verify/src/config.rs:416-418`), so they cannot
//! be swept on a fixed proof.
//!
//! Run (release only):
//! ```text
//! cargo test -p dregg-circuit-prove --release --test leaf_vs_recursion_sweep \
//!   -- --ignored --nocapture --test-threads=1
//! ```

use std::collections::BTreeMap;
use std::time::Instant;

use dregg_cell::{AuthRequired, Cell, Ledger, Permissions};
use dregg_circuit::descriptor_ir2::{
    Ir2Air, MemBoundaryWitness, UMemBoundaryWitness, ir2_airs_and_common_for_config,
    prove_vm_descriptor2_for_config,
};
use dregg_circuit::effect_vm::trace_rotated::{RotatedBlockWitness, transfer_caveat_manifest};
use dregg_circuit::effect_vm::{CellState, Effect};
use dregg_circuit_prove::plonky3_recursion_impl::recursive::{
    DreggRecursionConfig, create_recursion_backend, create_recursion_config_split_fri,
};
use dregg_turn::rotation_witness as rw;
use p3_air::BaseAir;
use p3_baby_bear::BabyBear as P3BabyBear;
use p3_circuit::{AluOpKind, Circuit, Op};
use p3_field::extension::BinomialExtensionField;
use p3_recursion::{RecursionInput, build_next_layer_circuit_with_expose};

const D: usize = 4;
type EF = BinomialExtensionField<P3BabyBear, D>;

/// `PaddingFreeSponge<Perm, WIDTH=16, RATE=8, OUT=8>` — `recursion-verify/src/config.rs:104`.
const RATE: usize = 8;

// ===========================================================================
// Census (same shape as `recursion_tower_profile.rs`; kept local so the two files do not
// couple — this one is a sweep, that one is the single deployed point.)
// ===========================================================================

#[derive(Default, Debug, Clone)]
struct Census {
    n_horner: u64,
    n_alu_other: u64,
    n_hint: u64,
    n_const: u64,
    n_public: u64,
    npo: BTreeMap<String, u64>,
    witness_count: u32,
}

impl Census {
    fn perms(&self) -> u64 {
        self.npo
            .iter()
            .filter(|(k, _)| k.starts_with("poseidon2_perm"))
            .map(|(_, v)| *v)
            .sum()
    }
    fn recompose(&self) -> u64 {
        self.npo.get("recompose").copied().unwrap_or(0)
    }
    fn alu(&self) -> u64 {
        self.n_horner + self.n_alu_other
    }
}

fn census(circuit: &Circuit<EF>) -> Census {
    let mut c = Census {
        witness_count: circuit.witness_count,
        ..Default::default()
    };
    for op in &circuit.ops {
        match op {
            Op::Const { .. } => c.n_const += 1,
            Op::Public { .. } => c.n_public += 1,
            Op::Hint { .. } => c.n_hint += 1,
            Op::Alu { kind, .. } => match kind {
                AluOpKind::HornerAcc => c.n_horner += 1,
                _ => c.n_alu_other += 1,
            },
            Op::NonPrimitiveOpWithExecutor { executor, .. } => {
                *c.npo
                    .entry(executor.op_type().as_str().to_string())
                    .or_insert(0) += 1;
            }
        }
    }
    c
}

// ===========================================================================
// Fixture — the deployed rotated transfer leaf (the child that is actually wrapped).
// ===========================================================================

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

/// The same wide dispatch `mint_rotated_participant_leg` runs — the path the apex fold takes.
/// (`recursion_tower_profile.rs` records why the narrow `generate_rotated_effect_vm_trace` path is
/// RED at HEAD; not re-litigated here.)
#[allow(clippy::type_complexity)]
fn rotated_transfer_workload() -> (
    dregg_circuit::descriptor_ir2::EffectVmDescriptor2,
    Vec<Vec<dregg_circuit::field::BabyBear>>,
    Vec<dregg_circuit::field::BabyBear>,
    Vec<Vec<dregg_circuit::heap_root::HeapLeaf>>,
    MemBoundaryWitness,
) {
    use dregg_circuit::effect_vm::trace_rotated::generate_rotated_effect_vm_descriptor_and_trace_wide;
    use dregg_turn::rotation_witness::{empty_revoked_root_8, produce, sender_membership_teeth};

    let before_balance: i64 = 100_000;
    let amount: u64 = 50;
    let st = CellState::new(before_balance as u64, 0);
    let effects = vec![Effect::Transfer {
        amount,
        direction: 1,
    }];
    let before_cell = producer_cell(before_balance, 0);
    let after_cell = producer_cell(before_balance - amount as i64, 0);
    let mut ledger = Ledger::new();
    ledger.insert_cell(after_cell.clone()).unwrap();
    let nullifier_root = dregg_circuit::heap_root::empty_heap_root_8();
    let commitments_root = dregg_circuit::heap_root::empty_heap_root_8();
    let receipt_log: Vec<[u8; 32]> = vec![[1u8; 32], [2u8; 32]];
    let mk = |c: &Cell| {
        produce(
            c,
            &ledger,
            &nullifier_root,
            &commitments_root,
            &empty_revoked_root_8(),
            &receipt_log,
            &dregg_cell::commitment::RotationCarrierMaterial::default(),
        )
    };
    let before_w = mk(&before_cell);
    let after_w = mk(&after_cell);
    let bridge = |w: &rw::RotationWitness| -> RotatedBlockWitness {
        RotatedBlockWitness::new(w.pre_limbs.clone(), w.iroot).expect("31 pre-iroot limbs")
    };
    let caveat = transfer_caveat_manifest();
    let (desc, trace, dpis, map_heaps, mem_boundary) =
        generate_rotated_effect_vm_descriptor_and_trace_wide(
            &st,
            &effects,
            &bridge(&before_w),
            &bridge(&after_w),
            &caveat,
            None,
            None,
            None,
            Some(sender_membership_teeth(&before_cell)),
        )
        .expect("the wide rotated producer dispatch");
    (desc, trace, dpis, map_heaps, mem_boundary)
}

// ===========================================================================
// One sweep point
// ===========================================================================

#[derive(Debug, Clone)]
struct Point {
    log_blowup: usize,
    log_arity: usize,
    num_queries: usize,
    /// `log₂` of the tallest child LDE = `log₂(max trace rows) + log_blowup`.
    m: usize,
    perms: u64,
    horner: u64,
    alu: u64,
    recompose: u64,
    hint: u64,
    witness: u32,
}

fn sweep_point(
    w: &(
        dregg_circuit::descriptor_ir2::EffectVmDescriptor2,
        Vec<Vec<dregg_circuit::field::BabyBear>>,
        Vec<dregg_circuit::field::BabyBear>,
        Vec<Vec<dregg_circuit::heap_root::HeapLeaf>>,
        MemBoundaryWitness,
    ),
    log_blowup: usize,
    log_arity: usize,
    num_queries: usize,
    query_pow_bits: usize,
) -> Point {
    let (desc, trace, dpis, map_heaps, mem_boundary) = w;
    // MINT == VERIFY: one config both proves the child and points the wrap's in-circuit FRI
    // verifier at exactly the knobs the child was minted under.
    let config = create_recursion_config_split_fri(
        log_blowup,
        0,
        log_arity,
        num_queries,
        0,
        query_pow_bits,
        log_blowup,
        0,
        0,
        query_pow_bits,
    );
    let inner = prove_vm_descriptor2_for_config::<DreggRecursionConfig>(
        desc,
        trace,
        dpis,
        mem_boundary,
        map_heaps,
        &UMemBoundaryWitness::default(),
        &config,
    )
    .expect("the rotated transfer leaf proves at this engine");

    let (airs, table_public_inputs, common) =
        ir2_airs_and_common_for_config(desc, &inner, dpis, &config).expect("verify triple");
    let max_dbits = inner.degree_bits.iter().copied().max().unwrap_or(0);

    let input: RecursionInput<'_, DreggRecursionConfig, Ir2Air> =
        RecursionInput::NativeBatchStark {
            airs: &airs,
            proof: &inner,
            common_data: &common,
            table_public_inputs,
        };
    let backend = create_recursion_backend();
    let (circuit, _vr) =
        build_next_layer_circuit_with_expose::<DreggRecursionConfig, Ir2Air, _, D>(
            &input, &config, &backend, None,
        )
        .expect("the leaf-wrap verification circuit builds");
    let c = census(&circuit);
    Point {
        log_blowup,
        log_arity,
        num_queries,
        m: max_dbits + log_blowup,
        perms: c.perms(),
        horner: c.n_horner,
        alu: c.alu(),
        recompose: c.recompose(),
        hint: c.n_hint,
        witness: c.witness_count,
    }
}

fn header() {
    println!(
        "\n{:>3} {:>5} {:>4} {:>4} | {:>10} {:>10} {:>10} {:>10} {:>10} {:>11}",
        "lb", "arity", "q", "m", "perms", "HornerAcc", "Alu(all)", "recompose", "Hint", "witness"
    );
    println!("{}", "-".repeat(96));
}

fn row(p: &Point) {
    println!(
        "{:>3} {:>5} {:>4} {:>4} | {:>10} {:>10} {:>10} {:>10} {:>10} {:>11}",
        p.log_blowup,
        1usize << p.log_arity,
        p.num_queries,
        p.m,
        p.perms,
        p.horner,
        p.alu,
        p.recompose,
        p.hint,
        p.witness
    );
}

// ===========================================================================
// §A — the q-sweep at fixed blowup: separates the per-query slope from the constant
// ===========================================================================

#[test]
#[ignore = "MEASUREMENT: re-mints the child once per point. --ignored --nocapture --test-threads=1"]
fn a_query_sweep_at_fixed_blowup() {
    let w = rotated_transfer_workload();
    println!(
        "\n═══ §A  q-SWEEP at fixed (log_blowup, arity) — slope = per-query cost, intercept = the \
         q-independent transcript/OOD constant ═══"
    );
    println!(
        "child: `{}` trace_width {} / pi_count {}; main traces at log2 rows {:?}",
        w.0.name,
        w.0.trace_width,
        w.0.public_input_count,
        {
            let cfg = create_recursion_config_split_fri(6, 0, 1, 19, 0, 16, 6, 0, 0, 16);
            let inner = prove_vm_descriptor2_for_config::<DreggRecursionConfig>(
                &w.0,
                &w.1,
                &w.2,
                &w.4,
                &w.3,
                &UMemBoundaryWitness::default(),
                &cfg,
            )
            .expect("shape probe");
            let (airs, _, _) = ir2_airs_and_common_for_config(&w.0, &inner, &w.2, &cfg).unwrap();
            let widths: Vec<usize> = airs
                .iter()
                .map(|a| BaseAir::<P3BabyBear>::width(a))
                .collect();
            println!(
                "  Σwidth {} · Σ⌈w/8⌉ {}",
                widths.iter().sum::<usize>(),
                widths.iter().map(|x| x.div_ceil(RATE)).sum::<usize>()
            );
            inner.degree_bits.clone()
        }
    );

    for (lb, arity) in [(6usize, 1usize), (3, 1), (2, 1)] {
        println!("\n── log_blowup {lb}, folding arity {} ──", 1usize << arity);
        header();
        let mut pts = Vec::new();
        for q in [12usize, 19, 28, 38, 57] {
            let t = Instant::now();
            let p = sweep_point(&w, lb, arity, q, 16);
            row(&p);
            let _ = t.elapsed();
            pts.push(p);
        }
        // least-squares slope/intercept on (q, perms) and (q, HornerAcc)
        fit("perms", &pts, |p| p.perms as f64);
        fit("HornerAcc", &pts, |p| p.horner as f64);
        fit("Alu(all)", &pts, |p| p.alu as f64);
        fit("recompose", &pts, |p| p.recompose as f64);
    }
}

fn fit(label: &str, pts: &[Point], f: impl Fn(&Point) -> f64) {
    let n = pts.len() as f64;
    let sx: f64 = pts.iter().map(|p| p.num_queries as f64).sum();
    let sy: f64 = pts.iter().map(&f).sum();
    let sxx: f64 = pts.iter().map(|p| (p.num_queries as f64).powi(2)).sum();
    let sxy: f64 = pts.iter().map(|p| p.num_queries as f64 * f(p)).sum();
    let slope = (n * sxy - sx * sy) / (n * sxx - sx * sx);
    let icept = (sy - slope * sx) / n;
    // exactness check: max |residual|
    let maxres = pts
        .iter()
        .map(|p| (f(p) - (slope * p.num_queries as f64 + icept)).abs())
        .fold(0.0f64, f64::max);
    println!(
        "    fit {label:<10}: per-query {slope:>12.2}   q-independent {icept:>12.2}   max|resid| {maxres:>10.2}"
    );
}

// ===========================================================================
// §B — the blowup sweep at fixed q: separates the Merkle-PATH term from the LEAF term
// ===========================================================================

#[test]
#[ignore = "MEASUREMENT: re-mints the child once per point. --ignored --nocapture --test-threads=1"]
fn b_blowup_sweep_at_fixed_queries() {
    let w = rotated_transfer_workload();
    println!(
        "\n═══ §B  BLOWUP SWEEP at fixed q=19, arity 2 — the ONLY thing that moves is m = \
         log₂(child LDE height), so Δperms/Δm is the Merkle-PATH term ═══"
    );
    header();
    let mut pts = Vec::new();
    for lb in [1usize, 2, 3, 4, 5, 6, 7, 8] {
        let p = sweep_point(&w, lb, 1, 19, 16);
        row(&p);
        pts.push(p);
    }
    println!("\n  Δ per unit of m (adjacent differences):");
    for pair in pts.windows(2) {
        let (a, b) = (&pair[0], &pair[1]);
        println!(
            "    lb {}→{} (m {}→{}): Δperms {:>8}  ΔHornerAcc {:>8}  Δrecompose {:>8}",
            a.log_blowup,
            b.log_blowup,
            a.m,
            b.m,
            b.perms as i64 - a.perms as i64,
            b.horner as i64 - a.horner as i64,
            b.recompose as i64 - a.recompose as i64,
        );
    }
}

// ===========================================================================
// §C — the folding-arity sweep: the knob nobody prices
// ===========================================================================

#[test]
#[ignore = "MEASUREMENT: re-mints the child once per point. --ignored --nocapture --test-threads=1"]
fn c_arity_sweep() {
    let w = rotated_transfer_workload();
    println!(
        "\n═══ §C  FOLDING-ARITY SWEEP at (lb 6, q 19) — higher arity = fewer FRI rounds = fewer \
         in-circuit Merkle paths, but a wider fold per round ═══"
    );
    header();
    for la in [1usize, 2, 3] {
        let p = sweep_point(&w, 6, la, 19, 16);
        row(&p);
    }
}

// ===========================================================================
// §D — THE ENGINE GRID the tower has never been priced on:
//      (leaf prove cost) + K · (wrap cost), at iso-security.
// ===========================================================================

#[test]
#[ignore = "MEASUREMENT: re-mints the child once per point. --ignored --nocapture --test-threads=1"]
fn d_iso_security_engine_grid() {
    let w = rotated_transfer_workload();
    println!(
        "\n═══ §D  ISO-SECURITY GRID — every row holds the capacity ledger `lb·q + pow ≥ 130`, the \
         leaf's deployed budget. The wrap's in-circuit cost is what varies. ═══"
    );
    println!(
        "  ⚠ `lb·q + pow` is the repo's own capacity ledger (`recursion-verify/src/config.rs:174`), \
         NOT a soundness theorem. It is the budget the deployed engines are gated against."
    );
    header();
    // (log_blowup, num_queries, query_pow) with lb·q + pow >= 130
    for (lb, q, pow) in [
        (2usize, 57usize, 16usize),
        (3, 38, 16),
        (4, 29, 16),
        (5, 23, 16),
        (6, 19, 16),
        (7, 17, 16),
        (8, 15, 16),
        (10, 12, 16),
        (12, 10, 16),
    ] {
        let p = sweep_point(&w, lb, 1, q, pow);
        println!(
            "{:>3} {:>5} {:>4} {:>4} | {:>10} {:>10} {:>10} {:>10} {:>10} {:>11}   ledger {}",
            p.log_blowup,
            1usize << p.log_arity,
            p.num_queries,
            p.m,
            p.perms,
            p.horner,
            p.alu,
            p.recompose,
            p.hint,
            p.witness,
            lb * q + pow
        );
    }
}
