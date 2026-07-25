//! PROFILE THE FOLD: attribute the CPU-bound `prove_turn_chain_recursive` (the
//! rotated 2-turn apex fold) across its prove stages, so the GPU lever is chosen
//! from MEASURED numbers, not a prior.
//!
//! The Plonky3 prover is instrumented top-to-bottom with `tracing` spans
//! (`build merkle tree`, `coset_lde_batch`, `FRI prover`, `query phase`,
//! `commit phase`, `compute quotient`, ...). This test installs a flat-profile
//! `tracing` subscriber that accumulates EXCLUSIVE (self) wall-time per span
//! name across the whole fold, then prints a `stage | seconds | %` table.
//!
//! Self-time attribution: a per-thread stack charges the time between two span
//! events to whichever span is currently on top of that thread's stack. On the
//! driving thread the self-times sum to the outer span's wall-clock; rayon
//! worker threads that open their own spans add their parallel CPU-time (so the
//! sum can exceed wall — the % is of the summed self-time, and the raw fold
//! wall-clock is printed alongside as ground truth).
//!
//! SLOW (~5 min): one real 2-turn rotated fold. Run with:
//!   cargo test -p dregg-circuit-prove --release --test fold_profile -- --ignored --nocapture

use std::cell::{Cell, RefCell};
use std::collections::HashMap;
use std::sync::{Mutex, OnceLock};
use std::time::{Duration, Instant};

use dregg_circuit::effect_vm::{CellState, Effect};
use dregg_circuit_prove::ivc_turn_chain::{FinalizedTurn, prove_turn_chain_recursive};
use dregg_circuit_prove::joint_turn_aggregation::DescriptorParticipant;
use dregg_turn_prover::rotation_witness::mint_rotated_participant_leg;
use tracing::span::Id;
use tracing_subscriber::layer::{Context, Layer};
use tracing_subscriber::prelude::*;
use tracing_subscriber::registry::LookupSpan;

// ---- the flat profiler ------------------------------------------------------

static PROFILE: OnceLock<Mutex<HashMap<String, (Duration, u64)>>> = OnceLock::new();

fn profile() -> &'static Mutex<HashMap<String, (Duration, u64)>> {
    PROFILE.get_or_init(|| Mutex::new(HashMap::new()))
}

thread_local! {
    static STACK: RefCell<Vec<&'static str>> = const { RefCell::new(Vec::new()) };
    static LAST: Cell<Option<Instant>> = const { Cell::new(None) };
}

/// Charge the interval [LAST, now] to whichever span is on top of this thread's
/// stack, then advance LAST to now.
fn charge(now: Instant) {
    LAST.with(|l| {
        if let Some(last) = l.get() {
            STACK.with(|st| {
                if let Some(&top) = st.borrow().last() {
                    let mut p = profile().lock().unwrap();
                    p.entry(top.to_string()).or_default().0 += now.saturating_duration_since(last);
                }
            });
        }
        l.set(Some(now));
    });
}

struct FlatProfiler;

impl<S> Layer<S> for FlatProfiler
where
    S: tracing::Subscriber + for<'a> LookupSpan<'a>,
{
    fn on_enter(&self, id: &Id, ctx: Context<'_, S>) {
        let now = Instant::now();
        charge(now); // account the parent's self-time up to this boundary
        if let Some(span) = ctx.span(id) {
            let name = span.name();
            STACK.with(|st| st.borrow_mut().push(name));
            let mut p = profile().lock().unwrap();
            p.entry(name.to_string()).or_default().1 += 1;
        }
    }

    fn on_exit(&self, _id: &Id, _ctx: Context<'_, S>) {
        let now = Instant::now();
        charge(now); // this span's self-time since the last boundary
        STACK.with(|st| {
            st.borrow_mut().pop();
        });
    }
}

// ---- the fixed 2-turn rotated chain (apex_shrink_bn254_tooth.rs fixture) -----

fn open_permissions() -> dregg_cell::Permissions {
    use dregg_cell::AuthRequired;
    dregg_cell::Permissions {
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

fn producer_cell(balance: i64, nonce: u64) -> dregg_cell::Cell {
    let mut pk = [0u8; 32];
    pk[0] = 7;
    let mut cell = dregg_cell::Cell::with_balance(pk, [0u8; 32], balance);
    cell.permissions = open_permissions();
    for _ in 0..nonce {
        let _ = cell.state.increment_nonce();
    }
    cell
}

fn make_turn(balance: u64, nonce: u32) -> Result<FinalizedTurn, String> {
    let state = CellState::new(balance, nonce);
    // Keep this fixture aligned with `gpu_backend_shrink_e2e`: IncrementNonce
    // remains available while the transfer descriptor is mid-regeneration, so
    // a profiling run cannot silently turn into a zero-work SKIP.
    let effects = vec![Effect::IncrementNonce];
    let before_cell = producer_cell(balance as i64, nonce as u64);
    let after_cell = producer_cell(balance as i64, nonce as u64);
    let receipt_log: Vec<[u8; 32]> = vec![[1u8; 32], [2u8; 32]];
    let leg = mint_rotated_participant_leg(
        &state,
        &effects,
        &before_cell,
        &after_cell,
        &dregg_circuit::heap_root::empty_heap_root_8(),
        &dregg_circuit::heap_root::empty_heap_root_8(),
        &receipt_log,
        None,
    )?;
    Ok(FinalizedTurn::new(DescriptorParticipant::rotated(leg)))
}

fn the_chain() -> Result<Vec<FinalizedTurn>, String> {
    Ok(vec![make_turn(1000, 0)?, make_turn(1000, 1)?])
}

#[test]
#[ignore = "SLOW: one real 2-turn rotated fold (~minutes); run with --ignored --nocapture"]
fn profile_the_fold() {
    let subscriber = tracing_subscriber::registry().with(FlatProfiler);
    let _guard = tracing::subscriber::set_default(subscriber);

    let chain = the_chain().expect("the fixed IncrementNonce profiling chain mints");

    // Production dispatch is GPU-auto now. This profiler deliberately samples
    // the original CPU wall so `perf` and the tracing spans explain where the
    // historical inner-fold bottleneck went before the GPU cutover.
    unsafe { std::env::set_var("DREGG_GPU_RECURSION", "cpu") };
    let t0 = Instant::now();
    let whole = prove_turn_chain_recursive(&chain).expect("the fixed 2-turn chain folds");
    let wall = t0.elapsed();
    unsafe { std::env::remove_var("DREGG_GPU_RECURSION") };
    // Flush the driving thread's final charge.
    charge(Instant::now());
    std::hint::black_box(&whole);

    // Snapshot + sort by self-time.
    let map = profile().lock().unwrap().clone();
    let mut rows: Vec<(String, Duration, u64)> =
        map.into_iter().map(|(k, (d, c))| (k, d, c)).collect();
    rows.sort_by(|a, b| b.1.cmp(&a.1));

    let total_self: Duration = rows.iter().map(|r| r.1).sum();

    println!("\n=== FOLD PROFILE (prove_turn_chain_recursive, 2-turn rotated) ===");
    println!("fold wall-clock        : {wall:?}");
    println!("summed span self-time  : {total_self:?}  (>wall by the rayon parallel factor)");
    println!(
        "\n{:<34} {:>10} {:>8} {:>9}",
        "span (stage)", "self (s)", "% self", "count"
    );
    for (name, d, c) in &rows {
        let pct = if total_self.as_secs_f64() > 0.0 {
            100.0 * d.as_secs_f64() / total_self.as_secs_f64()
        } else {
            0.0
        };
        if d.as_secs_f64() < 0.05 && *c < 50 {
            continue; // hide the noise floor
        }
        println!("{name:<34} {:>10.2} {pct:>7.1}% {c:>9}", d.as_secs_f64());
    }

    // Roll the child spans up into the GPU-relevant buckets so the lever is
    // obvious. Use exact names: the Radix2Dit implementation records almost
    // all of its time under butterfly/bit-reversal children (not under the
    // parent `coset_lde_batch_with_transform` span), while FRI's opening
    // reduction uses `reduce matrix quotient`, which must not be confused with
    // AIR quotient-polynomial evaluation.
    let bucket = |names: &[&str]| -> Duration {
        rows.iter()
            .filter(|(n, _, _)| names.iter().any(|s| n == s))
            .map(|(_, d, _)| *d)
            .sum()
    };
    let dft = bucket(&[
        "coset_lde_batch_with_transform",
        "coset_dft_oop",
        "coset_dft",
        "first_half_general_oop",
        "first_half_general",
        "second_half_general",
        "first_half",
        "second_half",
        "reverse_matrix_index_bits",
        "idft final poly",
    ]);
    let merkle = bucket(&["build merkle tree", "first digest layer"]);
    let fri = bucket(&[
        "FRI prover",
        "query phase",
        "commit phase",
        "fold_matrix",
        "compress mat",
        "reduce matrix quotient",
        "columnwise_dot_product",
        "compute opened values with Lagrange interpolation",
        "compute_inverse_denominators",
    ]);
    let quotient = bucket(&[
        "compute quotient",
        "compute quotient polynomial",
        "infer constraint degree",
        "evaluate constraints symbolically",
    ]);
    println!("\n--- GPU-lever buckets (substring roll-up of the above) ---");
    let show = |label: &str, d: Duration| {
        let pct = if total_self.as_secs_f64() > 0.0 {
            100.0 * d.as_secs_f64() / total_self.as_secs_f64()
        } else {
            0.0
        };
        println!("  {label:<28} {:>8.2}s  {pct:>5.1}%", d.as_secs_f64());
    };
    show("DFT / LDE (GpuDft)", dft);
    show("Merkle (GpuBabyBearMmcs)", merkle);
    show("FRI (commit+query+fold)", fri);
    show("quotient/constraint eval", quotient);
}
