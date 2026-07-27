//! WHERE THE DEPLOYED KERNEL-STEP PROVE ACTUALLY SPENDS ITS CPU TIME.
//!
//! The GPU A/B harness (`tests/gpu_kernel_step_reparam_measure.rs`) reports the
//! CPU/GPU wall-clock ratio and that ZERO GPU DFTs are dispatched, but it does
//! not decompose the CPU arm. Without that decomposition "what would the LDE be
//! worth on the GPU" is a guess.
//!
//! This probe reads the split off the REAL prove with no source modification:
//! Plonky3 already carries `#[instrument]` spans on the load-bearing phases
//! (`coset_lde_batch_with_transform` in p3-dft, `build merkle tree` in
//! p3-merkle-tree, `compute quotient polynomial` in p3-batch-stark, `FRI prover`
//! in p3-fri). A tiny accumulating `Layer` sums span busy time per name, and the
//! LDE spans additionally carry their `dims`/`added_bits` fields, so the exact
//! committed matrix shapes come out too.
//!
//! Run: `cargo run --release -p dregg-circuit-prove --example lde_cpu_share_probe`

use std::collections::BTreeMap;
use std::sync::Mutex;
use std::time::{Duration, Instant};

use dregg_circuit::CellState;
use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, MemBoundaryWitness, UMemBoundaryWitness, prove_vm_descriptor2_for_config,
};
use dregg_circuit::effect_vm::Effect;
use dregg_circuit::effect_vm::trace_rotated::{
    RotatedBlockWitness, generate_rotated_effect_vm_descriptor_and_trace_wide,
    transfer_caveat_manifest,
};
use dregg_circuit::field::BabyBear;
use dregg_circuit::heap_root::HeapLeaf;
use dregg_circuit_prove::plonky3_recursion_impl::recursive::create_recursion_config_with_fri;
use dregg_turn::rotation_witness as rw;

use dregg_cell::{AuthRequired, Cell, Ledger, Permissions};

use tracing::field::{Field, Visit};
use tracing::span::{Attributes, Id};
use tracing::{Subscriber, level_filters::LevelFilter};
use tracing_subscriber::layer::{Context, Layer, SubscriberExt};
use tracing_subscriber::registry::LookupSpan;
use tracing_subscriber::util::SubscriberInitExt;

// ---------------------------------------------------------------------------
// span accumulator
// ---------------------------------------------------------------------------

static TOTALS: Mutex<Option<BTreeMap<String, (u64, Duration)>>> = Mutex::new(None);

struct Enter(Instant);
struct Label(String);

#[derive(Default)]
struct FieldGrab(String);

impl Visit for FieldGrab {
    fn record_debug(&mut self, field: &Field, value: &dyn std::fmt::Debug) {
        if !self.0.is_empty() {
            self.0.push(' ');
        }
        self.0.push_str(&format!("{}={:?}", field.name(), value));
    }
    fn record_str(&mut self, field: &Field, value: &str) {
        if !self.0.is_empty() {
            self.0.push(' ');
        }
        self.0.push_str(&format!("{}={}", field.name(), value));
    }
}

struct Accum;

impl<S> Layer<S> for Accum
where
    S: Subscriber + for<'a> LookupSpan<'a>,
{
    fn on_new_span(&self, attrs: &Attributes<'_>, id: &Id, ctx: Context<'_, S>) {
        let mut g = FieldGrab::default();
        attrs.record(&mut g);
        let name = attrs.metadata().name();
        let label = if g.0.is_empty() {
            name.to_string()
        } else {
            format!("{name} [{}]", g.0)
        };
        if let Some(span) = ctx.span(id) {
            span.extensions_mut().insert(Label(label));
        }
    }

    fn on_enter(&self, id: &Id, ctx: Context<'_, S>) {
        if let Some(span) = ctx.span(id) {
            span.extensions_mut().insert(Enter(Instant::now()));
        }
    }

    fn on_exit(&self, id: &Id, ctx: Context<'_, S>) {
        let Some(span) = ctx.span(id) else { return };
        let mut ext = span.extensions_mut();
        let Some(Enter(t0)) = ext.remove::<Enter>() else {
            return;
        };
        let dt = t0.elapsed();
        let label = ext
            .get_mut::<Label>()
            .map(|l| l.0.clone())
            .unwrap_or_else(|| span.name().to_string());
        drop(ext);
        let mut lock = TOTALS.lock().unwrap();
        if let Some(map) = lock.as_mut() {
            let e = map.entry(label).or_insert((0, Duration::ZERO));
            e.0 += 1;
            e.1 += dt;
        }
    }
}

// ---------------------------------------------------------------------------
// the deployed statement (identical fixture to gpu_kernel_step_reparam_measure)
// ---------------------------------------------------------------------------

const LOG_BLOWUP: usize = 6;
const LOG_FINAL_POLY_LEN: usize = 0;
const MAX_LOG_ARITY: usize = 3;
const COMMIT_POW_BITS: usize = 0;
const QUERY_POW_BITS: usize = 16;
const NUM_QUERIES: usize = 19;
const REPS: usize = 3;

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

fn producer_cell(balance: i64) -> Cell {
    let mut pk = [0u8; 32];
    pk[0] = 7;
    let mut cell = Cell::with_balance(pk, [0u8; 32], balance);
    cell.permissions = open_permissions();
    cell
}

fn honest_wide_transfer() -> (
    EffectVmDescriptor2,
    Vec<Vec<BabyBear>>,
    Vec<BabyBear>,
    Vec<Vec<HeapLeaf>>,
    MemBoundaryWitness,
) {
    let before_balance: i64 = 100_000;
    let amount: u64 = 50;
    let st = CellState::new(before_balance as u64, 0);
    let effects = vec![Effect::Transfer {
        amount,
        direction: 1,
    }];
    let mut ledger = Ledger::new();
    let before_cell = producer_cell(before_balance);
    let after_cell = producer_cell(before_balance - amount as i64);
    ledger.insert_cell(after_cell.clone()).unwrap();
    let receipt_log: Vec<[u8; 32]> = vec![[1u8; 32], [2u8; 32]];
    let produce = |cell: &Cell| {
        rw::produce(
            cell,
            &ledger,
            &dregg_circuit::heap_root::empty_heap_root_8(),
            &dregg_circuit::heap_root::empty_heap_root_8(),
            &dregg_turn::rotation_witness::empty_revoked_root_8(),
            &receipt_log,
            &Default::default(),
        )
    };
    let bridge =
        |w: &rw::RotationWitness| RotatedBlockWitness::new(w.pre_limbs.clone(), w.iroot).unwrap();
    let before_w = produce(&before_cell);
    let after_w = produce(&after_cell);
    let membership_teeth = (BabyBear::new(0xA11CE), BabyBear::new(0xF00D));
    let (desc, trace, dpis, map_heaps, mb) = generate_rotated_effect_vm_descriptor_and_trace_wide(
        &st,
        &effects,
        &bridge(&before_w),
        &bridge(&after_w),
        &transfer_caveat_manifest(),
        None,
        None,
        None,
        Some(membership_teeth),
    )
    .expect("the deployed wide transfer leg mints");
    (desc, trace, dpis, map_heaps, mb)
}

fn main() {
    tracing_subscriber::registry()
        .with(Accum)
        .with(LevelFilter::DEBUG)
        .init();

    let (desc, trace, dpis, map_heaps, mb) = honest_wide_transfer();
    let umem = UMemBoundaryWitness::default();
    let cfg = create_recursion_config_with_fri(
        LOG_BLOWUP,
        LOG_FINAL_POLY_LEN,
        MAX_LOG_ARITY,
        NUM_QUERIES,
        COMMIT_POW_BITS,
        QUERY_POW_BITS,
    );

    // warm-up (twiddle caches, allocator) — NOT accumulated.
    let _ = prove_vm_descriptor2_for_config(&desc, &trace, &dpis, &mb, &map_heaps, &umem, &cfg)
        .expect("warm-up prove");

    *TOTALS.lock().unwrap() = Some(BTreeMap::new());
    let mut wall = Vec::new();
    for _ in 0..REPS {
        let t0 = Instant::now();
        let _ = prove_vm_descriptor2_for_config(&desc, &trace, &dpis, &mb, &map_heaps, &umem, &cfg)
            .expect("prove");
        wall.push(t0.elapsed());
    }
    let totals = TOTALS.lock().unwrap().take().unwrap();

    wall.sort();
    let best = wall[0].as_secs_f64() * 1e3;
    let mean: f64 = wall.iter().map(|d| d.as_secs_f64()).sum::<f64>() / REPS as f64 * 1e3;
    println!("\n=== deployed kernel step, CPU arm, lb={LOG_BLOWUP} q={NUM_QUERIES} ===");
    println!("prove wall (self-verify included): best {best:.1} ms, mean {mean:.1} ms over {REPS}");
    println!("\nspan totals (busy time summed over {REPS} proves; per-prove in the last column)");
    println!(
        "{:<78} {:>6} {:>12} {:>12}",
        "span", "calls", "total ms", "per-prove ms"
    );
    let mut rows: Vec<_> = totals.into_iter().collect();
    rows.sort_by(|a, b| b.1.1.cmp(&a.1.1));
    for (name, (n, d)) in rows {
        let ms = d.as_secs_f64() * 1e3;
        if ms < 0.5 {
            continue;
        }
        println!(
            "{:<78} {:>6} {:>12.2} {:>12.2}",
            name,
            n,
            ms,
            ms / REPS as f64
        );
    }
}
