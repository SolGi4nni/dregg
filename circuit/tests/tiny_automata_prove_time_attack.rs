//! ⚑⚑ **SUPERSEDED AXIS (2026-07-29) — READ BEFORE QUOTING ANY PER-INSTANCE NUMBER BELOW.**
//!
//! Every figure in this file that prices an `Ir2Air::ExactPublicRow` BATCH INSTANCE, or that
//! treats `MAX_EXACT_PUBLIC_ROWS = 128` as a reachability limit, was measured against a
//! realization that no longer exists. `Ir2Air::ExactPublicTable` carries a whole Lean-emitted
//! manifest as ONE multiplicity-bearing instance with the rows in a preprocessed matrix — which
//! is the shape this file's own CONTROL (shape B, the range/byte table) always had. So the
//! deployed exact-public shape costs 2 instances at every `(k, n, m)`, the caps are `2^21` rows /
//! `2^25` cells, and the points this file reported as INEXPRESSIBLE now prove. The trace-row,
//! FRI-knob and Poseidon2-profile measurements are UNAFFECTED and still stand; the per-instance
//! and cap-reachability ones are HISTORY. The tests themselves have been updated and are green.
//!
//! ⚠⚠⚠ HEADLINE CORRECTION — READ BEFORE QUOTING ANY PERCENTAGE FROM THIS FILE.
//!
//! An independent re-verification (this harness's own verify agent died before running, so the
//! numbers below went into a commit message unchecked) reproduced §2/§3/§4 EXACTLY — several
//! figures to the byte — and REFUTED the §1 headline and both of its framings:
//!
//! 1. "97.9% Merkle" DOES NOT REPRODUCE and is self-contradictory: 97.9% + the file's own
//!    4.6–8.5% PoW + 1.3% LDE exceeds 100%. Three runs of the same point gave Merkle sums of
//!    78.8% / 89.5% / 97.9%. Load-robust user-CPU answer: **Merkle ≈ 90% ± 4**. Cause: the
//!    instrument claim retracted in §1 below.
//!
//! 2. ⚑ "THE PER-AIR-INSTANCE HYPOTHESIS WAS REFUTED" IS BACKWARDS — IT WAS CONFIRMED.
//!    `instance_airs` (circuit/src/descriptor_ir2.rs:5916-5925) DOES push one
//!    `Ir2Air::ExactPublicRow` per declared row; verified at runtime, `inst=129` for A k=4 n=32
//!    (= 1 + 4·32) and `inst=65` for n=16. The headline was measured on **shape B**, which uses a
//!    `sem:"range"` table and therefore has **2 instances BY CONSTRUCTION for every (k,n)** — so
//!    "per-instance overhead ~0 because there are 2 instances" is CIRCULAR: shape B has no
//!    per-row instances to cost. Marginal cost where it EXISTS is a measured 0.11 ms/instance.
//!
//! 3. ⚑ AND SHAPE B IS NOT THE DEPLOYED CARRIER. Shape A is: it ships by name as
//!    `dregg-dfa-routing-table::exact-public-v1` (descriptor_by_name.rs:84). The deployed shape is
//!    **DFT-BOUND, NOT HASH-BOUND** — at A k=4 n=32, `coset_dft_oop` 48.9%, LDE 11.5%, with Merkle
//!    at **8.4%**. It also CANNOT REACH the headline point at all: `MAX_EXACT_PUBLIC_ROWS = 128`
//!    (descriptor_ir2.rs:378) versus k·n = 4096. Extrapolating the measured 0.11 ms/instance, the
//!    deployed shape at k=4 n=1024 would pay ~450 ms of per-instance overhead — 3× the ENTIRE
//!    shape-B prove.
//!
//! 4. The blowup cross-check REPRODUCES (my grid: 6.40/10.80/19.20/36.80/71.60/138.40 ms at
//!    B=2..64) but does NOT isolate commitment: `coset_lde_batch_with_transform` does B separate
//!    size-n coset DFTs, so LDE is EXACTLY linear in B, as are the FRI commit-phase folds and
//!    their per-layer Merkle trees. Blowup-proportionality is real; "and nothing but commitment"
//!    is not licensed by it. (The ~1% LDE figure survives on a DIFFERENT argument — an n-sweep at
//!    fixed B, where T/n is flat-to-decreasing across 16×.) Also "98.2% of the DEPLOYED prove" is
//!    wrong: that fit is at pow=0, and the deployed config is pow=16 → 90.1–94.1%.
//!
//! ⇒ THE SURVIVING CONCLUSION, correctly scoped: the SHARED-TABLE (shape B) prove at n=1024 is
//!   Poseidon2-Merkle-bound at ~90%. The DEPLOYED per-row shape is DFT- and instance-bound. Any
//!   "make it megafast" work must say WHICH SHAPE it is optimising — they have opposite profiles.
//!
//! # PROVE-TIME ATTACK — where do the 175 ms at `n = 1024` ACTUALLY go?
//!
//! `tiny_automata_prover_shape_measure.rs` established the WALL numbers for a 4-automaton
//! composition on the deployed IR-v2 prover (production `ir2_config`: `log_blowup = 6,
//! 19 queries, 16 PoW bits`) and fit `T(n,k) ≈ G + F·n + c·k·n`. It did NOT say which
//! prover stage the `F·n` term lives in. This file ATTRIBUTES it, and then attacks it.
//!
//! Two instruments, both on the SAME descriptors that file proves (and every point measured
//! here is PROVED and VERIFIED before its number is printed — a cost is only ever quoted for
//! an object that has a satisfying witness):
//!
//! 1. **`SpanProfiler`** — a ~120-line `tracing::Subscriber` that accumulates INCLUSIVE and
//!    SELF wall time per span NAME across the plonky3 prover's own `#[instrument]` /
//!    `info_span!` / `debug_span!` sites (`p3-batch-stark::prove_batch`, `p3-fri`'s
//!    `commit`/`FRI prover`/`commit phase`/`query phase`, `p3-merkle-tree`'s `build merkle
//!    tree`, the per-instance `infer log of constraint degree` and `compute quotient`).
//!    No new dependency: `tracing` is already a `dregg-circuit` dependency.
//!
//!    ⚠⚠ RETRACTED — THIS PARAGRAPH USED TO CLAIM: "the FRI proof-of-work grind sits between
//!    `commit phase` and `query phase` inside `prove_fri` WITHOUT a span of its own, so it lands
//!    in `FRI prover` SELF time." THAT IS FALSE, and it is the root cause of a wrong headline.
//!    `GrindingChallenger::grind` carries `#[instrument(name = "grind for proof-of-work witness",
//!    skip_all)]` (plonky3 `challenger/src/grinding_challenger.rs:106` and `:293`) — it prints as
//!    its OWN line in every profile, and `FRI prover` self-time is ~0 (below the 0.05 ms print
//!    threshold in an isolated run).
//!
//!    ⚠ WORSE, THE SPAN MEASURES BLOCKING WALL, NOT CPU: `grind` is
//!    `…into_par_iter().find_any(…)`, so the thread entering the span BLOCKS on a rayon worker.
//!    Under co-tenant load its wall inflated 66× (444 ms wall for 6.7 ms of CPU) with large
//!    run-to-run variance — which is exactly the knob that moved the "Merkle sum" across
//!    78.8% / 89.5% / 97.9% on three runs of the same point. A 3-significant-figure split is NOT
//!    a supportable reading of this instrument.
//!
//!    ⚠ AND THE DOCUMENTED RUN COMMAND BELOW CORRUPTS ITS OWN PROFILE: `SpanProfiler` is a
//!    process-global singleton with a global `on` flag and a shared accumulator, while libtest
//!    runs the tests CONCURRENTLY. Run as documented it reports `prove_batch` count 2 for ONE
//!    profiled prove, 13,176 `coset_dft_oop` calls against 504 isolated, self-percentages summing
//!    past 250%, and a NEGATIVE marginal per-instance cost. Use `--test-threads=1`.
//!
//!    LOAD-ROBUST NUMBERS (user CPU, independent re-measurement) at `B k=4 n=1024`, production:
//!    total ~145 ms; PoW grind 4.2–6.7 ms (3–5%); blowup-proportional 136.5 ms (94.1%);
//!    LDE/DFT ~1 ms central (≤ ~7% at 1σ); **Merkle ≈ 90% ± 4, NOT 97.9%**.
//!
//! 2. **The FRI knob grid at security parity.** `ir2_config`'s own doc-comment says the
//!    `(6, 19)` point was chosen because "the tables are 2³–2⁸ rows, so the prover-side LDE
//!    cost of high blowup is milliseconds". At `n = 2^10` that premise is FALSE: `log_blowup
//!    = 6` means every committed matrix is Reed–Solomon-extended and Merkle-hashed over a
//!    64× domain. This grid walks the ISO-BUDGET line `num_queries · log_blowup = 114`
//!    (the same arithmetic `ir2_config`'s doc states for both its conjectured-capacity and
//!    its proven/Johnson figure — the AUTHORITY on those numbers is the Lean ledger
//!    `@[export] dregg_fri_ledger` via `circuit-prove/tests/fri_params_soundness_budget.rs`,
//!    NOT this file) and reports prove ms AND wire bytes at each point.
//!
//! Nothing here changes a production parameter, and no non-default config ever reaches the
//! wire (`prove_vm_descriptor2_with_config` is `#[doc(hidden)]` measurement-only).
//!
//! ## ⚑ WHAT IT MEASURED (2026-07-25, this box, USER CPU per prove, `RAYON_NUM_THREADS=1`)
//!
//! The box was at load average ~360 on 12 cores, so WALL numbers taken in-process are
//! ~19× inflated and are NOT reported; every number below is `(user(reps=R) −
//! user(reps=0))/R` from `attack_one_point` under `/usr/bin/time -p`. Reps 20–60.
//!
//! **(1) Where the 175 ms goes at `k = 4, n = 1024` (shared-table shape, 2 instances).**
//! Production `(6, 19, 16)` = **153 ms user CPU** (the committed harness's 175 ms wall).
//! The span profile says `first digest layer` 55.9% + `build merkle tree` 42.0% =
//! **97.9% Poseidon2 Merkle hashing**; LDE/DFT ~1.3%; LogUp permutation generation,
//! quotient, FRI folding and the FRI query phase together < 0.2%; per-AIR-instance
//! overhead ~0 (there are 2 instances). The PoW grind is 7–13 ms, size-independent.
//! INDEPENDENT CROSS-CHECK, no profiler: hold everything but `log_blowup` fixed
//! (`pow = 0`, `n = 1024`, `k = 4`) and the blowup FACTOR `B = 2^log_blowup` gives
//!
//! ```text
//!   B      2      4      8     16     32     64
//!  ms   6.80  11.20  18.80  36.80  71.20 140.40      T(B) = 2.155·B + 2.49  (fit to ±5%)
//! ```
//!
//! i.e. **98.2% of the deployed prove time is strictly proportional to the blowup
//! factor** — the signature of commit-over-the-blown-up-domain, and nothing else.
//! `ir2_config`'s premise ("the tables are 2³–2⁸ rows, so the prover-side LDE cost of
//! high blowup is milliseconds") is TRUE at `n = 16` and FALSE by two orders at `n = 2^10`.
//!
//! **(2) The per-batch-instance cost of the DEPLOYED exact-public shape.** Identical main
//! trace, `pow = 0`, production FRI: `A k=4 n=32` (129 instances) = 20.00 ms vs
//! `B k=4 n=32` (2 instances) = 6.33 ms ⇒ **0.108 ms per extra `ExactPublicRow` instance**;
//! at `n = 16` (65 vs 2 instances) 10.83 vs 3.33 ms ⇒ **0.119 ms**. So the run-table
//! discipline's "one AIR instance per declared row" costs ≈ **0.11·n ms**, and at
//! `k = 4, n = 32` it is 68% of that shape's whole prove. Its profile is completely
//! different from shape B's: 45.4% `coset_dft_oop`, 19.7% `reverse_matrix_index_bits`,
//! 18.5% `coset_lde_batch_with_transform` — 32,508 tiny-matrix DFT calls for 129
//! instances — with Merkle at 0.4%. BOTH hypotheses are true, in different regimes.
//!
//! **(3) The two fixes, at the ONE grid point both shapes reach (`k = 4, n = 32`, same
//! main trace, same lane statement, `pow = 0`):**
//!
//! ```text
//!   deployed  A @ (blowup 6, 19 q)   20.00 ms   272,901 B
//!   shape fix B @ (blowup 6, 19 q)    6.33 ms    52,440 B    3.2x faster, 5.2x smaller
//!   + config  B @ (blowup 2, 57 q)    0.67 ms    99,450 B   ~20-30x faster, 2.7x smaller
//!     ⚠ the speedup figure is AT THE QUANTIZATION FLOOR — 0.67 ms rests on a single 0.02 s reading
//!     at R=30, i.e. one tick. An independent re-run read 1.000 ms → 20.7x. Do not carry three
//!     significant figures here; the wire size (99,450 B) reproduced EXACTLY and is solid.
//! ```
//!
//! The config change ALONE is a bad trade for shape A (`A @ (2,57)` = 6.00 ms but
//! 668,095 B — 129 instances × 57 queries of openings), and at `n = 1024` on shape B it
//! costs bytes for time at parity: `(6,19)` 153 ms / 76.1 KiB, `(3,38)` 23.5 ms /
//! 119.8 KiB, `(1,114)` 17.0 ms / 294.6 KiB.
//!
//! **(4) An incidental finding.** The 16-bit FRI query PoW is a FIXED geometric draw PER
//! `(descriptor, witness)` — the prover is deterministic, so the same descriptor grinds the
//! same number of hashes every time. Measured spread across five points: 0.67 ms
//! (`B k=4 n=16`), 6.33 ms (`A k=4 n=32`), 7.75 ms (`B k=4 n=256`), ~13 ms
//! (`B k=4 n=1024`), **36 ms** (`B k=4 n=32`, where it is 85% of the whole prove). A
//! descriptor can be an order of magnitude unluckier than the 2^16-hash mean and stay
//! that way forever. It does NOT scale with the trace.
//!
//! Run (release; debug times would be lies, and `debug_assertions` also switches on
//! plonky3's in-prover `check_constraints`, which is itself most of a debug prove):
//! ```text
//! cargo test -p dregg-circuit --release --test tiny_automata_prove_time_attack -- --nocapture \
//!   --test-threads=1
//!
//! ⚠ `--test-threads=1` IS MANDATORY, NOT A PREFERENCE. `SpanProfiler` is a process-global
//! singleton with a global `on` flag and one shared accumulator, and libtest runs these tests
//! CONCURRENTLY by default. Without it the profile is silently cross-contaminated: an independent
//! re-verification running exactly the old command line got `prove_batch` count 2 for ONE profiled
//! prove, 13,176 `coset_dft_oop` calls against 504 isolated, self-percentages summing past 250%,
//! and a NEGATIVE marginal per-instance cost. The old command line (without the flag) is what
//! produced this file's retracted 97.9% headline.
//! ```

use std::cell::RefCell;
use std::collections::HashMap;
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::sync::{Mutex, OnceLock};
use std::time::Instant;

use tracing::span::{Attributes, Id, Record};
use tracing::subscriber::Interest;
use tracing::{Event, Metadata, Subscriber};

use dregg_circuit::descriptor_ir2::{
    IR2_FRI_LOG_FINAL_POLY_LEN, IR2_FRI_MAX_LOG_ARITY, IR2_FRI_QUERY_POW_BITS, MemBoundaryWitness,
    TID_RANGE, parse_vm_descriptor2, prove_vm_descriptor2, prove_vm_descriptor2_with_config,
    verify_vm_descriptor2, verify_vm_descriptor2_with_config,
};
use dregg_circuit::field::BabyBear;
use dregg_circuit::plonky3_prover::{DreggStarkConfig, create_config_with_fri};

// ============================================================================
// The descriptors — VERBATIM shapes from `tiny_automata_prover_shape_measure.rs`
// ============================================================================

/// `.custom 30` = wire id 35, exactly as `DfaRoutingTableEmit.TRT_TID`.
const TRT_TID: usize = 35;

fn sym_at(lane: usize, row: usize) -> u32 {
    let x = (lane as u64).wrapping_mul(0x9E37_79B9_7F4A_7C15)
        ^ (row as u64).wrapping_mul(0xBF58_476D_1CE4_E5B9);
    ((x >> 33) & 1) as u32
}

fn lane_chain(lane: usize, n: usize) -> Vec<(u32, u32, u32)> {
    let mut cur = 0u32;
    let mut out = Vec::with_capacity(n);
    for row in 0..n {
        let sym = sym_at(lane, row);
        let next = cur ^ sym;
        out.push((cur, sym, next));
        cur = next;
    }
    out
}

/// Shape A: the DEPLOYED `exact_public_rows` table routing. `instance_airs` pushes ONE
/// `Ir2Air::ExactPublicRow` batch instance PER DECLARED MANIFEST ROW, so the batch carries
/// `1 + k·n·m` instances. `MAX_EXACT_PUBLIC_ROWS = 128` caps `k·n·m ≤ 128`.
fn shape_a_json_m(k: usize, n: usize, m: usize) -> String {
    let mut manifest: Vec<String> = Vec::with_capacity(k * n * m);
    for lane in 0..k {
        for (c, s, x) in lane_chain(lane, n) {
            for _ in 0..m {
                manifest.push(format!("[{c},{s},{x}]"));
            }
        }
    }
    let mut constraints: Vec<String> = Vec::new();
    for j in 0..k {
        let (c, s, x) = (3 * j, 3 * j + 1, 3 * j + 2);
        for _ in 0..m {
            constraints.push(format!(
                "{{\"t\":\"lookup\",\"table\":{TRT_TID},\"tuple\":[{{\"t\":\"var\",\"v\":{c}}},{{\"t\":\"var\",\"v\":{s}}},{{\"t\":\"var\",\"v\":{x}}}]}}"
            ));
        }
        constraints.push(format!(
            "{{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{{\"t\":\"add\",\"l\":{{\"t\":\"nxt\",\"c\":{c}}},\"r\":{{\"t\":\"mul\",\"l\":{{\"t\":\"const\",\"v\":-1}},\"r\":{{\"t\":\"loc\",\"c\":{x}}}}}}}}}"
        ));
        constraints.push(format!(
            "{{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":{c},\"pi_index\":{}}}",
            2 * j
        ));
        constraints.push(format!(
            "{{\"t\":\"pi_binding\",\"row\":\"last\",\"col\":{x},\"pi_index\":{}}}",
            2 * j + 1
        ));
    }
    format!(
        "{{\"name\":\"attack-shape-a-k{k}-n{n}-m{m}\",\"ir\":2,\"trace_width\":{},\"public_input_count\":{},\
         \"tables\":[{{\"id\":{TRT_TID},\"name\":\"dfa_transition_table\",\"arity\":3,\"sem\":\"exact_public_rows\",\"rows\":[{}]}}],\
         \"constraints\":[{}],\"hash_sites\":[],\"ranges\":[]}}",
        3 * k,
        2 * k,
        manifest.join(","),
        constraints.join(",")
    )
}

fn shape_a_json(k: usize, n: usize) -> String {
    shape_a_json_m(k, n, 1)
}

/// Shape B: the SHARED multiplicity-carrying table — 2 batch instances for every `(k, n, m)`.
fn shape_b_json_m(k: usize, n: usize, m: usize) -> String {
    let mut constraints: Vec<String> = Vec::new();
    for j in 0..k {
        let (c, s, x) = (3 * j, 3 * j + 1, 3 * j + 2);
        for _ in 0..m {
            constraints.push(format!(
                "{{\"t\":\"lookup\",\"table\":{TID_RANGE},\"tuple\":[{{\"t\":\"var\",\"v\":{s}}}]}}"
            ));
        }
        constraints.push(format!(
            "{{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{{\"t\":\"add\",\"l\":{{\"t\":\"nxt\",\"c\":{c}}},\"r\":{{\"t\":\"mul\",\"l\":{{\"t\":\"const\",\"v\":-1}},\"r\":{{\"t\":\"loc\",\"c\":{x}}}}}}}}}"
        ));
        constraints.push(format!(
            "{{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":{c},\"pi_index\":{}}}",
            2 * j
        ));
        constraints.push(format!(
            "{{\"t\":\"pi_binding\",\"row\":\"last\",\"col\":{x},\"pi_index\":{}}}",
            2 * j + 1
        ));
    }
    format!(
        "{{\"name\":\"attack-shape-b-k{k}-n{n}-m{m}\",\"ir\":2,\"trace_width\":{},\"public_input_count\":{},\
         \"tables\":[{{\"id\":{TID_RANGE},\"name\":\"range\",\"arity\":1,\"sem\":\"range\",\"bits\":4}}],\
         \"constraints\":[{}],\"hash_sites\":[],\"ranges\":[]}}",
        3 * k,
        2 * k,
        constraints.join(",")
    )
}

fn shape_b_json(k: usize, n: usize) -> String {
    shape_b_json_m(k, n, 1)
}

fn trace_and_pis(k: usize, n: usize) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    let chains: Vec<Vec<(u32, u32, u32)>> = (0..k).map(|lane| lane_chain(lane, n)).collect();
    let mut rows = Vec::with_capacity(n);
    for row in 0..n {
        let mut r = Vec::with_capacity(3 * k);
        for chain in &chains {
            let (c, s, x) = chain[row];
            r.push(BabyBear::new(c));
            r.push(BabyBear::new(s));
            r.push(BabyBear::new(x));
        }
        rows.push(r);
    }
    let mut pis = Vec::with_capacity(2 * k);
    for chain in &chains {
        pis.push(BabyBear::new(chain[0].0));
        pis.push(BabyBear::new(chain[n - 1].2));
    }
    (rows, pis)
}

// ============================================================================
// SpanProfiler — a minimal `tracing::Subscriber` that times plonky3's own spans
// ============================================================================

#[derive(Default, Clone, Copy)]
struct Acc {
    count: u64,
    incl_ns: u128,
    self_ns: u128,
}

struct SpanProfiler {
    next_id: AtomicU64,
    names: Mutex<HashMap<u64, &'static str>>,
    acc: Mutex<HashMap<&'static str, Acc>>,
    on: AtomicBool,
}

thread_local! {
    /// (span id, entered-at, total time charged to CHILDREN of this span)
    static STACK: RefCell<Vec<(u64, Instant, u128)>> = const { RefCell::new(Vec::new()) };
}

/// A ZST handle: `set_global_default` wants `Subscriber + Send + Sync + 'static` BY VALUE, so
/// the trait is implemented on this and every method delegates to the process-wide singleton.
#[derive(Clone, Copy)]
struct Handle;

static PROF: OnceLock<SpanProfiler> = OnceLock::new();

impl SpanProfiler {
    fn get() -> &'static SpanProfiler {
        let p = PROF.get_or_init(|| SpanProfiler {
            next_id: AtomicU64::new(1),
            names: Mutex::new(HashMap::new()),
            acc: Mutex::new(HashMap::new()),
            on: AtomicBool::new(false),
        });
        // `set_global_default` may only succeed once per process; every profiled scope goes
        // through this one subscriber, gated by `on`. `.ok()` because a sibling `#[test]`
        // thread may have installed it already.
        let _ = tracing::subscriber::set_global_default(Handle);
        p
    }

    fn reset(&self) {
        self.acc.lock().unwrap().clear();
    }

    fn snapshot(&self) -> Vec<(&'static str, Acc)> {
        let mut v: Vec<(&'static str, Acc)> = self
            .acc
            .lock()
            .unwrap()
            .iter()
            .map(|(k, a)| (*k, *a))
            .collect();
        v.sort_by(|a, b| b.1.self_ns.cmp(&a.1.self_ns));
        v
    }
}

impl Subscriber for Handle {
    /// Deliberately `sometimes()`: the default `register_callsite` CACHES the answer of
    /// `enabled`, which would freeze the `on` gate at whatever it was on first use.
    fn register_callsite(&self, _m: &'static Metadata<'static>) -> Interest {
        Interest::sometimes()
    }

    fn enabled(&self, _m: &Metadata<'_>) -> bool {
        PROF.get().is_some_and(|p| p.on.load(Ordering::Relaxed))
    }

    fn new_span(&self, attrs: &Attributes<'_>) -> Id {
        let p = SpanProfiler::get();
        let id = p.next_id.fetch_add(1, Ordering::Relaxed);
        p.names.lock().unwrap().insert(id, attrs.metadata().name());
        Id::from_u64(id)
    }

    fn record(&self, _: &Id, _: &Record<'_>) {}
    fn record_follows_from(&self, _: &Id, _: &Id) {}
    fn event(&self, _: &Event<'_>) {}

    fn enter(&self, id: &Id) {
        STACK.with(|s| s.borrow_mut().push((id.into_u64(), Instant::now(), 0)));
    }

    fn exit(&self, id: &Id) {
        let Some((sid, at, child_ns)) = STACK.with(|s| s.borrow_mut().pop()) else {
            return;
        };
        debug_assert_eq!(sid, id.into_u64());
        let p = SpanProfiler::get();
        let incl = at.elapsed().as_nanos();
        let self_ns = incl.saturating_sub(child_ns);
        let name = *p.names.lock().unwrap().get(&sid).unwrap_or(&"<unnamed>");
        {
            let mut acc = p.acc.lock().unwrap();
            let e = acc.entry(name).or_default();
            e.count += 1;
            e.incl_ns += incl;
            e.self_ns += self_ns;
        }
        STACK.with(|s| {
            if let Some(parent) = s.borrow_mut().last_mut() {
                parent.2 += incl;
            }
        });
    }
}

/// Prove `json` ONCE with the profiler armed and print the per-span split. The point is
/// proved and verified under the production config FIRST, unprofiled, so the number is a
/// number for an object with a satisfying witness.
fn profile_point(label: &str, json: &str, k: usize, n: usize) {
    let desc = parse_vm_descriptor2(json).expect("descriptor parses");
    let (trace, pis) = trace_and_pis(k, n);
    let mem = MemBoundaryWitness::default();
    let heaps: Vec<Vec<dregg_circuit::heap_root::HeapLeaf>> = vec![];

    // WITNESS LEG: this descriptor + trace really do prove and really do verify.
    let warm = prove_vm_descriptor2(&desc, &trace, &pis, &mem, &heaps)
        .unwrap_or_else(|e| panic!("{label} k={k} n={n} must prove: {e}"));
    verify_vm_descriptor2(&desc, &warm, &pis)
        .unwrap_or_else(|e| panic!("{label} k={k} n={n} must verify: {e:?}"));
    let instances = warm.degree_bits.len();
    drop(warm);

    let p = SpanProfiler::get();
    p.reset();
    p.on.store(true, Ordering::Relaxed);
    let t0 = Instant::now();
    let proof = prove_vm_descriptor2(&desc, &trace, &pis, &mem, &heaps).expect("proves");
    let total_ms = t0.elapsed().as_secs_f64() * 1000.0;
    p.on.store(false, Ordering::Relaxed);
    std::hint::black_box(&proof);

    println!(
        "\n== PROFILE {label} k={k} n={n} inst={instances} main_w={} :: profiled prove = {total_ms:.2} ms ==",
        desc.trace_width
    );
    println!(
        "   {:<38} {:>6}  {:>10}  {:>10}  {:>6}",
        "span", "count", "incl ms", "self ms", "self %"
    );
    for (name, a) in p.snapshot() {
        let self_ms = a.self_ns as f64 / 1e6;
        if self_ms < 0.05 {
            continue;
        }
        println!(
            "   {:<38} {:>6}  {:>10.2}  {:>10.2}  {:>5.1}%",
            name,
            a.count,
            a.incl_ns as f64 / 1e6,
            self_ms,
            100.0 * self_ms / total_ms
        );
    }
}

// ============================================================================
// (1) WHERE THE TIME GOES
// ============================================================================

/// The headline point (`k = 4`, `n = 1024`, the shared-table shape — the deployed
/// exact-public shape CANNOT reach it, `k·n = 4096 > 128`), plus the smaller rungs and the
/// exact-public shape at its own ceiling.
#[test]
fn where_the_time_goes() {
    println!("== (1) PHASE ATTRIBUTION at production ir2_config (blowup 6, 19 queries, 16 PoW) ==");
    for n in [256usize, 1024] {
        profile_point("B", &shape_b_json(4, n), 4, n);
    }
    // Shape A at its ceiling: k=4, n=32 => 129 batch instances.
    profile_point("A", &shape_a_json(4, 32), 4, 32);
    // The SAME trace under the shared-table shape: 2 instances. The delta is per-instance.
    profile_point("B", &shape_b_json(4, 32), 4, 32);
}

// ============================================================================
// (2) THE PER-INSTANCE COST, isolated at a FIXED main trace
// ============================================================================

fn best_prove_ms(json: &str, k: usize, n: usize, reps: usize) -> (f64, usize, usize) {
    let desc = parse_vm_descriptor2(json).expect("descriptor parses");
    let (trace, pis) = trace_and_pis(k, n);
    let mem = MemBoundaryWitness::default();
    let heaps: Vec<Vec<dregg_circuit::heap_root::HeapLeaf>> = vec![];
    let warm = prove_vm_descriptor2(&desc, &trace, &pis, &mem, &heaps).expect("proves");
    verify_vm_descriptor2(&desc, &warm, &pis).expect("verifies");
    let instances = warm.degree_bits.len();
    let bytes = postcard::to_allocvec(&warm).expect("postcard").len();
    let mut best = f64::INFINITY;
    for _ in 0..reps {
        let t0 = Instant::now();
        let proof = prove_vm_descriptor2(&desc, &trace, &pis, &mem, &heaps).expect("proves");
        let ms = t0.elapsed().as_secs_f64() * 1000.0;
        std::hint::black_box(&proof);
        best = best.min(ms);
    }
    (best, instances, bytes)
}

/// The DECLARED-ROW axis in TIME. `k = 1, n = 16` is held bit-identical while `m` multiplies
/// the declared manifest (16 → 128 rows).
///
/// ⚑ **2026-07-29: THE QUANTITY THIS TEST WAS BUILT TO MEASURE NO LONGER EXISTS.** It used to
/// report `d(prove ms)/d(instances)` — the marginal cost of one extra `ExactPublicRow` batch
/// instance — because the manifest cost one instance per declared ROW (16 → 128 rows ⇒ 17 → 129
/// instances). `Ir2Air::ExactPublicTable` makes a manifest ONE multiplicity-bearing instance, the
/// shape shape B (the range/byte table) always had, so BOTH columns are 2 instances at every `m`
/// and the marginal-per-instance slope is over a zero-length axis. What remains measurable is the
/// A−B time gap at fixed `m`: the residual cost of carrying the declared rows as TABLE rows.
#[test]
fn per_instance_cost() {
    println!("\n== (2) MARGINAL COST OF ONE BATCH INSTANCE (fixed trace k=1 n=16) ==");
    let reps = 7;
    let mut pts: Vec<(usize, usize, f64, f64)> = Vec::new();
    for m in [1usize, 2, 4, 8] {
        let (a_ms, a_inst, a_bytes) = best_prove_ms(&shape_a_json_m(1, 16, m), 1, 16, reps);
        let (b_ms, b_inst, b_bytes) = best_prove_ms(&shape_b_json_m(1, 16, m), 1, 16, reps);
        assert_eq!(
            a_inst, 2,
            "the manifest is ONE instance now, not one per declared row"
        );
        assert_eq!(b_inst, 2);
        println!(
            "   m={m:<2} declared={:<4} A inst={a_inst:<4} A={a_ms:>8.2} ms {a_bytes:>7} B  |  B inst={b_inst} B={b_ms:>7.2} ms {b_bytes:>7} B  |  A-B={:>8.2} ms",
            16 * m,
            a_ms - b_ms
        );
        pts.push((a_inst, b_inst, a_ms, b_ms));
    }
    let (_, _, a0, b0) = pts[0];
    let (_, _, a1, b1) = pts[pts.len() - 1];
    println!(
        "   -> the INSTANCE axis is now zero-length (A inst = B inst = 2 at every m); the \
         declared-row cost that remains is A-B = {:.2} ms at m=1 and {:.2} ms at m=8",
        a0 - b0,
        a1 - b1
    );
}

// ============================================================================
// (3) THE FRI KNOB GRID — the shape change that actually attacks `F·n`
// ============================================================================

struct GridPoint {
    log_blowup: usize,
    num_queries: usize,
}

/// The ISO-BUDGET line: `num_queries · log_blowup = 114` (⇒ the conjectured-capacity figure
/// `114 + 16 = 130` and the proven/Johnson figure `57 + 16 = 73` that `ir2_config`'s
/// doc-comment states are IDENTICAL at every point). The Lean ledger is the authority on
/// those numbers, not this file — this file measures TIME and BYTES.
const GRID: &[GridPoint] = &[
    GridPoint {
        log_blowup: 6,
        num_queries: 19,
    }, // the DEPLOYED point
    GridPoint {
        log_blowup: 3,
        num_queries: 38,
    },
    GridPoint {
        log_blowup: 2,
        num_queries: 57,
    },
    GridPoint {
        log_blowup: 1,
        num_queries: 114,
    },
];

fn grid_measure(label: &str, json: &str, k: usize, n: usize, reps: usize) {
    let desc = parse_vm_descriptor2(json).expect("descriptor parses");
    let (trace, pis) = trace_and_pis(k, n);
    let mem = MemBoundaryWitness::default();
    let heaps: Vec<Vec<dregg_circuit::heap_root::HeapLeaf>> = vec![];
    println!("\n-- {label} k={k} n={n} --");
    println!(
        "   {:>6} {:>8} {:>4}  {:>10}  {:>10}  {:>9}",
        "blowup", "queries", "pow", "prove ms", "wire B", "KiB"
    );
    for gp in GRID {
        for pow in [IR2_FRI_QUERY_POW_BITS, 0] {
            let cfg: DreggStarkConfig = create_config_with_fri(
                gp.log_blowup,
                IR2_FRI_LOG_FINAL_POLY_LEN,
                IR2_FRI_MAX_LOG_ARITY,
                gp.num_queries,
                pow,
            );
            let warm = prove_vm_descriptor2_with_config(&desc, &trace, &pis, &mem, &heaps, &cfg)
                .unwrap_or_else(|e| panic!("{label} blowup={} must prove: {e}", gp.log_blowup));
            // WITNESS LEG at EVERY grid point: the measured object verifies.
            verify_vm_descriptor2_with_config(&desc, &warm, &pis, &cfg)
                .unwrap_or_else(|e| panic!("{label} blowup={} must verify: {e:?}", gp.log_blowup));
            let bytes = postcard::to_allocvec(&warm).expect("postcard").len();
            drop(warm);
            let mut best = f64::INFINITY;
            for _ in 0..reps {
                let t0 = Instant::now();
                let proof =
                    prove_vm_descriptor2_with_config(&desc, &trace, &pis, &mem, &heaps, &cfg)
                        .expect("proves");
                let ms = t0.elapsed().as_secs_f64() * 1000.0;
                std::hint::black_box(&proof);
                best = best.min(ms);
            }
            println!(
                "   {:>6} {:>8} {:>4}  {:>10.2}  {:>10}  {:>9.1}",
                gp.log_blowup,
                gp.num_queries,
                pow,
                best,
                bytes,
                bytes as f64 / 1024.0
            );
        }
    }
}

/// **CPU-TIME MODE.** This box is a shared co-tenant build machine (load average 200+ during
/// this lane), so a wall-clock prove timing taken inside one process is dominated by
/// preemption. The contention-robust reading is USER CPU TIME, measured by the OS on a
/// process that does exactly one thing: prove ONE `(shape, k, n, blowup, queries, pow)` point
/// `ATTACK_REPS` times, single-threaded. The caller runs
///
/// ```text
/// ATTACK_ONE=B:4:1024:6:19:16 ATTACK_REPS=8 RAYON_NUM_THREADS=1 \
///   /usr/bin/time -p <bin> attack_one_point --exact --nocapture
/// ```
///
/// and subtracts the `ATTACK_REPS=0` baseline (process start + descriptor parse + trace build
/// + the one witness prove/verify) from the user time. `ATTACK_REPS=0` still runs the WITNESS
/// LEG, so the baseline is itself proof that the timed object is satisfiable.
#[test]
#[ignore = "MEASUREMENT DRIVER, not a test: with ATTACK_ONE unset it returns immediately and \
            reported PASSED, a green that asserted nothing. Ignored so it reports SKIPPED instead. \
            Run it as ATTACK_ONE=A:4:16:1:100:0 … -- --ignored --exact attack_one_point."]
fn attack_one_point() {
    let Ok(spec) = std::env::var("ATTACK_ONE") else {
        return;
    };
    let p: Vec<&str> = spec.split(':').collect();
    assert_eq!(
        p.len(),
        6,
        "ATTACK_ONE=<A|B>:<k>:<n>:<blowup>:<queries>:<pow>"
    );
    let k: usize = p[1].parse().expect("k");
    let n: usize = p[2].parse().expect("n");
    let log_blowup: usize = p[3].parse().expect("blowup");
    let num_queries: usize = p[4].parse().expect("queries");
    let pow: usize = p[5].parse().expect("pow");
    let reps: usize = std::env::var("ATTACK_REPS")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(8);
    let json = match p[0] {
        "A" => shape_a_json(k, n),
        "B" => shape_b_json(k, n),
        other => panic!("unknown shape {other}"),
    };
    let desc = parse_vm_descriptor2(&json).expect("descriptor parses");
    let (trace, pis) = trace_and_pis(k, n);
    let mem = MemBoundaryWitness::default();
    let heaps: Vec<Vec<dregg_circuit::heap_root::HeapLeaf>> = vec![];
    let cfg: DreggStarkConfig = create_config_with_fri(
        log_blowup,
        IR2_FRI_LOG_FINAL_POLY_LEN,
        IR2_FRI_MAX_LOG_ARITY,
        num_queries,
        pow,
    );
    // WITNESS LEG — always, even at reps = 0.
    let warm =
        prove_vm_descriptor2_with_config(&desc, &trace, &pis, &mem, &heaps, &cfg).expect("proves");
    verify_vm_descriptor2_with_config(&desc, &warm, &pis, &cfg).expect("verifies");
    let bytes = postcard::to_allocvec(&warm).expect("postcard").len();
    let inst = warm.degree_bits.len();
    drop(warm);
    let mut sink = 0usize;
    for _ in 0..reps {
        let proof = prove_vm_descriptor2_with_config(&desc, &trace, &pis, &mem, &heaps, &cfg)
            .expect("proves");
        sink = sink.wrapping_add(proof.degree_bits.len());
    }
    println!("attack_one_point {spec} reps={reps} inst={inst} wire={bytes} sink={sink}");
}

#[test]
fn fri_knob_grid_at_parity() {
    println!("\n== (3) FRI KNOB GRID at iso-budget `queries * log_blowup = 114` ==");
    println!("   (every row is PROVED and VERIFIED under its own config before it is timed)");
    grid_measure("B", &shape_b_json(4, 1024), 4, 1024, 5);
    grid_measure("B", &shape_b_json(4, 256), 4, 256, 5);
    grid_measure("B", &shape_b_json(4, 16), 4, 16, 9);
    grid_measure("A", &shape_a_json(4, 32), 4, 32, 5);
}
