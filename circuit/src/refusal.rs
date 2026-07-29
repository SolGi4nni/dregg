//! **`refusal`** — the shared REFUSAL DISCRIMINATOR for adversarial tests.
//!
//! # Why this module exists
//!
//! The dominant anti-pattern in this tree's adversarial suite was:
//!
//! ```ignore
//! // IGNORED: a DELIBERATELY-BROKEN exhibit. This is the anti-pattern the module exists
//! // to replace — it is shown BECAUSE it is wrong, and the `..` placeholder is not Rust.
//! // Compiling it would defeat the point; `must_refuse` below is the shape to copy.
//! match std::panic::catch_unwind(|| prove(&desc, &forged_rows, ..)) {
//!     Err(_) => {}                              // a panic — "refused"
//!     Ok(res) => assert!(res.is_err(), "tooth OPEN"),
//! }
//! ```
//!
//! **Any** panic and **any** `Err` both count as "the forgery was refused". That tooth cannot
//! distinguish *"the constraint system rejected the forgery"* from *"the process crashed"* — so a
//! stray `.unwrap()` or a producer-side `debug_assert!` in **trace assembly** keeps it green while
//! proving nothing about the constraint system.
//!
//! This is not hypothetical. At the commit that introduced this module,
//! `descriptor_ir2::tests::ir2_forged_map_opening_refuses` reported `ok` because
//! `descriptor_ir2.rs:5195`'s `debug_assert_eq!(end, root, "old path must authenticate against
//! root8")` — a **witness-assembly sanity check**, not a constraint — panicked first. The prover
//! was never asked to refuse anything. The `Err(_) => {}` arm swallowed it.
//!
//! # What a refusal actually looks like
//!
//! There are exactly **two** honest refusal mechanisms on the `prove_vm_descriptor2*` path, and
//! they are reached under different conditions:
//!
//! 1. **A typed `Err`** — the pre-flight in-trace replay (gated on `check: true`, i.e. the public
//!    [`crate::descriptor_ir2::prove_vm_descriptor2`] entry) eagerly refuses a bad witness
//!    fail-closed and returns `Err(String)`. In a release build this is also what the batch
//!    self-verify surfaces. **This is the mechanism to prefer, and [`must_refuse`] requires it.**
//!
//! 2. **The p3 batch prover's DOCUMENTED unsat panic** — the adversarial teeth that call
//!    `prove_vm_descriptor2_inner` DIRECTLY with `check: false` bypass the replay, so the forged
//!    witness reaches `p3_batch_stark::prove_batch`. That function runs two `#[cfg(debug_assertions)]`
//!    checks which **panic** rather than return:
//!
//!    * `batch-stark/src/check_constraints.rs:133` — `panic!("constraints not satisfied on row
//!      {row_index}: failed constraints = {rendered}")`
//!    * `lookup/src/debug_util.rs:82` (via `MultiSet::assert_empty`, called by `check_lookups`) —
//!      `panic!("Lookup mismatch ({label}): tuple {:?} has net multiplicity {:?} ...")`
//!
//!    Under `cargo test` (a debug build) these fire *before* the prover could return anything, so
//!    for a `check: false` site the panic genuinely **is** the refusal. [`must_refuse_or_unsat_panic`]
//!
//! ⚑ **CORRECTION (2026-07-25) — the discriminator above is WRONG, and it misrouted a real tooth.**
//! The unsat-panic mechanism is NOT about `check: false`. The real discriminator is **whether the
//! descriptor has LOOKUPS**:
//!
//!   * **With lookups** — p3's debug check runs inside `prove_batch` and PANICS
//!     (`batch-stark/src/check_constraints.rs:133`, "constraints not satisfied on row N") **before**
//!     the self-verify can return anything. So at such a site in a DEBUG build, `Err` is
//!     structurally unreachable and [`must_refuse`] cannot pass.
//!   * **Without lookups** — p3 gates that check on `if !all_lookups[i].is_empty()`
//!     (`batch-stark/src/prover.rs:232`), so it never runs at all, and only the producer's
//!     self-verify `Err` fires (surfacing as e.g. `OodEvaluationMismatch`).
//!
//! Note also that `prove_vm_descriptor2_for_config`'s `check: true` pre-flight replays only the
//! mem/map/umem/exact-public/submask witnesses — **not** the algebraic gates or the PI pins
//! (`descriptor_ir2.rs:4432-5471`). So `check: true` does not mean "an `Err` will describe a bad
//! witness".
//!
//! This is why the same helper was correct in `custom_leaf_adapter` (an arity pre-flight, a genuine
//! `Err`) and wrong in `shielded_ring_clearing_air` (a lookup-carrying descriptor, an unavoidable
//! panic). Two forgery teeth sat RED for ten days on that mistake while asserting the *right* thing —
//! the constraint system refused every forgery; the harness just could not observe it. **Pick the
//! helper by whether the descriptor has lookups, not by the `check` flag.**
//!
//! ⚑⚑ **SECOND CORRECTION (2026-07-29) — the paragraph above says `check && debug_assertions`, and
//! THAT WAS THE BUG.** The producer self-verify was gated on `cfg!(debug_assertions)` from
//! `934258ea0` (2026-06-24), so under `--release` a forged witness reached NEITHER mechanism: p3's
//! two panics are `#[cfg(debug_assertions)]` and the self-verify was too. `prove_vm_descriptor2`
//! returned `Ok` for an all-zeros trace, and **twenty** forgery teeth across `dregg-circuit` and
//! `dregg-circuit-prove` reported "the forgery was ACCEPTED" for 35 days. The self-verify runs in
//! every profile now (`descriptor_ir2::prove_vm_descriptor2_inner`, under `check` alone).
//!
//! The doctrine that follows from it: **a tooth that accepts only [`P3_UNSAT_PANIC_MARKERS`] is a
//! DEBUG-ONLY tooth**, because both of those strings come from `#[cfg(debug_assertions)]` code in
//! p3. Pair them with [`DEPLOYED_VERIFIER_REFUSAL_MARKERS`] — the verdicts that exist in every
//! profile — or, when the tooth's subject is a specific gate, use
//! [`assert_violated_constraint_not_bus`], which keeps the constraint-vs-bus discrimination
//! identically in both.
//!    accepts it — but **only** it, matched by message against [`P3_UNSAT_PANIC_MARKERS`]. Any other
//!    panic (a trace-assembly `debug_assert`, a stray `unwrap`, an index OOB, an OOM) is a **test
//!    failure**, because it is not a refusal — it is a crash wearing a refusal's clothes.
//!
//! Note what is deliberately **not** in the marker list: `check_constraints.rs:54/62`'s
//! `assert_eq!` on trace heights, and `debug_util.rs:243`'s `"only two-row windows are supported"`.
//! Those are **shape/deploy faults**, not unsat verdicts. A tooth that "passes" because the trace
//! was the wrong height has not witnessed a refusal, so those panics red the test.
//!
//! # The `Err` side of the same disease
//!
//! The paragraph above closed the discrimination on the **panic** side only. A shape fault reached
//! through an `Err` was still laundered: `Ok(Err(e)) => e` handed **any** error back as a refusal, so
//! `base row width 3065 must equal descriptor trace_width 1963` — the prover's *pre-flight arity
//! check*, fired before the constraint system reads one cell of the witness — satisfied a forgery
//! tooth exactly as a stray `unwrap` used to. That was found in the wild
//! (`circuit/tests/heap_write_roundtrip.rs`, which was green with the forgery neutered) and repaired
//! only in that one file. [`SHAPE_FAULT_MARKERS`] and [`assert_committed_shape`] are that repair,
//! lifted here so every site inherits it; [`must_refuse`], [`must_refuse_or_unsat_panic`] and
//! [`classify`] all RED on a shape-marked `Err`. A tooth whose *subject* is the arity pre-flight says
//! so by name with [`must_refuse_shape_fault`].
//!
//! # Placement
//!
//! This is test-support code living in a production crate's `src/`, which deserves a justification:
//!
//! * `dregg-circuit-prove` depends on `dregg-circuit` as a **normal** `[dependencies]` entry, so one
//!   `pub mod` here is reachable from both crates' unit tests (`#[cfg(test)]` in `src/`) **and**
//!   their integration tests (`tests/`, which link the crate as an external rlib and therefore
//!   cannot see a `#[cfg(test)]` module). No other single placement covers all four.
//! * It is deliberately **not** behind a Cargo feature. A feature that arms test-only code is
//!   exactly the `test-stubs` leak this tree already has (CRATE-EXCELLENCE-PLAN §1.3: feature
//!   unification armed `StubVerifier` inside the production node binary). Features unify; `pub mod`
//!   does not.
//! * The soundness surface is nil in the strict sense: this module has no accept path. Every
//!   function here either returns a refusal reason or panics. It can only make a test **stricter**,
//!   never more permissive, so shipping it in a production build arms nothing.

use std::any::Any;
use std::cell::Cell;
use std::panic::{AssertUnwindSafe, catch_unwind};
use std::sync::Once;

use crate::descriptor_ir2::EffectVmDescriptor2;
use crate::field::BabyBear;

/// Substrings of a refusal `Err` that name a **SHAPE / ARITY fault** — the prover complaining about
/// the trace's *geometry* — rather than a verdict on the WITNESS.
///
/// This is the `Err`-side twin of the panic-side discrimination already documented above. The panic
/// side was closed at the module's birth ([`P3_UNSAT_PANIC_MARKERS`] excludes the height
/// `assert_eq!`s on purpose); the `Err` side was not, and `Ok(Err(e)) => e` accepted **any** error
/// as a refusal. A tooth handed a mis-shaped trace gets
///
/// ```text
/// base row width 3065 must equal descriptor trace_width 1963
/// ```
///
/// back from `prove_vm_descriptor2`'s pre-flight — **before** `check_descriptor2`'s replay or
/// `prove_batch`'s constraint check sees a single cell of the forgery — and a tooth reading that as
/// "refused" has recorded a refusal it never earned. This was found in the wild
/// (`circuit/tests/heap_write_roundtrip.rs`, whose header narrates it) and repaired only locally.
///
/// Every marker here is a substring of a **pre-flight arity check** in
/// [`crate::descriptor_ir2::prove_vm_descriptor2_inner`] / [`crate::lean_descriptor_air`], verified
/// unique in-tree:
///
/// * `descriptor_ir2.rs:5958`, `lean_descriptor_air.rs:1822` — base row width vs `trace_width`.
/// * `descriptor_ir2.rs:5965` — PI vector length vs `public_input_count`.
/// * `descriptor_ir2.rs:5949`, `lean_descriptor_air.rs:1818` — empty base trace.
/// * `descriptor_ir2.rs:5952` — base trace height not a power of two.
///
/// Deliberately **absent**, because they are real verdicts a tooth may legitimately earn: bare
/// `"must be a power of two"` and `"length mismatch"` (witness-builder validation that several teeth
/// genuinely test — `membership_descriptor_4ary`, `note_spend_witness`, `merkle_air`), the verifier's
/// instance-count refusal, the range-table-degree refusal (a taller byte table widens every limb
/// range — that one IS a tooth), and `"descriptor declares no {mem,map,umem} ops but a … witness was
/// supplied"` (`descriptor_ir2.rs:5974/5981/5987`). That last set is a JUDGEMENT CALL: they are
/// pre-flight and the trace is never read, but refusing an uncommitted-table witness is itself a
/// soundness gate a tooth may want to attack, so marking them would risk turning a genuine tooth red.
/// If one is ever found satisfying a forgery tooth, move it here.
pub const SHAPE_FAULT_MARKERS: [&str; 4] = [
    "must equal descriptor trace_width",
    "!= descriptor public_input_count",
    "base trace must be non-empty",
    "base trace height",
];

/// The [`SHAPE_FAULT_MARKERS`] entry `msg` trips, if any.
pub fn shape_fault(msg: &str) -> Option<&'static str> {
    SHAPE_FAULT_MARKERS
        .iter()
        .copied()
        .find(|m| msg.contains(m))
}

/// RED if `rendered` is a shape/arity complaint. Called on every `Err` that this module would
/// otherwise hand back as a refusal, so all `must_refuse*` / [`classify`] sites inherit it.
#[track_caller]
fn reject_shape_fault(what: &str, rendered: &str) {
    if let Some(m) = shape_fault(rendered) {
        panic!(
            "{what}: the call refused with a SHAPE/ARITY fault, NOT a verdict on the witness.\n  \
             matched marker: {m:?}\n  error: {rendered}\n\
             The prover rejected the trace's GEOMETRY in its pre-flight, before the constraint \
             system examined one cell of the witness — so this tooth witnessed NOTHING and the \
             refusal it recorded was never earned. Fix the fixture so the trace/PI vector has the \
             committed member's shape (`refusal::assert_committed_shape` pins it structurally). If \
             the arity check itself IS the tooth, say so with `must_refuse_shape_fault`."
        );
    }
}

/// **`assert_committed_shape`** — pin, STRUCTURALLY, that `trace`/`dpis` already have exactly the
/// committed member's shape, so a subsequent prover `Err` cannot be an arity complaint.
///
/// This is the primary guard and [`SHAPE_FAULT_MARKERS`] is only the second net behind it: string
/// matching catches the faults we have *seen*, whereas this catches the class. Call it before
/// proving in any tooth that assembles or mutates a trace by hand.
///
/// It is deliberately stricter than the prover in ONE direction, which is why it is not redundant
/// with the marker net: `trace_with_chip_lanes` (`descriptor_ir2.rs:6075`) zero-`resize`s a row that
/// is NARROWER than `trace_width` up to the committed width before the arity pre-flight runs, so a
/// short row PROVES and emits no marker at all (measured, `heap_write_roundtrip.rs`). Only an
/// OVER-WIDE row reaches `descriptor_ir2.rs:5957`. A tooth should hand the prover the exact committed
/// shape rather than rely on that pad, so this pins equality in both directions.
#[track_caller]
pub fn assert_committed_shape(
    what: &str,
    desc: &EffectVmDescriptor2,
    trace: &[Vec<BabyBear>],
    dpis: &[BabyBear],
) {
    assert!(
        !trace.is_empty(),
        "{what}: the trace is EMPTY — a SHAPE fault, not a refusal"
    );
    for (i, row) in trace.iter().enumerate() {
        assert_eq!(
            row.len(),
            desc.trace_width,
            "{what}: row {i} is {} wide but the committed {} is {} — a SHAPE fault. The prover \
             reports it as an Err, and a tooth that reads any Err as 'refused' would pass here with \
             the forgery never examined.",
            row.len(),
            desc.name,
            desc.trace_width
        );
    }
    assert_eq!(
        dpis.len(),
        desc.public_input_count,
        "{what}: PI vector is {} long but the committed {} declares {} — a SHAPE fault, not a \
         refusal",
        dpis.len(),
        desc.name,
        desc.public_input_count
    );
}

/// The p3 batch prover's two DOCUMENTED unsatisfiable-witness panics, verified by reading
/// Plonky3 @ `82cfad73cd734d37a0d51953094f970c531817ec`:
///
/// * `batch-stark/src/check_constraints.rs:133` — an AIR constraint is violated on some row.
/// * `lookup/src/debug_util.rs:82` — a lookup/permutation bus does not balance.
///
/// Both are `#[cfg(debug_assertions)]`-gated inside `prove_batch`, so they are live under
/// `cargo test` and absent under `--release`. A panic matching neither marker is **not** a
/// refusal.
pub const P3_UNSAT_PANIC_MARKERS: [&str; 2] =
    ["constraints not satisfied on row", "Lookup mismatch"];

/// ⚑ The DEPLOYED VERIFIER's own refusal verdicts — the ones that exist in EVERY build profile.
///
/// [`P3_UNSAT_PANIC_MARKERS`] above are `#[cfg(debug_assertions)]`-only, and a tooth that accepts
/// only those is a DEBUG-ONLY tooth. That is not a hypothetical: from `934258ea0` (2026-06-24) to
/// 2026-07-29 the IR-v2 producer's self-verify was itself behind `cfg!(debug_assertions)`, so
/// under `--release` a forged witness produced `Ok` and twenty forgery teeth across
/// `dregg-circuit` and `dregg-circuit-prove` reported "the forgery was ACCEPTED".
///
/// * `OodEvaluationMismatch` — `folded_constraints(ζ) · Z_H(ζ)⁻¹ ≠ quotient(ζ)`, i.e. some AIR
///   constraint of the named instance does not vanish. `index: Some(0)` is the Main AIR.
/// * `LookupError` — the GLOBAL LogUp sums do not cancel across instances (a bus imbalance).
///
/// These two discriminate the same way the p3 pair does: `constraints not satisfied on row` and
/// `OodEvaluationMismatch` are CONSTRAINT verdicts; `Lookup mismatch` and `LookupError` are BUS
/// verdicts. A tooth whose subject is "a violated constraint, NOT a bus imbalance" keeps that
/// discrimination by pairing a constraint marker with the absence of a bus one — see
/// [`assert_violated_constraint_not_bus`].
pub const DEPLOYED_VERIFIER_REFUSAL_MARKERS: [&str; 2] = ["OodEvaluationMismatch", "LookupError"];

/// The refusal named a VIOLATED CONSTRAINT, in whichever profile the tooth ran, and did **not**
/// name a bus/lookup imbalance.
///
/// Under `cargo test` this is p3's row-naming `constraints not satisfied on row N`; under
/// `--release` it is the deployed verifier's `OodEvaluationMismatch`. Both are constraint
/// verdicts. The load-bearing half is the NEGATIVE clause: a tooth whose subject is a specific
/// gate (a PI pin, a carry decomposition) must not be satisfied by the bus failing instead, and
/// that clause holds identically in both profiles.
pub fn assert_violated_constraint_not_bus(what: &str, reason: &str) {
    let bus = ["Lookup mismatch", "LookupError"];
    assert!(
        !bus.iter().any(|m| reason.contains(m)),
        "{what}: refused by a BUS IMBALANCE, not by the violated constraint this tooth names: \
         {reason}"
    );
    assert!(
        reason.contains("constraints not satisfied on row")
            || reason.contains("OodEvaluationMismatch"),
        "{what}: the refusal names neither a violated constraint (`constraints not satisfied on \
         row`, p3's debug check) nor the deployed verifier's constraint verdict \
         (`OodEvaluationMismatch`): {reason}"
    );
}

/// How a call under test refused. Returned by [`must_refuse_or_unsat_panic`] so a caller can
/// match on the reason once `LeafError`/`Ir2VerifyError` land (CRATE-EXCELLENCE-PLAN Move 5) —
/// today the `Err` payload is still a `String` on most boundaries.
#[derive(Debug)]
pub enum Refusal<E> {
    /// The call returned `Err` — the replay/verify refused fail-closed. The preferred shape.
    Err(E),
    /// The p3 debug prover panicked with one of [`P3_UNSAT_PANIC_MARKERS`]. Carries the full
    /// panic message so a caller can assert *which* constraint or bus caught the forgery.
    UnsatPanic(String),
}

impl<E> Refusal<E> {
    /// The refusal rendered as text, for a caller that wants to assert on the reason uniformly
    /// across both mechanisms.
    pub fn reason(&self) -> String
    where
        E: std::fmt::Debug,
    {
        match self {
            Refusal::Err(e) => format!("{e:?}"),
            Refusal::UnsatPanic(m) => m.clone(),
        }
    }
}

/// The full outcome of a call under test, including ACCEPTANCE. Returned by [`classify`].
///
/// Needed by teeth whose real soundness boundary is one layer **down**: under `--release`, a
/// `check: false` prove emits an unverified proof, so "the prover returned `Ok`" is not yet a
/// failure — the CONSUMER's verify is what must reject. Such a tooth must be able to take the
/// accepted proof and go check it, rather than fail on the spot.
#[derive(Debug)]
pub enum Outcome<T, E> {
    /// The call RETURNED `Ok`. **Not** necessarily a hole — see the type docs — but the caller
    /// now owes an assertion against the next boundary down.
    Accepted(T),
    /// Refused fail-closed with a typed/stringly error.
    Err(E),
    /// Refused by the p3 debug prover's DOCUMENTED unsat panic ([`P3_UNSAT_PANIC_MARKERS`]).
    UnsatPanic(String),
}

/// **`classify`** — run `f` and discriminate its outcome three ways, REDDING on any panic that is
/// not the p3 prover's documented unsat verdict.
///
/// This is the primitive [`must_refuse_or_unsat_panic`] is built from. Reach for `classify`
/// directly only when acceptance at this layer is legitimately not a failure (see [`Outcome`]);
/// otherwise prefer the `must_*` wrappers, which cannot forget to assert.
#[track_caller]
pub fn classify<T, E: std::fmt::Debug, F>(what: &str, f: F) -> Outcome<T, E>
where
    F: FnOnce() -> Result<T, E>,
{
    match catch_quietly(f) {
        Err(p) => {
            let msg = panic_message(&*p);
            if P3_UNSAT_PANIC_MARKERS.iter().any(|m| msg.contains(m)) {
                Outcome::UnsatPanic(msg)
            } else {
                panic!(
                    "{what}: the call panicked, but NOT with the p3 debug prover's documented \
                     unsat panic — so this is NOT a refusal, it is a crash:\n  {msg}\n\
                     Expected the panic to contain one of {P3_UNSAT_PANIC_MARKERS:?} \
                     (batch-stark/src/check_constraints.rs:133 or lookup/src/debug_util.rs:82). \
                     A trace-assembly debug_assert, a stray unwrap, or a trace-shape assert_eq! \
                     means the prover was never asked to refuse the forgery."
                )
            }
        }
        Ok(Ok(v)) => Outcome::Accepted(v),
        Ok(Err(e)) => {
            reject_shape_fault(what, &format!("{e:?}"));
            Outcome::Err(e)
        }
    }
}

/// Extract a panic payload as text. `panic!("literal")` yields `&'static str`; a formatted
/// `panic!("{x}")` and `assert*!` yield `String`.
fn panic_message(payload: &(dyn Any + Send)) -> String {
    if let Some(s) = payload.downcast_ref::<String>() {
        s.clone()
    } else if let Some(s) = payload.downcast_ref::<&'static str>() {
        (*s).to_string()
    } else {
        "<non-string panic payload>".to_string()
    }
}

/// Set while this thread is inside [`catch_quietly`]. The hook installed below reads it, so
/// silencing is scoped to the thread that asked for it.
thread_local! {
    static QUIET: Cell<bool> = const { Cell::new(false) };
}

static QUIET_HOOK: Once = Once::new();

/// Run `f`, silencing the default panic hook **on this thread** for its duration, so an *expected*
/// unsat panic does not spray a backtrace across passing test output.
///
/// ⚠ THE HOOK IS PROCESS-GLOBAL AND THIS USED TO IGNORE THAT. The previous implementation did
/// `take_hook()` / `set_hook(|_| {})` / `set_hook(prev)` around `f`. `std::panic`'s hook is one
/// slot for the whole process, so for the duration of any `must_refuse` anywhere, EVERY thread's
/// panic printed nothing — and a test binary runs its tests in parallel. The cost is not
/// theoretical: measured 2026-07-26 on persvati at `--test-threads=4`, all six failures of
/// `tests/effect_vm_umem_real_turn.rs` reported a bare `FAILED` with an EMPTY stdout block. The
/// panics happened while a sibling test held the silent hook, so the assertion messages were
/// swallowed and the reds named nothing anyone could act on. Two full census runs read them as
/// mysteries.
///
/// So the silence is now a THREAD-LOCAL flag consulted by a hook installed once. A concurrent
/// thread's genuine failure prints normally; the expected unsat panic on this thread still does
/// not. The flag is saved and restored rather than cleared, so nesting cannot un-silence an outer
/// `catch_quietly`.
fn catch_quietly<T>(f: impl FnOnce() -> T) -> Result<T, Box<dyn Any + Send>> {
    QUIET_HOOK.call_once(|| {
        let prev = std::panic::take_hook();
        std::panic::set_hook(Box::new(move |info| {
            if QUIET.with(Cell::get) {
                return;
            }
            prev(info);
        }));
    });
    let outer = QUIET.with(|q| q.replace(true));
    let r = catch_unwind(AssertUnwindSafe(f));
    QUIET.with(|q| q.set(outer));
    r
}

/// **`must_refuse`** — require that `f` refuses by returning `Err`, and hand back the error so the
/// caller can assert *why*.
///
/// This is the default, and the shape every site should reach for. It is strictly stronger than the
/// idiom it replaces:
///
/// * `f` **panicked** → this test **FAILS**. A panic is not a refusal. This is the whole point: a
///   stray `unwrap` in trace assembly now reds the suite instead of silently satisfying the tooth.
/// * `f` returned `Ok` → this test **FAILS**: the forgery was ACCEPTED, the tooth is OPEN.
/// * `f` returned `Err(e)` naming a [`SHAPE_FAULT_MARKERS`] fault → this test **FAILS**. A width /
///   PI-arity complaint is the prover refusing the trace's GEOMETRY in its pre-flight; the forgery
///   was never examined, so it is a crash wearing a refusal's clothes exactly as a stray panic is.
/// * `f` returned `Err(e)` otherwise → returns `e`.
///
/// `what` names the forgery under test and is quoted in every failure message, so a red says which
/// tooth broke without a backtrace.
///
/// Use [`must_refuse_or_unsat_panic`] **only** for a site that calls `prove_vm_descriptor2_inner`
/// with `check: false`, where the p3 debug prover's panic is genuinely the mechanism.
#[track_caller]
pub fn must_refuse<T, E: std::fmt::Debug, F>(what: &str, f: F) -> E
where
    F: FnOnce() -> Result<T, E>,
{
    match catch_quietly(f) {
        Err(p) => panic!(
            "{what}: expected a fail-closed Err refusal, but the call PANICKED: {}\n\
             A panic is NOT a refusal — this tooth cannot tell 'rejected the forgery' from \
             'crashed'. If the p3 debug prover's documented unsat panic is genuinely the \
             mechanism here (a `check: false` prove_vm_descriptor2_inner site), use \
             `must_refuse_or_unsat_panic`. Otherwise this is a real bug in the path under test.",
            panic_message(&*p)
        ),
        Ok(Ok(_)) => panic!("{what}: the forgery was ACCEPTED — this tooth is OPEN."),
        Ok(Err(e)) => {
            reject_shape_fault(what, &format!("{e:?}"));
            e
        }
    }
}

/// **`must_refuse_shape_fault`** — the NAMED escape hatch for a tooth whose subject genuinely IS the
/// prover's shape/arity pre-flight ("a mis-sized trace must be rejected, not silently padded").
///
/// Such a check is a real refusal, but of a **different statement** than an in-circuit one, and it
/// says nothing about any forged witness. Naming it keeps the distinction visible instead of letting
/// it hide behind a generic [`must_refuse`], which now reds on shape faults. `expected` must be one
/// of [`SHAPE_FAULT_MARKERS`] (or a substring of the specific message), and the error must contain it.
#[track_caller]
pub fn must_refuse_shape_fault<T, E: std::fmt::Debug, F>(what: &str, expected: &str, f: F) -> E
where
    F: FnOnce() -> Result<T, E>,
{
    match catch_quietly(f) {
        Err(p) => panic!(
            "{what}: expected a fail-closed SHAPE-fault Err, but the call PANICKED: {}",
            panic_message(&*p)
        ),
        Ok(Ok(_)) => panic!(
            "{what}: the mis-shaped input was ACCEPTED — the prover's arity pre-flight is OPEN."
        ),
        Ok(Err(e)) => {
            let rendered = format!("{e:?}");
            assert!(
                rendered.contains(expected),
                "{what}: refused, but not with the expected shape fault.\n  expected to contain: \
                 {expected}\n  got: {rendered}"
            );
            e
        }
    }
}

/// **`must_refuse_or_unsat_panic`** — require that `f` refuses either by returning `Err` **or** by
/// the p3 debug prover's DOCUMENTED unsat panic ([`P3_UNSAT_PANIC_MARKERS`]).
///
/// Reserved for sites that bypass the pre-flight replay (`prove_vm_descriptor2_inner` with
/// `check: false`), where a forged witness reaches `prove_batch` and the debug-gated constraint /
/// lookup check panics before anything can be returned. There, the panic **is** the refusal.
///
/// It is still a discriminator, not a shrug:
///
/// * panic **matching** a marker → `Refusal::UnsatPanic(msg)`.
/// * panic **not** matching → this test **FAILS**. A trace-assembly `debug_assert`, a stray
///   `unwrap`, a height-mismatch `assert_eq!` — none of those are the constraint system refusing.
/// * `Ok(Ok(_))` → this test **FAILS**: forgery accepted, tooth OPEN.
/// * `Ok(Err(e))` naming a [`SHAPE_FAULT_MARKERS`] fault → this test **FAILS** (inherited from
///   [`classify`]): a width / PI-arity complaint is the pre-flight refusing the trace's geometry.
/// * `Ok(Err(e))` otherwise → `Refusal::Err(e)`.
#[track_caller]
pub fn must_refuse_or_unsat_panic<T, E: std::fmt::Debug, F>(what: &str, f: F) -> Refusal<E>
where
    F: FnOnce() -> Result<T, E>,
{
    match classify(what, f) {
        Outcome::UnsatPanic(m) => Refusal::UnsatPanic(m),
        Outcome::Err(e) => Refusal::Err(e),
        Outcome::Accepted(_) => panic!("{what}: the forgery was ACCEPTED — this tooth is OPEN."),
    }
}

/// **`must_panic_containing`** — require that `f` panics with a SPECIFIC, named message.
///
/// For the narrow case where a panic is genuinely the documented mechanism but it is **not** the
/// p3 prover's unsat verdict — e.g. a producer-side `debug_assert!` in trace assembly that refuses
/// to build a trace for a forged witness. Such a check is a real refusal, but it is a **different
/// tooth** from the in-circuit one, and it is compiled out under `--release`. Naming it forces the
/// distinction to stay visible instead of being laundered by an `Err(_) => {}` arm.
///
/// Any other panic, or no panic at all, is a test failure. Returns the panic message.
#[track_caller]
pub fn must_panic_containing<T, F>(what: &str, expected: &str, f: F) -> String
where
    F: FnOnce() -> T,
{
    match catch_quietly(f) {
        Err(p) => {
            let msg = panic_message(&*p);
            assert!(
                msg.contains(expected),
                "{what}: panicked, but not with the expected message.\n  expected to contain: \
                 {expected}\n  got: {msg}"
            );
            msg
        }
        Ok(_) => panic!("{what}: expected a panic containing {expected:?}, but the call RETURNED."),
    }
}

/// **`must_accept`** — the honest pole. Require that `f` ACCEPTS, so the paired negative is not
/// vacuous.
///
/// CRATE-EXCELLENCE-PLAN §S1 requires every forgery tooth to re-assert the honest pole first:
/// a tooth that rejects the forgery *and also* rejects the honest witness has proved nothing —
/// it might reject everything. Panics carry the underlying error/panic text.
#[track_caller]
pub fn must_accept<T, E: std::fmt::Debug, F>(what: &str, f: F) -> T
where
    F: FnOnce() -> Result<T, E>,
{
    match catch_quietly(f) {
        Err(p) => panic!(
            "{what}: the HONEST witness PANICKED: {}\n\
             The honest pole must be accepted — otherwise the paired forgery test is vacuous \
             (it would 'reject' everything).",
            panic_message(&*p)
        ),
        Ok(Err(e)) => panic!(
            "{what}: the HONEST witness was REJECTED: {e:?}\n\
             The honest pole must be accepted — otherwise the paired forgery test is vacuous \
             (it would 'reject' everything)."
        ),
        Ok(Ok(v)) => v,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn must_refuse_returns_the_error_for_a_fail_closed_reject() {
        let e = must_refuse("probe", || Err::<(), _>("replay refused: forged opening"));
        assert_eq!(e, "replay refused: forged opening");
    }

    #[test]
    #[should_panic(expected = "the forgery was ACCEPTED")]
    fn must_refuse_reds_when_the_forgery_is_accepted() {
        must_refuse("probe", || Ok::<_, String>(()));
    }

    /// THE POINT OF THE WHOLE MODULE: a stray panic in trace assembly used to satisfy the tooth.
    /// It must now RED.
    #[test]
    #[should_panic(expected = "expected a fail-closed Err refusal, but the call PANICKED")]
    fn must_refuse_reds_on_a_stray_trace_assembly_panic() {
        must_refuse("probe", || -> Result<(), String> {
            panic!("old path must authenticate against root8")
        });
    }

    #[test]
    fn unsat_panic_variant_accepts_the_documented_constraint_panic() {
        let r = must_refuse_or_unsat_panic("probe", || -> Result<(), String> {
            panic!("constraints not satisfied on row 3: failed constraints = [..]")
        });
        assert!(matches!(r, Refusal::UnsatPanic(ref m) if m.contains("row 3")));
    }

    #[test]
    fn unsat_panic_variant_accepts_the_documented_lookup_panic() {
        let r = must_refuse_or_unsat_panic("probe", || -> Result<(), String> {
            panic!("Lookup mismatch (global lookup 'ir2_chip'): tuple [..] has net multiplicity 1")
        });
        assert!(matches!(r, Refusal::UnsatPanic(_)));
    }

    /// The discriminator's real teeth: even the panic-tolerant variant must REJECT a panic that is
    /// not the prover's unsat verdict.
    #[test]
    #[should_panic(expected = "NOT with the p3 debug prover's documented unsat panic")]
    fn unsat_panic_variant_reds_on_a_stray_assembly_panic() {
        must_refuse_or_unsat_panic("probe", || -> Result<(), String> {
            panic!("old path must authenticate against root8")
        });
    }

    /// A trace-SHAPE assert is a deploy fault, not an unsat verdict — it must not be laundered
    /// into a refusal.
    #[test]
    #[should_panic(expected = "NOT with the p3 debug prover's documented unsat panic")]
    fn unsat_panic_variant_reds_on_a_trace_shape_assert() {
        must_refuse_or_unsat_panic("probe", || -> Result<(), String> {
            panic!(
                "debug constraint check requires permutation trace height (4) to match main trace height (8)"
            )
        });
    }

    #[test]
    #[should_panic(expected = "a stray unwrap")]
    fn unsat_panic_variant_reds_on_a_stray_unwrap() {
        must_refuse_or_unsat_panic("probe", || -> Result<(), String> {
            None::<()>.expect("a stray unwrap in trace assembly");
            Ok(())
        });
    }

    // ------------------------------------------------------------------
    // THE Err-SIDE SHAPE GUARD — both poles.
    // ------------------------------------------------------------------

    /// POLE 1, the defect closed: the EXACT `Err` the heap-write tooth was passing on. Before this
    /// guard, `must_refuse` handed this back as a refusal reason and the tooth went green with the
    /// forgery never examined.
    #[test]
    #[should_panic(expected = "refused with a SHAPE/ARITY fault")]
    fn must_refuse_reds_on_a_row_width_complaint() {
        must_refuse("forged heap-write", || {
            Err::<(), _>("base row width 3065 must equal descriptor trace_width 1963".to_string())
        });
    }

    #[test]
    #[should_panic(expected = "refused with a SHAPE/ARITY fault")]
    fn must_refuse_reds_on_a_pi_arity_complaint() {
        must_refuse("forged PI", || {
            Err::<(), _>("public input count 7 != descriptor public_input_count 76".to_string())
        });
    }

    #[test]
    #[should_panic(expected = "refused with a SHAPE/ARITY fault")]
    fn unsat_tolerant_variant_reds_on_a_row_width_complaint() {
        must_refuse_or_unsat_panic("forged heap-write", || {
            Err::<(), _>("base row width 3065 must equal descriptor trace_width 1963".to_string())
        });
    }

    /// `classify` is the primitive under ~100 emit-gate `rejects()` helpers, which return a `bool`.
    /// A shape fault flowing back as `true` == "rejected" is the same vacuity one layer out.
    #[test]
    #[should_panic(expected = "refused with a SHAPE/ARITY fault")]
    fn classify_reds_on_a_row_width_complaint() {
        let _: Outcome<(), String> = classify("emit gate", || {
            Err("base trace height 3 must be a power of two".to_string())
        });
    }

    /// POLE 2, THE ANTI-OVER-STRICTNESS POLE: a genuine constraint refusal must still pass through
    /// untouched. Without this, a guard that redded on *every* `Err` would look identical.
    #[test]
    fn a_genuine_replay_refusal_still_passes_through() {
        let e = must_refuse("forged opening", || {
            Err::<(), _>("in-trace replay refused: old path does not authenticate against root8")
        });
        assert!(e.contains("replay refused"));
    }

    /// Refusals that MENTION shape-ish words but are real verdicts must NOT be laundered into reds:
    /// the witness-builder validations several teeth genuinely test.
    #[test]
    fn near_miss_refusals_are_not_treated_as_shape_faults() {
        for msg in [
            "membership depth 3 must be a power of two ≥ 2 (the trace-height requirement)",
            "siblings/positions length mismatch (4 vs 3)",
            "range-table instance committed at 2^9 rows; the deployed table is 2^8 under this PCS",
            "IR v2 proof carries 3 instances but the descriptor's present-table set is 4",
        ] {
            assert!(
                shape_fault(msg).is_none(),
                "{msg:?} is a real verdict, not a shape fault — marking it would break a genuine \
                 tooth into a false red"
            );
            let e = must_refuse("near miss", || Err::<(), _>(msg.to_string()));
            assert_eq!(e, msg);
        }
    }

    /// The named escape hatch: a tooth whose SUBJECT is the arity pre-flight still has a way to say
    /// so, and it must name the fault it expects.
    #[test]
    fn shape_fault_tooth_can_name_its_subject() {
        let e = must_refuse_shape_fault(
            "arity pre-flight",
            "must equal descriptor trace_width",
            || Err::<(), _>("base row width 4 must equal descriptor trace_width 8".to_string()),
        );
        assert!(e.contains("trace_width"));
    }

    #[test]
    #[should_panic(expected = "the mis-shaped input was ACCEPTED")]
    fn shape_fault_tooth_reds_if_the_preflight_is_open() {
        must_refuse_shape_fault("arity pre-flight", "trace_width", || Ok::<_, String>(()));
    }

    #[test]
    #[should_panic(expected = "row 1 is 4 wide but the committed")]
    fn assert_committed_shape_reds_on_a_ragged_trace() {
        let desc = EffectVmDescriptor2 {
            name: "probe".to_string(),
            trace_width: 8,
            public_input_count: 1,
            tables: vec![],
            constraints: vec![],
            hash_sites: vec![],
            ranges: vec![],
        };
        let trace = vec![vec![BabyBear::new(0); 8], vec![BabyBear::new(0); 4]];
        assert_committed_shape("probe", &desc, &trace, &[BabyBear::new(0)]);
    }

    #[test]
    #[should_panic(expected = "PI vector is 2 long but the committed")]
    fn assert_committed_shape_reds_on_a_mis_sized_pi_vector() {
        let desc = EffectVmDescriptor2 {
            name: "probe".to_string(),
            trace_width: 8,
            public_input_count: 1,
            tables: vec![],
            constraints: vec![],
            hash_sites: vec![],
            ranges: vec![],
        };
        let trace = vec![vec![BabyBear::new(0); 8]];
        assert_committed_shape("probe", &desc, &trace, &[BabyBear::new(0); 2]);
    }

    #[test]
    fn must_accept_passes_the_honest_pole_through() {
        assert_eq!(must_accept("honest", || Ok::<_, String>(7u8)), 7);
    }

    #[test]
    #[should_panic(expected = "the HONEST witness was REJECTED")]
    fn must_accept_reds_when_the_honest_pole_is_rejected() {
        must_accept("honest", || Err::<(), _>("nope".to_string()));
    }
}
