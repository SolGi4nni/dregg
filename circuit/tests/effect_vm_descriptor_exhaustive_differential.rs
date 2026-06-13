//! EXHAUSTIVE EffectVM-descriptor differential — the running `EffectVmDescriptorAir`
//! decides EXACTLY the verified reference `decideVm` (= `satisfiedVm`), over a
//! GENERATED corpus that hits every constraint form and every expression form.
//!
//! ## The residual this closes (the DEEPEST Argus edge)
//!
//! The class-A Argus theorems (`Dregg2/Circuit/Argus/Compile.lean`, every
//! `Effects/*.lean`) are stated against `satisfiedVm`
//! (`Dregg2/Circuit/Emit/EffectVmEmit.lean:346`) — an ABSTRACT `Prop`. The
//! parallel verified core `Dregg2/Circuit/Argus/InterpCore.lean` shrinks the
//! interpreter TCB by proving `decideVm = true ↔ satisfiedVm`
//! (`decideVm_iff_satisfiedVm`, axiom-clean) — a TOTAL, computable Boolean
//! reference. `InterpCore.lean`'s own doc-comment names the precise remaining
//! obligation as a Rust↔Lean transcription OUTSIDE Lean's kernel:
//!
//!   > "The TCB is (a) `decideVm` (verified here) and (b) the transcription
//!   >  `eval ≈ decideVm`."
//!   > "the multi-row AIR quantifies windows over the trace with the
//!   >  `when_transition` factoring … The factoring belongs to the LIFT, not
//!   >  the reference."
//!
//! THIS FILE IS THE ROW-DOMAIN (R2) LEG OF (b). It transcribes `decideVm`
//! into Rust (`oracle_decide_vm`, the multi-row lift = the running AIR's domain
//! factoring), then proves — over a GENERATED corpus, not a fixed ~6-case hand
//! list — that the running `EffectVmDescriptorAir`'s accept/reject decision
//! (`descriptor_air_accepts`, the audited verifier's exact predicate via
//! `p3_air::check_all_constraints`) EQUALS the reference on every case:
//!
//!     descriptor_air_accepts(desc, base, pi)  ==  oracle_decide_vm(desc, full, pi)
//!
//! where `full = base + hash-aux + range-bits` (the witness the prover commits to).
//!
//! ## Why a GENERATOR (the "exhaustive" in the name)
//!
//! The existing `lean_emitted_effectvm_transfer_differential`
//! (`lean_descriptor_air.rs`, in-crate) and `effect_vm_p3_descriptor_differential.rs`
//! pin the differential on the SINGLE transfer descriptor with a hand corpus of
//! honest + ~6 tampered witnesses. That binds the running AIR to `decideVm` for
//! ONE descriptor shape. The deeper edge is the INTERPRETER itself: does
//! `EffectVmDescriptorAir::eval` realize `decideVm` for ANY descriptor the IR can
//! name? This file generates random descriptors covering EVERY arm of the Rust
//! `VmConstraint` enum (`Gate` / `Transition` / `Boundary{First}` /
//! `Boundary{Last}` / `PiBinding{First}` /
//! `PiBinding{Last}`), every `LeanExpr` form (`Var` / `Const` / `Add` / `Mul`,
//! nested), every `VmHashSite` input form (`Col` / `Digest` / `Zero`, arity 2 and
//! 4, ordered digest chains), and `RangeSpec` (in- and out-of-range), over random
//! multi-row base traces — and checks the AIR-vs-reference equality on each,
//! tracking per-form coverage AND both accept/reject polarities so the agreement
//! is provably non-vacuous.
//!
//! A single AIR-vs-reference disagreement is a genuine interpreter drift (a
//! `decideVm` arm the running circuit decides differently) and FAILS the test.
//!
//! ## The HONEST residual (carried forward, not papered)
//!
//! This is an EXHAUSTIVELY-TESTED transcription bound (overwhelming, generated
//! coverage of every IR form), NOT a Lean-kernel PROOF that the Rust `eval`
//! equals `decideVm` for all inputs — that would require extracting/modelling the
//! p3 `eval` in Lean (out of scope; the Rust AIR is the un-verified leaf by
//! design, per `InterpCore.lean`). The hand-transcription `oracle_decide_vm`
//! itself is pinned against the LEAN-COMPUTED `decideVm` verdicts by the golden
//! corpus (`Dregg2/Circuit/Argus/InterpGolden.lean` ↔
//! `lean_descriptor_air.rs::tests::lean_decide_vm_golden_corpus_agrees` — every
//! arm, all four flag settings, both polarities), closing the cascade
//! `decideVm ≡ golden ≡ ℤ-transcription ≈ oracle ≡ AIR`, with the remaining
//! `≈` the ℤ→BabyBear field representation (corpus values bounded ≪ p, the
//! prover differentials running the real field). R1 from `InterpCore` is CLOSED: the Rust
//! `VmConstraint` enum has a `Boundary { row, body }` variant realizing Lean's
//! `VmConstraint.boundary` (a `when_first_row`/`when_last_row`-guarded `assert_zero`
//! of the body polynomial), and this generator NOW emits `Boundary{First}` and
//! `Boundary{Last}` forms — accept-leg (body vanishes on the boundary row) and
//! reject-leg (a perturbed boundary cell), both decided identically by the AIR and
//! the reference. The generator therefore covers the WHOLE representable IR.

use dregg_circuit::field::BabyBear;
use dregg_circuit::lean_descriptor_air::{
    EffectVmDescriptor, HashInput, LeanExpr, RangeSpec, VmConstraint, VmHashSite, VmRow,
    descriptor_air_accepts,
};
use dregg_circuit::plonky3_prover::{POSEIDON2_WIDTH, poseidon2_permute_aux_witness};

// ===========================================================================
// The EffectVM layout offsets (mirror of `effect_vm/columns.rs` /
// `EffectVmEmit.lean §0`, re-stated locally — the test owns no shared file).
// These are the SAME absolute indices the running AIR reads, so generated
// `Transition{hi,lo}` forms address the genuine state blocks.
// ===========================================================================
const NUM_EFFECTS: usize = 54;
const STATE_SIZE: usize = 14;
const STATE_BEFORE_BASE: usize = NUM_EFFECTS; // 54
const STATE_AFTER_BASE: usize = NUM_EFFECTS + STATE_SIZE + 8; // 76 (after 8 params)
const EFFECT_VM_WIDTH: usize = 186;

// ===========================================================================
// PART A — a tiny deterministic PRNG (SplitMix64). Zero new dependencies, fully
// reproducible: the seed sweep below replays the exact same corpus every run, so
// a failure is a stable, debuggable witness (the cargo registry `rand` is an
// optional feature of this crate and not enabled for the default test build).
// ===========================================================================

struct Rng {
    state: u64,
}

impl Rng {
    fn new(seed: u64) -> Self {
        Rng { state: seed }
    }

    /// One SplitMix64 step.
    fn next_u64(&mut self) -> u64 {
        self.state = self.state.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.state;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }

    /// Uniform-ish in `[0, n)` (n > 0). Modulo bias is irrelevant for a test
    /// generator over small ranges.
    fn below(&mut self, n: usize) -> usize {
        (self.next_u64() % (n as u64)) as usize
    }

    fn bool(&mut self) -> bool {
        self.next_u64() & 1 == 1
    }

    /// A small field value (kept well under 2^30 so the range-check wires can be
    /// in-range when we want them to be, and the recomposition arithmetic is
    /// transparent).
    fn small_field(&mut self) -> BabyBear {
        BabyBear::new((self.next_u64() % 1024) as u32)
    }
}

// ===========================================================================
// PART B — the ORACLE: a Rust transcription of Lean `decideVm`
// (`InterpCore.lean:272`) lifted to the MULTI-ROW domain, i.e. the running AIR's
// domain factoring (`EffectVmDescriptorAir::eval`, `lean_descriptor_air.rs:1417`).
//
//   * `decideConstraints` (the `∀ c ∈ constraints` conjunct of `satisfiedVm`):
//       - `Gate(body)`          → `body.eval(local) = 0`  on `when_transition`
//                                  (rows `0..n-2`).
//       - `Transition{hi,lo}`   → `next[sbCol hi] = local[saCol lo]` on the SAME
//                                  transition domain (`next` is the next row;
//                                  the transition domain excludes the last row,
//                                  so the wrap-around `next` is never read here).
//       - `PiBinding{First,..}` → `local[col] = pub[k]` on row 0 only.
//       - `PiBinding{Last,..}`  → `local[col] = pub[k]` on row n-1 only.
//   * `decideSites` (the `siteHoldsAll` conjunct): every site's `digest_col`
//       carries its genuine Poseidon2 digest, on EVERY row (whole domain), each
//       site reading the earlier sites' digests (the ordered chain).
//   * ranges: each wire's field value `< 2^bits`, on EVERY row.
//
// This matches `decideVm`'s two conjuncts per row-window, with the row-domain
// guards (`isFirst`/`isLast`/`isTransition`) instantiated exactly as
// `check_all_constraints` sets them: `is_first_row = (r==0)`,
// `is_last_row = (r==n-1)`, `is_transition = (r != n-1)`, `next = rows[(r+1)%n]`.
// (Confirmed against the p3 source `air/src/check_constraints.rs:618-682`.)
// ===========================================================================

/// Concrete evaluation of a `LeanExpr` over a field row — the `BabyBear` sibling
/// of `LeanExpr::eval_expr` (which builds `AB::Expr`). Same recursion, so a gate's
/// reference value matches its `eval`-time polynomial pointwise. This is the Rust
/// transcription of Lean `EmittedExpr.eval` (the `var`/`const`/`add`/`mul` AST
/// that `InterpCore.evalExpr_*` pins exhaustively).
fn eval_expr_concrete(e: &LeanExpr, row: &[BabyBear]) -> BabyBear {
    match e {
        LeanExpr::Var(i) => row[*i],
        LeanExpr::Const(c) => i64_to_bb(*c),
        LeanExpr::Add(a, b) => eval_expr_concrete(a, row) + eval_expr_concrete(b, row),
        LeanExpr::Mul(a, b) => eval_expr_concrete(a, row) * eval_expr_concrete(b, row),
    }
}

/// Reduce a signed i64 into BabyBear (matches `lean_descriptor_air::i64_to_babybear`;
/// re-stated locally so the test does not depend on that fn's visibility quirks).
fn i64_to_bb(c: i64) -> BabyBear {
    let p = ((1u64 << 31) - (1u64 << 27) + 1) as i64;
    let r = ((c % p) + p) % p;
    BabyBear::new(r as u32)
}

/// Resolve a hash-site input under `(row, earlier-digests)` — the Rust mirror of
/// Lean `HashInput.resolve` (`col`/`digest`/`zero`) and the AIR's
/// `vm_site_input_state_concrete`. `Digest k` out of range resolves to 0 (the
/// emitter only references earlier sites, so this never fires on well-formed
/// descriptors — the generator enforces `Digest k` ⟹ `k < site_index`).
fn resolve_input(inp: &HashInput, row: &[BabyBear], digests: &[BabyBear]) -> BabyBear {
    match inp {
        HashInput::Col(c) => row[*c],
        HashInput::Digest(k) => digests.get(*k).copied().unwrap_or(BabyBear::ZERO),
        HashInput::Zero => BabyBear::ZERO,
    }
}

/// The genuine Poseidon2 digest of a hash site (= `state[0]` of the final round),
/// resolving inputs as the AIR's `vm_site_input_state` does: inputs into rate
/// positions `0..arity`, position 4 = the arity capacity tag. This is the SAME
/// digest `extend_vm_trace` writes and `EffectVmDescriptorAir::eval` binds
/// (`auxw[len - WIDTH]`).
fn site_digest(site: &VmHashSite, row: &[BabyBear], digests: &[BabyBear]) -> BabyBear {
    let mut input = [BabyBear::ZERO; POSEIDON2_WIDTH];
    for (i, inp) in site.inputs.iter().enumerate() {
        input[i] = resolve_input(inp, row, digests);
    }
    input[4] = BabyBear::new(site.arity as u32);
    let auxw = poseidon2_permute_aux_witness(input);
    auxw[auxw.len() - POSEIDON2_WIDTH]
}

/// **`oracle_decide_vm`** — the multi-row lift of Lean `decideVm`, i.e. the
/// reference accept/reject the running `EffectVmDescriptorAir` must realize.
/// `rows` is the FULL trace (base + hash-aux + range-bits, exactly what the prover
/// commits to and `descriptor_air_accepts` constraint-checks); `public_inputs` is
/// the descriptor's PI prefix. Returns `true` iff the descriptor's denotation
/// accepts the witness on EVERY row-window.
fn oracle_decide_vm(
    desc: &EffectVmDescriptor,
    rows: &[Vec<BabyBear>],
    public_inputs: &[BabyBear],
) -> bool {
    let n = rows.len();
    if n == 0 {
        return false;
    }

    // -- hash sites + ranges hold on EVERY row (whole domain, like the AIR's bare
    //    `builder.assert_zero`). --
    for row in rows.iter() {
        let mut digests: Vec<BabyBear> = Vec::with_capacity(desc.hash_sites.len());
        for site in &desc.hash_sites {
            let d = site_digest(site, row, &digests);
            if row[site.digest_col] != d {
                return false;
            }
            digests.push(d);
        }
        for r in &desc.ranges {
            let v = row[r.wire].as_u32() as u64;
            // low `bits` bits recompose to the wire ⇔ high bits are 0 ⇔ v < 2^bits
            // (the bit-decomposition range gate's satisfiability — `eval`'s
            // booleanity + recomposition).
            if r.bits < 64 && v >= (1u64 << r.bits) {
                return false;
            }
        }
    }

    // -- per-row gates + transition continuity on the TRANSITION domain (rows
    //    0..n-2), mirroring the AIR's `when_transition`. --
    for r in 0..n.saturating_sub(1) {
        let local = &rows[r];
        let next = &rows[r + 1];
        for c in &desc.constraints {
            match c {
                VmConstraint::Gate(body) => {
                    if eval_expr_concrete(body, local) != BabyBear::ZERO {
                        return false;
                    }
                }
                VmConstraint::Transition { hi, lo } => {
                    if next[STATE_BEFORE_BASE + hi] != local[STATE_AFTER_BASE + lo] {
                        return false;
                    }
                }
                // Boundary + PI-binding fire only on the first/last row (below).
                VmConstraint::Boundary { .. } | VmConstraint::PiBinding { .. } => {}
            }
        }
    }

    // -- boundary forms: First on row 0, Last on row n-1 (the AIR's `when_first_row`
    //    / `when_last_row`). Both the polynomial-vanishing `Boundary` (R1) and the
    //    `PiBinding` are guarded `isFirst/isLast → P`, mirroring Lean
    //    `VmConstraint.holdsVm .boundary/.piBinding`. --
    for c in &desc.constraints {
        match c {
            VmConstraint::PiBinding { row, col, pi_index } => {
                let r = match row {
                    VmRow::First => 0,
                    VmRow::Last => n - 1,
                };
                if rows[r][*col] != public_inputs[*pi_index] {
                    return false;
                }
            }
            VmConstraint::Boundary { row, body } => {
                let r = match row {
                    VmRow::First => 0,
                    VmRow::Last => n - 1,
                };
                if eval_expr_concrete(body, &rows[r]) != BabyBear::ZERO {
                    return false;
                }
            }
            _ => {}
        }
    }

    true
}

// ===========================================================================
// PART C — the GENERATOR. Builds a random well-formed `EffectVmDescriptor` + a
// random multi-row base trace + PI vector, deliberately covering every IR form.
//
// "Well-formed" = `desc.check_bounds()` passes (all column / PI / digest indices
// in range): the generator chooses indices within `trace_width` / `piCount` and
// `Digest k` strictly earlier. The trace VALUES are random (so honest AND
// violating witnesses both occur), and we randomly choose, per hash site, whether
// to plant the genuine digest in `digest_col` (accept) or a wrong one (reject),
// and per range whether the wire is in- or out-of-range — driving BOTH polarities.
// ===========================================================================

/// A coverage tally so the test asserts every form was actually generated AND
/// that both accept/reject decisions occurred (non-vacuity).
#[derive(Default, Debug)]
struct Coverage {
    gate: usize,
    transition: usize,
    boundary_first: usize,
    boundary_last: usize,
    pi_first: usize,
    pi_last: usize,
    expr_var: usize,
    expr_const: usize,
    expr_add: usize,
    expr_mul: usize,
    site_col: usize,
    site_digest_input: usize,
    site_zero: usize,
    site_arity2: usize,
    site_arity4: usize,
    range_in: usize,
    range_out: usize,
    accepts: usize,
    rejects: usize,
    // which clause each injected reject broke (so every reject path is exercised).
    viol_gate: usize,
    viol_transition: usize,
    viol_boundary: usize,
    viol_pi: usize,
    viol_site: usize,
    viol_range: usize,
    cases: usize,
}

/// Generate a random `LeanExpr` over columns `[0, width)`, depth-bounded, tallying
/// every form. We bias leaves toward `Var` (so gates actually read the trace) and
/// keep constants small/signed (so `Const` reduction and negative handling are hit).
fn gen_expr(rng: &mut Rng, width: usize, depth: usize, cov: &mut Coverage) -> LeanExpr {
    if depth == 0 || rng.below(3) == 0 {
        // leaf
        if rng.below(4) == 0 {
            cov.expr_const += 1;
            // signed constants, including negatives (exercise i64→field reduction)
            let c = (rng.next_u64() % 17) as i64 - 8;
            LeanExpr::Const(c)
        } else {
            cov.expr_var += 1;
            LeanExpr::Var(rng.below(width))
        }
    } else if rng.bool() {
        cov.expr_add += 1;
        LeanExpr::Add(
            Box::new(gen_expr(rng, width, depth - 1, cov)),
            Box::new(gen_expr(rng, width, depth - 1, cov)),
        )
    } else {
        cov.expr_mul += 1;
        LeanExpr::Mul(
            Box::new(gen_expr(rng, width, depth - 1, cov)),
            Box::new(gen_expr(rng, width, depth - 1, cov)),
        )
    }
}

/// Negate a `LeanExpr` as `Mul(Const(-1), e)` — the canonical "subtract" the Lean
/// emitter uses (`EffectVmEmit` gates are `lhs + (-1)·rhs`).
fn neg(e: LeanExpr) -> LeanExpr {
    LeanExpr::Mul(Box::new(LeanExpr::Const(-1)), Box::new(e))
}

/// A generated case: a descriptor, the random base trace, the PI vector, and the
/// INTENDED polarity (what the reference SHOULD decide). The test cross-checks the
/// reference decision against this intent (catching a generator bug), then checks
/// the running AIR equals the reference.
struct Case {
    desc: EffectVmDescriptor,
    base: Vec<Vec<BabyBear>>,
    pi: Vec<BabyBear>,
    intended_accept: bool,
}

/// Generate one random well-formed case, with a SATISFYING witness built by
/// construction, then (when `target_accept == false`) ONE injected violation so
/// the case rejects. `width = EFFECT_VM_WIDTH` so the layout offsets and the
/// Poseidon2 aux extension match the running interpreter exactly.
///
/// Construction order (so the witness genuinely satisfies the descriptor):
///   1. random base trace (the "scratch" values gates/sites read).
///   2. gates: a mix of TAUTOLOGICAL gates `e + (-1)·e` (vanish on any trace,
///      arbitrary AST → Var/Const/Add/Mul coverage) and EQUALITY gates
///      `col[i] - col[j]` with the trace forced so `col[i]==col[j]` (so a later
///      perturbation can break exactly this gate).
///   3. transitions: pick `(hi,lo)` then SET `next.before[hi] = local.after[lo]`
///      across the window so continuity holds.
///   4. PI bindings: pick `(col, k)` then DERIVE `pi[k] = trace[row][col]`.
///   5. hash sites: plant the GENUINE digest in `digest_col`.
///   6. ranges: force each wire in-range.
/// Then if `!target_accept`, break exactly one clause (chosen by `viol`).
fn gen_case(rng: &mut Rng, target_accept: bool, cov: &mut Coverage) -> Case {
    let width = EFFECT_VM_WIDTH;
    let n_rows = 2 + rng.below(3); // 2..4 rows
    // ≥2 public inputs so the first- and last-row PI bindings always get DISTINCT
    // slots (no shared-slot special case — keeps the satisfying-witness derivation a
    // single clean dead-last pass).
    let pi_count = 2 + rng.below(4); // 2..5 public inputs

    // ---- the random base scratch trace. ----
    let mut base: Vec<Vec<BabyBear>> = (0..n_rows)
        .map(|_| (0..width).map(|_| rng.small_field()).collect())
        .collect();

    let mut constraints: Vec<VmConstraint> = Vec::new();

    // Track the equality gates' (i,j) cell pairs so we can break one for a reject.
    // Each equality gate gets a DISJOINT cell pair (so forcing one never disturbs
    // another's equality). The param block [68,76) holds up to 4 disjoint pairs.
    let mut eq_pairs: Vec<(usize, usize)> = Vec::new();
    let mut eq_slot = 0usize;

    // ---- (2) gates. ----
    let n_gates = 2 + rng.below(2); // 2..3 gates
    for _ in 0..n_gates {
        // prefer an equality gate when a disjoint pair slot is still available, else
        // a tautological gate; randomized but capped at 4 equality gates.
        if rng.bool() && eq_slot < 4 {
            // equality gate col[i] - col[j], trace forced i==j on a DISJOINT param
            // pair (never collides with sites' digest_col or range wires). Breakable.
            cov.gate += 1;
            cov.expr_var += 2; // two Var leaves
            cov.expr_add += 1;
            cov.expr_mul += 1; // the (-1)· multiply
            cov.expr_const += 1;
            let i = 68 + 2 * eq_slot; // param block [68,76), disjoint pairs
            let j = 69 + 2 * eq_slot;
            eq_slot += 1;
            for row in base.iter_mut() {
                row[j] = row[i]; // force equality so the gate vanishes
            }
            eq_pairs.push((i, j));
            constraints.push(VmConstraint::Gate(LeanExpr::Add(
                Box::new(LeanExpr::Var(i)),
                Box::new(neg(LeanExpr::Var(j))),
            )));
        } else {
            // tautological gate: e + (-1)·e  (always vanishes, rich AST → expr forms).
            cov.gate += 1;
            let e = gen_expr(rng, width, 3, cov);
            constraints.push(VmConstraint::Gate(LeanExpr::Add(
                Box::new(e.clone()),
                Box::new(neg(e)),
            )));
        }
    }

    // ---- (3) transitions: record `(hi,lo)` with DISJOINT `hi` targets (so the
    //      continuity-forcing of one never overwrites another's). The actual
    //      forcing (`next.before[hi] = local.after[lo]`) is applied LAST, after
    //      ranges/digests, so nothing clobbers it (state_before [54,68) is touched
    //      by no other step). --
    let n_trans = 1 + rng.below(2); // 1..2 transitions
    let mut trans_specs: Vec<(usize, usize)> = Vec::new();
    let mut used_hi: Vec<usize> = Vec::new();
    for _ in 0..n_trans {
        // pick an unused `hi` (STATE_SIZE = 14 ≫ n_trans, so this always succeeds).
        let mut hi = rng.below(STATE_SIZE);
        while used_hi.contains(&hi) {
            hi = (hi + 1) % STATE_SIZE;
        }
        used_hi.push(hi);
        let lo = rng.below(STATE_SIZE);
        cov.transition += 1;
        trans_specs.push((hi, lo));
        constraints.push(VmConstraint::Transition { hi, lo });
    }

    // ---- (4) PI bindings: derive pi[k] = trace[boundary-row][col]. ----
    // first-row binding
    let pi_first_col = rng.below(width);
    let pi_first_k = rng.below(pi_count);
    cov.pi_first += 1;
    constraints.push(VmConstraint::PiBinding {
        row: VmRow::First,
        col: pi_first_col,
        pi_index: pi_first_k,
    });
    // last-row binding (distinct PI slot so it doesn't clash with the first one's
    // derived value on a different boundary row).
    let pi_last_col = rng.below(width);
    let pi_last_k = if pi_count > 1 {
        // pick a slot != pi_first_k to keep both derivations independent.
        let mut k = rng.below(pi_count);
        if k == pi_first_k {
            k = (k + 1) % pi_count;
        }
        k
    } else {
        0
    };
    cov.pi_last += 1;
    constraints.push(VmConstraint::PiBinding {
        row: VmRow::Last,
        col: pi_last_col,
        pi_index: pi_last_k,
    });

    // ---- (4b) boundary forms (R1): an equality polynomial `col[i] - col[j]` that must
    //      VANISH on the boundary row (`when_first_row` / `when_last_row`). We force
    //      `col[i] == col[j]` on the boundary row using a DISJOINT cell pair in the AUX
    //      region [100,104) — touched by NO other clause: the transition step reads
    //      `state_after [76,90)` (sources) and writes `state_before [54,68)`; eq-gate pairs
    //      are param [68,76); range wires are [2,5); digest cols are [120,..). So a boundary
    //      break perturbs ONLY the boundary clause (modulo a hash site reading the cell as a
    //      Col input, which we re-plant for). One First and one Last boundary so both row
    //      tags are covered; the (row, i, j) triples are recorded so a reject can break
    //      exactly one boundary. --
    let mut boundary_specs: Vec<(VmRow, usize, usize)> = Vec::new();
    for (bi, brow) in [VmRow::First, VmRow::Last].into_iter().enumerate() {
        // disjoint AUX pair per boundary: [100,102) for First, [102,104) for Last.
        let i = 100 + 2 * bi;
        let j = 101 + 2 * bi;
        let brow_idx = match brow {
            VmRow::First => 0,
            VmRow::Last => n_rows - 1,
        };
        base[brow_idx][j] = base[brow_idx][i]; // force the body to vanish on the boundary row
        match brow {
            VmRow::First => cov.boundary_first += 1,
            VmRow::Last => cov.boundary_last += 1,
        }
        cov.expr_var += 2;
        cov.expr_add += 1;
        cov.expr_mul += 1;
        cov.expr_const += 1;
        boundary_specs.push((brow, i, j));
        constraints.push(VmConstraint::Boundary {
            row: brow,
            body: LeanExpr::Add(Box::new(LeanExpr::Var(i)), Box::new(neg(LeanExpr::Var(j)))),
        });
    }

    // ---- (5) hash sites: 0..2 ordered sites; genuine digest planted below. The
    //      digest columns live in [120, 120+n_sites). A site's `Col` input must NOT
    //      read any digest column (else the site is self-referential: planting its
    //      digest would change an input it reads, so no fixed point exists — the
    //      running interpreter's `vm_site_input_state` reads `local[c]` BEFORE the
    //      digest is bound, and the real emitter never aliases a digest cell as an
    //      input). So `Col` inputs are drawn from the SAFE pool below 120. --
    let n_sites = rng.below(3);
    let col_pool = 120usize; // safe Col-input columns: [0, 120) (all below digest cols)
    let mut hash_sites: Vec<VmHashSite> = Vec::new();
    for si in 0..n_sites {
        let arity = if rng.bool() { 2 } else { 4 };
        if arity == 2 {
            cov.site_arity2 += 1;
        } else {
            cov.site_arity4 += 1;
        }
        let mut inputs: Vec<HashInput> = Vec::with_capacity(arity);
        for _ in 0..arity {
            let pick = rng.below(3);
            if pick == 1 && si > 0 {
                cov.site_digest_input += 1;
                inputs.push(HashInput::Digest(rng.below(si)));
            } else if pick == 2 {
                cov.site_zero += 1;
                inputs.push(HashInput::Zero);
            } else {
                cov.site_col += 1;
                inputs.push(HashInput::Col(rng.below(col_pool)));
            }
        }
        let digest_col = 120 + si; // distinct AUX column per site, inside [0,width)
        hash_sites.push(VmHashSite {
            digest_col,
            arity,
            inputs,
        });
    }

    // ---- (6) ranges: 0..2 checks; force in-range below. ----
    let n_ranges = rng.below(3);
    let mut ranges: Vec<RangeSpec> = Vec::new();
    for ri in 0..n_ranges {
        let wire = 2 + ri; // distinct small cols, away from digest_col / param block
        ranges.push(RangeSpec { wire, bits: 12 });
    }
    // force every range wire in-range on every row.
    for r in &ranges {
        for row in base.iter_mut() {
            row[r.wire] = BabyBear::new((rng.next_u64() % (1 << r.bits)) as u32);
        }
    }

    // ---- apply transition continuity LAST among trace WRITES (state_before
    //      [54,68) is written by nothing else; the disjoint `hi` guarantees no two
    //      transitions clobber each other). After this, every gate/transition
    //      clause is satisfied and the trace's value cells are FINAL. --
    for &(hi, lo) in &trans_specs {
        for r in 0..n_rows - 1 {
            let v = base[r][STATE_AFTER_BASE + lo];
            base[r + 1][STATE_BEFORE_BASE + hi] = v;
        }
    }

    // Plant the GENUINE site digests (now that all input cells are final). Process
    // sites in order; later sites read earlier genuine digests, exactly as the AIR's
    // `digests.push(d)` loop does. (Site `Col` inputs never read a digest column —
    // enforced above — so this is a genuine fixed point.)
    for row in base.iter_mut() {
        let mut digests: Vec<BabyBear> = Vec::with_capacity(hash_sites.len());
        for site in &hash_sites {
            let genuine = site_digest(site, row, &digests);
            row[site.digest_col] = genuine;
            digests.push(genuine);
        }
    }

    // Derive the PI vector from the (now-FINAL) boundary rows so both bindings hold.
    // `pi_first_k != pi_last_k` (pi_count ≥ 2), so the two derivations are
    // independent and NO trace rewrite is needed.
    let mut pi: Vec<BabyBear> = (0..pi_count).map(|_| rng.small_field()).collect();
    pi[pi_first_k] = base[0][pi_first_col];
    pi[pi_last_k] = base[n_rows - 1][pi_last_col];

    // At this point the witness SATISFIES the descriptor. Tally the accept-leg
    // range sub-coverage (genuine digests / in-range wires are implied by accept).
    for _ in &ranges {
        for _ in 0..n_rows {
            cov.range_in += 1;
        }
    }

    let mut intended_accept = true;

    // ---- inject ONE violation when a reject case was requested. ----
    if !target_accept {
        intended_accept = false;
        // choose a violation among the clauses that are PRESENT (each tag enabled
        // only when that clause exists in this descriptor).
        let mut kinds: Vec<u8> = Vec::new();
        if !eq_pairs.is_empty() {
            kinds.push(0);
        }
        if !trans_specs.is_empty() {
            kinds.push(1);
        }
        kinds.push(2); // PI-first is always present
        kinds.push(3); // PI-last is always present
        if !hash_sites.is_empty() {
            kinds.push(4);
        }
        if !ranges.is_empty() {
            kinds.push(5);
        }
        kinds.push(6); // boundary forms are always present (one First + one Last)
        let viol = kinds[rng.below(kinds.len())];
        match viol {
            0 => {
                // break an equality gate: bump col[i] on a TRANSITION row (row 0)
                // so the per-row gate fires (gates run on rows 0..n-2).
                let (i, _j) = eq_pairs[rng.below(eq_pairs.len())];
                base[0][i] = base[0][i] + BabyBear::new(1);
                // re-plant site digests on row 0 (col i is in the param block; a site
                // could read it as a Col input).
                let mut digests: Vec<BabyBear> = Vec::with_capacity(hash_sites.len());
                for site in &hash_sites {
                    let genuine = site_digest(site, &base[0], &digests);
                    base[0][site.digest_col] = genuine;
                    digests.push(genuine);
                }
                cov.viol_gate += 1;
            }
            1 => {
                // break a transition: bump next.before[hi] on the first window.
                let (hi, _lo) = trans_specs[rng.below(trans_specs.len())];
                base[1][STATE_BEFORE_BASE + hi] =
                    base[1][STATE_BEFORE_BASE + hi] + BabyBear::new(1);
                // re-plant row1 site digests (the bumped cell could feed a site).
                let mut digests: Vec<BabyBear> = Vec::with_capacity(hash_sites.len());
                for site in &hash_sites {
                    let genuine = site_digest(site, &base[1], &digests);
                    base[1][site.digest_col] = genuine;
                    digests.push(genuine);
                }
                cov.viol_transition += 1;
            }
            2 => {
                // break the first-row PI binding: bump pi[pi_first_k].
                pi[pi_first_k] = pi[pi_first_k] + BabyBear::new(1);
                // if the last binding shares the slot (pi_count==1) this also breaks
                // it; still a reject. To keep it a pure first-row break when slots are
                // distinct, that's already the case.
                cov.viol_pi += 1;
            }
            3 => {
                // break the last-row PI binding: bump pi[pi_last_k].
                pi[pi_last_k] = pi[pi_last_k] + BabyBear::new(1);
                cov.viol_pi += 1;
            }
            4 => {
                // break a hash-site digest binding: corrupt one site's digest_col on
                // some row (the binding holds on the WHOLE domain).
                let s = rng.below(hash_sites.len());
                let r = rng.below(n_rows);
                let dc = hash_sites[s].digest_col;
                base[r][dc] = base[r][dc] + BabyBear::new(1);
                cov.viol_site += 1;
            }
            5 => {
                // break a range: push a wire out of range on some row.
                let r = rng.below(ranges.len());
                let row = rng.below(n_rows);
                let bits = ranges[r].bits;
                base[row][ranges[r].wire] = BabyBear::new((1u32 << bits) + 1);
                cov.range_out += 1;
                // re-plant site digests on that row (the wire could feed a site).
                let mut digests: Vec<BabyBear> = Vec::with_capacity(hash_sites.len());
                for site in &hash_sites {
                    let genuine = site_digest(site, &base[row], &digests);
                    base[row][site.digest_col] = genuine;
                    digests.push(genuine);
                }
                cov.viol_range += 1;
            }
            6 => {
                // break a boundary (R1): bump col[i] on the boundary row so `col[i]-col[j]`
                // no longer vanishes there. The body is checked ONLY on the boundary row
                // (when_first_row / when_last_row), so this fires exactly the boundary
                // clause — the anti-vacuity tooth that the running AIR REJECTS a
                // boundary-violating witness.
                let (brow, i, _j) = boundary_specs[rng.below(boundary_specs.len())];
                let brow_idx = match brow {
                    VmRow::First => 0,
                    VmRow::Last => n_rows - 1,
                };
                base[brow_idx][i] = base[brow_idx][i] + BabyBear::new(1);
                // re-plant that row's site digests (the bumped AUX cell could feed a site).
                let mut digests: Vec<BabyBear> = Vec::with_capacity(hash_sites.len());
                for site in &hash_sites {
                    let genuine = site_digest(site, &base[brow_idx], &digests);
                    base[brow_idx][site.digest_col] = genuine;
                    digests.push(genuine);
                }
                cov.viol_boundary += 1;
            }
            _ => unreachable!(),
        }
    }

    let desc = EffectVmDescriptor {
        name: "dregg-exhaustive-diff-v0".to_string(),
        trace_width: width,
        public_input_count: pi_count,
        constraints,
        hash_sites,
        ranges,
    };

    Case {
        desc,
        base,
        pi,
        intended_accept,
    }
}

// ===========================================================================
// PART D — the exhaustive differential test.
// ===========================================================================

/// **THE EXHAUSTIVE DIFFERENTIAL.** Over a generated corpus covering every IR
/// form, the running `EffectVmDescriptorAir` (via the audited verifier's exact
/// FRI-free predicate `descriptor_air_accepts`) decides accept/reject IDENTICALLY
/// to the verified reference `decideVm` (transcribed as `oracle_decide_vm`,
/// multi-row lift). A disagreement is an interpreter drift and fails here.
///
/// This REPLACES the fixed ~6-case hand corpus of the transfer differential with
/// a generator that exercises the WHOLE representable IR, discharging the
/// Rust-side `eval ≈ decideVm` transcription obligation `InterpCore.lean` §5
/// names — with full per-form coverage AND both polarities (non-vacuity).
#[test]
fn exhaustive_descriptor_air_decides_decide_vm() {
    let mut cov = Coverage::default();
    let mut disagreements: Vec<String> = Vec::new();
    // A second tooth: the GENERATOR's intent must match the REFERENCE. If a case we
    // built to accept is rejected by `oracle_decide_vm` (or vice versa), the
    // generator (not the AIR) is buggy — catch it so a generator bug can never
    // silently make the differential vacuous (e.g. both reject for the wrong reason).
    let mut intent_mismatches: Vec<String> = Vec::new();

    // A reproducible seed sweep. Each seed yields one random case; we ALTERNATE the
    // intended polarity so the corpus is ~half satisfying witnesses (accept) and
    // ~half single-violation witnesses (reject). The assert block below FAILS if any
    // IR form, either polarity, or any reject-clause path is missing.
    const N_CASES: usize = 320;
    for seed in 0..N_CASES as u64 {
        let mut rng = Rng::new(seed.wrapping_mul(0x1234_5678_9ABC_DEF1).wrapping_add(1));
        let target_accept = seed % 2 == 0;
        let case = gen_case(&mut rng, target_accept, &mut cov);
        cov.cases += 1;

        // The reference verdict (multi-row `decideVm`) over the witness the prover
        // commits to. `descriptor_air_accepts` extends the base internally with the
        // Poseidon2 aux + range-bit columns; the oracle computes the SAME hash digest
        // and range-bit recomposition as a deterministic function of the base row, so
        // checking them on the base row is equivalent to checking the extended aux
        // columns the AIR constrains. Gate/transition/PI clauses read only base
        // columns. So `oracle_decide_vm(desc, base, pi)` is exactly the reference over
        // the committed witness.
        let oracle = oracle_decide_vm(&case.desc, &case.base, &case.pi);
        let air = descriptor_air_accepts(&case.desc, &case.base, &case.pi);

        if oracle {
            cov.accepts += 1;
        } else {
            cov.rejects += 1;
        }

        if oracle != case.intended_accept {
            intent_mismatches.push(format!(
                "seed {seed}: generator intended accept={} but reference decided {oracle}",
                case.intended_accept
            ));
        }

        if oracle != air {
            disagreements.push(format!(
                "seed {seed} (intended accept={}): oracle(decideVm)={oracle} but \
                 AIR-accepts={air}",
                case.intended_accept
            ));
            if disagreements.len() >= 8 {
                break;
            }
        }
    }

    assert!(
        intent_mismatches.is_empty(),
        "GENERATOR/REFERENCE DESYNC — a constructed witness did not decide as intended \
         (the generator is buggy, not the AIR) on {} case(s):\n{}",
        intent_mismatches.len(),
        intent_mismatches.join("\n")
    );

    assert!(
        disagreements.is_empty(),
        "INTERPRETER DRIFT — the running EffectVmDescriptorAir decided differently \
         from the verified reference decideVm on {} case(s):\n{}",
        disagreements.len(),
        disagreements.join("\n")
    );

    // ---- COVERAGE: every IR form was generated, AND both polarities occurred. ----
    // (A vacuous "always reject" or "always accept" agreement is impossible if both
    // accepts and rejects are present and the AIR matched on every case.)
    let missing: Vec<(&str, usize)> = [
        ("constraint:Gate", cov.gate),
        ("constraint:Transition", cov.transition),
        ("constraint:Boundary{First}", cov.boundary_first),
        ("constraint:Boundary{Last}", cov.boundary_last),
        ("constraint:PiBinding{First}", cov.pi_first),
        ("constraint:PiBinding{Last}", cov.pi_last),
        ("expr:Var", cov.expr_var),
        ("expr:Const", cov.expr_const),
        ("expr:Add", cov.expr_add),
        ("expr:Mul", cov.expr_mul),
        ("hashinput:Col", cov.site_col),
        ("hashinput:Digest", cov.site_digest_input),
        ("hashinput:Zero", cov.site_zero),
        ("hashsite:arity2", cov.site_arity2),
        ("hashsite:arity4", cov.site_arity4),
        ("range:in-range", cov.range_in),
        ("range:out-of-range", cov.range_out),
        ("polarity:accept", cov.accepts),
        ("polarity:reject", cov.rejects),
        // every reject-clause path must be exercised (so the AIR's REJECT decision is
        // tested for a broken gate, transition, PI, hash-site, AND range — not just
        // one easy clause).
        ("reject-via:gate", cov.viol_gate),
        ("reject-via:transition", cov.viol_transition),
        ("reject-via:boundary", cov.viol_boundary),
        ("reject-via:pi", cov.viol_pi),
        ("reject-via:hash-site", cov.viol_site),
        ("reject-via:range", cov.viol_range),
    ]
    .into_iter()
    .filter(|(_, c)| *c == 0)
    .collect();

    assert!(
        missing.is_empty(),
        "COVERAGE GAP — the generator never produced: {:?}\nfull coverage = {:?}",
        missing,
        cov
    );

    eprintln!(
        "exhaustive differential PASS: {} cases, AIR ≡ decideVm on all; coverage = {:?}",
        cov.cases, cov
    );
}

/// A FOCUSED non-vacuity tooth: for a fixed minimal single-gate descriptor whose
/// gate is `Var(76) - Var(54) = 0` (the transfer-style balance-equality shape), an
/// honest row (col76 == col54) is ACCEPTED by BOTH the AIR and the reference, and a
/// row that breaks it is REJECTED by BOTH — pinned directly (not generated), so the
/// differential's sharp tooth is visible without reading the generator. Mirrors
/// `InterpCore.decideVm_selectorOnly_{accepts,rejects}` in spirit: a real gate,
/// both polarities, through the running circuit.
#[test]
fn focused_single_gate_both_polarities_agree() {
    let width = EFFECT_VM_WIDTH;
    // gate body: col[76] - col[54]  (Add(Var 76, Mul(Const -1, Var 54)))
    let body = LeanExpr::Add(
        Box::new(LeanExpr::Var(76)),
        Box::new(LeanExpr::Mul(
            Box::new(LeanExpr::Const(-1)),
            Box::new(LeanExpr::Var(54)),
        )),
    );
    let desc = EffectVmDescriptor {
        name: "dregg-focused-gate-v0".to_string(),
        trace_width: width,
        public_input_count: 0,
        constraints: vec![VmConstraint::Gate(body)],
        hash_sites: vec![],
        ranges: vec![],
    };

    let mk_rows = |c76: u32, c54: u32| -> Vec<Vec<BabyBear>> {
        let mut row = vec![BabyBear::ZERO; width];
        row[76] = BabyBear::new(c76);
        row[54] = BabyBear::new(c54);
        // a 2-row trace; both rows satisfy/break identically (the gate is per-row on
        // the transition domain = row 0 here).
        vec![row.clone(), row]
    };

    // honest: col76 == col54 ⇒ both accept.
    let honest = mk_rows(42, 42);
    assert!(
        oracle_decide_vm(&desc, &honest, &[]),
        "reference must accept the honest balance-equality row"
    );
    assert!(
        descriptor_air_accepts(&desc, &honest, &[]),
        "running AIR must accept the honest balance-equality row"
    );

    // broken: col76 != col54 ⇒ both reject.
    let broken = mk_rows(42, 43);
    assert!(
        !oracle_decide_vm(&desc, &broken, &[]),
        "reference must reject the broken balance-equality row"
    );
    assert!(
        !descriptor_air_accepts(&desc, &broken, &[]),
        "running AIR must reject the broken balance-equality row"
    );
}
