//! The **Cert-F STARK** — the fhEgg Stage-1 Tier-1 bridge: a Cert-F primal-dual
//! certificate proven in a REAL dregg STARK over the verified Cert-F check.
//!
//! ## What this is (the wiring step the fhegg-solver named)
//!
//! `fhegg-solver/src/air.rs` emits the Cert-F check as a structured
//! [`ConstraintSystem`](../../../fhegg-solver/src/air.rs) — the `n + 4m + 1`
//! rows `conservation(==0) · box(≥0) · slack_sign(≥0) · dual_feas(≥0) ·
//! duality_gap(≤ε)`. `metatheory/Market/CertF.lean` PROVES that check sound
//! (`certifies_epsilon_optimal`, `weak_duality`) and emits it as a linear
//! `Dregg2.Circuit` (`certCircuit`, `satisfied certCircuit ↔ certificate`). Both
//! halves stopped one wiring step short: turning the emitted constraint rows into
//! a real dregg STARK-provable AIR and proving a certificate in the production
//! prover. THIS module is that step.
//!
//! For the circulation LP `max wᵀf s.t. Af=0, 0≤f≤c` with dual `(π, s)`, a
//! certificate `(f, π, s)` is `ε`-optimal iff
//!
//! ```text
//!   A f = 0,   0 ≤ f ≤ c,   s ≥ 0,   Aᵀπ + s ≥ w,   cᵀs − wᵀf ≤ ε
//! ```
//!
//! ([`CertF::check`](../../../fhegg-solver/src/cert.rs) / `Market.Certified`).
//! [`cert_f_descriptor`] lowers exactly those rows to an
//! [`EffectVmDescriptor2`] over the witness columns `(f, π, s)`; the PUBLIC program
//! `(A, w, c, ε)` rides as descriptor constants. [`prove_cert_f`] proves the AIR in
//! the production IR-v2 STARK ([`prove_vm_descriptor2`], BabyBear + FRI); the
//! witness `(f, π, s)` — the private flows/allocations — lives ONLY in the trace
//! (hidden under the hiding PCS), and the only public value exposed is the cleared
//! volume `wᵀf`. That is the Tier-1 posture (`docs/deos/DREGGFI-PRIVACY-TIERS.md`):
//! solver-sees, PRIVATE-FROM-THE-WORLD, PQ.
//!
//! ## The rows, and how each is enforced in-AIR
//!
//!   * **conservation** `Σ_{head=i} f_e − Σ_{tail=i} f_e = 0` — one arithmetic Gate
//!     per node (equality). Field-sound because every `f_e` is range-bounded below
//!     the wrap point (see the range gadget), so the field equation `≡ 0 (mod p)` is
//!     the integer equation `= 0`.
//!   * **box lower** `f_e ≥ 0` — the range gadget on `f_e` (bit-decompose into
//!     `VALUE_BITS` booleans that recompose to it, forcing `f_e ∈ [0, 2^VALUE_BITS)`).
//!   * **box upper** `c_e − f_e ≥ 0` — a slack column `u_e == c_e − f_e` (Gate) with
//!     the range gadget on `u_e`.
//!   * **slack sign** `s_e ≥ 0` — the range gadget on `s_e`.
//!   * **dual feas** `π_head − π_tail + s_e − w_e ≥ 0` — a slack column
//!     `d_e == π_head − π_tail + s_e − w_e` (Gate) with the range gadget on `d_e`.
//!   * **gap** `cᵀs − wᵀf ≤ ε` — a slack column `g == ε − (cᵀs − wᵀf)` (Gate) with
//!     the range gadget on `g` (so `g ≥ 0`, i.e. `gap ≤ ε`).
//!
//! Every gate is AFFINE in the witness: `w, c, ε` are public constants (coefficients),
//! so `cᵀs`, `wᵀf`, `w_e`, `c_e` never multiply a second witness cell. This is the
//! `O(m + nnz A)` linear check `CertF.lean §4` describes — the AIR enforces the
//! CERTIFICATE, never the `T` solver iterations (untrusted search, checked output).
//!
//! ## Honest scope
//!
//! Tier-1 = STARK-ZK, private-from-the-WORLD (the world learns the public clearing
//! `wᵀf` + the program `(A,w,c,ε)`, not the individual orders `f, π, s`). It is NOT
//! Tier-0 no-viewer: the SOLVER sees plaintext orders. The ZK-hiding of the witness
//! rests on the STARK's zero-knowledge (the reveal-nothing floor — the formal
//! "the proof leaks nothing beyond `wᵀf`" theorem is the sibling ZK lane, named, not
//! discharged here). The range gadget closes integer conservation for values below
//! `2^VALUE_BITS`; larger amounts ride a wider decomposition or the off-AIR range
//! proof (the same BabyBear field cap the shielded-ring AIR documents).

use dregg_circuit::descriptor_ir2::DreggStarkConfig;
use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, Ir2BatchProof, MemBoundaryWitness, VmConstraint2, prove_vm_descriptor2,
    verify_vm_descriptor2,
};
use dregg_circuit::field::{BABYBEAR_P, BabyBear};
use dregg_circuit::lean_descriptor_air::{LeanExpr, VmConstraint, VmRow};

/// The in-AIR range-gadget bit-width. A range target is bit-decomposed into this
/// many booleans that recompose to it, forcing it into `[0, 2^VALUE_BITS)`. `28`
/// leaves headroom below `p ≈ 2^30.9`: a conservation node of degree `d` sums `d`
/// range-bounded flows, and `MAX_NODE_DEGREE · 2^VALUE_BITS < p` (asserted per
/// descriptor) keeps that field sum canonical, so the field conservation gate IS the
/// integer conservation (no wraparound). Amounts `≥ 2^VALUE_BITS` need a wider
/// decomposition (named residual — one BabyBear field caps the no-wrap range).
pub const VALUE_BITS: usize = 28;

/// The main-trace height (power of two). Every row carries the same constant
/// certificate data; gates fire on the transition rows, the objective PiBinding on
/// the first.
const TRACE_HEIGHT: usize = 8;

/// An INTEGER Cert-F certificate: the public program `(edges, w, c, ε)` + the private
/// primal-dual witness `(f, π, s)`. The STARK proves this exact object. Integer-valued
/// (the field the STARK proves over is `ℤ/p`, and `Market.CertF` is proved over any
/// ordered ring, instantiated at `ℤ`); a floating-point solver output is brought here
/// by fixed-point scaling ([`CertFWitness::from_solution_json`]).
#[derive(Clone, Debug)]
pub struct CertFWitness {
    /// Number of nodes (rows of `A`).
    pub n_nodes: usize,
    /// Public incidence, edge list `(tail, head)` (columns of `A`).
    pub edges: Vec<(u32, u32)>,
    /// Public objective weights `w`.
    pub w: Vec<i64>,
    /// Public capacities `c`.
    pub c: Vec<i64>,
    /// Private primal flow `f`.
    pub f: Vec<i64>,
    /// Private dual potentials `π`.
    pub pi: Vec<i64>,
    /// Private dual slacks `s`.
    pub s: Vec<i64>,
    /// The public accuracy target `ε` (`gap ≤ ε` ⇒ ε-optimal).
    pub epsilon: i64,
}

/// The result of the native Cert-F check over integers — the exact predicate
/// `Market.Certified` decides, and the exact predicate the AIR enforces per row.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CertFCheck {
    pub conserves: bool,
    pub box_ok: bool,
    pub slack_sign_ok: bool,
    pub dual_feasible: bool,
    pub gap_ok: bool,
    pub gap: i64,
    pub valid: bool,
}

impl CertFWitness {
    /// `m` = number of edges.
    pub fn m(&self) -> usize {
        self.edges.len()
    }

    /// `Aᵀπ` at edge `e`: `π_head − π_tail` (the incidence transpose applied to π).
    fn at_pi(&self, e: usize) -> i64 {
        let (t, h) = self.edges[e];
        self.pi[h as usize] - self.pi[t as usize]
    }

    /// The conservation residual at node `i`: `Σ_{head=i} f_e − Σ_{tail=i} f_e`.
    fn conservation_residual(&self, i: usize) -> i64 {
        let mut acc = 0i64;
        for (e, &(t, h)) in self.edges.iter().enumerate() {
            if h as usize == i {
                acc += self.f[e];
            }
            if t as usize == i {
                acc -= self.f[e];
            }
        }
        acc
    }

    /// The box-upper slack `u_e = c_e − f_e`.
    fn box_upper_slack(&self, e: usize) -> i64 {
        self.c[e] - self.f[e]
    }

    /// The dual-feasibility slack `d_e = π_head − π_tail + s_e − w_e`.
    fn dual_slack(&self, e: usize) -> i64 {
        self.at_pi(e) + self.s[e] - self.w[e]
    }

    /// The duality gap `cᵀs − wᵀf`.
    pub fn gap(&self) -> i64 {
        let cs: i64 = self.c.iter().zip(&self.s).map(|(c, s)| c * s).sum();
        let wf: i64 = self.w.iter().zip(&self.f).map(|(w, f)| w * f).sum();
        cs - wf
    }

    /// The gap slack `g = ε − gap` (≥ 0 iff `gap ≤ ε`).
    fn gap_slack(&self) -> i64 {
        self.epsilon - self.gap()
    }

    /// The public objective `wᵀf` — the cleared volume the world learns.
    pub fn objective(&self) -> i64 {
        self.w.iter().zip(&self.f).map(|(w, f)| w * f).sum()
    }

    /// Run the Cert-F check over integers (the `Market.Certified` predicate). This is
    /// the authoritative accept/reject the AIR must match on both polarities.
    pub fn check(&self) -> CertFCheck {
        let conserves = (0..self.n_nodes).all(|i| self.conservation_residual(i) == 0);
        let box_ok = (0..self.m()).all(|e| self.f[e] >= 0 && self.f[e] <= self.c[e]);
        let slack_sign_ok = self.s.iter().all(|&s| s >= 0);
        let dual_feasible = (0..self.m()).all(|e| self.dual_slack(e) >= 0);
        let gap = self.gap();
        let gap_ok = gap <= self.epsilon;
        let valid = conserves && box_ok && slack_sign_ok && dual_feasible && gap_ok;
        CertFCheck {
            conserves,
            box_ok,
            slack_sign_ok,
            dual_feasible,
            gap_ok,
            gap,
            valid,
        }
    }

    // -- column layout -----------------------------------------------------------

    fn f_col(&self, e: usize) -> usize {
        e
    }
    fn s_col(&self, e: usize) -> usize {
        self.m() + e
    }
    fn pi_col(&self, i: usize) -> usize {
        2 * self.m() + i
    }
    fn obj_col(&self) -> usize {
        2 * self.m() + self.n_nodes
    }
    fn u_col(&self, e: usize) -> usize {
        self.obj_col() + 1 + e
    }
    fn d_col(&self, e: usize) -> usize {
        self.obj_col() + 1 + self.m() + e
    }
    fn g_col(&self) -> usize {
        self.obj_col() + 1 + 2 * self.m()
    }
    fn bit_base(&self) -> usize {
        self.g_col() + 1
    }
    /// The `4m + 1` range targets, in trace order: `f · u · s · d · g`.
    fn range_target_cols(&self) -> Vec<usize> {
        let m = self.m();
        let mut v = Vec::with_capacity(4 * m + 1);
        v.extend((0..m).map(|e| self.f_col(e)));
        v.extend((0..m).map(|e| self.u_col(e)));
        v.extend((0..m).map(|e| self.s_col(e)));
        v.extend((0..m).map(|e| self.d_col(e)));
        v.push(self.g_col());
        v
    }
    fn range_bit_col(&self, target: usize, j: usize) -> usize {
        self.bit_base() + target * VALUE_BITS + j
    }
    /// Full trace width: scalars + the `(4m+1)·VALUE_BITS` range bits.
    fn width(&self) -> usize {
        self.bit_base() + (4 * self.m() + 1) * VALUE_BITS
    }

    /// The public inputs the STARK exposes: `[wᵀf]` (the cleared volume). The witness
    /// `(f, π, s)` is NOT exposed — it stays hidden in the trace.
    pub fn public_inputs(&self) -> Vec<BabyBear> {
        vec![fe(self.objective())]
    }

    /// Build the base main trace (`TRACE_HEIGHT × width`). Every row is identical (the
    /// certificate is constant data); the range bits are the honest bit-decompositions
    /// of each range target. A tampered witness whose targets fall outside
    /// `[0, 2^VALUE_BITS)` has no recomposing bits ⇒ the recompose gate is violated
    /// (the soundness tooth).
    pub fn base_trace(&self) -> Vec<Vec<BabyBear>> {
        let m = self.m();
        let mut row = vec![BabyBear::ZERO; self.width()];
        for e in 0..m {
            row[self.f_col(e)] = fe(self.f[e]);
            row[self.s_col(e)] = fe(self.s[e]);
            row[self.u_col(e)] = fe(self.box_upper_slack(e));
            row[self.d_col(e)] = fe(self.dual_slack(e));
        }
        for i in 0..self.n_nodes {
            row[self.pi_col(i)] = fe(self.pi[i]);
        }
        row[self.obj_col()] = fe(self.objective());
        row[self.g_col()] = fe(self.gap_slack());

        // Range bits: low `VALUE_BITS` bits of each target's value (as an unsigned
        // canonical residue). For an in-range nonneg target these recompose to it; a
        // wrapped/negative/out-of-range target's low bits do NOT recompose to the
        // canonical field value, so the recompose gate rejects it.
        let targets = self.range_target_cols();
        for (t, &col) in targets.iter().enumerate() {
            let v = row[col].as_u32();
            for j in 0..VALUE_BITS {
                row[self.range_bit_col(t, j)] = BabyBear::new((v >> j) & 1);
            }
        }
        vec![row; TRACE_HEIGHT]
    }
}

/// `x − y` as a `LeanExpr`.
fn sub(x: LeanExpr, y: LeanExpr) -> LeanExpr {
    LeanExpr::add(x, LeanExpr::mul(LeanExpr::Const(-1), y))
}

/// A pure per-row vanishing gate `body == 0`.
fn gate(body: LeanExpr) -> VmConstraint2 {
    VmConstraint2::Base(VmConstraint::Gate(body))
}

/// Lift a signed integer to its canonical BabyBear representative.
fn fe(x: i64) -> BabyBear {
    let p = BABYBEAR_P as i64;
    let r = ((x % p) + p) % p; // canonical in [0, p)
    BabyBear::new(r as u32)
}

/// Build the range gadget for one target column: `VALUE_BITS` boolean gates plus one
/// recompose gate `col − Σⱼ 2ʲ·bitⱼ == 0`. Proves `col ∈ [0, 2^VALUE_BITS)`.
fn range_gadget(cs: &mut Vec<VmConstraint2>, col: usize, bit_col: impl Fn(usize) -> usize) {
    for j in 0..VALUE_BITS {
        let b = LeanExpr::Var(bit_col(j));
        cs.push(gate(LeanExpr::mul(b.clone(), sub(b, LeanExpr::Const(1)))));
    }
    let mut acc = LeanExpr::Var(col);
    for j in 0..VALUE_BITS {
        acc = sub(
            acc,
            LeanExpr::mul(LeanExpr::Const(1i64 << j), LeanExpr::Var(bit_col(j))),
        );
    }
    cs.push(gate(acc));
}

/// **Lower the Cert-F check to a dregg IR-v2 AIR** over the witness `(f, π, s)`. The
/// `n + 4m + 1` Cert-F rows become arithmetic Gates + range gadgets; the cleared
/// volume `wᵀf` is exposed as the one public input. `w, c, ε` ride as constants.
pub fn cert_f_descriptor(cert: &CertFWitness) -> EffectVmDescriptor2 {
    let m = cert.m();

    // No-wrap soundness for conservation: the max node degree times 2^VALUE_BITS must
    // stay below p, so a node's signed flow sum is canonical and the field gate == 0
    // is the integer conservation.
    let mut deg = vec![0u64; cert.n_nodes];
    for &(t, h) in &cert.edges {
        deg[t as usize] += 1;
        deg[h as usize] += 1;
    }
    let max_deg = deg.iter().copied().max().unwrap_or(0);
    assert!(
        max_deg * (1u64 << VALUE_BITS) < BABYBEAR_P as u64,
        "conservation no-wrap broken: node degree {max_deg} · 2^{VALUE_BITS} ≥ p — \
         lower VALUE_BITS or split high-degree nodes"
    );

    let mut cs: Vec<VmConstraint2> = Vec::new();

    // 1. conservation: one Gate per node, Σ_{head=i} f_e − Σ_{tail=i} f_e == 0.
    for i in 0..cert.n_nodes {
        let mut body = LeanExpr::Const(0);
        for (e, &(t, h)) in cert.edges.iter().enumerate() {
            if h as usize == i {
                body = LeanExpr::add(body, LeanExpr::Var(cert.f_col(e)));
            }
            if t as usize == i {
                body = sub(body, LeanExpr::Var(cert.f_col(e)));
            }
        }
        cs.push(gate(body));
    }

    // 2. box lower f_e ≥ 0: range gadget on f_e (target index e).
    for e in 0..m {
        range_gadget(&mut cs, cert.f_col(e), |j| cert.range_bit_col(e, j));
    }

    // 3. box upper c_e − f_e ≥ 0: u_e == c_e − f_e (Gate) + range gadget on u_e.
    for e in 0..m {
        // u_e − c_e + f_e == 0.
        cs.push(gate(LeanExpr::add(
            sub(LeanExpr::Var(cert.u_col(e)), LeanExpr::Const(cert.c[e])),
            LeanExpr::Var(cert.f_col(e)),
        )));
        range_gadget(&mut cs, cert.u_col(e), |j| cert.range_bit_col(m + e, j));
    }

    // 4. slack sign s_e ≥ 0: range gadget on s_e.
    for e in 0..m {
        range_gadget(&mut cs, cert.s_col(e), |j| cert.range_bit_col(2 * m + e, j));
    }

    // 5. dual feas π_head − π_tail + s_e − w_e ≥ 0: d_e == that (Gate) + range gadget.
    for (e, &(t, h)) in cert.edges.iter().enumerate() {
        // d_e − (π_h − π_t + s_e − w_e) == 0.
        let dual_expr = sub(
            LeanExpr::add(
                sub(
                    LeanExpr::Var(cert.pi_col(h as usize)),
                    LeanExpr::Var(cert.pi_col(t as usize)),
                ),
                LeanExpr::Var(cert.s_col(e)),
            ),
            LeanExpr::Const(cert.w[e]),
        );
        cs.push(gate(sub(LeanExpr::Var(cert.d_col(e)), dual_expr)));
        range_gadget(&mut cs, cert.d_col(e), |j| cert.range_bit_col(3 * m + e, j));
    }

    // 6. gap cᵀs − wᵀf ≤ ε: g == ε − (cᵀs − wᵀf) (Gate) + range gadget on g.
    // g − ε + Σ c_e s_e − Σ w_e f_e == 0.
    let mut gap_body = sub(LeanExpr::Var(cert.g_col()), LeanExpr::Const(cert.epsilon));
    for e in 0..m {
        gap_body = LeanExpr::add(
            gap_body,
            LeanExpr::mul(LeanExpr::Const(cert.c[e]), LeanExpr::Var(cert.s_col(e))),
        );
        gap_body = sub(
            gap_body,
            LeanExpr::mul(LeanExpr::Const(cert.w[e]), LeanExpr::Var(cert.f_col(e))),
        );
    }
    cs.push(gate(gap_body));
    range_gadget(&mut cs, cert.g_col(), |j| cert.range_bit_col(4 * m, j));

    // 7. objective obj == wᵀf (Gate) + expose it as the public clearing volume.
    let mut obj_body = LeanExpr::Var(cert.obj_col());
    for e in 0..m {
        obj_body = sub(
            obj_body,
            LeanExpr::mul(LeanExpr::Const(cert.w[e]), LeanExpr::Var(cert.f_col(e))),
        );
    }
    cs.push(gate(obj_body));
    cs.push(VmConstraint2::Base(VmConstraint::PiBinding {
        row: VmRow::First,
        col: cert.obj_col(),
        pi_index: 0,
    }));

    EffectVmDescriptor2 {
        name: "cert-f".into(),
        trace_width: cert.width(),
        public_input_count: 1,
        tables: vec![],
        constraints: cs,
        hash_sites: vec![],
        ranges: vec![],
    }
}

/// **Prove a Cert-F certificate in a real dregg STARK.** Lowers the certificate to
/// the IR-v2 AIR and proves it in the production prover ([`prove_vm_descriptor2`],
/// BabyBear + FRI, `ir2_config`). The witness `(f, π, s)` is hidden in the trace; only
/// `wᵀf` is public. A witness violating any Cert-F row (non-conserving, out-of-box,
/// negative slack, dual-infeasible, gap > ε) has no satisfying trace — the prover's
/// self-verify refuses it (returns `Err` or panics; use [`prove_cert_f_refused`] for
/// the negative polarity).
pub fn prove_cert_f(
    cert: &CertFWitness,
) -> Result<
    (
        EffectVmDescriptor2,
        Ir2BatchProof<DreggStarkConfig>,
        Vec<BabyBear>,
    ),
    String,
> {
    let desc = cert_f_descriptor(cert);
    let pis = cert.public_inputs();
    let base_trace = cert.base_trace();
    let proof = prove_vm_descriptor2(
        &desc,
        &base_trace,
        &pis,
        &MemBoundaryWitness::default(),
        &[],
    )?;
    Ok((desc, proof, pis))
}

/// Verify a Cert-F STARK proof against the descriptor + public inputs.
pub fn verify_cert_f(
    desc: &EffectVmDescriptor2,
    proof: &Ir2BatchProof<DreggStarkConfig>,
    pis: &[BabyBear],
) -> Result<(), String> {
    verify_vm_descriptor2(desc, proof, pis)
}

/// The negative-polarity gate: return `true` iff a bad certificate CANNOT produce a
/// verifying Cert-F STARK proof — the soundness tooth, held in BOTH debug and release.
///
/// A forged/non-conserving/gap-violating witness has no satisfying trace, so its
/// quotient is not divisible by the vanishing polynomial: the AIR constraint bites at
/// VERIFY time (`OodEvaluationMismatch`). We therefore treat the certificate as refused
/// iff EITHER the prover errs OR — when the prover mints a proof — that proof FAILS to
/// verify. This is release-correct: in release the producer-side self-verify is skipped
/// (`prove_vm_descriptor2` gates it on `debug_assertions`), so `prove_cert_f` returns
/// `Ok` for a bad cert, but `verify_cert_f` still rejects it (the consumer's verify is
/// the real soundness boundary). In debug the pre-flight self-verify makes `prove_cert_f`
/// itself err — both polarities land on "refused". `catch_unwind` covers a pre-flight
/// replay that panics rather than returns `Err`.
pub fn prove_cert_f_refused(cert: &CertFWitness) -> bool {
    let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| prove_cert_f(cert)));
    match r {
        Err(_) => true,     // panicked (pre-flight refusal)
        Ok(Err(_)) => true, // prove returned Err (debug self-verify / preflight rejected)
        Ok(Ok((desc, proof, pis))) => {
            // A proof was minted (release path). It is REFUSED iff it does NOT verify —
            // the AIR constraint (conservation / range) bites at verify time.
            verify_cert_f(&desc, &proof, &pis).is_err()
        }
    }
}

// ============================================================================
// Worked integer instances (positive polarity, non-vacuous) + the solver bridge.
// ============================================================================

/// **The 3-cycle worked certificate** — the exact lift of `Market.CertF.lean`'s
/// `ringLP`/`ringCert_valid` into the edge/vector `CertFWitness` shape. Directed
/// triangle `0→1→2→0`, unit weights + caps, the tight optimum `f = (1,1,1)`, dual
/// `π = 0`, `s = (1,1,1)`, `gap = 0`, `ε = 0`. A concrete non-vacuous certificate of a
/// real optimum (`wᵀf = 3`).
pub fn ring3_cert() -> CertFWitness {
    CertFWitness {
        n_nodes: 3,
        edges: vec![(0, 1), (1, 2), (2, 0)],
        w: vec![1, 1, 1],
        c: vec![1, 1, 1],
        f: vec![1, 1, 1],
        pi: vec![0, 0, 0],
        s: vec![1, 1, 1],
        epsilon: 0,
    }
}

/// A larger worked certificate: a single directed `n`-cycle, integer caps `cap`,
/// unit weights, pushing `cap` around the whole cycle. Optimum `f_e = cap`, dual
/// `π = 0`, `s = w = 1`, `gap = 0` — a tight certificate at any `n`, `cap`.
pub fn cycle_cert(n: usize, cap: i64) -> CertFWitness {
    let edges: Vec<(u32, u32)> = (0..n).map(|i| (i as u32, ((i + 1) % n) as u32)).collect();
    CertFWitness {
        n_nodes: n,
        edges,
        w: vec![1; n],
        c: vec![cap; n],
        f: vec![cap; n],
        pi: vec![0; n],
        s: vec![1; n],
        epsilon: 0,
    }
}

/// **The solver bridge** — build an integer Cert-F certificate from a fhegg-solver
/// `CertF` JSON emission (the f64 wire format of `fhegg-solver/src/cert.rs`) by
/// FIXED-POINT scaling. The solver's `(f, π)` (found by the untrusted PDHG search) are
/// scaled by `scale` and rounded; `s` is re-derived as `(scale·w − Aᵀ(scale·π))₊` so
/// `s ≥ 0` and dual feasibility hold in the integer grid by construction, and `ε` is
/// set to the resulting integer gap so the certificate is Cert-F-valid at that
/// fixed-point resolution. The check `check()` must pass before this is proven — the
/// bridge asserts nothing it does not verify.
pub fn from_solution_json(json: &str, scale: i64) -> Result<CertFWitness, String> {
    let v: serde_json::Value =
        serde_json::from_str(json).map_err(|e| format!("cert JSON parse: {e}"))?;
    let n_nodes = v["n_nodes"].as_u64().ok_or("missing n_nodes")? as usize;
    let edges: Vec<(u32, u32)> = v["edges"]
        .as_array()
        .ok_or("missing edges")?
        .iter()
        .map(|p| {
            let a = p[0].as_u64().unwrap_or(0) as u32;
            let b = p[1].as_u64().unwrap_or(0) as u32;
            (a, b)
        })
        .collect();
    let read = |k: &str| -> Result<Vec<f64>, String> {
        v[k].as_array()
            .ok_or_else(|| format!("missing {k}"))?
            .iter()
            .map(|x| x.as_f64().ok_or_else(|| format!("{k} not f64")))
            .collect()
    };
    let wf = read("w")?;
    let cf = read("c")?;
    let ff = read("f")?;
    let pif = read("pi")?;
    let m = edges.len();

    let round = |x: f64| -> i64 { (x * scale as f64).round() as i64 };
    let w: Vec<i64> = wf.iter().map(|&x| round(x)).collect();
    let c: Vec<i64> = cf.iter().map(|&x| round(x)).collect();
    let f: Vec<i64> = ff.iter().map(|&x| round(x)).collect();
    let pi: Vec<i64> = pif.iter().map(|&x| round(x)).collect();

    // s = (w − Aᵀπ)₊ in the integer grid (so s ≥ 0 and Aᵀπ + s ≥ w by construction).
    let at_pi = |e: usize| -> i64 {
        let (t, h) = edges[e];
        pi[h as usize] - pi[t as usize]
    };
    let s: Vec<i64> = (0..m).map(|e| (w[e] - at_pi(e)).max(0)).collect();

    let mut cert = CertFWitness {
        n_nodes,
        edges,
        w,
        c,
        f,
        pi,
        s,
        epsilon: 0,
    };
    // ε absorbs the fixed-point quantization: set it to the (nonneg, by weak duality)
    // integer gap so `gap ≤ ε` holds. gap_nonneg (CertF.lean) guarantees gap ≥ 0.
    cert.epsilon = cert.gap().max(0);
    Ok(cert)
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_circuit::descriptor_ir2::{ir2_eval_accepts_i64, parse_vm_descriptor2};

    /// **THE LEAN-AUTHORED DESCRIPTOR (byte-twin discipline).** `metatheory/Market/CertFDescriptor.lean`
    /// AUTHORS the Cert-F `EffectVmDescriptor2` (`certFDescriptorOf`) and PROVES the emit-soundness
    /// bridge `Satisfied2 ↔ certificate-valid` (`certFDescriptor_emit_sound`) — the theorem this
    /// hand-built Rust could only *test*. The Lean descriptor's canonical wire string is emitted by
    /// `emitVmJson2` and committed at `circuit/descriptors/dregg-cert-f-ir2.json`. This constant is
    /// that byte string; Lean is the source of truth, the Rust builder is the checked twin.
    const CERT_F_LEAN_JSON: &str = include_str!("../../circuit/descriptors/dregg-cert-f-ir2.json");

    /// **THE BYTE-TWIN GATE.** The hand-built Rust descriptor for the worked 3-cycle is BYTE-IDENTICAL
    /// to the Lean-authored one (decoded from the committed `emitVmJson2` wire string). This retires the
    /// hand-write as the source of truth: `cert_f_descriptor` is now validated against the Lean descriptor
    /// that carries the proven `Satisfied2 ↔ valid` emit-soundness, exactly as the effect_vm family pins
    /// its Rust twin to the Lean `#guard` golden. (The @[export] archive build that would let Rust
    /// consume the Lean object directly is the deploy step; this twin is the same staged discipline the
    /// rotation lanes use — the JSON is regenerated from Lean via `emitVmJson2`.)
    #[test]
    fn cert_f_descriptor_matches_lean() {
        let rust = cert_f_descriptor(&ring3_cert());
        let lean = parse_vm_descriptor2(CERT_F_LEAN_JSON)
            .expect("the Lean-authored Cert-F descriptor JSON must parse");
        assert_eq!(
            rust, lean,
            "SOURCE-OF-TRUTH DRIFT: the hand-built Rust Cert-F descriptor is NOT byte-identical to the \
             Lean-authored `certFDescriptorOf ring3Prog` (regenerate the golden with \
             `emitVmJson2 certFDescriptor` if the Lean descriptor changed)"
        );
    }

    /// The i64 base-trace as the native evaluator wants it (single row is enough — every
    /// row is identical, but we hand it the real height).
    fn i64_trace(cert: &CertFWitness) -> Vec<Vec<i64>> {
        let felt = cert.base_trace();
        felt.iter()
            .map(|r| r.iter().map(|c| c.as_u32() as i64).collect())
            .collect()
    }

    #[test]
    fn ring3_check_is_valid_tight() {
        let cert = ring3_cert();
        let chk = cert.check();
        assert!(
            chk.valid,
            "the worked ring certificate must be Cert-F-valid: {chk:?}"
        );
        assert_eq!(chk.gap, 0, "tight optimum: gap exactly 0");
        assert_eq!(cert.objective(), 3, "cleared volume wᵀf = 3");
    }

    /// The AIR (native row evaluator, the SAME `Ir2Air::Main` the prover commits) ACCEPTS
    /// the valid certificate. Fast pre-check before the full STARK.
    #[test]
    fn air_accepts_valid_ring3() {
        let cert = ring3_cert();
        let desc = cert_f_descriptor(&cert);
        let pis: Vec<i64> = cert
            .public_inputs()
            .iter()
            .map(|b| b.as_u32() as i64)
            .collect();
        assert!(
            ir2_eval_accepts_i64(&desc, &i64_trace(&cert), &pis),
            "the Cert-F AIR must accept a valid certificate"
        );
    }

    /// AIR ACCEPTS a larger cycle certificate (n=6, cap=1000) — the emission scales.
    #[test]
    fn air_accepts_cycle6() {
        let cert = cycle_cert(6, 1000);
        assert!(cert.check().valid);
        let desc = cert_f_descriptor(&cert);
        let pis: Vec<i64> = cert
            .public_inputs()
            .iter()
            .map(|b| b.as_u32() as i64)
            .collect();
        assert!(ir2_eval_accepts_i64(&desc, &i64_trace(&cert), &pis));
        assert_eq!(cert.objective(), 6000);
    }

    /// NEGATIVE (conservation): a non-conserving f (leak on one edge) is REJECTED by the
    /// AIR — both the check and the native evaluator refuse it.
    #[test]
    fn air_rejects_nonconserving() {
        let mut cert = ring3_cert();
        cert.f[0] += 1; // break Af = 0 (and the box)
        assert!(!cert.check().conserves);
        let desc = cert_f_descriptor(&cert);
        let pis: Vec<i64> = cert
            .public_inputs()
            .iter()
            .map(|b| b.as_u32() as i64)
            .collect();
        assert!(
            !ir2_eval_accepts_i64(&desc, &i64_trace(&cert), &pis),
            "a non-conserving certificate must be rejected by the AIR"
        );
    }

    /// NEGATIVE (gap): a sub-optimal flow (zero flow) against the honest dual has gap 3 > ε=0
    /// — the gap-slack range gadget rejects it (g = −3 has no VALUE_BITS-bit preimage).
    #[test]
    fn air_rejects_gap_violation() {
        let mut cert = ring3_cert();
        cert.f = vec![0, 0, 0]; // feasible but sub-optimal; gap = cᵀs − wᵀf = 3 > 0
        assert!(cert.check().conserves, "zero flow still conserves");
        assert!(!cert.check().gap_ok, "gap 3 > ε 0");
        let desc = cert_f_descriptor(&cert);
        let pis: Vec<i64> = cert
            .public_inputs()
            .iter()
            .map(|b| b.as_u32() as i64)
            .collect();
        assert!(
            !ir2_eval_accepts_i64(&desc, &i64_trace(&cert), &pis),
            "a gap-violating certificate must be rejected by the AIR"
        );
    }

    /// NEGATIVE (box / range): an over-capacity flow (f_e > c_e) makes the box-upper slack
    /// negative — the range gadget on u_e rejects it.
    #[test]
    fn air_rejects_over_capacity() {
        let mut cert = cycle_cert(4, 5);
        cert.f[0] = 6; // > cap 5 ⇒ u_0 = c_0 − f_0 = −1 < 0
        cert.f[1] = 6;
        cert.f[2] = 6;
        cert.f[3] = 6; // keep conservation (all equal) so ONLY the box bites
        assert!(cert.check().conserves);
        assert!(!cert.check().box_ok);
        let desc = cert_f_descriptor(&cert);
        let pis: Vec<i64> = cert
            .public_inputs()
            .iter()
            .map(|b| b.as_u32() as i64)
            .collect();
        assert!(!ir2_eval_accepts_i64(&desc, &i64_trace(&cert), &pis));
    }

    // ========================================================================
    // The REAL STARK — a production dregg BabyBear+FRI proof over the Cert-F AIR.
    // (Native-eval above is the fast pre-check; THESE mint + verify actual proofs.)
    // ========================================================================

    /// POSITIVE: a valid certificate is proven in a REAL dregg STARK and the proof
    /// VERIFIES. The witness `(f, π, s)` lives only in the trace (hidden under the
    /// FRI/PCS commitment); the sole public value is the cleared volume `wᵀf`.
    #[test]
    fn stark_proves_and_verifies_ring3() {
        let cert = ring3_cert();
        assert!(cert.check().valid);
        let (desc, proof, pis) =
            prove_cert_f(&cert).expect("a valid Cert-F certificate must prove in the STARK");
        // The public input the world sees is exactly the cleared volume wᵀf = 3.
        assert_eq!(pis, cert.public_inputs());
        assert_eq!(pis[0].as_u32(), 3);
        verify_cert_f(&desc, &proof, &pis).expect("the minted Cert-F STARK proof must verify");
    }

    /// POSITIVE (scales): a larger cycle certificate (n=6, cap=1000) proves + verifies —
    /// the real STARK ingests the certificate, not the T search iterations.
    #[test]
    fn stark_proves_and_verifies_cycle6() {
        let cert = cycle_cert(6, 1000);
        assert!(cert.check().valid);
        let (desc, proof, pis) = prove_cert_f(&cert).expect("valid cycle-6 must prove");
        assert_eq!(pis[0].as_u32(), 6000); // wᵀf = 6 * 1000
        verify_cert_f(&desc, &proof, &pis).expect("cycle-6 proof must verify");
    }

    /// NEGATIVE (STARK teeth): a non-conserving certificate has NO satisfying trace —
    /// the real prover REFUSES it (returns Err or pre-flight panics), never mints a proof.
    #[test]
    fn stark_refuses_nonconserving() {
        let mut cert = ring3_cert();
        cert.f[0] += 1; // break Af = 0
        assert!(!cert.check().valid);
        assert!(
            prove_cert_f_refused(&cert),
            "the STARK must REFUSE a non-conserving certificate"
        );
    }

    /// NEGATIVE (STARK teeth): a sub-optimal flow (gap 3 > ε 0) has a gap-slack that is
    /// negative and has no VALUE_BITS-bit range preimage — the STARK refuses it.
    #[test]
    fn stark_refuses_gap_violation() {
        let mut cert = ring3_cert();
        cert.f = vec![0, 0, 0]; // feasible but gap = 3 > ε = 0
        assert!(cert.check().conserves && !cert.check().gap_ok);
        assert!(
            prove_cert_f_refused(&cert),
            "the STARK must REFUSE a gap-violating certificate"
        );
    }

    /// THE DECISIVE SOUNDNESS DIAGNOSTIC (release-hard): even when the prover MINTS a
    /// proof for a bad certificate (which it does in release, where the producer-side
    /// self-verify is skipped), that minted proof MUST FAIL to verify. This is the
    /// verify-not-find soundness boundary: a forged/non-conserving/gap-violating cert
    /// cannot produce a VERIFYING STARK proof. Runs the mint→verify path directly so the
    /// property is asserted regardless of build profile.
    #[test]
    fn stark_bad_cert_proof_does_not_verify() {
        // (a) non-conserving.
        let mut nonconserving = ring3_cert();
        nonconserving.f[0] += 1;
        assert!(!nonconserving.check().valid);
        if let Ok((desc, proof, pis)) = prove_cert_f(&nonconserving) {
            assert!(
                verify_cert_f(&desc, &proof, &pis).is_err(),
                "SOUNDNESS HOLE: a minted proof of a NON-CONSERVING cert verified"
            );
        }
        // (b) gap-violating.
        let mut gap_bad = ring3_cert();
        gap_bad.f = vec![0, 0, 0];
        assert!(gap_bad.check().conserves && !gap_bad.check().gap_ok);
        if let Ok((desc, proof, pis)) = prove_cert_f(&gap_bad) {
            assert!(
                verify_cert_f(&desc, &proof, &pis).is_err(),
                "SOUNDNESS HOLE: a minted proof of a GAP-VIOLATING cert verified"
            );
        }
    }

    /// The solver bridge, end-to-end into the REAL STARK: take a fhegg-solver Cert-F
    /// JSON emission, fixed-point scale it to an integer certificate, and prove THAT in
    /// the production prover. Closes fhegg-solver → circuit-prove at the STARK level.
    #[test]
    fn stark_proves_solver_json_bridge() {
        // A minimal hand-written solver JSON (the wire shape of fhegg-solver/src/cert.rs):
        // the 3-cycle at unit weights/caps, f = π = 0-derived s. Scale = 1 keeps it integral.
        let json = r#"{
            "n_nodes": 3,
            "m_edges": 3,
            "edges": [[0,1],[1,2],[2,0]],
            "w": [1.0, 1.0, 1.0],
            "c": [1.0, 1.0, 1.0],
            "f": [1.0, 1.0, 1.0],
            "pi": [0.0, 0.0, 0.0],
            "s": [1.0, 1.0, 1.0],
            "epsilon": 0.0
        }"#;
        let cert = from_solution_json(json, 1).expect("solver JSON must bridge to an integer cert");
        assert!(
            cert.check().valid,
            "bridged certificate must be Cert-F-valid"
        );
        let (desc, proof, pis) =
            prove_cert_f(&cert).expect("the bridged solver certificate must prove in the STARK");
        verify_cert_f(&desc, &proof, &pis).expect("bridged-cert proof must verify");
    }

    /// SOUNDNESS of verification (not just of proving): a genuine proof of the ring-3
    /// certificate must FAIL to verify against a WRONG public input (a claimed cleared
    /// volume ≠ the real `wᵀf`). This rules out a vacuous verifier — the public value is
    /// cryptographically bound to the witness.
    #[test]
    fn stark_verify_rejects_wrong_public_input() {
        let cert = ring3_cert();
        let (desc, proof, pis) = prove_cert_f(&cert).expect("valid ring3 must prove");
        assert!(
            verify_cert_f(&desc, &proof, &pis).is_ok(),
            "honest PI verifies"
        );
        // Claim a different cleared volume (4 instead of the real 3).
        let wrong = vec![fe(cert.objective() + 1)];
        assert_ne!(wrong, pis);
        assert!(
            verify_cert_f(&desc, &proof, &wrong).is_err(),
            "a proof must NOT verify against a falsified cleared-volume public input"
        );
    }
}
