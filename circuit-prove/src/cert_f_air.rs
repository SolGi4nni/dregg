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
//! `(A, w, c, ε)` rides as descriptor constants. Because those constants are
//! algebra, each public program must be emitted from Lean and byte-pinned; Rust
//! refuses an unregistered program rather than specializing constraints at runtime.
//! (The field-level emit-soundness proof `certFDescriptor_emit_sound` is GENERIC over the
//! program. Integer registration additionally chooses proved flow/slack range policies; the
//! deployed ring3 and market4 policies are discharged by `ring3Prog_integerAdmission` and
//! `market4Prog_integerAdmission`.)
//! [`prove_cert_f`] proves the AIR in the production non-hiding IR-v2 STARK
//! ([`prove_vm_descriptor2`], BabyBear + FRI).  [`prove_cert_f_zk`] proves the
//! identical descriptor through Plonky3's `HidingFriPcs`; that is the Tier-1 path
//! whose witness `(f, π, s)` stays private from proof consumers while the public
//! program `(A, w, c, ε)` and cleared volume `wᵀf` remain visible.
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
//! Tier-0 no-viewer: the SOLVER sees plaintext orders.  Callers making the Tier-1
//! claim must use [`prove_cert_f_zk`], not the compatibility [`prove_cert_f`] path.
//! The construction uses the repository's OS-seeded hiding PCS; a formal simulator
//! theorem for the complete batch-STARK transcript remains a separate proof floor.
//! The range gadget closes integer conservation for values below `2^VALUE_BITS`;
//! larger amounts ride a wider decomposition or the off-AIR range proof (the same
//! BabyBear field cap the shielded-ring AIR documents).

use dregg_circuit::descriptor_ir2::DreggStarkConfig;
use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, Ir2BatchProof, MemBoundaryWitness, UMemBoundaryWitness,
    parse_vm_descriptor2, prove_vm_descriptor2, prove_vm_descriptor2_for_config,
    verify_vm_descriptor2, verify_vm_descriptor2_with_config,
};
use dregg_circuit::field::{BABYBEAR_P, BabyBear};
use dregg_circuit::stark_zk::{DreggZkStarkConfig, create_zk_config};

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
    /// Historical scalar + `f,u,s,d,g` range-bit prefix.
    fn core_width(&self) -> usize {
        self.bit_base() + (4 * self.m() + 1) * VALUE_BITS
    }
    /// Dedicated potential range bits appended by the integer-admission descriptor revision.
    fn potential_range_bit_col(&self, i: usize, j: usize) -> usize {
        self.core_width() + i * VALUE_BITS + j
    }
    /// Full trace width: historical prefix plus one 28-bit decomposition per potential.
    fn width(&self) -> usize {
        self.core_width() + self.n_nodes * VALUE_BITS
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
        if let Some(program) = registered_program(self) {
            assert!(
                program.flow_bits <= VALUE_BITS && program.slack_bits <= VALUE_BITS,
                "registered Cert-F tight-range policy exceeds its 28-bit source decomposition"
            );
        }
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

        // Core range bits: low `VALUE_BITS` bits of each target's value (as an unsigned
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
        // Potentials were unrestricted in descriptor v1.  The integer-admission revision appends
        // a real 28-bit range gadget for every π cell.  A negative/wrapped/out-of-range potential
        // cannot recompose from these low bits and is rejected by the AIR.
        for i in 0..self.n_nodes {
            let v = row[self.pi_col(i)].as_u32();
            for j in 0..VALUE_BITS {
                row[self.potential_range_bit_col(i, j)] = BabyBear::new((v >> j) & 1);
            }
        }
        vec![row; TRACE_HEIGHT]
    }
}

/// Lift a signed integer to its canonical BabyBear representative.
fn fe(x: i64) -> BabyBear {
    let p = BABYBEAR_P as i64;
    let r = ((x % p) + p) % p; // canonical in [0, p)
    BabyBear::new(r as u32)
}

/// Exact artifact emitted from `Market.CertFDescriptor.certFDescriptor` and
/// byte-pinned in Lean (`CERT_F_RING3_GOLDEN`). The proved unit ring-3.
pub const CERT_F_RING3_DESCRIPTOR_JSON: &str =
    include_str!("../../circuit/descriptors/dregg-cert-f-ir2.json");

/// Exact artifact emitted from `Market.CertFDescriptor.certFMarket4Descriptor` and byte-pinned in
/// Lean (`CERT_F_MARKET4_GOLDEN`) — the first REAL market shape past the ring-3 toy: the
/// 3-asset / 4-order DrEX trade-circulation batch (`fhegg_clear`'s nodes=assets, edge-per-order
/// mapping) at fixed-point scale 100 with a PRESCRIPTIVE accuracy budget `ε = 2000`.
pub const CERT_F_MARKET4_DESCRIPTOR_JSON: &str =
    include_str!("../../circuit/descriptors/dregg-cert-f-market4-ir2.json");

/// One registered Cert-F public program: the `(A, w, c, ε)` constants a Lean-emitted,
/// byte-pinned descriptor bakes in. `epsilon` is PRESCRIPTIVE — the accuracy budget the
/// registered program grants — not the solve's achieved gap.
struct RegisteredCertFProgram {
    n_nodes: usize,
    edges: &'static [(u32, u32)],
    w: &'static [i64],
    c: &'static [i64],
    epsilon: i64,
    /// Enforced descriptor policy.  The tight recompose gates reuse the low portion of the
    /// historical 28-bit flow/slack decomposition.
    flow_bits: usize,
    slack_bits: usize,
    /// The fixed-point scale whose image of a solver f64 program is exactly this
    /// registration's integer `(w, c)`.  This is BRIDGE metadata, not an AIR constant: the
    /// descriptor bakes in `(w, c, epsilon)` as integers, and this records which f64 program
    /// those integers are the `×scale` image of, so a live batch can RESOLVE ITSELF to this
    /// registration instead of an operator guessing `CERT_F_SCALE`.
    scale: i64,
    descriptor_json: &'static str,
}

/// The Cert-F program registry. `certFDescriptor_emit_sound` supplies the generic field theorem,
/// but integer registration also chooses flow/slack bounds and proves that those enforced bounds
/// keep the program's complete weighted residuals from wrapping. Ring3 and market4 have the
/// unconditional admissions `ring3Prog_integerAdmission` / `market4Prog_integerAdmission`.
const CERT_F_REGISTRY: &[RegisteredCertFProgram] = &[
    RegisteredCertFProgram {
        n_nodes: 3,
        edges: &[(0, 1), (1, 2), (2, 0)],
        w: &[1, 1, 1],
        c: &[1, 1, 1],
        epsilon: 0,
        flow_bits: 28,
        slack_bits: 28,
        scale: 1,
        descriptor_json: CERT_F_RING3_DESCRIPTOR_JSON,
    },
    RegisteredCertFProgram {
        n_nodes: 3,
        edges: &[(0, 1), (1, 2), (2, 0), (1, 0)],
        w: &[100, 100, 100, 300],
        c: &[500, 500, 500, 300],
        epsilon: 2000,
        flow_bits: 21,
        slack_bits: 19,
        scale: 100,
        descriptor_json: CERT_F_MARKET4_DESCRIPTOR_JSON,
    },
];

fn registered_program(cert: &CertFWitness) -> Option<&'static RegisteredCertFProgram> {
    CERT_F_REGISTRY.iter().find(|p| {
        p.n_nodes == cert.n_nodes
            && p.edges == cert.edges.as_slice()
            && p.w == cert.w.as_slice()
            && p.c == cert.c.as_slice()
            && p.epsilon == cert.epsilon
    })
}

/// Resolve a Cert-F public program to a Lean-emitted, byte-pinned artifact. New
/// `(A,w,c,epsilon)` programs must first be emitted from `CertFDescriptor.lean`
/// (`certFDescriptorOf p`), given sufficient proved range policies, byte-pinned, committed, and
/// registered here. The field theorem is generic; integer admission is deliberately fail-closed.
pub fn try_cert_f_descriptor(cert: &CertFWitness) -> Result<EffectVmDescriptor2, String> {
    let Some(prog) = registered_program(cert) else {
        return Err(
            "Cert-F public program is not registered as a Lean-emitted descriptor; \
             choose and prove sufficient integer range policies, emit certFDescriptorOf(program), \
             byte-pin, and register it before proving"
                .into(),
        );
    };
    parse_vm_descriptor2(prog.descriptor_json)
        .map_err(|e| format!("Lean-emitted Cert-F descriptor failed to parse: {e}"))
}

/// Infallible compatibility wrapper for the registered ring-3 program.
pub fn cert_f_descriptor(cert: &CertFWitness) -> EffectVmDescriptor2 {
    try_cert_f_descriptor(cert).expect("Cert-F descriptor program must be Lean-registered")
}

// ============================================================================
// DYNAMIC REGISTRATION — a live batch resolves ITSELF to a registered program.
// ============================================================================

/// How a solver f64 Cert-F program bridges onto one registered Lean-emitted program: the
/// fixed-point `scale` whose image is that registration's integer `(w, c)`, and the
/// prescriptive `epsilon` budget the registration grants in the scaled integer grid.
///
/// `epsilon` here is not a number this crate chose. It is `p.eps` of the `CertFProg` that
/// `Market.CertFDescriptor` authored and byte-pinned; the Rust side only reports it.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct RegisteredScaling {
    pub scale: i64,
    pub epsilon: i64,
    /// Solver-unit budget: `epsilon / scale^2`. The bridge scales both factors of every
    /// product in `cᵀs − wᵀf`, so an integer budget is this much in the solver's own units.
    pub solver_epsilon: f64,
}

/// The public program half of a solver f64 certificate — the part registration is decided on.
struct SolverProgram {
    n_nodes: usize,
    edges: Vec<(u32, u32)>,
    w: Vec<f64>,
    c: Vec<f64>,
}

fn parse_solver_program(json: &str) -> Result<SolverProgram, String> {
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
    Ok(SolverProgram {
        n_nodes,
        edges,
        w: read("w")?,
        c: read("c")?,
    })
}

/// `x·scale`, but only when that product is an exact integer to within float noise.
///
/// This is the tooth that keeps resolution HONEST. Rounding `1.005 × 100 = 100.5` down to
/// `100` would let a batch whose weights are NOT the registered program's be certified
/// against the registered program's constants — the certificate would then be about a
/// program nobody ran. A non-integral image is refused, never rounded into a registration.
fn exact_scaled(x: f64, scale: i64) -> Option<i64> {
    if !x.is_finite() {
        return None;
    }
    let scaled = x * scale as f64;
    if scaled.abs() > (i64::MAX / 2) as f64 {
        return None;
    }
    let rounded = scaled.round();
    let tolerance = 1e-9 * scaled.abs().max(1.0);
    ((scaled - rounded).abs() <= tolerance).then_some(rounded as i64)
}

fn matches_registration(program: &SolverProgram, reg: &RegisteredCertFProgram) -> bool {
    if program.n_nodes != reg.n_nodes
        || program.edges.as_slice() != reg.edges
        || program.w.len() != reg.w.len()
        || program.c.len() != reg.c.len()
    {
        return false;
    }
    program
        .w
        .iter()
        .zip(reg.w)
        .all(|(x, &want)| exact_scaled(*x, reg.scale) == Some(want))
        && program
            .c
            .iter()
            .zip(reg.c)
            .all(|(x, &want)| exact_scaled(*x, reg.scale) == Some(want))
}

/// **Resolve a live batch to its registration.** Given a solver f64 Cert-F emission (the
/// wire `fhegg_clear` writes under `solverCert`), find the registered Lean-emitted program
/// whose integer `(w, c)` is exactly the `×scale` image of this batch's public program, and
/// return that registration's fixed-point scale and prescriptive `epsilon` budget.
///
/// This is what makes the STARK wrap REACHABLE without an operator supplying `CERT_F_SCALE`
/// and `CERT_F_EPSILON` by hand: an unset scale defaulted to `1`, which is the image of
/// almost no registered program, so every live batch was refused before it ever reached the
/// prover. Resolution is still FAIL-CLOSED — a batch that is not the preimage of a
/// registration is refused with the exact artifact it is missing, and nothing is
/// specialised at runtime.
pub fn resolve_registered_scaling(json: &str) -> Result<RegisteredScaling, String> {
    let program = parse_solver_program(json)?;
    let Some(reg) = CERT_F_REGISTRY
        .iter()
        .find(|reg| matches_registration(&program, reg))
    else {
        return Err(format!(
            "this batch's public program (nodes={}, edges={}, w={:?}, c={:?}) is the \
             fixed-point preimage of NO registered Cert-F program. The registry holds {} \
             Lean-emitted programs. To admit this shape: author its `CertFProg` in \
             `metatheory/Market/CertFDescriptor.lean`, discharge `CertFProg.IntegerAdmission` \
             for it, `#guard` the `emitVmJson2` byte pin, commit the artifact under \
             `circuit/descriptors/`, and add its registry entry. Nothing here specialises \
             constraints at runtime.",
            program.n_nodes,
            program.edges.len(),
            program.w,
            program.c,
            CERT_F_REGISTRY.len(),
        ));
    };
    Ok(RegisteredScaling {
        scale: reg.scale,
        epsilon: reg.epsilon,
        solver_epsilon: reg.epsilon as f64 / (reg.scale as f64 * reg.scale as f64),
    })
}

/// **The solver bridge, DYNAMICALLY REGISTERED** — resolve the batch to its registration
/// (scale and prescriptive epsilon both read off the Lean-emitted program, never guessed),
/// then bridge prescriptively. Returns the integer witness together with the registration
/// it landed on.
///
/// REFUSES, without proving anything, when the batch is not the preimage of a registration
/// or when its achieved integer gap exceeds the budget that registration grants.
pub fn from_solution_json_registered(
    json: &str,
) -> Result<(CertFWitness, RegisteredScaling), String> {
    let scaling = resolve_registered_scaling(json)?;
    let cert = from_solution_json_with_epsilon(json, scaling.scale, scaling.epsilon)?;
    Ok((cert, scaling))
}

/// **Prove a Cert-F certificate in a real dregg STARK.** Lowers the certificate to
/// the IR-v2 AIR and proves it in the production prover ([`prove_vm_descriptor2`],
/// BabyBear + FRI, `ir2_config`). The witness `(f, π, s)` lives in the trace and is
/// absent from the public-input vector, but this compatibility path's PCS is binding,
/// **not hiding**; use [`prove_cert_f_zk`] when witness privacy is a protocol
/// requirement. A witness violating any Cert-F row (non-conserving, out-of-box,
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
    let desc = try_cert_f_descriptor(cert)?;
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

/// Prove the same Lean-emitted Cert-F descriptor through Plonky3's hiding PCS.
///
/// The AIR, public program registration, public inputs, and trace construction are
/// byte-for-byte the same as [`prove_cert_f`].  Only the caller-supplied STARK
/// configuration changes: `DreggZkStarkConfig` uses OS-seeded salted Merkle leaves,
/// random trace rows, and random FRI codewords.  The proof therefore exposes the
/// registered public program and `wᵀf`, but not raw openings of `(f, π, s)`.
pub fn prove_cert_f_zk(
    cert: &CertFWitness,
) -> Result<
    (
        EffectVmDescriptor2,
        Ir2BatchProof<DreggZkStarkConfig>,
        Vec<BabyBear>,
    ),
    String,
> {
    let desc = try_cert_f_descriptor(cert)?;
    let pis = cert.public_inputs();
    let base_trace = cert.base_trace();
    let config = create_zk_config();
    let proof = prove_vm_descriptor2_for_config(
        &desc,
        &base_trace,
        &pis,
        &MemBoundaryWitness::default(),
        &[],
        &UMemBoundaryWitness::default(),
        &config,
    )?;
    Ok((desc, proof, pis))
}

/// Verify a hiding Cert-F proof against its Lean-emitted descriptor and public
/// cleared value.  Verification needs no witness and no prover RNG state.
pub fn verify_cert_f_zk(
    desc: &EffectVmDescriptor2,
    proof: &Ir2BatchProof<DreggZkStarkConfig>,
    pis: &[BabyBear],
) -> Result<(), String> {
    let config = create_zk_config();
    verify_vm_descriptor2_with_config(desc, proof, pis, &config)
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

/// **The market4 worked certificate** — the exact optimum of the REGISTERED 3-asset / 4-order
/// DrEX batch program (`Market.CertFDescriptor.market4Prog`): nodes = assets, one edge per order
/// `(wantAsset → offerAsset)` (`fhegg_clear`'s mapping), at fixed-point scale 100 with the
/// prescriptive budget `ε = 2000`. Unique optimum `f = (500, 200, 200, 300)` (ring at 200 + the
/// priority-3 bilateral leg at its 300 cap), dual `π = (200, 0, 100)`, `s = (w − Aᵀπ)₊ =
/// (300, 0, 0, 100)`, tight `gap = 0`, cleared volume `wᵀf = 180000`.
pub fn market4_cert() -> CertFWitness {
    CertFWitness {
        n_nodes: 3,
        edges: vec![(0, 1), (1, 2), (2, 0), (1, 0)],
        w: vec![100, 100, 100, 300],
        c: vec![500, 500, 500, 300],
        f: vec![500, 200, 200, 300],
        pi: vec![200, 0, 100],
        s: vec![300, 0, 0, 100],
        epsilon: 2000,
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

/// **The solver bridge, PRESCRIPTIVE form** — build an integer Cert-F certificate from a
/// fhegg-solver `CertF` JSON emission (the f64 wire format of `fhegg-solver/src/cert.rs`) by
/// FIXED-POINT scaling, against a caller-supplied accuracy budget `epsilon` (the REGISTERED
/// program's ε, in the scaled integer grid). The solver's `(f, π)` are scaled by `scale` and
/// rounded; `s` is re-derived as `(scale·w − Aᵀ(scale·π))₊` so `s ≥ 0` and dual feasibility
/// hold by construction. The certificate's `ε` is the BUDGET, not the achieved gap — so a real
/// solve with a nonzero achieved gap matches a registered `(A,w,c,ε)` program exactly (the
/// historical descriptive form set `ε := achieved gap`, which could never equal a registered
/// budget unless the solve landed exactly tight — the ε-mismatch trap). REFUSES (Err) when the
/// achieved integer gap exceeds the budget: the bridge asserts nothing it does not verify.
pub fn from_solution_json_with_epsilon(
    json: &str,
    scale: i64,
    epsilon: i64,
) -> Result<CertFWitness, String> {
    let mut cert = bridge_solution_json(json, scale)?;
    let gap = cert.gap();
    if gap > epsilon {
        return Err(format!(
            "solver certificate achieved integer gap {gap} exceeds the prescriptive \
             epsilon budget {epsilon} at scale={scale}; converge tighter or raise the budget"
        ));
    }
    cert.epsilon = epsilon;
    Ok(cert)
}

/// **The solver bridge, DESCRIPTIVE form** — as [`from_solution_json_with_epsilon`], but `ε` is
/// set to the achieved (nonneg, by weak duality) integer gap, so the certificate is Cert-F-valid
/// at that fixed-point resolution by construction. NOTE: a descriptive `ε` only matches a
/// registered program whose pinned budget happens to EQUAL the achieved gap (for ring-3, only an
/// exactly-tight `gap = 0` solve); use the prescriptive form to prove against an ε-budget
/// registration.
pub fn from_solution_json(json: &str, scale: i64) -> Result<CertFWitness, String> {
    let mut cert = bridge_solution_json(json, scale)?;
    // ε absorbs the fixed-point quantization: set it to the (nonneg, by weak duality)
    // integer gap so `gap ≤ ε` holds. gap_nonneg (CertF.lean) guarantees gap ≥ 0.
    cert.epsilon = cert.gap().max(0);
    Ok(cert)
}

/// The shared f64→integer scaling core of the two bridge forms. Returns the certificate with
/// `ε = 0`; the caller decides the ε policy (prescriptive budget vs descriptive achieved gap).
fn bridge_solution_json(json: &str, scale: i64) -> Result<CertFWitness, String> {
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
    let mut pi: Vec<i64> = pif.iter().map(|&x| round(x)).collect();

    // CANONICAL POTENTIAL REPRESENTATIVE. Every Cert-F clause that mentions `π` mentions it
    // only as the difference `π_head − π_tail` (dual feasibility, and nothing else — the gap
    // and the objective do not involve π at all), so the certificate is invariant under a
    // common shift of all potentials. A first-order solver has no reason to return a
    // nonnegative dual: a real market4 solve returns `π = (1, −1, 0)`, whose ×100 image
    // carries `−100`. In BabyBear that lifts to `p − 100`, which has no 28-bit
    // decomposition, so the descriptor's potential range gadget REFUSES it — an honest,
    // Cert-F-valid certificate that the deployed AIR cannot accept.
    //
    // The bridge therefore presents the canonical translate `π − min(π) ≥ 0`. This is a
    // change of REPRESENTATIVE, not of the certificate: `Aᵀπ` is unchanged, hence `s`, the
    // dual slacks, the gap and the objective are all unchanged, and `Market.Certified` holds
    // for exactly the same set of certificates. It removes no tooth: the range gadget still
    // rejects any potential at or above `2^VALUE_BITS`, which is what
    // `air_rejects_unranged_potential_shift` pins.
    if let Some(&min_pi) = pi.iter().min() {
        if min_pi < 0 {
            for value in &mut pi {
                *value -= min_pi;
            }
        }
    }
    // Assert nothing we do not verify: if the canonical translate still does not fit the
    // deployed range gadget, refuse here rather than mint a witness the AIR will reject.
    let potential_bound: i64 = 1i64 << VALUE_BITS;
    if let Some(&max_pi) = pi.iter().max() {
        if max_pi >= potential_bound {
            return Err(format!(
                "the canonical potential translate spans {max_pi} >= 2^{VALUE_BITS}: the dual \
                 prices of this batch do not fit the deployed potential range gadget at \
                 scale={scale}. Lower the fixed-point scale or register a program with a wider \
                 potential decomposition; nothing here widens a deployed range."
            ));
        }
    }

    // s = (w − Aᵀπ)₊ in the integer grid (so s ≥ 0 and Aᵀπ + s ≥ w by construction).
    // Shift-invariant: `at_pi` is a difference, so this is the same `s` either side of the
    // canonicalisation above.
    let at_pi = |e: usize| -> i64 {
        let (t, h) = edges[e];
        pi[h as usize] - pi[t as usize]
    };
    let s: Vec<i64> = (0..m).map(|e| (w[e] - at_pi(e)).max(0)).collect();

    Ok(CertFWitness {
        n_nodes,
        edges,
        w,
        c,
        f,
        pi,
        s,
        epsilon: 0,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_circuit::descriptor_ir2::{
        VmConstraint2, eval_lean_expr, ir2_eval_accepts_i64, parse_vm_descriptor2,
    };
    use dregg_circuit::lean_descriptor_air::VmConstraint;

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
            "the runtime descriptor must be exactly the Lean-emitted `certFDescriptorOf ring3Prog`"
        );
    }

    /// The integer-admission revision is a deliberate descriptor compatibility break.  These
    /// shape teeth turn RED if a flow/slack tight recompose or any potential range gadget is
    /// removed from either registered wire.
    #[test]
    fn registered_descriptors_carry_integer_admission_policy() {
        let ring = cert_f_descriptor(&ring3_cert());
        assert_eq!(ring.trace_width, 465);
        assert_eq!(ring.constraints.len(), 482);

        let market = try_cert_f_descriptor(&market4_cert()).expect("market4 is registered");
        assert_eq!(market.trace_width, 581);
        assert_eq!(market.constraints.len(), 602);

        let ring_policy = registered_program(&ring3_cert()).unwrap();
        assert_eq!((ring_policy.flow_bits, ring_policy.slack_bits), (28, 28));
        let market_policy = registered_program(&market4_cert()).unwrap();
        assert_eq!(
            (market_policy.flow_bits, market_policy.slack_bits),
            (21, 19)
        );
    }

    /// RED-WHEN-BROKEN: shifting every potential by `2^28` preserves every integer certificate
    /// equation (only potential differences are used), so the native Cert-F check still accepts.
    /// Descriptor v1 also accepted because π was unrestricted; the appended π range gadgets must
    /// reject this otherwise-valid representative.
    #[test]
    fn air_rejects_unranged_potential_shift() {
        let mut cert = ring3_cert();
        for pi in &mut cert.pi {
            *pi += 1 << VALUE_BITS;
        }
        assert!(
            cert.check().valid,
            "a common potential shift preserves Cert-F"
        );
        let desc = cert_f_descriptor(&cert);
        let pis: Vec<i64> = cert
            .public_inputs()
            .iter()
            .map(|b| b.as_u32() as i64)
            .collect();
        assert!(
            !ir2_eval_accepts_i64(&desc, &i64_trace(&cert), &pis),
            "an otherwise-valid 2^28 potential shift must hit the deployed range tooth"
        );
        // ring3: core 389 + 3 flow + 3 slack + π₀'s 28 boolean gates, then recompose.
        let row = cert.base_trace();
        assert_ne!(gate_value(&desc, 423, &row[0]), BabyBear::ZERO);
    }

    /// The two market-specific tight recomposes reuse the original boolean bands but bind only
    /// their low 21 / 19 bits. These direct gate teeth isolate the exact policy constraints from
    /// the other certificate families, so deleting either append turns this test RED.
    #[test]
    fn market4_tight_flow_and_slack_gates_bite() {
        let mut flow = market4_cert();
        flow.f[0] = 1 << 21;
        let desc = try_cert_f_descriptor(&flow).expect("public program remains registered");
        let row = flow.base_trace();
        // market4 core ends at 507; the first appended gate is f₀ < 2²¹.
        assert_ne!(gate_value(&desc, 507, &row[0]), BabyBear::ZERO);

        let mut slack = market4_cert();
        slack.s[0] = 1 << 19;
        let row = slack.base_trace();
        // Four flow guards occupy 507..510; s₀ < 2¹⁹ is constraint 511.
        assert_ne!(gate_value(&desc, 511, &row[0]), BabyBear::ZERO);
    }

    /// The i64 base-trace as the native evaluator wants it (single row is enough — every
    /// row is identical, but we hand it the real height).
    fn i64_trace(cert: &CertFWitness) -> Vec<Vec<i64>> {
        let felt = cert.base_trace();
        felt.iter()
            .map(|r| r.iter().map(|c| c.as_u32() as i64).collect())
            .collect()
    }

    fn gate_value(desc: &EffectVmDescriptor2, constraint: usize, row: &[BabyBear]) -> BabyBear {
        match &desc.constraints[constraint] {
            VmConstraint2::Base(VmConstraint::Gate(body)) => eval_lean_expr(body, row),
            other => panic!("constraint {constraint} is not an admission gate: {other:?}"),
        }
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

    /// A new public program is refused until it has its own proved Lean artifact.
    #[test]
    fn unregistered_cycle6_is_refused() {
        let cert = cycle_cert(6, 1000);
        assert!(cert.check().valid);
        let err = try_cert_f_descriptor(&cert).expect_err("cycle-6 is not Lean-registered");
        assert!(err.contains("not registered"));
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
        let mut cert = ring3_cert();
        cert.f = vec![2, 2, 2]; // keep conservation; every f exceeds unit capacity
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

    /// POSITIVE: a valid certificate is proven in the production, binding IR-v2
    /// STARK and the proof VERIFIES.  This compatibility proof is not witness-hiding;
    /// the hiding polarity is pinned separately below.
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

    /// HIDING POSITIVE + BINDING NEGATIVE: the same Cert-F AIR proves under
    /// `HidingFriPcs`, verifies without the witness, and refuses a changed public
    /// cleared volume.  The config's randomness comes from fresh OS entropy; this
    /// tooth exercises the actual batch-STARK ZK path rather than merely type-checking
    /// the config.
    #[test]
    fn hiding_stark_proves_and_binds_public_volume_ring3() {
        let cert = ring3_cert();
        assert!(cert.check().valid);
        let (desc, proof, pis) =
            prove_cert_f_zk(&cert).expect("valid ring3 must prove through HidingFriPcs");
        assert_eq!(pis, cert.public_inputs());
        assert_eq!(pis[0].as_u32(), 3);
        assert!(
            proof.commitments.random.is_some(),
            "the batch proof must carry the ZK random-polynomial commitment"
        );
        assert!(
            proof
                .opened_values
                .instances
                .iter()
                .all(|instance| instance.base_opened_values.random.is_some()),
            "every present AIR instance must carry its ZK random opening"
        );
        verify_cert_f_zk(&desc, &proof, &pis)
            .expect("the hiding Cert-F proof must verify without its witness");

        let mut forged_pis = pis.clone();
        forged_pis[0] = BabyBear::new(4);
        assert!(
            verify_cert_f_zk(&desc, &proof, &forged_pis).is_err(),
            "a hiding proof for volume 3 must not verify as volume 4"
        );
    }

    /// The proving surface also fails closed for an unregistered public program.
    #[test]
    fn stark_refuses_unregistered_cycle6() {
        let cert = cycle_cert(6, 1000);
        assert!(cert.check().valid);
        let err = match prove_cert_f(&cert) {
            Err(e) => e,
            Ok(_) => panic!("unregistered cycle-6 must fail closed"),
        };
        assert!(err.contains("not registered"));
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

    // ========================================================================
    // The MARKET4 registered program — the first real market shape past ring-3
    // (3 assets / 4 orders, fixed-point scale 100, PRESCRIPTIVE ε = 2000).
    // ========================================================================

    /// The worked market4 optimum is Cert-F-valid and tight.
    #[test]
    fn market4_check_is_valid_tight() {
        let cert = market4_cert();
        let chk = cert.check();
        assert!(
            chk.valid,
            "the worked market4 certificate must be valid: {chk:?}"
        );
        assert_eq!(chk.gap, 0, "exact optimum: gap 0");
        assert_eq!(cert.objective(), 180_000, "cleared volume wᵀf = 180000");
    }

    /// POSITIVE: the market4 program resolves to the Lean-emitted market4 artifact
    /// (not ring-3's) and its worked certificate proves + verifies in the REAL STARK.
    #[test]
    fn stark_proves_and_verifies_market4() {
        let cert = market4_cert();
        let desc = try_cert_f_descriptor(&cert).expect("market4 is Lean-registered");
        assert_eq!(
            desc.trace_width, 581,
            "the market4 descriptor (m=4), not ring-3's 465"
        );
        let (desc, proof, pis) =
            prove_cert_f(&cert).expect("the worked market4 certificate must prove");
        assert_eq!(pis[0].as_u32(), 180_000, "the world sees exactly wᵀf");
        verify_cert_f(&desc, &proof, &pis).expect("the minted market4 proof must verify");
    }

    /// **THE ε-BUDGET FIX, positive polarity:** a certificate with a REAL nonzero achieved
    /// gap (1000 > 0) under the registered budget (ε = 2000) registers AND proves — the
    /// exact case the ε=0-only ring-3 era refused. The mutation tooth is inline: the SAME
    /// witness carrying the OLD descriptive semantics (ε := achieved gap = 1000) does NOT
    /// match any registration and fails closed.
    #[test]
    fn stark_market4_epsilon_budget_accepts_nonzero_gap() {
        // Perturb the dual: π = (200, 0, 98). s = (w − Aᵀπ)₊ = (300, 2, 0, 100);
        // cᵀs = 150000 + 1000 + 0 + 30000 = 181000; gap = 1000 ∈ (0, 2000].
        let mut cert = market4_cert();
        cert.pi = vec![200, 0, 98];
        cert.s = vec![300, 2, 0, 100];
        let chk = cert.check();
        assert!(
            chk.valid,
            "gap-1000 certificate is valid under the 2000 budget: {chk:?}"
        );
        assert_eq!(chk.gap, 1000, "the achieved gap is genuinely nonzero");
        let (desc, proof, pis) =
            prove_cert_f(&cert).expect("a real (gap > 0) certificate within budget must prove");
        verify_cert_f(&desc, &proof, &pis).expect("the ε-budget proof must verify");

        // Mutation tooth: the OLD `ε := achieved gap` bridge semantics on the same witness
        // is unregistered (1000 ≠ 2000) — the mismatch this fix removed from the real path.
        let mut descriptive = cert.clone();
        descriptive.epsilon = descriptive.gap();
        assert!(descriptive.check().valid);
        let err = try_cert_f_descriptor(&descriptive)
            .expect_err("descriptive ε must NOT match the ε-budget registration");
        assert!(err.contains("not registered"));
    }

    /// NEGATIVE (budget teeth): a certificate whose achieved gap EXCEEDS the registered
    /// budget (5000 > 2000) is refused by the STARK — the gap slack g = ε − gap = −3000
    /// has no VALUE_BITS-bit range preimage.
    #[test]
    fn stark_market4_refuses_gap_over_budget() {
        // π = (200, 0, 90): s = (300, 10, 0, 100); cᵀs = 185000; gap = 5000 > ε = 2000.
        let mut cert = market4_cert();
        cert.pi = vec![200, 0, 90];
        cert.s = vec![300, 10, 0, 100];
        let chk = cert.check();
        assert!(
            chk.conserves && !chk.gap_ok,
            "gap 5000 must exceed the 2000 budget: {chk:?}"
        );
        assert!(
            prove_cert_f_refused(&cert),
            "the STARK must REFUSE a certificate over the ε budget"
        );
    }

    /// **THE REAL SOLVE, end-to-end:** run the ACTUAL PDHG solver (fhegg-solver) on the
    /// market4 f64 program, restore exact feasibility, emit the Cert-F JSON wire, bridge it
    /// at the registered scale (100) under the registered prescriptive budget (2000), and
    /// prove THAT in the production STARK. This is roadmap §4.2(a): a genuine solver output
    /// on a registered shape proving without landing exactly tight.
    #[test]
    fn stark_proves_real_market4_pdhg_solve() {
        use fhegg_solver::cert::CertF;
        use fhegg_solver::pdhg::{FlowLp, restore_feasibility, solve_cpu};
        // The f64 program whose ×100 fixed-point image is the REGISTERED market4 program.
        let lp = FlowLp {
            n_nodes: 3,
            edges: vec![(0, 1), (1, 2), (2, 0), (1, 0)],
            w: vec![1.0, 1.0, 1.0, 3.0],
            c: vec![5.0, 5.0, 5.0, 3.0],
        };
        let res = solve_cpu(&lp, 8000);
        let (f_exact, _box_viol) = restore_feasibility(&lp, res.f.clone());
        let cert_f64 = CertF::from_solution(&lp, &f_exact, &res.y, 0.2);
        assert!(
            cert_f64.check_strict().valid,
            "the untrusted PDHG search must produce a strictly-checkable f64 certificate"
        );
        let json = cert_f64.to_json();

        let cert = from_solution_json_with_epsilon(&json, 100, 2000)
            .expect("the real solve must bridge under the registered ε budget");
        let chk = cert.check();
        assert!(
            chk.valid,
            "bridged real-solve certificate must be Cert-F-valid: {chk:?}"
        );
        assert!(
            chk.gap >= 0 && chk.gap <= 2000,
            "achieved gap within budget: {}",
            chk.gap
        );
        let (desc, proof, pis) =
            prove_cert_f(&cert).expect("the real market4 solve must prove in the STARK");
        assert_eq!(
            pis[0].as_u32() as i64,
            cert.objective(),
            "the public input is the solve's own cleared volume"
        );
        verify_cert_f(&desc, &proof, &pis).expect("the real-solve proof must verify");
    }

    /// The prescriptive bridge REFUSES a solve whose achieved gap exceeds the budget —
    /// it asserts nothing it does not verify.
    #[test]
    fn bridge_with_epsilon_refuses_over_budget_gap() {
        // The worked optimum's JSON wire, but with a deliberately bad dual (π = 0 makes
        // s = w, cᵀs = 500+500+500+900 = 2400 → scaled gap = 24_000_000... use the f64
        // program at unit scale instead: gap = cᵀs − wᵀf = 2400·… ). Simplest: scale 100
        // with π = 0 on the market4 program: s = w = (100,100,100,300) after scaling,
        // cᵀs = 500·100·3 + 300·300 = 240000; wᵀf = 180000; gap = 60000 > 2000.
        let json = r#"{
            "n_nodes": 3,
            "m_edges": 4,
            "edges": [[0,1],[1,2],[2,0],[1,0]],
            "w": [1.0, 1.0, 1.0, 3.0],
            "c": [5.0, 5.0, 5.0, 3.0],
            "f": [5.0, 2.0, 2.0, 3.0],
            "pi": [0.0, 0.0, 0.0],
            "s": [1.0, 1.0, 1.0, 3.0],
            "epsilon": 0.0
        }"#;
        let err = from_solution_json_with_epsilon(json, 100, 2000)
            .expect_err("a 60000 gap must not pass a 2000 budget");
        assert!(
            err.contains("exceeds the prescriptive"),
            "named refusal: {err}"
        );
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
