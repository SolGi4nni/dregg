//! **WHAT BINDS A `degree_bits = 0` INSTANCE'S AIR CHECK** — the control for the root batch's
//! one-row table (`expose_claim`), whose closing equality is an IDENTITY IN ζ.
//!
//! ## The observation this exists to bound
//!
//! `circuit-prove/src/bin/root_air_instance.rs` measures, on dregg's committed root proof, that
//! bending ζ while holding the opened values fixed leaves `expose_claim`'s closing equality
//! satisfied — six of seven instances refuse the bend, `expose_claim` does not. The shape is
//! forced: at `degree_bits = 0` the trace domain is `{1}`, so p3's `selectors_at_point` returns
//! `is_first_row = is_last_row = 1` (ζ-FREE) and `is_transition = ζ − 1 = Z_H(ζ)`, and the two
//! size-1 quotient chunks carry EQUAL values, which recompose to a ζ-free constant.
//!
//! Written as an equation, with `A` the α-fold of every constraint NOT gated by
//! `when_transition` and `B` the α-fold of the transition-gated ones:
//!
//! ```text
//!   accumulator(ζ)  =  A + (ζ − 1)·B          quotient(ζ)  =  Σ_i zps_i(ζ)·c_i
//!   the verifier checks   accumulator(ζ) · Z_H(ζ)^{-1}  ==  quotient(ζ)
//!                    i.e.  A/(ζ − 1) + B  ==  quotient(ζ)
//! ```
//!
//! An HONEST prover has `A = 0` and equal chunks, so both sides are the constant `B` and the
//! equality holds at EVERY ζ. That is the identity. It is a property of the honest transcript.
//!
//! ## The thing that is NOT true, and that this file refuses
//!
//! "The out-of-domain point binds nothing there." It binds the FORGERY, which is the only thing
//! an OOD point is ever asked to bind. `A`, `B` and the `c_i` are all fixed BEFORE ζ is sampled —
//! the trace/permutation/preprocessed openings and the quotient chunks of a height-1 table are
//! each committed on a domain of size 1, and `p3_fri`'s verifier REQUIRES the reduced opening at
//! `log_height == log_blowup` to be exactly zero (`vendor/plonky3-fri-82cfad73/src/verifier.rs`,
//! the `reduced_openings.get(&params.log_blowup)` guard), which pins every one of them to a
//! constant equal to its claimed opening. So the check is the evaluation at a uniform ζ of
//!
//! ```text
//!   P(X)  =  A + (X − 1)·B  −  (X − 1)·Σ_i zps_i(X)·c_i        deg P ≤ 2
//! ```
//!
//! and `P(1) = A`. A prover with `A ≠ 0` has `P ≢ 0`, so `P` has at most two roots and the check
//! refuses except with probability `≤ 2/|EF| ≈ 2^-123`. ζ is exactly what forces `A = 0`.
//!
//! ## What the legs measure
//!
//! * [`height1_selectors_are_one_one_zh_and_inv_zh`] — the identity's PREMISE, from p3's own
//!   `selectors_at_point`, not from this comment.
//! * [`height1_honest_closing_equality_is_an_identity_in_zeta`] — reproduces the observation from
//!   the shape alone: `A = 0` + equal chunks ⇒ the equality holds at every ζ tried.
//! * [`height1_forged_accumulator_is_refused_at_a_resampled_zeta`] — **the refutation.** A forger
//!   with `A ≠ 0` CAN repair the equality at one prescribed ζ (measured: it closes there), and
//!   the repaired instance then fails at every other ζ. ζ binds the forgery it is there to bind.
//! * [`degree_bits_zero_tables_gate_no_constraint_behind_when_transition`] — **the recurrence
//!   guard.** The real hazard of a one-row table is not the identity: it is that `is_transition`
//!   VANISHES on a one-row domain, so any constraint written `builder.when_transition()` is
//!   unenforced there. `ExposeClaimAir` writes none, and LogUp's transition-gated running-sum
//!   update is redundant at height 1 because its first-row and last-row siblings pin `s = 0` and
//!   `cumulative_sum = contribution`. Both facts are asserted over p3's own symbolic constraints.
//! * [`root_verifier_refuses_a_falsified_expose_claim`] — end-to-end on the committed root proof:
//!   falsify the host-readable claim, the trace opening, a quotient chunk or the LogUp cumulative
//!   sum, and dregg's deployed verifier must refuse. ⚑ It refuses all four at the PCS
//!   (`InvalidOpeningArgument`), never at the AIR equality: every one of those fields is in the
//!   transcript, so a post-hoc tamper cannot reach the closing equality. That is why the AIR
//!   check's own bindingness has to be measured separately, in the leg above.
//!
//! ⚑ SUBSTRATE: no AIR is authored here. Every constraint object is p3's (`ExposeClaimAir`,
//! `LogUpGadget`) and every evaluator is p3's (`selectors_at_point`,
//! `recompose_quotient_from_chunks`, `get_symbolic_constraints`). This file only MEASURES them.

use dregg_circuit_prove::ivc_turn_chain::{WholeChainProofBytes, ir2_leaf_wrap_config};
use dregg_circuit_prove::plonky3_recursion_impl::recursive::{
    DreggRecursionConfig, verify_recursive_batch_proof_with_config,
};
use p3_air::BaseAir;
use p3_air::symbolic::{
    AirLayout, BaseLeaf, ExtLeaf, SymbolicExpr, SymbolicExpression, SymbolicExpressionExt,
};
use p3_baby_bear::BabyBear;
use p3_batch_stark::symbolic::get_symbolic_constraints;
use p3_circuit_prover::BatchStarkProof;
use p3_circuit_prover::air::ExposeClaimAir;
use p3_commit::PolynomialSpace;
use p3_field::coset::TwoAdicMultiplicativeCoset;
use p3_field::extension::BinomialExtensionField;
use p3_field::{BasedVectorSpace, Field, PrimeCharacteristicRing};
use p3_lookup::{Kind, LogUpGadget, Lookups};
use p3_uni_stark::recompose_quotient_from_chunks;

/// The root's base field.
type F = BabyBear;
/// The root's challenge field (`circuit-prove/src/plonky3_recursion_impl.rs:136`).
type EF = BinomialExtensionField<F, 4>;
/// The config the root verifies under.
type SC = DreggRecursionConfig;
/// The circuit's extension degree.
const D: usize = 4;
/// `SEG_WIDTH = NUM_CHAIN_CLAIMS` (`circuit-prove/src/ivc_turn_chain.rs:366,278`).
const NUM_CHAIN_CLAIMS: usize = 25;
/// The committed whole-history envelope the end-to-end leg reads.
const FIXTURE: &str = "ugc-dregg/tests/fixtures/whole_history_proof.bin";

/// The deployed one-row table: 25 lanes, no preprocessed content of its own, `min_height = 1`.
fn expose_claim_air() -> ExposeClaimAir<F, D> {
    ExposeClaimAir::<F, D>::new_with_preprocessed(NUM_CHAIN_CLAIMS, Vec::new(), 1)
}

/// A deterministic pseudorandom `EF`, so a red is reproducible.
fn ef_at(seed: u64) -> EF {
    let mut x = seed.wrapping_mul(0x9e37_79b9_7f4a_7c15).wrapping_add(1);
    let mut limbs = [F::ZERO; D];
    for limb in &mut limbs {
        x ^= x >> 30;
        x = x.wrapping_mul(0xbf58_476d_1ce4_e5b9);
        x ^= x >> 27;
        x = x.wrapping_mul(0x94d0_49bb_1331_11eb);
        x ^= x >> 31;
        *limb = F::from_u32((x % 2_013_265_921) as u32);
    }
    EF::from_basis_coefficients_slice(&limbs).expect("D limbs is the extension dimension")
}

/// The trace domain of a `degree_bits`-bit instance, exactly as `verify_batch` builds it
/// (`natural_domain_for_degree(1 << degree_bits)`, which for `TwoAdicFriPcs` is the natural coset).
fn trace_domain(degree_bits: usize) -> TwoAdicMultiplicativeCoset<F> {
    TwoAdicMultiplicativeCoset::<F>::new(F::ONE, degree_bits)
        .expect("degree_bits within BabyBear's two-adicity")
}

/// The quotient chunk domains, exactly as `verify_batch` builds them
/// (`batch-stark/src/verifier/mod.rs:360-375` at `is_zk = 0`).
fn chunk_domains(degree_bits: usize, log_num_chunks: usize) -> Vec<TwoAdicMultiplicativeCoset<F>> {
    trace_domain(degree_bits)
        .create_disjoint_domain(1 << (degree_bits + log_num_chunks))
        .split_domains(1 << log_num_chunks)
}

/// Encode one `EF` value in the wire shape a quotient chunk opening has: `DIMENSION` basis
/// coefficients, each lifted into `EF` (which is what `from_ext_basis_coefficients` consumes).
fn chunk_opening(v: EF) -> Vec<EF> {
    let limbs: &[F] = <EF as BasedVectorSpace<F>>::as_basis_coefficients_slice(&v);
    limbs.iter().map(|c| EF::from(*c)).collect()
}

/// The closing equality `p3_batch_stark`'s verifier checks, for an instance whose accumulator
/// decomposes as `first·a_first + last·a_last + a_plain + transition·b`.
///
/// The selector multiplications are p3's values, not assumed constants — at `degree_bits > 0`
/// they are not 1 and this still models the check faithfully.
struct Height1Instance {
    degree_bits: usize,
    /// The α-fold of the `when_first_row`-gated constraints.
    a_first: EF,
    /// The α-fold of the `when_last_row`-gated constraints.
    a_last: EF,
    /// The α-fold of the ungated constraints.
    a_plain: EF,
    /// The α-fold of the `when_transition`-gated constraints.
    b: EF,
}

impl Height1Instance {
    fn accumulator(&self, zeta: EF) -> EF {
        let s = trace_domain(self.degree_bits).selectors_at_point(zeta);
        s.is_first_row * self.a_first
            + s.is_last_row * self.a_last
            + self.a_plain
            + s.is_transition * self.b
    }

    /// `A` — the ζ-free half at `degree_bits = 0`, and the quantity the check forces to zero.
    fn a(&self) -> EF {
        self.a_first + self.a_last + self.a_plain
    }

    fn closes(&self, chunks: &[Vec<EF>], zeta: EF) -> bool {
        let log_num_chunks = chunks.len().trailing_zeros() as usize;
        let doms = chunk_domains(self.degree_bits, log_num_chunks);
        let s = trace_domain(self.degree_bits).selectors_at_point(zeta);
        let quotient = recompose_quotient_from_chunks::<SC>(&doms, chunks, zeta);
        self.accumulator(zeta) * s.inv_vanishing == quotient
    }
}

// ===========================================================================
// LEG A — the identity's PREMISE, measured from p3's own selectors.
// ===========================================================================

/// **A ONE-ROW TRACE DOMAIN MAKES TWO OF THE FOUR SELECTORS ζ-FREE.** `is_first_row` and
/// `is_last_row` are both the constant `1`, `is_transition` IS the vanishing polynomial, and the
/// inverse vanishing polynomial is its inverse. Everything downstream in this file rests on this,
/// so it is measured rather than asserted in prose.
#[test]
fn height1_selectors_are_one_one_zh_and_inv_zh() {
    let dom = trace_domain(0);
    assert_eq!(dom.size(), 1, "degree_bits = 0 is a one-row trace domain");

    for seed in 0..16u64 {
        let zeta = ef_at(seed);
        if zeta == EF::ONE {
            continue; // Z_H(1) = 0; the verifier's ζ is uniform over a 2^124-element field.
        }
        let s = dom.selectors_at_point(zeta);
        let z_h = zeta - EF::ONE;
        assert_eq!(s.is_first_row, EF::ONE, "is_first_row is the constant 1");
        assert_eq!(s.is_last_row, EF::ONE, "is_last_row is the constant 1");
        assert_eq!(s.is_transition, z_h, "is_transition IS Z_H(zeta)");
        assert_eq!(
            s.inv_vanishing,
            z_h.inverse(),
            "inv_vanishing is 1/Z_H(zeta)"
        );
    }

    // The contrast: at any degree_bits > 0 the first/last-row selectors move with zeta.
    for db in 1..4usize {
        let s0 = trace_domain(db).selectors_at_point(ef_at(101));
        let s1 = trace_domain(db).selectors_at_point(ef_at(202));
        assert_ne!(
            s0.is_first_row, s1.is_first_row,
            "degree_bits {db}: is_first_row must depend on zeta"
        );
    }
}

// ===========================================================================
// LEG B — the observation reproduced, then REFUTED as a statement about the check.
// ===========================================================================

/// **THE OBSERVATION, FROM THE SHAPE ALONE.** An honest one-row instance (`A = 0`, equal chunks)
/// satisfies the closing equality at EVERY ζ. This is what `root_air_instance` measures on the
/// committed root proof as `zetaBinding = false`, reproduced here without the proof so the cause
/// is visible: it is the honest transcript's insensitivity, not the check's.
#[test]
fn height1_honest_closing_equality_is_an_identity_in_zeta() {
    for log_num_chunks in 0..3usize {
        let b = ef_at(7);
        let inst = Height1Instance {
            degree_bits: 0,
            a_first: ef_at(11),
            a_last: ef_at(13),
            // A = a_first + a_last + a_plain = 0 — an honest prover's non-transition fold.
            a_plain: -(ef_at(11) + ef_at(13)),
            b,
        };
        assert_eq!(inst.a(), EF::ZERO, "the honest non-transition fold is zero");

        // Equal chunks: `Σ_i zps_i(ζ) = 1`, so the quotient recomposes to the constant `b`.
        let chunks: Vec<Vec<EF>> = (0..(1 << log_num_chunks))
            .map(|_| chunk_opening(b))
            .collect();

        for seed in 0..12u64 {
            let zeta = ef_at(1_000 + seed);
            assert!(
                inst.closes(&chunks, zeta),
                "{} chunks: the honest one-row closing equality must hold at every zeta",
                1 << log_num_chunks
            );
        }
    }
}

/// **THE REFUTATION.** A forged one-row trace moves `A` off zero. The forger can always repair the
/// closing equality at ONE prescribed ζ — that freedom is real and is measured here, not waved at.
/// But the quotient chunks are committed BEFORE ζ is sampled, so the repair is pinned to the ζ it
/// was solved for: at every other ζ the equality fails. The out-of-domain point binds the forgery.
///
/// This is the leg that would go red if a future change made a one-row closing equality genuinely
/// vacuous — e.g. if the quotient were recomposed ζ-free AND the `Z_H(ζ)^{-1}` division dropped.
#[test]
fn height1_forged_accumulator_is_refused_at_a_resampled_zeta() {
    for log_num_chunks in 0..3usize {
        let n_chunks = 1usize << log_num_chunks;
        let doms = chunk_domains(0, log_num_chunks);

        // A forged trace: the non-transition fold is now nonzero.
        let forged = Height1Instance {
            degree_bits: 0,
            a_first: ef_at(21),
            a_last: ef_at(23),
            a_plain: ef_at(29),
            b: ef_at(31),
        };
        assert_ne!(forged.a(), EF::ZERO, "the forgery must actually move A");

        // Honest chunks (all equal to `b`) do NOT close for a forged A — the naive forgery is
        // refused outright.
        let honest_chunks: Vec<Vec<EF>> = (0..n_chunks).map(|_| chunk_opening(forged.b)).collect();
        assert!(
            !forged.closes(&honest_chunks, ef_at(2_001)),
            "{n_chunks} chunks: a forged A with honest chunks must not close"
        );

        // The ADAPTIVE forgery: solve the chunk openings that repair the equality at `zeta_hit`.
        // `zps_0(zeta)` is read off p3's own recomposition by feeding it a unit first chunk.
        let zeta_hit = ef_at(3_003);
        let s = trace_domain(0).selectors_at_point(zeta_hit);
        let target = forged.accumulator(zeta_hit) * s.inv_vanishing;
        let mut unit: Vec<Vec<EF>> = (0..n_chunks).map(|_| chunk_opening(EF::ZERO)).collect();
        unit[0] = chunk_opening(EF::ONE);
        let zps_0 = recompose_quotient_from_chunks::<SC>(&doms, &unit, zeta_hit);
        assert_ne!(
            zps_0,
            EF::ZERO,
            "the first chunk's Lagrange weight is nonzero"
        );

        let mut repaired: Vec<Vec<EF>> = (0..n_chunks).map(|_| chunk_opening(EF::ZERO)).collect();
        repaired[0] = chunk_opening(target * zps_0.inverse());

        assert!(
            forged.closes(&repaired, zeta_hit),
            "{n_chunks} chunks: the forger CAN repair the equality at the zeta it solved for — \
             if this is red the experiment is not testing what it claims"
        );

        // …and nowhere else. `P(X) = A + (X-1)B - (X-1)·q(X)` has degree ≤ 2 and `P(1) = A ≠ 0`,
        // so at most two zetas can satisfy it. Twelve fresh zetas must all refuse.
        let mut survived = Vec::new();
        for seed in 0..12u64 {
            let zeta = ef_at(4_000 + seed);
            if forged.closes(&repaired, zeta) {
                survived.push(seed);
            }
        }
        assert!(
            survived.is_empty(),
            "{n_chunks} chunks: a zeta-solved forgery survived a RESAMPLED zeta at seeds \
             {survived:?} — the out-of-domain point would not be binding this instance"
        );

        // The same, for the forgery that keeps the chunks EQUAL (so the quotient stays zeta-free,
        // matching the honest shape byte-for-byte and defeating any "are the chunks equal?" check).
        let flat: Vec<Vec<EF>> = (0..n_chunks).map(|_| chunk_opening(target)).collect();
        assert!(
            forged.closes(&flat, zeta_hit),
            "{n_chunks} chunks: the equal-chunk forgery closes at its solved zeta"
        );
        for seed in 0..12u64 {
            assert!(
                !forged.closes(&flat, ef_at(5_000 + seed)),
                "{n_chunks} chunks: an equal-chunk forgery survived a resampled zeta"
            );
        }
    }
}

// ===========================================================================
// LEG C — the recurrence guard: what a one-row table may NOT hide.
// ===========================================================================

fn base_leaf_counts(
    e: &SymbolicExpression<F>,
    first: &mut usize,
    last: &mut usize,
    tr: &mut usize,
) {
    match e {
        SymbolicExpr::Leaf(BaseLeaf::IsFirstRow) => *first += 1,
        SymbolicExpr::Leaf(BaseLeaf::IsLastRow) => *last += 1,
        SymbolicExpr::Leaf(BaseLeaf::IsTransition) => *tr += 1,
        SymbolicExpr::Leaf(_) => {}
        SymbolicExpr::Add { x, y, .. } | SymbolicExpr::Sub { x, y, .. } => {
            base_leaf_counts(x, first, last, tr);
            base_leaf_counts(y, first, last, tr);
        }
        SymbolicExpr::Mul { x, y, .. } => {
            base_leaf_counts(x, first, last, tr);
            base_leaf_counts(y, first, last, tr);
        }
        SymbolicExpr::Neg { x, .. } => base_leaf_counts(x, first, last, tr),
    }
}

fn ext_leaf_counts(
    e: &SymbolicExpressionExt<F, EF>,
    first: &mut usize,
    last: &mut usize,
    tr: &mut usize,
) {
    match e {
        SymbolicExpr::Leaf(ExtLeaf::Base(b)) => base_leaf_counts(b, first, last, tr),
        SymbolicExpr::Leaf(_) => {}
        SymbolicExpr::Add { x, y, .. } | SymbolicExpr::Sub { x, y, .. } => {
            ext_leaf_counts(x, first, last, tr);
            ext_leaf_counts(y, first, last, tr);
        }
        SymbolicExpr::Mul { x, y, .. } => {
            ext_leaf_counts(x, first, last, tr);
            ext_leaf_counts(y, first, last, tr);
        }
        SymbolicExpr::Neg { x, .. } => ext_leaf_counts(x, first, last, tr),
    }
}

/// **THE ONE-ROW HAZARD, NAMED AND GATED.** `is_transition` is `Z_H(ζ)` on a one-row domain, so it
/// vanishes on the domain: a constraint written `builder.when_transition()` is NOT enforced on a
/// `degree_bits = 0` table. That — not the ζ-identity — is what a future one-row table could
/// silently acquire.
///
/// Measured over p3's own symbolic constraint sets:
///
/// * `ExposeClaimAir`'s OWN constraints (`base`) contain no `IsTransition` leaf at all: all 25
///   lane bindings `active·(public_value − v_0)` are ungated and therefore enforced at height 1.
/// * LogUp contributes exactly three constraints per lookup — `when_first_row(s = 0)`,
///   `when_transition(running-sum update)`, `when_last_row(cumulative_sum pinned)`. The
///   transition-gated one is the vacuous one at height 1, and it is redundant there: the first-row
///   and last-row siblings on the SAME row give `s = 0` and `cumulative_sum·denom = numerator`,
///   which is the bus binding the table's soundness rests on.
///
/// A fourth transition-gated LogUp constraint, or an `ExposeClaimAir` constraint moved behind
/// `when_transition`, moves these counts and turns this leg red.
#[test]
fn degree_bits_zero_tables_gate_no_constraint_behind_when_transition() {
    let air = expose_claim_air();
    let lookups = Lookups::<F>::from_air::<EF, _>(&air);
    let num_global = lookups
        .iter()
        .filter(|c| matches!(&c.kind, Kind::Global(_)))
        .count();
    assert_eq!(
        num_global, NUM_CHAIN_CLAIMS,
        "one WitnessChecks read per exposed claim"
    );

    let layout = AirLayout {
        preprocessed_width: air.preprocessed_width(),
        main_width: air.width(),
        num_public_values: air.num_public_values(),
        num_permutation_values: num_global,
        ..Default::default()
    };
    let (base, ext) = get_symbolic_constraints::<F, EF, _, _>(&air, layout, &lookups, &LogUpGadget);

    // --- the AIR's own constraints: none may be transition-gated ---------------
    let mut b_first = 0;
    let mut b_last = 0;
    let mut b_tr = 0;
    for c in &base {
        base_leaf_counts(c, &mut b_first, &mut b_last, &mut b_tr);
    }
    assert_eq!(
        base.len(),
        NUM_CHAIN_CLAIMS,
        "one lane binding per exposed claim"
    );
    assert_eq!(
        b_tr, 0,
        "a degree_bits = 0 table put {b_tr} of its own constraints behind `when_transition`; on a \
         one-row domain `is_transition = Z_H(zeta)` vanishes and those constraints are NOT \
         ENFORCED. Give the table a real height or drop the gate."
    );
    assert_eq!(
        (b_first, b_last),
        (0, 0),
        "ExposeClaimAir's lane bindings are ungated"
    );

    // --- LogUp's constraints: the transition-gated one must have both boundary siblings ---
    let mut per_constraint = Vec::new();
    for c in &ext {
        let (mut f, mut l, mut t) = (0, 0, 0);
        ext_leaf_counts(c, &mut f, &mut l, &mut t);
        per_constraint.push((f > 0, l > 0, t > 0));
    }
    let n_first = per_constraint.iter().filter(|(f, _, _)| *f).count();
    let n_last = per_constraint.iter().filter(|(_, l, _)| *l).count();
    let n_tr = per_constraint.iter().filter(|(_, _, t)| *t).count();

    assert_eq!(
        (n_first, n_tr, n_last),
        (num_global, num_global, num_global),
        "LogUp's per-lookup shape moved. It must stay first-row(s = 0) + transition(update) + \
         last-row(cumulative_sum pinned): at height 1 the transition leg is vacuous and ONLY the \
         two boundary legs bind the bus. Counts were first={n_first} transition={n_tr} \
         last={n_last} over {} ext constraints for {num_global} lookups.",
        ext.len()
    );
    assert_eq!(
        ext.len(),
        3 * num_global,
        "three LogUp constraints per lookup and no more"
    );
}

// ===========================================================================
// LEG D — end-to-end: dregg's deployed verifier, on dregg's committed root proof.
// ===========================================================================

fn repo_relative(rel: &str) -> std::path::PathBuf {
    let here = std::path::Path::new(rel);
    if here.exists() {
        return here.to_path_buf();
    }
    let manifest = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    let from_root = manifest.parent().unwrap_or(manifest).join(rel);
    if from_root.exists() {
        return from_root;
    }
    here.to_path_buf()
}

fn load_root() -> BatchStarkProof<SC> {
    let fixture = repo_relative(FIXTURE);
    let bytes = std::fs::read(&fixture)
        .unwrap_or_else(|e| panic!("cannot read {}: {e}", fixture.display()));
    let env = WholeChainProofBytes::from_postcard(&bytes)
        .unwrap_or_else(|e| panic!("the committed envelope does not decode: {e:?}"));
    postcard::from_bytes(&env.root_proof)
        .unwrap_or_else(|e| panic!("root BatchStarkProof does not decode: {e}"))
}

/// **CAN A PROVER PUT ANYTHING FALSE IN `expose_claim`'s TRACE AND HAVE DREGG'S OWN VERIFIER
/// ACCEPT IT?** Measured on the committed whole-history root proof: falsify the host-readable
/// claim (the `expose_claim` table's public values — genesis root, final root, `num_turns`, chain
/// digest) or the main-trace cell it is bound to, and `verify_recursive_batch_proof_with_config`
/// must refuse. The unmodified proof must still verify, so the harness is live rather than
/// refusing everything.
#[test]
fn root_verifier_refuses_a_falsified_expose_claim() {
    let config = ir2_leaf_wrap_config();
    let root = load_root();

    verify_recursive_batch_proof_with_config(&root, &config)
        .expect("the committed root proof must verify unmodified");

    let idx = root
        .non_primitives
        .iter()
        .position(|e| e.op_type.as_str() == "expose_claim")
        .expect("the root carries an expose_claim table");
    // The batch instance index: three primitive tables precede the non-primitives.
    let inst = 3 + idx;
    assert_eq!(
        root.proof.degree_bits[inst], 0,
        "expose_claim is the degree_bits = 0 instance this file is about"
    );

    // The refusal REASON is printed, not just the refusal. ⚑ MEASURED, and worth knowing: all four
    // die at `InvalidOpeningArgument`, never at `OodEvaluationMismatch`. Every field touched here
    // is in the Fiat-Shamir transcript — public values at `observe_main`, `global_lookup_data` at
    // `observe_perm_and_sample_alpha`, and every opened value at the head of `pcs.verify` — so a
    // post-hoc tamper desyncs the challenger and dies in FRI before the AIR closing equality is
    // ever evaluated. Tampering with a FINISHED proof therefore cannot exercise the AIR check at
    // all; the adversary the AIR check exists to stop is one who RE-PROVES consistently against a
    // false trace, and that adversary is the one modelled in
    // `height1_forged_accumulator_is_refused_at_a_resampled_zeta`.
    let mut refusals: Vec<(&str, String)> = Vec::new();

    // (1) Falsify the host-readable claim itself.
    let mut forged = load_root();
    let pv = &mut forged.non_primitives[idx].public_values;
    assert!(!pv.is_empty(), "expose_claim exposes public values");
    pv[0] += F::ONE;
    refusals.push((
        "public value (the host-readable chain claim)",
        verify_recursive_batch_proof_with_config(&forged, &config).expect_err(
            "a falsified expose_claim PUBLIC VALUE was ACCEPTED — the host-readable chain claim is \
             forgeable and every downstream reader of `non_primitives[].public_values` is unsound",
        ),
    ));

    // (2) Falsify the main-trace cell the public value is locally bound to.
    let mut forged = load_root();
    forged.proof.opened_values.instances[inst]
        .base_opened_values
        .trace_local[0] += EF::ONE;
    refusals.push((
        "trace opening v_0",
        verify_recursive_batch_proof_with_config(&forged, &config)
            .expect_err("a falsified expose_claim TRACE opening was ACCEPTED"),
    ));

    // (3) Falsify a quotient chunk — the half a one-row instance's closing equality leans on.
    let mut forged = load_root();
    forged.proof.opened_values.instances[inst]
        .base_opened_values
        .quotient_chunks[0][0] += EF::ONE;
    refusals.push((
        "quotient chunk",
        verify_recursive_batch_proof_with_config(&forged, &config)
            .expect_err("a falsified expose_claim QUOTIENT CHUNK was ACCEPTED"),
    ));

    // (4) Falsify the LogUp cumulative sum — the bus binding, which at height 1 is pinned by the
    // last-row constraint ALONE (the transition-gated running-sum update is vacuous there).
    let mut forged = load_root();
    forged.proof.global_lookup_data[inst]
        .first_mut()
        .expect("expose_claim carries global WitnessChecks lookup data")
        .cumulative_sum += EF::ONE;
    refusals.push((
        "LogUp cumulative sum (the WitnessChecks bus binding)",
        verify_recursive_batch_proof_with_config(&forged, &config).expect_err(
            "a falsified expose_claim CUMULATIVE SUM was ACCEPTED — the WitnessChecks bus does not \
             bind the one-row table",
        ),
    ));

    for (what, why) in &refusals {
        println!("  falsified {what} -> REFUSED: {why}");
    }
}
