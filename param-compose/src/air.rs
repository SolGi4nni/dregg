//! **THE GENERAL PARAMETER-COMPOSITION AIR.**
//!
//! It proves, for a bounded [`ComposeShape`]:
//!
//! > Given the canonical ordered list of typed projections committed by `subjects_root`,
//! > and the versioned law committed by `ruleset_root`, the value committed by
//! > `outcome_commitment` is the composition that law licenses — and the per-term
//! > contributions committed by `explanation_root` are the terms it is made of.
//!
//! Everything the AIR *knows* is a bound. It does not know a role, a param name, a rule,
//! or a game. The law is WITNESSED and bound to a public root, so a new ruleset is new
//! data under the same VK.
//!
//! # The teeth, and exactly what each one reaches
//!
//! | tooth | mechanism | reaches |
//! |---|---|---|
//! | canonical order + duplicate rejection | STRICT increase of `identity` across active slots, via `forced_ge0` over the shape's `identity_bits`-bounded range | refuses an unsorted or identity-duplicated list IN-CIRCUIT (not by host courtesy) |
//! | a role is a KEY | pairwise `role_i != role_j` for active slots, plus `role != 0` when active | makes `role -> subject` a FUNCTION, so the outcome is not prover-malleable |
//! | the law is load-bearing | every coefficient is a witnessed column absorbed into the `ruleset_root` chain, and the root is PI-bound | a prover using other coefficients cannot publish the committed root |
//! | the projections are bound | every `(active, identity, role, params)` felt is absorbed into the `subjects_root` chain | a forged/edited projection moves the root |
//! | absence is committed | inactive slots and out-of-`param_count` slots are pinned to ZERO and absorbed anyway | a missing value is a proven zero, never an ambiguity |
//! | the nonlinearity | `kcontrib = coeff * val_a * val_b` (degree 3) | the product of two state values — the thing `AffineLe`/`AffineEq` cannot express |
//! | fuel | every loop is over a SHAPE bound | a composition is priceable from the shape alone |
//!
//! # What the AIR does NOT do (the honest boundary)
//!
//! It does not prove `new_commit8` contains the outcome. `[old8 ‖ new8]` ride the door's
//! ABI and the EXECUTOR welds them to the cell's roots
//! (`custom_state_binding` tooth 1); binding `outcome_commitment` INTO the cell's new
//! state needs a cell-state-layout-aware weld, which is app-specific and would defeat this
//! crate's genericity. The general form of that weld — an executor-enforced atom
//! requiring the new state to carry the sub-proof's published outcome commitment — is the
//! named residual (see the crate doc).

use dregg_circuit::dsl::circuit::ColumnKind;
use dregg_circuit::field::BabyBear;

use crate::builder::{Builder, Head, fb};
use crate::digest::{
    ABSORB_RATE, DIGEST_FELTS, DOMAIN_EXPLANATION, DOMAIN_OUTCOME, DOMAIN_RULESET, DOMAIN_SUBJECTS,
    iv8,
};
use crate::model::{ComposeError, Composition, Subject};
use crate::reference::compose_over;
use crate::shape::ComposeShape;
use crate::shape::PARAM_COMPOSE_ABI_VERSION;

/// Deliberate deviations from the honest build, for the non-vacuity tests. Each removes a
/// HOST-side check or claims a value the law does not license, so what refuses the result
/// is the AIR and nothing else.
#[derive(Clone, Debug, Default)]
pub struct Forgery {
    /// Lay the subjects into slots in EXACTLY this order — no canonicalization, no
    /// duplicate check. The host tooth is removed so the IN-CIRCUIT ordering tooth is
    /// what is under test (a swap or a duplicate must have no satisfying witness).
    pub raw_subject_order: Option<Vec<Subject>>,
    /// Claim this outcome instead of the one the ruleset licenses. Everything else in the
    /// witness stays self-consistent (the commitment chain honestly commits the CLAIM), so
    /// the only constraint that can refuse it is the composition law itself.
    pub claimed_outcome: Option<i128>,
    /// **THE KNOT CANARY.** Pin every knot contribution to ZERO instead of
    /// `coeff * val_a * val_b`, i.e. delete the nonlinearity. Compositions that differ
    /// only in their products then stop differing — which is what makes the knot terms
    /// demonstrably load-bearing rather than decorative.
    pub neuter_knots: bool,
}

/// The AIR's column handles, for tests that need to name a column.
pub struct ComposeAir {
    pub builder: Builder,
    pub shape: ComposeShape,
    /// The outcome column (pinned to the sum of contributions by THE LAW).
    pub outcome_col: usize,
    /// Per-slot subject identity columns.
    pub identity_cols: Vec<usize>,
    /// Per-slot knot contribution columns.
    pub knot_contrib_cols: Vec<usize>,
    /// The `ruleset_root` columns, in PI order.
    pub ruleset_root_cols: Vec<usize>,
    /// The `subjects_root` columns, in PI order.
    pub subjects_root_cols: Vec<usize>,
}

/// A summary shape (the `Builder` holds a whole descriptor; printing it in a test failure
/// would bury the message).
impl core::fmt::Debug for ComposeAir {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("ComposeAir")
            .field("shape", &self.shape)
            .field("trace_width", &self.builder.width())
            .field("constraints", &self.builder.constraint_count())
            .field("hash_sites", &self.builder.hash_site_count())
            .field("public_inputs", &self.builder.pis.len())
            .field("accepts", &self.builder.air_accepts())
            .finish()
    }
}

/// Build the honest AIR + witness for `comp` at `shape`, riding the door's
/// `[old8 ‖ new8]` state prefix.
pub fn build(
    shape: &ComposeShape,
    comp: &Composition,
    old8: &[BabyBear; 8],
    new8: &[BabyBear; 8],
) -> Result<ComposeAir, ComposeError> {
    build_forged(shape, comp, old8, new8, &Forgery::default())
}

/// The `cap_node8` Merkle-Damgård chain of `crate::digest`, over witnessed columns.
/// In-circuit twin of [`crate::digest::wide_digest`].
///
/// Seed an 8-felt accumulator with the domain IV, then absorb `data_cols` 8 felts at a
/// time via `acc8 := cap_node8(acc8, block8)` — ONE `MerkleHash8` (arity-16 `node8`) site
/// per block, all 8 output lanes program-owned. Returns the 8 columns of the final
/// accumulator (the root), which the caller PI-binds.
fn wide_chain(
    b: &mut Builder,
    tag: &str,
    domain: u64,
    data_cols: &[usize],
    zero_col: usize,
) -> Vec<usize> {
    let iv = iv8(domain);
    // The 8-felt seed accumulator, each lane pinned to its domain-separated IV.
    let mut acc: [usize; DIGEST_FELTS] = core::array::from_fn(|lane| {
        let c = b.alloc_f(format!("{tag}_iv{lane}"), ColumnKind::Value, iv[lane]);
        b.assert_const(c, iv[lane]);
        c
    });
    for (bi, block) in data_cols.chunks(ABSORB_RATE).enumerate() {
        // The 8-felt data block, zero-padded past the stream end (the shared zero column).
        let mut right = [zero_col; DIGEST_FELTS];
        for (i, &c) in block.iter().enumerate() {
            right[i] = c;
        }
        // out8 = cap_node8(acc8, block8) — 8 fresh program-owned digest columns.
        let out_vals = b.cap_node8_value(acc, right);
        let out: [usize; DIGEST_FELTS] = core::array::from_fn(|lane| {
            b.alloc_f(
                format!("{tag}_h{bi}_l{lane}"),
                ColumnKind::Value,
                out_vals[lane],
            )
        });
        b.push_merkle_hash8(out, acc, right);
        acc = out;
    }
    acc.to_vec()
}

/// A boolean prefix indicator vector of `n` slots whose sum is pinned to `count_col`.
/// Prefix-monotone (`f[i+1] => f[i]`), so "active" is a PREFIX and the canonical padding
/// is unambiguous.
fn prefix_flags(
    b: &mut Builder,
    tag: &str,
    n: usize,
    active: usize,
    count_col: usize,
) -> Vec<usize> {
    let mut flags = Vec::with_capacity(n);
    for i in 0..n {
        let c = b.alloc(
            format!("{tag}{i}"),
            ColumnKind::Binary,
            (i < active) as i128,
        );
        b.assert_binary(c);
        flags.push(c);
    }
    // f[i+1] * (1 - f[i]) == 0
    for i in 0..n.saturating_sub(1) {
        b.assert_zero(&Head::lin(1, flags[i + 1]).add_prod(-1, vec![flags[i + 1], flags[i]]));
    }
    // Σ f == count
    let mut h = Head::lin(-1, count_col);
    for &c in &flags {
        h = h.add_lin(1, c);
    }
    b.assert_zero(&h);
    flags
}

/// Resolve `(role, param)` to a value, IN-CIRCUIT.
///
/// Two gated one-hots: one over subject slots pinned by ROLE (never by slot index — slot
/// order is an identity-sort artifact the ruleset author cannot predict), one over param
/// slots pinned by index. The read is `Σ_j Σ_p sel_j * selp_p * param[j][p]` — degree 3.
///
/// Refusals that ride here: a role no ACTIVE subject occupies (`Σ sel_j*active_j` cannot
/// reach 1), and a param slot at or past `param_count` (`Σ selp_p*pactive_p` cannot).
#[allow(clippy::too_many_arguments)]
fn fetch(
    b: &mut Builder,
    tag: &str,
    shape: &ComposeShape,
    sactive: &[usize],
    srole: &[usize],
    sparams: &[Vec<usize>],
    pactive: &[usize],
    term_active_col: usize,
    term_active: bool,
    role_col: usize,
    param_col: usize,
    subj_idx: Option<usize>,
    param_idx: usize,
) -> usize {
    // --- one-hot over subject slots, pinned by ROLE ---
    let mut sel = Vec::with_capacity(shape.max_subjects);
    for j in 0..shape.max_subjects {
        let v = (term_active && subj_idx == Some(j)) as i128;
        let c = b.alloc(format!("{tag}_ss{j}"), ColumnKind::Binary, v);
        b.assert_binary(c);
        sel.push(c);
    }
    // Σ sel == term_active
    let mut h = Head::lin(-1, term_active_col);
    for &c in &sel {
        h = h.add_lin(1, c);
    }
    b.assert_zero(&h);
    // Σ sel_j * role_j == term_active * role_col   (resolution BY ROLE)
    let mut h = Head::zero().add_prod(-1, vec![term_active_col, role_col]);
    for (j, &c) in sel.iter().enumerate() {
        h = h.add_prod(1, vec![c, srole[j]]);
    }
    b.assert_zero(&h);
    // Σ sel_j * sactive_j == term_active   (the selected subject must be ACTIVE)
    let mut h = Head::lin(-1, term_active_col);
    for (j, &c) in sel.iter().enumerate() {
        h = h.add_prod(1, vec![c, sactive[j]]);
    }
    b.assert_zero(&h);

    // --- one-hot over param slots, pinned by index ---
    let mut selp = Vec::with_capacity(shape.max_params);
    for p in 0..shape.max_params {
        let v = (term_active && p == param_idx) as i128;
        let c = b.alloc(format!("{tag}_sp{p}"), ColumnKind::Binary, v);
        b.assert_binary(c);
        selp.push(c);
    }
    // Σ selp == term_active
    let mut h = Head::lin(-1, term_active_col);
    for &c in &selp {
        h = h.add_lin(1, c);
    }
    b.assert_zero(&h);
    // Σ p * selp_p == term_active * param_col
    let mut h = Head::zero().add_prod(-1, vec![term_active_col, param_col]);
    for (p, &c) in selp.iter().enumerate() {
        h = h.add_lin(p as i128, c);
    }
    b.assert_zero(&h);
    // Σ selp_p * pactive_p == term_active   (the param must be within param_count)
    let mut h = Head::lin(-1, term_active_col);
    for (p, &c) in selp.iter().enumerate() {
        h = h.add_prod(1, vec![c, pactive[p]]);
    }
    b.assert_zero(&h);

    // --- the read: Σ_j Σ_p sel_j * selp_p * param[j][p]  (degree 3) ---
    let mut val = BabyBear::ZERO;
    let mut read = Head::zero();
    for j in 0..shape.max_subjects {
        for p in 0..shape.max_params {
            read = read.add_prod(1, vec![sel[j], selp[p], sparams[j][p]]);
            val += b.value(sel[j]) * b.value(selp[p]) * b.value(sparams[j][p]);
        }
    }
    b.alloc_head(&format!("{tag}_val"), &read, val)
}

/// Build the AIR + witness, with deliberate deviations. See [`Forgery`].
pub fn build_forged(
    shape: &ComposeShape,
    comp: &Composition,
    old8: &[BabyBear; 8],
    new8: &[BabyBear; 8],
    f: &Forgery,
) -> Result<ComposeAir, ComposeError> {
    comp.check_shape(shape)?;
    let canonical = match &f.raw_subject_order {
        Some(v) => v.clone(),
        None => comp.canonical_subjects()?,
    };
    let composed = compose_over(&canonical, &comp.ruleset, comp.param_count, f.neuter_knots)?;

    let ComposeShape {
        max_subjects: n,
        max_params: p_max,
        max_linear: l_max,
        max_knots: k_max,
        identity_bits,
    } = *shape;
    // A shape whose identity width defeats the ordering comparison's non-vacuity is
    // refused rather than built: it would produce a circuit that LOOKS ordered and
    // canonically-deduplicated while the comparison bit went free.
    if !shape.identity_bits_sound() {
        return Err(ComposeError::ExceedsShape(
            "identity_bits (ordering comparison would be VACUOUS)",
        ));
    }

    let mut b = Builder::new(format!(
        "param-compose-v{PARAM_COMPOSE_ABI_VERSION}-n{n}p{p_max}l{l_max}k{k_max}w{DIGEST_FELTS}i{identity_bits}"
    ));

    // The shared zero column: the canonical absent value, and the absorb padding.
    let zero = b.alloc("zero", ColumnKind::Value, 0);
    b.assert_const(zero, BabyBear::ZERO);

    // ---- the committed shape/version scalars ----
    let abi_col = b.alloc(
        "abi_version",
        ColumnKind::Value,
        PARAM_COMPOSE_ABI_VERSION as i128,
    );
    b.assert_const(abi_col, fb(PARAM_COMPOSE_ABI_VERSION as i128));
    let subject_count = b.alloc("subject_count", ColumnKind::Value, canonical.len() as i128);
    let param_count = b.alloc("param_count", ColumnKind::Value, comp.param_count as i128);
    let linear_count = b.alloc(
        "linear_count",
        ColumnKind::Value,
        comp.ruleset.linear.len() as i128,
    );
    let knot_count = b.alloc(
        "knot_count",
        ColumnKind::Value,
        comp.ruleset.knots.len() as i128,
    );

    // ---- param activity: the schema width, as a prefix ----
    let pactive = prefix_flags(&mut b, "pactive", p_max, comp.param_count, param_count);

    // ---- the subjects ----
    let mut sactive = Vec::with_capacity(n);
    let mut sident = Vec::with_capacity(n);
    let mut srole = Vec::with_capacity(n);
    let mut sparams: Vec<Vec<usize>> = Vec::with_capacity(n);
    for i in 0..n {
        let s = canonical.get(i);
        let ac = b.alloc(
            format!("s{i}_active"),
            ColumnKind::Binary,
            s.is_some() as i128,
        );
        b.assert_binary(ac);

        let id_val = s.map(|x| x.identity as i128).unwrap_or(0);
        let id = b.alloc(format!("s{i}_id"), ColumnKind::Value, id_val);
        // identity < 2^IDENTITY_BITS — the precondition that keeps the ordering
        // comparison below NON-VACUOUS (see `Builder::forced_ge0`).
        b.range_nonneg(
            &format!("s{i}_idr"),
            &Head::lin(1, id),
            id_val,
            identity_bits,
        );
        // inactive => identity 0
        b.assert_zero(&Head::lin(1, id).add_prod(-1, vec![ac, id]));

        let role_val = s.map(|x| x.role as i128).unwrap_or(0);
        let role = b.alloc(format!("s{i}_role"), ColumnKind::Value, role_val);
        // inactive => role 0 (the canonical absent tag)
        b.assert_zero(&Head::lin(1, role).add_prod(-1, vec![ac, role]));
        // active => role != 0, so tag 0 unambiguously means "no subject"
        b.cond_nonzero(&format!("s{i}_rnz"), ac, role);

        let mut ps = Vec::with_capacity(p_max);
        for (p, &pa) in pactive.iter().enumerate() {
            let v = match s {
                Some(x) if p < comp.param_count => x.params.get(p).copied().unwrap_or(0) as i128,
                _ => 0,
            };
            let c = b.alloc(format!("s{i}_p{p}"), ColumnKind::Value, v);
            // a slot at/past param_count is ZERO — absence is proven, then committed
            b.assert_zero(&Head::lin(1, c).add_prod(-1, vec![pa, c]));
            // an inactive subject projects nothing
            b.assert_zero(&Head::lin(1, c).add_prod(-1, vec![ac, c]));
            ps.push(c);
        }

        sactive.push(ac);
        sident.push(id);
        srole.push(role);
        sparams.push(ps);
    }

    // active is a PREFIX, and its weight is the committed count
    for i in 0..n.saturating_sub(1) {
        b.assert_zero(&Head::lin(1, sactive[i + 1]).add_prod(-1, vec![sactive[i + 1], sactive[i]]));
    }
    let mut h = Head::lin(-1, subject_count);
    for &c in &sactive {
        h = h.add_lin(1, c);
    }
    b.assert_zero(&h);

    // **CANONICAL ORDER + DUPLICATE REJECTION**: identity STRICTLY increases across
    // active slots. Strictness is what rejects a duplicate; monotonicity is what makes
    // `subjects_root` a function of the SET rather than of the host's chosen order.
    for i in 0..n.saturating_sub(1) {
        let d = Head::lin(1, sident[i + 1])
            .add_lin(-1, sident[i])
            .add_const(-1);
        let d_val = b.value(sident[i + 1]).0 as i128 - b.value(sident[i]).0 as i128 - 1;
        let ge = b.forced_ge0(&format!("ord{i}"), &d, d_val, shape.identity_cmp_bits());
        // active[i+1] => ge   (an inactive tail is exempt: its identity is 0)
        b.assert_zero(&Head::lin(1, sactive[i + 1]).add_prod(-1, vec![sactive[i + 1], ge]));
    }

    // **A ROLE IS A KEY**: pairwise distinct among active subjects, so `role -> subject`
    // is a FUNCTION and the prover cannot choose which subject a rule term reads.
    for i in 0..n {
        for j in (i + 1)..n {
            let both = b.alloc_prod(&format!("act{i}_{j}"), sactive[i], sactive[j]);
            let diff_val = b.value(srole[i]) - b.value(srole[j]);
            let diff = b.alloc_head(
                &format!("rdiff{i}_{j}"),
                &Head::lin(1, srole[i]).add_lin(-1, srole[j]),
                diff_val,
            );
            b.cond_nonzero(&format!("runiq{i}_{j}"), both, diff);
        }
    }

    // ---- the ruleset (witnessed; bound to ruleset_root below) ----
    let rid = b.alloc("ruleset_id", ColumnKind::Value, comp.ruleset.id as i128);
    let rver = b.alloc(
        "ruleset_version",
        ColumnKind::Value,
        comp.ruleset.version as i128,
    );

    let lactive = prefix_flags(
        &mut b,
        "lactive",
        l_max,
        comp.ruleset.linear.len(),
        linear_count,
    );
    let mut lin_cols = Vec::with_capacity(l_max);
    let mut lin_contrib = Vec::with_capacity(l_max);
    for (t, &ac) in lactive.iter().enumerate() {
        let term = comp.ruleset.linear.get(t);
        let role = b.alloc(
            format!("l{t}_role"),
            ColumnKind::Value,
            term.map(|x| x.role as i128).unwrap_or(0),
        );
        let par = b.alloc(
            format!("l{t}_param"),
            ColumnKind::Value,
            term.map(|x| x.param as i128).unwrap_or(0),
        );
        let coeff = b.alloc(
            format!("l{t}_coeff"),
            ColumnKind::Value,
            term.map(|x| x.coeff as i128).unwrap_or(0),
        );
        // an inactive slot is canonically all-zero, so the padded stream is unambiguous
        for c in [role, par, coeff] {
            b.assert_zero(&Head::lin(1, c).add_prod(-1, vec![ac, c]));
        }

        let subj_idx = match term {
            Some(x) => Some(resolve_idx(&canonical, x.role)?),
            None => None,
        };
        let val = fetch(
            &mut b,
            &format!("lf{t}"),
            shape,
            &sactive,
            &srole,
            &sparams,
            &pactive,
            ac,
            term.is_some(),
            role,
            par,
            subj_idx,
            term.map(|x| x.param).unwrap_or(0),
        );
        // contribution = coeff * value (an inactive slot has coeff 0, hence contributes 0)
        let contrib = b.alloc_prod(&format!("l{t}_contrib"), coeff, val);
        lin_cols.push([ac, role, par, coeff]);
        lin_contrib.push(contrib);
    }

    let kactive = prefix_flags(
        &mut b,
        "kactive",
        k_max,
        comp.ruleset.knots.len(),
        knot_count,
    );
    let mut knot_cols = Vec::with_capacity(k_max);
    let mut knot_contrib = Vec::with_capacity(k_max);
    for (t, &ac) in kactive.iter().enumerate() {
        let kn = comp.ruleset.knots.get(t);
        let role_a = b.alloc(
            format!("k{t}_role_a"),
            ColumnKind::Value,
            kn.map(|x| x.role_a as i128).unwrap_or(0),
        );
        let par_a = b.alloc(
            format!("k{t}_param_a"),
            ColumnKind::Value,
            kn.map(|x| x.param_a as i128).unwrap_or(0),
        );
        let role_b = b.alloc(
            format!("k{t}_role_b"),
            ColumnKind::Value,
            kn.map(|x| x.role_b as i128).unwrap_or(0),
        );
        let par_b = b.alloc(
            format!("k{t}_param_b"),
            ColumnKind::Value,
            kn.map(|x| x.param_b as i128).unwrap_or(0),
        );
        let coeff = b.alloc(
            format!("k{t}_coeff"),
            ColumnKind::Value,
            kn.map(|x| x.coeff as i128).unwrap_or(0),
        );
        for c in [role_a, par_a, role_b, par_b, coeff] {
            b.assert_zero(&Head::lin(1, c).add_prod(-1, vec![ac, c]));
        }

        let (ia, ib) = match kn {
            Some(x) => (
                Some(resolve_idx(&canonical, x.role_a)?),
                Some(resolve_idx(&canonical, x.role_b)?),
            ),
            None => (None, None),
        };
        let va = fetch(
            &mut b,
            &format!("ka{t}"),
            shape,
            &sactive,
            &srole,
            &sparams,
            &pactive,
            ac,
            kn.is_some(),
            role_a,
            par_a,
            ia,
            kn.map(|x| x.param_a).unwrap_or(0),
        );
        let vb = fetch(
            &mut b,
            &format!("kb{t}"),
            shape,
            &sactive,
            &srole,
            &sparams,
            &pactive,
            ac,
            kn.is_some(),
            role_b,
            par_b,
            ib,
            kn.map(|x| x.param_b).unwrap_or(0),
        );

        // **THE KNOT** — `coeff * val_a * val_b`, degree 3. The product of two subjects'
        // state values: precisely what the LINEAR StateConstraint vocabulary cannot say,
        // and the reason this Custom VK exists.
        let contrib_val = if f.neuter_knots {
            BabyBear::ZERO
        } else {
            b.value(coeff) * b.value(va) * b.value(vb)
        };
        let contrib = b.alloc_f(format!("k{t}_contrib"), ColumnKind::Value, contrib_val);
        if f.neuter_knots {
            // THE CANARY: the nonlinearity deleted.
            b.assert_const(contrib, BabyBear::ZERO);
        } else {
            b.assert_zero(&Head::lin(1, contrib).add_prod(-1, vec![coeff, va, vb]));
        }
        knot_cols.push([ac, role_a, par_a, role_b, par_b, coeff]);
        knot_contrib.push(contrib);
    }

    // ---- THE LAW: outcome == Σ linear contributions + Σ knot contributions ----
    let outcome_val = fb(f.claimed_outcome.unwrap_or(composed.outcome));
    let outcome_col = b.alloc_f("outcome", ColumnKind::Value, outcome_val);
    let mut h = Head::lin(1, outcome_col);
    for &c in lin_contrib.iter().chain(knot_contrib.iter()) {
        h = h.add_lin(-1, c);
    }
    b.assert_zero(&h);

    // ---- the roots. Stream order is pinned to `crate::reference`'s host twins. ----
    let mut subj_stream = vec![subject_count, param_count];
    for i in 0..n {
        subj_stream.push(sactive[i]);
        subj_stream.push(sident[i]);
        subj_stream.push(srole[i]);
        subj_stream.extend_from_slice(&sparams[i]);
    }
    let subjects_root_cols = wide_chain(&mut b, "subjroot", DOMAIN_SUBJECTS, &subj_stream, zero);

    let mut rule_stream = vec![rid, rver, linear_count, knot_count];
    for c in &lin_cols {
        rule_stream.extend_from_slice(c);
    }
    for c in &knot_cols {
        rule_stream.extend_from_slice(c);
    }
    let ruleset_root_cols = wide_chain(&mut b, "ruleroot", DOMAIN_RULESET, &rule_stream, zero);

    let outcome_root_cols = wide_chain(&mut b, "outroot", DOMAIN_OUTCOME, &[outcome_col], zero);

    let mut expl_stream = lin_contrib.clone();
    expl_stream.extend_from_slice(&knot_contrib);
    let expl_root_cols = wide_chain(&mut b, "explroot", DOMAIN_EXPLANATION, &expl_stream, zero);

    // ---- the public inputs, in `crate::pi` layout order ----
    for x in old8.iter().chain(new8.iter()) {
        b.add_pi(*x);
    }
    b.bind_pi(abi_col);
    b.bind_pi(subject_count);
    b.bind_pi(param_count);
    b.bind_pi(linear_count);
    b.bind_pi(knot_count);
    for c in ruleset_root_cols
        .iter()
        .chain(subjects_root_cols.iter())
        .chain(outcome_root_cols.iter())
        .chain(expl_root_cols.iter())
    {
        b.bind_pi(*c);
    }

    Ok(ComposeAir {
        builder: b,
        shape: *shape,
        outcome_col,
        identity_cols: sident,
        knot_contrib_cols: knot_contrib,
        ruleset_root_cols,
        subjects_root_cols,
    })
}

fn resolve_idx(canonical: &[Subject], role: u64) -> Result<usize, ComposeError> {
    canonical
        .iter()
        .position(|s| s.role == role)
        .ok_or(ComposeError::UnresolvedRole(role))
}
