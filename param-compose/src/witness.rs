//! **THE WITNESS PRODUCER for the LEAN-AUTHORED parameter-composition AIR.**
//!
//! The constraints live in Lean (`metatheory/Dregg2/Circuit/Emit/ParamComposeEmit.lean`); this
//! module authors NONE of them. It fills the column layout that file's §2 declares, from the same
//! host-side composition data the reference oracle ([`crate::reference`]) evaluates, so
//! [`dregg_circuit::descriptor_ir2::prove_vm_descriptor2`] can prove the Lean-emitted descriptor.
//!
//! ## What a witness producer is, and what it is not
//!
//! It is a TRACE FILL: for every column the emitted descriptor declares, the value an honest
//! composition puts there. It does not decide acceptance, it does not evaluate a constraint, and it
//! carries no `air_accepts` twin — the judge is the emitted object plus the deployed prover. A
//! producer that fills a column wrongly does not weaken the AIR; it produces an UNSATISFYING
//! witness and the leaf fails to prove.
//!
//! Two things keep the layout honest rather than merely parallel:
//!
//!   * [`ComposeLayout::width`] must equal the emitted descriptor's `trace_width`; and
//!   * [`ComposeLayout::root_cols`] must equal the columns the descriptor's own `PiBinding`
//!     constraints name.
//!
//! [`check_layout_against_descriptor`] asserts BOTH against the decoded Lean golden, so a layout
//! that drifts from the emitted object is caught structurally rather than by a proof that mysteriously
//! stops closing.
//!
//! ## The layout (mirrors `ParamComposeEmit.lean` §2 — that file is the source of truth)
//!
//! ```text
//!   0            abi_version
//!   1..5         subject_count, param_count, linear_count, knot_count
//!   5..5+p       param-activity prefix flags
//!   subj_base    per subject i (stride 4 + p + ib):
//!                  active, id, role, params[p], id-range bits[ib], role-inverse
//!   ord_base     per adjacent pair i (stride 2 + ib): ge bit, cmp range bits[ib+1]
//!   ru_base      per subject pair (i<j) (stride 3): both, diff, inverse
//!   rs_base      ruleset id, ruleset version
//!   la_base      linear-term activity flags[l]
//!   lin_base     per linear term (stride 4 + fetch_w): role, param, coeff, FETCH, contrib
//!   ka_base      knot activity flags[k]
//!   knot_base    per knot (stride 6 + 2·fetch_w): role_a, par_a, role_b, par_b, coeff,
//!                  FETCH_A, FETCH_B, contrib
//!   out_col      the outcome
//!   dig_base     the four `cap_node8` chains' 8-felt block outputs, in stream order
//! ```
//!
//! A FETCH block at base `fb` is `sel[n] ‖ selp[p] ‖ value` (width `n + p + 1`).
//!
//! Two columns the hand-written Rust AIR carried are ABSENT here because Lean replaced them with
//! literal constants in the chip tuple: the shared `zero` padding column and the four 8-felt domain
//! IV groups (33 columns at every shape). A constant cannot be tampered.
//!
//! ## The chip lanes are NOT this module's job
//!
//! Each digest block is one wide `node8` chip lookup whose 8 output lanes are program-owned. This
//! producer fills the DIGEST columns (the chain outputs). The prover's `trace_with_chip_lanes`
//! derives the exposed permutation lanes; a producer never needs per-site lane knowledge.

use dregg_circuit::cap_root::cap_node8;
use dregg_circuit::descriptor_ir2::{EffectVmDescriptor2, VmConstraint2};
use dregg_circuit::field::BabyBear;
use dregg_circuit::lean_descriptor_air::VmConstraint;

use crate::digest::{
    ABSORB_RATE, DIGEST_FELTS, DOMAIN_EXPLANATION, DOMAIN_OUTCOME, DOMAIN_RULESET, DOMAIN_SUBJECTS,
    iv8,
};
use crate::field::fb;
use crate::model::{ComposeError, Composition, Subject};
use crate::pi;
use crate::reference::compose_over;
use crate::shape::{ComposeShape, PARAM_COMPOSE_ABI_VERSION};

/// Column: the committed ABI version (`ParamComposeEmit.C_ABI`).
pub const C_ABI: usize = 0;
/// Column: the active subject count.
pub const C_NSUBJ: usize = 1;
/// Column: the active param width.
pub const C_NPARAM: usize = 2;
/// Column: the active linear-term count.
pub const C_NLIN: usize = 3;
/// Column: the active knot count.
pub const C_NKNOT: usize = 4;
/// Base of the param-activity prefix flags (`ComposeShape.paBase`).
pub const PA_BASE: usize = 5;

/// The four digest chains, in the order `ParamComposeEmit` emits them.
pub const CHAIN_SUBJECTS: usize = 0;
/// Chain index of the ruleset stream.
pub const CHAIN_RULESET: usize = 1;
/// Chain index of the outcome stream.
pub const CHAIN_OUTCOME: usize = 2;
/// Chain index of the explanation stream.
pub const CHAIN_EXPLANATION: usize = 3;

/// `⌈len / ABSORB_RATE⌉`, at least one (`ParamComposeEmit.blocksOf`).
fn blocks_of(len: usize) -> usize {
    len.div_ceil(ABSORB_RATE).max(1)
}

/// **The column layout of the Lean-authored AIR at one shape.** Every offset is
/// `ParamComposeEmit.lean` §2, transcribed as arithmetic on the shape — no allocation order, so a
/// decoder and this producer agree by construction.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ComposeLayout {
    /// The shape this layout is for.
    pub shape: ComposeShape,
    /// Per-subject stride (`4 + p + ib`).
    pub subj_w: usize,
    /// Base of the subject block (`5 + p`).
    pub subj_base: usize,
    /// Base of the ordering-comparison block.
    pub ord_base: usize,
    /// Per-comparison stride (`2 + ib`).
    pub ord_w: usize,
    /// Base of the role-key pair block.
    pub ru_base: usize,
    /// Base of the ruleset scalars.
    pub rs_base: usize,
    /// Base of the linear-term activity flags.
    pub la_base: usize,
    /// A fetch block's width (`n + p + 1`).
    pub fet_w: usize,
    /// Per-linear-term stride (`4 + fet_w`).
    pub lin_w: usize,
    /// Base of the linear-term block.
    pub lin_base: usize,
    /// Base of the knot activity flags.
    pub ka_base: usize,
    /// Per-knot stride (`6 + 2·fet_w`).
    pub knot_w: usize,
    /// Base of the knot block.
    pub knot_base: usize,
    /// The outcome column.
    pub out_col: usize,
    /// Base of the digest-chain output columns.
    pub dig_base: usize,
    /// `node8` block counts, per chain (subjects, ruleset, outcome, explanation).
    pub blocks: [usize; 4],
    /// The main-trace width.
    pub width: usize,
}

impl ComposeLayout {
    /// The layout of `shape`.
    pub fn new(shape: &ComposeShape) -> Self {
        let ComposeShape {
            max_subjects: n,
            max_params: p,
            max_linear: l,
            max_knots: k,
            identity_bits: ib,
        } = *shape;

        let subj_w = 4 + p + ib;
        let subj_base = PA_BASE + p;
        let ord_base = subj_base + n * subj_w;
        let ord_w = 2 + ib;
        let ru_base = ord_base + n.saturating_sub(1) * ord_w;
        let pairs = n * n.saturating_sub(1) / 2;
        let rs_base = ru_base + 3 * pairs;
        let la_base = rs_base + 2;
        let fet_w = n + p + 1;
        let lin_w = 4 + fet_w;
        let lin_base = la_base + l;
        let ka_base = lin_base + l * lin_w;
        let knot_w = 6 + 2 * fet_w;
        let knot_base = ka_base + k;
        let out_col = knot_base + k * knot_w;
        let dig_base = out_col + 1;
        let blocks = [
            blocks_of(shape.subjects_stream_len()),
            blocks_of(shape.ruleset_stream_len()),
            blocks_of(1),
            blocks_of(shape.explanation_stream_len()),
        ];
        let width = dig_base + DIGEST_FELTS * blocks.iter().sum::<usize>();

        ComposeLayout {
            shape: *shape,
            subj_w,
            subj_base,
            ord_base,
            ord_w,
            ru_base,
            rs_base,
            la_base,
            fet_w,
            lin_w,
            lin_base,
            ka_base,
            knot_w,
            knot_base,
            out_col,
            dig_base,
            blocks,
            width,
        }
    }

    /// The `q`-th param-activity flag.
    pub fn pa_col(&self, q: usize) -> usize {
        PA_BASE + q
    }
    /// Base of subject slot `i`.
    pub fn s_base(&self, i: usize) -> usize {
        self.subj_base + i * self.subj_w
    }
    /// Subject `i`'s activity flag.
    pub fn s_active(&self, i: usize) -> usize {
        self.s_base(i)
    }
    /// Subject `i`'s identity.
    pub fn s_id(&self, i: usize) -> usize {
        self.s_base(i) + 1
    }
    /// Subject `i`'s role tag.
    pub fn s_role(&self, i: usize) -> usize {
        self.s_base(i) + 2
    }
    /// Subject `i`'s param slot `q`.
    pub fn s_param(&self, i: usize, q: usize) -> usize {
        self.s_base(i) + 3 + q
    }
    /// Base of subject `i`'s identity range bits (`ib` of them).
    pub fn s_id_bits(&self, i: usize) -> usize {
        self.s_base(i) + 3 + self.shape.max_params
    }
    /// Subject `i`'s role-nonzero witnessed inverse.
    pub fn s_role_inv(&self, i: usize) -> usize {
        self.s_base(i) + 3 + self.shape.max_params + self.shape.identity_bits
    }
    /// The `i`-th ordering comparison's `[d ≥ 0]` bit.
    pub fn o_ge(&self, i: usize) -> usize {
        self.ord_base + i * self.ord_w
    }
    /// Base of the `i`-th ordering comparison's range bits (`ib + 1` of them).
    pub fn o_bits(&self, i: usize) -> usize {
        self.ord_base + i * self.ord_w + 1
    }
    /// The ordered list of distinct subject-slot pairs `(i, j)` with `i < j`.
    pub fn pair_list(&self) -> Vec<(usize, usize)> {
        let n = self.shape.max_subjects;
        (0..n)
            .flat_map(|i| ((i + 1)..n).map(move |j| (i, j)))
            .collect()
    }
    /// The `t`-th pair's `active_i · active_j` column.
    pub fn ru_both(&self, t: usize) -> usize {
        self.ru_base + 3 * t
    }
    /// The `t`-th pair's `role_i − role_j` column.
    pub fn ru_diff(&self, t: usize) -> usize {
        self.ru_base + 3 * t + 1
    }
    /// The `t`-th pair's witnessed inverse.
    pub fn ru_inv(&self, t: usize) -> usize {
        self.ru_base + 3 * t + 2
    }
    /// The ruleset catalog id.
    pub fn c_rid(&self) -> usize {
        self.rs_base
    }
    /// The ruleset version.
    pub fn c_rver(&self) -> usize {
        self.rs_base + 1
    }
    /// The `t`-th linear term's activity flag.
    pub fn la_col(&self, t: usize) -> usize {
        self.la_base + t
    }
    /// Base of linear term `t`.
    pub fn l_base(&self, t: usize) -> usize {
        self.lin_base + t * self.lin_w
    }
    /// Linear term `t`'s addressed role.
    pub fn l_role(&self, t: usize) -> usize {
        self.l_base(t)
    }
    /// Linear term `t`'s addressed param slot.
    pub fn l_param(&self, t: usize) -> usize {
        self.l_base(t) + 1
    }
    /// Linear term `t`'s coefficient.
    pub fn l_coeff(&self, t: usize) -> usize {
        self.l_base(t) + 2
    }
    /// Base of linear term `t`'s fetch block.
    pub fn l_fet(&self, t: usize) -> usize {
        self.l_base(t) + 3
    }
    /// Linear term `t`'s contribution.
    pub fn l_contrib(&self, t: usize) -> usize {
        self.l_base(t) + 3 + self.fet_w
    }
    /// The `t`-th knot's activity flag.
    pub fn ka_col(&self, t: usize) -> usize {
        self.ka_base + t
    }
    /// Base of knot `t`.
    pub fn k_base(&self, t: usize) -> usize {
        self.knot_base + t * self.knot_w
    }
    /// Knot `t`'s left role.
    pub fn k_role_a(&self, t: usize) -> usize {
        self.k_base(t)
    }
    /// Knot `t`'s left param slot.
    pub fn k_par_a(&self, t: usize) -> usize {
        self.k_base(t) + 1
    }
    /// Knot `t`'s right role.
    pub fn k_role_b(&self, t: usize) -> usize {
        self.k_base(t) + 2
    }
    /// Knot `t`'s right param slot.
    pub fn k_par_b(&self, t: usize) -> usize {
        self.k_base(t) + 3
    }
    /// Knot `t`'s coefficient.
    pub fn k_coeff(&self, t: usize) -> usize {
        self.k_base(t) + 4
    }
    /// Base of knot `t`'s LEFT fetch block.
    pub fn k_fet_a(&self, t: usize) -> usize {
        self.k_base(t) + 5
    }
    /// Base of knot `t`'s RIGHT fetch block.
    pub fn k_fet_b(&self, t: usize) -> usize {
        self.k_base(t) + 5 + self.fet_w
    }
    /// Knot `t`'s contribution — THE NONLINEARITY.
    pub fn k_contrib(&self, t: usize) -> usize {
        self.k_base(t) + 5 + 2 * self.fet_w
    }
    /// A fetch block's subject selector `j`.
    pub fn f_sel(&self, fetch_base: usize, j: usize) -> usize {
        fetch_base + j
    }
    /// A fetch block's param selector `q`.
    pub fn f_selp(&self, fetch_base: usize, q: usize) -> usize {
        fetch_base + self.shape.max_subjects + q
    }
    /// A fetch block's read value.
    pub fn f_val(&self, fetch_base: usize) -> usize {
        fetch_base + self.shape.max_subjects + self.shape.max_params
    }
    /// Block-column base of chain `c`.
    fn chain_off(&self, c: usize) -> usize {
        match c {
            0 => 0,
            1 => self.blocks[0],
            2 => self.blocks[0] + self.blocks[1],
            _ => self.blocks[0] + self.blocks[1] + self.blocks[2],
        }
    }
    /// The first of the 8 output columns of chain `c`'s block `b`.
    pub fn chain_cols(&self, c: usize, b: usize) -> usize {
        self.dig_base + DIGEST_FELTS * (self.chain_off(c) + b)
    }
    /// The first of the 8 ROOT columns of chain `c` (its last block's output).
    pub fn root_cols(&self, c: usize) -> usize {
        self.chain_cols(c, self.blocks[c] - 1)
    }
}

/// **A produced witness**: the single logical trace row of the Lean-authored AIR, plus the public
/// inputs in `crate::pi` layout order.
#[derive(Clone, Debug)]
pub struct ComposeWitness {
    /// The column layout the row is laid into.
    pub layout: ComposeLayout,
    /// The main-trace row (`layout.width` columns). Chip LANE columns do not exist here — the wide
    /// `node8` lanes are program-owned digest columns, filled by [`ComposeWitness::fill_chains`].
    pub row: Vec<BabyBear>,
    /// The public inputs `[old8 ‖ new8 ‖ abi ‖ counts ‖ ruleset ‖ subjects ‖ outcome ‖ explanation]`.
    pub pis: Vec<BabyBear>,
}

impl ComposeWitness {
    /// The base trace `prove_vm_descriptor2` consumes: the row repeated to `num_rows` (a power of
    /// two). Every emitted constraint is row-local, so a repeated row satisfies the descriptor on
    /// every row and the PI bindings on the first.
    pub fn base_trace(&self, num_rows: usize) -> Vec<Vec<BabyBear>> {
        vec![self.row.clone(); num_rows]
    }

    /// The 8 felts of chain `c`'s root, read back off the row.
    pub fn root(&self, c: usize) -> Vec<BabyBear> {
        let base = self.layout.root_cols(c);
        self.row[base..base + DIGEST_FELTS].to_vec()
    }

    /// Recompute all four `cap_node8` Merkle–Damgård chains from the row's current stream columns.
    /// Idempotent on an untouched row; after a deliberate column edit it re-commits to the edited
    /// value, so a "consistent" forgery still has to face the composition law.
    pub fn fill_chains(&mut self) {
        let (subj, rule, out, expl) = self.streams();
        self.chain(CHAIN_SUBJECTS, DOMAIN_SUBJECTS, &subj);
        self.chain(CHAIN_RULESET, DOMAIN_RULESET, &rule);
        self.chain(CHAIN_OUTCOME, DOMAIN_OUTCOME, &out);
        self.chain(CHAIN_EXPLANATION, DOMAIN_EXPLANATION, &expl);
    }

    /// Refill the public inputs from the row (the four roots and the four counts), keeping the
    /// door's `[old8 ‖ new8]` prefix.
    pub fn fill_pis(&mut self) {
        self.pis[pi::ABI_VERSION] = self.row[C_ABI];
        self.pis[pi::SUBJECT_COUNT] = self.row[C_NSUBJ];
        self.pis[pi::PARAM_COUNT] = self.row[C_NPARAM];
        self.pis[pi::LINEAR_COUNT] = self.row[C_NLIN];
        self.pis[pi::KNOT_COUNT] = self.row[C_NKNOT];
        for (chain, base) in [
            (CHAIN_RULESET, pi::ruleset_root_base()),
            (CHAIN_SUBJECTS, pi::subjects_root_base()),
            (CHAIN_OUTCOME, pi::outcome_commitment_base()),
            (CHAIN_EXPLANATION, pi::explanation_root_base()),
        ] {
            let cols = self.layout.root_cols(chain);
            for t in 0..DIGEST_FELTS {
                self.pis[base + t] = self.row[cols + t];
            }
        }
    }

    /// The four canonical streams, as column index lists (`ParamComposeEmit` §11 — the same felt
    /// order as `crate::reference`'s host twins).
    fn streams(&self) -> (Vec<usize>, Vec<usize>, Vec<usize>, Vec<usize>) {
        let l = &self.layout;
        let s = &l.shape;
        let mut subj = vec![C_NSUBJ, C_NPARAM];
        for i in 0..s.max_subjects {
            subj.push(l.s_active(i));
            subj.push(l.s_id(i));
            subj.push(l.s_role(i));
            for q in 0..s.max_params {
                subj.push(l.s_param(i, q));
            }
        }
        let mut rule = vec![l.c_rid(), l.c_rver(), C_NLIN, C_NKNOT];
        for t in 0..s.max_linear {
            rule.extend_from_slice(&[l.la_col(t), l.l_role(t), l.l_param(t), l.l_coeff(t)]);
        }
        for t in 0..s.max_knots {
            rule.extend_from_slice(&[
                l.ka_col(t),
                l.k_role_a(t),
                l.k_par_a(t),
                l.k_role_b(t),
                l.k_par_b(t),
                l.k_coeff(t),
            ]);
        }
        let out = vec![l.out_col];
        let mut expl: Vec<usize> = (0..s.max_linear).map(|t| l.l_contrib(t)).collect();
        expl.extend((0..s.max_knots).map(|t| l.k_contrib(t)));
        (subj, rule, out, expl)
    }

    /// One `cap_node8` chain: seed with the domain IV, absorb the stream 8 columns at a time
    /// (the final block zero-padded with LITERAL zeros, exactly as the emitted tuple's `.const 0`).
    fn chain(&mut self, c: usize, domain: u64, stream: &[usize]) {
        let mut acc = iv8(domain);
        for b in 0..self.layout.blocks[c] {
            let mut right = [BabyBear::ZERO; DIGEST_FELTS];
            for (t, slot) in right.iter_mut().enumerate() {
                if let Some(&col) = stream.get(b * ABSORB_RATE + t) {
                    *slot = self.row[col];
                }
            }
            let outv = cap_node8(acc, right);
            let base = self.layout.chain_cols(c, b);
            self.row[base..base + DIGEST_FELTS].copy_from_slice(&outv);
            acc = outv;
        }
    }
}

/// A subject's param at `slot`, applying the canonical-default rule (a slot the subject did not
/// supply reads ZERO).
fn param_of(s: &Subject, slot: usize) -> i64 {
    s.params.get(slot).copied().unwrap_or(0)
}

/// Resolve a role to its canonical subject index. Fail-closed: a role no subject occupies makes the
/// composition unprovable (the in-circuit twin is `Σ sel_j · active_j == term_active`).
fn resolve_idx(canonical: &[Subject], role: u64) -> Result<usize, ComposeError> {
    canonical
        .iter()
        .position(|s| s.role == role)
        .ok_or(ComposeError::UnresolvedRole(role))
}

/// Fill `bits` boolean columns starting at `base` with the little-endian bits of `value`, which
/// must already lie in `[0, 2^bits)`.
fn fill_bits(row: &mut [BabyBear], base: usize, bits: usize, value: u128) {
    for t in 0..bits {
        row[base + t] = BabyBear::new(((value >> t) & 1) as u32);
    }
}

/// **THE WITNESS PRODUCER.** Fill the Lean column layout for `comp` at `shape`, riding the Custom-VK
/// door's `[old8 ‖ new8]` state prefix.
///
/// Errors are the HOST-side well-formedness refusals of [`crate::model::ComposeError`] — a shape
/// overflow, an unresolved role, a param past `param_count`, an out-of-range identity. Each has an
/// in-circuit twin that makes the same shape UNSATISFIABLE, so a producer that (say) laid a
/// duplicate identity into the row would emit a row the emitted ordering gate refuses rather than a
/// proof of a false statement.
pub fn compose_witness(
    shape: &ComposeShape,
    comp: &Composition,
    old8: &[BabyBear; 8],
    new8: &[BabyBear; 8],
) -> Result<ComposeWitness, ComposeError> {
    compose_witness_over(shape, comp, &comp.canonical_subjects()?, old8, new8)
}

/// [`compose_witness`] over an EXPLICITLY GIVEN subject slot order, with no canonicalization and no
/// host-side duplicate check.
///
/// This exists so a falsifier can hand the producer an unsorted or identity-duplicated list and
/// watch the EMITTED ordering gate refuse it — the tooth is in the descriptor, not in this function.
/// Production callers use [`compose_witness`].
pub fn compose_witness_over(
    shape: &ComposeShape,
    comp: &Composition,
    slots: &[Subject],
    old8: &[BabyBear; 8],
    new8: &[BabyBear; 8],
) -> Result<ComposeWitness, ComposeError> {
    comp.check_shape(shape)?;
    if !shape.identity_bits_sound() {
        return Err(ComposeError::ExceedsShape(
            "identity_bits (ordering comparison would be VACUOUS)",
        ));
    }
    if slots.len() > shape.max_subjects {
        return Err(ComposeError::ExceedsShape("max_subjects"));
    }
    let composed = compose_over(slots, &comp.ruleset, comp.param_count, false)?;

    let layout = ComposeLayout::new(shape);
    let ComposeShape {
        max_subjects: n,
        max_params: p,
        max_linear: l,
        max_knots: k,
        identity_bits: ib,
    } = *shape;
    let mut row = vec![BabyBear::ZERO; layout.width];

    // ---- the committed shape/version scalars ----
    row[C_ABI] = fb(PARAM_COMPOSE_ABI_VERSION as i128);
    row[C_NSUBJ] = fb(slots.len() as i128);
    row[C_NPARAM] = fb(comp.param_count as i128);
    row[C_NLIN] = fb(comp.ruleset.linear.len() as i128);
    row[C_NKNOT] = fb(comp.ruleset.knots.len() as i128);

    // ---- param activity: the schema width, as a prefix ----
    for q in 0..p {
        row[layout.pa_col(q)] = fb((q < comp.param_count) as i128);
    }

    // ---- the subjects ----
    for i in 0..n {
        let s = slots.get(i);
        row[layout.s_active(i)] = fb(s.is_some() as i128);
        let id = s.map(|x| x.identity).unwrap_or(0);
        row[layout.s_id(i)] = fb(id as i128);
        fill_bits(&mut row, layout.s_id_bits(i), ib, id as u128);
        let role = s.map(|x| x.role).unwrap_or(0);
        row[layout.s_role(i)] = fb(role as i128);
        // active ⇒ role ≠ 0: the witnessed inverse of the role tag.
        row[layout.s_role_inv(i)] = match s {
            Some(_) => fb(role as i128).inverse().unwrap_or(BabyBear::ZERO),
            None => BabyBear::ZERO,
        };
        for q in 0..p {
            let v = match s {
                Some(x) if q < comp.param_count => param_of(x, q),
                _ => 0,
            };
            row[layout.s_param(i, q)] = fb(v as i128);
        }
    }

    // ---- canonical order: identity STRICTLY increases across active slots ----
    for i in 0..n.saturating_sub(1) {
        let d = row[layout.s_id(i + 1)].0 as i128 - row[layout.s_id(i)].0 as i128 - 1;
        let ge = d >= 0;
        row[layout.o_ge(i)] = fb(ge as i128);
        let term = if ge { d } else { -d - 1 };
        // The comparison term lands in `[0, 2^(ib+1))` for every in-range identity pair; an
        // out-of-range one has NO satisfying bit assignment, which is the ordering tooth.
        let canon = {
            let p_mod = dregg_circuit::field::BABYBEAR_P as i128;
            (((term % p_mod) + p_mod) % p_mod) as u128
        };
        fill_bits(&mut row, layout.o_bits(i), shape.identity_cmp_bits(), canon);
    }

    // ---- a role is a KEY: pairwise distinct among active subjects ----
    for (t, (i, j)) in layout.pair_list().into_iter().enumerate() {
        let both = row[layout.s_active(i)] * row[layout.s_active(j)];
        let diff = row[layout.s_role(i)] - row[layout.s_role(j)];
        row[layout.ru_both(t)] = both;
        row[layout.ru_diff(t)] = diff;
        row[layout.ru_inv(t)] = if both != BabyBear::ZERO {
            diff.inverse().unwrap_or(BabyBear::ZERO)
        } else {
            BabyBear::ZERO
        };
    }

    // ---- the ruleset (witnessed; bound to `ruleset_root` by the emitted chain) ----
    row[layout.c_rid()] = fb(comp.ruleset.id as i128);
    row[layout.c_rver()] = fb(comp.ruleset.version as i128);

    for t in 0..l {
        let term = comp.ruleset.linear.get(t);
        row[layout.la_col(t)] = fb(term.is_some() as i128);
        row[layout.l_role(t)] = fb(term.map(|x| x.role as i128).unwrap_or(0));
        row[layout.l_param(t)] = fb(term.map(|x| x.param as i128).unwrap_or(0));
        row[layout.l_coeff(t)] = fb(term.map(|x| x.coeff as i128).unwrap_or(0));
        let subj_idx = match term {
            Some(x) => Some(resolve_idx(slots, x.role)?),
            None => None,
        };
        let val = fill_fetch(
            &mut row,
            &layout,
            layout.l_fet(t),
            subj_idx,
            term.map(|x| x.param).unwrap_or(0),
            term.is_some(),
        );
        let coeff = row[layout.l_coeff(t)];
        row[layout.l_contrib(t)] = coeff * val;
    }

    for t in 0..k {
        let kn = comp.ruleset.knots.get(t);
        row[layout.ka_col(t)] = fb(kn.is_some() as i128);
        row[layout.k_role_a(t)] = fb(kn.map(|x| x.role_a as i128).unwrap_or(0));
        row[layout.k_par_a(t)] = fb(kn.map(|x| x.param_a as i128).unwrap_or(0));
        row[layout.k_role_b(t)] = fb(kn.map(|x| x.role_b as i128).unwrap_or(0));
        row[layout.k_par_b(t)] = fb(kn.map(|x| x.param_b as i128).unwrap_or(0));
        row[layout.k_coeff(t)] = fb(kn.map(|x| x.coeff as i128).unwrap_or(0));
        let (ia, ib_idx) = match kn {
            Some(x) => (
                Some(resolve_idx(slots, x.role_a)?),
                Some(resolve_idx(slots, x.role_b)?),
            ),
            None => (None, None),
        };
        let va = fill_fetch(
            &mut row,
            &layout,
            layout.k_fet_a(t),
            ia,
            kn.map(|x| x.param_a).unwrap_or(0),
            kn.is_some(),
        );
        let vb = fill_fetch(
            &mut row,
            &layout,
            layout.k_fet_b(t),
            ib_idx,
            kn.map(|x| x.param_b).unwrap_or(0),
            kn.is_some(),
        );
        // THE KNOT — `coeff · va · vb`, the degree-3 product of two subjects' state values.
        let kcoeff = row[layout.k_coeff(t)];
        row[layout.k_contrib(t)] = kcoeff * va * vb;
    }

    // ---- THE LAW's left-hand side ----
    row[layout.out_col] = fb(composed.outcome);

    let mut w = ComposeWitness {
        layout,
        row,
        pis: vec![BabyBear::ZERO; pi::public_input_count()],
    };
    w.fill_chains();
    w.pis[..8].copy_from_slice(old8);
    w.pis[8..16].copy_from_slice(new8);
    w.fill_pis();
    Ok(w)
}

/// Fill one fetch block (`sel[n] ‖ selp[p] ‖ value`) and return the read value.
fn fill_fetch(
    row: &mut [BabyBear],
    layout: &ComposeLayout,
    fetch_base: usize,
    subj_idx: Option<usize>,
    param_idx: usize,
    active: bool,
) -> BabyBear {
    for j in 0..layout.shape.max_subjects {
        row[layout.f_sel(fetch_base, j)] = fb((active && subj_idx == Some(j)) as i128);
    }
    for q in 0..layout.shape.max_params {
        row[layout.f_selp(fetch_base, q)] = fb((active && q == param_idx) as i128);
    }
    // The emitted read is `Σ_j Σ_q sel_j · selp_q · param[j][q]` (degree 3); with the one-hots
    // above that is exactly the addressed slot, and ZERO when the term is inactive.
    let mut val = BabyBear::ZERO;
    for j in 0..layout.shape.max_subjects {
        for q in 0..layout.shape.max_params {
            val += row[layout.f_sel(fetch_base, j)]
                * row[layout.f_selp(fetch_base, q)]
                * row[layout.s_param(j, q)];
        }
    }
    row[layout.f_val(fetch_base)] = val;
    val
}

/// **THE FAIL-CLOSED PRODUCER CANARY.** Judge a produced witness with the DEPLOYED IR-v2 row-local
/// evaluator (`Ir2Air::Main::eval`, the constraint evaluator the verifier runs) over the EMITTED
/// descriptor.
///
/// This is NOT an acceptance predicate this crate authored — it decides nothing itself, it asks the
/// emitted object. Its job is to catch a witness-generator fault BEFORE the trace is handed to the
/// prover, which is the one unproven step on this path. It is silent on the cross-table bus arms
/// (the `node8` chip lookups): the digest chain's own correctness is pinned by
/// [`ComposeWitness::root`] against `crate::reference`'s host twins, and by the batch prover.
pub fn compose_trace_accepts(desc: &EffectVmDescriptor2, w: &ComposeWitness) -> bool {
    // TWO rows: a single replicated row exercises only the first-row PI bindings.
    let rows: Vec<Vec<i64>> = w
        .base_trace(2)
        .iter()
        .map(|r| r.iter().map(|f| f.0 as i64).collect())
        .collect();
    let pis: Vec<i64> = w.pis.iter().map(|f| f.0 as i64).collect();
    dregg_circuit::descriptor_ir2::ir2_eval_accepts_i64(desc, &rows, &pis)
}

/// **THE STRUCTURAL TIE.** Check this producer's layout against the EMITTED descriptor: the width
/// must match, and the four root column groups must be exactly the columns the descriptor's own
/// `PiBinding` constraints bind to the root PI slots.
///
/// This is what keeps the layout from being a parallel invention: it is checked against the decoded
/// Lean object rather than against itself. Returns the list of disagreements (empty = agreement).
pub fn check_layout_against_descriptor(
    layout: &ComposeLayout,
    desc: &EffectVmDescriptor2,
) -> Vec<String> {
    let mut bad = Vec::new();
    if layout.width != desc.trace_width {
        bad.push(format!(
            "trace width: layout {} != emitted {}",
            layout.width, desc.trace_width
        ));
    }
    if desc.public_input_count != pi::public_input_count() {
        bad.push(format!(
            "PI count: layout {} != emitted {}",
            pi::public_input_count(),
            desc.public_input_count
        ));
    }
    // The emitted PI bindings, as `pi_index -> column`.
    let mut bound = std::collections::BTreeMap::new();
    for c in &desc.constraints {
        if let VmConstraint2::Base(VmConstraint::PiBinding { col, pi_index, .. }) = c {
            bound.insert(*pi_index, *col);
        }
    }
    let expect: [(usize, usize); 4] = [
        (CHAIN_RULESET, pi::ruleset_root_base()),
        (CHAIN_SUBJECTS, pi::subjects_root_base()),
        (CHAIN_OUTCOME, pi::outcome_commitment_base()),
        (CHAIN_EXPLANATION, pi::explanation_root_base()),
    ];
    for (chain, base) in expect {
        let cols = layout.root_cols(chain);
        for t in 0..DIGEST_FELTS {
            match bound.get(&(base + t)) {
                Some(&col) if col == cols + t => {}
                other => bad.push(format!(
                    "chain {chain} lane {t}: layout col {} != emitted {other:?} at PI {}",
                    cols + t,
                    base + t
                )),
            }
        }
    }
    for (col, idx) in [
        (C_ABI, pi::ABI_VERSION),
        (C_NSUBJ, pi::SUBJECT_COUNT),
        (C_NPARAM, pi::PARAM_COUNT),
        (C_NLIN, pi::LINEAR_COUNT),
        (C_NKNOT, pi::KNOT_COUNT),
    ] {
        match bound.get(&idx) {
            Some(&c) if c == col => {}
            other => bad.push(format!(
                "scalar PI {idx}: layout col {col} != emitted {other:?}"
            )),
        }
    }
    bad
}
