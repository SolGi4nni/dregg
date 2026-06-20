//! THE PREDICATE / CAVEAT COMPOSER (L2) — the "lamesauce language uplift".
//!
//! The protocol's predicate/caveat language — `dregg_cell`'s
//! [`StateConstraint`] slot-caveat algebra (50-odd atoms: sender bindings,
//! balance-delta rate gates, value allowlists, cross-slot relations, the
//! `AnyOfBound` anti-strip disjunction) — is the surface that makes real apps
//! enforce real invariants. Before this module that surface had NO inspector
//! and NO builder: an author hand-wrote `StateConstraint` literals and hoped.
//! This is L2 of the moldable inspector (`docs/deos/INSPECTOR-FRAMEWORK.md`
//! Part 3 §L2): it gives the predicate family legibility (the
//! [`Presentable`] face: `Source` prose · `Trace` evaluation · `RawFields`)
//! and constructibility (the [`PredicateComposer`] gadget: build a REAL
//! `StateConstraint` out of genuine atoms, validate it fail-closed against
//! anti-strip / cost / coordination safety, install it onto a cell as a real
//! [`CellProgram`], and fire a turn the VERIFIED executor enforces).
//!
//! Everything is pure data + the real machinery, proven by `cargo test`
//! exactly as `presentable.rs`/`simulate.rs` are. No gpui type crosses the
//! boundary. The discipline (the documented "toy disease" scar): we NEVER
//! reinvent a predicate evaluator — the gadget's `validate()`/`Trace`
//! presentation CALL the genuine [`CellProgram::evaluate`] the executor owns,
//! and the committing path rides `simulate.rs`'s `IntentDraft → simulate →
//! commit` spine so the value that lands is the one the executor checks.
//!
//! ## What it builds
//!
//! The composer assembles a [`StateConstraint`] from the post-uplift grammar:
//!   * **sender atoms** — `SenderIs` / `SenderMemberOf` (the multi-admin actor
//!     binding the polis council needs),
//!   * **context atoms** — `BalanceGte` / `BalanceLte` (own-balance floors/ceilings),
//!   * **balance-delta atoms** — `BalanceDeltaLte` / `BalanceDeltaGte` (the
//!     per-turn rate gates — the BOUNDED/ordering pole of §8),
//!   * **value atoms** — `FieldEquals` / `FieldGte` / `FieldLte` (static slot bounds),
//!   * **composite combinators** — `AnyOf` (a disjunction of simple atoms) and
//!     `AnyOfBound` (the witnessed/cheap disjunction with the anti-strip tooth).
//!
//! It then VALIDATES the composition (§ [`ComposerValidation`]):
//!   * **anti-strip** — an `AnyOfBound` whose cheap branch dominates a witnessed
//!     branch is the proof-strip forge §4 warns of; the validator refuses a
//!     composition that lets a stripped proof slide down to a free leg.
//!   * **non-vacuity** — an empty `AnyOf`/`AnyOfBound` is vacuously-false and a
//!     `MemberOf {}`-style empty value set is a dead caveat; refused.
//!   * **cost / coordination (§8)** — every atom carries a [`CostClass`]; a
//!     composition mixing a coordination-FREE intent with a BOUNDED (ordering-
//!     pole) atom is FLAGGED so the author sees the i-confluence cost they took.
//!
//! ## What enforces it
//!
//! [`PredicateComposer::install_and_fire`] (the [`CommittingGadget`] path):
//! installs the built constraint as a `CellProgram::Predicate([c])` on the
//! target cell via [`World::set_cell_program`] (the genesis-path authority
//! install the verified compositor already uses, `scene.rs`), then emits a
//! `SetField` turn through `simulate`/`commit`. A turn that VIOLATES the
//! installed caveat is REFUSED by the executor's program-check loop; a
//! satisfying one commits. This is the proof the composer yields a REAL
//! protocol value the verified executor enforces — never a mock.

use dregg_cell::program::{BoundBranch, SimpleStateConstraint};
use dregg_cell::{
    field_from_u64, CellId, CellProgram, CellState, EvalContext, ProgramError, StateConstraint,
};

use crate::reflect::{self, Field, Inspectable, ObjectKind};
use crate::presentable::{
    GadgetError, GadgetValidation, Presentable, PresentCtx, Presentation, PresentationBody,
    PresentationKind, TraceStep, TraceView,
};
use crate::simulate::{self, EffectKind, IntentDraft, SimOutcome};
use crate::world::{CommitOutcome, World};

// ===========================================================================
// §8 — the cost / coordination classifier (over the REAL atom set).
// ===========================================================================

/// The §8 cost / coordination class of a predicate atom — the i-confluence
/// pole the atom sits at. The protocol does not ship a runtime classifier (the
/// classification lives per-variant in `program.rs`'s rustdoc); this lifts that
/// documented property into a value the composer can reason over and SURFACE,
/// so an author building a caveat sees the coordination cost they incur.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CostClass {
    /// FREE / i-confluent: a predicate over the single turn's own context with
    /// no cross-turn invariant (sender bindings, static slot bounds, value
    /// allowlists). Composes without forcing ordering on the cell.
    Free,
    /// BOUNDED / ordering pole: a rate-bound on a decrementable quantity (the
    /// balance-delta gates). i-confluent only under the single serializer
    /// (n=1); n>1 forces every concurrent debit to order against this cell.
    Bounded,
}

impl CostClass {
    /// A short legend label (the §8 readout in the Invariant/Source face).
    pub fn label(&self) -> &'static str {
        match self {
            CostClass::Free => "FREE (i-confluent)",
            CostClass::Bounded => "BOUNDED (ordering pole; n=1 only)",
        }
    }
}

/// The §8 cost class of a [`SimpleStateConstraint`] atom, reading the documented
/// per-variant classification. Composite simples (`Not`/`AnyOf`-nested) take the
/// MOST-coordinating (worst) class of their parts — the conservative read.
fn simple_cost(c: &SimpleStateConstraint) -> CostClass {
    match c {
        // The balance-delta rate gates are the BOUNDED / ordering pole (a rate
        // bound on a decrementable quantity), per their `program.rs` rustdoc.
        SimpleStateConstraint::BalanceDeltaLte { .. }
        | SimpleStateConstraint::BalanceDeltaGte { .. } => CostClass::Bounded,
        // Negation takes its inner's class.
        SimpleStateConstraint::Not(inner) => simple_cost(inner),
        // Everything else (sender bindings, static field bounds, height gates,
        // own-balance absolute floors, value allowlists, …) is FREE.
        _ => CostClass::Free,
    }
}

/// The §8 cost class of a whole [`StateConstraint`]: the most-coordinating class
/// of any atom it contains.
pub fn constraint_cost(c: &StateConstraint) -> CostClass {
    let mut worst = CostClass::Free;
    fn bump(worst: &mut CostClass, c: CostClass) {
        if c == CostClass::Bounded {
            *worst = CostClass::Bounded;
        }
    }
    match c {
        StateConstraint::AnyOf { variants } => {
            for v in variants {
                bump(&mut worst, simple_cost(v));
            }
        }
        StateConstraint::AnyOfBound { branches } => {
            for b in branches {
                if let BoundBranch::Simple(s) = b {
                    bump(&mut worst, simple_cost(s));
                }
            }
        }
        // The balance-delta gates also exist as outer-enum-free; the rate gates
        // we surface live in `SimpleStateConstraint`, so a bare outer atom is
        // FREE unless it is one of the rate forms we model above.
        _ => {}
    }
    worst
}

// ===========================================================================
// §L2 — the composable atom palette (the post-uplift grammar, real atoms).
// ===========================================================================

/// One leaf atom the composer offers — a thin, legible wrapper over a genuine
/// [`SimpleStateConstraint`]. Every variant lowers to a REAL atom the executor
/// evaluates; this enum is only the builder's palette (so the gpui form renders
/// a fixed menu) — it adds NO semantics.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Atom {
    /// The turn's sender must equal `pk` (the literal actor binding).
    SenderIs { pk: [u8; 32] },
    /// The turn's sender must be one of `members` (the multi-admin board).
    SenderMemberOf { members: Vec<[u8; 32]> },
    /// The cell's own post-turn balance must be `>= min` (a solvency floor).
    BalanceGte { min: u64 },
    /// The cell's own post-turn balance must be `<= max` (a spend ceiling).
    BalanceLte { max: u64 },
    /// Per-turn balance change `<= max` (the BOUNDED rate gate; signed).
    BalanceDeltaLte { max: i64 },
    /// Per-turn balance change `>= min` (the BOUNDED rate gate; signed).
    BalanceDeltaGte { min: i64 },
    /// Slot `index` must equal the u64 `value` (a static value pin).
    FieldEquals { index: u8, value: u64 },
    /// Slot `index` must be `>= value` (a static floor).
    FieldGte { index: u8, value: u64 },
    /// Slot `index` must be `<= value` (a static ceiling).
    FieldLte { index: u8, value: u64 },
}

impl Atom {
    /// Lower to the genuine [`SimpleStateConstraint`] — the real protocol atom.
    pub fn lower(&self) -> SimpleStateConstraint {
        match self {
            Atom::SenderIs { pk } => SimpleStateConstraint::SenderIs { pk: *pk },
            Atom::SenderMemberOf { members } => SimpleStateConstraint::SenderMemberOf {
                members: members.clone(),
            },
            Atom::BalanceGte { min } => SimpleStateConstraint::BalanceGte { min: *min },
            Atom::BalanceLte { max } => SimpleStateConstraint::BalanceLte { max: *max },
            Atom::BalanceDeltaLte { max } => SimpleStateConstraint::BalanceDeltaLte { max: *max },
            Atom::BalanceDeltaGte { min } => SimpleStateConstraint::BalanceDeltaGte { min: *min },
            Atom::FieldEquals { index, value } => SimpleStateConstraint::FieldEquals {
                index: *index,
                value: field_from_u64(*value),
            },
            Atom::FieldGte { index, value } => SimpleStateConstraint::FieldGte {
                index: *index,
                value: field_from_u64(*value),
            },
            Atom::FieldLte { index, value } => SimpleStateConstraint::FieldLte {
                index: *index,
                value: field_from_u64(*value),
            },
        }
    }

    /// A one-line human "what-is" of the atom (the Source prose row).
    pub fn prose(&self) -> String {
        match self {
            Atom::SenderIs { pk } => {
                format!("the turn's sender must be {}", reflect::short_hex(pk))
            }
            Atom::SenderMemberOf { members } => format!(
                "the turn's sender must be one of {} listed members",
                members.len()
            ),
            Atom::BalanceGte { min } => format!("the cell's own balance must be ≥ {min}"),
            Atom::BalanceLte { max } => format!("the cell's own balance must be ≤ {max}"),
            Atom::BalanceDeltaLte { max } => {
                format!("the cell may change its balance by at most {max} this turn")
            }
            Atom::BalanceDeltaGte { min } => {
                format!("the cell must change its balance by at least {min} this turn")
            }
            Atom::FieldEquals { index, value } => format!("slot {index} must equal {value}"),
            Atom::FieldGte { index, value } => format!("slot {index} must be ≥ {value}"),
            Atom::FieldLte { index, value } => format!("slot {index} must be ≤ {value}"),
        }
    }

    /// The §8 cost class of this atom (delegates to the real classifier).
    pub fn cost(&self) -> CostClass {
        simple_cost(&self.lower())
    }
}

/// The composite the author is building — the recursive shape the form edits.
/// Lowers to a single [`StateConstraint`] the executor enforces.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Composite {
    /// A bare leaf atom (lowers to whichever outer/simple form fits).
    Leaf(Atom),
    /// A disjunction of simple atoms — `AnyOf` (`SLOT-CAVEATS-EVALUATION §4.3`:
    /// only simples nest here). At least one branch must hold.
    AnyOf(Vec<Atom>),
    /// The anti-strip disjunction (`§11.3` — the `AnyOfBound` rung). Each
    /// witnessed branch names its OWN proof carrier, so a stripped proof FAILS
    /// that branch and cannot masquerade as a no-proof branch.
    AnyOfBound(Vec<Branch>),
}

/// A branch of an [`Composite::AnyOfBound`] — the cheap (no-proof) leg or the
/// witnessed (proof-bearing, cross-cell-read) leg. Lowers to the genuine
/// [`BoundBranch`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Branch {
    /// The cheap, no-proof leg — a plain atom (a timeout, a sender binding).
    Simple(Atom),
    /// The proof-bearing leg — the cross-cell verified-observation read. Admits
    /// IFF the host `FinalizedRootAuthority` opens `source_field` on peer
    /// `source_cell` at `at_root` to a value that `new[local_field]` equals.
    /// Names its OWN proof blob (`proof_witness_index`) — the anti-strip tooth.
    Witnessed {
        local_field: u8,
        source_cell: [u8; 32],
        source_field: u8,
        at_root: [u8; 32],
        proof_witness_index: usize,
    },
}

impl Branch {
    fn lower(&self) -> BoundBranch {
        match self {
            Branch::Simple(a) => BoundBranch::Simple(a.lower()),
            Branch::Witnessed {
                local_field,
                source_cell,
                source_field,
                at_root,
                proof_witness_index,
            } => BoundBranch::Witnessed {
                local_field: *local_field,
                source_cell: *source_cell,
                source_field: *source_field,
                at_root: *at_root,
                proof_witness_index: *proof_witness_index,
            },
        }
    }

    fn is_witnessed(&self) -> bool {
        matches!(self, Branch::Witnessed { .. })
    }
}

impl Composite {
    /// Lower the whole composite to a single genuine [`StateConstraint`].
    pub fn lower(&self) -> StateConstraint {
        match self {
            Composite::Leaf(a) => match a {
                // The own-balance / static-field / sender atoms each have an
                // outer-enum form; we route the leaf through the outer enum
                // where it has a direct variant, else wrap a singleton `AnyOf`
                // (a one-branch disjunction is semantically the atom itself).
                Atom::FieldEquals { index, value } => StateConstraint::FieldEquals {
                    index: *index,
                    value: field_from_u64(*value),
                },
                Atom::FieldGte { index, value } => StateConstraint::FieldGte {
                    index: *index,
                    value: field_from_u64(*value),
                },
                Atom::FieldLte { index, value } => StateConstraint::FieldLte {
                    index: *index,
                    value: field_from_u64(*value),
                },
                // Sender + balance atoms live only in `SimpleStateConstraint`;
                // a singleton `AnyOf` is the canonical outer lift (the same
                // device `SimpleStateConstraint::implies` uses).
                other => StateConstraint::AnyOf {
                    variants: vec![other.lower()],
                },
            },
            Composite::AnyOf(atoms) => StateConstraint::AnyOf {
                variants: atoms.iter().map(Atom::lower).collect(),
            },
            Composite::AnyOfBound(branches) => StateConstraint::AnyOfBound {
                branches: branches.iter().map(Branch::lower).collect(),
            },
        }
    }
}

// ===========================================================================
// Validation — anti-strip / non-vacuity / cost-coordination (fail-closed).
// ===========================================================================

/// Why a composition is unsafe to install (the composer's fail-closed verdict).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ComposerRefusal {
    /// An empty disjunction (`AnyOf`/`AnyOfBound` with no branches) — vacuously
    /// false, a dead caveat that rejects every transition.
    EmptyDisjunction,
    /// An empty `SenderMemberOf` board — no sender can ever match (a vacuous
    /// actor binding).
    EmptyMemberSet,
    /// The anti-strip forge: an `AnyOfBound` carries a witnessed (proof-bearing)
    /// branch AND a cheap leg that is `Atom`-trivially-satisfiable (an
    /// unconditional pass), so a submitter would strip the proof and slide down
    /// the free leg — the §4 proof-strip unsoundness. Refused.
    StrippableProofBranch { detail: String },
}

impl ComposerRefusal {
    fn reason(&self) -> String {
        match self {
            ComposerRefusal::EmptyDisjunction => {
                "empty disjunction: a caveat with no branches is vacuously false".to_string()
            }
            ComposerRefusal::EmptyMemberSet => {
                "empty SenderMemberOf board: no sender can satisfy an empty member set".to_string()
            }
            ComposerRefusal::StrippableProofBranch { detail } => {
                format!("anti-strip: {detail}")
            }
        }
    }
}

/// The result of validating a [`Composite`] (the live fail-closed check + the
/// §8 cost readout). `Ok` means buildable; `Unsafe` means refuse to install.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ComposerValidation {
    /// Safe to install. Carries the §8 cost class of the whole composition so
    /// the author sees the coordination cost they took (a `Bounded` here means
    /// the caveat is i-confluent only under the single serializer).
    Ok { cost: CostClass },
    /// Refused — the composition is unsafe; `refusal` says why.
    Unsafe { refusal: ComposerRefusal },
}

impl ComposerValidation {
    /// `true` iff the composition is safe to install/build.
    pub fn is_ok(&self) -> bool {
        matches!(self, ComposerValidation::Ok { .. })
    }
    /// `true` iff the composition is fail-closed (will NOT install).
    pub fn is_fail_closed(&self) -> bool {
        matches!(self, ComposerValidation::Unsafe { .. })
    }
    /// Map to the L1 [`GadgetValidation`] shape (so the gadget form renders it).
    pub fn to_gadget(&self) -> GadgetValidation {
        match self {
            ComposerValidation::Ok { .. } => GadgetValidation::Ok,
            ComposerValidation::Unsafe { refusal } => GadgetValidation::Invalid {
                reason: refusal.reason(),
            },
        }
    }
}

/// Does an atom, on its own, satisfy EVERY transition (i.e. is it a trivial
/// no-op cheap leg)? The anti-strip check uses this: a witnessed branch sitting
/// beside an always-true cheap leg is the proof-strip forge. None of the real
/// atoms here are unconditionally-true (sender/balance/field atoms all gate
/// SOMETHING), so the only strippable shape is a `SenderMemberOf` with an empty
/// board treated as "anyone" — which we already refuse as `EmptyMemberSet`. We
/// nonetheless model the predicate explicitly so adding a future trivial atom
/// (e.g. a `True`/`Always`) is caught by construction rather than slipping
/// through. Returns the trivially-true-ness of the cheap leg.
fn atom_is_unconditional(_a: &Atom) -> bool {
    // No atom in the current palette is an unconditional pass.
    false
}

/// Validate a [`Composite`] — the anti-strip / non-vacuity / cost check.
pub fn validate(c: &Composite) -> ComposerValidation {
    // (1) non-vacuity + empty-member checks, recursively over atoms.
    fn check_atom(a: &Atom) -> Option<ComposerRefusal> {
        if let Atom::SenderMemberOf { members } = a {
            if members.is_empty() {
                return Some(ComposerRefusal::EmptyMemberSet);
            }
        }
        None
    }

    match c {
        Composite::Leaf(a) => {
            if let Some(r) = check_atom(a) {
                return ComposerValidation::Unsafe { refusal: r };
            }
        }
        Composite::AnyOf(atoms) => {
            if atoms.is_empty() {
                return ComposerValidation::Unsafe {
                    refusal: ComposerRefusal::EmptyDisjunction,
                };
            }
            for a in atoms {
                if let Some(r) = check_atom(a) {
                    return ComposerValidation::Unsafe { refusal: r };
                }
            }
        }
        Composite::AnyOfBound(branches) => {
            if branches.is_empty() {
                return ComposerValidation::Unsafe {
                    refusal: ComposerRefusal::EmptyDisjunction,
                };
            }
            let has_witnessed = branches.iter().any(Branch::is_witnessed);
            // (2) THE ANTI-STRIP TOOTH: a witnessed branch beside an
            // unconditional cheap leg lets a stripped proof slide to the free
            // leg. Refuse a composition where a witnessed branch coexists with a
            // trivially-true cheap branch.
            if has_witnessed {
                for b in branches {
                    if let Branch::Simple(a) = b {
                        if atom_is_unconditional(a) {
                            return ComposerValidation::Unsafe {
                                refusal: ComposerRefusal::StrippableProofBranch {
                                    detail: format!(
                                        "the cheap branch '{}' is unconditionally satisfiable, so a \
                                         submitter could strip the witnessed proof and slide down it",
                                        a.prose()
                                    ),
                                },
                            };
                        }
                        if let Some(r) = check_atom(a) {
                            return ComposerValidation::Unsafe { refusal: r };
                        }
                    }
                }
            } else {
                for b in branches {
                    if let Branch::Simple(a) = b {
                        if let Some(r) = check_atom(a) {
                            return ComposerValidation::Unsafe { refusal: r };
                        }
                    }
                }
            }
        }
    }

    ComposerValidation::Ok {
        cost: constraint_cost(&c.lower()),
    }
}

// ===========================================================================
// THE PRESENTABLE FACE — Source (prose) · Trace (eval) · RawFields.
// ===========================================================================

/// A thin newtype wrapping a built [`StateConstraint`] as a [`Presentable`] —
/// the predicate's legible faces. The constraint lives in the foreign
/// `dregg_cell` crate, so we present via this wrapper (the established
/// reflect-a-foreign-struct pattern). The `Trace` presentation evaluates the
/// constraint against a SAMPLE (`new`, `old`, `ctx`) via the genuine
/// [`CellProgram::evaluate`] — never a re-derived evaluator.
#[derive(Clone, Debug)]
pub struct ReflectedConstraint {
    /// The genuine constraint being presented.
    pub constraint: StateConstraint,
    /// An optional sample post-state to drive the Trace evaluation.
    pub sample_new: Option<CellState>,
    /// An optional sample pre-state (for transition atoms).
    pub sample_old: Option<CellState>,
    /// An optional sample eval context (sender / height) for the Trace.
    pub sample_ctx: Option<EvalContext>,
}

impl ReflectedConstraint {
    /// Wrap a constraint with no sample (Source + RawFields only).
    pub fn new(constraint: StateConstraint) -> Self {
        ReflectedConstraint {
            constraint,
            sample_new: None,
            sample_old: None,
            sample_ctx: None,
        }
    }

    /// Attach a sample evaluation so the Trace presentation fires the REAL
    /// evaluator against it.
    pub fn with_sample(
        mut self,
        new: CellState,
        old: Option<CellState>,
        ctx: Option<EvalContext>,
    ) -> Self {
        self.sample_new = Some(new);
        self.sample_old = old;
        self.sample_ctx = ctx;
        self
    }

    /// The Source "what-is" prose of the constraint — the human-readable
    /// statement of the invariant it enforces. Reads the constraint's genuine
    /// shape (it does NOT paraphrase a parallel model).
    pub fn source_prose(&self) -> String {
        constraint_prose(&self.constraint)
    }

    /// Evaluate the constraint against the attached sample via the REAL
    /// [`CellProgram::evaluate`], returning a step-by-step [`TraceView`] of the
    /// genuine accept/reject result. With no sample, a single explanatory step.
    pub fn trace(&self) -> TraceView {
        let Some(new) = &self.sample_new else {
            return TraceView {
                steps: vec![TraceStep {
                    index: 0,
                    label: "no sample state attached — Source only".to_string(),
                }],
            };
        };
        let program = CellProgram::Predicate(vec![self.constraint.clone()]);
        let result = program.evaluate(new, self.sample_old.as_ref(), self.sample_ctx.as_ref());
        let mut steps = vec![
            TraceStep {
                index: 0,
                label: format!("constraint: {}", constraint_prose(&self.constraint)),
            },
            TraceStep {
                index: 1,
                label: format!("sample balance = {}", new.balance()),
            },
        ];
        match &result {
            Ok(()) => steps.push(TraceStep {
                index: steps.len(),
                label: "→ ACCEPT (the executor would admit this transition)".to_string(),
            }),
            Err(e) => steps.push(TraceStep {
                index: steps.len(),
                label: format!("→ REJECT: {}", program_error_prose(e)),
            }),
        }
        TraceView { steps }
    }

    /// `true` iff the attached sample ACCEPTS under the real evaluator. Panics
    /// if no sample is attached (callers should attach one first).
    pub fn sample_accepts(&self) -> bool {
        let new = self
            .sample_new
            .as_ref()
            .expect("sample_accepts requires an attached sample");
        CellProgram::Predicate(vec![self.constraint.clone()])
            .evaluate(new, self.sample_old.as_ref(), self.sample_ctx.as_ref())
            .is_ok()
    }
}

impl Presentable for ReflectedConstraint {
    fn object_kind(&self) -> ObjectKind {
        ObjectKind::Cell
    }

    fn present(&self, _ctx: &PresentCtx) -> Vec<Presentation> {
        let mut out: Vec<Presentation> = Vec::new();

        // (1) RawFields — the MANDATORY floor: the constraint's structural shape.
        let insp = constraint_inspectable(&self.constraint);
        out.push(Presentation {
            kind: PresentationKind::RawFields,
            label: "Constraint".to_string(),
            search_text: PresentationBody::Fields(insp.clone()).search_text(),
            body: PresentationBody::Fields(insp),
        });

        // (2) Source — the human "what-is" prose of the invariant it enforces.
        let prose = self.source_prose();
        out.push(Presentation {
            kind: PresentationKind::Source,
            label: "What it enforces".to_string(),
            search_text: format!("source {prose}"),
            body: PresentationBody::Prose(prose),
        });

        // (3) Trace — the step-by-step evaluation against the sample, run
        //     through the GENUINE CellProgram::evaluate (never re-derived).
        let trace = self.trace();
        let trace_text = trace
            .steps
            .iter()
            .map(|s| s.label.as_str())
            .collect::<Vec<_>>()
            .join(" ");
        out.push(Presentation {
            // The step-by-step evaluation renders as a DomainVisual whose body
            // is the Trace payload (the seven KINDs are the lens taxonomy; the
            // Trace is a BODY a DomainVisual lens carries — cf. the census's
            // "Trace(eval)" rows under slice 3).
            kind: PresentationKind::DomainVisual,
            label: "Evaluation".to_string(),
            search_text: format!("trace {trace_text}"),
            body: PresentationBody::Trace(trace),
        });

        // (4) Invariant — the §8 cost / coordination readout.
        let cost = constraint_cost(&self.constraint);
        out.push(Presentation {
            kind: PresentationKind::Invariant,
            label: "Cost / coordination (§8)".to_string(),
            search_text: format!("invariant cost {}", cost.label()),
            body: PresentationBody::Prose(format!(
                "coordination class: {}\n\nA FREE atom is i-confluent (it composes without forcing \
                 ordering on the cell); a BOUNDED atom is a rate-bound on a decrementable quantity \
                 and is i-confluent only under the single serializer (n=1).",
                cost.label()
            )),
        });

        out
    }
}

/// Project a [`StateConstraint`] into a structural [`Inspectable`] (the
/// RawFields floor). Reuses the genuine `StateConstraintView::to_view` shape
/// where it helps, but presents the salient fields directly.
fn constraint_inspectable(c: &StateConstraint) -> Inspectable {
    let (title, fields): (String, Vec<Field>) = match c {
        StateConstraint::AnyOf { variants } => (
            "AnyOf (disjunction)".to_string(),
            vec![Field::text(
                "branches".to_string(),
                format!("{} simple atom(s); at least one must hold", variants.len()),
            )],
        ),
        StateConstraint::AnyOfBound { branches } => {
            let witnessed = branches.iter().filter(|b| matches!(b, BoundBranch::Witnessed { .. })).count();
            (
                "AnyOfBound (anti-strip disjunction)".to_string(),
                vec![
                    Field::text("branches".to_string(), format!("{} branch(es)", branches.len())),
                    Field::text(
                        "witnessed".to_string(),
                        format!("{witnessed} proof-bearing branch(es) (each names its own proof)"),
                    ),
                ],
            )
        }
        StateConstraint::FieldEquals { index, .. } => (
            "FieldEquals".to_string(),
            vec![Field::text("slot".to_string(), index.to_string())],
        ),
        StateConstraint::FieldGte { index, .. } => (
            "FieldGte".to_string(),
            vec![Field::text("slot".to_string(), index.to_string())],
        ),
        StateConstraint::FieldLte { index, .. } => (
            "FieldLte".to_string(),
            vec![Field::text("slot".to_string(), index.to_string())],
        ),
        other => (
            "StateConstraint".to_string(),
            vec![Field::text(
                "kind".to_string(),
                format!("{other:?}").chars().take(64).collect::<String>(),
            )],
        ),
    };
    Inspectable {
        kind: ObjectKind::Cell,
        title,
        subtitle: "slot caveat (the executor enforces it on every transition)".to_string(),
        fields,
    }
}

/// The human "what-is" prose of a whole [`StateConstraint`].
fn constraint_prose(c: &StateConstraint) -> String {
    match c {
        StateConstraint::AnyOf { variants } => {
            let parts: Vec<String> = variants.iter().map(simple_prose).collect();
            format!("at least one of: {}", parts.join("; OR "))
        }
        StateConstraint::AnyOfBound { branches } => {
            let parts: Vec<String> = branches
                .iter()
                .map(|b| match b {
                    BoundBranch::Simple(s) => simple_prose(s),
                    BoundBranch::Witnessed {
                        local_field,
                        source_field,
                        ..
                    } => format!(
                        "slot {local_field} equals peer's finalized field {source_field} \
                         (a proof-bearing cross-cell read)"
                    ),
                })
                .collect();
            format!("at least one branch holds (anti-strip): {}", parts.join("; OR "))
        }
        StateConstraint::FieldEquals { index, value } => {
            format!("slot {index} must equal {}", field_prose(value))
        }
        StateConstraint::FieldGte { index, value } => {
            format!("slot {index} must be ≥ {}", field_prose(value))
        }
        StateConstraint::FieldLte { index, value } => {
            format!("slot {index} must be ≤ {}", field_prose(value))
        }
        other => format!("{other:?}"),
    }
}

/// The human "what-is" prose of a [`SimpleStateConstraint`] atom.
fn simple_prose(s: &SimpleStateConstraint) -> String {
    match s {
        SimpleStateConstraint::SenderIs { pk } => {
            format!("the sender is {}", reflect::short_hex(pk))
        }
        SimpleStateConstraint::SenderMemberOf { members } => {
            format!("the sender is one of {} members", members.len())
        }
        SimpleStateConstraint::BalanceGte { min } => format!("own balance ≥ {min}"),
        SimpleStateConstraint::BalanceLte { max } => format!("own balance ≤ {max}"),
        SimpleStateConstraint::BalanceDeltaLte { max } => {
            format!("per-turn balance change ≤ {max}")
        }
        SimpleStateConstraint::BalanceDeltaGte { min } => {
            format!("per-turn balance change ≥ {min}")
        }
        SimpleStateConstraint::FieldEquals { index, value } => {
            format!("slot {index} equals {}", field_prose(value))
        }
        SimpleStateConstraint::FieldGte { index, value } => {
            format!("slot {index} ≥ {}", field_prose(value))
        }
        SimpleStateConstraint::FieldLte { index, value } => {
            format!("slot {index} ≤ {}", field_prose(value))
        }
        SimpleStateConstraint::Not(inner) => format!("NOT ({})", simple_prose(inner)),
        other => format!("{other:?}").chars().take(48).collect::<String>(),
    }
}

/// Render a [`dregg_cell::FieldElement`]'s low u64 (the big-endian-last-8 lane).
fn field_prose(f: &[u8; 32]) -> String {
    let mut be = [0u8; 8];
    be.copy_from_slice(&f[24..32]);
    u64::from_be_bytes(be).to_string()
}

/// A short prose of a [`ProgramError`] (the Trace reject row).
fn program_error_prose(e: &ProgramError) -> String {
    format!("{e:?}").chars().take(120).collect()
}

// ===========================================================================
// THE COMPOSER — a CommittingGadget: build → validate → install → fire.
// ===========================================================================

/// The composer's outcome of installing the built caveat and firing a turn.
#[derive(Clone, Debug)]
pub enum EnforcementOutcome {
    /// The turn COMMITTED — the installed caveat ADMITTED this transition.
    Committed { receipt_hash: [u8; 32] },
    /// The turn was REFUSED by the executor's program-check loop (the installed
    /// caveat enforced its invariant) — the reason the executor pinned.
    Refused { reason: String },
}

impl EnforcementOutcome {
    /// `true` iff the turn committed (the caveat admitted it).
    pub fn committed(&self) -> bool {
        matches!(self, EnforcementOutcome::Committed { .. })
    }
}

/// THE PREDICATE COMPOSER — builds a real [`StateConstraint`], installs it onto
/// a cell as a `CellProgram::Predicate([c])`, and fires a `SetField` turn the
/// VERIFIED executor enforces. The construction + install + fire is the full
/// L2 spine: it reuses [`World::set_cell_program`] (the genesis-path authority
/// install) + `simulate.rs`'s commit path, so the value that lands is the one
/// the executor checks.
///
/// `target` is the cell the caveat is installed on (and whose slot the fired
/// turn writes); `agent` is the principal authorizing the turn (the sender the
/// `SenderIs`/`SenderMemberOf` atoms gate on). For an own-cell caveat,
/// `agent == target`.
#[derive(Clone, Debug)]
pub struct PredicateComposer {
    /// The cell the caveat installs on / the turn targets.
    pub target: CellId,
    /// The principal authorizing the fired turn.
    pub agent: CellId,
    /// The composite the author is building.
    pub composite: Composite,
}

impl PredicateComposer {
    /// A fresh composer over `target` (caveat install + turn target) authorized
    /// by `agent`, seeded with `composite`.
    pub fn new(target: CellId, agent: CellId, composite: Composite) -> Self {
        PredicateComposer {
            target,
            agent,
            composite,
        }
    }

    /// The live fail-closed validation verdict (anti-strip / non-vacuity / §8).
    pub fn validate(&self) -> ComposerValidation {
        validate(&self.composite)
    }

    /// Materialize the genuine [`StateConstraint`] — fails closed if validation
    /// refuses (the unsafe composition never builds).
    pub fn build(&self) -> Result<StateConstraint, GadgetError> {
        match self.validate() {
            ComposerValidation::Ok { .. } => Ok(self.composite.lower()),
            ComposerValidation::Unsafe { refusal } => Err(GadgetError::Lowering {
                reason: refusal.reason(),
            }),
        }
    }

    /// The built constraint as a [`ReflectedConstraint`] for presentation, with
    /// the given sample attached so its Trace fires the real evaluator.
    pub fn reflected(
        &self,
        sample_new: CellState,
        sample_old: Option<CellState>,
        sample_ctx: Option<EvalContext>,
    ) -> Result<ReflectedConstraint, GadgetError> {
        let c = self.build()?;
        Ok(ReflectedConstraint::new(c).with_sample(sample_new, sample_old, sample_ctx))
    }

    /// Install the built caveat onto `target` as a `CellProgram::Predicate([c])`
    /// (the genesis-path authority install) and return whether the cell existed.
    /// Fails closed if the composition is unsafe (nothing is installed).
    pub fn install(&self, world: &mut World) -> Result<bool, GadgetError> {
        let c = self.build()?;
        Ok(world.set_cell_program(&self.target, CellProgram::Predicate(vec![c])))
    }

    /// Build the `SetField` [`IntentDraft`] that writes `value` into `slot` of
    /// `target` — the turn whose admission the installed caveat gates.
    pub fn write_draft(&self, slot: usize, value: u64) -> IntentDraft {
        let mut draft = IntentDraft::new(self.agent);
        let ai = draft.add_action(self.target);
        draft.add_effect(
            ai,
            EffectKind::SetField {
                index: slot,
                value: field_from_u64(value),
            },
        );
        draft
    }

    /// PREDICT the `SetField` turn against the live world (reuses
    /// `simulate::simulate`) — the caveat-gated verdict, one turn ahead, with
    /// the live world untouched.
    pub fn predict_write(&self, world: &World, slot: usize, value: u64) -> SimOutcome {
        simulate::simulate(world, &self.write_draft(slot, value))
    }

    /// INSTALL the caveat then FIRE a `SetField` turn for real, returning the
    /// executor's verdict. A turn that VIOLATES the installed caveat is REFUSED
    /// by the executor's program-check loop; a satisfying one commits. This is
    /// the proof the composer yields a REAL protocol value the verified executor
    /// enforces — never a mock.
    pub fn install_and_fire(
        &self,
        world: &mut World,
        slot: usize,
        value: u64,
    ) -> Result<EnforcementOutcome, GadgetError> {
        // The cell must exist for the caveat to install onto.
        if !self.install(world)? {
            return Err(GadgetError::Lowering {
                reason: format!(
                    "target cell {} is not in the ledger — cannot install a caveat onto it",
                    reflect::short_hex(self.target.as_bytes())
                ),
            });
        }
        let draft = self.write_draft(slot, value);
        Ok(match simulate::commit(world, &draft) {
            CommitOutcome::Committed { receipt, .. } => EnforcementOutcome::Committed {
                receipt_hash: receipt.receipt_hash(),
            },
            CommitOutcome::Rejected { reason, .. } => EnforcementOutcome::Refused { reason },
            // The world is suspended (meta-debug): the turn staged, not enforced.
            CommitOutcome::Queued { .. } => EnforcementOutcome::Refused {
                reason: "world suspended: turn queued, not committed".to_string(),
            },
        })
    }
}

// ===========================================================================
// TESTS — the model, proven gpui-free (exactly as presentable.rs's are).
// ===========================================================================

#[cfg(test)]
mod tests {
    use super::*;

    /// A one-cell world: an open cell (the controller) with a balance.
    fn one_cell_world() -> (World, CellId) {
        let mut w = World::new();
        let cell = w.genesis_cell(0x33, 1_000);
        (w, cell)
    }

    // ── the composer builds a REAL constraint out of genuine atoms ──────────

    #[test]
    fn the_composer_builds_a_real_state_constraint() {
        let (_w, cell) = one_cell_world();
        // A disjunction: the sender is the controller OR slot 0 equals 7.
        let composite = Composite::AnyOf(vec![
            Atom::SenderIs {
                pk: *cell.as_bytes(),
            },
            Atom::FieldEquals { index: 0, value: 7 },
        ]);
        let composer = PredicateComposer::new(cell, cell, composite);
        let built = composer.build().expect("a valid composition builds");
        // It is the GENUINE StateConstraint::AnyOf, with the real lowered atoms.
        match built {
            StateConstraint::AnyOf { variants } => {
                assert_eq!(variants.len(), 2);
                assert!(matches!(variants[0], SimpleStateConstraint::SenderIs { .. }));
                assert!(matches!(
                    variants[1],
                    SimpleStateConstraint::FieldEquals { index: 0, .. }
                ));
            }
            other => panic!("expected AnyOf, got {other:?}"),
        }
    }

    // ── validation catches an over-permissive / vacuous composition ─────────

    #[test]
    fn validation_fails_closed_on_vacuous_compositions() {
        let (_w, cell) = one_cell_world();

        // An empty disjunction is vacuously false — refused.
        let empty = PredicateComposer::new(cell, cell, Composite::AnyOf(vec![]));
        assert!(empty.validate().is_fail_closed());
        assert!(empty.build().is_err());

        // An empty SenderMemberOf board is a vacuous actor binding — refused.
        let empty_board = PredicateComposer::new(
            cell,
            cell,
            Composite::Leaf(Atom::SenderMemberOf { members: vec![] }),
        );
        assert!(matches!(
            empty_board.validate(),
            ComposerValidation::Unsafe {
                refusal: ComposerRefusal::EmptyMemberSet
            }
        ));
        assert!(empty_board.build().is_err());

        // An empty AnyOfBound (no branches) is also refused.
        let empty_bound = PredicateComposer::new(cell, cell, Composite::AnyOfBound(vec![]));
        assert!(empty_bound.validate().is_fail_closed());
    }

    // ── the §8 cost / coordination classifier surfaces the BOUNDED pole ─────

    #[test]
    fn the_cost_classifier_flags_the_bounded_ordering_pole() {
        let (_w, cell) = one_cell_world();
        // A FREE composition (sender + static field).
        let free = PredicateComposer::new(
            cell,
            cell,
            Composite::AnyOf(vec![
                Atom::SenderIs {
                    pk: *cell.as_bytes(),
                },
                Atom::FieldGte { index: 1, value: 5 },
            ]),
        );
        assert_eq!(
            free.validate(),
            ComposerValidation::Ok {
                cost: CostClass::Free
            }
        );

        // A composition carrying a balance-delta rate gate is BOUNDED.
        let bounded = PredicateComposer::new(
            cell,
            cell,
            Composite::AnyOf(vec![
                Atom::BalanceDeltaLte { max: 100 },
                Atom::SenderIs {
                    pk: *cell.as_bytes(),
                },
            ]),
        );
        assert_eq!(
            bounded.validate(),
            ComposerValidation::Ok {
                cost: CostClass::Bounded
            }
        );
    }

    // ── a built caveat, INSTALLED and FIRED, is ENFORCED by the executor ────

    #[test]
    fn a_built_caveat_is_enforced_by_the_real_executor() {
        // The caveat: slot 0 must be ≤ 100. A write of 50 satisfies it; a write
        // of 500 violates it. The executor's program-check loop is what refuses.
        let (mut w, cell) = one_cell_world();
        let composer = PredicateComposer::new(
            cell,
            cell,
            Composite::Leaf(Atom::FieldLte {
                index: 0,
                value: 100,
            }),
        );

        // A SATISFYING write (slot 0 := 50) commits.
        let ok = composer
            .install_and_fire(&mut w, 0, 50)
            .expect("a valid composition installs + fires");
        assert!(
            ok.committed(),
            "a write within the caveat bound commits: {ok:?}"
        );

        // A VIOLATING write (slot 0 := 500) is REFUSED by the executor — install
        // the caveat fresh on a second cell to fire the violating turn against it.
        let cell2 = w.genesis_cell(0x44, 1_000);
        let composer2 = PredicateComposer::new(
            cell2,
            cell2,
            Composite::Leaf(Atom::FieldLte {
                index: 0,
                value: 100,
            }),
        );
        let bad = composer2
            .install_and_fire(&mut w, 0, 500)
            .expect("install succeeds; the executor is what refuses the turn");
        assert!(
            !bad.committed(),
            "a write exceeding the caveat bound is REFUSED by the executor: {bad:?}"
        );
    }

    // ── predict (no commit) shows the caveat verdict one turn ahead ─────────

    #[test]
    fn predict_shows_the_caveat_verdict_without_committing() {
        let (mut w, cell) = one_cell_world();
        let composer = PredicateComposer::new(
            cell,
            cell,
            Composite::Leaf(Atom::FieldLte {
                index: 0,
                value: 100,
            }),
        );
        // Install the caveat (no turn yet).
        assert!(composer.install(&mut w).expect("installs"));

        // PREDICT a satisfying write → would commit; a violating write → refused.
        // The live world is never mutated by predict.
        let good = composer.predict_write(&w, 0, 50);
        assert!(good.would_commit(), "a satisfying write would commit");

        let bad = composer.predict_write(&w, 0, 500);
        assert!(
            !bad.would_commit(),
            "a violating write would be refused: {}",
            simulate::render_outcome(&bad)
        );
    }

    // ── the Source + Trace presentations reflect the REAL evaluation ────────

    #[test]
    fn the_source_and_trace_presentations_reflect_the_real_evaluation() {
        let (_w, cell) = one_cell_world();
        let composer = PredicateComposer::new(
            cell,
            cell,
            Composite::Leaf(Atom::FieldLte {
                index: 0,
                value: 100,
            }),
        );

        // A SATISFYING sample (slot 0 = 50) traces to ACCEPT.
        let mut new_ok = CellState::new(1_000);
        new_ok.set_field(0, field_from_u64(50));
        let refl_ok = composer
            .reflected(new_ok, None, None)
            .expect("valid composition reflects");
        assert!(
            refl_ok.sample_accepts(),
            "slot 0 = 50 satisfies slot 0 ≤ 100"
        );

        let ctx = PresentCtx::new(&_w, cell);
        let set = refl_ok.present(&ctx);
        // The Source face speaks the real invariant.
        let src = set
            .iter()
            .find(|p| p.kind == PresentationKind::Source)
            .expect("Source present");
        match &src.body {
            PresentationBody::Prose(p) => assert!(
                p.contains("slot 0") && p.contains("100"),
                "Source prose states the real bound: {p}"
            ),
            other => panic!("Source should be Prose, got {other:?}"),
        }
        // The Trace face evaluated the REAL constraint and accepted (found by
        // its Trace BODY — the step-by-step eval lens).
        let trace = set
            .iter()
            .find(|p| matches!(p.body, PresentationBody::Trace(_)))
            .expect("Trace present");
        match &trace.body {
            PresentationBody::Trace(t) => assert!(
                t.steps.iter().any(|s| s.label.contains("ACCEPT")),
                "the Trace reflects the real ACCEPT: {:?}",
                t.steps
            ),
            other => panic!("Trace should be Trace, got {other:?}"),
        }

        // A VIOLATING sample (slot 0 = 500) traces to REJECT — the SAME
        // evaluator the executor runs.
        let mut new_bad = CellState::new(1_000);
        new_bad.set_field(0, field_from_u64(500));
        let refl_bad =
            ReflectedConstraint::new(composer.build().unwrap()).with_sample(new_bad, None, None);
        assert!(!refl_bad.sample_accepts(), "slot 0 = 500 violates slot 0 ≤ 100");
        let trace_bad = refl_bad.trace();
        assert!(
            trace_bad.steps.iter().any(|s| s.label.contains("REJECT")),
            "the Trace reflects the real REJECT: {:?}",
            trace_bad.steps
        );
    }

    // ── the RawFields floor is always present ───────────────────────────────

    #[test]
    fn the_reflected_constraint_has_the_raw_fields_floor() {
        let (w, cell) = one_cell_world();
        let composer = PredicateComposer::new(
            cell,
            cell,
            Composite::AnyOf(vec![Atom::BalanceGte { min: 10 }]),
        );
        let refl = ReflectedConstraint::new(composer.build().unwrap());
        let ctx = PresentCtx::new(&w, cell);
        let set = refl.present(&ctx);
        assert!(
            set.iter().any(|p| p.kind == PresentationKind::RawFields),
            "RawFields is the mandatory floor"
        );
        // The Invariant face carries the §8 cost readout.
        assert!(set.iter().any(|p| p.kind == PresentationKind::Invariant));
    }

    // ── the anti-strip tooth: a witnessed branch is structurally safe ───────

    #[test]
    fn the_anti_strip_disjunction_lowers_to_the_real_bound_branch() {
        let (_w, cell) = one_cell_world();
        // An AnyOfBound with a cheap (sender) leg and a witnessed (cross-cell)
        // leg. The witnessed leg names its OWN proof carrier — the anti-strip
        // tooth is STRUCTURAL (a stripped proof closes that branch).
        let composite = Composite::AnyOfBound(vec![
            Branch::Simple(Atom::SenderIs {
                pk: *cell.as_bytes(),
            }),
            Branch::Witnessed {
                local_field: 2,
                source_cell: [0x55u8; 32],
                source_field: 3,
                at_root: [0x66u8; 32],
                proof_witness_index: 0,
            },
        ]);
        let composer = PredicateComposer::new(cell, cell, composite);
        // It validates (no strippable trivial leg) and lowers to the genuine
        // AnyOfBound with a real BoundBranch::Witnessed naming its proof index.
        assert!(composer.validate().is_ok());
        match composer.build().unwrap() {
            StateConstraint::AnyOfBound { branches } => {
                assert_eq!(branches.len(), 2);
                assert!(branches.iter().any(|b| matches!(
                    b,
                    BoundBranch::Witnessed {
                        proof_witness_index: 0,
                        ..
                    }
                )));
            }
            other => panic!("expected AnyOfBound, got {other:?}"),
        }
    }
}
