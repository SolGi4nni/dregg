//! **THE REFERENCE ORACLE** — the host-side composition, the canonical field streams, and
//! the roots. It computes the outcome OFF-circuit; `crate::air` RE-CHECKS it in-circuit
//! (translation validation, automatafl's posture).
//!
//! This module is where §9.3's "define now" list is actually decided:
//!
//!   * **canonical subject ordering** — ascending `identity` ([`canonical_subjects`]);
//!   * **duplicate rejection** — equal identities are refused, in-circuit by a STRICT
//!     increase (`crate::air`), so there is no separate host tooth to trust;
//!   * **missing/hidden/default values** — a param slot at or past `param_count` is
//!     canonically ZERO and is bound as zero into `subjects_root`; absence is COMMITTED,
//!     never ambiguous. A ruleset term addressing such a slot is REFUSED;
//!   * **schema/projection compatibility** — `param_count` is a PI and is absorbed into
//!     `subjects_root`, so a projection built under a different width yields a different
//!     root and cannot be silently reinterpreted;
//!   * **role tags** — opaque `u64`s, unique among active subjects, `0` reserved for
//!     absent. A term whose role is absent is UNRESOLVED and the composition is
//!     unprovable (fail-closed);
//!   * **explanation-term commitments** — [`Composed::contributions`] is the per-term
//!     vector `explanation_root` binds, so a "Why?" cannot diverge from the proven terms;
//!   * **finalized-root/witness semantics** — the AIR proves a composition over the
//!     projections it is GIVEN. It does not witness their finality; the projections'
//!     provenance rides `subjects_root` and is the caller's obligation (see
//!     `crate::model::Subject::identity` and the crate doc's honest-scope section).
//!
//! # The privacy boundary
//!
//! Param VALUES are private witness — they never appear in a public input. What is public
//! is: the counts, the four roots, and (by opening a root) whatever the caller chooses to
//! disclose. So the default posture is "nothing about a subject's params is revealed, and
//! the outcome is a commitment". Selective disclosure = the caller opens `subjects_root`
//! or `explanation_root` for the terms it wishes to reveal, against the same committed
//! vectors the AIR proved over — no second encoding, no second identity.

use dregg_circuit::field::BabyBear;

use crate::digest::{
    DOMAIN_EXPLANATION, DOMAIN_OUTCOME, DOMAIN_RULESET, DOMAIN_SUBJECTS, wide_digest,
};
use crate::field::fb;
use crate::model::{ComposeError, Composition, ROLE_ABSENT, Subject};
use crate::shape::{ComposeShape, MAX_SOUND_IDENTITY_BITS};

/// The result of composing: the outcome and the per-term contributions the explanation
/// root binds.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Composed {
    /// The composed value, exact in `i128` (the AIR's field twin is `fb(outcome)`).
    pub outcome: i128,
    /// Per-linear-term contributions, in ruleset order.
    pub linear_contributions: Vec<i128>,
    /// Per-knot contributions, in ruleset order. These are the NONLINEAR terms.
    pub knot_contributions: Vec<i128>,
}

impl Composed {
    /// The full per-term contribution vector `explanation_root` commits to: linear terms
    /// then knots, in ruleset order.
    pub fn contributions(&self) -> Vec<i128> {
        let mut v = self.linear_contributions.clone();
        v.extend_from_slice(&self.knot_contributions);
        v
    }
}

/// Resolve a role to its index in a subject list. Fail-closed on absence: a rule term
/// whose role no subject occupies makes the composition UNPROVABLE, never silently zero.
/// (The in-circuit twin is `Σ sel_j * active_j == term_active`, which cannot be satisfied
/// when no active subject carries the role.)
fn resolve(subjects: &[Subject], role: u64) -> Result<usize, ComposeError> {
    subjects
        .iter()
        .position(|s| s.role == role)
        .ok_or(ComposeError::UnresolvedRole(role))
}

/// A subject's param at `slot`, applying the canonical-default rule: a slot the subject
/// did not supply (but which is `< param_count`) reads ZERO.
fn param_of(s: &Subject, slot: usize) -> i64 {
    s.params.get(slot).copied().unwrap_or(0)
}

/// **THE COMPOSITION LAW**, over an explicitly-given subject list.
///
/// ```text
///   outcome = Σ_linear coeff * P[role].params[param]
///           + Σ_knots  coeff * P[role_a].params[param_a] * P[role_b].params[param_b]
/// ```
///
/// The knot sum is the nonlinear part. Evaluated exactly in `i128`; the AIR's field twin
/// is the image under `fb` (a ring homomorphism), so the two agree.
///
/// `subjects` is taken AS GIVEN — unsorted and un-deduplicated lists are composed
/// happily. That is deliberate: canonical ordering and duplicate rejection are the AIR's
/// job (a STRICT identity increase), so the forgery tests can hand this oracle a swapped
/// or duplicated list and watch the AIR — not the host — refuse it.
///
/// `neuter_knots` is THE CANARY: it deletes the nonlinear terms, so a caller can show that
/// compositions differing only in their products stop differing.
pub fn compose_over(
    subjects: &[Subject],
    ruleset: &crate::model::Ruleset,
    param_count: usize,
    neuter_knots: bool,
) -> Result<Composed, ComposeError> {
    let mut linear_contributions = Vec::with_capacity(ruleset.linear.len());
    for t in &ruleset.linear {
        if t.param >= param_count {
            return Err(ComposeError::ParamOutOfRange {
                param: t.param,
                param_count,
            });
        }
        let i = resolve(subjects, t.role)?;
        let v = param_of(&subjects[i], t.param) as i128;
        linear_contributions.push(t.coeff as i128 * v);
    }

    let mut knot_contributions = Vec::with_capacity(ruleset.knots.len());
    for k in &ruleset.knots {
        for p in [k.param_a, k.param_b] {
            if p >= param_count {
                return Err(ComposeError::ParamOutOfRange {
                    param: p,
                    param_count,
                });
            }
        }
        let ia = resolve(subjects, k.role_a)?;
        let ib = resolve(subjects, k.role_b)?;
        let va = param_of(&subjects[ia], k.param_a) as i128;
        let vb = param_of(&subjects[ib], k.param_b) as i128;
        knot_contributions.push(if neuter_knots {
            0
        } else {
            k.coeff as i128 * va * vb
        });
    }

    let outcome: i128 =
        linear_contributions.iter().sum::<i128>() + knot_contributions.iter().sum::<i128>();
    Ok(Composed {
        outcome,
        linear_contributions,
        knot_contributions,
    })
}

impl Composition {
    /// Check the composition against a shape's fuel bounds.
    pub fn check_shape(&self, shape: &ComposeShape) -> Result<(), ComposeError> {
        if self.subjects.len() > shape.max_subjects {
            return Err(ComposeError::ExceedsShape("max_subjects"));
        }
        if self.param_count > shape.max_params {
            return Err(ComposeError::ExceedsShape("max_params"));
        }
        if self.ruleset.linear.len() > shape.max_linear {
            return Err(ComposeError::ExceedsShape("max_linear"));
        }
        if self.ruleset.knots.len() > shape.max_knots {
            return Err(ComposeError::ExceedsShape("max_knots"));
        }
        if !shape.identity_bits_sound() {
            return Err(ComposeError::ExceedsShape("identity_bits"));
        }
        for s in &self.subjects {
            if s.identity >= (1u64 << shape.identity_bits) {
                return Err(ComposeError::IdentityOutOfRange(s.identity));
            }
            if s.params.len() > self.param_count {
                return Err(ComposeError::ParamOutOfRange {
                    param: s.params.len(),
                    param_count: self.param_count,
                });
            }
        }
        Ok(())
    }

    /// **CANONICAL SUBJECT ORDERING.** Ascending `identity`, duplicates refused, roles
    /// checked to be a KEY (unique, non-absent).
    ///
    /// The in-circuit twin is a STRICT increase of identity across active subjects, so an
    /// unsorted or duplicated list has no satisfying witness — the host does not get to be
    /// trusted with this.
    pub fn canonical_subjects(&self) -> Result<Vec<Subject>, ComposeError> {
        let mut sorted = self.subjects.clone();
        sorted.sort_by_key(|s| s.identity);
        for w in sorted.windows(2) {
            if w[0].identity == w[1].identity {
                return Err(ComposeError::DuplicateIdentity(w[0].identity));
            }
        }
        for s in &sorted {
            // The widest namespace any shape may declare; the SHAPE's own (possibly
            // narrower) `identity_bits` is checked by `check_shape`.
            if s.identity >= (1u64 << MAX_SOUND_IDENTITY_BITS) {
                return Err(ComposeError::IdentityOutOfRange(s.identity));
            }
            if s.role == ROLE_ABSENT {
                return Err(ComposeError::AbsentRoleTag);
            }
        }
        for i in 0..sorted.len() {
            for j in (i + 1)..sorted.len() {
                if sorted[i].role == sorted[j].role {
                    return Err(ComposeError::DuplicateRole(sorted[i].role));
                }
            }
        }
        Ok(sorted)
    }

    /// **THE COMPOSITION LAW**, over this composition's canonical subject order.
    /// See [`compose_over`].
    pub fn compose(&self) -> Result<Composed, ComposeError> {
        let canonical = self.canonical_subjects()?;
        compose_over(&canonical, &self.ruleset, self.param_count, false)
    }

    // -------------------------------------------------------------------------
    // The canonical field streams. Each is padded to the SHAPE's maxima with the
    // canonical inactive encoding (all-zero), so the stream length — and hence the
    // digest — is a function of the shape, and an active/inactive flag is bound for
    // every slot. Absence is committed, never inferred from length.
    // -------------------------------------------------------------------------

    /// The canonical subjects stream (`subject_count, param_count`, then per slot:
    /// `active, identity, role, params[0..max_params]`).
    pub fn subjects_stream(&self, shape: &ComposeShape) -> Result<Vec<BabyBear>, ComposeError> {
        let canonical = self.canonical_subjects()?;
        let mut out = vec![fb(canonical.len() as i128), fb(self.param_count as i128)];
        for i in 0..shape.max_subjects {
            match canonical.get(i) {
                Some(s) => {
                    out.push(fb(1));
                    out.push(fb(s.identity as i128));
                    out.push(fb(s.role as i128));
                    for p in 0..shape.max_params {
                        let v = if p < self.param_count {
                            param_of(s, p)
                        } else {
                            0
                        };
                        out.push(fb(v as i128));
                    }
                }
                None => {
                    for _ in 0..(3 + shape.max_params) {
                        out.push(BabyBear::ZERO);
                    }
                }
            }
        }
        Ok(out)
    }

    /// The canonical ruleset stream (`id, version, linear_count, knot_count`, then per
    /// linear slot `active, role, param, coeff`, then per knot slot
    /// `active, role_a, param_a, role_b, param_b, coeff`).
    pub fn ruleset_stream(&self, shape: &ComposeShape) -> Vec<BabyBear> {
        let r = &self.ruleset;
        let mut out = vec![
            fb(r.id as i128),
            fb(r.version as i128),
            fb(r.linear.len() as i128),
            fb(r.knots.len() as i128),
        ];
        for i in 0..shape.max_linear {
            match r.linear.get(i) {
                Some(t) => {
                    out.extend_from_slice(&[
                        fb(1),
                        fb(t.role as i128),
                        fb(t.param as i128),
                        fb(t.coeff as i128),
                    ]);
                }
                None => out.extend_from_slice(&[BabyBear::ZERO; 4]),
            }
        }
        for i in 0..shape.max_knots {
            match r.knots.get(i) {
                Some(k) => {
                    out.extend_from_slice(&[
                        fb(1),
                        fb(k.role_a as i128),
                        fb(k.param_a as i128),
                        fb(k.role_b as i128),
                        fb(k.param_b as i128),
                        fb(k.coeff as i128),
                    ]);
                }
                None => out.extend_from_slice(&[BabyBear::ZERO; 6]),
            }
        }
        out
    }

    /// `ruleset_root` — THE NAMED COMPOSITION LAW, at the fixed 8-felt binding width.
    pub fn ruleset_root(&self, shape: &ComposeShape) -> Vec<BabyBear> {
        wide_digest(DOMAIN_RULESET, &self.ruleset_stream(shape))
    }

    /// `subjects_root` — the canonical ordered projection list.
    pub fn subjects_root(&self, shape: &ComposeShape) -> Result<Vec<BabyBear>, ComposeError> {
        Ok(wide_digest(DOMAIN_SUBJECTS, &self.subjects_stream(shape)?))
    }

    /// `outcome_commitment`.
    pub fn outcome_commitment(&self, shape: &ComposeShape) -> Result<Vec<BabyBear>, ComposeError> {
        let c = self.compose()?;
        Ok(wide_digest(DOMAIN_OUTCOME, &[fb(c.outcome)]))
    }

    /// The explanation stream: the per-term contributions, padded to the shape's maxima.
    pub fn explanation_stream(&self, shape: &ComposeShape) -> Result<Vec<BabyBear>, ComposeError> {
        let c = self.compose()?;
        let mut out = Vec::with_capacity(shape.explanation_stream_len());
        for i in 0..shape.max_linear {
            out.push(fb(c.linear_contributions.get(i).copied().unwrap_or(0)));
        }
        for i in 0..shape.max_knots {
            out.push(fb(c.knot_contributions.get(i).copied().unwrap_or(0)));
        }
        Ok(out)
    }

    /// `explanation_root` — binds the per-term contributions, so a human-readable "Why?"
    /// can be checked against the terms the AIR actually proved.
    pub fn explanation_root(&self, shape: &ComposeShape) -> Result<Vec<BabyBear>, ComposeError> {
        Ok(wide_digest(
            DOMAIN_EXPLANATION,
            &self.explanation_stream(shape)?,
        ))
    }
}
