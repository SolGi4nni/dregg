//! # Membrane / forwarder — the unit of ocap *abstraction*, where authority
//! composes UPWARD.
//!
//! `docs/deos/MEMBRANE-FORWARDER.md`. dregg's existing cap discipline is a
//! *descent*: [`crate::facet::is_facet_attenuation`] narrows authority on the
//! way down ([`EffectMask`] submask, never amplify), and
//! [`crate::read_cap::ReadCap::attenuate`] does the dual for reads. Both answer
//! "may a child do *less* than its parent?". They have no answer for the
//! opposite move — *composing* two held authorities into a single new one that
//! the holder may exercise only by presenting **both**.
//!
//! A **membrane** is a cell whose program is a composition policy: it holds (or
//! references) caps **A** and **B**, and exposes a new cap **C** whose exercise
//! REQUIRES presenting both A and B. This is the forwarder pattern of E /
//! object-capability practice: a guarded facet that re-exports a *conjunction*
//! of inner authorities. It is the dual of attenuation — authority composes
//! upward through it — and it is the unit of ocap abstraction (a membrane *is*
//! an object whose interface is "exercise C", implemented over A and B).
//!
//! ## The non-amplification floor (the load-bearing constraint)
//!
//! A membrane MUST NOT leak more authority than its held caps jointly justify.
//! The conjunctive policy "C fires only when both A and B authorize" admits, as
//! its least-authority bound, exactly the **meet** of the two facets:
//!
//! ```text
//!     compose(A, B)  =  a_mask & b_mask      (the conjunction floor)
//! ```
//!
//! An effect bit may appear in C's exposed authority only if BOTH A and B carry
//! it — otherwise one of the two held caps could not have justified it, so
//! granting it would be amplification. The membrane therefore enforces
//!
//! ```text
//!     exposed ⊑ compose(A, B)               (no amplification)
//! ```
//!
//! at SEAL time ([`Membrane::seal`] returns [`None`] on any over-grant) AND
//! re-checks it at EXERCISE time ([`SealedMembrane::exercise`]), so a *forged*
//! membrane object whose `exposed` mask claims a bit outside `a & b` is
//! REJECTED rather than honoured. This mirrors the proven submask non-amp on the
//! descent side ([`crate::facet::is_facet_attenuation`]): the membrane is
//! exactly that same partial order read *upward through a meet*.
//!
//! ## Formal grounding (the non-amp floor is PROVEN, not just smoke-tested)
//!
//! The non-amplification floor enforced here — `exposed ⊑ a & b` ([`Membrane::
//! is_non_amplifying`], rechecked at [`Membrane::seal`] and
//! [`SealedMembrane::exercise`]) — is the EXECUTOR image of a proven Lean rung:
//! the **upward (conjunction) leg** of `metatheory/Dregg2/Deos/Membrane.lean`.
//! There the meet `a & b` is `compose` (intersection over the same `List Auth` /
//! `capAuthConferred ⊆` order the cap crown proves on), and
//!
//!   * `membrane_non_amplifies` — `exposed ⊆ compose a b ⟹ exposed ⊆ a ∧
//!     exposed ⊆ b` (this `is_non_amplifying`/`seal` floor cannot amplify), and
//!   * `sealed_refuses_unheld` — an authority a held cap lacks is absent from the
//!     meet, so a sealed membrane cannot expose it (the negative tooth, the Lean
//!     image of [`tests::forged_over_grant_is_rejected_at_seal`]),
//!
//! are both `#assert_all_clean` (kernel-axiom-clean), proven BY REUSE of the
//! submask/meet lattice (`List.mem_of_mem_filter` + `Subset.trans`) — no new
//! lattice. The Lean `Deos.Membrane` is the dual of attenuation read upward
//! through a meet, exactly as this module's docs state. The test
//! [`tests::non_amp_floor_matches_lean_rung`] mirrors that rung's witnesses on
//! the [`EffectMask`] shape so the Rust is checked against the proven statement.
//!
//! ## Honest seams (named with their lanes)
//!
//! - **Executor-grounded; the circuit witness is the named VK follow-up.** The
//!   Lean rung above grounds the EXECUTOR non-amp tooth. Binding the membrane's
//!   `exposed` mask into the cell state-commitment / cap-root the circuit sees
//!   (so a light client — not just the executor — witnesses "C's authority =
//!   a&b") is the VK-affecting weld named in
//!   `metatheory/docs/HOUSE-CAPACITIES-WELD-PLAN.md` (membrane row: "Medium,
//!   VK-affecting — new authorization predicate + circuit auth check"), the same
//!   VK-gated lane the cap-root reshape (`project-cap-reshape-plan`) drives. The
//!   non-amp tooth here is the *executor* tooth; the circuit tooth is its shadow.
//! - **2-of-2 is the genuine slice.** The policy generalises to k-of-n (hold a
//!   `Vec` of facets, require a quorum) and to predicate-gated composition
//!   (the [`crate::capability::CapabilityCaveat::Witnessed`] surface); the
//!   minimal genuine membrane is the conjunction of two. The generalisation is
//!   the next slice, not a stub.

use serde::{Deserialize, Serialize};

use crate::facet::{EffectMask, is_facet_attenuation};
use crate::id::CellId;

/// One inner authority the membrane holds — a facet (`mask`) over a target
/// cell. This is the held-cap face the membrane composes from. It is
/// deliberately the bare authority shape (target + facet mask), the same
/// `EffectMask` the descent side ([`crate::facet`]) narrows: composition and
/// attenuation operate on the SAME lattice, read in opposite directions.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct HeldFacet {
    /// Which cell this held authority points at.
    pub target: CellId,
    /// The effect-mask facet of the held cap (which effect kinds it permits).
    pub mask: EffectMask,
}

impl HeldFacet {
    /// A held facet over `target` permitting exactly the effect kinds in `mask`.
    pub fn new(target: CellId, mask: EffectMask) -> Self {
        HeldFacet { target, mask }
    }
}

/// The composition policy a membrane enforces.
///
/// v1 ships the genuine slice: a **2-of-2 conjunction** — C fires only when the
/// caller presents proof of holding BOTH A and B, and C's exposed authority is
/// bounded by the meet `a & b`. The enum is the additive surface for the
/// k-of-n / predicate-gated generalisations (the next slice).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum CompositionPolicy {
    /// Require both held facets (A AND B). The exposed authority floor is the
    /// meet of the two masks.
    BothOf,
}

impl CompositionPolicy {
    /// The least-authority bound this policy admits over the held facets — the
    /// most authority a membrane under this policy may *ever* expose without
    /// amplifying.
    ///
    /// For [`CompositionPolicy::BothOf`] this is the **meet** (bitwise AND): an
    /// effect bit is justified only if BOTH held caps carry it. This is the
    /// conjunction floor — the upward-composition dual of the submask descent.
    pub fn authority_bound(&self, a: &HeldFacet, b: &HeldFacet) -> EffectMask {
        match self {
            CompositionPolicy::BothOf => a.mask & b.mask,
        }
    }
}

/// Convenience: the meet of two held facets under the 2-of-2 conjunction
/// policy — the authority floor a [`BothOf`](CompositionPolicy::BothOf)
/// membrane may expose. Exposed here as a named primitive so the soundness
/// tooth (`exposed ⊑ compose(A,B)`) reads directly.
pub fn compose_both(a: &HeldFacet, b: &HeldFacet) -> EffectMask {
    a.mask & b.mask
}

/// An UNSEALED membrane: the held facets, the policy, and the *claimed* exposed
/// authority for cap C. Constructing one of these is unprivileged — it is just
/// a claim. The non-amplification check happens at [`Membrane::seal`], which is
/// the only path to a [`SealedMembrane`] (and hence to a usable [`MembraneCap`]).
///
/// A forged membrane is exactly an `exposed` that claims more than the policy's
/// `authority_bound` over `(a, b)`; [`Membrane::seal`] returns [`None`] on it.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Membrane {
    /// The membrane cell's own identity (the object exposing cap C).
    pub cell: CellId,
    /// Held cap A.
    pub a: HeldFacet,
    /// Held cap B.
    pub b: HeldFacet,
    /// The composition policy gating C's exercise.
    pub policy: CompositionPolicy,
    /// The cell C's authority points at (the forwarded target). For the
    /// conjunction-forwarder this is typically `a.target == b.target`, but the
    /// type does not force it; the meet of masks is the floor regardless.
    pub exposed_target: CellId,
    /// The CLAIMED effect-mask authority of cap C. Subject to the non-amp
    /// check at seal: must satisfy `exposed ⊑ authority_bound(a, b)`.
    pub exposed: EffectMask,
}

impl Membrane {
    /// Build an unsealed membrane claiming `exposed` authority for cap C over
    /// `exposed_target`, gated by `policy` on held facets `a` and `b`.
    pub fn new(
        cell: CellId,
        a: HeldFacet,
        b: HeldFacet,
        policy: CompositionPolicy,
        exposed_target: CellId,
        exposed: EffectMask,
    ) -> Self {
        Membrane {
            cell,
            a,
            b,
            policy,
            exposed_target,
            exposed,
        }
    }

    /// Build the *maximal* lawful membrane: exposes exactly the policy's
    /// authority bound (`a & b` for 2-of-2). This can never amplify by
    /// construction, so it always seals.
    pub fn maximal(
        cell: CellId,
        a: HeldFacet,
        b: HeldFacet,
        policy: CompositionPolicy,
        exposed_target: CellId,
    ) -> Self {
        let exposed = policy.authority_bound(&a, &b);
        Membrane {
            cell,
            a,
            b,
            policy,
            exposed_target,
            exposed,
        }
    }

    /// The non-amplification predicate: is the claimed `exposed` authority a
    /// submask of the policy's bound over the held facets?
    ///
    /// This is [`is_facet_attenuation`] read against the *composed* floor — the
    /// SAME submask order the descent side enforces, with the parent being the
    /// upward composition `authority_bound(a, b)` rather than a single held cap.
    pub fn is_non_amplifying(&self) -> bool {
        let bound = self.policy.authority_bound(&self.a, &self.b);
        is_facet_attenuation(bound, self.exposed)
    }

    /// **Seal** the membrane: verify the composition policy is non-amplifying,
    /// and on success yield a [`SealedMembrane`] (the only thing that can mint a
    /// usable cap C). Returns [`None`] — the forge rejection — if `exposed`
    /// claims any authority outside the policy's bound.
    ///
    /// This is the upward-composition analogue of
    /// [`crate::read_cap::ReadCap::attenuate`] returning `None` on a slot the
    /// holder cannot read: a membrane that would leak authority simply does not
    /// come into being.
    pub fn seal(self) -> Option<SealedMembrane> {
        if self.is_non_amplifying() {
            Some(SealedMembrane { membrane: self })
        } else {
            None
        }
    }
}

/// A proof presented to exercise cap C: the caller asserts it holds both A and
/// B by presenting a facet for each. For the executor-level slice the
/// "presentation" is the held facet itself (target + mask); the circuit slice
/// replaces this with the in-circuit cap-membership witness (the lane named in
/// the module docs).
///
/// The conjunction gate checks that each presented facet (a) targets the same
/// cell the membrane holds, and (b) carries at least the authority the membrane
/// recorded — you cannot satisfy "I hold A" by presenting something weaker than
/// A.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Presentation {
    /// The facet presented as evidence of holding A.
    pub a: Option<HeldFacet>,
    /// The facet presented as evidence of holding B.
    pub b: Option<HeldFacet>,
}

impl Presentation {
    /// Present both A and B.
    pub fn both(a: HeldFacet, b: HeldFacet) -> Self {
        Presentation {
            a: Some(a),
            b: Some(b),
        }
    }

    /// Present only A (the deficient presentation the membrane must REFUSE).
    pub fn only_a(a: HeldFacet) -> Self {
        Presentation {
            a: Some(a),
            b: None,
        }
    }

    /// Present only B.
    pub fn only_b(b: HeldFacet) -> Self {
        Presentation {
            a: None,
            b: Some(b),
        }
    }
}

/// Why a membrane exercise was refused.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MembraneError {
    /// The presentation did not include cap A.
    MissingA,
    /// The presentation did not include cap B.
    MissingB,
    /// A presented facet did not match the held cap it claimed to be
    /// (wrong target, or weaker than the membrane recorded).
    PresentationMismatch,
    /// The requested effect is not within the membrane's exposed authority.
    NotExposed,
    /// The membrane's exposed authority exceeds its composition floor — a
    /// forged/over-granting membrane. (Reachable only if a `SealedMembrane` is
    /// constructed bypassing [`Membrane::seal`], e.g. via tampered
    /// deserialization; [`SealedMembrane::exercise`] re-checks defensively.)
    AmplifyingMembrane,
}

/// A membrane whose composition policy has PASSED the non-amplification check.
/// This is the verified-policy object; only it can mint cap C.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SealedMembrane {
    membrane: Membrane,
}

impl SealedMembrane {
    /// The exposed cap C this membrane forwards.
    pub fn cap_c(&self) -> MembraneCap {
        MembraneCap {
            membrane_cell: self.membrane.cell,
            target: self.membrane.exposed_target,
            authority: self.membrane.exposed,
        }
    }

    /// The composition floor this membrane sits under (`a & b` for 2-of-2) —
    /// the non-amp soundness bound. The exposed authority is always `⊑` this.
    pub fn composition_floor(&self) -> EffectMask {
        self.membrane
            .policy
            .authority_bound(&self.membrane.a, &self.membrane.b)
    }

    /// Read access to the underlying (verified) membrane.
    pub fn membrane(&self) -> &Membrane {
        &self.membrane
    }

    /// **Exercise** cap C for `requested_effect`, presenting evidence of holding
    /// the inner caps.
    ///
    /// The require-both gate (in order):
    /// 1. Both A and B must be presented ([`MembraneError::MissingA`] /
    ///    [`MembraneError::MissingB`] otherwise — this is the refuse-without-both
    ///    tooth).
    /// 2. Each presented facet must MATCH the held cap (same target, and at
    ///    least as much authority as recorded) — you cannot forge "I hold A" by
    ///    presenting a weaker or wrong-target facet.
    /// 3. The membrane re-verifies its own non-amplification (defence against a
    ///    tampered `SealedMembrane`).
    /// 4. `requested_effect` must lie within the exposed authority.
    ///
    /// On success returns the forwarded [`MembraneCap`] authorising
    /// `requested_effect` over the exposed target.
    pub fn exercise(
        &self,
        presentation: &Presentation,
        requested_effect: EffectMask,
    ) -> Result<MembraneCap, MembraneError> {
        // 1. require-both
        let pres_a = presentation.a.as_ref().ok_or(MembraneError::MissingA)?;
        let pres_b = presentation.b.as_ref().ok_or(MembraneError::MissingB)?;

        // 2. each presentation must match (or exceed) the held cap it claims.
        // "Holding A" means presenting a facet over A's target whose mask
        // covers A's recorded mask (held ⊆ presented). Presenting something
        // weaker than the membrane's A does not prove you hold A.
        if pres_a.target != self.membrane.a.target
            || !is_facet_attenuation(pres_a.mask, self.membrane.a.mask)
        {
            return Err(MembraneError::PresentationMismatch);
        }
        if pres_b.target != self.membrane.b.target
            || !is_facet_attenuation(pres_b.mask, self.membrane.b.mask)
        {
            return Err(MembraneError::PresentationMismatch);
        }

        // 3. defensive non-amp re-check (forge-detector at exercise time).
        if !self.membrane.is_non_amplifying() {
            return Err(MembraneError::AmplifyingMembrane);
        }

        // 4. the requested effect must be within the exposed authority.
        // The exposed authority is `⊑ a & b` (guaranteed by 3), so this also
        // guarantees the requested effect is jointly authorised by A and B.
        if requested_effect & self.membrane.exposed != requested_effect || requested_effect == 0 {
            return Err(MembraneError::NotExposed);
        }

        Ok(MembraneCap {
            membrane_cell: self.membrane.cell,
            target: self.membrane.exposed_target,
            authority: requested_effect,
        })
    }
}

/// The exposed cap **C** a membrane forwards. Its `authority` is always a
/// submask of the membrane's composition floor (`a & b` for 2-of-2): the
/// upward composition never grants more than its held caps jointly justify.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct MembraneCap {
    /// The membrane cell that exposes this cap.
    pub membrane_cell: CellId,
    /// The cell this cap forwards authority over.
    pub target: CellId,
    /// The forwarded authority (effect-mask facet). `⊑ a & b`.
    pub authority: EffectMask,
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::facet::{
        EFFECT_EMIT_EVENT, EFFECT_GRANT_CAPABILITY, EFFECT_SET_FIELD, EFFECT_SET_PERMISSIONS,
        EFFECT_TRANSFER,
    };

    fn cell(n: u8) -> CellId {
        CellId::from_bytes([n; 32])
    }

    // ── the meet / composition floor ────────────────────────────────────────

    #[test]
    fn compose_is_the_meet() {
        let a = HeldFacet::new(
            cell(1),
            EFFECT_SET_FIELD | EFFECT_TRANSFER | EFFECT_EMIT_EVENT,
        );
        let b = HeldFacet::new(
            cell(1),
            EFFECT_TRANSFER | EFFECT_EMIT_EVENT | EFFECT_SET_PERMISSIONS,
        );
        // only TRANSFER and EMIT_EVENT are in BOTH.
        assert_eq!(compose_both(&a, &b), EFFECT_TRANSFER | EFFECT_EMIT_EVENT);
        assert_eq!(
            CompositionPolicy::BothOf.authority_bound(&a, &b),
            EFFECT_TRANSFER | EFFECT_EMIT_EVENT
        );
    }

    // ── seal: non-amp at construction ───────────────────────────────────────

    #[test]
    fn maximal_membrane_always_seals_and_exposes_the_meet() {
        let a = HeldFacet::new(cell(1), EFFECT_SET_FIELD | EFFECT_TRANSFER);
        let b = HeldFacet::new(cell(1), EFFECT_TRANSFER | EFFECT_EMIT_EVENT);
        let m = Membrane::maximal(cell(9), a, b, CompositionPolicy::BothOf, cell(1));
        let sealed = m.seal().expect("maximal membrane must seal");
        assert_eq!(sealed.cap_c().authority, EFFECT_TRANSFER); // the meet
        assert_eq!(sealed.composition_floor(), EFFECT_TRANSFER);
    }

    #[test]
    fn sub_floor_exposed_seals() {
        // Exposing LESS than the floor is lawful (you may forward a narrower C).
        let a = HeldFacet::new(cell(1), EFFECT_TRANSFER | EFFECT_EMIT_EVENT);
        let b = HeldFacet::new(cell(1), EFFECT_TRANSFER | EFFECT_EMIT_EVENT);
        let m = Membrane::new(
            cell(9),
            a,
            b,
            CompositionPolicy::BothOf,
            cell(1),
            EFFECT_TRANSFER, // floor is TRANSFER|EMIT; exposing just TRANSFER
        );
        assert!(m.is_non_amplifying());
        assert!(m.seal().is_some());
    }

    // ── THE NON-AMP FORGE-DETECTOR ──────────────────────────────────────────

    #[test]
    fn forged_over_grant_is_rejected_at_seal() {
        // A claims SET_FIELD|TRANSFER, B claims TRANSFER|EMIT.
        // floor = a & b = TRANSFER. A forged membrane claims C grants
        // SET_FIELD too (which only A has) — amplification. MUST be refused.
        let a = HeldFacet::new(cell(1), EFFECT_SET_FIELD | EFFECT_TRANSFER);
        let b = HeldFacet::new(cell(1), EFFECT_TRANSFER | EFFECT_EMIT_EVENT);
        let forged = Membrane::new(
            cell(9),
            a,
            b,
            CompositionPolicy::BothOf,
            cell(1),
            EFFECT_TRANSFER | EFFECT_SET_FIELD, // SET_FIELD not in b → amplify
        );
        assert!(!forged.is_non_amplifying());
        assert!(forged.seal().is_none(), "forged over-grant must NOT seal");
    }

    #[test]
    fn forged_grant_of_bit_in_neither_is_rejected() {
        // The strongest forge: C claims a bit NEITHER held cap carries.
        let a = HeldFacet::new(cell(1), EFFECT_TRANSFER);
        let b = HeldFacet::new(cell(1), EFFECT_TRANSFER);
        let forged = Membrane::new(
            cell(9),
            a,
            b,
            CompositionPolicy::BothOf,
            cell(1),
            EFFECT_SET_PERMISSIONS, // in neither A nor B
        );
        assert!(!forged.is_non_amplifying());
        assert!(forged.seal().is_none());
    }

    // ── exercise: require-both gate ─────────────────────────────────────────

    fn sample_membrane() -> SealedMembrane {
        let a = HeldFacet::new(cell(1), EFFECT_TRANSFER | EFFECT_EMIT_EVENT);
        let b = HeldFacet::new(cell(1), EFFECT_TRANSFER | EFFECT_EMIT_EVENT);
        Membrane::maximal(cell(9), a, b, CompositionPolicy::BothOf, cell(1))
            .seal()
            .unwrap()
    }

    #[test]
    fn a_plus_b_exercises_c() {
        let m = sample_membrane();
        let a = m.membrane().a.clone();
        let b = m.membrane().b.clone();
        let cap = m
            .exercise(&Presentation::both(a, b), EFFECT_TRANSFER)
            .expect("A+B must exercise C");
        assert_eq!(cap.authority, EFFECT_TRANSFER);
        assert_eq!(cap.target, cell(1));
    }

    #[test]
    fn a_alone_is_refused() {
        let m = sample_membrane();
        let a = m.membrane().a.clone();
        let err = m
            .exercise(&Presentation::only_a(a), EFFECT_TRANSFER)
            .unwrap_err();
        assert_eq!(err, MembraneError::MissingB);
    }

    #[test]
    fn b_alone_is_refused() {
        let m = sample_membrane();
        let b = m.membrane().b.clone();
        let err = m
            .exercise(&Presentation::only_b(b), EFFECT_TRANSFER)
            .unwrap_err();
        assert_eq!(err, MembraneError::MissingA);
    }

    #[test]
    fn presenting_a_weaker_facet_does_not_prove_holding() {
        // Caller presents both, but their "A" is weaker than the held A
        // (missing EMIT_EVENT). They have not proven they hold A.
        let m = sample_membrane();
        let weak_a = HeldFacet::new(cell(1), EFFECT_TRANSFER); // held A also has EMIT
        let b = m.membrane().b.clone();
        let err = m
            .exercise(&Presentation::both(weak_a, b), EFFECT_TRANSFER)
            .unwrap_err();
        assert_eq!(err, MembraneError::PresentationMismatch);
    }

    #[test]
    fn presenting_wrong_target_does_not_prove_holding() {
        let m = sample_membrane();
        let wrong_a = HeldFacet::new(cell(2), EFFECT_TRANSFER | EFFECT_EMIT_EVENT);
        let b = m.membrane().b.clone();
        let err = m
            .exercise(&Presentation::both(wrong_a, b), EFFECT_TRANSFER)
            .unwrap_err();
        assert_eq!(err, MembraneError::PresentationMismatch);
    }

    #[test]
    fn exercising_outside_exposed_authority_is_refused() {
        // C exposes only TRANSFER (the meet). Asking for EMIT-only is fine
        // (it's in the meet here), but asking for SET_FIELD — outside the
        // floor — must be refused even with both presented.
        let a = HeldFacet::new(cell(1), EFFECT_TRANSFER); // floor will be TRANSFER
        let b = HeldFacet::new(cell(1), EFFECT_TRANSFER);
        let m = Membrane::maximal(
            cell(9),
            a.clone(),
            b.clone(),
            CompositionPolicy::BothOf,
            cell(1),
        )
        .seal()
        .unwrap();
        let err = m
            .exercise(&Presentation::both(a, b), EFFECT_SET_FIELD)
            .unwrap_err();
        assert_eq!(err, MembraneError::NotExposed);
    }

    // ── exercise-time defensive forge-detector ──────────────────────────────

    #[test]
    fn tampered_sealed_membrane_is_rejected_at_exercise() {
        // Simulate a SealedMembrane that bypassed seal() (e.g. tampered
        // deserialization): exposed claims more than the floor. The exercise
        // path re-checks and refuses.
        let a = HeldFacet::new(cell(1), EFFECT_TRANSFER);
        let b = HeldFacet::new(cell(1), EFFECT_TRANSFER);
        let mut tampered = Membrane::maximal(
            cell(9),
            a.clone(),
            b.clone(),
            CompositionPolicy::BothOf,
            cell(1),
        )
        .seal()
        .unwrap();
        // forge the exposed mask post-seal.
        tampered.membrane.exposed = EFFECT_TRANSFER | EFFECT_SET_PERMISSIONS;
        let err = tampered
            .exercise(&Presentation::both(a, b), EFFECT_SET_PERMISSIONS)
            .unwrap_err();
        assert_eq!(err, MembraneError::AmplifyingMembrane);
    }

    // ── the upward/downward duality ─────────────────────────────────────────

    #[test]
    fn exposed_is_always_submask_of_held_meet() {
        // The core soundness invariant, stated directly: for any sealed
        // membrane, exposed ⊑ a & b.
        for (am, bm) in [
            (EFFECT_TRANSFER | EFFECT_EMIT_EVENT, EFFECT_TRANSFER),
            (
                EFFECT_SET_FIELD | EFFECT_TRANSFER,
                EFFECT_TRANSFER | EFFECT_EMIT_EVENT,
            ),
            (EFFECT_ALL_TEST, EFFECT_TRANSFER | EFFECT_SET_FIELD),
        ] {
            let a = HeldFacet::new(cell(1), am);
            let b = HeldFacet::new(cell(1), bm);
            let m = Membrane::maximal(
                cell(9),
                a.clone(),
                b.clone(),
                CompositionPolicy::BothOf,
                cell(1),
            )
            .seal()
            .unwrap();
            let exposed = m.cap_c().authority;
            let meet = compose_both(&a, &b);
            assert_eq!(exposed & meet, exposed, "exposed must be ⊑ a & b");
        }
    }

    const EFFECT_ALL_TEST: EffectMask =
        EFFECT_SET_FIELD | EFFECT_TRANSFER | EFFECT_EMIT_EVENT | EFFECT_SET_PERMISSIONS;

    // ── the Lean rung: this executor floor is PROVEN, not just smoke-tested ──

    /// Mirror of the upward-leg witnesses in `metatheory/Dregg2/Deos/Membrane.lean`
    /// (`compose` / `membrane_non_amplifies` / `sealed_refuses_unheld`, all
    /// `#assert_all_clean`). The Lean proves over `List Auth`; here the SAME
    /// structure is checked over [`EffectMask`], so the Rust non-amp floor is
    /// checked against the proven statement, not just an ad-hoc tampering.
    ///
    /// Lean: A = {write, read, grant}, B = {read, grant, call}, meet = {read,
    /// grant}; A-only and B-only bits are darkened; the meet seals, a sub-floor
    /// seals, an over-grant (A-only bit) and a bit in neither both refuse.
    #[test]
    fn non_amp_floor_matches_lean_rung() {
        // A-only ≙ write, shared ≙ {read, grant} ≙ {SET_FIELD, TRANSFER},
        // B-only ≙ call, neither ≙ reply. Map to distinct EffectMask bits:
        let a_only = EFFECT_EMIT_EVENT; // Lean `write` (A-only)
        let shared = EFFECT_SET_FIELD | EFFECT_TRANSFER; // Lean {read, grant}
        let b_only = EFFECT_GRANT_CAPABILITY; // Lean `call` (B-only)
        let neither = EFFECT_SET_PERMISSIONS; // Lean `reply` (in neither)

        let a = HeldFacet::new(cell(5), a_only | shared);
        let b = HeldFacet::new(cell(5), shared | b_only);

        // `compose` == the meet (only what BOTH hold): the Lean `#guard compose fA fB == [read,grant]`.
        assert_eq!(compose_both(&a, &b), shared);
        // A-only and B-only bits are darkened (Lean: write/call ∉ the meet).
        assert_eq!(compose_both(&a, &b) & a_only, 0);
        assert_eq!(compose_both(&a, &b) & b_only, 0);

        // The maximal membrane (exposes exactly the meet) seals — `membrane_non_amplifies`.
        let maximal = Membrane::maximal(
            cell(9),
            a.clone(),
            b.clone(),
            CompositionPolicy::BothOf,
            cell(5),
        );
        assert!(maximal.is_non_amplifying());
        assert_eq!(maximal.clone().seal().unwrap().cap_c().authority, shared);

        // A sub-floor exposed also seals (Lean `#guard [read] ⊆ compose fA fB`).
        let sub = Membrane::new(
            cell(9),
            a.clone(),
            b.clone(),
            CompositionPolicy::BothOf,
            cell(5),
            EFFECT_SET_FIELD,
        );
        assert!(sub.is_non_amplifying());

        // Over-grant of an A-only bit does NOT seal (Lean `!([read,write] ⊆ meet)`).
        let over = Membrane::new(
            cell(9),
            a.clone(),
            b.clone(),
            CompositionPolicy::BothOf,
            cell(5),
            shared | a_only,
        );
        assert!(!over.is_non_amplifying());
        assert!(over.seal().is_none());

        // A bit in NEITHER held cap does not seal (Lean `!([reply] ⊆ meet)`) —
        // the executor image of `sealed_refuses_unheld`.
        let alien = Membrane::new(cell(9), a, b, CompositionPolicy::BothOf, cell(5), neither);
        assert!(!alien.is_non_amplifying());
        assert!(alien.seal().is_none());
    }
}
