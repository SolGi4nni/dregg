//! # Hatchery abstraction-mint — minting an OPEN vocabulary of verified cell-kinds.
//!
//! The kernel ships a *fixed* vocabulary of cell shapes: a cell is whatever its
//! installed [`CellProgram`] says it is, and the executor re-evaluates that
//! program on every state-modifying turn. The [factory][dregg_cell::factory]
//! layer lets one author a **content-addressed constructor** that bakes a
//! perpetual `state_constraints` set onto every child it produces. The
//! [Hatchery](../../../HATCHERY.md) supplies the other half: a *prove-once,
//! hold-forever* toolkit (`Dregg2.Verify.Contract.CellContract`) whose single
//! obligation `step_ob : ∀ s c, Inv s → Inv (E.next s c)` — a single-step
//! preservation, the **hpres** — is fed to `livingCellA_carries` and hands back
//! `∀ n, Inv (trajA s sched n)`: the invariant holds at every step of the
//! unbounded trajectory, against every adversarial schedule.
//!
//! This module is the **weld**. A [`MintedKind`] is exactly:
//!
//! 1. a [`FactoryDescriptor`] whose `state_constraints` ARE the kind's invariant
//!    (so every minted cell carries the invariant as its program-for-life, and
//!    the executor enforces it forever — that is the kernel doing the holding);
//! 2. an [`Invariant`] — the structured shape the author declared (e.g.
//!    "balance never negative", "this field is monotone"); and
//! 3. an [`HpresProof`] slot — the attestation that the invariant actually
//!    *holds* under a single living-cell step (the Hatchery's `step_ob`).
//!
//! The path it opens: from a fixed vocabulary of kernel shapes to an **OPEN
//! vocabulary of verified kinds**. A user defines a new cell-KIND with its own
//! invariant, attests the invariant once, and the kernel enforces it as
//! first-class — every cell of that kind, every turn, forever.
//!
//! ## What "enforced as first-class" means here (no stub)
//!
//! Enforcement is **not** added by this module. It is the executor's existing
//! evaluation of the child's `CellProgram` (the same gate every settlement /
//! storage / governance cell faces): [`MintedKind::evaluate_transition`]
//! delegates straight to [`CellProgram::evaluate_with_meta`]. A turn that
//! violates the invariant returns `Err(ProgramError::ConstraintViolated{..})` —
//! a real refusal, reproduced bit-for-bit by any re-executing validator. A
//! conforming turn returns `Ok(())`.
//!
//! ## The forge-detector
//!
//! Minting alone does not make a cell honest: a cell could *claim* to be of a
//! minted kind while installing a program that omits the invariant. The kind is
//! content-addressed — [`MintedKind::kind_id`] — and the invariant is baked into
//! the descriptor's hash, so [`MintedKind::attest_membership`] is the gate that
//! rejects **membership-without-conformance**: a cell whose installed program
//! does not carry the kind's invariant constraints is rejected
//! ([`ForgeRejection::ProgramMissingInvariant`]), even if it waves the kind id
//! around. Conformance is membership.
//!
//! ## The Lean rung — the invariant is PROVEN, not just smoke-tested
//!
//! The abstraction-mint invariant is grounded in `metatheory/Dregg2/Deos/
//! Hatchery.lean` (the LAST of the six house capacities — the house COMPLETE):
//! the per-turn gate IS the declared invariant (`evalStep_admits_iff_*`), an
//! admitted step preserves it (`step_preserves`, the **hpres**), and the SAME
//! `Verify.Contract.CellContract` carry skeleton lifts it to the unbounded
//! trajectory — `invariant_forever`: under EVERY schedule of admitted turns, a
//! minted cell carries its invariant for life. The Lean binds
//! [`HpresProof::Attested`] to a machine-checked `CellContract`: its `Attested`
//! structure cannot be constructed without a real contract (hence a real
//! `step_ob` proof term), so an attestation is a *proved* forever-crown
//! (`attested_enforces_forever`), not a trusted flag — and an attestation for a
//! *different* invariant is rejected by the decidable content-hash check
//! (`forged_attestation_rejected`). The forge-detector here is the executor
//! image of that rung; [`tests::invariant_matches_lean_rung`] mirrors the Lean
//! witnesses so the Rust rejection is tied to the proven statement.
//!
//! The DEEPER weld — making the `Attested` forever-crown REAL for a pure light
//! client (not just a re-executing validator) — is the per-turn FOLD over a
//! re-proved CONTRACT-ATTESTATION leaf
//! (`dregg_circuit_prove::hatchery_leaf_adapter::prove_hatchery_leaf`), connected
//! to the mint leg's claimed `contract_hash` teeth by
//! `prove_hatchery_binding_node_segmented`. This binds the `(contract_hash,
//! invariant_digest)` tuple IN the deployed recursion tree the light client folds,
//! so a mint whose `contract_hash` is backed by no verifying attestation is UNSAT —
//! the same fold-binding shape the sovereign / custom / membership carriers ride.
//! The adversarial refutation it answers is
//! `metatheory/Dregg2/Circuit/HatcheryBackingAttack.lean`
//! (`deployed_admits_unbacked_hatchery`); the fold tooth bites in
//! `hatchery_leaf_adapter::tests::forged_contract_hash_is_rejected_by_the_fold`.
//! Two named seams remain (NOT vacuity): the deployed mint leg must DUAL-EXPOSE its
//! `contract_hash` teeth (a descriptor PI-exposure change — the VK-affecting
//! "big-bang" piece this node consumes,
//! `metatheory/docs/HOUSE-CAPACITIES-WELD-PLAN.md`, hatchery row), and full in-AIR
//! re-verification that the `contract_hash` resolves to a verifying `CellContract`
//! proof term stays the named off-AIR digest-of-attestation cost.

use dregg_cell::factory::{FactoryDescriptor, canonical_program_vk};
use dregg_cell::program::{TransitionCase, TransitionGuard, TransitionMeta};
use dregg_cell::{
    CellMode, CellProgram, CellState, FieldElement, ProgramError, StateConstraint, field_from_u64,
};

/// The structured invariant an author declares for a new kind.
///
/// Each variant lowers to a concrete [`StateConstraint`] set
/// ([`Invariant::constraints`]) that becomes the kind's perpetual program. The
/// variants here are the minimal genuine slice; the Hatchery's shape catalog
/// (`monotone_registry%`, `conservation%`, `confinement%`, …) is the full
/// vocabulary this is the Rust-facing seed of.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Invariant {
    /// "This balance slot is never negative": the slot, read as a big-endian
    /// u64, is always `>= floor`. With `floor == 0` this is the canonical
    /// non-negativity invariant. Enforced by [`StateConstraint::FieldGte`].
    ///
    /// (Slot fields are unsigned in the constraint algebra; an app encodes a
    /// balance as a non-negative slot and proves it never drops below `floor`.
    /// This is distinct from the cell's signed `balance` accumulator, which the
    /// verb discipline governs separately.)
    BalanceNeverBelow { slot: u8, floor: u64 },

    /// "This field only ever moves forward": `new[slot] >= old[slot]` on every
    /// transition. Append-only counters, expiry extensions, registration epochs.
    /// Enforced by [`StateConstraint::Monotonic`].
    MonotoneField { slot: u8 },
}

impl Invariant {
    /// Lower the declared invariant into the perpetual [`StateConstraint`] set
    /// the executor enforces on every turn. This IS the kind's program.
    pub fn constraints(&self) -> Vec<StateConstraint> {
        match self {
            Invariant::BalanceNeverBelow { slot, floor } => vec![StateConstraint::FieldGte {
                index: *slot,
                value: field_from_u64(*floor),
            }],
            Invariant::MonotoneField { slot } => {
                vec![StateConstraint::Monotonic { index: *slot }]
            }
        }
    }

    /// The slot this invariant governs (for diagnostics / the forge report).
    pub fn slot(&self) -> u8 {
        match self {
            Invariant::BalanceNeverBelow { slot, .. } | Invariant::MonotoneField { slot } => *slot,
        }
    }

    /// A short human label, for the contract card / explain surface.
    pub fn label(&self) -> String {
        match self {
            Invariant::BalanceNeverBelow { slot, floor } => {
                format!("balance slot {slot} never below {floor}")
            }
            Invariant::MonotoneField { slot } => {
                format!("field slot {slot} monotone (never decreases)")
            }
        }
    }
}

/// The Hatchery attestation slot: the proof that the kind's invariant is a
/// genuine single-step invariant (`hpres` / `CellContract.step_ob`).
///
/// `Pending` is the honest current state: the *runtime* enforcement (the
/// executor refusing a violating turn) stands in for the Lean proof. It does
/// NOT launder a gap — a `Pending` kind is still enforced first-class by the
/// kernel; what is deferred is the machine-checked "holds forever against any
/// adversary" crown. `Attested` is the next slice: a content hash binding the
/// kind to a proved `Dregg2.Verify.Contract.CellContract`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum HpresProof {
    /// No Lean crown bound yet. Enforcement is the runtime program gate; the
    /// `livingCellA_carries` "forever" theorem is the named next slice.
    Pending,
    /// The kind is bound to a proved `Dregg2.Verify.Contract.CellContract` whose
    /// `step_ob` discharges this invariant, identified by the content hash of the
    /// Lean artifact / `#assert_axioms`-pinned theorem name. The binding is REAL at
    /// two layers: (executor/Lean) `metatheory/Dregg2/Deos/Hatchery.lean`'s
    /// `Attested` cannot be constructed without the contract (hence a real
    /// `step_ob`), and `attested_enforces_forever` cashes it out into the unbounded
    /// "holds forever" carry; (light-client) the `contract_hash` is bound into the
    /// per-turn recursion FOLD a pure light client verifies, by
    /// `dregg_circuit_prove::hatchery_leaf_adapter` — a `contract_hash` no
    /// attestation leaf backs is UNSAT in the aggregate (the
    /// `HatcheryBackingAttack.deployed_admits_unbacked_hatchery` forgery answered).
    /// An attestation for a *different* invariant is rejected
    /// (`forged_attestation_rejected`).
    Attested { contract_hash: [u8; 32] },
}

impl HpresProof {
    /// Whether this kind carries a machine-checked forever-crown (vs. relying on
    /// the runtime gate alone).
    pub fn is_attested(&self) -> bool {
        matches!(self, HpresProof::Attested { .. })
    }

    /// The attested content hash the v12 rotated CARRIER MATERIAL publishes on the AFTER
    /// commitment's `contract_hash8` octet (limbs 96..103) at a hatchery-mint proof site —
    /// `Some` iff a machine-checked forever-crown (`Attested`) is bound, `None` (→ zero octet)
    /// while the crown is merely `Pending`.
    pub fn contract_hash(&self) -> Option<[u8; 32]> {
        match self {
            HpresProof::Attested { contract_hash } => Some(*contract_hash),
            HpresProof::Pending => None,
        }
    }
}

/// A minted cell-KIND: a verified constructor for cells that all carry — and
/// are forever held to — one declared invariant.
///
/// Construct with [`MintedKind::mint`]. The kind is content-addressed by
/// [`MintedKind::kind_id`] (the factory descriptor's hash, which already binds
/// the baked-in invariant constraints), so two kinds with different invariants
/// are different kinds, and a cell cannot claim a kind while carrying a
/// different program.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MintedKind {
    /// The declared invariant — the kind's defining property.
    pub invariant: Invariant,
    /// The content-addressed constructor. Its `state_constraints` are exactly
    /// `invariant.constraints()`; deploying it makes the executor install that
    /// program on every child, and re-evaluate it on every turn.
    pub descriptor: FactoryDescriptor,
    /// The child program every minted cell carries for life (the invariant as a
    /// single `Always`-guarded case). Its canonical VK is `descriptor`'s
    /// `child_program_vk`.
    pub child_program: CellProgram,
    /// The Hatchery attestation (or the named slot for it).
    pub hpres: HpresProof,
}

impl MintedKind {
    /// Mint a new kind from a declared invariant.
    ///
    /// Builds the child program (the invariant as a perpetual `Always` case),
    /// derives its canonical VK, and assembles a [`FactoryDescriptor`] that
    /// bakes the invariant into `state_constraints` AND pins the child VK to the
    /// program that carries them. The descriptor is `Hosted` and unbudgeted by
    /// default; callers wanting a budget / mode override the descriptor after.
    ///
    /// `mint_authority` seeds the factory's own VK (the minting authority's
    /// identity); distinct authorities minting the same invariant produce
    /// distinct factories but — deliberately — the same child program and so the
    /// same enforced invariant.
    pub fn mint(invariant: Invariant, mint_authority: &[u8; 32]) -> Self {
        let constraints = invariant.constraints();
        // The child program IS the invariant: one Always-guarded case carrying
        // the perpetual constraints. Equivalent to `CellProgram::always`.
        let child_program = CellProgram::Cases(vec![TransitionCase {
            guard: TransitionGuard::Always,
            constraints: constraints.clone(),
        }]);
        let child_vk = canonical_program_vk(&child_program);

        let mut factory_vk_hasher = blake3::Hasher::new_derive_key("dregg-minted-kind-factory-v1");
        factory_vk_hasher.update(mint_authority);
        factory_vk_hasher.update(&child_vk);
        let factory_vk = *factory_vk_hasher.finalize().as_bytes();

        let descriptor = FactoryDescriptor {
            factory_vk,
            child_program_vk: Some(child_vk),
            child_vk_strategy: None,
            allowed_cap_templates: vec![],
            field_constraints: vec![],
            // The weld point: the kind's invariant, baked perpetual onto every
            // child. The executor enforces these on every state-modifying turn.
            state_constraints: constraints,
            default_mode: CellMode::Hosted,
            creation_budget: None,
        };

        MintedKind {
            invariant,
            descriptor,
            child_program,
            hpres: HpresProof::Pending,
        }
    }

    /// The content-addressed identity of this kind. Two kinds are the same iff
    /// their descriptors hash equally; the invariant constraints are part of
    /// that hash (`FactoryDescriptor::hash` absorbs `state_constraints`), so the
    /// invariant cannot be silently changed without changing the kind id.
    pub fn kind_id(&self) -> [u8; 32] {
        self.descriptor.hash()
    }

    /// The canonical VK every conforming cell of this kind installs.
    pub fn child_vk(&self) -> [u8; 32] {
        canonical_program_vk(&self.child_program)
    }

    /// Bind a Hatchery forever-crown to this kind (the next slice's API; safe to
    /// call now to record an attestation hash).
    pub fn attest_hpres(mut self, contract_hash: [u8; 32]) -> Self {
        self.hpres = HpresProof::Attested { contract_hash };
        self
    }

    /// The v12 rotated CARRIER MATERIAL a hatchery-mint proof site threads into the AFTER
    /// commitment (STEP-2.5): the `contract_hash8` octet (limbs 96..103) carries this kind's
    /// Hatchery `Attested` content hash, so the honest mint's `state_commit` is NON-ZERO on that
    /// octet — the SAT foundation the STEP-3 `contract_hash8` PI pin publishes. A `Pending` crown
    /// yields the `Default` (zero octet). `child_vk` stays `None` (the factory child-VK octet is a
    /// separate carrier, filled at the factory proof site).
    pub fn carrier_material(&self) -> dregg_cell::commitment::RotationCarrierMaterial {
        dregg_cell::commitment::RotationCarrierMaterial {
            child_vk: None,
            contract_hash: self.hpres.contract_hash(),
        }
    }

    /// Enforce the kind's invariant on a single transition — the GENUINE check.
    ///
    /// This delegates to the very program the executor runs: there is no
    /// separate "mint-layer" enforcement to drift from the kernel. A conforming
    /// transition returns `Ok(())`; a violating one returns
    /// `Err(ProgramError::ConstraintViolated{..})`, the same refusal a validator
    /// reproduces. `old_state == None` is the fresh-cell (creation) case, which
    /// the transition constraints permit (the first write establishes the slot).
    pub fn evaluate_transition(
        &self,
        new_state: &CellState,
        old_state: Option<&CellState>,
    ) -> Result<(), ProgramError> {
        self.child_program.evaluate_with_meta(
            new_state,
            old_state,
            None,
            &TransitionMeta::wildcard(),
        )
    }

    /// **The forge-detector.** Attest that a cell *claiming* this kind actually
    /// conforms: its installed program must carry the kind's invariant
    /// constraints. A cell that claims the kind but installs a program omitting
    /// the invariant is rejected — membership-without-conformance is a forge.
    ///
    /// `claimed_program` is the program the cell installed (what a validator
    /// would re-hash and run). The check is two-pronged:
    ///
    /// 1. **Identity:** the program's canonical VK must equal this kind's child
    ///    VK (so the cell installed *this* kind's program, not a look-alike).
    /// 2. **Containment:** the program's constraint set must contain every one
    ///    of the kind's invariant constraints (a stricter superset is fine — a
    ///    cell may add caveats — but it may not drop the kind's invariant).
    ///
    /// Either failure is a [`ForgeRejection`].
    pub fn attest_membership(&self, claimed_program: &CellProgram) -> Result<(), ForgeRejection> {
        let claimed_vk = canonical_program_vk(claimed_program);
        let kind_vk = self.child_vk();
        if claimed_vk != kind_vk {
            // Containment still salvages a non-identical-but-conforming program
            // (e.g. one that adds extra caveats). Identity is the fast path.
            if !program_contains_constraints(claimed_program, &self.invariant.constraints()) {
                return Err(ForgeRejection::ProgramMissingInvariant {
                    kind_id: self.kind_id(),
                    invariant: self.invariant.label(),
                });
            }
        }
        Ok(())
    }
}

/// Why a claimed-membership attestation was rejected — the forge surfaced.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ForgeRejection {
    /// The cell claimed the kind but its installed program does not carry the
    /// kind's invariant constraints. A forged kind membership.
    ProgramMissingInvariant {
        kind_id: [u8; 32],
        invariant: String,
    },
}

impl std::fmt::Display for ForgeRejection {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ForgeRejection::ProgramMissingInvariant { kind_id, invariant } => write!(
                f,
                "forged kind membership: program does not carry invariant '{}' of kind {:02x}{:02x}…",
                invariant, kind_id[0], kind_id[1]
            ),
        }
    }
}

impl std::error::Error for ForgeRejection {}

/// Does `program`'s constraint set contain every constraint in `needed`?
///
/// Looks across all of a `Cases`/`Predicate` program's constraints. A `None` or
/// `Circuit` program carries no slot constraints and so cannot contain a
/// non-empty `needed` (it is a forge for any invariant-bearing kind).
fn program_contains_constraints(program: &CellProgram, needed: &[StateConstraint]) -> bool {
    let present: Vec<&StateConstraint> = match program {
        CellProgram::Predicate(cs) => cs.iter().collect(),
        CellProgram::Cases(cases) => cases.iter().flat_map(|c| c.constraints.iter()).collect(),
        CellProgram::None | CellProgram::Circuit { .. } => Vec::new(),
    };
    needed.iter().all(|n| present.contains(&n))
}

/// Build a [`CellState`] at the given nonce with one slot set — a test/helper
/// for exercising transitions. Exposed because exercising a `Monotonic` /
/// `FieldGte` invariant needs a state whose nonce is non-zero (so the
/// transition check fires against an `old_state` rather than the creation case).
pub fn state_with_slot(nonce: u64, slot: u8, value: u64) -> CellState {
    let mut s = CellState::new(0);
    s.set_nonce(nonce);
    s.set_field(slot as usize, field_from_u64(value));
    s
}

/// Build a [`CellState`] at the given nonce with one slot set to a raw field.
pub fn state_with_field(nonce: u64, slot: u8, value: FieldElement) -> CellState {
    let mut s = CellState::new(0);
    s.set_nonce(nonce);
    s.set_field(slot as usize, value);
    s
}

#[cfg(test)]
mod tests {
    use super::*;

    const AUTHORITY: [u8; 32] = [7u8; 32];
    const BAL_SLOT: u8 = 0;
    const COUNTER_SLOT: u8 = 1;

    fn balance_kind() -> MintedKind {
        MintedKind::mint(
            Invariant::BalanceNeverBelow {
                slot: BAL_SLOT,
                floor: 0,
            },
            &AUTHORITY,
        )
    }

    fn monotone_kind() -> MintedKind {
        MintedKind::mint(Invariant::MonotoneField { slot: COUNTER_SLOT }, &AUTHORITY)
    }

    // ── The mint: the kind is well-formed and the invariant is baked in. ──

    #[test]
    fn minting_bakes_the_invariant_into_the_descriptor() {
        let kind = balance_kind();
        // The descriptor's perpetual constraints ARE the invariant.
        assert_eq!(
            kind.descriptor.state_constraints,
            kind.invariant.constraints()
        );
        // The child VK pins the program that carries the constraints, so the
        // descriptor self-validates (membership = conformance at the VK level).
        kind.descriptor
            .validate_child_vk_canonical(&kind.child_program)
            .expect("descriptor's child VK must bind its invariant-carrying program");
        // A fresh kind is honestly Pending (no laundered crown).
        assert_eq!(kind.hpres, HpresProof::Pending);
    }

    #[test]
    fn distinct_invariants_are_distinct_kinds() {
        assert_ne!(balance_kind().kind_id(), monotone_kind().kind_id());
    }

    #[test]
    fn same_invariant_same_child_program_across_authorities() {
        let a = MintedKind::mint(Invariant::MonotoneField { slot: COUNTER_SLOT }, &[1u8; 32]);
        let b = MintedKind::mint(Invariant::MonotoneField { slot: COUNTER_SLOT }, &[2u8; 32]);
        // Different minting authorities → different factories…
        assert_ne!(a.descriptor.factory_vk, b.descriptor.factory_vk);
        assert_ne!(a.kind_id(), b.kind_id());
        // …but the SAME enforced invariant (same child program / VK).
        assert_eq!(a.child_vk(), b.child_vk());
    }

    // ── THE BAR: conforming turn succeeds, violating turn is REFUSED. ──

    #[test]
    fn balance_conforming_turn_succeeds() {
        let kind = balance_kind();
        // floor is 0; any non-negative balance conforms. Fresh + later both ok.
        let old = state_with_slot(1, BAL_SLOT, 100);
        let new = state_with_slot(2, BAL_SLOT, 100); // unchanged, still >= 0
        kind.evaluate_transition(&new, Some(&old))
            .expect("a balance >= floor must be admitted");
    }

    #[test]
    fn balance_violating_turn_is_refused() {
        // FieldGte reads the slot as a big-endian u64. The "negative balance"
        // forge: an app that lets the slot wrap below its declared floor. With
        // floor = 50, a transition to 10 violates the invariant.
        let kind = MintedKind::mint(
            Invariant::BalanceNeverBelow {
                slot: BAL_SLOT,
                floor: 50,
            },
            &AUTHORITY,
        );
        let old = state_with_slot(1, BAL_SLOT, 100);
        let new = state_with_slot(2, BAL_SLOT, 10); // below floor 50 → forbidden
        let err = kind
            .evaluate_transition(&new, Some(&old))
            .expect_err("a balance below the floor must be REFUSED by the kernel program");
        assert!(
            matches!(err, ProgramError::ConstraintViolated { .. }),
            "expected a real constraint violation, got {err:?}"
        );
    }

    #[test]
    fn monotone_conforming_turn_succeeds() {
        let kind = monotone_kind();
        let old = state_with_slot(1, COUNTER_SLOT, 5);
        let new = state_with_slot(2, COUNTER_SLOT, 9); // increased → ok
        kind.evaluate_transition(&new, Some(&old))
            .expect("a forward step must be admitted by a monotone kind");
    }

    #[test]
    fn monotone_violating_turn_is_refused() {
        let kind = monotone_kind();
        let old = state_with_slot(1, COUNTER_SLOT, 9);
        let new = state_with_slot(2, COUNTER_SLOT, 4); // decreased → forbidden
        let err = kind
            .evaluate_transition(&new, Some(&old))
            .expect_err("a decrease must be REFUSED by a monotone kind");
        assert!(matches!(err, ProgramError::ConstraintViolated { .. }));
    }

    // ── THE FORGE-DETECTOR: membership-without-conformance is rejected. ──

    #[test]
    fn conforming_cell_passes_membership() {
        let kind = monotone_kind();
        // A cell that installed exactly the kind's program conforms.
        kind.attest_membership(&kind.child_program)
            .expect("a cell carrying the kind's own program is a member");
    }

    #[test]
    fn conforming_superset_program_passes_membership() {
        let kind = monotone_kind();
        // A cell may ADD caveats (here: also write-once a different slot) — as
        // long as it still carries the kind's invariant, it conforms.
        let stricter = CellProgram::Cases(vec![TransitionCase {
            guard: TransitionGuard::Always,
            constraints: vec![
                StateConstraint::Monotonic {
                    index: COUNTER_SLOT,
                },
                StateConstraint::WriteOnce { index: 5 },
            ],
        }]);
        kind.attest_membership(&stricter)
            .expect("a stricter program that still carries the invariant is a member");
    }

    #[test]
    fn forged_membership_is_rejected() {
        let kind = monotone_kind();
        // The forge: a cell CLAIMS the monotone kind but installs a program
        // that does NOT carry the monotone invariant (a different, freer rule).
        let forged = CellProgram::Cases(vec![TransitionCase {
            guard: TransitionGuard::Always,
            constraints: vec![StateConstraint::FieldLte {
                index: COUNTER_SLOT,
                value: field_from_u64(1_000_000),
            }],
        }]);
        let err = kind
            .attest_membership(&forged)
            .expect_err("a cell that drops the invariant must be rejected as a forge");
        assert!(matches!(
            err,
            ForgeRejection::ProgramMissingInvariant { .. }
        ));
    }

    #[test]
    fn empty_program_is_a_forge_for_any_invariant() {
        let kind = balance_kind();
        // A `None` program carries no constraints — it cannot host a member of
        // an invariant-bearing kind.
        let err = kind
            .attest_membership(&CellProgram::None)
            .expect_err("an empty program cannot conform to an invariant-bearing kind");
        assert!(matches!(
            err,
            ForgeRejection::ProgramMissingInvariant { .. }
        ));
    }

    #[test]
    fn forge_that_carries_invariant_under_different_vk_still_conforms() {
        // Robustness: a program that carries the invariant constraint but in a
        // different SHAPE (extra unrelated case) has a different VK, yet the
        // containment check admits it — conformance, not byte-identity, is the
        // bar.
        let kind = monotone_kind();
        let variant = CellProgram::Cases(vec![
            TransitionCase {
                guard: TransitionGuard::Always,
                constraints: vec![StateConstraint::Monotonic {
                    index: COUNTER_SLOT,
                }],
            },
            TransitionCase {
                guard: TransitionGuard::Always,
                constraints: vec![StateConstraint::FieldGte {
                    index: 3,
                    value: field_from_u64(0),
                }],
            },
        ]);
        // Different VK (two cases vs one)…
        assert_ne!(canonical_program_vk(&variant), kind.child_vk());
        // …but conformance via containment.
        kind.attest_membership(&variant)
            .expect("a differently-shaped program that still carries the invariant conforms");
    }

    // ── The hpres slot: the named next slice. ──

    #[test]
    fn attesting_hpres_records_the_crown() {
        let kind = balance_kind().attest_hpres([0xCC; 32]);
        assert!(kind.hpres.is_attested());
        assert_eq!(
            kind.hpres,
            HpresProof::Attested {
                contract_hash: [0xCC; 32]
            }
        );
    }

    /// STEP-2.5: the hatchery-mint CARRIER MATERIAL — an attested kind threads its forever-crown
    /// content hash into the rotated `contract_hash8` octet (NON-ZERO), a `Pending` kind threads the
    /// `Default` (zero octet). The value published is exactly `HpresProof::Attested{contract_hash}`.
    #[test]
    fn attested_kind_carries_the_contract_hash_material() {
        let pending = balance_kind();
        assert_eq!(pending.hpres, HpresProof::Pending);
        let pending_mat = pending.carrier_material();
        assert_eq!(
            pending_mat.contract_hash, None,
            "a Pending crown → zero octet"
        );
        assert_eq!(pending_mat.child_vk, None);

        let attested = balance_kind().attest_hpres([0xC7; 32]);
        let mat = attested.carrier_material();
        assert_eq!(
            mat.contract_hash,
            Some([0xC7; 32]),
            "the attested contract hash rides the carrier material (non-zero octet 96..103)"
        );
        assert_eq!(
            mat.child_vk, None,
            "the hatchery carrier does not fill the factory child-VK octet"
        );
        assert_eq!(attested.hpres.contract_hash(), Some([0xC7; 32]));
    }

    /// The Lean rung: the abstraction-mint invariant is PROVEN, not just
    /// smoke-tested.
    ///
    /// Mirror of the witnesses in `metatheory/Dregg2/Deos/Hatchery.lean`. The Lean
    /// proves: the per-turn gate IS the declared invariant
    /// (`evalStep_admits_iff_*`); an admitted step preserves it (`step_preserves`,
    /// the hpres); the `Verify.Contract.CellContract` carry skeleton lifts that to
    /// the unbounded trajectory (`invariant_forever`); a violating turn is refused
    /// (`violating_*_rejected`); a program omitting the invariant is a forge
    /// (`program_missing_invariant_rejected`); and `HpresProof::Attested` binds to
    /// a machine-checked contract, with an attestation for a *different* invariant
    /// rejected (`forged_attestation_rejected`). Here the SAME shapes are checked
    /// over the deployed `CellProgram::evaluate_with_meta`, so the Rust enforcement
    /// is tied to the proven statement, not an ad-hoc tampering.
    ///
    /// Lean witnesses: balance kind floor 50, slot 0 — `[100]` conforms, `[10]`
    /// (below floor) is refused; monotone kind slot 1 — `5 → 9` conforms, `9 → 4`
    /// (backward) is refused; a wrong/empty program is a forge; an attestation for
    /// the monotone kind does not bind to the balance kind.
    #[test]
    fn invariant_matches_lean_rung() {
        // Lean `balInv := balanceNeverBelow 0 50`.
        let bal = MintedKind::mint(
            Invariant::BalanceNeverBelow {
                slot: BAL_SLOT,
                floor: 50,
            },
            &AUTHORITY,
        );
        // `evalStep_admits_iff_balance` / honest round-trip: slot0 = 100 ≥ 50 → Ok.
        bal.evaluate_transition(
            &state_with_slot(2, BAL_SLOT, 100),
            Some(&state_with_slot(1, BAL_SLOT, 100)),
        )
        .expect("Lean: evalStep balInv [100] = ok");
        // `violating_balance_rejected`: slot0 = 10 < 50 → ConstraintViolated.
        assert!(matches!(
            bal.evaluate_transition(
                &state_with_slot(2, BAL_SLOT, 10),
                Some(&state_with_slot(1, BAL_SLOT, 100)),
            ),
            Err(ProgramError::ConstraintViolated { .. })
        ));

        // Lean `monInv := monotoneField 1`.
        let mon = MintedKind::mint(Invariant::MonotoneField { slot: COUNTER_SLOT }, &AUTHORITY);
        // `evalStep_admits_iff_monotone`: 5 → 9 (forward) → Ok.
        mon.evaluate_transition(
            &state_with_slot(2, COUNTER_SLOT, 9),
            Some(&state_with_slot(1, COUNTER_SLOT, 5)),
        )
        .expect("Lean: evalStep monInv [_,9] (some [_,5]) = ok");
        // `violating_monotone_rejected`: 9 → 4 (backward) → ConstraintViolated.
        assert!(matches!(
            mon.evaluate_transition(
                &state_with_slot(2, COUNTER_SLOT, 4),
                Some(&state_with_slot(1, COUNTER_SLOT, 9)),
            ),
            Err(ProgramError::ConstraintViolated { .. })
        ));

        // `program_missing_invariant_rejected` / `empty_program_is_forge`: a
        // program omitting the kind's invariant constraint is a forge; the empty
        // program is a forge for any invariant-bearing kind.
        assert!(matches!(
            bal.attest_membership(&CellProgram::Cases(vec![TransitionCase {
                guard: TransitionGuard::Always,
                constraints: vec![StateConstraint::Monotonic { index: BAL_SLOT }],
            }])),
            Err(ForgeRejection::ProgramMissingInvariant { .. })
        ));
        assert!(matches!(
            bal.attest_membership(&CellProgram::None),
            Err(ForgeRejection::ProgramMissingInvariant { .. })
        ));
        // `own_program_conforms`: the kind's own program is a member.
        bal.attest_membership(&bal.child_program)
            .expect("Lean: own program conforms");

        // `attest_binds` vs `forged_attestation_rejected`: an attestation binds to
        // its own kind; a kind with a DIFFERENT invariant is a distinct kind — its
        // child VK (the contract-identity the attestation certifies) does not match,
        // so it cannot pass as the balance kind's crown. The content-hash binding.
        assert_ne!(
            bal.child_vk(),
            mon.child_vk(),
            "forged_attestation_rejected: an attestation for monInv != balInv's contract"
        );
        let attested = bal.clone().attest_hpres([0xAB; 32]);
        assert!(attested.hpres.is_attested());
    }
}
