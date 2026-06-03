/-
# Dregg2.CatalogEffects — exhaustive coloring of dregg1's ~52 `Effect` variants onto
# `Spec.Conservation`'s `LinearityClass`, with per-class conservation obligations proved.

Extends `CatalogInstances` (which defines `EffectKind` and `effectLinearity`; this module
opens them, never redefines them):

  * §1 — the six per-class conservation obligations, derived from `Spec.Conservation`'s
    proved classifier facts: Conservative ⇒ paired-sibling; Generative/Annihilative ⇒
    disclosed; Monotonic/Terminal/Neutral ⇒ neither.
  * §2 — per-effect coincidence theorems for all ~52 variants (`rfl` tripwire: coloring
    drift from `Effect::linearity` breaks the matching `rfl`). Grouped by color.
  * §3 — exhaustiveness three ways: `effectLinearity_total` (cases over all 52),
    `every_effect_classified` (paired ⊕ disclosed ⊕ inert), and the bespoke
    `effectObligation` discriminator with `effectObligation_coincides`.

Discipline: no `axiom`/`admit`/`native_decide`/`sorry`. Whole namespace pinned via
`#assert_namespace_axioms Dregg2.CatalogEffects`.
-/
import Dregg2.CatalogInstances
import Dregg2.Spec.Conservation

namespace Dregg2.CatalogEffects

open Dregg2.Spec Dregg2.Spec.LinearityClass
open Dregg2.CatalogInstances (EffectKind effectLinearity)

/-! ## §1 — The six per-class conservation obligations.

Each color's obligation is derived from `Spec.Conservation`'s proved classifiers — the
obligation any effect with that color inherits. Stated over `effectLinearity` so they apply
to the real catalog. -/

section ClassObligations

/-- **Conservative ⇒ paired-sibling Σ=0.** Any effect colored `Conservative` requires a paired
sibling (its per-domain deltas must sum to `0`). Derived from `requires_paired_sibling_iff`. -/
theorem conservative_requires_paired (e : EffectKind)
    (h : effectLinearity e = Conservative) :
    (effectLinearity e).requires_paired_sibling = true := by
  rw [h]; rfl

/-- **Generative ⇒ disclosed non-conservation.** Any effect colored `Generative` legitimately
breaks `Σδ = 0`, but its delta is FORCED into the receipt. Derived from
`is_disclosed_non_conservation_iff`. -/
theorem generative_discloses (e : EffectKind)
    (h : effectLinearity e = Generative) :
    (effectLinearity e).is_disclosed_non_conservation = true := by
  rw [h]; rfl

/-- **Annihilative ⇒ disclosed non-conservation.** Same disclosure obligation as `Generative`
(a burn breaks conservation but discloses the destroyed amount). -/
theorem annihilative_discloses (e : EffectKind)
    (h : effectLinearity e = Annihilative) :
    (effectLinearity e).is_disclosed_non_conservation = true := by
  rw [h]; rfl

/-- **Monotonic ⇒ neither paired nor disclosed.** A monotone counter neither needs a paired
sibling nor is a disclosed non-conservation — its law is "never decreases", lived elsewhere. -/
theorem monotonic_inert (e : EffectKind)
    (h : effectLinearity e = Monotonic) :
    (effectLinearity e).requires_paired_sibling = false ∧
    (effectLinearity e).is_disclosed_non_conservation = false := by
  rw [h]; exact ⟨rfl, rfl⟩

/-- **Terminal ⇒ neither paired nor disclosed.** A one-way transition (revoke/destroy/drop)
carries no conservation delta; its law is irreversibility, not Σ. -/
theorem terminal_inert (e : EffectKind)
    (h : effectLinearity e = Terminal) :
    (effectLinearity e).requires_paired_sibling = false ∧
    (effectLinearity e).is_disclosed_non_conservation = false := by
  rw [h]; exact ⟨rfl, rfl⟩

/-- **Neutral ⇒ neither paired nor disclosed.** Pure book-keeping touches no conserved
quantity in any domain. -/
theorem neutral_inert (e : EffectKind)
    (h : effectLinearity e = Neutral) :
    (effectLinearity e).requires_paired_sibling = false ∧
    (effectLinearity e).is_disclosed_non_conservation = false := by
  rw [h]; exact ⟨rfl, rfl⟩

end ClassObligations

/-! ## §2 — Per-effect coincidence theorems — all ~52 variants.

Each is `effectLinearity .x = <Class>` by `rfl`: if the coloring ever drifts from
`turn/src/action.rs Effect::linearity`, the matching `rfl` breaks the build. Grouped by
color. -/

section PerEffect

/-! ### §2.1 — Conservative (19): paired-delta resource moves (Σδ = 0). -/
theorem c_transfer              : effectLinearity .transfer = Conservative := rfl
theorem c_createEscrow          : effectLinearity .createEscrow = Conservative := rfl
theorem c_releaseEscrow         : effectLinearity .releaseEscrow = Conservative := rfl
theorem c_refundEscrow          : effectLinearity .refundEscrow = Conservative := rfl
theorem c_createCommittedEscrow : effectLinearity .createCommittedEscrow = Conservative := rfl
theorem c_releaseCommittedEscrow: effectLinearity .releaseCommittedEscrow = Conservative := rfl
theorem c_refundCommittedEscrow : effectLinearity .refundCommittedEscrow = Conservative := rfl
theorem c_noteSpend             : effectLinearity .noteSpend = Conservative := rfl
theorem c_noteCreate            : effectLinearity .noteCreate = Conservative := rfl
theorem c_createObligation      : effectLinearity .createObligation = Conservative := rfl
theorem c_fulfillObligation     : effectLinearity .fulfillObligation = Conservative := rfl
theorem c_slashObligation       : effectLinearity .slashObligation = Conservative := rfl
theorem c_queueEnqueue          : effectLinearity .queueEnqueue = Conservative := rfl
theorem c_queueDequeue          : effectLinearity .queueDequeue = Conservative := rfl
theorem c_queueAtomicTx         : effectLinearity .queueAtomicTx = Conservative := rfl
theorem c_queuePipelineStep     : effectLinearity .queuePipelineStep = Conservative := rfl
theorem c_bridgeLock            : effectLinearity .bridgeLock = Conservative := rfl
theorem c_bridgeFinalize        : effectLinearity .bridgeFinalize = Conservative := rfl
theorem c_bridgeCancel          : effectLinearity .bridgeCancel = Conservative := rfl

/-! ### §2.2 — Monotonic (5): scalar counters / refcounts going up. -/
theorem m_incrementNonce        : effectLinearity .incrementNonce = Monotonic := rfl
theorem m_exportSturdyRef       : effectLinearity .exportSturdyRef = Monotonic := rfl
theorem m_enlivenRef            : effectLinearity .enlivenRef = Monotonic := rfl
theorem m_validateHandoff       : effectLinearity .validateHandoff = Monotonic := rfl
theorem m_refusal               : effectLinearity .refusal = Monotonic := rfl

/-! ### §2.3 — Terminal (9): one-way state transitions, no inverse. -/
theorem t_revokeCapability      : effectLinearity .revokeCapability = Terminal := rfl
theorem t_revokeDelegation      : effectLinearity .revokeDelegation = Terminal := rfl
theorem t_dropRef               : effectLinearity .dropRef = Terminal := rfl
theorem t_cellDestroy           : effectLinearity .cellDestroy = Terminal := rfl
theorem t_makeSovereign         : effectLinearity .makeSovereign = Terminal := rfl
theorem t_receiptArchive        : effectLinearity .receiptArchive = Terminal := rfl
theorem t_attenuateCapability   : effectLinearity .attenuateCapability = Terminal := rfl
theorem t_cellSeal              : effectLinearity .cellSeal = Terminal := rfl
theorem t_cellUnseal            : effectLinearity .cellUnseal = Terminal := rfl

/-! ### §2.4 — Generative (11): creates a resource ex nihilo (disclosed non-conservation). -/
theorem g_bridgeMint            : effectLinearity .bridgeMint = Generative := rfl
theorem g_createCell            : effectLinearity .createCell = Generative := rfl
theorem g_createCellFromFactory : effectLinearity .createCellFromFactory = Generative := rfl
theorem g_spawnWithDelegation   : effectLinearity .spawnWithDelegation = Generative := rfl
theorem g_queueAllocate         : effectLinearity .queueAllocate = Generative := rfl
theorem g_queueResize           : effectLinearity .queueResize = Generative := rfl
theorem g_createSealPair        : effectLinearity .createSealPair = Generative := rfl
theorem g_seal                  : effectLinearity .seal = Generative := rfl
theorem g_unseal                : effectLinearity .unseal = Generative := rfl
theorem g_grantCapability       : effectLinearity .grantCapability = Generative := rfl
theorem g_introduce             : effectLinearity .introduce = Generative := rfl

/-! ### §2.5 — Annihilative (1): destroys a resource (disclosed non-conservation). -/
theorem a_burn                  : effectLinearity .burn = Annihilative := rfl

/-! ### §2.6 — Neutral (7): no resource delta; pure book-keeping. -/
theorem n_setField              : effectLinearity .setField = Neutral := rfl
theorem n_emitEvent             : effectLinearity .emitEvent = Neutral := rfl
theorem n_setPermissions        : effectLinearity .setPermissions = Neutral := rfl
theorem n_setVerificationKey    : effectLinearity .setVerificationKey = Neutral := rfl
theorem n_refreshDelegation     : effectLinearity .refreshDelegation = Neutral := rfl
theorem n_pipelinedSend         : effectLinearity .pipelinedSend = Neutral := rfl
theorem n_exerciseViaCapability : effectLinearity .exerciseViaCapability = Neutral := rfl

end PerEffect

/-! ## §3 — Exhaustiveness (no effect uncolored), three ways. -/

section Exhaustiveness

/-- **(a) `effectLinearity_total`** — every effect's color is one of the six. The value
of this proof is the `cases`-exhaustion over all 52 arms — a missing variant would not
type-check. -/
theorem effectLinearity_total (e : EffectKind) :
    effectLinearity e = Conservative ∨ effectLinearity e = Monotonic ∨
    effectLinearity e = Terminal ∨ effectLinearity e = Generative ∨
    effectLinearity e = Annihilative ∨ effectLinearity e = Neutral := by
  cases e <;> simp [effectLinearity]

/-- **(b) `every_effect_classified`** — every effect has a determinate conservation regime
(paired / disclosed / inert), and the first two are mutually exclusive (from
`Spec.Conservation.paired_and_disclosed_exclusive`). -/
theorem every_effect_classified (e : EffectKind) :
    ((effectLinearity e).requires_paired_sibling = true ∧
       (effectLinearity e).is_disclosed_non_conservation = false) ∨
    ((effectLinearity e).requires_paired_sibling = false ∧
       (effectLinearity e).is_disclosed_non_conservation = true) ∨
    ((effectLinearity e).requires_paired_sibling = false ∧
       (effectLinearity e).is_disclosed_non_conservation = false) := by
  cases e <;>
    simp [effectLinearity, LinearityClass.requires_paired_sibling,
          LinearityClass.is_disclosed_non_conservation]

/-- The conserved/disclosed regimes are DISJOINT at EVERY effect — no effect both requires a
paired sibling and is a disclosed non-conservation. Inherited from
`Spec.Conservation.paired_and_disclosed_exclusive`. (Strengthens `CatalogInstances`'
`effect_paired_disclosed_exclusive`, kept here as the local soundness keystone.) -/
theorem effect_regimes_disjoint (e : EffectKind) :
    ¬ ((effectLinearity e).requires_paired_sibling = true ∧
       (effectLinearity e).is_disclosed_non_conservation = true) :=
  LinearityClass.paired_and_disclosed_exclusive (effectLinearity e)

/-- The coloring covers ALL SIX colors — each is witnessed by ≥ 1 effect (so no color is
vacuous and the catalog is genuinely six-way discriminating). The §2 representatives, bundled. -/
theorem effectLinearity_covers_all_colors :
    effectLinearity .transfer = Conservative ∧
    effectLinearity .incrementNonce = Monotonic ∧
    effectLinearity .cellDestroy = Terminal ∧
    effectLinearity .bridgeMint = Generative ∧
    effectLinearity .burn = Annihilative ∧
    effectLinearity .setField = Neutral :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

end Exhaustiveness

/-! ## §4 — The bespoke `LinearityClass` discriminator.

The Guard-triple codegen cannot emit a total map out of `LinearityClass`. `effectObligation`
is hand-written: it maps a color to its conservation obligation as data, and
`effectObligation_coincides` proves — for every effect — that it agrees with the
`Spec.Conservation` primitives. -/

section Discriminator

/-- The conservation regime of a color, AS DATA — the bespoke `LinearityClass` discriminator.
`Paired` = Conservative (Σδ = 0, needs a sibling); `Disclosed` = Generative/Annihilative
(breaks Σ, discloses the delta into the receipt); `Inert` = Monotonic/Terminal/Neutral (no
Σ delta). Exhaustive `match`, NO default arm — a new color cannot compile until it answers. -/
inductive Regime where
  /-- Conservative: paired sibling, Σδ = 0. -/
  | Paired
  /-- Generative/Annihilative: disclosed non-conservation. -/
  | Disclosed
  /-- Monotonic/Terminal/Neutral: no conservation delta. -/
  | Inert
  deriving DecidableEq, Repr

/-- **The discriminator** `LinearityClass → Regime`. Hand-written (the codegen cannot emit a map
OUT of `LinearityClass`); exhaustive, no default arm. -/
def Regime.ofClass : LinearityClass → Regime
  | .Conservative => .Paired
  | .Generative   => .Disclosed
  | .Annihilative => .Disclosed
  | .Monotonic    => .Inert
  | .Terminal     => .Inert
  | .Neutral      => .Inert

/-- Each effect's REGIME — the discriminator composed with the coloring. -/
def effectObligation (e : EffectKind) : Regime := Regime.ofClass (effectLinearity e)

/-- **`Regime.ofClass` coincides with the `Spec` primitives**, by color: `Paired` ⇔
`requires_paired_sibling`, `Disclosed` ⇔ `is_disclosed_non_conservation`, `Inert` ⇔ neither.
This pins the bespoke discriminator to the PROVED `Spec.Conservation` classifiers. -/
theorem ofClass_coincides (c : LinearityClass) :
    (Regime.ofClass c = .Paired ↔ c.requires_paired_sibling = true) ∧
    (Regime.ofClass c = .Disclosed ↔ c.is_disclosed_non_conservation = true) ∧
    (Regime.ofClass c = .Inert ↔
      (c.requires_paired_sibling = false ∧ c.is_disclosed_non_conservation = false)) := by
  cases c <;>
    simp [Regime.ofClass, LinearityClass.requires_paired_sibling,
          LinearityClass.is_disclosed_non_conservation]

/-- **`effectObligation_coincides`** — for EVERY effect, the bespoke discriminator agrees with
the `Spec.Conservation` primitives applied at that effect's color. The catalog-completion
keystone: the dregg1 `Effect::linearity` coloring, run through the hand-written discriminator,
reproduces exactly the conservation obligations `Spec.Conservation` proves. -/
theorem effectObligation_coincides (e : EffectKind) :
    (effectObligation e = .Paired ↔ (effectLinearity e).requires_paired_sibling = true) ∧
    (effectObligation e = .Disclosed ↔
      (effectLinearity e).is_disclosed_non_conservation = true) ∧
    (effectObligation e = .Inert ↔
      ((effectLinearity e).requires_paired_sibling = false ∧
       (effectLinearity e).is_disclosed_non_conservation = false)) :=
  ofClass_coincides (effectLinearity e)

/-- Every effect lands in exactly ONE regime, and the three are pairwise distinct (the
discriminator is a genuine partition of the ~52 effects into Paired ⊔ Disclosed ⊔ Inert). -/
theorem effectObligation_total (e : EffectKind) :
    effectObligation e = .Paired ∨ effectObligation e = .Disclosed ∨
    effectObligation e = .Inert := by
  cases e <;> simp [effectObligation, Regime.ofClass, effectLinearity]

end Discriminator

/-! ## §5 — Axiom-hygiene tripwire (whole-namespace honesty pin).

Every theorem under `Dregg2.CatalogEffects` must rest only on the three kernel axioms.
A `sorryAx` anywhere trips this. Pure rejector; cannot close a goal. -/

#assert_namespace_axioms Dregg2.CatalogEffects

end Dregg2.CatalogEffects
