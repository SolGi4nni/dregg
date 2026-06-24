/-
# Dregg2.Circuit.Spec.AbstractVerbAdapter — the SHARED adapter behind every per-effect
abstract-verb binding (the unification, factored once).

`SupplyAbstractBinding.lean` (mint/burn) and `TransferAbstractBinding.lean` (transfer) each
hand-built the SAME shape: from a concrete authority gate `g : Bool`, derive a held rights bundle
(`{control}` on accept, `∅` on reject), produce a `control` edge bounded by it, and assemble a `Verb`
whose authority leg is that authorized production and whose value/evidence/state legs are idle. This
module factors that shape ONCE so the remaining ~20 effects bind as THIN instantiations:

  * `heldOfGate g` / `producedOfGate g` — the abstraction function on the authority leg, gate-driven.
  * `gate_covers_production` — THE BRIDGE: `g = true ⟹ AuthorizedProduction (heldOfGate g) (producedOfGate g)`.
  * `stateWriteVerb` — the `delta=0` verb shape (value idle, authority = the gate's production,
    evidence + state idle) shared by every field-write effect.
  * `stateWriteVerb_footprint` — its footprint is `Fpu`, from the bridge.
  * `gateProduction_not_fpu` — the shared mutation tooth (unauthorized amplification is NOT `Fpu`).

The authority leg is the `authConnects ⟹ AuthorizedProduction` law (Miller, `Production.lean §1`)
read off whatever boolean gate the concrete effect uses (`authorizedB`, `stateAuthB`, …). The
NO-AUTHORITY effects (emitEvent — anyone may post on a live cell) instantiate with the gate FORCED
`false`-side-irrelevant: their produced edge is `∅` (an idle authority leg), still `Fpu`.

DISCIPLINE: every lemma `#assert_axioms`'d kernel-clean. This is the meta-law made literally shared:
`Fires = Admission ∧ Footprint-Fpu`, one adapter, instantiated per effect.
-/
import Metatheory.Dynamics.Production

namespace Dregg2.Circuit.Spec.AbstractVerbAdapter

open Dregg2.Resource
open Metatheory.Dynamics
open scoped Dregg2.Resource.ResourceAlgebra

/-- The `control` edge — the smallest non-trivial production a held authority cap confers. -/
def controlEdge : USet Rights := ⟨{Dregg2.Authority.Auth.control}⟩

/-- **`heldOfGate g`** — the abstraction function on the authority leg: an accepting gate (`g = true`)
GRANTS the `{control}` held bundle, a rejecting gate grants `∅` (so an unauthorized actor holds `∅`
and can produce nothing). This is the gate-driven abstraction function shared by every effect. -/
def heldOfGate (g : Bool) : USet Rights :=
  if g = true then controlEdge else ⟨∅⟩

/-- **`gate_covers_production` — THE SHARED BRIDGE, PROVED, kernel-clean.** An accepting gate's
held bundle covers the produced `control` edge: `AuthorizedProduction (heldOfGate true) controlEdge`.
The hypothesis `g = true` is LOAD-BEARING — `heldOfGate false = ∅` covers no `control` edge. This is
the executable image of "only connectivity begets connectivity" (Miller), read off ANY boolean gate. -/
theorem gate_covers_production (g : Bool) (hg : g = true) :
    AuthorizedProduction (heldOfGate g) controlEdge := by
  refine (USet.fits_iff controlEdge (heldOfGate g)).mpr ?_
  simp [heldOfGate, hg, controlEdge]

/-- **`production_footprint_fpu`** — producing `produced` under the held bound `● held` is `Fpu` in
the authority camera whenever it is an `AuthorizedProduction`. The shared authority-leg ontic half. -/
theorem production_footprint_fpu (held produced : USet Rights)
    (hauth : AuthorizedProduction held produced) :
    Fpu (R := Auth (USet Rights))
      (.mk (some held) 0) (.mk (some held) produced) :=
  production_step_fpu USet.add_idem held produced hauth

/-! ## The shared `delta = 0` state-write verb.

Every field-write effect (setField/setVK/setPermissions/setProgram/incrementNonce/makeSovereign/…)
has the SAME footprint shape: NO value move (the value leg idle at total `0`), the authority leg is
the gate's authorized production, evidence + state idle. We give it ONCE, parameterized by the held
and produced rights bundles, so each effect's binding is a thin instantiation. -/

/-- **`stateWriteVerb adm held produced`** — the shared `delta=0` verb: value idle, authority leg
produces `produced` under `● held`, evidence + state idle. setField/setVK/setPermissions/setProgram/
incrementNonce/makeSovereign/receiptArchive/refusal all inhabit this with `held := heldOfGate g`,
`produced := controlEdge`; emitEvent inhabits it with `produced := ⟨∅⟩` (no authority gate). -/
def stateWriteVerb {P : Type} (adm : Admission P) (held produced : USet Rights) :
    Verb P DreggValue DreggAuthority DreggEvidence DreggState where
  admission := adm
  pre  := (.mk (some 0) 0, .mk (some held) 0,        .mk (some ⟨∅⟩) 0, .ex 0)
  post := (.mk (some 0) 0, .mk (some held) produced, .mk (some ⟨∅⟩) 0, .ex 0)

/-- **`stateWriteVerb_footprint`** — the shared state-write footprint is `Fpu`, from the
authorization: value idle (`Fpu.refl`), authority the authorized production, evidence + state idle.
LOAD-BEARING on the authorization (an unauthorized production breaks the authority leg). -/
theorem stateWriteVerb_footprint {P : Type} (adm : Admission P) (held produced : USet Rights)
    (hauth : AuthorizedProduction held produced) :
    Footprint (stateWriteVerb adm held produced) := by
  show Fpu _ _
  refine fpu_prod (Fpu.refl _) (fpu_prod ?_ (fpu_prod (Fpu.refl _) (Fpu.refl _)))
  exact production_footprint_fpu held produced hauth

/-- **`stateWriteVerb_fires`** — the shared firing lemma: an admitting witness + an authorized
production make `stateWriteVerb` FIRE. This is the per-effect refinement's engine — each effect feeds
its gate fact through `gate_covers_production`, this glues it to the admission. -/
theorem stateWriteVerb_fires {P W : Type} [Dregg2.Laws.Verifiable P W]
    (adm : Admission P) (held produced : USet Rights) (w : W)
    (hadm : Admits (P := P) (W := W) adm w)
    (hauth : AuthorizedProduction held produced) :
    Fires (W := W) (stateWriteVerb adm held produced) w :=
  fires_intro (W := W) _ w hadm (stateWriteVerb_footprint adm held produced hauth)

/-- **`stateWrite_preserves_product_validity`** — the shared governance lemma: a fired state-write
verb preserves the product validity of EVERY compatible frame (`kernel_meta_law`). -/
theorem stateWrite_preserves_product_validity {P W : Type} [Dregg2.Laws.Verifiable P W]
    (adm : Admission P) (held produced : USet Rights) (w : W)
    (hadm : Admits (P := P) (W := W) adm w)
    (hauth : AuthorizedProduction held produced)
    (fr : Product DreggValue DreggAuthority DreggEvidence DreggState)
    (hfr : ResourceAlgebra.valid ((stateWriteVerb adm held produced).pre ⊙ fr)) :
    ResourceAlgebra.valid ((stateWriteVerb adm held produced).post ⊙ fr) :=
  kernel_meta_law _ w (stateWriteVerb_fires adm held produced w hadm hauth) fr hfr

/-- **`gateProduction_not_fpu` — THE SHARED MUTATION TOOTH, PROVED, kernel-clean.** Were any binding's
authority leg an UNAUTHORIZED amplification (producing `write` under a held bound of only `read`), it
would NOT be `Fpu` — so no verb built on it could `Fires`. The shared load-bearing tooth: every
per-effect tooth is THIS, specialized. -/
theorem gateProduction_not_fpu :
    ¬ Fpu (R := Auth (USet Rights))
        (.mk (some ⟨{Dregg2.Authority.Auth.read}⟩) 0)
        (.mk (some ⟨{Dregg2.Authority.Auth.read}⟩) ⟨{Dregg2.Authority.Auth.write}⟩) :=
  unauthorized_amplification_not_production

/-- The idle authority production (no gate): the EMPTY produced edge is covered by ANY held bundle —
the binding shape for NO-AUTHORITY effects (emitEvent). An idle authority leg is trivially authorized. -/
theorem idle_authorized_production (held : USet Rights) :
    AuthorizedProduction held (⟨∅⟩ : USet Rights) :=
  ⟨held, by simp [USet.set_inj]⟩

/-! ## The EVIDENCE-growth verb (noteSpend / noteCreate).

Some effects grow the EVIDENCE substance (the spent-nullifier / commitment ∪-monoid, `Auth (USet
Nat)`) rather than producing authority. Spending a nullifier `nf` enlarges the authoritative evidence
element `● ev` to `● (ev + {nf})` — the monotone "once known, never unknown" law (`auth_grow_fpu`).
This is a SEPARATE footprint leg from authority; we give the verb shape that exercises it (value +
authority + state idle, evidence growing). -/

/-- **`evidenceGrowthVerb adm ev grown`** — the evidence-growth verb: value idle, authority idle,
EVIDENCE grows the authoritative element from `● ev` to `● grown`, state idle. noteSpend inhabits it
with `grown := ev + {nf}` (the spent nullifier); noteCreate with the published commitment. -/
def evidenceGrowthVerb {P : Type} (adm : Admission P) (ev grown : USet Nat) :
    Verb P DreggValue DreggAuthority DreggEvidence DreggState where
  admission := adm
  pre  := (.mk (some 0) 0, .mk (some ⟨∅⟩) 0, .mk (some ev) 0,    .ex 0)
  post := (.mk (some 0) 0, .mk (some ⟨∅⟩) 0, .mk (some grown) 0, .ex 0)

/-- **`evidenceGrowthVerb_footprint`** — the evidence-growth footprint is `Fpu`, derived from the
monotone evidence law (`auth_grow_fpu`): value idle, authority idle, evidence GROWS `● ev → ● (ev +
t)` (always `Fpu` — knowledge only enlarges), state idle. `fpu_prod` glues. -/
theorem evidenceGrowthVerb_footprint {P : Type} (adm : Admission P) (ev t : USet Nat) :
    Footprint (evidenceGrowthVerb adm ev (ev + t)) := by
  show Fpu _ _
  refine fpu_prod (Fpu.refl _) (fpu_prod (Fpu.refl _) (fpu_prod ?_ (Fpu.refl _)))
  exact auth_grow_fpu ev t 0

/-- **`evidenceGrowthVerb_fires`** — an admitting witness fires the evidence-growth verb (its
footprint is always `Fpu` — evidence growth is unconditionally monotone). -/
theorem evidenceGrowthVerb_fires {P W : Type} [Dregg2.Laws.Verifiable P W]
    (adm : Admission P) (ev t : USet Nat) (w : W)
    (hadm : Admits (P := P) (W := W) adm w) :
    Fires (W := W) (evidenceGrowthVerb adm ev (ev + t)) w :=
  fires_intro (W := W) _ w hadm (evidenceGrowthVerb_footprint adm ev t)

/-- **`evidenceGrowth_not_fpu` — the evidence mutation tooth, PROVED.** Evidence growth is monotone:
SHRINKING the authoritative element (`● {0} → ● ∅`, forgetting a spent nullifier) is NOT `Fpu` — a
frame holding `{0}` fits `● {0}` but not `● ∅`. So "once known, never unknown" is load-bearing: an
effect cannot un-spend a nullifier. The dual tooth to the authority `gateProduction_not_fpu`. -/
theorem evidenceGrowth_not_fpu :
    ¬ Fpu (R := Auth (USet Nat))
        (.mk (some ⟨{0}⟩) 0) (.mk (some ⟨∅⟩) 0) := by
  intro hF
  have hv : ResourceAlgebra.valid
      ((Auth.mk (some (⟨{0}⟩ : USet Nat)) 0 : Auth (USet Nat)) ⊙ .mk none ⟨{0}⟩) := by
    simp only [ResourceAlgebra.op, ResourceAlgebra.valid, Auth.op, Auth.valid]
    rw [zero_add, USet.fits_iff]
  have hpost := hF (.mk none ⟨{0}⟩) hv
  simp only [ResourceAlgebra.op, ResourceAlgebra.valid, Auth.op, Auth.valid] at hpost
  rw [zero_add, USet.fits_iff] at hpost
  have hmem := hpost (Finset.mem_singleton_self 0)
  simp at hmem

#assert_axioms gate_covers_production
#assert_axioms production_footprint_fpu
#assert_axioms stateWriteVerb_footprint
#assert_axioms stateWriteVerb_fires
#assert_axioms stateWrite_preserves_product_validity
#assert_axioms gateProduction_not_fpu
#assert_axioms idle_authorized_production
#assert_axioms evidenceGrowthVerb_footprint
#assert_axioms evidenceGrowthVerb_fires
#assert_axioms evidenceGrowth_not_fpu

end Dregg2.Circuit.Spec.AbstractVerbAdapter
