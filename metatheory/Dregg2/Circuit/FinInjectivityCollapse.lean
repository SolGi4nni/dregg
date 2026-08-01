import Dregg2.Circuit.StateCommit
import Dregg2.Circuit.Poseidon2Binding
import Dregg2.Circuit.Freshness
import Dregg2.Circuit.FinBindsKernel
import Dregg2.Circuit.StateCommitReduceRaw

/-!
# DEBT-B — the state-commitment surface at the R4-constructed finite leaf

## ⚰ THE COLLAPSE THESIS IS RETIRED (2026-08-01), and this is why

This file used to claim: `CARRIER-CENSUS.md` cluster 2's three injectivity carriers
(`compressInjective` / `compressNInjective` / `cellLeafInjective`) COLLAPSE to a single
`Poseidon2SpongeCR sponge`, exhibited by `finCommitSurface` whose four `CommitSurface` injectivity
FIELDS were all discharged internally from one `hCR`. That was a real reduction and it is now
pointless in BOTH directions:

  * the SOURCE is gone — `CircuitSoundness.CommitSurface`'s four injectivity fields are DELETED, each
    refuted at deployed BabyBear width by pigeonhole (`Verify/ApexPremiseVacuity.lean:177`), so there
    is nothing left to collapse;
  * the TARGET is refuted too — `Poseidon2SpongeCR sponge` is bounded-hash injectivity, and
    `HashFloorHonesty.poseidon2SpongeCR_false_babyBear` refutes it at the deployed width. Reducing
    four false premises to one false premise leaves every theorem downstream vacuous. A collapse is
    only worth stating when its target is SATISFIABLE.

DELETED with the thesis: `injectivity_collapses_to_poseidon2CR` (the four-way conjunction of the
surface's own fields), `finCommitSurface_leafInj` (an `rfl` projection of a deleted field's witness),
`collapse_fires` (its `compressNInjective` corollary). `collapse_needs_CR` survives — it is a
REFUTATION (`¬ Poseidon2SpongeCR (fun _ => 0)`), anti-floor content, and refutations are never
deleted.

## What this file still carries, honestly

`finCommitSurface` is the state-commitment surface at R4's CONSTRUCTED finite leaf
(`FinBindsKernel.CH_fin`, from `encV_injective` — a real serialization, not a carrier) over an
arbitrary sponge. It carries NO crypto floor: its only input beyond the sponge is
`RestHashIffFrameFin RH`, which on the reachable denote-image is a THEOREM
(`FinFrameHash.restHashIffFrame_of_fin`). `finCommitSurface_binds` is the kernel binding at it, in
REDUCTION FORM — equal commitments force equal kernels, OR a concrete collision of one of the four
carriers — so it is valid at the deployed hash rather than vacuously true above it.

SCOPE: the DEBT-B state-commitment surface (the `recStateCommit_binds_kernel` path). The tree-wide
injectivity uses on the DEBT-A / AIR / `EffectCommit` paths are a separate mechanical routing, NOT
owned here (CARRIER-CENSUS.md).
-/

namespace Dregg2.Circuit.FinInjectivityCollapse

open Dregg2.Circuit.StateCommit
open Dregg2.Circuit.RestFrameFin (FiniteRepresentable RestHashIffFrameFin)
open Dregg2.Circuit.CircuitSoundness (CommitSurface)
open Dregg2.Circuit.CollisionReduce (OrBreak)
open Dregg2.Circuit.Freshness (spongeCommitSurface)
open Dregg2.Circuit.FinBindsKernel (CH_fin finLeafRealization CH_fin_injective)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)

/-- **`finCommitSurface`** — the DEBT-B state-commitment surface at R4's CONSTRUCTED finite leaf.
`cmb`/`compress` are 2-element sponge absorbs, `compressN` IS the sponge, `CH` is `CH_fin` (built
from `encV_injective`, not assumed). Its only input beyond the sponge is `RestHashIffFrameFin RH` —
and on the reachable denote-image that is a THEOREM (`FinFrameHash.restHashIffFrame_of_fin`).

⚑ **NO CRYPTO FLOOR (2026-08-01).** It took `hCR : Poseidon2SpongeCR sponge`, whose only job was to
fill the four now-deleted `CommitSurface` injectivity fields through the old
`Freshness.poseidon2CommitSurface`. `Poseidon2SpongeCR` is refuted at deployed BabyBear width, so
carrying it made this surface — and everything stated over it — vacuous at exactly the parameters
that matter. -/
def finCommitSurface (sponge : List ℤ → ℤ)
    (RH : Dregg2.Exec.RecordKernelState → ℤ) (hRest : RestHashIffFrameFin RH) : CommitSurface :=
  spongeCommitSurface sponge (CH_fin sponge) RH hRest

/-- The surface's `CH` IS R4's constructed finite leaf — not a free lever. -/
theorem finCommitSurface_CH (sponge : List ℤ → ℤ)
    (RH : Dregg2.Exec.RecordKernelState → ℤ) (hRest : RestHashIffFrameFin RH) :
    (finCommitSurface sponge RH hRest).CH = CH_fin sponge := rfl

/-- The surface's `compressN` IS the single sponge. -/
theorem finCommitSurface_compressN (sponge : List ℤ → ℤ)
    (RH : Dregg2.Exec.RecordKernelState → ℤ) (hRest : RestHashIffFrameFin RH) :
    (finCommitSurface sponge RH hRest).compressN = sponge := rfl

/-! ## Teeth — the refutation of the retired collapse target stays. -/

/-- **TOOTH (bites).** The collapsing sponge `fun _ => 0` violates `Poseidon2SpongeCR`
(`collapsing_not_CR`). Retained as anti-floor content: the retired collapse's target was a genuine
constraint, and it is ALSO false at deployed width — which is why the collapse was retired rather
than re-proved. -/
theorem collapse_needs_CR : ¬ Poseidon2SpongeCR (fun _ => (0 : ℤ)) :=
  Dregg2.Circuit.FinFrameHash.collapsing_not_CR

#assert_axioms finCommitSurface
#assert_axioms collapse_needs_CR

/-- **THE KERNEL BINDING AT THE CONSTRUCTED SURFACE, IN EXTRACTOR FORM.** Equal commitments force
equal kernels — OR the NAMED residual `CommitColl` holds at exactly those two kernels.
`CommitSurface.commit_binds_or_collides` instantiated at `finCommitSurface`: NO
`compressInjective`/`compressNInjective`/`cellLeafInjective` hypothesis, NO `Poseidon2SpongeCR`, and
the only non-residual obligations are `RestHashIffFrameFin` (R4-discharged on the reachable image) and
the SATISFIABLE `AccountsWF`/`FiniteRepresentable` side conditions.

⚑ Was `finCommitSurface_binds` over `CommitSurface.commit_binds`, which consumed four refuted fields
and was therefore VACUOUSLY TRUE at deployed parameters; then `finCommitSurface_binds_orBreak` over
`commit_binds_orBreak`, whose `OrBreak … .StateBreak` disjunct is FREE at every BabyBear-bounded
sponge (`CommitSurface.orBreak_stateBreak_iff_True`) — vacuous a second time. The residual here names
argument PAIRS, so it discriminates. -/
theorem finCommitSurface_binds_or_collides (sponge : List ℤ → ℤ)
    (RH : Dregg2.Exec.RecordKernelState → ℤ) (hRest : RestHashIffFrameFin RH)
    (k k' : Dregg2.Exec.RecordKernelState) (t : Dregg2.Exec.Turn)
    (hwf : AccountsWF k) (hwf' : AccountsWF k')
    (hfin : FiniteRepresentable k) (hfin' : FiniteRepresentable k')
    (h : (finCommitSurface sponge RH hRest).commit k t
          = (finCommitSurface sponge RH hRest).commit k' t) :
    k = k' ∨ (finCommitSurface sponge RH hRest).CommitColl k k' t :=
  (finCommitSurface sponge RH hRest).commit_binds_or_collides k k' t hwf hwf' hfin hfin' h

/-- The S3 form at the constructed surface. -/
theorem finCommitSurface_binds_of_noColl (sponge : List ℤ → ℤ)
    (RH : Dregg2.Exec.RecordKernelState → ℤ) (hRest : RestHashIffFrameFin RH)
    (k k' : Dregg2.Exec.RecordKernelState) (t : Dregg2.Exec.Turn)
    (hwf : AccountsWF k) (hwf' : AccountsWF k')
    (hfin : FiniteRepresentable k) (hfin' : FiniteRepresentable k')
    (hno : ¬ (finCommitSurface sponge RH hRest).CommitColl k k' t)
    (h : (finCommitSurface sponge RH hRest).commit k t
          = (finCommitSurface sponge RH hRest).commit k' t) :
    k = k' :=
  (finCommitSurface sponge RH hRest).commit_binds_of_noColl k k' t hwf hwf' hfin hfin' hno h

#assert_axioms finCommitSurface_binds_or_collides
#assert_axioms finCommitSurface_binds_of_noColl

end Dregg2.Circuit.FinInjectivityCollapse
