import Dregg2.Circuit.StateCommit
import Dregg2.Circuit.Poseidon2Binding
import Dregg2.Circuit.Freshness
import Dregg2.Circuit.FinBindsKernel

/-!
# DEBT-B — the injectivity cluster COLLAPSES to a single `Poseidon2SpongeCR`

`CARRIER-CENSUS.md` cluster 2: `compressInjective` / `compressNInjective` / `cellLeafInjective` appear as BARE
HYPOTHESES throughout the state-commitment path. They are NOT a debt — they are collision-resistance, and the
reductions (`Freshness.spongeCompress_inj`, `Poseidon2Binding.compressNInjective_of_poseidon2CR`,
`cellLeafInjective_of_realization`) exist. The one thing that USED to block the collapse was `cellLeafInjective`,
whose `LeafRealization` was an UN-REALIZED carrier (census). R4 (`FinBindsKernel`) CONSTRUCTED it
(`finLeafRealization`, from `encV_injective`).

This file EXHIBITS the collapse: `finCommitSurface` is the DEBT-B state-commitment surface built from a SINGLE
`Poseidon2SpongeCR sponge` — every one of its four injectivity carriers is discharged internally from `hCR`
(the surface's own `.cmbInj`/`.compInj`/`.compNInj`/`.leafInj` fields ARE those reduced proofs), and the leaf
realization is R4's constructed `finLeafRealization`, not a carrier. Its only remaining non-floor input is
`RestHashIffFrameFin RH`, which on the reachable denote-image is a THEOREM
(`FinFrameHash.restHashIffFrame_of_fin`). So on the states that occur, the surface's crypto floor is ONE
`Poseidon2SpongeCR`.

SCOPE: this collapses the DEBT-B state-commitment surface (the `recStateCommit_binds_kernel` path). The
tree-wide injectivity uses on the DEBT-A / AIR / `EffectCommit` paths are a separate mechanical routing, NOT
owned here (CARRIER-CENSUS.md). Residual: `Poseidon2SpongeCR` alone (+ `RestHashIffFrame` on the image).
-/

namespace Dregg2.Circuit.FinInjectivityCollapse

open Dregg2.Circuit.StateCommit
open Dregg2.Circuit.RestFrameFin (FiniteRepresentable RestHashIffFrameFin)
open Dregg2.Circuit.CircuitSoundness (CommitSurface)
open Dregg2.Circuit.Freshness (poseidon2CommitSurface)
open Dregg2.Circuit.FinBindsKernel (CH_fin finLeafRealization CH_fin_injective)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)

/-- **`finCommitSurface`** — the DEBT-B state-commitment surface, resting on `Poseidon2SpongeCR` ALONE for its
injectivity floor. The four injectivity fields are discharged internally from `hCR` (via
`poseidon2CommitSurface`); the leaf realization is R4's constructed `finLeafRealization`, NOT a carrier. The
only remaining input is `RestHashIffFrameFin RH` — and on the reachable denote-image that is a THEOREM
(`FinFrameHash.restHashIffFrame_of_fin`), so on the states that occur this surface's crypto floor is one
`Poseidon2SpongeCR`. -/
def finCommitSurface (sponge : List ℤ → ℤ) (hCR : Poseidon2SpongeCR sponge)
    (RH : Dregg2.Exec.RecordKernelState → ℤ) (hRest : RestHashIffFrameFin RH) : CommitSurface :=
  poseidon2CommitSurface sponge hCR (CH_fin sponge) (finLeafRealization sponge hCR) RH hRest

/-- **THE COLLAPSE — all four `CommitSurface` injectivity carriers hold from ONE `Poseidon2SpongeCR`.** The
surface's own fields witness it: `cmbInj`/`compInj` (2-element sponge), `compNInj` (`compressN = sponge`),
`leafInj` (via the constructed realization). No injectivity carrier is assumed; the sole crypto hypothesis is
`hCR`. (`RestHashIffFrame` is a data condition on the two states, not a crypto carrier.) -/
theorem injectivity_collapses_to_poseidon2CR (sponge : List ℤ → ℤ) (hCR : Poseidon2SpongeCR sponge)
    (RH : Dregg2.Exec.RecordKernelState → ℤ) (hRest : RestHashIffFrameFin RH) :
    compressInjective (finCommitSurface sponge hCR RH hRest).cmb
      ∧ compressInjective (finCommitSurface sponge hCR RH hRest).compress
      ∧ compressNInjective (finCommitSurface sponge hCR RH hRest).compressN
      ∧ cellLeafInjective (finCommitSurface sponge hCR RH hRest).CH :=
  let S := finCommitSurface sponge hCR RH hRest
  ⟨S.cmbInj, S.compInj, S.compNInj, S.leafInj⟩

/-- The surface's leaf-injectivity IS the `hCR`-constructed one — not a free lever. -/
theorem finCommitSurface_leafInj (sponge : List ℤ → ℤ) (hCR : Poseidon2SpongeCR sponge)
    (RH : Dregg2.Exec.RecordKernelState → ℤ) (hRest : RestHashIffFrameFin RH) :
    (finCommitSurface sponge hCR RH hRest).CH = CH_fin sponge := rfl

/-- The surface's `compressN` IS the single sponge. -/
theorem finCommitSurface_compressN (sponge : List ℤ → ℤ) (hCR : Poseidon2SpongeCR sponge)
    (RH : Dregg2.Exec.RecordKernelState → ℤ) (hRest : RestHashIffFrameFin RH) :
    (finCommitSurface sponge hCR RH hRest).compressN = sponge := rfl

/-! ## Teeth — `Poseidon2SpongeCR` is load-bearing for the collapse. -/

/-- **TOOTH (fires).** With a genuine CR sponge, the collapse yields `compressNInjective`. -/
theorem collapse_fires (sponge : List ℤ → ℤ) (hCR : Poseidon2SpongeCR sponge)
    (RH : Dregg2.Exec.RecordKernelState → ℤ) (hRest : RestHashIffFrameFin RH) :
    compressNInjective (finCommitSurface sponge hCR RH hRest).compressN :=
  (injectivity_collapses_to_poseidon2CR sponge hCR RH hRest).2.2.1

/-- **TOOTH (bites).** The collapse hypothesis is load-bearing: the collapsing sponge `fun _ => 0` violates
`Poseidon2SpongeCR` (`collapsing_not_CR`), so the four carriers are not free. -/
theorem collapse_needs_CR : ¬ Poseidon2SpongeCR (fun _ => (0 : ℤ)) :=
  Dregg2.Circuit.FinFrameHash.collapsing_not_CR

#assert_axioms injectivity_collapses_to_poseidon2CR
#assert_axioms finCommitSurface

/-- **THE COLLAPSE, ROUTED THROUGH THE APEX BINDING.** `CommitSurface.commit_binds` — the apex's
kernel-commitment binding — instantiated at `finCommitSurface`. Its FOUR injectivity carriers are internal to
the surface (derived from `hCR`), so this theorem takes NO `compressInjective`/`compressNInjective`/
`cellLeafInjective` hypothesis: equal Poseidon2 commitments force equal kernels, with crypto residual
`Poseidon2SpongeCR` + `RestHashIffFrame` (the latter R4-discharged on the reachable image) + the SATISFIABLE
`AccountsWF` (aligned-default; `finInit_accountsWF`). This is the injectivity cluster COLLAPSED to one floor on
the deployed state-commitment apex path. -/
theorem finCommitSurface_binds (sponge : List ℤ → ℤ) (hCR : Poseidon2SpongeCR sponge)
    (RH : Dregg2.Exec.RecordKernelState → ℤ) (hRest : RestHashIffFrameFin RH)
    (k k' : Dregg2.Exec.RecordKernelState) (t : Dregg2.Exec.Turn)
    (hwf : AccountsWF k) (hwf' : AccountsWF k')
    (hfin : FiniteRepresentable k) (hfin' : FiniteRepresentable k')
    (h : (finCommitSurface sponge hCR RH hRest).commit k t
          = (finCommitSurface sponge hCR RH hRest).commit k' t) :
    k = k' :=
  (finCommitSurface sponge hCR RH hRest).commit_binds k k' t hwf hwf' hfin hfin' h

#assert_axioms finCommitSurface_binds

end Dregg2.Circuit.FinInjectivityCollapse
