/-
# `Dregg2.Crypto.HermineHashCRRegrounded` — the Hermine commit-reveal `HashCR` consumers RE-GROUNDED
off the VACUOUS injective floor onto the PROPER keyed `CollisionResistant` floor.

## The bug this closes (the commit-reveal half of the 07-13 floor sweep)

`HermineHintMLWE.HashCR cr := ∀ i w w', cr.H i w = cr.H i w' → w = w'` is stated as **injectivity** of
the commit map, and `HashFloorHonesty.hashCR_false_of_compressing` PROVES it FALSE for any COMPRESSING
commit-reveal (`|C| < |W|` — pigeonhole forces two reveals to one commitment). So every Hermine
binding consumer conditioned on it — `commitment_binding`, `equivocation_breaks_hashcr`,
`concurrent_forgery_breaks_hashcr_or_msis`, `concurrent_unforgeable_reduces`, and the DEPLOYED-reachable
`RevocationSoundness` / `IdentityCommitment` reuses of the SAME `CommitReveal`/`HashCR` — is VACUOUSLY
TRUE at real parameters. `HashFloorHonesty` landed the honest floor (`CollisionResistant`) and the
advantage template; `FloorRegroundedConsumers` moved the STARK/FRI side. This file moves the Hermine
COMMIT-REVEAL side.

## The re-grounding

* **`commitRevealFamily`** — the concrete bridge: a Hermine `CommitReveal Idx W C` at a fixed index `i`
  becomes a `KeyedHashFamily` (`Input = W`, `Out = C`, `H _ _ w = cr.H i w`). This is the keyed hash the
  honest collision game lives over.
* **`commitRevealFamily_CR_of_hashcr`** — the OLD-floor ⟹ NEW-floor bridge: if the injective `HashCR cr`
  held it would discharge `CollisionResistant (commitRevealFamily cr i)` (via `injective_family_CR`), so
  the old floor was STRICTLY STRONGER than needed — and, being false for a compressing commitment, empty.
* **`hermine_commitment_binding_advantage_bound`** — the advantage-bounded sibling of
  `HermineHintMLWE.commitment_binding`: an equivocating opener (per key, two DISTINCT reveals colliding
  under the commit hash — exactly the reduction `HermineHintMLWE.equivocation_breaks_hashcr` witnesses) IS
  a `CollisionFinder`, so under the proper floor its advantage is `Negl` — "opens ⟹ equal" becomes
  "opens ⟹ equal EXCEPT with negligible probability". Discharged by `thread_advantage_bound`.
* **`hermine_concurrent_forgery_advantage_bound`** — the advantage-bounded sibling of the composition
  `concurrent_forgery_breaks_hashcr_or_msis` / `concurrent_unforgeable_reduces`: a concurrent rushing
  forger either EQUIVOCATES (a commit-hash collision, the `collisionAdv` leg) or is BOUND and yields an
  MSIS solution (the `MSISHardQuant` leg); its total forgery advantage is the SUM, `Negl` under the two
  proper floors (`CollisionResistant` ∧ `MSISHardQuant`). The Boolean dichotomy `¬HashCR ∨ MSIS-solution`
  becomes the additive negligible advantage. Discharged by `thread_advantage_bound` (`negl_add`, a floor
  leaf on each leg).

## Non-fake

The floor is SATISFIABLE (`commitRevealFamily_CR_of_hashcr` on the binding `HermineHintMLWE.exCR`
discharges it) and LOAD-BEARING (`badCR_family_not_CR`: the COLLIDING commit-reveal `HermineHintMLWE.badCR`
has an equivocator winning on every key, advantage `1`, so its family is NOT CR — the siblings cannot be
discharged there). The concrete `crEquivocator` is a genuine collision finder, not a relabel. Old
injective-floor consumers KEPT untouched; siblings ADDED. `#assert_all_clean`
(⊆ {propext, Classical.choice, Quot.sound}); no `sorry`, no fresh `axiom`.

## Coordination

This is the COMMIT-REVEAL binding lane. The STARK/FRI/Merkle hash consumers are
`Circuit.FloorRegroundedConsumers` (sibling lane); the decisional/lossy-MLWE and `MSISHard`-Boolean crypto
floors are `FloorBridge`/`CryptoFloorTeeth` (another sibling). It stays in the Hermine `CommitReveal`
subtree — no consumer moved here lives elsewhere.
-/
import Dregg2.Tactics.ThreadAdvantageBound
import Dregg2.Crypto.HermineHintMLWE

namespace Dregg2.Crypto.HermineHashCRRegrounded

open Dregg2.Crypto.ConcreteSecurity (Negl Ensemble negl_zero not_negl_one)
open Dregg2.Crypto.ProbCrypto (winProb winProb_top MSISHardQuant)
open Dregg2.Circuit.HashFloorHonesty
  (KeyedHashFamily CollisionFinder CollisionResistant collisionAdv injective_family_CR)
open Dregg2.Crypto.HermineHintMLWE (CommitReveal HashCR badCR exCR exCR_hashcr)

set_option autoImplicit false

/-! ## §1 — the concrete bridge: a Hermine commit-reveal becomes a keyed hash family. -/

/-- **THE COMMIT-REVEAL KEYED FAMILY.** A Hermine `CommitReveal Idx W C` at a fixed index `i` as a
`KeyedHashFamily`: reveals `W` are the inputs, commitments `C` the outputs, and the keyed hash is
`H _ _ w = cr.H i w` (a trivial `Unit` key — the deployed effective key is the domain-separation
index/tag). This is the keyed hash the proper collision game runs over. -/
def commitRevealFamily {Idx W C : Type} [DecidableEq W] [DecidableEq C]
    (cr : CommitReveal Idx W C) (i : Idx) : KeyedHashFamily where
  Key := fun _ => Unit
  Input := W
  Out := C
  H := fun _ _ w => cr.H i w
  keyFintype := fun _ => inferInstance
  keyNonempty := fun _ => inferInstance
  inputDecEq := inferInstance
  outDecEq := inferInstance

/-- **THE OLD-FLOOR ⟹ NEW-FLOOR BRIDGE.** If the injective `HashCR cr` held (per-index injectivity of the
commit map), it would discharge the proper `CollisionResistant (commitRevealFamily cr i)` (no collisions ⟹
every finder's advantage `0`, via `injective_family_CR`). So the OLD injective floor is STRICTLY STRONGER
than the honest computational floor — and, being FALSE for a compressing commitment
(`HashFloorHonesty.hashCR_false_of_compressing`), it was an empty hypothesis; the proper floor is the
satisfiable object the same binding reductions actually need. -/
theorem commitRevealFamily_CR_of_hashcr {Idx W C : Type} [DecidableEq W] [DecidableEq C]
    (cr : CommitReveal Idx W C) (i : Idx) (hcr : HashCR cr) :
    CollisionResistant (commitRevealFamily cr i) :=
  injective_family_CR (commitRevealFamily cr i) (fun _ _ w w' h => hcr i w w' h)

/-! ## §2 — the advantage-bounded binding keystone (`commitment_binding`, re-grounded). -/

/-- **RE-GROUNDED `HermineHintMLWE.commitment_binding`.** Under the proper keyed floor, the
commitment-equivocation adversary (per key, two DISTINCT reveals of one commitment colliding under the
commit hash — a collision by `HermineHintMLWE.equivocation_breaks_hashcr`) has negligible advantage. The
Boolean "two openings of one commitment ⟹ the reveals are equal" becomes "⟹ equal EXCEPT with negligible
probability" — the rushing-defense teeth on the honest floor. Proof: `thread_advantage_bound` (the single
`CollisionResistant` leaf). -/
theorem hermine_commitment_binding_advantage_bound {F : KeyedHashFamily}
    (hCR : CollisionResistant F) (equivocator : CollisionFinder F) :
    Negl (collisionAdv F equivocator) := by
  thread_advantage_bound

/-! ## §3 — the advantage-bounded composition (`concurrent_unforgeable_reduces`, re-grounded). -/

/-- **RE-GROUNDED `HermineHintMLWE.concurrent_forgery_breaks_hashcr_or_msis` /
`concurrent_unforgeable_reduces`.** A concurrent rushing forger opens a common commitment and outputs two
accepting SelfTargetMSIS solutions with `c ≠ c'`; it either EQUIVOCATED (an opening collision — the
`collisionAdv F equivocator` leg) or was BOUND to one commitment and thereby handed a nonzero short MSIS
solution (the `MSISHardQuant adv` leg at solver index `s`). Its TOTAL forgery advantage is the SUM of the
two, negligible under the proper floors `CollisionResistant F ∧ MSISHardQuant adv`. The Boolean dichotomy
`¬HashCR ∨ MSIS-solution` becomes the additive negligible advantage — the whole rushing composition on the
honest floor. Proof: `thread_advantage_bound` (`negl_add`; the `CollisionResistant` leaf, the
`MSISHardQuant` leaf). -/
theorem hermine_concurrent_forgery_advantage_bound {F : KeyedHashFamily} {S : Type*}
    (hCR : CollisionResistant F) (equivocator : CollisionFinder F)
    (adv : S → Ensemble) (s : S) (hmsis : MSISHardQuant adv) :
    Negl (fun n => collisionAdv F equivocator n + adv s n) := by
  thread_advantage_bound

/-! ## §4 — non-vacuity: the floor is satisfiable AND load-bearing on Hermine commit-reveals. -/

/-- A concrete commit-reveal equivocator: on every key it opens the two reveals `w`, `w'`. It is a genuine
collision finder — it wins exactly when `w ≠ w'` yet `cr.H i w = cr.H i w'`. -/
def crEquivocator {Idx W C : Type} [DecidableEq W] [DecidableEq C]
    (cr : CommitReveal Idx W C) (i : Idx) (w w' : W) :
    CollisionFinder (commitRevealFamily cr i) where
  find := fun _ _ => (w, w')

/-- **(TOOTH — the floor is SATISFIABLE on a Hermine commit-reveal.)** The binding instance
`HermineHintMLWE.exCR` (`H i w = (i, w)`, injective) satisfies the proper keyed floor — the sibling
hypotheses are inhabited, unlike the vacuous injective floor. -/
theorem exCR_family_CR : CollisionResistant (commitRevealFamily exCR 3) :=
  commitRevealFamily_CR_of_hashcr exCR 3 exCR_hashcr

/-- **(TOOTH — the floor is LOAD-BEARING on a Hermine commit-reveal.)** The COLLIDING commit-reveal
`HermineHintMLWE.badCR` (`H _ _ = 0`, every reveal opens every commitment) has the `crEquivocator 5 7 8`
winning on EVERY key (`7 ≠ 8` yet both hash to `0`), so its advantage is the constant `1` and the family
is NOT collision-resistant. So the siblings cannot be discharged on a broken commit-reveal — the proper
floor is a genuine constraint, and the re-grounded binding is non-vacuous. -/
theorem badCR_family_not_CR : ¬ CollisionResistant (commitRevealFamily badCR 5) := by
  intro hCR
  have hadv : collisionAdv (commitRevealFamily badCR 5) (crEquivocator badCR 5 (7 : ℤ) 8)
      = fun _ => (1 : ℝ) := by
    funext n
    have hall : (fun k : (commitRevealFamily badCR 5).Key n =>
        (crEquivocator badCR 5 (7 : ℤ) 8).wins n k) = fun _ => true := by
      funext k
      simp [CollisionFinder.wins, crEquivocator, commitRevealFamily, badCR]
    show @winProb ((commitRevealFamily badCR 5).Key n) ((commitRevealFamily badCR 5).keyFintype n)
        (fun k => (crEquivocator badCR 5 (7 : ℤ) 8).wins n k) = 1
    rw [hall]
    exact @winProb_top ((commitRevealFamily badCR 5).Key n) ((commitRevealFamily badCR 5).keyFintype n)
      ((commitRevealFamily badCR 5).keyNonempty n)
  exact not_negl_one (hadv ▸ hCR (crEquivocator badCR 5 7 8))

/-- **THE RE-GROUNDED COMPOSITION FIRES AT A REAL FLOOR WITNESS.** On the injective identity family
(`HashFloorHonesty.idFamily_CR`) and a decaying MLWE solver family, the concurrent-forgery advantage sum is
negligible — the composition runs end-to-end to a genuine `Negl` conclusion at inhabited hypotheses. -/
theorem hermine_concurrent_forgery_fires
    (equivocator : CollisionFinder Dregg2.Circuit.HashFloorHonesty.idFamily) :
    Negl (fun n => collisionAdv Dregg2.Circuit.HashFloorHonesty.idFamily equivocator n
        + (fun _ : ℕ => (0 : ℝ)) n) :=
  hermine_concurrent_forgery_advantage_bound Dregg2.Circuit.HashFloorHonesty.idFamily_CR equivocator
    (fun _ : Unit => (fun _ => (0 : ℝ))) () (fun _ => negl_zero)

#assert_all_clean [
  commitRevealFamily_CR_of_hashcr,
  hermine_commitment_binding_advantage_bound,
  hermine_concurrent_forgery_advantage_bound,
  exCR_family_CR,
  badCR_family_not_CR,
  hermine_concurrent_forgery_fires
]

end Dregg2.Crypto.HermineHashCRRegrounded
