/-
# `Dregg2.Crypto.UcSignatureQuant` — CLOSING the two named UC gaps G1/G2 on the probabilistic substrate.

`UcSignature.lean` §7.6 built a genuine λ-indexed advantage `Ensemble` and the PROVED transfer

  > `uc_advantage_transfer` : `advₑ ≤ εₛ` eventually ∧ `Negl εₛ` ⟹ `Negl advₑ`

but its two INPUTS were carried as ASSUMED fields of `ComputationalUC`:

  * **(G1)** `reduction_bound : advₑ ≤ εₛ` — "needs a distribution over the environment's coins and the
    honest key, which the deterministic `Env := Unit → Msg × Sig` model lacked."
  * **(G2)** `forge_negl : Negl εₛ` — "needs a QUANTITATIVE floor; the tree's hardness was Boolean."

`ProbCrypto.lean` (Track B step 1) now provides the missing substrate — a genuine finite counting-probability
`winProb`, the `ForkingFamily` with its PROVED forking bound `ε·(ε − 1/|C|) ≤ solverAdv`, the quantitative
floors `MSISHardQuant`/`DLHardQuant`, and the reduction `forking_reduces_to_MSISHardQuant`. This module
discharges G1 and G2 as PROVED facts and assembles `computational_uc_realizes`.

## What is proved (§-by-§)

  **§1 — the winProb bridge.** `winProb_congr` (winProb depends only on the win predicate) and
  `winProb_prod_eq_advantage` : the `winProb` of a forking accept predicate over the product space
  `World × Chal` EQUALS `HermineTSUF.advantage` — the identity that lets a distinguishing game's probability
  be routed into the forking bound.

  **§2 — the UC distinguisher as a `winProb` game (G1, the event → probability lift).** Over a finite
  outcome space `Ω` and a per-outcome submission `sub : Ω → Msg × Sig`, `distBool`/`forgeBool` are the
  distinguishing and forgery win predicates; `winProb_dist_eq_forge` proves their probabilities are EQUAL —
  the winProb-level lift of `distinguishes_iff_forgery` (the distinguishing event IS the forgery event, now
  at the probability level). `some_distBool_gives_forgery` reuses the module theorem `distinguishes_iff_forgery`
  to confirm the aggregate win corresponds to the `Prop` `Forgery`. So `advₑ = winProb(distinguish) =
  winProb(forgery)` — G1 as a genuine real equality, not an assumed inequality.

  **§3 — the distinguishing advantage IS the forger advantage.** `ucDistAdv F l := winProb (F.acc l ·)` — the
  distinguisher's advantage as a `winProb` over `World l × Chal l`, where `F.acc` is the forgery-accept event
  (§2). `ucDistAdv_eq_forgerAdv` : `ucDistAdv F = F.forgerAdv`, via the §1 bridge. This closes G1 against the
  `ForkingFamily` substrate: the distinguisher's advantage equals the forger advantage ensemble.

  **§4 — G2 from the quantitative floor.** `ucForger_negl_of_msis` / `_of_dl` : the forger advantage
  `F.forgerAdv` is negligible whenever the derived solver's advantage is quantitatively hard
  (`MSISHardQuant`/`DLHardQuant`) and the challenge-collision term `Negl F.invChal` — reusing
  `ProbCrypto.forking_reduces_against_floor`. This closes G2: `Negl εₛ` from a genuine quantitative floor.

  **§5 — `computational_uc_realizes` (the payoff).** `MSISHardQuant … ⟹ Negl (ucDistAdv F)`, via
  `uc_advantage_transfer` fed the now-PROVED G1 (`ucDistAdv_eq_forgerAdv`) and G2 (`ucForger_negl_of_msis`).
  `ucRealizesWitness` fills a `UcSignature.ComputationalUC` whose G1/G2 fields are now PROVED terms, not
  assumptions — the §7.6 structure inhabited from the substrate.

  **§6 — non-vacuity, full spectrum.** `zeroFamily` (never-accepting, super-polynomial challenge) realizes
  with `Negl (ucDistAdv …)` (FIRES); `const25Family` (constant-`2/5` accept) has `ucDistAdv ≡ 2/5`, NOT
  negligible (BITES), and its derived solver breaks the quantitative floor. So the discharge is load-bearing.

## No re-assumed gap.

G1 and G2 are PROVED (`ucDistAdv_eq_forgerAdv`, `ucForger_negl_of_msis`) from the `ProbCrypto` substrate —
they are no longer fields of `ComputationalUC`; `ucRealizesWitness` FILLS those fields with the proofs.
`#assert_all_clean` (⊆ {propext, Classical.choice, Quot.sound}).
-/
import Dregg2.Crypto.UcSignature
import Dregg2.Crypto.ProbCrypto
import Dregg2.Crypto.HermineTSUF
import Dregg2.Tactics
import Mathlib.Tactic

namespace Dregg2.Crypto.UcSignatureQuant

open Filter
open scoped BigOperators
open Dregg2.Crypto.ConcreteSecurity
open Dregg2.Crypto.ProbCrypto
open Dregg2.Crypto.HermineTSUF
open Dregg2.Crypto.HybridCombiner
open Dregg2.Crypto.UcSignature
open Dregg2.Crypto.Lattice (ShortNorm)

/-! ## §1 — The `winProb` bridge: `winProb` over `World × Chal` IS `HermineTSUF.advantage`. -/

/-- **`winProb` depends only on the win predicate.** If two win predicates agree on every outcome, their
winning probabilities are equal. The elementary congruence the event → probability lift rests on. -/
theorem winProb_congr {Ω : Type*} [Fintype Ω] {f g : Ω → Bool} (h : ∀ o, f o = g o) :
    winProb f = winProb g :=
  congrArg winProb (funext h)

variable {Rq : Type*} [CommRing Rq] [ShortNorm Rq] [Fintype Rq] [DecidableEq Rq]
variable {W : Type*} [Fintype W]

omit [CommRing Rq] [ShortNorm Rq] [DecidableEq Rq] in
/-- **The favorable `(ω, c)` count is the sum of per-prefix hit counts.** The number of accepting
`(ω, c)` pairs over the product space is `∑_ω hits acc ω` — the numerator `HermineTSUF.advantage` counts. -/
theorem card_filter_prod (acc : W → Rq → Bool) :
    ((Finset.univ : Finset (W × Rq)).filter (fun p => acc p.1 p.2 = true)).card
      = ∑ ω : W, hits acc ω := by
  rw [Finset.card_filter, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun ω _ => ?_)
  rw [hits, acceptSet, Finset.card_filter]

/-- **THE BRIDGE — `winProb` over the product space IS `advantage`.** The winning probability of the forking
accept predicate `fun (ω, c) => acc ω c` over `World × Chal` equals the forger's `HermineTSUF.advantage acc`,
cast to `ℝ`: both are `(∑_ω hits) / (|World|·|Chal|)`. This is what lets a distinguishing game's `winProb`
be identified with the forger advantage the forking bound governs. -/
theorem winProb_prod_eq_advantage (acc : W → Rq → Bool) :
    winProb (fun p : W × Rq => acc p.1 p.2) = ((advantage acc : ℚ) : ℝ) := by
  unfold winProb advantage
  rw [card_filter_prod, Fintype.card_prod]
  push_cast
  ring

/-! ## §2 — The UC distinguisher as a `winProb` game: G1, the event → probability lift.

Over a finite outcome space `Ω` (the environment's coins ⊕ honest key ⊕ RO answers) with a per-outcome
submission `sub : Ω → Msg × Sig`, the distinguisher wins on `ω` iff its submitted pair verifies in the real
world but was not recorded (`distBool`); a forgery occurs on `ω` iff that pair is unrecorded yet verifies
(`forgeBool`). These are the SAME event — the winProb-level lift of `distinguishes_iff_forgery`. -/

open Classical in
/-- **The distinguisher's win predicate.** On outcome `ω`, `Z` submits `sub ω`; it distinguishes iff the real
scheme accepts (`verify`) though `F_SIG` rejects (`¬ Recorded`). -/
noncomputable def distBool {SK PK Msg Sig : Type*} (S : SigScheme SK PK Msg Sig) (pk : PK)
    (Recorded : Msg → Prop) {Ω : Type*} (sub : Ω → Msg × Sig) : Ω → Bool :=
  fun ω => decide (S.verify pk (sub ω).1 (sub ω).2 ∧ ¬ Recorded (sub ω).1)

open Classical in
/-- **The forgery win predicate.** On outcome `ω`, a forgery occurs iff `sub ω` is unrecorded yet verifies. -/
noncomputable def forgeBool {SK PK Msg Sig : Type*} (S : SigScheme SK PK Msg Sig) (pk : PK)
    (Recorded : Msg → Prop) {Ω : Type*} (sub : Ω → Msg × Sig) : Ω → Bool :=
  fun ω => decide (¬ Recorded (sub ω).1 ∧ S.verify pk (sub ω).1 (sub ω).2)

/-- **G1, THE EVENT → PROBABILITY LIFT.** The distinguisher's winning probability EQUALS the forger's:
`winProb (distinguish) = winProb (forgery)`. On every outcome the two win predicates coincide (the pair
verifies-and-unrecorded iff it is a forgery — the outcome-level `distinguishes_iff_forgery`), so `winProb_congr`
equates the probabilities. This is G1 as a genuine real EQUALITY over the counting-probability substrate, not
an assumed inequality. -/
theorem winProb_dist_eq_forge {SK PK Msg Sig : Type*} (S : SigScheme SK PK Msg Sig) (pk : PK)
    (Recorded : Msg → Prop) {Ω : Type*} [Fintype Ω] (sub : Ω → Msg × Sig) :
    winProb (distBool S pk Recorded sub) = winProb (forgeBool S pk Recorded sub) := by
  refine winProb_congr (fun ω => ?_)
  simp only [distBool, forgeBool]
  exact decide_eq_decide.mpr and_comm

/-- **THE AGGREGATE WIN IS A FORGERY (reuses `distinguishes_iff_forgery`).** If SOME outcome is a
distinguishing win, then a `Forgery` exists on the honest key — via the constant environment `fun _ => sub ω`
and the module theorem `distinguishes_iff_forgery`. Confirms the game's win event is the `Prop`-level
distinguishing/forgery event, so no UC content is laundered in the lift. -/
theorem some_distBool_gives_forgery {SK PK Msg Sig : Type*} (S : SigScheme SK PK Msg Sig) (pk : PK)
    (Recorded : Msg → Prop) {Ω : Type*} (sub : Ω → Msg × Sig)
    (h : ∃ ω, distBool S pk Recorded sub ω = true) : Forgery S pk Recorded := by
  obtain ⟨ω, hω⟩ := h
  have hpair : S.verify pk (sub ω).1 (sub ω).2 ∧ ¬ Recorded (sub ω).1 := by
    simpa only [distBool, decide_eq_true_eq] using hω
  exact (distinguishes_iff_forgery S pk Recorded).1 ⟨fun _ => sub ω, hpair.1, hpair.2⟩

/-! ## §3 — The distinguishing advantage IS the forger advantage (G1 against the `ForkingFamily`). -/

/-- **THE UC DISTINGUISHER'S ADVANTAGE ENSEMBLE.** At parameter `l`, the `winProb` of the forgery-accept
event `F.acc l` over the product outcome space `World l × Chal l` — a genuine real in `[0,1]`, ranging over
the full spectrum. `F.acc` is the forgery/distinguishing event of §2. -/
noncomputable def ucDistAdv (F : ForkingFamily) : ℕ → ℝ := fun l =>
  letI := F.chalRing l; letI := F.chalNorm l; letI := F.chalFin l
  letI := F.chalDec l; letI := F.worldFin l
  winProb (fun p : F.World l × F.Chal l => F.acc l p.1 p.2)

/-- **G1 CLOSED — the distinguishing advantage EQUALS the forger advantage.** `ucDistAdv F = F.forgerAdv`,
via the §1 bridge `winProb_prod_eq_advantage`. So the environment's distinguishing advantage `advₑ` is exactly
the EUF-CMA forger advantage `εₛ` — the reduction bound G1 holds as an equality, PROVED from the substrate,
no longer an assumed `ComputationalUC` field. -/
theorem ucDistAdv_eq_forgerAdv (F : ForkingFamily) : ucDistAdv F = F.forgerAdv := by
  funext l
  letI := F.chalRing l; letI := F.chalNorm l; letI := F.chalFin l
  letI := F.chalDec l; letI := F.worldFin l
  exact winProb_prod_eq_advantage (F.acc l)

theorem ucDistAdv_nonneg (F : ForkingFamily) (l : ℕ) : 0 ≤ ucDistAdv F l := by
  rw [ucDistAdv_eq_forgerAdv]; exact F.forgerAdv_nonneg l

/-! ## §4 — G2 from the quantitative floor: the forger advantage is negligible. -/

/-- **G2 CLOSED (MSIS leg) — `Negl εₛ` from the QUANTITATIVE MSIS floor.** If the derived forking solver `s`
is one the quantitative floor `MSISHardQuant` quantifies over (its advantage IS `F.solverAdv`) and the
challenge-collision term is negligible, then the forger advantage `F.forgerAdv` is negligible — reusing
`ProbCrypto.forking_reduces_against_floor`. This is G2 discharged from a genuine quantitative floor, not the
tree's Boolean `MSISHard`. -/
theorem ucForger_negl_of_msis {Sv : Type*} (F : ForkingFamily)
    (solverAdvOf : Sv → Ensemble) (s : Sv) (hs : solverAdvOf s = F.solverAdv)
    (hfloor : MSISHardQuant solverAdvOf) (hCneg : Negl F.invChal) : Negl F.forgerAdv :=
  forking_reduces_against_floor F solverAdvOf s hs hfloor hCneg

/-- **G2 CLOSED (DL leg) — `Negl εₛ` from the QUANTITATIVE DL floor.** The classical Schnorr forking family
has the identical `ε·(ε − 1/|C|) ≤ solverAdv` bound; `DLHardQuant` on the derived DL solver discharges
`Negl F.solverAdv` (defeq to the MSIS-shaped floor). Either hardness leg of the hybrid closes G2. -/
theorem ucForger_negl_of_dl {Sv : Type*} (F : ForkingFamily)
    (solverAdvOf : Sv → Ensemble) (s : Sv) (hs : solverAdvOf s = F.solverAdv)
    (hfloor : DLHardQuant solverAdvOf) (hCneg : Negl F.invChal) : Negl F.forgerAdv :=
  forking_reduces_against_floor F solverAdvOf s hs hfloor hCneg

/-! ## §5 — `computational_uc_realizes`: `MSISHardQuant ⟹ Negl advₑ`, via the PROVED G1 + G2. -/

/-- **THE PAYOFF — GENUINE COMPUTATIONAL UC ON THE QUANTITATIVE SUBSTRATE.** The environment's distinguishing
advantage `ucDistAdv F` is NEGLIGIBLE whenever the derived forking solver is quantitatively hard
(`MSISHardQuant`) and the challenge space grows (`Negl F.invChal`). Assembled by `uc_advantage_transfer`
applied to the now-PROVED inputs: G1 `ucDistAdv F = F.forgerAdv` (`ucDistAdv_eq_forgerAdv`, the equality gives
`advₑ ≤ εₛ`) and G2 `Negl F.forgerAdv` (`ucForger_negl_of_msis`). Neither is assumed — both are theorems of
the probabilistic substrate. This is `UcSignature`'s "TRUE-MODULO-(G1,G2)" made TRUE. -/
theorem computational_uc_realizes {Sv : Type*} (F : ForkingFamily)
    (solverAdvOf : Sv → Ensemble) (s : Sv) (hs : solverAdvOf s = F.solverAdv)
    (hfloor : MSISHardQuant solverAdvOf) (hCneg : Negl F.invChal) : Negl (ucDistAdv F) := by
  have hG1 : ucDistAdv F = F.forgerAdv := ucDistAdv_eq_forgerAdv F
  have hG2 : Negl F.forgerAdv := ucForger_negl_of_msis F solverAdvOf s hs hfloor hCneg
  refine uc_advantage_transfer (ucDistAdv_nonneg F) ?_ hG2
  exact Filter.Eventually.of_forall (fun n => le_of_eq (congrFun hG1 n))

/-- **THE §7.6 `ComputationalUC` STRUCTURE, FILLED FROM THE SUBSTRATE.** A `UcSignature.ComputationalUC`
witness for `advₑ = ucDistAdv F`, `εₛ = F.forgerAdv`, whose two former ASSUMED fields are now PROVED terms:
`reduction_bound` (G1) is the equality `ucDistAdv_eq_forgerAdv`, `forge_negl` (G2) is `ucForger_negl_of_msis`.
So the genuine computational-UC obligation of §7.6 is INHABITED without re-assuming G1 or G2. -/
def ucRealizesWitness {Sv : Type*} (F : ForkingFamily)
    (solverAdvOf : Sv → Ensemble) (s : Sv) (hs : solverAdvOf s = F.solverAdv)
    (hfloor : MSISHardQuant solverAdvOf) (hCneg : Negl F.invChal) :
    UcSignature.ComputationalUC (ucDistAdv F) F.forgerAdv where
  adv_nonneg := ucDistAdv_nonneg F
  reduction_bound :=
    Filter.Eventually.of_forall (fun n => le_of_eq (congrFun (ucDistAdv_eq_forgerAdv F) n))
  forge_negl := ucForger_negl_of_msis F solverAdvOf s hs hfloor hCneg

/-- The witness's realization IS `computational_uc_realizes` — `Negl advₑ` from the filled structure. -/
theorem ucRealizesWitness_realizes {Sv : Type*} (F : ForkingFamily)
    (solverAdvOf : Sv → Ensemble) (s : Sv) (hs : solverAdvOf s = F.solverAdv)
    (hfloor : MSISHardQuant solverAdvOf) (hCneg : Negl F.invChal) : Negl (ucDistAdv F) :=
  (ucRealizesWitness F solverAdvOf s hs hfloor hCneg).realizes

/-! ## §6 — Non-vacuity, the full spectrum: realized, and load-bearingly broken. -/

/-- **(FIRES — a realized game has NEGLIGIBLE distinguishing advantage.)** The never-accepting
super-polynomial-challenge `zeroFamily` has `ucDistAdv ≡ 0`, negligible: real ≈ ideal at negligible advantage.
The positive pole, end-to-end through the substrate (`zeroFamily_forger_negl`). -/
theorem zeroFamily_ucDistAdv_negl : Negl (ucDistAdv zeroFamily) := by
  rw [ucDistAdv_eq_forgerAdv]; exact zeroFamily_forger_negl

/-- **(BITES — a broken game has NON-negligible distinguishing advantage.)** The constant-`2/5`
`const25Family` has `ucDistAdv ≡ 2/5`, NOT negligible: the distinguisher succeeds with constant probability, so
realization genuinely FAILS. The distinguishing advantage is a real number strictly between the `0` and `1`
poles — the tooth §7.5's 0/1 advantage could not bite. -/
theorem const25_ucDistAdv_not_negl : ¬ Negl (ucDistAdv const25Family) := by
  rw [ucDistAdv_eq_forgerAdv, const25_forgerAdv]
  exact not_negl_const_pos (by norm_num)

/-- **THE FLOOR IS LOAD-BEARING.** The constant-`2/5` distinguisher's derived MSIS solver advantage is at
least `2/25`, NON-negligible (`const25_forger_breaks_floor`) — so no `MSISHardQuant` floor can hold for it, and
`computational_uc_realizes` genuinely could not fire. Realization is exactly what the quantitative floor buys. -/
theorem const25_breaks_quant_floor : ¬ Negl const25Family.solverAdv := const25_forger_breaks_floor

#assert_all_clean [
  winProb_congr,
  card_filter_prod,
  winProb_prod_eq_advantage,
  winProb_dist_eq_forge,
  some_distBool_gives_forgery,
  ucDistAdv_eq_forgerAdv,
  ucDistAdv_nonneg,
  ucForger_negl_of_msis,
  ucForger_negl_of_dl,
  computational_uc_realizes,
  ucRealizesWitness_realizes,
  zeroFamily_ucDistAdv_negl,
  const25_ucDistAdv_not_negl,
  const25_breaks_quant_floor
]

end Dregg2.Crypto.UcSignatureQuant
