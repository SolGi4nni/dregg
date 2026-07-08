/-
# `Dregg2.Crypto.HermineLossiness` — MLWE lossiness PROVED by pigeonhole.

`Dregg2.Crypto.HermineDischarge.lossiness_discharges_nonzero` consumes an MLWE-lossiness pair —
two distinct short preimages `s ≠ s'` with `A s = A s'` — as a HYPOTHESIS. This file proves that
pair EXISTS whenever the map compresses: a linear `A` from a set `S` of short vectors into a
finite codomain strictly smaller than `S` cannot be injective on `S` (pigeonhole), so two distinct
short vectors collide. That collision IS the lossiness fact; the "assumed lossiness" flag becomes
a counting theorem.

* **The general theorem** (`lossiness_of_card_lt`): `S : Finset M` of `β`-short vectors,
  `A : M →ₗ[Rq] N` with `N` finite and `Fintype.card N < S.card` ⟹
  `∃ s ∈ S, ∃ s' ∈ S, s ≠ s' ∧ A s = A s'` (both short). Mathlib's
  `Finset.exists_ne_map_eq_of_card_lt_of_maps_to` does the counting; the linear structure rides
  along untouched so the collision plugs directly into the discharge theorems.
* **The concrete instance**: `A : ℤ² →ₗ[ℤ] ZMod 3`, `v ↦ v₀ + 2·v₁ (mod 3)` — a genuine
  compression — and `S` = the five L1-norm-≤ 1 integer vectors. `card (ZMod 3) = 3 < 5 = S.card`
  is PROVED (`decide` on the actual numbers), so the pigeonhole FIRES: the card hypothesis is
  satisfied, not vacuous. The produced pair is exhibited explicitly (`(1,0) ≠ (0,−1)`, both map
  to `1 mod 3`) and checked by `decide`.
* **End-to-end**: the pigeonhole pair feeds `lossiness_discharges_nonzero` (generic wrapper AND
  on the concrete numbers), and a concrete forked forgery over the SAME compressing `A` runs
  through `forked_forgery_yields_msis_solution_discharged` — lossiness → nonzero → MSIS solution
  with NO assumed lossiness anywhere: every hypothesis in the chain is proved on the instance.
-/
import Dregg2.Crypto.HermineConcrete
import Mathlib.Data.ZMod.Basic

namespace Dregg2.Crypto.HermineLossiness

open Dregg2.Crypto.Lattice
open Dregg2.Crypto.HermineMSIS
open Dregg2.Crypto.HermineDischarge
open Dregg2.Crypto.HermineConcrete

variable {Rq : Type*} [CommRing Rq]
variable {M : Type*} [AddCommGroup M] [Module Rq M] [ShortNorm M]
variable {N : Type*} [AddCommGroup N] [Module Rq N]

/-! ## Target 1 — the general pigeonhole lossiness theorem -/

/-- **MLWE lossiness from compression (pigeonhole).** If a finite set `S` of `β`-short vectors is
strictly larger than the (finite) codomain, then `A` restricted to `S` is not injective: there are
two DISTINCT SHORT vectors with the same image. The produced pair `(s, s')` with `s ≠ s'` and
`A s = A s'` is exactly the MLWE-lossiness hypothesis pair consumed by
`HermineDischarge.lossiness_discharges_nonzero` / `forked_forgery_yields_msis_solution_discharged`
(`hss`/`ht`) — lossiness DERIVED from counting, not assumed. -/
theorem lossiness_of_card_lt [Fintype N] (A : M →ₗ[Rq] N) (β : ℕ) (S : Finset M)
    (hshort : ∀ v ∈ S, IsShort β v) (hcard : Fintype.card N < S.card) :
    ∃ s ∈ S, ∃ s' ∈ S, s ≠ s' ∧ A s = A s' ∧ IsShort β s ∧ IsShort β s' := by
  obtain ⟨s, hs, s', hs', hne, heq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to
      (t := (Finset.univ : Finset N))
      (by simpa [Finset.card_univ] using hcard)
      (f := fun v => A v)
      (fun v _ => by simp)
  exact ⟨s, hs, s', hs', hne, heq, hshort s hs, hshort s' hs'⟩

/-- **Pigeonhole feeds the discharge, generically.** From the same counting hypothesis, produce the
collision AND run it through `lossiness_discharges_nonzero`: for any invertible challenge
difference, at least one extracted MSIS candidate is nonzero. The lossiness leg of the discharged
reduction is now a THEOREM about compressing maps. -/
theorem lossiness_of_card_lt_discharges_nonzero [Fintype N]
    (A : M →ₗ[Rq] N) (β : ℕ) (S : Finset M)
    (hshort : ∀ v ∈ S, IsShort β v) (hcard : Fintype.card N < S.card)
    (c c' : Rq) (z z' : M) (hinv : IsUnit (c - c')) :
    ∃ s ∈ S, ∃ s' ∈ S, A s = A s' ∧
      ((z - z') - (c - c') • s ≠ 0 ∨ (z - z') - (c - c') • s' ≠ 0) := by
  obtain ⟨s, hs, s', hs', hne, heq, _, _⟩ := lossiness_of_card_lt A β S hshort hcard
  exact ⟨s, hs, s', hs', heq, lossiness_discharges_nonzero s s' c c' z z' hne hinv⟩

/-! ## Target 2 — the concrete, non-vacuous instance

Domain `ℤ²` with the L1 `ShortNorm` from `HermineConcrete`; codomain `ZMod 3` — genuinely FINITE,
so the compression is real (any infinite set of integer vectors compresses, and already the five
norm-≤ 1 vectors overflow the three residues). -/

/-- The concrete compressing map `A : ℤ² →ₗ[ℤ] ZMod 3`, `v ↦ v₀ + 2·v₁ (mod 3)` — the mod-`q`
reduction of `HermineConcrete.Amat`'s row `[1 2]`. -/
def Aq : (Fin 2 → ℤ) →ₗ[ℤ] ZMod 3 where
  toFun v := ((v 0 + 2 * v 1 : ℤ) : ZMod 3)
  map_add' x y := by
    simp only [Pi.add_apply]
    push_cast
    ring
  map_smul' r x := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, zsmul_eq_mul]
    push_cast
    ring

/-- The five integer vectors of L1 norm ≤ 1 — the full `β = 1` short ball in `ℤ²`. -/
def Sshort : Finset (Fin 2 → ℤ) :=
  {![0, 0], ![1, 0], ![-1, 0], ![0, 1], ![0, -1]}

/-- The short ball really has five elements (the finset literal has no duplicates). -/
theorem Sshort_card : Sshort.card = 5 := by decide

/-- Every element of `Sshort` is `1`-short in the REAL L1 `ShortNorm` — decided on the numbers. -/
theorem Sshort_short : ∀ v ∈ Sshort, IsShort 1 v := by
  have h : ∀ v ∈ Sshort, nrm v ≤ 1 := by decide
  exact h

/-- **The card inequality GENUINELY HOLDS**: `card (ZMod 3) = 3 < 5 = Sshort.card`. This is the
anti-vacuity fact — the pigeonhole hypothesis is satisfied, not an unsatisfiable antecedent. -/
theorem concrete_card_lt : Fintype.card (ZMod 3) < Sshort.card := by
  rw [ZMod.card, Sshort_card]
  decide

/-- **The pigeonhole FIRES on the concrete instance**: two distinct short vectors in the `β = 1`
ball collide under `Aq`. Produced by the general theorem from the PROVED card inequality. -/
theorem concrete_lossiness :
    ∃ s ∈ Sshort, ∃ s' ∈ Sshort, s ≠ s' ∧ Aq s = Aq s' ∧ IsShort 1 s ∧ IsShort 1 s' :=
  lossiness_of_card_lt Aq 1 Sshort Sshort_short concrete_card_lt

/-- The concrete lossy secret, `s = (1, 0)`; `Aq s = 1`. -/
def svec : Fin 2 → ℤ := ![1, 0]

/-- The concrete lossy twin, `s' = (0, −1)`; `Aq s' = −2 = 1 (mod 3)`. Distinct from `s`, equally
short (`‖s'‖₁ = 1`) — the secret is information-theoretically hidden between them. -/
def svec' : Fin 2 → ℤ := ![0, -1]

/-- An EXPLICIT collision pair witnessing the lossiness the pigeonhole guarantees: `(1,0)` and
`(0,−1)` are distinct members of the short ball with `Aq (1,0) = 1 = −2 = Aq (0,−1)` — every leg
checked on the actual numbers. -/
theorem explicit_collision :
    svec ∈ Sshort ∧ svec' ∈ Sshort ∧ svec ≠ svec' ∧ Aq svec = Aq svec' := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-! ## Target 3 — end-to-end: proven lossiness through the discharged reduction

The forger signs with the TWIN secret over the SAME compressing `Aq`: mask `y = 0` (so `w = 0`),
challenges `c = 1, c' = 0`, responses `z = y + c·s' = (0,−1)`, `z' = y + c'·s' = 0`. -/

/-- Fork challenge difference `1 − 0 = 1` is a unit of `ℤ`. -/
theorem concrete_challenge_isUnit : IsUnit ((1 : ℤ) - 0) := by
  simp

/-- The proven collision pair runs through `lossiness_discharges_nonzero` on the concrete numbers:
at least one extracted MSIS candidate is nonzero — the `u ≠ 0` leg derived from PROVEN lossiness. -/
theorem concrete_nonzero_from_proven_lossiness :
    (![0, -1] - 0) - ((1 : ℤ) - 0) • svec ≠ 0 ∨
    (![0, -1] - 0) - ((1 : ℤ) - 0) • svec' ≠ 0 :=
  lossiness_discharges_nonzero svec svec' 1 0 ![0, -1] 0
    explicit_collision.2.2.1 concrete_challenge_isUnit

/-- Both forked transcripts VERIFY (the real `HermineThreshold.verify` relation `Aq z = w + c • t`
against the honest key `t = Aq svec`), checked on the numbers. -/
theorem forked_transcripts_verify :
    HermineThreshold.verify Aq (Aq svec) 0 1 ![0, -1] ∧
    HermineThreshold.verify Aq (Aq svec) 0 0 (0 : Fin 2 → ℤ) := by
  constructor <;> · show _ = _; decide

/-- **The fully connected chain**: PROVEN pigeonhole lossiness (`explicit_collision`, from the
satisfied card inequality) + concrete unit challenge difference + verified fork, fed to the REAL
`forked_forgery_yields_msis_solution_discharged` — an MSIS solution for the compressing `Aq` at
bound `βz + βz + βcs = 1 + 1 + 1 = 3`, with NO assumed lossiness and NO assumed `u ≠ 0` anywhere
in the chain. -/
theorem concrete_end_to_end : ∃ u, IsMSISSolution Aq 3 u :=
  forked_forgery_yields_msis_solution_discharged Aq svec svec' 0 1 0 ![0, -1] 0 1 1
    explicit_collision.2.2.1 explicit_collision.2.2.2 concrete_challenge_isUnit
    (by decide) (by decide) (by decide) (by decide)
    forked_transcripts_verify.1 forked_transcripts_verify.2

#assert_axioms lossiness_of_card_lt
#assert_axioms lossiness_of_card_lt_discharges_nonzero
#assert_axioms Sshort_card
#assert_axioms Sshort_short
#assert_axioms concrete_card_lt
#assert_axioms concrete_lossiness
#assert_axioms explicit_collision
#assert_axioms concrete_challenge_isUnit
#assert_axioms concrete_nonzero_from_proven_lossiness
#assert_axioms forked_transcripts_verify
#assert_axioms concrete_end_to_end

end Dregg2.Crypto.HermineLossiness
