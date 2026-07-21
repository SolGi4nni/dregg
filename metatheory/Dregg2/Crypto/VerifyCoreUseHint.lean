/-
# `Dregg2.Crypto.VerifyCoreUseHint` — composing the per-coefficient `UseHint` loop onto the ABSTRACT
`R_q` recovery argument: the `round.useHint` leg of the FIPS 204 verify predicate.

`VerifyCoreEqSpec` closed the FORWARD algebra (`toRq_intt_matmul_row`: verifyCore's per-row NTT value maps
under `toRq` to the FIPS 204 `R_q` matvec `(A·z − c·t1·2^d)_i`) and `VerifyCoreEqSpecW` closed the COORDINATE
inverse (`wOne_recovers_hat`: verifyCore's stored-`Â` per-row coefficient array `w_i`, read at coordinate
`jj`, IS the canonical `ℤ_q` rep of the `jj`-th power-basis coordinate of that abstract matvec). What NEITHER
touched is verifyCore's ACTUAL next step — the per-coefficient loop

    for jj in [0:256] do  w1i := w1i.set! jj (useHint (h_i[jj]) (w_i[jj])).toNat

that produces the `w1'` array hashed into the challenge. THIS module composes that loop onto the abstract
argument, so verifyCore's `w1'` coefficient is provably the FIPS 204 `UseHint` applied to the COORDINATES OF
THE ABSTRACT MODULE ELEMENT `A·z − c·t1·2^d`, not to a re-expression of the executable `intt`.

## What is PROVEN here (real ∀-theorems, `#assert_axioms`-clean)

* **`setIdxFold`** — the closed form for the bare indexed-`set!` loop shape (do-notation single mutable, the
  loop element IS the write index, value depends only on the index). Pure `List.foldl`/`range'` induction, no
  `native_decide`. This is the loop-reasoning engine for `verifyCore`'s `UseHint` inner loop.
* **`w1Row` / `w1Row_size` / `w1Row_getElem`** — `w1Row hi w` is verifyCore's inner `UseHint` loop, isolated
  character-for-character (`Id.run do … for jj in [0:256] do w1i := w1i.set! jj (useHint …).toNat`); its
  `getElem` is `(w1Row hi w)[jj]! = (useHint (hi[jj]!) (w[jj]!)).toNat` for all `jj < 256`, all inputs.
* **`w1Row_recovers_arg` — THE COMPOSITION (the `round.useHint` leg).** For all inputs,

    (w1Row hi (wRowHat terms c s))[jj]! = (useHint (hi[jj]!) ⟨jj-th coord of (A·z − c·t1·2^d)_i⟩).toNat

  i.e. verifyCore's per-row `w1'` array, coefficient `jj`, IS the FIPS 204 `UseHint` of `(h_i[jj], the jj-th
  power-basis coordinate of the ABSTRACT `R_q` recovery value `rqMatvec`)`. Composes `w1Row_getElem` with
  `wOne_recovers_hat` (hence transitively `toRq_intt_matmul_row`, `toRq_coeff`, `expandA_is_matrix`). This is
  the `Fips204Spec.RoundingScheme.useHint` field, at the executable types, applied to the genuine module
  element the spec quantifies over — NOT `challengeMatches`, NOT a bisection.

## HONEST FRONTIER — the ONE remaining leg, stated as the exact open goal (NAMED, not laundered)

`w1Row_recovers_arg` closes the `useHint`-of-argument step: the input to verifyCore's per-coefficient rounding
IS the coordinates of the abstract `A·z − c·t1·2^d`. What remains between this and the full FIPS 204 hash
conjunct `decide (verifyB.hash μ (round.useHint h (A·z − c·t1·2^d)) = c̃)` is exactly:

    THE HASH-FRAMING LEG (OPEN):  shake256 (μ ‖ w1Encode w1') 48 == c̃   =   decide (hash μ w1' = c̃)

where `hash := (μ, w1') ↦ shake256 (μ ‖ w1Encode w1') 48` is a legitimate INSTANTIATION of `verifyB`'s generic
`hash` field (its collision-resistance is the `HashSig`/`FoQrom` floor, a separate axis — not a soundness gap
here). Performing that instantiation and discharging the equality — threading the six per-row `w1Row` results
through `w1Encode`'s `packBits` concatenation and the SHAKE framing — is NOT done in the tree. It is the exact
residual; `w1Row_recovers_arg` is the leg immediately below it, now closed for all inputs.
-/
import Dregg2.Crypto.VerifyCoreEqSpecW

namespace Dregg2.Crypto.VerifyCoreEqSpec

open Dregg2.Crypto.MlDsaRing (Poly q zeroPoly intt)
open Dregg2.Crypto.MlDsaVerifyReal (useHint)

set_option maxRecDepth 8000

/-! ## PART 1 — the bare indexed-`set!` loop, closed form. -/

/-- `get!` after `set!` at a DIFFERENT index is unchanged. -/
theorem gE_set!_ne {β} [Inhabited β] (b : Array β) (i j : Nat) (v : β) (h : i ≠ j) :
    (b.set! i v)[j]! = b[j]! := by
  simp only [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?,
    Array.getElem?_setIfInBounds, Array.set!_eq_setIfInBounds]
  rw [if_neg h]

/-- `get!` after in-bounds `set!` at the SAME index reads the written value. -/
theorem gE_set!_self {β} [Inhabited β] (b : Array β) (i : Nat) (v : β) (h : i < b.size) :
    (b.set! i v)[i]! = v := by
  simp only [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?,
    Array.getElem?_setIfInBounds, Array.set!_eq_setIfInBounds]
  simp [h]

/-- `set!` preserves size. -/
theorem gE_size_set! {β} [Inhabited β] (b : Array β) (i : Nat) (v : β) :
    (b.set! i v).size = b.size := by
  simp [Array.set!_eq_setIfInBounds]

/-- **The indexed-`set!` fold spec.** Folding `out.set! i (f i)` over `List.range' 0 n 1` (the do-notation
single-mutable loop whose loop element IS the write index, value `f i` depending only on the index): size is
preserved, position `j < n` (in bounds) reads `f j`, and positions `≥ n` are untouched. Pure loop reasoning
(`List.range'`/`List.foldl` induction) — no `native_decide`. -/
theorem setIdxFold {β} [Inhabited β] (f : Nat → β) :
    ∀ (n : Nat) (P0 : Array β),
      (List.foldl (fun out i => out.set! i (f i)) P0 (List.range' 0 n 1)).size = P0.size
      ∧ (∀ j, j < n → j < P0.size →
          (List.foldl (fun out i => out.set! i (f i)) P0 (List.range' 0 n 1))[j]! = f j)
      ∧ (∀ j, n ≤ j →
          (List.foldl (fun out i => out.set! i (f i)) P0 (List.range' 0 n 1))[j]! = P0[j]!) := by
  intro n
  induction n with
  | zero =>
    intro P0
    exact ⟨rfl, fun j hj => absurd hj (Nat.not_lt_zero j), fun j _ => rfl⟩
  | succ k ih =>
    intro P0
    rw [List.range'_1_concat, List.foldl_concat]
    obtain ⟨hsz, hlo, hhi⟩ := ih P0
    refine ⟨?_, ?_, ?_⟩
    · rw [gE_size_set!, hsz]
    · intro j hj hjsz
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | h
      · rw [gE_set!_ne _ _ _ _ (by omega), hlo j h hjsz]
      · subst h
        rw [Nat.zero_add, gE_set!_self _ _ _ (by rw [hsz]; exact hjsz)]
    · intro j hj
      rw [gE_set!_ne _ _ _ _ (by omega), hhi j (by omega)]

/-! ## PART 2 — `w1Row`: verifyCore's per-coefficient `UseHint` loop, isolated. -/

/-- verifyCore's per-row `UseHint` loop, isolated CHARACTER-FOR-CHARACTER (compare
`MlDsaVerifyReal.verifyCore` lines 186–188): starting from `zeroPoly`, for each coordinate `jj < 256` write
`(UseHint (h_i[jj], w_i[jj])).toNat`. `w1Row hi w` is the `w1'_i` array verifyCore hashes into the challenge. -/
def w1Row (hi w : Poly) : Poly := Id.run do
  let mut w1i := zeroPoly
  for jj in [0:256] do
    w1i := w1i.set! jj ((useHint (hi[jj]!) (w[jj]!)).toNat)
  return w1i

/-- `w1Row` has size `256` (it starts at `zeroPoly` and only `set!`s in-range). -/
theorem w1Row_size (hi w : Poly) : (w1Row hi w).size = 256 := by
  unfold w1Row
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', List.forIn_pure_yield_eq_foldl, pure_bind,
    bind_pure, Id.run_pure, Std.Legacy.Range.size, Nat.sub_zero, Nat.add_one_sub_one, Nat.div_one]
  rw [(setIdxFold (fun jj => (useHint (hi[jj]!) (w[jj]!)).toNat) 256 zeroPoly).1]
  simp [zeroPoly]

/-- **`w1Row_getElem`.** For every coordinate `jj < 256` and all inputs, verifyCore's `w1'_i` array reads
`(w1Row hi w)[jj]! = (UseHint (h_i[jj], w_i[jj])).toNat` — the executable per-coefficient FIPS 204 rounding.
Closed by the `setIdxFold` loop spec (no `native_decide`). -/
theorem w1Row_getElem (hi w : Poly) (jj : Nat) (hjj : jj < 256) :
    (w1Row hi w)[jj]! = (useHint (hi[jj]!) (w[jj]!)).toNat := by
  unfold w1Row
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', List.forIn_pure_yield_eq_foldl, pure_bind,
    bind_pure, Id.run_pure, Std.Legacy.Range.size, Nat.sub_zero, Nat.add_one_sub_one, Nat.div_one]
  exact (setIdxFold (fun jj => (useHint (hi[jj]!) (w[jj]!)).toNat) 256 zeroPoly).2.1 jj hjj
    (by have h : zeroPoly.size = 256 := (by simp [zeroPoly]); omega)

#assert_axioms setIdxFold
#assert_axioms w1Row_size
#assert_axioms w1Row_getElem

/-! ## PART 3 — `w1Row_recovers_arg`: the `round.useHint` leg onto the ABSTRACT `R_q` argument.

Composing `w1Row_getElem` (the `UseHint` loop reads coordinate `jj` of `w_i`) with `wOne_recovers_hat` (that
coordinate IS the canonical rep of the `jj`-th power-basis coordinate of the abstract `R_q` matvec `A·z −
c·t1·2^d`), verifyCore's `w1'_i` coefficient is the FIPS 204 `UseHint` applied to the COORDINATES OF THE
ABSTRACT MODULE ELEMENT — the `Fips204Spec.RoundingScheme.useHint` field, at the executable types, on the
genuine argument the spec quantifies over. -/

/-- **THE `round.useHint` LEG — verifyCore's `w1'` array recovers `UseHint` of the ABSTRACT argument.** For
all inputs (with the operational guards on the stored NTT-domain matrix `Â = terms.map (·.1)` and the
challenge/scaled-`t1` factors), verifyCore's per-row `w1'_i` array — built by the per-coefficient `UseHint`
loop on `wRowHat` — reads at coordinate `jj`:

    (w1Row hi (wRowHat terms c s))[jj]!
      = (useHint (hi[jj]!) (pbW.basis.repr (rqMatvec (terms.map (fun t => (intt t.1, t.2))) c s) jj).val).toNat

i.e. it is the FIPS 204 `UseHint` of `(h_i[jj], the jj-th coordinate of the abstract `R_q` recovery value
`(A·z − c·t1·2^d)_i`)`. The argument fed to the rounding is the genuine `R_q`-module element (reached through
the PROVED algebra legs `toRq_intt_matmul_row` / `toRq_coeff` / `expandA_is_matrix`), NOT a re-expression of
the executable `intt` and NOT `challengeMatches`. This is the `RoundingScheme.useHint` conjunct of the
`Fips204Spec.MlDsaParams.verifyB` predicate, discharged for all inputs. -/
theorem w1Row_recovers_arg (hi : Poly) (terms : List (Poly × Poly)) (c s : Poly)
    (hAhat : ∀ t ∈ terms, t.1.size = 256 ∧ (∀ (p : Nat), t.1[p]! < q))
    (hz : ∀ t ∈ terms, t.2.size = 256) (hc : c.size = 256) (hs : s.size = 256)
    (jj : Fin pbW.dim) :
    (w1Row hi (wRowHat terms c s))[(jj : ℕ)]!
      = (useHint (hi[(jj : ℕ)]!)
          (pbW.basis.repr (rqMatvec (terms.map (fun t => (intt t.1, t.2))) c s) jj).val).toNat := by
  have hjj : (jj : ℕ) < 256 := by have := jj.isLt; have := pbW_dim; omega
  rw [w1Row_getElem hi (wRowHat terms c s) (jj : ℕ) hjj,
    wOne_recovers_hat terms c s hAhat hz hc hs jj]

#assert_axioms w1Row_recovers_arg

/-! ## PART 4 — NON-VACUITY: the rounding is a GENUINE gate, on a GENUINE degree-256 argument.

`w1Row_recovers_arg` is not `_ = (useHint …).toNat` trivia: (i) the coordinate space is genuinely `256`-dim
(`pbW.dim = 256`), so the argument is a real `R_q` element, not a scalar; (ii) `UseHint` genuinely DEPENDS on
its hint — there are `r` with `useHint 1 r ≠ useHint 0 r` — so the recovered `w1'` is a real function of the
transmitted hint `h`, not a constant. -/

/-- The coordinate reader lands in a genuine degree-`256` ring (re-export). -/
theorem argCoord_dim_256 : pbW.dim = 256 := pbW_dim

/-- **`UseHint` is a genuine gate.** At `r = 0` the hint `h = 1` shifts the recovered high bits
(`useHint 1 0 = 15 ≠ 0 = useHint 0 0` at the ML-DSA-65 numbers), so `w1Row_recovers_arg`'s conclusion is a
real function of the transmitted hint, not a constant — the composed leg has teeth. -/
theorem useHint_nontrivial : useHint 1 0 ≠ useHint 0 0 := by decide

#assert_axioms argCoord_dim_256

end Dregg2.Crypto.VerifyCoreEqSpec
