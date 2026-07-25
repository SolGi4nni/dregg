/-
# `Dregg2.Crypto.VerifyCoreArgRows` — verifyCore's `w1` ROW FOLD, resolved.

The deployed challenge conjunct (`VerifyCoreSpec.challengeMatches`, `verifyCore`'s body minus the norm
test) contains FOUR nested `do`-loops: the `ẑ_j` push loop, the `k`-row `w1` push loop, the `l`-term
matvec accumulator fold, and the 256-coefficient `UseHint` loop. This module resolves the ROW-INDEXED
outer fold and names the per-row body, so the downstream assembly
(`Dregg2.Crypto.VerifyCoreArgAssembly`) can reason one row at a time.

* `pushFoldGet` — the closed form for the `Array.push` accumulation loop (size and `getElem!`), by
  `List.range'` induction. The push-loop analogue of `VerifyCoreUseHint.setIdxFold`.
* `azOf` / `rowBody` — verifyCore's `l`-term matvec accumulator and its per-row `w1'` body, transcribed
  VERBATIM (compare `VerifyCoreSpec.challengeMatches` line for line).
* `azOf_eq` / `rowBody_eq_execRow` — that body IS `w1Row h_i (wRowHat …)`, the shape `VerifyCoreUseHint`
  and `VerifyCoreEqSpecW` reason about. The only content is the `List.range'`-indexed accumulator
  versus the explicit term list; the 256-coefficient loop is never expanded.
* `challengeMatches_w1Of` / `w1Of_get` / `challengeMatches_rows` — the deployed digest with the row
  fold replaced by ANY array whose `k` entries are the row bodies. Real `∀`; no `native_decide`.

## ★ A BUILD CONSTRAINT THAT SHAPES THIS FILE (do not "simplify" it away)

The definitions here are `noncomputable` and every proof keeps `rowBody`/`azOf` FOLDED. That is not
style. Nothing executes these — the deployed code is `verifyCore` itself — and a proof that `unfold`s
the row body inside the `k`-row context materialises the 256-coefficient `UseHint` loop six times over;
the resulting proof term does not fit in the 24 GB build cgroup (measured: OOM at ~29 GB, twice, on
`lake build`; `lake env lean` without olean emission does not show it). Keep the row body behind a
definition and rewrite with small lemmas.
-/
import Dregg2.Crypto.VerifyCoreHashFrame

namespace Dregg2.Crypto.VerifyCoreArgRows

open Dregg2.Crypto.MlDsaRing (Poly q zeroPoly ntt intt addPoly subPoly pointwiseMul)
open Dregg2.Crypto.MlDsaVerifyReal (w1Encode useHint scaleT1 paramD)
open Dregg2.Crypto.MlDsaCodec (paramK paramL packBits pkDecode sigDecode)
open Dregg2.Crypto.MlDsaExpandA (expandA)
open Dregg2.Crypto.MlDsaSampleInBall (sampleInBall)
open Dregg2.Crypto.Keccak (shake256)
open Dregg2.Crypto.VerifyCoreSpec (challengeMatches)
open Dregg2.Crypto.VerifyCoreEqSpec (setIdxFold w1Row wRowHat)

set_option maxRecDepth 20000

/-! ## PART 0 — array plumbing. -/

/-- Extensionality through `getElem!`. -/
theorem arrExt {β : Type} [Inhabited β] (a b : Array β) (hs : a.size = b.size)
    (h : ∀ j, j < a.size → a[j]! = b[j]!) : a = b := by
  apply Array.ext hs
  intro i h1 h2
  have hh := h i h1
  rwa [getElem!_pos a i h1, getElem!_pos b i h2] at hh

/-- `getElem!` of `Array.ofFn` in range. -/
theorem ofFn_get! {β : Type} [Inhabited β] {n : Nat} (f : Fin n → β) (j : Nat) (hj : j < n) :
    (Array.ofFn f)[j]! = f ⟨j, hj⟩ := by
  have hsz : j < (Array.ofFn f).size := by simpa using hj
  rw [getElem!_pos (Array.ofFn f) j hsz]
  simp

/-- `getElem!` below a `push` is unchanged. -/
theorem gE_push_lt {β : Type} [Inhabited β] (a : Array β) (v : β) (m : Nat) (h : m < a.size) :
    (a.push v)[m]! = a[m]! := by
  have h' : m < (a.push v).size := by rw [Array.size_push]; omega
  rw [getElem!_pos (a.push v) m h', getElem!_pos a m h, Array.getElem_push_lt]

/-- `getElem!` at the `push` position reads the pushed value. -/
theorem gE_push_eq {β : Type} [Inhabited β] (a : Array β) (v : β) : (a.push v)[a.size]! = v := by
  have h' : a.size < (a.push v).size := by rw [Array.size_push]; omega
  rw [getElem!_pos (a.push v) a.size h']
  simp

/-- **The `push` accumulation loop, closed form.** Folding `out.push (f i)` over `List.range' 0 n 1`
(the do-notation single-mutable loop that APPENDS a value computed from the index) grows the array by
`n` and puts `f j` at offset `j`. Pure `List.range'`/`List.foldl` induction; no `native_decide`. -/
theorem pushFoldGet {β : Type} [Inhabited β] (f : Nat → β) :
    ∀ (n : Nat) (A0 : Array β),
      (List.foldl (fun out i => out.push (f i)) A0 (List.range' 0 n 1)).size = A0.size + n
      ∧ (∀ j, j < n →
          (List.foldl (fun out i => out.push (f i)) A0 (List.range' 0 n 1))[A0.size + j]! = f j) := by
  intro n
  induction n with
  | zero => intro A0; exact ⟨rfl, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  | succ k ih =>
    intro A0
    rw [List.range'_1_concat, List.foldl_concat]
    obtain ⟨hsz, hget⟩ := ih A0
    refine ⟨by rw [Array.size_push, hsz]; omega, ?_⟩
    intro j hj
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | h
    · rw [gE_push_lt _ _ _ (by rw [hsz]; omega), hget j h]
    · subst h
      rw [show A0.size + j = (List.foldl (fun out i => out.push (f i)) A0 (List.range' 0 j 1)).size
        from by rw [hsz], gE_push_eq]
      simp

/-- The `A0 = Array.mkEmpty n` specialisation — the shape the deployed loops start from. -/
theorem pushFoldGet0 {β : Type} [Inhabited β] (f : Nat → β) (n j : Nat) (hj : j < n) :
    (List.foldl (fun out i => out.push (f i)) (Array.mkEmpty n) (List.range' 0 n 1))[j]! = f j := by
  have h := (pushFoldGet f n (Array.mkEmpty n)).2 j hj
  simpa using h

/-- `scaleT1` produces a 256-coefficient polynomial (it only `set!`s into `zeroPoly`). -/
theorem scaleT1_size (p : Poly) : (scaleT1 p).size = 256 := by
  unfold scaleT1
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', List.forIn_pure_yield_eq_foldl, pure_bind,
    bind_pure, Id.run_pure, Std.Legacy.Range.size, Nat.sub_zero, Nat.add_one_sub_one, Nat.div_one]
  rw [(setIdxFold (fun i => (p[i]! * 2 ^ paramD) % q) 256 zeroPoly).1]
  simp [zeroPoly]

/-! ## PART 1 — the `w1Encode` congruence. -/

/-- `w1Encode` reads exactly the `k = 6` rows. -/
theorem w1Encode_shape (a : Array Poly) : w1Encode a
    = (packBits (a[0]!) 4 ++ packBits (a[1]!) 4 ++ packBits (a[2]!) 4
        ++ packBits (a[3]!) 4 ++ packBits (a[4]!) 4 ++ packBits (a[5]!) 4).toList := by
  unfold w1Encode
  simp [Std.Legacy.Range.forIn_eq_forIn_range', List.forIn_pure_yield_eq_foldl, paramK,
    List.range']

/-- **The `w1Encode` congruence.** Two coefficient views agreeing on the `k` rows encode identically.
(BOTH sides of the `hArg` hypothesis call the SAME `w1Encode`, so no `packBits` reasoning is needed
here; the FIPS 204 Alg. 28 ENCODER refinement is a different leg, `Fips204BitPack.w1Encode_eq_spec`.) -/
theorem w1Encode_congr (a b : Array Poly) (h : ∀ i, i < paramK → a[i]! = b[i]!) :
    w1Encode a = w1Encode b := by
  rw [w1Encode_shape, w1Encode_shape, h 0 (by decide), h 1 (by decide), h 2 (by decide),
    h 3 (by decide), h 4 (by decide), h 5 (by decide)]

/-! ## PART 2 — the deployed row body. -/

/-- The framed message digest `μ` the deployed verifier computes (FIPS 204 Alg. 3 framing, Alg. 8). -/
noncomputable def muOf (pk M ctx : List UInt8) : List UInt8 :=
  shake256 (shake256 pk 64 ++ ((UInt8.ofNat 0) :: (UInt8.ofNat ctx.length) :: (ctx ++ M))) 64

/-- **verifyCore's `l`-term matvec accumulator for row `i`, transcribed VERBATIM**: precompute
`ẑ_j = ntt z_j`, then accumulate `Σ_j Â_{ij} ⊙ ẑ_j`. -/
noncomputable def azOf (aHat zp : Array Poly) (i : Nat) : Poly := Id.run do
  let mut zHat : Array Poly := Array.mkEmpty paramL
  for j in [0:paramL] do
    zHat := zHat.push (ntt (zp[j]!))
  let mut az := zeroPoly
  for j in [0:paramL] do
    az := addPoly az (pointwiseMul (aHat[i * paramL + j]!) (zHat[j]!))
  return az

/-- The row-`i` term list of the deployed matvec: the stored NTT-domain `Â` entries against the
decoded response polynomials. -/
def rowTerms (aHat zp : Array Poly) (i : Nat) : List (Poly × Poly) :=
  [(aHat[i * paramL + 0]!, zp[0]!), (aHat[i * paramL + 1]!, zp[1]!),
   (aHat[i * paramL + 2]!, zp[2]!), (aHat[i * paramL + 3]!, zp[3]!),
   (aHat[i * paramL + 4]!, zp[4]!)]

/-- **The `l`-term accumulator IS the explicit term-list fold.** The `range'`-indexed loop with the
precomputed `ẑ` array equals `wRowHat`'s `List.foldl` over `rowTerms`, for every row index. Real `∀`;
the 256-coefficient loop is nowhere in this statement, which is what keeps the proof term small. -/
theorem azOf_eq (aHat zp : Array Poly) (i : Nat) :
    azOf aHat zp i
      = List.foldl (fun az t => addPoly az (pointwiseMul t.1 (ntt t.2))) zeroPoly
          (rowTerms aHat zp i) := by
  unfold azOf rowTerms
  simp only [Id.run, bind, pure, Std.Legacy.Range.forIn_eq_forIn_range',
    List.forIn_pure_yield_eq_foldl, Std.Legacy.Range.size, Nat.sub_zero, Nat.add_one_sub_one,
    Nat.div_one, paramL]
  rfl

/-- **verifyCore's per-row `w1'` body, transcribed VERBATIM** from `challengeMatches`. -/
noncomputable def rowBody (pk sig : List UInt8) (i : Nat) : Poly := Id.run do
  let w := intt (subPoly (azOf (expandA (pkDecode pk).1) (sigDecode sig).2.1 i)
    (pointwiseMul (ntt (sampleInBall (sigDecode sig).1))
      (ntt (scaleT1 ((pkDecode pk).2[i]!)))))
  let hi := (sigDecode sig).2.2[i]!
  let mut w1i := zeroPoly
  for jj in [0:256] do
    w1i := w1i.set! jj ((useHint (hi[jj]!) (w[jj]!)).toNat)
  return w1i

/-- verifyCore's per-row `w1'` polynomial in the `w1Row ∘ wRowHat` form the coordinate legs use. -/
noncomputable def execRow (pk sig : List UInt8) (i : Nat) : Poly :=
  w1Row ((sigDecode sig).2.2[i]!)
    (wRowHat (rowTerms (expandA (pkDecode pk).1) (sigDecode sig).2.1 i)
      (sampleInBall (sigDecode sig).1) (scaleT1 ((pkDecode pk).2[i]!)))

/-- **The deployed row body IS `w1Row ∘ wRowHat`**, for every row index. The `UseHint` loop matches
definitionally on both sides (`w1Row` IS that loop); the content is `azOf_eq`. -/
theorem rowBody_eq_execRow (pk sig : List UInt8) (i : Nat) :
    rowBody pk sig i = execRow pk sig i := by
  show w1Row ((sigDecode sig).2.2[i]!)
      (intt (subPoly (azOf (expandA (pkDecode pk).1) (sigDecode sig).2.1 i)
        (pointwiseMul (ntt (sampleInBall (sigDecode sig).1))
          (ntt (scaleT1 ((pkDecode pk).2[i]!)))))) = execRow pk sig i
  unfold execRow wRowHat
  rw [azOf_eq]

/-! ## PART 3 — the row fold. -/

/-- verifyCore's `k`-row `w1` accumulator, isolated. -/
noncomputable def w1Of (pk sig : List UInt8) : Array Poly := Id.run do
  let mut w1 : Array Poly := Array.mkEmpty paramK
  for i in [0:paramK] do
    w1 := w1.push (rowBody pk sig i)
  return w1

/-- **The deployed challenge conjunct, with its `w1` accumulator NAMED.** `challengeMatches` verbatim,
with the `k`-row loop read as `w1Of` and the message framing as `muOf`. Both sides keep the row body
FOLDED, so this is a definitional identity once the hint-size guard fires. -/
theorem challengeMatches_w1Of (pk M ctx sig : List UInt8)
    (hh : (sigDecode sig).2.2.size = paramK) :
    challengeMatches pk M ctx sig
      = (shake256 (muOf pk M ctx ++ w1Encode (w1Of pk sig)) 48 == (sigDecode sig).1) := by
  unfold challengeMatches
  simp only [Id.run, bind, pure, hh, ne_eq, not_true_eq_false, if_false]
  rfl

/-- Row `i` of the accumulator IS the row body — the `pushFoldGet` loop spec, body folded. -/
theorem w1Of_get (pk sig : List UInt8) (i : Nat) (hi : i < paramK) :
    (w1Of pk sig)[i]! = rowBody pk sig i := by
  unfold w1Of
  simp only [Id.run, bind, pure, Std.Legacy.Range.forIn_eq_forIn_range',
    List.forIn_pure_yield_eq_foldl, Std.Legacy.Range.size, Nat.sub_zero, Nat.add_one_sub_one,
    Nat.div_one]
  exact pushFoldGet0 (fun i => rowBody pk sig i) paramK i hi

/-- **THE ROW FOLD.** The deployed challenge conjunct, with verifyCore's `k`-row `Array.push` loop
replaced by ANY array whose `k` entries are the row bodies. Real `∀` over all inputs whose hint
decodes; no `native_decide`. -/
theorem challengeMatches_rows (pk M ctx sig : List UInt8) (A : Array Poly)
    (hh : (sigDecode sig).2.2.size = paramK)
    (hA : ∀ i, i < paramK → rowBody pk sig i = A[i]!) :
    challengeMatches pk M ctx sig
      = (shake256 (muOf pk M ctx ++ w1Encode A) 48 == (sigDecode sig).1) := by
  rw [challengeMatches_w1Of pk M ctx sig hh, w1Encode_congr _ A]
  intro i hi
  rw [w1Of_get pk sig i hi]
  exact hA i hi

#assert_axioms arrExt
#assert_axioms ofFn_get!
#assert_axioms pushFoldGet
#assert_axioms pushFoldGet0
#assert_axioms scaleT1_size
#assert_axioms w1Encode_congr
#assert_axioms azOf_eq
#assert_axioms rowBody_eq_execRow
#assert_axioms challengeMatches_w1Of
#assert_axioms w1Of_get
#assert_axioms challengeMatches_rows

end Dregg2.Crypto.VerifyCoreArgRows
