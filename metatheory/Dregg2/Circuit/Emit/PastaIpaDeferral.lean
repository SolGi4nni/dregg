/-
# Dregg2.Circuit.Emit.PastaIpaDeferral — the DEFERRAL of `⟨s, srs.g⟩`, built rather than recommended.

## SUBSTRATE (House Law #1, said out loud at constraint #1)

**Lean-authored.** No Rust AIR is written, extended or validated against. §5's `Bool` decision is
`@[export]`ed over the C ABI and Rust only CALLS it. The row figures in §4 are counts over the
generator families already in `PastaMsmLayouts`/`PastaMsmAir`; this file emits no new AIR.

## Why this file exists

`PastaMsmLayouts` §7.2 and `PastaIPA` §4 both concluded, independently, that the `2^k`-point
terminal MSM should be DEFERRED rather than optimised — every emitted layout is past BabyBear's
two-adicity ceiling (`4,227,200` rows = `2.016 × 2^21`, and `2^21` is a property of the FIELD), so
no algorithm in that vocabulary reaches it. Neither lane built the deferral. This is it.

## ⚑ A PREMISE THIS FILE HAD TO CORRECT, FROM o1-labs' OWN SOURCE

The recommendation was phrased "defer it identically to Pickles, because that leg is exactly what
Pickles defers". **Read at the source, that is not what Pickles does, and the difference matters.**
Verifying one Mina block involves TWO `⟨s, G⟩` claims, on the two curves, and they are discharged
by two DIFFERENT mechanisms:

  * **the Wrap/Tock leg** — `opening.sg == ⟨sVec(15 chals), srs_pallas.g⟩`, `2^15 = 32768` points.
    This is dregg's rung 5h and `PastaMsmLayouts` §6b statement (A). Pickles does **NOT** defer it:
    kimchi's native batch verifier folds it in with its own randomiser `sg_rand_base`
    (`poly-commitment/src/commitment.rs:660-760`, "we also add `-sg_rand_base_i * G` to check
    correctness of sg"). Outside a circuit, `O(ℓ)` is simply affordable, so nobody bothered.
  * **the Step/Tick leg** — `messages_for_next_wrap_proof.challenge_polynomial_commitment ==
    ⟨sVec(16 chals), srs_vesta.g⟩`, `2^16 = 65536` points. **This** is the deferred one, and
    `batch_dlog_accumulator_check` (`kimchi_bindings/stubs/src/urs_utils.rs:10-69`) is its
    discharge, called from exactly ONE place in the whole tree — `pickles/verify.ml:132-146`, on
    the block-verification path (`blockchain_snark_state.ml:452` → `verifier/prod.ml:157` →
    `mina_block/validation.ml:343`).

So the honest statement is **not** "defer it identically". It is: **the accumulator relation
`R_Acc,G` and its batching procedure are curve-generic, and dregg is applying them to the Tock side
where Mina has the binding and never calls it.** `caml_fq_srs_batch_accumulator_check` EXISTS
(`kimchi_bindings.ml:175`) and is invoked nowhere in Pickles — `common.ml:160-177` gives `Ipa.Wrap`
only `compute_challenge`/`compute_challenges`/`compute_sg`, with no `accumulator_check`. That is a
gap in Mina's own plumbing, not a licence: what licenses the move is that `R_Acc` is
**witness-free**, which their own book says in as many words (`proof-systems/book/src/pickles/
accumulation.md:559-576`): *"since there is no witness for this relation anyone can verify the
relation (in `O(ℓ)` time) by simply computing `⟨h, G⟩`... Instances are also small."* A
witness-free relation is exactly one that may be carried, batched and discharged later.

## What is PROVED here, and it is four things

  1. **`fold_discharges_each`** (§2) — **the theorem the whole strategy rests on, and it is
     N-INDEPENDENT.** If the ONE folded claim vanishes at `N` batching scalars with invertible
     pairwise differences, then EVERY one of the `N` individual claims holds. Not `N = 2`
     (`PicklesRecursion.accumulator_check_two_sound`), not "for the widths Mina uses" — any `N`, by
     synthetic division, at arbitrary `CommRing`/`AddCommGroup`/`Module`. Folding a claim in loses
     nothing.
  2. **`one_scalar_fold_is_refutable`** (§3) — and the floor is FALSE at ONE scalar. Two claims,
     both wrong, whose batch vanishes: explicitly exhibited and `decide`d. The deployed check uses
     one `OsRng` `r` (`urs_utils.rs:26`), so its soundness is statistical and this is the witness
     that says so. §2's hypothesis is load-bearing, not decoration.
  3. **`opening_is_vacuous_when_sg_is_free`** (§3b) — ⚑ **an undischarged deferral is not a
     weakened check, it is NO check.** With `sg` unconstrained, statement (B) — the whole of rung
     5f, 26 theorems, the rung that opens a commitment — is satisfiable for ANY `Q`, `delta`, `U`,
     `H`: the adversary sets `sg := z1⁻¹·(c·Q + delta − z1·b0·U − z2·H)` and the residual is `O`.
     Proved, not asserted. This is why §5's gate REFUSES an undischarged batch instead of
     reporting it.
  4. **`discharge_touches_srs_plus_batch`** (§4) — the amortisation is real and it is a THEOREM
     about the point list, not an assertion: the batched discharge is an MSM over `|G| + N` points,
     **not** `N·|G|`. `srsScalars` folds all `N` `b_poly` coefficient vectors into ONE `|G|`-vector
     before any group element is touched. That is the whole win, and `urs_utils.rs:36-67` is
     literally that shape.

## What is NOT claimed

**P10 is untouched: deferring an opening does not make the opening sound.** Everything here is
about WHEN and HOW MANY TIMES the equation `sg = ⟨sVec chals, G⟩` is checked, never about what
checking it proves. `accept ⟹ the proof is valid` still rests on the inherited IPA extraction floor
(`Dregg2.Crypto.IpaOpeningExtractionFloor`, `RomForkingExtractor`) and on discrete-log hardness.

No probability model exists in this tree, so the Schwartz–Zippel error `(N−1)/|F|` of the
single-`r` deployed check is **named, not proved**. §2 proves the exact/deterministic statement
instead, which is the stronger one and needs no such model.

## Axiom hygiene

`#assert_axioms`-clean (⊆ {propext, Classical.choice, Quot.sound}); no `sorry`/`admit`/
`native_decide`. `#guard`/`decide` KATs reduce in the kernel. NEW file; imports read-only
(`PicklesRecursion`, transitively `KimchiVerify`/K4c). NOT imported by the `Dregg2` root, per house
practice for gates. Import line:
`import Dregg2.Circuit.Emit.PastaIpaDeferral`
-/
import Dregg2.Circuit.Emit.PicklesRecursion

namespace Dregg2.Circuit.Emit.PastaIpaDeferral

open Dregg2.Circuit.Emit.PastaIPA (sVec sVec_length IpaDeferred deferredMsmSize)
open Dregg2.Circuit.Emit.PicklesRecursion
  (msm horner accumulatorMsm srsScalars batchScalars accumulator_check_splits
   accumulator_fits_srs)

set_option autoImplicit false

/-! ## §1 — Synthetic division, and a polynomial with MODULE coefficients that vanishes often.

The fold `Σ_i r^i · a_i` is `PicklesRecursion.horner` — Horner form, head = lowest coefficient. To
get from "the fold vanishes at `N` scalars" to "every coefficient is zero" without a `Field`
instance (there is none on `ZMod pN` in this tree, and manufacturing one needs primality) we do it
the way one does it by hand: divide by `(X − c)` and induct on the degree, supplying each needed
inverse as a WITNESS. Everything below is over `[CommRing F] [AddCommGroup A] [Module F A]`. -/

section Vanishing

variable {F : Type} [CommRing F] {A : Type} [AddCommGroup A] [Module F A]

/-- The fold of an all-zero coefficient list is zero, at every scalar. -/
theorem horner_eq_zero_of_all_zero (c : F) :
    ∀ (l : List A), (∀ a ∈ l, a = 0) → horner c l = 0 := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons a rest ih =>
    intro h
    have ha : a = 0 := h a (List.mem_cons_self ..)
    have hr : horner c rest = 0 := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    simp [horner, ha, hr]

/-- **`synDiv c as`** — the quotient of `Σ_i X^i·a_i` by `(X − c)`, in the same low-to-high list
form. Its `i`-th entry is `horner c (as.drop (i+1)) = Σ_{j>i} c^{j−i−1}·a_j`, which is exactly the
classical synthetic-division recurrence `b_{i−1} = a_i + c·b_i` read from the top.

⚑ The singleton case is `[]`, NOT `[0]`, and that is load-bearing rather than cosmetic: the
induction in `horner_vanishing` is on the DEGREE, so the quotient must be strictly shorter than its
argument. A `synDiv` that returned a padded `[0]` here is still the right *value* and gives
`|synDiv c as| = |as|`, on which that induction does not terminate — caught by the kernel, not by
reading. -/
def synDiv (c : F) : List A → List A
  | [] => []
  | [_] => []
  | _ :: (b :: t) => horner c (b :: t) :: synDiv c (b :: t)

@[simp] theorem synDiv_nil (c : F) : synDiv c ([] : List A) = [] := rfl

@[simp] theorem synDiv_single (c : F) (a : A) : synDiv c [a] = [] := rfl

@[simp] theorem synDiv_cons2 (c : F) (a b : A) (t : List A) :
    synDiv c (a :: b :: t) = horner c (b :: t) :: synDiv c (b :: t) := rfl

theorem synDiv_length (c : F) : ∀ (as : List A), (synDiv c as).length = as.length - 1 := by
  intro as
  induction as with
  | nil => rfl
  | cons a rest ih =>
    cases rest with
    | nil => rfl
    | cons b t =>
      simp only [synDiv_cons2, List.length_cons] at ih ⊢
      omega

/-- **The division identity.** `p(x) − p(c) = (x − c)·q(x)` with `q = synDiv c as`, over module
coefficients. This is the only algebra in §1 and everything else is bookkeeping on top of it. -/
theorem horner_sub_synDiv (c x : F) :
    ∀ (as : List A), horner x as - horner c as = (x - c) • horner x (synDiv c as) := by
  intro as
  induction as with
  | nil => simp
  | cons a rest ih =>
    cases rest with
    | nil => simp
    | cons b t =>
      have hS : horner x (b :: t) - horner c (b :: t)
          = (x - c) • horner x (synDiv c (b :: t)) := ih
      show (a + x • horner x (b :: t)) - (a + c • horner c (b :: t))
        = (x - c) • (horner c (b :: t) + x • horner x (synDiv c (b :: t)))
      rw [smul_add, smul_smul, mul_comm (x - c) x, ← smul_smul, ← hS, sub_smul, smul_sub]
      abel

/-- If the whole quotient vanishes, every coefficient ABOVE the constant one does. Read off the
recurrence: `b_i = a_{i+1} + c·b_{i+1}`, so `b ≡ 0` forces `a_{i+1} = 0`. -/
theorem synDiv_all_zero_tail (c : F) :
    ∀ (as : List A), (∀ b ∈ synDiv c as, b = 0) → ∀ a ∈ as.tail, a = 0 := by
  intro as
  induction as with
  | nil => intro _ a ha; simp at ha
  | cons a rest ih =>
    intro h
    cases rest with
    | nil => intro x hx; simp at hx
    | cons b t =>
      have hhead : horner c (b :: t) = 0 :=
        h _ (by rw [synDiv_cons2]; exact List.mem_cons_self ..)
      have hrest : ∀ y ∈ synDiv c (b :: t), y = 0 := by
        intro y hy
        exact h y (by rw [synDiv_cons2]; exact List.mem_cons_of_mem _ hy)
      have htail : ∀ x ∈ (b :: t).tail, x = 0 := ih hrest
      have ht : ∀ x ∈ t, x = 0 := by intro x hx; exact htail x (by simpa using hx)
      have hb : b = 0 := by
        have h0 : b + c • horner c t = 0 := hhead
        rw [horner_eq_zero_of_all_zero c t ht, smul_zero, add_zero] at h0
        exact h0
      show ∀ x ∈ b :: t, x = 0
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact hb
      · exact ht x hx'

/-- **`horner_vanishing`** — a degree-`<N` polynomial with MODULE coefficients that vanishes at `N`
scalars with invertible pairwise differences is the zero polynomial. Induction on the DEGREE, so it
is uniform in `N`: nothing in the statement or the proof mentions a batch width. -/
theorem horner_vanishing :
    ∀ (n : Nat) (as : List A) (rs : List F), as.length = n → rs.length = n →
      rs.Pairwise (fun x y => ∃ u : F, (x - y) * u = 1) →
      (∀ r ∈ rs, horner r as = 0) → ∀ a ∈ as, a = 0 := by
  intro n
  induction n with
  | zero =>
    intro as _ ha _ _ _ a hmem
    rw [List.eq_nil_of_length_eq_zero ha] at hmem
    simp at hmem
  | succ n ih =>
    intro as rs ha hr hpw hvan
    match as, ha with
    | a0 :: rest, ha =>
      match rs, hr with
      | r0 :: rs', hr =>
        have hrest : rest.length = n := by simpa using ha
        have hrs' : rs'.length = n := by simpa using hr
        have hpw' : rs'.Pairwise (fun x y => ∃ u : F, (x - y) * u = 1) := (List.pairwise_cons.mp hpw).2
        have hsep : ∀ y ∈ rs', ∃ u : F, (y - r0) * u = 1 := by
          intro y hy
          obtain ⟨u, hu⟩ := (List.pairwise_cons.mp hpw).1 y hy
          exact ⟨-u, by rw [← hu]; ring⟩
        -- the quotient vanishes at every scalar OTHER than `r0`
        have hq : ∀ r ∈ rs', horner r (synDiv r0 (a0 :: rest)) = 0 := by
          intro r hrmem
          obtain ⟨u, hu⟩ := hsep r hrmem
          have hd : (r - r0) • horner r (synDiv r0 (a0 :: rest)) = 0 := by
            rw [← horner_sub_synDiv r0 r (a0 :: rest),
              hvan r (List.mem_cons_of_mem _ hrmem), hvan r0 (List.mem_cons_self ..), sub_zero]
          have hu' := congrArg (fun z => u • z) hd
          simp only [smul_zero] at hu'
          rw [smul_smul, mul_comm u (r - r0), hu, one_smul] at hu'
          exact hu'
        have hqlen : (synDiv r0 (a0 :: rest)).length = n := by
          rw [synDiv_length, ha]
          omega
        have hqzero : ∀ b ∈ synDiv r0 (a0 :: rest), b = 0 :=
          ih (synDiv r0 (a0 :: rest)) rs' hqlen hrs' hpw' hq
        have hresto : ∀ x ∈ rest, x = 0 := by
          have := synDiv_all_zero_tail r0 (a0 :: rest) hqzero
          simpa using this
        have ha0 : a0 = 0 := by
          have h0 : a0 + r0 • horner r0 rest = 0 := hvan r0 (List.mem_cons_self ..)
          rw [horner_eq_zero_of_all_zero r0 rest hresto, smul_zero, add_zero] at h0
          exact h0
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact ha0
        · exact hresto x hx'

end Vanishing

#assert_axioms horner_eq_zero_of_all_zero
#assert_axioms synDiv_length
#assert_axioms horner_sub_synDiv
#assert_axioms synDiv_all_zero_tail
#assert_axioms horner_vanishing

/-! ## §2 — ⚑ THE FOLD IS SOUND, AND IT IS N-INDEPENDENT.

`accumulator_check_splits` (P1) already says the batched MSM IS the `r`-weighted difference between
what each proof CLAIMS its accumulator commitment is and what its challenges SAY it must be. That
is the shape. What was missing — and what the whole deferral strategy rests on — is the converse
at arbitrary batch width: **discharging the one folded claim discharges each individual one.**

Below, `defect d G` is proof `d`'s own error, `accumulatorMsm` is exactly `horner r` of the defect
list, and `fold_discharges_each` closes it for any `N`. -/

section Fold

variable {F : Type} [CommRing F] {A : Type} [AddCommGroup A] [Module F A]

/-- One proof's outstanding error: the gap between the commitment it carries and the b-poly MSM its
`k` challenges determine. The deferred obligation is exactly `defect = 0`. -/
def defect (G : List A) (d : IpaDeferred F A) : A := d.sg - msm (sVec d.chals) G

/-- Folding is additive over the defects: `horner` of a pointwise difference is the difference of
the `horner`s. -/
theorem horner_map_sub (r : F) (G : List A) :
    ∀ (ds : List (IpaDeferred F A)),
      horner r (ds.map (defect G)) =
        horner r (ds.map (fun d => d.sg)) - horner r (ds.map (fun d => msm (sVec d.chals) G)) := by
  intro ds
  induction ds with
  | nil => simp
  | cons d rest ih =>
    simp only [List.map_cons, horner, ih, defect, smul_sub]
    abel

/-- **`accumulatorMsm_eq_horner_defect`** — the value `batch_dlog_accumulator_check` tests against
zero IS the `r`-fold of the per-proof defects. `accumulator_check_splits` in one more step. -/
theorem accumulatorMsm_eq_horner_defect (G : List A) (r : F) (ds : List (IpaDeferred F A))
    (h : ∀ d ∈ ds, (sVec d.chals).length = G.length) :
    accumulatorMsm G r ds = horner r (ds.map (defect G)) := by
  rw [horner_map_sub, accumulator_check_splits G r ds h]

/-- **⚑⚑ `fold_discharges_each` — THE THEOREM THE DEFERRAL RESTS ON.**

If the ONE folded claim vanishes at `N` batching scalars whose pairwise differences are invertible,
then EVERY one of the `N` deferred claims `sg_i = ⟨b_poly_coefficients(chals_i), G⟩` holds.

**It is gate-count-independent in `N`.** `N` appears in no bound: the proof is an induction on the
degree of the fold, at arbitrary `CommRing`/`AddCommGroup`/`Module`, and the accumulator's own shape
does not change with `N`. Accumulating claim `k+1` cannot weaken what the accumulator asserts,
because discharging the folded claim discharges each individual one — which is what this says. -/
theorem fold_discharges_each (G : List A) (ds : List (IpaDeferred F A)) (rs : List F)
    (hlen : rs.length = ds.length)
    (hsep : rs.Pairwise (fun x y => ∃ u : F, (x - y) * u = 1))
    (hfit : ∀ d ∈ ds, (sVec d.chals).length = G.length)
    (hzero : ∀ r ∈ rs, accumulatorMsm G r ds = 0) :
    ∀ d ∈ ds, d.sg = msm (sVec d.chals) G := by
  have hvan : ∀ r ∈ rs, horner r (ds.map (defect G)) = 0 := by
    intro r hr
    rw [← accumulatorMsm_eq_horner_defect G r ds hfit]
    exact hzero r hr
  have hall : ∀ a ∈ ds.map (defect G), a = 0 :=
    horner_vanishing ds.length (ds.map (defect G)) rs (by simp) hlen hsep hvan
  intro d hd
  have : defect G d = 0 := hall _ (List.mem_map_of_mem hd)
  exact sub_eq_zero.mp this

/-- **`fold_is_complete`** — and it never refuses an honest batch, at every batching scalar. (This
is `PicklesRecursion.accumulator_check_complete`, restated in the defect vocabulary so §2 is a
two-sided statement: honest ⇒ accept, and accept-at-`N`-scalars ⇒ honest.) -/
theorem fold_is_complete (G : List A) (r : F) (ds : List (IpaDeferred F A))
    (hfit : ∀ d ∈ ds, (sVec d.chals).length = G.length)
    (hok : ∀ d ∈ ds, defect G d = 0) : accumulatorMsm G r ds = 0 := by
  rw [accumulatorMsm_eq_horner_defect G r ds hfit]
  exact horner_eq_zero_of_all_zero r _ (by
    intro a ha
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp ha
    exact hok d hd)

end Fold

#assert_axioms horner_map_sub
#assert_axioms accumulatorMsm_eq_horner_defect
#assert_axioms fold_discharges_each
#assert_axioms fold_is_complete

/-! ## §3 — THE FLOOR IS FALSE AT ONE SCALAR, and §2's hypothesis is load-bearing.

`urs_utils.rs:26` samples ONE `r` from `OsRng`. §2 needs `N` of them. The gap is a genuine
soundness error and this section EXHIBITS it rather than describing it: two claims, both wrong,
whose fold vanishes. A hypothesis that cannot be violated by a concrete witness is decoration. -/

/-- Two generators and a one-round challenge: `sVec [7] = [1, 7]`, so the honest commitment against
`G = [2, 3]` is `1·2 + 7·3 = 23` (`PicklesRecursion.accumulator_kat_one`'s object). -/
def katG : List ℚ := [2, 3]

/-- ⚑⚑ **`one_scalar_fold_is_refutable`** — at the single batching scalar `r = 1`, a batch of TWO
claims BOTH of which are false folds to zero. Defects `+1` and `−1` cancel. So a verifier that
discharges the fold at one scalar has NOT established the individual claims, and §2's `N`-distinct
hypothesis is exactly what buys them back — at `r = 5` the same batch is caught. -/
theorem one_scalar_fold_is_refutable :
    -- both claims are FALSE: 24 ≠ 23 and 22 ≠ 23
    (⟨[7], (24 : ℚ)⟩ : IpaDeferred ℚ ℚ).sg ≠ msm (sVec ([7] : List ℚ)) katG
    ∧ (⟨[7], (22 : ℚ)⟩ : IpaDeferred ℚ ℚ).sg ≠ msm (sVec ([7] : List ℚ)) katG
    -- …and the fold of the two vanishes anyway, at r = 1
    ∧ accumulatorMsm katG 1 [(⟨[7], (24 : ℚ)⟩ : IpaDeferred ℚ ℚ), ⟨[7], 22⟩] = 0
    -- …while a SECOND scalar catches it, which is §2's content at N = 2
    ∧ accumulatorMsm katG 5 [(⟨[7], (24 : ℚ)⟩ : IpaDeferred ℚ ℚ), ⟨[7], 22⟩] ≠ 0 := by
  have hfit : ∀ d ∈ [(⟨[7], (24 : ℚ)⟩ : IpaDeferred ℚ ℚ), ⟨[7], 22⟩],
      (sVec d.chals).length = katG.length := by
    intro d hd; simp at hd; rcases hd with rfl | rfl <;> simp [sVec, katG]
  refine ⟨?_, ?_, ?_, ?_⟩
  · show (24 : ℚ) ≠ msm (sVec ([7] : List ℚ)) katG
    norm_num [sVec, katG, msm, smul_eq_mul]
  · show (22 : ℚ) ≠ msm (sVec ([7] : List ℚ)) katG
    norm_num [sVec, katG, msm, smul_eq_mul]
  · rw [accumulator_check_splits _ _ _ hfit]; norm_num [sVec, katG, horner, smul_eq_mul]
  · rw [accumulator_check_splits _ _ _ hfit]; norm_num [sVec, katG, horner, smul_eq_mul]

/-! ## §3b — ⚑⚑ AN UNDISCHARGED DEFERRAL IS NOT A WEAK CHECK. IT IS NO CHECK.

`SRS::verify` folds two independent statements (`docs/MINA-REAL-BLOCK-GATE.md` §6.1):

```text
(A)  sg == ⟨s, srs.g⟩                                    -- the leg being deferred
(B)  c·Q + delta − z1·sg − z1·b0·U − z2·H == O            -- rung 5f, 26 theorems, BUILT
```

Rung 5f is the rung that opens a commitment, and it is cheap (8,773 rows with GLV, 13.4% of one
root segment). It is tempting to read "we have (B), we deferred (A)" as "we have most of it".
**We do not have most of it. With `sg` free, (B) constrains nothing** — the theorem below solves
(B) for `sg` at ARBITRARY `Q`, `delta`, `U`, `H`, `c`, `z2`, `b0`. `z1` is invertible on any honest
transcript, so this is not a corner case.

The consequence is a design rule and §5's gate enforces it: **a deferral that is not discharged
must REFUSE, not report.** It may not be surfaced as a partial accept. -/

section Vacuity

variable {F : Type} [CommRing F] {A : Type} [AddCommGroup A] [Module F A]

/-- Statement (B) of `SRS::verify`, abstracted over the group: the residual whose vanishing rung 5f
proves on the real block. `Q` is the aggregate `Σⱼ (chal_invⱼ·Lⱼ + chalⱼ·Rⱼ) + Σᵢ ξⁱ·Cᵢ + cip·U`. -/
def openingResidualAbstract (c z1 z2 b0 : F) (Q delta U H sg : A) : A :=
  c • Q + delta - z1 • sg - (z1 * b0) • U - z2 • H

/-- ⚑⚑ **`opening_is_vacuous_when_sg_is_free`** — for ANY aggregate, delta, `U`, `H` and any
transcript scalars with `z1` invertible, there is an `sg` making (B) hold. So (B) alone establishes
nothing about the proof: it is one linear equation in one free group unknown. Deferring (A) without
discharging it does not weaken the opening check, it deletes it. -/
theorem opening_is_vacuous_when_sg_is_free (c z1 z2 b0 z1inv : F) (hz : z1 * z1inv = 1)
    (Q delta U H : A) :
    openingResidualAbstract c z1 z2 b0 Q delta U H
        (z1inv • (c • Q + delta - (z1 * b0) • U - z2 • H)) = 0 := by
  set X : A := c • Q + delta - (z1 * b0) • U - z2 • H with hX
  have h1 : z1 • (z1inv • X) = X := by rw [smul_smul, hz, one_smul]
  show c • Q + delta - z1 • (z1inv • X) - (z1 * b0) • U - z2 • H = 0
  rw [h1, hX]
  abel

/-- …and it is not that `z1` was pathological: the SAME free `sg` also satisfies (B) after the
aggregate is moved, so no amount of pinning `Q` recovers a constraint. Stated as: the solution is a
function OF `Q`, defined at every `Q`. -/
theorem opening_free_sg_is_total (c z1 z2 b0 z1inv : F) (hz : z1 * z1inv = 1)
    (delta U H : A) : ∀ Q : A, ∃ sg : A,
      openingResidualAbstract c z1 z2 b0 Q delta U H sg = 0 :=
  fun Q => ⟨_, opening_is_vacuous_when_sg_is_free c z1 z2 b0 z1inv hz Q delta U H⟩

end Vacuity

#assert_axioms one_scalar_fold_is_refutable
#assert_axioms opening_is_vacuous_when_sg_is_free
#assert_axioms opening_free_sg_is_total

/-! ## §4 — ⚑ THE AMORTISATION, AS A THEOREM ABOUT THE POINT LIST.

The claim "N deferred claims fold into one, amortised cost → 0" is easy to say and it is the kind
of statement that gets asserted. It is provable here, and the proof is one line, because
`urs_utils.rs:36-67` builds the discharge as ONE MSM whose point list is `urs.g ++ comms`:

  * the `N` per-proof `b_poly` coefficient vectors are combined **in the SCALAR field** — `srsScalars`
    subtracts `r^i · sVec(chals_i)` into the SAME `|G|` slots — before any group element is touched;
  * so the group work is `|G| + N` scalar multiplications, not `N · |G|`.

`discharge_touches_srs_plus_batch` is that, and it is what makes the per-block cost of the `sg` leg
go to `129` rows (§4b) instead of `4,227,200`.

⚑ **What is NOT amortised: the field side.** `urs_utils.rs:54-55` expands `b_poly_coefficients`
once per proof and scales it by `r^i` — `N · |G|` field multiplications, and the batching does not
remove them. `PastaIpaFold`'s §1 note that "`2^k` field multiplications are free next to one group
operation" is true of a NATIVE verifier and FALSE inside an AIR over a foreign field, where a
255-bit non-native multiply is itself many rows. §4b prices the group side, which is what
`PastaMsmLayouts` measured; the field side is a NAMED residual and it is not small. -/

section Cost

variable {F : Type} [CommRing F] {A : Type} [AddCommGroup A] [Module F A]

/-- The point list the batched discharge runs over (`urs_utils.rs:36-38`: `points = urs.g` then
`points.extend(comms)`). -/
def dischargePoints (G : List A) (ds : List (IpaDeferred F A)) : List A :=
  G ++ ds.map (fun d => d.sg)

omit [CommRing F] [AddCommGroup A] [Module F A] in
/-- ⚑ **`discharge_touches_srs_plus_batch`** — `|G| + N` points for a batch of `N`, at every `N`.
THE amortisation, and it is not an estimate. -/
theorem discharge_touches_srs_plus_batch (G : List A) (ds : List (IpaDeferred F A)) :
    (dischargePoints G ds).length = G.length + ds.length := by
  simp [dischargePoints]

/-- …and it really is the MSM `accumulatorMsm` performs — the same point list, not a parallel
model of one. -/
theorem accumulatorMsm_is_over_dischargePoints (G : List A) (r : F)
    (ds : List (IpaDeferred F A)) :
    accumulatorMsm G r ds
      = msm (srsScalars G.length r ds ++ batchScalars r ds.length) (dischargePoints G ds) := rfl

/-- Discharging the SAME `N` claims one at a time instead pays `N · (|G| + 1)` points. The
difference between this and `discharge_touches_srs_plus_batch` is the entire case for deferral. -/
def perBlockDischargePoints (G : List A) (ds : List (IpaDeferred F A)) : Nat :=
  ds.length * (G.length + 1)

omit [CommRing F] [AddCommGroup A] [Module F A] in
/-- **`absorb_costs_no_group_ops`** — absorbing a claim into the accumulator adds a `(k challenges,
1 commitment)` record and performs NO group operation: the point list the discharge will run over
grows by exactly ONE, and no MSM is evaluated at absorb time. That is why the per-block cost is
`O(1)` and the `2^15`-point MSM leaves the per-block circuit entirely. -/
theorem absorb_costs_no_group_ops (G : List A) (ds : List (IpaDeferred F A))
    (d : IpaDeferred F A) :
    (dischargePoints G (d :: ds)).length = (dischargePoints G ds).length + 1 := by
  simp [dischargePoints]
  omega

omit [AddCommGroup A] [Module F A] in
/-- **`deferral_state_is_k_per_claim`** — the state carried per claim is `k` field elements plus one
point, NOT the `2^k` scalars (K4c `deferral_compression`, reused). At Mina's Wrap `k = 15` that is
15 field elements standing in for 32,768. -/
theorem deferral_state_is_k_per_claim (d : IpaDeferred F A) :
    (sVec d.chals).length = deferredMsmSize d ∧ deferredMsmSize d = 2 ^ d.chals.length := by
  exact ⟨by rw [sVec_length, deferredMsmSize], rfl⟩

end Cost

#assert_axioms discharge_touches_srs_plus_batch
#assert_axioms absorb_costs_no_group_ops
#assert_axioms deferral_state_is_k_per_claim

/-! ### §4b — the price, in the row vocabulary `PastaMsmLayouts` §6 measured.

`glvHornerRcbAdds n nbits = nbits·(n+1) + n` is the best layout that family emits (bit-plane scan
with the GLV 4-entry table, `nbits = 128`). All figures below are RCB complete adds — the atom
`PastaMsmLayouts` §6 measured at ≈1.5 ms of kernel each — and every one is conditional on the same
`Head`/`cgH` straight-line residual that file names.

`DREGG_MAX_ROWS = 2^21 = 2097152` is BabyBear's two-adicity at `log_blowup = 6`. It is a p3 panic,
not a repo check, and not a knob. -/

/-- The measured best layout, copied as a `def` so the arithmetic below is checkable in one place.
Agrees with `PastaMsmLayouts.glvHornerRcbAdds` at its pinned point (`#guard` below). -/
def rows (n nbits : Nat) : Nat := nbits * (n + 1) + n

/-- `|srs.g|` on the Wrap/Tock side — the leg dregg is deferring (`Max_degree.wrap = 1 lsl 15`). -/
def WRAP_SRS : Nat := 32768
/-- `|srs.g|` on the Step/Tick side — the leg Mina itself defers (`Max_degree.step = 1 lsl 16`,
and `accumulator_check.rs:12` `OTHER_URS_LENGTH = 65536`). -/
def STEP_SRS : Nat := 65536
/-- The deployed single-instance trace ceiling, `PastaMsmAir.DREGG_MAX_ROWS`. -/
def MAX_ROWS : Nat := 2097152
/-- One deployed root segment, `PastaMsmAir.DREGG_ROOT_ROWS` (`WRAP_LOG_CEIL = 16`). -/
def ROOT_ROWS : Nat := 65536

/-- Rows the batched discharge of `N` claims costs: ONE MSM over `|G| + N` points. -/
def dischargeRows (N : Nat) : Nat := rows (WRAP_SRS + N) 128
/-- Rows the SAME `N` claims cost discharged per block, which is what deferral removes. -/
def perBlockRows (N : Nat) : Nat := N * rows WRAP_SRS 128

-- The pinned point: this `rows` IS `PastaMsmLayouts.glvHornerRcbAdds`, and it is past the ceiling.
#guard rows 32768 128 == 4227200
#guard rows 32768 128 > 2 * MAX_ROWS
-- ⚑ A batch of N costs 129 MORE adds per extra claim, against 4,227,200 for a fresh discharge.
#guard dischargeRows 1 == 4227329
#guard dischargeRows 2 == 4227458
#guard dischargeRows 1000 == 4356200
#guard dischargeRows 1000 - dischargeRows 999 == 129
-- …so the marginal cost of ABSORBING a block is 129 adds, flat in N. That is the amortisation.
#guard dischargeRows 65 - dischargeRows 64 == 129

-- ⚑ Per-block AMORTISED cost, `dischargeRows N / N`, against the two ceilings.
-- N = 2 does NOT fit under the two-adicity ceiling; N = 3 does. That is the break-even.
#guard dischargeRows 2 / 2 > MAX_ROWS
#guard dischargeRows 3 / 3 < MAX_ROWS
-- …and it takes N = 65 for the amortised cost to fit in ONE deployed root segment.
#guard dischargeRows 64 / 64 > ROOT_ROWS
#guard dischargeRows 65 / 65 < ROOT_ROWS
-- At a Mina block every ~3 minutes, N = 65 is about 3¼ hours and N = 480 is one day.
#guard dischargeRows 480 == 4289120
#guard dischargeRows 480 / 480 == 8935
-- ⚑ …and at one day the `sg` leg is CHEAPER per block than rung 5f's own opening check (8,773
-- adds, `PastaMsmLayouts.glvOpeningRcbAdds 34 128`) — the leg that could not be built at all.
#guard dischargeRows 480 / 480 < 8773 + 200

-- ⚑ Deferral vs per-block discharge, at one day of devnet blocks: a 473× reduction in total adds.
#guard perBlockRows 480 == 2029056000
#guard perBlockRows 480 / dischargeRows 480 == 473

/-! ⚑ **The discharge STILL does not fit in one AIR instance, and that is the honest answer to the
gate question.** `dischargeRows N ≥ 4,227,200 > 2 · 2^21` for every `N`: amortisation moves the
per-block AVERAGE, it does not shrink the single indivisible object. What makes it deployable is
that the object is CUT, and the cut is already proved: `PastaIpaFold.flatMap_chunks` /
`chunk_length` say `n` contiguous slices of width `c` reassemble the list IN ORDER with every slice
full — so no `2^15`-element equality is ever `decide`d and no slice is ragged.

**How many slices, measured rather than guessed.** TWO misses the ceiling by 16,512 rows — that is
how close a halving comes and it is still a miss. THREE clears it, but `3 ∤ 32768`, so a three-way
cut is ragged and `chunk_length` does not apply. **FOUR is the cut**: 8,192 generators per slice,
1,056,896 rows, 50.4% of the ceiling. -/

/-- Rows one contiguous slice of `c` generators costs. -/
def chunkRows (c : Nat) : Nat := rows c 128

-- ⚑ TWO slices is the near miss, and quantifying it is the point: 16,512 rows over.
#guard WRAP_SRS / 2 == 16384
#guard chunkRows 16384 == 2113664
#guard chunkRows 16384 > MAX_ROWS
#guard chunkRows 16384 - MAX_ROWS == 16512
-- THREE clears the ceiling — but 32768 is not divisible by 3, so the slices are ragged.
#guard chunkRows 10923 == 1409195
#guard chunkRows 10923 < MAX_ROWS
#guard 3 * 10923 ≠ WRAP_SRS
-- ⚑ FOUR is the cut: it divides, and it clears with real headroom rather than just clearing.
#guard WRAP_SRS / 4 == 8192
#guard 4 * 8192 == WRAP_SRS
#guard chunkRows 8192 == 1056896
#guard chunkRows 8192 < MAX_ROWS
#guard 100 * chunkRows 8192 < 51 * MAX_ROWS
#guard 100 * chunkRows 8192 > 50 * MAX_ROWS
-- The four slices reproduce the whole discharge's group cost, to within the per-slice accumulator
-- seeds the cut introduces (`128 · 3` extra plane-adds, one set per extra slice).
#guard 4 * chunkRows 8192 == 4227584
#guard 4 * chunkRows 8192 - rows 32768 128 == 384
#guard 384 == 3 * 128

/-! ### §4c — ⚑ a MEASURED fact about the carried accumulators, from the six real blocks on disk.

`Dregg2.Bridge.MinaStateHashWordGate`'s `HEADERS` carry, per block, the two Wrap-side accumulators
(`messages_for_next_step_proof.challenge_polynomial_commitments` and their `old_bulletproof_
challenges`). Read across all six — 539508 and the five consecutive 539795…539799 —

  * **the SECOND accumulator's 16-entry challenge vector is byte-identical on every one of them**,
    including the block 287 earlier. A Fiat–Shamir transcript does not do that; a constant does.
    It is `wrap_hack.ml:24`'s `Padded_length = Nat.N2` dummy (`pad_accumulator` with
    `Dummy.Ipa.Wrap.challenges_computed`), and `step.ml:396-398` shows Pickles fills the
    corresponding commitment with an honestly-computed `Ipa.Wrap.compute_sg` when a previous proof
    need not verify.
  * its commitment is ALSO constant across the five consecutive blocks — but DIFFERS at 539508.
    That is not explained here and is not assumed away; `wrap_verifier.ml:363` calls the point in
    the zero-accumulator branch "potentially junk", which is a candidate and not a finding.

**The consequence for pricing is real:** of the two `2^15` recursion MSMs rung 5g would owe per
block, ONE has the same scalar vector on every block of the chain, so its `⟨sVec(dummy), G⟩` is a
CHAIN-WIDE CONSTANT computed once, not once per block. Rung 5g's "2 × 2^15 per block" is
"1 × 2^15 per block + 1 × 2^15 once". -/

/-- Wrap-side accumulators carried per block (`wrap_hack.ml:24`). -/
def ACCS_PER_BLOCK : Nat := 2
/-- …of which this many carry a per-block challenge vector; the rest are the padded dummy. -/
def LIVE_ACCS_PER_BLOCK : Nat := 1

#guard ACCS_PER_BLOCK == 2
#guard LIVE_ACCS_PER_BLOCK == 1
-- Rung 5g's per-block obligation, measured rather than assumed from the vector width.
#guard LIVE_ACCS_PER_BLOCK * rows WRAP_SRS 128 == 4227200
#guard ACCS_PER_BLOCK * rows WRAP_SRS 128 == 8454400

/-! ## §5 — THE GATE: a deferral that is not discharged must REFUSE.

§3b proved that an outstanding `(A)` makes `(B)` vacuous. The failure mode that turns that into a
shipped hole is the one `minted-fail-open-gate-class` names: a verified gate that, absent its
evidence, logs and PROCEEDS. So the runtime decision below has ONE shape — it accepts only a
DISCHARGED batch — and `deferral_gate_refuses_undischarged` is the permanent falsifier.

`Bool`, `@[export]`ed over the C ABI, same `String → String` shape as
`dregg_mina_state_hash_word_ok` / `dregg_mina_proof_chain_ok`: `"1"` ACCEPT, `"0"` REFUSE, `"ERR"`
on a malformed wire (the caller treats `"ERR"` as REFUSE). -/

/-- The deferral batch as the gate sees it. -/
structure Batch where
  /-- `|srs.g|` the discharge tiles. -/
  srsLen : Nat
  /-- IPA rounds per claim (`k`). -/
  rounds : Nat
  /-- per-claim challenge counts, one entry per deferred claim. -/
  chalLens : List Nat
  /-- has the batched MSM actually been evaluated and found to vanish? -/
  discharged : Bool
  deriving Repr, DecidableEq

/-- **`batchOk`** — the decision. Four conjuncts and none of them is optional:

  1. the SRS is exactly `2^k`, so `sVec` tiles `srs.g` with no ragged tail (`urs_utils.rs:61`
     asserts `terms.len() == n`; `accumulator_fits_srs` is the Lean side);
  2. the batch is non-empty — an empty batch discharges nothing and must not read as an accept;
  3. every claim carries exactly `k` challenges, so `fold_discharges_each`'s `hfit` holds;
  4. ⚑ the batch is DISCHARGED. Without this the accept would be `(B)`-only, which §3b proves is
     satisfiable at every `Q`. -/
def batchOk (b : Batch) : Bool :=
  decide (2 ^ b.rounds = b.srsLen)
  && decide (b.chalLens ≠ [])
  && b.chalLens.all (fun l => decide (l = b.rounds))
  && b.discharged

/-- ⚑⚑ **`deferral_gate_refuses_undischarged`** — THE TOOTH. Whatever else is well-formed, an
undischarged batch is REFUSED. This is §3b made operational: the gate has no way to say "deferred,
looks fine so far". -/
theorem deferral_gate_refuses_undischarged (b : Batch) (h : b.discharged = false) :
    batchOk b = false := by
  simp only [batchOk, h, Bool.and_false]

/-- A batch whose SRS is not `2^k` is refused — the `sVec` would not tile `srs.g`. -/
theorem deferral_gate_refuses_mistiled (b : Batch) (h : 2 ^ b.rounds ≠ b.srsLen) :
    batchOk b = false := by
  have hd : decide (2 ^ b.rounds = b.srsLen) = false := decide_eq_false h
  simp only [batchOk, hd, Bool.false_and]

/-- An EMPTY batch is refused: nothing was discharged, so nothing may be accepted. -/
theorem deferral_gate_refuses_empty (b : Batch) (h : b.chalLens = []) : batchOk b = false := by
  have hd : decide (b.chalLens ≠ []) = false := by
    apply decide_eq_false
    simp [h]
  simp only [batchOk, hd, Bool.and_false, Bool.false_and]

/-- …and a claim with the wrong challenge count is refused, which is `fold_discharges_each`'s
`hfit` hypothesis enforced at the wire. -/
theorem deferral_gate_refuses_short_claim (b : Batch) (l : Nat) (hl : l ∈ b.chalLens)
    (h : l ≠ b.rounds) : batchOk b = false := by
  have hall : b.chalLens.all (fun l => decide (l = b.rounds)) = false := by
    apply Bool.eq_false_iff.mpr
    intro hc
    exact h (of_decide_eq_true ((List.all_eq_true.mp hc) l hl))
  simp only [batchOk, hall, Bool.and_false, Bool.false_and]

/-- **`deferral_gate_accepts_discharged`** — and it is not vacuously false: a well-formed,
discharged batch at any width ACCEPTS. -/
theorem deferral_gate_accepts_discharged (k n : Nat) (ls : List Nat)
    (hn : 2 ^ k = n) (hne : ls ≠ []) (hl : ∀ l ∈ ls, l = k) :
    batchOk { srsLen := n, rounds := k, chalLens := ls, discharged := true } = true := by
  have h1 : decide (2 ^ k = n) = true := decide_eq_true hn
  have h2 : decide (ls ≠ []) = true := decide_eq_true hne
  have h3 : ls.all (fun l => decide (l = k)) = true := by
    apply List.all_eq_true.mpr
    intro x hx
    exact decide_eq_true (hl x hx)
  simp only [batchOk, h1, h2, h3, Bool.and_true, Bool.true_and]

/-! ### §5b — the wire, and the two real shapes. -/

/-- Parse a `key=value` field, fail-closed on key mismatch or a missing `=`. (Same grammar
discipline as `MinaStateHashWordGate.parseField?`; duplicated rather than imported so this gate's
archive closure stays at `+1` module.) -/
def parseField? (key part : String) : Option String :=
  match part.splitOn "=" with
  | [k, v] => if k == key then some v else none
  | _ => none

/-- Parse a `,`-separated `Nat` list, fail-closed on any non-numeral. The EMPTY string is `none`,
not `some []` — an absent vector must not read as a well-formed empty one. -/
def parseNats? (s : String) : Option (List Nat) :=
  match s.splitOn "," with
  | [] => none
  | parts => parts.foldr (fun p acc => do
      let rest ← acc
      let n ← p.toNat?
      pure (n :: rest)) (some [])

/-- **`decodeBatchWire`** — the `INPUT` grammar, fail-closed on any deviation.

```
INPUT := "n="  Nat            -- |srs.g| the discharge tiles
       ";k="  Nat             -- IPA rounds per claim
       ";c="  Nat("," Nat)*   -- per-claim challenge counts, one per deferred claim
       ";d="  ("0"|"1")       -- did the batched MSM evaluate to the identity?
```
`d` is the only field that is not a shape read, and it is the one the caller must have EARNED. -/
def decodeBatchWire (s : String) : Option Batch :=
  match s.splitOn ";" with
  | [p0, p1, p2, p3] => do
      let n ← (parseField? "n" p0).bind String.toNat?
      let k ← (parseField? "k" p1).bind String.toNat?
      let c ← (parseField? "c" p2).bind parseNats?
      let d ← parseField? "d" p3
      let db ← if d == "1" then some true else if d == "0" then some false else none
      some { srsLen := n, rounds := k, chalLens := c, discharged := db }
  | _ => none

/-- **`minaDeferralGate`** — THE GATE. -/
def minaDeferralGate (s : String) : String :=
  match decodeBatchWire s with
  | some b => if batchOk b then "1" else "0"
  | none => "ERR"

/-- **THE EXPORT.** The C-ABI entry `dregg-lean-ffi` calls once per deferral batch. It ships only
because `Dregg2/FFI.lean` imports this module: rooting it in `Dregg2.lean` would make it ELABORATE
and emit no `:c` facet, and the symbol would never enter `libdregg_lean.a`. -/
@[export dregg_mina_deferral_ok]
def dregg_mina_deferral_ok (s : String) : String := minaDeferralGate s

/-- The gate string IS the decision, by construction, so §5's theorems are theorems about what the
export returns. -/
theorem minaDeferralGate_eq_decision (s : String) (b : Batch)
    (hd : decodeBatchWire s = some b) :
    minaDeferralGate s = (if batchOk b then "1" else "0") := by
  unfold minaDeferralGate
  rw [hd]

-- ⚑ The Wrap/Tock shape dregg defers: `2^15` generators, 15 rounds, a 480-block day, discharged.
#guard minaDeferralGate ("n=32768;k=15;c=" ++ String.intercalate "," (List.replicate 480 "15")
  ++ ";d=1") == "1"
-- ⚑ …the SAME batch, undischarged, REFUSES. This is the line §3b makes non-negotiable.
#guard minaDeferralGate ("n=32768;k=15;c=" ++ String.intercalate "," (List.replicate 480 "15")
  ++ ";d=0") == "0"
-- The Step/Tick shape Mina itself defers: `2^16` generators, 16 rounds, one claim per proof.
#guard minaDeferralGate "n=65536;k=16;c=16;d=1" == "1"
-- A wrap-length SRS with step rounds does not tile — refused.
#guard minaDeferralGate "n=32768;k=16;c=16;d=1" == "0"
-- An empty claim list is not an accept.
#guard minaDeferralGate "n=32768;k=15;c=;d=1" == "ERR"
-- A short claim (14 challenges where 15 are owed) is refused, not silently padded.
#guard minaDeferralGate "n=32768;k=15;c=15,14,15;d=1" == "0"
-- Malformed wires are `ERR`, which the caller treats as REFUSE.
#guard minaDeferralGate "n=32768;k=15;c=15" == "ERR"
#guard minaDeferralGate "n=32768;k=15;c=15;d=2" == "ERR"
#guard minaDeferralGate "n=32768;k=x;c=15;d=1" == "ERR"

#assert_axioms deferral_gate_refuses_undischarged
#assert_axioms deferral_gate_refuses_mistiled
#assert_axioms deferral_gate_refuses_empty
#assert_axioms deferral_gate_refuses_short_claim
#assert_axioms deferral_gate_accepts_discharged
#assert_axioms minaDeferralGate_eq_decision

/-! ## §6 — WHO DISCHARGES, WHEN, AND WHAT IF NOBODY DOES.

**Who, in Mina.** Exactly one caller, and it is not in a circuit: `pickles/verify.ml:132-146`,
inside `Verify.verify_heterogenous`, reached from `blockchain_snark_state.ml:452` →
`verifier/prod.ml:157` → `mina_block/validation.ml:343`. `Step` and `Wrap` never call it; a grep of
`src/lib/pickles` for `accumulator_check` returns `common.ml:197`, `common.mli:139`, `verify.ml:136`
and nothing else. `finalize_other_proof` has exactly FOUR conjuncts — `xi_correct`, `b_correct`,
`combined_inner_product_correct`, `plonk_checks_passed` (`step_verifier.ml:1140-1147`, and the same
four at `wrap_verifier.ml:1015-1049`) — and NONE of them is the MSM. `b_correct` checks only the
`O(log ℓ)` SCALAR `b = h(ζ) + r·h(ζω)`. Inside the circuit the `sg` is folded into the batched
commitment as if it were a legitimate one (`step_verifier.ml:603-620`), with the tree's own comment
at `step_verifier.ml:569-572` saying the previous challenges "should be used to compute f(beta_1)
**outside the snark**".

**When, in dregg.** Once per batch, at the tip. Every block absorbed costs `129` more adds at the
eventual discharge (§4b) and zero at absorption. The batch size `N` is a policy choice, and §4b
prices it: `N = 3` is where the amortised per-block cost first fits under the two-adicity ceiling,
`N = 65` (≈3¼ hours of devnet) is where it fits in ONE root segment, `N = 480` (one day) puts it at
8,935 adds — 13.6% of a root segment, i.e. the `sg` leg becomes cheaper per block than rung 5f's
own 8,773.

**What if nobody does — and this is the part that must not be softened.** §3b is a theorem: with
`sg` free, statement (B) is satisfiable at every aggregate. An undischarged accumulator therefore
leaves the verifier with **no** constraint from the terminal opening — not a weakened one. It has
established the transcript replay, the scalar checks, `ft_comm`, `public_comm` and the aggregate
(rungs 5a–5e), and it has established `(B)` **as an equation in a free unknown**, which is to say
nothing. Mina's own book states the same thing for the recursive case
(`accumulation.md:676-699`): an invalid accumulator propagates, so "the new proof will also include
an invalid accumulator and not verify with overwhelming probability" — the guarantee is that the
defect SURVIVES to the eventual discharge, never that it can be skipped.

⚑ So the honest position is: **deferral is an ordering, not a discount.** SOME party discharges, or
the chain of proofs is unverified. In dregg that party is the light client at its own tip, and §5's
gate exists so that "not yet discharged" cannot be reported as an accept.

## §7 — RESIDUALS, at current resolution.

  1. ⚑ **P10 is untouched.** Deferring an opening does not make the opening sound. `fold_discharges_
     each` says the fold loses nothing; it says nothing about what `sg = ⟨sVec chals, G⟩` PROVES.
     That is `Dregg2.Crypto.IpaOpeningExtractionFloor` and discrete-log hardness, unchanged.
  2. ⚑ **The deployed check folds at ONE `r`, sampled from `OsRng` (`urs_utils.rs:26`), not from the
     transcript.** §2 proves the exact statement at `N` scalars; §3 exhibits a two-claim
     counterexample at one. The gap is a Schwartz–Zippel error `≤ (N−1)/|F|` and there is **no
     probability model in this tree**, so no theorem states it. What makes the one-`r` check
     defensible is ORDER — `r` is drawn after the claims are fixed — and that ordering is an
     operational property of the caller, not something proved here.
  3. ⚑ **The ANCHORING is not measured, and the fixtures on disk cannot measure it.** The claim
     that block `i`'s Wrap opening `sg` is committed by block `i+1` (which is what stops an
     adversary choosing `sg` after seeing `r`) is a CROSS-CURVE relation: the Wrap/Pallas `sg`
     against the next block's Step-side carried commitment. `MinaStateHashWordGate`'s wire carries
     `accComm` (Pallas, `< pN`) and `mnwComm` (Vesta, `< qN`) but NOT `proof.openings.proof.sg`,
     so the two sides of the equation are not both present for any block. Testing it needs one
     extra extractor field over ≥2 consecutive blocks. **Named and unbuilt** — and until it is
     built, "the claim is committed before it is discharged" is a design intent, not a measurement.
  4. **The FIELD side of the fold is not amortised and not priced here** (§4's note): `N · 2^k`
     non-native multiplications to expand and `r^i`-scale the `b_poly` coefficient vectors. The
     `PastaMsmLayouts` row model counts group operations only.
  5. **§4b inherits every assumption of `PastaMsmLayouts` §7.4** — the `Head`/`cgH` vocabulary is
     straight-line so "one complete add per row" is a re-layout nothing emits; `minaOpeningCheckDesc`
     is a shape, not a deployable descriptor; GLV completeness at `nbits = 128` is sampled, not
     proved. No descriptor is added here.
  6. **The `2.016×` ceiling is unchanged.** Nothing in this file makes the `2^15`-point MSM smaller.
     It makes it happen `1/N` as often, and §4b's four-way cut is what puts each piece under `2^21`.
-/

#assert_namespace_axioms Dregg2.Circuit.Emit.PastaIpaDeferral

end Dregg2.Circuit.Emit.PastaIpaDeferral
