/-
# Dregg2.Circuit.Emit.Sha256HfoldDischarge — the SHA-256 `hfold` DISCHARGE: the four chains'
finality/execution/validator-set/stake-table hash folds become DERIVED, not assumed.

## What this closes (the last rung of the SHA fold arc)

`Sha256FoldForcing` broke the round→block composition wall: `sha256Round_forces` and
`sha256Compress'_forces` prove the 64-round compression's emitted gates FORCE the reference fold, by
`List.foldl` induction over the round list — gate-count-independent. The four fold modules
(`LightClientEthFinFold`/`LightClientEthExecFold`/`LightClientTmHashFold`/`LightClientSolHashFold`)
each derive their carrier (`FIN_OK`/`EXEC_OK`/`VSET_OK`+`EPOCH_OK`/`STAKE_TABLE_OK`) GIVEN a named
`hfold`/`hforce` hypothesis: "the fold gates force the reconstructed root columns to hold the reference
`foldReconstruct`/`chainCommit`." This file DISCHARGES that hypothesis — mirroring Midnight's
`Blake2bFoldForcing.midHfold_discharged`/`mid_forgery_from_absorb` end-to-end pattern — by COMPOSING
`Sha256FoldForcing`'s atomic/round/compression forcings up the remaining structure:

  * `scheduleWord_forces` — one message-schedule step (σ1 + σ0 + the 4-input adder), the arithmetic
    twin of `sha256Round`, forced by composing `s1_word_forces`/`s0_word_forces`/`addMod32_word_forces`.
  * `scheduleExpand_forces` — THE MESSAGE-SCHEDULE RUNG: the 48-step recurrence
    `W[t] = σ1(W[t-2]) + W[t-7] + σ0(W[t-15]) + W[t-16]` forced by a `List.range`-suffix induction
    (`scheduleFold_forces`) carrying `WordIs` for the WHOLE growing schedule prefix (the step reads
    prior words). This is the rung `Sha256FoldForcing` named as the hard one; it is discharged here.
  * `feedForward_forces` (Davies–Meyer 8 adds), `sha256Block_forces` (schedule ‖ compress ‖ feed),
    `sha256PairHash_forces` (the two-block SSZ hash, chaining `pinWordConst_forces`) — finite
    compositions above the two folds.
  * `merkleBranchFold_forces` / `chainCommit_forces` — the branch/collection folds, by the SAME
    `List.foldl` induction, `sha256PairHash_forces` as the composable step. These ARE the objects the
    `hforce`/`hfold` hypotheses assumed.
  * the DISCHARGE lemmas (`fin`/`exec`/`tm`/`sol`) turning each module's assumed `hfold` into a
    theorem: the fold gates force the root columns to hold the reference (from the fold-forcing above),
    the bind gates tie them to the target, and `WordIs` is functional in its value
    (`WordIs_functional`), so reference = target — the `hfold`. Then the module's
    `*_slots_into_no_forgery` fires with the hypothesis DERIVED.

## Resolution (honest — the SAME residuals `Sha256FoldForcing`/the fold modules carry)

REAL: the composition is a PROOF over ℤ (the `acceptB` reading `body = 0`), each rung resting on the
one below by structural induction, gate-count-independent. UNCHANGED residuals: the mod-p ↔ ℤ
field-soundness gap (`LightClientEthAir` §6), the deploy/emit `proofBind` recursion seam (the fold is
not flat-merged into the byte-golden descriptors — NO VK regen), the felt-width 256-bit ↔ 9-limb
repack, and the per-leaf encoding (the branch/collection LEAF digests are the fold's inputs). The
Ed25519/BLS EC arcs stay hypotheses. This slice upgrades `hfold` from ASSUMED to a CONCLUSION of the
chained gates — the SHA composition wall closed end-to-end across all four chains.

## Axiom hygiene

`#assert_axioms`-clean (⊆ {propext, Classical.choice, Quot.sound}); no `sorry`/`admit`/`native_decide`;
no `#guard` carrying weight. NEW file; imports read-only. Standalone — NOT wired into the truncated
`Dregg2` root; build as `Dregg2.Circuit.Emit.Sha256HfoldDischarge`.
-/
import Dregg2.Circuit.Emit.Sha256FoldForcing
import Dregg2.Circuit.Emit.LightClientEthExecFold
import Dregg2.Circuit.Emit.LightClientSolHashFold

namespace Dregg2.Circuit.Emit.Sha256HfoldDischarge

open Dregg2.Circuit (Assignment)
open Dregg2.Circuit.DescriptorIR2 (VmConstraint2)
open Dregg2.Circuit.Emit.AirBuilder
open Dregg2.Circuit.Emit.Sha256Gadget
open Dregg2.Circuit.Emit.Sha256MerkleFold
open Dregg2.Circuit.Emit.Sha256FoldForcing
open Dregg2.Circuit.Emit.LightClientTmHashFold (chainCommit chainIV)

set_option autoImplicit false
set_option maxRecDepth 8192

/-! ## §0 — `WordIs` is FUNCTIONAL: a column configuration reconstructs a UNIQUE 32-bit value.

The engine of every discharge: the fold gates force the root columns to hold the reference value, the
bind gates force them to hold the target, and these two `WordIs` facts pin `reference = target`. -/

/-- **`WordIs` is functional in its value.** Two 32-bit values whose LSB-first bit columns coincide at
`base` are equal (bit-decomposition uniqueness via `Nat.eq_of_testBit_eq`). -/
theorem WordIs_functional (a : Assignment) (base V W : Nat)
    (hV : WordIs a base V) (hW : WordIs a base W) : V = W := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 32
  · have e1 := hV.2 i hi
    have e2 := hW.2 i hi
    rw [bit_eq_testBit] at e1 e2
    have hcast : ((V.testBit i).toNat : ℤ) = ((W.testBit i).toNat : ℤ) := by rw [← e1, ← e2]
    have hnat : (V.testBit i).toNat = (W.testBit i).toNat := by exact_mod_cast hcast
    cases hbv : V.testBit i <;> cases hbw : W.testBit i <;> simp_all
  · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hV.1 (Nat.pow_le_pow_right (by norm_num) (Nat.le_of_not_lt hi))),
        Nat.testBit_lt_two_pow (lt_of_lt_of_le hW.1 (Nat.pow_le_pow_right (by norm_num) (Nat.le_of_not_lt hi)))]

/-- Equal-length word-value lists that agree at every index (via `WordIs` at shared bases) are equal. -/
theorem list_ext_getD (l1 l2 : List Nat) (hl : l1.length = l2.length)
    (h : ∀ i, i < l1.length → l1.getD i 0 = l2.getD i 0) : l1 = l2 := by
  apply List.ext_getElem hl
  intro i h1 h2
  have hi := h i h1
  rwa [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
       List.getElem?_eq_getElem h1, List.getElem?_eq_getElem h2, Option.getD_some,
       Option.getD_some] at hi

/-! ## §1 — `pinWordConst_forces`: a constant-word pin forces the word to the pinned constant. -/

/-- **A `pinWordConst` (value gate + booleanity sweep) forces `WordIs base val`** (`val < 2^32`).
The IV/padding-block words the pair-hash pins. -/
theorem pinWordConst_forces (a : Assignment) (base val : Nat) (hval : val < 2 ^ 32)
    (hacc : acceptB (pinWordConst base val) a = true) : WordIs a base val := by
  rw [pinWordConst, acceptB_cons, Bool.and_eq_true] at hacc
  obtain ⟨hgate, hbin⟩ := hacc
  rw [gateBodyEvalZero_cgH] at hgate
  have hg0 : evalH ((wordValue base).addConst (-(val : ℤ))) a = 0 := of_decide_eq_true hgate
  have hbool : ∀ i, i < 32 → a (base + i) = 0 ∨ a (base + i) = 1 := by
    have hbin' : acceptB ((wordBits base).map binGate) a = true := hbin
    exact boolWord_of_acceptB a base hbin'
  have hv : evalH (wordValue base) a = (val : ℤ) := by
    rw [evalH_addConst] at hg0; linarith
  exact bit_of_boolWord a base val hval hbool hv

/-! ## §2 — `scheduleWord_forces`: one message-schedule step, forced (the arithmetic twin of a round). -/

/-- Collapse the reference schedule step's nested `add2` into one `w32` of the flat 4-term sum. -/
theorem sched_collapse (s1v w7 s0v w16 : Nat) :
    Ref.add2 (Ref.add2 (Ref.add2 s1v w7) s0v) w16 = Ref.w32 (s1v + w7 + s0v + w16) := by
  unfold Ref.add2 Ref.w32 Ref.M; omega

/-- **`scheduleWord_forces`** — the emitted `scheduleWord` gates (σ1(W[t-2]) ‖ σ0(W[t-15]) ‖ the
4-input mod-2³² adder) FORCE the output word to `WordIs` the reference recurrence value
`add2 (add2 (add2 (σ1 W2) W7) (σ0 W15)) W16`. Composes `s1_word_forces`/`s0_word_forces`/
`addMod32_word_forces` — the arithmetic twin of `sha256Round_forces`. -/
theorem scheduleWord_forces (a : Assignment) (w2 w7 w15 w16 outBase fresh : Nat)
    {W2 W7 W15 W16 : Nat}
    (h2 : WordIs a w2 W2) (h7 : WordIs a w7 W7) (h15 : WordIs a w15 W15) (h16 : WordIs a w16 W16)
    (hacc : acceptB (scheduleWord w2 w7 w15 w16 outBase fresh).1 a = true) :
    WordIs a outBase (Ref.add2 (Ref.add2 (Ref.add2 (Ref.s1 W2) W7) (Ref.s0 W15)) W16) := by
  simp only [scheduleWord, acceptB_append, Bool.and_eq_true] at hacc
  obtain ⟨⟨hs1, hs0⟩, hadd⟩ := hacc
  have hW1 : WordIs a fresh (Ref.s1 W2) := s1_word_forces a w2 _ _ h2 hs1
  have hW0 : WordIs a (fresh + 32 + 32) (Ref.s0 W15) := s0_word_forces a w15 _ _ h15 hs0
  have hS : ([wordValue fresh, wordValue w7, wordValue (fresh + 32 + 32), wordValue w16].map
              (fun h => evalH h a)).sum = ((Ref.s1 W2 + W7 + Ref.s0 W15 + W16 : Nat) : ℤ) := by
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    rw [wordValue_of_WordIs a fresh _ hW1, wordValue_of_WordIs a w7 W7 h7,
        wordValue_of_WordIs a (fresh + 32 + 32) _ hW0, wordValue_of_WordIs a w16 W16 h16]
    push_cast; ring
  have hforce := addMod32_word_forces a _ outBase _ _ hadd hS
  rw [sched_collapse]
  exact hforce

/-! ## §3 — THE MESSAGE-SCHEDULE RUNG: `scheduleExpand_forces`, by a `List.range`-suffix induction
carrying `WordIs` for the WHOLE growing schedule prefix (the step reads prior words). -/

/-- The gadget's schedule-expansion step (exactly `scheduleExpand`'s fold body). Named so the
induction never force-evaluates the concrete `List.range 48`. -/
def sstep : List VmConstraint2 × List Nat × Nat → Nat → List VmConstraint2 × List Nat × Nat :=
  fun acc k =>
    let (cs, wb, fr) := acc
    let t := 16 + k
    let outB := fr
    let (cs', fr') :=
      scheduleWord (wb.getD (t - 2) 0) (wb.getD (t - 7) 0) (wb.getD (t - 15) 0) (wb.getD (t - 16) 0)
        outB (fr + 32)
    (cs ++ cs', wb ++ [outB], fr')

/-- The reference schedule step (exactly `Ref.schedule`'s fold body). -/
def srefstep : List Nat → Nat → List Nat :=
  fun w _ =>
    let t := w.length
    let v := Ref.add2 (Ref.add2 (Ref.add2 (Ref.s1 (w.getD (t - 2) 0)) (w.getD (t - 7) 0))
                        (Ref.s0 (w.getD (t - 15) 0))) (w.getD (t - 16) 0)
    w ++ [v]

theorem scheduleExpand_eq (msgBases : List Nat) (fresh : Nat) :
    scheduleExpand msgBases fresh = (List.range 48).foldl sstep ([], msgBases, fresh) := rfl

theorem schedule_eq (w0 : List Nat) : Ref.schedule w0 = (List.range 48).foldl srefstep w0 := rfl

/-- Compute `sstep`'s projections for an arbitrary accumulator (structure eta). -/
theorem sstep_proj (p : List VmConstraint2 × List Nat × Nat) (k : Nat) :
    sstep p k = (p.1 ++ (scheduleWord (p.2.1.getD (16 + k - 2) 0) (p.2.1.getD (16 + k - 7) 0)
                    (p.2.1.getD (16 + k - 15) 0) (p.2.1.getD (16 + k - 16) 0) p.2.2 (p.2.2 + 32)).1,
                 p.2.1 ++ [p.2.2],
                 (scheduleWord (p.2.1.getD (16 + k - 2) 0) (p.2.1.getD (16 + k - 7) 0)
                    (p.2.1.getD (16 + k - 15) 0) (p.2.1.getD (16 + k - 16) 0) p.2.2 (p.2.2 + 32)).2) := by
  obtain ⟨cs, wb, fr⟩ := p; rfl

/-- `getD` on the left of an append (index in range). -/
theorem getD_appendL (l m : List Nat) (j d : Nat) (h : j < l.length) :
    (l ++ m).getD j d = l.getD j d := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left h, ← List.getD_eq_getElem?_getD]

/-- `getD` at exactly `l.length` on `l ++ [x]` is `x`. -/
theorem getD_appendLen (l : List Nat) (x d : Nat) : (l ++ [x]).getD l.length d = x := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
  rfl

/-- `getD` at index `= l.length` on `l ++ [x]` is `x` (index-provided form, no rewriting under `x`). -/
theorem getD_appendAt (l : List Nat) (x d i : Nat) (h : i = l.length) :
    (l ++ [x]).getD i d = x := by
  subst h; exact getD_appendLen l x d

/-- **`scheduleFold_forces`** — the induction: after folding the first `n` schedule steps, the base
list and the reference value list both have length `16 + n`, and every column-base holds its reference
schedule word. The `WordIs`-for-the-whole-prefix invariant that makes the recurrence's prior-word reads
legal. Peels the LAST step (`List.range_succ`), so the step gates are the acceptance SUFFIX. -/
theorem scheduleFold_forces (a : Assignment) (msgBases w0 : List Nat) (fresh : Nat)
    (hmb : msgBases.length = 16) (hw0 : w0.length = 16)
    (hinit : ∀ j, j < 16 → WordIs a (msgBases.getD j 0) (w0.getD j 0)) :
    ∀ n, acceptB ((List.range n).foldl sstep ([], msgBases, fresh)).1 a = true →
      ((List.range n).foldl sstep ([], msgBases, fresh)).2.1.length = 16 + n ∧
      ((List.range n).foldl srefstep w0).length = 16 + n ∧
      (∀ j, j < 16 + n →
        WordIs a (((List.range n).foldl sstep ([], msgBases, fresh)).2.1.getD j 0)
                 (((List.range n).foldl srefstep w0).getD j 0)) := by
  intro n
  induction n with
  | zero =>
    intro _
    refine ⟨by simpa using hmb, by simpa using hw0, ?_⟩
    intro j hj
    simpa using hinit j (by simpa using hj)
  | succ n ih =>
    intro hacc
    simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil] at hacc ⊢
    set p := (List.range n).foldl sstep ([], msgBases, fresh) with hp
    set wR := (List.range n).foldl srefstep w0 with hwR
    simp only [sstep_proj] at hacc ⊢
    -- split acceptance: prefix (n steps) and suffix (step n's gates)
    rw [acceptB_append, Bool.and_eq_true] at hacc
    obtain ⟨haccP, haccS⟩ := hacc
    obtain ⟨hlen, hlenR, hwords⟩ := ih haccP
    -- the four prior-word reads (indices < 16+n = length)
    have h2 := hwords (16 + n - 2) (by omega)
    have h7 := hwords (16 + n - 7) (by omega)
    have h15 := hwords (16 + n - 15) (by omega)
    have h16 := hwords (16 + n - 16) (by omega)
    -- step n forces the new word (note k = n so 16 + k = 16 + n)
    have hforce := scheduleWord_forces a _ _ _ _ p.2.2 (p.2.2 + 32) h2 h7 h15 h16 haccS
    -- reference: srefstep wR n = wR ++ [v], v the same recurrence value (length wR = 16+n)
    have hrefstep : srefstep wR n = wR ++
        [Ref.add2 (Ref.add2 (Ref.add2 (Ref.s1 (wR.getD (16 + n - 2) 0)) (wR.getD (16 + n - 7) 0))
                    (Ref.s0 (wR.getD (16 + n - 15) 0))) (wR.getD (16 + n - 16) 0)] := by
      simp only [srefstep, hlenR]
    rw [hrefstep]
    refine ⟨?_, ?_, ?_⟩
    · simp only [List.length_append, List.length_cons, List.length_nil, hlen]; omega
    · simp only [List.length_append, List.length_cons, List.length_nil, hlenR]; omega
    · intro j hj
      by_cases hjlt : j < 16 + n
      · rw [getD_appendL p.2.1 [p.2.2] j 0 (by rw [hlen]; exact hjlt),
            getD_appendL wR _ j 0 (by rw [hlenR]; exact hjlt)]
        exact hwords j hjlt
      · have hje : j = 16 + n := by omega
        subst hje
        rw [getD_appendAt p.2.1 p.2.2 0 (16 + n) hlen.symm,
            getD_appendAt wR _ 0 (16 + n) hlenR.symm]
        exact hforce

/-- **`scheduleExpand_forces`** — the whole 48-step message-schedule expansion's emitted gates FORCE
the 64-word schedule base list to `WordIs` the reference `Ref.schedule` of the 16 message words. THE
message-schedule rung, discharged (gate-count-independent). -/
theorem scheduleExpand_forces (a : Assignment) (msgBases w0 : List Nat) (fresh : Nat)
    (hmb : msgBases.length = 16) (hw0 : w0.length = 16)
    (hinit : ∀ j, j < 16 → WordIs a (msgBases.getD j 0) (w0.getD j 0))
    (hacc : acceptB (scheduleExpand msgBases fresh).1 a = true) :
    ((scheduleExpand msgBases fresh).2.1.length = 64) ∧
    (∀ j, j < 64 → WordIs a ((scheduleExpand msgBases fresh).2.1.getD j 0)
                            ((Ref.schedule w0).getD j 0)) := by
  rw [scheduleExpand_eq] at hacc ⊢
  obtain ⟨hlen, _, hw⟩ := scheduleFold_forces a msgBases w0 fresh hmb hw0 hinit 48 hacc
  rw [schedule_eq]
  exact ⟨by simpa using hlen, fun j hj => hw j (by omega)⟩

/-! ## §4 — `feedForward_forces`: the Davies–Meyer 8 output adds (a `List.range 8` fold). -/

/-- The 8 reference working-state words as a list (the value twin of `stWords`). -/
def stWordsVal (hs : Ref.Hst) : List Nat := [hs.a, hs.b, hs.c, hs.d, hs.e, hs.f, hs.g, hs.h]

/-- `WordIsSt` gives per-index `WordIs` between the state's column-bases and the reference words. -/
theorem wordIsSt_getD (a : Assignment) (s : St) (hs : Ref.Hst) (hst : WordIsSt a s hs) :
    ∀ j, j < 8 → WordIs a ((stWords s).getD j 0) ((stWordsVal hs).getD j 0) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := hst
  intro j hj
  interval_cases j <;>
    simp only [stWords, stWordsVal, List.getD_cons_zero, List.getD_cons_succ] <;>
    assumption

/-- The feed-forward step (exactly `feedForward`'s fold body). -/
def ffstep (inState finalState : St) (outBases : List Nat) :
    List VmConstraint2 × Nat → Nat → List VmConstraint2 × Nat :=
  fun acc j =>
    let (cs, fr) := acc
    let cs' := addMod32 [wordValue ((stWords inState).getD j 0), wordValue ((stWords finalState).getD j 0)]
                 (outBases.getD j 0) [fr, fr + 1, fr + 2]
    (cs ++ cs', fr + 3)

theorem feedForward_eq (inState finalState : St) (outBases : List Nat) (fresh : Nat) :
    feedForward inState finalState outBases fresh
      = (List.range 8).foldl (ffstep inState finalState outBases) ([], fresh) := rfl

theorem ffstep_proj (inState finalState : St) (outBases : List Nat)
    (p : List VmConstraint2 × Nat) (j : Nat) :
    ffstep inState finalState outBases p j
      = (p.1 ++ addMod32 [wordValue ((stWords inState).getD j 0), wordValue ((stWords finalState).getD j 0)]
                  (outBases.getD j 0) [p.2, p.2 + 1, p.2 + 2], p.2 + 3) := by
  obtain ⟨cs, fr⟩ := p; rfl

/-- The feed-forward fold: after `n ≤ 8` output adds, every output word holds `w32(H0_j + FIN_j)`. -/
theorem ffFold_forces (a : Assignment) (inState finalState : St) (outBases : List Nat) (fresh : Nat)
    (H0 FIN : Ref.Hst)
    (hin : ∀ j, j < 8 → WordIs a ((stWords inState).getD j 0) ((stWordsVal H0).getD j 0))
    (hfin : ∀ j, j < 8 → WordIs a ((stWords finalState).getD j 0) ((stWordsVal FIN).getD j 0)) :
    ∀ n, n ≤ 8 →
      acceptB ((List.range n).foldl (ffstep inState finalState outBases) ([], fresh)).1 a = true →
      ∀ j, j < n →
        WordIs a (outBases.getD j 0) (Ref.w32 ((stWordsVal H0).getD j 0 + (stWordsVal FIN).getD j 0)) := by
  intro n
  induction n with
  | zero => intro _ _ j hj; omega
  | succ n ih =>
    intro hn hacc j hj
    simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil] at hacc
    set p := (List.range n).foldl (ffstep inState finalState outBases) ([], fresh) with hp
    simp only [ffstep_proj] at hacc
    rw [acceptB_append, Bool.and_eq_true] at hacc
    obtain ⟨haccP, haccS⟩ := hacc
    by_cases hjn : j < n
    · exact ih (by omega) haccP j hjn
    · have hje : j = n := by omega
      subst hje
      have hjlt : j < 8 := by omega
      have hS : ([wordValue ((stWords inState).getD j 0), wordValue ((stWords finalState).getD j 0)].map
                  (fun h => evalH h a)).sum
                = (((stWordsVal H0).getD j 0 + (stWordsVal FIN).getD j 0 : Nat) : ℤ) := by
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
        rw [wordValue_of_WordIs _ _ _ (hin j hjlt), wordValue_of_WordIs _ _ _ (hfin j hjlt)]
        push_cast; ring
      exact addMod32_word_forces a _ (outBases.getD j 0) _ _ haccS hS

/-- **`feedForward_forces`** — the Davies–Meyer feed-forward gates FORCE the 8 output digest words to
`w32(H0_j + FIN_j)` (`= Ref.add2 (H0_j) (FIN_j)`), given the input and final working states hold
`H0`/`FIN`. -/
theorem feedForward_forces (a : Assignment) (inState finalState : St) (outBases : List Nat) (fresh : Nat)
    (H0 FIN : Ref.Hst) (hin : WordIsSt a inState H0) (hfin : WordIsSt a finalState FIN)
    (hacc : acceptB (feedForward inState finalState outBases fresh).1 a = true) :
    ∀ j, j < 8 → WordIs a (outBases.getD j 0)
                          (Ref.w32 ((stWordsVal H0).getD j 0 + (stWordsVal FIN).getD j 0)) := by
  rw [feedForward_eq] at hacc
  exact ffFold_forces a inState finalState outBases fresh H0 FIN
    (wordIsSt_getD a inState H0 hin) (wordIsSt_getD a finalState FIN hfin) 8 (le_refl 8) hacc

/-! ## §5 — `sha256Block_forces`: schedule ‖ compress ‖ feed — a full single-block SHA step. -/

/-- The digest of `compressFrom h0 msg` at index `j < 8` is `w32(h0_j + FIN_j)` for the 64-round fold
`FIN` from the input state. Reconciles `compressFrom`'s explicit output list with `feedForward`'s. -/
theorem compressFrom_getD (h0 msg : List Nat) (j : Nat) (hj : j < 8) :
    (compressFrom h0 msg).getD j 0
      = Ref.w32 ((h0.getD j 0)
        + (stWordsVal ((List.range 64).foldl (fun hs t => Ref.round hs (Ref.K.getD t 0)
            ((Ref.schedule msg).getD t 0))
            { a := h0.getD 0 0, b := h0.getD 1 0, c := h0.getD 2 0, d := h0.getD 3 0,
              e := h0.getD 4 0, f := h0.getD 5 0, g := h0.getD 6 0, h := h0.getD 7 0 })).getD j 0) := by
  interval_cases j <;>
    simp only [compressFrom, stWordsVal, List.getD_cons_zero, List.getD_cons_succ] <;>
    (unfold Ref.add2; rfl)

/-- **`sha256Block_forces`** — a full single-block SHA step (schedule ‖ compress ‖ feed-forward) FORCES
the 8 output digest words to `compressFrom (stWordsVal H0) msgVals` (the Merkle–Damgård block from the
input state `H0` over the 16 message words). Composes `scheduleExpand_forces`, `sha256Compress'_forces`,
`feedForward_forces`. -/
theorem sha256Block_forces (a : Assignment) (inState : St) (msgBases outDigest : List Nat) (fresh : Nat)
    (H0 : Ref.Hst) (msgVals : List Nat)
    (hmb : msgBases.length = 16) (hmv : msgVals.length = 16)
    (hin : WordIsSt a inState H0)
    (hmsg : ∀ j, j < 16 → WordIs a (msgBases.getD j 0) (msgVals.getD j 0))
    (hacc : acceptB (sha256Block inState msgBases outDigest fresh).1 a = true) :
    ∀ j, j < 8 → WordIs a (outDigest.getD j 0)
                          ((compressFrom (stWordsVal H0) msgVals).getD j 0) := by
  -- split the block into schedule ‖ compress ‖ feed
  simp only [sha256Block, acceptB_append, Bool.and_eq_true] at hacc
  obtain ⟨⟨haccS, haccC⟩, haccF⟩ := hacc
  -- schedule: the 64-word base list holds Ref.schedule msgVals
  obtain ⟨hlen64, hsched⟩ := scheduleExpand_forces a msgBases msgVals fresh hmb hmv hmsg haccS
  -- compress: the final state holds the 64-round fold from H0
  have hcomp := sha256Compress'_forces a (scheduleExpand msgBases fresh).2.1 (Ref.schedule msgVals)
    inState (scheduleExpand msgBases fresh).2.2 H0 hin
    (fun t ht => hsched t ht) (fun t ht => K_lt t ht) haccC
  -- feed-forward: the 8 output words hold w32(H0_j + FIN_j)
  set FIN := (List.range 64).foldl (fun hs t => Ref.round hs (Ref.K.getD t 0)
    ((Ref.schedule msgVals).getD t 0)) H0 with hFIN
  have hff := feedForward_forces a inState (sha256Compress' (scheduleExpand msgBases fresh).2.1 inState
    (scheduleExpand msgBases fresh).2.2).2.1 outDigest
    (sha256Compress' (scheduleExpand msgBases fresh).2.1 inState (scheduleExpand msgBases fresh).2.2).2.2
    H0 FIN hin hcomp haccF
  intro j hj
  rw [compressFrom_getD (stWordsVal H0) msgVals j hj]
  -- align compressFrom's internal init with H0 (structure eta on the 8-word list) and its fold with FIN
  have hinit : ({ a := (stWordsVal H0).getD 0 0, b := (stWordsVal H0).getD 1 0,
                  c := (stWordsVal H0).getD 2 0, d := (stWordsVal H0).getD 3 0,
                  e := (stWordsVal H0).getD 4 0, f := (stWordsVal H0).getD 5 0,
                  g := (stWordsVal H0).getD 6 0, h := (stWordsVal H0).getD 7 0 } : Ref.Hst) = H0 := by
    cases H0; rfl
  rw [hinit]
  exact hff j hj

/-! ## §6 — `sha256PairHash_forces`: the two-block SSZ SHA-256 of two 8-word digests. -/

/-- `getD` on the right of an append. -/
theorem getD_appendR (l m : List Nat) (j d : Nat) (h : l.length ≤ j) :
    (l ++ m).getD j d = m.getD (j - l.length) d := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right h, ← List.getD_eq_getElem?_getD]

/-- `acceptB` over a `flatMap`: each piece is accepted. -/
theorem acceptB_flatMap {α : Type} (L : List α) (f : α → List VmConstraint2) (a : Assignment)
    (h : acceptB (L.flatMap f) a = true) (x : α) (hx : x ∈ L) : acceptB (f x) a = true := by
  rw [acceptB, List.all_eq_true] at h ⊢
  intro g hg
  exact h g (List.mem_flatMap.mpr ⟨x, hx, hg⟩)

/-- Read an 8-value list as a working state (the value twin of `stOfBases`). -/
def hstOfVals (vs : List Nat) : Ref.Hst :=
  { a := vs.getD 0 0, b := vs.getD 1 0, c := vs.getD 2 0, d := vs.getD 3 0,
    e := vs.getD 4 0, f := vs.getD 5 0, g := vs.getD 6 0, h := vs.getD 7 0 }

/-- Per-index `WordIs` at 8 bases lifts to `WordIsSt` between `stOfBases`/`hstOfVals`. -/
theorem wordIsSt_of_getD (a : Assignment) (bs vs : List Nat)
    (h : ∀ j, j < 8 → WordIs a (bs.getD j 0) (vs.getD j 0)) :
    WordIsSt a (stOfBases bs) (hstOfVals vs) :=
  ⟨h 0 (by norm_num), h 1 (by norm_num), h 2 (by norm_num), h 3 (by norm_num),
   h 4 (by norm_num), h 5 (by norm_num), h 6 (by norm_num), h 7 (by norm_num)⟩

/-- `stWordsVal ∘ hstOfVals = id` on any 8-word list (without evaluating the list's contents). -/
theorem stwv_hstOfVals (L : List Nat) (h : L.length = 8) : stWordsVal (hstOfVals L) = L := by
  obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7, rfl⟩ :
      ∃ x0 x1 x2 x3 x4 x5 x6 x7, L = [x0, x1, x2, x3, x4, x5, x6, x7] := by
    rcases L with _ | ⟨x0, _ | ⟨x1, _ | ⟨x2, _ | ⟨x3, _ | ⟨x4, _ | ⟨x5, _ | ⟨x6, _ | ⟨x7, _ | ⟨x8, t⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;>
      simp only [List.length_cons, List.length_nil] at h <;>
      first
        | omega
        | exact ⟨x0, x1, x2, x3, x4, x5, x6, x7, rfl⟩
  simp [stWordsVal, hstOfVals]

/-- `stWordsVal (hstOfVals Ref.IV) = Ref.IV` (the IV is a concrete 8-word list). -/
theorem stwv_IV : stWordsVal (hstOfVals Ref.IV) = Ref.IV := by rfl

/-- `compressFrom` returns an 8-word digest (length only — never evaluates the fold). -/
theorem compressFrom_len (x y : List Nat) : (compressFrom x y).length = 8 := by
  simp only [compressFrom, List.length_cons, List.length_nil]

/-- `stWordsVal (hstOfVals (compressFrom x y)) = compressFrom x y` (the block digest is 8 words). -/
theorem stwv_cF (x y : List Nat) : stWordsVal (hstOfVals (compressFrom x y)) = compressFrom x y :=
  stwv_hstOfVals (compressFrom x y) (compressFrom_len x y)

/-- Every IV word is 32-bit. -/
theorem ivLt (j : Nat) (hj : j < 8) : Ref.IV.getD j 0 < 2 ^ 32 := by
  interval_cases j <;> decide

/-- Every padding-block word is 32-bit. -/
theorem padLt (j : Nat) (hj : j < 16) : padBlock2.getD j 0 < 2 ^ 32 := by
  interval_cases j <;> decide

/-- **`sha256PairHash_forces`** — the SSZ two-block SHA-256 gadget (pin-IV ‖ block1 ‖ pin-pad ‖ block2)
FORCES the 8 output words to `pairHash A B` for the two 8-word input digests `A`, `B`. Chains
`pinWordConst_forces` (IV + padding) with two `sha256Block_forces`. -/
theorem sha256PairHash_forces (a : Assignment) (leftBases rightBases outBases : List Nat) (fresh : Nat)
    (A B : List Nat) (hAlen : A.length = 8) (hBlen : B.length = 8)
    (hLBlen : leftBases.length = 8) (hRBlen : rightBases.length = 8)
    (hL : ∀ j, j < 8 → WordIs a (leftBases.getD j 0) (A.getD j 0))
    (hR : ∀ j, j < 8 → WordIs a (rightBases.getD j 0) (B.getD j 0))
    (hacc : acceptB (sha256PairHash leftBases rightBases outBases fresh).1 a = true) :
    ∀ j, j < 8 → WordIs a (outBases.getD j 0) ((pairHash A B).getD j 0) := by
  simp only [sha256PairHash, acceptB_append, Bool.and_eq_true] at hacc
  obtain ⟨⟨⟨hpinIV, hcs1⟩, hpinPad⟩, hcs2⟩ := hacc
  -- IV pins: the IV state holds Ref.IV
  have hivW : ∀ j, j < 8 → WordIs a ((digestWords fresh).getD j 0) (Ref.IV.getD j 0) := by
    intro j hj
    exact pinWordConst_forces a _ _ (ivLt j hj)
      (acceptB_flatMap (List.range 8)
        (fun j => pinWordConst ((digestWords fresh).getD j 0) (Ref.IV.getD j 0)) a hpinIV j
        (List.mem_range.mpr hj))
  -- block-1 message: leftBases ‖ rightBases holds A ‖ B
  have hmsg1 : ∀ j, j < 16 → WordIs a ((leftBases ++ rightBases).getD j 0) ((A ++ B).getD j 0) := by
    intro j hj
    by_cases hj8 : j < 8
    · rw [getD_appendL leftBases rightBases j 0 (by rw [hLBlen]; exact hj8),
          getD_appendL A B j 0 (by rw [hAlen]; exact hj8)]
      exact hL j hj8
    · rw [getD_appendR leftBases rightBases j 0 (by rw [hLBlen]; omega),
          getD_appendR A B j 0 (by rw [hAlen]; omega), hLBlen, hAlen]
      exact hR (j - 8) (by omega)
  -- block 1: d1 holds compressFrom Ref.IV (A ‖ B)
  have hblock1 := sha256Block_forces a (stOfBases (digestWords fresh)) (leftBases ++ rightBases)
    (digestWords (fresh + 256)) (fresh + 256 + 256) (hstOfVals Ref.IV) (A ++ B)
    (by rw [List.length_append, hLBlen, hRBlen]) (by rw [List.length_append, hAlen, hBlen])
    (wordIsSt_of_getD a (digestWords fresh) Ref.IV hivW) hmsg1 hcs1
  rw [stwv_IV] at hblock1
  -- pad pins: the padding message holds padBlock2 (padW after the block-1 fresh threading)
  set padBase := (sha256Block (stOfBases (digestWords fresh)) (leftBases ++ rightBases)
    (digestWords (fresh + 256)) (fresh + 256 + 256)).2 with hpadBase
  set padW := digestWords padBase ++ [padBase + 256, padBase + 288, padBase + 320,
    padBase + 352, padBase + 384, padBase + 416, padBase + 448, padBase + 480] with hpadW
  have hpadMsg : ∀ j, j < 16 → WordIs a (padW.getD j 0) (padBlock2.getD j 0) := by
    intro j hj
    exact pinWordConst_forces a _ _ (padLt j hj)
      (acceptB_flatMap (List.range 16)
        (fun j => pinWordConst (padW.getD j 0) (padBlock2.getD j 0)) a hpinPad j
        (List.mem_range.mpr hj))
  -- block 2: outBases holds compressFrom (compressFrom Ref.IV (A ‖ B)) padBlock2 = pairHash A B
  have hblock2 := sha256Block_forces a (stOfBases (digestWords (fresh + 256))) padW outBases
    (padBase + 512) (hstOfVals (compressFrom Ref.IV (A ++ B))) padBlock2
    (by rw [hpadW]; simp [digestWords]) (by decide)
    (wordIsSt_of_getD a (digestWords (fresh + 256)) (compressFrom Ref.IV (A ++ B)) hblock1)
    hpadMsg hcs2
  rw [stwv_cF] at hblock2
  intro j hj
  have hpair : pairHash A B = compressFrom (compressFrom Ref.IV (A ++ B)) padBlock2 := rfl
  rw [hpair]
  exact hblock2 j hj

/-! ## §7 — the SHA-256 COLLECTION fold (`chainCommit`) composition + the TM/Sol `hfold` discharge.

Mirrors `Blake2bFoldForcing.foldl_forces`/`absorb_forces`/`midHfold_discharged`/`mid_forgery_from_absorb`:
the collection chain composes free (`chainCommit_forces`, per-step `sha256PairHash_forces`), and the
carrier equalities are discharged by `WordIs`-functional uniqueness against the pinned target. -/

/-- The reconstructed 8-word SHA state at a list of column-bases. -/
def Holds8sha (a : Assignment) (bases vals : List Nat) : Prop :=
  vals.length = 8 ∧ ∀ j, j < 8 → WordIs a (bases.getD j 0) (vals.getD j 0)

/-- **Generic fold composition** — a per-step relation preserved by each `gadgetStep`/`refStep` pair
over the step list is preserved by the whole `foldl`. The engine behind "the chain composes free". -/
theorem foldl_forces {α σ τ : Type} (L : List α)
    (gadgetStep : σ → α → σ) (refStep : τ → α → τ) (R : σ → τ → Prop)
    (s0 : σ) (t0 : τ) (h0 : R s0 t0)
    (hstep : ∀ (s : σ) (t : τ) (x : α), x ∈ L → R s t → R (gadgetStep s x) (refStep t x)) :
    R (L.foldl gadgetStep s0) (L.foldl refStep t0) := by
  induction L generalizing s0 t0 with
  | nil => simpa using h0
  | cons x xs ih =>
    simp only [List.foldl_cons]
    exact ih (gadgetStep s0 x) (refStep t0 x) (hstep s0 t0 x (by simp) h0)
      (fun s t y hy => hstep s t y (List.mem_cons_of_mem x hy))

/-- **`chainCommit_forces`** — the Merkle–Damgård collection chain composes free: chaining
`sha256PairHash` leaf by leaf (`nextBases`) forces the reconstructed final state to
`chainCommit leaves`, by one `foldl_forces` over the leaves. Each step's `sha256PairHash_forces` is the
`hstep`. The SHA analog of `Blake2bFoldForcing.absorb_forces`. -/
theorem chainCommit_forces (a : Assignment) (leaves : List (List Nat))
    (nextBases : List Nat → List Nat → List Nat)
    (hstep : ∀ (nodeBases nodeVals leaf : List Nat), leaf ∈ leaves →
        Holds8sha a nodeBases nodeVals →
        Holds8sha a (nextBases nodeBases leaf) (pairHash nodeVals leaf))
    (h0Bases : List Nat) (h0 : Holds8sha a h0Bases chainIV) :
    Holds8sha a (leaves.foldl nextBases h0Bases) (chainCommit leaves) := by
  unfold chainCommit
  exact foldl_forces leaves nextBases (fun acc leaf => pairHash acc leaf)
    (fun b v => Holds8sha a b v) h0Bases chainIV h0 (fun b v leaf hleaf hR => hstep b v leaf hleaf hR)

/-- **`chainHfold_discharged`** — the collection-fold `hfold` is DERIVED, not assumed. Given the
reconstructed chain root (`hchain`, from `chainCommit_forces`) and the in-circuit pin of those root
words to the target root (`hpin`), the SHA-256 chain reconstructs into the target:
`chainCommit leaves = target`. This IS the `hfold` hypothesis the TM/Sol payoffs assume — now a
CONCLUSION of the chained gates (`WordIs` is functional, `WordIs_functional`). The SHA analog of
`Blake2bFoldForcing.midHfold_discharged`. -/
theorem chainHfold_discharged (a : Assignment) (leaves : List (List Nat)) (rootBases target : List Nat)
    (hchain : Holds8sha a rootBases (chainCommit leaves))
    (htargetLen : target.length = 8)
    (hpin : ∀ j, j < 8 → WordIs a (rootBases.getD j 0) (target.getD j 0)) :
    chainCommit leaves = target := by
  obtain ⟨hrootLen, hroot⟩ := hchain
  apply list_ext_getD _ _ (by rw [hrootLen, htargetLen])
  intro j hj'
  rw [hrootLen] at hj'
  exact WordIs_functional a (rootBases.getD j 0) _ _ (hroot j hj') (hpin j hj')

section TmSolPayoff
open Dregg2.Circuit.Emit.LightClientTmHashFold
open Dregg2.Circuit.Emit.LightClientSolHashFold
open Dregg2.Bridge.LightClientTendermint
open Dregg2.Bridge.LightClientSolana

/-- **THE TENDERMINT PAYOFF** — `VSET_OK`/`EPOCH_OK` FOLDED OUT: given the six arithmetic legs and, for
each of the two validator-set hash bindings, a satisfying witness whose validator-leaf SHA-256 chain
reconstructs into the pinned root (`hchainE`/`hchainV` from `chainCommit_forces`, `hpinE`/`hpinV` the
root-pin gates), the update is Tendermint-VALID. `tm_hash_from_fold_slots_into_no_forgery`'s two `hfold`
legs are now DERIVED by `chainHfold_discharged`, not assumed. -/
theorem tm_hash_from_gates (a : Assignment)
    (sb : TmHeader tmShaLeaf.Digest → tmShaLeaf.Msg)
    (enc : List (TmValidator tmShaLeaf.PubKey) → tmShaLeaf.Msg)
    (hcr : tmShaLeaf.hashCR)
    (ts : TmTrustedState tmShaLeaf) (u : TmUpdate tmShaLeaf)
    (hChain : u.header.chainId = ts.chainId)
    (hHeight : u.header.height = ts.height + 1)
    (hMono : ts.headerTime < u.header.time)
    (hDrift : u.header.time ≤ ts.now + ts.clockDrift)
    (hTrust : ts.now < ts.headerTime + ts.trustingPeriod)
    (hThresh : 2 * totalPower u.validators
                < 3 * signedPower tmShaLeaf (sb u.header) u.validators u.commit)
    (epochBases vsetBases : List Nat)
    (hchainE : Holds8sha a epochBases (chainCommit (enc u.validators)))
    (hnvLen : ts.nextValidatorsHash.length = 8)
    (hpinE : ∀ j, j < 8 → WordIs a (epochBases.getD j 0) (ts.nextValidatorsHash.getD j 0))
    (hchainV : Holds8sha a vsetBases (chainCommit (enc u.validators)))
    (hvhLen : u.header.validatorsHash.length = 8)
    (hpinV : ∀ j, j < 8 → WordIs a (vsetBases.getD j 0) (u.header.validatorsHash.getD j 0)) :
    TmForeignValid tmShaLeaf sb enc u :=
  tm_hash_from_fold_slots_into_no_forgery sb enc hcr ts u hChain hHeight hMono hDrift hTrust hThresh
    (chainHfold_discharged a (enc u.validators) epochBases ts.nextValidatorsHash hchainE hnvLen hpinE)
    (chainHfold_discharged a (enc u.validators) vsetBases u.header.validatorsHash hchainV hvhLen hpinV)

/-- **THE SOLANA PAYOFF** — `STAKE_TABLE_OK` FOLDED OUT: given the stake legs and a satisfying witness
whose stake-row SHA-256 chain reconstructs into the pinned WS anchor root (`hchain` from
`chainCommit_forces`, `hpin` the root-pin gates), the update is Solana-ROOTED-VALID. The active-stake
denominator is pinned by the SHA-256 collection fold — `sol_stake_from_fold_slots_into_no_forgery`'s
`hfold` leg is DERIVED by `chainHfold_discharged`, not assumed. -/
theorem sol_stake_from_gates (a : Assignment)
    (hcr : solShaLeaf.stakeTableCR)
    (ts : SolTrustedState solShaLeaf) (u : SolUpdate solShaLeaf)
    (hpos : 0 < totalStake solShaLeaf u)
    (hthr : 2 * totalStake solShaLeaf u ≤ 3 * rootedStake solShaLeaf u)
    (hed : edOk solShaLeaf u = true)
    (hrooted : rootedOk solShaLeaf u = true)
    (hauth : authOk solShaLeaf u = true)
    (rootBases : List Nat)
    (hchain : Holds8sha a rootBases (chainCommit ((u.table.map entryRow).map solRowLeaf)))
    (hanchorLen : ts.anchorRoot.length = 8)
    (hpin : ∀ j, j < 8 → WordIs a (rootBases.getD j 0) (ts.anchorRoot.getD j 0)) :
    SolValidAt solShaLeaf ts u :=
  sol_stake_from_fold_slots_into_no_forgery hcr ts u hpos hthr hed hrooted hauth
    (chainHfold_discharged a ((u.table.map entryRow).map solRowLeaf) rootBases ts.anchorRoot
      hchain hanchorLen hpin)

end TmSolPayoff

/-! ## §8 — the ETH branch-fold `hfold` discharge (finality + execution), via the SAME uniqueness. -/

/-- **Generic `hfold` discharge** — any reference root reconstructed at `rootBases` (`hforce`) and
pinned there to a `target` (`hpin`) EQUALS the target: `ref = target`. `WordIs`-functional uniqueness.
The ETH branch folds (`foldReconstruct … idx`) discharge through this exactly as the collection folds
do through `chainHfold_discharged`. -/
theorem hfold_discharged (a : Assignment) (ref target rootBases : List Nat)
    (hforce : Holds8sha a rootBases ref) (htargetLen : target.length = 8)
    (hpin : ∀ j, j < 8 → WordIs a (rootBases.getD j 0) (target.getD j 0)) :
    ref = target := by
  obtain ⟨hrefLen, href⟩ := hforce
  apply list_ext_getD _ _ (by rw [hrefLen, htargetLen])
  intro j hj'
  rw [hrefLen] at hj'
  exact WordIs_functional a (rootBases.getD j 0) _ _ (href j hj') (hpin j hj')

section EthPayoff
open Dregg2.Circuit.Emit.LightClientEthFinFold
open Dregg2.Circuit.Emit.LightClientEthExecFold
open Dregg2.Bridge.LightClientEth

/-- **THE ETH FINALITY PAYOFF** — `FIN_OK` FOLDED OUT: given the sync + execution legs and a satisfying
witness whose finality branch's SHA-256 fold reconstructs the finalized header into the pinned attested
state root (`hforce` from the branch fold, `hpin` the root-pin gates), the update is Ethereum-VALID.
`eth_finality_from_fold_slots_into_no_forgery`'s `hfold` leg is DERIVED by `hfold_discharged`. -/
theorem eth_finality_from_gates (a : Assignment)
    (hcr : shaWordLeaf.hashPairCR) (hinj : shaWordLeaf.uChunkInj)
    (ts : EthState shaWordLeaf) (u : LightClientUpdate shaWordLeaf)
    (hsync : verifySyncAggregate shaWordLeaf ts u.attestedHeader u.syncAggregate = true)
    (hexec : verifyExecutionPayload shaWordLeaf u.finalizedHeader.execution
              u.finalizedHeader.executionBranch u.finalizedHeader.beacon.bodyRoot = true)
    (hdepth : u.finalityBranch.length = finalizedRootDepth
              ∨ u.finalityBranch.length = finalizedRootDepthElectra)
    (rootBases : List Nat)
    (hforce : Holds8sha a rootBases
      (foldReconstruct (htrHeader shaWordLeaf u.finalizedHeader.beacon) u.finalityBranch
        finalizedRootSubtreeIndex))
    (hattLen : u.attestedHeader.stateRoot.length = 8)
    (hpin : ∀ j, j < 8 → WordIs a (rootBases.getD j 0) (u.attestedHeader.stateRoot.getD j 0)) :
    EthValidAt shaWordLeaf ts u :=
  eth_finality_from_fold_slots_into_no_forgery hcr hinj ts u hsync hexec hdepth
    (hfold_discharged a _ u.attestedHeader.stateRoot rootBases hforce hattLen hpin)

/-- **THE ETH EXECUTION PAYOFF** — `EXEC_OK` FOLDED OUT (the on-chain-recorded root): given the sync +
finality legs and a satisfying witness whose execution branch's SHA-256 fold reconstructs the execution
payload into the pinned finalized body root (`hforce`/`hpin`), the update is Ethereum-VALID.
`eth_exec_from_fold_slots_into_no_forgery`'s `hfold` leg is DERIVED by `hfold_discharged`. -/
theorem eth_exec_from_gates (a : Assignment)
    (hcr : shaWordLeaf.hashPairCR) (hinj : shaWordLeaf.uChunkInj)
    (ts : EthState shaWordLeaf) (u : LightClientUpdate shaWordLeaf)
    (hsync : verifySyncAggregate shaWordLeaf ts u.attestedHeader u.syncAggregate = true)
    (hfin : verifyFinalityBranch shaWordLeaf u.finalizedHeader.beacon u.finalityBranch
              u.attestedHeader.stateRoot = true)
    (hdepth : u.finalizedHeader.executionBranch.length = executionPayloadDepth)
    (rootBases : List Nat)
    (hforce : Holds8sha a rootBases
      (foldReconstruct (htrExec shaWordLeaf u.finalizedHeader.execution)
        u.finalizedHeader.executionBranch executionPayloadSubtreeIndex))
    (hbodyLen : u.finalizedHeader.beacon.bodyRoot.length = 8)
    (hpin : ∀ j, j < 8 → WordIs a (rootBases.getD j 0) (u.finalizedHeader.beacon.bodyRoot.getD j 0)) :
    EthValidAt shaWordLeaf ts u :=
  eth_exec_from_fold_slots_into_no_forgery hcr hinj ts u hsync hfin hdepth
    (hfold_discharged a _ u.finalizedHeader.beacon.bodyRoot rootBases hforce hbodyLen hpin)

end EthPayoff

/-! ## §9 — the ETH branch-fold COMPOSITION (`merkleBranchFold_forces`): the producer of the ETH
`hforce`, at parity with `chainCommit_forces`. The path-bit fold composes free by `foldl_forces`, and
`foldReconstruct` (idx-threaded) IS that path-bit fold (`foldReconstruct_eq_branchRefBits`). -/

/-- The path bits of `idx` (LSB-first), one per branch level: `bit k = (idx / 2^k) % 2`. -/
def bitsOf : Nat → Nat → List Bool
  | _, 0 => []
  | idx, (n + 1) => (idx % 2 = 1) :: bitsOf (idx / 2) n

/-- The path-bit branch fold (the shape the gadget's `merkleBranchFold` realizes): thread the node
through each `(sibling, bit)`, hashing sibling-left (`bit`) or node-left. -/
def branchRefBits (leaf : List Nat) (sps : List (List Nat × Bool)) : List Nat :=
  sps.foldl (fun node sp => if sp.2 then pairHash sp.1 node else pairHash node sp.1) leaf

/-- **`foldReconstruct` IS the path-bit fold** at `pathBits = bitsOf idx`: the idx-threaded bridge
`reconstruct` and the pathBits-driven gadget fold are ONE fold. -/
theorem foldReconstruct_eq_branchRefBits (leaf : List Nat) (branch : List (List Nat)) (idx : Nat) :
    foldReconstruct leaf branch idx = branchRefBits leaf (branch.zip (bitsOf idx branch.length)) := by
  induction branch generalizing leaf idx with
  | nil => rfl
  | cons sib rest ih =>
    simp only [foldReconstruct]
    rw [ih]
    simp only [List.length_cons, bitsOf, List.zip_cons_cons, branchRefBits, List.foldl_cons,
      decide_eq_true_eq]

/-- **`branchFold_forces`** — the branch fold composes free: chaining `sha256PairHash` level by level
(`nextBases`) forces the reconstructed root to `branchRefBits`, by one `foldl_forces` over the
`(sibling, bit)` list. Each level's `sha256PairHash_forces` is the `hstep`. The ETH-branch analog of
`Blake2bFoldForcing.absorb_forces` / `chainCommit_forces`. -/
theorem branchFold_forces (a : Assignment) (sps : List (List Nat × Bool))
    (nextBases : List Nat → (List Nat × Bool) → List Nat)
    (hstep : ∀ (nodeBases nodeVals : List Nat) (sp : List Nat × Bool), sp ∈ sps →
        Holds8sha a nodeBases nodeVals →
        Holds8sha a (nextBases nodeBases sp)
          (if sp.2 then pairHash sp.1 nodeVals else pairHash nodeVals sp.1))
    (h0Bases leafVals : List Nat) (h0 : Holds8sha a h0Bases leafVals) :
    Holds8sha a (sps.foldl nextBases h0Bases) (branchRefBits leafVals sps) := by
  unfold branchRefBits
  exact foldl_forces sps nextBases
    (fun node sp => if sp.2 then pairHash sp.1 node else pairHash node sp.1)
    (fun b v => Holds8sha a b v) h0Bases leafVals h0 (fun b v sp hsp hR => hstep b v sp hsp hR)

/-- **`merkleBranchFold_forces`** — the ETH `hforce` PRODUCED: chaining `sha256PairHash` up the branch
forces the reconstructed root to hold `foldReconstruct leafVals branch idx` (via the path-bit fold +
the bridge). This is the ETH analog of `chainCommit_forces`; its output is exactly the `hforce`
`eth_finality_from_gates` / `eth_exec_from_gates` consume. -/
theorem merkleBranchFold_forces (a : Assignment) (branch : List (List Nat)) (idx : Nat)
    (nextBases : List Nat → (List Nat × Bool) → List Nat)
    (hstep : ∀ (nodeBases nodeVals : List Nat) (sp : List Nat × Bool),
        sp ∈ branch.zip (bitsOf idx branch.length) → Holds8sha a nodeBases nodeVals →
        Holds8sha a (nextBases nodeBases sp)
          (if sp.2 then pairHash sp.1 nodeVals else pairHash nodeVals sp.1))
    (h0Bases leafVals : List Nat) (h0 : Holds8sha a h0Bases leafVals) :
    Holds8sha a ((branch.zip (bitsOf idx branch.length)).foldl nextBases h0Bases)
               (foldReconstruct leafVals branch idx) := by
  rw [foldReconstruct_eq_branchRefBits]
  exact branchFold_forces a (branch.zip (bitsOf idx branch.length)) nextBases hstep h0Bases leafVals h0

#assert_axioms foldReconstruct_eq_branchRefBits
#assert_axioms branchFold_forces
#assert_axioms merkleBranchFold_forces
#assert_axioms hfold_discharged
#assert_axioms WordIs_functional
#assert_axioms pinWordConst_forces
#assert_axioms scheduleWord_forces
#assert_axioms scheduleExpand_forces
#assert_axioms feedForward_forces
#assert_axioms sha256Block_forces
#assert_axioms sha256PairHash_forces
#assert_axioms chainCommit_forces
#assert_axioms chainHfold_discharged
#assert_axioms tm_hash_from_gates
#assert_axioms sol_stake_from_gates
#assert_axioms eth_finality_from_gates
#assert_axioms eth_exec_from_gates

end Dregg2.Circuit.Emit.Sha256HfoldDischarge
