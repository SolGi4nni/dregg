/-
# Dregg2.Circuit.Emit.Sha256FoldForcing — the SHA-256 COMPOSITION forcing: `hfold` derived, not assumed.

## What this closes (the composition wall)

Every SHA-256 hash fold (ETH `FIN_OK`/`EXEC_OK`, tm/sol `VSET_OK`/…) is derived in `…FinFold` /
`…ExecFold` / `LightClient{Tm,Sol}HashFold` GIVEN a named `hfold`/`hforce` hypothesis: "the fold's
emitted gates FORCE the SHA output over the ~30k-gate-per-block chain." It was assumed because a
kernel `#guard` cannot REDUCE over ~30k gates. This file proves it instead — by structural induction
over the generators, composing the already-proven ATOMIC forcing lemmas (`xor3_forces`/
`chHead_forces`/`majHead_forces`/`addMod32_forces` in `Sha256Gadget`/`Sha256MerkleFold`) up the
round→block structure, WITHOUT evaluating a single gate. This is the honest completion of the SHA
fold arc: it upgrades the folds from "derived GIVEN `hfold`" to "derived up to the named residuals".

## The tower (bottom-up), all `#assert_axioms`-clean ⊆ {propext, Classical.choice, Quot.sound}

  * `WordIs a base v` — the composable "the 32 boolean columns at `base` LSB-first encode `v < 2^32`"
    relation the fold threads. `wordValue_of_WordIs` (bits→value, via a self-contained bit
    reconstruction) and `bit_of_boolWord` (value→bits, binary-representation uniqueness) are the two
    directions that let the value-gate (`addMod32`) and the bit-gates (Σ/σ/Ch/Maj) compose.
  * ATOMIC gadget forcings — each gadget's accepted gates force its output `WordIs` the reference
    function: `chWord_forces`/`majWord_forces` (Ch/Maj bit-bridges via `Nat.testBit`),
    `addMod32_word_forces` (the mod-2³² value gate → `Ref.w32` of the input sum), and
    `sigmaWord_forces` composed with the ROTR/SHR bit-bridge (`rotr_bit`/`shr_bit` — the genuinely
    geometric rung — and `{bS0,bS1,s0,s1}_bridge`).
  * `sha256Round_forces` — the FIXED finite composition of the eight gadgets: accepted round gates
    force the output state `WordIsSt` the reference `Ref.round`.
  * **`sha256Compress'_forces` — THE COMPOSITION WALL.** `sha256Compress'` is `List.foldl sha256Round`
    over 64 rounds (~30k gates); its accepted gates force the final state to the reference 64-round
    fold, by a `List.foldl` induction (`foldl_cstep_forces`) that composes `sha256Round_forces` per
    step. Gate-count-INDEPENDENT — the wall falls. `K_lt` discharges the round-constant bound.

The deployed reading is `acceptB` = the ℤ reading `body = 0` of the emitted gate bodies (the same
predicate `Sha256Gadget`'s KATs use); the mod-p ↔ ℤ gap is the SAME field-soundness residual
`LightClientEthAir` §6 carries — untouched here.

## Named residuals (NOT sorry-ed — the remaining rungs, each a real theorem)

  * `scheduleExpand_forces` — the 48-step message-schedule recurrence
    `W[t] = σ1(W[t-2]) + W[t-7] + σ0(W[t-15]) + W[t-16]`. Structurally the SAME `List.foldl` induction
    as `sha256Compress'_forces`, but the step reads PRIOR schedule words, so the invariant must carry
    `WordIs` for the whole growing schedule prefix. This is the message-schedule rung.
  * `feedForward_forces` (Davies–Meyer 8 adds) + `sha256Block_forces` (schedule ‖ compress ‖ feed) +
    `sha256PairHash_forces` (the two-block SSZ hash) — finite compositions above the two folds.
  * `merkleBranchFold_forces` / `chainCommit_forces` — the depth/collection fold that IS `hforce`
    (`rootDigest = foldReconstruct …`): the SAME `List.foldl` induction proved here for the 64 rounds,
    now over the branch/entry list using `sha256PairHash_forces` as the composable step. Discharging
    it + `bindRootWords` (→ `hbind`) feeds `LightClientEthFinFold.finFold_derives_finalityCommits`,
    turning its assumed `hfold` into a theorem.

NEW file; imports read-only (`Sha256MerkleFold`). Standalone — not wired into the truncated `Dregg2`
root; build with `lake env lean` (or add to a target) against the warm tree.
-/
import Dregg2.Circuit.Emit.Sha256MerkleFold

namespace Dregg2.Circuit.Emit.Sha256FoldForcing

open Dregg2.Circuit (Assignment)
open Dregg2.Circuit.DescriptorIR2 (VmConstraint2)
open Dregg2.Circuit.Emit.AirBuilder
open Dregg2.Circuit.Emit.Sha256Gadget
open Dregg2.Circuit.Emit.Sha256MerkleFold

set_option autoImplicit false

/-! ## §0 — Bit primitives: `Ref.bit` is the arithmetic bit; LSB-first reconstruction. -/

-- Ref.bit is the arithmetic bit
theorem toNat_testBit (x i : Nat) : (x.testBit i).toNat = x / 2 ^ i % 2 := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (x / 2 ^ i) with h | h <;> simp [h]

theorem bit_eq_testBit (x j : Nat) : Ref.bit x j = (x.testBit j).toNat := by
  unfold Ref.bit
  rw [toNat_testBit, Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]

-- reconstruction, Nat form
theorem bitSum_mod (v : Nat) : ∀ n : Nat,
    ((List.range n).map (fun i => (v.testBit i).toNat * 2 ^ i)).sum = v % 2 ^ n := by
  intro n
  induction n with
  | zero => simp [Nat.mod_one]
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    rw [toNat_testBit, pow_succ, Nat.mod_mul]
    ring

-- acceptB algebra
theorem acceptB_append (l1 l2 : List VmConstraint2) (a : Assignment) :
    acceptB (l1 ++ l2) a = (acceptB l1 a && acceptB l2 a) := by
  simp [acceptB, List.all_append]

theorem acceptB_cons (g : VmConstraint2) (rest : List VmConstraint2) (a : Assignment) :
    acceptB (g :: rest) a = (gateBodyEvalZero a g && acceptB rest a) := by
  simp [acceptB]

theorem gateBodyEvalZero_cgH (a : Assignment) (h : Head) :
    gateBodyEvalZero a (cgH h) = decide (evalH h a = 0) := by
  simp only [cgH, cg, gateBodyEvalZero, headToExpr_eval]

-- reconstruction in ℤ, by direct induction
theorem bitSum_recon_aux (v : Nat) : ∀ n : Nat,
    ((List.range n).map (fun i => (2 ^ i : ℤ) * ((v.testBit i).toNat : ℤ))).sum
      = ((v % 2 ^ n : Nat) : ℤ) := by
  intro n
  induction n with
  | zero => simp [Nat.mod_one]
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    rw [toNat_testBit]
    have hm : v % 2 ^ (n + 1) = v % 2 ^ n + 2 ^ n * (v / 2 ^ n % 2) := by
      rw [pow_succ, Nat.mod_mul]
    rw [hm]; push_cast; ring

theorem bitSum_recon_int (v : Nat) (hv : v < 2 ^ 32) :
    ((List.range 32).map (fun i => (2 ^ i : ℤ) * ((v.testBit i).toNat : ℤ))).sum = (v : ℤ) := by
  rw [bitSum_recon_aux v 32, Nat.mod_eq_of_lt hv]

/-! ## WordIs: the 32 bit columns at `base` are boolean and LSB-first encode `v < 2^32`. -/

/-- The 32 columns `base..base+31` are the LSB-first bits of the Nat word `v` (with `v < 2^32`).
This is the composable "the columns represent word `v`" relation the fold threads. -/
def WordIs (a : Assignment) (base v : Nat) : Prop :=
  v < 2 ^ 32 ∧ ∀ i, i < 32 → a (base + i) = (Ref.bit v i : ℤ)

theorem wordValue_eval (a : Assignment) (base : Nat) :
    evalH (wordValue base) a = ((List.range 32).map (fun i => (2 ^ i : ℤ) * a (base + i))).sum := by
  unfold wordValue
  rw [evalH_foldl_addLinG a Head.zero (fun i => (2 ^ i : ℤ)) (List.range 32) (fun i => base + i)]
  simp [evalH_zero]

/-- `WordIs` pins the value head to `v` (the ℤ reading; the mod-p ↔ ℤ gap is the shared residual). -/
theorem wordValue_of_WordIs (a : Assignment) (base v : Nat) (hw : WordIs a base v) :
    evalH (wordValue base) a = (v : ℤ) := by
  obtain ⟨hlt, hbits⟩ := hw
  rw [wordValue_eval]
  have hmap : (List.range 32).map (fun i => (2 ^ i : ℤ) * a (base + i))
            = (List.range 32).map (fun i => (2 ^ i : ℤ) * ((v.testBit i).toNat : ℤ)) := by
    apply List.map_congr_left
    intro i hi
    rw [List.mem_range] at hi
    rw [hbits i hi, bit_eq_testBit]
  rw [hmap, bitSum_recon_int v hlt]

/-! ## Reference bit-bridges: Ch and Maj decode per-bit to the gate arithmetic. -/

theorem chf_testBit (E F G i : Nat) (hi : i < 32) :
    (Ref.chf E F G).testBit i = (if E.testBit i then F.testBit i else G.testBit i) := by
  have hM : (4294967296 : Nat) = 2 ^ 32 := by norm_num
  have h4 : (4294967295 : Nat) = 2 ^ 32 - 1 := by norm_num
  unfold Ref.chf Ref.notw Ref.w32 Ref.M
  rw [Nat.testBit_xor, Nat.testBit_and, Nat.testBit_and, hM, Nat.testBit_mod_two_pow,
      Nat.testBit_xor, h4, Nat.testBit_two_pow_sub_one]
  simp only [hi, decide_true, Bool.true_and]
  cases E.testBit i <;> cases F.testBit i <;> cases G.testBit i <;> rfl

theorem chf_bit_arith (E F G i : Nat) (hi : i < 32) :
    (Ref.bit (Ref.chf E F G) i : ℤ)
      = (Ref.bit E i : ℤ) * (Ref.bit F i : ℤ) + (1 - (Ref.bit E i : ℤ)) * (Ref.bit G i : ℤ) := by
  rw [bit_eq_testBit, bit_eq_testBit, bit_eq_testBit, bit_eq_testBit, chf_testBit E F G i hi]
  cases E.testBit i <;> cases F.testBit i <;> cases G.testBit i <;> norm_num

theorem majf_bit_arith (E F G i : Nat) :
    (Ref.bit (Ref.majf E F G) i : ℤ)
      = (Ref.bit E i : ℤ) * (Ref.bit F i : ℤ) + (Ref.bit F i : ℤ) * (Ref.bit G i : ℤ)
        + (Ref.bit G i : ℤ) * (Ref.bit E i : ℤ)
        - 2 * ((Ref.bit E i : ℤ) * (Ref.bit F i : ℤ) * (Ref.bit G i : ℤ)) := by
  rw [bit_eq_testBit, bit_eq_testBit, bit_eq_testBit, bit_eq_testBit]
  unfold Ref.majf
  rw [Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_and, Nat.testBit_and, Nat.testBit_and]
  cases E.testBit i <;> cases F.testBit i <;> cases G.testBit i <;> norm_num

/-! ## `< 2^32` bounds for the reference bit functions. -/

theorem notw_lt (E : Nat) : Ref.notw E < 2 ^ 32 := by
  unfold Ref.notw Ref.w32 Ref.M
  exact Nat.mod_lt _ (by norm_num)

theorem chf_lt (E F G : Nat) (hE : E < 2 ^ 32) : Ref.chf E F G < 2 ^ 32 := by
  unfold Ref.chf
  exact Nat.xor_lt_two_pow (lt_of_le_of_lt (Nat.and_le_left) hE)
    (lt_of_le_of_lt (Nat.and_le_left) (notw_lt E))

theorem majf_lt (E F G : Nat) (hE : E < 2 ^ 32) (hF : F < 2 ^ 32) : Ref.majf E F G < 2 ^ 32 := by
  unfold Ref.majf
  exact Nat.xor_lt_two_pow
    (Nat.xor_lt_two_pow (lt_of_le_of_lt (Nat.and_le_left) hE) (lt_of_le_of_lt (Nat.and_le_left) hE))
    (lt_of_le_of_lt (Nat.and_le_left) hF)

/-! ## Acceptance extraction over the per-bit-position gate folds. -/

/-- From acceptance of a `cgH`-mapped list, each mapped head evaluates to zero. -/
theorem head_of_acceptB_map {α : Type} (l : List α) (g : α → Head) (a : Assignment)
    (h : acceptB (l.map (fun x => cgH (g x))) a = true) (x : α) (hx : x ∈ l) :
    evalH (g x) a = 0 := by
  rw [acceptB, List.all_eq_true] at h
  have hmem : cgH (g x) ∈ l.map (fun x => cgH (g x)) := List.mem_map.mpr ⟨x, hx, rfl⟩
  have hb := h _ hmem
  rw [gateBodyEvalZero_cgH] at hb
  exact of_decide_eq_true hb

/-! ## Gadget forcings: `chWord` / `majWord` accepted ⟹ output `WordIs` the reference function. -/

theorem chWord_forces (a : Assignment) (eBase fBase gBase outBase : Nat) {E F G : Nat}
    (hE : WordIs a eBase E) (hF : WordIs a fBase F) (hG : WordIs a gBase G)
    (hacc : acceptB (chWord eBase fBase gBase outBase) a = true) :
    WordIs a outBase (Ref.chf E F G) := by
  refine ⟨chf_lt E F G hE.1, ?_⟩
  intro i hi
  rw [chWord, acceptB_append, Bool.and_eq_true] at hacc
  have hg : evalH (chHead (eBase + i) (fBase + i) (gBase + i) (outBase + i)) a = 0 :=
    head_of_acceptB_map (List.range 32)
      (fun i => chHead (eBase + i) (fBase + i) (gBase + i) (outBase + i)) a hacc.1 i
      (List.mem_range.mpr hi)
  rw [chHead_forces a (eBase + i) (fBase + i) (gBase + i) (outBase + i) hg,
      hE.2 i hi, hF.2 i hi, hG.2 i hi]
  exact (chf_bit_arith E F G i hi).symm

theorem majWord_forces (a : Assignment) (aBase bBase cBase outBase : Nat) {A B C : Nat}
    (hA : WordIs a aBase A) (hB : WordIs a bBase B) (hC : WordIs a cBase C)
    (hacc : acceptB (majWord aBase bBase cBase outBase) a = true) :
    WordIs a outBase (Ref.majf A B C) := by
  refine ⟨majf_lt A B C hA.1 hB.1, ?_⟩
  intro i hi
  rw [majWord, acceptB_append, Bool.and_eq_true] at hacc
  have hg : evalH (majHead (aBase + i) (bBase + i) (cBase + i) (outBase + i)) a = 0 :=
    head_of_acceptB_map (List.range 32)
      (fun i => majHead (aBase + i) (bBase + i) (cBase + i) (outBase + i)) a hacc.1 i
      (List.mem_range.mpr hi)
  rw [majHead_forces a (aBase + i) (bBase + i) (cBase + i) (outBase + i) hg,
      hA.2 i hi, hB.2 i hi, hC.2 i hi]
  exact (majf_bit_arith A B C i).symm

/-! ## Binary-representation uniqueness: a boolean word whose VALUE is `V` has bits `Ref.bit V`.
This lifts the value-level adder gate to a per-bit `WordIs` (its outputs feed the next round's
bit gadgets). -/

theorem list_finset_sum {M : Type} [AddCommMonoid M] (g : Nat → M) (n : Nat) :
    ((List.range n).map g).sum = ∑ i ∈ Finset.range n, g i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
    simp

theorem boolSum_testBit : ∀ (n : Nat) (f : Nat → Nat), (∀ i, f i < 2) → ∀ k, k < n →
    ((∑ i ∈ Finset.range n, f i * 2 ^ i).testBit k).toNat = f k := by
  intro n
  induction n with
  | zero => intro f _ k hk; omega
  | succ n ih =>
    intro f hf k hk
    have hsum : (∑ i ∈ Finset.range (n + 1), f i * 2 ^ i)
              = 2 * (∑ i ∈ Finset.range n, f (i + 1) * 2 ^ i) + f 0 := by
      rw [Finset.sum_range_succ', Finset.mul_sum]
      simp only [pow_zero, mul_one]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      rw [pow_succ]; ring
    rw [hsum]
    have hf0 : f 0 < 2 := hf 0
    cases k with
    | zero =>
      rw [toNat_testBit]; simp only [pow_zero, Nat.div_one]; omega
    | succ k =>
      rw [toNat_testBit]
      have hdiv : (2 * (∑ i ∈ Finset.range n, f (i + 1) * 2 ^ i) + f 0) / 2 ^ (k + 1)
                = (∑ i ∈ Finset.range n, f (i + 1) * 2 ^ i) / 2 ^ k := by
        rw [pow_succ, mul_comm (2 ^ k) 2, ← Nat.div_div_eq_div_mul]
        congr 1; omega
      rw [hdiv]
      have hih := ih (fun i => f (i + 1)) (fun i => hf (i + 1)) k (by omega)
      rw [toNat_testBit] at hih
      exact hih

theorem bit_of_boolWord (a : Assignment) (base V : Nat) (hV : V < 2 ^ 32)
    (hbool : ∀ i, i < 32 → a (base + i) = 0 ∨ a (base + i) = 1)
    (hval : evalH (wordValue base) a = (V : ℤ)) :
    WordIs a base V := by
  refine ⟨hV, ?_⟩
  set f : Nat → Nat := fun i => if a (base + i) = 1 then 1 else 0 with hfdef
  have hflt : ∀ i, f i < 2 := by intro i; simp only [hfdef]; split <;> omega
  have hafi : ∀ i, i < 32 → a (base + i) = (f i : ℤ) := by
    intro i hi; rcases hbool i hi with h | h <;> simp [hfdef, h]
  have hcast : (V : ℤ) = ((∑ i ∈ Finset.range 32, f i * 2 ^ i : Nat) : ℤ) := by
    rw [← hval, wordValue_eval, list_finset_sum]
    push_cast
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    rw [hafi i hi]; ring
  have hVeq : (∑ i ∈ Finset.range 32, f i * 2 ^ i) = V := by exact_mod_cast hcast.symm
  intro k hk
  rw [hafi k hk, bit_eq_testBit]
  have hbit : f k = (V.testBit k).toNat := by
    have hb := boolSum_testBit 32 f hflt k hk
    rw [hVeq] at hb; exact hb.symm
  rw [hbit]

/-! ## The mod-2³² adder gate lifted to a per-bit `WordIs` of the reference `Ref.w32` of the sum. -/

theorem carTerm_factor (l : List (Nat × Nat)) (a : Assignment) :
    (l.map (fun p => -(2 ^ 32 * 2 ^ p.2 : ℤ) * a p.1)).sum
      = 2 ^ 32 * (-(l.map (fun p => (2 ^ p.2 : ℤ) * a p.1)).sum) := by
  induction l with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons, List.sum_cons, ih]; ring

theorem boolSum_lt (f : Nat → Nat) (hf : ∀ i, f i < 2) :
    ∀ n, ∑ i ∈ Finset.range n, f i * 2 ^ i < 2 ^ n := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, pow_succ]
    have h1 : f n * 2 ^ n ≤ 2 ^ n := by
      have : f n ≤ 1 := by have := hf n; omega
      calc f n * 2 ^ n ≤ 1 * 2 ^ n := Nat.mul_le_mul_right _ this
        _ = 2 ^ n := by ring
    omega

theorem boolWord_lt (a : Assignment) (base : Nat)
    (hb : ∀ i, i < 32 → a (base + i) = 0 ∨ a (base + i) = 1) :
    ∃ N : Nat, N < 2 ^ 32 ∧ evalH (wordValue base) a = (N : ℤ) := by
  set f : Nat → Nat := fun i => if a (base + i) = 1 then 1 else 0 with hfdef
  have hflt : ∀ i, f i < 2 := by intro i; simp only [hfdef]; split <;> omega
  have hafi : ∀ i, i < 32 → a (base + i) = (f i : ℤ) := by
    intro i hi; rcases hb i hi with h | h <;> simp [hfdef, h]
  refine ⟨∑ i ∈ Finset.range 32, f i * 2 ^ i, boolSum_lt f hflt 32, ?_⟩
  rw [wordValue_eval, list_finset_sum]
  push_cast
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  rw [hafi i hi]; ring

/-- **The mod-2³² adder gate FORCES its output to `WordIs` the reference `Ref.w32` of the input sum.**
Given the adder's gates accepted and the input heads summing to `(S : ℤ)` (each a `WordIs` value),
the 32 output columns are the LSB-first bits of `Ref.w32 S`. -/
theorem addMod32_word_forces (a : Assignment) (ins : List Head) (outBase : Nat) (carBits : List Nat)
    (S : Nat)
    (hacc : acceptB (addMod32 ins outBase carBits) a = true)
    (hS : (ins.map (fun h => evalH h a)).sum = (S : ℤ)) :
    WordIs a outBase (Ref.w32 S) := by
  rw [addMod32, acceptB_append, acceptB_cons] at hacc
  simp only [Bool.and_eq_true] at hacc
  obtain ⟨⟨hgate, hout⟩, _hcar⟩ := hacc
  rw [gateBodyEvalZero_cgH] at hgate
  have hgate0 : evalH (addMod32Head ins outBase carBits) a = 0 := of_decide_eq_true hgate
  have hbits : ∀ i, i < 32 → a (outBase + i) = 0 ∨ a (outBase + i) = 1 := by
    intro i hi
    rw [acceptB, List.all_eq_true] at hout
    have hmem : binGate (outBase + i) ∈ (wordBits outBase).map binGate :=
      List.mem_map.mpr ⟨outBase + i, by
        rw [wordBits]; exact List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩, rfl⟩
    have hb := hout _ hmem
    simp only [binGate, cg, gateBodyEvalZero] at hb
    exact (gBin_eval_zero_iff a (outBase + i)).mp (of_decide_eq_true hb)
  have hval := addMod32_forces a ins outBase carBits hgate0
  rw [hS] at hval
  obtain ⟨cs, hcs⟩ : ∃ cs : ℤ,
      (carBits.zipIdx.map (fun p => -(2 ^ 32 * 2 ^ p.2 : ℤ) * a p.1)).sum = 2 ^ 32 * cs :=
    ⟨_, carTerm_factor carBits.zipIdx a⟩
  rw [hcs] at hval
  obtain ⟨N, hNlt, hNval⟩ := boolWord_lt a outBase hbits
  rw [hNval] at hval
  have hp : (2 : ℤ) ^ 32 = 4294967296 := by norm_num
  have hpn : (2 : ℕ) ^ 32 = 4294967296 := by norm_num
  rw [hp] at hval
  have hNlt' : N < 4294967296 := by rw [hpn] at hNlt; exact hNlt
  have hNeq : N = S % 4294967296 := by omega
  have hw32 : Ref.w32 S = N := by unfold Ref.w32 Ref.M; rw [hNeq]
  rw [hw32]
  exact bit_of_boolWord a outBase N hNlt hbits hNval

/-! ## The Σ/σ gadget: the circuit side (compose the per-bit XOR gates), parametrized over the
reference rotr/shr bit-bridge. -/

/-- Booleanity of a word's columns from acceptance of its `binGate` pins. -/
theorem boolWord_of_acceptB (a : Assignment) (base : Nat)
    (h : acceptB ((wordBits base).map binGate) a = true) :
    ∀ i, i < 32 → a (base + i) = 0 ∨ a (base + i) = 1 := by
  intro i hi
  rw [acceptB, List.all_eq_true] at h
  have hmem : binGate (base + i) ∈ (wordBits base).map binGate :=
    List.mem_map.mpr ⟨base + i, by
      rw [wordBits]; exact List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩, rfl⟩
  have hb := h _ hmem
  simp only [binGate, cg, gateBodyEvalZero] at hb
  exact (gBin_eval_zero_iff a (base + i)).mp (of_decide_eq_true hb)

/-- The XOR gate over a source LIST forces `out = (Σ sources) − 2·carry`. -/
theorem xorList_forces (a : Assignment) (ins : List Nat) (out car : Nat)
    (hg : evalH (xorHead ins out car) a = 0) :
    a out = (ins.map a).sum - 2 * a car := by
  rw [xorHead_eval] at hg; linarith

theorem cast_map_bit_sum (l : List Nat) (X : Nat) :
    (l.map (fun s => (Ref.bit X s : ℤ))).sum = ((l.map (Ref.bit X)).sum : ℤ) := by
  induction l with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons, List.sum_cons, ih]; push_cast; ring

theorem sigmaSources_lt (r1 r2 third i : Nat) (isShift : Bool) (s : Nat)
    (hs : s ∈ sigmaSources r1 r2 third isShift i) : s < 32 := by
  have h32 : (0 : Nat) < 32 := by norm_num
  unfold sigmaSources at hs
  by_cases hsh : isShift
  · rw [if_pos hsh] at hs
    by_cases hg : i + third < 32
    · rw [if_pos hg] at hs
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with h | h | h <;> (subst h; first | exact Nat.mod_lt _ h32 | omega)
    · rw [if_neg hg] at hs
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with h | h <;> (subst h; exact Nat.mod_lt _ h32)
  · rw [if_neg hsh] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with h | h | h <;> (subst h; first | exact Nat.mod_lt _ h32 | omega)

/-- **The Σ/σ gadget FORCES its output `WordIs` the value `V`**, GIVEN the reference bit-bridge
`hbridge` (bit `i` of `V` is the XOR = parity of the gadget's source bits of `X`). The circuit
composition — the per-bit XOR gates + booleanity — is discharged here; `hbridge` is the rotr/shr
reference-decode, proved for each concrete Σ/σ below. -/
theorem sigmaWord_forces (a : Assignment) (inBase outBase carBase r1 r2 third X V : Nat)
    (isShift : Bool) (hX : WordIs a inBase X)
    (hacc : acceptB (sigmaWord inBase outBase carBase r1 r2 third isShift) a = true)
    (hVlt : V < 2 ^ 32)
    (hbridge : ∀ i, i < 32 →
      Ref.bit V i = ((sigmaSources r1 r2 third isShift i).map (Ref.bit X)).sum % 2) :
    WordIs a outBase V := by
  refine ⟨hVlt, ?_⟩
  intro i hi
  rw [sigmaWord, acceptB_append, acceptB_append] at hacc
  simp only [Bool.and_eq_true] at hacc
  obtain ⟨⟨hgates, houtbin⟩, _⟩ := hacc
  have hbool := boolWord_of_acceptB a outBase houtbin i hi
  have hg : evalH (xorHead ((sigmaSources r1 r2 third isShift i).map (inBase + ·))
      (outBase + i) (carBase + i)) a = 0 :=
    head_of_acceptB_map (List.range 32)
      (fun i => xorHead ((sigmaSources r1 r2 third isShift i).map (inBase + ·))
        (outBase + i) (carBase + i)) a hgates i (List.mem_range.mpr hi)
  have hforce := xorList_forces a ((sigmaSources r1 r2 third isShift i).map (inBase + ·))
    (outBase + i) (carBase + i) hg
  -- rewrite the source sum to (nsum : ℤ)
  have hmap : (((sigmaSources r1 r2 third isShift i).map (inBase + ·)).map a)
            = (sigmaSources r1 r2 third isShift i).map (fun s => (Ref.bit X s : ℤ)) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro s hs
    exact hX.2 s (sigmaSources_lt r1 r2 third i isShift s hs)
  rw [hmap, cast_map_bit_sum] at hforce
  set nsum : Nat := ((sigmaSources r1 r2 third isShift i).map (Ref.bit X)).sum with hnsum
  rw [hbridge i hi]
  -- hforce : a (outBase+i) = (nsum : ℤ) - 2 * a (carBase+i) ; hbool ; goal a(out+i) = (nsum%2 : ℤ)
  rcases hbool with h | h <;> rw [h] at hforce ⊢ <;> omega

/-! ## The rotr/shr reference bit-bridge (the genuinely geometric rung). -/

/-- Bits at index ≥ 32 of a 32-bit word are zero. -/
theorem bit_high_zero (X j : Nat) (hX : X < 2 ^ 32) (hj : 32 ≤ j) : Ref.bit X j = 0 := by
  rw [bit_eq_testBit, Nat.testBit_lt_two_pow (lt_of_lt_of_le hX (Nat.pow_le_pow_right (by norm_num) hj))]
  rfl

/-- `SHR n` is a plain bit re-index (bits shifted off the bottom drop). -/
theorem shr_bit (n X i : Nat) : Ref.bit (Ref.shr n X) i = Ref.bit X (i + n) := by
  rw [bit_eq_testBit, bit_eq_testBit]
  unfold Ref.shr
  rw [Nat.testBit_shiftRight, Nat.add_comm i n]

/-- **`ROTR n` is a cyclic bit re-index**: output bit `i` reads input bit `(i+n) mod 32`. -/
theorem rotr_bit (n X i : Nat) (hn : 0 < n) (hn32 : n < 32) (hi : i < 32) (hX : X < 2 ^ 32) :
    Ref.bit (Ref.rotr n X) i = Ref.bit X ((i + n) % 32) := by
  rw [bit_eq_testBit, bit_eq_testBit]
  unfold Ref.rotr Ref.w32 Ref.M
  have hM : (4294967296 : Nat) = 2 ^ 32 := by norm_num
  rw [hM, Nat.testBit_mod_two_pow]
  simp only [hi, decide_true, Bool.true_and]
  rw [Nat.testBit_or, Nat.testBit_shiftRight, Nat.testBit_shiftLeft]
  by_cases hlow : i + n < 32
  · have h1 : (i + n) % 32 = i + n := Nat.mod_eq_of_lt hlow
    have h2 : ¬ (i ≥ 32 - n) := by omega
    rw [h1]
    simp only [h2, decide_false, Bool.false_and, Bool.or_false]
    rw [Nat.add_comm n i]
  · have hlt64 : i + n < 64 := by omega
    have h1 : (i + n) % 32 = i + n - 32 := by omega
    have hge : i ≥ 32 - n := by omega
    have hlowfalse : X.testBit (n + i) = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hX (Nat.pow_le_pow_right (by norm_num) (by omega)))
    rw [h1, hlowfalse]
    simp only [hge, decide_true, Bool.true_and, Bool.false_or]
    have hidx : i - (32 - n) = i + n - 32 := by omega
    rw [hidx]

/-- XOR of two words is per-bit parity. -/
theorem xor_bit (A B i : Nat) : Ref.bit (A ^^^ B) i = (Ref.bit A i + Ref.bit B i) % 2 := by
  rw [bit_eq_testBit, bit_eq_testBit, bit_eq_testBit, Nat.testBit_xor]
  cases A.testBit i <;> cases B.testBit i <;> decide

/-! ### Bounds: every Σ/σ output is a 32-bit word. -/

theorem rotr_lt (n X : Nat) : Ref.rotr n X < 2 ^ 32 := by
  unfold Ref.rotr Ref.w32 Ref.M
  rw [show (4294967296 : Nat) = 2 ^ 32 from by norm_num]
  exact Nat.mod_lt _ (by norm_num)

theorem shr_lt (n X : Nat) (hX : X < 2 ^ 32) : Ref.shr n X < 2 ^ 32 := by
  unfold Ref.shr
  rw [Nat.shiftRight_eq_div_pow]
  exact lt_of_le_of_lt (Nat.div_le_self X (2 ^ n)) hX

theorem bS0_lt (X : Nat) : Ref.bS0 X < 2 ^ 32 := by
  unfold Ref.bS0
  exact Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (rotr_lt _ _) (rotr_lt _ _)) (rotr_lt _ _)

theorem bS1_lt (X : Nat) : Ref.bS1 X < 2 ^ 32 := by
  unfold Ref.bS1
  exact Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (rotr_lt _ _) (rotr_lt _ _)) (rotr_lt _ _)

theorem s0_lt (X : Nat) (hX : X < 2 ^ 32) : Ref.s0 X < 2 ^ 32 := by
  unfold Ref.s0
  exact Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (rotr_lt _ _) (rotr_lt _ _)) (shr_lt _ _ hX)

theorem s1_lt (X : Nat) (hX : X < 2 ^ 32) : Ref.s1 X < 2 ^ 32 := by
  unfold Ref.s1
  exact Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (rotr_lt _ _) (rotr_lt _ _)) (shr_lt _ _ hX)

/-! ### The four concrete Σ/σ bridges (bit `i` of the function = parity of the source bits). -/

theorem bS0_bridge (X i : Nat) (hi : i < 32) (hX : X < 2 ^ 32) :
    Ref.bit (Ref.bS0 X) i = ((sigmaSources 2 13 22 false i).map (Ref.bit X)).sum % 2 := by
  unfold Ref.bS0
  rw [xor_bit, xor_bit, rotr_bit 2 X i (by norm_num) (by norm_num) hi hX,
      rotr_bit 13 X i (by norm_num) (by norm_num) hi hX,
      rotr_bit 22 X i (by norm_num) (by norm_num) hi hX,
      show sigmaSources 2 13 22 false i
         = [(i + 2) % 32, (i + 13) % 32, (i + 22) % 32] from rfl]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  omega

theorem bS1_bridge (X i : Nat) (hi : i < 32) (hX : X < 2 ^ 32) :
    Ref.bit (Ref.bS1 X) i = ((sigmaSources 6 11 25 false i).map (Ref.bit X)).sum % 2 := by
  unfold Ref.bS1
  rw [xor_bit, xor_bit, rotr_bit 6 X i (by norm_num) (by norm_num) hi hX,
      rotr_bit 11 X i (by norm_num) (by norm_num) hi hX,
      rotr_bit 25 X i (by norm_num) (by norm_num) hi hX,
      show sigmaSources 6 11 25 false i
         = [(i + 6) % 32, (i + 11) % 32, (i + 25) % 32] from rfl]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  omega

theorem s0_bridge (X i : Nat) (hi : i < 32) (hX : X < 2 ^ 32) :
    Ref.bit (Ref.s0 X) i = ((sigmaSources 7 18 3 true i).map (Ref.bit X)).sum % 2 := by
  unfold Ref.s0
  rw [xor_bit, xor_bit, rotr_bit 7 X i (by norm_num) (by norm_num) hi hX,
      rotr_bit 18 X i (by norm_num) (by norm_num) hi hX, shr_bit 3 X i,
      show sigmaSources 7 18 3 true i
         = (if i + 3 < 32 then [(i + 7) % 32, (i + 18) % 32, i + 3]
            else [(i + 7) % 32, (i + 18) % 32]) from rfl]
  by_cases hg : i + 3 < 32
  · rw [if_pos hg]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    omega
  · rw [if_neg hg, bit_high_zero X (i + 3) hX (by omega)]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    omega

theorem s1_bridge (X i : Nat) (hi : i < 32) (hX : X < 2 ^ 32) :
    Ref.bit (Ref.s1 X) i = ((sigmaSources 17 19 10 true i).map (Ref.bit X)).sum % 2 := by
  unfold Ref.s1
  rw [xor_bit, xor_bit, rotr_bit 17 X i (by norm_num) (by norm_num) hi hX,
      rotr_bit 19 X i (by norm_num) (by norm_num) hi hX, shr_bit 10 X i,
      show sigmaSources 17 19 10 true i
         = (if i + 10 < 32 then [(i + 17) % 32, (i + 19) % 32, i + 10]
            else [(i + 17) % 32, (i + 19) % 32]) from rfl]
  by_cases hg : i + 10 < 32
  · rw [if_pos hg]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    omega
  · rw [if_neg hg, bit_high_zero X (i + 10) hX (by omega)]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    omega

/-! ## Σ/σ concrete wrappers: the gadget forces its output `WordIs` the specific function. -/

theorem bS1_word_forces (a : Assignment) (inBase outBase carBase : Nat) {X : Nat} (hX : WordIs a inBase X)
    (hacc : acceptB (sigmaWord inBase outBase carBase 6 11 25 false) a = true) :
    WordIs a outBase (Ref.bS1 X) :=
  sigmaWord_forces a inBase outBase carBase 6 11 25 X (Ref.bS1 X) false hX hacc (bS1_lt X)
    (fun i hi => bS1_bridge X i hi hX.1)

theorem bS0_word_forces (a : Assignment) (inBase outBase carBase : Nat) {X : Nat} (hX : WordIs a inBase X)
    (hacc : acceptB (sigmaWord inBase outBase carBase 2 13 22 false) a = true) :
    WordIs a outBase (Ref.bS0 X) :=
  sigmaWord_forces a inBase outBase carBase 2 13 22 X (Ref.bS0 X) false hX hacc (bS0_lt X)
    (fun i hi => bS0_bridge X i hi hX.1)

theorem s0_word_forces (a : Assignment) (inBase outBase carBase : Nat) {X : Nat} (hX : WordIs a inBase X)
    (hacc : acceptB (sigmaWord inBase outBase carBase 7 18 3 true) a = true) :
    WordIs a outBase (Ref.s0 X) :=
  sigmaWord_forces a inBase outBase carBase 7 18 3 X (Ref.s0 X) true hX hacc (s0_lt X hX.1)
    (fun i hi => s0_bridge X i hi hX.1)

theorem s1_word_forces (a : Assignment) (inBase outBase carBase : Nat) {X : Nat} (hX : WordIs a inBase X)
    (hacc : acceptB (sigmaWord inBase outBase carBase 17 19 10 true) a = true) :
    WordIs a outBase (Ref.s1 X) :=
  sigmaWord_forces a inBase outBase carBase 17 19 10 X (Ref.s1 X) true hX hacc (s1_lt X hX.1)
    (fun i hi => s1_bridge X i hi hX.1)

/-! ## The mod-2³² collapse lemmas (nested `add2` = one `w32` of the flat sum). -/

theorem add2_w32 (a b : Nat) : Ref.add2 (Ref.w32 a) (Ref.w32 b) = Ref.w32 (a + b) := by
  unfold Ref.add2 Ref.w32 Ref.M; omega

theorem t1_collapse (h e c k w : Nat) :
    Ref.add2 (Ref.add2 (Ref.add2 (Ref.add2 h e) c) k) w = Ref.w32 (h + e + c + k + w) := by
  unfold Ref.add2 Ref.w32 Ref.M; omega

/-! ## The state relation and the round forcing (the finite composition of the 8 gadgets). -/

/-- The 8 state columns of `s` LSB-first encode the reference working state `hs`. -/
def WordIsSt (a : Assignment) (s : St) (hs : Ref.Hst) : Prop :=
  WordIs a s.a hs.a ∧ WordIs a s.b hs.b ∧ WordIs a s.c hs.c ∧ WordIs a s.d hs.d ∧
  WordIs a s.e hs.e ∧ WordIs a s.f hs.f ∧ WordIs a s.g hs.g ∧ WordIs a s.h hs.h

/-- **`sha256Round_forces`** — the emitted round gates FORCE the output state to `WordIsSt` the
reference `Ref.round` of the input state, message word, and constant. A FIXED finite composition of
the four gadget forcings; no gate evaluation. -/
theorem sha256Round_forces (a : Assignment) (s : St) (wBase K fresh : Nat) (hs : Ref.Hst) (W : Nat)
    (hst : WordIsSt a s hs) (hW : WordIs a wBase W) (hK : K < 2 ^ 32)
    (hacc : acceptB (sha256Round s wBase (K : ℤ) fresh).1 a = true) :
    WordIsSt a (sha256Round s wBase (K : ℤ) fresh).2.1 (Ref.round hs K W) := by
  obtain ⟨hsa, hsb, hsc, hsd, hse, hsf, hsg, hsh⟩ := hst
  simp only [sha256Round, acceptB_append, Bool.and_eq_true] at hacc
  obtain ⟨⟨⟨⟨⟨⟨⟨hSig1, hCh⟩, hT1⟩, hSig0⟩, hMaj⟩, hT2⟩, hNe⟩, hNa⟩ := hacc
  -- Σ1(e), Ch(e,f,g)
  have hWs1 := bS1_word_forces a s.e fresh (fresh + 32) hse hSig1
  have hWch := chWord_forces a s.e s.f s.g (fresh + 32 + 32) hse hsf hsg hCh
  -- T1
  have hST1 : ([wordValue s.h, wordValue fresh, wordValue (fresh + 32 + 32), Head.c (K : ℤ),
      wordValue wBase].map (fun h => evalH h a)).sum
      = ((hs.h + Ref.bS1 hs.e + Ref.chf hs.e hs.f hs.g + K + W : Nat) : ℤ) := by
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    rw [wordValue_of_WordIs a s.h hs.h hsh, wordValue_of_WordIs a fresh _ hWs1,
        wordValue_of_WordIs a (fresh + 32 + 32) _ hWch, wordValue_of_WordIs a wBase W hW, evalH_c]
    push_cast; ring
  have hWt1 := addMod32_word_forces a _ (fresh + 32 + 32 + 32) _ _ hT1 hST1
  -- Σ0(a), Maj(a,b,c)
  have hWs0 := bS0_word_forces a s.a (fresh + 32 + 32 + 32 + 32 + 3) (fresh + 32 + 32 + 32 + 32 + 3 + 32)
    hsa hSig0
  have hWmj := majWord_forces a s.a s.b s.c (fresh + 32 + 32 + 32 + 32 + 3 + 32 + 32) hsa hsb hsc hMaj
  -- T2
  have hST2 : ([wordValue (fresh + 32 + 32 + 32 + 32 + 3),
      wordValue (fresh + 32 + 32 + 32 + 32 + 3 + 32 + 32)].map (fun h => evalH h a)).sum
      = ((Ref.bS0 hs.a + Ref.majf hs.a hs.b hs.c : Nat) : ℤ) := by
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    rw [wordValue_of_WordIs _ _ _ hWs0, wordValue_of_WordIs _ _ _ hWmj]
    push_cast; ring
  have hWt2 := addMod32_word_forces a _ (fresh + 32 + 32 + 32 + 32 + 3 + 32 + 32 + 32) _ _ hT2 hST2
  -- new e
  have hSne : ([wordValue s.d, wordValue (fresh + 32 + 32 + 32)].map (fun h => evalH h a)).sum
      = ((hs.d + Ref.w32 (hs.h + Ref.bS1 hs.e + Ref.chf hs.e hs.f hs.g + K + W) : Nat) : ℤ) := by
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    rw [wordValue_of_WordIs a s.d hs.d hsd, wordValue_of_WordIs _ _ _ hWt1]
    push_cast; ring
  have hWne := addMod32_word_forces a _ (fresh + 32 + 32 + 32 + 32 + 3 + 32 + 32 + 32 + 32 + 3) _ _
    hNe hSne
  -- new a
  have hSna : ([wordValue (fresh + 32 + 32 + 32),
      wordValue (fresh + 32 + 32 + 32 + 32 + 3 + 32 + 32 + 32)].map (fun h => evalH h a)).sum
      = ((Ref.w32 (hs.h + Ref.bS1 hs.e + Ref.chf hs.e hs.f hs.g + K + W)
          + Ref.w32 (Ref.bS0 hs.a + Ref.majf hs.a hs.b hs.c) : Nat) : ℤ) := by
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    rw [wordValue_of_WordIs _ _ _ hWt1, wordValue_of_WordIs _ _ _ hWt2]
    push_cast; ring
  have hWna := addMod32_word_forces a _ _ _ _ hNa hSna
  -- assemble: collapse `Ref.round`'s nested `add2` into the flat `w32` values the adders forced
  have hround : Ref.round hs K W =
      { a := Ref.w32 (Ref.w32 (hs.h + Ref.bS1 hs.e + Ref.chf hs.e hs.f hs.g + K + W)
                      + Ref.w32 (Ref.bS0 hs.a + Ref.majf hs.a hs.b hs.c)),
        b := hs.a, c := hs.b, d := hs.c,
        e := Ref.w32 (hs.d + Ref.w32 (hs.h + Ref.bS1 hs.e + Ref.chf hs.e hs.f hs.g + K + W)),
        f := hs.e, g := hs.f, h := hs.g } := by
    dsimp only [Ref.round]
    rw [Ref.Hst.mk.injEq]
    refine ⟨?_, rfl, rfl, rfl, ?_, rfl, rfl, rfl⟩ <;> (unfold Ref.add2 Ref.w32 Ref.M; omega)
  rw [hround]
  dsimp only [WordIsSt, sha256Round]
  exact ⟨hWna, hsa, hsb, hsc, hWne, hse, hsf, hsg⟩

/-! ## THE COMPOSITION WALL: the 64-round compression fold, by induction over the round list.

`sha256Compress'` is `List.foldl` of `sha256Round`. This is exactly the ~30k-gate object no kernel
`#guard` can reduce; here it falls to a `List.foldl` induction that composes `sha256Round_forces` per
step, gate-count-independent. -/

/-- The compression step: exactly `sha256Compress'`'s fold body (round `t` over the accumulator). -/
def cstep (wBases : List Nat) : List VmConstraint2 × St × Nat → Nat → List VmConstraint2 × St × Nat :=
  fun acc t =>
    let (cs, st, fr) := acc
    let (cs', st', fr') := sha256Round st (wBases.getD t 0) ((Ref.K.getD t 0 : Nat) : ℤ) fr
    (cs ++ cs', st', fr')

theorem sha256Compress'_eq (wBases : List Nat) (s0 : St) (fresh : Nat) :
    sha256Compress' wBases s0 fresh = (List.range 64).foldl (cstep wBases) ([], s0, fresh) := rfl

/-- The accumulated constraints always keep the starting list as a prefix (state/columns are
independent of the constraint accumulator). -/
theorem cstep_prefix (wBases : List Nat) : ∀ (ts : List Nat) (X : List VmConstraint2) (st : St)
    (fr : Nat), ∃ Y, (ts.foldl (cstep wBases) (X, st, fr)).1 = X ++ Y := by
  intro ts
  induction ts with
  | nil => intro X st fr; exact ⟨[], by simp⟩
  | cons t rest ih =>
    intro X st fr
    rw [List.foldl_cons]
    obtain ⟨Y, hY⟩ := ih (cstep wBases (X, st, fr) t).1 (cstep wBases (X, st, fr) t).2.1
      (cstep wBases (X, st, fr) t).2.2
    refine ⟨(sha256Round st (wBases.getD t 0) ((Ref.K.getD t 0 : Nat) : ℤ) fr).1 ++ Y, ?_⟩
    rw [show (cstep wBases (X, st, fr) t) = ((cstep wBases (X, st, fr) t).1,
        (cstep wBases (X, st, fr) t).2.1, (cstep wBases (X, st, fr) t).2.2) from rfl] at hY ⊢
    rw [hY]
    dsimp only [cstep]
    rw [List.append_assoc]

theorem acceptB_prefix (l m : List VmConstraint2) (a : Assignment)
    (h : acceptB (l ++ m) a = true) : acceptB l a = true := by
  rw [acceptB_append, Bool.and_eq_true] at h; exact h.1

/-- **The 64-round fold forces the compression** — by induction over the round list. -/
theorem foldl_cstep_forces (a : Assignment) (wBases w : List Nat) :
    ∀ (ts : List Nat) (cs0 : List VmConstraint2) (st0 : St) (fr0 : Nat) (hs0 : Ref.Hst),
      WordIsSt a st0 hs0 →
      (∀ t ∈ ts, WordIs a (wBases.getD t 0) (w.getD t 0)) →
      (∀ t ∈ ts, Ref.K.getD t 0 < 2 ^ 32) →
      acceptB ((ts.foldl (cstep wBases) (cs0, st0, fr0)).1) a = true →
      WordIsSt a (ts.foldl (cstep wBases) (cs0, st0, fr0)).2.1
        (ts.foldl (fun hs t => Ref.round hs (Ref.K.getD t 0) (w.getD t 0)) hs0) := by
  intro ts
  induction ts with
  | nil => intro cs0 st0 fr0 hs0 hst0 _ _ _; exact hst0
  | cons t rest ih =>
    intro cs0 st0 fr0 hs0 hst0 hW hK hacc
    rw [List.foldl_cons] at hacc ⊢
    rw [List.foldl_cons]
    -- the round-`t` constraints and their acceptance
    set cs' := (sha256Round st0 (wBases.getD t 0) ((Ref.K.getD t 0 : Nat) : ℤ) fr0).1 with hcs'
    have hstep : cstep wBases (cs0, st0, fr0) t
        = (cs0 ++ cs', (sha256Round st0 (wBases.getD t 0) ((Ref.K.getD t 0 : Nat) : ℤ) fr0).2.1,
           (sha256Round st0 (wBases.getD t 0) ((Ref.K.getD t 0 : Nat) : ℤ) fr0).2.2) := rfl
    rw [hstep] at hacc ⊢
    -- extract acceptance of round t
    obtain ⟨Y, hY⟩ := cstep_prefix wBases rest (cs0 ++ cs') _ _
    have haccStep : acceptB cs' a = true := by
      have h1 : acceptB (cs0 ++ cs') a = true := acceptB_prefix (cs0 ++ cs') Y a (by rw [hY] at hacc; exact hacc)
      rw [acceptB_append, Bool.and_eq_true] at h1
      exact h1.2
    -- round t forces the next state
    have hstepForce : WordIsSt a
        (sha256Round st0 (wBases.getD t 0) ((Ref.K.getD t 0 : Nat) : ℤ) fr0).2.1
        (Ref.round hs0 (Ref.K.getD t 0) (w.getD t 0)) :=
      sha256Round_forces a st0 (wBases.getD t 0) (Ref.K.getD t 0) fr0 hs0 (w.getD t 0)
        hst0 (hW t List.mem_cons_self) (hK t List.mem_cons_self) haccStep
    exact ih (cs0 ++ cs') _ _ _ hstepForce
      (fun t' ht' => hW t' (List.mem_cons_of_mem t ht'))
      (fun t' ht' => hK t' (List.mem_cons_of_mem t ht')) hacc

/-- **`sha256Compress'_forces`** — the whole 64-round compression's emitted gates FORCE the final
working state to `WordIsSt` the reference `Ref.round`-fold, given the 16+48 message words are
`WordIs` their reference values. The composition wall for the compression core, DISCHARGED. -/
theorem sha256Compress'_forces (a : Assignment) (wBases w : List Nat) (s0 : St) (fresh : Nat)
    (hs0 : Ref.Hst) (hst0 : WordIsSt a s0 hs0)
    (hW : ∀ t, t < 64 → WordIs a (wBases.getD t 0) (w.getD t 0))
    (hK : ∀ t, t < 64 → Ref.K.getD t 0 < 2 ^ 32)
    (hacc : acceptB (sha256Compress' wBases s0 fresh).1 a = true) :
    WordIsSt a (sha256Compress' wBases s0 fresh).2.1
      ((List.range 64).foldl (fun hs t => Ref.round hs (Ref.K.getD t 0) (w.getD t 0)) hs0) := by
  rw [sha256Compress'_eq] at hacc ⊢
  exact foldl_cstep_forces a wBases w (List.range 64) [] s0 fresh hs0 hst0
    (fun t ht => hW t (List.mem_range.mp ht)) (fun t ht => hK t (List.mem_range.mp ht)) hacc

/-- The 64 SHA-256 round constants are 32-bit (the compression's `hK` obligation, discharged). -/
theorem K_lt (t : Nat) (ht : t < 64) : Ref.K.getD t 0 < 2 ^ 32 := by
  interval_cases t <;> decide

#assert_axioms chWord_forces
#assert_axioms majWord_forces
#assert_axioms addMod32_word_forces
#assert_axioms sigmaWord_forces
#assert_axioms rotr_bit
#assert_axioms sha256Round_forces
#assert_axioms sha256Compress'_forces
#assert_axioms K_lt

end Dregg2.Circuit.Emit.Sha256FoldForcing
