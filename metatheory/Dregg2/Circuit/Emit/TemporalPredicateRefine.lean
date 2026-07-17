/-
# Dregg2.Circuit.Emit.TemporalPredicateRefine — the WHOLE-DESCRIPTOR functional-correctness bridge
for the TEMPORAL predicate (GTE continuous-predicate) family.

`TemporalPredicateEmit` byte-pins the descriptor and proves per-GATE lemmas (`diff_gate_zero_iff`,
`bit_binary_zero_iff`, `t3_constancy_zero_iff`). This file composes those gates into the
WHOLE-descriptor bridge: a trace `Satisfied2` of `temporalPredicateDesc` corresponds to the GENUINE
semantic relation the circuit is meant to compute — "the GTE predicate `value ≥ threshold` HELD at
every step of the padded run, against the published threshold."

## The semantic relation (`GtePredicateHeld`) and the weld

At every active (non-last) row environment `e`, the range gadget (`diff = value − threshold`, a 30-bit
boolean decomposition, and the recomposition gate) forces

  * ORDER — `e.loc THRESHOLD ≤ e.loc VALUE`   (the GTE predicate held at that step).

This is `GtePredicateHeld`. The census designates the TEMPORAL family's semantic model as
`Dregg2.Authority.TemporalAlgebra` (`spec_status = SPEC_EXISTS_NO_EMIT`), whose vesting/GTE atom
`TemporalAtom.afterHeight h` admits at a height `ht` EXACTLY when `h ≤ ht`. So the circuit's per-step
acceptance is welded to that PROVEN model (`temporalPredicate_forces_afterHeight`): a `Satisfied2`
trace forces `(afterHeight threshold).eval value` on every active step — and, through the proven
CTL reading `afterHeight_iff_AG`, places each step's value in the "once vested, vested forever"
satisfaction set of the branching calculus (`temporalPredicate_forces_afterHeight_AG`).

The ORDER leg composes `diff_gate_zero_iff` + `bit_binary_zero_iff` + the recomposition-fold algebra
(`recomp_eval`) into `RecordCircuit.range_proves_le` — the EXACT conclusion `Crypto/RangeProof.lean`
derives. The anti-forge THRESHOLD pin (`temporalPredicate_threshold_is_published`) reads the row-0
`piBinding`.

## Direction

SAT_IMPLIES_SEM (soundness): `Satisfied2 … ⟹` the GTE predicate held on every active step. The whole
leg is PURE ALGEBRA over the boolean bits + the PI pins — the descriptor carries NO hash sites / chip
lookups, so NO cryptographic carrier is needed at all. (Completeness `SEM ⟹ SAT` would require
synthesizing a full padded trace — bits, accumulators, window continuity, boundary/PI bindings, and
the memory legs — and is out of scope here.)

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. There is NO cryptographic residue: the
temporal-predicate descriptor is main-only (no Poseidon2 chip/hash), so the bridge is carrier-free.
NEW file; imports read-only.
-/
import Dregg2.Circuit.Emit.TemporalPredicateEmit
import Dregg2.Circuit.Emit.EffectVmEmitTransfer
import Dregg2.Exec.RecordCircuit
import Dregg2.Authority.TemporalAlgebra

namespace Dregg2.Circuit.Emit.TemporalPredicateRefine

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmRowEnv VmConstraint VmRow)
open Dregg2.Circuit.DescriptorIR2
  (EffectVmDescriptor2 VmConstraint2 Satisfied2 VmTrace envAt)
open Dregg2.Circuit.Emit.TemporalPredicateEmit
open Dregg2.Circuit.Emit.EffectVmEmitTransfer (pPrimeInt)
open Dregg2.Exec.RecordCircuit (bitsToInt Boolean range_sound range_proves_le)
open Dregg2.Authority.TemporalAlgebra (TemporalAtom heightClock afterHeight_iff_AG)
open Dregg2.Proof.CTL (AG)

set_option autoImplicit false

/-! §0 — field-denotation glue. The DEPLOYED `VmConstraint.holdsVm` pins each gate/PI only
`≡ 0 [ZMOD p]` / `≡ pub [ZMOD p]` (`p` the BabyBear prime), NOT `= 0` over ℤ. The genuine ℤ ORDER
(`threshold ≤ value`) is recovered off the DEPLOYED range-check envelope `TpCanon` (bit/diff cells
canonical; value/threshold in the low half — the wrap-free window the high-bit-zero gate needs), the
same lift green `CommittedThresholdRefine` rides. -/

/-- **The deployed range-check canonicality envelope for an active temporal-predicate row.**
The 30 bit cells and the `DIFF` cell are canonical field cells (`0 ≤ · < p`); `VALUE` / `THRESHOLD`
additionally sit in the LOW HALF (`2·x < p`), so — with the high-bit-zero gate forcing `diff < 2^29 <
p/2` — the field subtraction `diff = value − threshold` is WRAP-FREE over ℤ. Without it the congruence
`diff ≡ value − threshold [ZMOD p]` admits the underflow forgery. Inhabited by `acceptEnv_canon`. -/
def TpCanon (e : VmRowEnv) : Prop :=
  (∀ j, j < NUM_DIFF_BITS →
      0 ≤ e.loc (DIFF_BITS_START + j) ∧ e.loc (DIFF_BITS_START + j) < 2013265921)
  ∧ (0 ≤ e.loc DIFF ∧ e.loc DIFF < 2013265921)
  ∧ (0 ≤ e.loc VALUE ∧ 2 * e.loc VALUE < 2013265921)
  ∧ (0 ≤ e.loc THRESHOLD ∧ 2 * e.loc THRESHOLD < 2013265921)

/-! ## §1 — The recomposition-gate arithmetic: the emitted fold IS `bitsToInt` over the bit columns.

The `recomposeSum` right-fold is `Σ_{i<30} 2^i·bit_i`. §1 proves the emitted fold equals `bitsToInt`
of the 30 bit columns, so a satisfied recomposition gate says exactly `bitsToInt (bit columns) = diff`
— the bridge from the wire-form fold to the `RecordCircuit` range-gadget denotation. Pure algebra. -/

/-- The bit columns of a row, as a `List ℤ` (the 30-bit little-endian decomposition witness). -/
def bitVals (a : Assignment) : List ℤ :=
  (List.range NUM_DIFF_BITS).map (fun i => a (DIFF_BITS_START + i))

/-- Appending a HIGH bit `y` past a little-endian bit list adds it at weight `2 ^ |xs|`. -/
theorem bitsToInt_append_singleton (xs : List ℤ) (y : ℤ) :
    bitsToInt (xs ++ [y]) = bitsToInt xs + 2 ^ xs.length * y := by
  induction xs with
  | nil => simp [bitsToInt]
  | cons b rest ih =>
    simp only [List.cons_append, bitsToInt, ih, List.length_cons, pow_succ]
    ring

/-- The `2^·`-weighted sum over `range n` equals `bitsToInt` of the mapped bit list. -/
theorem sum_pow2_eq_bitsToInt (n : Nat) (w : Nat → ℤ) :
    ((List.range n).map (fun i => (2 : ℤ) ^ i * w i)).sum = bitsToInt ((List.range n).map w) := by
  induction n generalizing w with
  | zero => simp [bitsToInt]
  | succ n ih =>
    simp only [List.range_succ, List.map_append, List.sum_append, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, add_zero]
    rw [ih w, bitsToInt_append_singleton, List.length_map, List.length_range]

/-- The emitted right-fold over any index list evaluates to the `2^·`-weighted sum plus the tail. -/
theorem fold_eval (l : List Nat) (tail : EmittedExpr) (a : Assignment) :
    (l.foldr (fun i acc => EmittedExpr.add (.mul (.const ((2 : ℤ) ^ i)) (.var (DIFF_BITS_START + i))) acc)
        tail).eval a
      = (l.map (fun i => (2 : ℤ) ^ i * a (DIFF_BITS_START + i))).sum + tail.eval a := by
  induction l with
  | nil => simp only [List.foldr_nil, List.map_nil, List.sum_nil, zero_add]
  | cons x xs ih =>
    simp only [List.foldr_cons, EmittedExpr.eval, ih, List.map_cons, List.sum_cons]
    ring

/-- **`recomposeSum` evaluates to `bitsToInt` of the bit columns.** -/
theorem recomposeSum_eval (a : Assignment) :
    recomposeSum.eval a = bitsToInt (bitVals a) := by
  rw [recomposeSum, fold_eval, sum_pow2_eq_bitsToInt NUM_DIFF_BITS (fun i => a (DIFF_BITS_START + i))]
  simp only [bitVals, EmittedExpr.eval, add_zero]

/-- **The recomposition gate body IS `bitsToInt (bit columns) − diff`.** So the emitted recomposition
gate vanishing (C3) says exactly `bitsToInt (bit columns) = diff`. -/
theorem recomp_eval (a : Assignment) :
    recomposeBody.eval a = bitsToInt (bitVals a) - a DIFF := by
  simp only [recomposeBody, EmittedExpr.eval, recomposeSum_eval]
  ring

/-! ## §2 — Membership of each load-bearing gate in `temporalPredicateDesc.constraints`.

`constraints = perRowGates ++ windowGates ++ boundaries`, and
`perRowGates = (C1 :: bitGates) ++ [C3, C4, C5, C6]`. The ORDER bridge needs C1 (diff), the 30 bit
gates (C2), C3 (recompose), and the row-0 threshold PI pin. -/

theorem mem_diff :
    VmConstraint2.base (.gate diffBody) ∈ temporalPredicateDesc.constraints := by
  simp only [temporalPredicateDesc, perRowGates]
  apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
  apply List.mem_cons_self

theorem mem_bit (j : Nat) (hj : j < NUM_DIFF_BITS) :
    VmConstraint2.base (.gate (bitBinaryBody j)) ∈ temporalPredicateDesc.constraints := by
  simp only [temporalPredicateDesc, perRowGates]
  apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
  apply List.mem_cons_of_mem
  exact List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩

theorem mem_recompose :
    VmConstraint2.base (.gate recomposeBody) ∈ temporalPredicateDesc.constraints := by
  simp only [temporalPredicateDesc, perRowGates]
  apply List.mem_append_left; apply List.mem_append_left
  apply List.mem_append_right
  apply List.mem_cons_self

theorem mem_highbit :
    VmConstraint2.base (.gate highBitBody) ∈ temporalPredicateDesc.constraints := by
  simp only [temporalPredicateDesc, perRowGates]
  apply List.mem_append_left; apply List.mem_append_left
  apply List.mem_append_right
  apply List.mem_cons_of_mem; apply List.mem_cons_self

theorem mem_pi_threshold :
    VmConstraint2.base (.piBinding VmRow.first THRESHOLD PI_THRESHOLD)
      ∈ temporalPredicateDesc.constraints := by
  simp only [temporalPredicateDesc, boundaries]
  apply List.mem_append_right
  apply List.mem_cons_of_mem; apply List.mem_cons_of_mem; apply List.mem_cons_of_mem
  apply List.mem_cons_self

/-! ## §3 — The whole-descriptor soundness bridge. -/

/-- **`GtePredicateHeld e`** — the genuine per-step semantic relation the temporal-predicate circuit
computes at a row environment `e`: the GTE predicate held, `THRESHOLD ≤ VALUE` (i.e. `value ≥
threshold`). -/
def GtePredicateHeld (e : VmRowEnv) : Prop := e.loc THRESHOLD ≤ e.loc VALUE

/-- **THE WHOLE-DESCRIPTOR BRIDGE (SAT_IMPLIES_SEM).** A multi-table witness that `Satisfied2` the
temporal-predicate descriptor forces the genuine semantic relation on EVERY active (non-last) row:
the GTE predicate `value ≥ threshold` held at that step. The proof composes `diff_gate_zero_iff` +
`bit_binary_zero_iff` + the recomposition-fold algebra (`recomp_eval`) into
`RecordCircuit.range_proves_le` — the EXACT conclusion `Crypto/RangeProof.lean` derives. Whole
descriptor, not a single gate; no cryptographic carrier (the descriptor is main-only). -/
theorem temporalPredicate_satisfied2_sound
    (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hsat : Satisfied2 hash temporalPredicateDesc minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnotlast : i + 1 ≠ t.rows.length)
    (hcanon : TpCanon (envAt t i)) :
    GtePredicateHeld (envAt t i) := by
  have hlast : (i + 1 == t.rows.length) = false := by
    simp only [beq_eq_false_iff_ne]; exact hnotlast
  obtain ⟨hcBit, hcDiff, hcVal, hcTh⟩ := hcanon
  -- every declared per-row gate forces its body to vanish MOD `p` on the active non-last row.
  have gate_forces : ∀ g : EmittedExpr,
      VmConstraint2.base (.gate g) ∈ temporalPredicateDesc.constraints →
      g.eval (envAt t i).loc ≡ 0 [ZMOD 2013265921] := by
    intro g hmem
    have h := hsat.rowConstraints i hi _ hmem
    simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm, hlast] at h
    exact h
  -- C2: every bit column is genuinely boolean over ℤ (prime splits `p ∣ b·(b−1)`; canonical window).
  have hbit : ∀ j, j < NUM_DIFF_BITS →
      (envAt t i).loc (DIFF_BITS_START + j) = 0 ∨ (envAt t i).loc (DIFF_BITS_START + j) = 1 := by
    intro j hj
    have hg := gate_forces (bitBinaryBody j) (mem_bit j hj)
    have hkey : (bitBinaryBody j).eval (envAt t i).loc
        = (envAt t i).loc (DIFF_BITS_START + j) * ((envAt t i).loc (DIFF_BITS_START + j) - 1) := by
      simp only [bitBinaryBody, EmittedExpr.eval]; ring
    rw [hkey, Int.modEq_zero_iff_dvd] at hg
    have hc := hcBit j hj
    rcases pPrimeInt.dvd_mul.mp hg with hx | hx
    · obtain ⟨k, hk⟩ := hx; left; omega
    · obtain ⟨k, hk⟩ := hx; right; omega
  have hbool : Boolean (bitVals (envAt t i).loc) := by
    intro b hb
    simp only [bitVals, List.mem_map, List.mem_range] at hb
    obtain ⟨j, hj, rfl⟩ := hb
    exact hbit j hj
  -- C4: the high bit is genuinely ZERO (its gate + canonicality), so the recomposed diff < 2^29.
  have hb29 : (envAt t i).loc (DIFF_BITS_START + 29) = 0 := by
    have hg := gate_forces highBitBody mem_highbit
    simp only [highBitBody, EmittedExpr.eval] at hg
    rw [show DIFF_BITS_START + NUM_DIFF_BITS - 1 = DIFF_BITS_START + 29 by
          simp only [NUM_DIFF_BITS]; omega] at hg
    have hg' : (2013265921 : ℤ) ∣ (envAt t i).loc (DIFF_BITS_START + 29) :=
      Int.modEq_zero_iff_dvd.mp hg
    have hc := hcBit 29 (by decide)
    obtain ⟨k, hk⟩ := hg'
    omega
  -- C3: `bitsToInt (bit columns) = diff` — the recomposition binds mod `p`, and both sides lie in
  -- `[0, p)` (30 boolean bits give `< 2^30 < p`; `diff` is canonical), so the congruence is an ℤ eq.
  have hrec : bitsToInt (bitVals (envAt t i).loc) = (envAt t i).loc DIFF := by
    have hg := gate_forces recomposeBody mem_recompose
    rw [show recomposeBody.eval (envAt t i).loc
          = bitsToInt (bitVals (envAt t i).loc) - (envAt t i).loc DIFF
        from recomp_eval (envAt t i).loc, Int.modEq_zero_iff_dvd] at hg
    have hlow := range_sound _ hbool
    rw [show (bitVals (envAt t i).loc).length = 30 from by
          simp only [bitVals, List.length_map, List.length_range, NUM_DIFF_BITS],
        show ((2 : ℤ) ^ 30) = 1073741824 from by norm_num] at hlow
    obtain ⟨k, hk⟩ := hg
    omega
  -- diff < 2^29 (the high bit being zero drops the top weight from the recomposed value).
  have hsplit : bitVals (envAt t i).loc
      = ((List.range 29).map (fun j => (envAt t i).loc (DIFF_BITS_START + j)))
        ++ [(envAt t i).loc (DIFF_BITS_START + 29)] := by
    rw [bitVals, show NUM_DIFF_BITS = 30 from rfl, List.range_succ, List.map_append,
      List.map_cons, List.map_nil]
  have hlowBool : Boolean ((List.range 29).map (fun j => (envAt t i).loc (DIFF_BITS_START + j))) := by
    intro b hb
    simp only [List.mem_map, List.mem_range] at hb
    obtain ⟨j, hj, rfl⟩ := hb
    exact hbit j (by rw [show NUM_DIFF_BITS = 30 from rfl]; omega)
  have hlow29 := range_sound _ hlowBool
  rw [List.length_map, List.length_range, show ((2 : ℤ) ^ 29) = 536870912 from by norm_num] at hlow29
  have hfull : bitsToInt (bitVals (envAt t i).loc)
      = bitsToInt ((List.range 29).map (fun j => (envAt t i).loc (DIFF_BITS_START + j))) := by
    rw [hsplit, bitsToInt_append_singleton, show (envAt t i).loc (DIFF_BITS_START + 29) = 0 from hb29]
    ring
  have hDiffLt : (envAt t i).loc DIFF < 536870912 := by rw [← hrec, hfull]; omega
  -- C1: `diff ≡ value − threshold [ZMOD p]`; `diff < 2^29 < p/2` + the low-half windows make the
  -- subtraction wrap-free, so the congruence IS the ℤ identity.
  have hdiff : (envAt t i).loc DIFF
      = (envAt t i).loc VALUE - (envAt t i).loc THRESHOLD := by
    have hg := gate_forces diffBody mem_diff
    have hkey : diffBody.eval (envAt t i).loc
        = (envAt t i).loc DIFF - (envAt t i).loc VALUE + (envAt t i).loc THRESHOLD := by
      simp only [diffBody, EmittedExpr.eval]; ring
    rw [hkey, Int.modEq_zero_iff_dvd] at hg
    obtain ⟨k, hk⟩ := hg
    omega
  -- welded to RecordCircuit.range_proves_le: threshold ≤ value.
  show (envAt t i).loc THRESHOLD ≤ (envAt t i).loc VALUE
  exact range_proves_le _ _ (bitVals (envAt t i).loc) hbool (hrec.trans hdiff)

/-- **The GTE predicate held at EVERY step of the run** — the whole-run reading of the bridge: on
every active (non-last) row window, the descriptor forces `value ≥ threshold`. -/
theorem temporalPredicate_held_every_active_step
    (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hsat : Satisfied2 hash temporalPredicateDesc minit mfin maddrs t)
    (hcanon : ∀ i, i < t.rows.length → i + 1 ≠ t.rows.length → TpCanon (envAt t i)) :
    ∀ i, i < t.rows.length → i + 1 ≠ t.rows.length → GtePredicateHeld (envAt t i) :=
  fun i hi hnl => temporalPredicate_satisfied2_sound hash minit mfin maddrs t hsat i hi hnl (hcanon i hi hnl)

/-- **The anti-forge THRESHOLD pin (row 0).** A `Satisfied2` trace binds the row-0 threshold column to
the published PI `pi[PI_THRESHOLD]` — the audit-#3 constancy surface (`t3Body` propagates it across
rows). -/
theorem temporalPredicate_threshold_is_published
    (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hsat : Satisfied2 hash temporalPredicateDesc minit mfin maddrs t)
    (hlen : 0 < t.rows.length) :
    (envAt t 0).loc THRESHOLD ≡ (envAt t 0).pub PI_THRESHOLD [ZMOD 2013265921] := by
  have h := hsat.rowConstraints 0 hlen _ mem_pi_threshold
  simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm] at h
  exact h rfl

/-! ## §4 — The WELD to the existing proven model `Dregg2.Authority.TemporalAlgebra`.

The GTE the range gadget proves is EXACTLY the admission of the vesting/GTE atom
`TemporalAtom.afterHeight threshold` at height `value` (`afterHeight h` admits iff `h ≤ height`). So
the circuit's per-step acceptance forces the proven model's atom, and — via the proven CTL reading
`afterHeight_iff_AG` — places each accepted step's value in the "once vested, vested forever" `AG`
satisfaction set of the branching calculus over `heightClock`. -/

/-- **`Satisfied2 ⟹ the proven `afterHeight` atom admits`** (per active step). For naturals `vN, tN`
that are the step's value / threshold columns, the descriptor forces `(afterHeight tN).eval vN` — the
GTE atom of `TemporalAlgebra` admits at the step. -/
theorem temporalPredicate_forces_afterHeight
    (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hsat : Satisfied2 hash temporalPredicateDesc minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnotlast : i + 1 ≠ t.rows.length)
    (hcanon : TpCanon (envAt t i))
    (vN tN : Nat) (rec : Dregg2.Exec.Value)
    (hv : (envAt t i).loc VALUE = (vN : ℤ)) (ht : (envAt t i).loc THRESHOLD = (tN : ℤ)) :
    (TemporalAtom.afterHeight tN).eval vN rec = true := by
  have horder : (envAt t i).loc THRESHOLD ≤ (envAt t i).loc VALUE :=
    temporalPredicate_satisfied2_sound hash minit mfin maddrs t hsat i hi hnotlast hcanon
  rw [hv, ht] at horder
  have hle : tN ≤ vN := by exact_mod_cast horder
  simpa only [TemporalAtom.eval, decide_eq_true_eq] using hle

/-- **`Satisfied2 ⟹ the step's value is in the `AG`-vested satisfaction set`** — the branching-time
reading, inherited verbatim through the PROVEN `afterHeight_iff_AG`: every accepted step's value `vN`
satisfies `AG heightClock {m | tN ≤ m}` — once the GTE gate opens at that value it is open on every
future of the height-indexed trace ("value ≥ threshold, permanently"). -/
theorem temporalPredicate_forces_afterHeight_AG
    (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hsat : Satisfied2 hash temporalPredicateDesc minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnotlast : i + 1 ≠ t.rows.length)
    (hcanon : TpCanon (envAt t i))
    (vN tN : Nat) (rec : Dregg2.Exec.Value)
    (hv : (envAt t i).loc VALUE = (vN : ℤ)) (ht : (envAt t i).loc THRESHOLD = (tN : ℤ)) :
    vN ∈ AG heightClock { m | tN ≤ m } :=
  (afterHeight_iff_AG tN vN rec).mp
    (temporalPredicate_forces_afterHeight hash minit mfin maddrs t hsat i hi hnotlast hcanon vN tN rec hv ht)

#assert_axioms temporalPredicate_satisfied2_sound
#assert_axioms temporalPredicate_threshold_is_published
#assert_axioms temporalPredicate_forces_afterHeight
#assert_axioms temporalPredicate_forces_afterHeight_AG

/-! ## §5 — NON-VACUITY: a concrete SATISFYING assignment, and constraints that BITE.

The anti-scar witnesses. §5a exhibits `acceptLoc`, a concrete row assignment on which EVERY declared
per-row gate body vanishes (so the `Satisfied2` hypothesis is genuinely inhabitable at the row level),
together with `acceptEnv_meets` proving the CONCLUSION holds on it with real, distinct numbers
(`3 ≤ 8`, threshold pinned `3 = 3`), NOT a `P → P`. §5b exhibits `rejectLoc` (value LOWERED below the
threshold), on which the difference gate BITES, the model-welded proof that an under-threshold value
has NO range witness, and `underThreshold_rejected` — a concrete `Satisfied2` that FAILS whenever the
row-0 value is below the threshold. -/

/-! ### §5a — the ACCEPT side. -/

/-- A concrete satisfying local row: value `8`, threshold `3`, diff `5` (bits 0 and 2 set),
accumulator `1`/`acc+1 = 2`, `step+1 = 1`, everything else `0`. -/
def acceptLoc : Assignment := fun c =>
  if c = VALUE then 8
  else if c = THRESHOLD then 3
  else if c = DIFF then 5
  else if c = DIFF_BITS_START then 1
  else if c = DIFF_BITS_START + 2 then 1
  else if c = ACCUMULATOR then 1
  else if c = ACC_PLUS_ONE then 2
  else if c = STEP_PLUS_ONE then 1
  else 0

/-- The matching public inputs: `pi[PI_THRESHOLD] = 3` (the published threshold). -/
def acceptPub : Assignment := fun k => if k = PI_THRESHOLD then 3 else 0

/-- The satisfying row environment. -/
def acceptEnv : VmRowEnv := { loc := acceptLoc, nxt := acceptLoc, pub := acceptPub }

-- Every declared PER-ROW gate body VANISHES on the satisfying assignment (accept witness, gate by gate).
#guard decide (diffBody.eval acceptLoc = 0)
#guard decide ((bitBinaryBody 0).eval acceptLoc = 0)
#guard decide ((bitBinaryBody 2).eval acceptLoc = 0)
#guard decide ((bitBinaryBody 29).eval acceptLoc = 0)
#guard decide (recomposeBody.eval acceptLoc = 0)
#guard decide (highBitBody.eval acceptLoc = 0)
#guard decide (accStepBody.eval acceptLoc = 0)
#guard decide (stepIncBody.eval acceptLoc = 0)
-- The row-0 threshold PI pin holds.
#guard decide (acceptLoc THRESHOLD = acceptPub PI_THRESHOLD)
-- The GTE atom of the proven model admits at the accept value, and rejects a below-threshold value.
#guard (TemporalAtom.afterHeight 3).eval 8 (Dregg2.Exec.Value.int 0) == true
#guard (TemporalAtom.afterHeight 3).eval 2 (Dregg2.Exec.Value.int 0) == false

/-- **The CONCLUSION is non-trivially inhabited.** The semantic relation `GtePredicateHeld` holds on
the satisfying environment with REAL, distinct numbers (`3 ≤ 8`), and the threshold is the published
one (`3 = 3`) — so the bridge's conclusion is genuine, not a `True`/`P → P` shell. -/
theorem acceptEnv_meets :
    GtePredicateHeld acceptEnv ∧ acceptEnv.loc THRESHOLD = acceptEnv.pub PI_THRESHOLD := by
  refine ⟨?_, ?_⟩
  · show acceptLoc THRESHOLD ≤ acceptLoc VALUE
    decide
  · show acceptLoc THRESHOLD = acceptPub PI_THRESHOLD
    decide

/-- **The proven-model atom admits on the accept env** — `afterHeight 3` (threshold) admits at value
`8`, non-trivially (`3 ≤ 8`). -/
theorem acceptEnv_afterHeight :
    (TemporalAtom.afterHeight 3).eval 8 (Dregg2.Exec.Value.int 0) = true := by decide

/-- **The canonicality envelope is genuinely INHABITED** — every enveloped cell of the accept witness
(bits `0`/`1`, `diff = 5`, value `8` / threshold `3` deep in the low half) is a small canonical field
value. So the bridge does NOT rest on a vacuous range-check hypothesis. -/
theorem acceptEnv_canon : TpCanon acceptEnv := by
  refine ⟨?_, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩⟩
  intro j hj
  have hj30 : j < 30 := hj
  interval_cases j <;> exact ⟨by decide, by decide⟩

/-! ### §5b — the REJECT side (the constraint BITES). -/

/-- The accept assignment with the value LOWERED below the threshold (`2 < 3`), keeping the diff
column — so the difference gate can no longer vanish. -/
def rejectLoc : Assignment := fun c => if c = VALUE then 2 else acceptLoc c

/-- **The difference gate BITES** on the under-threshold assignment
(`diff − value + threshold = 5 − 2 + 3 = 6 ≠ 0`): the constraint system rejects it. -/
theorem reject_diff_bites : ¬ (diffBody.eval rejectLoc = 0) := by decide

/-- **Model-welded reject (the honest soundness bite).** An under-threshold value has NO range
witness: the honest diff `value − threshold = 2 − 3 = −1` cannot be a boolean bit-decomposition,
because `bitsToInt` of boolean bits is non-negative (`RecordCircuit.range_sound`). So the range
gadget is UNSATISFIABLE for `value < threshold`. -/
theorem underThreshold_has_no_range_witness :
    ¬ ∃ bits : List ℤ, Boolean bits ∧ bitsToInt bits = (2 : ℤ) - 3 := by
  rintro ⟨bits, hbool, hrec⟩
  have h := (range_sound bits hbool).1
  rw [hrec] at h
  omega

/-- **`underThreshold_rejected` — a concrete `Satisfied2` that FAILS (constraint bites, whole
descriptor).** ANY witness whose row-0 value is strictly below the threshold CANNOT satisfy the
temporal-predicate descriptor (≥ 2 rows, so row 0 is active). The hypothesis `value < threshold` is
freely satisfiable, so this rejection is non-vacuous — the descriptor is a genuine, biting filter,
not a rubber stamp. Directly contraposes the soundness bridge. -/
theorem underThreshold_rejected
    (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hlen : 1 < t.rows.length) (hcanon : TpCanon (envAt t 0))
    (hunder : (envAt t 0).loc VALUE < (envAt t 0).loc THRESHOLD) :
    ¬ Satisfied2 hash temporalPredicateDesc minit mfin maddrs t := by
  intro hsat
  have hnotlast : 0 + 1 ≠ t.rows.length := by omega
  have h : (envAt t 0).loc THRESHOLD ≤ (envAt t 0).loc VALUE :=
    temporalPredicate_satisfied2_sound hash minit mfin maddrs t hsat 0 (by omega) hnotlast hcanon
  omega

#assert_axioms acceptEnv_meets
#assert_axioms acceptEnv_afterHeight
#assert_axioms acceptEnv_canon
#assert_axioms underThreshold_has_no_range_witness
#assert_axioms underThreshold_rejected

end Dregg2.Circuit.Emit.TemporalPredicateRefine
