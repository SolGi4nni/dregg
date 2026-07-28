/-
# Dregg2.Circuit.Emit.StakeWidthRange — the ENCODER WIDTH GATE, and the bite `rangeNonneg` never had

## The wound this closes

`Sha256MerkleFold.pairHash_ignores_bits_above_64` and `LightClientMidHashFold`'s BLAKE2b twin prove
that a hash MESSAGE WORD is read only modulo `2^64`. Every light-client collection encoder in the
tree drops an unbounded `Nat` — a stake, a weight, a height — straight into such a word:

  * `LightClientSolHashFold.solRowLeaf` — the Solana stake-table row. `solTable_stake_collision`
    exhibits stake `50` and stake `50 + 2^64` sharing an anchor root.
  * `LightClientMidHashFold.rowBlock` — the Midnight authority row.
    `authSetRootRef_weight_collision` exhibits weight `0` and weight `2^64` sharing an authority-set
    root.

Both were written up as a NAMED RESIDUAL ("the missing encoder range-check"). This file is that
range-check, and it is LEAN-AUTHORED AIR: a `def`-generator over `AirBuilder.Head` plus a FORCING
lemma over the emitted gates. No Rust hand-writes a constraint for it.

## What was actually missing — `rangeNonneg` HAD NO BITE

`AirBuilder.rangeNonneg` (the `Builder::range_nonneg` twin) has existed and has been emitted by
`Bls12381Tower.fpLimbRange` and the automatafl coordinate decompose. **Nothing in the tree ever
proved that a satisfied `rangeNonneg` FORCES its term into `[0, 2^rbits)`.** `AirBuilder`'s
`#assert_axioms` block pins `gBin_eval_zero_iff`, `condNonzero_forces` and `forcedGe0Term_eval` — the
range gadget is absent from it, because there was no theorem to pin. A generator with no forcing
lemma is a shape, not a check; `rangeNonneg_forces` below is the check.

## The three things proved here

  * `rangeNonneg_forces` / `rangeNonneg_forces_nat` — **THE BITE.** A satisfied boolean pin on every
    bit column plus the satisfied recomposition gate forces `0 ≤ term < 2^|bits|`. Stated over the
    EMITTED objects (`gBin` evaluation, `evalH` of the recomposition head), and `rangeNonneg_eq`
    proves those two hypotheses are EXACTLY the constraint list `rangeNonneg` emits — not a
    hand-picked subset.
  * `widthGate` + `widthGate_forces` — the same at one witnessed value column, which is the shape a
    row encoder emits per field. `widthGate_refuses` is the tooth: the inflated Solana stake
    `50 + 2^64` has NO satisfying assignment at 64 bits.
  * `alias_collapses_in_range` — the algebra the whole repair rests on. The truncation family is
    `v ↦ v + k·2^rbits`; two in-range members force `k = 0`. So the alias class collapses to a point
    and the exhibited collisions become UNWITNESSABLE rather than merely unexhibited.

## Both legs, because a shape that only refutes is half a floor

  * SATISFIABLE — `demoAsg` is an explicit assignment putting `50` at the value column and its LSB-
    first bits at the bit columns; `demo_bits_boolean` / `demo_recomp` check EVERY emitted gate of
    `widthGate 0 1 8` by kernel evaluation, so the gate is not `False` in disguise
    (`demo_in_range_nonvacuous` pins that the witnessed value is genuinely nonzero).
  * REFUTABLE — `widthGate_refuses` derives `False` from a satisfying assignment for an out-of-range
    value. Both the Solana stake witness and the Midnight weight witness are refused
    (`sol_stake_witness_refused`, `mid_weight_witness_refused`).

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; no `sorry`/`admit`/`native_decide`.
NEW file; imports read-only (`AirBuilder` only, so both the SHA-256 and the BLAKE2b light-client
folds can import it without either importing the other).
-/
import Dregg2.Circuit.Emit.AirBuilder

namespace Dregg2.Circuit.Emit.StakeWidthRange

open Dregg2.Circuit (Assignment)
open Dregg2.Circuit.DescriptorIR2 (VmConstraint2)
open Dregg2.Circuit.Emit.AirBuilder

set_option autoImplicit false

/-! ## §1 — The recomposition head, NAMED, and the emitted list it belongs to. -/

/-- The recomposition head `term − Σ 2^t·b_t` — the second half of `AirBuilder.rangeNonneg`, named so
a forcing lemma has something to take as a hypothesis. -/
def recompHead (term : Head) (bits : List Nat) : Head :=
  bits.zipIdx.foldl (fun h (p : Nat × Nat) => h.addLin (-(2 ^ p.2 : ℤ)) p.1) term

/-- **The hypotheses below ARE the emitted gates.** `rangeNonneg` is exactly the boolean pins on the
bit columns followed by the recomposition gate — so a proof consuming "every `gBin` is zero" plus
"the recomposition head is zero" is consuming the WHOLE emitted list, not a chosen subset. -/
theorem rangeNonneg_eq (term : Head) (bits : List Nat) :
    rangeNonneg term bits = bits.map binGate ++ [cgH (recompHead term bits)] := rfl

/-! ## §2 — THE BITE. -/

/-- Negating under a `map` negates the sum. -/
theorem sum_map_neg {α : Type} (l : List α) (f : α → ℤ) :
    (l.map (fun x => -(f x))).sum = -((l.map f).sum) := by
  induction l with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons, List.sum_cons, ih]; ring

/-- The weighted bit sum of BOOLEAN columns, starting at bit index `n`, lies in
`[0, 2^(n+len) − 2^n]`. The arithmetic core of the range gadget. -/
theorem bitSum_bounds (a : Assignment) :
    ∀ (bits : List Nat) (n : Nat), (∀ c ∈ bits, a c = 0 ∨ a c = 1) →
      0 ≤ ((bits.zipIdx n).map (fun p => (2 ^ p.2 : ℤ) * a p.1)).sum
      ∧ ((bits.zipIdx n).map (fun p => (2 ^ p.2 : ℤ) * a p.1)).sum
          ≤ 2 ^ (n + bits.length) - 2 ^ n := by
  intro bits
  induction bits with
  | nil => intro n _; simp
  | cons c cs ih =>
    intro n hb
    have hc : a c = 0 ∨ a c = 1 := hb c (by simp)
    have hrest : ∀ x ∈ cs, a x = 0 ∨ a x = 1 := fun x hx => hb x (by simp [hx])
    have h := ih (n + 1) hrest
    have hp : (0 : ℤ) < 2 ^ n := by positivity
    have hs : (2 : ℤ) ^ (n + 1) = 2 * 2 ^ n := by rw [pow_succ]; ring
    have hidx : n + (c :: cs).length = n + 1 + cs.length := by simp [List.length_cons]; omega
    rw [hidx]
    simp only [List.zipIdx_cons, List.map_cons, List.sum_cons]
    obtain ⟨h1, h2⟩ := h
    rw [hs] at h2
    rcases hc with hc | hc <;> rw [hc]
    · constructor <;> [linarith; linarith]
    · constructor <;> [linarith; linarith]

/-- **THE RANGE GADGET BITES.** A satisfied `AirBuilder.rangeNonneg term bits` — every bit column
pinned boolean by its `gBin` gate, and the recomposition gate zero — FORCES
`0 ≤ term < 2^|bits|`. A term outside that window has NO satisfying assignment.

This is the theorem `rangeNonneg` was emitted without. -/
theorem rangeNonneg_forces (a : Assignment) (term : Head) (bits : List Nat)
    (hbin : ∀ c ∈ bits, (gBin c).eval a = 0)
    (hrec : evalH (recompHead term bits) a = 0) :
    0 ≤ evalH term a ∧ evalH term a < 2 ^ bits.length := by
  have hb : ∀ c ∈ bits, a c = 0 ∨ a c = 1 := fun c hc => (gBin_eval_zero_iff a c).mp (hbin c hc)
  have hfold := evalH_foldl_addLinG a term (fun p : Nat × Nat => -(2 ^ p.2 : ℤ)) bits.zipIdx
    (fun p : Nat × Nat => p.1)
  rw [recompHead, hfold] at hrec
  have hneg : (bits.zipIdx.map (fun p : Nat × Nat => -(2 ^ p.2 : ℤ) * a p.1)).sum
      = -((bits.zipIdx.map (fun p : Nat × Nat => (2 ^ p.2 : ℤ) * a p.1)).sum) := by
    have := sum_map_neg bits.zipIdx (fun p : Nat × Nat => (2 ^ p.2 : ℤ) * a p.1)
    simpa using this
  rw [hneg] at hrec
  have hval : evalH term a = (bits.zipIdx.map (fun p : Nat × Nat => (2 ^ p.2 : ℤ) * a p.1)).sum := by
    linarith
  obtain ⟨h1, h2⟩ := bitSum_bounds a bits 0 hb
  rw [← hval] at h1 h2
  refine ⟨h1, ?_⟩
  simp only [Nat.zero_add, pow_zero] at h2
  linarith

/-- **THE BITE, in `Nat`** — the form a model-side encoder consumes: a witnessed value column
carrying the `Nat` `v` is forced `v < 2^|bits|`. -/
theorem rangeNonneg_forces_nat (a : Assignment) (v col : Nat) (bits : List Nat)
    (hval : a col = (v : ℤ))
    (hbin : ∀ c ∈ bits, (gBin c).eval a = 0)
    (hrec : evalH (recompHead (Head.lin 1 col) bits) a = 0) :
    v < 2 ^ bits.length := by
  have h := (rangeNonneg_forces a (Head.lin 1 col) bits hbin hrec).2
  rw [evalH_lin, hval, one_mul] at h
  exact_mod_cast h

/-! ## §3 — `widthGate`: the per-FIELD generator a row encoder emits. -/

/-- **THE ENCODER WIDTH GATE (Lean-authored AIR).** `rbits` fresh boolean columns at `bit0` plus the
recomposition binding them to the witnessed value column `valCol`. This IS `AirBuilder.rangeNonneg`
at a single column; it is named so a stake / weight / height encoder has exactly ONE thing to emit
per field, and so the forcing lemma below can be quoted per field.

`rbits + 1` constraints (`rbits` boolean pins + one recomposition gate). -/
def widthGate (valCol bit0 rbits : Nat) : List VmConstraint2 :=
  rangeNonneg (Head.lin 1 valCol) (bitsFrom bit0 rbits)

/-- The gate's bit columns are `rbits` many. -/
theorem bitsFrom_length (base len : Nat) : (bitsFrom base len).length = len := by
  simp [bitsFrom]

/-- The emitted budget: `rbits` boolean pins + one recomposition gate. -/
theorem widthGate_length (valCol bit0 rbits : Nat) :
    (widthGate valCol bit0 rbits).length = rbits + 1 := by
  simp [widthGate, rangeNonneg, bitsFrom]

/-- **THE WIDTH GATE FORCES THE WIDTH.** A satisfying assignment whose value column carries the
`Nat` `v` has `v < 2^rbits`. -/
theorem widthGate_forces (a : Assignment) (v valCol bit0 rbits : Nat)
    (hval : a valCol = (v : ℤ))
    (hbin : ∀ c ∈ bitsFrom bit0 rbits, (gBin c).eval a = 0)
    (hrec : evalH (recompHead (Head.lin 1 valCol) (bitsFrom bit0 rbits)) a = 0) :
    v < 2 ^ rbits := by
  have h := rangeNonneg_forces_nat a v valCol (bitsFrom bit0 rbits) hval hbin hrec
  rwa [bitsFrom_length] at h

/-- **THE TOOTH — an out-of-range value is UNWITNESSABLE.** There is no satisfying assignment for a
value column carrying `v ≥ 2^rbits`. This is the whole security content: the collision exhibits
below are not merely unexhibited under the gate, they cannot be witnessed. -/
theorem widthGate_refuses (a : Assignment) (v valCol bit0 rbits : Nat)
    (hbig : 2 ^ rbits ≤ v)
    (hval : a valCol = (v : ℤ))
    (hbin : ∀ c ∈ bitsFrom bit0 rbits, (gBin c).eval a = 0)
    (hrec : evalH (recompHead (Head.lin 1 valCol) (bitsFrom bit0 rbits)) a = 0) :
    False := by
  have h := widthGate_forces a v valCol bit0 rbits hval hbin hrec
  omega

/-! ## §4 — The alias algebra: WHY the width gate closes the collisions.

A hash that reads a message word only modulo `2^w`, or an encoder that truncates a field to `w`
bits, generates exactly ONE family of confusions: `v ↦ v + k·2^w`. Range-checking to `w` bits
collapses every such class to a point. -/

/-- **THE ALIAS FAMILY COLLAPSES IN RANGE.** If both `v` and its `k`-fold `2^rbits`-shift are
in range, the shift is trivial. -/
theorem alias_collapses_in_range (rbits v k : Nat)
    (h₂ : v + k * 2 ^ rbits < 2 ^ rbits) : k = 0 := by
  rcases Nat.eq_zero_or_pos k with h | h
  · exact h
  · exfalso
    have : 2 ^ rbits ≤ k * 2 ^ rbits := Nat.le_mul_of_pos_left _ h
    omega

/-- The modular form: a truncating read is INJECTIVE on the in-range domain. -/
theorem mod_injective_in_range (m v w : Nat) (hv : v < m) (hw : w < m) (h : v % m = w % m) :
    v = w := by
  rwa [Nat.mod_eq_of_lt hv, Nat.mod_eq_of_lt hw] at h

/-! ## §5 — BOTH LEGS.

The repo's own instrument doctrine: a shape that is only REFUTABLE is half a floor. §5a exhibits a
satisfying assignment by kernel evaluation of every emitted gate; §5b refutes the two collision
witnesses this file exists to kill. -/

/-! ### §5a — SATISFIABLE: `50` at 8 bits, every emitted gate checked in the kernel.

Value column `0`, bit columns `1..8` (LSB-first). `50 = 0b110010`, so bits 1, 4, 5 are set — columns
2, 5, 6. -/

/-- The witness assignment for `widthGate 0 1 8` at value `50`. -/
def demoAsg : Assignment
  | 0 => 50
  | 2 => 1
  | 5 => 1
  | 6 => 1
  | _ => 0

/-- Every boolean pin the gate emits is satisfied. -/
theorem demo_bits_boolean : ∀ c ∈ bitsFrom 1 8, (gBin c).eval demoAsg = 0 := by decide

/-- The recomposition gate the range gadget emits is satisfied. -/
theorem demo_recomp : evalH (recompHead (Head.lin 1 0) (bitsFrom 1 8)) demoAsg = 0 := by decide

/-- The satisfying witness carries a genuinely NONZERO value — the class is not the empty one
wearing the gadget's name. -/
theorem demo_in_range_nonvacuous : demoAsg 0 = 50 ∧ (50 : Nat) < 2 ^ 8 := ⟨rfl, by decide⟩

/-- **THE GATE FIRES ON A SATISFIED PREMISE** — the forcing lemma run on the exhibited witness,
so floor, coverage and conclusion are exercised together rather than separately. -/
theorem widthGate_forces_fires : (50 : Nat) < 2 ^ 8 :=
  widthGate_forces demoAsg 50 0 1 8 rfl demo_bits_boolean demo_recomp

/-! ### §5b — REFUTABLE: the two collision witnesses are UNWITNESSABLE under the gate. -/

/-- **THE SOLANA STAKE-INFLATION WITNESS IS REFUSED.** `LightClientSolHashFold.solTable_stake_collision`
puts stake `50 + 2^64` at the same anchor root as stake `50`. Under a 64-bit stake width gate — the
width of the deployed `EpochStakeTable`'s `u64` lamports (`bridge/src/solana_consensus.rs:132`,
hashed as `stake.to_le_bytes()`) — that value has NO satisfying assignment. -/
theorem sol_stake_witness_refused (a : Assignment) (valCol bit0 : Nat)
    (hval : a valCol = ((50 + 2 ^ 64 : Nat) : ℤ))
    (hbin : ∀ c ∈ bitsFrom bit0 64, (gBin c).eval a = 0)
    (hrec : evalH (recompHead (Head.lin 1 valCol) (bitsFrom bit0 64)) a = 0) :
    False :=
  widthGate_refuses a (50 + 2 ^ 64) valCol bit0 64 (by omega) hval hbin hrec

/-- **THE MIDNIGHT WEIGHT-INFLATION WITNESS IS REFUSED.**
`LightClientMidHashFold.authSetRootRef_weight_collision` puts weight `2^64` at the same authority-set
root as weight `0`. Under a 64-bit weight width gate — the BLAKE2b word width, which is also the
Midnight authority weight's `u64` — that value has NO satisfying assignment. -/
theorem mid_weight_witness_refused (a : Assignment) (valCol bit0 : Nat)
    (hval : a valCol = ((2 ^ 64 : Nat) : ℤ))
    (hbin : ∀ c ∈ bitsFrom bit0 64, (gBin c).eval a = 0)
    (hrec : evalH (recompHead (Head.lin 1 valCol) (bitsFrom bit0 64)) a = 0) :
    False :=
  widthGate_refuses a (2 ^ 64) valCol bit0 64 (by omega) hval hbin hrec

/-! ## §6 — axiom hygiene. -/

#assert_axioms sum_map_neg
#assert_axioms bitSum_bounds
#assert_axioms rangeNonneg_forces
#assert_axioms rangeNonneg_forces_nat
#assert_axioms widthGate_forces
#assert_axioms widthGate_refuses
#assert_axioms alias_collapses_in_range
#assert_axioms mod_injective_in_range
#assert_axioms demo_bits_boolean
#assert_axioms demo_recomp
#assert_axioms widthGate_forces_fires
#assert_axioms sol_stake_witness_refused
#assert_axioms mid_weight_witness_refused

#print axioms rangeNonneg_forces
#print axioms widthGate_refuses

end Dregg2.Circuit.Emit.StakeWidthRange
