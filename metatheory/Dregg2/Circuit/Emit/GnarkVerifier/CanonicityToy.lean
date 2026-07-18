/-
# Dregg2.Circuit.Emit.GnarkVerifier.CanonicityToy — THE toy end-to-end ∀-refinement.

ONE emitted gnark check — `AssertIsCanonical(babybear v)` (babybear.go:69: two 31-bit
range checks, `v < 2^31` AND `(p−1) − v < 2^31`, together pinning `v ∈ [0, p)` for
`p = BabyBearP = 2013265921`) — PROVED, as a genuine ∀-theorem over every `v : Fr`, to
hold exactly on the canonical BabyBear residues:

    canonicity_refines :          gHolds canonicityData (canonAsg v) ↔ v.val < 2013265921
    canonicity_refines_emitted :  satisfiedEmitted (emit canonicityData) (canonAsg v)
                                    ↔ v.val < 2013265921

So the emit socket (`EmitFaithful`) genuinely REFINES a spec end to end: spec
(`v.val < BabyBearP`) ↔ frontend circuit ↔ lowered genuine R1CS (`gHolds`, riding the
foundation's proven bridge) ↔ the emitted wire form the JSON grammar renders. Not a
`#guard` sample — a theorem quantified over all `2^254`-ish field elements.

Layout (gnark-shape): `var 0` = the public input `v`; `vars 1–31` = the 31 bit hints of
`v`'s range check; `vars 32–62` = the 31 bit hints of the `(p−1) − v` check. `canonAsg v`
is the honest hint fill (the Lean twin of gnark's hint solver / `test.IsSolved`), exactly
the posture of `BabyBearFr`'s builder — whose `runCanon` `#guard`s sample this same
gadget at 8 points; here the whole family is closed under a ∀.

Classified seams (named, not silent — same ledger as the foundation headers):
  * The theorems quantify over the HONEST hint fill (`canonAsg`), as `BabyBearFr` names
    for all its gadgets. The adversarial face is `canonicity_sound_of_boolean`: ANY
    witness whose hint region is boolean is forced canonical. Discharging the booleanity
    hypothesis itself from `b·b = b` needs `x² = x → x ∈ {0,1}` in `Fr` — true because
    `rBN254` is prime, i.e. exactly the named Pratt-certificate seam of `R1csFr`
    (`Field Fr`); a `CommRing` alone admits nontrivial idempotents.
  * Range checks realized as bit decomposition (same contract as deployed gnark's lookup
    argument — the seam already named in `BabyBearFr`).
-/
import Mathlib.Tactic.LinearCombination
import Dregg2.Tactics
import Dregg2.Circuit.R1csFr
import Dregg2.Circuit.BabyBearFr
import Dregg2.Circuit.Emit.GnarkVerifier.EmitFaithful

namespace Dregg2.Circuit.Emit.GnarkVerifier

open Dregg2.Circuit.R1csFr
open Dregg2.Circuit.BabyBearFr (pBB)

instance : NeZero rBN254 := ⟨by norm_num [rBN254]⟩

/-! ## §1 The circuit: `AssertIsCanonical` over `var 0`, bits as hint variables. -/

/-- The recomposition wire of an `n`-bit region at `base`: `Σ_{i<n} 2^i · var (base+i)`. -/
def recompWire (base : ℕ) : ℕ → Wire
  | 0     => .const 0
  | n + 1 => .add (recompWire base n) (.mul (.const ((2 ^ n : ℕ) : Fr)) (.var (base + n)))

/-- The range-check assert block for `w < 2^n` with bit hints at `base`: booleanity
`bᵢ·bᵢ = bᵢ` for each hint plus the recomposition `w = Σ 2^i·bᵢ` (the `BabyBearFr.rangeCheck`
constraint shape, laid out at fixed indices so the circuit is a closed term). -/
def rangeAsserts (w : Wire) (base n : ℕ) : List (Wire × Wire) :=
  ((List.range n).map fun i =>
    (Wire.mul (.var (base + i)) (.var (base + i)), Wire.var (base + i)))
    ++ [(w, recompWire base n)]

/-- **The canonicity circuit** — `BBApi.AssertIsCanonical(var 0)` (babybear.go:69): both
`v < 2^31` (bits at 1–31) and `(p−1) − v < 2^31` (bits at 32–62), the second wire spelled
`(p−1) + (−1)·v` exactly as the gnark `api.Sub(BabyBearP-1, v)`. -/
def canonicityCircuit : Circuit :=
  ⟨rangeAsserts (.var 0) 1 31
    ++ rangeAsserts
        (.add (.const ((pBB - 1 : ℕ) : Fr)) (.mul (.const (-1)) (.var 0))) 32 31⟩

/-- The emission package for the toy: one public input `v ↦ var 0`, one recorded gadget
invocation `AssertIsCanonical(var 0)`, the circuit above. -/
def canonicityData : GnarkCircuitData :=
  { name         := "babybear_assert_is_canonical_v1"
    publicInputs := [("v", 0)]
    gadgets      := [⟨"AssertIsCanonical", [0]⟩]
    circuit      := canonicityCircuit }

/-- **The honest hint fill** (the Lean twin of gnark's hint solver): `var 0 = v`, bits of
`v.val` at 1–31, bits of `(p−1) − v.val` (ℕ-truncated when `v` is non-canonical — in
which case the recomposition assert FAILS, the reject polarity) at 32–62. -/
def canonAsg (v : Fr) : Assignment := fun i =>
  if i = 0 then v
  else if i < 32 then ((v.val / 2 ^ (i - 1) % 2 : ℕ) : Fr)
  else (((pBB - 1 - v.val) / 2 ^ (i - 32) % 2 : ℕ) : Fr)

/-! ## §2 Recomposition lemmas. -/

/-- ℕ-cast injectivity below the modulus. -/
private theorem cast_inj_lt {x y : ℕ} (hx : x < rBN254) (hy : y < rBN254)
    (h : (x : Fr) = (y : Fr)) : x = y := by
  have h' := congrArg ZMod.val h
  rwa [ZMod.val_cast_of_lt hx, ZMod.val_cast_of_lt hy] at h'

private theorem natCast_val_self (v : Fr) : ((v.val : ℕ) : Fr) = v :=
  ZMod.natCast_rightInverse v

/-- Under honest bit hints for `x`, the recomposition wire evaluates to `x % 2^n`. -/
private theorem recompWire_eval_honest (x base : ℕ) (a : Assignment) :
    ∀ n : ℕ, (∀ i, i < n → a (base + i) = ((x / 2 ^ i % 2 : ℕ) : Fr)) →
      (recompWire base n).eval a = ((x % 2 ^ n : ℕ) : Fr)
  | 0, _ => by simp [recompWire, Wire.eval, Nat.mod_one]
  | n + 1, ha => by
      have hih := recompWire_eval_honest x base a n fun i hi => ha i (by omega)
      have hbit := ha n (by omega)
      have hmod : x % 2 ^ (n + 1) = x % 2 ^ n + 2 ^ n * (x / 2 ^ n % 2) := by
        rw [pow_succ, Nat.mod_mul]
      simp only [recompWire, Wire.eval, hih, hbit, hmod]
      push_cast
      ring

/-- Under ANY boolean bit fill, the recomposition wire evaluates to SOME `x < 2^n` —
the adversarial-face engine. -/
private theorem recompWire_eval_boolean (base : ℕ) (a : Assignment) :
    ∀ n : ℕ, (∀ i, i < n → a (base + i) = 0 ∨ a (base + i) = 1) →
      ∃ x : ℕ, x < 2 ^ n ∧ (recompWire base n).eval a = (x : Fr)
  | 0, _ => ⟨0, by norm_num, by simp [recompWire, Wire.eval]⟩
  | n + 1, hb => by
      obtain ⟨x, hx, hev⟩ := recompWire_eval_boolean base a n fun i hi => hb i (by omega)
      have h2 : 2 ^ (n + 1) = 2 ^ n * 2 := pow_succ 2 n
      rcases hb n (by omega) with h | h
      · exact ⟨x, by omega, by simp [recompWire, Wire.eval, hev, h]⟩
      · refine ⟨x + 2 ^ n, by omega, ?_⟩
        simp only [recompWire, Wire.eval, hev, h]
        push_cast
        ring

/-- Under honest bit hints for `x`, the whole range block is satisfied IFF the checked
wire evaluates to `x % 2^n` (booleanity asserts hold automatically for honest bits). -/
private theorem rangeAsserts_honest_iff (w : Wire) (base x n : ℕ) (a : Assignment)
    (ha : ∀ i, i < n → a (base + i) = ((x / 2 ^ i % 2 : ℕ) : Fr)) :
    (∀ p ∈ rangeAsserts w base n, p.1.eval a = p.2.eval a)
      ↔ w.eval a = ((x % 2 ^ n : ℕ) : Fr) := by
  simp only [rangeAsserts]
  constructor
  · intro h
    have hlast := h (w, recompWire base n) (by simp)
    simpa [recompWire_eval_honest x base a n ha] using hlast
  · intro hw p hp
    rcases List.mem_append.mp hp with hp | hp
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp
      have hbit := ha i (List.mem_range.mp hi)
      rcases Nat.mod_two_eq_zero_or_one (x / 2 ^ i) with h0 | h0 <;>
        simp [Wire.eval, hbit, h0]
    · have hp' : p = (w, recompWire base n) := by simpa using hp
      subst hp'
      simpa [recompWire_eval_honest x base a n ha] using hw

/-- Under ANY boolean bit fill, a satisfied range block forces the checked wire to SOME
value `< 2^n`. -/
private theorem rangeAsserts_boolean_bound (w : Wire) (base n : ℕ) (a : Assignment)
    (hb : ∀ i, i < n → a (base + i) = 0 ∨ a (base + i) = 1)
    (h : ∀ p ∈ rangeAsserts w base n, p.1.eval a = p.2.eval a) :
    ∃ x : ℕ, x < 2 ^ n ∧ w.eval a = (x : Fr) := by
  obtain ⟨x, hx, hev⟩ := recompWire_eval_boolean base a n hb
  have hlast := h (w, recompWire base n) (by simp [rangeAsserts])
  exact ⟨x, hx, hlast.trans hev⟩

/-! ## §3 The frontend ∀-theorem. -/

/-- The canonicity circuit under the honest hint fill accepts EXACTLY the canonical
BabyBear residues — the frontend face of the toy refinement, for every `v : Fr`. -/
theorem canonicity_frontend (v : Fr) :
    canonicityCircuit.satisfied (canonAsg v) ↔ v.val < pBB := by
  have hp : pBB = 2013265921 := rfl
  have h31 : (2 : ℕ) ^ 31 = 2147483648 := by norm_num
  have hvr : v.val < rBN254 := ZMod.val_lt v
  have hpr : pBB - 1 < rBN254 := by decide
  have ha1 : ∀ i : ℕ, i < 31 → canonAsg v (1 + i) = ((v.val / 2 ^ i % 2 : ℕ) : Fr) := by
    intro i hi
    have h0 : ¬(1 + i = 0) := by omega
    have h1 : 1 + i < 32 := by omega
    have h2 : 1 + i - 1 = i := by omega
    simp only [canonAsg, if_neg h0, if_pos h1, h2]
  have ha2 : ∀ i : ℕ, i < 31 →
      canonAsg v (32 + i) = (((pBB - 1 - v.val) / 2 ^ i % 2 : ℕ) : Fr) := by
    intro i hi
    have h0 : ¬(32 + i = 0) := by omega
    have h1 : ¬(32 + i < 32) := by omega
    have h2 : 32 + i - 32 = i := by omega
    simp only [canonAsg, if_neg h0, if_neg h1, h2]
  have hv0 : canonAsg v 0 = v := by simp [canonAsg]
  show (∀ p ∈ canonicityCircuit.asserts, p.1.eval (canonAsg v) = p.2.eval (canonAsg v))
    ↔ v.val < pBB
  simp only [canonicityCircuit]
  rw [List.forall_mem_append,
    rangeAsserts_honest_iff _ 1 v.val 31 _ ha1,
    rangeAsserts_honest_iff _ 32 (pBB - 1 - v.val) 31 _ ha2]
  simp only [Wire.eval, hv0]
  constructor
  · rintro ⟨h1, h2⟩
    have hm : v.val % 2 ^ 31 < 2 ^ 31 := Nat.mod_lt _ (by omega)
    have hval31 : v.val < 2 ^ 31 := by
      have h1' := congrArg ZMod.val h1
      rw [ZMod.val_cast_of_lt (a := v.val % 2 ^ 31)
        (lt_of_le_of_lt (Nat.mod_le _ _) hvr)] at h1'
      omega
    by_contra hge
    simp only [not_lt] at hge
    have hz : pBB - 1 - v.val = 0 := by omega
    rw [hz] at h2
    have h2' : ((pBB - 1 : ℕ) : Fr) = v := by
      have hzz : ((0 % 2 ^ 31 : ℕ) : Fr) = 0 := by norm_num
      rw [hzz] at h2
      linear_combination h2
    have h2v := congrArg ZMod.val h2'
    rw [ZMod.val_cast_of_lt hpr] at h2v
    omega
  · intro hlt
    have hle : v.val ≤ pBB - 1 := by omega
    refine ⟨?_, ?_⟩
    · rw [Nat.mod_eq_of_lt (by omega : v.val < 2 ^ 31), natCast_val_self]
    · rw [Nat.mod_eq_of_lt (by omega : pBB - 1 - v.val < 2 ^ 31),
        Nat.cast_sub hle, natCast_val_self]
      ring

/-! ## §4 THE TOY ∀-REFINEMENT — the deliverable. -/

/-- **`canonicity_refines`** — the toy end-to-end ∀-refinement: the LOWERED genuine R1CS
of the emitted `AssertIsCanonical(babybear v)` package, under the canonical witness
extension of the honest hint fill, is satisfied IFF `v.val < 2013265921` (`BabyBearP`) —
for EVERY `v : Fr`. The socket shape is a genuine refinement of the spec: spec ↔ frontend
(`canonicity_frontend`) ↔ R1CS (the foundation's proven `R1csFr.gHolds` bridge). -/
theorem canonicity_refines (v : Fr) :
    gHolds canonicityData (canonAsg v) ↔ v.val < 2013265921 := by
  unfold gHolds
  rw [← R1csFr.gHolds]
  exact canonicity_frontend v

/-- The same ∀-refinement at the EMITTED wire form (composing `emit_faithful`): the bytes
the JSON grammar renders denote exactly the canonicity spec. -/
theorem canonicity_refines_emitted (v : Fr) :
    satisfiedEmitted (emit canonicityData) (canonAsg v) ↔ v.val < 2013265921 :=
  (emit_faithful canonicityData (canonAsg v)).symm.trans (canonicity_refines v)

/-- **The adversarial face** (modulo booleanity — the named idempotent/primality seam):
ANY witness whose hint region 1–62 is boolean and which satisfies the circuit has a
CANONICAL public input. No boolean hint fill exists for a non-canonical `v`. -/
theorem canonicity_sound_of_boolean (a : Assignment)
    (hbool : ∀ i : ℕ, 1 ≤ i → i ≤ 62 → a i = 0 ∨ a i = 1)
    (hsat : canonicityCircuit.satisfied a) :
    (a 0).val < 2013265921 := by
  have hp : pBB = 2013265921 := rfl
  have h31 : (2 : ℕ) ^ 31 = 2147483648 := by norm_num
  have hr : rBN254
      = 21888242871839275222246405745257275088548364400416034343698204186575808495617 :=
    rfl
  have hsat' : ∀ p ∈ canonicityCircuit.asserts, p.1.eval a = p.2.eval a := hsat
  simp only [canonicityCircuit] at hsat'
  rw [List.forall_mem_append] at hsat'
  obtain ⟨hs1, hs2⟩ := hsat'
  obtain ⟨x, hx, hev1⟩ := rangeAsserts_boolean_bound _ 1 31 a
    (fun i hi => hbool (1 + i) (by omega) (by omega)) hs1
  obtain ⟨y, hy, hev2⟩ := rangeAsserts_boolean_bound _ 32 31 a
    (fun i hi => hbool (32 + i) (by omega) (by omega)) hs2
  simp only [Wire.eval] at hev1 hev2
  have hval : (a 0).val = x := by
    rw [hev1, ZMod.val_cast_of_lt (by omega)]
  by_contra hge
  simp only [not_lt] at hge
  have hkey : ((rBN254 + (pBB - 1) - x : ℕ) : Fr) = (y : Fr) := by
    rw [Nat.cast_sub (by omega : x ≤ rBN254 + (pBB - 1)), Nat.cast_add,
      ZMod.natCast_self, zero_add, ← hev1]
    linear_combination hev2
  have hval2 := congrArg ZMod.val hkey
  rw [ZMod.val_cast_of_lt (by omega), ZMod.val_cast_of_lt (by omega)] at hval2
  omega

#assert_axioms canonicity_frontend
#assert_axioms canonicity_refines
#assert_axioms canonicity_refines_emitted
#assert_axioms canonicity_sound_of_boolean

/-! ## §5 Teeth — decidable samples at both polarities (the ∀-theorems above subsume
these; the guards pin that the DEFINITIONS compute, mirroring `BabyBearFr.runCanon`). -/

#guard canonicityCircuit.satisfied (canonAsg 0)
#guard canonicityCircuit.satisfied (canonAsg ((pBB - 1 : ℕ) : Fr))
#guard ¬ canonicityCircuit.satisfied (canonAsg ((pBB : ℕ) : Fr))
#guard ¬ canonicityCircuit.satisfied (canonAsg ((2 ^ 31 : ℕ) : Fr))
#guard ¬ canonicityCircuit.satisfied (canonAsg ((rBN254 - 5 : ℕ) : Fr))

end Dregg2.Circuit.Emit.GnarkVerifier
