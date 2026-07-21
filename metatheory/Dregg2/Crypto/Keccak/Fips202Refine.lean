/-
# `Dregg2.Crypto.Keccak.Fips202Refine` — the FIRST theorems the Keccak floor has ever had.

The executable `Dregg2.Crypto.Keccak` stores the 1600-bit state as 25 `UInt64` lanes; the FIPS 202
spec `Dregg2.Crypto.Keccak.Fips202` models it as a bit function `Fin 5 → Fin 5 → Fin 64 → Bool`. The
bridge is `laneBit`/`toSpec`: lane `(x, y)` is word `a[x + 5·y]!`, and its bit `z` is
`(word).toBitVec.getLsbD z`. This is the little-endian lane/bit convention the executable's `absorb`
and `squeeze` use (byte `i` of a lane at shift `8·(i mod 8)`), so `getLsbD z` picks FIPS 202's
`A[x, y, z]`.

## What is PROVEN here (genuine `∀`, against the executable primitives, `#print axioms` clean)

* `getLsbD_xor/and/not/or` bridges — the per-bit meaning of the `UInt64` bit operations.
* **`chi_bit`** — the executable's exact χ combinator `b0 ^^^ (~~~b1 &&& b2)` equals FIPS 202 §3.2.4's
  `chiBit` at every bit, for ALL three lanes. This is the χ step mapping, proven at the bit level.
* **`rotl64_getLsbD`** — the executable rotation `Keccak.rotl64 w n` equals the FIPS 202 z-rotation
  `subZ` at every bit, for ALL words and ALL shift amounts `< 64`. This is the ρ primitive (and the
  `r = 1` rotation inside θ's `D`).
* **`theta_D_bit`** — the executable's exact `D` combinator `c0 ^^^ rotl64 c1 1` equals FIPS 202
  §3.2.1's `D[x, z] = C[x−1, z] ⊕ C[x+1, z−1]` at every bit (given `c0, c1` are the neighbouring
  column parities). The θ column-mixing, proven at the bit level.
* `rc_lanes_eq_exec` — the spec's Algorithm-5 LFSR round constants reproduce the executable's 24
  precomputed `RC` lanes (`native_decide`; honestly a compiled-evaluation KAT, not a `∀`).

## What is OPEN (stated explicitly, NOT `sorry`-ed — see the `Prop`s at the end)

`chi_bit`/`theta_D_bit`/`rotl64_getLsbD` establish that the per-lane `UInt64` COMBINATORS the
executable uses compute the FIPS 202 step maps bit-for-bit. The remaining obligation is that the
monolithic `keccakRound` (an `Id.run do` with `Array.set!` at literal indices) WIRES those
combinators at the FIPS-mandated lane indices — the θ `C[x]` fan-in, the ρ+π index permutation
`(x,y) ↦ (y, (2x+3y) mod 5)` with the `rho` offset table, and ι touching only lane 0 — i.e. that
`toSpec (Keccak.keccakRound a rc) = Fips202.rnd (…) (toSpec a)`. `keccakRound` exposes no per-step
`def`, so this composition cannot be a gap-free step lemma; it is stated as `RoundCompositionObligation`.
`KeccakFRefinesObligation` (24-fold) and `SpongeRefinesObligation` (pad10*1/absorb/squeeze) complete
the chain. These are the honest remaining work; none is discharged here.
-/
import Dregg2.Crypto.Keccak
import Dregg2.Crypto.Keccak.Fips202Spec

namespace Dregg2.Crypto.Keccak.Fips202Refine

open Dregg2.Crypto.Keccak (rotl64)
open Dregg2.Crypto.Keccak.Fips202

/-- Bit `z` of a `UInt64` lane, little-endian (LSB = z 0). This is FIPS 202's per-lane bit selector. -/
@[inline] def laneBit (w : UInt64) (z : Fin 64) : Bool := w.toBitVec.getLsbD z.val

/-- The abstraction `Array UInt64 → KState`: lane `(x, y)` is word `a[x + 5·y]!`, bit `z` is
`laneBit`. Requires a 25-word array; on the executable's states this always holds. -/
def toSpec (a : Array UInt64) : KState := fun x y z => laneBit (a[x.val + 5 * y.val]!) z

/-! ## Per-bit meaning of the `UInt64` bit operations (foundational bridges). -/

theorem laneBit_xor (a b : UInt64) (z : Fin 64) :
    laneBit (a ^^^ b) z = xor (laneBit a z) (laneBit b z) := by
  simp [laneBit]

theorem laneBit_and (a b : UInt64) (z : Fin 64) :
    laneBit (a &&& b) z = (laneBit a z && laneBit b z) := by
  simp [laneBit]

theorem laneBit_not (a : UInt64) (z : Fin 64) :
    laneBit (~~~ a) z = ! (laneBit a z) := by
  simp only [laneBit, UInt64.toBitVec_not, BitVec.getLsbD_not]
  simp [z.isLt]

theorem laneBit_or (a b : UInt64) (z : Fin 64) :
    laneBit (a ||| b) z = (laneBit a z || laneBit b z) := by
  simp [laneBit]

/-! ## χ — FIPS 202 §3.2.4 (rotation-free; the executable's exact combinator). -/

/-- **χ step, bit level.** The executable computes each χ output lane as `b0 ^^^ (~~~b1 &&& b2)`
(the `o.set!` line of `keccakRound`). For ALL `b0 b1 b2` and every bit `z`, that word's bit is FIPS
202 §3.2.4's `chiBit (bit b0) (bit b1) (bit b2)`. -/
theorem chi_bit (b0 b1 b2 : UInt64) (z : Fin 64) :
    laneBit (b0 ^^^ ((~~~ b1) &&& b2)) z
      = chiBit (laneBit b0 z) (laneBit b1 z) (laneBit b2 z) := by
  simp only [chiBit, laneBit_xor, laneBit_and, laneBit_not]

/-! ## ρ — FIPS 202 §3.2.2 : the rotation primitive `Keccak.rotl64`. -/

/-- **ρ primitive, bit level.** `Keccak.rotl64 w n` (a left-rotation by `n < 64`) reads bit `z` from
bit `(z − n) mod 64` of `w` — exactly the FIPS 202 z-rotation `subZ`. Holds for ALL `w` and ALL
`n < 64`, including the `n = 0` identity. This is the ρ step's rotation, and (at `n = 1`) the
rotation inside θ's `D`. -/
theorem rotl64_getLsbD (w n : UInt64) (hn : n.toNat < 64) (z : Fin 64) :
    laneBit (rotl64 w n) z = laneBit w (subZ z n.toNat) := by
  have hz : z.val < 64 := z.isLt
  have hmod : n.toNat % 64 = n.toNat := Nat.mod_eq_of_lt hn
  simp only [laneBit, subZ]
  unfold rotl64
  by_cases hne : n = 0
  · -- identity branch: n = 0
    subst hne
    simp only [beq_self_eq_true, if_true]
    congr 1
    simp only [UInt64.toNat_ofNat]
    omega
  · -- rotation branch: n ≠ 0
    rw [if_neg (by simpa using hne)]
    have hnn : n.toNat ≠ 0 := by
      intro h; exact hne (UInt64.toNat_inj.mp (by simp [h]))
    have hnpos : 0 < n.toNat := Nat.pos_of_ne_zero hnn
    have hle : n ≤ (64 : UInt64) := by
      simp only [UInt64.le_iff_toNat_le, UInt64.toNat_ofNat]; omega
    have h64 : (64 : BitVec 64).toNat = 64 := rfl
    have hsl : (n.toBitVec % 64).toNat = n.toNat := by
      simp only [BitVec.toNat_umod, UInt64.toNat_toBitVec, h64]; omega
    have hsr : (((64 : UInt64) - n).toBitVec % 64).toNat = 64 - n.toNat := by
      simp only [BitVec.toNat_umod, UInt64.toNat_toBitVec, UInt64.toNat_sub_of_le _ _ hle,
        UInt64.toNat_ofNat, h64]; omega
    simp only [UInt64.toBitVec_or, BitVec.getLsbD_or, UInt64.toBitVec_shiftLeft,
      UInt64.toBitVec_shiftRight, BitVec.shiftLeft_eq', BitVec.ushiftRight_eq',
      BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight, hsl, hsr, hmod]
    by_cases hzn : z.val < n.toNat
    · -- z < n : the shift-left part is empty, output bit comes from the shift-right part
      simp only [decide_eq_true hzn, Bool.not_true, Bool.and_false, Bool.false_and, Bool.false_or]
      congr 1
      omega
    · -- z ≥ n : the shift-right part is out of range, output bit comes from the shift-left part
      rw [BitVec.getLsbD_of_ge w.toBitVec (64 - n.toNat + z.val) (by omega)]
      simp only [Bool.or_false, decide_eq_true hz, decide_eq_false hzn, Bool.not_false,
        Bool.true_and]
      congr 1
      omega

/-! ## θ — FIPS 202 §3.2.1 : the column-mixing `D` combinator. -/

/-- **θ `D` combinator, bit level.** The executable computes `d[x] = c0 ^^^ rotl64 c1 1` where
`c0 = C[(x−1) mod 5]` and `c1 = C[(x+1) mod 5]` are column parities. Its bit `z` is FIPS 202 §3.2.1's
`D[x, z] = C[x−1, z] ⊕ C[x+1, (z−1) mod 64]`, for ALL `c0 c1`. -/
theorem theta_D_bit (c0 c1 : UInt64) (z : Fin 64) :
    laneBit (c0 ^^^ rotl64 c1 1) z
      = xor (laneBit c0 z) (laneBit c1 (subZ z 1)) := by
  rw [laneBit_xor, rotl64_getLsbD c1 1 (by decide) z]
  rfl

/-! ## Round-constant cross-check (compiled-evaluation KAT, honestly labelled). -/

/-- The spec's Algorithm-5 LFSR round constants (`rcLaneOf`, packed into a lane) reproduce the
executable's 24 precomputed `RC` words, bit for bit. `native_decide` (compiled-evaluation residual —
`Lean.ofReduceBool`), so this is a KAT over the 24×64 constant bits, NOT a `∀`-refinement. -/
theorem rc_lanes_eq_exec :
    (List.range 24).all (fun ir =>
      (List.range 64).all (fun z =>
        Fips202.rcLaneOf ir ⟨z % 64, Nat.mod_lt _ (by decide)⟩
          == (Dregg2.Crypto.Keccak.RC[ir]!).toBitVec.getLsbD z)) = true := by
  native_decide

/-! ## The OPEN obligations — stated exactly, discharged NOWHERE. -/

/-- The round-composition obligation: `keccakRound` wires the proven per-lane combinators at the
FIPS 202 lane indices. NOT proven (the executable round is a monolithic `Id.run do`). -/
def RoundCompositionObligation : Prop :=
  ∀ (a : Array UInt64) (ir : Nat), a.size = 25 →
    toSpec (Dregg2.Crypto.Keccak.keccakRound a (Dregg2.Crypto.Keccak.RC[ir]!))
      = Fips202.rnd (Fips202.rcLaneOf ir) (toSpec a)

/-- The permutation obligation: the 24-fold round is Keccak-f[1600]. NOT proven. -/
def KeccakFRefinesObligation : Prop :=
  ∀ (a : Array UInt64), a.size = 25 →
    toSpec (Dregg2.Crypto.Keccak.keccakF a) = Fips202.keccakF (toSpec a)

/-- The sponge obligation: pad10*1 / absorb / squeeze refine the FIPS 202 sponge (UNspecified here —
this file specifies only the permutation). NOT proven. -/
def SpongeRefinesObligation : Prop := True  -- placeholder: sponge spec not yet authored

end Dregg2.Crypto.Keccak.Fips202Refine
