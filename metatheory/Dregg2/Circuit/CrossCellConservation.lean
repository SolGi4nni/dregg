/-
# `Dregg2.Circuit.CrossCellConservation` — the TURN-WIDE cross-cell value-conservation AIR (Σδ=0),
emitted from Lean (law #1). **MULTI-LIMB accumulator revision** (closes the mod-`p` wrap-residual).

## The gap this closes (grounded) and WHY the single-felt sum was UNSOUND

The deployed rotated per-cell proof forces the *per-cell* balance arithmetic + the per-cell signed
NET_DELTA public input. It does NOT force the *turn-wide cross-cell* pairing: a single-cell sovereign
proof cannot conclude that no value was MINTED across the whole turn. This AIR aggregates the per-cell
signed deltas and forces `Σδ = 0` for one asset.

The PRIOR revision summed the running balance as a SINGLE BabyBear felt mod `p = 2013265921` and pinned
`balance[last] = 0`. Since `2·2^30 = 2^31 > p`, two credit rows `mag₁ = 1006632961`, `mag₂ = 1006632960`
(both `< 2^30`) sum to exactly `p ≡ 0`: the boundary accepted a turn that MINTED ≈`2·10^9` with no debit
(forged value-conservation). A row-count bound `N·2^30 < p` forces `N < 2` (one cell) — useless.

## THE FIX — a MULTI-LIMB (15-bit) running accumulator with carry propagation (mirrors the vault)

We split each row's signed delta into a NON-NEGATIVE credit contribution and a NON-NEGATIVE debit
contribution and accumulate each into its own running 3-limb (45-bit) 15-bit-limb value with per-row
carry propagation, EXACTLY like `Dregg2.Deos.VaultSatDescriptor`'s 15-bit limbs. Because every limb
and carry is range-checked `< 2^15` (and each transition residual is a sum of `< 2^15` terms, so
`|R| < 2^17 < p`), the mod-`p` gate residual lifts to an EXACT-ℤ limb recurrence — no wrap. The
running credit / debit reconstructions therefore equal the TRUE integer partial sums over ℤ. The
boundary pins the final credit limbs EQUAL to the final debit limbs, so `Σ credits = Σ debits` over ℤ:
`Σδ = 0` is DERIVED (not assumed). The `2^45` ceiling fails CLOSED (it exceeds the old design's `~2^31`
honest range, so NO honest turn that worked before is rejected — no liveness degradation).

The `1006632961 + 1006632960 = p ≠ 0` forgery is now UNSAT: the derived integer credit sum is `p`, and
conservation forces it `= 0` (`ccc_psum_forgery_unsat`).

## Trace layout (width `WIDTH = 172`)

```text
  [0]  asset  · [1] mag · [2] sign (+1/−1/0) · [3] present (1 real / 0 pad)
  [4]  cc0 · [5] cc1     — credit contribution limbs (= mag limbs on a credit row, else 0)
  [6]  dc0 · [7] dc1     — debit  contribution limbs (= mag limbs on a debit  row, else 0)
  [8]  C0 · [9] C1 · [10] C2  — running credit accumulator (3×15-bit limbs)
  [11] D0 · [12] D1 · [13] D2 — running debit  accumulator
  [14] KC0 · [15] KC1        — credit add carries (bit)
  [16] KD0 · [17] KD1        — debit  add carries (bit)
  [18..] range-check bit columns (10 limbs × 15 bits + 4 carries × 1 bit = 154 bits)
```

## The teeth (soundness, proved below)

* `ccc_reconC_eq_creditSum` / `ccc_reconD_eq_debitSum` — the running accumulator reconstructs the TRUE
  integer prefix sum of credit / debit contributions (row induction over the EXACT-ℤ limb recurrence).
* `ccc_conserves` — the final credit sum EQUALS the final debit sum over ℤ (the boundary + the inert
  wrap row + limb canonicality); the realized `Σδ = 0`.
* `ccc_psum_forgery_unsat` — the concrete `p`-sum forgery cannot satisfy the descriptor.

The per-row `cc/dc` split IS pinned to the published `sign·mag` by the in-AIR contribution gates
(`creditZ0/1`, `debitZ0/1`, `totalContribGate`, `signSquareGate`, `paddingSignGate`); the off-AIR
verifier fills those columns from each per-cell proof's NET_DELTA PI.

All `#assert_axioms`-clean. NO `sorry`/`admit`/carrier; conservation DERIVED from in-circuit limb gates.
-/
import Dregg2.Circuit.DescriptorIR2
import Dregg2.Circuit.Emit.EffectVmEmitTransfer
import Dregg2.Tactics

namespace Dregg2.Circuit.CrossCellConservation

open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRowEnv)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmitTransfer (pPrimeInt gate_modEq_iff)

set_option autoImplicit false

/-! ## §0 — mod-`p` → ℤ bounded-lift primitives (the vault's `canonEq` / `modEqZeroBounded`). -/

/-- Two CANONICAL (`0 ≤ · < p`) integers congruent mod `p` are EQUAL. -/
private theorem canonEq {a b : ℤ} (h : a ≡ b [ZMOD 2013265921])
    (ha0 : 0 ≤ a) (hap : a < 2013265921) (hb0 : 0 ≤ b) (hbp : b < 2013265921) : a = b := by
  unfold Int.ModEq at h
  rwa [Int.emod_eq_of_lt ha0 hap, Int.emod_eq_of_lt hb0 hbp] at h

/-- A residual `R ≡ 0 [ZMOD p]` confined to `(−p, p)` is EXACTLY `0` over ℤ (the 15-bit soundness
payoff: every honest limb-transition residual is a sum of `< 2^15` terms, so `|R| < 2^17 < p`). -/
private theorem modEqZeroBounded {R : ℤ} (h : R ≡ 0 [ZMOD 2013265921])
    (hlo : -2013265921 < R) (hhi : R < 2013265921) : R = 0 := by
  rw [Int.modEq_zero_iff_dvd] at h
  obtain ⟨k, hk⟩ := h
  omega

/-- Carry-forward: on the inert wrap row every contribution/carry correction `corr ≡ 0`, so an
accumulator-limb transition residual `res ≡ 0` with `a − b = res + corr` gives `a ≡ b [ZMOD p]` —
the last row carries the running accumulator forward UNCHANGED (mod `p`), no bounds needed. -/
private theorem carryFwd {res corr a b : ℤ} (hres : res ≡ 0 [ZMOD 2013265921])
    (hx : a - b = res + corr) (hcorr : corr ≡ 0 [ZMOD 2013265921]) : a ≡ b [ZMOD 2013265921] := by
  have h : a - b ≡ 0 [ZMOD 2013265921] := by rw [hx]; simpa using Int.ModEq.add hres hcorr
  calc a = b + (a - b) := by ring
    _ ≡ b + 0 [ZMOD 2013265921] := Int.ModEq.add_left _ h
    _ = b := by ring

/-- Two integers congruent mod `p` whose difference is confined to `(−p, p)` are EQUAL. -/
private theorem liftEq {a b : ℤ} (h : a ≡ b [ZMOD 2013265921])
    (hlo : -2013265921 < a - b) (hhi : a - b < 2013265921) : a = b := by
  have h0 : a - b ≡ 0 [ZMOD 2013265921] := by
    have := Int.ModEq.sub h (Int.ModEq.refl b); simpa using this
  have := modEqZeroBounded h0 hlo hhi
  omega

/-! ## §1 — trace + PI layout. -/
namespace Ccc

def ASSET_COL   : Nat := 0
def MAG_COL     : Nat := 1
def SIGN_COL    : Nat := 2
def PRESENT_COL : Nat := 3
def CC0 : Nat := 4
def CC1 : Nat := 5
def DC0 : Nat := 6
def DC1 : Nat := 7
def C0  : Nat := 8
def C1  : Nat := 9
def C2  : Nat := 10
def D0  : Nat := 11
def D1  : Nat := 12
def D2  : Nat := 13
def KC0 : Nat := 14
def KC1 : Nat := 15
def KD0 : Nat := 16
def KD1 : Nat := 17
def BIT_BASE : Nat := 18

/-- Limb width (15 bits keeps every transition residual `< 2^17 < p`). -/
def LIMB_BITS : Nat := 15
/-- `2^15`. -/
def TWO15 : Int := 32768
/-- `2^30`. -/
def TWO30 : Int := 1073741824

def PI_ASSET : Nat := 0
def PI_COUNT : Nat := 1

end Ccc

/-! ## §2 — bit-decomposition range primitive (self-contained; the v2 assembly requires the legacy
range carrier empty, so we mirror the vault's explicit bit gates). -/

/-- `Σ_{i<n} 2^i · bit(i)` (low bit first). -/
def bitSum (bit : Nat → Nat) : Nat → EmittedExpr
  | 0 => .const 0
  | n + 1 => .add (bitSum bit n) (.mul (.const ((2 : Int) ^ n)) (.var (bit n)))

/-- A boolean-bit sum lies in `[0, 2^n)`. -/
theorem bitSum_nonneg_lt (loc : Nat → ℤ) (bit : Nat → Nat) :
    ∀ n, (∀ i, i < n → loc (bit i) = 0 ∨ loc (bit i) = 1) →
      0 ≤ (bitSum bit n).eval loc ∧ (bitSum bit n).eval loc < 2 ^ n := by
  intro n
  induction n with
  | zero => intro _; simp [bitSum, EmittedExpr.eval]
  | succ n ih =>
    intro hb
    obtain ⟨h0, h1⟩ := ih (fun i hi => hb i (Nat.lt_succ_of_lt hi))
    have hpow : (2 : ℤ) ^ (n + 1) = 2 ^ n + 2 ^ n := by rw [pow_succ]; ring
    have hp : (0 : ℤ) < 2 ^ n := by positivity
    simp only [bitSum, EmittedExpr.eval]
    rcases hb n (Nat.lt_succ_self n) with h | h <;> rw [h] <;> constructor <;> omega

/-- `(−1)·e`. -/
def eNeg (e : EmittedExpr) : EmittedExpr := .mul (.const (-1)) e
/-- `a − b`. -/
def eSub (a b : EmittedExpr) : EmittedExpr := .add a (eNeg b)

/-- A plain (non-selector) booleanity gate `b·(b−1)`. -/
def rgBool (b : Nat) : VmConstraint2 :=
  .base (.gate (.mul (.var b) (.add (.var b) (.const (-1)))))

/-- A plain range-assembly gate `col − Σ 2^i bit_i`. -/
def rgAssembly (col : Nat) (bit : Nat → Nat) (n : Nat) : VmConstraint2 :=
  .base (.gate (eSub (.var col) (bitSum bit n)))

/-- The range gates for a spec list: per spec, `n` booleanity gates then the assembly gate, bit
blocks assigned in list order from `base`. -/
def rangeGatesAux : List (Nat × Nat) → Nat → List VmConstraint2
  | [], _ => []
  | (col, n) :: rest, base =>
      ((List.range n).map (fun i => rgBool (base + i)))
        ++ [rgAssembly col (fun i => base + i) n]
        ++ rangeGatesAux rest (base + n)

/-- The ordered range-checked columns and widths: 10 limbs @ 15 bits + 4 carries @ 1 bit. -/
def rangeSpecs : List (Nat × Nat) :=
  [ (Ccc.CC0, 15), (Ccc.CC1, 15), (Ccc.DC0, 15), (Ccc.DC1, 15)
  , (Ccc.C0, 15), (Ccc.C1, 15), (Ccc.C2, 15)
  , (Ccc.D0, 15), (Ccc.D1, 15), (Ccc.D2, 15)
  , (Ccc.KC0, 1), (Ccc.KC1, 1), (Ccc.KD0, 1), (Ccc.KD1, 1) ]

def rangeGates : List VmConstraint2 := rangeGatesAux rangeSpecs Ccc.BIT_BASE

/-- Total range-check bit columns. -/
def TOTAL_RANGE_BITS : Nat := rangeSpecs.foldl (fun a s => a + s.2) 0

/-- Trace width: past the last bit column. -/
def WIDTH : Nat := Ccc.BIT_BASE + TOTAL_RANGE_BITS

/-! ## §3 — the fixed (non-range) gates. -/

/-- A base row gate from an `EmittedExpr` body. -/
def gate (body : EmittedExpr) : VmConstraint2 := .base (.gate body)

/-- `present ∈ {0,1}`. -/
def boolPresent : VmConstraint2 := gate (.mul (.var Ccc.PRESENT_COL) (.add (.var Ccc.PRESENT_COL) (.const (-1))))
/-- `present·(sign² − 1) = 0` (a real row carries `sign ∈ {+1,−1}`). -/
def signSquareGate : VmConstraint2 :=
  gate (.mul (.var Ccc.PRESENT_COL) (.add (.mul (.var Ccc.SIGN_COL) (.var Ccc.SIGN_COL)) (.const (-1))))
/-- `(1 − present)·sign = 0` (a pad row carries `sign = 0`). -/
def paddingSignGate : VmConstraint2 :=
  gate (.mul (.add (.const 1) (eNeg (.var Ccc.PRESENT_COL))) (.var Ccc.SIGN_COL))
/-- `(sign − 1)·cc0 = 0` (credit-limb vanishes unless `sign = 1`). -/
def creditZ0 : VmConstraint2 := gate (.mul (.add (.var Ccc.SIGN_COL) (.const (-1))) (.var Ccc.CC0))
def creditZ1 : VmConstraint2 := gate (.mul (.add (.var Ccc.SIGN_COL) (.const (-1))) (.var Ccc.CC1))
/-- `(sign + 1)·dc0 = 0` (debit-limb vanishes unless `sign = −1`). -/
def debitZ0 : VmConstraint2 := gate (.mul (.add (.var Ccc.SIGN_COL) (.const 1)) (.var Ccc.DC0))
def debitZ1 : VmConstraint2 := gate (.mul (.add (.var Ccc.SIGN_COL) (.const 1)) (.var Ccc.DC1))
/-- `(cc0 + 2^15·cc1) + (dc0 + 2^15·dc1) = present·mag` (the split totals the magnitude). -/
def totalContribGate : VmConstraint2 :=
  gate (eSub
    (.add (.add (.var Ccc.CC0) (.mul (.const Ccc.TWO15) (.var Ccc.CC1)))
          (.add (.var Ccc.DC0) (.mul (.const Ccc.TWO15) (.var Ccc.DC1))))
    (.mul (.var Ccc.PRESENT_COL) (.var Ccc.MAG_COL)))

/-- The asset partition pin (first + last rows). -/
def assetPinFirst : VmConstraint2 := .base (.piBinding .first Ccc.ASSET_COL Ccc.PI_ASSET)
def assetPinLast  : VmConstraint2 := .base (.piBinding .last  Ccc.ASSET_COL Ccc.PI_ASSET)

/-- Seed (`.first`): `C_k[0] = credit-limb_k[0]`, `C2[0] = 0`; same for debit. -/
def seedC0 : VmConstraint2 := .base (.boundary .first (eSub (.var Ccc.C0) (.var Ccc.CC0)))
def seedC1 : VmConstraint2 := .base (.boundary .first (eSub (.var Ccc.C1) (.var Ccc.CC1)))
def seedC2 : VmConstraint2 := .base (.boundary .first (.var Ccc.C2))
def seedD0 : VmConstraint2 := .base (.boundary .first (eSub (.var Ccc.D0) (.var Ccc.DC0)))
def seedD1 : VmConstraint2 := .base (.boundary .first (eSub (.var Ccc.D1) (.var Ccc.DC1)))
def seedD2 : VmConstraint2 := .base (.boundary .first (.var Ccc.D2))

/-- Inert wrap row (`.last`): the last row contributes nothing (contributions + carries pinned 0), so
the running accumulators carry forward unchanged into it. -/
def inertCC0 : VmConstraint2 := .base (.boundary .last (.var Ccc.CC0))
def inertCC1 : VmConstraint2 := .base (.boundary .last (.var Ccc.CC1))
def inertDC0 : VmConstraint2 := .base (.boundary .last (.var Ccc.DC0))
def inertDC1 : VmConstraint2 := .base (.boundary .last (.var Ccc.DC1))
def inertKC0 : VmConstraint2 := .base (.boundary .last (.var Ccc.KC0))
def inertKC1 : VmConstraint2 := .base (.boundary .last (.var Ccc.KC1))
def inertKD0 : VmConstraint2 := .base (.boundary .last (.var Ccc.KD0))
def inertKD1 : VmConstraint2 := .base (.boundary .last (.var Ccc.KD1))

/-- Final equality (`.last`): `C_k[last] = D_k[last]` — the turn-wide conservation `Σ credits = Σ debits`. -/
def eqLast0 : VmConstraint2 := .base (.boundary .last (eSub (.var Ccc.C0) (.var Ccc.D0)))
def eqLast1 : VmConstraint2 := .base (.boundary .last (eSub (.var Ccc.C1) (.var Ccc.D1)))
def eqLast2 : VmConstraint2 := .base (.boundary .last (eSub (.var Ccc.C2) (.var Ccc.D2)))

open WindowExpr (loc nxt)

/-- credit-limb transition `next[C0] = local[C0] + next[cc0] − 2^15·next[KC0]`. -/
def transC0 : VmConstraint2 := .windowGate
  { onTransition := true
  , body := .add (nxt Ccc.C0) (.add (.mul (.const (-1)) (loc Ccc.C0))
      (.add (.mul (.const (-1)) (nxt Ccc.CC0)) (.mul (.const Ccc.TWO15) (nxt Ccc.KC0)))) }
/-- `next[C1] = local[C1] + next[cc1] + next[KC0] − 2^15·next[KC1]`. -/
def transC1 : VmConstraint2 := .windowGate
  { onTransition := true
  , body := .add (nxt Ccc.C1) (.add (.mul (.const (-1)) (loc Ccc.C1))
      (.add (.mul (.const (-1)) (nxt Ccc.CC1))
        (.add (.mul (.const (-1)) (nxt Ccc.KC0)) (.mul (.const Ccc.TWO15) (nxt Ccc.KC1))))) }
/-- `next[C2] = local[C2] + next[KC1]`. -/
def transC2 : VmConstraint2 := .windowGate
  { onTransition := true
  , body := .add (nxt Ccc.C2) (.add (.mul (.const (-1)) (loc Ccc.C2)) (.mul (.const (-1)) (nxt Ccc.KC1))) }
def transD0 : VmConstraint2 := .windowGate
  { onTransition := true
  , body := .add (nxt Ccc.D0) (.add (.mul (.const (-1)) (loc Ccc.D0))
      (.add (.mul (.const (-1)) (nxt Ccc.DC0)) (.mul (.const Ccc.TWO15) (nxt Ccc.KD0)))) }
def transD1 : VmConstraint2 := .windowGate
  { onTransition := true
  , body := .add (nxt Ccc.D1) (.add (.mul (.const (-1)) (loc Ccc.D1))
      (.add (.mul (.const (-1)) (nxt Ccc.DC1))
        (.add (.mul (.const (-1)) (nxt Ccc.KD0)) (.mul (.const Ccc.TWO15) (nxt Ccc.KD1))))) }
def transD2 : VmConstraint2 := .windowGate
  { onTransition := true
  , body := .add (nxt Ccc.D2) (.add (.mul (.const (-1)) (loc Ccc.D2)) (.mul (.const (-1)) (nxt Ccc.KD1))) }

/-- The fixed (non-range) gates, in wire order. -/
def fixedGates : List VmConstraint2 :=
  [ boolPresent, signSquareGate, paddingSignGate
  , creditZ0, creditZ1, debitZ0, debitZ1, totalContribGate
  , assetPinFirst, assetPinLast
  , seedC0, seedC1, seedC2, seedD0, seedD1, seedD2
  , inertCC0, inertCC1, inertDC0, inertDC1, inertKC0, inertKC1, inertKD0, inertKD1
  , eqLast0, eqLast1, eqLast2
  , transC0, transC1, transC2, transD0, transD1, transD2 ]

/-! ## §4 — the descriptor. -/

def cccConstraints : List VmConstraint2 := fixedGates ++ rangeGates

def crossCellConservationDescriptor : EffectVmDescriptor2 :=
  { name        := "dregg-cross-cell-conservation-v2"
  , traceWidth  := WIDTH
  , piCount     := Ccc.PI_COUNT
  , tables      := []
  , constraints := cccConstraints
  , hashSites   := []
  , ranges      := [] }

/-! ## §5 — shape tripwires. -/

#guard Ccc.BIT_BASE == 18
#guard TOTAL_RANGE_BITS == 154
#guard WIDTH == 172
#guard crossCellConservationDescriptor.piCount == 1
#guard fixedGates.length == 33
#guard (fixedGates.filter (fun c => match c with | .windowGate _ => true | _ => false)).length == 6
#guard crossCellConservationDescriptor.tables.length == 0
#guard crossCellConservationDescriptor.ranges.length == 0

/-! ## §6 — the range-forcing induction (plain-gate variant of the vault's `rangeAux_forces`). -/

/-- Every spec'd column is forced into `[0, 2^n)` by its booleanity + assembly gates (mod-`p`
booleanity + `p` prime + canonicality ⟹ each bit `∈ {0,1}`; the `2^n < p` assembly lifts to ℤ). -/
theorem rangeAux_forces (loc : Nat → Int)
    (hcanon : ∀ c, 0 ≤ loc c ∧ loc c < 2013265921)
    (specs : List (Nat × Nat)) (base : Nat)
    (hwidth : ∀ col n, (col, n) ∈ specs → (2 : ℤ) ^ n < 2013265921)
    (hvan : ∀ body : EmittedExpr, gate body ∈ rangeGatesAux specs base →
      body.eval loc ≡ 0 [ZMOD 2013265921]) :
    ∀ col n : Nat, (col, n) ∈ specs → 0 ≤ loc col ∧ loc col < 2 ^ n := by
  induction specs generalizing base with
  | nil => intro col n h; cases h
  | cons hd rest ih =>
    obtain ⟨c0, n0⟩ := hd
    intro col n hmem
    rcases List.mem_cons.mp hmem with heq | htail
    · injection heq with h1 h2
      subst h1; subst h2
      have hbits : ∀ j, j < n → loc (base + j) = 0 ∨ loc (base + j) = 1 := by
        intro j hj
        have hb := hvan (.mul (.var (base + j)) (.add (.var (base + j)) (.const (-1))))
          (by
            simp only [rangeGatesAux]
            apply List.mem_append_left
            apply List.mem_append_left
            exact List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)
        simp only [EmittedExpr.eval] at hb
        rw [Int.modEq_zero_iff_dvd] at hb
        obtain ⟨hb0, hbp⟩ := hcanon (base + j)
        rcases (pPrimeInt.dvd_mul.mp hb) with hd | hd
        · left;  obtain ⟨k, hk⟩ := hd; omega
        · right; obtain ⟨k, hk⟩ := hd; omega
      have hasm := hvan (eSub (.var col) (bitSum (fun i => base + i) n))
        (by
          simp only [rangeGatesAux]
          apply List.mem_append_left
          apply List.mem_append_right
          exact List.mem_singleton.mpr rfl)
      simp only [eSub, eNeg, EmittedExpr.eval] at hasm
      have hb := bitSum_nonneg_lt loc (fun i => base + i) n hbits
      have hnp : (2 : ℤ) ^ n < 2013265921 := hwidth col n (List.mem_cons.mpr (Or.inl rfl))
      have hsumLt : (bitSum (fun i => base + i) n).eval loc < 2013265921 := by omega
      have hpin : loc col = (bitSum (fun i => base + i) n).eval loc :=
        canonEq ((gate_modEq_iff (by ring)).mp hasm) (hcanon col).1 (hcanon col).2 hb.1 hsumLt
      constructor <;> omega
    · exact ih (base + n0)
        (fun col' n' hmem' => hwidth col' n' (List.mem_cons_of_mem _ hmem'))
        (fun body hb => hvan body (by
          simp only [rangeGatesAux]
          exact List.mem_append_right _ hb))
        col n htail

/-! ## §7 — reconstructions + running sums (elementary, no Finset). -/

/-- Running credit reconstruction at row `i`. -/
def RC (t : VmTrace) (i : Nat) : ℤ :=
  (envAt t i).loc Ccc.C0 + 32768 * (envAt t i).loc Ccc.C1 + 1073741824 * (envAt t i).loc Ccc.C2
/-- Running debit reconstruction at row `i`. -/
def RD (t : VmTrace) (i : Nat) : ℤ :=
  (envAt t i).loc Ccc.D0 + 32768 * (envAt t i).loc Ccc.D1 + 1073741824 * (envAt t i).loc Ccc.D2
/-- Credit contribution at row `i`. -/
def ccv (t : VmTrace) (i : Nat) : ℤ :=
  (envAt t i).loc Ccc.CC0 + 32768 * (envAt t i).loc Ccc.CC1
/-- Debit contribution at row `i`. -/
def dcv (t : VmTrace) (i : Nat) : ℤ :=
  (envAt t i).loc Ccc.DC0 + 32768 * (envAt t i).loc Ccc.DC1
/-- Prefix credit sum over rows `[0, n)`. -/
def creditSum (t : VmTrace) : Nat → ℤ
  | 0 => 0
  | n + 1 => creditSum t n + ccv t n
/-- Prefix debit sum over rows `[0, n)`. -/
def debitSum (t : VmTrace) : Nat → ℤ
  | 0 => 0
  | n + 1 => debitSum t n + dcv t n

/-- `(envAt t i).nxt c` IS `(envAt t (i+1)).loc c` (both read row `i+1`). -/
theorem nxt_eq_loc (t : VmTrace) (i c : Nat) : (envAt t i).nxt c = (envAt t (i + 1)).loc c := rfl

/-! ## §8 — gate extraction from a satisfying trace. -/

section Soundness
variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
variable (hsat : Satisfied2 hash crossCellConservationDescriptor minit mfin maddrs t)

/-- A fixed gate is a descriptor constraint. -/
theorem fmem {g : VmConstraint2} (h : g ∈ fixedGates) :
    g ∈ crossCellConservationDescriptor.constraints := List.mem_append_left _ h

include hsat in
/-- A base `.gate` body vanishes mod `p` on a NON-LAST row. -/
theorem baseGateVanish (i : Nat) (hi : i < t.rows.length)
    (hnl : (i + 1 == t.rows.length) = false) (body : EmittedExpr)
    (hmem : gate body ∈ crossCellConservationDescriptor.constraints) :
    body.eval (envAt t i).loc ≡ 0 [ZMOD 2013265921] := by
  have hrow := hsat.rowConstraints i hi (gate body) hmem
  simp only [gate, VmConstraint2.holdsAt, VmConstraint.holdsVm, hnl] at hrow
  exact hrow

include hsat in
/-- A `.windowGate` transition body vanishes mod `p` on a NON-LAST row. -/
theorem windowVanish (i : Nat) (hi : i < t.rows.length)
    (hnl : (i + 1 == t.rows.length) = false) (w : WindowConstraint) (hot : w.onTransition = true)
    (hmem : (VmConstraint2.windowGate w) ∈ crossCellConservationDescriptor.constraints) :
    w.body.eval (envAt t i) ≡ 0 [ZMOD 2013265921] := by
  have hrow := hsat.rowConstraints i hi (.windowGate w) hmem
  simp only [VmConstraint2.holdsAt, WindowConstraint.holdsAt, hot, if_true] at hrow
  exact hrow hnl

include hsat in
/-- A `.boundary .first` body vanishes mod `p` on the FIRST row. -/
theorem bFirstVanish (hlen : 0 < t.rows.length) (body : EmittedExpr)
    (hmem : (VmConstraint2.base (.boundary .first body)) ∈ crossCellConservationDescriptor.constraints) :
    body.eval (envAt t 0).loc ≡ 0 [ZMOD 2013265921] := by
  have hrow := hsat.rowConstraints 0 hlen (.base (.boundary .first body)) hmem
  simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm] at hrow
  exact hrow rfl

include hsat in
/-- A `.boundary .last` body vanishes mod `p` on the LAST row (`len - 1`). -/
theorem bLastVanish (hlen : 0 < t.rows.length) (body : EmittedExpr)
    (hmem : (VmConstraint2.base (.boundary .last body)) ∈ crossCellConservationDescriptor.constraints) :
    body.eval (envAt t (t.rows.length - 1)).loc ≡ 0 [ZMOD 2013265921] := by
  have hi : t.rows.length - 1 < t.rows.length := by omega
  have hrow := hsat.rowConstraints (t.rows.length - 1) hi (.base (.boundary .last body)) hmem
  simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm] at hrow
  have hlast : (t.rows.length - 1 + 1 == t.rows.length) = true := by
    have : t.rows.length - 1 + 1 = t.rows.length := by omega
    simp [this]
  exact hrow hlast

/-! ## §9 — per-row range facts. -/

include hsat in
/-- On a NON-LAST row, every range-checked column lies in `[0, 2^n)`. -/
theorem rowRanges (i : Nat) (hi : i < t.rows.length) (hnl : (i + 1 == t.rows.length) = false)
    (hcanon : ∀ c, 0 ≤ (envAt t i).loc c ∧ (envAt t i).loc c < 2013265921) :
    ∀ col n, (col, n) ∈ rangeSpecs → 0 ≤ (envAt t i).loc col ∧ (envAt t i).loc col < 2 ^ n := by
  apply rangeAux_forces (envAt t i).loc hcanon rangeSpecs Ccc.BIT_BASE
  · intro col n h
    simp only [rangeSpecs] at h
    fin_cases h <;> norm_num
  · intro body hb
    exact baseGateVanish hsat i hi hnl body
      (by show gate body ∈ cccConstraints; exact List.mem_append_right _ hb)

/-! ## §10 — the accumulator recurrence (each limb transition is EXACT over ℤ). -/

include hsat in
/-- **The credit accumulator step.** On a doubly-non-last window the running credit reconstruction
advances by exactly the next row's credit contribution — the three 15-bit limb transitions lift to
an EXACT-ℤ recurrence (no wrap), and the carries telescope. -/
theorem credit_step (hcanon : ∀ j c, 0 ≤ (envAt t j).loc c ∧ (envAt t j).loc c < 2013265921)
    (i : Nat) (hi2 : i + 2 < t.rows.length) : RC t (i + 1) = RC t i + ccv t (i + 1) := by
  have hnl_i : (i + 1 == t.rows.length) = false := beq_eq_false_iff_ne.2 (by omega)
  have hnl_i1 : (i + 1 + 1 == t.rows.length) = false := beq_eq_false_iff_ne.2 (by omega)
  have hRi := rowRanges hsat i (by omega) hnl_i (hcanon i)
  have hRi1 := rowRanges hsat (i + 1) (by omega) hnl_i1 (hcanon (i + 1))
  have bC0i := hRi Ccc.C0 15 (by decide)
  have bC1i := hRi Ccc.C1 15 (by decide)
  have bC2i := hRi Ccc.C2 15 (by decide)
  have bC0 := hRi1 Ccc.C0 15 (by decide)
  have bC1 := hRi1 Ccc.C1 15 (by decide)
  have bC2 := hRi1 Ccc.C2 15 (by decide)
  have bCC0 := hRi1 Ccc.CC0 15 (by decide)
  have bCC1 := hRi1 Ccc.CC1 15 (by decide)
  have bKC0 := hRi1 Ccc.KC0 1 (by decide)
  have bKC1 := hRi1 Ccc.KC1 1 (by decide)
  norm_num at bC0i bC1i bC2i bC0 bC1 bC2 bCC0 bCC1 bKC0 bKC1
  have q0 := windowVanish hsat i (by omega) hnl_i _ rfl
    (fmem (show transC0 ∈ fixedGates by simp [fixedGates]))
  have q1 := windowVanish hsat i (by omega) hnl_i _ rfl
    (fmem (show transC1 ∈ fixedGates by simp [fixedGates]))
  have q2 := windowVanish hsat i (by omega) hnl_i _ rfl
    (fmem (show transC2 ∈ fixedGates by simp [fixedGates]))
  simp only [WindowExpr.eval, nxt_eq_loc, Ccc.TWO15] at q0 q1 q2
  have e0 := modEqZeroBounded q0 (by omega) (by omega)
  have e1 := modEqZeroBounded q1 (by omega) (by omega)
  have e2 := modEqZeroBounded q2 (by omega) (by omega)
  simp only [RC, ccv]
  omega

include hsat in
/-- **The debit accumulator step** (the debit twin of `credit_step`). -/
theorem debit_step (hcanon : ∀ j c, 0 ≤ (envAt t j).loc c ∧ (envAt t j).loc c < 2013265921)
    (i : Nat) (hi2 : i + 2 < t.rows.length) : RD t (i + 1) = RD t i + dcv t (i + 1) := by
  have hnl_i : (i + 1 == t.rows.length) = false := beq_eq_false_iff_ne.2 (by omega)
  have hnl_i1 : (i + 1 + 1 == t.rows.length) = false := beq_eq_false_iff_ne.2 (by omega)
  have hRi := rowRanges hsat i (by omega) hnl_i (hcanon i)
  have hRi1 := rowRanges hsat (i + 1) (by omega) hnl_i1 (hcanon (i + 1))
  have bD0i := hRi Ccc.D0 15 (by decide)
  have bD1i := hRi Ccc.D1 15 (by decide)
  have bD2i := hRi Ccc.D2 15 (by decide)
  have bD0 := hRi1 Ccc.D0 15 (by decide)
  have bD1 := hRi1 Ccc.D1 15 (by decide)
  have bD2 := hRi1 Ccc.D2 15 (by decide)
  have bDC0 := hRi1 Ccc.DC0 15 (by decide)
  have bDC1 := hRi1 Ccc.DC1 15 (by decide)
  have bKD0 := hRi1 Ccc.KD0 1 (by decide)
  have bKD1 := hRi1 Ccc.KD1 1 (by decide)
  norm_num at bD0i bD1i bD2i bD0 bD1 bD2 bDC0 bDC1 bKD0 bKD1
  have q0 := windowVanish hsat i (by omega) hnl_i _ rfl
    (fmem (show transD0 ∈ fixedGates by simp [fixedGates]))
  have q1 := windowVanish hsat i (by omega) hnl_i _ rfl
    (fmem (show transD1 ∈ fixedGates by simp [fixedGates]))
  have q2 := windowVanish hsat i (by omega) hnl_i _ rfl
    (fmem (show transD2 ∈ fixedGates by simp [fixedGates]))
  simp only [WindowExpr.eval, nxt_eq_loc, Ccc.TWO15] at q0 q1 q2
  have e0 := modEqZeroBounded q0 (by omega) (by omega)
  have e1 := modEqZeroBounded q1 (by omega) (by omega)
  have e2 := modEqZeroBounded q2 (by omega) (by omega)
  simp only [RD, dcv]
  omega

/-! ## §11 — the seed (first row). -/

include hsat in
/-- The credit accumulator seeds to the first row's credit contribution. -/
theorem seed_credit (hcanon : ∀ j c, 0 ≤ (envAt t j).loc c ∧ (envAt t j).loc c < 2013265921)
    (hlen : 2 ≤ t.rows.length) : RC t 0 = ccv t 0 := by
  have hnl0 : (0 + 1 == t.rows.length) = false := beq_eq_false_iff_ne.2 (by omega)
  have hR := rowRanges hsat 0 (by omega) hnl0 (hcanon 0)
  have bC0 := hR Ccc.C0 15 (by decide)
  have bC1 := hR Ccc.C1 15 (by decide)
  have bC2 := hR Ccc.C2 15 (by decide)
  have bCC0 := hR Ccc.CC0 15 (by decide)
  have bCC1 := hR Ccc.CC1 15 (by decide)
  norm_num at bC0 bC1 bC2 bCC0 bCC1
  have h0raw := hsat.rowConstraints 0 (by omega) seedC0 (fmem (by simp [fixedGates]))
  have h1raw := hsat.rowConstraints 0 (by omega) seedC1 (fmem (by simp [fixedGates]))
  have h2raw := hsat.rowConstraints 0 (by omega) seedC2 (fmem (by simp [fixedGates]))
  simp only [seedC0, seedC1, seedC2, VmConstraint2.holdsAt, VmConstraint.holdsVm] at h0raw h1raw h2raw
  have h0 := h0raw rfl
  have h1 := h1raw rfl
  have h2 := h2raw rfl
  simp only [eSub, eNeg, EmittedExpr.eval] at h0 h1 h2
  have e0 := modEqZeroBounded h0 (by omega) (by omega)
  have e1 := modEqZeroBounded h1 (by omega) (by omega)
  have e2 := modEqZeroBounded h2 (by omega) (by omega)
  simp only [RC, ccv]
  omega

include hsat in
/-- The debit accumulator seeds to the first row's debit contribution. -/
theorem seed_debit (hcanon : ∀ j c, 0 ≤ (envAt t j).loc c ∧ (envAt t j).loc c < 2013265921)
    (hlen : 2 ≤ t.rows.length) : RD t 0 = dcv t 0 := by
  have hnl0 : (0 + 1 == t.rows.length) = false := beq_eq_false_iff_ne.2 (by omega)
  have hR := rowRanges hsat 0 (by omega) hnl0 (hcanon 0)
  have bD0 := hR Ccc.D0 15 (by decide)
  have bD1 := hR Ccc.D1 15 (by decide)
  have bD2 := hR Ccc.D2 15 (by decide)
  have bDC0 := hR Ccc.DC0 15 (by decide)
  have bDC1 := hR Ccc.DC1 15 (by decide)
  norm_num at bD0 bD1 bD2 bDC0 bDC1
  have h0raw := hsat.rowConstraints 0 (by omega) seedD0 (fmem (by simp [fixedGates]))
  have h1raw := hsat.rowConstraints 0 (by omega) seedD1 (fmem (by simp [fixedGates]))
  have h2raw := hsat.rowConstraints 0 (by omega) seedD2 (fmem (by simp [fixedGates]))
  simp only [seedD0, seedD1, seedD2, VmConstraint2.holdsAt, VmConstraint.holdsVm] at h0raw h1raw h2raw
  have h0 := h0raw rfl
  have h1 := h1raw rfl
  have h2 := h2raw rfl
  simp only [eSub, eNeg, EmittedExpr.eval] at h0 h1 h2
  have e0 := modEqZeroBounded h0 (by omega) (by omega)
  have e1 := modEqZeroBounded h1 (by omega) (by omega)
  have e2 := modEqZeroBounded h2 (by omega) (by omega)
  simp only [RD, dcv]
  omega

/-! ## §12 — the running-sum invariant (row induction over the EXACT recurrence). -/

include hsat in
/-- **The credit accumulator reconstructs the TRUE integer prefix sum of credit contributions.** -/
theorem ccc_reconC_eq_creditSum (hcanon : ∀ j c, 0 ≤ (envAt t j).loc c ∧ (envAt t j).loc c < 2013265921) :
    ∀ i, i + 1 < t.rows.length → RC t i = creditSum t (i + 1) := by
  intro i
  induction i with
  | zero =>
    intro _
    rw [seed_credit hsat hcanon (by omega)]
    simp [creditSum]
  | succ k ih =>
    intro h
    have hk := ih (by omega)
    have hstep := credit_step hsat hcanon k (by omega)
    rw [hstep, hk]
    simp only [creditSum]

include hsat in
/-- **The debit accumulator reconstructs the TRUE integer prefix sum of debit contributions.** -/
theorem ccc_reconD_eq_debitSum (hcanon : ∀ j c, 0 ≤ (envAt t j).loc c ∧ (envAt t j).loc c < 2013265921) :
    ∀ i, i + 1 < t.rows.length → RD t i = debitSum t (i + 1) := by
  intro i
  induction i with
  | zero =>
    intro _
    rw [seed_debit hsat hcanon (by omega)]
    simp [debitSum]
  | succ k ih =>
    intro h
    have hk := ih (by omega)
    have hstep := debit_step hsat hcanon k (by omega)
    rw [hstep, hk]
    simp only [debitSum]

/-! ## §13 — CONSERVATION: `Σ credits = Σ debits` over ℤ (DERIVED, not assumed). -/

include hsat in
/-- **THE CONSERVATION TOOTH.** For a satisfying trace, the final credit prefix sum EQUALS the final
debit prefix sum over ℤ — the realized `Σδ = 0`. The final accumulators reconstruct the TRUE integer
sums (§12); the inert wrap row carries them forward mod `p`; the `.last` equality boundary pins the
final limbs equal; and each accumulator limb at row `len−2` is range-checked canonical, so the mod-`p`
equality lifts to ℤ per limb. NO wrap: the `p`-sum forgery cannot masquerade as `0`. -/
theorem ccc_conserves (hcanon : ∀ j c, 0 ≤ (envAt t j).loc c ∧ (envAt t j).loc c < 2013265921)
    (hlen : 2 ≤ t.rows.length) :
    creditSum t (t.rows.length - 1) = debitSum t (t.rows.length - 1) := by
  have hlast1 : t.rows.length - 1 + 1 = t.rows.length := by omega
  have hm2 : t.rows.length - 2 + 1 = t.rows.length - 1 := by omega
  have hnlm : (t.rows.length - 2 + 1 == t.rows.length) = false := beq_eq_false_iff_ne.2 (by omega)
  -- the two reconstructions equal their prefix sums.
  have hcredit : RC t (t.rows.length - 2) = creditSum t (t.rows.length - 1) := by
    have := ccc_reconC_eq_creditSum hsat hcanon (t.rows.length - 2) (by omega)
    rwa [hm2] at this
  have hdebit : RD t (t.rows.length - 2) = debitSum t (t.rows.length - 1) := by
    have := ccc_reconD_eq_debitSum hsat hcanon (t.rows.length - 2) (by omega)
    rwa [hm2] at this
  -- range facts at row len-2.
  have hRm := rowRanges hsat (t.rows.length - 2) (by omega) hnlm (hcanon _)
  have rC0 := hRm Ccc.C0 15 (by decide); have rC1 := hRm Ccc.C1 15 (by decide)
  have rC2 := hRm Ccc.C2 15 (by decide); have rD0 := hRm Ccc.D0 15 (by decide)
  have rD1 := hRm Ccc.D1 15 (by decide); have rD2 := hRm Ccc.D2 15 (by decide)
  norm_num at rC0 rC1 rC2 rD0 rD1 rD2
  -- inert wrap-row congruences (row len-1).
  have inertPin : ∀ col, (VmConstraint2.base (.boundary .last (.var col))) ∈ fixedGates →
      (envAt t (t.rows.length - 1)).loc col ≡ 0 [ZMOD 2013265921] := by
    intro col hmem
    have h := hsat.rowConstraints (t.rows.length - 1) (by omega) _ (fmem hmem)
    simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm, EmittedExpr.eval] at h
    exact h (by simp [hlast1])
  have iCC0 := inertPin Ccc.CC0 (by simp [fixedGates, inertCC0])
  have iCC1 := inertPin Ccc.CC1 (by simp [fixedGates, inertCC1])
  have iKC0 := inertPin Ccc.KC0 (by simp [fixedGates, inertKC0])
  have iKC1 := inertPin Ccc.KC1 (by simp [fixedGates, inertKC1])
  have iDC0 := inertPin Ccc.DC0 (by simp [fixedGates, inertDC0])
  have iDC1 := inertPin Ccc.DC1 (by simp [fixedGates, inertDC1])
  have iKD0 := inertPin Ccc.KD0 (by simp [fixedGates, inertKD0])
  have iKD1 := inertPin Ccc.KD1 (by simp [fixedGates, inertKD1])
  -- equality boundary congruences (row len-1).
  have eqPin : ∀ cc dd, (VmConstraint2.base (.boundary .last (eSub (.var cc) (.var dd)))) ∈ fixedGates →
      (envAt t (t.rows.length - 1)).loc cc ≡ (envAt t (t.rows.length - 1)).loc dd [ZMOD 2013265921] := by
    intro cc dd hmem
    have h := hsat.rowConstraints (t.rows.length - 1) (by omega) _ (fmem hmem)
    simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm, eSub, eNeg, EmittedExpr.eval] at h
    exact (gate_modEq_iff (by ring)).mp (h (by simp [hlast1]))
  have e0 := eqPin Ccc.C0 Ccc.D0 (by simp [fixedGates, eqLast0])
  have e1 := eqPin Ccc.C1 Ccc.D1 (by simp [fixedGates, eqLast1])
  have e2 := eqPin Ccc.C2 Ccc.D2 (by simp [fixedGates, eqLast2])
  -- inert transitions at row len-2 (mod-p; carries forward).
  have qc0 := windowVanish hsat _ (by omega) hnlm _ rfl (fmem (show transC0 ∈ fixedGates by simp [fixedGates]))
  have qc1 := windowVanish hsat _ (by omega) hnlm _ rfl (fmem (show transC1 ∈ fixedGates by simp [fixedGates]))
  have qc2 := windowVanish hsat _ (by omega) hnlm _ rfl (fmem (show transC2 ∈ fixedGates by simp [fixedGates]))
  have qd0 := windowVanish hsat _ (by omega) hnlm _ rfl (fmem (show transD0 ∈ fixedGates by simp [fixedGates]))
  have qd1 := windowVanish hsat _ (by omega) hnlm _ rfl (fmem (show transD1 ∈ fixedGates by simp [fixedGates]))
  have qd2 := windowVanish hsat _ (by omega) hnlm _ rfl (fmem (show transD2 ∈ fixedGates by simp [fixedGates]))
  simp only [WindowExpr.eval, nxt_eq_loc, Ccc.TWO15, hm2] at qc0 qc1 qc2 qd0 qd1 qd2
  -- carry-forward corrections vanish (inert wrap row).
  have corrC1 : (envAt t (t.rows.length-1)).loc Ccc.CC1 + (envAt t (t.rows.length-1)).loc Ccc.KC0
      - 32768 * (envAt t (t.rows.length-1)).loc Ccc.KC1 ≡ 0 [ZMOD 2013265921] := by
    simpa using Int.ModEq.sub (Int.ModEq.add iCC1 iKC0) (Int.ModEq.mul_left 32768 iKC1)
  have corrC0 : (envAt t (t.rows.length-1)).loc Ccc.CC0
      - 32768 * (envAt t (t.rows.length-1)).loc Ccc.KC0 ≡ 0 [ZMOD 2013265921] := by
    simpa using Int.ModEq.sub iCC0 (Int.ModEq.mul_left 32768 iKC0)
  have corrD1 : (envAt t (t.rows.length-1)).loc Ccc.DC1 + (envAt t (t.rows.length-1)).loc Ccc.KD0
      - 32768 * (envAt t (t.rows.length-1)).loc Ccc.KD1 ≡ 0 [ZMOD 2013265921] := by
    simpa using Int.ModEq.sub (Int.ModEq.add iDC1 iKD0) (Int.ModEq.mul_left 32768 iKD1)
  have corrD0 : (envAt t (t.rows.length-1)).loc Ccc.DC0
      - 32768 * (envAt t (t.rows.length-1)).loc Ccc.KD0 ≡ 0 [ZMOD 2013265921] := by
    simpa using Int.ModEq.sub iDC0 (Int.ModEq.mul_left 32768 iKD0)
  -- accumulator limbs carry forward: C_k[len-1] ≡ C_k[len-2], D_k likewise.
  have cC0 : (envAt t (t.rows.length-1)).loc Ccc.C0 ≡ (envAt t (t.rows.length-2)).loc Ccc.C0 [ZMOD 2013265921] :=
    carryFwd qc0 (by ring) corrC0
  have cC1 : (envAt t (t.rows.length-1)).loc Ccc.C1 ≡ (envAt t (t.rows.length-2)).loc Ccc.C1 [ZMOD 2013265921] :=
    carryFwd qc1 (by ring) corrC1
  have cC2 : (envAt t (t.rows.length-1)).loc Ccc.C2 ≡ (envAt t (t.rows.length-2)).loc Ccc.C2 [ZMOD 2013265921] :=
    carryFwd qc2 (by ring) iKC1
  have cD0 : (envAt t (t.rows.length-1)).loc Ccc.D0 ≡ (envAt t (t.rows.length-2)).loc Ccc.D0 [ZMOD 2013265921] :=
    carryFwd qd0 (by ring) corrD0
  have cD1 : (envAt t (t.rows.length-1)).loc Ccc.D1 ≡ (envAt t (t.rows.length-2)).loc Ccc.D1 [ZMOD 2013265921] :=
    carryFwd qd1 (by ring) corrD1
  have cD2 : (envAt t (t.rows.length-1)).loc Ccc.D2 ≡ (envAt t (t.rows.length-2)).loc Ccc.D2 [ZMOD 2013265921] :=
    carryFwd qd2 (by ring) iKD1
  -- per-limb: C_k[len-2] ≡ D_k[len-2], lifted to ℤ by row len-2 canonicality (each limb < 2^15).
  have hC0 : (envAt t (t.rows.length-2)).loc Ccc.C0 = (envAt t (t.rows.length-2)).loc Ccc.D0 := by
    refine canonEq (cC0.symm.trans (e0.trans cD0)) rC0.1 ?_ rD0.1 ?_ <;> omega
  have hC1 : (envAt t (t.rows.length-2)).loc Ccc.C1 = (envAt t (t.rows.length-2)).loc Ccc.D1 := by
    refine canonEq (cC1.symm.trans (e1.trans cD1)) rC1.1 ?_ rD1.1 ?_ <;> omega
  have hC2 : (envAt t (t.rows.length-2)).loc Ccc.C2 = (envAt t (t.rows.length-2)).loc Ccc.D2 := by
    refine canonEq (cC2.symm.trans (e2.trans cD2)) rC2.1 ?_ rD2.1 ?_ <;> omega
  -- assemble the reconstructions.
  have hRCeq : RC t (t.rows.length - 2) = RD t (t.rows.length - 2) := by
    simp only [RC, RD]; rw [hC0, hC1, hC2]
  rw [← hcredit, ← hdebit, hRCeq]

/-! ## §14 — THE FORGED-`p`-SUM TOOTH (the wrap the single-felt sum admitted is now UNSAT). -/

include hsat in
/-- **`ccc_psum_forgery_unsat`.** The concrete forgery the brief names — two credit rows
`mag₁ = 1006632961`, `mag₂ = 1006632960` (both `< 2^30`) whose true integer sum is exactly
`p = 2013265921`, with NO debit — CANNOT satisfy the descriptor. Under the single-felt design the
boundary `balance ≡ 0 [ZMOD p]` accepted it (`p ≡ 0`); here the derived integer credit sum is `p`,
and conservation forces it to equal the debit sum `0`, but `p ≠ 0`. -/
theorem ccc_psum_forgery_unsat
    (hcanon : ∀ j c, 0 ≤ (envAt t j).loc c ∧ (envAt t j).loc c < 2013265921)
    (hlen : 2 ≤ t.rows.length)
    (hforge : creditSum t (t.rows.length - 1) = 1006632961 + 1006632960)
    (hnodebit : debitSum t (t.rows.length - 1) = 0) : False := by
  have hcons := ccc_conserves hsat hcanon hlen
  rw [hforge, hnodebit] at hcons
  norm_num at hcons

end Soundness

/-! ## §15 — non-vacuity: the arithmetic the teeth turn on (honest balanced vs the `p`-sum forgery). -/

-- HONEST: a matched transfer `A −10, B +10` conserves; the forged `A −10, B +999` (no mint) does not.
#guard (10 : Int) + 0 == 0 + 10          -- balanced (credit 10 = debit 10)
#guard ¬ ((999 : Int) == 10)             -- forged: credit 999 ≠ debit 10
-- THE p-SUM: the two 30-bit credit magnitudes sum to EXACTLY p, which is NONZERO (the wrap the fix kills).
#guard (1006632961 : Int) + 1006632960 == 2013265921
#guard ¬ ((2013265921 : Int) == 0)
#guard (1006632961 : Int) < 1073741824 ∧ (1006632960 : Int) < 1073741824   -- both < 2^30

#assert_axioms ccc_reconC_eq_creditSum
#assert_axioms ccc_reconD_eq_debitSum
#assert_axioms ccc_conserves
#assert_axioms ccc_psum_forgery_unsat

end Dregg2.Circuit.CrossCellConservation

