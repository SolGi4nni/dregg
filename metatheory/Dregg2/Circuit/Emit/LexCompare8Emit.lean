/-
# Dregg2.Circuit.Emit.LexCompare8Emit — the lex-`<` AIR gadget over 8-felt `Digest8` keys
(felt-width #4/#10, the ONE genuinely-new circuit piece).

## What this is

The note-nullifier sorted-tree bracket `low.addr < k < low.nextAddr` must run over 8-felt
keys. `Dregg2/Crypto/Digest8KeySpike.lean` machine-confirmed the SOUNDNESS side transfers
free at `Digest8Key := Lex (Fin 8 → ℤ)` (instantiate `sorted_gap_excludes` / `imtAbsentK_excludes`
— zero new bracketing math). The remaining genuinely-new work was the IN-CIRCUIT comparison:
THIS file authors it, in Lean (house law #1 — Rust only decodes the emitted bytes; it never
hand-writes these constraints).

CONVENTION (matches the spike): felt 0 is the MOST-SIGNIFICANT limb; `a <_lex b` iff at the
first index where they differ, `a i < b i`, with all earlier (more-significant) limbs equal.

## The construction (BabyBear has no native order — the field wraps)

A bare field inequality is meaningless mod `p`; worse, comparing two FULL felts by
range-checking their difference is UNSOUND for every lookup width (the difference ranges over
all residues). The sound construction decomposes the compared limbs:

  * a one-hot selector block `s[0..8)` picks the DECIDING limb `j` (booleanity + Σs = 1 —
    equality of the whole key has NO deciding limb, so `a = b` is rejected structurally);
  * prefix gates `(1 − Σ_{i≤k} s_i)·(a_k − b_k) = 0` force every limb ABOVE the decider equal;
  * the SELECTED limbs `Σ s_i·a_i`, `Σ s_i·b_i` are split `x = 2^27·hi + lo` with
    `hi ∈ [0,16)` from four boolean bit columns and `lo ∈ [0,2^27)` by range LOOKUP
    (`DescriptorIR2` §8 `rangeRows` — the same range-by-lookup mechanism that replaced the
    v1 range-bit columns, `lookup_replaces_range` at DescriptorIR2:1374);
  * **the `p`-boundary exclusion** (load-bearing, since `p = 15·2^27 + 1`): `hi = 15 ⟹ lo = 0`,
    realized degree-3 as `P·Q·lo = 0` with pair columns `P = h0·h1`, `Q = h2·h3`. WITHOUT it the
    split is ambiguous mod `p` (any `x < 2^27 − 1` also decomposes as `(15, x+1)`) and an
    adversary could order-swap small keys — the canary teeth below pin this;
  * the two sub-limbs compare lexicographically via one branch bit `t` and ONE 27-bit range
    lookup on the witnessed difference `delta` (`t=1`: `hi_a < hi_b`; `t=0`: `hi` equal and
    `lo_a < lo_b`) — differences of 27-bit/4-bit-bounded values cannot wrap (`2^28 < p`).

## What is proved (field-faithful, mirroring `BilateralAggregationEmit.cg3_body_modEq_zero_iff`)

`lexLt8_refines`: for canonical keys (`0 ≤ cell < p`, the deployed range-check envelope), the
constraint block is satisfiable with those key cells IFF `toLex a < toLex b` at
`Lex (Fin 8 → ℤ)` — the spike's `Digest8Key` order, literally (the spike's `Digest8Key` is an
abbrev for this type; its olean is not in the current build tree so the type is named
structurally here). Soundness (`lexLt8_sound`) holds for ANY trace family whose range table is
faithful; completeness (`lexLt8_complete`) exhibits the witness. Teeth: a concrete witness
computing through every gate with the decider at limb 5 (NOT lane 0, with a full-felt `p−1`
limb in the equal prefix and the `hi=15/lo=0` boundary exercised on the b-side), rejection of
equal keys and of the reversed pair (via soundness — rejects EVERY witness, not one), and a
limb-7-only accept.

Follow-ups (out of scope here): leaf-schema widening (addr/nextAddr 1 felt → 8 felts) and the
sorted-tree membership AIR wiring that instantiates this block per bracket compare.

Heap safety: `rangeRows 27` (a `2^27`-row table) is NEVER evaluated — every membership fact
goes through `range_row_mem_iff`; no `native_decide`; `decide` only on literal-int gate values.
-/
import Dregg2.Circuit.DescriptorIR2
import Dregg2.Circuit.Emit.EffectVmEmitTransfer
import Mathlib.Order.PiLex

namespace Dregg2.Circuit.Emit.LexCompare8Emit

open Dregg2.Circuit (Assignment)
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRowEnv)
open Dregg2.Circuit.Emit.EffectVmEmitTransfer (eSub pPrimeInt eqToModEq)
open Dregg2.Exec.CircuitEmit (EmittedExpr)

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-! ## §0 — Column layout (row-local; a single gadget row).

```
 0..7   a[0..8)      the left key (limb 0 most significant)
 8..15  b[0..8)      the right key
16..23  s[0..8)      one-hot deciding-limb selectors
24..27  aH0..aH3     bit decomposition of hi(a_j)   (aHi = aH0 + 2·aH1 + 4·aH2 + 8·aH3)
28      aP = aH0·aH1     29  aQ = aH2·aH3          (pair columns for the degree-3 boundary gate)
30      aLo ∈ [0, 2^27)  (range lookup)
31..34  bH0..bH3     35  bP   36  bQ   37  bLo
38      t            branch bit: 1 ⇒ hi decides, 0 ⇒ hi equal ∧ lo decides
39      delta ∈ [0, 2^27)  the witnessed strict difference minus one
```
-/

/-- Trace width of the gadget block. -/
def LEX_WIDTH : Nat := 40

/-- The dedicated 27-bit range table id (`.custom 27`, wire id 32). A CUSTOM id — the shared
`TableId.range` is the 30-bit `BAL_LIMB_BITS` table, and this gadget's soundness needs the
EXACT 27-bit bound (`2^28 < p` is what makes the lo-difference wrap-free). Content contract:
`tf (.custom LEX_RANGE_TID) = rangeRows 27`. -/
def LEX_RANGE_TID : Nat := 27

/-- `2^27`, the lo-limb bound (`p = 15·2^27 + 1`). -/
def LO_BOUND : ℤ := 134217728

/-! ## §1 — Gate bodies. -/

/-- `1 − e` as an `EmittedExpr`. -/
def eOneMinus (e : EmittedExpr) : EmittedExpr := .add (.const 1) (.mul (.const (-1)) e)

/-- Booleanity body `x·(x − 1)` for column `c`. -/
def gBool (c : Nat) : EmittedExpr := .mul (.var c) (.add (.var c) (.const (-1)))

/-- The selector sum `s0 + … + s7`. -/
def eS : EmittedExpr :=
  .add (.add (.add (.add (.add (.add (.add (.var 16) (.var 17)) (.var 18)) (.var 19))
    (.var 20)) (.var 21)) (.var 22)) (.var 23)

/-- One-hot body `Σs − 1`. -/
def gOneHot : EmittedExpr := .add eS (.const (-1))

/-- Prefix selector partial sums `s0 + … + s_k`. -/
def ePre0 : EmittedExpr := .var 16
def ePre1 : EmittedExpr := .add ePre0 (.var 17)
def ePre2 : EmittedExpr := .add ePre1 (.var 18)
def ePre3 : EmittedExpr := .add ePre2 (.var 19)
def ePre4 : EmittedExpr := .add ePre3 (.var 20)
def ePre5 : EmittedExpr := .add ePre4 (.var 21)
def ePre6 : EmittedExpr := .add ePre5 (.var 22)

/-- Prefix-equality body for limb `k`: `(1 − Σ_{i≤k} s_i)·(a_k − b_k)`. Above the deciding
limb the partial sum is 0 and the limbs are forced equal; at and below it the factor
vanishes. (Limb 7 needs no gate: its partial sum is the full one-hot sum 1.) -/
def gPre0 : EmittedExpr := .mul (eOneMinus ePre0) (eSub (.var 0) (.var 8))
def gPre1 : EmittedExpr := .mul (eOneMinus ePre1) (eSub (.var 1) (.var 9))
def gPre2 : EmittedExpr := .mul (eOneMinus ePre2) (eSub (.var 2) (.var 10))
def gPre3 : EmittedExpr := .mul (eOneMinus ePre3) (eSub (.var 3) (.var 11))
def gPre4 : EmittedExpr := .mul (eOneMinus ePre4) (eSub (.var 4) (.var 12))
def gPre5 : EmittedExpr := .mul (eOneMinus ePre5) (eSub (.var 5) (.var 13))
def gPre6 : EmittedExpr := .mul (eOneMinus ePre6) (eSub (.var 6) (.var 14))

/-- The selected limbs `Σ s_i·a_i`, `Σ s_i·b_i`. -/
def eSelA : EmittedExpr :=
  .add (.add (.add (.add (.add (.add (.add (.mul (.var 16) (.var 0)) (.mul (.var 17) (.var 1)))
    (.mul (.var 18) (.var 2))) (.mul (.var 19) (.var 3))) (.mul (.var 20) (.var 4)))
    (.mul (.var 21) (.var 5))) (.mul (.var 22) (.var 6))) (.mul (.var 23) (.var 7))
def eSelB : EmittedExpr :=
  .add (.add (.add (.add (.add (.add (.add (.mul (.var 16) (.var 8)) (.mul (.var 17) (.var 9)))
    (.mul (.var 18) (.var 10))) (.mul (.var 19) (.var 11))) (.mul (.var 20) (.var 12)))
    (.mul (.var 21) (.var 13))) (.mul (.var 22) (.var 14))) (.mul (.var 23) (.var 15))

/-- `hi` as the bit combination `h0 + 2·h1 + 4·h2 + 8·h3`. -/
def eHiA : EmittedExpr :=
  .add (.var 24) (.add (.mul (.const 2) (.var 25))
    (.add (.mul (.const 4) (.var 26)) (.mul (.const 8) (.var 27))))
def eHiB : EmittedExpr :=
  .add (.var 31) (.add (.mul (.const 2) (.var 32))
    (.add (.mul (.const 4) (.var 33)) (.mul (.const 8) (.var 34))))

/-- Pair columns pinned to their bit products (keeps the boundary gate at degree 3). -/
def gPairAP : EmittedExpr := eSub (.var 28) (.mul (.var 24) (.var 25))
def gPairAQ : EmittedExpr := eSub (.var 29) (.mul (.var 26) (.var 27))
def gPairBP : EmittedExpr := eSub (.var 35) (.mul (.var 31) (.var 32))
def gPairBQ : EmittedExpr := eSub (.var 36) (.mul (.var 33) (.var 34))

/-- **The `p`-boundary exclusion** `P·Q·lo = 0`: all four hi-bits set (`hi = 15`) forces
`lo = 0`, so the split value `2^27·hi + lo` stays `≤ p − 1` and the decomposition of a
canonical felt is UNIQUE mod `p`. Without this gate the gadget is forgeable (see the
`boundary_gate_is_load_bearing` canary). -/
def gTopA : EmittedExpr := .mul (.mul (.var 28) (.var 29)) (.var 30)
def gTopB : EmittedExpr := .mul (.mul (.var 35) (.var 36)) (.var 37)

/-- Decomposition bodies: `Σ s_i·a_i − 2^27·hiA − aLo` (and the b twin). -/
def gDecompA : EmittedExpr := eSub eSelA (.add (.mul (.const 134217728) eHiA) (.var 30))
def gDecompB : EmittedExpr := eSub eSelB (.add (.mul (.const 134217728) eHiB) (.var 37))

/-- Branch-consistency body: `(1 − t)·(hiA − hiB)` — when the lo-limb decides, the hi-limbs
must be equal. -/
def gHiEq : EmittedExpr := .mul (eOneMinus (.var 38)) (eSub eHiA eHiB)

/-- The strict-difference body: `t·(hiB − hiA) + (1 − t)·(bLo − aLo) − 1 − delta`. With
`delta ∈ [0, 2^27)` by lookup, the deciding sub-limb of `a` is strictly below `b`'s. -/
def gDelta : EmittedExpr :=
  .add (.mul (.var 38) (eSub eHiB eHiA))
    (.add (.mul (eOneMinus (.var 38)) (eSub (.var 37) (.var 30)))
      (.add (.const (-1)) (.mul (.const (-1)) (.var 39))))

/-- The three 27-bit range lookups (`aLo`, `bLo`, `delta`). -/
def lkALo : Lookup := ⟨.custom LEX_RANGE_TID, [.var 30]⟩
def lkBLo : Lookup := ⟨.custom LEX_RANGE_TID, [.var 37]⟩
def lkDelta : Lookup := ⟨.custom LEX_RANGE_TID, [.var 39]⟩

/-- **The lex-`<` constraint block** — 35 gates + 3 range lookups, row-local. Holds (on a
transition row, against a faithful range table) IFF the key columns satisfy `a <_lex b`. -/
def lexLt8Constraints : List VmConstraint2 :=
  [ .base (.gate (gBool 16)), .base (.gate (gBool 17)), .base (.gate (gBool 18)),
    .base (.gate (gBool 19)), .base (.gate (gBool 20)), .base (.gate (gBool 21)),
    .base (.gate (gBool 22)), .base (.gate (gBool 23)),
    .base (.gate gOneHot),
    .base (.gate gPre0), .base (.gate gPre1), .base (.gate gPre2), .base (.gate gPre3),
    .base (.gate gPre4), .base (.gate gPre5), .base (.gate gPre6),
    .base (.gate (gBool 24)), .base (.gate (gBool 25)), .base (.gate (gBool 26)),
    .base (.gate (gBool 27)),
    .base (.gate (gBool 31)), .base (.gate (gBool 32)), .base (.gate (gBool 33)),
    .base (.gate (gBool 34)),
    .base (.gate gPairAP), .base (.gate gPairAQ), .base (.gate gPairBP), .base (.gate gPairBQ),
    .base (.gate gTopA), .base (.gate gTopB),
    .base (.gate gDecompA), .base (.gate gDecompB),
    .base (.gate (gBool 38)),
    .base (.gate gHiEq),
    .base (.gate gDelta),
    .lookup lkALo, .lookup lkBLo, .lookup lkDelta ]

/-- The gadget's dedicated 27-bit range table (`rangeRows 27` content contract). -/
def lexRangeTableDef : TableDef := ⟨.custom LEX_RANGE_TID, "lex_range_27", 1, .rangeLimb 27⟩

/-- The standalone descriptor packaging the block (PI-free: the key columns are wired by the
enclosing sorted-tree AIR; this is a pluggable sub-block). -/
def lexLt8Descriptor : EffectVmDescriptor2 :=
  { name        := "dregg-lex-lt8-digest8-v1"
  , traceWidth  := LEX_WIDTH
  , piCount     := 0
  , tables      := [lexRangeTableDef]
  , constraints := lexLt8Constraints
  , hashSites   := []
  , ranges      := [] }

/-! ## §2 — Denotation carriers. -/

/-- The block's denotation on a (transition) row: every constraint holds. The `hash`
parameter is irrelevant (no map ops); gates fire on non-last rows exactly as deployed. -/
def lexBlockHolds (tf : TraceFamily) (env : VmRowEnv) : Prop :=
  ∀ c ∈ lexLt8Constraints, c.holdsAt (fun _ => 0) tf env false false

/-- The two keys as `Fin 8 → ℤ` column reads (limb 0 most significant). -/
def lexKeyA (env : VmRowEnv) : Fin 8 → ℤ := fun i => env.loc i.val
def lexKeyB (env : VmRowEnv) : Fin 8 → ℤ := fun i => env.loc (8 + i.val)

/-- The deployed range-check canonicality envelope on the 16 KEY cells (`0 ≤ cell < p`) —
the same hypothesis discipline as `BilateralAggregationEmit.agg_rejects_count_mismatch`.
Witness cells need NO such hypothesis: their bounds come from the block's own lookups/gates. -/
def LexCanon (env : VmRowEnv) : Prop :=
  ∀ k : ℕ, k < 16 → 0 ≤ env.loc k ∧ env.loc k < 2013265921

/-- The canonical trace family for the standalone gadget: the 27-bit range table and
nothing else. -/
def lexTf : TraceFamily := fun tid => if tid = .custom LEX_RANGE_TID then rangeRows 27 else []

theorem lexTf_range : lexTf (.custom LEX_RANGE_TID) = rangeRows 27 := by
  simp [lexTf]

/-! ## §3 — ℤ/dvd toolkit (all field reasoning routed through `p ∣ ·` + `linear_combination`
+ `omega`, shape-blind). -/

/-- ModEq-to-dvd bridge (`Int.modEq_zero_iff_dvd`). -/
theorem dvd_of_modEq_zero {x : ℤ} (h : x ≡ 0 [ZMOD 2013265921]) : (2013265921:ℤ) ∣ x :=
  Int.modEq_zero_iff_dvd.mp h

/-- Reshape a divisibility fact along a ring identity. -/
theorem reshape {E T : ℤ} (h : (2013265921:ℤ) ∣ E) (heq : E = T) : (2013265921:ℤ) ∣ T :=
  heq ▸ h

/-- A boolean gate pins its cell to a genuine 0/1 residue (primality of `p`). -/
theorem bool01 {x : ℤ} (h : (2013265921:ℤ) ∣ x * (x - 1)) :
    ∃ c : ℤ, (c = 0 ∨ c = 1) ∧ (2013265921:ℤ) ∣ x - c := by
  rcases pPrimeInt.2.2 x (x - 1) h with hx | hx
  · exact ⟨0, Or.inl rfl, by simpa using hx⟩
  · exact ⟨1, Or.inr rfl, hx⟩

/-- Prefix-equality extraction: a gate `(1 − S)·(x − y) ≡ 0` with `S ≡ 0` and both cells
canonical forces genuine equality. -/
theorem prefix_eq {S x y : ℤ} (hS : (2013265921:ℤ) ∣ S)
    (hg : (2013265921:ℤ) ∣ (1 - S) * (x - y))
    (hx : 0 ≤ x) (hx' : x < 2013265921) (hy : 0 ≤ y) (hy' : y < 2013265921) : x = y := by
  obtain ⟨u, hu⟩ := hS
  obtain ⟨v, hv⟩ := hg
  have hd : (2013265921:ℤ) ∣ (x - y) :=
    ⟨v + u * (x - y), by linear_combination hv + (x - y) * hu⟩
  obtain ⟨w, hw⟩ := hd
  omega

/-- The one-hot select-sum pins `Σ s_i·a_i` to the deciding limb, given the 8 selector
residues and the (branch-literal) coefficient identity. -/
theorem select8_pin {s0 s1 s2 s3 s4 s5 s6 s7 a0 a1 a2 a3 a4 a5 a6 a7 : ℤ}
    {c0 c1 c2 c3 c4 c5 c6 c7 aj : ℤ}
    (h0 : (2013265921:ℤ) ∣ s0 - c0) (h1 : (2013265921:ℤ) ∣ s1 - c1)
    (h2 : (2013265921:ℤ) ∣ s2 - c2) (h3 : (2013265921:ℤ) ∣ s3 - c3)
    (h4 : (2013265921:ℤ) ∣ s4 - c4) (h5 : (2013265921:ℤ) ∣ s5 - c5)
    (h6 : (2013265921:ℤ) ∣ s6 - c6) (h7 : (2013265921:ℤ) ∣ s7 - c7)
    (hsum : c0*a0 + c1*a1 + c2*a2 + c3*a3 + c4*a4 + c5*a5 + c6*a6 + c7*a7 = aj) :
    (2013265921:ℤ) ∣ (s0*a0 + s1*a1 + s2*a2 + s3*a3 + s4*a4 + s5*a5 + s6*a6 + s7*a7) - aj := by
  obtain ⟨k0, hk0⟩ := h0; obtain ⟨k1, hk1⟩ := h1; obtain ⟨k2, hk2⟩ := h2
  obtain ⟨k3, hk3⟩ := h3; obtain ⟨k4, hk4⟩ := h4; obtain ⟨k5, hk5⟩ := h5
  obtain ⟨k6, hk6⟩ := h6; obtain ⟨k7, hk7⟩ := h7
  refine ⟨k0*a0 + k1*a1 + k2*a2 + k3*a3 + k4*a4 + k5*a5 + k6*a6 + k7*a7, ?_⟩
  linear_combination a0*hk0 + a1*hk1 + a2*hk2 + a3*hk3 + a4*hk4 + a5*hk5 + a6*hk6 + a7*hk7 + hsum

/-- Bit residues pin the hi combination. -/
theorem hi4_pin {h0 h1 h2 h3 d0 d1 d2 d3 : ℤ}
    (hb0 : (2013265921:ℤ) ∣ h0 - d0) (hb1 : (2013265921:ℤ) ∣ h1 - d1)
    (hb2 : (2013265921:ℤ) ∣ h2 - d2) (hb3 : (2013265921:ℤ) ∣ h3 - d3) :
    (2013265921:ℤ) ∣ (h0 + 2*h1 + 4*h2 + 8*h3) - (d0 + 2*d1 + 4*d2 + 8*d3) := by
  obtain ⟨k0, hk0⟩ := hb0; obtain ⟨k1, hk1⟩ := hb1
  obtain ⟨k2, hk2⟩ := hb2; obtain ⟨k3, hk3⟩ := hb3
  exact ⟨k0 + 2*k1 + 4*k2 + 8*k3, by linear_combination hk0 + 2*hk1 + 4*hk2 + 8*hk3⟩

/-- **The per-operand keystone**: a canonical felt whose selected decomposition satisfies the
bit/pair/boundary/decomposition gates and the `lo` lookup IS `2^27·hi + lo` with the RESIDUE
hi — the split is exact over ℤ, not merely mod `p`. The `p`-boundary gate (`htop`) is what
excludes the shifted second representation. -/
theorem operand_pinned {x h0 h1 h2 h3 pp qq lo : ℤ} {d0 d1 d2 d3 : ℤ}
    (hx : 0 ≤ x) (hx' : x < 2013265921)
    (hlo : 0 ≤ lo) (hlo' : lo < 134217728)
    (hd0 : d0 = 0 ∨ d0 = 1) (hd1 : d1 = 0 ∨ d1 = 1)
    (hd2 : d2 = 0 ∨ d2 = 1) (hd3 : d3 = 0 ∨ d3 = 1)
    (hb0 : (2013265921:ℤ) ∣ h0 - d0) (hb1 : (2013265921:ℤ) ∣ h1 - d1)
    (hb2 : (2013265921:ℤ) ∣ h2 - d2) (hb3 : (2013265921:ℤ) ∣ h3 - d3)
    (hP : (2013265921:ℤ) ∣ pp - h0*h1) (hQ : (2013265921:ℤ) ∣ qq - h2*h3)
    (htop : (2013265921:ℤ) ∣ pp*qq*lo)
    (hdec : (2013265921:ℤ) ∣ (134217728*(h0 + 2*h1 + 4*h2 + 8*h3) + lo - x)) :
    x = 134217728*(d0 + 2*d1 + 4*d2 + 8*d3) + lo := by
  -- move the decomposition onto the genuine 0/1 residues
  have hdecD : (2013265921:ℤ) ∣ (134217728*(d0 + 2*d1 + 4*d2 + 8*d3) + lo - x) := by
    obtain ⟨u, hu⟩ := hdec
    obtain ⟨v, hv⟩ := hi4_pin hb0 hb1 hb2 hb3
    exact ⟨u - 134217728*v, by linear_combination hu - 134217728*hv⟩
  -- pair columns carry the residue products
  have hPd : (2013265921:ℤ) ∣ pp - d0*d1 := by
    obtain ⟨u, hu⟩ := hP; obtain ⟨v0, hv0⟩ := hb0; obtain ⟨v1, hv1⟩ := hb1
    exact ⟨u + h0*v1 + d1*v0, by linear_combination hu + h0*hv1 + d1*hv0⟩
  have hQd : (2013265921:ℤ) ∣ qq - d2*d3 := by
    obtain ⟨u, hu⟩ := hQ; obtain ⟨v2, hv2⟩ := hb2; obtain ⟨v3, hv3⟩ := hb3
    exact ⟨u + h2*v3 + d3*v2, by linear_combination hu + h2*hv3 + d3*hv2⟩
  -- the boundary exclusion: hi-residue 15 forces lo = 0
  have h15 : d0 + 2*d1 + 4*d2 + 8*d3 = 15 → lo = 0 := by
    intro hD
    have he0 : d0 = 1 := by omega
    have he1 : d1 = 1 := by omega
    have he2 : d2 = 1 := by omega
    have he3 : d3 = 1 := by omega
    rw [he0, he1] at hPd
    rw [he2, he3] at hQd
    have hlo0 : (2013265921:ℤ) ∣ lo := by
      obtain ⟨u, hu⟩ := htop; obtain ⟨v, hv⟩ := hPd; obtain ⟨w, hw⟩ := hQd
      exact ⟨u - lo*pp*w - lo*v, by linear_combination hu - lo*pp*hw - lo*hv⟩
    obtain ⟨w, hw⟩ := hlo0
    omega
  -- the exact split: the p-shifted branch is killed by h15
  obtain ⟨k, hk⟩ := hdecD
  by_cases hD : d0 + 2*d1 + 4*d2 + 8*d3 = 15
  · have := h15 hD
    omega
  · omega

/-- **The decider compare**: exact hi/lo splits + the branch bit + the range-checked
difference give strict `<` on the selected limbs. -/
theorem decider_lt {xa xb HA HB loa lob t delta : ℤ}
    (hEa : xa = 134217728*HA + loa) (hEb : xb = 134217728*HB + lob)
    (hHA0 : 0 ≤ HA) (hHA1 : HA ≤ 15) (hHB0 : 0 ≤ HB) (hHB1 : HB ≤ 15)
    (hloa : 0 ≤ loa) (hloa' : loa < 134217728)
    (hlob : 0 ≤ lob) (hlob' : lob < 134217728)
    (hdelta : 0 ≤ delta) (hdelta' : delta < 134217728)
    (ht : (2013265921:ℤ) ∣ t ∨ (2013265921:ℤ) ∣ t - 1)
    (hhiEq : (2013265921:ℤ) ∣ (1 - t)*(HA - HB))
    (hdel : (2013265921:ℤ) ∣ (t*(HB - HA) + (1 - t)*(lob - loa) - 1 - delta)) :
    xa < xb := by
  rcases ht with h0 | h1
  · -- t ≡ 0: hi equal, lo decides
    obtain ⟨k, hk⟩ := h0
    have hHeq : (2013265921:ℤ) ∣ (HA - HB) := by
      obtain ⟨w, hw⟩ := hhiEq
      exact ⟨w + k*(HA - HB), by linear_combination hw + (HA - HB)*hk⟩
    have hHeq' : HA = HB := by obtain ⟨w, hw⟩ := hHeq; omega
    have hlt : (2013265921:ℤ) ∣ (lob - loa - 1 - delta) := by
      obtain ⟨u, hu⟩ := hdel
      exact ⟨u - k*(HB - HA) + k*(lob - loa),
        by linear_combination hu - (HB - HA)*hk + (lob - loa)*hk⟩
    obtain ⟨w, hw⟩ := hlt
    omega
  · -- t ≡ 1: hi decides
    obtain ⟨k, hk⟩ := h1
    have hlt : (2013265921:ℤ) ∣ (HB - HA - 1 - delta) := by
      obtain ⟨u, hu⟩ := hdel
      exact ⟨u - k*(HB - HA) + k*(lob - loa),
        by linear_combination hu - (HB - HA)*hk + (lob - loa)*hk⟩
    obtain ⟨w, hw⟩ := hlt
    omega

/-! ## §4 — Soundness: a satisfying row's keys are genuinely lex-ordered. -/

set_option maxHeartbeats 1600000

/-- The one-hot residue sum (isolated so `omega` runs in a minimal, disjunction-free
context). -/
private theorem onehot_sum {c0 c1 c2 c3 c4 c5 c6 c7 : ℤ}
    {s0 s1 s2 s3 s4 s5 s6 s7 e0 e1 e2 e3 e4 e5 e6 e7 m : ℤ}
    (hc0 : c0 = 0 ∨ c0 = 1) (hc1 : c1 = 0 ∨ c1 = 1) (hc2 : c2 = 0 ∨ c2 = 1)
    (hc3 : c3 = 0 ∨ c3 = 1) (hc4 : c4 = 0 ∨ c4 = 1) (hc5 : c5 = 0 ∨ c5 = 1)
    (hc6 : c6 = 0 ∨ c6 = 1) (hc7 : c7 = 0 ∨ c7 = 1)
    (he0 : s0 - c0 = 2013265921 * e0) (he1 : s1 - c1 = 2013265921 * e1)
    (he2 : s2 - c2 = 2013265921 * e2) (he3 : s3 - c3 = 2013265921 * e3)
    (he4 : s4 - c4 = 2013265921 * e4) (he5 : s5 - c5 = 2013265921 * e5)
    (he6 : s6 - c6 = 2013265921 * e6) (he7 : s7 - c7 = 2013265921 * e7)
    (hm : s0 + s1 + s2 + s3 + s4 + s5 + s6 + s7 - 1 = 2013265921 * m) :
    c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7 = 1 := by
  omega

/-- One-hot case split over the genuine selector residues. -/
private theorem onehot_cases {c0 c1 c2 c3 c4 c5 c6 c7 : ℤ}
    (hc0 : c0 = 0 ∨ c0 = 1) (hc1 : c1 = 0 ∨ c1 = 1) (hc2 : c2 = 0 ∨ c2 = 1)
    (hc3 : c3 = 0 ∨ c3 = 1) (hc4 : c4 = 0 ∨ c4 = 1) (hc5 : c5 = 0 ∨ c5 = 1)
    (hc6 : c6 = 0 ∨ c6 = 1) (hc7 : c7 = 0 ∨ c7 = 1)
    (hsum : c0 + c1 + c2 + c3 + c4 + c5 + c6 + c7 = 1) :
    (c0 = 1 ∧ c1 = 0 ∧ c2 = 0 ∧ c3 = 0 ∧ c4 = 0 ∧ c5 = 0 ∧ c6 = 0 ∧ c7 = 0)
      ∨ (c0 = 0 ∧ c1 = 1 ∧ c2 = 0 ∧ c3 = 0 ∧ c4 = 0 ∧ c5 = 0 ∧ c6 = 0 ∧ c7 = 0)
      ∨ (c0 = 0 ∧ c1 = 0 ∧ c2 = 1 ∧ c3 = 0 ∧ c4 = 0 ∧ c5 = 0 ∧ c6 = 0 ∧ c7 = 0)
      ∨ (c0 = 0 ∧ c1 = 0 ∧ c2 = 0 ∧ c3 = 1 ∧ c4 = 0 ∧ c5 = 0 ∧ c6 = 0 ∧ c7 = 0)
      ∨ (c0 = 0 ∧ c1 = 0 ∧ c2 = 0 ∧ c3 = 0 ∧ c4 = 1 ∧ c5 = 0 ∧ c6 = 0 ∧ c7 = 0)
      ∨ (c0 = 0 ∧ c1 = 0 ∧ c2 = 0 ∧ c3 = 0 ∧ c4 = 0 ∧ c5 = 1 ∧ c6 = 0 ∧ c7 = 0)
      ∨ (c0 = 0 ∧ c1 = 0 ∧ c2 = 0 ∧ c3 = 0 ∧ c4 = 0 ∧ c5 = 0 ∧ c6 = 1 ∧ c7 = 0)
      ∨ (c0 = 0 ∧ c1 = 0 ∧ c2 = 0 ∧ c3 = 0 ∧ c4 = 0 ∧ c5 = 0 ∧ c6 = 0 ∧ c7 = 1) := by
  rcases hc0 with rfl | rfl <;> rcases hc1 with rfl | rfl <;> rcases hc2 with rfl | rfl <;>
    rcases hc3 with rfl | rfl <;> rcases hc4 with rfl | rfl <;> rcases hc5 with rfl | rfl <;>
    rcases hc6 with rfl | rfl <;> rcases hc7 with rfl | rfl <;> omega

/-- The branch-independent tail: once the deciding limb `jn` is fixed (selector residues
resolved), the composed gate facts force `a <_lex b` with the decision at `jn`. -/
private theorem lex_branch_finish (env : VmRowEnv)
    (jn : Nat) (hjn : jn < 8)
    (hxa0 : 0 ≤ env.loc jn) (hxa1 : env.loc jn < 2013265921)
    (hxb0 : 0 ≤ env.loc (8 + jn)) (hxb1 : env.loc (8 + jn) < 2013265921)
    (hALo : 0 ≤ env.loc 30 ∧ env.loc 30 < 134217728)
    (hBLo : 0 ≤ env.loc 37 ∧ env.loc 37 < 134217728)
    (hDel : 0 ≤ env.loc 39 ∧ env.loc 39 < 134217728)
    {dA0 dA1 dA2 dA3 dB0 dB1 dB2 dB3 : ℤ}
    (hdA0 : dA0 = 0 ∨ dA0 = 1) (hdA1 : dA1 = 0 ∨ dA1 = 1)
    (hdA2 : dA2 = 0 ∨ dA2 = 1) (hdA3 : dA3 = 0 ∨ dA3 = 1)
    (hdB0 : dB0 = 0 ∨ dB0 = 1) (hdB1 : dB1 = 0 ∨ dB1 = 1)
    (hdB2 : dB2 = 0 ∨ dB2 = 1) (hdB3 : dB3 = 0 ∨ dB3 = 1)
    (hbA0 : (2013265921:ℤ) ∣ env.loc 24 - dA0) (hbA1 : (2013265921:ℤ) ∣ env.loc 25 - dA1)
    (hbA2 : (2013265921:ℤ) ∣ env.loc 26 - dA2) (hbA3 : (2013265921:ℤ) ∣ env.loc 27 - dA3)
    (hbB0 : (2013265921:ℤ) ∣ env.loc 31 - dB0) (hbB1 : (2013265921:ℤ) ∣ env.loc 32 - dB1)
    (hbB2 : (2013265921:ℤ) ∣ env.loc 33 - dB2) (hbB3 : (2013265921:ℤ) ∣ env.loc 34 - dB3)
    (hpAP : (2013265921:ℤ) ∣ env.loc 28 - env.loc 24 * env.loc 25)
    (hpAQ : (2013265921:ℤ) ∣ env.loc 29 - env.loc 26 * env.loc 27)
    (hpBP : (2013265921:ℤ) ∣ env.loc 35 - env.loc 31 * env.loc 32)
    (hpBQ : (2013265921:ℤ) ∣ env.loc 36 - env.loc 33 * env.loc 34)
    (htopA : (2013265921:ℤ) ∣ env.loc 28 * env.loc 29 * env.loc 30)
    (htopB : (2013265921:ℤ) ∣ env.loc 35 * env.loc 36 * env.loc 37)
    (hselA : (2013265921:ℤ) ∣ (env.loc 16 * env.loc 0 + env.loc 17 * env.loc 1
      + env.loc 18 * env.loc 2 + env.loc 19 * env.loc 3 + env.loc 20 * env.loc 4
      + env.loc 21 * env.loc 5 + env.loc 22 * env.loc 6 + env.loc 23 * env.loc 7)
      - env.loc jn)
    (hselB : (2013265921:ℤ) ∣ (env.loc 16 * env.loc 8 + env.loc 17 * env.loc 9
      + env.loc 18 * env.loc 10 + env.loc 19 * env.loc 11 + env.loc 20 * env.loc 12
      + env.loc 21 * env.loc 13 + env.loc 22 * env.loc 14 + env.loc 23 * env.loc 15)
      - env.loc (8 + jn))
    (hdecA : (2013265921:ℤ) ∣ (env.loc 16 * env.loc 0 + env.loc 17 * env.loc 1
      + env.loc 18 * env.loc 2 + env.loc 19 * env.loc 3 + env.loc 20 * env.loc 4
      + env.loc 21 * env.loc 5 + env.loc 22 * env.loc 6 + env.loc 23 * env.loc 7)
      - 134217728*(env.loc 24 + 2*env.loc 25 + 4*env.loc 26 + 8*env.loc 27) - env.loc 30)
    (hdecB : (2013265921:ℤ) ∣ (env.loc 16 * env.loc 8 + env.loc 17 * env.loc 9
      + env.loc 18 * env.loc 10 + env.loc 19 * env.loc 11 + env.loc 20 * env.loc 12
      + env.loc 21 * env.loc 13 + env.loc 22 * env.loc 14 + env.loc 23 * env.loc 15)
      - 134217728*(env.loc 31 + 2*env.loc 32 + 4*env.loc 33 + 8*env.loc 34) - env.loc 37)
    (htOr : (2013265921:ℤ) ∣ env.loc 38 ∨ (2013265921:ℤ) ∣ env.loc 38 - 1)
    (hhiEqD : (2013265921:ℤ) ∣ (1 - env.loc 38)
      * ((dA0 + 2*dA1 + 4*dA2 + 8*dA3) - (dB0 + 2*dB1 + 4*dB2 + 8*dB3)))
    (hdelD : (2013265921:ℤ) ∣ (env.loc 38
        * ((dB0 + 2*dB1 + 4*dB2 + 8*dB3) - (dA0 + 2*dA1 + 4*dA2 + 8*dA3))
      + (1 - env.loc 38) * (env.loc 37 - env.loc 30) - 1 - env.loc 39))
    (hpre : ∀ k, k < jn → env.loc k = env.loc (8 + k)) :
    toLex (lexKeyA env) < toLex (lexKeyB env) := by
  have hdecAx : (2013265921:ℤ) ∣ (134217728*(env.loc 24 + 2*env.loc 25 + 4*env.loc 26
      + 8*env.loc 27) + env.loc 30 - env.loc jn) := by
    obtain ⟨u, hu⟩ := hdecA
    obtain ⟨w, hw⟩ := hselA
    exact ⟨-u + w, by linear_combination -hu + hw⟩
  have hdecBx : (2013265921:ℤ) ∣ (134217728*(env.loc 31 + 2*env.loc 32 + 4*env.loc 33
      + 8*env.loc 34) + env.loc 37 - env.loc (8 + jn)) := by
    obtain ⟨u, hu⟩ := hdecB
    obtain ⟨w, hw⟩ := hselB
    exact ⟨-u + w, by linear_combination -hu + hw⟩
  have hEa := operand_pinned hxa0 hxa1 hALo.1 hALo.2 hdA0 hdA1 hdA2 hdA3
    hbA0 hbA1 hbA2 hbA3 hpAP hpAQ htopA hdecAx
  have hEb := operand_pinned hxb0 hxb1 hBLo.1 hBLo.2 hdB0 hdB1 hdB2 hdB3
    hbB0 hbB1 hbB2 hbB3 hpBP hpBQ htopB hdecBx
  have hlt : env.loc jn < env.loc (8 + jn) :=
    decider_lt hEa hEb (by omega) (by omega) (by omega) (by omega)
      hALo.1 hALo.2 hBLo.1 hBLo.2 hDel.1 hDel.2 htOr hhiEqD hdelD
  exact ⟨⟨jn, hjn⟩, fun m hm => hpre m.val hm, hlt⟩

/-- **Soundness.** A row satisfying the block (against a faithful 27-bit range table), with
canonical key cells, carries keys with `a <_lex b` — the spike's `Digest8Key` order (its
`Lex (Fin 8 → ℤ)`, felt 0 most significant). -/
theorem lexLt8_sound (tf : TraceFamily) (hr : tf (.custom LEX_RANGE_TID) = rangeRows 27)
    (env : VmRowEnv) (hcanon : LexCanon env) (h : lexBlockHolds tf env) :
    toLex (lexKeyA env) < toLex (lexKeyB env) := by
  simp only [lexBlockHolds, lexLt8Constraints, List.forall_mem_cons,
    VmConstraint2.holdsAt, VmConstraint.holdsVm, Lookup.holdsAt,
    gBool, gOneHot, gPre0, gPre1, gPre2, gPre3, gPre4, gPre5, gPre6,
    gPairAP, gPairAQ, gPairBP, gPairBQ, gTopA, gTopB, gDecompA, gDecompB, gHiEq, gDelta,
    eS, ePre0, ePre1, ePre2, ePre3, ePre4, ePre5, ePre6, eSelA, eSelB, eHiA, eHiB,
    eOneMinus, eSub, lkALo, lkBLo, lkDelta,
    EmittedExpr.eval, List.map_cons, List.map_nil] at h
  obtain ⟨hg16, hg17, hg18, hg19, hg20, hg21, hg22, hg23, hgOne,
    hgP0, hgP1, hgP2, hgP3, hgP4, hgP5, hgP6,
    hg24, hg25, hg26, hg27, hg31, hg32, hg33, hg34,
    hgAP, hgAQ, hgBP, hgBQ, hgTA, hgTB, hgDA, hgDB, hg38, hgHiE, hgDel,
    hlk1, hlk2, hlk3, -⟩ := h
  -- range lookups → genuine ℤ bounds (never evaluating the 2^27 table)
  rw [hr] at hlk1 hlk2 hlk3
  have hALo := (range_row_mem_iff _ 27).mp hlk1
  have hBLo := (range_row_mem_iff _ 27).mp hlk2
  have hDel := (range_row_mem_iff _ 27).mp hlk3
  norm_num at hALo hBLo hDel
  -- canonicality of the 16 key cells
  have hx0 := hcanon 0 (by norm_num); have hx1 := hcanon 1 (by norm_num)
  have hx2 := hcanon 2 (by norm_num); have hx3 := hcanon 3 (by norm_num)
  have hx4 := hcanon 4 (by norm_num); have hx5 := hcanon 5 (by norm_num)
  have hx6 := hcanon 6 (by norm_num); have hx7 := hcanon 7 (by norm_num)
  have hx8 := hcanon 8 (by norm_num); have hx9 := hcanon 9 (by norm_num)
  have hx10 := hcanon 10 (by norm_num); have hx11 := hcanon 11 (by norm_num)
  have hx12 := hcanon 12 (by norm_num); have hx13 := hcanon 13 (by norm_num)
  have hx14 := hcanon 14 (by norm_num); have hx15 := hcanon 15 (by norm_num)
  -- boolean residues: selectors, hi bits, branch bit
  obtain ⟨c0, hc0, hs0⟩ := bool01 (reshape (dvd_of_modEq_zero hg16) (by ring))
  obtain ⟨c1, hc1, hs1⟩ := bool01 (reshape (dvd_of_modEq_zero hg17) (by ring))
  obtain ⟨c2, hc2, hs2⟩ := bool01 (reshape (dvd_of_modEq_zero hg18) (by ring))
  obtain ⟨c3, hc3, hs3⟩ := bool01 (reshape (dvd_of_modEq_zero hg19) (by ring))
  obtain ⟨c4, hc4, hs4⟩ := bool01 (reshape (dvd_of_modEq_zero hg20) (by ring))
  obtain ⟨c5, hc5, hs5⟩ := bool01 (reshape (dvd_of_modEq_zero hg21) (by ring))
  obtain ⟨c6, hc6, hs6⟩ := bool01 (reshape (dvd_of_modEq_zero hg22) (by ring))
  obtain ⟨c7, hc7, hs7⟩ := bool01 (reshape (dvd_of_modEq_zero hg23) (by ring))
  obtain ⟨dA0, hdA0, hbA0⟩ := bool01 (reshape (dvd_of_modEq_zero hg24) (by ring))
  obtain ⟨dA1, hdA1, hbA1⟩ := bool01 (reshape (dvd_of_modEq_zero hg25) (by ring))
  obtain ⟨dA2, hdA2, hbA2⟩ := bool01 (reshape (dvd_of_modEq_zero hg26) (by ring))
  obtain ⟨dA3, hdA3, hbA3⟩ := bool01 (reshape (dvd_of_modEq_zero hg27) (by ring))
  obtain ⟨dB0, hdB0, hbB0⟩ := bool01 (reshape (dvd_of_modEq_zero hg31) (by ring))
  obtain ⟨dB1, hdB1, hbB1⟩ := bool01 (reshape (dvd_of_modEq_zero hg32) (by ring))
  obtain ⟨dB2, hdB2, hbB2⟩ := bool01 (reshape (dvd_of_modEq_zero hg33) (by ring))
  obtain ⟨dB3, hdB3, hbB3⟩ := bool01 (reshape (dvd_of_modEq_zero hg34) (by ring))
  obtain ⟨ct, hct, hst⟩ := bool01 (reshape (dvd_of_modEq_zero hg38) (by ring))
  have htOr : (2013265921:ℤ) ∣ env.loc 38 ∨ (2013265921:ℤ) ∣ env.loc 38 - 1 := by
    rcases hct with rfl | rfl
    · exact Or.inl (by simpa using hst)
    · exact Or.inr hst
  -- clean dvd forms of the structural gates
  have hpre0D : (2013265921:ℤ) ∣ (1 - env.loc 16) * (env.loc 0 - env.loc 8) :=
    reshape (dvd_of_modEq_zero hgP0) (by ring)
  have hpre1D : (2013265921:ℤ) ∣ (1 - (env.loc 16 + env.loc 17))
      * (env.loc 1 - env.loc 9) := reshape (dvd_of_modEq_zero hgP1) (by ring)
  have hpre2D : (2013265921:ℤ) ∣ (1 - (env.loc 16 + env.loc 17 + env.loc 18))
      * (env.loc 2 - env.loc 10) := reshape (dvd_of_modEq_zero hgP2) (by ring)
  have hpre3D : (2013265921:ℤ) ∣ (1 - (env.loc 16 + env.loc 17 + env.loc 18 + env.loc 19))
      * (env.loc 3 - env.loc 11) := reshape (dvd_of_modEq_zero hgP3) (by ring)
  have hpre4D : (2013265921:ℤ) ∣ (1 - (env.loc 16 + env.loc 17 + env.loc 18 + env.loc 19
      + env.loc 20)) * (env.loc 4 - env.loc 12) := reshape (dvd_of_modEq_zero hgP4) (by ring)
  have hpre5D : (2013265921:ℤ) ∣ (1 - (env.loc 16 + env.loc 17 + env.loc 18 + env.loc 19
      + env.loc 20 + env.loc 21)) * (env.loc 5 - env.loc 13) :=
    reshape (dvd_of_modEq_zero hgP5) (by ring)
  have hpre6D : (2013265921:ℤ) ∣ (1 - (env.loc 16 + env.loc 17 + env.loc 18 + env.loc 19
      + env.loc 20 + env.loc 21 + env.loc 22)) * (env.loc 6 - env.loc 14) :=
    reshape (dvd_of_modEq_zero hgP6) (by ring)
  have hpAPd : (2013265921:ℤ) ∣ env.loc 28 - env.loc 24 * env.loc 25 :=
    reshape (dvd_of_modEq_zero hgAP) (by ring)
  have hpAQd : (2013265921:ℤ) ∣ env.loc 29 - env.loc 26 * env.loc 27 :=
    reshape (dvd_of_modEq_zero hgAQ) (by ring)
  have hpBPd : (2013265921:ℤ) ∣ env.loc 35 - env.loc 31 * env.loc 32 :=
    reshape (dvd_of_modEq_zero hgBP) (by ring)
  have hpBQd : (2013265921:ℤ) ∣ env.loc 36 - env.loc 33 * env.loc 34 :=
    reshape (dvd_of_modEq_zero hgBQ) (by ring)
  have htopAd : (2013265921:ℤ) ∣ env.loc 28 * env.loc 29 * env.loc 30 :=
    reshape (dvd_of_modEq_zero hgTA) (by ring)
  have htopBd : (2013265921:ℤ) ∣ env.loc 35 * env.loc 36 * env.loc 37 :=
    reshape (dvd_of_modEq_zero hgTB) (by ring)
  have hdecAd : (2013265921:ℤ) ∣ (env.loc 16 * env.loc 0 + env.loc 17 * env.loc 1
      + env.loc 18 * env.loc 2 + env.loc 19 * env.loc 3 + env.loc 20 * env.loc 4
      + env.loc 21 * env.loc 5 + env.loc 22 * env.loc 6 + env.loc 23 * env.loc 7)
      - 134217728*(env.loc 24 + 2*env.loc 25 + 4*env.loc 26 + 8*env.loc 27) - env.loc 30 :=
    reshape (dvd_of_modEq_zero hgDA) (by ring)
  have hdecBd : (2013265921:ℤ) ∣ (env.loc 16 * env.loc 8 + env.loc 17 * env.loc 9
      + env.loc 18 * env.loc 10 + env.loc 19 * env.loc 11 + env.loc 20 * env.loc 12
      + env.loc 21 * env.loc 13 + env.loc 22 * env.loc 14 + env.loc 23 * env.loc 15)
      - 134217728*(env.loc 31 + 2*env.loc 32 + 4*env.loc 33 + 8*env.loc 34) - env.loc 37 :=
    reshape (dvd_of_modEq_zero hgDB) (by ring)
  -- hi-eq / delta gates moved onto the genuine bit residues
  have hhiA := hi4_pin hbA0 hbA1 hbA2 hbA3
  have hhiB := hi4_pin hbB0 hbB1 hbB2 hbB3
  have hhiEqD : (2013265921:ℤ) ∣ (1 - env.loc 38)
      * ((dA0 + 2*dA1 + 4*dA2 + 8*dA3) - (dB0 + 2*dB1 + 4*dB2 + 8*dB3)) := by
    have hraw : (2013265921:ℤ) ∣ (1 - env.loc 38)
        * ((env.loc 24 + 2*env.loc 25 + 4*env.loc 26 + 8*env.loc 27)
          - (env.loc 31 + 2*env.loc 32 + 4*env.loc 33 + 8*env.loc 34)) :=
      reshape (dvd_of_modEq_zero hgHiE) (by ring)
    obtain ⟨u, hu⟩ := hraw
    obtain ⟨va, hva⟩ := hhiA
    obtain ⟨vb, hvb⟩ := hhiB
    exact ⟨u - (1 - env.loc 38)*va + (1 - env.loc 38)*vb,
      by linear_combination hu - (1 - env.loc 38)*hva + (1 - env.loc 38)*hvb⟩
  have hdelD : (2013265921:ℤ) ∣ (env.loc 38
      * ((dB0 + 2*dB1 + 4*dB2 + 8*dB3) - (dA0 + 2*dA1 + 4*dA2 + 8*dA3))
      + (1 - env.loc 38) * (env.loc 37 - env.loc 30) - 1 - env.loc 39) := by
    have hraw : (2013265921:ℤ) ∣ (env.loc 38
        * ((env.loc 31 + 2*env.loc 32 + 4*env.loc 33 + 8*env.loc 34)
          - (env.loc 24 + 2*env.loc 25 + 4*env.loc 26 + 8*env.loc 27))
        + (1 - env.loc 38) * (env.loc 37 - env.loc 30) - 1 - env.loc 39) :=
      reshape (dvd_of_modEq_zero hgDel) (by ring)
    obtain ⟨u, hu⟩ := hraw
    obtain ⟨va, hva⟩ := hhiA
    obtain ⟨vb, hvb⟩ := hhiB
    exact ⟨u - env.loc 38 * vb + env.loc 38 * va,
      by linear_combination hu - env.loc 38 * hvb + env.loc 38 * hva⟩
  -- selector residues as explicit equations, one-hot sum, and the 8-way branch
  obtain ⟨e0, he0⟩ := id hs0
  obtain ⟨e1, he1⟩ := id hs1
  obtain ⟨e2, he2⟩ := id hs2
  obtain ⟨e3, he3⟩ := id hs3
  obtain ⟨e4, he4⟩ := id hs4
  obtain ⟨e5, he5⟩ := id hs5
  obtain ⟨e6, he6⟩ := id hs6
  obtain ⟨e7, he7⟩ := id hs7
  have honeD : (2013265921:ℤ) ∣ (env.loc 16 + env.loc 17 + env.loc 18 + env.loc 19
      + env.loc 20 + env.loc 21 + env.loc 22 + env.loc 23 - 1) :=
    reshape (dvd_of_modEq_zero hgOne) (by ring)
  obtain ⟨m, hm⟩ := honeD
  have hbranch := onehot_cases hc0 hc1 hc2 hc3 hc4 hc5 hc6 hc7
    (onehot_sum hc0 hc1 hc2 hc3 hc4 hc5 hc6 hc7
      he0 he1 he2 he3 he4 he5 he6 he7 hm)
  rcases hbranch with ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    | ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    | ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    | ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    | ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · -- decider at limb 0
    exact lex_branch_finish env 0 (by norm_num) hx0.1 hx0.2 hx8.1 hx8.2 hALo hBLo hDel
      hdA0 hdA1 hdA2 hdA3 hdB0 hdB1 hdB2 hdB3 hbA0 hbA1 hbA2 hbA3 hbB0 hbB1 hbB2 hbB3
      hpAPd hpAQd hpBPd hpBQd htopAd htopBd
      (select8_pin hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 (by ring))
      (select8_pin hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 (by ring))
      hdecAd hdecBd htOr hhiEqD hdelD
      (fun k hk => absurd hk (Nat.not_lt_zero k))
  · -- decider at limb 1
    exact lex_branch_finish env 1 (by norm_num) hx1.1 hx1.2 hx9.1 hx9.2 hALo hBLo hDel
      hdA0 hdA1 hdA2 hdA3 hdB0 hdB1 hdB2 hdB3 hbA0 hbA1 hbA2 hbA3 hbB0 hbB1 hbB2 hbB3
      hpAPd hpAQd hpBPd hpBQd htopAd htopBd
      (select8_pin hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 (by ring))
      (select8_pin hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 (by ring))
      hdecAd hdecBd htOr hhiEqD hdelD
      (by
        intro k hk
        interval_cases k
        · exact prefix_eq ⟨e0, by linear_combination he0⟩ hpre0D hx0.1 hx0.2 hx8.1 hx8.2)
  · -- decider at limb 2
    exact lex_branch_finish env 2 (by norm_num) hx2.1 hx2.2 hx10.1 hx10.2 hALo hBLo hDel
      hdA0 hdA1 hdA2 hdA3 hdB0 hdB1 hdB2 hdB3 hbA0 hbA1 hbA2 hbA3 hbB0 hbB1 hbB2 hbB3
      hpAPd hpAQd hpBPd hpBQd htopAd htopBd
      (select8_pin hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 (by ring))
      (select8_pin hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 (by ring))
      hdecAd hdecBd htOr hhiEqD hdelD
      (by
        intro k hk
        interval_cases k
        · exact prefix_eq ⟨e0, by linear_combination he0⟩ hpre0D hx0.1 hx0.2 hx8.1 hx8.2
        · exact prefix_eq ⟨e0 + e1, by linear_combination he0 + he1⟩ hpre1D
            hx1.1 hx1.2 hx9.1 hx9.2)
  · -- decider at limb 3
    exact lex_branch_finish env 3 (by norm_num) hx3.1 hx3.2 hx11.1 hx11.2 hALo hBLo hDel
      hdA0 hdA1 hdA2 hdA3 hdB0 hdB1 hdB2 hdB3 hbA0 hbA1 hbA2 hbA3 hbB0 hbB1 hbB2 hbB3
      hpAPd hpAQd hpBPd hpBQd htopAd htopBd
      (select8_pin hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 (by ring))
      (select8_pin hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 (by ring))
      hdecAd hdecBd htOr hhiEqD hdelD
      (by
        intro k hk
        interval_cases k
        · exact prefix_eq ⟨e0, by linear_combination he0⟩ hpre0D hx0.1 hx0.2 hx8.1 hx8.2
        · exact prefix_eq ⟨e0 + e1, by linear_combination he0 + he1⟩ hpre1D
            hx1.1 hx1.2 hx9.1 hx9.2
        · exact prefix_eq ⟨e0 + e1 + e2, by linear_combination he0 + he1 + he2⟩ hpre2D
            hx2.1 hx2.2 hx10.1 hx10.2)
  · -- decider at limb 4
    exact lex_branch_finish env 4 (by norm_num) hx4.1 hx4.2 hx12.1 hx12.2 hALo hBLo hDel
      hdA0 hdA1 hdA2 hdA3 hdB0 hdB1 hdB2 hdB3 hbA0 hbA1 hbA2 hbA3 hbB0 hbB1 hbB2 hbB3
      hpAPd hpAQd hpBPd hpBQd htopAd htopBd
      (select8_pin hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 (by ring))
      (select8_pin hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 (by ring))
      hdecAd hdecBd htOr hhiEqD hdelD
      (by
        intro k hk
        interval_cases k
        · exact prefix_eq ⟨e0, by linear_combination he0⟩ hpre0D hx0.1 hx0.2 hx8.1 hx8.2
        · exact prefix_eq ⟨e0 + e1, by linear_combination he0 + he1⟩ hpre1D
            hx1.1 hx1.2 hx9.1 hx9.2
        · exact prefix_eq ⟨e0 + e1 + e2, by linear_combination he0 + he1 + he2⟩ hpre2D
            hx2.1 hx2.2 hx10.1 hx10.2
        · exact prefix_eq ⟨e0 + e1 + e2 + e3, by linear_combination he0 + he1 + he2 + he3⟩
            hpre3D hx3.1 hx3.2 hx11.1 hx11.2)
  · -- decider at limb 5
    exact lex_branch_finish env 5 (by norm_num) hx5.1 hx5.2 hx13.1 hx13.2 hALo hBLo hDel
      hdA0 hdA1 hdA2 hdA3 hdB0 hdB1 hdB2 hdB3 hbA0 hbA1 hbA2 hbA3 hbB0 hbB1 hbB2 hbB3
      hpAPd hpAQd hpBPd hpBQd htopAd htopBd
      (select8_pin hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 (by ring))
      (select8_pin hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 (by ring))
      hdecAd hdecBd htOr hhiEqD hdelD
      (by
        intro k hk
        interval_cases k
        · exact prefix_eq ⟨e0, by linear_combination he0⟩ hpre0D hx0.1 hx0.2 hx8.1 hx8.2
        · exact prefix_eq ⟨e0 + e1, by linear_combination he0 + he1⟩ hpre1D
            hx1.1 hx1.2 hx9.1 hx9.2
        · exact prefix_eq ⟨e0 + e1 + e2, by linear_combination he0 + he1 + he2⟩ hpre2D
            hx2.1 hx2.2 hx10.1 hx10.2
        · exact prefix_eq ⟨e0 + e1 + e2 + e3, by linear_combination he0 + he1 + he2 + he3⟩
            hpre3D hx3.1 hx3.2 hx11.1 hx11.2
        · exact prefix_eq ⟨e0 + e1 + e2 + e3 + e4,
              by linear_combination he0 + he1 + he2 + he3 + he4⟩
            hpre4D hx4.1 hx4.2 hx12.1 hx12.2)
  · -- decider at limb 6
    exact lex_branch_finish env 6 (by norm_num) hx6.1 hx6.2 hx14.1 hx14.2 hALo hBLo hDel
      hdA0 hdA1 hdA2 hdA3 hdB0 hdB1 hdB2 hdB3 hbA0 hbA1 hbA2 hbA3 hbB0 hbB1 hbB2 hbB3
      hpAPd hpAQd hpBPd hpBQd htopAd htopBd
      (select8_pin hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 (by ring))
      (select8_pin hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 (by ring))
      hdecAd hdecBd htOr hhiEqD hdelD
      (by
        intro k hk
        interval_cases k
        · exact prefix_eq ⟨e0, by linear_combination he0⟩ hpre0D hx0.1 hx0.2 hx8.1 hx8.2
        · exact prefix_eq ⟨e0 + e1, by linear_combination he0 + he1⟩ hpre1D
            hx1.1 hx1.2 hx9.1 hx9.2
        · exact prefix_eq ⟨e0 + e1 + e2, by linear_combination he0 + he1 + he2⟩ hpre2D
            hx2.1 hx2.2 hx10.1 hx10.2
        · exact prefix_eq ⟨e0 + e1 + e2 + e3, by linear_combination he0 + he1 + he2 + he3⟩
            hpre3D hx3.1 hx3.2 hx11.1 hx11.2
        · exact prefix_eq ⟨e0 + e1 + e2 + e3 + e4,
              by linear_combination he0 + he1 + he2 + he3 + he4⟩
            hpre4D hx4.1 hx4.2 hx12.1 hx12.2
        · exact prefix_eq ⟨e0 + e1 + e2 + e3 + e4 + e5,
              by linear_combination he0 + he1 + he2 + he3 + he4 + he5⟩
            hpre5D hx5.1 hx5.2 hx13.1 hx13.2)
  · -- decider at limb 7
    exact lex_branch_finish env 7 (by norm_num) hx7.1 hx7.2 hx15.1 hx15.2 hALo hBLo hDel
      hdA0 hdA1 hdA2 hdA3 hdB0 hdB1 hdB2 hdB3 hbA0 hbA1 hbA2 hbA3 hbB0 hbB1 hbB2 hbB3
      hpAPd hpAQd hpBPd hpBQd htopAd htopBd
      (select8_pin hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 (by ring))
      (select8_pin hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 (by ring))
      hdecAd hdecBd htOr hhiEqD hdelD
      (by
        intro k hk
        interval_cases k
        · exact prefix_eq ⟨e0, by linear_combination he0⟩ hpre0D hx0.1 hx0.2 hx8.1 hx8.2
        · exact prefix_eq ⟨e0 + e1, by linear_combination he0 + he1⟩ hpre1D
            hx1.1 hx1.2 hx9.1 hx9.2
        · exact prefix_eq ⟨e0 + e1 + e2, by linear_combination he0 + he1 + he2⟩ hpre2D
            hx2.1 hx2.2 hx10.1 hx10.2
        · exact prefix_eq ⟨e0 + e1 + e2 + e3, by linear_combination he0 + he1 + he2 + he3⟩
            hpre3D hx3.1 hx3.2 hx11.1 hx11.2
        · exact prefix_eq ⟨e0 + e1 + e2 + e3 + e4,
              by linear_combination he0 + he1 + he2 + he3 + he4⟩
            hpre4D hx4.1 hx4.2 hx12.1 hx12.2
        · exact prefix_eq ⟨e0 + e1 + e2 + e3 + e4 + e5,
              by linear_combination he0 + he1 + he2 + he3 + he4 + he5⟩
            hpre5D hx5.1 hx5.2 hx13.1 hx13.2
        · exact prefix_eq ⟨e0 + e1 + e2 + e3 + e4 + e5 + e6,
              by linear_combination he0 + he1 + he2 + he3 + he4 + he5 + he6⟩
            hpre6D hx6.1 hx6.2 hx14.1 hx14.2)

/-! ## §5 — Completeness: every lex-ordered pair of canonical keys has a satisfying witness. -/

/-- The selector one-hot collapse: exactly the deciding limb survives the select-sum. -/
private theorem sel_collapse (x : Fin 8 → ℤ) (j : Fin 8) :
    (if j.val = 0 then (1:ℤ) else 0) * x 0 + (if j.val = 1 then (1:ℤ) else 0) * x 1
      + (if j.val = 2 then (1:ℤ) else 0) * x 2 + (if j.val = 3 then (1:ℤ) else 0) * x 3
      + (if j.val = 4 then (1:ℤ) else 0) * x 4 + (if j.val = 5 then (1:ℤ) else 0) * x 5
      + (if j.val = 6 then (1:ℤ) else 0) * x 6 + (if j.val = 7 then (1:ℤ) else 0) * x 7
      = x j := by
  rcases j with ⟨jv, hjv⟩
  interval_cases jv <;> norm_num <;> rfl

/-- Prefix indicator sums collapse to 1 once the decider is inside the prefix. -/
private theorem preSum0 (j : Fin 8) (h : j.val ≤ 0) :
    (if j.val = 0 then (1:ℤ) else 0) = 1 := by
  rcases j with ⟨jv, hjv⟩
  interval_cases jv
  norm_num

private theorem preSum1 (j : Fin 8) (h : j.val ≤ 1) :
    (if j.val = 0 then (1:ℤ) else 0) + (if j.val = 1 then (1:ℤ) else 0) = 1 := by
  rcases j with ⟨jv, hjv⟩
  interval_cases jv <;> norm_num

private theorem preSum2 (j : Fin 8) (h : j.val ≤ 2) :
    (if j.val = 0 then (1:ℤ) else 0) + (if j.val = 1 then (1:ℤ) else 0)
      + (if j.val = 2 then (1:ℤ) else 0) = 1 := by
  rcases j with ⟨jv, hjv⟩
  interval_cases jv <;> norm_num

private theorem preSum3 (j : Fin 8) (h : j.val ≤ 3) :
    (if j.val = 0 then (1:ℤ) else 0) + (if j.val = 1 then (1:ℤ) else 0)
      + (if j.val = 2 then (1:ℤ) else 0) + (if j.val = 3 then (1:ℤ) else 0) = 1 := by
  rcases j with ⟨jv, hjv⟩
  interval_cases jv <;> norm_num

private theorem preSum4 (j : Fin 8) (h : j.val ≤ 4) :
    (if j.val = 0 then (1:ℤ) else 0) + (if j.val = 1 then (1:ℤ) else 0)
      + (if j.val = 2 then (1:ℤ) else 0) + (if j.val = 3 then (1:ℤ) else 0)
      + (if j.val = 4 then (1:ℤ) else 0) = 1 := by
  rcases j with ⟨jv, hjv⟩
  interval_cases jv <;> norm_num

private theorem preSum5 (j : Fin 8) (h : j.val ≤ 5) :
    (if j.val = 0 then (1:ℤ) else 0) + (if j.val = 1 then (1:ℤ) else 0)
      + (if j.val = 2 then (1:ℤ) else 0) + (if j.val = 3 then (1:ℤ) else 0)
      + (if j.val = 4 then (1:ℤ) else 0) + (if j.val = 5 then (1:ℤ) else 0) = 1 := by
  rcases j with ⟨jv, hjv⟩
  interval_cases jv <;> norm_num

private theorem preSum6 (j : Fin 8) (h : j.val ≤ 6) :
    (if j.val = 0 then (1:ℤ) else 0) + (if j.val = 1 then (1:ℤ) else 0)
      + (if j.val = 2 then (1:ℤ) else 0) + (if j.val = 3 then (1:ℤ) else 0)
      + (if j.val = 4 then (1:ℤ) else 0) + (if j.val = 5 then (1:ℤ) else 0)
      + (if j.val = 6 then (1:ℤ) else 0) = 1 := by
  rcases j with ⟨jv, hjv⟩
  interval_cases jv <;> norm_num

/-- 27-bit range-row membership from the literal bound (routes around the `2^27` power;
NEVER evaluates the table). -/
private theorem mem_range27 {v : ℤ} (h0 : 0 ≤ v) (h1 : v < 134217728) :
    [v] ∈ rangeRows 27 :=
  (range_row_mem_iff v 27).mpr ⟨h0, lt_of_lt_of_le h1 (by norm_num)⟩

/-- The selector indicators sum to one. -/
private theorem sel_one (j : Fin 8) :
    (if j.val = 0 then (1:ℤ) else 0) + (if j.val = 1 then (1:ℤ) else 0)
      + (if j.val = 2 then (1:ℤ) else 0) + (if j.val = 3 then (1:ℤ) else 0)
      + (if j.val = 4 then (1:ℤ) else 0) + (if j.val = 5 then (1:ℤ) else 0)
      + (if j.val = 6 then (1:ℤ) else 0) + (if j.val = 7 then (1:ℤ) else 0) = 1 := by
  rcases j with ⟨jv, hjv⟩
  interval_cases jv <;> norm_num

/-- An honest bit cell satisfies its booleanity gate. -/
private theorem bit_gate (x : ℤ) : (x % 2) * (x % 2 + -1) = 0 := by
  have h : x % 2 = 0 ∨ x % 2 = 1 := by omega
  rcases h with h | h <;> rw [h] <;> norm_num

/-- An honest canonical felt satisfies the `p`-boundary gate: its hi-nibble bits can only
all be set when the felt is `p − 1`, whose lo-limb is zero. -/
private theorem top_gate (v : ℤ) (hv0 : 0 ≤ v) (hv1 : v < 2013265921) :
    (v / 134217728 % 2) * (v / 134217728 / 2 % 2)
      * ((v / 134217728 / 4 % 2) * (v / 134217728 / 8 % 2)) * (v % 134217728) = 0 := by
  have h0 : v / 134217728 % 2 = 0 ∨ v / 134217728 % 2 = 1 := by omega
  have h1 : v / 134217728 / 2 % 2 = 0 ∨ v / 134217728 / 2 % 2 = 1 := by omega
  have h2 : v / 134217728 / 4 % 2 = 0 ∨ v / 134217728 / 4 % 2 = 1 := by omega
  have h3 : v / 134217728 / 8 % 2 = 0 ∨ v / 134217728 / 8 % 2 = 1 := by omega
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;>
    rcases h3 with h3 | h3 <;> rw [h0, h1, h2, h3] <;> norm_num
  omega

/-- The hi-nibble bit recombination is exact for canonical felts. -/
private theorem hi_recombine (v : ℤ) (hv0 : 0 ≤ v) (hv1 : v < 2013265921) :
    v / 134217728 % 2 + 2 * (v / 134217728 / 2 % 2) + 4 * (v / 134217728 / 4 % 2)
      + 8 * (v / 134217728 / 8 % 2) = v / 134217728 := by
  omega

/-- **The completeness witness**: the honest assignment for keys `a`, `b` deciding at `j`. -/
def wAsg (a b : Fin 8 → ℤ) (j : Fin 8) : Assignment := fun c =>
  match c with
  | 0 => a 0 | 1 => a 1 | 2 => a 2 | 3 => a 3
  | 4 => a 4 | 5 => a 5 | 6 => a 6 | 7 => a 7
  | 8 => b 0 | 9 => b 1 | 10 => b 2 | 11 => b 3
  | 12 => b 4 | 13 => b 5 | 14 => b 6 | 15 => b 7
  | 16 => if j.val = 0 then 1 else 0
  | 17 => if j.val = 1 then 1 else 0
  | 18 => if j.val = 2 then 1 else 0
  | 19 => if j.val = 3 then 1 else 0
  | 20 => if j.val = 4 then 1 else 0
  | 21 => if j.val = 5 then 1 else 0
  | 22 => if j.val = 6 then 1 else 0
  | 23 => if j.val = 7 then 1 else 0
  | 24 => a j / 134217728 % 2
  | 25 => a j / 134217728 / 2 % 2
  | 26 => a j / 134217728 / 4 % 2
  | 27 => a j / 134217728 / 8 % 2
  | 28 => (a j / 134217728 % 2) * (a j / 134217728 / 2 % 2)
  | 29 => (a j / 134217728 / 4 % 2) * (a j / 134217728 / 8 % 2)
  | 30 => a j % 134217728
  | 31 => b j / 134217728 % 2
  | 32 => b j / 134217728 / 2 % 2
  | 33 => b j / 134217728 / 4 % 2
  | 34 => b j / 134217728 / 8 % 2
  | 35 => (b j / 134217728 % 2) * (b j / 134217728 / 2 % 2)
  | 36 => (b j / 134217728 / 4 % 2) * (b j / 134217728 / 8 % 2)
  | 37 => b j % 134217728
  | 38 => if a j / 134217728 = b j / 134217728 then 0 else 1
  | 39 => if a j / 134217728 = b j / 134217728 then b j % 134217728 - a j % 134217728 - 1
          else b j / 134217728 - a j / 134217728 - 1
  | _ => 0

/-- **Completeness.** Canonical keys with `a <_lex b` admit a witness row satisfying the
whole block against the canonical trace family. -/
theorem lexLt8_complete (a b : Fin 8 → ℤ)
    (ha : ∀ i : Fin 8, 0 ≤ a i ∧ a i < 2013265921)
    (hb : ∀ i : Fin 8, 0 ≤ b i ∧ b i < 2013265921)
    (hlt : toLex a < toLex b) :
    ∃ env : VmRowEnv, (∀ i : Fin 8, env.loc i.val = a i)
      ∧ (∀ i : Fin 8, env.loc (8 + i.val) = b i)
      ∧ lexBlockHolds lexTf env := by
  obtain ⟨j, hpre, hjlt⟩ := hlt
  have haj := ha j
  have hbj := hb j
  refine ⟨⟨wAsg a b j, wAsg a b j, wAsg a b j⟩, ?_, ?_, ?_⟩
  · intro i; fin_cases i <;> rfl
  · intro i; fin_cases i <;> rfl
  simp only [lexBlockHolds, lexLt8Constraints, List.forall_mem_cons,
    VmConstraint2.holdsAt, VmConstraint.holdsVm, Lookup.holdsAt,
    gBool, gOneHot, gPre0, gPre1, gPre2, gPre3, gPre4, gPre5, gPre6,
    gPairAP, gPairAQ, gPairBP, gPairBQ, gTopA, gTopB, gDecompA, gDecompB, gHiEq, gDelta,
    eS, ePre0, ePre1, ePre2, ePre3, ePre4, ePre5, ePre6, eSelA, eSelB, eHiA, eHiB,
    eOneMinus, eSub, lkALo, lkBLo, lkDelta,
    EmittedExpr.eval, List.map_cons, List.map_nil, wAsg]
  have hpre' : ∀ m : Fin 8, m < j → a m = b m := hpre
  have hjlt' : a j < b j := hjlt
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- s-booleanity (8)
  · apply eqToModEq
    by_cases hq : j.val = 0
    · rw [if_pos hq]; norm_num
    · rw [if_neg hq]; norm_num
  · apply eqToModEq
    by_cases hq : j.val = 1
    · rw [if_pos hq]; norm_num
    · rw [if_neg hq]; norm_num
  · apply eqToModEq
    by_cases hq : j.val = 2
    · rw [if_pos hq]; norm_num
    · rw [if_neg hq]; norm_num
  · apply eqToModEq
    by_cases hq : j.val = 3
    · rw [if_pos hq]; norm_num
    · rw [if_neg hq]; norm_num
  · apply eqToModEq
    by_cases hq : j.val = 4
    · rw [if_pos hq]; norm_num
    · rw [if_neg hq]; norm_num
  · apply eqToModEq
    by_cases hq : j.val = 5
    · rw [if_pos hq]; norm_num
    · rw [if_neg hq]; norm_num
  · apply eqToModEq
    by_cases hq : j.val = 6
    · rw [if_pos hq]; norm_num
    · rw [if_neg hq]; norm_num
  · apply eqToModEq
    by_cases hq : j.val = 7
    · rw [if_pos hq]; norm_num
    · rw [if_neg hq]; norm_num
  -- one-hot
  · exact eqToModEq (by linear_combination sel_one j)
  -- prefix gates (7)
  · apply eqToModEq
    rcases Nat.lt_or_ge 0 j.val with hk | hk
    · rw [hpre' 0 (by rw [Fin.lt_def]; simpa using hk)]; ring
    · rw [preSum0 j (by omega)]; ring
  · apply eqToModEq
    rcases Nat.lt_or_ge 1 j.val with hk | hk
    · rw [hpre' 1 (by rw [Fin.lt_def]; simpa using hk)]; ring
    · rw [preSum1 j (by omega)]; ring
  · apply eqToModEq
    rcases Nat.lt_or_ge 2 j.val with hk | hk
    · rw [hpre' 2 (by rw [Fin.lt_def]; simpa using hk)]; ring
    · rw [preSum2 j (by omega)]; ring
  · apply eqToModEq
    rcases Nat.lt_or_ge 3 j.val with hk | hk
    · rw [hpre' 3 (by rw [Fin.lt_def]; simpa using hk)]; ring
    · rw [preSum3 j (by omega)]; ring
  · apply eqToModEq
    rcases Nat.lt_or_ge 4 j.val with hk | hk
    · rw [hpre' 4 (by rw [Fin.lt_def]; simpa using hk)]; ring
    · rw [preSum4 j (by omega)]; ring
  · apply eqToModEq
    rcases Nat.lt_or_ge 5 j.val with hk | hk
    · rw [hpre' 5 (by rw [Fin.lt_def]; simpa using hk)]; ring
    · rw [preSum5 j (by omega)]; ring
  · apply eqToModEq
    rcases Nat.lt_or_ge 6 j.val with hk | hk
    · rw [hpre' 6 (by rw [Fin.lt_def]; simpa using hk)]; ring
    · rw [preSum6 j (by omega)]; ring
  -- hi-bit booleanity (8)
  · exact eqToModEq (bit_gate (a j / 134217728))
  · exact eqToModEq (bit_gate (a j / 134217728 / 2))
  · exact eqToModEq (bit_gate (a j / 134217728 / 4))
  · exact eqToModEq (bit_gate (a j / 134217728 / 8))
  · exact eqToModEq (bit_gate (b j / 134217728))
  · exact eqToModEq (bit_gate (b j / 134217728 / 2))
  · exact eqToModEq (bit_gate (b j / 134217728 / 4))
  · exact eqToModEq (bit_gate (b j / 134217728 / 8))
  -- pair columns (4)
  · exact eqToModEq (by ring)
  · exact eqToModEq (by ring)
  · exact eqToModEq (by ring)
  · exact eqToModEq (by ring)
  -- the p-boundary gates (2)
  · exact eqToModEq (top_gate (a j) haj.1 haj.2)
  · exact eqToModEq (top_gate (b j) hbj.1 hbj.2)
  -- decompositions (2)
  · apply eqToModEq
    have hsel := sel_collapse a j
    have hhi := hi_recombine (a j) haj.1 haj.2
    have hsplit : 134217728 * (a j / 134217728) + a j % 134217728 = a j := by omega
    linear_combination hsel - 134217728 * hhi - hsplit
  · apply eqToModEq
    have hsel := sel_collapse b j
    have hhi := hi_recombine (b j) hbj.1 hbj.2
    have hsplit : 134217728 * (b j / 134217728) + b j % 134217728 = b j := by omega
    linear_combination hsel - 134217728 * hhi - hsplit
  -- branch-bit booleanity
  · apply eqToModEq
    by_cases hq : a j / 134217728 = b j / 134217728
    · rw [if_pos hq]; norm_num
    · rw [if_neg hq]; norm_num
  -- hi-equality under t = 0
  · apply eqToModEq
    have hhiA := hi_recombine (a j) haj.1 haj.2
    have hhiB := hi_recombine (b j) hbj.1 hbj.2
    by_cases hq : a j / 134217728 = b j / 134217728
    · rw [if_pos hq]
      linear_combination hhiA - hhiB + hq
    · rw [if_neg hq]
      ring
  -- the strict-difference gate
  · apply eqToModEq
    have hhiA := hi_recombine (a j) haj.1 haj.2
    have hhiB := hi_recombine (b j) hbj.1 hbj.2
    by_cases hq : a j / 134217728 = b j / 134217728
    · rw [if_pos hq, if_pos hq]
      ring
    · rw [if_neg hq, if_neg hq]
      linear_combination hhiB - hhiA
  -- the three range lookups
  · rw [lexTf_range]
    exact mem_range27 (by omega) (by omega)
  · rw [lexTf_range]
    exact mem_range27 (by omega) (by omega)
  · rw [lexTf_range]
    by_cases hq : a j / 134217728 = b j / 134217728
    · rw [if_pos hq]
      exact mem_range27 (by omega) (by omega)
    · rw [if_neg hq]
      exact mem_range27 (by omega) (by omega)
  -- the exhausted tail
  · intro x hx
    exact absurd hx (by simp)

/-! ## §6 — `lexLt8_refines`: the iff, both directions. -/

/-- **The refinement, both directions.** For canonical 8-felt keys, the block is satisfiable
with those key cells IFF `a <_lex b` at `Lex (Fin 8 → ℤ)` — the spike's `Digest8Key` order
(felt 0 most significant), so `sorted_gap_excludes_digest8` / `imtAbsentK_excludes_digest8`
compose with this gadget with zero new bracketing math. -/
theorem lexLt8_refines (a b : Fin 8 → ℤ)
    (ha : ∀ i : Fin 8, 0 ≤ a i ∧ a i < 2013265921)
    (hb : ∀ i : Fin 8, 0 ≤ b i ∧ b i < 2013265921) :
    (∃ env : VmRowEnv, (∀ i : Fin 8, env.loc i.val = a i)
        ∧ (∀ i : Fin 8, env.loc (8 + i.val) = b i)
        ∧ lexBlockHolds lexTf env)
      ↔ toLex a < toLex b := by
  constructor
  · rintro ⟨env, hka, hkb, hblock⟩
    have hcanon : LexCanon env := by
      intro k hk
      rcases Nat.lt_or_ge k 8 with h8 | h8
      · have hk' : env.loc k = a ⟨k, h8⟩ := hka ⟨k, h8⟩
        rw [hk']
        exact ha ⟨k, h8⟩
      · have hk8 : k - 8 < 8 := by omega
        have hk' : env.loc (8 + (k - 8)) = b ⟨k - 8, hk8⟩ := hkb ⟨k - 8, hk8⟩
        have h8' : 8 + (k - 8) = k := by omega
        rw [h8'] at hk'
        rw [hk']
        exact hb ⟨k - 8, hk8⟩
    have hlt := lexLt8_sound lexTf lexTf_range env hcanon hblock
    have hA : lexKeyA env = a := funext fun i => hka i
    have hB : lexKeyB env = b := funext fun i => hkb i
    rwa [hA, hB] at hlt
  · intro hlt
    exact lexLt8_complete a b ha hb hlt

/-! ## §7 — Teeth. The accept side runs a NON-lane-0 decider (limb 5) with a full-felt
`p − 1` limb inside the EQUAL prefix and the `hi = 15 / lo = 0` boundary split exercised on
the b-side; a limb-7-only pair kills any lane-0 masquerade; the reject side refuses EVERY
witness (via soundness), not one fixture. -/

/-- Tooth key A: `(42, 0, p−1, 314159, 2^30, 1500, 7, 9)`. -/
def toothA : Fin 8 → ℤ := fun i =>
  if i.val = 0 then 42 else if i.val = 1 then 0 else if i.val = 2 then 2013265920
  else if i.val = 3 then 314159 else if i.val = 4 then 1073741824
  else if i.val = 5 then 1500 else if i.val = 6 then 7 else 9

/-- Tooth key B: equal to A on limbs 0–4, `p − 1` at limb 5 (the decider), free suffix. -/
def toothB : Fin 8 → ℤ := fun i =>
  if i.val = 0 then 42 else if i.val = 1 then 0 else if i.val = 2 then 2013265920
  else if i.val = 3 then 314159 else if i.val = 4 then 1073741824
  else if i.val = 5 then 2013265920 else if i.val = 6 then 3 else 9

theorem toothA_canon : ∀ i : Fin 8, 0 ≤ toothA i ∧ toothA i < 2013265921 := by decide
theorem toothB_canon : ∀ i : Fin 8, 0 ≤ toothB i ∧ toothB i < 2013265921 := by decide

/-- The reference order agrees: decided at limb 5, equal above. -/
theorem toothA_lt_toothB : toLex toothA < toLex toothB := by
  refine ⟨⟨5, by norm_num⟩, ?_, by decide⟩
  intro m hm
  fin_cases m <;> first | rfl | exact absurd hm (by decide)

/-- **★ ACCEPT (non-lane-0).** The limb-5-decided pair admits a satisfying row — the
constructive witness is `wAsg toothA toothB 5` (see the `#guard`s below computing the
gadget's cells and gate values on it). -/
theorem tooth_accepts_limb5 :
    ∃ env : VmRowEnv, (∀ i : Fin 8, env.loc i.val = toothA i)
      ∧ (∀ i : Fin 8, env.loc (8 + i.val) = toothB i)
      ∧ lexBlockHolds lexTf env :=
  lexLt8_complete toothA toothB toothA_canon toothB_canon toothA_lt_toothB

-- The witness COMPUTES through the gadget: the b-side decomposes at the p-boundary
-- (hi-bits all 1, lo = 0), the decider difference witness is 14 ∈ [0, 2^27), and the
-- decomposition / boundary / difference gate bodies all evaluate to field zeros.
#guard (wAsg toothA toothB 5) 31 == 1 && (wAsg toothA toothB 5) 32 == 1
  && (wAsg toothA toothB 5) 33 == 1 && (wAsg toothA toothB 5) 34 == 1
  && (wAsg toothA toothB 5) 37 == 0
#guard (wAsg toothA toothB 5) 30 == 1500 && (wAsg toothA toothB 5) 38 == 1
  && (wAsg toothA toothB 5) 39 == 14
#guard (gDecompA.eval (wAsg toothA toothB 5)) % 2013265921 == 0
#guard (gDecompB.eval (wAsg toothA toothB 5)) % 2013265921 == 0
#guard (gTopA.eval (wAsg toothA toothB 5)) % 2013265921 == 0
#guard (gTopB.eval (wAsg toothA toothB 5)) % 2013265921 == 0
#guard (gHiEq.eval (wAsg toothA toothB 5)) % 2013265921 == 0
#guard (gDelta.eval (wAsg toothA toothB 5)) % 2013265921 == 0
-- …and on the REVERSED pair the honest difference witness falls OUT of the range table
-- (delta = −16): the lookup leg is what refuses the swap.
#guard decide (¬ (0 ≤ (wAsg toothB toothA 5) 39))

/-- Lane-0-masquerade killer: a pair differing ONLY at the LAST limb (felt 7). -/
def tail7A : Fin 8 → ℤ := fun _ => 0
/-- `(0,…,0,1)` — greater than `tail7A` only at felt 7. -/
def tail7B : Fin 8 → ℤ := fun i => if i.val = 7 then 1 else 0

theorem tail7_lt : toLex tail7A < toLex tail7B := by
  refine ⟨⟨7, by norm_num⟩, ?_, by decide⟩
  intro m hm
  fin_cases m <;> first | rfl | exact absurd hm (by decide)

/-- **★ ACCEPT (limb 7 only).** The least-significant-limb decider also has a witness — the
gadget is genuinely 8-limb-deep, not a lane-0 (or any-prefix) disguise. -/
theorem tooth_accepts_limb7 :
    ∃ env : VmRowEnv, (∀ i : Fin 8, env.loc i.val = tail7A i)
      ∧ (∀ i : Fin 8, env.loc (8 + i.val) = tail7B i)
      ∧ lexBlockHolds lexTf env :=
  lexLt8_complete tail7A tail7B (by decide) (by decide) tail7_lt

/-- **★ REJECT (equal keys, EVERY witness).** No row carrying equal canonical keys
satisfies the block: equality has no deciding limb for the one-hot selector to name. -/
theorem lexLt8_rejects_equal (env : VmRowEnv) (hcanon : LexCanon env)
    (heq : ∀ i : Fin 8, env.loc i.val = env.loc (8 + i.val)) :
    ¬ lexBlockHolds lexTf env := by
  intro h
  have hlt := lexLt8_sound lexTf lexTf_range env hcanon h
  have hAB : lexKeyA env = lexKeyB env := funext heq
  rw [hAB] at hlt
  obtain ⟨i, _, hii⟩ := hlt
  exact lt_irrefl _ hii

/-- **★ REJECT (lex-larger pair, EVERY witness).** No row carrying `(toothB, toothA)` — the
strictly larger key on the a-side — satisfies the block. -/
theorem tooth_rejects_reversed (env : VmRowEnv) (hcanon : LexCanon env)
    (hka : ∀ i : Fin 8, env.loc i.val = toothB i)
    (hkb : ∀ i : Fin 8, env.loc (8 + i.val) = toothA i) :
    ¬ lexBlockHolds lexTf env := by
  intro h
  have hlt := lexLt8_sound lexTf lexTf_range env hcanon h
  have hA : lexKeyA env = toothB := funext fun i => hka i
  have hB : lexKeyB env = toothA := funext fun i => hkb i
  rw [hA, hB] at hlt
  exact lt_asymm toothA_lt_toothB hlt

/-! ## §8 — CANARY: the `p`-boundary gate is LOAD-BEARING.

`p = 15·2^27 + 1`, so without the `hi = 15 ⟹ lo = 0` exclusion every felt `x < 2^27 − 1`
has a SECOND decomposition `x ≡ 2^27·15 + (x+1) [ZMOD p]` and an adversary can order-swap
keys at will. The forged row below "proves" `0 <_lex 0` by decomposing the b-side zero as
`(15, 1)`: it satisfies EVERY constraint except `gTopB`, and `gTopB` alone refuses it. -/

/-- The forged witness: all-zero keys, decider limb 0, b-side decomposed as `p`'s digits. -/
def forgeAsg : Assignment := fun c =>
  match c with
  | 16 => 1
  | 31 => 1 | 32 => 1 | 33 => 1 | 34 => 1
  | 35 => 1 | 36 => 1
  | 37 => 1
  | 38 => 1
  | 39 => 14
  | _ => 0

-- Index 29 of the block IS the b-side boundary gate (the erasure below drops exactly it).
#guard lexLt8Constraints.length == 38

theorem topB_is_index_29 : lexLt8Constraints[29]? = some (.base (.gate gTopB)) := rfl

/-- The forged row satisfies the WHOLE block minus the b-side boundary gate… -/
theorem boundary_canary_others_hold :
    ∀ c ∈ lexLt8Constraints.eraseIdx 29,
      c.holdsAt (fun _ => 0) lexTf ⟨forgeAsg, forgeAsg, forgeAsg⟩ false false := by
  simp only [lexLt8Constraints, List.eraseIdx_cons_succ, List.eraseIdx_cons_zero,
    List.forall_mem_cons,
    VmConstraint2.holdsAt, VmConstraint.holdsVm, Lookup.holdsAt,
    gBool, gOneHot, gPre0, gPre1, gPre2, gPre3, gPre4, gPre5, gPre6,
    gPairAP, gPairAQ, gPairBP, gPairBQ, gTopA, gDecompA, gDecompB, gHiEq, gDelta,
    eS, ePre0, ePre1, ePre2, ePre3, ePre4, ePre5, ePre6, eSelA, eSelB, eHiA, eHiB,
    eOneMinus, eSub, lkALo, lkBLo, lkDelta,
    EmittedExpr.eval, List.map_cons, List.map_nil, forgeAsg]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    first
      | (rw [lexTf_range]; exact mem_range27 (by norm_num) (by norm_num))
      | (intro x hx; exact absurd hx (by simp))
      | decide

/-- …and the b-side boundary gate ALONE refuses it. -/
theorem boundary_canary_top_refuses :
    ¬ (VmConstraint2.base (.gate gTopB)).holdsAt (fun _ => 0) lexTf
      ⟨forgeAsg, forgeAsg, forgeAsg⟩ false false := by
  simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm, gTopB, EmittedExpr.eval, forgeAsg]
  decide

/-! ## §9 — Wire byte-pin + shape pins + axiom hygiene. -/

-- Structural pins (the Rust decode gate asserts the same shape on the decoded twin).
#guard lexLt8Descriptor.traceWidth == 40
#guard lexLt8Descriptor.piCount == 0
#guard lexLt8Descriptor.constraints.length == 38
#guard lexLt8Descriptor.tables.length == 1

/-- Exact emitted-wire golden. Generated once from `emitVmJson2 lexLt8Descriptor`; the Rust
side `include_str!`s these bytes verbatim when the sorted-tree AIR integration lands. -/
def LEX_LT8_GOLDEN : String :=
  "{\"name\":\"dregg-lex-lt8-digest8-v1\",\"ir\":2,\"trace_width\":40,\"public_input_count\":0,\"tables\":[{\"id\":32,\"name\":\"lex_range_27\",\"arity\":1,\"sem\":\"range\",\"bits\":27}],\"constraints\":[{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":16},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":16},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":17},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":17},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":18},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":18},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":19},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":19},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":20},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":20},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":21},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":21},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":22},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":22},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":23},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":23},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":16},\"r\":{\"t\":\"var\",\"v\":17}},\"r\":{\"t\":\"var\",\"v\":18}},\"r\":{\"t\":\"var\",\"v\":19}},\"r\":{\"t\":\"var\",\"v\":20}},\"r\":{\"t\":\"var\",\"v\":21}},\"r\":{\"t\":\"var\",\"v\":22}},\"r\":{\"t\":\"var\",\"v\":23}},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":16}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":0},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":8}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":16},\"r\":{\"t\":\"var\",\"v\":17}}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":9}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":16},\"r\":{\"t\":\"var\",\"v\":17}},\"r\":{\"t\":\"var\",\"v\":18}}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":10}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":16},\"r\":{\"t\":\"var\",\"v\":17}},\"r\":{\"t\":\"var\",\"v\":18}},\"r\":{\"t\":\"var\",\"v\":19}}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":3},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":11}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":16},\"r\":{\"t\":\"var\",\"v\":17}},\"r\":{\"t\":\"var\",\"v\":18}},\"r\":{\"t\":\"var\",\"v\":19}},\"r\":{\"t\":\"var\",\"v\":20}}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":4},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":12}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":16},\"r\":{\"t\":\"var\",\"v\":17}},\"r\":{\"t\":\"var\",\"v\":18}},\"r\":{\"t\":\"var\",\"v\":19}},\"r\":{\"t\":\"var\",\"v\":20}},\"r\":{\"t\":\"var\",\"v\":21}}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":5},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":13}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":16},\"r\":{\"t\":\"var\",\"v\":17}},\"r\":{\"t\":\"var\",\"v\":18}},\"r\":{\"t\":\"var\",\"v\":19}},\"r\":{\"t\":\"var\",\"v\":20}},\"r\":{\"t\":\"var\",\"v\":21}},\"r\":{\"t\":\"var\",\"v\":22}}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":6},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":14}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":24},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":24},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":25},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":25},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":26},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":26},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":27},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":27},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":31},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":31},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":33},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":33},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":34},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":34},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":28},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":24},\"r\":{\"t\":\"var\",\"v\":25}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":29},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":26},\"r\":{\"t\":\"var\",\"v\":27}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":35},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":31},\"r\":{\"t\":\"var\",\"v\":32}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":36},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":33},\"r\":{\"t\":\"var\",\"v\":34}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":28},\"r\":{\"t\":\"var\",\"v\":29}},\"r\":{\"t\":\"var\",\"v\":30}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":35},\"r\":{\"t\":\"var\",\"v\":36}},\"r\":{\"t\":\"var\",\"v\":37}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":16},\"r\":{\"t\":\"var\",\"v\":0}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":17},\"r\":{\"t\":\"var\",\"v\":1}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":18},\"r\":{\"t\":\"var\",\"v\":2}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":19},\"r\":{\"t\":\"var\",\"v\":3}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":20},\"r\":{\"t\":\"var\",\"v\":4}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":21},\"r\":{\"t\":\"var\",\"v\":5}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":22},\"r\":{\"t\":\"var\",\"v\":6}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":23},\"r\":{\"t\":\"var\",\"v\":7}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":134217728},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":24},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"var\",\"v\":25}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":4},\"r\":{\"t\":\"var\",\"v\":26}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":8},\"r\":{\"t\":\"var\",\"v\":27}}}}}},\"r\":{\"t\":\"var\",\"v\":30}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":16},\"r\":{\"t\":\"var\",\"v\":8}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":17},\"r\":{\"t\":\"var\",\"v\":9}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":18},\"r\":{\"t\":\"var\",\"v\":10}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":19},\"r\":{\"t\":\"var\",\"v\":11}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":20},\"r\":{\"t\":\"var\",\"v\":12}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":21},\"r\":{\"t\":\"var\",\"v\":13}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":22},\"r\":{\"t\":\"var\",\"v\":14}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":23},\"r\":{\"t\":\"var\",\"v\":15}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":134217728},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":31},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"var\",\"v\":32}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":4},\"r\":{\"t\":\"var\",\"v\":33}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":8},\"r\":{\"t\":\"var\",\"v\":34}}}}}},\"r\":{\"t\":\"var\",\"v\":37}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":38},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":38},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":38}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":24},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"var\",\"v\":25}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":4},\"r\":{\"t\":\"var\",\"v\":26}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":8},\"r\":{\"t\":\"var\",\"v\":27}}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":31},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"var\",\"v\":32}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":4},\"r\":{\"t\":\"var\",\"v\":33}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":8},\"r\":{\"t\":\"var\",\"v\":34}}}}}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":38},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":31},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"var\",\"v\":32}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":4},\"r\":{\"t\":\"var\",\"v\":33}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":8},\"r\":{\"t\":\"var\",\"v\":34}}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":24},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"var\",\"v\":25}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":4},\"r\":{\"t\":\"var\",\"v\":26}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":8},\"r\":{\"t\":\"var\",\"v\":27}}}}}}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":38}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":37},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":30}}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":39}}}}}},{\"t\":\"lookup\",\"table\":32,\"tuple\":[{\"t\":\"var\",\"v\":30}]},{\"t\":\"lookup\",\"table\":32,\"tuple\":[{\"t\":\"var\",\"v\":37}]},{\"t\":\"lookup\",\"table\":32,\"tuple\":[{\"t\":\"var\",\"v\":39}]}],\"hash_sites\":[],\"ranges\":[]}"

#guard emitVmJson2 lexLt8Descriptor == LEX_LT8_GOLDEN

theorem descriptor_has_block_shape :
    lexLt8Descriptor.constraints = lexLt8Constraints := rfl

#assert_axioms operand_pinned
#assert_axioms decider_lt
#assert_axioms lexLt8_sound
#assert_axioms lexLt8_complete
#assert_axioms lexLt8_refines
#assert_axioms tooth_accepts_limb5
#assert_axioms tooth_accepts_limb7
#assert_axioms lexLt8_rejects_equal
#assert_axioms tooth_rejects_reversed
#assert_axioms boundary_canary_others_hold
#assert_axioms boundary_canary_top_refuses
#assert_axioms descriptor_has_block_shape

end Dregg2.Circuit.Emit.LexCompare8Emit

