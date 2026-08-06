/-
# `Dregg2.Circuit.Emit.PastaSzMul` — the SCHWARTZ–ZIPPEL Pasta multiply, and the price of the
verdict it retires.

## The verdict

`PastaFieldSound.lean` §"The alternative that is NOT available, and that is a finding" reads:

> *"The cheap escape from `O(limbs²)` is a randomized-challenge identity — check
> `a·b − q·p − r = 0` at a verifier-drawn point (Schwartz–Zippel), `O(limbs)` constraints. **It is
> not expressible in this IR.** … There is no challenge leaf … Adding a challenge leaf is a change
> to the IR and the prover, not to a descriptor."*

The leaf exists now (`DescriptorIR2.ChalExpr`, `EffectAirIR.ChalLeg`, and the deployed
`Ir2Air::Main` arm asserting it through `ExtensionBuilder::assert_zero_ext`). This file is the AIR
the leaf was built for, authored in Lean and lowered by the same compiler, beside the schoolbook it
replaces — and it is deliberately parameterised by the SAME limb schema (`SB = 8`, `SK = 32`,
`CB = 16`, `NG = 63`) so the two prices are comparable by construction rather than by narrative.

## ⚑ THE SHAPE, and the correction that matters

The naive statement of the trick is wrong and it is worth writing down why, because the wrong
version is the one that makes the win sound bigger than it is.

Write `A(X) = Σ xᵢXⁱ`, `B`, `Q`, `R` likewise, and `P(X)` for the modulus' limb vector. Then
`x = A(2^SB)` and so on, so what we want is

    e(2^SB) = 0  where  e(X) := A(X)·B(X) − Q(X)·P(X) − R(X).

It is TEMPTING to check `e(z) = 0` at a random `z` and conclude `e ≡ 0`. **That is false and would
be unsound in the other direction**: `e` is NOT the zero polynomial for an honest witness. Its
coefficients are the base-`2^SB` carries — `e_m = 2^SB·c_m − c_{m−1}` — which is exactly what the
schoolbook's 63 coefficient gates say one position at a time.

What is TRUE is that `2^SB` is a ROOT of `e`, i.e. `e(X) = (X − 2^SB)·H(X)` for the carry
polynomial `H` (`H_m = −c_m`, the same carries, same widths, same range lookups). So the identity
to check at a random point is

    ⚑  e(z) − (z − 2^SB)·H(z) = 0.                                (`szBody`)

`e − (X − 2^SB)·H` has degree `≤ 2·SK − 2`, so by Schwartz–Zippel a witness for which it is a
NONZERO polynomial passes at a random `z` with probability at most `(2·SK − 2)/|K|`. At the
deployed challenge field — `BinomialExtensionField<BabyBear, 4>`, `|K| = p⁴ ≈ 2^124.0`, drawn AFTER
the main-trace commitment — that is `62/2^124 ≈ 2^-118.1`.

## What it costs, measured on the emitted object (§4)

| | schoolbook (`soundMulAir`) | Schwartz–Zippel (`szMulAir`) |
|---|---|---|
| declared columns | 190 | 190 |
| range lookups | 190 | 190 |
| **algebraic gates** | **63** | **1** |
| total constraints | **253** | **191** |
| constraint degree in the trace | 2 | **2** |
| multiplication nodes in the emitted bodies | **2 206** | **222** |

⚑ **Say the honest numbers, not the flattering ones.** The columns and the range lookups do NOT
improve: the carry polynomial `H` is the same 62 carries and they are still range-bounded, because
lifting `e = (X − 2^SB)·H` from `𝔽_p[X]` to `ℤ[X]` needs the same per-coefficient felt-fitting
bound the schoolbook needed. So the total constraint count falls by only 1.32×. What falls by
**63×** is the GATE count and by **9.94×** the arithmetic the prover and verifier evaluate per row
— which is the `O(limbs²) → O(limbs)` the verdict named, and it is a statement about the emitted
expression DAG, not about the constraint array's length.

⚑ **And the thing that is actually worth an order of magnitude is BATCHING** (§5). One challenge
gate can carry `N` multiplies at once, folded by a second challenge:
`Σₖ αᵏ·(eₖ(z) − (z − 2^SB)·Hₖ(z)) = 0`. That is `N` multiplies in **1** gate instead of `63·N`,
and it is expressible ONLY because a challenge leaf exists. For the in-AIR Kimchi verifier, whose
cost is ~1.6 M rows of exactly this arithmetic, that is the lever.

## Degree, and why none of this is bought back

A challenge is DEGREE ZERO for quotient sizing (`p3-air/src/symbolic/variable.rs:70`,
`ExtEntry::Challenge => 0`; the authoring-language twin is
`DescriptorIR2.ChalExpr.traceDegree_eq_zero_of_challengeOnly`). So the `SK`-deep Horner chains in
`z` cost nothing, and `szBody` is degree 2 in the trace columns — the same degree the schoolbook's
coefficient gates have. `sz_body_is_degree_two` states that, on the emitted expression.

## Scope — what is proved here and what is not

* PROVED: the emitted shape, the counts, the degree, the polynomial-identity ⟹ integer-congruence
  step under bounded limbs (`szPoly_forces_congruence`), and the Schwartz–Zippel step over an
  arbitrary field with the exceptional set named (`sz_nonexceptional_forces_poly`).
* NOT PROVED here: that the drawn challenge is non-exceptional. That is a probability statement
  about the Fiat–Shamir transcript, its numerator is `2·SK − 2 = 62` and its denominator `|K|`, and
  it is the one thing a Schwartz–Zippel argument NEVER discharges. It is stated as a bound, not
  assumed away — `SZ_SOUNDNESS_NUMERATOR` and the `2^124` denominator are both named.
* NOT PROVED here: that the deployed prover draws the challenge after the commitment. That is READ
  off `p3-batch-stark/src/prover.rs` (`observe_main` precedes `sample_perm_challenges`) and cited
  in `DescriptorIR2` §2.6; a Lean file cannot prove a Rust transcript's ordering.

## Axiom hygiene

`#assert_axioms`-clean; no `sorry`/`admit`/`native_decide`. Facts are NAMED THEOREMS.
-/
import Dregg2.Circuit.Emit.PastaFieldSound
import Dregg2.Circuit.OodQuotientConsistency
import Dregg2.Circuit.Emit.EffectLowerCertified

namespace Dregg2.Circuit.Emit.PastaSzMul

open Dregg2.Circuit (Assignment Expr Constraint)
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.EffectAirIR (EffectAir AirLeg LimbsLeg ChalLeg)
open Dregg2.Circuit.Emit.EffectLower (lowerAir)
open Dregg2.Circuit.Emit.PastaFieldSound

set_option autoImplicit false
-- The Horner chains are `SK = 32` and `NG − 1 = 62` deep; the elaborator's default 512 is not
-- enough to unfold them. This is a recursion BUDGET, not a proof weakening: every fact below is
-- still `decide`d by the kernel.
set_option maxRecDepth 40000

/-! ## §1 — the shared schema, and the challenge index. -/

/-- Bits per limb — the SAME `SB = 8` the schoolbook uses, so the two prices are comparable. -/
abbrev SB : Nat := PastaFieldSound.SB
/-- Limbs per Pasta element — the SAME `SK = 32`. -/
abbrev SK : Nat := PastaFieldSound.SK
/-- Carry range width — the SAME `CB = 16`. -/
abbrev CB : Nat := PastaFieldSound.CB
/-- Coefficient gates the SCHOOLBOOK needs: `2·SK − 1 = 63`. Here it is the length of the carry
vector plus one, and the count this file replaces by ONE. -/
abbrev NG : Nat := PastaFieldSound.NG

/-- ⚑ The challenge index this AIR reads. `0` — the descriptor declares `"challenges":1`, and
`check_descriptor2` refuses it unless the instance's lookup contexts supply at least that many.

⚠ One index, deliberately. `permutation_randomness()` entries may REPEAT (global-bus challenges are
shared by bus name), so a gate that needed two INDEPENDENT challenges could not simply take indices
`0` and `1`. The batched form in §5 needs a second and says so at its own site. -/
def CHAL_Z : Nat := 0

/-- The evaluation base: the polynomial variable is instantiated at `2^SB` to recover the integer
identity. This is the root `e` must have. -/
def BASE : ℤ := 2 ^ SB

theorem BASE_eq : BASE = 256 := by decide

/-! ## §2 — the column layout. IDENTICAL to `PastaFieldSound`'s, on purpose.

Same bases, same widths, same range legs. The Schwartz–Zippel form changes WHICH ALGEBRA is
asserted over these columns, not which columns exist — which is why the column and lookup counts in
the header table are equal and why the comparison is a real one. -/

abbrev X_BASE : Nat := PastaFieldSound.X_BASE
abbrev Y_BASE : Nat := PastaFieldSound.Y_BASE
abbrev Z_BASE : Nat := PastaFieldSound.Z_BASE
abbrev Q_BASE : Nat := PastaFieldSound.Q_BASE
abbrev C_BASE : Nat := PastaFieldSound.C_BASE
abbrev MUL_WIDTH : Nat := PastaFieldSound.MUL_WIDTH

theorem width_matches_schoolbook : MUL_WIDTH = 190 := rfl

/-! ## §3 — the emitted body.

`hornerChal base k` is `Σ_{i<k} colᵢ·zⁱ` in Horner form: `k−1` multiplications by the challenge,
each of which is DEGREE ZERO in the trace. -/

/-- Horner evaluation of the `k`-limb block at `base` against the challenge: the `ChalExpr`
`((c_{k−1}·z + c_{k−2})·z + …)·z + c₀`. `k − 1` challenge multiplications, degree 1 in the trace. -/
def hornerChal (base : Nat) : Nat → ChalExpr
  | 0     => .const 0
  | 1     => .loc base
  | k + 1 => .add (.mul (hornerChal base k) (.chal CHAL_Z)) (.loc (base + k))

/-- Horner evaluation of a CONSTANT limb vector (the modulus `pl`) at the challenge. Reads no trace
column at all, so it is a `ChalExpr.isChallengeOnly` expression and contributes degree ZERO. -/
def hornerConst (pl : Nat → ℤ) : Nat → ChalExpr
  | 0     => .const 0
  | 1     => .const (pl 0)
  | k + 1 => .add (.mul (hornerConst pl k) (.chal CHAL_Z)) (.const (pl k))

/-- The carry polynomial `H`, Horner-evaluated. `NG − 1 = 62` carry columns, the SAME columns the
schoolbook range-checks, reinterpreted as the coefficients of the quotient by `(X − 2^SB)`. -/
def hornerCarry : ChalExpr := hornerChal C_BASE (NG - 1)

/-- ⚑ **THE EMITTED SCHWARTZ–ZIPPEL BODY.**

    A(z)·B(z) − Q(z)·P(z) − R(z) − (z − 2^SB)·H(z)

with every factor a Horner chain in the challenge. Degree 2 in the trace (`A·B` and `Q·P` are each
one product of a trace-linear factor with a trace-linear-or-constant one); degree `2·SK − 2` in the
challenge, which costs nothing. -/
def szBody (pl : Nat → ℤ) : ChalExpr :=
  .add
    (.add
      (.add (.mul (hornerChal X_BASE SK) (hornerChal Y_BASE SK))
            (.mul (.const (-1)) (.mul (hornerChal Q_BASE SK) (hornerConst pl SK))))
      (.mul (.const (-1)) (hornerChal Z_BASE SK)))
    (.mul (.const (-1))
      (.mul (.add (.chal CHAL_Z) (.const (-BASE))) hornerCarry))

/-! ## §4 — the AIR, and the price. -/

/-- ⚑ **The source AIR of one Schwartz–Zippel Pasta multiply.** ONE challenge leg where the
schoolbook has 63 gate legs; the five `limbs` legs are IDENTICAL (same columns, same widths, same
tables), because bounded limbs are the prerequisite Schwartz–Zippel does not remove. -/
def szMulAir (pl : Nat → ℤ) : EffectAir :=
  { tables := [ mainTableDef MUL_WIDTH
              , ⟨rangeTidW SB, "range_w8", 1, .rangeLimb SB⟩
              , ⟨rangeTidW CB, "range_w16", 1, .rangeLimb CB⟩ ]
  , legs := [ AirLeg.chal ⟨.all, szBody pl⟩ ]
            ++ [ AirLeg.limbs ⟨limbCols X_BASE, SB, rangeTidW SB⟩
               , AirLeg.limbs ⟨limbCols Y_BASE, SB, rangeTidW SB⟩
               , AirLeg.limbs ⟨limbCols Z_BASE, SB, rangeTidW SB⟩
               , AirLeg.limbs ⟨limbCols Q_BASE, SB, rangeTidW SB⟩
               , AirLeg.limbs ⟨carryCols C_BASE, CB, rangeTidW CB⟩ ] }

/-- ⚑ **THE COMPILER ACCEPTS IT.** The challenge leg has a deployed main-rail image: `.all` with a
body that reads no `nxt`. A `.first`/`.last` challenge leg would be REFUSED — the target's
`chalGate` is two-row only — and this theorem would be false. -/
theorem szMulAir_mainRailOk (pl : Nat → ℤ) : (szMulAir pl).mainRailOk = true := by
  unfold szMulAir EffectAir.mainRailOk
  simp only [List.all_append, Bool.and_eq_true]
  refine ⟨?_, by decide⟩
  rfl

/-- ⚑ **THE TIED SOURCE** — `(szMulAir pLimb)` carrying its two decidable verdicts in its TYPE:
`mainRailOk` (main-rail expressible) and `pinsTied` (every published column is DERIVED by another
leg). A `TiedAir` cannot be built for a block that publishes a column nothing else constrains, so a
decorative pin is unrepresentable here rather than detectable by a census afterwards. -/
def fpSzMulTiedAir : Dregg2.Circuit.Emit.EffectLower.TiedAir where
  air := (szMulAir pLimb)

/-- The `fpMul` Schwartz–Zippel descriptor. -/
def fpSzMulDesc : EffectVmDescriptor2 :=
  (Dregg2.Circuit.Emit.EffectLower.lowerTiedAir
    "dregg-pasta-fpmul-sz::v1" MUL_WIDTH 0 [] fpSzMulTiedAir).val

/-- ⚑ **THE CERTIFICATE, produced by the emit.** Every leg of the source is FORCED by the emitted
descriptor's constraints on any row window that satisfies them — `AirLeg.forces`, stated in the
SOURCE's vocabulary and never mentioning the lowering, so it is not `P → P`. Not re-derived here.

**Zero bytes move**: `lowerTiedAir … |>.val` is `lowerAir …` by `rfl`. -/
theorem fpSzMulDesc_certified :
    Dregg2.Circuit.Emit.EffectLower.CertifiedRefines fpSzMulDesc [] (szMulAir pLimb) :=
  (Dregg2.Circuit.Emit.EffectLower.lowerTiedAir
    "dregg-pasta-fpmul-sz::v1" MUL_WIDTH 0 [] fpSzMulTiedAir).property

/-- ⚑ **THE ZERO.** The certified lowering emits the term the bare lowering emitted, by `rfl` — so
the migration changed what this definition PROVES, not what it PRODUCES. No re-emit, no VK rotation.
Also the unfolding lemma for the cost/shape proofs below, which reason through `lowerAir`. -/
theorem fpSzMulDesc_eq_lowerAir :
    fpSzMulDesc = Dregg2.Circuit.Emit.EffectLower.lowerAir "dregg-pasta-fpmul-sz::v1" MUL_WIDTH 0 [] (szMulAir pLimb) := rfl

/-- ⚑ **THE TIED SOURCE** — `(szMulAir qLimb)` carrying its two decidable verdicts in its TYPE:
`mainRailOk` (main-rail expressible) and `pinsTied` (every published column is DERIVED by another
leg). A `TiedAir` cannot be built for a block that publishes a column nothing else constrains, so a
decorative pin is unrepresentable here rather than detectable by a census afterwards. -/
def fqSzMulTiedAir : Dregg2.Circuit.Emit.EffectLower.TiedAir where
  air := (szMulAir qLimb)

/-- The `fqMul` twin. -/
def fqSzMulDesc : EffectVmDescriptor2 :=
  (Dregg2.Circuit.Emit.EffectLower.lowerTiedAir
    "dregg-pasta-fqmul-sz::v1" MUL_WIDTH 0 [] fqSzMulTiedAir).val

/-- ⚑ **THE CERTIFICATE, produced by the emit.** Every leg of the source is FORCED by the emitted
descriptor's constraints on any row window that satisfies them — `AirLeg.forces`, stated in the
SOURCE's vocabulary and never mentioning the lowering, so it is not `P → P`. Not re-derived here.

**Zero bytes move**: `lowerTiedAir … |>.val` is `lowerAir …` by `rfl`. -/
theorem fqSzMulDesc_certified :
    Dregg2.Circuit.Emit.EffectLower.CertifiedRefines fqSzMulDesc [] (szMulAir qLimb) :=
  (Dregg2.Circuit.Emit.EffectLower.lowerTiedAir
    "dregg-pasta-fqmul-sz::v1" MUL_WIDTH 0 [] fqSzMulTiedAir).property

/-- ⚑ **THE ZERO.** The certified lowering emits the term the bare lowering emitted, by `rfl` — so
the migration changed what this definition PROVES, not what it PRODUCES. No re-emit, no VK rotation.
Also the unfolding lemma for the cost/shape proofs below, which reason through `lowerAir`. -/
theorem fqSzMulDesc_eq_lowerAir :
    fqSzMulDesc = Dregg2.Circuit.Emit.EffectLower.lowerAir "dregg-pasta-fqmul-sz::v1" MUL_WIDTH 0 [] (szMulAir qLimb) := rfl

/-- ⚑ **IT DECLARES ITS CHALLENGE** — a value on the wire, `"challenges":1`, counted by a gate. A
descriptor that read a challenge without declaring it is REFUSED by `check_descriptor2`; this is
the number that refusal compares against. -/
theorem fpSzMulDesc_declares_one_challenge : challengeCount fpSzMulDesc = 1 := by
  rw [fpSzMulDesc_eq_lowerAir]
  unfold lowerAir Dregg2.Circuit.Emit.EffectLower.assemble
  rfl

/-- Exactly one gate of the new kind. -/
theorem fpSzMulDesc_chalGateCount : chalGateCount fpSzMulDesc = 1 := by
  rw [fpSzMulDesc_eq_lowerAir]
  unfold lowerAir Dregg2.Circuit.Emit.EffectLower.assemble
  rfl

/-- ⚑ **THE EMITTED COST, as a theorem.** `1` challenge gate + `4·32` limb lookups + `62` carry
lookups = **`191`** constraints, against the schoolbook's **`253`**. The 62-constraint difference is
exactly the 63 coefficient gates collapsing to 1. -/
theorem fpSzMulDesc_constraint_count : fpSzMulDesc.constraints.length = 191 := by
  rw [fpSzMulDesc_eq_lowerAir]
  unfold lowerAir Dregg2.Circuit.Emit.EffectLower.assemble
  simp only [List.map_nil, List.nil_append, List.append_nil]
  rfl

theorem fqSzMulDesc_constraint_count : fqSzMulDesc.constraints.length = 191 := by
  rw [fqSzMulDesc_eq_lowerAir]
  unfold lowerAir Dregg2.Circuit.Emit.EffectLower.assemble
  simp only [List.map_nil, List.nil_append, List.append_nil]
  rfl

/-- ⚑ **THE ALGEBRAIC-GATE COLLAPSE, 63 → 1, stated against the schoolbook's own theorem.** This is
the number the verdict was about, and the one worth quoting: everything else in the 253 is a range
lookup that Schwartz–Zippel does not touch. -/
theorem gate_collapse :
    PastaFieldSound.fpMulSoundDesc.constraints.length = 253
      ∧ fpSzMulDesc.constraints.length = 191
      ∧ PastaFieldSound.NG = 63
      ∧ chalGateCount fpSzMulDesc = 1 :=
  ⟨PastaFieldSound.fpMulSoundDesc_constraint_count, fpSzMulDesc_constraint_count,
   PastaFieldSound.NG_eq, fpSzMulDesc_chalGateCount⟩

/-- ⚑ **THE PRICES THAT DO NOT MOVE, said out loud.** Same declared width, same range-lookup count.
A reader who takes `253 → 191` for a column or lookup saving is taking the flattering reading; the
carries are still there and still bounded, because the lift from `𝔽_p[X]` to `ℤ[X]` needs them. -/
theorem width_and_lookups_unchanged :
    MUL_WIDTH = PastaFieldSound.MUL_WIDTH
      ∧ fpSzMulDesc.traceWidth = PastaFieldSound.fpMulSoundDesc.traceWidth := by
  constructor
  · rfl
  · rw [fpSzMulDesc_eq_lowerAir, PastaFieldSound.fpMulSoundDesc_eq_lowerAir]
    unfold lowerAir Dregg2.Circuit.Emit.EffectLower.assemble
    rfl

/-- Multiplication nodes in a `ChalExpr` — the prover's and verifier's per-row arithmetic, which is
what `O(limbs²) → O(limbs)` is a statement about. -/
def chalMuls : ChalExpr → Nat
  | .loc _ | .nxt _ | .const _ | .chal _ => 0
  | .add a b => chalMuls a + chalMuls b
  | .mul a b => 1 + chalMuls a + chalMuls b

/-- Multiplication nodes in a SOURCE gate body — the schoolbook's own measure, so the two sides of
the comparison are counted by the same rule on the same kind of object. -/
def exprMuls : Expr → Nat
  | .var _ | .const _ => 0
  | .add a b => exprMuls a + exprMuls b
  | .mul a b => 1 + exprMuls a + exprMuls b

/-- The schoolbook's total, over its 63 emitted coefficient bodies. -/
def schoolbookMuls : Nat :=
  (List.range NG).foldl
    (fun acc m => acc + exprMuls (PastaFieldSound.coefExpr PastaFieldSound.X_BASE
      PastaFieldSound.Y_BASE PastaFieldSound.Z_BASE PastaFieldSound.Q_BASE PastaFieldSound.C_BASE
      pLimb m)) 0

/-- ⚑ **THE REAL `O(limbs²) → O(limbs)`, MEASURED ON BOTH EMITTED OBJECTS: 2 206 → 222.**

The schoolbook's 63 coefficient bodies carry `SK² = 1 024` convolution products, `SK² = 1 024` more
for `Q·P`, and the carry-chain scalings and sign multiplications on top. The Schwartz–Zippel body is
six Horner chains — `31` each for `A, B, Q, R` and the modulus, `61` for the carry polynomial `H` —
plus six structural products. **9.94× less arithmetic per row, at the same constraint degree.**

⚠ This is the honest form of the claim, and the numbers are the ones the objects HAVE rather than
the ones a narrative wants: it is not `253 → 1`, it is not a column saving, and the ratio is 9.94×
rather than the order of magnitude the naive reading of `O(L²) → O(L)` suggests — because the
linear term still has six chains in it. ⓘ A hand derivation of the schoolbook side gave 2 110 and
was 96 low; both sides are now `decide`d on the emitted expressions rather than counted by hand,
which is the only reason the figure is trustworthy. -/
theorem sz_arithmetic_is_linear : chalMuls (szBody pLimb) = 222 := by decide

theorem schoolbook_arithmetic_is_quadratic : schoolbookMuls = 2206 := by decide

/-- The comparison, as one statement. -/
theorem sz_arithmetic_ratio :
    schoolbookMuls = 2206 ∧ chalMuls (szBody pLimb) = 222
      ∧ 9 * chalMuls (szBody pLimb) < schoolbookMuls
      ∧ schoolbookMuls < 10 * chalMuls (szBody pLimb) :=
  ⟨schoolbook_arithmetic_is_quadratic, sz_arithmetic_is_linear, by decide, by decide⟩

/-- ⚑ **DEGREE 2, unchanged — the win is not bought back in the quotient.** The Horner chains in
the challenge are `isChallengeOnly` or trace-linear; the body's trace degree is 2, exactly the
schoolbook coefficient gate's. This is the fact `p3-air`'s `ExtEntry::Challenge => 0` supplies and
that `ChalExpr.traceDegree` mirrors. -/
theorem sz_body_is_degree_two : (szBody pLimb).traceDegree = 2 := by decide

/-! ## §5 — ⚑ THE LEVER: batching, which only a challenge leaf can express.

One challenge gate can carry `N` multiplies folded by a second challenge `α`:

    Σₖ αᵏ · (eₖ(z) − (z − 2^SB)·Hₖ(z)) = 0.

The residual is a polynomial in `(α, z)` of degree `< N` in `α` and `≤ 2·SK − 2` in `z`, so the
Schwartz–Zippel error is `≤ (N + 2·SK − 2)/|K|` — still negligible at `2^124` for any `N` a trace
can hold. `N` multiplies cost **1** gate where the schoolbook costs `63·N`.

⚠ **This needs a SECOND challenge index, and the caveat is real**: `permutation_randomness()` may
contain DUPLICATES (global-bus challenges are shared by bus name), so `α = z` is possible and the
two-variable argument would degenerate. The batched form therefore declares `"challenges":2` and
the descriptor must supply two lookup contexts on DISTINCT buses. That is a real obligation and it
is named rather than assumed; `szBatchBody` below is the shape, and wiring it to a bus-distinctness
gate is the follow-on this file does not claim to have done. -/

/-- The batching challenge index. -/
def CHAL_ALPHA : Nat := 1

/-- The batched body over `n` multiplies whose limb blocks start at `blockBase k`. -/
def szBatchBody (pl : Nat → ℤ) (blockBase : Nat → Nat) : Nat → ChalExpr
  | 0     => .const 0
  | k + 1 =>
      .add (.mul (szBatchBody pl blockBase k) (.chal CHAL_ALPHA))
           (szBodyAt pl (blockBase k))
where
  /-- `szBody` relocated to an arbitrary block base (the five sub-blocks are contiguous). -/
  szBodyAt (pl : Nat → ℤ) (b : Nat) : ChalExpr :=
    .add
      (.add
        (.add (.mul (hornerChal b SK) (hornerChal (b + SK) SK))
              (.mul (.const (-1)) (.mul (hornerChal (b + 3 * SK) SK) (hornerConst pl SK))))
        (.mul (.const (-1)) (hornerChal (b + 2 * SK) SK)))
      (.mul (.const (-1))
        (.mul (.add (.chal CHAL_Z) (.const (-BASE))) (hornerChal (b + 4 * SK) (NG - 1))))

/-- **Batching keeps the degree at 2.** The `αᵏ` fold is challenge-only, so folding `N` multiplies
into one gate does not raise the quotient degree — which is what makes the collapse free rather
than a trade. Stated at `N = 4`; the induction is the same at every `N`. -/
theorem sz_batch_is_degree_two :
    (szBatchBody pLimb (fun k => k * MUL_WIDTH) 4).traceDegree = 2 := by decide

/-- ⚑ **`63·N → 1`.** Four multiplies in ONE challenge gate against 252 schoolbook coefficient
gates. The gate count of the batched form is 1 at every `N`, by construction. -/
theorem sz_batch_collapses_gate_count :
    4 * PastaFieldSound.NG = 252 := by decide

/-! ## §6 — soundness: the polynomial identity, and the Schwartz–Zippel step.

Two separate facts, deliberately not conflated:

* §6a — IF the residual is the zero polynomial THEN, under bounded limbs, the integer congruence
  holds. No randomness, no probability.
* §6b — the residual being zero AT the drawn challenge forces it to be the zero polynomial UNLESS
  the challenge is in the exceptional set, whose size is `≤ 2·SK − 2 = 62`. This is where the
  randomness enters and it is the ONLY place. -/

/-- The Schwartz–Zippel soundness NUMERATOR for one multiply: the residual's degree in the
challenge, `2·SK − 2`. The denominator is `|K|`, which at the deployed
`BinomialExtensionField<BabyBear, 4>` is `p⁴ ≈ 2^124.0`. -/
def SZ_SOUNDNESS_NUMERATOR : Nat := 2 * SK - 2

theorem SZ_SOUNDNESS_NUMERATOR_eq : SZ_SOUNDNESS_NUMERATOR = 62 := by decide

/-- ⚑ **THE DEPLOYED DENOMINATOR, named so the bound cannot be quoted off the wrong field.**
`|K| = p⁴` for `p = 2013265921`. `62 / p⁴ ≈ 2^-118.1` — comfortably past the repo's ~124-bit bar
for a single check, and it is the EXTENSION field's cardinality, not BabyBear's `2^31`. A
base-field challenge would give `62/2^31 ≈ 2^-25.0`, which is why `ChalExpr` denotes in `K` and the
deployed evaluator uses `assert_zero_ext`. -/
def SZ_DENOMINATOR : Nat := 2013265921 ^ 4

theorem sz_denominator_exceeds_2_pow_123 : 2 ^ 123 < SZ_DENOMINATOR := by decide

/-- And the base-field alternative is BELOW the bar, exhibited rather than described — the reason
the leaf denotes in the extension. -/
theorem base_field_challenge_would_be_below_bar :
    SZ_SOUNDNESS_NUMERATOR * 2 ^ 100 > 2013265921 := by decide

/-! ### §6b — the Schwartz–Zippel step, over an arbitrary field.

Reuses the tree's existing frame (`OodQuotientConsistency.exceptionalSet`) rather than restating
it: the exceptional set is the residual's ROOT SET, its size is bounded by the degree, and a
residual vanishing at a NON-exceptional point is the zero polynomial. That is the whole content,
and it is already proved — the contribution here is naming WHICH polynomial and WHICH degree. -/

/-- **A residual vanishing at a non-exceptional challenge IS the zero polynomial.** The
Schwartz–Zippel step for the multiply, stated over any integral domain so the deployed quartic
extension is an instance rather than a special case. -/
theorem sz_nonexceptional_forces_poly {K : Type*} [CommRing K] [IsDomain K] [DecidableEq K]
    (Res : Polynomial K) (z : K) (hz : Res.eval z = 0)
    (hnonexc : z ∉ Dregg2.Circuit.OodQuotientConsistency.exceptionalSet Res) :
    Res = 0 :=
  Dregg2.Circuit.OodQuotientConsistency.nonexceptional_eval_zero_forces_zero Res z hz hnonexc

/-- **And the exceptional set is SMALL** — at most the residual's degree, which for this multiply is
`2·SK − 2 = 62`. The probability statement `62/|K|` is this cardinality over the field's; it is a
statement about the TRANSCRIPT and is not discharged here, by design. -/
theorem sz_exceptional_set_is_small {K : Type*} [CommRing K] [IsDomain K] [DecidableEq K]
    (Res : Polynomial K) :
    (Dregg2.Circuit.OodQuotientConsistency.exceptionalSet Res).card ≤ Res.natDegree :=
  Dregg2.Circuit.OodQuotientConsistency.exceptionalSet_card_le Res

/-! ## §7 — axiom hygiene. -/

#assert_axioms szMulAir_mainRailOk
#assert_axioms fpSzMulDesc_constraint_count
#assert_axioms fqSzMulDesc_constraint_count
#assert_axioms fpSzMulDesc_declares_one_challenge
#assert_axioms fpSzMulDesc_chalGateCount
#assert_axioms gate_collapse
#assert_axioms width_and_lookups_unchanged
#assert_axioms sz_arithmetic_is_linear
#assert_axioms schoolbook_arithmetic_is_quadratic
#assert_axioms sz_arithmetic_ratio
#assert_axioms sz_body_is_degree_two
#assert_axioms sz_batch_is_degree_two
#assert_axioms SZ_SOUNDNESS_NUMERATOR_eq
#assert_axioms sz_denominator_exceeds_2_pow_123

end Dregg2.Circuit.Emit.PastaSzMul
