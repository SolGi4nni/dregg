/-
# `Dregg2.Circuit.Emit.PastaSzMul` — the SCHWARTZ–ZIPPEL Pasta multiply, REPAIRED and PROVED.

## ⚑⚑ THE DEFECT THIS REVISION REPAIRS (2026-08-09), measured before any deployment

The previous revision of this file emitted a body that was **UNSATISFIABLE for every honest
witness**, by three independent defects, none caught by its own theorems (which pinned counts,
degree and Fiat–Shamir plumbing — everything except what the body SAYS):

1. **The carry offset was dropped.** The schoolbook stores carries OFFSET-ENCODED — a carry column
   holds `c + COFF`, `COFF = 2^15` (`PastaFieldSound.chainVal`, `:315`) — and `COFF` did not occur
   in this file at all. The old `hornerCarry` read the columns RAW.
2. **The carry term's sign was flipped.** The body subtracted `(z − 2^8)·H(z)`, so an in-range
   witness existed only when every true carry was `≤ 0`.
3. **The Horner direction contradicted its own docstring.** `hornerChal` recursed as
   `H(k+1) = H(k)·z + c_k` — innermost coefficient `c₀`, i.e. `Σ cᵢ z^(k−1−i)`, the REVERSED
   polynomial — while the docstring (and every consumer of the algebra) said `Σ cᵢ zⁱ`. Reversal at
   per-block lengths is incoherent: the products reverse at length 63 while the `R` block reverses
   at length 32, so the emitted body was not the evaluation of ANY carry-quotient residual.

**MEASURED** (2,000 random Pallas multiplies, exact integer arithmetic; probe re-run 2026-08-09):
every honest witness has a positive carry somewhere (2000/2000; max |carry| 2777 ≪ 2^15), the old
emitted body admits an in-range witness on **0/2000** instances even solving for the carry columns
directly, and the repaired body below vanishes IDENTICALLY in `z` on the schoolbook's own offset
columns on **2000/2000**. ⚑ Caught before deployment: no Rust consumer and no emitted JSON for
`dregg-pasta-fpmul-sz::v1` existed, so nothing re-emits and no VK rotates — the name is kept.

## The repaired shape

With `A, B, R, Q` the limb polynomials, `P` the modulus limb vector, and
`D(X) = Σₖ (colₖ − COFF)·Xᵏ` the OFFSET-DECODED carry polynomial read from the SAME columns the
schoolbook range-checks:

    szBody  =  A(z)·B(z) − Q(z)·P(z) − R(z) + (z − 2^8)·D(z),

all six chains FORWARD Horner (`Σ cᵢ zⁱ`). The residual polynomial's `m`-th coefficient is then
EXACTLY the schoolbook's `coefBody` — `[(X−256)·D]ₘ = Dₘ₋₁ − 256·Dₘ = chainVal m − 256·chainVal
(m+1)` — which is `szResidual_coeff`, proved, and the reason `szPoly_forces_congruence` (§6a) can
hand its conclusion to the already-proved, axiom-clean `felt_gates_force_congruence`.

## ⚑ TWO challenge gates, and why one is not enough — the ε ledger (§6d)

`|K| = 2013265921⁴ = 2^123.63` (not "2^124.0"; say the real bound). One gate per multiply is
`ε = 62/|K| = 2^−117.7` per check — but EVERY multiply in a wrap proof shares ONE per-instance
challenge, so the exceptional sets UNION: at the 588,732-multiply wrap workload that is
`ε_wrap = 588732·62/|K| = 2^−98.5`, **below this repo's own ~124-bit bar**. The repair is a SECOND
gate at an independent challenge: acceptance then needs the shared residual to vanish at TWO
independent points, `ε = (588732·62/|K|)² = 2^−197.0`, clearing the bar with margin (and still
clearing it at a 2^33-multiply census, `sz_two_point_bar_robust_to_census`). All four numbers are
NAMED THEOREMS in §6d, bracketed to the power of two rather than quoted.

⚠ Independence of the two draws is a REAL obligation, and the criterion is the MEASURED one:
`permutation_randomness()` entries `2k`/`2k+1` are one lookup context's `(α, β)` — two distinct
post-commitment samples — while entries of DIFFERENT contexts may be EQUAL (global-bus sharing;
and the deployed range realization puts every nibble limb on the ONE byte bus, so a "distinct
bus" criterion would be unsatisfiable here). `DescriptorIR2.chalIndicesDistinctOk` is that verdict
as a decidable refusal, and `fpSzMulDesc_chal_indices_distinct` discharges it on the emitted
descriptor at `(CHAL_Z, CHAL_Z2) = (0, 1)`.

## What it costs, measured on the emitted object (§4)

| | schoolbook (`soundMulAir`) | Schwartz–Zippel, two-point (`szMulAir`) |
|---|---|---|
| declared columns | 190 | 190 |
| range lookups | 190 | 190 |
| **algebraic gates** | **63** | **2** |
| total constraints | **253** | **192** |
| constraint degree in the trace | 2 | **2** |
| multiplication nodes in the emitted bodies | **2 206** | **442** (221 per gate) |

⚑ **Say the honest numbers.** Columns and range lookups do NOT improve — the carries survive and
stay range-bounded, because lifting `𝔽_p[X] → ℤ[X]` needs the same per-coefficient felt-fitting
bound the schoolbook needed. The win is 63 → 2 gates and 2 206 → 442 multiplication nodes per row
(4.99×; 9.94× per gate) — prover/verifier EVALUATION arithmetic and constraint count in recursion,
not trace size. Anyone selling sz as a trace-size fix is quoting the wrong currency.

## Scope — what is proved here and what is not

* PROVED: the emitted shape, counts, degree; the weld from the emitted body's FAITHFUL denotation
  (`ChalExpr.evalIn` over any `CommRing K` — what `assert_zero_ext` checks) to the residual
  polynomial (`szBodyAt_evalIn`); the polynomial-identity ⟹ integer-congruence step
  (`szPoly_forces_congruence`, via `felt_gates_force_congruence`); the end-to-end gate theorem
  consuming `ChalConstraint.holdsIn` at either of two independent draws
  (`fpSzMulDesc_two_point_forces`, `fqSzMulDesc_two_point_forces`); that the exact gates those
  theorems quantify over ARE constraints of the emitted descriptor
  (`fpSzMulDesc_carries_the_gates`); and the ε ledger.
* NOT PROVED here: that a drawn challenge is non-exceptional. That is the probability statement —
  numerator 62 per gate, denominator `|K| = 2^123.63`, and the two-gate form squares it — and it is
  the one thing a Schwartz–Zippel argument NEVER discharges. Stated as named bounds, not assumed.
* NOT PROVED here: the deployed transcript ordering (`observe_main` before
  `sample_perm_challenges`) and the per-context sampling structure. READ off
  `p3-batch-stark/src/{prover,transcript}.rs` (pinned rev `82cfad7`) and cited in `DescriptorIR2`
  §2.6; a Lean file cannot prove a Rust transcript's ordering.
* `SZ_WRAP_MULTIPLIES = 588732` is the wrap-workload census READ from the campaign brief, not
  re-derived here; the bar verdicts are additionally stated at a 2^33 ceiling so the conclusion
  survives that census being wrong by three orders of magnitude.

## Axiom hygiene

`#assert_axioms`-clean; no `sorry`/`admit`/`native_decide`. Facts are NAMED THEOREMS.
-/
import Dregg2.Circuit.Emit.PastaFieldSound
import Dregg2.Circuit.OodQuotientConsistency
import Dregg2.Circuit.ChalSchwartzZippel
import Dregg2.Circuit.Emit.EffectLowerCertified

namespace Dregg2.Circuit.Emit.PastaSzMul

open Dregg2.Circuit (Assignment Expr Constraint)
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.EffectAirIR (EffectAir AirLeg LimbsLeg ChalLeg)
open Dregg2.Circuit.Emit.EffectLower (lowerAir P)
open Dregg2.Circuit.Emit.EffectVmEmit (VmRowEnv)
open Dregg2.Circuit.Emit.PastaFieldSound
open Dregg2.Circuit.Emit.PastaField (pN qN)

set_option autoImplicit false
-- The Horner chains are `SK = 32` and `NG − 1 = 62` deep; the elaborator's default 512 is not
-- enough to unfold them. This is a recursion BUDGET, not a proof weakening: every fact below is
-- still `decide`d by the kernel.
set_option maxRecDepth 40000

/-! ## §1 — the shared schema, and the two challenge indices. -/

/-- Bits per limb — the SAME `SB = 8` the schoolbook uses, so the two prices are comparable. -/
abbrev SB : Nat := PastaFieldSound.SB
/-- Limbs per Pasta element — the SAME `SK = 32`. -/
abbrev SK : Nat := PastaFieldSound.SK
/-- Carry range width — the SAME `CB = 16`. -/
abbrev CB : Nat := PastaFieldSound.CB
/-- Coefficient gates the SCHOOLBOOK needs: `2·SK − 1 = 63`. Here it is the residual's coefficient
count, and the gate count this file replaces by TWO. -/
abbrev NG : Nat := PastaFieldSound.NG

/-- ⚑ The FIRST challenge index: `permutation_randomness()[0]`, the `α` of the instance's first
lookup context. The descriptor declares `"challenges":2` and `check_descriptor2` refuses it unless
the instance's lookup contexts supply at least that many. -/
def CHAL_Z : Nat := 0

/-- ⚑ The SECOND challenge index: `permutation_randomness()[1]`, the `β` of the SAME first lookup
context — two distinct post-commitment draws of one `sample_n_challenges(2)` call, whatever bus
that context rides. This is the pair `DescriptorIR2.chalIndicesDistinctOk` licenses, and the ONLY
kind it licenses: same-slot entries of different contexts can be the identical value (global-bus
sharing), and for this descriptor every context rides the one byte bus, so a distinct-bus pairing
does not even exist. Discharged on the emitted object at `fpSzMulDesc_chal_indices_distinct`. -/
def CHAL_Z2 : Nat := 1

/-- The evaluation base: the polynomial variable is instantiated at `2^SB` to recover the integer
identity. This is the root the raw residual `A·B − Q·P − R` must have. -/
def BASE : ℤ := 2 ^ SB

theorem BASE_eq : BASE = 256 := by decide

/-! ## §2 — the column layout. IDENTICAL to `PastaFieldSound`'s, on purpose.

Same bases, same widths, same range legs. The Schwartz–Zippel form changes WHICH ALGEBRA is
asserted over these columns, not which columns exist — which is why the column and lookup counts in
the header table are equal and why the comparison is a real one. In particular the carry columns
hold the SAME offset-encoded values `c + COFF` the schoolbook's honest witness generator
(`mulAsg`) writes; this file DECODES them (`− COFF`) instead of misreading them raw. -/

abbrev X_BASE : Nat := PastaFieldSound.X_BASE
abbrev Y_BASE : Nat := PastaFieldSound.Y_BASE
abbrev Z_BASE : Nat := PastaFieldSound.Z_BASE
abbrev Q_BASE : Nat := PastaFieldSound.Q_BASE
abbrev C_BASE : Nat := PastaFieldSound.C_BASE
abbrev MUL_WIDTH : Nat := PastaFieldSound.MUL_WIDTH

theorem width_matches_schoolbook : MUL_WIDTH = 190 := rfl

/-! ## §3 — the emitted body.

All chains are FORWARD Horner — `F(base, k) = c_base + z·F(base+1, k−1)`, so `hornerChal zi base k`
denotes `Σ_{i<k} col_{base+i}·zⁱ` (the docstring and the recursion now agree; the previous
revision's recursion was coefficient-reversed). `k − 1` challenge multiplications, degree ≤ 1 in
the trace. -/

/-- Forward Horner over a limb block: `Σ_{i<k} loc(base+i)·zⁱ`. -/
def hornerChal (zi : Nat) : Nat → Nat → ChalExpr
  | _,    0     => .const 0
  | base, 1     => .loc base
  | base, k + 2 => .add (.loc base) (.mul (.chal zi) (hornerChal zi (base + 1) (k + 1)))

/-- Forward Horner over a CONSTANT vector (the modulus limbs): `Σ_{i<k} pl(j+i)·zⁱ`. Reads no trace
column, so it is challenge-only and contributes degree ZERO. -/
def hornerConst (zi : Nat) (pl : Nat → ℤ) : Nat → Nat → ChalExpr
  | _, 0     => .const 0
  | j, 1     => .const (pl j)
  | j, k + 2 => .add (.const (pl j)) (.mul (.chal zi) (hornerConst zi pl (j + 1) (k + 1)))

/-- ⚑ Forward Horner with OFFSET-DECODED coefficients: `Σ_{i<k} (loc(base+i) − off)·zⁱ`. This is
how the carry columns are read — the schoolbook commits `c + COFF`, so the polynomial coefficient
is the column MINUS the offset. The previous revision read the columns raw, which is defect (1). -/
def hornerChalOff (zi : Nat) (off : ℤ) : Nat → Nat → ChalExpr
  | _,    0     => .const 0
  | base, 1     => .add (.loc base) (.const (-off))
  | base, k + 2 =>
      .add (.add (.loc base) (.const (-off)))
           (.mul (.chal zi) (hornerChalOff zi off (base + 1) (k + 1)))

/-- ⚑ **THE EMITTED SCHWARTZ–ZIPPEL BODY, at arbitrary block bases** (the emitted core uses the
one-multiply layout; the batched form and any adopting composed row relocate it):

    A(z)·B(z) − Q(z)·P(z) − R(z) + (z − 2^SB)·D(z),

`D` the offset-decoded carry polynomial. Degree 2 in the trace (`A·B` is the one degree-2 product);
degree `2·SK − 2 = 62` in the challenge, which costs nothing. -/
def szBodyAt (pl : Nat → ℤ) (zi xB yB zB qB cB : Nat) : ChalExpr :=
  .add
    (.add
      (.add (.mul (hornerChal zi xB SK) (hornerChal zi yB SK))
            (.mul (.const (-1)) (.mul (hornerChal zi qB SK) (hornerConst zi pl 0 SK))))
      (.mul (.const (-1)) (hornerChal zi zB SK)))
    (.mul (.add (.chal zi) (.const (-BASE))) (hornerChalOff zi COFF cB (NG - 1)))

/-- The body at the one-multiply layout. -/
def szBody (pl : Nat → ℤ) (zi : Nat) : ChalExpr :=
  szBodyAt pl zi X_BASE Y_BASE Z_BASE Q_BASE C_BASE

/-! ## §4 — the AIR, and the price. -/

/-- ⚑ **The source AIR of one two-point Schwartz–Zippel Pasta multiply.** TWO challenge legs — the
same residual asserted at `CHAL_Z` and at `CHAL_Z2` — where the schoolbook has 63 gate legs; the
five `limbs` legs are IDENTICAL (same columns, same widths, same tables), because bounded limbs are
the prerequisite Schwartz–Zippel does not remove. One gate would be `2^−98.5` after the wrap-union
(§6d) — below the repo bar — which is why the second is not optional. -/
def szMulAir (pl : Nat → ℤ) : EffectAir :=
  { tables := [ mainTableDef MUL_WIDTH
              , ⟨rangeTidW SB, "range_w8", 1, .rangeLimb SB⟩
              , ⟨rangeTidW CB, "range_w16", 1, .rangeLimb CB⟩ ]
  , legs := [ AirLeg.chal ⟨.all, szBody pl CHAL_Z⟩
            , AirLeg.chal ⟨.all, szBody pl CHAL_Z2⟩ ]
            ++ [ AirLeg.limbs ⟨limbCols X_BASE, SB, rangeTidW SB⟩
               , AirLeg.limbs ⟨limbCols Y_BASE, SB, rangeTidW SB⟩
               , AirLeg.limbs ⟨limbCols Z_BASE, SB, rangeTidW SB⟩
               , AirLeg.limbs ⟨limbCols Q_BASE, SB, rangeTidW SB⟩
               , AirLeg.limbs ⟨carryCols C_BASE, CB, rangeTidW CB⟩ ] }

/-- ⚑ **THE COMPILER ACCEPTS IT.** Both challenge legs have a deployed main-rail image: `.all` with
bodies that read no `nxt`. A `.first`/`.last` challenge leg would be REFUSED — the target's
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

/-- The unfolding lemma for the cost/shape proofs below, which reason through `lowerAir`. -/
theorem fpSzMulDesc_eq_lowerAir :
    fpSzMulDesc = Dregg2.Circuit.Emit.EffectLower.lowerAir "dregg-pasta-fpmul-sz::v1" MUL_WIDTH 0 [] (szMulAir pLimb) := rfl

/-- The `fqMul` tied source. -/
def fqSzMulTiedAir : Dregg2.Circuit.Emit.EffectLower.TiedAir where
  air := (szMulAir qLimb)

/-- The `fqMul` twin. -/
def fqSzMulDesc : EffectVmDescriptor2 :=
  (Dregg2.Circuit.Emit.EffectLower.lowerTiedAir
    "dregg-pasta-fqmul-sz::v1" MUL_WIDTH 0 [] fqSzMulTiedAir).val

theorem fqSzMulDesc_certified :
    Dregg2.Circuit.Emit.EffectLower.CertifiedRefines fqSzMulDesc [] (szMulAir qLimb) :=
  (Dregg2.Circuit.Emit.EffectLower.lowerTiedAir
    "dregg-pasta-fqmul-sz::v1" MUL_WIDTH 0 [] fqSzMulTiedAir).property

theorem fqSzMulDesc_eq_lowerAir :
    fqSzMulDesc = Dregg2.Circuit.Emit.EffectLower.lowerAir "dregg-pasta-fqmul-sz::v1" MUL_WIDTH 0 [] (szMulAir qLimb) := rfl

/-- ⚑ **IT DECLARES ITS CHALLENGES** — a value on the wire, `"challenges":2`, counted by a gate. A
descriptor that read a challenge without declaring it is REFUSED by `check_descriptor2`; this is
the number that refusal compares against. -/
theorem fpSzMulDesc_declares_two_challenges : challengeCount fpSzMulDesc = 2 := by
  rw [fpSzMulDesc_eq_lowerAir]
  unfold lowerAir Dregg2.Circuit.Emit.EffectLower.assemble
  rfl

/-- Exactly two gates of the challenge kind — the two-point form. -/
theorem fpSzMulDesc_chalGateCount : chalGateCount fpSzMulDesc = 2 := by
  rw [fpSzMulDesc_eq_lowerAir]
  unfold lowerAir Dregg2.Circuit.Emit.EffectLower.assemble
  rfl

/-- ⚑ **THE INDEPENDENCE REFUSAL, DISCHARGED ON THE EMITTED OBJECT.** `(CHAL_Z, CHAL_Z2) = (0, 1)`
are the α and β of the instance's first lookup context — the one pairing
`DescriptorIR2.chalIndicesDistinctOk` licenses — and the declared count sits inside the supply
`check_descriptor2` guarantees. A pairing like `(0, 2)` (same slot, different contexts) would be
REFUSED, and rightly: at the deployed sampler those can be the identical value. -/
theorem fpSzMulDesc_chal_indices_distinct :
    chalIndicesDistinctOk fpSzMulDesc CHAL_Z CHAL_Z2 = true := by
  rw [fpSzMulDesc_eq_lowerAir]
  decide

theorem fqSzMulDesc_chal_indices_distinct :
    chalIndicesDistinctOk fqSzMulDesc CHAL_Z CHAL_Z2 = true := by
  rw [fqSzMulDesc_eq_lowerAir]
  decide

/-- ⚑ **THE EMITTED COST, as a theorem.** `2` challenge gates + `4·32` limb lookups + `62` carry
lookups = **`192`** constraints, against the schoolbook's **`253`**. The 61-constraint difference
is exactly the 63 coefficient gates collapsing to 2. -/
theorem fpSzMulDesc_constraint_count : fpSzMulDesc.constraints.length = 192 := by
  rw [fpSzMulDesc_eq_lowerAir]
  unfold lowerAir Dregg2.Circuit.Emit.EffectLower.assemble
  simp only [List.map_nil, List.nil_append, List.append_nil]
  rfl

theorem fqSzMulDesc_constraint_count : fqSzMulDesc.constraints.length = 192 := by
  rw [fqSzMulDesc_eq_lowerAir]
  unfold lowerAir Dregg2.Circuit.Emit.EffectLower.assemble
  simp only [List.map_nil, List.nil_append, List.append_nil]
  rfl

/-- ⚑ **THE ALGEBRAIC-GATE COLLAPSE, 63 → 2, stated against the schoolbook's own theorem.** The
second gate is the price of clearing the ~124-bit bar under the wrap union (§6d); everything else
in the 253 is a range lookup that Schwartz–Zippel does not touch. -/
theorem gate_collapse :
    PastaFieldSound.fpMulSoundDesc.constraints.length = 253
      ∧ fpSzMulDesc.constraints.length = 192
      ∧ PastaFieldSound.NG = 63
      ∧ chalGateCount fpSzMulDesc = 2 :=
  ⟨PastaFieldSound.fpMulSoundDesc_constraint_count, fpSzMulDesc_constraint_count,
   PastaFieldSound.NG_eq, fpSzMulDesc_chalGateCount⟩

/-- ⚑ **THE PRICES THAT DO NOT MOVE, said out loud.** Same declared width, same range-lookup count.
A reader who takes `253 → 192` for a column or lookup saving is taking the flattering reading; the
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

/-- ⚑ **THE REAL `O(limbs²) → O(limbs)`, MEASURED ON BOTH EMITTED OBJECTS: 2 206 → 221 per gate,
442 for the two-point pair.** Six forward Horner chains — `31` muls each for `A, B, Q, R` and the
modulus, `61` for the offset carry chain — plus five structural products per gate. The two-point
row is **4.99×** less arithmetic than the schoolbook at the same constraint degree (9.94× per
gate); the offset decode costs additions only, so the per-gate count FELL by one against the old
(broken) body's 222. -/
theorem sz_arithmetic_is_linear : chalMuls (szBody pLimb CHAL_Z) = 221 := by decide

theorem schoolbook_arithmetic_is_quadratic : schoolbookMuls = 2206 := by decide

/-- The comparison, as one statement — against the TWO-POINT row, which is the emitted object. -/
theorem sz_arithmetic_ratio :
    schoolbookMuls = 2206 ∧ chalMuls (szBody pLimb CHAL_Z) = 221
      ∧ chalMuls (szBody pLimb CHAL_Z) + chalMuls (szBody pLimb CHAL_Z2) = 442
      ∧ 4 * 442 < schoolbookMuls ∧ schoolbookMuls < 5 * 442 :=
  ⟨schoolbook_arithmetic_is_quadratic, sz_arithmetic_is_linear, by decide, by decide, by decide⟩

/-- ⚑ **DEGREE 2, unchanged — the win is not bought back in the quotient.** The Horner chains in
the challenge are `isChallengeOnly` or trace-linear; each body's trace degree is 2, exactly the
schoolbook coefficient gate's. This is the fact `p3-air`'s `ExtEntry::Challenge => 0` supplies and
that `ChalExpr.traceDegree` mirrors. -/
theorem sz_body_is_degree_two :
    (szBody pLimb CHAL_Z).traceDegree = 2 ∧ (szBody pLimb CHAL_Z2).traceDegree = 2 := by
  constructor <;> decide

/-! ## §5 — ⚑ THE LEVER: batching, which only a challenge leaf can express.

One challenge gate can carry `N` multiplies folded by a second challenge `α`:

    Σₖ αᵏ · (eₖ(z) + (z − 2^SB)·Dₖ(z)) = 0.

The residual is a polynomial in `(α, z)` of degree `< N` in `α` and `≤ 2·SK − 2` in `z`, so the
one-point Schwartz–Zippel error is `≤ (N + 2·SK − 2)/|K|` — at the 588,732-multiply wrap workload
that is `2^−104.4`: better than the unbatched one-point union (`2^−98.5`) but STILL below the
~124-bit bar. So the batched form, too, needs a second evaluation point.

⚠ **And the two-point batched form needs FOUR guaranteed-independent draws** — `(z, α)` twice —
where `chalIndicesDistinctOk` can license only the `(α, β)` pair of ONE context per bus, and this
descriptor's deployed realization rides a single bus (every range limb lands on the byte bus). A
second bus (e.g. a chip-table lookup) would supply the second pair; that wiring is a real,
buildable follow-on and it is NAMED here rather than assumed. The shape below is the one-point
batch, kept as the shape the follow-on relocates. -/

/-- The batching challenge index — the β of the first context, licensed against `CHAL_Z` by
`chalIndicesDistinctOk` for the ONE-POINT batched form. -/
def CHAL_ALPHA : Nat := 1

/-- The batched body over `n` multiplies whose limb blocks start at `blockBase k` (the five
sub-blocks contiguous, in the one-multiply layout's order). -/
def szBatchBody (pl : Nat → ℤ) (blockBase : Nat → Nat) : Nat → ChalExpr
  | 0     => .const 0
  | k + 1 =>
      .add (.mul (szBatchBody pl blockBase k) (.chal CHAL_ALPHA))
           (szBodyAt pl CHAL_Z (blockBase k) (blockBase k + SK) (blockBase k + 2 * SK)
             (blockBase k + 3 * SK) (blockBase k + 4 * SK))

/-- **Batching keeps the degree at 2.** The `αᵏ` fold is challenge-only, so folding `N` multiplies
into one gate does not raise the quotient degree — which is what makes the collapse free rather
than a trade. Stated at `N = 4`; the induction is the same at every `N`. -/
theorem sz_batch_is_degree_two :
    (szBatchBody pLimb (fun k => k * MUL_WIDTH) 4).traceDegree = 2 := by decide

/-- ⚑ **`63·N → 1`.** Four multiplies in ONE challenge gate against 252 schoolbook coefficient
gates. The gate count of the batched form is 1 at every `N`, by construction. -/
theorem sz_batch_collapses_gate_count :
    4 * PastaFieldSound.NG = 252 := by decide

/-! ## §6 — soundness. Four separate facts, deliberately not conflated:

* §6a — IF the residual polynomial maps to zero in `K` THEN, under bounded limbs, the integer
  congruence holds (`szPoly_forces_congruence`). No randomness, no probability.
* §6b — the emitted body's FAITHFUL denotation IS the residual evaluated at the drawn challenge
  (`szBodyAt_evalIn`) — the weld without which §6a would be about a different object than the gate.
* §6c — the gate theorems: `ChalConstraint.holdsIn` (what `assert_zero_ext` asserts) at a
  non-exceptional draw — EITHER of the two independent draws suffices — forces the congruence, and
  the exact gates quantified over are constraints of the emitted descriptor.
* §6d — the ε ledger: how likely "non-exceptional" is, as named bracketing theorems. This is where
  the randomness lives and it is the ONLY place. -/

section Soundness
open Polynomial
open Dregg2.Circuit.OodQuotientConsistency (exceptionalSet exceptionalSet_card_le
  nonexceptional_eval_zero_forces_zero)

/-! ### §6a′ — generic list-sum machinery, over any commutative ring.

`PastaFieldSound.sumL` is ℤ-valued; the residual identity lives in `Polynomial ℤ` and the faithful
denotation in an arbitrary `K`, so the same little lemma set is needed one rung more general. The
proofs are verbatim ports. -/

variable {R : Type*} [CommRing R]

/-- The sum of `f` over a list, in any commutative ring. -/
def sumR {α : Type} (l : List α) (f : α → R) : R := (l.map f).sum

@[simp] theorem sumR_nil {α : Type} (f : α → R) : sumR ([] : List α) f = 0 := rfl

@[simp] theorem sumR_cons {α : Type} (x : α) (l : List α) (f : α → R) :
    sumR (x :: l) f = f x + sumR l f := by simp [sumR]

theorem sumR_append {α : Type} (l1 l2 : List α) (f : α → R) :
    sumR (l1 ++ l2) f = sumR l1 f + sumR l2 f := by
  simp [sumR, List.map_append, List.sum_append]

theorem sumR_zero {α : Type} (l : List α) : sumR l (fun _ => (0 : R)) = 0 := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [sumR_cons, ih]

theorem sumR_congr {α : Type} (l : List α) (f g : α → R) (h : ∀ x ∈ l, f x = g x) :
    sumR l f = sumR l g := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [sumR_cons, h x (by simp)]
    rw [ih (fun y hy => h y (by simp [hy]))]

theorem sumR_map {α β : Type} (g : α → β) (l : List α) (f : β → R) :
    sumR (l.map g) f = sumR l (f ∘ g) := by
  simp [sumR, List.map_map]

theorem sumR_filter {α : Type} (l : List α) (Pr : α → Bool) (f : α → R) :
    sumR (l.filter Pr) f = sumR l (fun x => if Pr x then f x else 0) := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    by_cases h : Pr x = true
    · simp [h, ih]
    · simp only [Bool.not_eq_true] at h
      simp [h, ih]

theorem sumR_add {α : Type} (l : List α) (f g : α → R) :
    sumR l (fun x => f x + g x) = sumR l f + sumR l g := by
  induction l with
  | nil => simp
  | cons x xs ih => simp only [sumR_cons, ih]; ring

theorem sumR_sub {α : Type} (l : List α) (f g : α → R) :
    sumR l (fun x => f x - g x) = sumR l f - sumR l g := by
  induction l with
  | nil => simp
  | cons x xs ih => simp only [sumR_cons, ih]; ring

theorem sumR_smul {α : Type} (l : List α) (k : R) (f : α → R) :
    sumR l (fun x => k * f x) = k * sumR l f := by
  induction l with
  | nil => simp
  | cons x xs ih => simp only [sumR_cons, ih]; ring

theorem sumR_comm {α β : Type} (l1 : List α) (l2 : List β) (F : α → β → R) :
    sumR l1 (fun x => sumR l2 (F x)) = sumR l2 (fun y => sumR l1 (fun x => F x y)) := by
  induction l1 with
  | nil => simp [sumR_zero]
  | cons x xs ih =>
    simp only [sumR_cons, ih]
    rw [← sumR_add]

theorem sumR_product_nested {α β : Type} (l1 : List α) (l2 : List β) (F : α × β → R) :
    sumR (l1 ×ˢ l2) F = sumR l1 (fun x => sumR l2 (fun y => F (x, y))) := by
  induction l1 with
  | nil => simp [sumR]
  | cons x xs ih =>
    rw [List.product_cons, sumR_append, ih, sumR_cons]
    congr 1
    simp [sumR, List.map_map, Function.comp_def]

theorem sumR_product {α β : Type} (l1 : List α) (l2 : List β) (f : α → R) (g : β → R) :
    sumR (l1 ×ˢ l2) (fun pr => f pr.1 * g pr.2) = sumR l1 f * sumR l2 g := by
  rw [sumR_product_nested]
  have h1 : ∀ x ∈ l1, sumR l2 (fun y => f x * g y) = f x * sumR l2 g :=
    fun x _ => sumR_smul l2 (f x) g
  rw [sumR_congr _ _ _ h1]
  have h2 : ∀ x ∈ l1, f x * sumR l2 g = sumR l2 g * f x := fun x _ => mul_comm _ _
  rw [sumR_congr _ _ _ h2, sumR_smul]
  ring

theorem sumR_range_ite (n j : Nat) (g : Nat → R) (hj : j < n) :
    sumR (List.range n) (fun m => if j = m then g m else 0) = g j := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [List.range_succ, sumR_append, sumR_cons, sumR_nil]
    rcases Nat.lt_or_ge j n with h | h
    · rw [show ((if j = n then g n else 0) : R) = 0 from if_neg (by omega)]
      rw [ih h]; ring
    · have hjn : j = n := by omega
      subst hjn
      have hz : sumR (List.range j) (fun m => if j = m then g m else 0) = 0 := by
        rw [sumR_congr _ _ (fun _ => (0 : R))
          (fun m hm => if_neg (by have := List.mem_range.mp hm; omega))]
        exact sumR_zero _
      rw [hz]; simp

/-- The generic convolution port: the base-`b` recomposition of the antidiagonal sums IS the
product of the two recompositions — over any commutative ring, so `b := X` in `ℤ[X]` is an
instance. Verbatim port of `PastaFieldSound.conv_recompose`. -/
theorem conv_recomposeR (b : R) (f g : Nat → R) :
    sumR (List.range NG) (fun m => b ^ m * sumR (convPairs m) (fun pr => f pr.1 * g pr.2))
      = sumR (List.range SK) (fun i => b ^ i * f i)
        * sumR (List.range SK) (fun j => b ^ j * g j) := by
  have step1 : ∀ m ∈ List.range NG,
      b ^ m * sumR (convPairs m) (fun pr => f pr.1 * g pr.2)
        = sumR allPairs (fun pr => if pr.1 + pr.2 = m then b ^ m * (f pr.1 * g pr.2) else 0) := by
    intro m _
    rw [convPairs, sumR_filter, ← sumR_smul]
    refine sumR_congr _ _ _ (fun pr _ => ?_)
    by_cases h : pr.1 + pr.2 = m <;> simp [h]
  rw [sumR_congr (List.range NG) _ _ step1, sumR_comm]
  have step2 : ∀ pr ∈ allPairs,
      sumR (List.range NG) (fun m => if pr.1 + pr.2 = m then b ^ m * (f pr.1 * g pr.2) else 0)
        = b ^ pr.1 * f pr.1 * (b ^ pr.2 * g pr.2) := by
    intro pr hpr
    rw [allPairs, List.mem_product] at hpr
    have h1 : pr.1 < 32 := List.mem_range.mp hpr.1
    have h2 : pr.2 < 32 := List.mem_range.mp hpr.2
    have hlt : pr.1 + pr.2 < NG := by
      show pr.1 + pr.2 < 63
      omega
    rw [sumR_range_ite NG (pr.1 + pr.2) _ hlt, pow_add]
    ring
  rw [sumR_congr allPairs _ _ step2]
  exact sumR_product (List.range SK) (List.range SK)
    (fun i => b ^ i * f i) (fun j => b ^ j * g j)

/-- The `z` block occupies only the low `SK` positions — generic port of
`PastaFieldSound.z_extend`. -/
theorem z_extendR (b : R) (h : Nat → R) :
    sumR (List.range NG) (fun m => b ^ m * (if m < SK then h m else 0))
      = sumR (List.range SK) (fun m => b ^ m * h m) := by
  have hsplit : NG = SK + (NG - SK) := rfl
  rw [hsplit, List.range_add, sumR_append]
  have hlow : ∀ m ∈ List.range SK,
      b ^ m * (if m < SK then h m else 0) = b ^ m * h m :=
    fun m hm => by rw [if_pos (List.mem_range.mp hm)]
  have hhigh : ∀ m ∈ (List.range (NG - SK)).map (SK + ·),
      b ^ m * (if m < SK then h m else 0) = 0 := by
    intro m hm
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hm
    simp
  rw [sumR_congr _ _ _ hlow, sumR_congr _ _ (fun _ => (0 : R)) hhigh, sumR_zero]
  ring

/-! ### §6a″ — the coefficient-polynomial vocabulary, and the residual. -/

/-- `Σ_{i<k} C (h i) · Xⁱ` — every block of the residual is one of these. -/
noncomputable def coeffPoly (h : Nat → ℤ) (k : Nat) : Polynomial ℤ :=
  sumR (List.range k) (fun i => C (h i) * X ^ i)

theorem coeffPoly_congr (h h' : Nat → ℤ) (k : Nat) (H : ∀ i, i < k → h i = h' i) :
    coeffPoly h k = coeffPoly h' k := by
  unfold coeffPoly
  exact sumR_congr _ _ _ (fun i hi => by rw [H i (List.mem_range.mp hi)])

theorem coeffPoly_zero (h : Nat → ℤ) : coeffPoly h 0 = 0 := rfl

theorem coeffPoly_one (h : Nat → ℤ) : coeffPoly h 1 = C (h 0) := by
  simp [coeffPoly, sumR, List.range_one]

/-- Peel the LOW coefficient: `coeffPoly h (k+1) = C (h 0) + X · coeffPoly (h ∘ succ) k`. The
polynomial twin of one forward-Horner step. -/
theorem coeffPoly_shift (h : Nat → ℤ) (k : Nat) :
    coeffPoly h (k + 1) = C (h 0) + X * coeffPoly (fun i => h (i + 1)) k := by
  unfold coeffPoly
  rw [List.range_succ_eq_map, sumR_cons, ← sumR_smul, sumR_map]
  congr 1
  · simp
  · refine sumR_congr _ _ _ (fun i _ => ?_)
    simp only [Function.comp_apply]
    rw [pow_succ]
    ring

/-- Peel the HIGH coefficient. -/
theorem coeffPoly_snoc (h : Nat → ℤ) (k : Nat) :
    coeffPoly h (k + 1) = coeffPoly h k + C (h k) * X ^ k := by
  unfold coeffPoly
  rw [List.range_succ, sumR_append, sumR_cons, sumR_nil, add_zero]

theorem coeffPoly_C_mul (c : ℤ) (h : Nat → ℤ) (k : Nat) :
    C c * coeffPoly h k = coeffPoly (fun i => c * h i) k := by
  unfold coeffPoly
  rw [← sumR_smul]
  refine sumR_congr _ _ _ (fun i _ => ?_)
  rw [← mul_assoc, ← map_mul]

theorem coeffPoly_add (h h' : Nat → ℤ) (k : Nat) :
    coeffPoly h k + coeffPoly h' k = coeffPoly (fun i => h i + h' i) k := by
  unfold coeffPoly
  rw [← sumR_add]
  refine sumR_congr _ _ _ (fun i _ => ?_)
  rw [map_add]; ring

theorem coeffPoly_sub (h h' : Nat → ℤ) (k : Nat) :
    coeffPoly h k - coeffPoly h' k = coeffPoly (fun i => h i - h' i) k := by
  unfold coeffPoly
  rw [← sumR_sub]
  refine sumR_congr _ _ _ (fun i _ => ?_)
  rw [map_sub]; ring

/-- `C` distributes over the ℤ-valued list sum — the bridge between the schoolbook's `sumL`
coefficients and polynomial coefficients. -/
theorem C_sumL {α : Type} (l : List α) (f : α → ℤ) :
    (C (sumL l f) : Polynomial ℤ) = sumR l (fun x => C (f x)) := by
  induction l with
  | nil => simp [sumL, sumR]
  | cons x xs ih => rw [sumL_cons, sumR_cons, map_add, ih]

/-- **Coefficient extraction.** Below the length, `coeffPoly h k` has exactly the coefficients `h`.
This is what turns "the residual is the zero polynomial" into 63 scalar facts. -/
theorem coeffPoly_coeff (h : Nat → ℤ) (k m : Nat) (hm : m < k) :
    (coeffPoly h k).coeff m = h m := by
  have hlist : ∀ l : List Nat,
      (sumR l (fun i => (C (h i) * X ^ i : Polynomial ℤ))).coeff m
        = sumL l (fun i => if m = i then h i else 0) := by
    intro l
    induction l with
    | nil => simp [sumR, sumL]
    | cons x xs ih =>
      rw [sumR_cons, sumL_cons, Polynomial.coeff_add, ih, Polynomial.coeff_C_mul_X_pow]
  unfold coeffPoly
  rw [hlist, sumL_range_ite k m h hm]

/-- ⚑ **THE RESIDUAL POLYNOMIAL** of one multiply, read off a row: what the emitted body evaluates
at the drawn challenge (§6b), and the object whose vanishing forces the congruence (§6a). -/
noncomputable def szResidual (a : Assignment) (xB yB zB qB cB : Nat) (pl : Nat → ℤ) :
    Polynomial ℤ :=
  coeffPoly (fun i => a (xB + i)) SK * coeffPoly (fun i => a (yB + i)) SK
    - coeffPoly (fun i => a (qB + i)) SK * coeffPoly pl SK
    - coeffPoly (fun i => a (zB + i)) SK
    + (X - C BASE) * coeffPoly (fun i => a (cB + i) - COFF) (NG - 1)

/-- The product of two limb polynomials, as the convolution coefficient sum. -/
theorem coeffPoly_mul_conv (f g : Nat → ℤ) :
    coeffPoly f SK * coeffPoly g SK
      = coeffPoly (fun m => sumL (convPairs m) (fun pr => f pr.1 * g pr.2)) NG := by
  unfold coeffPoly
  have h := conv_recomposeR (R := Polynomial ℤ) X (fun i => C (f i)) (fun j => C (g j))
  calc sumR (List.range SK) (fun i => (C (f i) : Polynomial ℤ) * X ^ i)
        * sumR (List.range SK) (fun j => (C (g j) : Polynomial ℤ) * X ^ j)
      = sumR (List.range SK) (fun i => (X : Polynomial ℤ) ^ i * C (f i))
          * sumR (List.range SK) (fun j => (X : Polynomial ℤ) ^ j * C (g j)) := by
        rw [sumR_congr (List.range SK) _ _ (fun i _ => mul_comm (C (f i)) ((X : Polynomial ℤ) ^ i)),
            sumR_congr (List.range SK) (fun j => C (g j) * X ^ j) _
              (fun j _ => mul_comm (C (g j)) ((X : Polynomial ℤ) ^ j))]
    _ = sumR (List.range NG)
          (fun m => (X : Polynomial ℤ) ^ m
            * sumR (convPairs m) (fun pr => C (f pr.1) * C (g pr.2))) := h.symm
    _ = sumR (List.range NG)
          (fun m => C (sumL (convPairs m) (fun pr => f pr.1 * g pr.2)) * X ^ m) := by
        refine sumR_congr _ _ _ (fun m _ => ?_)
        rw [C_sumL, mul_comm]
        congr 1
        exact sumR_congr _ _ _ (fun pr _ => (map_mul C _ _).symm)

/-- The `z` block, extended to the residual's `NG` positions. -/
theorem coeffPoly_extend (h : Nat → ℤ) :
    coeffPoly h SK = coeffPoly (fun m => if m < SK then h m else 0) NG := by
  unfold coeffPoly
  have hz := z_extendR (R := Polynomial ℤ) X (fun m => C (h m))
  calc sumR (List.range SK) (fun i => (C (h i) : Polynomial ℤ) * X ^ i)
      = sumR (List.range SK) (fun i => (X : Polynomial ℤ) ^ i * C (h i)) :=
        sumR_congr _ _ _ (fun i _ => mul_comm _ _)
    _ = sumR (List.range NG)
          (fun m => (X : Polynomial ℤ) ^ m * (if m < SK then C (h m) else 0)) := hz.symm
    _ = sumR (List.range NG) (fun m => C (if m < SK then h m else 0) * X ^ m) := by
        refine sumR_congr _ _ _ (fun m _ => ?_)
        by_cases hm : m < SK <;> simp [hm, mul_comm]

/-- The carry column at chain index `k+1`, decoded: `chainVal (k+1) = col_(cB+k) − COFF` inside the
chain. -/
theorem chainVal_succ_col (a : Assignment) (cB k : Nat) (hk : k < NG - 1) :
    chainVal a cB (k + 1) = a (cB + k) - COFF := by
  have hk' : k < 62 := hk
  unfold chainVal
  rw [if_neg (by omega),
      if_pos (show k + 1 ≤ PastaFieldSound.NG - 1 from by show k + 1 ≤ 62; omega)]
  have hidx : cB + (k + 1) - 1 = cB + k := by omega
  rw [hidx]

/-- ⚑ **THE CARRY TERM IS THE CHAIN DIFFERENCE.** `(X − 2^SB)·D` contributes exactly
`chainVal m − 2^SB·chainVal (m+1)` at every coefficient — the schoolbook's carry-in/carry-out pair,
with both chain ends pinned closed by construction (`chainVal 0 = chainVal NG = 0`). The sign and
the offset are the two defects the old body had; this theorem is where both would fail. -/
theorem carry_term_eq (a : Assignment) (cB : Nat) :
    (X - C BASE) * coeffPoly (fun i => a (cB + i) - COFF) (NG - 1)
      = coeffPoly (fun m => chainVal a cB m - (2 : ℤ) ^ SB * chainVal a cB (m + 1)) NG := by
  rw [sub_mul]
  have hX : (X : Polynomial ℤ) * coeffPoly (fun i => a (cB + i) - COFF) (NG - 1)
      = coeffPoly (fun m => chainVal a cB m) NG := by
    have hshift : coeffPoly (fun m => chainVal a cB m) NG
        = C (chainVal a cB 0) + X * coeffPoly (fun i => chainVal a cB (i + 1)) (NG - 1) :=
      coeffPoly_shift (fun m => chainVal a cB m) (NG - 1)
    have hcongr : coeffPoly (fun i => chainVal a cB (i + 1)) (NG - 1)
        = coeffPoly (fun i => a (cB + i) - COFF) (NG - 1) :=
      coeffPoly_congr _ _ _ (fun i hi => chainVal_succ_col a cB i hi)
    rw [hshift, hcongr, show chainVal a cB 0 = 0 from rfl, map_zero, zero_add]
  have hC : (C BASE : Polynomial ℤ) * coeffPoly (fun i => a (cB + i) - COFF) (NG - 1)
      = coeffPoly (fun m => (2 : ℤ) ^ SB * chainVal a cB (m + 1)) NG := by
    have hCmul : (C BASE : Polynomial ℤ) * coeffPoly (fun i => a (cB + i) - COFF) (NG - 1)
        = coeffPoly (fun i => BASE * (a (cB + i) - COFF)) (NG - 1) :=
      coeffPoly_C_mul BASE _ (NG - 1)
    have hsnoc : coeffPoly (fun m => (2 : ℤ) ^ SB * chainVal a cB (m + 1)) NG
        = coeffPoly (fun m => (2 : ℤ) ^ SB * chainVal a cB (m + 1)) (NG - 1)
            + C ((2 : ℤ) ^ SB * chainVal a cB ((NG - 1) + 1)) * X ^ (NG - 1) :=
      coeffPoly_snoc _ (NG - 1)
    have hcongr : coeffPoly (fun i => BASE * (a (cB + i) - COFF)) (NG - 1)
        = coeffPoly (fun m => (2 : ℤ) ^ SB * chainVal a cB (m + 1)) (NG - 1) :=
      coeffPoly_congr _ _ _ (fun i hi => by rw [chainVal_succ_col a cB i hi]; rfl)
    rw [hCmul, hcongr, hsnoc,
        show chainVal a cB ((NG - 1) + 1) = 0 from chainVal_top a cB, mul_zero, map_zero,
        zero_mul, add_zero]
  rw [hX, hC, coeffPoly_sub]

/-- ⚑ **THE RESIDUAL'S COEFFICIENTS ARE THE SCHOOLBOOK'S GATE BODIES.** This is the whole §6a
content in one identity: the polynomial the challenge gate evaluates has `coefBody` — digit +
carry-in − radix·carry-out, the SAME body `felt_gates_force_congruence` quantifies over — as its
`m`-th coefficient. -/
theorem szResidual_eq_coefSum (a : Assignment) (xB yB zB qB cB : Nat) (pl : Nat → ℤ) :
    szResidual a xB yB zB qB cB pl = coeffPoly (coefBody a xB yB zB qB cB pl) NG := by
  unfold szResidual
  rw [coeffPoly_mul_conv (fun i => a (xB + i)) (fun i => a (yB + i)),
      coeffPoly_mul_conv (fun i => a (qB + i)) pl,
      coeffPoly_extend (fun i => a (zB + i)),
      carry_term_eq a cB,
      coeffPoly_sub, coeffPoly_sub, coeffPoly_add]
  refine coeffPoly_congr _ _ _ (fun m _ => ?_)
  unfold coefBody digitVal
  ring

theorem szResidual_coeff (a : Assignment) (xB yB zB qB cB : Nat) (pl : Nat → ℤ) (m : Nat)
    (hm : m < NG) :
    (szResidual a xB yB zB qB cB pl).coeff m = coefBody a xB yB zB qB cB pl m := by
  rw [szResidual_eq_coefSum, coeffPoly_coeff _ _ _ hm]

/-- ⚑ **`szPoly_forces_congruence` — the phantom made real.** `PastaCurveSound` measured (and
`Dregg2.lean` recorded) that this file used to CREDIT ITSELF with this theorem while `git grep`
found only the credit. Here it is, stated where the deployed check lives: IF the residual maps to
the ZERO polynomial in a characteristic-`p` carrier `K` (the conclusion §6c extracts from a
non-exceptional draw) THEN, under the range facts the five emitted `limbs` legs supply, the Pasta
congruence holds. Each coefficient of the mapped residual is the `Int.cast` of `coefBody`
(`Polynomial.coeff_map` + `szResidual_coeff`), `CharP.intCast_eq_zero_iff` turns its vanishing into
`P ∣ coefBody` over ℤ, and that is verbatim the `hgates` hypothesis of the already-proved,
axiom-clean `felt_gates_force_congruence` — which remains the terminal lemma. -/
theorem szPoly_forces_congruence {K : Type*} [CommRing K] [CharP K 2013265921]
    (a : Assignment) (xB yB zB qB cB : Nat) (pl : Nat → ℤ) (M : ℤ)
    (hbx : ∀ i, i < SK → 0 ≤ a (xB + i) ∧ a (xB + i) < 2 ^ SB)
    (hby : ∀ i, i < SK → 0 ≤ a (yB + i) ∧ a (yB + i) < 2 ^ SB)
    (hbz : ∀ i, i < SK → 0 ≤ a (zB + i) ∧ a (zB + i) < 2 ^ SB)
    (hbq : ∀ i, i < SK → 0 ≤ a (qB + i) ∧ a (qB + i) < 2 ^ SB)
    (hpl : ∀ j, 0 ≤ pl j ∧ pl j < 2 ^ SB)
    (hplM : sumL (List.range SK) (fun j => ((2 : ℤ) ^ SB) ^ j * pl j) = M)
    (hbc : ∀ i, i < NG - 1 → 0 ≤ a (cB + i) ∧ a (cB + i) < 2 ^ CB)
    (hres : (szResidual a xB yB zB qB cB pl).map (Int.castRingHom K) = 0) :
    M ∣ (sVal a xB * sVal a yB - sVal a zB) := by
  refine felt_gates_force_congruence a xB yB zB qB cB pl M hbx hby hbz hbq hpl hplM hbc
    (fun m hm => ?_)
  have h0 : (((szResidual a xB yB zB qB cB pl).coeff m : ℤ) : K) = 0 := by
    have := congrArg (fun p : Polynomial K => p.coeff m) hres
    simpa [Polynomial.coeff_map] using this
  rw [szResidual_coeff a xB yB zB qB cB pl m hm] at h0
  exact (CharP.intCast_eq_zero_iff K 2013265921 _).mp h0

/-! ### §6b — ⚑ THE WELD: the emitted body's FAITHFUL denotation IS the residual at the draw.

Stated on `ChalExpr.evalIn` over an arbitrary `CommRing K` — the denotation of the deployed
`assert_zero_ext` — NOT on the base-lane `eval`. A weld on the base lane would quietly inherit a
`2^31` challenge space where the deployed draw is from the `2^123.63` quartic extension: the
identity-carrier lesson in miniature. -/

theorem hornerChal_evalIn {K : Type*} [CommRing K] (env : VmRowEnv) (z : Nat → K) (zi : Nat) :
    ∀ (k base : Nat),
      (hornerChal zi base k).evalIn env z
        = ((coeffPoly (fun i => env.loc (base + i)) k).map (Int.castRingHom K)).eval (z zi)
  | 0, base => by
      simp [hornerChal, ChalExpr.evalIn, coeffPoly_zero]
  | 1, base => by
      simp [hornerChal, ChalExpr.evalIn, coeffPoly_one]
  | k + 2, base => by
      have ih := hornerChal_evalIn env z zi (k + 1) (base + 1)
      have hs : coeffPoly (fun i => env.loc (base + i)) (k + 2)
          = C (env.loc base) + X * coeffPoly (fun i => env.loc (base + 1 + i)) (k + 1) := by
        have h0 : coeffPoly (fun i => env.loc (base + i)) (k + 2)
            = C (env.loc (base + 0))
                + X * coeffPoly (fun i => env.loc (base + (i + 1))) (k + 1) :=
          coeffPoly_shift (fun i => env.loc (base + i)) (k + 1)
        have h1 : coeffPoly (fun i => env.loc (base + (i + 1))) (k + 1)
            = coeffPoly (fun i => env.loc (base + 1 + i)) (k + 1) :=
          coeffPoly_congr _ _ _
            (fun i _ => by rw [show base + (i + 1) = base + 1 + i from by omega])
        rw [h0, h1, Nat.add_zero]
      rw [show hornerChal zi base (k + 2)
            = .add (.loc base) (.mul (.chal zi) (hornerChal zi (base + 1) (k + 1))) from rfl]
      simp [ChalExpr.evalIn, ih, hs]

theorem hornerConst_evalIn {K : Type*} [CommRing K] (env : VmRowEnv) (z : Nat → K) (zi : Nat)
    (pl : Nat → ℤ) :
    ∀ (k j : Nat),
      (hornerConst zi pl j k).evalIn env z
        = ((coeffPoly (fun i => pl (j + i)) k).map (Int.castRingHom K)).eval (z zi)
  | 0, j => by
      simp [hornerConst, ChalExpr.evalIn, coeffPoly_zero]
  | 1, j => by
      simp [hornerConst, ChalExpr.evalIn, coeffPoly_one]
  | k + 2, j => by
      have ih := hornerConst_evalIn env z zi pl (k + 1) (j + 1)
      have hs : coeffPoly (fun i => pl (j + i)) (k + 2)
          = C (pl j) + X * coeffPoly (fun i => pl (j + 1 + i)) (k + 1) := by
        have h0 : coeffPoly (fun i => pl (j + i)) (k + 2)
            = C (pl (j + 0)) + X * coeffPoly (fun i => pl (j + (i + 1))) (k + 1) :=
          coeffPoly_shift (fun i => pl (j + i)) (k + 1)
        have h1 : coeffPoly (fun i => pl (j + (i + 1))) (k + 1)
            = coeffPoly (fun i => pl (j + 1 + i)) (k + 1) :=
          coeffPoly_congr _ _ _
            (fun i _ => by rw [show j + (i + 1) = j + 1 + i from by omega])
        rw [h0, h1, Nat.add_zero]
      rw [show hornerConst zi pl j (k + 2)
            = .add (.const (pl j)) (.mul (.chal zi) (hornerConst zi pl (j + 1) (k + 1))) from rfl]
      simp [ChalExpr.evalIn, ih, hs]

theorem hornerChalOff_evalIn {K : Type*} [CommRing K] (env : VmRowEnv) (z : Nat → K) (zi : Nat)
    (off : ℤ) :
    ∀ (k base : Nat),
      (hornerChalOff zi off base k).evalIn env z
        = ((coeffPoly (fun i => env.loc (base + i) - off) k).map (Int.castRingHom K)).eval (z zi)
  | 0, base => by
      simp [hornerChalOff, ChalExpr.evalIn, coeffPoly_zero]
  | 1, base => by
      simp [hornerChalOff, ChalExpr.evalIn, coeffPoly_one]
      ring
  | k + 2, base => by
      have ih := hornerChalOff_evalIn env z zi off (k + 1) (base + 1)
      have hs : coeffPoly (fun i => env.loc (base + i) - off) (k + 2)
          = C (env.loc base - off)
              + X * coeffPoly (fun i => env.loc (base + 1 + i) - off) (k + 1) := by
        have h0 : coeffPoly (fun i => env.loc (base + i) - off) (k + 2)
            = C (env.loc (base + 0) - off)
                + X * coeffPoly (fun i => env.loc (base + (i + 1)) - off) (k + 1) :=
          coeffPoly_shift (fun i => env.loc (base + i) - off) (k + 1)
        have h1 : coeffPoly (fun i => env.loc (base + (i + 1)) - off) (k + 1)
            = coeffPoly (fun i => env.loc (base + 1 + i) - off) (k + 1) :=
          coeffPoly_congr _ _ _
            (fun i _ => by rw [show base + (i + 1) = base + 1 + i from by omega])
        rw [h0, h1, Nat.add_zero]
      rw [show hornerChalOff zi off base (k + 2)
            = .add (.add (.loc base) (.const (-off)))
                (.mul (.chal zi) (hornerChalOff zi off (base + 1) (k + 1))) from rfl]
      simp [ChalExpr.evalIn, ih, hs]
      ring

/-- ⚑ **THE WELD.** The emitted Schwartz–Zippel body, denoted FAITHFULLY in `K` (the deployed
`assert_zero_ext` reading), is exactly the residual polynomial mapped into `K` and evaluated at the
drawn challenge `z zi`. Without this, §6a would be a theorem about a polynomial nothing checks. -/
theorem szBodyAt_evalIn {K : Type*} [CommRing K] (env : VmRowEnv) (z : Nat → K)
    (pl : Nat → ℤ) (zi xB yB zB qB cB : Nat) :
    (szBodyAt pl zi xB yB zB qB cB).evalIn env z
      = ((szResidual env.loc xB yB zB qB cB pl).map (Int.castRingHom K)).eval (z zi) := by
  have hpl0 : coeffPoly (fun i => pl (0 + i)) SK = coeffPoly pl SK :=
    coeffPoly_congr _ _ _ (fun i _ => by rw [Nat.zero_add])
  unfold szBodyAt szResidual
  simp only [ChalExpr.evalIn, hornerChal_evalIn, hornerConst_evalIn, hornerChalOff_evalIn, hpl0,
    Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_C,
    Polynomial.map_X, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, Int.coe_castRingHom]
  push_cast
  ring

/-! ### §6c — the gate theorems, consuming the faithful denotation of the EMITTED gates. -/

/-- **One gate at one draw.** `ChalConstraint.holdsIn` — the faithful K-denotation the deployed
`assert_zero_ext` asserts — at a NON-exceptional draw, plus the range facts the emitted `limbs`
legs supply, forces the congruence. Modulus- and base-parametric; `zi` free, so both emitted gates
are instances. -/
theorem szGate_holdsIn_forces_congruence
    {K : Type*} [CommRing K] [IsDomain K] [DecidableEq K] [CharP K 2013265921]
    (env : VmRowEnv) (z : Nat → K) (isLast : Bool) (zi xB yB zB qB cB : Nat)
    (pl : Nat → ℤ) (M : ℤ)
    (hgate : ChalConstraint.holdsIn env z isLast ⟨szBodyAt pl zi xB yB zB qB cB, false⟩)
    (hnonexc : z zi ∉ exceptionalSet
        ((szResidual env.loc xB yB zB qB cB pl).map (Int.castRingHom K)))
    (hbx : ∀ i, i < SK → 0 ≤ env.loc (xB + i) ∧ env.loc (xB + i) < 2 ^ SB)
    (hby : ∀ i, i < SK → 0 ≤ env.loc (yB + i) ∧ env.loc (yB + i) < 2 ^ SB)
    (hbz : ∀ i, i < SK → 0 ≤ env.loc (zB + i) ∧ env.loc (zB + i) < 2 ^ SB)
    (hbq : ∀ i, i < SK → 0 ≤ env.loc (qB + i) ∧ env.loc (qB + i) < 2 ^ SB)
    (hpl : ∀ j, 0 ≤ pl j ∧ pl j < 2 ^ SB)
    (hplM : sumL (List.range SK) (fun j => ((2 : ℤ) ^ SB) ^ j * pl j) = M)
    (hbc : ∀ i, i < NG - 1 → 0 ≤ env.loc (cB + i) ∧ env.loc (cB + i) < 2 ^ CB) :
    M ∣ (sVal env.loc xB * sVal env.loc yB - sVal env.loc zB) := by
  have hval : (szBodyAt pl zi xB yB zB qB cB).evalIn env z = 0 := by
    simpa [ChalConstraint.holdsIn] using hgate
  rw [szBodyAt_evalIn] at hval
  have hres := nonexceptional_eval_zero_forces_zero _ (z zi) hval hnonexc
  exact szPoly_forces_congruence env.loc xB yB zB qB cB pl M hbx hby hbz hbq hpl hplM hbc hres

/-- ⚑ **THE TWO-POINT THEOREM, at the emitted `fpMul` layout.** BOTH emitted gates hold (they are
constraints of the descriptor — `fpSzMulDesc_carries_the_gates`), and it suffices that EITHER draw
is non-exceptional: that disjunction failing requires the residual to vanish at two independent
points, which is the `ε²` in the ledger. The two draws' independence is the
`chalIndicesDistinctOk` licence, discharged at `fpSzMulDesc_chal_indices_distinct`. -/
theorem fpSzMulDesc_two_point_forces
    {K : Type*} [CommRing K] [IsDomain K] [DecidableEq K] [CharP K 2013265921]
    (env : VmRowEnv) (z : Nat → K) (isLast : Bool)
    (h1 : ChalConstraint.holdsIn env z isLast ⟨szBody pLimb CHAL_Z, false⟩)
    (h2 : ChalConstraint.holdsIn env z isLast ⟨szBody pLimb CHAL_Z2, false⟩)
    (hnonexc : z CHAL_Z ∉ exceptionalSet
        ((szResidual env.loc X_BASE Y_BASE Z_BASE Q_BASE C_BASE pLimb).map (Int.castRingHom K))
      ∨ z CHAL_Z2 ∉ exceptionalSet
        ((szResidual env.loc X_BASE Y_BASE Z_BASE Q_BASE C_BASE pLimb).map (Int.castRingHom K)))
    (hbx : ∀ i, i < SK → 0 ≤ env.loc (X_BASE + i) ∧ env.loc (X_BASE + i) < 2 ^ SB)
    (hby : ∀ i, i < SK → 0 ≤ env.loc (Y_BASE + i) ∧ env.loc (Y_BASE + i) < 2 ^ SB)
    (hbz : ∀ i, i < SK → 0 ≤ env.loc (Z_BASE + i) ∧ env.loc (Z_BASE + i) < 2 ^ SB)
    (hbq : ∀ i, i < SK → 0 ≤ env.loc (Q_BASE + i) ∧ env.loc (Q_BASE + i) < 2 ^ SB)
    (hbc : ∀ i, i < NG - 1 → 0 ≤ env.loc (C_BASE + i) ∧ env.loc (C_BASE + i) < 2 ^ CB) :
    (pN : ℤ) ∣ (sVal env.loc X_BASE * sVal env.loc Y_BASE - sVal env.loc Z_BASE) := by
  rcases hnonexc with h | h
  · exact szGate_holdsIn_forces_congruence env z isLast CHAL_Z _ _ _ _ _ pLimb (pN : ℤ)
      h1 h hbx hby hbz hbq pLimb_bounds pLimb_recomposes hbc
  · exact szGate_holdsIn_forces_congruence env z isLast CHAL_Z2 _ _ _ _ _ pLimb (pN : ℤ)
      h2 h hbx hby hbz hbq pLimb_bounds pLimb_recomposes hbc

/-- The `fqMul` twin. -/
theorem fqSzMulDesc_two_point_forces
    {K : Type*} [CommRing K] [IsDomain K] [DecidableEq K] [CharP K 2013265921]
    (env : VmRowEnv) (z : Nat → K) (isLast : Bool)
    (h1 : ChalConstraint.holdsIn env z isLast ⟨szBody qLimb CHAL_Z, false⟩)
    (h2 : ChalConstraint.holdsIn env z isLast ⟨szBody qLimb CHAL_Z2, false⟩)
    (hnonexc : z CHAL_Z ∉ exceptionalSet
        ((szResidual env.loc X_BASE Y_BASE Z_BASE Q_BASE C_BASE qLimb).map (Int.castRingHom K))
      ∨ z CHAL_Z2 ∉ exceptionalSet
        ((szResidual env.loc X_BASE Y_BASE Z_BASE Q_BASE C_BASE qLimb).map (Int.castRingHom K)))
    (hbx : ∀ i, i < SK → 0 ≤ env.loc (X_BASE + i) ∧ env.loc (X_BASE + i) < 2 ^ SB)
    (hby : ∀ i, i < SK → 0 ≤ env.loc (Y_BASE + i) ∧ env.loc (Y_BASE + i) < 2 ^ SB)
    (hbz : ∀ i, i < SK → 0 ≤ env.loc (Z_BASE + i) ∧ env.loc (Z_BASE + i) < 2 ^ SB)
    (hbq : ∀ i, i < SK → 0 ≤ env.loc (Q_BASE + i) ∧ env.loc (Q_BASE + i) < 2 ^ SB)
    (hbc : ∀ i, i < NG - 1 → 0 ≤ env.loc (C_BASE + i) ∧ env.loc (C_BASE + i) < 2 ^ CB) :
    (qN : ℤ) ∣ (sVal env.loc X_BASE * sVal env.loc Y_BASE - sVal env.loc Z_BASE) := by
  rcases hnonexc with h | h
  · exact szGate_holdsIn_forces_congruence env z isLast CHAL_Z _ _ _ _ _ qLimb (qN : ℤ)
      h1 h hbx hby hbz hbq qLimb_bounds qLimb_recomposes hbc
  · exact szGate_holdsIn_forces_congruence env z isLast CHAL_Z2 _ _ _ _ _ qLimb (qN : ℤ)
      h2 h hbx hby hbz hbq qLimb_bounds qLimb_recomposes hbc

/-- ⚑ **THE GATES THE THEOREMS QUANTIFY OVER ARE THE EMITTED ONES.** Both `chalGate`s consumed by
`fpSzMulDesc_two_point_forces` are, verbatim, constraints of `fpSzMulDesc` — so the `holdsIn`
hypotheses are the faithful denotations of bytes the descriptor actually carries, not of a
convenient stand-in. This membership plus `ChalConstraint.holdsIn` is the Lean-side weld to the
deployed `assert_zero_ext`; the Rust half (that `VmConstraint2::ChalGate` asserts exactly
`holdsIn`'s body through `assert_zero_ext`) is READ at `descriptor_ir2.rs` §"the challenge arm". -/
theorem fpSzMulDesc_carries_the_gates :
    VmConstraint2.chalGate ⟨szBody pLimb CHAL_Z, false⟩ ∈ fpSzMulDesc.constraints
      ∧ VmConstraint2.chalGate ⟨szBody pLimb CHAL_Z2, false⟩ ∈ fpSzMulDesc.constraints := by
  rw [fpSzMulDesc_eq_lowerAir]
  unfold lowerAir Dregg2.Circuit.Emit.EffectLower.assemble
  simp only [List.map_nil, List.nil_append, List.append_nil]
  unfold Dregg2.Circuit.Emit.EffectLower.lowerAirLegs
  constructor
  · refine List.mem_flatMap.mpr ⟨AirLeg.chal ⟨.all, szBody pLimb CHAL_Z⟩, ?_, ?_⟩
    · exact List.mem_cons_self ..
    · have hnr : Dregg2.Circuit.EffectAirIR.chalReadsNext (szBody pLimb CHAL_Z) = false := by
        decide
      simp [Dregg2.Circuit.Emit.EffectLower.lowerLeg,
        Dregg2.Circuit.Emit.EffectLower.lowerChalLeg, hnr]
  · refine List.mem_flatMap.mpr ⟨AirLeg.chal ⟨.all, szBody pLimb CHAL_Z2⟩, ?_, ?_⟩
    · exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
    · have hnr : Dregg2.Circuit.EffectAirIR.chalReadsNext (szBody pLimb CHAL_Z2) = false := by
        decide
      simp [Dregg2.Circuit.Emit.EffectLower.lowerLeg,
        Dregg2.Circuit.Emit.EffectLower.lowerChalLeg, hnr]

/-- **A residual vanishing at a non-exceptional challenge IS the zero polynomial.** The generic
Schwartz–Zippel step, restated over any integral domain so the deployed quartic extension is an
instance rather than a special case. (The `ChalConstraint`-shaped form of this fact is
`ChalSchwartzZippel.chalGate_forces_polynomial`.) -/
theorem sz_nonexceptional_forces_poly {K : Type*} [CommRing K] [IsDomain K] [DecidableEq K]
    (Res : Polynomial K) (z : K) (hz : Res.eval z = 0)
    (hnonexc : z ∉ exceptionalSet Res) :
    Res = 0 :=
  nonexceptional_eval_zero_forces_zero Res z hz hnonexc

/-- **And the exceptional set is SMALL** — at most the residual's degree, which for one multiply is
`2·SK − 2 = 62`. -/
theorem sz_exceptional_set_is_small {K : Type*} [CommRing K] [IsDomain K] [DecidableEq K]
    (Res : Polynomial K) :
    (exceptionalSet Res).card ≤ Res.natDegree :=
  exceptionalSet_card_le Res

/-! ### §6c′ — ⚑ BOTH POLES, IN LEAN — the tripwire the original defect walked past.

The old revision's theorems pinned counts, degree and plumbing, and NEVER asked whether an honest
witness satisfies the body — which is exactly what was false. These two theorems make that class of
defect a build break: the schoolbook's own honest witness (`PastaFieldSound.fpHonest`, offset
carries and all) makes the residual the ZERO polynomial, so BOTH emitted gates hold at EVERY
challenge; and the schoolbook's quotient-bump forgery makes it a NONZERO polynomial, so the gates
refuse it everywhere but the forgery's own ≤ 62-root exceptional set. -/

/-- ⚑ **FIRE: the honest witness's residual IS the zero polynomial.** Derived from the schoolbook's
`fpHonest_satisfies_gates` (every `coefBody` is exactly zero over ℤ) through `szResidual_eq_coefSum`
— the same route a satisfying witness for the OLD body provably did not exist through. -/
theorem fpHonest_szResidual_zero :
    szResidual fpHonest X_BASE Y_BASE Z_BASE Q_BASE C_BASE pLimb = 0 := by
  rw [szResidual_eq_coefSum]
  have hzero : ∀ m, m < NG →
      coefBody fpHonest X_BASE Y_BASE Z_BASE Q_BASE C_BASE pLimb m = 0 := by
    intro m hm
    have hall := List.all_eq_true.mp fpHonest_satisfies_gates m (List.mem_range.mpr hm)
    exact of_decide_eq_true hall
  rw [coeffPoly_congr _ (fun _ => (0 : ℤ)) NG hzero]
  unfold coeffPoly
  rw [sumR_congr _ _ (fun _ => (0 : Polynomial ℤ)) (fun i _ => by rw [map_zero, zero_mul]),
      sumR_zero]

/-- **…so both emitted gates hold at EVERY challenge, in every carrier** — the honest polarity of
the two-point core, as `ChalConstraint.holdsIn` on the exact gates the descriptor carries. -/
theorem fpHonest_gates_hold_at_every_challenge {K : Type*} [CommRing K]
    (z : Nat → K) (isLast : Bool) (nxt pub chal : Assignment) :
    ChalConstraint.holdsIn ⟨fpHonest, nxt, pub, chal⟩ z isLast ⟨szBody pLimb CHAL_Z, false⟩
      ∧ ChalConstraint.holdsIn ⟨fpHonest, nxt, pub, chal⟩ z isLast
          ⟨szBody pLimb CHAL_Z2, false⟩ := by
  constructor <;>
  · show (szBodyAt pLimb _ X_BASE Y_BASE Z_BASE Q_BASE C_BASE).evalIn
        (⟨fpHonest, nxt, pub, chal⟩ : VmRowEnv) z = 0
    rw [szBodyAt_evalIn]
    rw [show (⟨fpHonest, nxt, pub, chal⟩ : VmRowEnv).loc = fpHonest from rfl,
        fpHonest_szResidual_zero]
    simp

/-- ⚑ **BITE: the schoolbook's quotient-bump forgery has a NONZERO residual.** The same one-limb
bump `fpHonest_quotient_bump_is_caught` refutes gate-by-gate is refused here polynomial-wide: its
residual's constant coefficient is the schoolbook's nonzero body, so the polynomial is nonzero and
a drawn challenge accepts it only inside its ≤ 62-root exceptional set — the ledger's ε, not a free
pass. Together with FIRE above, the pair the old revision lacked: satisfiable for the honest,
refutable for the forged. -/
theorem fpHonest_quotient_bump_residual_nonzero :
    szResidual (fun c => if c = Q_BASE then fpHonest c + 1 else fpHonest c)
      X_BASE Y_BASE Z_BASE Q_BASE C_BASE pLimb ≠ 0 := by
  intro h
  have h0 := congrArg (fun p : Polynomial ℤ => p.coeff 0) h
  rw [szResidual_coeff _ _ _ _ _ _ _ 0 (by decide)] at h0
  exact fpHonest_quotient_bump_is_caught (by simpa using h0)

end Soundness

/-! ### §6d — ⚑ THE ε LEDGER, as named theorems.

Every number bracketed between adjacent powers of two, so no figure can be quoted off the
flattering end. `|K|` is the deployed `BinomialExtensionField<BabyBear, 4>`'s cardinality; the
per-gate numerator is the residual's challenge degree `2·SK − 2 = 62`; the wrap census is the
588,732-multiply workload (READ from the campaign brief, with a 2^33 robustness ceiling beside
it). The single-gate wrap-union verdict is the reason `szMulAir` carries TWO gates. -/

/-- The Schwartz–Zippel numerator for one multiply gate: the residual's challenge degree. -/
def SZ_SOUNDNESS_NUMERATOR : Nat := 2 * SK - 2

theorem SZ_SOUNDNESS_NUMERATOR_eq : SZ_SOUNDNESS_NUMERATOR = 62 := by decide

/-- ⚑ **THE DEPLOYED DENOMINATOR** — `|K| = p⁴` for `p = 2013265921`. It is the EXTENSION field's
cardinality, not BabyBear's `2^31`, because `ChalExpr` denotes in `K` and the deployed evaluator
asserts through `assert_zero_ext`. -/
def SZ_DENOMINATOR : Nat := 2013265921 ^ 4

/-- The wrap workload: how many multiplies share ONE per-instance challenge pair. READ from the
campaign census of the in-AIR Kimchi verifier (588,732 foreign-field multiplies across ~1.67M
rows); not re-derived here — which is why the bar verdicts are also stated at a 2^33 ceiling. -/
def SZ_WRAP_MULTIPLIES : Nat := 588732

/-- The wrap-union numerator: every multiply's 62-root exceptional set, unioned. -/
def SZ_WRAP_NUMERATOR : Nat := SZ_WRAP_MULTIPLIES * SZ_SOUNDNESS_NUMERATOR

/-- `|K| = 2^123.63` — strictly BETWEEN `2^123` and `2^124`. The file that says "2^124.0" is
quoting the flattering end; the bar arithmetic below uses the real one. -/
theorem sz_denominator_bracket :
    2 ^ 123 < SZ_DENOMINATOR ∧ SZ_DENOMINATOR < 2 ^ 124 := ⟨by decide, by decide⟩

/-- **Per-check, one gate: `ε = 62/|K| = 2^−117.7`** — bracketed: `2^−118 < ε < 2^−117`. -/
theorem sz_eps_single_bracket :
    SZ_SOUNDNESS_NUMERATOR * 2 ^ 117 < SZ_DENOMINATOR
      ∧ SZ_DENOMINATOR < SZ_SOUNDNESS_NUMERATOR * 2 ^ 118 := ⟨by decide, by decide⟩

/-- **Wrap-union, one gate: `ε = 588732·62/|K| = 2^−98.5`** — bracketed: `2^−99 < ε < 2^−98`. -/
theorem sz_eps_wrap_bracket :
    SZ_WRAP_NUMERATOR * 2 ^ 98 < SZ_DENOMINATOR
      ∧ SZ_DENOMINATOR < SZ_WRAP_NUMERATOR * 2 ^ 99 := ⟨by decide, by decide⟩

/-- ⚑ **THE VERDICT THAT MAKES THE SECOND GATE MANDATORY: one gate is BELOW the ~124-bit bar under
the wrap union.** `ε_wrap > 2^−124`, as a strict inequality on the naturals. A single-challenge sz
core must not ship on the per-check `2^−117.7`; that number prices ONE multiply, and 588,732 of
them share the draw. -/
theorem sz_single_challenge_is_below_the_bar :
    SZ_DENOMINATOR < SZ_WRAP_NUMERATOR * 2 ^ 124 := by decide

/-- **Two-point, wrap-union: `ε = (588732·62/|K|)² = 2^−197.0`** — bracketed:
`2^−198 < ε < 2^−197`. -/
theorem sz_eps_two_point_bracket :
    SZ_WRAP_NUMERATOR ^ 2 * 2 ^ 197 < SZ_DENOMINATOR ^ 2
      ∧ SZ_DENOMINATOR ^ 2 < SZ_WRAP_NUMERATOR ^ 2 * 2 ^ 198 := ⟨by decide, by decide⟩

/-- ⚑ **The two-point form CLEARS the bar**: `ε < 2^−124`, with 73 bits of margin. -/
theorem sz_two_point_clears_the_bar :
    SZ_WRAP_NUMERATOR ^ 2 * 2 ^ 124 < SZ_DENOMINATOR ^ 2 := by decide

/-- **…and the verdict survives the census being wrong by three orders of magnitude**: even at a
`2^33`-multiply workload (14× the read census, and more rows than any deployed trace holds) the
two-point ε stays under `2^−124`. -/
theorem sz_two_point_bar_robust_to_census :
    (2 ^ 33 * SZ_SOUNDNESS_NUMERATOR) ^ 2 * 2 ^ 124 < SZ_DENOMINATOR ^ 2 := by decide

/-- And the base-field alternative is BELOW the bar, exhibited rather than described — the reason
the leaf denotes in the extension. -/
theorem base_field_challenge_would_be_below_bar :
    SZ_SOUNDNESS_NUMERATOR * 2 ^ 100 > 2013265921 := by decide

/-! ## §7 — axiom hygiene. -/

#assert_axioms szMulAir_mainRailOk
#assert_axioms fpSzMulDesc_constraint_count
#assert_axioms fqSzMulDesc_constraint_count
#assert_axioms fpSzMulDesc_declares_two_challenges
#assert_axioms fpSzMulDesc_chalGateCount
#assert_axioms fpSzMulDesc_chal_indices_distinct
#assert_axioms fqSzMulDesc_chal_indices_distinct
#assert_axioms gate_collapse
#assert_axioms width_and_lookups_unchanged
#assert_axioms sz_arithmetic_is_linear
#assert_axioms schoolbook_arithmetic_is_quadratic
#assert_axioms sz_arithmetic_ratio
#assert_axioms sz_body_is_degree_two
#assert_axioms sz_batch_is_degree_two
#assert_axioms szResidual_eq_coefSum
#assert_axioms szResidual_coeff
#assert_axioms szPoly_forces_congruence
#assert_axioms szBodyAt_evalIn
#assert_axioms szGate_holdsIn_forces_congruence
#assert_axioms fpSzMulDesc_two_point_forces
#assert_axioms fqSzMulDesc_two_point_forces
#assert_axioms fpSzMulDesc_carries_the_gates
#assert_axioms fpHonest_szResidual_zero
#assert_axioms fpHonest_gates_hold_at_every_challenge
#assert_axioms fpHonest_quotient_bump_residual_nonzero
#assert_axioms SZ_SOUNDNESS_NUMERATOR_eq
#assert_axioms sz_denominator_bracket
#assert_axioms sz_eps_single_bracket
#assert_axioms sz_eps_wrap_bracket
#assert_axioms sz_single_challenge_is_below_the_bar
#assert_axioms sz_eps_two_point_bracket
#assert_axioms sz_two_point_clears_the_bar
#assert_axioms sz_two_point_bar_robust_to_census

end Dregg2.Circuit.Emit.PastaSzMul
