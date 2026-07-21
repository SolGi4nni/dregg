/-
# `Dregg2.Circuit.TfhePbsRefinement` — Lean authority for the exact PBS seam

This file specifies the native-`2^64` torus boundary implemented by
`fhegg-fhe/src/shaders/torus_pbs_extract_keyswitch.wgsl`:

```
blind rotation → degree-zero GLWE sample extraction → standard LWE key switch
```

The useful content here is deliberately narrower than “the WGSL is verified”.

* `sampleExtractZero` is the typed, pure Lean authority for degree-zero sample
  extraction.  Its two sign theorems pin the exact tfhe-rs convention: the
  constant mask coefficient is copied, while every non-constant coefficient is
  read in reverse order and negated.
* `keySwitch` is the standard subtractive LWE key-switch relation, parameterised
  by the signed gadget-decomposition digits.  The types force an input row for
  every extracted `(mask polynomial, coefficient, level)` and exactly one LWE
  ciphertext of output dimension `outDim` per row.
* `pbs` composes an abstract blind rotation with those two exact stages.
  `wgpu_refines_pbs` turns an EXPLICIT byte/element correspondence premise into
  the semantic postcondition and exposes the sign and dimension facts together.

The external premise is load-bearing.  Rust's independent tfhe-rs differential
currently supplies empirical evidence for it; no theorem in this file connects
WGSL buffers, dispatch order, limb arithmetic, or wgpu execution to these Lean
functions.  Consequently this is a Lean-first authority/refinement target for
the boundary, not a verification claim about the shader.
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.ZMod.Basic
import Dregg2.Tactics

namespace Dregg2.Circuit.TfhePbsRefinement

set_option autoImplicit false

open scoped BigOperators

/-- The exact native TFHE torus used by the Rust and WGSL implementations. -/
abbrev Torus := ZMod (2 ^ 64)

/-- A GLWE ciphertext with `maskPolys` mask polynomials of degree `degree` and
one body polynomial.  Thus its flattened GLWE size is `maskPolys + 1`. -/
structure Glwe (maskPolys degree : Nat) where
  mask : Fin maskPolys → Fin degree → Torus
  body : Fin degree → Torus

/-- An LWE ciphertext indexed by its mask coordinates. -/
structure Lwe (ι : Type) where
  mask : ι → Torus
  body : Torus

/-- The flattened tfhe-rs/WGSL index of a GLWE mask coefficient. -/
def flatMaskIndex {maskPolys degree : Nat} (i : Fin maskPolys × Fin degree) : Nat :=
  i.1.val * degree + i.2.val

/-- Flattening the structured extraction index never leaves the exact
`maskPolys * degree` input-LWE envelope. -/
theorem flatMaskIndex_lt {maskPolys degree : Nat}
    (i : Fin maskPolys × Fin degree) :
    flatMaskIndex i < maskPolys * degree := by
  calc
    flatMaskIndex i < i.1.val * degree + degree :=
      Nat.add_lt_add_left i.2.isLt (i.1.val * degree)
    _ = (i.1.val + 1) * degree := by
      simp only [Nat.add_mul, Nat.one_mul]
    _ ≤ maskPolys * degree :=
      Nat.mul_le_mul_right degree (Nat.succ_le_iff.mpr i.1.isLt)

/-- The negacyclic source index used when extracting coefficient zero:
`j ↦ degree-j` for every nonzero `j`. -/
def reversedNonzeroIndex {degree : Nat} [NeZero degree]
    (j : Fin degree) (hj : j ≠ 0) : Fin degree :=
  ⟨degree - j.val, by
    have hdegree : 0 < degree := Nat.zero_lt_of_lt j.isLt
    have hjval : 0 < j.val := by
      exact Nat.pos_of_ne_zero (fun hzero => hj (Fin.ext (by simpa using hzero)))
    exact Nat.sub_lt hdegree hjval⟩

/-- Degree-zero GLWE sample extraction, with the exact standard negacyclic sign
convention used by tfhe-rs and the fused WGSL kernel. -/
def sampleExtractZero {maskPolys degree : Nat} [NeZero degree]
    (ct : Glwe maskPolys degree) : Lwe (Fin maskPolys × Fin degree) where
  mask i :=
    if hzero : i.2 = 0 then
      ct.mask i.1 0
    else
      -ct.mask i.1 (reversedNonzeroIndex i.2 hzero)
  body := ct.body 0

/-- The constant coefficient of every GLWE mask polynomial is copied with a
positive sign.  This is the `local == 0` branch in the WGSL kernel. -/
@[simp] theorem sampleExtractZero_mask_zero {maskPolys degree : Nat} [NeZero degree]
    (ct : Glwe maskPolys degree) (poly : Fin maskPolys) :
    (sampleExtractZero ct).mask (poly, 0) = ct.mask poly 0 := by
  simp [sampleExtractZero]

/-- Every non-constant coefficient is read at `degree-local` and negated.  This
is the load-bearing negacyclic sign branch in the WGSL kernel. -/
theorem sampleExtractZero_mask_nonzero {maskPolys degree : Nat} [NeZero degree]
    (ct : Glwe maskPolys degree) (poly : Fin maskPolys) (coeff : Fin degree)
    (hcoeff : coeff ≠ 0) :
    (sampleExtractZero ct).mask (poly, coeff) =
      -ct.mask poly (reversedNonzeroIndex coeff hcoeff) := by
  simp [sampleExtractZero, hcoeff]

/-- Degree-zero extraction copies the constant coefficient of the GLWE body. -/
@[simp] theorem sampleExtractZero_body {maskPolys degree : Nat} [NeZero degree]
    (ct : Glwe maskPolys degree) :
    (sampleExtractZero ct).body = ct.body 0 := rfl

/-- A standard key-switch key: one output LWE ciphertext for every input mask
coordinate and gadget-decomposition level. -/
abbrev KeySwitchKey (ι : Type) (levels outDim : Nat) :=
  ι → Fin levels → Lwe (Fin outDim)

/-- Exact subtractive standard-LWE key switching.  `digits` is the signed
gadget decomposer; keeping it explicit makes the arithmetic seam honest while
the extraction signs and all dimensions remain fully fixed here. -/
def keySwitch {ι : Type} [Fintype ι] {levels outDim : Nat}
    (digits : Torus → Fin levels → Torus)
    (ksk : KeySwitchKey ι levels outDim) (input : Lwe ι) : Lwe (Fin outDim) where
  mask out :=
    -∑ i : ι, ∑ level : Fin levels,
      digits (input.mask i) level * (ksk i level).mask out
  body :=
    input.body - ∑ i : ι, ∑ level : Fin levels,
      digits (input.mask i) level * (ksk i level).body

@[simp] theorem keySwitch_mask {ι : Type} [Fintype ι] {levels outDim : Nat}
    (digits : Torus → Fin levels → Torus)
    (ksk : KeySwitchKey ι levels outDim) (input : Lwe ι) (out : Fin outDim) :
    (keySwitch digits ksk input).mask out =
      -∑ i : ι, ∑ level : Fin levels,
        digits (input.mask i) level * (ksk i level).mask out := rfl

@[simp] theorem keySwitch_body {ι : Type} [Fintype ι] {levels outDim : Nat}
    (digits : Torus → Fin levels → Torus)
    (ksk : KeySwitchKey ι levels outDim) (input : Lwe ι) :
    (keySwitch digits ksk input).body =
      input.body - ∑ i : ι, ∑ level : Fin levels,
        digits (input.mask i) level * (ksk i level).body := rfl

/-- Number of native-torus coefficients in the flattened standard KSK consumed
by the fused kernel. -/
def keySwitchCoefficientCount (inputDim levels outDim : Nat) : Nat :=
  inputDim * levels * (outDim + 1)

/-- Native-torus coefficients in one standard-domain GGSW ciphertext for a
GLWE with `maskPolys + 1` polynomials. -/
def ggswCoefficientCount (maskPolys degree levels : Nat) : Nat :=
  levels * (maskPolys + 1) * (maskPolys + 1) * degree

/-- Native-torus coefficients in the complete standard bootstrapping key. -/
def bootstrappingKeyCoefficientCount
    (inputDim maskPolys degree levels : Nat) : Nat :=
  inputDim * ggswCoefficientCount maskPolys degree levels

/-- The fail-closed arithmetic shape enforced by the Rust primitive before the
fused kernel is dispatched.  `baseLog * levels < 64` leaves at least one
non-represented torus bit, exactly as the signed decomposer requires. -/
def ValidPbsShape (maskPolys degree baseLog levels outDim : Nat) : Prop :=
  0 < maskPolys ∧ 0 < degree ∧ 0 < baseLog ∧ baseLog ≤ 31 ∧
  0 < levels ∧ baseLog * levels < 64 ∧ 0 < outDim

instance (maskPolys degree baseLog levels outDim : Nat) :
    Decidable (ValidPbsShape maskPolys degree baseLog levels outDim) := by
  unfold ValidPbsShape
  infer_instance

/-- A valid GLWE shape always extracts a nonempty standard-LWE mask. -/
theorem validPbsShape_inputDimension_pos {maskPolys degree baseLog levels outDim : Nat}
    (h : ValidPbsShape maskPolys degree baseLog levels outDim) :
    0 < maskPolys * degree := Nat.mul_pos h.1 h.2.1

/-- A valid standard key-switch shape always has a nonempty flattened KSK. -/
theorem validPbsShape_keySwitchCount_pos
    {maskPolys degree baseLog levels outDim : Nat}
    (h : ValidPbsShape maskPolys degree baseLog levels outDim) :
    0 < keySwitchCoefficientCount (maskPolys * degree) levels outDim := by
  unfold keySwitchCoefficientCount
  exact Nat.mul_pos (Nat.mul_pos (validPbsShape_inputDimension_pos h) h.2.2.2.2.1)
    (Nat.succ_pos outDim)

/-- The degree-zero extracted LWE dimension is exactly
`maskPolys * degree`, so the standard KSK has precisely the Rust/WGSL flattened
shape `(maskPolys*degree) * levels * (outDim+1)`. -/
theorem extracted_keySwitchCoefficientCount (maskPolys degree levels outDim : Nat) :
    keySwitchCoefficientCount (maskPolys * degree) levels outDim =
      maskPolys * degree * levels * (outDim + 1) := rfl

/-- The final flattened LWE ciphertext contains `outDim` mask coefficients and
one body coefficient. -/
def outputLweCoefficientCount (outDim : Nat) : Nat := outDim + 1

/-- Pure Lean semantics of the three-stage PBS boundary.  `blindRotate` is kept
abstract in this first authority slice because the present WGPU blind-rotation
implementation is validated by an external differential, not emitted from Lean. -/
def pbs {maskPolys degree levels outDim : Nat} [NeZero degree]
    (blindRotate : Glwe maskPolys degree → Glwe maskPolys degree)
    (digits : Torus → Fin levels → Torus)
    (ksk : KeySwitchKey (Fin maskPolys × Fin degree) levels outDim)
    (accumulator : Glwe maskPolys degree) : Lwe (Fin outDim) :=
  keySwitch digits ksk (sampleExtractZero (blindRotate accumulator))

/-- The explicit external correspondence predicate for a WGPU result.  This is
the only bridge from an implementation-produced value into the Lean authority;
proving it from WGSL semantics remains a separate translation-validation task. -/
def WgpuRefinesPbs {maskPolys degree levels outDim : Nat} [NeZero degree]
    (blindRotate : Glwe maskPolys degree → Glwe maskPolys degree)
    (digits : Torus → Fin levels → Torus)
    (ksk : KeySwitchKey (Fin maskPolys × Fin degree) levels outDim)
    (accumulator : Glwe maskPolys degree) (wgpuOutput : Lwe (Fin outDim)) : Prop :=
  wgpuOutput = pbs blindRotate digits ksk accumulator

/-- **Composed authority theorem.**  Under the explicit WGPU correspondence
premise, the returned ciphertext is exactly blind-rotation followed by the
standard signed degree-zero extraction and subtractive key switch.  The theorem
also exposes the two extraction sign branches and both exact flattened shapes.

No shader fact is smuggled into the theorem: `hrefines` is load-bearing. -/
theorem wgpu_refines_pbs {maskPolys degree levels outDim : Nat} [NeZero degree]
    (blindRotate : Glwe maskPolys degree → Glwe maskPolys degree)
    (digits : Torus → Fin levels → Torus)
    (ksk : KeySwitchKey (Fin maskPolys × Fin degree) levels outDim)
    (accumulator : Glwe maskPolys degree) (wgpuOutput : Lwe (Fin outDim))
    (hrefines : WgpuRefinesPbs blindRotate digits ksk accumulator wgpuOutput) :
    wgpuOutput = keySwitch digits ksk (sampleExtractZero (blindRotate accumulator)) ∧
    (∀ poly : Fin maskPolys,
      (sampleExtractZero (blindRotate accumulator)).mask (poly, 0) =
        (blindRotate accumulator).mask poly 0) ∧
    (∀ (poly : Fin maskPolys) (coeff : Fin degree) (hcoeff : coeff ≠ 0),
      (sampleExtractZero (blindRotate accumulator)).mask (poly, coeff) =
        -(blindRotate accumulator).mask poly (reversedNonzeroIndex coeff hcoeff)) ∧
    keySwitchCoefficientCount (maskPolys * degree) levels outDim =
      maskPolys * degree * levels * (outDim + 1) ∧
    outputLweCoefficientCount outDim = outDim + 1 := by
  refine ⟨hrefines, ?_, ?_, rfl, rfl⟩
  · intro poly
    exact sampleExtractZero_mask_zero (blindRotate accumulator) poly
  · intro poly coeff hcoeff
    exact sampleExtractZero_mask_nonzero (blindRotate accumulator) poly coeff hcoeff

/-! ## Sign-convention falsifier.

This two-coefficient GLWE makes the negative reversed tail observably different
from the tempting but wrong positive-tail extraction. -/

def signToothGlwe : Glwe 1 2 where
  mask _ coeff := if coeff = 0 then 5 else 7
  body _ := 11

theorem signTooth_extracts_negative_tail :
    (sampleExtractZero signToothGlwe).mask (0, 1) = -(7 : Torus) := by
  norm_num [sampleExtractZero, signToothGlwe, reversedNonzeroIndex]

theorem signTooth_refuses_positive_tail :
    (sampleExtractZero signToothGlwe).mask (0, 1) ≠ (7 : Torus) := by
  norm_num [sampleExtractZero, signToothGlwe, reversedNonzeroIndex]
  decide

/-! ## Concrete deployed-shape teeth.

The present independent tfhe-rs qualification uses one GLWE mask polynomial,
degree 2048, a 2048-dimensional extracted LWE, four KS levels, and an
8-dimensional qualification output. The production-shaped prepared-plan gate
then uses the same extracted input with all 918 post-key-switch mask outputs and
the complete 918-slot BSK/KSK footprint. Only four BSK slots execute CMUX in
that gate, so these shape teeth make no dense-rotation performance claim. -/

#guard 1 * 2048 = 2048
#guard decide (ValidPbsShape 1 2048 4 4 8)
#guard keySwitchCoefficientCount (1 * 2048) 4 8 = 73728
#guard outputLweCoefficientCount 8 = 9
#guard decide (ValidPbsShape 1 2048 4 4 918)
#guard ggswCoefficientCount 1 2048 1 = 8192
#guard bootstrappingKeyCoefficientCount 918 1 2048 1 = 7520256
#guard keySwitchCoefficientCount (1 * 2048) 4 918 = 7528448
#guard outputLweCoefficientCount 918 = 919

#assert_axioms flatMaskIndex_lt
#assert_axioms sampleExtractZero_mask_zero
#assert_axioms sampleExtractZero_mask_nonzero
#assert_axioms validPbsShape_keySwitchCount_pos
#assert_axioms wgpu_refines_pbs
#assert_axioms signTooth_extracts_negative_tail
#assert_axioms signTooth_refuses_positive_tail

end Dregg2.Circuit.TfhePbsRefinement
