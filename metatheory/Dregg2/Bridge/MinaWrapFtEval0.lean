/-
# Dregg2.Bridge.MinaWrapFtEval0 — **`ft_eval0`, DERIVED per block from the wire, on BOTH sides of
the Pasta cycle. The named residual of `MinaWrapDeferredWeld`, addressed rather than restated.**

⚑ **SUBSTRATE.** No AIR. This file authors **no arithmetic at all**: it instantiates
`Dregg2.Circuit.Emit.KimchiVerify`'s existing `[CommRing R]` bodies — `gateLinConst` (the six
transcribed gate constraints), `ftEval0R`, `cipR`, `endoMap`, `sqIter` — at `ZMod pN` and
`ZMod qN`, and adds the wire grammar around them. **There is deliberately no `Nat`-mod mirror of a
gate body here**: a second copy of `poseidonConstraints` would be a twin, and the tree's own census
note says a `def` with no `@[export]` is the best predictor there is one. One body, two moduli.

## The residual this addresses, quoted from the file that named it

`MinaWrapDeferredWeld` §6:

> after this file the per-block path's residual is **two `ft_eval0`s** — the Step one (this file's
> `FT_EVAL0`, for `public_comm`) and the Wrap one (for `cipShifted`) — and nothing else.

and, at `FT_EVAL0` itself:

> ⚑⚑ **SOLVED FROM SLOT 0, NOT DERIVED.** `cipOf` is affine in this argument and it enters at
> exactly one index, so this value is whatever makes §4 hold.

Both halves are the SAME computation in two fields, and this tree already has that computation.
What it has never had is the two `ft_eval0`s' **inputs assembled from a block's own bytes**, and
what it has never done is **run `gateLinConst` on a proof whose four unexercised gate selectors are
non-zero.** Both are here; the measurement is `MinaWrapFtEval0Weld`.

## ⚑⚑ THE FINDING THAT MAKES THIS CHEAP, and it was sitting in the fixture

`KimchiVerify.gateLinConst` transcribes all six v1 gate bodies — generic (2 constraints), Poseidon
(15), complete_add (7), varbasemul (21), endomul (12), endomul_scalar (11) — and
`KimchiPoseidonGate` reproduced Rust's `PolishToken::evaluate(constant_term)` with it. But its two
fixtures had **`caddSel = mulSel = emulSel = emulScalarSel = 0`**, so four of the six bodies rested
on a source reading and nothing else, and `MinaRealBlockGate` consequently CARRIES `LCT` as a
literal instead of deriving it.

`MinaRealBlockGate.EVZ` slots 5-10 are the real devnet block's six gate selectors at ζ, and
**none of them is zero.** So the real Mina Wrap proof fires every gate the transcription covers,
and `gateLinConst` over that block's own 43 evaluation columns is a genuine differential against
`LCT` — the first one those four bodies have ever had.

Every input `gateLinConst` wants is on the wire: `Plonk_types.Evals` is
`[z] ++ selectors(6) ++ w(15) ++ coefficients(15) ++ s(6)` = 43 columns at ζ AND at ζω, and
`bridge/src/mina_pickles.rs` `decode_proof_at` walks all 86 of them (Wrap side) and all 86 more
(Step side, `prev_evals`) and discards every one.

## What is CONFIG here, and it is named rather than absorbed

Four objects are not on the wire and are passed as arguments so a reader can see them:

  * `er` — the endomorphism scalar of the challenge lift (`ScalarChallenge::to_field`). Fq side:
    `PastaCurve.lambdaPallas`. Fp side: `KimchiPoseidonGate.ENDO_R`.
  * `endo` — `env.endo_coefficient()`, the verifier index's `endo`. ⚑ **A DIFFERENT CONSTANT from
    `er`**, read by exactly one gate (`endoMulConstraints`) and by nothing else. Conflating the two
    produces a complete, self-consistent, entirely wrong `linConstTerm`.
  * `sh` — the seven coset `shifts` of the domain. Read only by `ftEval0R`'s denominator fold.
  * `mds` — the 3×3 Poseidon MDS of the field's sponge parameters, read only by the Poseidon body.

`omega`, `n`, `alpha^21..23` and the three `EndomulScalar` quotient constants are **DERIVED**, not
carried: `rootOfUnity` builds the domain generator from the two-adicity and the multiplicative
generator 5, and `quotientConsts` builds `11/6, −5/2, 2/3` from a checked inverse.

## ⚑ The inverses, and why nothing here trusts primality

`ftEval0R` wants `((ζ − ω^{n−3})(ζ − 1))⁻¹` and the public-evaluation Lagrange fold wants one
inverse per public word. `ZMod m` has no `Field` instance in this tree (no in-kernel primality
proof of a 255-bit modulus), so [`invCand`] produces a CANDIDATE by Fermat's ladder and every use
site **checks `x · y = 1` in the ring** ([`invOk`]). A composite modulus, or a non-invertible `x`,
therefore produces a REFUSAL rather than a wrong number. This is the witnessed-inverse device
`KimchiVerify` §9b already uses for `denomInv`, with the witness produced locally instead of
carried, so no field arithmetic crosses into Rust.

## What this establishes and what it does NOT

**Establishes:** given a block's 86 evaluation values, its four raw plonk challenges, its domain
log2 and the four named config objects, `ft_eval0` and the whole linearization constant term are
computable, compiled, at sponge-free cost.

**Does not:** it does not verify anything. `ft_eval0` is one input to the opening equation, not the
equation. And the derivation is only as good as `gateLinConst`'s transcription of the four gates no
differential ever exercised — which is precisely what `MinaWrapFtEval0Weld` measures, and until
that file is green nothing here should be described as closing anything.

## Cost and closure

Compiled, not kernel: every pin is `#guard`. The kernel's job stays the CHECKER (§6's shape
refusals). ⚑ Rooting this in `Dregg2/FFI.lean` costs **+0 modules**: `KimchiVerify` is already in
the archive closure (`FFI.lean` measured it in with `PicklesWrapShapeGate` on 2026-07-29, and
`PicklesProofChainGate` re-measured `+0` for the same reason). The heavy one-block literals stay in
`MinaRealBlockGate`, which this file does NOT import — the weld does, and the weld is not rooted.
-/
import Dregg2.Circuit.Emit.KimchiVerify
import Dregg2.Circuit.Emit.PastaField

set_option autoImplicit false
set_option maxRecDepth 40000

namespace Dregg2.Bridge.MinaWrapFtEval0

open Dregg2.Circuit.Emit.PastaField (pN qN)
open Dregg2.Circuit.Emit.KimchiVerify
  (PERMUTS COLUMNS GateEvals gateLinConst ftEval0R cipR zkPolyR endoMap sqIter
   endomulScalarConstsOk)

/-! ## §1 — the two ladders, over any `Monoid`.

`KimchiVerify.sqIter` is the squaring ladder and is reused verbatim. What it does not have is a
general square-and-multiply, and `ZMod m`'s `Monoid.npow` is unary: `x ^ ((m − 3) / 2)` at a 255-bit
modulus would be `2^254` multiplications. -/

/-- `powFast`'s worker, structurally recursive on FUEL. The exit at `e = 0` is an `if` rather than a
second pattern so the recursion is on the fuel ALONE — the shape `MinaWrapDeferred.powModAux` uses,
and for the same reason: the kernel reduces it. -/
def powFastAux {R : Type} [Monoid R] : Nat → R → Nat → R → R
  | 0, _, _, acc => acc
  | fuel + 1, b, e, acc =>
      if e = 0 then acc
      else powFastAux fuel (b * b) (e / 2) (if e % 2 = 1 then acc * b else acc)

/-- **`powFast b e`** — `b ^ e` by square-and-multiply. 512 bits of fuel covers every exponent this
file forms (the largest is `m − 2` at a 255-bit modulus). -/
def powFast {R : Type} [Monoid R] (b : R) (e : Nat) : R := powFastAux 512 b e 1

/-- `powFast` computes the power it names, on values small enough that the kernel checks BOTH sides.
This is the tie between the ladder and the exponent it stands for. -/
theorem powFast_is_pow :
    powFast (3 : Nat) 0 = 1 ∧ powFast (3 : Nat) 1 = 3 ∧ powFast (3 : Nat) 7 = 3 ^ 7
    ∧ powFast (5 : Nat) 40 = 5 ^ 40 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-! ## §2 — inverses, WITNESSED rather than trusted.

Nothing below assumes the modulus is prime. [`invCand`] is a heuristic that produces a candidate;
[`invOk`] is the check, and every consumer refuses when it fails. -/

/-- A CANDIDATE inverse by Fermat's ladder. ⚑ Correct only when the modulus is prime and `x ≠ 0` —
which is why no consumer uses it without [`invOk`]. -/
def invCand {m : Nat} (x : ZMod m) : ZMod m := powFast x (m - 2)

/-- The check that makes [`invCand`] safe: a unit's inverse is unique in any monoid, so `x · y = 1`
pins `y` without a `Field` instance, a primality proof, or a division. -/
def invOk {m : Nat} (x y : ZMod m) : Bool := decide (x * y = 1)

/-- The witnessed inverse, or `none`. `none` is a REFUSAL and every caller treats it as one. -/
def inv? {m : Nat} (x : ZMod m) : Option (ZMod m) :=
  let y := invCand x
  if invOk x y then some y else none

/-! ## §3 — the domain, DERIVED.

`Backend.Tick.Field.domain_generator ~log2_size` / `Tock`'s. Both Pasta fields have two-adicity 32
and arkworks' multiplicative `GENERATOR = 5`, so one function serves both. Deriving it rather than
carrying it removes a trusted 255-bit literal per field; the weld pins its exact order. -/

/-- Both Pasta scalar fields' two-adicity. -/
def TWO_ADICITY : Nat := 32

/-- arkworks' `FpConfig::GENERATOR` for both Pasta fields. -/
def GENERATOR : Nat := 5

/-- **`rootOfUnity m log2n`** — the `2^log2n`-th root of unity of `ZMod m`: the multiplicative
generator raised to the odd part of `m − 1`, then squared down. -/
def rootOfUnity (m : Nat) (log2n : Nat) : ZMod m :=
  sqIter (TWO_ADICITY - log2n) (powFast ((GENERATOR : Nat) : ZMod m) ((m - 1) / 2 ^ TWO_ADICITY))

/-! ## §4 — the three `EndomulScalar` quotient constants, DERIVED and CHECKED.

`endomul_scalar.rs:188-193` writes `11/6, −5/2, 2/3` as field divisions. `KimchiVerify` takes them
as witnessed ring elements and checks `6·cA = 11`, `2·cB = −5`, `3·cC = 2`
(`endomulScalarConstsOk`). This builds the witnesses instead of carrying them, and the check stays
exactly where it was. -/

/-- `(11/6, −5/2, 2/3)` in `ZMod m`, or `none` when 2, 3 or 6 is not invertible there. -/
def quotientConsts (m : Nat) : Option (ZMod m × ZMod m × ZMod m) :=
  match inv? ((6 : Nat) : ZMod m), inv? ((2 : Nat) : ZMod m), inv? ((3 : Nat) : ZMod m) with
  | some i6, some i2, some i3 => some (11 * i6, -5 * i2, 2 * i3)
  | _, _, _ => none

/-! ## §5 — the 43 evaluation columns, SLICED HERE.

`Plonk_types.Evals.to_absorption_sequence` (`plonk_types.ml:487-499`) is
`[z] ++ [generic, poseidon, complete_add, mul, emul, endomul_scalar] ++ w(15) ++ coefficients(15)
++ s(6)`, and the SAME list in the SAME order is `Evals.to_list`, which is what the
`combined_inner_product` fold walks.

⚑ The slicing is done here and not by the caller, for the reason `MinaWrapChallenges` re-chunks a
flat `lr` here and not by the caller: a caller that slices is a caller that can mis-slice, and a
mis-sliced column list does not fail — it produces a different, perfectly well-formed `ft_eval0`. -/

/-- Column indices, named once. -/
def IDX_Z : Nat := 0
/-- The first of the six gate selectors. -/
def IDX_SEL : Nat := 1
/-- The first of the 15 witness columns. -/
def IDX_W : Nat := 7
/-- The first of the 15 coefficient columns. -/
def IDX_COEFF : Nat := 22
/-- The first of the six σ columns. -/
def IDX_S : Nat := 37
/-- `[z] + 6 + 15 + 15 + 6`. -/
def NCOLS : Nat := 43

/-- ⚑ **THE SHAPE REFUSAL.** An evaluation list is positional: 42 columns instead of 43 does not
fail, it slides `w`, `coefficients` and `s` by one and derives a wrong `ft_eval0` that is
self-consistent all the way to the IPA challenges. -/
def colsOk {m : Nat} (ez ew sh mds9 : List (ZMod m)) (log2n : Nat) : Bool :=
  ez.length == NCOLS && ew.length == NCOLS && sh.length == PERMUTS && mds9.length == 9
    && decide (0 < log2n) && decide (log2n ≤ TWO_ADICITY)

/-- The MDS as `KimchiVerify` wants it — three rows of three, from the flat nine. -/
def mdsRows {m : Nat} (mds9 : List (ZMod m)) : List (List (ZMod m)) :=
  [mds9.take 3, (mds9.drop 3).take 3, (mds9.drop 6).take 3]

/-! ## §6 — the per-side inputs, as ONE record. -/

/-- **Everything one side of the Pasta cycle needs.** Field names are the wire's or the config
object's; nothing here is a slot index. -/
structure SideWire (m : Nat) where
  /-- `log2` of the evaluation domain — `branch_data.domain_log2` on the Step side, the verifier
  index's `domain.log_size_of_group` on the Wrap side. -/
  log2n : Nat
  /-- `deferred_values.plonk.alpha`, the RAW 128-bit `ScalarChallenge`. Lifted here. -/
  alphaChal : Nat
  /-- `deferred_values.plonk.beta`, RAW and NOT lifted — `beta` enters the constraints as the raw
  squeeze (`MinaWrapDeferred` §8's slot-5/6/7 correction is about the same three values). -/
  betaChal : Nat
  /-- `deferred_values.plonk.gamma`, RAW. -/
  gammaChal : Nat
  /-- `deferred_values.plonk.zeta`, the RAW `ScalarChallenge`. Lifted here. -/
  zetaChal : Nat
  /-- The 43 columns at ζ, in `to_absorption_sequence` order. WIRE. -/
  ez : List (ZMod m)
  /-- The 43 columns at ζω, same order. WIRE. -/
  ew : List (ZMod m)
  /-- `public_evals[0]` — the public polynomial at ζ, ALREADY NEGATED as kimchi computes it. On the
  wire on the Step side (`prev_evals.evals.public_input.0`); on the Wrap side it is
  [`publicEvalAt`] over the forty public-input words. -/
  pZeta : ZMod m
  /-- `ScalarChallenge::to_field`'s endomorphism scalar. ⚑ CONFIG. -/
  er : ZMod m
  /-- `env.endo_coefficient()` = the verifier index's `endo`. ⚑ CONFIG, and NOT `er`. -/
  endo : ZMod m
  /-- The seven coset `shifts`. ⚑ CONFIG. -/
  sh : List (ZMod m)
  /-- The Poseidon MDS, flat, row-major. ⚑ CONFIG. -/
  mds9 : List (ZMod m)

/-- The gate-constraint environment this side describes — `KimchiVerify.GateEvals`, assembled by
slicing §5's indices rather than by a caller. -/
def gateEvalsOf {m : Nat} (W : SideWire m) (cA cB cC : ZMod m) : GateEvals (ZMod m) :=
  { alpha := endoMap W.er W.alphaChal
    endo := W.endo
    mds := mdsRows W.mds9
    coeff := (W.ez.drop IDX_COEFF).take COLUMNS
    w := (W.ez.drop IDX_W).take COLUMNS
    wNext := (W.ew.drop IDX_W).take COLUMNS
    cA := cA, cB := cB, cC := cC
    genSel := W.ez.getD (IDX_SEL + 0) 0
    posSel := W.ez.getD (IDX_SEL + 1) 0
    caddSel := W.ez.getD (IDX_SEL + 2) 0
    mulSel := W.ez.getD (IDX_SEL + 3) 0
    emulSel := W.ez.getD (IDX_SEL + 4) 0
    emulScalarSel := W.ez.getD (IDX_SEL + 5) 0 }

/-- What one side's derivation produces. -/
structure SideOut (m : Nat) where
  /-- The evaluation domain size `2^log2n`. -/
  n : Nat
  /-- The derived domain generator. -/
  omega : ZMod m
  /-- `ζ`, lifted. -/
  zeta : ZMod m
  /-- `α`, lifted. -/
  alpha : ZMod m
  /-- ⚑ **The linearization constant term, DERIVED** — `Σ_gate selector·(Σᵢ αⁱ·constraintᵢ)` over
  all six transcribed bodies. This is the value `MinaRealBlockGate` carries as `LCT`. -/
  linConstTerm : ZMod m
  /-- ⚑ **`ft_eval0`**, the thing this file exists for. -/
  ftEval0 : ZMod m

/-- **`deriveSide`** — one side of the Pasta cycle, or `none`.

`none` is the fail-closed answer and every caller treats it as a REFUSAL: a mis-shaped column list,
a domain log2 outside the two-adicity, a modulus in which 2/3/6 is not invertible, or a `ζ` at which
the C5 denominator `(ζ − ω^{n−3})(ζ − 1)` vanishes. Never `ft_eval0` "on what did arrive". -/
def deriveSide {m : Nat} (W : SideWire m) : Option (SideOut m) :=
  if !colsOk W.ez W.ew W.sh W.mds9 W.log2n then none
  else
    match quotientConsts m with
    | none => none
    | some (cA, cB, cC) =>
      if !endomulScalarConstsOk cA cB cC then none else
      let n := 2 ^ W.log2n
      let omega := rootOfUnity m W.log2n
      let zeta := endoMap W.er W.zetaChal
      let alpha := endoMap W.er W.alphaChal
      let denom := (zeta - omega ^ (n - 3)) * (zeta - 1)
      match inv? denom with
      | none => none
      | some dinv =>
        let g := gateEvalsOf W cA cB cC
        let lct := gateLinConst g
        let beta := ((W.betaChal : Nat) : ZMod m)
        let gamma := ((W.gammaChal : Nat) : ZMod m)
        let a0 := powFast alpha 21
        let a1 := powFast alpha 22
        let a2 := powFast alpha 23
        let s := (W.ez.drop IDX_S).take (PERMUTS - 1)
        let ft := ftEval0R n omega zeta beta gamma a0 a1 a2 g.w s W.sh
          (W.ez.getD IDX_Z 0) (W.ew.getD IDX_Z 0) W.pZeta lct dinv
        some { n, omega, zeta, alpha, linConstTerm := lct, ftEval0 := ft }

/-! ## §7 — the public polynomial at a point, for the WRAP side.

The Wrap proof's wire carries no `public` evaluation (`decode_proof_at` reads none, and kimchi's
`to_batch` computes one when `proof.evals.public` is `None`). `verifier.rs`:

```text
  public_eval(x) = ( Σ_i (−pubᵢ)·ωⁱ/(x − ωⁱ) ) · (xⁿ − 1) / n
```

⚑ This is the C4 residual `KimchiVerify` §9b names ("recomputing `p(ζ)` needs the un-extracted
batch-inverted Lagrange denominators"). It is not un-extractable — it is `public_len` inverses, and
§2's witnessed device supplies them without a `Field` instance. What it needs is the forty public
input words, which is exactly what the Step side produces. -/

/-- **`publicEvalAt`** — kimchi's public-polynomial evaluation, or `none` when any `x − ωⁱ` or `n`
is not invertible (`x = ωⁱ` is a genuine refusal: the Lagrange form is undefined there). -/
def publicEvalAt {m : Nat} (n : Nat) (omega x : ZMod m) (pub : List (ZMod m)) :
    Option (ZMod m) :=
  match inv? ((n : Nat) : ZMod m) with
  | none => none
  | some nInv =>
    (List.range pub.length).foldl
      (fun acc i =>
        match acc with
        | none => none
        | some s =>
          let wi := powFast omega i
          match inv? (x - wi) with
          | none => none
          | some d => some (s + (-(pub.getD i 0)) * d * wi))
      (some 0)
    |>.map (fun s => s * (powFast x n - 1) * nInv)

/-! ## §8 — `shift_scalar`, the Wrap side's encoding of `combined_inner_product`.

`ipa.rs` `shift_scalar::<G>`: when the scalar modulus EXCEEDS the base modulus — which is Pallas's
case, and is the same fact that makes `MinaWrapChallenges.absorbFr` take the SPLITTING branch — the
map is `x − 2^{MODULUS_BIT_SIZE}`, a subtraction with no division. `cipShifted` is
`shiftScalarBig (cipR ξ r evζ evζω)` and is the last argument
`MinaWrapChallenges.ipaChallengesOf` is missing. -/

/-- `MODULUS_BIT_SIZE` for both Pasta fields. -/
def MODULUS_BITS : Nat := 255

/-- **`shiftScalarBig`** — `shift_scalar` on the branch where the scalar modulus is the larger of
the two, i.e. `x − 2^255`. The weld is its falsifier: `MinaWrapOpeningGate.CIP_SHIFTED` is
`MinaRealBlockGate.CIP` under this map or it is not. -/
def shiftScalarBig {m : Nat} (x : ZMod m) : ZMod m := x - powFast (2 : ZMod m) MODULUS_BITS

/-! ## §9 — the shape gate really refuses. Kernel `decide` over lengths and comparisons; no field
element is raised to any power, so this is cheap and it is the CHECKER half of the split. -/

/-- A minimal well-shaped column set, used only to make the refusals a discrimination. -/
def dummyCols : List (ZMod pN) := List.replicate NCOLS 1

/-- **`cols_shape_discriminates`** — the well-shaped tape is accepted and every single mutilation is
refused. Without the first conjunct this is a function returning `false`. -/
theorem cols_shape_discriminates :
    colsOk dummyCols dummyCols (List.replicate PERMUTS 1) (List.replicate 9 1) 14 = true
    -- 42 columns at ζ: a `to_absorption_sequence` that dropped one selector
    ∧ colsOk (List.replicate 42 1) dummyCols (List.replicate PERMUTS 1)
        (List.replicate 9 1) 14 = false
    -- …and at ζω, which only the Poseidon body and `z(ζω)` read
    ∧ colsOk dummyCols (List.replicate 42 1) (List.replicate PERMUTS 1)
        (List.replicate 9 1) 14 = false
    -- six coset shifts where seven belong
    ∧ colsOk dummyCols dummyCols (List.replicate 6 1) (List.replicate 9 1) 14 = false
    -- an 8-element MDS: `mdsRows` would pad the last row with zeros and the Poseidon body would
    -- silently drop a lane
    ∧ colsOk dummyCols dummyCols (List.replicate PERMUTS 1) (List.replicate 8 1) 14 = false
    -- a domain beyond the two-adicity has no root of unity at all
    ∧ colsOk dummyCols dummyCols (List.replicate PERMUTS 1) (List.replicate 9 1) 33 = false
    ∧ colsOk dummyCols dummyCols (List.replicate PERMUTS 1) (List.replicate 9 1) 0 = false := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- The column indices partition the 43 exactly — `1 + 6 + 15 + 15 + 6`, with `s` ending at 42.
Stated so a slicing change has to move a number a reader can see. -/
theorem the_column_layout_partitions :
    IDX_SEL = IDX_Z + 1 ∧ IDX_W = IDX_SEL + 6 ∧ IDX_COEFF = IDX_W + COLUMNS
    ∧ IDX_S = IDX_COEFF + COLUMNS ∧ IDX_S + (PERMUTS - 1) = NCOLS := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- `mdsRows` really is three rows of three, and a short flat list produces SHORT rows rather than
padded ones — which is why `colsOk` refuses the length instead of relying on `getD`. -/
theorem mdsRows_is_three_by_three :
    (mdsRows (List.replicate 9 (1 : ZMod pN))).length = 3
    ∧ ((mdsRows (List.replicate 9 (1 : ZMod pN))).getD 2 []).length = 3
    ∧ ((mdsRows (List.replicate 8 (1 : ZMod pN))).getD 2 []).length = 2 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- …and the fail-closed entry point returns `none` on a mis-shaped side rather than an `ft_eval0`.
⚑ Deliberately over the SHAPE arm only: the arms below it raise field elements to `2^log2n`, which
is a kernel cost this file's split exists to avoid. The weld exercises the rest, compiled. -/
theorem deriveSide_refuses_a_misshaped_side
    (W : SideWire pN) (h : W.ez.length = 42) : deriveSide W = none := by
  unfold deriveSide colsOk
  simp [h, NCOLS]

/-! ## §10 — THE WIRE + `@[export]`.

```text
INPUT  := "m=" ("p"|"q") ";lg=" Nat ";al=" Nat ";be=" Nat ";ga=" Nat ";ze=" Nat
          ";ez=" NATS ";ew=" NATS ";pz=" Nat ";er=" Nat ";en=" Nat ";sh=" NATS ";md=" NATS
NATS   := Nat ("," Nat)*        -- possibly empty
OUTPUT := "lct=" Nat ";ft0=" Nat ";om=" Nat ";ze=" Nat ";al=" Nat
        | "ERR"
```

`m` selects the field: `p` is the STEP side (`Tick`, `ZMod pN`), `q` is the WRAP side (`Tock`,
`ZMod qN`). Two fields, one body — the alternative is two exports and two chances to drift.

`"ERR"` is a refusal. There is no arm that derives `ft_eval0` from a tape it could not shape-check,
and no arm that proceeds on an inverse it could not witness. -/

/-- Parse `"a,b,c"`. An empty string is the empty list; anything non-numeric is a refusal. -/
def parseNats? (s : String) : Option (List Nat) :=
  if s.isEmpty then some []
  else (s.splitOn ",").foldr
    (fun part acc => match part.toNat?, acc with
      | some n, some r => some (n :: r)
      | _, _ => none) (some [])

/-- Parse a `key=value` field, fail-closed on a key mismatch or a missing `=`. -/
def parseField? (key part : String) : Option String :=
  match part.splitOn "=" with
  | [k, v] => if k == key then some v else none
  | _ => none

/-- A fully parsed wire, still field-agnostic: the numbers are `Nat` and the modulus has not been
chosen yet. -/
structure FtWire where
  /-- `m` — `true` for the WRAP side (`qN`), `false` for the STEP side (`pN`). -/
  wrapSide : Bool
  /-- `lg` — the domain log2. -/
  lg : Nat
  /-- `al`, `be`, `ga`, `ze` — the four RAW plonk challenges. -/
  al : Nat
  /-- `be`. -/
  be : Nat
  /-- `ga`. -/
  ga : Nat
  /-- `ze`. -/
  ze : Nat
  /-- `ez` — the 43 columns at ζ. -/
  ez : List Nat
  /-- `ew` — the 43 columns at ζω. -/
  ew : List Nat
  /-- `pz` — the public evaluation at ζ, already negated. -/
  pz : Nat
  /-- `er` — the challenge-lift endomorphism scalar. CONFIG. -/
  er : Nat
  /-- `en` — the gate `endo_coefficient`. CONFIG, and NOT `er`. -/
  en : Nat
  /-- `sh` — the seven coset shifts. CONFIG. -/
  sh : List Nat
  /-- `md` — the nine MDS entries. CONFIG. -/
  md : List Nat
deriving Repr, DecidableEq

/-- **`parseFtWire`** — the WHOLE parse, as ONE function of the split parts.

⚑ Factored out for a proof obligation rather than for taste, exactly as
`MinaWrapChallenges.parseChallengeWire` is: a gate that matched on the parts and then again on the
parsed fields cannot be welded in a rewrite, because the outer matcher does not iota-reduce. -/
def parseFtWire (parts : List String) : Option FtWire :=
  match parts with
  | [m, lg, al, be, ga, ze, ez, ew, pz, er, en, sh, md] =>
      match parseField? "m" m with
      | none => none
      | some side =>
        if side != "p" && side != "q" then none else
        match (parseField? "lg" lg).bind String.toNat?,
              (parseField? "al" al).bind String.toNat?,
              (parseField? "be" be).bind String.toNat?,
              (parseField? "ga" ga).bind String.toNat?,
              (parseField? "ze" ze).bind String.toNat?,
              (parseField? "ez" ez).bind parseNats?,
              (parseField? "ew" ew).bind parseNats?,
              (parseField? "pz" pz).bind String.toNat?,
              (parseField? "er" er).bind String.toNat?,
              (parseField? "en" en).bind String.toNat?,
              (parseField? "sh" sh).bind parseNats?,
              (parseField? "md" md).bind parseNats? with
        | some lgv, some alv, some bev, some gav, some zev, some ezv, some ewv,
          some pzv, some erv, some env, some shv, some mdv =>
            some { wrapSide := side == "q", lg := lgv, al := alv, be := bev, ga := gav,
                   ze := zev, ez := ezv, ew := ewv, pz := pzv, er := erv, en := env,
                   sh := shv, md := mdv }
        | _, _, _, _, _, _, _, _, _, _, _, _ => none
  | _ => none

/-- The parsed wire at a chosen modulus. Casting is `Nat.cast`, which reduces a non-canonical
representative — and that is safe HERE precisely because nothing in this file is a sponge: unlike
`MinaWrapChallenges.phase1WireOk`, two representatives of one element give the same `ft_eval0`. -/
def sideOf (m : Nat) (W : FtWire) : SideWire m :=
  { log2n := W.lg
    alphaChal := W.al, betaChal := W.be, gammaChal := W.ga, zetaChal := W.ze
    ez := W.ez.map (fun x => (x : ZMod m))
    ew := W.ew.map (fun x => (x : ZMod m))
    pZeta := (W.pz : ZMod m)
    er := (W.er : ZMod m), endo := (W.en : ZMod m)
    sh := W.sh.map (fun x => (x : ZMod m))
    mds9 := W.md.map (fun x => (x : ZMod m)) }

/-- Render one side's answer. -/
def renderSide {m : Nat} (o : SideOut m) : String :=
  "lct=" ++ toString o.linConstTerm.val ++ ";ft0=" ++ toString o.ftEval0.val
    ++ ";om=" ++ toString o.omega.val ++ ";ze=" ++ toString o.zeta.val
    ++ ";al=" ++ toString o.alpha.val

/-- The derivation on a parsed wire, rendered. Nothing else in this file decides. -/
def renderFromWire (W : FtWire) : String :=
  if W.wrapSide then
    match deriveSide (sideOf qN W) with
    | some o => renderSide o
    | none => "ERR"
  else
    match deriveSide (sideOf pN W) with
    | some o => renderSide o
    | none => "ERR"

/-- **`minaWrapFtEval0Gate`** — THE GATE. One scrutinee; every refusal is inside the parse or inside
`deriveSide`'s shape and inverse gates. -/
def minaWrapFtEval0Gate (s : String) : String :=
  match parseFtWire (s.splitOn ";") with
  | some W => renderFromWire W
  | none => "ERR"

/-- **THE EXPORT.** `@[export dregg_mina_wrap_ft_eval0]`. Rust decodes binprot to numbers and hands
them over; the ARCHIVE runs the six gate constraint bodies and the C5 fold. There is no Rust
linearization to drift, and there is no Rust modular inverse. -/
@[export dregg_mina_wrap_ft_eval0]
def dregg_mina_wrap_ft_eval0 (s : String) : String := minaWrapFtEval0Gate s

/-- **The gate string IS `renderFromWire` of the parse** — the string layer adds no arm. One
scrutinee, one rewrite; the shape `MinaWrapChallenges.challengesGate_is_the_derivation` uses. -/
theorem ftGate_is_the_derivation (s : String) (W : FtWire)
    (hp : parseFtWire (s.splitOn ";") = some W) :
    minaWrapFtEval0Gate s = renderFromWire W := by
  unfold minaWrapFtEval0Gate
  rw [hp]

/-- …and `renderFromWire` IS `deriveSide` at the modulus the `m` field selects, rendered. Chained
with the theorem above: the exported symbol runs `deriveSide` on `sideOf` the parse and nothing
else, so §9's refusals are refusals of the thing Rust actually calls. -/
theorem renderFromWire_is_deriveSide (W : FtWire) :
    renderFromWire W =
      (if W.wrapSide then
        (match deriveSide (sideOf qN W) with | some o => renderSide o | none => "ERR")
       else
        (match deriveSide (sideOf pN W) with | some o => renderSide o | none => "ERR")) := rfl

/-! ### §10b — the wire REFUSES. Compiled, milliseconds; no field element is exponentiated because
every one of these dies in the parse or in `colsOk`. -/

#guard minaWrapFtEval0Gate "" == "ERR"
#guard minaWrapFtEval0Gate "garbage" == "ERR"
-- a short field list
#guard minaWrapFtEval0Gate "m=p;lg=14;al=1;be=1;ga=1;ze=1;ez=;ew=;pz=1;er=1;en=1;sh=" == "ERR"
-- an unknown field selector: neither Pasta side, so nothing is derived on a guess
#guard minaWrapFtEval0Gate
         "m=z;lg=14;al=1;be=1;ga=1;ze=1;ez=1;ew=1;pz=1;er=1;en=1;sh=1;md=1" == "ERR"
-- a full-arity wire whose column lists are the WRONG SHAPE: refused, not derived on
#guard minaWrapFtEval0Gate
         "m=p;lg=14;al=1;be=1;ga=1;ze=1;ez=1;ew=1;pz=1;er=1;en=1;sh=1;md=1" == "ERR"
-- a non-numeric coordinate
#guard minaWrapFtEval0Gate
         "m=q;lg=14;al=1;be=1;ga=1;ze=1;ez=x;ew=1;pz=1;er=1;en=1;sh=1;md=1" == "ERR"
-- a key in the wrong position
#guard minaWrapFtEval0Gate
         "lg=14;m=p;al=1;be=1;ga=1;ze=1;ez=;ew=;pz=1;er=1;en=1;sh=;md=" == "ERR"

/-! ## §11 — axiom hygiene. -/

#assert_axioms powFast_is_pow
#assert_axioms cols_shape_discriminates
#assert_axioms the_column_layout_partitions
#assert_axioms mdsRows_is_three_by_three
#assert_axioms deriveSide_refuses_a_misshaped_side
#assert_axioms ftGate_is_the_derivation
#assert_axioms renderFromWire_is_deriveSide

#print axioms cols_shape_discriminates
#print axioms ftGate_is_the_derivation

end Dregg2.Bridge.MinaWrapFtEval0
