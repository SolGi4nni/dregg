/-
# Dregg2.Bridge.MinaWrapFtEval0Weld — **the reality gate: on devnet block 539508, the C5 FOLD is
EXACT (`ftEval0 + linConstTerm = FT0 + LCT`, byte-for-byte, from the derived shifts and the wire),
but `KimchiVerify.gateLinConst` does NOT reproduce the linearization constant term — a defect this
file exposes and PINS on BOTH sides of the Pasta cycle.**

## ⚠⚠ THIS FILE NEVER COMPILED before 2026-08-01, so nothing below was ever machine-checked

At its birth commit `bb7c0d7e3`, line 127 read `gammaChal := GAMMA_CHAL` — an identifier defined only
in `MinaWrapDeferredWeld`, never opened here — so `W539508` "used sorry" and EVERY `#guard` cascaded.
The celebratory claim in that commit ("six gate bodies reproduce the carried `LCT`") was **never
run.** The one-token fix (`GAMMA_CHAL → GAMMA_N`, §1c-pinned as the raw wrap γ) makes it compile, and
the claim is **FALSE on the real block.**

## ⚑⚑ WHAT IS MEASURED AND WHAT IS NOT — read before quoting this file

  * **WRAP side, the FOLD: MEASURED EXACT (§2a).** `ftEval0 + linConstTerm` equals `FT0 + LCT`
    (kimchi's own `afterZk = ft_eval0 + constant_term`) byte-for-byte. This validates `ftEval0R`, the
    SEVEN DERIVED SHIFTS, `p(ζ)`, the challenge lifts and every column — all at once, and independently
    of the endo (the sum cancels the constant term's endo-dependence).
  * ⚑ **WRAP side, `gateLinConst`: REFUTED (§2b-head, §3).** `linConstTerm ≠ LCT` and `ftEval0 ≠ FT0`,
    off by a fixed delta, for BOTH cube-root endos. Given §2a, the entire residual is
    `KimchiVerify.gateLinConst` — kimchi's generic 6-gate linearization transcription does not
    reproduce Rust's `PolishToken::evaluate(constant_term)`. `MinaRealBlockGate.LCT` is NOT retired.
  * **The public polynomial `p(ζ)`, `p(ζω)`: MEASURED (§4).** Recomputed from the forty public-input
    words with WITNESSED inverses.
  * **`cipShifted`: MEASURED (§5).** `shift_scalar` of `MinaRealBlockGate.CIP` IS
    `MinaWrapOpeningGate.CIP_SHIFTED`.
  * ⚑ **STEP side: the SHIFTS GAP is CLOSED; slot 0 is NOT yet a discrimination — SAME `gateLinConst`
    defect.** §6. The **seven Tick coset `shifts` at `domain_log2 = 16`** are DERIVED by
    `Dregg2.Bridge.TickShifts.tickShiftsFp 16` (`Shifts::new` Blake2b→field, byte-exact `#guard` vs
    o1-labs), so the Step side no longer REFUSES — it COMPUTES `ft_eval0` (`OUT_STEP.isSome`). With
    the derived shifts, the corrected `endo_coefficient` (`5^((p-1)/3)`, un-conflated from `er`), and
    every other input byte-exact, the derived `ft_eval0` = `19015…408756` ≠
    `MinaWrapDeferredWeld.FT_EVAL0` (`12860…098804`). The lane's premise — shifts were the ONLY
    residual — is FALSIFIED: the fold matches mina-rust `plonk_checks::ft_eval0` term-for-term, so the
    residual is the CONSTANT TERM, the SAME `gateLinConst` defect the WRAP side refutes independently
    (`OUT_STEP.linConstTerm = 14190…863095` vs the fold-implied `lct_true 20345…173047`). §6a PINS it.
    §6b shows the shifts are load-bearing regardless. SYNTHESIS-fidelity — NOT soundness.

Compiled, not kernel: every pin below is `#guard`, and that is the point of the file. NOT rooted in
`Dregg2/FFI.lean` — it imports one-block fixtures whose kernel cost belongs off the archive's hot
path, the same split `MinaWrapChallengesWeld` documents.
-/
import Dregg2.Bridge.MinaWrapFtEval0
import Dregg2.Bridge.MinaWrapDeferredWeld
import Dregg2.Bridge.TickShifts
import Dregg2.Circuit.Emit.MinaRealBlockGate
import Dregg2.Circuit.Emit.MinaWrapOpeningGate

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Dregg2.Bridge.MinaWrapFtEval0Weld

open Dregg2.Bridge.MinaWrapFtEval0
open Dregg2.Circuit.Emit.PastaField (pN qN)
open Dregg2.Circuit.Emit.PastaPoseidonFq (mdsQ)
open Dregg2.Circuit.Emit.KimchiVerify (gateLinConst cipR endoMap)
open Dregg2.Circuit.Emit.MinaRealBlockTranscript (BETA_N GAMMA_N ALPHA_CHAL ZETA_CHAL ENDO_R)
open Dregg2.Circuit.Emit.MinaWrapOpeningGate (CIP_SHIFTED)
open Dregg2.Circuit.Emit.MinaWrapPublicCommGate (PUBLIC_INPUT)

/-! ## §1 — the WRAP side of block 539508, assembled as a `SideWire`.

`MinaRealBlockGate.EVZ`/`EVZW` are the 47-entry C8 columns: two recursion b-polynomials, the public
polynomial, `ft`, then the 43 evaluation columns in `to_absorption_sequence` order. Dropping the
four-entry prefix is therefore exactly `Plonk_types.Evals`, which is what `SideWire.ez` wants — and
the prefix length is pinned below rather than trusted. -/

/-- The 43 columns at ζ. -/
def EZ : List (ZMod qN) := Dregg2.Circuit.Emit.MinaRealBlockGate.EVZ.drop 4
/-- …and at ζω. -/
def EW : List (ZMod qN) := Dregg2.Circuit.Emit.MinaRealBlockGate.EVZW.drop 4

/- The prefix really is four long and the remainder really is 43 columns. Without this the slicing
in `MinaWrapFtEval0` §5 would be reading `ft` as a selector and nothing would say so. -/
#guard EZ.length == 43
#guard EW.length == 43
/- …and the drop landed on `z`, not on `ft`: `EZ[0]` is `z(ζ)` and `EW[0]` is `z(ζω)`. -/
#guard EZ.getD IDX_Z 0 == Dregg2.Circuit.Emit.MinaRealBlockGate.ZZ
#guard EW.getD IDX_Z 0 == Dregg2.Circuit.Emit.MinaRealBlockGate.ZZW
/- …and the `w` slice starts where §5 says: `EZ[7]` is the first witness evaluation. -/
#guard (EZ.drop IDX_W).take 7 == Dregg2.Circuit.Emit.MinaRealBlockGate.WZ
/- …and the σ slice likewise. -/
#guard (EZ.drop IDX_S).take 6 == Dregg2.Circuit.Emit.MinaRealBlockGate.SZ

/-! ### §1b — ⚑ THE FINDING: all six gate selectors FIRE on the real block.

`KimchiPoseidonGate`'s and `KimchiRealProofGate`'s fixtures both had `caddSel = mulSel = emulSel =
emulScalarSel = 0`, so `gateLinConst`'s four largest bodies were multiplied by zero and their
transcription rested on a source reading. On a real Mina Wrap proof they do not. -/

#guard EZ.getD (IDX_SEL + 0) 0 != 0    -- generic
#guard EZ.getD (IDX_SEL + 1) 0 != 0    -- poseidon
#guard EZ.getD (IDX_SEL + 2) 0 != 0    -- ⚑ complete_add, never exercised before this file
#guard EZ.getD (IDX_SEL + 3) 0 != 0    -- ⚑ varbasemul, 21 constraints
#guard EZ.getD (IDX_SEL + 4) 0 != 0    -- ⚑ endomul, 12 constraints — the only reader of `endo`
#guard EZ.getD (IDX_SEL + 5) 0 != 0    -- ⚑ endomul_scalar, 11 constraints

/-- ⚑ **CONFIG, named.** `env.endo_coefficient()` = the Wrap verifier index's `endo`.

This is the one constant in the file that is a READING rather than a measurement, and it is read by
exactly one gate. `KimchiPoseidonGate.GEV` sets `endo := ENDO_R` on its Vesta fixture, but that
fixture's `emulSel` is ZERO, so the value was never consumed there and the agreement is vacuous.
§2 is the first place it is load-bearing; §2b is the discrimination that says so. -/
def ENDO_COEFF : ZMod qN := ENDO_R

/-- The `fq_kimchi` MDS, flat. `Constants::mds` is the sponge parameters of the field the circuit is
over, and the Wrap circuit is over `Fq` (`KimchiPoseidonGate`'s note names the Vesta half). -/
def MDS9 : List (ZMod qN) := (mdsQ.flatten).map (fun x => (x : ZMod qN))

#guard MDS9.length == 9

/-- **Block 539508's WRAP side, as `MinaWrapFtEval0` wants it.** Every field is either a wire value
`decode_proof_at` already walks or a config object named at its declaration. -/
def W539508 : SideWire qN :=
  { log2n := 14
    alphaChal := ALPHA_CHAL, betaChal := BETA_N, gammaChal := GAMMA_N, zetaChal := ZETA_CHAL
    ez := EZ, ew := EW
    pZeta := Dregg2.Circuit.Emit.MinaRealBlockGate.PZ
    er := ENDO_R
    endo := ENDO_COEFF
    sh := Dregg2.Circuit.Emit.MinaRealBlockGate.SHIFT
    mds9 := MDS9 }

/- The block's tape passes the shape gate — so `cols_shape_discriminates` is not refusing
everything. -/
#guard colsOk W539508.ez W539508.ew W539508.sh W539508.mds9 W539508.log2n

/- The domain is `2^14`, the real Wrap evaluation domain, and NOT the Step side's `2^16` — the
conflation `docs/MINA-REAL-BLOCK-GATE.md` §4.2 records. -/
#guard 2 ^ W539508.log2n == Dregg2.Circuit.Emit.MinaRealBlockGate.N

/-! ### §1c — the DERIVED domain generator and the DERIVED challenge lifts.

`rootOfUnity` builds `ω` from the two-adicity and the generator 5 instead of carrying it, and
`endoMap` lifts the raw prechallenges. Both are checked against values `MinaRealBlockGate` carries,
each of which was cross-checked in Rust against `proof.oracles(...)` before it was written down. -/

#guard rootOfUnity qN 14 == Dregg2.Circuit.Emit.MinaRealBlockGate.OMEGA
/- Order exactly `2^14`: a `2^14`-th root that is not a `2^13`-th root. -/
#guard powFast (rootOfUnity qN 14) (2 ^ 14) == (1 : ZMod qN)
#guard powFast (rootOfUnity qN 14) (2 ^ 13) != (1 : ZMod qN)
/- …and the ladder is consistent across sizes: `ω_14² = ω_13`. -/
#guard rootOfUnity qN 14 * rootOfUnity qN 14 == rootOfUnity qN 13

/- ζ and α are the endomorphism lifts of the phase-1 prechallenges `MinaWrapChallengesWeld` derives
from the block's own absorbed coordinates. This is the JOINT that ties the two files: that file
produces `ZETA_CHAL`/`ALPHA_CHAL` from wire points, this one consumes them. -/
#guard endoMap ENDO_R ZETA_CHAL == Dregg2.Circuit.Emit.MinaRealBlockGate.ZETA
#guard endoMap ENDO_R ALPHA_CHAL == Dregg2.Circuit.Emit.MinaRealBlockGate.ALPHA
/- β and γ are the RAW squeezes, not lifted — the same asymmetry `MinaWrapDeferred` §7 records for
public-input slots 5-8. -/
#guard ((BETA_N : ZMod qN)) == Dregg2.Circuit.Emit.MinaRealBlockGate.BETA
#guard ((GAMMA_N : ZMod qN)) == Dregg2.Circuit.Emit.MinaRealBlockGate.GAMMA

/- The permutation α-powers are DERIVED from α at `perm_alpha0 = 21`, not carried. -/
#guard powFast Dregg2.Circuit.Emit.MinaRealBlockGate.ALPHA 21
       == Dregg2.Circuit.Emit.MinaRealBlockGate.A0
#guard powFast Dregg2.Circuit.Emit.MinaRealBlockGate.ALPHA 22
       == Dregg2.Circuit.Emit.MinaRealBlockGate.A1
#guard powFast Dregg2.Circuit.Emit.MinaRealBlockGate.ALPHA 23
       == Dregg2.Circuit.Emit.MinaRealBlockGate.A2

/- The three `EndomulScalar` quotient constants are DERIVED and the ring check passes, so the
`endomul_scalar` body below is running on `11/6, −5/2, 2/3` and not on a carrier. -/
#guard match quotientConsts qN with
       | some (a, b, c) => Dregg2.Circuit.Emit.KimchiVerify.endomulScalarConstsOk a b c
       | none => false

/-! ## §2 — ⚑⚑ MEASURED (for the FIRST time): the fold is EXACT; `gateLinConst` is NOT.

⚠⚠ **THIS FILE NEVER COMPILED before this pass.** At its birth commit `bb7c0d7e3`, line 127 read
`gammaChal := GAMMA_CHAL`, an identifier defined only in `MinaWrapDeferredWeld` and never opened here,
so `W539508` "used sorry", EVERY `#guard` below cascaded, and NONE of §2–§7's claims was ever
machine-checked. The one-token fix (`GAMMA_CHAL → GAMMA_N`, the raw wrap γ, §1c-pinned) makes it
compile — and the headline it advertised is **FALSE on the real block**:

`MinaRealBlockGate.LCT` is Rust's `PolishToken::evaluate(constant_term)` and `FT0` is kimchi's own
`oracles().ft_eval0`; kimchi's identity is `ft_eval0 = afterZk − constant_term`, so `afterZk = FT0 +
LCT` is a value this tree can check against. **The fold reproduces it EXACTLY** — `deriveSide`'s
`ftEval0 + linConstTerm` equals `FT0 + LCT` byte-for-byte (§2a), which validates `ftEval0R`, the seven
shifts, `p(ζ)`, the challenge lifts and every column, all at once and independently of the endo (the
sum cancels the constant term's endo-dependence). **But `gateLinConst` does NOT reproduce the constant
term**: `OUT.linConstTerm ≠ LCT` (§2b-head), off by a fixed delta, for BOTH cube-root endos. The gap
is `KimchiVerify.gateLinConst` (kimchi's generic 6-gate linearization transcription), not any input or
the fold. Until it is fixed, `MinaRealBlockGate.LCT` is NOT retired and `ft_eval0` is NOT yet a pure
function of the wire. -/

/-- The derived side, once, so §2-§3 read the same object. -/
def OUT : Option (SideOut qN) := deriveSide W539508

#guard OUT.isSome

/-! ### §2a — ⚑⚑ THE FOLD IS EXACT. `afterZk = ftEval0 + linConstTerm = FT0 + LCT`, byte-for-byte.

This is the strong positive result the never-compiling file hid: `ftEval0R` over the seven derived
shifts and the block's 86 columns reproduces kimchi's `afterZk` (`FT0 + LCT`) EXACTLY. It is
endo-INDEPENDENT (the constant term's endo-dependence cancels in the sum), so it isolates the fold
from the constant term cleanly. -/
#guard match OUT with
       | some o => o.ftEval0 + o.linConstTerm ==
           Dregg2.Circuit.Emit.MinaRealBlockGate.FT0 + Dregg2.Circuit.Emit.MinaRealBlockGate.LCT
       | none => false

/-! ### §2b-head — ⚑ THE `gateLinConst` DEFECT, PINNED. `linConstTerm ≠ LCT`.

Given §2a (the fold is exact), this inequality localizes the entire residual to `gateLinConst`: it
does not reproduce kimchi's real `PolishToken::evaluate(constant_term)`. This guard PINS the defect —
when `KimchiVerify.gateLinConst` is corrected to match kimchi, `linConstTerm == LCT` and this flips
RED, which is the signal the constant term closed. -/
#guard match OUT with
       | some o => o.linConstTerm != Dregg2.Circuit.Emit.MinaRealBlockGate.LCT
       | none => false

/-! ### §2b — NON-VACUITY: each of the four bodies is LOAD-BEARING in `gateLinConst`'s OWN output.

⚑ These controls are measured against `LCT_DERIVED` (`gateLinConst`'s full output on this block), NOT
against `LCT` — because `gateLinConst ≠ LCT` already (§2b-head), so `≠ LCT` would be vacuous. Zeroing
a selector must move `gateLinConst`'s own value; that the four largest bodies contribute is true even
though their SUM is the wrong constant term. -/

/-- `gateLinConst`'s full output on block 539508 (the value §2b-head shows `≠ LCT`). -/
def LCT_DERIVED : ZMod qN :=
  match quotientConsts qN with
  | some (cA, cB, cC) => gateLinConst (gateEvalsOf W539508 cA cB cC)
  | none => 0

/-- `gateLinConst` at the real block, with one selector zeroed. -/
def lctWithSelZeroed (k : Nat) : ZMod qN :=
  match quotientConsts qN with
  | some (cA, cB, cC) => gateLinConst (gateEvalsOf { W539508 with ez := EZ.set (IDX_SEL + k) 0 } cA cB cC)
  | none => 0

#guard lctWithSelZeroed 0 != LCT_DERIVED   -- generic
#guard lctWithSelZeroed 1 != LCT_DERIVED   -- poseidon
#guard lctWithSelZeroed 2 != LCT_DERIVED   -- ⚑ complete_add
#guard lctWithSelZeroed 3 != LCT_DERIVED   -- ⚑ varbasemul
#guard lctWithSelZeroed 4 != LCT_DERIVED   -- ⚑ endomul
#guard lctWithSelZeroed 5 != LCT_DERIVED   -- ⚑ endomul_scalar

/- ⚑ And the `endo` CONFIG is genuinely consumed: the `endomul` body reads it, so a different
coefficient produces a different `gateLinConst` value. -/
#guard match quotientConsts qN with
       | some (cA, cB, cC) =>
         gateLinConst (gateEvalsOf { W539508 with endo := ENDO_COEFF + 1 } cA cB cC) != LCT_DERIVED
       | none => false

/- …and so are the coefficient column (the Poseidon round constants) and the ζω witness column
(only the fifth Poseidon round equation and `varbasemul`/`endomul`'s NEXT row read it). -/
#guard match quotientConsts qN with
       | some (cA, cB, cC) =>
         gateLinConst (gateEvalsOf { W539508 with ez := EZ.set IDX_COEFF 0 } cA cB cC) != LCT_DERIVED
       | none => false
#guard match quotientConsts qN with
       | some (cA, cB, cC) =>
         gateLinConst (gateEvalsOf { W539508 with ew := EW.set IDX_W 0 } cA cB cC) != LCT_DERIVED
       | none => false

/-! ## §3 — ⚑ `ft_eval0`: the fold is right, so `ftEval0 ≠ FT0` is EXACTLY the `gateLinConst` delta.

`ftEval0 = afterZk − linConstTerm`. §2a pins `afterZk` exact and §2b-head pins `linConstTerm ≠ LCT`,
so `ftEval0 ≠ FT0` follows, off by the same constant-term delta. When `gateLinConst` is corrected,
`ftEval0 == FT0` and this flips RED. -/
#guard match OUT with
       | some o => o.ftEval0 != Dregg2.Circuit.Emit.MinaRealBlockGate.FT0
       | none => false

/- The witnessed inverse really is `DINV` — so the ladder is not accidentally agreeing through a
cancelling error. -/
#guard inv? ((Dregg2.Circuit.Emit.MinaRealBlockGate.ZETA
              - powFast Dregg2.Circuit.Emit.MinaRealBlockGate.OMEGA (16384 - 3))
             * (Dregg2.Circuit.Emit.MinaRealBlockGate.ZETA - 1))
       == some Dregg2.Circuit.Emit.MinaRealBlockGate.DINV

/- Non-vacuity of the FOLD, measured against the exact `afterZk` (§2a) rather than the
`gateLinConst`-poisoned `ft_eval0`: a moved public evaluation, a moved σ column, or a bent coset
each breaks `ftEval0 + linConstTerm == FT0 + LCT`. So the fold genuinely reads these inputs, and the
shifts are load-bearing on BOTH sides of the cycle. -/
def afterZkGold : ZMod qN :=
  Dregg2.Circuit.Emit.MinaRealBlockGate.FT0 + Dregg2.Circuit.Emit.MinaRealBlockGate.LCT
#guard match deriveSide { W539508 with
                          pZeta := Dregg2.Circuit.Emit.MinaRealBlockGate.PZ + 1 } with
       | some o => o.ftEval0 + o.linConstTerm != afterZkGold
       | none => false
#guard match deriveSide { W539508 with ez := EZ.set IDX_S 0 } with
       | some o => o.ftEval0 + o.linConstTerm != afterZkGold
       | none => false
#guard match deriveSide { W539508 with
                          sh := Dregg2.Circuit.Emit.MinaRealBlockGate.SHIFT.set 1 0 } with
       | some o => o.ftEval0 + o.linConstTerm != afterZkGold
       | none => false

/-! ## §4 — ⚑ THE PUBLIC POLYNOMIAL, RE-COMPUTED. C4 closes.

`KimchiVerify` §9b: "C4 `p(ζ)` enters the C5 fold as an INPUT — recomputing it needs the
un-extracted batch-inverted Lagrange denominators, a named residual." It needs forty inverses, and
§2 of `MinaWrapFtEval0` witnesses each one instead of trusting a `Field` instance.

⚑ This is the leg that makes the Wrap side a function of the PUBLIC INPUT rather than of a carried
evaluation — i.e. the leg that connects the Step side's forty words to the Wrap side's transcript.
It is also, with `publicCommOf`, the second consumer of those forty words. -/

/-- The forty public-input words of block 539508, in `ZMod qN`. -/
def PUB : List (ZMod qN) := PUBLIC_INPUT.map (fun x => (x : ZMod qN))

#guard PUB.length == 40

/- ⚑ `p(ζ)` — equal to the value `MinaRealBlockGate` carries as `PZ`, which kimchi computed. -/
#guard publicEvalAt 16384 (rootOfUnity qN 14) Dregg2.Circuit.Emit.MinaRealBlockGate.ZETA PUB
       == some Dregg2.Circuit.Emit.MinaRealBlockGate.PZ
/- …and `p(ζω)`, which is `EVZW`'s third entry. A formula that only matched at ζ would be a
coincidence at one point. -/
#guard publicEvalAt 16384 (rootOfUnity qN 14)
         (Dregg2.Circuit.Emit.MinaRealBlockGate.ZETA * rootOfUnity qN 14) PUB
       == some (Dregg2.Circuit.Emit.MinaRealBlockGate.EVZW.getD 2 0)

/- Non-vacuity: every word is read. Moving slot 12 — the ONLY slot the served block enters — moves
`p(ζ)`, so a re-labelled header is visible in the Wrap transcript through this leg as well as
through `publicCommOf`. -/
#guard publicEvalAt 16384 (rootOfUnity qN 14) Dregg2.Circuit.Emit.MinaRealBlockGate.ZETA
         (PUB.set 12 0)
       != some Dregg2.Circuit.Emit.MinaRealBlockGate.PZ
/- …and the LAST word, so a fold that stopped early passes every earlier control and fails this. -/
#guard publicEvalAt 16384 (rootOfUnity qN 14) Dregg2.Circuit.Emit.MinaRealBlockGate.ZETA
         (PUB.set 39 1)
       != some Dregg2.Circuit.Emit.MinaRealBlockGate.PZ
/- …and slot 0, `combined_inner_product`, the word that needs the STEP side's `ft_eval0`. -/
#guard publicEvalAt 16384 (rootOfUnity qN 14) Dregg2.Circuit.Emit.MinaRealBlockGate.ZETA
         (PUB.set 0 0)
       != some Dregg2.Circuit.Emit.MinaRealBlockGate.PZ

/-! ## §5 — ⚑⚑ `cipShifted`, the OTHER non-decodable argument, CLOSED.

`MinaWrapChallengesWeld`'s header names exactly two arguments the per-block path could not supply:
`pubComm` and `cipShifted`. This is the second one.

`MinaRealBlockGate.real_cip` already proves `cipR VV UU EVZ EVZW = CIP` in the kernel, from the
block's own 47 evaluation entries. What was missing is the ENCODING: `SRS::verify` absorbs
`shift_scalar(cip)`, not `cip`. On Pallas the scalar modulus exceeds the base modulus, so
`shift_scalar` takes the `x − 2^255` branch — no division, and the same asymmetry that makes
`MinaWrapChallenges.absorbFr` split its absorb into two. -/

#guard cipR Dregg2.Circuit.Emit.MinaRealBlockGate.VV Dregg2.Circuit.Emit.MinaRealBlockGate.UU
         Dregg2.Circuit.Emit.MinaRealBlockGate.EVZ Dregg2.Circuit.Emit.MinaRealBlockGate.EVZW
       == Dregg2.Circuit.Emit.MinaRealBlockGate.CIP

/- ⚑ **THE CLOSE.** `shift_scalar` of the block's own aggregated opening value IS the scalar
`MinaWrapOpeningGate` absorbs at the head of the IPA transcript. -/
#guard (shiftScalarBig Dregg2.Circuit.Emit.MinaRealBlockGate.CIP).val == CIP_SHIFTED

/- …and it is not the identity, so the encoding is doing work. -/
#guard (shiftScalarBig Dregg2.Circuit.Emit.MinaRealBlockGate.CIP)
       != Dregg2.Circuit.Emit.MinaRealBlockGate.CIP

/-! ## §6 — ⚑⚑ THE STEP SIDE: the last config object DERIVED, and slot 0 becomes a DISCRIMINATION.

Everything `expand_deferred`'s `ft_eval0` wants is assembled below from block 539508's own binprot
bytes, which `MinaWrapDeferredWeld` extracted by re-walking `decode_proof_at` field for field —
and the ONE object that was not in the tree, the seven Tick coset `shifts`, is now DERIVED by
`Dregg2.Bridge.TickShifts.tickShiftsFp 16`:

| input | source | status |
|---|---|---|
| the 43+43 evaluation columns | `MinaWrapDeferredWeld.EVALS` | ✅ WIRE |
| `p(ζ)` | `prev_evals.evals.public_input.0` | ✅ WIRE — the Step side carries it, unlike the Wrap side |
| α′, β, γ, ζ′ | `deferred_values.plonk` | ✅ WIRE |
| `domain_log2` | `branch_data` | ✅ WIRE |
| `er` = `Endo.Wrap_inner_curve.scalar` | `MinaWrapDeferred.ENDO` | ✅ CONFIG, named |
| `mds` = `fp_kimchi` | `PastaPoseidon.mdsN` | ✅ CONFIG, in tree |
| `endo_coefficient` | the Tick verifier index | ⚠ CONFIG, read as `er` (see §2b for why that reading is only load-bearing where a selector fires) |
| **the seven Tick coset `shifts` at `2^16`** | `TickShifts.tickShiftsFp 16` | ✅ **DERIVED** (Blake2b→field; `#guard`-pinned to `Shifts::new` byte-exact) |

`Shifts::new` derives them by Blake2b over the domain; `TickShifts` transcribes exactly that
construction (counter from 7, `Blake2b512(i.to_be_bytes())`, `LE(digest[..31])`, keep the QNRs not
in the domain, distinct) and pins the seven values to o1-labs' own output. §3's shift control
already showed they are load-bearing: a single wrong shift moves `ft_eval0`.

⚑ **THE CLOSE.** With the derived shifts, the Step-side `ft_eval0` — and therefore public-input
word 0, and therefore `public_comm` — is COMPUTED from the wire, and it EQUALS
`MinaWrapDeferredWeld.FT_EVAL0`, the value that file SOLVED from public-input slot 0. So slot 0's
`combined_inner_product` leg stops being an arithmetic identity solved from its own slot and becomes
a DISCRIMINATION: the whole Step-side gate linearization + C5 fold, fed the derived shifts,
reproduces the anchor. §6b exhibits the red path — a bent shift moves the answer off `FT_EVAL0`. -/

/-- The Step side's 43 columns at ζ, from the block's own bytes. -/
def EZ_STEP : List (ZMod pN) :=
  Dregg2.Bridge.MinaWrapDeferredWeld.EVALS.map (fun p => ((p.1 : ZMod pN)))
/-- …and at ζω. -/
def EW_STEP : List (ZMod pN) :=
  Dregg2.Bridge.MinaWrapDeferredWeld.EVALS.map (fun p => ((p.2 : ZMod pN)))

#guard EZ_STEP.length == 43
#guard EW_STEP.length == 43

/-- ⚑ **THE DERIVED CONFIG OBJECT.** The seven Tick coset shifts at `domain_log2 = 16`, over the
Step field `ZMod pN`, DERIVED by `TickShifts.tickShiftsFp` and `#guard`-pinned there to
`Shifts::new`. No longer a hole. -/
def TICK_SHIFTS : List (ZMod pN) := Dregg2.Bridge.TickShifts.tickShiftsFp 16

/- It really is the seven-element derived vector. -/
#guard TICK_SHIFTS.length == 7

/-- Block 539508's STEP side, now COMPLETE — the `sh` is the derived shifts. -/
def S539508 : SideWire pN :=
  { log2n := Dregg2.Bridge.MinaWrapDeferredWeld.DOMAIN_LOG2
    alphaChal := Dregg2.Bridge.MinaWrapDeferredWeld.ALPHA_CHAL
    betaChal := Dregg2.Bridge.MinaWrapDeferredWeld.BETA_CHAL
    gammaChal := Dregg2.Bridge.MinaWrapDeferredWeld.GAMMA_CHAL
    zetaChal := Dregg2.Bridge.MinaWrapDeferredWeld.ZETA_CHAL
    ez := EZ_STEP, ew := EW_STEP
    pZeta := ((Dregg2.Bridge.MinaWrapDeferredWeld.PUB_EVAL.1 : Nat) : ZMod pN)
    er := ((Dregg2.Bridge.MinaWrapDeferred.ENDO : Nat) : ZMod pN)
    -- ⚑ CORRECTED: the endomul `endo_coefficient` is `GENERATOR^((p-1)/3)`, NOT `er` (=ENDO). The
    -- prior `endo := ENDO` conflated the two cube roots — the hazard `MinaWrapFtEval0` §54 names.
    endo := Dregg2.Bridge.TickShifts.stepEndoCoefficient
    sh := TICK_SHIFTS
    mds9 := (Dregg2.Circuit.Emit.PastaPoseidon.mdsN.flatten).map (fun x => (x : ZMod pN)) }

/-- The Step side's derivation, once. -/
def OUT_STEP : Option (SideOut pN) := deriveSide S539508

/- ⚑ The complete Step side is ACCEPTED — the shape gate passes with seven real shifts. The refusal
that `TICK_SHIFTS_PARTIAL` forced is GONE: the shifts gap is closed and the Step side now COMPUTES
`ft_eval0` from the wire rather than returning `none`. -/
#guard OUT_STEP.isSome

/-! ### §6a — ⚑ SLOT 0 IS NOT YET A DISCRIMINATION: a SECOND residual, MEASURED and NAMED.

The brief for this lane assumed the seven shifts were the ONLY thing between the Step side and
`FT_EVAL0`, so that deriving them would make `ftEval0 == FT_EVAL0` and turn slot 0 from
"solved-from-its-slot" into a differential. **That premise is FALSIFIED here.** With the derived
shifts (byte-exact, `TickShifts`), the corrected `endo_coefficient` (`5^((p-1)/3)`, not `ENDO`), and
EVERY other Step-side input confirmed byte-exact against o1-labs (columns in `to_absorption_sequence`
order — the same slice `MinaWrapDeferred` real-block-verifies; `mds` = `fp_kimchi`, oracle-matched;
`alpha`/`zeta` the `deferred.py`-verified lifts; `beta`/`gamma` raw), the derived `ft_eval0` is

    `OUT_STEP.ftEval0 = 19015133850720799981561969103347224543420887819567943801623456181067047408756`

which is **NOT** `FT_EVAL0 = 12860…098804`. The fold (`ftEval0R`) matches mina-rust
`plonk_checks::ft_eval0` term-for-term (PERM_ALPHA0 = 21, `ω^(n-3)`, shifts in the denominator), so
the residual is the linearization CONSTANT TERM: `deriveSide` computes it with
`KimchiVerify.gateLinConst`, and §2 above REFUTES that function INDEPENDENTLY on the WRAP side — where
the fold is provably exact (§2a: `ftEval0 + linConstTerm = FT0 + LCT`) yet `linConstTerm ≠ LCT`. So
`gateLinConst` is the SAME broken input on both sides; it does not reproduce Rust's
`PolishToken`/Pickles' `Scalars.Tick.constant_term`, which is what `FT_EVAL0` rests on. Solving the
fold for the constant term the anchor needs gives

    `lct_true   = 20345071543763246608538509185165536352110693439382108600930896203194519173047`
    `lct_gateLC = 14190819821033234537891308285146002190684630817697890984532326410246828863095`

(the derived one, `OUT_STEP.linConstTerm`). So the shifts gap is CLOSED and a distinct
`gateLinConst` ≠ `Scalars.Tick.constant_term` gap is EXPOSED — it lives in `KimchiVerify` (not in any
input this file controls) and is the real remaining work for slot 0. This guard PINS the current gap
so that closing the constant-term residual (making the two equal) flips it RED, which is the signal
that slot 0 has actually become a discrimination. -/
#guard match OUT_STEP with
       | some o => o.ftEval0.val != Dregg2.Bridge.MinaWrapDeferredWeld.FT_EVAL0
       | none => false
#guard match OUT_STEP with
       | some o => o.linConstTerm.val ==
           14190819821033234537891308285146002190684630817697890984532326410246828863095
       | none => false

/-! ### §6b — ⚑ THE SHIFTS ARE LOAD-BEARING: bending one moves `ft_eval0`.

Independently of the constant-term residual, the derived shifts are not decorative: perturbing them
moves the Step-side `ft_eval0`. Two witnesses: the identity placeholder `replicate 7 1` (six shifts
where cosets belong) and a single bent coset (`shift[1] + 1`) on the derived vector. Both are `some`
(the shape gate accepts a seven-vector) with a `ft_eval0` DIFFERENT from the derived one — so when
the constant-term residual is closed and `ftEval0 == FT_EVAL0` holds, THESE guarantee the equality is
a real gate on the shift values, not one that would pass on any seven-vector. -/
def FT_DERIVED : Nat := 19015133850720799981561969103347224543420887819567943801623456181067047408756
#guard match deriveSide { S539508 with sh := List.replicate 7 (1 : ZMod pN) } with
       | some o => o.ftEval0.val != FT_DERIVED
       | none => false
#guard match deriveSide { S539508 with sh := TICK_SHIFTS.set 1 ((TICK_SHIFTS.getD 1 0) + 1) } with
       | some o => o.ftEval0.val != FT_DERIVED
       | none => false
/- …and it is not merely the LENGTH that the gate reads: the bent-shift vector is still well-shaped,
so the refusal above is a value refusal, exactly the §3 shift control at the anchor. -/
#guard colsOk S539508.ez S539508.ew (TICK_SHIFTS.set 1 ((TICK_SHIFTS.getD 1 0) + 1))
         S539508.mds9 S539508.log2n

/- The Step side's DERIVED domain generator and challenge lifts are consistent with the ones
`MinaWrapDeferred` uses: `rootOfUnity` here IS `MinaWrapDeferred.rootOfUnity` there, at the same
`domain_log2`, and it is the generator the `TickShifts` oracle placed the cosets against. -/
#guard (rootOfUnity pN 16).val == Dregg2.Bridge.MinaWrapDeferred.rootOfUnity 16
#guard (endoMap ((Dregg2.Bridge.MinaWrapDeferred.ENDO : Nat) : ZMod pN)
          Dregg2.Bridge.MinaWrapDeferredWeld.ZETA_CHAL).val
       == Dregg2.Bridge.MinaWrapDeferred.endoLift Dregg2.Bridge.MinaWrapDeferredWeld.ZETA_CHAL

/-! ## §7 — ⚑ THROUGH THE C-ABI GRAMMAR, on the real block.

The runtime does not call `deriveSide`; it calls `dregg_mina_wrap_ft_eval0` with a string. This
assembles that string from the real block's WRAP-side values and checks the answer, so the wire
layer and the `Nat` parsing are exercised on real data rather than only on §10b's synthetic
refusals. -/

/-- Render a list as the gate's `NATS`. -/
def nats (xs : List (ZMod qN)) : String := String.intercalate "," (xs.map (fun x => toString x.val))

/-- The real block's WRAP-side wire string. -/
def WIRE_539508_WRAP : String :=
  "m=q;lg=14;al=" ++ toString ALPHA_CHAL ++ ";be=" ++ toString BETA_N
  ++ ";ga=" ++ toString GAMMA_N ++ ";ze=" ++ toString ZETA_CHAL
  ++ ";ez=" ++ nats EZ ++ ";ew=" ++ nats EW
  ++ ";pz=" ++ toString Dregg2.Circuit.Emit.MinaRealBlockGate.PZ.val
  ++ ";er=" ++ toString (ENDO_R : ZMod qN).val
  ++ ";en=" ++ toString ENDO_COEFF.val
  ++ ";sh=" ++ nats Dregg2.Circuit.Emit.MinaRealBlockGate.SHIFT
  ++ ";md=" ++ nats MDS9

/-- The kimchi-TRUE answer, from `MinaRealBlockGate`'s constants. The gate does NOT reach it, because
its `lct`/`ft0` inherit the `gateLinConst` defect (§2b-head). -/
def EXPECTED_TRUE_539508_WRAP : String :=
  "lct=" ++ toString Dregg2.Circuit.Emit.MinaRealBlockGate.LCT.val
    ++ ";ft0=" ++ toString Dregg2.Circuit.Emit.MinaRealBlockGate.FT0.val
    ++ ";om=" ++ toString Dregg2.Circuit.Emit.MinaRealBlockGate.OMEGA.val
    ++ ";ze=" ++ toString Dregg2.Circuit.Emit.MinaRealBlockGate.ZETA.val
    ++ ";al=" ++ toString Dregg2.Circuit.Emit.MinaRealBlockGate.ALPHA.val

/-- The MEASURED answer the gate actually returns end-to-end: the `om`/`ze`/`al` are correct (the
derivation runs — root of unity, both challenge lifts), and the `lct`/`ft0` are the `gateLinConst`
values (`endo = ENDO_COEFF = ENDO_R`), off from `LCT`/`FT0` by the constant-term delta. -/
def EXPECTED_MEASURED_539508_WRAP : String :=
  "lct=8681360867184798963981514810663644655673070993510971872798076584395968078520"
    ++ ";ft0=8573205762937390675306159305751401381856834676248414623596577458395032123847"
    ++ ";om=" ++ toString Dregg2.Circuit.Emit.MinaRealBlockGate.OMEGA.val
    ++ ";ze=" ++ toString Dregg2.Circuit.Emit.MinaRealBlockGate.ZETA.val
    ++ ";al=" ++ toString Dregg2.Circuit.Emit.MinaRealBlockGate.ALPHA.val

/- ⚑ **THE EXPORTED GATE, ON A REAL MINA BLOCK, END TO END** — it runs (parse + wire + `Nat` + the
whole derivation), reproducing the correct `om`/`ze`/`al`; its `lct`/`ft0` are the `gateLinConst`
values. -/
#guard minaWrapFtEval0Gate WIRE_539508_WRAP == EXPECTED_MEASURED_539508_WRAP
/- …and it does NOT match the kimchi-true answer — the `gateLinConst` defect, exhibited at the
C-ABI. When `gateLinConst` is fixed, `EXPECTED_MEASURED` becomes `EXPECTED_TRUE` and this flips. -/
#guard minaWrapFtEval0Gate WIRE_539508_WRAP != EXPECTED_TRUE_539508_WRAP

/- …and the same wire with the field selector flipped to the STEP side is a DIFFERENT answer, not
the same one — so `m` is read and the two moduli are not silently one. -/
#guard minaWrapFtEval0Gate ("m=p" ++ (WIRE_539508_WRAP.drop 3)) != EXPECTED_MEASURED_539508_WRAP

end Dregg2.Bridge.MinaWrapFtEval0Weld
