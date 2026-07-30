/-
# Dregg2.Bridge.MinaWrapFtEval0Weld — **the reality gate: on devnet block 539508's WRAP proof, the
six transcribed gate bodies reproduce the carried `LCT`, `ft_eval0` follows, the public polynomial
at ζ is RE-COMPUTED rather than carried, and `shift_scalar` closes `cipShifted`.**

## What this file is for

`MinaWrapDeferredWeld` §6 left the per-block path with a named residual — **two `ft_eval0`s**, one
per side of the Pasta cycle — and described both as wanting "a linearization constant term this
tree carries rather than derives". This file measures whether that is still true.

It is not. `KimchiVerify.gateLinConst` transcribes all six v1 gate bodies, and
**`MinaRealBlockGate.EVZ` slots 5-10 are the real block's six gate selectors and NONE of them is
zero** — so the real Mina Wrap proof fires `complete_add`, `varbasemul`, `endomul` and
`endomul_scalar`, the four bodies whose only previous evidence was a source reading against two
fixtures that zeroed their selectors. §2 below is the first differential those four have had.

## ⚑⚑ WHAT IS MEASURED AND WHAT IS NOT — read before quoting this file

  * **WRAP side, `linConstTerm`: MEASURED.** §2. Computed from the block's own 86 evaluation values
    and four named config objects, equal to `MinaRealBlockGate.LCT` — which came out of Rust's
    `PolishToken::evaluate(constant_term)` on a path that touches no Lean. The carrier is retired
    on a real Mina block.
  * **WRAP side, `ft_eval0`: MEASURED.** §3, and it is downstream of the line above, so it is not
    an independent fact — it is the statement that the C5 fold consumes the derived constant term
    correctly.
  * **The public polynomial `p(ζ)`, `p(ζω)`: MEASURED.** §4. `KimchiVerify` §9b names this as a
    residual ("recomputing `p(ζ)` needs the un-extracted batch-inverted Lagrange denominators");
    it is recomputed here from the forty public-input words with WITNESSED inverses.
  * **`cipShifted`: MEASURED.** §5. `shift_scalar` of `MinaRealBlockGate.CIP` IS
    `MinaWrapOpeningGate.CIP_SHIFTED`, which was the second of `MinaWrapChallengesWeld`'s two
    non-decodable arguments.
  * ⚠ **STEP side: NOT MEASURED, and the reason is CONFIG, not arithmetic.** §6. Every input the
    Step-side derivation wants is assembled below from block 539508's own binprot bytes EXCEPT the
    **seven Tick coset `shifts` at `domain_log2 = 16`**, which do not exist in this tree in any
    form. They are Blake2b-derived per domain (`kimchi/src/circuits/polynomials/permutation.rs`
    `Shifts::new`), so they are an EXTRACTOR line, not a formalization — but until that line is
    run, the Step side has a wire and no answer, and this file says so rather than letting a green
    build imply otherwise.

Compiled, not kernel: every pin below is `#guard`, and that is the point of the file. NOT rooted in
`Dregg2/FFI.lean` — it imports one-block fixtures whose kernel cost belongs off the archive's hot
path, the same split `MinaWrapChallengesWeld` documents.
-/
import Dregg2.Bridge.MinaWrapFtEval0
import Dregg2.Bridge.MinaWrapDeferredWeld
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
    alphaChal := ALPHA_CHAL, betaChal := BETA_N, gammaChal := GAMMA_CHAL, zetaChal := ZETA_CHAL
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

/-! ## §2 — ⚑⚑ THE HEADLINE: the six transcribed gate bodies REPRODUCE the carried `LCT`.

`MinaRealBlockGate.LCT` is Rust's `PolishToken::evaluate(constant_term)` on the real devnet block —
extracted on a path that runs o1-labs' own linearization and touches nothing in this tree. The left
side is `Σ_gate selector·(Σᵢ αⁱ·constraintᵢ)` over six bodies transcribed from
`kimchi/src/circuits/polynomials/*.rs`, evaluated at the block's own 43+43 columns.

**If this is green, `MinaRealBlockGate`'s `LCT` carrier is retired on a real Mina block and
`ft_eval0` is a function of the wire.** -/

/-- The derived side, once, so §2-§3 read the same object. -/
def OUT : Option (SideOut qN) := deriveSide W539508

#guard OUT.isSome

#guard match OUT with
       | some o => o.linConstTerm == Dregg2.Circuit.Emit.MinaRealBlockGate.LCT
       | none => false

/-! ### §2b — NON-VACUITY: each of the four previously-unexercised bodies is LOAD-BEARING.

Without these, "the six bodies reproduce `LCT`" is compatible with four bodies that contribute
nothing — which is exactly the state the two earlier fixtures were in. One control per selector:
zeroing it must move the constant term. -/

/-- `gateLinConst` at the real block, with one selector zeroed. -/
def lctWithSelZeroed (k : Nat) : ZMod qN :=
  match quotientConsts qN with
  | some (cA, cB, cC) => gateLinConst (gateEvalsOf { W539508 with ez := EZ.set (IDX_SEL + k) 0 } cA cB cC)
  | none => 0

#guard lctWithSelZeroed 0 != Dregg2.Circuit.Emit.MinaRealBlockGate.LCT   -- generic
#guard lctWithSelZeroed 1 != Dregg2.Circuit.Emit.MinaRealBlockGate.LCT   -- poseidon
#guard lctWithSelZeroed 2 != Dregg2.Circuit.Emit.MinaRealBlockGate.LCT   -- ⚑ complete_add
#guard lctWithSelZeroed 3 != Dregg2.Circuit.Emit.MinaRealBlockGate.LCT   -- ⚑ varbasemul
#guard lctWithSelZeroed 4 != Dregg2.Circuit.Emit.MinaRealBlockGate.LCT   -- ⚑ endomul
#guard lctWithSelZeroed 5 != Dregg2.Circuit.Emit.MinaRealBlockGate.LCT   -- ⚑ endomul_scalar

/- ⚑ And the `endo` CONFIG is genuinely consumed: the `endomul` body reads it, so a different
coefficient produces a different constant term. This is what `KimchiPoseidonGate` could not say,
because its `emulSel` was zero. -/
#guard match quotientConsts qN with
       | some (cA, cB, cC) =>
         gateLinConst (gateEvalsOf { W539508 with endo := ENDO_COEFF + 1 } cA cB cC)
           != Dregg2.Circuit.Emit.MinaRealBlockGate.LCT
       | none => false

/- …and so are the coefficient column (the Poseidon round constants) and the ζω witness column
(only the fifth Poseidon round equation and `varbasemul`/`endomul`'s NEXT row read it). -/
#guard match quotientConsts qN with
       | some (cA, cB, cC) =>
         gateLinConst (gateEvalsOf { W539508 with ez := EZ.set IDX_COEFF 0 } cA cB cC)
           != Dregg2.Circuit.Emit.MinaRealBlockGate.LCT
       | none => false
#guard match quotientConsts qN with
       | some (cA, cB, cC) =>
         gateLinConst (gateEvalsOf { W539508 with ew := EW.set IDX_W 0 } cA cB cC)
           != Dregg2.Circuit.Emit.MinaRealBlockGate.LCT
       | none => false

/-! ## §3 — ⚑⚑ `ft_eval0`, from the wire, with no carrier.

`MinaRealBlockGate.real_ft_eval0` proves the same equality in the kernel with `LCT` and `DINV` fed
in as literals. Here both are DERIVED: the constant term by §2, the inverse by the witnessed
Fermat ladder. -/

#guard match OUT with
       | some o => o.ftEval0 == Dregg2.Circuit.Emit.MinaRealBlockGate.FT0
       | none => false

/- The witnessed inverse really is `DINV` — so the ladder is not accidentally agreeing through a
cancelling error. -/
#guard inv? ((Dregg2.Circuit.Emit.MinaRealBlockGate.ZETA
              - powFast Dregg2.Circuit.Emit.MinaRealBlockGate.OMEGA (16384 - 3))
             * (Dregg2.Circuit.Emit.MinaRealBlockGate.ZETA - 1))
       == some Dregg2.Circuit.Emit.MinaRealBlockGate.DINV

/- Non-vacuity of the C5 fold through THIS path: a moved public evaluation moves `ft_eval0`, and so
does a moved σ column. `MinaRealBlockGate.real_ft_eval0_discriminates` says the same about the
shipped formula; this says it about the derivation that feeds it. -/
#guard match deriveSide { W539508 with
                          pZeta := Dregg2.Circuit.Emit.MinaRealBlockGate.PZ + 1 } with
       | some o => o.ftEval0 != Dregg2.Circuit.Emit.MinaRealBlockGate.FT0
       | none => false
#guard match deriveSide { W539508 with ez := EZ.set IDX_S 0 } with
       | some o => o.ftEval0 != Dregg2.Circuit.Emit.MinaRealBlockGate.FT0
       | none => false
/- …and a wrong coset shift moves it, which is what makes §6's residual a real one rather than a
formality. -/
#guard match deriveSide { W539508 with
                          sh := Dregg2.Circuit.Emit.MinaRealBlockGate.SHIFT.set 1 0 } with
       | some o => o.ftEval0 != Dregg2.Circuit.Emit.MinaRealBlockGate.FT0
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

/-! ## §6 — ⚠ THE STEP SIDE: a complete wire and ONE missing config object.

Everything `expand_deferred`'s `ft_eval0` wants is assembled below from block 539508's own binprot
bytes, which `MinaWrapDeferredWeld` extracted by re-walking `decode_proof_at` field for field:

| input | source | status |
|---|---|---|
| the 43+43 evaluation columns | `MinaWrapDeferredWeld.EVALS` | ✅ WIRE |
| `p(ζ)` | `prev_evals.evals.public_input.0` | ✅ WIRE — the Step side carries it, unlike the Wrap side |
| α′, β, γ, ζ′ | `deferred_values.plonk` | ✅ WIRE |
| `domain_log2` | `branch_data` | ✅ WIRE |
| `er` = `Endo.Wrap_inner_curve.scalar` | `MinaWrapDeferred.ENDO` | ✅ CONFIG, named |
| `mds` = `fp_kimchi` | `PastaPoseidon.mdsN` | ✅ CONFIG, in tree |
| `endo_coefficient` | the Tick verifier index | ⚠ CONFIG, read as `er` (see §2b for why that reading is only load-bearing where a selector fires) |
| **the seven Tick coset `shifts` at `2^16`** | — | ❌ **NOT IN THIS TREE** |

`Shifts::new` derives them by Blake2b over the domain, so they are one extractor line against
openmina's Step verifier index and not a formalization. §3's shift control shows they are
load-bearing: a single wrong shift moves `ft_eval0`.

⚑ Until that line is run, the STEP side's `ft_eval0` — and therefore public-input word 0, and
therefore `public_comm` — is **derived to within seven field elements of trusted config**, which is
a strictly smaller residual than "a ~3,300-line generated-OCaml constant term" and should be
described as the smaller one. -/

/-- The Step side's 43 columns at ζ, from the block's own bytes. -/
def EZ_STEP : List (ZMod pN) :=
  Dregg2.Bridge.MinaWrapDeferredWeld.EVALS.map (fun p => ((p.1 : ZMod pN)))
/-- …and at ζω. -/
def EW_STEP : List (ZMod pN) :=
  Dregg2.Bridge.MinaWrapDeferredWeld.EVALS.map (fun p => ((p.2 : ZMod pN)))

#guard EZ_STEP.length == 43
#guard EW_STEP.length == 43

/-- ⚑ **THE MISSING CONFIG OBJECT, exhibited as a hole rather than described as one.** Seven coset
shifts, of which only `shifts[0] = 1` is known without an extractor. A placeholder of the wrong
length is what this file has, and `deriveSide` REFUSES it — which is the fail-closed behaviour, and
is why §6 has no answer rather than a wrong one. -/
def TICK_SHIFTS_PARTIAL : List (ZMod pN) := [1]

/-- Block 539508's STEP side, complete except for `sh`. -/
def S539508 : SideWire pN :=
  { log2n := Dregg2.Bridge.MinaWrapDeferredWeld.DOMAIN_LOG2
    alphaChal := Dregg2.Bridge.MinaWrapDeferredWeld.ALPHA_CHAL
    betaChal := Dregg2.Bridge.MinaWrapDeferredWeld.BETA_CHAL
    gammaChal := Dregg2.Bridge.MinaWrapDeferredWeld.GAMMA_CHAL
    zetaChal := Dregg2.Bridge.MinaWrapDeferredWeld.ZETA_CHAL
    ez := EZ_STEP, ew := EW_STEP
    pZeta := ((Dregg2.Bridge.MinaWrapDeferredWeld.PUB_EVAL.1 : Nat) : ZMod pN)
    er := ((Dregg2.Bridge.MinaWrapDeferred.ENDO : Nat) : ZMod pN)
    endo := ((Dregg2.Bridge.MinaWrapDeferred.ENDO : Nat) : ZMod pN)
    sh := TICK_SHIFTS_PARTIAL
    mds9 := (Dregg2.Circuit.Emit.PastaPoseidon.mdsN.flatten).map (fun x => (x : ZMod pN)) }

/- ⚑ **THE REFUSAL, exhibited.** The Step side is not derived on seven-minus-six shifts; it is
refused, and the refusal is the shape gate's. -/
#guard (deriveSide S539508).isNone

/- …and everything ELSE about it is well-formed: swap in any seven-element placeholder and the
shape gate accepts, so the ONLY thing standing between this file and a Step-side answer is the
value of those seven elements. -/
#guard colsOk S539508.ez S539508.ew (List.replicate 7 (1 : ZMod pN)) S539508.mds9 S539508.log2n
#guard (deriveSide { S539508 with sh := List.replicate 7 (1 : ZMod pN) }).isSome

/- …and with a placeholder the answer is NOT the block's `ft_eval0` — stated so that when the
extractor lands, the difference between "the shifts are right" and "anything is accepted" is
already on the record. `MinaWrapDeferredWeld.FT_EVAL0` was SOLVED from public-input slot 0, so it
is the comparand the extractor must hit. -/
#guard match deriveSide { S539508 with sh := List.replicate 7 (1 : ZMod pN) } with
       | some o => o.ftEval0.val != Dregg2.Bridge.MinaWrapDeferredWeld.FT_EVAL0
       | none => false

/- The Step side's DERIVED domain generator and challenge lifts are consistent with the ones
`MinaWrapDeferred` uses, so when the shifts land nothing else has to move: `rootOfUnity` here IS
`MinaWrapDeferred.rootOfUnity` there, at the same `domain_log2`. -/
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

/-- The expected answer, assembled from `MinaRealBlockGate`'s constants and NOT from the gate's own
output. -/
def EXPECTED_539508_WRAP : String :=
  "lct=" ++ toString Dregg2.Circuit.Emit.MinaRealBlockGate.LCT.val
    ++ ";ft0=" ++ toString Dregg2.Circuit.Emit.MinaRealBlockGate.FT0.val
    ++ ";om=" ++ toString Dregg2.Circuit.Emit.MinaRealBlockGate.OMEGA.val
    ++ ";ze=" ++ toString Dregg2.Circuit.Emit.MinaRealBlockGate.ZETA.val
    ++ ";al=" ++ toString Dregg2.Circuit.Emit.MinaRealBlockGate.ALPHA.val

/- ⚑⚑ **THE EXPORTED GATE, ON A REAL MINA BLOCK, END TO END.** -/
#guard minaWrapFtEval0Gate WIRE_539508_WRAP == EXPECTED_539508_WRAP

/- …and the same wire with the field selector flipped to the STEP side is a DIFFERENT answer, not
the same one — so `m` is read and the two moduli are not silently one. -/
#guard minaWrapFtEval0Gate ("m=p" ++ (WIRE_539508_WRAP.drop 3)) != EXPECTED_539508_WRAP

end Dregg2.Bridge.MinaWrapFtEval0Weld
