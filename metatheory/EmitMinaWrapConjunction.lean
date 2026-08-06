/-
SCRATCH executable: emit the honest MULTI-ROW threaded trace for
`Dregg2.Circuit.Emit.MinaWrapConjunctionAir.conjunctionDesc`, and its falsifier.

  lake env lean --run EmitMinaWrapConjunction.lean trace  > ../circuit/tests/fixtures/mina-wrap-conjunction-trace.txt
  lake env lean --run EmitMinaWrapConjunction.lean forged > ../circuit/tests/fixtures/mina-wrap-conjunction-forged-trace.txt

⚑ **THE VALUES ARE THE REAL BLOCK'S, NOT INVENTED ONES.** ζ, ζω, ξ and the evalscale `r` are
`MinaRealBlockGate`'s extracted Wrap-side scalars; the 15 IPA challenges, their inverses, `c`, `z1`,
`z2`, `cip` and the claimed `b0` are `MinaWrapOpeningGate`'s, which that file DERIVES from the block's
own sponge (`derived_ipa_challenges`, `chal_inv_are_inverses`) and ties to the b-polynomial
(`b0_is_the_b_polynomial : bPoly CHAL ζ + r · bPoly CHAL ζω = B0`). So the honest fixture is the
block's own opening argument, folded.

⚑ **THE TRACE IS THREADED, WHICH IS THE WHOLE POINT.** Row `r` folds challenge `CHAL[14 − r]` into
the running product and squares the power; row `r+1`'s registers ARE row `r`'s outputs. After the 15
round rows the register entering row 15 is `bEval(ζ)` and `bEval(ζω)`, and row 15 — the terminal read
row — combines them by `r` and compares against the claimed `b0`.

⚠ **THE TERMINAL ROW CARRIES AN IDENTITY ROUND.** The round gates are every-row, so row 15 must
satisfy them too; it does, at challenge `1` and inverse `1` (a legal reciprocal pair). Its fold output
is never read — `bTerminalLegs` reads the register INPUT — so the identity factor enters nothing.
The alternative was to leave row 15's round columns unconstrained, and an unconstrained cell is worse
than a constrained meaningless one.

This file only RENDERS; it authors nothing.
-/
import Dregg2.Circuit.Emit.MinaWrapConjunctionAir
import Dregg2.Circuit.Emit.MinaWrapOpeningGate
import Dregg2.Circuit.Emit.MinaRealBlockGate

open Dregg2.Circuit.Emit.MinaWrapConjunctionAir
open Dregg2.Circuit.Emit.PastaField (qN)
open Dregg2.Circuit.Emit.PastaFieldSound (qLimb)

/-- ξ, the polyscale the deferred record claims and the sponge squeezes. -/
def XI_V : Nat := (Dregg2.Circuit.Emit.MinaRealBlockGate.VV).val
/-- ζ, endo-mapped. -/
def ZETA_V : Nat := (Dregg2.Circuit.Emit.MinaRealBlockGate.ZETA).val
/-- ζω. -/
def ZETAW_V : Nat := (Dregg2.Circuit.Emit.MinaRealBlockGate.ZETAW).val
/-- the evalscale `r` that combines the two evaluation points. -/
def RSQ_V : Nat := (Dregg2.Circuit.Emit.MinaRealBlockGate.UU).val

/-- The 15 round challenges, in `bEval`'s order (head = highest round). -/
def CHALS : List Nat := Dregg2.Circuit.Emit.MinaWrapOpeningGate.CHAL
/-- …and their inverses. -/
def CHALINVS : List Nat := Dregg2.Circuit.Emit.MinaWrapOpeningGate.CHAL_INV

/-- Row `r` carries challenge index `NCHAL − 1 − r`; the terminal row carries the identity pair. -/
def chalAt (r : Nat) : Nat × Nat :=
  if r < NCHAL then
    (CHALS.getD (NCHAL - 1 - r) 1, CHALINVS.getD (NCHAL - 1 - r) 1)
  else (1, 1)

/-- The global blocks, which every row repeats and the thread holds. -/
def mkRow (bcl sq0 sq1 fld0 fld1 : Nat) (r : Nat) : RowIn :=
  let cp := chalAt r
  { xiSq := XI_V, xiCl := XI_V, bCl := bcl
  , z1 := Dregg2.Circuit.Emit.MinaWrapOpeningGate.Z1
  , z2 := Dregg2.Circuit.Emit.MinaWrapOpeningGate.Z2
  , c := Dregg2.Circuit.Emit.MinaWrapOpeningGate.C
  , cip := Dregg2.Circuit.Emit.MinaWrapOpeningGate.CIP_N
  , zeta := ZETA_V, zetaw := ZETAW_V, rsq := RSQ_V
  , sq0 := sq0, sq1 := sq1, fld0 := fld0, fld1 := fld1
  , chal := cp.1, chalinv := cp.2 }

/-- The register sequence, advanced round by round. `reset?` re-seeds at row `k` — that is the
falsifier: an independently HONEST row whose registers do not continue the chain. -/
def regsAt (reset? : Option Nat) : Nat → Nat × Nat × Nat × Nat
  | 0 => (ZETA_V, ZETAW_V, 1, 1)
  | (r + 1) =>
      if reset? = some (r + 1) then (ZETA_V, ZETAW_V, 1, 1)
      else
        let st := regsAt reset? r
        stepRegs qN (mkRow 0 st.1 st.2.1 st.2.2.1 st.2.2.2 r)

/-- The claimed `b0` this trace forces: the terminal row's `fld(ζ) + r·fld(ζω)`. For the honest
trace that IS `MinaWrapOpeningGate.B0`; for the forged one it is the truncated fold's value, which is
what makes the forgery a real claim rather than a scribble. -/
def claimedB (reset? : Option Nat) : Nat :=
  let st := regsAt reset? NCHAL
  (st.2.2.1 + RSQ_V * st.2.2.2) % qN

def traceRows (reset? : Option Nat) : List (List ℤ) :=
  let bcl := claimedB reset?
  (List.range NROWS).map (fun r =>
    let st := regsAt reset? r
    conjunctionRow qN qLimb (mkRow bcl st.1 st.2.1 st.2.2.1 st.2.2.2 r))

def traceText (rows : List (List ℤ)) : String :=
  String.intercalate "\n" (rows.map (fun r => String.intercalate " " (r.map toString))) ++ "\n"

def main (args : List String) : IO Unit :=
  match args with
  | ["trace"] => IO.print (traceText (traceRows none))
  | ["forged"] => IO.print (traceText (traceRows (some 14)))
  | ["b0"] => do
      IO.println s!"honest claimed b0 = {claimedB none}"
      IO.println s!"MinaWrapOpeningGate.B0 = {Dregg2.Circuit.Emit.MinaWrapOpeningGate.B0}"
      IO.println s!"forged claimed b0 = {claimedB (some 14)}"
  | _ => IO.eprintln "usage: EmitMinaWrapConjunction.lean (trace|forged|b0)"
