/-
# EmitWrapFortyAgreement — the emitted forty against Mina's forty, SLOT BY SLOT, plus §19/§20's
own derivation against the REAL Wrap object it is now about.

⚑ **THIS PRINTS THE ONE NUMBER THE LADDER IS GRADED ON, AND IT IS NOT "REACH".** `w12_close`'s
docblock (`KimchiWrapMainPins10`) says a slot is REACHED when the assembly puts a DERIVATION there;
AGREEMENT is the strictly stronger question `emitted[i] == WRAP_PUBLIC_INPUT_MEASURED[i]`, and the
two have been read for one another. This driver answers only the second, per slot, with the
disagreeing pairs printed so a reader can see WHICH object each side is about.

⚠ **IT IS A DRIVER, NOT A GATE.** Nothing here is a theorem and nothing here can go red. The gates
are in `KimchiWrapMainPins10` and `KimchiWrapMainPins12`; this is how their counts are re-derived
when something moves.

    cd metatheory
    lake env lean --run Dregg2/Circuit/Emit/EmitWrapFortyAgreement.lean
-/
import Dregg2.Circuit.Emit.KimchiWrapMainCore

open Dregg2.Circuit.Emit.KimchiWrapMain
open Dregg2.Circuit.Emit.PastaField (qN)

def minaForty : List Nat := Dregg2.Circuit.Emit.MinaWrapDeferredWords.WRAP_PUBLIC_INPUT_MEASURED

def forty (name : String) (t : WrapData) (k : Rung) : IO Unit := do
  let em := (wrapPublicAt t k).map (fun z => (z % (qN : Int)).toNat)
  let n := minaForty.length
  let agree := (List.range n).filter (fun i => em.getD i 0 == minaForty.getD i 0)
  IO.println s!"== FORTY: {name} =="
  IO.println s!"   emitted width {em.length}, Mina's {n}"
  IO.println s!"   AGREE at {agree.length} of {n}: {agree}"
  for i in List.range n do
    let a := em.getD i 0
    let b := minaForty.getD i 0
    IO.println s!"   [{i}] {if a == b then "==" else "!="} emitted={a} mina={b}"

/-- §19's program on the RAW real evaluations — the probe environment. (It read "i.e. before
`finZW0` solves `z(ζω)`" until 2026-08-07; there is no solve any more, so "raw" and "emitted" name
one reading.) This is what should reproduce Mina's own `ft_eval0` if the block really is the real
Wrap proof and §19 really is `plonk_checks.ml`. -/
def probe (name : String) (t : WrapData) (p : Nat) : IO Unit := do
  let d := finProbeData t.sh t.sp p
  IO.println s!"== §19 PROBE (raw evals): {name} block {p} =="
  IO.println s!"   zetaN     = {d.vals.getD d.fp.slots.zetaN 0}"
  IO.println s!"   zkp       = {d.vals.getD d.fp.slots.zkp 0}"
  IO.println s!"   linConst  = {d.vals.getD d.fp.slots.linConst 0}"
  IO.println s!"   ftEval0   = {d.vals.getD d.fp.slots.ftEval0 0}"
  IO.println s!"   perm      = {d.vals.getD d.fp.slots.perm 0}"
  IO.println s!"   permUsed  = {d.vals.getD d.fp.slots.permUsed 0}"

def realBlock : IO Unit := do
  IO.println "== MINA DEVNET BLOCK 539508's OWN WRAP PROOF =="
  IO.println s!"   FT0 = {ZMod.val Dregg2.Circuit.Emit.MinaRealBlockGate.FT0}"
  IO.println s!"   FT1 = {ZMod.val Dregg2.Circuit.Emit.MinaRealBlockGate.FT1}"
  IO.println s!"   PZ  = {ZMod.val Dregg2.Circuit.Emit.MinaRealBlockGate.PZ}"
  IO.println s!"   LCT = {ZMod.val Dregg2.Circuit.Emit.MinaRealBlockGate.LCT}"
  IO.println s!"   CIP = {ZMod.val Dregg2.Circuit.Emit.MinaRealBlockGate.CIP}"
  IO.println s!"   V_CHAL (ξ′) = {Dregg2.Circuit.Emit.MinaRealBlockTranscript.V_CHAL}"
  IO.println s!"   U_CHAL (r′) = {Dregg2.Circuit.Emit.MinaRealBlockTranscript.U_CHAL}"

def statement : IO Unit := do
  IO.println "== THE LIVE BLOCK'S PACKED STATEMENT WORDS (STEP_PUBLIC_IN, recomposed) =="
  for w in [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 26] do
    IO.println s!"   block{FIN_LIVE_BLOCK} word {w} (packed {finBlockWord FIN_LIVE_BLOCK w}) \
                 = {finBlockVal FIN_LIVE_BLOCK w}"

def main : IO Unit := do
  realBlock
  statement
  IO.println s!"== §20 DERIVED WORDS (smoke) = {finSpDerivedWords tWSmoke}"
  probe "smoke" tWSmoke FIN_LIVE_BLOCK
  probe "smoke" tWSmoke (1 - FIN_LIVE_BLOCK)
  -- ⚑ **BOTH SHAPES, IN ONE RUN, SMOKE FIRST.** The driver printed only `shapeWrap`'s until
  -- 2026-08-09, which is precisely how the two get confused: `KimchiWrapMainPins12`'s docblock
  -- warns that quoting the smoke count as "the agreement" is a misquote, and its theorem carries
  -- both conjuncts *so a reader who finds one also finds the other* — while the instrument that
  -- re-derives them showed one. It is not a worse measurement of the same thing; it is a
  -- measurement of a different, smaller circuit, and it is labelled here.
  forty "shapeSmoke / w12_close  ⚠ NOT the ladder's number" tWSmoke .close
  forty "shapeWrap / w12_close  ⚑ THE NUMBER THE LADDER IS GRADED ON" (mkWrap shapeWrap) .close
where
  tWSmoke : WrapData := mkWrap shapeSmoke
