/-
# CheckKimchiCellCommit — THE COMPUTATIONAL GATE for the route-B GROUP-4 commitment binding.

## Why this is an executable and not a pile of `#guard`s

`KimchiCellCommit`'s emitted object is 15,600 instructions, 76,489 witness values and 10,570 rows.
`#guard` evaluates at ELABORATION time through `whnf`, which materialises the whole `List KRow` as
an expression: measured on hbox 2026-07-30, the module went past 20 GB resident and was still
climbing, and the elaboration had to be killed. So the checks live here and run through the
COMPILER instead — same `def`s, same predicates, ~10 s.

**It is a gate: it exits nonzero.** `EmitKimchiCellCommit` runs the same `emissionChecksHold`
before it will write an artifact, so the JSON the o1js side consumes cannot come from an emission
that fails one of these. `scripts/check-kimchi-cellcommit.sh` is the wrapper.

## What it checks, over the ACTUAL emitted rows

  * **acceptance** — every one of the 10,570 emitted rows is satisfied by the honest cell's witness
    (`rowAcceptB`, whose soundness for `KRow.holds` is a theorem in the module). This is the
    anti-vacuity exhibit: without it every forcing theorem could be true for want of a satisfying
    assignment. `badRowCount`/`firstBadRow` keep a failure legible — a conjunction going red tells
    you nothing about WHICH row, and this generator's ancestor has already been wrong once in a way
    only the row-level check caught.
  * **the digest carrier HOLDS at the honest cell** — each site's digest lane carries exactly
    `hash4to1Real` of the columns the DEPLOYED site absorbs. The one undischarged hypothesis of the
    forcing theorem therefore demands nothing an honest instance does not supply.
  * **the commitment is the deployed one** — the last lane equals `cellCommitOf hash4to1Real` of
    the cell's after-state, i.e. the felt `cell_state.rs::compute_commitment` produces.
  * **the witness stays inside the Pasta field** — every value the commitment emission produces.
  * **the cost pins** — rows, instruction count, variable count and gate histogram.
-/
import Dregg2.Circuit.Emit.KimchiCellCommit

open Dregg2.Circuit.Emit.KimchiCellCommit
open Dregg2.Circuit.Emit.KimchiTarget

/-- One named check. -/
structure Check where
  name : String
  ok : Bool
  detail : String

def checks : List Check :=
  [ ⟨"rows accept the honest cell", rowsAcceptHonestCell,
      s!"badRowCount={badRowCount} firstBadRow={firstBadRow}"⟩
  , ⟨"DigestCarrier holds at the honest cell", digestCarrierHoldsB, ""⟩
  , ⟨"the emitted lane IS the deployed cell commitment", commitLaneIsCellCommit,
      s!"lane={siteCtx.get (digLane 3)} cellCommitOf={cellCommitOf hash4to1Real cellAssign}"⟩
  , ⟨"every commitment witness value is in [0, pastaN)", commitValsInPasta, ""⟩
  , ⟨"cost pins", costPinsHold,
      s!"siteRows={siteRowCount} commitRows={commitRowCount} routeBRows={routeBRowCount} " ++
      s!"ops={siteOps.length} vars={siteCtx.vals.size} lanes={digestLaneVars} " ++
      s!"hist={repr (commitHistogram.filter (fun x => x.2 != 0))} " ++
      s!"picklesStep={effectRowsPerPickleStep}"⟩
  , ⟨"the wiring is the DEPLOYED site list", siteInCols == [[76,77,78,79],[80,81,82,83],
      [84,85,86,87],[98,99,100,186]] && siteDigestCols == [98,99,100,88],
      s!"in={siteInCols} digest={siteDigestCols}"⟩
  , ⟨"honestD3 IS cellCommitOf hash4to1Real, and is the pinned felt",
      honestD3_is_cellCommit && (honestD3 == (841295468 : ℤ)), s!"honestD3={honestD3}"⟩
  , ⟨"emissionChecksHold (the def the emitter gates on)", emissionChecksHold, ""⟩ ]

def main : IO UInt32 := do
  IO.println "== KimchiCellCommit — the GROUP-4 commitment emission, checked =="
  let mut bad := 0
  for c in checks do
    IO.println s!"[{if c.ok then \"ok  \" else \"FAIL\"}] {c.name}"
    if c.detail != "" then IO.println s!"         {c.detail}"
    if !c.ok then bad := bad + 1
  IO.println ""
  if bad == 0 then
    IO.println "VERDICT: green — the emitted circuit accepts the honest cell and computes its commitment."
    IO.println s!"         emitted rows: sites {siteRowCount} · commitment {commitRowCount} · route B {routeBRowCount}"
    return 0
  else
    IO.println s!"VERDICT: RED — {bad} check(s) failed."
    return 1
