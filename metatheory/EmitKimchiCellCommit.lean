/-
# EmitKimchiCellCommit — the ROUTE-B GROUP-4 COMMITMENT artifact emitter.

Streams `KimchiCellCommit`'s emitted instruction stream, the Lean-computed honest witness, and the
column map to stdout as JSON. The stream is ~15,600 instructions and ~76,500 witness values, so it
is written INCREMENTALLY: building the string first would be quadratic in `String.append`.

The o1js consumer (`bridge/mina-zkapp/src/DreggCellCommitNative.ts`) transcribes this array into
`Gates.generic` / `Gates.rangeCheck0` calls and witnesses the vector verbatim. It authors no
constraint and holds no dregg semantics — which is what keeps route B inside the
Lean-authored-AIR law.

SCRATCH executable:
  `lake env lean --run EmitKimchiCellCommit.lean > bridge/mina-zkapp/src/generated/kimchi-cellcommit-b.json`
-/
import Dregg2.Circuit.Emit.KimchiCellCommit

open Dregg2.Circuit.Emit.KimchiCellCommit
open Dregg2.Circuit.Emit.KimchiTarget
open Dregg2.Circuit.Emit.KimchiLower

def emitList {α : Type} (h : IO.FS.Stream) (xs : List α) (f : α → String) : IO Unit := do
  let mut first := true
  for x in xs do
    if !first then h.putStr ","
    first := false
    h.putStr (f x)

def main : IO Unit := do
  -- ⚑ REFUSE rather than emit from an emission that fails its own checks. The same `def`
  -- `CheckKimchiCellCommit` gates on, so the artifact and the gate cannot disagree about green.
  unless emissionChecksHold do
    throw (IO.userError
      "KimchiCellCommit: emissionChecksHold is FALSE — refusing to emit. Run CheckKimchiCellCommit.")
  let h ← IO.getStdout
  h.putStr "{\"air\":\"dregg-effectvm-incrementNonce-v2-kimchi-b-cellcommit\""
  h.putStr ",\"source\":\"Dregg2.Circuit.Emit.KimchiCellCommit.commitOps\""
  h.putStr s!",\"firstFreshVar\":{NVC}"
  h.putStr s!",\"ops\":{commitOps.length}"
  h.putStr s!",\"siteRows\":{siteRowCount}"
  h.putStr s!",\"commitRows\":{commitRowCount}"
  h.putStr s!",\"routeBRows\":{routeBRowCount}"
  h.putStr s!",\"vars\":{commitWitness.length}"
  h.putStr ",\"cols\":{"
  emitList h commitCols (fun p => "\"" ++ p.1 ++ "\":" ++ toString p.2)
  h.putStr "},\"siteInCols\":["
  emitList h siteInCols (fun l => "[" ++ String.intercalate "," (l.map toString) ++ "]")
  h.putStr "],\"siteDigestCols\":["
  emitList h siteDigestCols (fun c => toString c)
  h.putStr "],\"honestCommit\":\""
  h.putStr (toString honestD3)
  h.putStr "\",\"ops_\":["
  emitList h commitOps opJson
  h.putStr "],\"witness\":["
  emitList h commitWitness (fun z => "\"" ++ toString z ++ "\"")
  h.putStr "]}"
  h.putStr "\n"
