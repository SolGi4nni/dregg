/-
NullaryShareProbe — settles the contradiction `KimchiWrapProverChoice`'s header RETRACTED AS
UNRESOLVED (2026-08-03).

    cd metatheory && LEAN_PATH=$(lake env printenv LEAN_PATH) lean wip/NullaryShareProbe.lean

⚑ THE TWO CLAIMS THAT CANNOT BOTH HOLD:
  * `KimchiWrapProverChoice`'s header said "three commands here name `rowsWrapKey`, so this module
    pays it three times: ~51 minutes" — i.e. **nullary sharing is PER COMMAND**;
  * the commit that wrote that sentence records the module GREEN at **1 729 s = 28 min 49 s**, which
    is LESS than the ~51 min the sentence predicts, with two further `native_decide`s and a whole
    `rowsSmXhat` still unpaid — i.e. **nullary sharing is PER MODULE**;
  * and `KimchiStepProverChoice`'s §C7 batches fourteen claims into ONE command *because* it
    measured sharing to be per command.

The header names the settling probe and never ran it: "put `#time`-style `IO.monoMsNow` deltas
around two commands that name the same nullary `def` in a scratch module and read the second one's
cost." This is that probe. `#eval` runs on the SAME interpreter `native_decide` evaluates on.

⚑ READ THE THIRD COMMAND TOO. If command 2 is free but command 3 — which names the same nullary
through a *different* expression — is not, the sharing is on the CONSTANT, not on the command's
syntax, and that is the fact that governs how these census modules should batch.
-/
import Dregg2.Circuit.Emit.KimchiRenderCompleteAdd

open Dregg2.Circuit.Emit.KimchiRenderCompleteAdd

set_option maxRecDepth 100000

/-- ~3 000 Fermat inversions — priced at 0.229 ms each by `FloorProbe3`, so ~690 ms. Nullary, closed,
and expensive enough that "was it recomputed" is not a judgement call. -/
def bigThing : Nat :=
  (List.range 3000).foldl (fun acc k => acc + fInv (k + 7)) 1

def timeIt (label : String) (f : Unit → Nat) : IO Unit := do
  let t0 ← IO.monoMsNow
  let v := f ()
  if v == 0 then throw (IO.userError "degenerate")
  let t1 ← IO.monoMsNow
  IO.println s!"{label}: {t1 - t0} ms (val mod 10^6 = {v % 1000000})"

#eval timeIt "command 1 — first mention of `bigThing`" (fun _ => bigThing)

#eval timeIt "command 2 — SAME nullary, second command" (fun _ => bigThing)

#eval timeIt "command 3 — same nullary, different expression" (fun _ => bigThing + 0)

/-- A DIFFERENT nullary of the same cost, to prove command 2/3's reading is sharing and not a warm
cache in `fInv` itself. -/
def bigThing2 : Nat :=
  (List.range 3000).foldl (fun acc k => acc + fInv (k + 9)) 1

#eval timeIt "command 4 — a DIFFERENT nullary, same cost (control)" (fun _ => bigThing2)
