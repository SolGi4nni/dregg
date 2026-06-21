/-
# PolisGovernor — the VERIFIED govStep, runnable as a service.

A callable governor binary. `main : IO Unit` reads a line-based encoding of
(world, proposed move) from stdin, applies the VERIFIED `govStep` from
`Metatheory.PolisSandbox` (admit iff the move preserves the shared floor, else
shield), and prints the verdict (`ADMIT` / `REFUSE`) plus the resulting world.

The decision is the verified one: this file does NOT re-implement the envelope.
It calls `PolisSandbox.govStep` (the same function `sandbox_governed_safe`
proves keeps the floor for EVERY controller at EVERY tick), and reads the
verdict by comparing the governed result against the raw proposed step — i.e.
ADMIT exactly when `worldFloor (stepMove w m)` holds, which is precisely the
branch `govStep` takes. No new policy logic.

## Wire encoding (one request per stdin line)

    <distFalse> <distTrue> <actor> <action> [victim]

  * distFalse, distTrue : Nat            -- the two agents' distance-to-home
  * actor               : 0 | 1          -- which agent acts (Bool false/true)
  * action              : noop | stepHome | trap
  * victim              : 0 | 1          -- required iff action = trap

Output per line:

    ADMIT  d0 d1        -- move preserved the floor; world advanced
    REFUSE d0 d1        -- move would break the floor; shielded (world unchanged)
    ERROR  <message>    -- unparseable input

budget = 5: an agent keeps its bounded exit iff its distance ≤ 5. A `trap`
pushes the victim to distance 99 (> budget), so it is REFUSED.
-/
import Metatheory.PolisSandbox

open Metatheory.PolisSandbox

namespace PolisGovernor

/-- Parse a `Bool` agent id from `"0"`/`"1"`. -/
def parseAgent (s : String) : Option AgentId :=
  match s with
  | "0" => some false
  | "1" => some true
  | _   => none

/-- Parse a `Nat` (decimal, non-empty digits). -/
def parseNat (s : String) : Option Nat :=
  if s.isEmpty || !s.all Char.isDigit then none else some s.toNat!

/-- Parse one request line into the world + proposed move the verified `govStep`
expects. The world is a function `AgentId → Nat` built from the two distances. -/
def parseRequest (line : String) : Option (World × Move) := do
  let toks := (line.splitOn " ").filter (· ≠ "")
  match toks with
  | [d0s, d1s, actS, "noop"] =>
      let d0 ← parseNat d0s
      let d1 ← parseNat d1s
      let actor ← parseAgent actS
      let w : World := fun i => if i = false then d0 else d1
      pure (w, ⟨actor, .noop⟩)
  | [d0s, d1s, actS, "stepHome"] =>
      let d0 ← parseNat d0s
      let d1 ← parseNat d1s
      let actor ← parseAgent actS
      let w : World := fun i => if i = false then d0 else d1
      pure (w, ⟨actor, .stepHome⟩)
  | [d0s, d1s, actS, "trap", vS] =>
      let d0 ← parseNat d0s
      let d1 ← parseNat d1s
      let actor ← parseAgent actS
      let victim ← parseAgent vS
      let w : World := fun i => if i = false then d0 else d1
      pure (w, ⟨actor, .trap victim⟩)
  | _ => none

/-- Render a world's two distances. -/
def showWorld (w : World) : String :=
  s!"{w false} {w true}"

/-- Handle one request: apply the VERIFIED `govStep` and read its verdict.

The verdict is `ADMIT` exactly when the governed world differs from "shield"
because the floor held — equivalently `worldFloor (stepMove w m)`, the decidable
branch `govStep` itself tests. We reuse that very `Decidable` instance so the
verdict and the returned world are the SAME decision, not two. -/
def handle (w : World) (m : Move) : String :=
  let result := govStep w m          -- THE verified decision (no re-impl)
  if worldFloor (stepMove w m) then  -- the exact branch govStep took
    s!"ADMIT  {showWorld result}"
  else
    s!"REFUSE {showWorld result}"

/-- Process one input line to one output line. -/
def respond (line : String) : String :=
  match parseRequest line with
  | some (w, m) => handle w m
  | none        => s!"ERROR  unparseable request: {line}"

end PolisGovernor

/-- Read stdin line by line, governing each request with the verified envelope. -/
partial def main : IO Unit := do
  let stdin ← IO.getStdin
  let rec loop : IO Unit := do
    let line ← stdin.getLine
    if line.isEmpty then
      pure ()  -- EOF
    else
      let trimmed := line.trimAscii.toString
      if trimmed.isEmpty then
        loop
      else
        IO.println (PolisGovernor.respond trimmed)
        loop
  loop
