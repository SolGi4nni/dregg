/-
# `Dregg2.Apps.DelegAdmit` — the RUNTIME-CALLABLE delegated tool-access ADMISSION DECISION.

## What this is

`Dregg2/Apps/ToolAccessDelegation.lean` proves the delegation crown: on a mandate cell carrying the
baked slot-caveats, the production caveat-gated executor COMMITS a metered `calls_made : c → c+1`
write IFF the delegated policy admits the invocation (`tool_invocation_commit_iff_admit`), and the
over-rate / past-deadline / out-of-scope TEETH reject it otherwise. The policy it folds is
`delegAdmit`.

That `delegAdmit` was a plain `def` — not `@[export]`ed — so THREE hand-maintained Rust
re-implementations of the same five-conjunct decision shipped alongside it
(`sdk/src/tool_gateway.rs`, `starbridge-apps/tool-access-delegation/src/lib.rs`,
`dreggnet-offerings/src/session.rs`). Each was "the byte-faithful Rust mirror"; none of them was the
decision. A Rust mirror plus a differential test is NOT a verified implementation — there is no
formal semantics of Rust, so a case-test proves nothing about all inputs.

This module is where `Grant` and `delegAdmit` now LIVE, and it is `@[export dregg_deleg_admit]`-ed so
Rust CALLS it. `ToolAccessDelegation` imports this module, so every theorem it proves — the headline
`tool_invocation_commit_iff_admit`, the three teeth, the `AppDiffPinned` corpus — is a theorem about
THIS function, the one the C-ABI entry runs. There is no second model.

## Import discipline

Imports NOTHING beyond core `Init` — no Mathlib. The `@[export]`ed object must be self-contained so
its leanc-emitted `.c` splices into `libdregg_lean.a` without dragging a Mathlib-tactic initializer
closure into the FFI link (same discipline as `Dregg2.Circuit.CrossCellConserveDecision` /
`Dregg2.Exec.DeployedConstraint` / `Dregg2.Grain.R3Verify`; see `dregg-lean-ffi/src/lean_init.c`).
The executor-routing proofs (which DO import the executor + Mathlib) stay in `ToolAccessDelegation`.

## What the decision decides

`delegAdmit g now tool old new` — may the worker advance the rate counter `old → new`, presenting
tool `tool` at height `now`, under grant `g`?  Five conjuncts, every one fail-closed:

  * SCOPE     — `tool = g.toolId` (the single allowlisted tool / MCP id);
  * DEADLINE  — `now ≤ g.deadline` (still inside the granted window);
  * STEP      — `new = old + 1` (a genuine single-call advance, no batch jump);
  * SANE      — `0 ≤ old` (no negative prior count);
  * RATE      — `new ≤ g.rateLimit` (the granted ceiling N is never exceeded).
-/

namespace Dregg2.Apps.DelegAdmit

set_option autoImplicit false

/-! ## §1 — the grant and the folded admission predicate. -/

/-- The grantor's pinned delegation parameters. `toolId` is the single allowlisted tool/MCP id
(the SCOPE); `rateLimit` is the granted invocation ceiling N; `deadline` is the expiry height. -/
structure Grant where
  /-- The single allowlisted tool / MCP id the worker is scoped to (the SCOPE). -/
  toolId    : Int
  /-- The granted invocation ceiling N: at most N tool calls under this mandate (the RATE). -/
  rateLimit : Int
  /-- The expiry height/clock: invocations presented at `now > deadline` are refused (the DEADLINE). -/
  deadline  : Int
  deriving Repr, DecidableEq

/-- **`delegAdmit g now tool old new`** — does the delegated policy admit the invocation that advances
the rate counter `old → new`, presented at height `now` for tool `tool`, under grant `g`?
Decidable, computable, FAIL-CLOSED on every conjunct.

THIS is the object `@[export dregg_deleg_admit]` compiles and `ToolAccessDelegation`'s
`tool_invocation_commit_iff_admit` / `tool_invocation_*_rejected` are proven over. -/
def delegAdmit (g : Grant) (now tool : Int) (old new : Int) : Bool :=
  decide (tool = g.toolId)            -- SCOPE: the presented tool is the allowlisted one
    && decide (now ≤ g.deadline)      -- DEADLINE: still within the granted window
    && decide (new = old + 1)         -- single-step increment (a genuine one-call advance)
    && decide (0 ≤ old)               -- sane prior count
    && decide (new ≤ g.rateLimit)     -- RATE: the new count does not exceed the granted ceiling

/-! ## §2 — the `@[export]` wire codec (Rust → Lean).

Single-line, space-separated token stream of SEVEN signed decimal integers, in the argument order of
`delegAdmit` with the grant flattened first:

```
toolId  rateLimit  deadline  now  tool  old  new
```

Output: `"1"` ADMIT · `"0"` REFUSE (the policy said no) · `""` malformed wire (fail-closed; the Rust
wrapper turns an empty answer into an `Err`, and every caller REFUSES on `Err`). The two refusal
shapes are deliberately distinguishable: `"0"` is a verdict, `""` is "no verdict was reached". -/

/-- Parse a signed decimal token (`-…` allowed). -/
def parseInt? (s : String) : Option Int :=
  if s.startsWith "-" then (s.drop 1).toNat?.map (fun n => -(Int.ofNat n))
  else s.toNat?.map Int.ofNat

/-- Parse the seven-integer wire into `(grant, now, tool, old, new)`; `none` on any malformation. -/
def parseWire (s : String) : Option (Grant × Int × Int × Int × Int) :=
  match ((s.splitOn " ").filter (fun t => t != "")).map parseInt? with
  | [some toolId, some rateLimit, some deadline, some now, some tool, some old, some new] =>
      some ({ toolId := toolId, rateLimit := rateLimit, deadline := deadline }, now, tool, old, new)
  | _ => none

/-- The whole `String → String` decision. A malformed wire yields `""` (no verdict). -/
def delegAdmitWire (s : String) : String :=
  match parseWire s with
  | none => ""
  | some (g, now, tool, old, new) => if delegAdmit g now tool old new then "1" else "0"

/-- **`@[export dregg_deleg_admit]`** — the C-ABI entry Rust calls. The delegated tool-access
admission verdict is COMPUTED HERE; `sdk`, `starbridge-tool-access-delegation` and
`dreggnet-offerings` marshal to this boundary instead of re-deciding the policy in Rust. -/
@[export dregg_deleg_admit]
def delegAdmitFFI (s : String) : String := delegAdmitWire s

/-! ## §3 — self-tests (`#guard` FAILS the build on regression — teeth, not comments).

The demo grant is `ToolAccessDelegation.demoGrant`: tool 77, rate 3, deadline 100. -/

/-- The demo grant the executor-level `#guard`s in `ToolAccessDelegation` §8 run on. -/
def demoGrant : Grant := { toolId := 77, rateLimit := 3, deadline := 100 }

-- The folded policy admits the three legal advances and rejects every violation.
#guard delegAdmit demoGrant 50 77 0 1            --  invocation 1 admitted (in-scope, in-time, 1 ≤ 3)
#guard delegAdmit demoGrant 50 77 1 2            --  invocation 2 admitted (2 ≤ 3)
#guard delegAdmit demoGrant 50 77 2 3            --  invocation 3 admitted (3 ≤ 3, the LAST)
#guard delegAdmit demoGrant 50 77 3 4 == false   --  invocation 4 REJECTED (4 > rateLimit 3 — RATE)
#guard delegAdmit demoGrant 50 99 0 1 == false   --  out-of-scope tool 99 REJECTED (SCOPE)
#guard delegAdmit demoGrant 101 77 0 1 == false  --  past-deadline (now 101 > 100) REJECTED (DEADLINE)
#guard delegAdmit demoGrant 50 77 0 2 == false   --  batch jump 0→2 REJECTED (STEP)
#guard delegAdmit demoGrant 50 77 (-1) 0 == false --  negative prior count REJECTED (SANE)

-- THE WIRE, both polarities and fail-closed on malformation.
#guard delegAdmitWire "77 3 100 50 77 0 1" == "1"    --  admitted
#guard delegAdmitWire "77 3 100 50 77 2 3" == "1"    --  the last granted call
#guard delegAdmitWire "77 3 100 50 77 3 4" == "0"    --  over-rate REFUSED
#guard delegAdmitWire "77 3 100 50 99 0 1" == "0"    --  out-of-scope REFUSED
#guard delegAdmitWire "77 3 100 101 77 0 1" == "0"   --  past-deadline REFUSED
#guard delegAdmitWire "77 3 100 50 77 0 2" == "0"    --  batch jump REFUSED
#guard delegAdmitWire "-5 3 100 50 -5 0 1" == "1"    --  NEGATIVE tool ids round-trip (signed wire)
#guard delegAdmitWire "77 3 100 50 77 0" == ""       --  short wire ⇒ NO VERDICT (fail-closed)
#guard delegAdmitWire "77 3 100 50 77 0 1 9" == ""   --  long wire ⇒ NO VERDICT (fail-closed)
#guard delegAdmitWire "77 3 100 50 seven 0 1" == ""  --  non-numeric ⇒ NO VERDICT (fail-closed)
#guard delegAdmitWire "" == ""                       --  empty ⇒ NO VERDICT (fail-closed)

end Dregg2.Apps.DelegAdmit
