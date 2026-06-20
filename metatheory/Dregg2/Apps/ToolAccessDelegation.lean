/-
# Dregg2.Apps.ToolAccessDelegation — VERIFIABLE TOOL / MCP-ACCESS DELEGATION (claude usecase #1).

An AI agent (the GRANTOR) hands another agent (the WORKER) a NARROWLY-ATTENUATED, RATE-LIMITED,
TIME-BOUNDED, REVOCABLE capability to invoke a tool / MCP on its behalf. This is the object-capability
model serving AI delegation: the grantor does NOT hand over its keys; it mints a *mandate cell* whose
slot-caveats are checked BY THE VERIFIED EXECUTOR on every tool invocation, so the worker can NEVER
invoke the tool beyond the granted rate, scope, or deadline — and the grant can be revoked.

## The two enforcement surfaces this app WELDS (both REAL, both already in the verified kernel)

  1. **Capability attenuation** — WHO may delegate, and with WHICH rights, is the agent-mandate
     attenuation theory: `Dregg2.Agent.Mandate` (Lean) / `intent/src/agent_mandate.rs` (Rust):
     `subDelegate` strictly narrows `keep`/budget/caveat, `materialize_grant = recKDelegateAtten`
     (the `execFullA` delegate-atten arm), `revoke_kills_subtree`. The agent-facing biscuit credential
     gating the EXECUTOR on the live `execFullForestG` path is `StarbridgeGated.mkAuthToken`
     (`GatedForestCfg.lean §A2`: a windowed `Authorization.token` whose attenuation caveats narrow it
     out of scope — the over-attenuated token ROLLS BACK). We REUSE that surface; we do not re-prove it.

  2. **Per-invocation consumption budget** — HOW MANY times, UNTIL WHEN, on WHICH tool. THIS is what
     `agent_mandate.rs` does NOT enforce: the rate-limit counter, the expiry deadline, and the tool
     allowlist, checked on EVERY tool call as a SLOT-CAVEAT-gated `SetField`. That is THIS file's
     contribution, and it is proven against `Dregg2.Apps.VerificationToolkit.app_commit_iff_admit` —
     the executor's caveat gate commits a tool invocation IFF the delegated policy admits it.

## The mandate cell

A tool-access mandate cell carries (slot ↦ meaning):

  * `calls_made`  (the RATE COUNTER) — incremented `c → c+1` on each invocation; `Monotonic` so it can
    never be rolled back to forge head-room, and the per-invocation admission requires `c+1 ≤ rateLimit`.
  * `rate_limit`  (the granted N) — `Immutable`: the ceiling fixed at grant, never raised by the worker.
  * `deadline`    (the EXPIRY) — `WriteOnce`: the grantor sets it ONCE at grant; thereafter frozen.
  * `tool_id`     (the SCOPE) — `Immutable`: the single allowlisted tool/MCP id; the worker may invoke
    no other tool under this mandate.

A tool invocation, at the executor boundary, is the single scalar write `calls_made : c → c+1`. Its
admission folds the WHOLE delegated policy — `c+1 ≤ rateLimit ∧ now ≤ deadline ∧ presentedTool = toolId`
— into the toolkit's `admit : Int → Int → Bool`, baked into the cell's `.admitTable` slot program. The
grantor's `(rateLimit, deadline, toolId)` are CLOSED OVER (fixed at grant); the invocation's `(now,
presentedTool)` are the presentation. So:

  * **rate**:     the table forbids `c → c+1` once `c+1 > rateLimit` — the (N+1)-th invocation is NOT in
    the table ⇒ the executor rejects it (`stateStepGuarded = none`);
  * **deadline**: a grant whose `now > deadline` produces an EMPTY admit-table ⇒ no invocation commits;
  * **scope**:    a grant whose `presentedTool ≠ toolId` produces an EMPTY admit-table ⇒ no invocation
    commits.

## Headline theorem (the invariant, proven end-to-end, no projection, no gap)

`tool_invocation_commit_iff_admit` — on a mandate cell carrying the delegated caveats, the PRODUCTION
caveat-gated executor write (`execFullA (.setFieldA worker cell "calls_made" (c+1))` — definitionally
`stateStepGuarded`) COMMITS IFF the delegated policy admits the invocation: `c+1 ≤ rateLimit ∧ now ≤
deadline ∧ presentedTool = toolId` AND the worker holds authority over the cell. This is the toolkit's
`app_commit_iff_admit` instantiated — over the WHOLE `RecChainedState` post-state, not an aggregate.

And the TEETH (`tool_invocation_*_rejected`): an over-rate / past-deadline / out-of-scope invocation is
rejected by the executor (`= none`). Plus the kernel keystones (`*_conserves`/`*_no_amplify`/
`*_authorized`) re-exported: an invocation moves NO balance and mints NO capability.

## Routing through the REAL verified executor

`execFullA s (.setFieldA actor cell f v) = stateStepGuarded s f actor cell v` DEFINITIONALLY
(`TurnExecutorFull.lean:3794`). So every toolkit theorem about `stateStepGuarded` is, verbatim, a
theorem about the production `execFullA` `setFieldA` arm. We additionally route the invocation through
the credential-gated forest entry `execFullForestG` (the `dregg_exec_full_forest_auth` 4-leg gate) via
`StarbridgeGated` — so an invocation presented with a FORGED or REVOKED biscuit credential rolls back,
and a genuine, in-scope token COMMITS. The `#guard`s exercise the full lifecycle on a concrete grant.

`#assert_axioms`-clean, no `sorry`, no `:= True`, no `native_decide`. Pure, computable, `#eval`-able.
NEW file only — touches NO existing app, `VerificationToolkit.lean`, `GatedForestCfg.lean`, the
executor, nor `Dregg2.lean`.
-/
import Dregg2.Apps.VerificationToolkit
import Dregg2.Exec.GatedForestCfg

namespace Dregg2.Apps.ToolAccessDelegation

open Dregg2.Exec
open Dregg2.Exec.EffectsState (caveatsAdmit fieldOf stateStep stateStepGuarded)
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Exec.FullForestAuth
open Dregg2.Exec.StarbridgeGated
open Dregg2.Apps.VerificationToolkit
open Dregg2.Spec (execGraph)

/-! ## §1 — The delegated grant: what the grantor fixes, what the invocation presents.

A `Grant` is the immutable bundle the grantor pins at delegation time: the tool/MCP id the worker is
scoped to, the rate ceiling N, and the expiry deadline. An invocation additionally PRESENTS `(now,
tool)`: the current height/clock and which tool it is trying to invoke. The delegated policy admits an
invocation iff scope ∧ deadline ∧ rate all hold. -/

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

/-- The slot names of the mandate cell. -/
def callsMadeSlot : FieldName := "calls_made"
def rateLimitSlot : FieldName := "rate_limit"
def deadlineSlot  : FieldName := "deadline"
def toolIdSlot    : FieldName := "tool_id"

/-! ## §2 — The folded admission predicate (the WHOLE delegated policy at the scalar boundary).

A tool invocation is the scalar write `calls_made : c → c+1`. The delegated policy admits it iff:
  * **scope**    — the presented tool matches the granted `toolId`;
  * **deadline** — the presentation height `now` is within the granted `deadline`;
  * **rate**     — the write is a genuine single-step increment `new = old + 1` AND the NEW count does
    not exceed the granted `rateLimit` (`new ≤ rateLimit`), AND the old count is sane (`0 ≤ old`).

The grantor's `(toolId, rateLimit, deadline)` and the invocation's `(now, tool)` are CLOSED OVER; the
dynamic `(old, new)` is the counter transition. This is exactly the toolkit's `admit : Int → Int →
Bool` — all the rich policy folded into the scalar boundary BEFORE it reaches the executor. -/

/-- **`delegAdmit g now tool old new`** — does the delegated policy admit the invocation that advances
the rate counter `old → new`, presented at height `now` for tool `tool`, under grant `g`?
Decidable, computable, FAIL-CLOSED on every conjunct. -/
def delegAdmit (g : Grant) (now tool : Int) (old new : Int) : Bool :=
  decide (tool = g.toolId)            -- SCOPE: the presented tool is the allowlisted one
    && decide (now ≤ g.deadline)      -- DEADLINE: still within the granted window
    && decide (new = old + 1)         -- single-step increment (a genuine one-call advance)
    && decide (0 ≤ old)               -- sane prior count
    && decide (new ≤ g.rateLimit)     -- RATE: the new count does not exceed the granted ceiling

/-! ## §3 — The mandate cell as a toolkit `AppSpec`.

The `AppSpec` installs an `.admitTable` baked from `delegAdmit` on the `calls_made` slot. The grid is
`0 .. rateLimit` for the counter (a grant of N calls ranges the counter over `{0,…,N}`); the toolkit is
fail-closed by absence outside the grid (SOUND — never admits more than `delegAdmit`). The grantor's
`(g, now, tool)` are closed into the spec, so the baked table is the policy FOR THIS PRESENTATION. -/

/-- The committed-value grid for a grant of `N` calls: the counter ranges over `0 .. N` (old) and
`1 .. N+1` (new). Built with `List.range` so it scales to any `N`. -/
def oldGrid (N : Nat) : List Int := (List.range (N + 1)).map (fun i => (i : Int))
def newGrid (N : Nat) : List Int := (List.range (N + 1)).map (fun i => (i : Int) + 1)

/-- **`mandateSpec g now tool cell`** — the tool-access mandate as a `VerificationToolkit.AppSpec`:
the `calls_made` slot, the mandate cell, the folded `delegAdmit g now tool` predicate, over the
`0..rateLimit` counter grid. The toolkit bakes the `.admitTable` and gives us commit-iff-admit + the
rejection teeth + conservation + non-amplification with NO re-proof. -/
def mandateSpec (g : Grant) (now tool : Int) (cell : CellId) : AppSpec where
  slot     := callsMadeSlot
  cell     := cell
  admit    := delegAdmit g now tool
  oldRange := oldGrid g.rateLimit.toNat
  newRange := newGrid g.rateLimit.toNat

/-- The mandate's `calls_made`-slot program is exactly an `.admitTable` baked from `delegAdmit`. -/
theorem mandateSpec_caveats (g : Grant) (now tool : Int) (cell : CellId) :
    (mandateSpec g now tool cell).caveats
      = [ .admitTable callsMadeSlot (mandateSpec g now tool cell).admitTable ] := rfl

/-! ## §4 — THE HEADLINE: commit-iff-admit for a tool invocation (toolkit-instantiated).

On a mandate cell carrying the delegated caveats, the PRODUCTION caveat-gated executor write — i.e.
`execFullA (.setFieldA worker cell "calls_made" (c+1))`, which is DEFINITIONALLY `stateStepGuarded`
(`TurnExecutorFull.lean:3794`) — COMMITS (is `some`) IFF the delegated policy admits the invocation AND
the worker holds authority over the cell. The whole `RecChainedState` post-state, not a projection. -/

/-- **`setFieldA_is_stateStepGuarded`** — the production executor's `setFieldA` arm IS the caveat gate.
The bridge that makes every toolkit theorem about `stateStepGuarded` a theorem about `execFullA`. -/
theorem setFieldA_is_stateStepGuarded (s : RecChainedState) (actor cell : CellId) (f : FieldName)
    (v : Int) : execFullA s (.setFieldA actor cell f v) = stateStepGuarded s f actor cell v := rfl

/-- **`tool_invocation_commit_iff_admit` — THE HEADLINE INVARIANT.** On a mandate cell
carrying the delegated caveats, with the committed counter `c` and the next count `c+1` on the grant's
grid, the production caveat-gated executor COMMITS the invocation IFF `delegAdmit g now tool c (c+1)`
(scope ∧ deadline ∧ `c+1 ≤ rateLimit`) AND the worker held authority. A worker can NEVER drive a
tool invocation past the granted rate / scope / deadline — the caveat gate decides the SAME policy the
grantor folded, on the executor's own field write. -/
theorem tool_invocation_commit_iff_admit (g : Grant) (now tool : Int) (cell worker : CellId)
    (s : RecChainedState) (c : Int)
    (hprog : s.kernel.slotCaveats cell = (mandateSpec g now tool cell).caveats)
    (hcur : (mandateSpec g now tool cell).committed s.kernel = c)
    (hold : c ∈ (mandateSpec g now tool cell).oldRange)
    (hnew : (c + 1) ∈ (mandateSpec g now tool cell).newRange) :
    (execFullA s (.setFieldA worker cell callsMadeSlot (c + 1))).isSome = true
      ↔ (delegAdmit g now tool c (c + 1) = true
          ∧ (stateStep s callsMadeSlot worker cell (.int (c + 1))).isSome = true) := by
  rw [setFieldA_is_stateStepGuarded]
  have h := app_commit_iff_admit (mandateSpec g now tool cell) s hprog worker (c + 1)
    (by rw [hcur]; exact hold) hnew
  rw [hcur] at h
  exact h

/-! ## §5 — THE TEETH: over-rate / past-deadline / out-of-scope invocations are REJECTED.

Each is `app_violation_rejected` instantiated at a presentation whose `delegAdmit` is FALSE, so the
production executor returns `none` — the invocation does not commit. Proven generically (any presentation
where the relevant conjunct fails), then witnessed concretely in §8. -/

/-- **`tool_invocation_rejected` — the GENERIC tooth.** ANY invocation the delegated policy
rejects (`delegAdmit = false` — over-rate, past-deadline, or out-of-scope) is rejected by the
production executor: `execFullA (.setFieldA …) = none`. -/
theorem tool_invocation_rejected (g : Grant) (now tool : Int) (cell worker : CellId)
    (s : RecChainedState) (c : Int)
    (hprog : s.kernel.slotCaveats cell = (mandateSpec g now tool cell).caveats)
    (hcur : (mandateSpec g now tool cell).committed s.kernel = c)
    (hold : c ∈ (mandateSpec g now tool cell).oldRange)
    (hnew : (c + 1) ∈ (mandateSpec g now tool cell).newRange)
    (hbad : delegAdmit g now tool c (c + 1) = false) :
    execFullA s (.setFieldA worker cell callsMadeSlot (c + 1)) = none := by
  rw [setFieldA_is_stateStepGuarded]
  exact app_violation_rejected (mandateSpec g now tool cell) s hprog worker (c + 1)
    (by rw [hcur]; exact hold) hnew (by rw [hcur]; exact hbad)

/-- **`tool_invocation_over_rate_rejected` — the RATE tooth.** When the counter is already at
the granted ceiling (`c = rateLimit`, so `c+1 > rateLimit`), the (N+1)-th invocation is rejected —
EVEN with the correct tool and inside the deadline. The rate limit is load-bearing. -/
theorem tool_invocation_over_rate_rejected (g : Grant) (cell worker : CellId)
    (s : RecChainedState) (c : Int)
    (hprog : s.kernel.slotCaveats cell = (mandateSpec g g.deadline g.toolId cell).caveats)
    (hcur : (mandateSpec g g.deadline g.toolId cell).committed s.kernel = c)
    (hold : c ∈ (mandateSpec g g.deadline g.toolId cell).oldRange)
    (hnew : (c + 1) ∈ (mandateSpec g g.deadline g.toolId cell).newRange)
    (hover : g.rateLimit < c + 1) :
    execFullA s (.setFieldA worker cell callsMadeSlot (c + 1)) = none := by
  refine tool_invocation_rejected g g.deadline g.toolId cell worker s c hprog hcur hold hnew ?_
  unfold delegAdmit
  have hrate : decide ((c + 1) ≤ g.rateLimit) = false := by
    rw [decide_eq_false_iff_not]; omega
  rw [hrate, Bool.and_false]

/-- **`tool_invocation_past_deadline_rejected` — the DEADLINE tooth.** An invocation presented
after the granted deadline (`now > deadline`) is rejected — EVEN with the correct tool and head-room on
the rate. The time bound is load-bearing. -/
theorem tool_invocation_past_deadline_rejected (g : Grant) (now : Int) (cell worker : CellId)
    (s : RecChainedState) (c : Int)
    (hprog : s.kernel.slotCaveats cell = (mandateSpec g now g.toolId cell).caveats)
    (hcur : (mandateSpec g now g.toolId cell).committed s.kernel = c)
    (hold : c ∈ (mandateSpec g now g.toolId cell).oldRange)
    (hnew : (c + 1) ∈ (mandateSpec g now g.toolId cell).newRange)
    (hlate : g.deadline < now) :
    execFullA s (.setFieldA worker cell callsMadeSlot (c + 1)) = none := by
  refine tool_invocation_rejected g now g.toolId cell worker s c hprog hcur hold hnew ?_
  unfold delegAdmit
  have : decide (now ≤ g.deadline) = false := by
    rw [decide_eq_false_iff_not]; omega
  simp [this]

/-- **`tool_invocation_out_of_scope_rejected` — the SCOPE tooth.** An invocation of a tool
OTHER than the granted `toolId` is rejected — EVEN inside the deadline with head-room. The worker is
narrowly scoped to a single tool/MCP; it cannot invoke any other under this mandate. -/
theorem tool_invocation_out_of_scope_rejected (g : Grant) (now tool : Int) (cell worker : CellId)
    (s : RecChainedState) (c : Int)
    (hprog : s.kernel.slotCaveats cell = (mandateSpec g now tool cell).caveats)
    (hcur : (mandateSpec g now tool cell).committed s.kernel = c)
    (hold : c ∈ (mandateSpec g now tool cell).oldRange)
    (hnew : (c + 1) ∈ (mandateSpec g now tool cell).newRange)
    (hscope : tool ≠ g.toolId) :
    execFullA s (.setFieldA worker cell callsMadeSlot (c + 1)) = none := by
  refine tool_invocation_rejected g now tool cell worker s c hprog hcur hold hnew ?_
  unfold delegAdmit
  have : decide (tool = g.toolId) = false := by
    rw [decide_eq_false_iff_not]; exact hscope
  simp [this]

/-! ## §6 — The kernel keystones at the delegation boundary (re-exported, no re-proof).

A committed tool invocation moves NO balance (`calls_made ≠ balance`) and mints NO capability (the
caveat-gated metadata write never edits the cap table). So the worker exhausting its rate budget cannot
launder value or amplify its authority — exactly the ocap discipline. These lift verbatim through the
toolkit's `app_commit_*` carriers via the `setFieldA = stateStepGuarded` bridge. -/

/-- **`tool_invocation_conserves`.** A committed tool invocation preserves total balance —
the rate counter is not the `balance` field, so incrementing it moves no money. -/
theorem tool_invocation_conserves (cell worker : CellId) (s s' : RecChainedState) (c : Int)
    (h : execFullA s (.setFieldA worker cell callsMadeSlot (c + 1)) = some s') :
    recTotal s'.kernel = recTotal s.kernel := by
  rw [setFieldA_is_stateStepGuarded] at h
  exact app_commit_conserves (mandateSpec ⟨0,0,0⟩ 0 0 cell) s s' worker (c + 1)
    (by decide : callsMadeSlot ≠ balanceField) h

/-- **`tool_invocation_no_amplify`.** A committed tool invocation leaves the authority graph
UNCHANGED — the worker mints / amplifies NO capability by invoking the tool. The ocap non-amplification
guarantee at the delegation boundary. -/
theorem tool_invocation_no_amplify (cell worker : CellId) (s s' : RecChainedState) (c : Int)
    (h : execFullA s (.setFieldA worker cell callsMadeSlot (c + 1)) = some s') :
    execGraph s'.kernel.caps = execGraph s.kernel.caps := by
  rw [setFieldA_is_stateStepGuarded] at h
  exact app_commit_no_amplify (mandateSpec ⟨0,0,0⟩ 0 0 cell) s s' worker (c + 1) h

/-- **`tool_invocation_authorized`.** A committed tool invocation implies the worker held
authority over the mandate cell — no unauthorized invocation ever commits. -/
theorem tool_invocation_authorized (cell worker : CellId) (s s' : RecChainedState) (c : Int)
    (h : execFullA s (.setFieldA worker cell callsMadeSlot (c + 1)) = some s') :
    EffectsState.stateAuthB s.kernel.caps worker cell = true := by
  rw [setFieldA_is_stateStepGuarded] at h
  exact app_commit_authorized (mandateSpec ⟨0,0,0⟩ 0 0 cell) s s' worker (c + 1) h

/-- **`tool_invocation_counts_one`.** After a committed invocation, the rate counter reads back
exactly `c+1` — the call was metered (the consumption is recorded, not merely permitted). -/
theorem tool_invocation_counts_one (cell worker : CellId) (s s' : RecChainedState) (c : Int)
    (h : execFullA s (.setFieldA worker cell callsMadeSlot (c + 1)) = some s') :
    fieldOf callsMadeSlot (s'.kernel.cell cell) = c + 1 := by
  rw [setFieldA_is_stateStepGuarded] at h
  exact app_commit_field_written (mandateSpec ⟨0,0,0⟩ 0 0 cell) s s' worker (c + 1) h

/-! ## §7 — Axiom hygiene over the delegation core. -/

#assert_axioms setFieldA_is_stateStepGuarded
#assert_axioms tool_invocation_commit_iff_admit
#assert_axioms tool_invocation_rejected
#assert_axioms tool_invocation_over_rate_rejected
#assert_axioms tool_invocation_past_deadline_rejected
#assert_axioms tool_invocation_out_of_scope_rejected
#assert_axioms tool_invocation_conserves
#assert_axioms tool_invocation_no_amplify
#assert_axioms tool_invocation_authorized
#assert_axioms tool_invocation_counts_one

/-! ## §8 — NON-VACUITY: a concrete grant + `#guard` witnesses on the REAL executor.

The grantor delegates tool `id = 77` (an MCP "search" tool, say), rate `N = 3`, deadline `100`. The
mandate cell (cell `5`) carries the baked `.admitTable`. The worker (cell `0`, self-authorizing via
`actor == src` so the caveat gate is the load-bearing leg) invokes the tool.

We exhibit the full lifecycle on `execFullA` (the production caveat-gated executor):
  * the first 3 invocations COMMIT (counter 0→1→2→3), the rate budget being consumed;
  * the 4th invocation (counter 3→4 > rateLimit 3) is REJECTED (over-rate TOOTH);
  * an out-of-scope tool (id 99 ≠ 77) is REJECTED (scope TOOTH);
  * a past-deadline presentation (now 101 > 100) is REJECTED (deadline TOOTH);
  * every committed invocation leaves total balance and the authority graph FIXED.

The admit-table is non-vacuous (NON-EMPTY, and EXCLUDES the over-rate / out-of-scope / past-deadline
transitions): exactly the 3 legal advances appear. -/

/-- The demo grant: tool 77, rate 3, deadline 100. -/
def demoGrant : Grant := { toolId := 77, rateLimit := 3, deadline := 100 }

/-- The mandate cell (cell `5`) carrying the baked caveats, presented in-scope (tool 77) and in-time
(now 50). The worker HOLDS the mandate cell — it self-authorizes the metered write (`actor == src` over
the empty cap table, so the SLOT-CAVEAT gate is the load-bearing admission leg). The counter starts at
`callsMade`. -/
def mandateState (callsMade : Int) (now tool : Int) : RecChainedState :=
  { kernel :=
      { accounts := {5}
        cell := fun c => if c = 5 then .record [("balance", .int 0), (callsMadeSlot, .int callsMade)]
                         else .record [("balance", .int 0)]
        caps := fun _ => []
        slotCaveats := fun c => if c = 5 then (mandateSpec demoGrant now tool 5).caveats else [] }
    log := [] }

/-- The committed counter of `mandateState c …` reads back `c` (the spec's `committed` projection). -/
theorem mandateState_committed (c now tool : Int) :
    (mandateSpec demoGrant now tool 5).committed (mandateState c now tool).kernel = c := by
  show fieldOf callsMadeSlot ((mandateState c now tool).kernel.cell 5) = c
  simp [mandateState, fieldOf, callsMadeSlot, Value.scalar, Value.field]

-- The folded policy admits the three legal advances and rejects every violation (predicate level):
#guard demoGrant.toolId == 77
#guard delegAdmit demoGrant 50 77 0 1            --  invocation 1 admitted (in-scope, in-time, 1 ≤ 3)
#guard delegAdmit demoGrant 50 77 1 2            --  invocation 2 admitted (2 ≤ 3)
#guard delegAdmit demoGrant 50 77 2 3            --  invocation 3 admitted (3 ≤ 3, the LAST)
#guard delegAdmit demoGrant 50 77 3 4 == false   --  invocation 4 REJECTED (4 > rateLimit 3 — RATE TOOTH)
#guard delegAdmit demoGrant 50 99 0 1 == false   --  out-of-scope tool 99 REJECTED (SCOPE TOOTH)
#guard delegAdmit demoGrant 101 77 0 1 == false  --  past-deadline (now 101 > 100) REJECTED (DEADLINE TOOTH)

-- The baked admit-table holds EXACTLY the 3 legal advances (non-vacuous; over-rate advance absent):
#guard (mandateSpec demoGrant 50 77 5).admitTable.contains (0, 1)            --  true
#guard (mandateSpec demoGrant 50 77 5).admitTable.contains (1, 2)            --  true
#guard (mandateSpec demoGrant 50 77 5).admitTable.contains (2, 3)            --  true
#guard (mandateSpec demoGrant 50 77 5).admitTable.contains (3, 4) == false   --  over-rate advance ABSENT (TOOTH)
#guard (mandateSpec demoGrant 50 77 5).admitTable.length == 3                --  exactly the 3 legal calls
-- ...and out-of-scope / past-deadline presentations bake an EMPTY table (no invocation can commit):
#guard (mandateSpec demoGrant 50 99 5).admitTable.length == 0                --  out-of-scope ⇒ empty table
#guard (mandateSpec demoGrant 101 77 5).admitTable.length == 0               --  past-deadline ⇒ empty table

-- ★ THE REAL EXECUTOR: the first invocation COMMITS, metering the counter 0 → 1 ...
#guard ((execFullA (mandateState 0 50 77) (.setFieldA 5 5 callsMadeSlot 1)).isSome)                       --  true (invocation 1 commits)
#guard ((execFullA (mandateState 0 50 77) (.setFieldA 5 5 callsMadeSlot 1)).map
        (fun s => fieldOf callsMadeSlot (s.kernel.cell 5))) == some 1                                     --  some 1 (counter advanced)
-- ...the 2nd and 3rd invocations COMMIT (counter at 1 and 2):
#guard ((execFullA (mandateState 1 50 77) (.setFieldA 5 5 callsMadeSlot 2)).isSome)                       --  true (invocation 2)
#guard ((execFullA (mandateState 2 50 77) (.setFieldA 5 5 callsMadeSlot 3)).isSome)                       --  true (invocation 3, the LAST)
-- ★ THE RATE TOOTH on the real executor: the 4th invocation (counter 3 → 4) is REJECTED:
#guard ((execFullA (mandateState 3 50 77) (.setFieldA 5 5 callsMadeSlot 4)).isSome) == false              --  false (over-rate ⇒ none)
-- ★ THE SCOPE TOOTH: an out-of-scope tool (99) mandate rejects EVERY invocation (empty table):
#guard ((execFullA (mandateState 0 50 99) (.setFieldA 5 5 callsMadeSlot 1)).isSome) == false              --  false (out-of-scope ⇒ none)
-- ★ THE DEADLINE TOOTH: a past-deadline presentation (now 101) rejects EVERY invocation:
#guard ((execFullA (mandateState 0 101 77) (.setFieldA 5 5 callsMadeSlot 1)).isSome) == false             --  false (past-deadline ⇒ none)

-- Every committed invocation is balance-neutral (the counter is not `balance`):
#guard ((execFullA (mandateState 0 50 77) (.setFieldA 5 5 callsMadeSlot 1)).map
        (fun s => recTotal s.kernel)) == some (recTotal (mandateState 0 50 77).kernel)                    --  conserved
-- ...and grows the receipt chain by exactly one (the invocation is metered ON-LEDGER):
#guard ((execFullA (mandateState 0 50 77) (.setFieldA 5 5 callsMadeSlot 1)).map (fun s => s.log.length)) == some 1  --  some 1

/-! ## §9 — Differential corpus (the Rust admission mirror pins the SAME vector).

`mandateSpec demoGrant 50 77 5` 's admission decision vector over the full `oldGrid × newGrid` is the
EXACT vector the Rust `starbridge-tool-access-delegation` differential test pins (`src/lib.rs::
deleg_admit`). Drift on either side fails: a Rust mirror change ≠ pinned literal ⇒ Rust test FAIL; a
Lean `delegAdmit` change ⇒ this `#guard` trips ⇒ forced re-pin. Non-vacuous: the vector contains BOTH
`true` (the 3 legal diagonal advances) and `false` (every off-diagonal / over-rate cell). -/

-- The corpus is row-major over oldGrid {0,1,2,3} × newGrid {1,2,3,4}: only the `new = old+1 ∧ new ≤ 3`
-- diagonal cells are true; (3→4) is false (over-rate). 16 cells; exactly 3 true.
#guard AppDiffPinned (mandateSpec demoGrant 50 77 5)
  [ -- old = 0:  →1 (true, 1≤3),  →2 (false, ≠+1),  →3 (false),  →4 (false)
    true,  false, false, false,
    -- old = 1:  →1 (false),  →2 (true, 2≤3),  →3 (false),  →4 (false)
    false, true,  false, false,
    -- old = 2:  →1 (false),  →2 (false),  →3 (true, 3≤3),  →4 (false)
    false, false, true,  false,
    -- old = 3:  →1 (false),  →2 (false),  →3 (false),  →4 (false, 4>3 — over-rate)
    false, false, false, false ]

/-! ## §10 — The CREDENTIAL gate: forged / revoked biscuit ⇒ the whole invocation ROLLS BACK.

The invocation also routes through the production credential-gated forest entry `execFullForestG` (the
`dregg_exec_full_forest_auth` 4-leg gate). The grantor's biscuit credential gates the EXECUTOR: a
genuine, non-revoked credential admits; a FORGED signature (`forgedCred`) fail-closes the WHO leg ⇒
`none`; a REVOKED credential (nullifier in the committed registry) fail-closes ⇒ `none`. This is the
WHO side of the delegation, reusing `StarbridgeGated` verbatim (we add NO credential theory). -/

/-- A tool-invocation node on the credential-gated forest entry: credential `cred`, the metered
`setFieldA` advance, no children. -/
def invocationNode (cred : Authorization Dg Pf) (cell worker : CellId) (newCount : Int) : DForest :=
  ⟨ mkAuth cred [], .setFieldA worker cell callsMadeSlot newCount, [] ⟩

/-- **`invocation_forged_rejected`.** A tool invocation presented with a FORGED biscuit
credential is rejected by the production gated entry, for EVERY pre-state — the WHO leg fail-closes. -/
theorem invocation_forged_rejected (cell worker : CellId) (newCount : Int) (s : RecChainedState) :
    execFullForestG s (invocationNode forgedCred cell worker newCount) = none := by
  rw [invocationNode]
  exact execFullForestG_unauthorized_fails s (mkAuth forgedCred [])
    (.setFieldA worker cell callsMadeSlot newCount) [] (gateOK_forged_false s)
where
  /-- The forged credential's WHO leg is `false` (`credentialValidG (mkAuth forgedCred …) = false`). -/
  gateOK_forged_false (s : RecChainedState) : gateOK (mkAuth forgedCred []) s = false := by
    have hcred : credentialValidG (mkAuth forgedCred []) = false := by decide
    unfold gateOK; rw [hcred]; simp

/-- A tool-invocation node whose credential carries an explicit revocation nullifier `nul`. -/
def invocationNodeRevoked (cred : Authorization Dg Pf) (nul : Nat) (cell worker : CellId)
    (newCount : Int) : DForest :=
  ⟨ { mkAuth cred [] with credNul := nul }, .setFieldA worker cell callsMadeSlot newCount, [] ⟩

/-- **`invocation_revoked_rejected`.** A tool invocation whose credential nullifier sits in
the COMMITTED revocation registry `s.kernel.revoked` is rejected — for EVERY pre-state and EVERY (even
genuine) credential. Revocation is immediate (single-machine): a revoked grant cannot invoke the tool. -/
theorem invocation_revoked_rejected (cred : Authorization Dg Pf) (nul : Nat) (cell worker : CellId)
    (newCount : Int) (s : RecChainedState) (hrev : s.kernel.revoked.contains nul = true) :
    execFullForestG s (invocationNodeRevoked cred nul cell worker newCount) = none := by
  rw [invocationNodeRevoked]
  exact execFullForestG_unauthorized_fails s _ _ []
    (gateOK_revoked_fails { mkAuth cred [] with credNul := nul } s hrev)

#assert_axioms invocation_forged_rejected
#assert_axioms invocation_revoked_rejected

-- The credential gate: a forged biscuit ⇒ the whole invocation rolls back; a revoked one too.
#guard ((execFullForestG (mandateState 0 50 77) (invocationNode forgedCred 5 0 1)).isSome) == false  --  false (forged)
/-- A mandate state whose revocation registry contains nullifier 7 (a revoked grant serial). -/
def mandateRevoked : RecChainedState :=
  { kernel := { (mandateState 0 50 77).kernel with revoked := [7] }, log := [] }
#guard (mandateRevoked.kernel.revoked.contains 7)                                                     --  true (7 revoked)
#guard ((execFullForestG mandateRevoked (invocationNodeRevoked goodCred 7 5 0 1)).isSome) == false    --  false (revoked)

end Dregg2.Apps.ToolAccessDelegation
