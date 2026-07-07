# starbridge-tool-access-delegation

**Verifiable tool / MCP-access delegation** — the object-capability model serving AI delegation.

An AI agent (the **grantor**) hands another agent (the **worker**) a narrowly-attenuated,
rate-limited, time-bounded, revocable capability to invoke a tool / MCP on its behalf. The grantor
never hands over its keys; it mints a **mandate cell** whose slot-caveats are checked **by the verified
executor** on every tool invocation, so the worker can never invoke the tool beyond the granted **rate**,
**scope**, or **deadline** — and the grant can be **revoked**.

This is the Rust surface for the verified Lean app
[`metatheory/Dregg2/Apps/ToolAccessDelegation.lean`](../../metatheory/Dregg2/Apps/ToolAccessDelegation.lean).

## The invariant, proven (not asserted)

The Lean side proves, against `Dregg2.Apps.VerificationToolkit.app_commit_iff_admit`, the headline:

> **`tool_invocation_commit_iff_admit`** — on a mandate cell carrying the delegated caveats, the
> production caveat-gated executor write `execFullA (.setFieldA worker cell "calls_made" (c+1))`
> (definitionally `stateStepGuarded`, `TurnExecutorFull.lean:3794`) **commits iff** the delegated policy
> admits the invocation: `c+1 ≤ rate_limit ∧ now ≤ deadline ∧ presentedTool = tool_id` **and** the
> worker holds authority over the cell. Over the **whole `RecChainedState` post-state** — not an
> aggregate shadow.

…and the teeth, each `app_violation_rejected` instantiated:

| theorem | guarantee |
|---|---|
| `tool_invocation_over_rate_rejected`     | the (N+1)-th invocation (`c+1 > rate_limit`) is rejected `= none` |
| `tool_invocation_past_deadline_rejected` | an invocation presented after `deadline` is rejected `= none` |
| `tool_invocation_out_of_scope_rejected`  | an invocation of any tool ≠ `tool_id` is rejected `= none` |
| `tool_invocation_conserves`              | a committed invocation moves no balance |
| `tool_invocation_no_amplify`             | a committed invocation mints no capability (ocap non-amplification) |
| `invocation_forged_rejected`             | a forged biscuit credential ⇒ the whole gated turn rolls back |
| `invocation_revoked_rejected`            | a revoked credential (nullifier in the committed registry) ⇒ rolls back |

Every theorem is `#assert_axioms`-clean (only `{propext, Classical.choice, Quot.sound}`).

## Two enforcement surfaces, both real, both already in the kernel

1. **Capability attenuation** (WHO may delegate, with WHICH rights) is the agent-mandate theory in
   [`intent/src/agent_mandate.rs`](../../intent/src/agent_mandate.rs) /
   [`metatheory/Dregg2/Agent/Mandate.lean`](../../metatheory/Dregg2/Agent/Mandate.lean):
   `Mandate::sub_delegate` strictly narrows keep/budget/caveat; `materialize_grant = recKDelegateAtten`
   (the `execFullA` delegate-atten arm); `materialize_revoke`. The agent-facing biscuit credential
   gating the executor on the live `execFullForestG` path is `StarbridgeGated.mkAuthToken`
   ([`Dregg2/Exec/GatedForestCfg.lean §A2`](../../metatheory/Dregg2/Exec/GatedForestCfg.lean)). This
   crate **reuses** those surfaces — it does not reimplement them.

2. **Per-invocation consumption budget** (HOW MANY times, UNTIL WHEN, on WHICH tool) is **this crate's**
   contribution: the rate counter, expiry, and tool allowlist, checked on every call as a
   slot-caveat-gated `SetField`.

## The mandate cell

| slot | name | caveat | meaning |
|---|---|---|---|
| 0 | `calls_made` | `Monotonic` + `FieldLte rate_limit` | the rate counter; advances `c → c+1`, never rolls back, never exceeds N |
| 1 | `rate_limit` | `Immutable` | the granted ceiling N, fixed at grant |
| 2 | `deadline`   | `WriteOnce` + `FieldGteHeight` gate | the expiry, set once at grant; invocations past it are refused |
| 3 | `tool_id`    | `Immutable` | the single allowlisted tool / MCP id (the scope) |

`tad_cell_program()` / `tad_factory_descriptor()` install these; `build_grant_action` /
`build_invoke_action` / `build_revoke_action` are the turn builders.

## Differential pinning (anti-drift)

`deleg_admit` mirrors the Lean `delegAdmit` byte-for-byte; `deleg_corpus` enumerates the full
`(old, new)` grid. `tests/lean_differential.rs` pins the **identical** decision vector the Lean
`#guard AppDiffPinned (mandateSpec demoGrant 50 77 5) [...]` pins. Drift on either side fails: a Rust
change ≠ the literal ⇒ test fails; a Lean `delegAdmit` change ⇒ the Lean `#guard` trips at `lake build`.

## Build & test

```
lake build Dregg2.Apps.ToolAccessDelegation          # the verified app (from metatheory/)
cargo test -p starbridge-tool-access-delegation       # the Rust mirror + differential corpus
```
