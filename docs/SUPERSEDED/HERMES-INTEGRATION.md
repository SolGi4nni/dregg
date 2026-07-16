# Hermes ↔ dregg Integration — Scout + One-Seam Weld Plan

Hermes Agent (Nous Research, MIT) is a mature, multi-platform self-improving
agent loop. dregg does **not** rebuild that loop. Per the integrator thesis
(`project-dregg-integrators-one-seam`): an agent is an intricate loop; dregg
closes the enforcement gap at exactly **one seam** — the tool-call → verdict →
receipt boundary. Every tool-call Hermes makes becomes a cap-gated dregg
**turn**: authorized by a held capability, conservation-checked, refused
in-band if it exceeds the agent's mandate, and leaving a verifiable receipt the
tool-result carries. The running loop then renders as a cap-gated
agent-activity **Surface** cell in starbridge — the ADOS keystone.

This document is the plan. Nothing is vendored or wired yet.

---

## 1. Hermes architecture — and the exact tool-call seam

Hermes runs one agent core (`run_agent.py`, the `AIAgent` class) across CLI,
~20 messaging gateways, a TUI, an ACP adapter, and an Electron desktop. The
loop lives in `agent/conversation_loop.py:run_conversation` — model call →
parse `assistant_message.tool_calls` → dispatch tools → append results →
repeat. It learns across sessions (memory + skills), delegates to subagents,
and runs scheduled jobs.

**THE TOOL-CALL EXECUTION SEAM (the one place we interpose):**

There is a single, clean dispatch funnel. From outermost to the actual call:

1. `agent/tool_executor.py:execute_tool_calls_concurrent` (and the
   `…_sequential` twin) — the batch driver: takes
   `assistant_message.tool_calls`, parses args, runs guardrails, and calls
   each tool. **The per-tool invocation is `agent._invoke_tool(...)` at
   `tool_executor.py:494`.**
2. `run_agent.py:5225 AIAgent._invoke_tool` → forwards to
   `agent/agent_runtime_helpers.py:invoke_tool`.
3. `model_tools.py:876 handle_function_call` — *the* dispatcher. After the
   Tool-Search bridge unwrap and the tool-request middleware, it reaches the
   registry:
   **`registry.dispatch(function_name, function_args, …)` at `model_tools.py:1116`**
   (wrapped by `_run_agent_tool_execution_middleware`).
4. `tools/registry.py:ToolRegistry.dispatch` looks up a `ToolEntry`
   (`tools/registry.py:77`, slots `name, toolset, schema, handler, check_fn`)
   and calls its `handler`.

**The single narrowest chokepoint is `ToolRegistry.dispatch`** — every model
tool, every Tool-Search-bridged tool, and every plugin tool flows through it.
The cleanest *non-invasive* interposition point is one layer up, the existing
**middleware chain** Hermes already runs around dispatch:

- `agent/tool_executor.py:184 _apply_tool_request_middleware_for_agent` →
  `hermes_cli.middleware.apply_tool_request_middleware` (can rewrite/inspect
  args *before* execution).
- `agent/tool_executor.py:211 _run_agent_tool_execution_middleware` →
  `hermes_cli.middleware.run_tool_execution_middleware(name, args, _execute,
  …)` — a **wrap-around** middleware that receives the `execute` continuation.
  This is the ideal hook: a dregg middleware can authorize *before* calling
  `_execute`, and **refuse in-band by not calling it** (returning a denial
  string), with no core edits.

Hermes already has an in-band refusal precedent: `tool_guardrails.py` blocks a
tool call and synthesizes a tool-result message (`make_tool_result_message`,
`tool_dispatch_helpers.py:320`). The dregg verdict rides the same rail.

**Supporting subsystems we map onto dregg nouns:**

- **Toolsets** — `toolsets.py`: `TOOLSETS` dict, each entry
  `{description, tools:[...], includes:[...]}`; `resolve_toolset(name)` flattens
  composition. A `ToolEntry.toolset` field tags every tool with its toolset.
  *A toolset is a capability domain; a tool is an attenuated cap within it.*
- **Subagent delegation** — `tools/delegate_tool.py:delegate_task(goal,
  context, toolsets=[...], role, max_iterations, …)`, dispatched from
  `run_agent.py:5193 _dispatch_delegate_task`. A child `AIAgent` runs with a
  **restricted toolset list** — Hermes already attenuates by toolset here.
- **Memory / skills store** — `agent/memory_manager.py:313 MemoryManager`
  (agent-curated memory, FTS5 session search via `session_search`); skills are
  markdown docs under skill dirs (`agent/skill_utils.py`), CRUD via the
  `skill_manage` tool. The learning loop curates both.
- **Model-call boundary** — provider adapters (`agent/anthropic_adapter.py`,
  `chat_completion_helpers.py`, etc.); orthogonal to the tool seam and **left
  untouched** (prompt caching is sacred — AGENTS.md).

---

## 2. The one-seam weld — dregg at the tool-call boundary

### 2.1 The mapping (toolset = cap domain, tool = attenuated cap)

| Hermes | dregg |
|---|---|
| A session / agent | an agent **cell** (`CellId`) with a `HeldToken` mandate |
| A toolset (`TOOLSETS[name]`) | a **capability domain** — a granted verb-family on a target cell |
| A tool (`ToolEntry.name`) | an **attenuated cap** — one method verb (`action::symbol(tool_name)`) inside that domain |
| A tool-call | a **dregg turn**: one `Action` carrying `Effect`s, `Authorization::Token` (the agent's biscuit) |
| Tool refused (out-of-mandate) | executor returns `TokenInsufficientCapability` → in-band denial string |
| Tool succeeded | a `TurnReceipt` (the proof of execution) attached to the tool-result |
| `delegate_task(toolsets=[…])` | `AgentRuntime::spawn_sub_agent_scoped(restrictions, token, allowed_methods)` |

The verb a tool-call authorizes is the tool name as a method symbol; the
toolset is the service grant. This lines up precisely with how dregg already
mints sub-agent grants: `sdk/src/runtime.rs` issues one
`service(cell_hex, hex(symbol(method)))` grant *per allowed method* (the
comment block at `runtime.rs:146`). A toolset → a set of such grants.

### 2.2 The turn each tool-call becomes

For tool-call `(name, args)` the dregg middleware builds a turn through
`AgentRuntime` (`sdk/src/runtime.rs:212`):

- **Authorization** — `Authorization::Token` (`turn/src/action.rs:431`)
  carrying the agent cell's biscuit, scoped to the toolset's method verbs. The
  executor's `authorize.rs` path (`turn/src/executor/authorize.rs:206`) checks
  the token grants `service(agent_cell, symbol(name))`; if not →
  `TurnError::InvalidAuthorization` / `TokenInsufficientCapability`. **This is
  the anti-ghost tooth: the EXECUTOR refuses, not an out-of-band check**
  (`spawn_sub_agent_scoped` docstring, `runtime.rs:846`).
- **Effects** — most tool-calls are *witnessed* rather than state-mutating:
  the minimal faithful effect is `EmitEvent { cell: agent_cell, event }`
  (`turn/src/action.rs:972`) recording `(tool_name, args_hash, result_hash)`,
  so the receipt binds the tool-call into the chain without forging ledger
  state. Tools with genuine economic meaning (a metered/paid tool, a budget
  draw) additionally carry `Transfer` (`action.rs:958`) against a
  `SwarmBudget` cell. Conservation (Σδ=0) is checked for free.
- **Receipt** — `AgentRuntime::execute_turn` returns a `TurnReceipt`; wrapped
  as `sdk/src/receipt.rs:96 Receipt` (optionally `attach_proof` for a
  light-client `FullTurnProof`). The receipt hash chains via
  `previous_receipt_hash` (`turn/src/builder.rs:267`) — the agent's whole
  activity is one verifiable receipt chain.

The receipt (hash + height + optional proof handle) is serialized into the
tool-result string Hermes returns to the model, so the transcript itself
carries provenance. (Compare `acp_adapter/provenance.py` — Hermes already has
a provenance notion to extend.)

### 2.3 In-band refusal (the anti-ghost tooth)

A tool-call that exceeds the agent's held caps must be **refused in-band**, the
way `tool_guardrails` already blocks: the dregg execution-middleware calls
`AgentRuntime::execute_turn`; on `SdkError::…TokenInsufficientCapability` it
**does not call `_execute`** and instead returns a denial via
`make_tool_result_message(name, "[dregg: refused — '<tool>' exceeds this
agent's mandate; held caps: …]", tool_call_id)`. The model sees the refusal as
a normal tool-result and adapts. No faked success, ever — matching the
starbridge invariant "a refused action is shown as REFUSED, never faked"
(`starbridge-v2/src/agent.rs:83`, test
`a_refused_action_is_shown_as_refused_never_faked` in `starbridge-v2/src/agent.rs`).

### 2.4 The adapter (Python ↔ dregg bridge)

Three transport options, in increasing weld depth. **Phase 1 picks (a).**

- **(a) Local dregg gateway over HTTP — RECOMMENDED FIRST.** dregg already
  speaks this: `sdk/src/remote.rs:140 RemoteRuntime::connect(base_url, …)` →
  `POST /turns/submit` of a signed turn envelope (`remote.rs:313
  submit_envelope`), returning a receipt. A small Rust binary
  (`hermes/dregg-gateway/`, reusing `AgentRuntime` + the node ingress) exposes
  `POST /authorize_tool {agent, toolset, tool, args_hash}` → `{verdict,
  receipt}`. The Python middleware is a thin `requests`/`httpx` client. Zero
  FFI, zero build coupling; the gateway can run as a sidecar (mirrors the
  existing devnet `dregg-gateway` systemd unit). **Highest leverage, lowest
  risk.**
- **(b) PyO3 FFI** — bind `AgentRuntime` directly into a `dregg_py` extension
  module. Tighter (no network hop, can hold the receipt chain in-process) but
  couples the Python build to a Rust toolchain (`maturin`). A Phase-2
  hardening once (a) proves the seam.
- **(c) WASM** — `wasm/src/runtime.rs` already exposes a runtime binding; a
  `wasmtime`-hosted module is portable but the slowest to stand up. Park.

The bridge is registered as a Hermes **execution middleware**
(`hermes_cli.middleware.register_tool_execution_middleware`, the consumer of
`run_tool_execution_middleware`) — *not* a core edit. Per the Footprint Ladder
(AGENTS.md), this is rung 3/4 (service-gated middleware / plugin), the merge-
friendly path: gated on a `dregg` config block, invisible when unconfigured.

---

## 3. The starbridge surface — the loop as a cap-gated activity cell

This is already built on the dregg side and is the cleanest landing.
`starbridge-v2/src/agent.rs` defines exactly the model we need, fed purely from
the `World` (the ledger):

- `AgentActivity::build(world, agent, max_actions)` (`agent.rs:142`) reads the
  agent cell's c-list and renders:
  - **THE HELD MANDATE** — `MandateEdge` per capability edge (`agent.rs:54`:
    target, slot, rights, faceted, expires_at) = the agent's attenuated reach
    (its granted toolsets).
  - **RECENT ACTIONS** — `AgentAction` per committed/refused turn
    (`agent.rs:79`), `committed: false` flagged for refusals — the receipts of
    every tool-call.
  - **AUTHORIZATIONS** — `build_authorizations` (`agent.rs`): the legible
    "which verbs does this mandate admit" view.
- `AgentSurface` (`agent.rs:404`) binds the agent cell to a compositor
  `SurfaceId` — the agent-activity panel **is** a `Capability{Surface(cell)}`,
  a cap-confined window the shell composites.

**Wiring:** each Hermes session's agent cell drives one `AgentSurface`. The
dregg-gateway from §2.4, on each authorized tool-call, commits the turn into
the same `World` the starbridge cockpit reads; `AgentActivity::build` then
re-renders live (held mandate · the stream of cap-gated turns · their receipts
· refusals shown as refused). A Hermes `delegate_task` fan-out maps onto
`starbridge-v2/src/swarm.rs:258 SwarmMember` — each subagent is a
cap-confined `Surface` cell with its own `SurfaceCapability` (`swarm.rs:275`),
its `BudgetMeter`/`SwarmBudget` (`swarm.rs:193`) metering its computron draw,
and `NotifyEdge` inbox for peer coordination (`swarm.rs:132`,
`coordination.rs`). The operator sees the swarm's provable coordination — and
"can an operator be fooled about what two agents coordinated? No" (`swarm.rs`
header) holds because the activity is on-ledger truth.

No new starbridge types are required for Phase 1 — only a feed from the
gateway into the `World` that `AgentActivity` already reads.

---

## 4. The vendoring plan — fork, vendor, make it ours

### Where in the repo

A new **top-level `hermes/` directory**, vendored as a **git subtree** (not a
submodule — subtree keeps the tree in-repo, editable, and survives the AGPL
full-history posture; submodules would dangle). The breadstuffs repo is
AGPL-3.0-or-later; Hermes is MIT — **MIT is one-way compatible into AGPL**, so
the combined work ships AGPL while we preserve Hermes' `LICENSE` and copyright
notice verbatim inside `hermes/` (the MIT terms require only that the notice
travel with the copies — satisfied by keeping `hermes/LICENSE`). Add a short
`hermes/NOTICE.md` attributing Nous Research and stating the dregg fork intent.

Layout:
```
hermes/                      # vendored subtree (Hermes core)
  agent/ run_agent.py model_tools.py toolsets.py tools/  # KEEP — the loop
  LICENSE NOTICE.md
hermes-dregg/                # OUR code (not vendored — the weld)
  gateway/   (Rust: AgentRuntime-backed /authorize_tool sidecar)
  middleware/ (Python: the dregg execution-middleware + httpx client)
  dregg_toolset/  (the privileged native toolset — see below)
```

### KEEP vs STRIP

**KEEP (the core we weld onto):**
- `agent/` (the loop, `tool_executor.py`, `agent_runtime_helpers.py`),
  `run_agent.py`, `model_tools.py`, `toolsets.py`, `tools/registry.py` +
  `tools/` handlers, `agent/memory_manager.py` + skills (`agent/skill_utils.py`,
  the learning loop), `tools/delegate_tool.py` (subagent delegation),
  `hermes_cli/middleware.py` (our interposition rail).

**STRIP / defer (not needed for the seam; large surface):**
- The ~20 messaging gateways (`gateway/`, `tui_gateway/`), the TS desktop
  (`apps/`, `ui-tui/`, `web/`, `website/`), `cron/`, most `providers/` beyond
  the one model adapter we test with, `locales/`, `optional-mcps/`,
  `datagen-*`, `batch_runner.py`, `mini_swe_runner.py`. These can re-enter
  later but are dead weight for the weld.

This is a **big Python tree** (~2400 `.py`, a 679KB `cli.py`, a 246KB
`run_agent.py`). Be honest: vendoring + de-bloating is itself multi-day work.
Phase it — vendor the KEEP set first, leave STRIP in place but unbuilt, prune
opportunistically.

### "Make it ours"

1. **The dregg-native toolset is the privileged path.** Add a `dregg` toolset
   to `TOOLSETS` (and a `ToolEntry` with a `check_fn` gating on the dregg
   config) whose tools (`dregg_grant`, `dregg_receipt`, `dregg_inspect`) let
   the agent reason about its *own* mandate, mint attenuated sub-caps, and
   inspect its receipt chain. The agent becomes self-aware of its cap-graph —
   the dregg-native superpower no upstream Hermes has.
2. **Rebrand surface** — the activity feed / cockpit is starbridge's
   (`AgentSurface`), so the *visible* product is dregg/deos, with Hermes as the
   embedded loop engine. Light rename of the CLI entrypoint banner; keep
   internal module names to minimize subtree-merge conflict churn.
3. **The mandate is real, not advisory.** Because the gateway enforces via the
   executor, "make it ours" is not cosmetic — a vendored Hermes running under
   dregg literally *cannot* exceed its granted toolset, and every action it
   takes is light-client-verifiable. That property is the fork's reason to
   exist.

---

## The single highest-leverage first phase

**Stand up the local dregg-gateway sidecar + the Python execution-middleware,
and route ONE toolset through it end-to-end.**

Concretely:
1. Rust: `hermes-dregg/gateway/` — a binary wrapping `AgentRuntime`
   (`sdk/src/runtime.rs`) exposing `POST /authorize_tool {agent, toolset,
   tool, args_hash}` → `{verdict, receipt_hash, height}`. Reuse the existing
   `/turns/submit` envelope path (`sdk/src/remote.rs`). The turn is one
   `Action` with `Authorization::Token` + an `EmitEvent` witnessing the
   tool-call.
2. Python: register a dregg execution-middleware via
   `hermes_cli.middleware.register_tool_execution_middleware`, consumed at
   `agent/tool_executor.py:229 run_tool_execution_middleware`. It calls the
   gateway *before* `_execute`; on a refusal verdict it short-circuits with an
   in-band denial (`make_tool_result_message`), never calling the handler; on
   accept it runs the tool and appends the receipt to the result.
3. Prove the anti-ghost tooth on **one toolset** (e.g. `terminal`): grant the
   agent the `terminal` toolset, show `terminal` runs *with* a receipt, and
   show a `delegate_task`/`browser` call **refused in-band** because the
   mandate doesn't grant it — the executor's `TokenInsufficientCapability`, not
   an out-of-band check.
4. Feed the committed turns into the `World` the starbridge cockpit reads, so
   `AgentActivity::build` renders the live mandate + receipts + the refusal.

This phase touches **zero Hermes core files** (middleware registration only),
proves the load-bearing claim (cap-gated, receipted, refused-in-band), and
lights up the starbridge surface that already exists — the smallest cut that
demonstrates the whole thesis.

— ( ◕‿◕ ) one seam, witnessed.
