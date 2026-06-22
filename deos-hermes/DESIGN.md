# deos-hermes — Hermes as a confined deos agent

Hermes (Nous Research's self-improving agent, `~/pug/hermes-agent`) is a real,
capable tool-calling agent. **deos-hermes** integrates it as a *confined* deos
agent: every Hermes tool-call becomes a cap-gated, metered, **receipted** dregg
turn on the verified executor — or an in-band refusal Hermes sees. This is the
ADOS thesis (*a turn is the exercise of an attenuable proof-carrying token over
owned state, leaving a verifiable receipt*) realized with a real agent, so
Hermes can assist deos development without being trusted.

The enforcement is entirely the **proven** `ToolGateway` (`sdk/src/tool_gateway.rs`,
mirroring `metatheory/Dregg2/Apps/ToolAccessDelegation.lean`). This crate builds
no new policy and no new crypto — only the ACP↔gate seam.

## 1. How Hermes exposes itself over ACP

Hermes ships an ACP (Agent Client Protocol) adapter at
`~/pug/hermes-agent/acp_adapter`. ACP is a JSON-RPC stdio protocol (the one Zed
speaks to external agents). The shape relevant to confinement:

- **Entry** (`acp_adapter/entry.py`): `python -m acp_adapter.entry` / `hermes acp`
  runs `acp.run_agent(HermesACPAgent(), use_unstable_protocol=True)` over stdio.
  stdout is reserved for JSON-RPC frames; logging goes to stderr.
- **Sessions** (`acp_adapter/session.py`): each ACP session maps to a Hermes
  `AIAgent` instance, persisted to `~/.hermes/state.db`. `session/new`,
  `load_session`, `resume_session`, `fork_session`, `list_sessions`.
- **Prompt → stream** (`acp_adapter/server.py::prompt`): the editor sends
  `session/prompt`; Hermes runs its agent loop in a worker thread and streams
  back `session/update` notifications — agent message text, thoughts, plan
  updates, and **tool-call lifecycle** events.
- **Tool-call lifecycle** (`acp_adapter/events.py`, `tools.py`): when Hermes
  starts a tool, `make_tool_progress_cb` emits a `ToolCallStart`
  (`build_tool_start` → `tool_call_id`, `name`, `kind`, `raw_input`/args,
  `locations`); `make_step_cb` emits `ToolCallComplete` with the result. Each
  Hermes tool classifies into an ACP **kind** via `tools.py::TOOL_KIND_MAP` /
  `get_tool_kind`: `read | edit | execute | fetch | search | other`.
- **Permission gate** (`acp_adapter/permissions.py`): the load-bearing
  interception point. Before a *dangerous* tool-call runs, Hermes calls
  `conn.request_permission(session_id, tool_call=<ToolCallUpdate>, options=[…])`
  — the ACP **client** decides allow/deny and returns an `AllowedOutcome`
  (`option_id`) or a rejection. `_OPTION_ID_TO_HERMES` maps the option id back
  to Hermes's `once | session | always | deny`. **This is exactly the seam where
  deos substitutes the `ToolGateway` for a human allow/deny prompt.**

So ACP already gives us (a) a structured description of every tool-call
(`tool_call_id`, `name`, `kind`, `raw_input`) and (b) a request/response gate
(`request_permission` → `AllowedOutcome`) deos can answer with the gateway's
verdict.

## 2. The bridge design

```
  Hermes process (hermes acp, stdio JSON-RPC)
        │  session/update tool_call  +  session/request_permission
        ▼
  deos-side ACP CLIENT  ──parse──▶  acp::ToolCallRequest { session, id, name, kind, args }
        │
        ▼
  bridge::HermesGateway
        │  kind ─▶ grant_registry::GrantRegistry  (deos's per-kind ToolGrant: scope+rate+deadline)
        │  lazily ToolGateway::admit(runtime, root_token, grant)   ← cap-gated worker, verified executor
        ▼
  ToolGateway::invoke(tool_id, now, work)         ← the PROVEN delegAdmit gate
        │
        ├─ ADMITTED → metered turn COMMITS  → ToolReceipt(turn_hash) → PermissionOutcome::Allow
        └─ REFUSED  → no turn, no spend     → GatewayRefusal          → PermissionOutcome::Reject(reason)
        │
        ▼
  deos-side ACP CLIENT  ──reply──▶  AllowedOutcome{allow_once} | deny   (back to Hermes)
```

- **Per-tool grant.** deos is the GRANTOR: it pins a `ToolGrant` (SCOPE ∧
  DEADLINE ∧ RATE) per Hermes `ToolKind`. `grant_registry::GrantRegistry`
  expresses the standard confinement — tight rate ceilings on the dangerous
  classes (`Execute` 20, `Edit` 30), generous on read-only (`Read` 200,
  `Search` 100), `Fetch` 50, and the tightest default `Other` 10. An unknown
  tool falls into `Other`: **fail-closed by classification.** Each kind has a
  distinct `tool_id` (in-band scope key) and a distinct `tool_method` (the
  executor verb the worker's biscuit credential covers).
- **One worker per kind.** `HermesGateway` lazily `admit`s a cap-gated
  `ToolGateway` worker per kind on first use, each metering its own `calls_made`
  counter under its own mandate. deos can deny a whole class (rate 0) without
  touching another.
- **Both polarities are real.** An admitted call commits a genuine receipted
  turn (`turn_hash` is the receipt id deos returns to Hermes / the editor).
  A refused call is an in-band `Reject` naming the leg that bit (scope /
  deadline / rate), and submits NO turn — the anti-ghost tooth.

## 3. The built first slice (this crate)

`cd deos-hermes && cargo build && cargo test` (and `cargo run` for the demo).

- `src/acp.rs` — the ACP wire subset: `ToolKind` (byte-faithful to Hermes's
  `TOOL_KIND_MAP`), `ToolCallRequest`, `PermissionOutcome`.
- `src/grant_registry.rs` — `GrantRegistry`: deos's per-kind `ToolGrant`.
- `src/bridge.rs` — `HermesGateway::admit_call`: the seam.
- `tests/seam.rs` — both-polarity, on the **real verified executor**: a
  Hermes-style tool-call commits with a real receipt; over-rate and
  past-deadline calls are refused in-band.
- `src/main.rs` — a CLI driving a mocked ACP source of representative Hermes
  tool-calls through the gateway, printing the live verdicts.

**REAL in the slice:** the entire `ToolGateway` path (`admit` + `invoke` on the
verified Lean executor, genuine `TurnReceipt`s). **STUB in the slice:** the ACP
*transport* — a `ToolCallRequest` is fed in directly rather than parsed from a
live `hermes acp` subprocess. The point of the first slice is the load-bearing
tool-call→gated-turn seam, grounded in the real gateway; the transport is
roadmap (§4).

## 4. Roadmap — to a fully confined deos-hermes agent

1. **The ACP-client ↔ Hermes-process wiring.** Spawn `hermes acp` as a
   subprocess (`uvx hermes-agent[acp]==… hermes-acp`, per
   `acp_registry/agent.json`), speak JSON-RPC over its stdio, and implement the
   ACP **client** half: drive `session/new` + `session/prompt`, consume
   `session/update`, and — the seam — answer `session/request_permission` by
   calling `HermesGateway::admit_call` and replying with the mapped
   `AllowedOutcome`/deny. Adopt a Rust ACP crate (`agent-client-protocol`, the
   one Zed/`acp_thread` uses) or model the minimal JSON-RPC by hand. Map the ACP
   `tool_call` payload's `name`/`kind`/`raw_input` straight into
   `ToolCallRequest`.
2. **Tool work into the turn.** Today `admit_call` takes the tool's effects as
   an explicit `work: Vec<Effect>` (empty in the slice = a pure metered
   admission). Wire the real tool's side-effects (a file write, a shell spawn)
   as effects/intents that ride the SAME metered turn, so the receipt witnesses
   the actual work, not just the meter. (`granted_call_carries_tool_work_payload`
   in the SDK e2e shows the shape.)
3. **Richer per-tool grants.** Move from per-*kind* to per-*tool* grants where
   it matters (e.g. allow `read_file` but pin `terminal` to an allowlist of
   commands via the cell program), and surface a deos UI to set/inspect a
   session's mandate (the "agent dock"). Tie the `deadline` to the dregg clock /
   block height rather than a demo scalar.
4. **The sandbox-PD confinement (firmament/seL4).** Run the Hermes process in a
   confined sandbox protection-domain (the host-PD being built — see
   `project-firmament-sel4-boots`): its filesystem via `FirmamentFs` (a
   cap-scoped VFS), its network via an explicit net-cap. Then the `ToolGateway`
   meters/authorizes the *intent* of each tool-call AND the PD physically can't
   reach anything outside its caps — defense in depth: the gate is the
   authority face, the PD is the ambient-authority face.
5. **The chat/agent dock surface.** Surface the confined Hermes as a deos agent
   dock (starbridge-v2 / the moldable inspector epoch): a chat pane streaming
   Hermes's `session/update` output, a live view of each tool-call's
   receipt/refusal, and the mandate inspector. Hermes assists deos development
   from inside deos, every action receipted.
