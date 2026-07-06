# Agent-confinement red-team — the attack matrix

A genuinely adversarial sweep of the confined-agent boundary: the Hermes ACP
seam (`deos-hermes/src/{bridge,grant_registry,tool_effects}.rs`), the proven
`ToolGateway` it rides (`sdk/src/tool_gateway.rs`), the verified executor under
that (`turn/src/executor/`), and the OS-sandboxed firmament host-PD the agent
body runs in (`deos-hermes/src/confined.rs`).

Every attack is a TEST THAT RUNS (`deos-hermes/tests/red_team_*.rs`): each one
ATTEMPTS the escalation through the real path and asserts the refusal, or would
expose the hole. `cd deos-hermes && cargo test` is green — the refusal-tests all
pass, so each named limit HOLDS by running. No hole was found; the one
correction was a too-strong test assertion about *which* hash forms the receipt
chain (the chain links via `receipt_hash()`, not `turn_hash` — the defense was
real, my first assertion checked the wrong field).

The model in one line: **the agent is powerful over its OWN world, every action
is a receipted turn, and it cannot cross to another vessel.**

## The matrix

| # | Attack | Result | Mechanism that stopped it | Severity if it had held |
|---|--------|--------|---------------------------|-------------------------|
| 1 | **Mandate overrun — RATE** (one past the ceiling) | REFUSED | `deleg_admit` rate conjunct `new ≤ rateLimit` (in-band) + the executor `FieldLte`/`Monotonic` cell-program backstop. Boundary tested: calls `1..N` commit, `N+1` refused, no spend. | critical |
| 1 | **Mandate overrun — RATE 0** (whole-tool deny) | REFUSED | `with_grant_for_tool_deny` pins rate 0; first reach has `new=1 > 0` → refused. | critical |
| 1 | **Mandate overrun — DEADLINE** (clock past expiry) | REFUSED | `deleg_admit` deadline conjunct `now ≤ deadline`. Boundary tested: `now==deadline` admits, `now==deadline+1` refused. | critical |
| 1 | **Mandate overrun — SCOPE / unknown tool** | REFUSED (fail-closed) | An unknown tool name classifies to `ToolKind::Other` (rate-10 floor), metered, not an unbounded path. | high |
| 1 | **Cross-mandate budget leak** (exhaust Execute, borrow Fetch) | REFUSED | Each `MandateKey` is its OWN cap-gated worker + own `calls_made`; exhausting one cannot refill another. | high |
| 2 | **Authority amplification — fire a wider verb** (search-scoped worker fires `tool.execute`/`admin`) | REFUSED | The worker's biscuit credential covers EXACTLY `grant.tool_method`, anchored in its own cell's `verification_key`; the EXECUTOR rejects any other verb with `TokenInsufficientCapability`. Attacked *below* the in-band gate via `worker_for_test`. | critical |
| 2 | **Grant self-widening** (raise own rate/deadline through the seam) | REFUSED (no such API) | The `ToolGrant` is immutable after `admit`; the only mutation a call causes is the monotone counter advance. Grant unchanged after exercising the seam. | critical |
| 3 | **Confused deputy — act as another principal** (payload `principal:root`, `run_as:operator`, `uid:0`) | REFUSED (inert) | Every worker turn sets `agent == target == self.cell_id` (`SubAgent::execute_method`); the ACP payload carries no principal field that redirects the signer. The spoofed claim grants nothing — the call is metered on the agent's OWN rate-1 budget and the budget is genuinely exhausted after. | critical |
| 4 | **Replay** (resubmit an identical receipted call) | REFUSED (spends, then refuses) | The rate counter is monotonic and advances on every admitted call, so a replay is never a free repeat; once budget is gone the replay is refused in-band. | high |
| 4 | **Nonce / chain replay** (verbatim turn replay) | DETECTABLE | Each worker turn binds `previous_receipt_hash = receipt_hash()` of its predecessor + advances the cell nonce → distinct, chained receipts; a stale `previous_receipt_hash` is rejected by the executor with `ReceiptChainMismatch`. | high |
| 5 | **Receipt forgery / anti-ghost** (fabricate proof for an effect that didn't run) | REFUSED | A refusal is a VALUE (`PermissionOutcome::Reject`), never a receipt; a refused call yields no receipt id and no counter advance. The `remaining` an Allow reports is exactly `rate_limit − calls_made`, reaching 0 at the last admitted call — no fabricated head-room. | critical |
| 6 | **Sandbox escape — ambient file** (`open(/etc/passwd)` from the PD) | DENIED | macOS Seatbelt / Linux landlock applied after `fork`, before the body (`spawn_pd_confined`); probe verdict bit `OPEN_DENIED`. | critical |
| 6 | **Sandbox escape — ambient network** (`socket(AF_INET)`/connect) | DENIED | Seatbelt `network*` denied / Linux empty net namespace; probe bit `NET_DENIED`. | critical |
| 6 | **Ambient network — OFF the granted provider door** (`connect` to any non-granted host:port when a provider door IS open) | DENIED | macOS: SBPL allows only the one `remote ip "host:port"`; every other remote hits `(deny default)`. Linux: a seccomp `connect`-notification door (`sandbox.rs::provider_door` + `linux` backend) — the jailed body may `socket()` but every `connect()` traps to a trusted supervisor that admits ONLY the granted endpoints (pure `admits` match) and `EPERM`s the rest; the child's net namespace stays empty, so deny-default is structural and any plumbing failure fails closed. Probe bits `EGRESS_NET_GRANTED_OPEN` / `EGRESS_NET_SIBLING_DENIED`. (Linux connect-notify RUNTIME validated on a Linux host/CI; policy+cBPF config unit-tested + cross-builds.) | critical |
| 6 | **Sandbox escape — leaked fd** (hold any fd beyond the Endpoint) | DENIED | Confinement closes every non-granted fd; exactly one non-std fd (the firmament Endpoint) survives; probe bit `ONLY_ENDPOINT_FD`. | critical |
| 6 | **Sandbox escape — exec** | DENIED (by construction) | The confined child has NO exec authority (Seatbelt `process-exec*` / seccomp `execve` denied) — which is why the agent body must BE a Rust ACP peer, not an `execve`'d binary. | critical |
| 7 | **Empowered-but-accountable** (a JS-driven / broad agent action) | ALLOWED + RECEIPTED | The agent SHOULD act broadly over its OWN world — a feature. Every such action still passes the gate (`gateOK`/cap tooth) AND leaves a real `TurnReceipt` → SEE-able and REWIND-able. | (feature) |
| 7 | **Cross-vessel reach — THE EDGE** (forged `SetField`/`EmitEvent` into ANOTHER vessel's cell) | REFUSED | A worker's credential is anchored in its OWN cell; the executor `collect_touched_cells` re-checks every touched cell's authority, so an effect targeting a foreign cell fails. The agent stays fully empowered over its own cell. | critical |
| 7 | **Unbounded executor reachability** (a tool path to a raw executor at root) | NONE EXISTS | Every admitted tool-call terminates in a cap-gated, metered, receipted `ToolGateway` worker; every kind has a finite rate ceiling + deadline. No `HermesGateway` method hands back a root handle. **The Hermes→deos-js binding now EXISTS (`deos-hermes/src/run_js.rs`, behind `js-agent`) and mounts the JS runtime under the AGENT'S `held`, never root — it keeps the invariant, it does not open a root path.** | critical |

## Item 7 — the deos-js / agent-co-pilot angle (the standing invariant)

ember's framing: the agent running JS freely is the operator's co-pilot for a
cockpit too complex for a human alone. That is EXPECTED and GOOD — not an
escalation to prevent. So this surface does not lock the agent's JS down; it
verifies the model is **empowered-but-accountable** and that the one real edge —
cross-vessel isolation — holds.

What the deployed code already enforces (verified by inspection +
`red_team_empowered_accountable.rs`):

- **Accountable.** A deos-js applet `fire` (`deos-js/src/applet.rs`) runs the cap
  tooth `is_attenuation(held, required)` in-band AND commits a real `TurnReceipt`
  appended to an audit tape. The deos-hermes seam likewise turns every tool-call
  into a receipted turn. Every agent action is rewindable.
- **Isolated (the edge).** An applet `fire` writes only to `self.cell`
  (`action.effect_set_field(self.cell, …)`); a confined `ToolGateway` worker's
  effects are authority-checked per touched cell. A forged effect into another
  vessel's cell is refused.
- **No root path.** The `deos_hermes → deos-js` binding is now BUILT
  (`deos-hermes/src/run_js.rs`, "THE HANDS", behind the `js-agent` feature —
  `RunJsTool` EMBEDDED + `RunJsTool::run_attached_on` ATTACHED-to-live-World). It
  keeps exactly the invariant this doc set: it mounts the JS runtime under the
  AGENT'S attenuated cap (the mandate's `held`), NEVER root — the cap tooth in
  `deos_js::Applet::fire` / `AttachedApplet::fire` refuses any over-reach in-band,
  and a JS-driven turn binds the agent's OWN cell (cross-vessel reach blocked).
  The `run_js` tool-call itself is admitted as a normal scoped, rate-limited
  `ToolGrant` — a metered, receipted tool turn, bounded exactly as an applet's
  `fire` is. So the surface stays empowered-but-accountable-but-bounded; the
  invariant the binding had to keep, it keeps.

## The tests

| File | Surface | Tests |
|------|---------|-------|
| `red_team_mandate_overrun.rs` | 1 — scope/deadline/rate + boundaries | 5 |
| `red_team_authority_amplification.rs` | 2 + 3 — amplification, confused deputy | 4 |
| `red_team_replay_and_forgery.rs` | 4 + 5 — replay/nonce, anti-ghost | 5 |
| `red_team_sandbox_escape.rs` | 6 — ambient-authority escape | 1 (4 teeth) |
| `red_team_empowered_accountable.rs` | 7 — accountable + cross-vessel edge | 3 |

DONE = ran: `cd deos-hermes && cargo test` — all green, including these 18
red-team tests and every pre-existing test. Each named limit holds by running;
no escalation hole was found.
