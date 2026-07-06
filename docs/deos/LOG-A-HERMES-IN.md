# Log a Hermes in — watch a live brain drive the cockpit

A live Claude (over the `hermes-acp` ACP subprocess) is given a short task, **decides
the JavaScript itself**, and that JS runs `run_js` against the cockpit's **live
`World`**: a real crawl of the live cells plus real receipted verified turns landing
on the live ledger — each fire bounded by the agent's `held` authority (the cap
tooth; an over-reach is refused in-band). The cockpit inspector reflects the
committed turns.

This is the dregg confinement story made concrete: the brain is **empowered** (it
writes arbitrary JS), **accountable** (every `run_js` is a metered, receipted gateway
turn), and **bounded** (every affordance fire is cap-gated; the World's own executor
is the second gate).

## What you need

- The release binary (built once):
  ```
  cd starbridge-v2
  cargo build --release --features native-full,agent-js --bin starbridge-v2
  ```
  Binary: `starbridge-v2/target/release/starbridge-v2`.

- The live-brain bake binary (pulls the `hermes-acp` ACP loop + the run_js→live-World
  wiring; a heavier build — its own `live-brain` feature):
  ```
  cd starbridge-v2
  cargo build --release --features native-full,live-brain --bin starbridge-v2
  ```

- `hermes-acp` on PATH (or set `HERMES_ACP_BIN`). Confirm it is usable:
  ```
  hermes-acp --check          # must print "Hermes ACP check OK"
  ```
  It needs its venv's `agent-client-protocol` package. (`brew`/`uvx hermes-agent[acp]`.)

## Run it — the live brain on the live cockpit

```
cd starbridge-v2
HERMES_INFERENCE_PROVIDER=copilot \
HERMES_ACP_MODEL=copilot:claude-sonnet-4.5 \
HERMES_MAX_ITERATIONS=3 \
  target/release/starbridge-v2 --render-live-brain /tmp/live-brain
```

- `HERMES_INFERENCE_PROVIDER=copilot` + `HERMES_ACP_MODEL=copilot:claude-sonnet-4.5`
  drive a real Claude (Sonnet) on the box's **GitHub Copilot** subscription (no
  Anthropic credits required).
- `HERMES_MAX_ITERATIONS=3` **hard-caps** the agent loop to bound Copilot spend.

### What you'll see (a real run, observed)

1. **`/tmp/live-brain.before.png`** — the cockpit inspector over the live World
   before the brain runs (the agent cell's counter at its starting value, 0).
2. The brain handshakes (`initialize` → `session/new` → `session/set_model` →
   `session/prompt`), is given the task ("inspect the ledger, then bump your counter
   by 5"), and **decides the JS itself**. A real observed answer (Sonnet 4.5 on
   Copilot, 1 API call):
   ```
   ── the brain's chosen JS (run_js on the LIVE World) ──
   var cellCount = deos.world.cells().length;
   var app = deos.applet({ affordances: ["bump", "escalate"] });
   app.fire("bump", 5);
   ──
      run_js tool-call admitted = true; result = Some(5); fires committed = 1
      (real verified turns); receipts = [0d03f6ee9b81]
   ```
3. **`/tmp/live-brain.after.png`** — the inspector over the **same** World after; the
   committed turn is on the glass (provenance/blocklog feed shows the new receipt).
   The closing line reports the real ledger movement:
   `LIVE LEDGER: height 5→6, receipts 5→6, agent slot-0 0→5`.

Approx spend: ~1 Copilot API call (in≈15k tokens, ~97% cached; out≈50 tokens) —
negligible, well under the 3-iteration cap.

If the env can't reach a provider (no `hermes-acp`, or no Copilot auth), the bake
**skips gracefully** (exit 0): it still bakes the BEFORE shot and prints exactly which
step is missing. The `run_js`→live-World wiring is real either way — only the live
brain depends on the subprocess + provider.

### Two paths to the brain's tools — the answer path, and the DEEP MCP-server path

**(1) The answer path (`--render-live-brain`, always available).** Hermes's own
tool registry (`terminal`, `write_file`, …) does not include `run_js`, so this path
asks the brain to *emit* the deos-js program as its answer (a fenced ```js block);
`--render-live-brain` extracts it and runs that **exact** script through
`RunJsTool::run_attached_on` on the live cockpit World — a real cap-gated, receipted
verified turn on the live ledger. Faithful (real model, real chosen JS, real
receipts), but the model is reasoning in Hermes's OWN unconfined process: a benign
`terminal`/`write_file` it reached for would never reach dregg.

**(2) The DEEP MCP-server path (`deos-hermes mcp-server` + `with_dregg_mcp_server`,
BUILT and proven by running).** deos registers a **dregg stdio MCP server** as the
model's tool source on `session/new`'s `mcpServers`. Hermes spawns that server
(`deos-hermes mcp-server`) and the model's tools become *exactly* the ones it
advertises — `run_js` + `terminal`, and **only** those. There is no unconfined
shell to reach for. Every tool the model calls routes to our MCP server process —
the dregg sandbox:

- **`run_js`** → the model's chosen script runs through `RunJsTool` on a deos-js
  engine mounted under the agent's `held` (the cap tooth, never root): a cap-gated,
  receipted verified turn. (Cross-process seam, named below.)
- **`terminal`** → the command execs INSIDE a confined firmament PD
  (`confined::launch_confined`): file/net/exec are denied by the host OS sandbox
  (Seatbelt/seccomp+landlock), the PD's only channel is its Endpoint, and the four
  sandbox probes RUN inside it. A command attempting ambient authority (read a file
  outside the grant, open a socket) is **physically denied** — the returned
  confinement verdict `0xf` proves *every* tooth held. The call is a cap-gated,
  receipted dregg turn through the `HermesGateway`.

The server speaks standard MCP over stdio (the `mcp` Python SDK's `stdio_client` +
`ClientSession`): `initialize` (echo `protocolVersion`, advertise `tools`),
`tools/list` (exactly `run_js`/`terminal`), `tools/call` (route through dregg),
`ping`. See `deos-hermes/src/mcp_server.rs` + `tests/mcp_confined_tools.rs`
(6 tests, proven by running).

#### Run the deep path live

```
# Build the dregg MCP server binary (the model's tool source).
cd deos-hermes && cargo build --features js-agent --bin deos-hermes

# Drive a real hermes-acp brain whose ONLY tools are the dregg MCP server's.
HERMES_INFERENCE_PROVIDER=copilot \
HERMES_ACP_MODEL=copilot:claude-sonnet-4.5 \
HERMES_MAX_ITERATIONS=3 \
  cargo run --features js-agent --bin deos-hermes -- live-mcp
```

`live-mcp` registers `deos-hermes mcp-server` on `session/new`, prompts the model to
use `run_js`, and reports each tool-call the model issued — every dregg-named one was
executed in the dregg sandbox (the MCP subprocess; its confined execution logs to
stderr). For the **cockpit-attached** live brain, set `DEOS_MCP_SERVER_BIN` to the
`deos-hermes` (js-agent) binary before `--render-live-brain`: the live-brain bake then
registers the dregg server too.

**Observed live (Sonnet 4.5 on Copilot, real API calls):** the deep wire is LIVE. The
handshake + `session/new` with `mcpServers=[dregg]` completed against the real
`hermes-acp` subprocess, and Hermes **spawned our dregg MCP server and registered its
tools into the live model's tool surface** — observed in the live log:

```
tools.mcp_tool: MCP server 'dregg' (stdio): registered 2 tool(s): mcp_dregg_run_js, mcp_dregg_terminal
acp_adapter.server: refreshed tool surface after ACP MCP registration (25 tools)   # 23 base + our 2
```

(A spawn-probe wrapper confirmed `hermes-acp` exec'd our `deos-hermes mcp-server`
child.) So the live model is genuinely *offered* the dregg-confined `run_js`/`terminal`.

The last mile — *this* model on *this* Copilot path actually emitting the `tools/call`
— did not fire in the capped iterations (the model answered in text, `tool_turns=0`);
that is model tool-selection behavior, not a wiring gap. The tool *execution* is proven
by running over real MCP stdio (the direct drive below: `tools/list` = the two tools, a
`terminal` returning verdict `0xf` with ambient authority denied + a receipt, a `run_js`
receipted turn) and by `tests/mcp_confined_tools.rs` (6 tests). Once Hermes routes a
`mcp_dregg_*` call (a model that selects it, or a forced tool-choice), it lands in the
dregg sandbox exactly as the direct drive shows.

**Environment note:** the brew `hermes-agent` venv lacked the `mcp` Python SDK, so
`register_mcp_servers` silently no-op'd until `pip install mcp` into
`…/hermes-agent/libexec/bin/python`; after that the registration + spawn above are live.

#### The one `hermes-acp`-side seam — base toolset is additive, not exclusive

The current `hermes-acp` hardcodes the ACP session's `enabled_toolsets` to
`["hermes-acp"] + <mcp servers>` (`acp_adapter/session.py::_expand_acp_enabled_toolsets`);
there is **no ACP-level knob to empty the base toolset**. So registering the dregg MCP
server *adds* `run_js`/`terminal` to the model's tools rather than *replacing* Hermes's
built-ins — the live session above showed 23 tools, not 2. The "the model has no other
tool path" guarantee is therefore **layered, not yet exclusive against an unpatched
`hermes-acp`**:

- The dregg-provided tools (`run_js`, the MCP `terminal`) run in the dregg sandbox
  (cap-gated + receipted; the MCP `terminal` in a confined PD) — fully real.
- Hermes's OWN built-in `terminal`/`write_file` **still route through deos's
  `session/request_permission` authority gate** (`bridge.rs`) — every one is a
  cap-gated, refusable-in-band dregg turn (the `live-refuse` proof). They are confined
  at the *authority* face, but not yet OS-sandboxed in a PD.

EXCLUSIVITY is one upstream knob away: an ACP `session/new` that lets the client set
`enabled_toolsets=[]` (base off) so the dregg MCP server is the model's *only* tool
source. That is a `hermes-agent` change (drop the `or ["hermes-acp"]` default when the
client sends an explicit empty list), named here. With it, the model has no unconfined
shell, full stop. Until then, the unconfined shells are still **gated** (authority face)
but not **PD-sandboxed**.

#### Drive the MCP server directly (no provider needed — always green)

Pipe MCP frames into the server binary over stdio to see the confinement without a
model. A real observed run:

```
$ printf '%s\n' \
  '{"jsonrpc":"2.0","id":1,"method":"initialize","params":{"protocolVersion":"2025-06-18"}}' \
  '{"jsonrpc":"2.0","method":"notifications/initialized"}' \
  '{"jsonrpc":"2.0","id":2,"method":"tools/list","params":{}}' \
  '{"jsonrpc":"2.0","id":3,"method":"tools/call","params":{"name":"terminal","arguments":{"command":"cat /etc/passwd && curl http://1.1.1.1"}}}' \
  '{"jsonrpc":"2.0","id":4,"method":"tools/call","params":{"name":"run_js","arguments":{"script":"var app=deos.applet({affordances:[\"bump\"]}); app.fire(\"bump\",5);"}}}' \
  | deos-hermes mcp-server

# id 2: tools = [run_js, terminal]                        (the model's ONLY tools)
# id 3: terminal → "confinement verdict 0xf (ALL teeth held). The shell ran in the
#        container — file/net/exec denied; ambient-authority attempts refused."
#        + a dregg receipt                                 (cap-gated + receipted)
# id 4: run_js  → "1 verified turn(s) committed" + a dregg receipt
```

The `cat /etc/passwd && curl …` the model asked for could not reach the file or the
network: it ran inside the dregg PD, where the OS sandbox denies that ambient
authority. The shell ran in the container, not loose.

#### The one cross-process seam (named — and now WIRED)

An MCP server is a **separate subprocess** Hermes spawns, so it cannot share the
cockpit's `Rc<RefCell<World>>` (single-threaded, non-`Send`, in-process). By
default the `mcp-server`'s `run_js` drives its OWN embedded verified World (a real
receipted turn on its own ledger), NOT the cockpit's live-rendered World. The
socket that lands the model's `run_js` on the *cockpit's* live ledger over MCP is
BUILT: `McpToolHost::with_world_bridge(socket_path)` routes `run_js` through a
`SocketWorldSink` (`deos-hermes/src/world_bridge.rs` — the `WorldSink` surface
over a Unix socket, length-prefixed serde_json frames), and the cockpit process
answers it against its live `WorldSinkAdapter` via
`starbridge_v2::agent_attach::world_bridge` (`serve_world_bridge` blocking on the
World-owning thread, or `WorldBridgeServer::pump` from the frame loop). It is
FAIL-CLOSED: socket absent/dead ⇒ the tool call refuses in-band — never a silent
fallback to the embedded World. Proven end-to-end in
`deos-hermes/tests/world_bridge_e2e.rs` (the answer path (1) already lands on the
live cockpit World, so the two together cover both). The `terminal` confinement
is fully real in-process (the PD is forked from the MCP server).

## Depth of integration — the three confinement faces

- **Authority face** (`bridge.rs`, `HermesGateway`): every tool-call deos sees becomes
  a cap-gated, metered, receipted dregg turn. Fires on Hermes's dangerous-command
  permission requests (the `rm -rf` seam — `live-refuse`) AND on every dregg MCP
  `tools/call` (`McpToolHost::call_tool`).
- **Ambient face** (`confined.rs`): a body runs in an OS-sandboxed PD
  (Seatbelt/seccomp+landlock), reachable only over a firmament Endpoint — file/network/
  exec denied. The **MCP server's `terminal` execs inside exactly such a PD**: the
  command's ambient-authority attempts are physically denied (verdict `0xf`).
- **Tool-source face** (`mcp_server.rs`, the keystone): deos advertises the dregg MCP
  server as the model's tool source on `session/new`'s `mcpServers`, adding `run_js` +
  a confined `terminal` to the model's tools — every one routes through the two faces
  above (cap-gated + receipted; the `terminal` in a confined PD). Making these the
  model's **only** tools is one upstream `hermes-acp` knob away (empty base toolset over
  ACP — see the seam above).

**The disjointness the prior slice named is CLOSED in mechanism, and confinement is
layered today.** The real model can now *call* `run_js`/`terminal` as first-class MCP
tools that execute in the dregg sandbox — built (`deos-hermes mcp-server` +
`with_dregg_mcp_server`) and proven by running (`tests/mcp_confined_tools.rs`, 6 tests;
the `live-mcp` mode reached a live provider; the direct stdio drive shows verdict `0xf`).
Two seams remain, both named: (1) the cross-process socket that would land the MCP
`run_js` on the *cockpit's* live World (the answer path already lands `run_js` there;
the MCP `terminal` confinement is fully real in-process); (2) the upstream knob that
makes the dregg tools EXCLUSIVE (until then, Hermes's built-in shells are gated at the
authority face but not PD-sandboxed).

## The Anthropic-key path (one env swap)

When ember's Anthropic credits are restored, swap the provider — nothing else changes:

```
HERMES_INFERENCE_PROVIDER=anthropic \
HERMES_ACP_MODEL=anthropic:claude-sonnet-4-5 \
HERMES_MAX_ITERATIONS=3 \
ANTHROPIC_API_KEY=...   # ember's key; never commit it \
  target/release/starbridge-v2 --render-live-brain /tmp/live-brain
```

## The scripted live-cockpit drive (no brain, always green)

To see the `run_js`→live-cockpit machinery without a provider — a SCRIPTED `run_js`
on the live World (crawl 4 real cells, fire a real turn 5→6, an over-reach refused):

```
cd starbridge-v2
cargo build --release --features native-full,agent-js --bin starbridge-v2
target/release/starbridge-v2 --render-agent-attach /tmp/agent-attach
```

Produces `/tmp/agent-attach.png` (the inspector showing the cell the JS modified) and
prints the crawl/fire/refuse witness. Add `--fork` to drive a `world.fork()` (the safe
sandbox; the live image untouched).

## How it's wired (the seam)

- `starbridge-v2/src/agent_attach.rs` — `WorldSinkAdapter::live(...)` / `fork_of(...)`:
  a `deos_js::WorldSink` over the cockpit's `Rc<RefCell<World>>`. A fire goes through
  `World::commit_turn` (the real verified executor) and lands on the live ledger +
  provenance feed.
- `deos-hermes/src/run_js.rs` — `RunJsTool::run_attached_on(...)`: runs a JS script on
  a provided live `WorldSink` under the agent's `held` (the accountability turn + the
  cap-gated fires). This is what the bake calls with the brain's chosen script.
- `deos-hermes/src/live_js.rs` — `LiveJsHands` + `AcpClient::with_run_js_hook(...)`
  (`deos-hermes/src/acp_client.rs`): the forward-looking seam for when Hermes CAN call
  a `run_js` tool (the MCP-server bridge). A `run_js` permission request would be
  dispatched here, the model's `rawInput.script` executed on the live World, and the
  receipts recorded (`AcpClient::js_runs()`). Wired + ready; the bake uses the
  direct path above because Hermes does not yet expose `run_js` (see the seam note).
- `starbridge-v2/src/main.rs` — `--render-live-brain`: builds the live cockpit World,
  bakes before/after, drives the real `hermes-acp` brain, and runs its chosen JS.

---

## DREGG IS THE HOST — the polarity inversion (dregg-as-ADOS)

Everything above registers dregg's tools INTO hermes-acp's ACP session: **hermes
is the host**, dregg's `run_js`/`terminal` are guests added *alongside* hermes's
own base `[hermes-acp]` tools — and those base tools (an unconfined `terminal` /
`write_file` / `web`) are the leak. The authority gate (`bridge.rs`) confines them
at the *authority* face, but the agent **process** still runs with full ambient OS
authority.

`deos-hermes/src/host.rs` (`DreggHost`) inverts the polarity. **dregg hosts the
agent; the agent does not host dregg.** We do NOT fork hermes — the OS jail
neutralizes hermes's leaky base tools at the OS level, whatever its tool table
says.

### The three legs (each proven by running — `tests/dregg_hosts_the_agent.rs`)

1. **The agent runs inside a dregg jail.** `DreggHost::run_hosted_agent` spawns
   the agent body INSIDE a confined firmament PD (`confined.rs` →
   `ProcessKernel::spawn_pd_confined_with`) whose OS sandbox (macOS Seatbelt /
   Linux ns+seccomp+landlock) denies ambient file/exec/network + every inherited
   fd. The agent's ONLY channel is its firmament Endpoint — the dregg control
   channel. hermes's own base shell/file tools, run in this process, hit the jail
   walls (`open` denied, `socket` denied, `execve` denied) and go INERT.

2. **dregg's tools are the only *effective* effect-path.** The jailed agent's only
   way to *cause* anything is a dregg request over the Endpoint, routed through
   `McpToolHost` (cap-gated, receipted; `run_js` → a deos-js World, `terminal` → a
   nested confined PD). Every effect lands in OUR container, never the host.
   (Leg (a): `terminal` execs in a PD with file/net/exec denied + a dregg receipt.)

3. **Structured, opt-in egress.** `egress.rs` (`EgressPolicy`) is the host's
   standing set of granted doors — **sealed by default**. `grant_read(path)` opens
   ONE specific host subpath, threaded into the jail's sandbox profile as a single
   allow-rule (`spawn_pd_confined_with` carries the `Confinement`); that path — and
   ONLY that path — becomes readable inside the jail. A SIBLING outside the grant
   stays denied (a named door, not a hole). `revoke(path)` closes it. The agent
   never mints its own egress; the door is the host's cap, revocable.

   The **provider-only SOCKET door** is the network sibling: `grant_provider(host,
   port)` opens EXACTLY one outbound endpoint (a jailed live brain's model call),
   folded into `Confinement::net_out`. Deny-default: no grant ⇒ no outbound network
   at all. It is enforced on **both** platforms now:
   - **macOS** — an SBPL `(allow network-outbound (remote ip "host:port"))` rule
     (a loopback grant pins host+port; a remote host is port-scoped, hence the
     recommended trusted-localhost-proxy pattern).
   - **Linux** — a seccomp **`connect`-notification** door
     (`sandbox.rs::provider_door` + the `linux` backend). The jailed body may
     `socket()`, but every `connect()` traps to a trusted supervisor (firmament
     code kept in the connected net namespace) that admits EXACTLY the granted
     endpoints — establishing the connection on the child's behalf and injecting
     the connected fd — and `EPERM`s every other host:port. The child's own net
     namespace stays **empty**, so deny-default is *structural*: no route exists;
     the only reachable endpoint is one the supervisor opens after a pure `admits`
     match; any plumbing failure (dead supervisor, unreadable sockaddr) fails
     **closed**. Chosen over slirp4netns / veth+nftables because it needs no
     external binary and no host-network mutation, and it matches the loopback
     provider-door test exactly. STATUS: the policy + cBPF config layer is
     unit-tested (`sandbox.rs` tests) and the backend cross-builds for Linux; the
     connect-notify RUNTIME (the `provider_egress` test's socket teeth) is
     validated on a Linux host / CI — it is not exercised on a macOS dev host.

### What is REAL (the stand-in era is over)

REAL: the JAIL (file/net/exec/fd denied — the four base teeth + the three
base-tool-escape teeth, proven in-PD: an unconfined shell via `execve(/bin/sh)`,
a host-FS read via `open(/etc/passwd)`, an arbitrary `socket(AF_INET)` — each
DENIED); the EGRESS door (granted host path readable, sibling denied, both
proven in-PD; sealed/revoke close it); the dregg TOOL effect-path (cap-gated,
receipted turns on the verified executor, asserted on `McpToolHost`'s tape).

REAL: **the agent's BRAIN, in the jail.** The wire this section once named ("compile
hermes's agent loop into the PD body") is CLOSED: `host.rs::brain_body_serving`
compiles a real brain-driven ACP peer (`HermesAgentPeer::new(session_id, brain)`)
INTO the confined PD body, and the generic core `run_brain_confined` runs either
brain kind on the same jail/gate/receipt rail:

- the on-box `LocalBrain`, in the DEFAULT green suite —
  `tests/brain_in_jail.rs::confined_brain_run_is_jailed_and_leaves_real_receipts`
  (jailed multi-step ACP turn, every admitted tool-call a real 64-hex dregg receipt);
- a genuine `reqwest` `HttpLlm` brain (`brain.rs`, Anthropic Messages or
  OpenAI-compat, built by `live_brain_from_env`), behind the `live-brain` feature —
  `tests/provider_egress.rs::live_brain_in_jail_rides_the_provider_door_to_a_mock`:
  the brain POSTs a real completion from INSIDE the exec-denied PD over the granted
  provider socket, its tool-call receipts through the gate; execve/host-FS/other-net
  stay denied.

The honest residue (small, named): the jailed-live proof runs against a **hermetic
loopback mock provider**; the real-provider hit is the `#[ignore]`d
`live_completion_yields_a_nonempty_brainstep` + an env swap. And the jailed-live
path (`DreggHost::run_hosted_agent_live`) has **no CLI entry yet** — it is exercised
by the test, not a subcommand (`brain-live` runs the live brain over the standard
dock gateway, NOT in the jail). Both are wiring, not architecture.

### The firmament knob

`sel4/dregg-firmament/src/process_kernel.rs::spawn_pd_confined_with(granted,
confinement, body)` is the one knob this needed: it confines to a caller-supplied
`Confinement` (the Endpoint-only jail PLUS any granted egress read-paths) instead
of the implicit Endpoint-only one, forcing the control socket into the keep-list.
A caller that grants nothing gets the same jail as `spawn_pd_confined`. The egress
paths are canonicalized (symlink-resolved) before they enter the SBPL/Landlock
profile, because the OS sandbox matches the resolved path the kernel sees after
`open` follows symlinks (macOS `$TMPDIR` `/var/folders/…` → `/private/var/…`).

### Run it

```
cd deos-hermes
cargo test --test dregg_hosts_the_agent           # the three legs
cargo test                                        # full suite (incl. red-team)
cargo test --features js-agent                    # + the deos-js run_js leg
```
