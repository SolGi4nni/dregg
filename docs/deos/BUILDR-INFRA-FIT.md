# buildr / builders.dev ↔ dregg infra: the fit map

What of the dregg/deos infrastructure built this epoch genuinely serves David's
two repos — `buildr-private-beta` (the agent-harness/metaharness) and
`builders.dev` (the Cloudflare-native peer-coordination SaaS)? This is a
read-only synthesis: per NEED → which dregg piece serves it → how, concretely,
with file:line on both sides. It ends with the smallest real first slice and the
realistic Fork-B path.

The honest frame up front: **most of the dregg pieces are the *verified form* of
things David already built unverified.** buildr's bb engine, its spool, its RSH
gates, its restart-loop counter, its claims-fence — each has a dregg analogue
that is the same shape with a cryptographic/formal tooth. The value is not "a
new capability buildr lacks"; it is "the silence-incident / 15h-wedge / forged-OK
*class* of bug made structurally impossible." That is exactly the kind of value
that justifies a small adoption, not a rewrite.

---

## The two repos in one paragraph each

**buildr-private-beta** — a metaharness: the `herdr` Rust TUI binary
(`herdr/src/`, the workspace/pane multiplexer + Unix-socket API) plus the **RSH**
overlay (Rules/Skills/Hooks in `agents/claudecode/`) plus team-skin packs. Its
load-bearing asset, kept unanimously by the fleet, is the **bb engine**
(`herdr/src/blackboard.rs`): an append-only rkyv log with a BLAKE3 hash chain,
flock single-writer-per-conversation, plus the **A2A spool**
(`herdr/src/a2a_spool.rs`): per-pane "deliver-on-next-turn" queues with TTL/GC,
wake markers, and an append-only ack ledger. Its scars are all about that engine
drifting from artifact: a 69 MB ack ledger thrashing the TUI; pane-id reuse
delivering stale spool rows; RSH gates that pass on *mechanism* not *predicate*;
and the headline — the **15h wedge**, a restart-loop logging `revert OK` over a
live artifact that re-wedged every 4 minutes (assertion-over-artifact).

**builders.dev** — a hosted, Cloudflare-edge-native, multi-tenant SaaS where
humans and agents are equal-tier peers in a group-chat fabric, with a Council
deliberation primitive. Stack: Next.js 16 PWA on Workers; ~41 Workers; Durable
Objects as the stateful actors (`TeamAgent`, `GroupchatAgent`, `CouncilAgent`,
`McpAgent`, `BuilderAgent`); D1 (179 migrations) as system-of-record; KV for hot
caches; R2 for council artifacts; Cloudflare Queues (`council-events`,
`agent-events`, `bridge-events`, each with a DLQ); Analytics Engine for
observability. Auth = GitHub OAuth → 15m-TTL JWT in KV; per-agent MCP bearer
keys (`mcps_<hex>`) in D1; authority tiers 1–4 on memberships. Multi-tenancy =
team-scoped every query + trust-header stripping at the edge. Every state change
is symmetric (human UI ↔ agent MCP tool) and emitted to Analytics Engine.

---

## §1 — bb engine → the dregg data plane (`Bus`)

**buildr NEED.** The bb engine's hardest-won invariant: *a thing on the spool is
not a thing handled.* The silence-incident class — sender thinks a message was
delivered/handled; it was only enqueued — is what `a2a_spool.rs` fights with
ack-ledger markers (`surfaced`/`drained`/`presented`/`delivery_failed`/`expired`,
`a2a_spool.rs:58`), TTL+GC (`SPOOL_TTL_DAYS=7`, `a2a_spool.rs:53`), and the
hot-path budget guards born from the 69 MB incident
(`SPOOL_PENDING_BUDGET_*`, `a2a_spool.rs:66-100`). The ack-ledger is "handled"
as an *append to the same log* — which is exactly why it grows unbounded and why
"queued vs handled" can drift.

**dregg PIECE.** `captp/src/data_plane.rs` — the `Bus` (`data_plane.rs:366`). It
is the bb engine, point for point, with the queued/handled distinction made
*structural* rather than *ledgered*:

| bb engine | dregg `Bus` | file:line |
|---|---|---|
| append-only log | the blocklace / per-recipient relay | `data_plane.rs:368` (`relay: MessageRelay`) |
| spool / mailbox | `MessageRelay` per-recipient inbox | `data_plane.rs:627` (`drain`) |
| wake / event-notify | `Waker` — cursor-advance is the wake | `data_plane.rs:291`, `poll_wake` `:525` |
| ack-ledger ("handled") | `delivered: HashMap<…, Vec<[u8;32]>>` drain-witness | `data_plane.rs:380`, `delivered_hashes` `:642` |
| receipt-identity | `Delivery` (promise) vs `is_handled` (witness) | `data_plane.rs:235`, `:249` |

The keystone: **`Delivery::is_handled` consults the drain-witness, never the
promise** (`data_plane.rs:249-251`). "Queued" lives in the relay; "handled" lives
in the separate `delivered` log; you cannot conjure "handled" by holding the
receipt. The headline test proves both polarities — `enqueue_wake_drain_witness_lifecycle`
(`data_plane.rs:688`) and `undrained_is_distinguishable_and_convictable`
(`data_plane.rs:748`): an undrained box is *provably a drop*
(`adjudicate_from_inbox` returns conviction), and the same box flips to acquitted
once drained. This is the silence-incident fix as a theorem, not a guard.

**WHERE IT SUBSUMES / STRENGTHENS buildr.**
- The ack-ledger-runaway class (`a2a_spool.rs:66-100`) is *absent by construction*:
  "handled" is the set of drained content-hashes, which is bounded by real
  delivery, not an append-per-marker that needs compaction.
- The wake is unforgeable: it is minted only by `Waker::tick` on an admitted
  enqueue (`data_plane.rs:307`, the only mutator), and `wake_cannot_be_forged`
  (`data_plane.rs:885`) proves there is no setter. buildr's wake is a written
  signal in the ledger; dregg's is a *fact about the monotone cursor*.
- A refused send leaves **no phantom work** — no queue entry, no cursor tick, no
  receipt (`over_attenuated_enqueue_refused_no_phantom_work`, `data_plane.rs:820`).
  buildr's guard-a2a-murmur (`guard-a2a-murmur.sh`) caps message size *advisorily*;
  dregg refuses an over-broad send *at the seam* before anything is queued.
- Pane-id-reuse-inherits-stale-spool (`a2a_spool.rs:14-40`, bug #119/#91) is the
  channel-scoping problem; `SendCap` binds `(recipient, name, grant)` and
  `admits` checks all three (`data_plane.rs:168-178`), so a reused name cannot
  inherit another scope's authority.

**The gap to be honest about.** `Bus` is an in-process Rust struct; buildr's
spool is multi-process across panes (flock-gated). Adopting `Bus` as buildr's
comms substrate means giving it a process boundary (a daemon owning the relay,
panes talking to it) — which buildr already has (the herdr daemon + Unix socket).
The `Bus` would live in the daemon; the panes' bb verbs become RPCs to it. This
is real work but small: the daemon exists.

---

## §2 — the 15h wedge → the recovery monitor

**buildr NEED.** The root failure that burned the fleet for 15 hours
(`recovery_monitor.rs:26-29` records it verbatim): a restart-loop logged
`revert OK` / `refreshed=5` while the live artifact (dead tokens) re-wedged every
4 minutes — *assertion-over-artifact*. The fleet invented, under fire, a
restart-attempt counter + window + a `RECOVERY_NOT_HOLDING` escalation signal so
the loop would stop instead of running forever. This lives nowhere durable in
buildr; it was an emergency reflex. buildr's session-manager/cred-steward
concerns (session resume `agent_resume.rs`, `guard-trust.sh`/`guard-mcpservers.sh`
snapshot-restore, the cred-pool downshift in `rules/dev-process.md`) are exactly
the subsystems that wedge silently when a token rotates or a process dies.

**dregg PIECE.** `sel4/dregg-firmament/src/recovery_monitor.rs` — this *is* that
counter, generalized and made the design rather than the reflex. The mapping is
one-to-one and even cites the council:

- **artifact-over-assertion** is the trait contract: `Subsystem::probe` reads the
  LIVE ARTIFACT (`recovery_monitor.rs:129`), `Subsystem::claim` returns the
  self-report which is "NEVER TRUSTED AS EVIDENCE OF HEALTH"
  (`recovery_monitor.rs:100-105`).
- **the council's exact signal**: `Divergence::RecoveryNotHolding`
  (`recovery_monitor.rs:162`) fires when `claim == Recovered` but
  `probe() == Wedged` — the `revert OK` over a re-wedged artifact, caught
  structurally.
- **the restart-loop guard**: `Escalation::RecoveryNotHolding { attempts, last_artifact }`
  (`recovery_monitor.rs:178`) after `MonitorPolicy::max_attempts` within
  `rewedge_window` — "precisely the counter the council invented under fire to
  end a 15-hour restart-loop" (`recovery_monitor.rs:176-177`).
- **fail-closed**: a restart is `Verdict::Recovered` only if a FRESH post-restart
  probe witnesses health (`recovery_monitor.rs:194-198`, `:59-61`). The monitor
  never claims success the artifact does not support.
- **recursive**: a monitor is itself a `Subsystem` (`recovery_monitor.rs:64-70`),
  so a supervisor can recover a monitor that gave up — turtles up.

**WHERE IT SOLVES THE WEDGE CLASS FOR buildr.** Wrap each fragile buildr
subsystem in a `Subsystem` impl whose `probe()` reads the *artifact*, not the
log:
- cred-steward: `probe()` = does a token actually authenticate *right now* (a
  real auth round-trip), not `refreshed=5`. A rotation that "succeeded" but left
  dead tokens is caught as `RecoveryNotHolding`.
- session-manager: `probe()` = does the pane's agent process actually respond
  (the live REPL), not "session_id written." The `agent_resume.rs` registry is
  the *claim*; the round-trip is the *artifact*.
- the bb daemon itself: `probe()` = is the spool draining (real depth falling),
  the very metric `a2a_spool.rs:66-100` watches — but as an *external* watcher
  that can stop/restart, not a self-report tripwire.

This is the single most directly-valuable transplant: it is small (the module is
~deliberately a few hundred lines, no async/IO of its own,
`recovery_monitor.rs:17-19`), it is the verified form of a thing buildr already
wishes it had durably, and it kills the exact class that cost 15 hours.

---

## §3 — agent isolation / claims-fence → sandboxed firmament + confined PD

**buildr/builders NEED.** Two isolation problems. (a) buildr's
`guard-claims-fence.py` and `guard-build-offload.py` enforce — *advisorily, via
hooks* — that an agent edits only its claimed path glob and doesn't thrash shared
build dirs (INTEGRATIONS.md Principle P1: "each agent claims a path glob, never
edits outside"). A smarter model can satisfy the hook's *mechanism* while
violating the *intent* (the RSH advisory-vs-deterministic problem, per the
RSH-scaling notes). (b) builders.dev runs untrusted agent code in
sandbox backends (CF Containers / Fly / Hetzner / local Docker, the
`workspace-image-builder` + `builder-agent` workers) and needs real OS
confinement, not a path-glob promise.

**dregg PIECE.** `sel4/dregg-firmament/src/sandbox.rs` + `host_pd.rs`.
`Confinement` (`sandbox.rs:64`) is real OS-enforced confinement applied in the
child right after `fork()`, before the payload runs (`sandbox.rs:16-18`): on
macOS a `(deny default)` Seatbelt profile (no `network*`, no `process-exec*`, no
`mach-lookup*`, `sandbox.rs:24-25`); on Linux unshare+seccomp+Landlock+close_range
(`sandbox.rs:29-35`). The cap→OS mapping seed: a child keeps *exactly* its
granted fds (`endpoint_fds`, `sandbox.rs:66-68`) and the only channel is its
firmament Endpoint. `host_pd.rs` then makes that confined child a first-class
*capability*: a `HostPd(id)` cap is invoked by a validated round-trip over the
control socket (`host_pd.rs:99`), gated by the unified `granted ⊆ held`
attenuation check (`host_pd.rs:106`, `is_attenuation`) — the same lattice every
dregg cap uses. Holding the socket *is* holding the cap; if the child exits, the
cap is dead (`host_pd.rs:117-122`).

**WHERE IT SERVES.** The claims-fence stops being advisory: an agent's authority
to touch a path/channel becomes a *cap it holds*, and the confinement *physically
denies* everything outside it. The "mechanism vs predicate" gap closes because
there is no mechanism to game — the OS denies the syscall. For builders.dev this
is the verified substrate under the sandbox-backend story: instead of trusting
the container image, the agent PD is OS-confined to its Endpoint with an
attenuable cap. The recovery monitor's `HostPdSubsystem` adapter
(`recovery_monitor.rs:46`) already watches exactly these confined PDs — so §2 and
§3 compose.

**Honest gap.** This is seL4/firmament-flavored and Unix-only behind
`process-pd-sandbox`. builders.dev's actual sandbox runtime is Cloudflare's; the
fit is conceptual-plus-local-dev, not a drop-in for the CF data plane. The
strongest near-term use is local-swarm confinement (the `apps/sandbox-bridge`
local CLI spawner in INTEGRATIONS.md), where a real OS sandbox is available.

---

## §4 — the tool-call/verdict seam → ToolGateway-as-router (the ADOS one-seam)

**buildr/builders NEED.** Both repos converge on the same seam: every agent
tool-call should be admitted-or-refused against a mandate, metered, and leave a
record. buildr does this with RSH hooks (PreToolUse gates: `guard-commit.py`,
`guard-a2a-murmur`, `guard-build-offload`) — *advisory, per-harness, drift-prone*
(the conventional-commits guard/CI drift, `guard-commit.py:87-95`, is the
canonical "two copies of the policy disagree" bug). builders.dev does it with
per-agent MCP bearer keys (`mcp_keys` in D1) + scope-globs + budget caps
(`workers/budget`) + Analytics-Engine emission — but admission is scattered across
the entry proxy, the MCP server, and the budget worker, and "the record" is
analytics, not a verifiable receipt.

**dregg PIECE.** `sdk/src/tool_gateway.rs` — `ToolGateway`. The whole road in one
object: **admit → enqueue → execute → results-back** (`tool_gateway.rs:63-65`),
the on-ramp to the same `Bus` data plane. Admission folds the *whole* delegated
policy — SCOPE ∧ DEADLINE ∧ RATE — as `deleg_admit` (`tool_gateway.rs:125`), the
byte-faithful mirror of the proven Lean `delegAdmit`
(`metatheory/Dregg2/Apps/ToolAccessDelegation.lean`, cited at
`tool_gateway.rs:13-20`). Critically there are **two enforcement surfaces, both
load-bearing** (`tool_gateway.rs:29-46`): (1) in-band `deleg_admit` returns an
`Err` refusal with no turn submitted (the anti-ghost tooth — no spend, no counter
advance); (2) in the executor, the worker cell carries a `mandate_program`
(`FieldLte { calls_made ≤ rateLimit }` ∧ `Monotonic`), so even a caller that
bypassed `deleg_admit` is rejected by the cell-program check. The rate ceiling is
*bound into the committed transition*, not merely pre-checked. A granted call
commits with a receipt and a conserved spend; an out-of-mandate call is refused
in-band — the both-polarity shape the Lean crown proves.

**WHERE IT SERVES.** This is the ADOS one-seam (`HERMES-INTEGRATION.md:5-12`):
"an agent is an intricate loop; dregg closes the enforcement gap at exactly one
seam — the tool-call → verdict → receipt boundary." For buildr, the per-harness
RSH-gate drift dissolves: one `deleg_admit` predicate, one mandate, every harness
routes through it (no `style|revert`-vs-`release|rsh` skew because there is one
policy object, not a hook copy + a CI copy). For builders.dev, the scattered
admission (entry + mcp-server + budget) collapses to one gated router, and "the
record" becomes a verifiable receipt the tool-result carries — strictly stronger
than an analytics event. `deos-hermes` (`HERMES-INTEGRATION.md`) is the worked
example: Hermes' single dispatch funnel (`registry.dispatch` at
`model_tools.py:1116`) is the exact interposition point, and dregg does *not*
rebuild the loop — it gates the one seam.

---

## §5 — builders.dev (the SaaS) wants dregg

builders.dev is the place the dregg control-plane story (caps/receipts/cells) and
the dregg data-plane story (`Bus`) line up with a real product's needs:

| builders.dev need | builders.dev today | dregg piece | how |
|---|---|---|---|
| auth | GitHub OAuth → 15m JWT in KV; MCP bearer in D1; tiers 1–4 | **caps** | `login = receiving your root cap; a session = the cap-tree you hold; logout = revoking it` (`SESSION-LOGIN.md`). A session *is* a c-list, not a JWT+table. Authority tiers become cap attenuations. |
| audit | Analytics Engine events; `budget_spend_events` D1 table | **receipts** | every state-change becomes a `CustodyReceipt`/`TurnReceipt` — a *verifiable* record, not a self-emitted analytics row. "It didn't happen unless it's measurable" (Rule 9) upgrades to "it didn't happen unless there's a receipt." |
| multi-tenant | team-scoped queries + trust-header stripping at edge | **cells** | a tenant = a cell sub-tree; scope-fencing becomes cap-reachability, not query discipline. Cross-team leakage is unreachable, not just un-queried. |
| data plane | CF Queues (`council/agent/bridge-events`) + DLQs + Durable Objects | **`Bus`** | the queued-vs-handled distinction (`is_handled`) is exactly what a DLQ approximates; `Bus` makes "delivered" a witness, "dropped" convictable. The `firehose` WS becomes `Bus::publish` fan-out with per-subscriber receipts. |
| metered tool-calls | budget worker circuit-breaker | **ToolGateway** | the per-agent rate/scope/deadline mandate as `deleg_admit`, bound into the committed transition (§4). |

The strongest single alignment: builders.dev's **symmetric-action** principle
(every state-change has a human-UI face and an agent-MCP-tool face) is the dregg
*turn* — one verified transition regardless of who initiated it. dregg is the
substrate that makes "human and agent are equal-tier peers" enforceable rather
than conventional.

**Honest gap.** builders.dev is Cloudflare-edge-native (Workers/DO/D1/KV/R2).
dregg is a Rust/Lean substrate, not a CF Worker. So §5 is *direction*, not a
drop-in: the realistic path is dregg-as-a-service behind one Worker binding (a
`cloud-bb`-shaped worker already exists as the "inception-merge keystone"),
proving receipts/caps on one surface (e.g. the council artifact log) before any
broad migration.

---

## §6 — the smallest real first slice (sequenced by value/effort)

Not the grand Fork-B rewrite. Concrete, adoptable-today slices, ordered by
(value ÷ effort):

1. **The recovery monitor as a standalone watcher** *(highest ratio)*. Lift
   `recovery_monitor.rs` (it has no async, no I/O, no dregg-cell deps in its core
   — `recovery_monitor.rs:72` imports only `String`). Write one `Subsystem` impl
   whose `probe()` does a real cred/auth round-trip. Point it at the
   cred-steward. Outcome: the 15h-wedge class cannot recur — a `revert OK` over a
   dead token escalates instead of looping. **Effort: a day. Value: the exact
   scar.** This is the slice to do first.

2. **`Bus` as a comms lib in the herdr daemon** *(high ratio)*. The daemon
   already owns the spool and a Unix socket. Replace the ack-ledger-as-truth with
   `Bus`: enqueue returns a `Delivery`; "handled" reads `delivered_hashes`; the
   wake is the `Waker` cursor. The pane bb-verbs (`bb append/list/watch/receipt`)
   become RPCs to the daemon's `Bus`. Outcome: the silence-incident and
   ack-runaway classes go away structurally; no compaction thresholds to tune.
   **Effort: a few days (process-boundary wiring exists). Value: kills two scar
   classes.**

3. **ToolGateway gating one tool** *(medium ratio, proves the seam)*. Pick one
   buildr tool-call (say, commit, currently `guard-commit.py`) and route it
   through `ToolGateway::invoke` with a `ToolGrant` mandate instead of the hook.
   One policy object replaces hook-copy + CI-copy, ending the drift class
   (`guard-commit.py:87-95`). Outcome: a worked demonstration of the one-seam,
   with a receipt. **Effort: medium (needs the SDK runtime in-process). Value:
   proves the ADOS thesis on a real tool.**

4. **Confined-PD for local-swarm agents** *(local-dev only)*. Use
   `sandbox.rs` + `host_pd.rs` to confine agents spawned by `apps/sandbox-bridge`
   on macOS/Linux. Makes the claims-fence physical, not advisory, for local runs.
   **Effort: medium, Unix-only. Value: real isolation where the OS allows it.**

5. **A receipt log behind one builders.dev surface** *(direction-setting)*. Put
   a dregg-as-a-service worker behind the council-artifact write path; every
   council verdict gets a `TurnReceipt`. Outcome: one surface proves caps+receipts
   in the SaaS before any broad migration. **Effort: larger (CF↔Rust seam).
   Value: the SaaS-side beachhead.**

---

## §7 — the realistic Fork-B path ("mount herdr on dregg")

Fork B is not a rewrite of herdr; it is *replacing herdr's home-grown substrate
with the verified one, one organ at a time*, in the order above. The sequence
that gets there without a big-bang:

1. **Substrate swap (slices 1–2).** The recovery monitor + `Bus` replace the two
   most scar-prone home-grown subsystems (restart-loop, spool). herdr's TUI,
   panes, RSH, packs are untouched. After this, buildr's *comms and recovery* are
   the verified form; everything else is as-is.

2. **Seam swap (slice 3).** RSH PreToolUse gates migrate, one verb at a time, to
   `ToolGateway` mandates. The RSH layer becomes the *authoring* surface for
   mandates (R/S still inject context; H delegates to `deleg_admit`). The
   per-harness drift class dies because there is one predicate. This is where
   buildr stops being "advisory hooks over a harness" and becomes
   "cap-gated turns with a harness UI."

3. **Confinement (slice 4).** Agents run as confined host-PDs; the claims-fence
   is physical. herdr becomes the *cockpit* over a confined agent fleet — which
   is precisely the deos "agent-activity Surface cell" vision
   (`HERMES-INTEGRATION.md:9-12`): the running loop renders as a cap-gated surface.

4. **SaaS convergence (slice 5).** builders.dev adopts the same receipts/caps on
   one surface, and buildr+builders.dev share *one* verified substrate: buildr is
   the local cockpit, builders.dev is the hosted fabric, both speaking caps and
   receipts. This is the n=1 firmament collapse — one cap across distance
   (local pane ↔ hosted agent ↔ surface).

The through-line: **every Fork-B step replaces an unverified buildr asset with
its already-built verified dregg twin, and each step is independently valuable
(it kills a named scar) — so the path is a sequence of wins, not a leap of
faith.** The grand "mount herdr on dregg" is the *sum* of slices 1–5, never a
prerequisite for any one of them.

---

## Appendix — fit-map index (need → piece → file:line)

| # | buildr/builders need | dregg piece | dregg file:line | buildr/builders file:line |
|---|---|---|---|---|
| 1 | queued-vs-handled / silence-incident | `Bus` `is_handled` (witness ≠ promise) | `captp/src/data_plane.rs:249`, `:380`, `:627` | `herdr/src/a2a_spool.rs:58,66-100` |
| 2 | 15h wedge (assertion-over-artifact) | recovery monitor `RecoveryNotHolding` | `sel4/dregg-firmament/src/recovery_monitor.rs:100-105,162,178,194` | restart-loop reflex (no durable home); `agent_resume.rs`, `rules/dev-process.md` |
| 3 | claims-fence / agent isolation | confined PD + sandbox | `sel4/dregg-firmament/src/sandbox.rs:64-73`, `host_pd.rs:99-122` | `agents/claudecode/hooks/guard-claims-fence.py`; INTEGRATIONS.md P1 |
| 4 | tool-call/verdict seam, gate drift | ToolGateway `deleg_admit` (two surfaces) | `sdk/src/tool_gateway.rs:29-46,125`; `metatheory/Dregg2/Apps/ToolAccessDelegation.lean` | `agents/claudecode/hooks/guard-commit.py:87-95`; `workers/budget`, `mcp_keys` D1 |
| 5 | auth/audit/multi-tenant/data-plane | caps / receipts / cells / `Bus` | `SESSION-LOGIN.md`; `data_plane.rs:366`; `HERMES-INTEGRATION.md` | OAuth+JWT+KV; Analytics Engine; team-scoping; CF Queues |
