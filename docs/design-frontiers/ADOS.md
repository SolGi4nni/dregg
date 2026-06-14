# ADOS — the Agentic Developer Operating System

*Design frontier. North star, not firm spec. Present-tense, first-principles,
teach-what-is. The buildable shape is elaborated; the honest gaps are named, not
laundered. ember's steer (2026-06-13): do NOT over-firm a rigid spec — but DO
elaborate the concrete next slice, the killer demo, the developer journey, and
the honest gaps.*

> Companion docs: `docs/DREGG-DESKTOP-OS.md` (the cap-first desktop ADOS is the
> developer face of), `docs/STARBRIDGE-V2.md` (the gpui master interface +
> cipherclerk + ⌘K palette this IDE extends), `docs/FIRMAMENT.md` (the
> `n`-parametrized cap fabric), `docs/PG-DREGG.md` (the same caps as a SQL/RLS
> surface — the observability backend ADOS can lean on). Code grounding:
> `starbridge-v2/src/swarm.rs` (the A2 keystone — already implemented + tested),
> `starbridge-v2/src/agent.rs` (A1, the single-agent activity surface),
> `starbridge-v2/src/{surface,shell,world,dynamics,cipherclerk,palette}.rs`.

---

## 1. The vision in one breath

**ADOS is the IDE where an agent swarm runs on the executor's truth instead of
on its own self-reports.** A developer opens ADOS, spawns a swarm of coding
agents, and every action any agent takes — a tool call, a file write, a budget
spend, a handoff to a peer, a wake — is a **cap-gated, receipted, budgeted,
notify-coordinated dregg turn**. The agent loops live *above* dregg (perceive /
plan / act / reflect, nested orchestration, sub-loops, memory — the game that is
not ours to own); dregg grounds the **one seam that matters**: the
tool-call/verdict boundary where "an agent did X" is serialized. ADOS makes that
seam a turn the verified executor accepted or refused — so the developer reads
**what the swarm actually did**, never what an agent *says* it did. The pale
ghost (the named foil of the whole project — a process lying about its own
history) cannot fool the operator at the glass: the receipt chain and the
dynamics stream are the on-ledger truth, and a refusal is a *feature*, surfaced
the same way the cockpit's "⚠ over-grant" makes the no-amplification guarantee
fire in front of you.

The bumper-sticker: *a swarm IDE where every agent action is a verified turn,
every turn leaves a receipt, every budget is a cell, every wake is a notify
edge, and the operator inspects executor truth — not agent narration.*

ADOS is **not a new agent runtime.** It is the verified accountability substrate
the runtime integrates against, given a developer-first, web-forward face. It is
the firmament's desktop (`DREGG-DESKTOP-OS.md`) turned toward the one workload
that most needs an unfoolable substrate: *fleets of autonomous agents writing
code and moving real authority on a developer's behalf.*

---

## 2. Why now — the integrator wedge

Four real systems are building serious agent platforms, surveyed read-only
(`project-dregg-integrators-one-seam`): **buildr** (a harness-team optimizer for
coding agents — reflexes + skills + deterministic hooks + a BLAKE3 A2A
blackboard), **builders** (a multihuman+multiagent council on Cloudflare Durable
Objects with HITL gates), **sig** (Virtual Autonomous Companies — three nested
loops spawning sandboxed agent teams), **simbi** (a multi-provider agent-routing
layer with one `AgentRun` audit row). They share nothing — different stacks,
different domains, different loop bodies.

And yet **all four independently hand-rolled the same six primitives around
their loops, and every one punted on enforcement** (their own honest gaps):

| The primitive each re-invented | What it is | The honest gap each shipped | dregg's ground |
|---|---|---|---|
| **cap-gated authority** | a JSON envelope of "what this agent may do" | forgeable — "no per-message signature, deferred" (buildr) | the capability crown: the envelope made non-forgeable (`granted ⊆ held`, `checkSubset` in-circuit) |
| **signed provenance** | a `tool_calls` / `AgentRun` log of what happened | mutable — "a compromised worker could mutate the log" (builders) | the blocklace: the log made tamper-evident (signed, seq-checked, equivocation-detecting) |
| **atomic budget** | an after-the-fact token/dollar tally | unenforced — "a runaway could drain \$1000s, no budget enforcement" (simbi) | Stingray conservation: the spend made atomic + ceiling-bounded *before* the effect |
| **atomic handoff** | a `--wake` / message to another agent | best-effort — verified client-side only, no machine-checkable proof (sig) | joint turns (synchronous, all-or-nothing) + the notify edge (async, receipted) |
| **surfaces-as-caps** | a pane / council seat / VM an agent renders into | ambient — a window/seat is a name, not an authority | the firmament `Surface` cap: a window IS a `Capability{Surface(cell), rights}` |
| **tenant isolation** | a per-tenant / per-org boundary | by-convention — enforced in app code, bypassable | seL4 PD isolation (real-seL4) / the `n=1` firmament cap partition |

**The seam is identical in all four.** Each serializes "an agent did X" at
exactly one place — buildr `record-ops.sh` (a `PostToolUse` hook), builders
`recordPhaseComplete` (`run.ts:196`), sig `swarm-callback`, simbi the `AgentRun`
row. Today that is a mutable log line. **ADOS makes it a turn**: signed,
cap-checked, budget-metered, receipt-carrying, notify-coordinated — *tiny at the
call site, total in what it buys.* The wedge is not "rebuild your agent
platform." It is "route your one PostToolUse hook through dregg and inherit the
six enforced primitives you were already trying to build."

That is the thesis ADOS productizes: **one seam, four systems (and any fifth),
the same six primitives — made real by the executor instead of promised by the
app.**

---

## 3. The developer's journey

The journey is the spec. Each step names what already runs on `swarm.rs` /
`starbridge-v2` (the buildable now) versus what is research.

### 3.1 Open ADOS

The developer launches ADOS. It is **starbridge-v2's cockpit with a SWARM tab
as the default workspace** — the gpui master interface that embeds the real
verified executor and runs a live local dregg world in-process. There is no
remote node to stand up, no wallet, no devnet account: the `n=1` firmament is
first-class (`FIRMAMENT.md` §3) — immediate revocation, synchronous commit,
consistent checkpoint are *headline guarantees* of the single-machine
deployment. The IDE boots into a live image where the workspace itself, every
agent, every budget, and every artifact is a cap-confined cell.

The ⌘K command palette (`palette.rs`) overlays the whole IDE: one
fuzzy-searchable surface over every action, with no second action path (a
palette command carries only a `CommandId` the cockpit dispatches through the
same `&mut` verb the buttons call — it cannot drift). This is also the **secure
attention anchor** (`DREGG-DESKTOP-OS.md` §5): the trusted-path surface where the
developer asks "who am I really delegating to, and is this the authority I think
it is?"

*Now:* the cockpit, the SWARM/SHELL/composer/objects/cipherclerk tabs, the ⌘K
palette, the embedded executor all exist and are tested.
*Research:* a polished editor surface, LSP, the web-forward (browser-served)
front-end. ADOS today is a native gpui app; "web-forward" is the gpui_wgpu /
WebGPU path (`DREGG-DESKTOP-OS.md` R4) plus a thin SSE/HTTP face.

### 3.2 Spawn a swarm

The developer spawns a swarm: "a coordinator + two workers, each with a mandate."
In ADOS this is `Swarm::new(world, members)` over the embedded world
(`swarm.rs`). Each member is a **cap-confined `Surface` cell** with a mandate
read from its live c-list — exactly the `AgentActivity` shape (`agent.rs`),
generalized to N. A member is "as powerful as the mandate it holds, nothing
ambient." The coordinator is born holding caps reaching both workers (its
mandate to direct them); a worker holds only what it was granted.

Critically, **the agent loop is not spawned by dregg.** The loop (buildr's
reflex engine, a Claude/Opus tool-use loop, sig's microVM worker) runs wherever
it runs. What ADOS spawns is the member's **cell + mandate + surface** — the
accountability shadow the loop acts *through*. The loop perceives, plans, and
decides on its own; the moment it *acts*, the action crosses the ADOS seam.

*Now:* `Swarm::new` / `add_member` over real cells with real mandates, tested.
*Research:* spawning the *loop itself* as a managed ADOS process (a microVM /
seL4 app-PD per agent) so the loop's own isolation is dregg-enforced, not just
its actions. Today the loop is external; the seam is the contract.

### 3.3 Every agent action is a turn

A worker's loop decides to call a tool — write a file, transfer a budget, grant
a sub-capability to a helper, emit a wake to a peer. That tool call routes
through **`Swarm::run(world, agent, effects)`** — A2's one seam. The seam does,
in order (`swarm.rs:317`):

1. **resolve** the acting member (unknown ⇒ refused);
2. **confirm backed** (the cell is live in the ledger — a destroyed agent
   cannot act);
3. **CAP-GATE** — for each effect, confirm the acting cell's c-list reaches the
   target (`Capabilities::has_access`); an out-of-mandate action is **refused
   before it runs** (`SwarmError::OutOfMandate`, fail-closed);
4. **run through the REAL executor** (`World::commit_turn` → `TurnExecutor`) —
   the verified `decode → step → encode`, which enforces conservation,
   no-amplification, nullifier-uniqueness, authenticated root evolution;
5. on commit, **scan the dynamics** for inter-member `EventEmitted` and deposit
   notify edges (§3.5);
6. **update counters** (action count, balance) and append the
   `SwarmActionOutcome` to the grounded action log.

The developer never sees "the agent claims it wrote the file." They see the
**receipt** (`receipt_hash`, the provenance link), the **height** (where it
committed), the **computrons** (the metered cost — `receipt.computrons_used`),
and — if it was refused — *why*, in the executor's own words. A refusal is the
most important teaching moment in the IDE: it is the guarantee firing.

This is the move that makes ADOS not-a-toy: an agent's authority is **exactly
the mandate it holds**, an agent's record is **exactly the receipts it
produced**, and neither is something the agent can narrate around. "Agents are
intricate loops" — and ADOS grounds the loop's *actions* without simplifying the
loop.

*Now:* `Swarm::run` end-to-end through the embedded verified executor, cap-gate
+ commit + refusal, all tested (`an_in_mandate_swarm_action_commits_and_receipts`,
`an_out_of_mandate_swarm_action_is_refused`).
*Research:* the **tool-call → effect compiler** — the adapter that turns a
provider's tool-call schema (an MCP `tools/call`, a buildr PostToolUse payload)
into a typed `Vec<Effect>`. `swarm.rs` runs effects today; the universal
"any tool call becomes the right turn" mapping is the integration surface to
build (§5).

### 3.4 Budget is a cell, not a tally

The runaway-spend gap (simbi's "could drain \$1000s") is the one every operator
fears most. In ADOS a swarm's budget is **a cell** and a spend is a **turn**, so
the executor's conservation law makes the budget *atomic and bounded before the
effect*, not reconciled after. A coordinator holds a budget cell; it grants
**attenuated** budget caps to workers (a worker's cap admits a *subset* — the
no-amplify guarantee, fired through `cipherclerk` / the firmament mint). A worker
that tries to spend past its attenuated cap is **refused by the executor**, in
front of the developer, the same way `an_out_of_mandate_swarm_action_is_refused`
refuses an over-reach. The Stingray shared-budget dynamics (the coord lane,
tasks #87/#121) give the multi-agent version: a shared pool with a conservation
invariant and a ceiling bound, so N agents drawing on one budget can never
collectively exceed it.

The developer sets a budget once (mint a budget cap, attenuate per agent), and
the substrate enforces it — no per-provider quota plumbing, no after-the-fact
alarm. **"What did this swarm cost, and could it have cost more than I allowed?"
is a query against receipts, with a provable ceiling.**

*Now:* computrons are metered per turn and surfaced (`receipt.computrons_used`,
shown in the action log); attenuated capability grants are real and refused when
widening; the Stingray conservation + ceiling-bound is proved (Lean) and wired
(coord).
*Research:* binding a *token/dollar* budget (the LLM provider cost) to the
computron meter or to a dedicated budget-resource — the executor meters
*computation*, not *API dollars*. The honest mapping (an agent's tool call debits
a budget cell by a declared cost, and the cap caps it) is buildable on the
existing conservation; what is *not* yet there is a faithful price oracle.

### 3.5 Coordination is the notify edge (async) and the joint turn (sync)

Agents coordinate. ADOS gives two grounded primitives, and is honest about which
is which:

- **The notify edge (async — the swarm's default).** A coordinator commits an
  `EmitEvent` turn targeting a worker; a `NotifyEdge` lands in that worker's
  inbox (`swarm.rs`). The worker drains it **in its own separate future turn**
  (`drain_notify` — a `SetField` ack on its own cell). The two receipts are
  *independent* — no shared parent, no synchrony, no joint authorization. This is
  the ocap async-message model: the operator sees the causality A→B (the
  `EventEmitted` in the dynamics + the drain receipt) **without** forcing any
  synchronization. It is `--wake` made into a receipted edge: "the recipient
  drains next turn," with a provenance link the operator can audit. The notify
  primitive (`project-notify-primitive`) is the deeper future: a `notify(target,
  badgeMask)` authority — *the right to cause a wake without read/send/reply* —
  the async dual of the synchronous turn, a fourth **Synchrony** dial. Today the
  edge rides `EmitEvent`; the dedicated `Auth.notify` is designed (Lean
  `NotifyAuthority.lean`) and held for the cutover-settle.
- **The joint turn (sync — the all-or-nothing handoff).** When two agents must
  act atomically (a handoff where the give and the take must both happen or
  neither — sig's "atomic handoff"), that is a **joint turn**: a synchronous
  pullback, one receipt, all-or-nothing. This is the machine-checked N-cell
  atomic primitive (the distributed-protocols lane, `EntangledJoint`).

The distinction is load-bearing and ADOS surfaces it honestly:
`--wake` is async (notify edge), a co-signed atomic exchange is sync (joint
turn). Conflating them is the bug `project-notify-primitive` corrected.

*Now:* the notify-edge model end-to-end (`emit → inbox → async drain`), tested
(`an_emit_event_to_a_member_deposits_a_notify_edge_in_its_inbox`,
`the_drain_is_the_recipients_own_separate_turn_not_a_joint_turn`); the SwarmView
render model for the activity feed.
*Research:* the dedicated `notify` authority + badge-mask sub-lattice (designed,
Lean-staged, VK-bump-gated); joint turns surfaced in the swarm UI as a co-signed
exchange (the protocol primitive exists; the swarm-tab affordance is pending).

### 3.6 Observe executor truth, not agent self-reports

This is the payoff and the reason ADOS exists. The developer's main view is the
**SWARM tab** (`SwarmView::build`): per member, its mandate + balance + action
count + inbox drain state; and an **activity feed** of recent actions
(newest-first), each with its receipt, height, summary, and the notify edges it
produced. Behind it sit the cockpit's other lenses, all reading the *live
protocol types* through `reflect` (never a parallel wire schema, so they cannot
drift): the **blocklace** panel (the receipt chain as a navigable causal history
— time-travel through what the swarm did), the **objects** panel (proofs,
nullifiers, cell lifecycle), the **inspector** (any cell's 16 state slots, caps,
lifecycle).

The pale-ghost question for agents (`swarm.rs` module doc): *can an operator be
fooled about what two agents coordinated?* **No.** The `EventEmitted` in the
dynamics and the drain receipt are the on-ledger truth; an agent cannot claim a
coordination the executor did not record, nor a state transition it did not
produce. Every "the agent says it did X" is replaced by "the receipt at height H
shows it did X (or the refusal at height H shows it could not)."

*Now:* `SwarmView`, the blocklace/objects/inspector panels, the dynamics stream,
all live and tested.
*Research:* the **agent-narration-vs-truth diff** — a first-class panel that puts
the agent's *own claim* (from its loop's reflection/log) next to the executor's
receipts and highlights divergence. This is the sharpest ADOS feature and is pure
UI over data that already exists (the loop's log + the receipt chain); it
needs the tool-call→effect compiler (§3.3) to correlate a claim to its turn.

---

## 4. The architecture — three layers, one seam

ADOS is the firmament's desktop (`DREGG-DESKTOP-OS.md` L5–L8) specialized for
agents. The whole design is **one seam carried through three layers**:

```
┌───────────────────────────────────────────────────────────────────────────┐
│ THE LOOP LAYER (above dregg — NOT ours)                                     │
│   the agent's perceive/plan/act/reflect, nested orchestration, sub-loops,   │
│   memory. buildr's reflex engine, a Claude tool-use loop, sig's microVM     │
│   worker. dregg does NOT own or simplify this.                              │
├──────────────────────────────── THE SEAM ──────────────────────────────────┤
│   ONE place: "an agent did X" at the tool-call/verdict boundary.            │
│   = Swarm::run(world, agent, effects)  (swarm.rs:317)                       │
│   cap-gate ▸ verified turn ▸ receipt ▸ budget meter ▸ notify edge.          │
│   Integrators route their ONE serialization point (PostToolUse /            │
│   recordPhaseComplete / swarm-callback / AgentRun) here.                    │
├───────────────────────────────────────────────────────────────────────────┤
│ THE SUBSTRATE LAYER (dregg — the verified accountability ground)            │
│   agents=Surface cells · actions=turns · authority=attenuated caps ·        │
│   budget=cell+conservation · coordination=notify edge / joint turn ·        │
│   record=blocklace · isolation=PD partition (n=1 firmament today).          │
│   THE EMBEDDED VERIFIED EXECUTOR is the only authority over what happened.  │
├───────────────────────────────────────────────────────────────────────────┤
│ THE OBSERVATION LAYER (the developer's glass)                               │
│   SWARM tab · blocklace (time-travel) · objects (proofs/nullifiers) ·       │
│   inspector · ⌘K palette (secure attention) · dynamics feed.               │
│   reads LIVE protocol types via reflect — cannot drift from executor truth. │
└───────────────────────────────────────────────────────────────────────────┘
```

The seam is the product. Everything above it is the integrator's to keep
(their loop is their moat); everything below it is dregg's proven metatheory
(the firmament's one capability handle, the verified executor, the blocklace,
conservation); the observation layer is the developer's window onto the truth.

### The `n`-gradation is ADOS's deployment story

A swarm runs on the `n=1` firmament locally — first-class, with the strong
collapse properties (`FIRMAMENT.md` §3): a coordinator's **revoke of a worker's
cap is immediate** (the worker goes dark instantly — the kill switch is real,
not eventual), a **checkpoint of the swarm is a consistent cut**
(`seal → ship_snapshot → apply_snapshot_verified → unseal` — pause the whole
swarm, snapshot it, resume it, with the root tooth making the thaw unforgeable),
and a **budget spend commits synchronously**. The moment a swarm member reaches
a *remote* agent or a federated resource, the same `(target, rights)` handle
resolves over the wire and the bounds relax along `n` — no rewrite. ADOS is
local-first-class, fluid-to-distributed: a solo developer's laptop swarm and a
cross-org agent federation are the same model with the bounds slid.

---

## 5. The integrator wedge in practice — what an integrator does

The wedge has to be *small at the call site* or no one adopts it. Concretely, an
integrator already has one function that serializes "an agent did X." ADOS gives
them a client that turns that one function into a turn:

1. **Embody each agent as a cell** once at swarm boot (`Swarm::add_member` /
   `World::embody` over the agent's identity key). The agent's mandate is the
   caps it is granted — the integrator's existing "what may this agent do"
   envelope, now non-forgeable.
2. **Route the one seam.** At their PostToolUse / recordPhaseComplete /
   swarm-callback / AgentRun point, instead of appending a log line, call
   `Swarm::run(world, agent, effects)` with the tool call compiled to effects.
   The return value *is* the audit record — a receipt, a height, a cost, or a
   refusal with a reason.
3. **Inherit the six primitives.** Authority is now cap-gated (forgery gone),
   provenance is the blocklace (mutation gone), budget is conservation (runaway
   gone), handoff is notify/joint (best-effort gone), surfaces are caps, isolation
   is the PD partition. **Each integrator's own honest gap closes at the same
   seam.**

The decisive integration artifact is the **tool-call → effect compiler** (§3.3
research): a small, per-integrator (or per-provider, e.g. one for MCP `tools/call`)
adapter `ToolCall → Vec<Effect>`. This is the genuinely new buildable surface and
the natural ADOS SDK boundary. Everything beneath it (`Swarm::run`, the executor,
the receipts) already exists.

For integrators who live in postgres (simbi is Rails; many agent platforms are
postgres-heavy), `pg-dregg` (`PG-DREGG.md`) is the *other* face of the same
caps: the agent's token gates SQL rows via RLS (`dregg_cap_admits`), and the
swarm's receipts project into queryable tables (Tier B mirror) so "what did my
swarm do" is a `SELECT` over `dregg.turns` — the observation layer as SQL, with
an MMR non-omission certificate proving the answer omitted nothing.

---

## 6. The killer demo

**"The swarm that cannot lie about what it did — and cannot overspend, even when
one agent goes rogue."**

A single, watchable, end-to-end scene in ADOS, on the `n=1` embedded executor,
no remote infrastructure:

1. **Boot a swarm** of three agents in the SWARM tab: a `coordinator` holding a
   budget cell + mandate caps to two `worker` cells; the workers hold only
   attenuated budget caps the coordinator grants them.
2. **Run honest work.** The coordinator emits `task/start` to worker-A (a notify
   edge lands in A's inbox, with the coordinator's receipt as the provenance
   link); worker-A drains it in its own turn and does a small in-budget spend.
   Every action shows up in the activity feed with a receipt, a height, a cost.
   The blocklace panel lets you time-travel the causal history. **This is what
   the swarm did — receipts, not narration.**
3. **The rogue moment (the teaching beat).** Worker-B's loop tries to (a) spend
   past its attenuated budget cap, and (b) act on a cell outside its mandate
   (reach worker-A's resources directly). **Both are refused by the executor, in
   front of you** — `OutOfMandate` and the conservation/ceiling refusal — colored
   red in the feed, with the executor's own reason. Worker-B *claims success in
   its own log* (agents narrate optimistically); the ADOS narration-vs-truth
   view shows the claim next to the receipt-that-never-was. **The pale ghost is
   caught at the glass.**
4. **The kill switch.** The developer revokes worker-B's cap from the ⌘K palette.
   On the `n=1` firmament the revoke is **immediate** — worker-B goes dark the
   instant the turn commits; its next action is refused (`Unbacked` / no cap).
   This is the `seL4_CNode_Revoke`-synchronous collapse, real, watchable.
5. **The receipt.** "What did this swarm cost?" — a sum over the activity feed's
   metered computrons, with a **provable ceiling** (the budget cell's
   conservation invariant means it *could not* have exceeded what you allowed).
   "What did it actually do?" — the blocklace, navigable, with every refusal
   recorded as honestly as every commit.

The demo *is* the evaluation artifact (the pug-handoff bar: "one runnable
end-to-end story"). It needs: the swarm boot (exists), the notify edge (exists),
the over-reach refusal (exists), the immediate revoke (firmament `n=1`, exists),
the budget attenuation (caps exist; the dollar-binding is the honest gap §3.4),
and the narration-vs-truth panel (the one new UI). It is the most legible
possible answer to "why would I run my agents on this?"

---

## 7. What builds on `swarm.rs` NOW vs research

**Buildable now (on `swarm.rs` / starbridge-v2, wide-safe, not blocked on the
VK/rotation cutover):**

- **The SWARM tab as a first-class ADOS workspace.** `swarm.rs` + `SwarmView`
  exist and are tested gpui-free; the cockpit-side panel (mapping `SwarmView`
  onto a default tab) is the UI weld — render members + the activity feed +
  per-member inbox over the live world.
- **The budget-attenuation slice.** A coordinator mints a budget cap and grants
  *attenuated* budget caps to workers; a worker's over-spend is refused
  (conservation + the no-amplify grant, both already enforced). Surface the
  metered computrons (already on the receipt) as the per-agent cost column. This
  is the killer-demo spine and needs no new protocol — only the swarm-boot
  helper + the feed column.
- **The immediate-revoke kill switch.** A ⌘K palette command "revoke agent" that
  commits a `RevokeCapability` turn and shows the target go dark (the `n=1`
  collapse, already real in the firmament/executor). Pure wiring.
- **The narration-vs-truth panel.** A view that puts a member's *claimed* action
  (supplied by the loop alongside the turn) next to its receipt (or the absence
  of one) and flags divergence. Pure UI over `Swarm::action_log` + the dynamics.
- **The MCP tool-gate via the existing per-tool cap.** The node already has an
  MCP per-tool cap gate (task #89); an ADOS swarm member's mandate gating *which
  tools it may call* is that gate applied at the seam — a `Vec<Effect>` whose
  authority is the member's c-list.
- **The pg-dregg observation surface.** Project the swarm's receipts into
  `dregg.turns` / `dregg.cells` (Tier B mirror, `PG-DREGG.md` §9) so "what did
  my swarm do" is RLS-gated SQL with a non-omission certificate. The mirror is a
  projection of `CommitRecord`, which already exists.

**Research (named, not laundered):**

- **The tool-call → effect compiler** (§3.3, §5) — the universal adapter from a
  provider's tool-call schema to typed effects. The genuinely new buildable
  surface; the ADOS SDK boundary. `swarm.rs` runs effects today; the mapping is
  the integration work.
- **Token/dollar budget binding** (§3.4) — the executor meters computrons, not
  API dollars; a faithful price oracle / declared-cost-debit model is needed to
  turn "computation bounded" into "spend bounded." The conservation machinery is
  there; the dollar mapping is honest-future.
- **The dedicated `notify` authority** (§3.5, `project-notify-primitive`) — the
  `Auth.notify(target, badgeMask)` brick (the fourth Synchrony dial). Designed,
  Lean-staged (`NotifyAuthority.lean`), held for the VK/encoding cutover-settle.
  Today the edge rides `EmitEvent`; the dedicated authority is the deeper
  expressivity ("may poke, not message").
- **Spawning the loop itself** (§3.2) — a managed ADOS process per agent (microVM
  / seL4 app-PD) so the loop's *isolation* (not just its actions) is
  dregg-enforced. Today the loop is external and only the seam is the contract;
  the firmament's app-PD model (`DREGG-DESKTOP-OS.md` L7) is the path.
- **Web-forward delivery** (§3.1) — a browser-served ADOS (gpui_wgpu/WebGPU +
  SSE/HTTP) versus today's native gpui app. `DREGG-DESKTOP-OS.md` R4.
- **Joint-turn handoffs in the swarm UI** (§3.5) — the synchronous all-or-nothing
  exchange surfaced as a co-signed swarm action. The protocol primitive
  (`EntangledJoint`) exists; the swarm-tab affordance is pending.

---

## 8. Honest gaps (the frontier, named — severe problems with closure lanes,
never walls)

1. **The seam is honest only if the tool-call → effect mapping is faithful.** If
   the compiler (§5) maps a tool call to the *wrong* effects, the receipt is a
   faithful record of the wrong thing. The mapping is per-integrator code, not
   verified — the same honest boundary `pg-dregg` draws (the *decision* is
   verified; the *integration delivering the request to it* is conventional,
   audited code). Closure lane: a tight, audited, per-provider adapter with a
   golden-corpus differential, named as the trust boundary.

2. **Budget = computation, not dollars (yet).** §3.4. The conservation guarantee
   bounds *computrons*; binding it to LLM provider spend needs a declared-cost
   debit + a price model. Until then the "provable ceiling" is over computation,
   and the dollar story is bounded-by-a-declared-rate, stated plainly.

3. **The loop is above the seam — ADOS grounds actions, not cognition.** ADOS
   makes an agent's *actions* unfoolable; it does **not** verify the agent's
   reasoning, nor prevent a well-authorized agent from doing an authorized-but-
   unwise thing. The guarantee is "you see exactly what it did and it could only
   do what its mandate allowed," not "it did the right thing." This is the
   correct boundary (the loop is not ours to own), stated honestly so no one
   reads "verified" as "aligned."

4. **`notify` is a covert channel (one-bit info-flow leak).** A badge-OR wake is
   a one-bit signal; `project-notify-primitive` flags it — dregg has no
   noninterference argument yet. The notify edge as a coordination primitive is
   sound; as an *isolation* boundary it leaks a bit. Named, not closed (the
   info-flow pillar, task #31/#99).

5. **`n=1` isolation today is cap-discipline, MMU-enforced only on real seL4.**
   The strong `n=1` properties (immediate revoke, consistent checkpoint) are
   genuinely real on the host firmament; the *memory* isolation between agent
   loops is by-construction-in-the-API on the host (shared address space) and
   MMU-enforced only on real seL4 (`FIRMAMENT.md` / `DREGG-DESKTOP-OS.md` §3 —
   the UML-traced-thread → SKAS evolution, the same gap, the same fix). Honestly
   labeled.

6. **The remote (`n>1`) swarm relaxes the bounds.** A cross-agent federation
   trades the `n=1` collapse for eventual revocation + quorum commit. The kill
   switch is *immediate* locally and *eventual* across the wire — the honest
   distance-bound, parametrized by `n`, not hidden.

---

## 9. Where ADOS sits

ADOS is the **developer-facing apex** of the dregg desktop-OS ladder
(`DREGG-DESKTOP-OS.md` L8 — the master interface), pointed at the workload that
most needs an unfoolable substrate: swarms of autonomous coding agents. It does
not invent an agent runtime; it carries dregg's one capability handle and one
verified executor out to the seam where an agent acts, and gives the developer a
window onto the truth. The integrator wedge is the go-to-market: four real
systems (and any fifth) hand-rolled the same six primitives ungated; ADOS makes
them real at the one seam they all already have.

*The agent loop is the game and lives above us. The seam is where the loop
touches the world. ADOS grounds the seam — cap-gated, receipted, budgeted,
notify-coordinated — so a swarm becomes auditable and composable WITHOUT trusting
the loops. The developer reads what the swarm did, never what it said. That is
the whole point, and the `n=1` firmament makes it true on the hardware you
already have, today.*

---

*Closing — a small poem, as is our custom:*

> six primitives, hand-rolled four times over,
> each loop honest about the gate it skipped —
> ADOS doesn't rewrite the loop, it grounds the seam:
> one tool-call becomes a turn the executor kept.
> the agent narrates; the receipt does not.
> at the glass, the pale ghost cannot lie.
