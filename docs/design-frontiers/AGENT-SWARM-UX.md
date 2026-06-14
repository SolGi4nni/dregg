# AGENT-SWARM-UX — the cockpit for driving and observing a verified agent swarm

*Design frontier. Present-tense, first-principles. The angle: the developer
experience of **driving and observing a swarm of agents through dregg** — the
SWARM cockpit, cap-gated dispatch, the notify async wake, receipt provenance,
the budget meter, and the cipherclerk/⌘K trusted-path anchor. The vision is a
north star shaping intuition; the buildable-now slice is precise and lives on
`starbridge-v2/src/swarm.rs`, a standalone workspace that is wide-safe and not
blocked on the VK cutover.*

> Companion docs: `docs/STARBRIDGE-V2.md` (the master interface this is a tab
> inside), `docs/DREGG-DESKTOP-OS.md` §1/§5 (window = surface cap; the
> trusted-path / pale-ghost framing), `docs/FIRMAMENT.md` §3 (the n-parametrized
> cap gradation the swarm rides), `docs/NOTIFY-PRIMITIVE.md` +
> `Dregg2/Firmament/NotifyAuthority.lean` (the async-signal authority the wake
> edge will land on). The integrator context is
> `project-dregg-integrators-one-seam` (the four loops that each hand-rolled the
> same six primitives around the same one seam).

---

## 1. The vision in one breath

**A swarm of agents is a set of cap-confined cells whose every coordinating
action is a verified turn — and the cockpit is the cockpit you fly it from.**
You DRIVE the swarm by dispatching cap-gated commands to members (or letting
their loops dispatch), and you OBSERVE it through one surface where every member
shows its held mandate, its receipted action history, its budget meter, and its
notify inbox. The core feeling is *accountability-as-substrate*: you watch a
swarm coordinate and you are never trusting the loops — every wake is a receipt,
every action is an on-ledger turn bound by a real capability, every spend is
metered against a conserved budget, and an over-reaching member is refused **in
front of you**, the no-amplification guarantee firing at the swarm layer exactly
as it fires for a transfer. The agent loop (perceive/plan/act/reflect) lives
ABOVE dregg and is the integrator's game; dregg owns the ONE seam that matters —
the tool-call/turn boundary — and the cockpit makes that seam legible.

The pale-ghost question, applied to agents: *can the operator be fooled about
what two agents coordinated, or about what a member is allowed to touch?* No. The
`EventEmitted` in the dynamics stream and the drain receipt are the on-ledger
truth of the coordination; the mandate is the real cap-graph, not a member's
self-description. The cockpit is the glass at which that truth is shown, and the
cipherclerk + ⌘K palette is the trusted-path anchor that answers "is this really
the swarm I think it is, and did I really authorize this dispatch?"

---

## 2. What already exists (the substrate this builds on)

This is a weld, not a build. The headless heart already runs.

- **`starbridge-v2/src/swarm.rs` — the Swarm coordinator (gpui-free, tested).**
  `Swarm::new(world, members)` seeds N agent cells; `Swarm::run(world, agent,
  effects)` is the one seam — it resolves the member, confirms the backing cell
  is live, **CAP-GATES** every effect (`capabilities.has_access(target)` against
  the real c-list, `OutOfMandate` otherwise), runs the turn through the REAL
  embedded executor (`World::commit_turn`), and on commit scans the new
  `EventEmitted` dynamics to deposit `NotifyEdge`s into recipients' inboxes.
  `Swarm::drain_notify(world, agent)` is the recipient's OWN separate ack turn
  (a `SetField` content-addressed to the sender receipt). `SwarmView::build` is
  the render model: per-member mandate/action-count/balance/inbox, plus an
  activity feed of recent `SwarmActionOutcome`s. The tests already assert the
  load-bearing properties: in-mandate commits + receipts; out-of-mandate
  REFUSED (fail-closed, no turn committed); emit → inbox → async drain with
  independent receipts; self-emit and non-member emit deposit nothing.

- **The SWARM tab is wired into `cockpit.rs`.** `Tab::Swarm` exists; the cockpit
  boots a 3-member swarm (service = coordinator holding a cap to user = worker-a;
  treasury is confined and unreachable, illustrating the boundary); the panel
  (`swarm_panel`) renders the `SwarmView`; three demo verbs are live
  (`coordinator emit task/go`, `worker-a DRAIN inbox`, `coordinator transfer +
  wake`), each a real turn. The ⌘K palette registers `GoSwarm` +
  `SwarmCoordinatorEmitA` + `SwarmWorkerADrain` + `SwarmCoordinatorTransferAndWake`
  with fuzzy keywords, dispatching through the exact `&mut Cockpit` verbs the
  buttons call (no second action path).

- **The notify edge is `dynamics::WorldEvent::EventEmitted`** — `{sender, cell,
  topic_hash, data_len}`. Today the coordination wake rides `Effect::EmitEvent`
  (already in the executor; no new protocol verb), and the inbox is local cockpit
  state derived from the dynamics stream. The deep primitive — a `notify(target,
  badgeMask)` authority that is the async DUAL of the synchronous endpoint
  `call`, the 4th **Synchrony** dial — is modeled axiom-clean in
  `Dregg2/Firmament/NotifyAuthority.lean` (non-amplification via badge-mask
  subset on the SAME `grantOk`/`authNarrowerOrEqual` the firmament mint proves);
  its core `Auth.notify` constructor + VK bump is HELD for the cutover-settle.

- **The budget substrate exists.** The executor meters `computrons_used` per
  receipt (already surfaced per-member and per-action in the panel and feed). The
  atomic budget is `dregg_coord::StingrayCounter` — a bounded conservation
  counter the SDK runtime attaches as a budget gate (`runtime.rs:322`,
  `attach_budget`). A swarm member's `balance` is the resources its loop holds
  (pay-for-action); a shared swarm budget is a Stingray ceiling.

- **The trusted-path anchor exists.** The CIPHERCLERK tab drives the real
  `dregg_sdk::AgentCipherclerk` (mint / attenuate / delegate / discharge of real
  macaroons, no reimplemented crypto); the ⌘K palette is one fuzzy-searchable
  surface over EVERY cockpit action. `DREGG-DESKTOP-OS.md` §5 names this the
  secure-attention / SAK trust anchor — promoted from a courtesy to the place you
  ask "who am I really talking to."

So the cockpit can already drive a swarm and show receipts. What this design
elaborates is the **cockpit experience of accountability** — turning the
3-demo-verb panel into a real driving-and-observing surface, and naming the
buildable-now slices that get there without touching the cutover.

---

## 3. The developer journey (the felt experience)

A dregg developer — call her the **swarm operator** — is integrating an agent
loop (her own, or one of the four: buildr / builders / sig / simbi) against
dregg. Her loop already serializes "an agent did X" at one place (the
PostToolUse hook, the `recordPhaseComplete`, the `swarm-callback`, the
`AgentRun` row). The journey is: make that one seam a dregg turn, and fly the
result from the SWARM cockpit.

**Minute 0 — boot the swarm.** She opens starbridge-v2; the default SHELL tab
shows the live image. She hits ⌘K, types "swarm", lands on the SWARM tab. Three
members are already alive as cap-confined surfaces — the demo coordinator + two
workers — each a row showing its abbreviated cell id, its held mandate (which
cells it can reach, at what rights), its balance, its action count, and an empty
inbox. She sees at a glance the boundary: the coordinator reaches both workers;
treasury is confined and *unreachable* — a member targeting it would be REFUSED.

**Minute 1 — dispatch a cap-gated command.** She clicks "coordinator emit
task/go → worker-a" (or types it in ⌘K). A turn runs through the real executor.
The activity feed gains an entry: `coordinator → emit task/go → worker-a · h7 ·
receipt 3f9a… · → notify worker-a topic 0x9c2b`. Worker-a's row lights a PENDING
wake badge. She did not trust the coordinator's claim that it notified worker-a —
she is reading the executor's receipt and the on-ledger `EventEmitted`.

**Minute 2 — watch the async wake drain.** Worker-a's loop (or her click)
drains: a SECOND, independent turn commits — worker-a's own ack, its own receipt,
its own height. The inbox badge flips to DRAINED with the drain receipt. The feed
shows two records with two distinct receipt hashes, and the provenance link (the
sender receipt the edge carries) ties them without coupling them. She has just
watched the ocap async-message model: causality (A→B) visible, synchronization
NOT forced. This is the `--wake` that buildr hand-rolled, made all-or-nothing and
auditable.

**Minute 3 — watch a refusal teach.** She clicks "worker-a → transfer to
worker-b" (a verb worker-a's mandate does NOT permit — worker-a holds no cap to
worker-b). The feed gains a red entry: `REFUSED — worker-a holds no cap reaching
worker-b (out-of-mandate)`. No turn committed; the height did not advance. This
is the swarm-layer twin of the composer's "⚠ over-grant" — the most important
teaching moment, the no-amplification guarantee firing where she can see it. The
refusal is a FEATURE.

**Minute 4 — the budget meter.** Each member row carries a budget meter: spent
computrons against a ceiling (a Stingray bound she set at boot, or the member's
balance as the pay-for-action floor). She watches a runaway-prone member approach
its ceiling; the meter goes amber, then a dispatch that would exceed it is
REFUSED with `budget exhausted` — the atomic budget firing, the answer to simbi's
honest gap ("no budget enforcement, a runaway could drain $1000s"). The spend is
conserved: the swarm's total budget went down by exactly what the receipts
metered, no more.

**Minute 5 — the trusted-path check.** Before authorizing a value-moving
dispatch (the coordinator transferring real resources to a worker), she invokes
the cipherclerk via ⌘K: "who is this member, really?" The cipherclerk shows the
member's identity drawn from the live ledger (NOT its self-description — the §5
T2 label-binding property), its mandate's attenuation lineage, and — when the
attested-volition lane lands — requires her gesture to authorize the dispatch, so
the turn carries proof a real operator clicked. She is never fooled about which
swarm she is flying.

**The binding home.** Every "she clicks" above has a non-cockpit twin: the same
`Swarm::run` seam is what her integrated loop calls at its one serialization
point. The cockpit is the cockpit; the SDK binding (`dregg_sdk::embed::
DreggEngine::execute_turn` + `Effect::EmitEvent` + the cell c-list mandate) is
the same seam her loop drives headless. The cockpit is the evaluation artifact —
the demo IS how pug judges whether this is usable — and the SDK path is the
adoption.

---

## 4. The cockpit anatomy (what the SWARM tab IS)

The SWARM tab is the observing-and-driving surface. Six regions, each backed by
real `World` state, none faked.

### 4.1 The member roster (observe: who is in the swarm, and what may they touch)

One row per member, in boot order. Each row is a cap-confined view (the agent
cell rendered as a `Surface`, §1 of the desktop-OS doc), showing:

- **identity** — abbreviated cell id + operator-assigned name + a backed/missing
  badge (a dead agent reads honestly; its loop is grounded in a real cell or it
  is not). The identity is drawn from the live ledger, anti-spoof — a member
  cannot impersonate another cell's identity (the §5 T2 property carried to the
  swarm).
- **THE HELD MANDATE** — the member's attenuated capability edges: which cells it
  reaches, at what `AuthRequired` rights, whether faceted (effect-restricted),
  and any expiry height. This is "adoption IS attenuation" made legible — the
  member is exactly as powerful as the mandate it holds, nothing ambient. The
  `MandateEdge` model already exists in `agent.rs`.
- **THE AUTHORIZATION BOUNDARY** — the projection of the mandate into legible
  verbs: what the member CAN do and (as important) what it CAN'T. The "DON'T"
  entries are the edge of the loop's reach. `agent.rs::Authorization` already
  builds this.
- **THE BUDGET METER** — spent computrons against a ceiling, with an amber/red
  threshold (§5). The member's balance is the pay-for-action floor; a shared
  Stingray ceiling is the swarm budget.
- **THE INBOX** — pending (and recently drained) `NotifyEdge`s from peers,
  newest-first, with the sender, topic, and drain state. A PENDING badge counts
  undrained wakes.

### 4.2 The activity feed (observe: what did the swarm actually do)

A newest-first log of `SwarmActionOutcome`s — every dispatch that ran through the
seam, committed or refused. Each entry: the acting member, the receipt hash
(short), the height, the computrons metered, the effect summary, and the notify
edges it produced (`→ notify worker-a topic 0x…`). A refused entry is colored red
and carries the refusal reason. This is the swarm's grounded seam history — the
on-ledger truth an operator audits, not a self-report. The feed is the
"tool_calls table made tamper-evident" — each row a signed, cap-checked,
budget-metered, receipted turn instead of a mutable log line.

### 4.3 The coordination graph (observe: the causal shape of the swarm)

A small directed view: members as nodes, notify edges as arrows (A→B), the
mandate edges as a fainter background graph (who CAN reach whom). The notify
arrows animate as wakes land and fade as they drain. This makes the causality
visible *without* implying synchronization — the arrow is "A woke B", the
independent receipts are the proof they did not jointly authorize. (Buildable as
a simple force-free layout over the member set; the whole-graph delegation view
is the designed-pending row in STARBRIDGE-V2's matrix.)

### 4.4 The dispatch bar (drive: send a cap-gated command)

The driving surface. A member selector + a verb selector + a target selector,
assembling a typed `SwarmCommand` (the same vocabulary as `terminal::Command`) or
the `raw_effects` path for multi-effect turns. On dispatch it calls `Swarm::run`
— the same one seam — so a hand-driven dispatch and a loop-driven dispatch are
indistinguishable at the boundary. The bar PRE-CHECKS the mandate as you build the
command (greying out targets the selected member can't reach), so the refusal is
*predicted* before you fire it — the over-grant teaching moment, anticipated. But
the real gate is the executor: even if the UI mispredicts, the cap-gate fires.

### 4.5 The budget meter strip (drive + observe: the conserved spend)

A swarm-aggregate meter: total budget, total spent (the sum of metered
computrons), headroom, and a per-member breakdown. Setting a member's ceiling is
a dispatch (a Stingray bound). The meter is the answer to "a runaway could drain
$1000s" — the spend is atomic and conserved; the swarm cannot collectively
exceed its bound, and the proof is the conservation property the Stingray counter
already carries.

### 4.6 The trusted-path strip (the anchor)

A persistent strip (or the cipherclerk tab, reached via ⌘K) that answers the
secure-attention question for the swarm: for the selected member, the genuine
`(cellId, sourceStateRoot)` read straight from the ledger, the mandate's
attenuation lineage (root macaroon → confined → delegated), and the authorize
gesture for value-moving dispatches. This is the cipherclerk promoted to the
swarm's trust anchor — "is this really the member I think it is, and did I really
authorize this?"

---

## 5. The budget meter (the conserved spend, in depth)

The budget meter is the cockpit face of *atomic budget*, the third of the six
primitives the integrators hand-rolled. Three layers, each already substantiated:

1. **The per-turn meter (live).** Every receipt carries `computrons_used`; the
   panel already shows per-member and per-action computrons. The meter is the
   running sum, drawn as a bar against a ceiling.

2. **The pay-for-action floor (live).** A member's `balance` is the resources its
   loop holds. A dispatch that would overspend the member's balance is REFUSED by
   the executor (the conservation guarantee — value is neither created nor
   destroyed). This is the floor: a member cannot act beyond what it holds.

3. **The shared Stingray ceiling (weld).** A swarm budget is a
   `dregg_coord::StingrayCounter` — a bounded conservation counter. Members draw
   against it; the counter's invariant (drawn ≤ ceiling, and the sum is
   conserved across resolution) makes "the swarm collectively spent at most B"
   provable, not best-effort. The SDK already attaches it as a budget gate
   (`runtime.rs::attach_budget`); the cockpit surfaces it as the aggregate meter
   strip and a member that would breach the ceiling is REFUSED with `budget
   exhausted`.

The meter's UX discipline mirrors the refusal discipline: amber as a member
approaches its ceiling (a warning, not a denial), red + REFUSED at the breach
(the guarantee firing). The operator watches the conserved spend the way she
watches conserved value — the budget is just another conservation law, surfaced.

This is the precise answer to simbi's honest gap. simbi's `AgentRun` row records
spend after the fact; the Stingray ceiling makes the spend atomic at the seam, so
a runaway is refused at dispatch, not discovered in the audit.

---

## 6. The notify async wake (the coordination edge, in depth)

The wake is the cockpit face of *atomic handoff* — buildr's `--wake` made
all-or-nothing. The model is the async DUAL of a synchronous joint turn:

```
  member A  ──(EmitEvent turn · receipt rA)──▶  notify inbox of B
                                                      │
                                               [pending wake]   ← observable in the cockpit
                                                      │
  member B  ◀──(drain turn · receipt rB)──────────────
```

The two receipts are INDEPENDENT on-ledger records — no shared parent, no
synchrony, no joint authorization. B decides when to drain, how, and with what
effects. The cockpit shows the causality (the arrow, the inbox badge) and the
proof of independence (two distinct receipt hashes). This is the corrected
understanding from `project-notify-primitive`: `--wake` is ASYNC ("recipient
drains next turn"), NOT a joint turn; `JointTurn` is the SYNCHRONOUS pullback;
the metatheory had no async cross-agent signal until notify.

**Today** the wake rides `Effect::EmitEvent` (already executed; the inbox is
cockpit-local state derived from the dynamics stream). This is honest and
buildable now — the coordination is real and receipted. **The deep version** is
`notify(target, badgeMask)`: the right to cause a WAKE without read/send/reply,
the 4th **Synchrony** dial (sibling to dregg4's Disclosure × Transferability ×
Agreement). The badge-mask is a real sub-lattice riding the SAME non-amplification
the firmament mint proves — `[.notify]` = "may poke, not message" is new
expressivity. The cockpit's inbox is exactly the badge-OR accumulator made
visible: idempotent coalescing of async signals. The Lean keystone
(`NotifyAuthority.lean`) is axiom-clean; the core constructor + VK bump is HELD
for the cutover-settle — so the cockpit's near-term inbox is `EmitEvent`-backed,
and the badge-mask authority drops in when notify lands without changing the UX.

**One honest flag carried, not closed:** a badge-OR is a covert channel (a
one-bit info-flow leak) — dregg has no noninterference argument yet. The cockpit
should not pretend the wake is information-free; the inbox shows the topic, which
is exactly the bit that leaks. Flagged at the surface, per the notify study.

---

## 7. Why the operator is never trusting the loops (the accountability thesis)

The whole point — the feeling the cockpit must produce — is that the operator
audits a swarm she did not write and could not trust, and is nonetheless never
fooled. Each of the four observables makes one untrusted thing accountable:

| The loop could lie about… | The cockpit shows instead… | Backed by |
|---|---|---|
| "I was authorized to do X" | the cap-gate REFUSED it (out-of-mandate, on-ledger, no commit) | `Swarm::run` cap-gate + `capabilities.has_access` |
| "I did X" / "I coordinated with B" | the executor's receipt + the `EventEmitted` dynamics (the seam record) | `World::commit_turn` receipts + the dynamics stream |
| "I stayed within budget" | the conserved computron spend against the Stingray ceiling | per-receipt computrons + `StingrayCounter` conservation |
| "I am member M" | the identity drawn from the live ledger, not self-description | the §5 T2 label-binding (the cipherclerk anchor) |

This is the integrator wedge made felt: all four loops (buildr / builders / sig /
simbi) hand-rolled these same four observables around the same one seam, and
every one punted on enforcement. The SWARM cockpit is the place where the
enforced versions are *visible* — the JSON envelope made non-forgeable (the
mandate), the mutable tool_calls table made tamper-evident (the feed), the
after-the-fact budget made atomic (the meter), the `--wake` made all-or-nothing
(the inbox). One seam, four systems, identical shape — tiny at the call-site,
total in what it buys, and now legible at the glass.

---

## 8. The buildable-now slices (wide-safe, separate workspace, not blocked on the cutover)

`starbridge-v2/` is its own standalone build (rolling-nightly, embeds the
verified executor, its own target dir) — it does NOT participate in the workspace
build and is NOT gated by the VK rotation / cutover. Everything below is a weld on
the EXISTING `swarm.rs` heart + the cockpit, gpui-free where the logic lives,
`cargo test`-able in the headless heart, with the gpui panel as the thin render
layer. Sequenced so each lands by its own test against the REAL embedded executor.

**S0 — the budget meter (headless model + panel strip).** Add a `BudgetMeter` to
the `Swarm`: per-member `spent: u64` (running sum of metered computrons, already
on each `SwarmActionOutcome`) and an optional `ceiling: Option<u64>`; an aggregate
`SwarmBudget { total_ceiling, total_spent, headroom }`. Extend `Swarm::run` to
REFUSE a dispatch that would breach the member's ceiling (a new
`SwarmError::BudgetExhausted { member, spent, ceiling }`), BEFORE the turn runs —
fail-closed, no commit. Extend `SwarmView`/`SwarmMemberView` with the meter
fields. Tests: a member under its ceiling commits and `spent` grows by the
metered computrons; a dispatch that would breach is REFUSED with the budget error
and no height advance; the aggregate meter sums correctly. (Pure headless; the
panel strip is the thin render. The Stingray ceiling is the floor model — the
real `StingrayCounter` weld is S3.)

**S1 — the dispatch bar (drive any cap-gated command, not just the 3 demos).**
Generalize the 3 hardcoded verbs into a `SwarmDispatch` builder: select member +
verb (`SwarmCommand` vocabulary, mirroring `terminal::Command`) + target,
assembling effects and calling `Swarm::run`. Add a mandate PRE-CHECK helper
(`Swarm::can_reach(agent, target) -> bool`, reading the live c-list) so the UI
greys out unreachable targets and PREDICTS the refusal. New palette commands per
verb (one `CommandId` each, dispatched through the same `&mut Cockpit` verb).
Tests: the dispatch builder assembles the right effects; `can_reach` agrees with
the cap-gate; a predicted-refused dispatch is in fact refused by the executor
(the UI prediction and the real gate agree). (This is the keystone that turns the
panel from a demo into a driving surface.)

**S2 — the authorization-boundary + identity per member (observe the mandate in
full).** Reuse `agent.rs::AgentActivity` to render, per swarm member, the full
held mandate (every `MandateEdge` with rights/facet/expiry) and the authorization
boundary (CAN / CAN'T verbs). Add the anti-spoof identity badge drawn from the
live ledger (the §5 T2 property — a member cannot masquerade). Tests: the mandate
view matches the cell's real c-list; the authorization boundary's CAN set is
exactly the reachable+permitted verbs; a member whose backing cell is sealed
shows the lifecycle honestly. (Mostly a render weld over existing models.)

**S3 — the Stingray ceiling weld (the atomic shared budget).** Replace S0's floor
ceiling model with a real `dregg_coord::StingrayCounter` as the swarm's shared
budget: members draw against it; the conservation invariant makes "the swarm
spent at most B" provable. Wire it the way the SDK runtime does
(`attach_budget`). Tests: the swarm budget conserves (drawn = sum of metered
across members); a draw past the ceiling is refused; the aggregate meter reflects
the counter's state. (This is the depth lift from a UI counter to a verified
conservation bound — the simbi-gap closure made real.)

**S4 — the coordination graph (the causal shape).** A gpui-free graph model
(`SwarmGraph::build`): nodes = members, notify arrows = the `NotifyEdge`s from the
inbox state, mandate edges = the fainter reach graph. A simple deterministic
layout. The panel animates arrows on land/drain. Tests: the graph model's arrows
match the deposited notify edges; the mandate background matches the cap-graph.

**S5 — the cipherclerk trusted-path strip for the swarm.** Bind the existing
CIPHERCLERK surface to the selected swarm member: show its ledger-drawn identity,
its mandate's attenuation lineage (root → confined → delegated, the real macaroon
chain), and — gated on the broader attested-volition lane — an authorize gesture
for value-moving dispatches. Tests: the lineage shown matches a real
mint→attenuate→delegate chain; the identity is ledger-drawn, not self-reported.
(S5's gesture-to-turn binding is the one slice that LEANS on a not-yet-landed
lane — see §9 — so the near-term S5 is the identity + lineage strip, with the
gesture as the designed-pending tooth.)

**S6 — a runnable demo script + the SDK-binding doc.** The "two agents,
trustline, channel, mailbox" handoff story (the pug evaluation artifact) extended
with the swarm: boot N members, dispatch a cap-gated task, watch the wake drain,
watch a refusal, watch the budget meter bite. Plus a short `swarm-sdk.md` showing
the integrator how the SAME `Swarm::run` seam binds to their one serialization
point (the PostToolUse hook / the `recordPhaseComplete` / the `AgentRun` row).
(This is the handoff-readiness deliverable — the demo IS the evaluation.)

Sequencing: **S0 → S1 → S2** is the core driving-and-observing loop and is pure
weld on the existing heart, all wide-safe and cutover-independent. **S3** is the
budget depth lift. **S4/S5** are the richer observability. **S6** is the handoff
artifact. None of these touch the metatheory workspace, the VK rotation, or the
circuit — they live entirely in the standalone starbridge-v2 crate.

---

## 9. The killer demo

**A three-agent swarm where the operator watches accountability fire four times
in ninety seconds, never trusting the loops.** On the SWARM tab:

1. **Coordinate (the wake).** The coordinator dispatches `task/go` to worker-a.
   The activity feed shows the receipted `EmitEvent`; worker-a's inbox lights
   PENDING. Worker-a drains in its OWN separate ack turn — two distinct receipt
   hashes in the feed, the causality visible, the independence proven. *The
   `--wake` made all-or-nothing and auditable.*

2. **Refuse (the mandate).** The operator dispatches worker-a → transfer to
   worker-b. The dispatch bar already greyed the target (predicted refusal); she
   fires anyway; the executor REFUSES — `out-of-mandate`, red in the feed, no
   height advance. *The no-amplification guarantee firing at the swarm layer.*

3. **Meter (the budget).** The coordinator runs a burst of dispatches; its budget
   meter climbs amber, then a dispatch that would breach the Stingray ceiling is
   REFUSED — `budget exhausted`. The aggregate meter shows the conserved spend:
   the swarm spent exactly its receipts, no more. *The runaway refused at the
   seam, not discovered in the audit.*

4. **Attest (the identity).** Before a value-moving dispatch, the operator opens
   the cipherclerk on the coordinator: its identity is ledger-drawn (not
   self-reported), its mandate's attenuation lineage is shown, the dispatch
   carries her authorization. *She is never fooled about which swarm she flies.*

The bumper-sticker: **every agent action — provably authorized, recorded,
budgeted, and coordinated — without trusting the loops.** The demo is the
evaluation artifact: it is exactly what a stranger (pug) runs to judge whether
the accountability substrate is real and usable, and every frame is a real turn
through the embedded verified executor, not a mock.

A small poem for the glass:

> four small lies a loop might tell —
> *authorized, did, paid, am* —
> four receipts the ledger keeps;
> the swarm cannot pretend.

---

## 10. The honest gaps (severe problems with closure lanes, never walls)

- **The inbox is cockpit-local state, not yet the recipient cell's own storage.**
  Today the `NotifyEdge` inbox is tracked by starbridge-v2 from the dynamics
  stream (honest for the n=1 embedded image). In a distributed setting the inbox
  is the recipient cell's own state field (a pending-event queue) with the
  dregg-node routing `EmitEvent` as a network message and the cell's program
  draining it. CLOSURE: the cell-storage inbox is a cell-program lane (the
  language uplift makes a per-cell pending queue expressible); the node routing
  is the remote `.turn()` lane (#171). Until then, the inbox is correct for the
  single-image cockpit and labeled as such.

- **The deep `notify(target, badgeMask)` authority is HELD, not landed.** The
  near-term wake rides `Effect::EmitEvent` (already executed, fully receipted) —
  so the coordination is real and the cockpit UX is final, but the badge-mask
  sub-lattice ("may poke, not message") is not yet enforced at the core. CLOSURE:
  `Dregg2/Firmament/NotifyAuthority.lean` is the axiom-clean keystone; Step 2 (the
  `Auth.notify` constructor + α-totalization + felt-encoder/VK bump, ~9 mechanical
  arms) is HELD for the cutover-settle (it is a VK/encoding bump, mid-circuit
  churn). When it lands, the badge-mask drops into the cockpit's inbox model
  without any UX change.

- **The badge-OR is a covert channel (a one-bit info-flow leak).** A wake's
  presence/topic is observable; dregg has no noninterference argument yet. The
  cockpit shows the topic (the leaking bit) rather than pretending the wake is
  information-free. CLOSURE: this is research-pillar #31 (info-flow); flagged at
  the surface per the notify study, not closed.

- **The attested-volition gesture (S5's authorize tooth) leans on a not-yet-landed
  lane.** Binding "the operator clicked" to a turn premise (a signed
  input-receipt the executor requires) is the DREGG-DESKTOP-OS §5 attested-volition
  property — which needs the compositor-PD signed-input-receipt machinery. CLOSURE:
  the near-term S5 ships the identity + attenuation-lineage strip (fully buildable
  on the existing cipherclerk); the gesture-to-turn binding is the designed-pending
  tooth that lands with the trusted-path compositor work (DREGG-DESKTOP-OS R3).

- **The Stingray ceiling is a swarm-local budget, not a cross-node shared
  budget.** S3's `StingrayCounter` is conserved within the embedded image; a
  budget shared across federated nodes is the distributed Stingray (the
  `SharedBudgetDynamics` / cert-reconciliation model exists in the metatheory but
  the cockpit's swarm is n=1). CLOSURE: this is the n-parametrized collapse of
  FIRMAMENT §3 — at n=1 the budget is synchronous and exact (a headline guarantee,
  not a limitation); the n>1 shared budget is the same counter with the bounds
  relaxed, landing with federation.

- **The coordination graph is a single-image view.** The graph (S4) shows the
  members of THIS image's swarm. A cross-image swarm (members on different
  federated nodes) is the federation-connect lane (designed-pending in
  STARBRIDGE-V2's matrix). CLOSURE: same n-parametrization — the local graph is
  first-class; the federated graph is the same model over the peer view when
  federation-connect lands.

None of these are walls. Each is a labeled seam with a named closure lane (a
cell-program feature, a held VK bump, a research pillar, a federation lane), held
to one worthwhile semantics, and — crucially — none of them block the buildable
S0→S2 core that makes the SWARM cockpit a real driving-and-observing surface
today, on the hardware the operator already has, in a workspace untouched by the
cutover.

---

*The SWARM cockpit is the firmament's accountability made visual for agents. We
do not own the loop — the loop is the integrator's game, living above dregg. We
own the one seam where the loop's action becomes a turn, and we make that seam
legible at the glass: authorized, recorded, budgeted, coordinated, never trusting
the loops. n=1 is first-class today (synchronous wake-drain, exact budget,
immediate refusal); the same seam reaches the wire tomorrow with only the bounds
relaxed.*
