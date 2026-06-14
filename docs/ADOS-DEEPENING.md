# ADOS-DEEPENING — the swarm cockpit as a real multi-agent dev environment

*Design frontier. Present-tense, first-principles, teach-what-is. A **deepening**
of `docs/design-frontiers/ADOS.md`: where that doc states the thesis (one seam,
six primitives, the integrator wedge) and the developer journey, this one goes
down one level into the **agent-IDE itself** — the concrete affordances that turn
the SWARM tab from a three-verb demo into a real cockpit a developer lives in,
and the aspirations those affordances reach toward. North star, not rigid spec:
the buildable-now slice is grounded in code on disk; every gap is named as work
with a closure lever, never a wall.*

> Read first: `docs/design-frontiers/ADOS.md` (the thesis + the journey + the
> killer demo), `docs/design-frontiers/AGENT-SWARM-UX.md` (the cockpit anatomy —
> the six regions, the budget meter and notify edge in depth). This doc does not
> repeat them; it deepens the IDE-as-environment angle and names the next
> affordances precisely.
>
> Companion docs: `docs/STARBRIDGE-V2.md` (the gpui master interface this is a tab
> inside — the embedded executor, the cap-first shell, the ⌘K palette,
> cipherclerk), `docs/DISTRIBUTED-SERVO.md` §3 (the *provable + agent-driven*
> facet — a web interaction routed through the same `Swarm::run` seam, the
> narration-vs-truth tooth on the web), `docs/FIRMAMENT.md` §3 (the `n`
> deployment gradation), `docs/FRONTIER-ROADMAP.md` (the prioritized build list —
> the N1–N11 lanes this doc's affordances map onto).
>
> Code grounding (verified on disk): `starbridge-v2/src/swarm.rs` (the A2 seam +
> `run` + `run_atomic` + `bind_surface` + `drain_notify` + `SwarmView`, gpui-free
> and tested), `starbridge-v2/src/agent.rs` (A1 — `AgentActivity`, `MandateEdge`,
> the `Authorization` boundary), `starbridge-v2/src/proofs.rs` (the
> `VerificationTier` board), `starbridge-v2/src/cockpit.rs` (the live SWARM tab +
> the three demo verbs + the ⌘K registry).

---

## 1. The aspiration in one breath

**ADOS is the development environment where a developer *lives inside* an agent
swarm the way they live inside an editor — and the environment's ground truth is
the verified executor's receipts, not the agents' self-reports.** Today a
developer running a fleet of coding agents reads a scroll of terminal output and a
pile of log lines each agent wrote about itself; the environment is a *transcript
viewer over narration*. ADOS's aspiration is to make the environment a **cockpit
over executor truth**: the developer sees, at a glance and in real time, which
agents are alive and what each may touch (the mandate roster), what the swarm
actually did (the receipted activity feed, not the claimed one), what it cost and
whether it could have cost more than allowed (the conserved budget meter), how the
agents are coordinating (the causal notify graph), and — the sharpest tooth —
**where any agent's narration diverges from its receipts** (the
narration-vs-truth panel). The agent loops live *above* dregg and are the
integrator's game; the environment grounds the one seam where a loop's action
becomes a turn, and renders that seam as a place a developer can stand.

The deepening's bumper-sticker: *an IDE you fly a swarm from — every pane a
cap-confined cell, every agent action a verified turn, every cost a conserved
spend, every coordination a receipted edge, and a first-class panel that catches
an agent the moment it says more than it did.*

This is not a new agent runtime, and it is not a dashboard bolted onto one. It is
`starbridge-v2`'s cockpit (the embedded verified executor, the cap-first shell,
the ⌘K palette) **specialized into a multi-agent development environment**, with
the SWARM tab as the workspace a developer defaults into.

---

## 2. What is live in starbridge-v2 today (the verified surface this deepens)

Everything below runs in `starbridge-v2` *now*, against the **real embedded
verified executor** (`World::commit_turn` → `dregg_turn::executor::TurnExecutor`
over a `dregg_cell::Ledger`), gpui-free where the logic lives, and `cargo
test`-able in the headless heart. This is the substrate the deepening stands on —
named precisely so the frontier (§4) is honestly the *remaining* work.

### 2.1 The swarm seam, A2 — `swarm.rs` (live, tested)

The one seam is real and carries three coordination shapes:

- **`Swarm::run(world, agent, effects)`** — the cap-gated, receipted seam
  (`swarm.rs:353`). In order: resolve the member (unknown ⇒ `UnknownMember`),
  confirm the backing cell is live (gone ⇒ `Unbacked` — a destroyed agent cannot
  act), **cap-gate** each effect against the acting cell's c-list
  (`capabilities.has_access(target)`; out-of-mandate ⇒ `OutOfMandate`, *fail-
  closed, no turn committed*), run through the real executor, scan the new
  `EventEmitted` dynamics and deposit `NotifyEdge`s into peer inboxes, and append
  a `SwarmActionOutcome` (receipt hash, height, **metered computrons**, summary,
  notify edges) to the grounded action log. A *refused* action is logged too,
  with its reason — the refusal is a record, not a silent drop.
- **`Swarm::run_atomic(world, agent, actions)`** — the synchronous all-or-nothing
  bundle (`swarm.rs:546`): a coordinator bundles N member-actions into ONE
  `forest_turn` the executor commits as a unit (any invalid action ⇒ the whole
  bundle rejects, no partial effect), every effect cap-gated against the
  *coordinator's* mandate, ONE receipt for the bundle. This is the swarm-layer
  atomic handoff (the synchronous dual of the async notify edge).
- **`Swarm::drain_notify(world, agent)`** — the recipient's OWN separate ack turn
  (`swarm.rs:679`): the notify edge was deposited by the *sender's* committed
  turn; the drain is a wholly independent future turn by the *recipient* (a
  `SetField` ack on its own cell). The two receipts are independent — causality
  visible (A→B), synchronization not forced. This is the ocap async-message model,
  `--wake` made into a receipted edge.
- **`Swarm::bind_surface(shell, agent)`** — each member gets its OWN cap-confined
  pane, owned via a real `dregg_firmament` `SurfaceCapability` the shell mints
  (`swarm.rs:496`): a forged cap is refused on every window op, so the swarm's
  *panes* carry the same no-ambient-authority discipline as its *turns*.
- **`SwarmView::build`** — the render model (`swarm.rs:821`): per-member mandate +
  action count + balance + inbox drain state, plus an activity feed of recent
  `SwarmActionOutcome`s.

The tests assert the load-bearing properties directly: in-mandate commits +
receipts; out-of-mandate **refused** (no turn committed); emit → inbox → async
drain with independent receipts; an unknown member is refused; the atomic bundle
commits-or-refuses as a unit; self-emit and non-member emit deposit no edge.

### 2.2 The single-agent activity surface, A1 — `agent.rs` (live, tested)

`AgentActivity::build(world, agent, max_actions)` (`agent.rs:142`) reads ONE
agent's provable activity straight from the live ledger:

- **`MandateEdge`** (`agent.rs:54`) — the agent's held capability edges decoded
  from its c-list: which cells it reaches, at what rights (`rights_label`). The
  mandate is the *real cap-graph*, not a self-description — "as powerful as the
  mandate it holds, nothing ambient" made legible.
- **`Authorization`** (`agent.rs:102`) — the projection of the mandate into
  legible CAN / CAN'T verbs (`build_authorizations`, `agent.rs:299`). The "CAN'T"
  entries are the edge of the loop's reach — as important to show as the "CAN".
- **`AgentSurface`** (`agent.rs:404`) — the agent rendered as a cap-confined
  `Surface`, so one agent's activity is a window over its real cell.

This is the N=1 shape the swarm generalizes; the SWARM roster (§3.1) is N copies
of this surface over the swarm's members.

### 2.3 The verification-tier board — `proofs.rs` (live, tested)

`ProofBoard::build(world, max)` (`proofs.rs:193`) classifies every committed
turn's **honest verification tier** — never inflated:

- **`VerifiedByConstruction`** (tier 1) — the embedded verified executor enforced
  every guarantee inline; the receipt's existence *is* the proof. This is the tier
  every embedded turn sits at today.
- **`ExecutorSigned`** (tier 2) — the producer Ed25519-signed the receipt hash; a
  verifier checks the signature, not the re-execution.
- **`StarkAttached`** (tier 3) — an explicit STARK over the whole-turn statement
  rides the turn; a light client verifies with NO trust in the producer (the
  `dregg_sdk::full_turn_proof` federated lane).

`next_route` names the honest path to the next tier. The pale-ghost question for
proofs — *can a light client be fooled about whether a turn was verified?* — is
answered by the tiering refusing to claim more than the receipt carries. **This is
the panel that lets the cockpit show, per agent action, exactly how strong its
proof is** (§3.6).

### 2.4 The cockpit shell this all lives in — `cockpit.rs` + `STARBRIDGE-V2.md`

- The **SWARM tab is wired** (`cockpit.rs`: `Tab::Swarm`, `swarm_panel`): the
  cockpit boots a 3-member swarm (service = coordinator holding a cap to user =
  worker-a; treasury is confined + unreachable, illustrating the boundary), and
  three demo verbs run real turns (`coordinator emit task/go`, `worker-a DRAIN`,
  `coordinator transfer + wake`), each registered in the **⌘K palette**
  (`GoSwarm`, `SwarmCoordinatorEmitA`, `SwarmWorkerADrain`,
  `SwarmCoordinatorTransferAndWake`) and dispatched through the exact `&mut
  Cockpit` verb the buttons call — no second action path.
- The **cap-first shell** (the N7 verified-surface-ops surface): every window op
  (open/focus/raise/move/resize/minimize/close) is cap-gated; a forged cap is
  refused on every op; the trusted-path identity chrome is shell-drawn from the
  live ledger (anti-spoof — a dangling surface reads `missing`); the compositor's
  T1–T4 anti-ghost teeth (overpaint / label-spoof / double-focus REJECT) are Lean
  theorems over the scene graph (`FRONTIER-ROADMAP.md` N7). This is the surface
  discipline the swarm's per-member panes (`bind_surface`) inherit.
- **cipherclerk + ⌘K** are first-class and wired to real crypto (the
  `dregg_sdk::AgentCipherclerk` macaroon mint/attenuate/delegate/discharge; the
  fuzzy palette over every action) — the trusted-path anchor (§3.7) and the secure
  attention surface.

**The honest line:** the cockpit can already *boot* a swarm, *run* its actions
through the verified executor, *show* receipts, and *gate* its panes. The
deepening (§3) turns those primitives into the lived environment; the frontier
(§4) names what is genuinely not yet there.

---

## 3. The deepening — the concrete next affordances of the agent-IDE

Each affordance below names what it *is*, what it stands on (the §2 surface), and
its build status (a near-term weld on the existing heart, or a named frontier with
its lever). The ordering is the felt importance of the environment, not the build
sequence (that is `FRONTIER-ROADMAP.md`).

### 3.1 The mandate roster — *who is in the swarm, and what may each touch*

The default-left region of the SWARM tab: one row per member, rendered from
`SwarmView` over the live world. Each row shows the member's identity (abbreviated
cell id + operator name + a **backed/missing badge** drawn from the ledger, never
self-reported), its **held mandate** (every `MandateEdge` with rights — the real
c-list), its **authorization boundary** (the legible CAN / CAN'T verbs from
`agent.rs::Authorization` — the "CAN'T" entries the edge of the loop's reach), its
**balance**, its **action count**, and its **inbox** (pending + recently drained
notify edges).

The aspiration: a developer glances at the roster and *knows the blast radius of
every agent* — not by reading a config file the agent could be ignoring, but by
reading the cap-graph the executor will actually enforce. The boundary is visible
*before* anything runs: the demo's `treasury` cell sits confined and unreachable,
so a member targeting it is refused — the roster shows that wall as a structural
fact.

*Status:* a near-term weld. `SwarmView` + `agent.rs::AgentActivity` exist and are
tested; the roster is the gpui panel that renders N members' mandate + auth
boundary + inbox over the live world. (`FRONTIER-ROADMAP.md` N2/N3 — the per-member
mandate + authorization-boundary render.)

### 3.2 The activity feed — *what the swarm actually did (receipts, not narration)*

The center region: a newest-first log of `SwarmActionOutcome`s — every dispatch
that crossed the seam, committed *or refused*. Each entry carries the acting
member, the **receipt hash** (the provenance link), the **height** (where it
committed), the **metered computrons** (the real cost from
`receipt.computrons_used`), the effect summary, and the notify edges it produced.
A refused entry is colored red with the executor's own reason.

This is the move that makes the environment not-a-transcript-viewer: the developer
reads *the executor's record of what happened*, never *the agent's claim*. The
feed is "the `tool_calls` table made tamper-evident" — each row a signed,
cap-checked, budget-metered, receipted turn instead of a mutable log line. A
**refusal is the most important entry in the feed**: it is a guarantee firing
where the developer can see it (the swarm-layer twin of the composer's "⚠
over-grant"), and the deepening surfaces it as a teaching beat, not an error to
hide.

*Status:* live in the model (`Swarm::action_log` + `SwarmActivityEntry` in
`SwarmView`); the feed is the gpui render of it. The cost column (computrons) is
already on every outcome.

### 3.3 The budget meter — *what it cost, and whether it could have cost more*

A per-member meter (spent computrons against a ceiling) plus a swarm-aggregate
strip (total budget, total spent, headroom). The discipline mirrors the refusal
discipline: **amber** as a member approaches its ceiling (a warning), **red +
REFUSED** at the breach (the guarantee firing). The aspiration is the precise
answer to the runaway-spend fear every operator carries: *"could this swarm have
cost more than I allowed?"* becomes a query with a **provable ceiling**, because
budget is a cell and a spend is a turn, so conservation makes the bound atomic
*before* the effect, not reconciled after.

Two depths, both grounded:

- **The floor (near-term weld, N1):** add a `BudgetMeter` to the `Swarm` —
  per-member `spent` (the running sum of metered computrons, already on each
  outcome) and an optional `ceiling`; extend `Swarm::run` to **refuse** a dispatch
  that would breach the ceiling (`BudgetExhausted`, *before* the turn runs,
  fail-closed). This needs no new protocol — only the gate + the meter fields +
  the panel strip.
- **The depth lift (N9):** replace the floor ceiling with a real
  `dregg_coord::StingrayCounter` as the swarm's shared budget (wired the way
  `sdk runtime.rs::attach_budget` does), so "the swarm spent at most B" is
  *provable* (the conservation invariant), not best-effort — N agents drawing on
  one pool can never collectively exceed it.

*The honest gap carried (ADOS.md §8.2):* the executor meters **computation**, not
**API dollars**. The provable ceiling is over computrons; binding it to LLM
provider spend needs a declared-cost-debit + a price oracle. Until then the dollar
story is "bounded by a declared rate," stated plainly — never "verified dollar
ceiling."

### 3.4 The coordination graph — *the causal shape of the swarm*

A small directed view: members as nodes, **notify edges as animated arrows** (A→B,
landing on emit, fading on drain), with the **mandate edges as a fainter
background graph** (who CAN reach whom). The aspiration: the developer *sees the
swarm think* — the causality of who woke whom — **without** the view implying
synchronization. The arrow is "A woke B"; the two independent receipts are the
proof they did not jointly authorize. This is the deepest legibility win over a
log scroll: a flat feed cannot show a DAG, and agent coordination *is* a DAG.

*Status:* a near-term weld (N4 / `AGENT-SWARM-UX.md` §4.3 / `S4`): a gpui-free
`SwarmGraph` over the deposited `NotifyEdge`s (the arrows) and the cap-graph (the
background), with a simple deterministic layout. The notify edges already exist in
the member inboxes; the graph is the render. (At `n>1` a cross-image swarm's graph
is the federation-connect lane — same model over the peer view.)

### 3.5 The narration-vs-truth panel — *the sharpest tooth*

The first-class panel that puts a member's **own claimed action** (from its loop's
reflection/log, supplied alongside the turn) next to its **receipt** (or the
*absence* of one) and **highlights divergence**. This is the reason ADOS exists,
sharpened into UI:

| the agent CLAIMS… | the receipt chain SHOWS… | the divergence the panel flags |
|---|---|---|
| "I did X" | no committed turn for X | a **fabricated action** |
| "I was authorized to do X" | a refused (red) outcome for X | a **claimed-but-refused** action |
| "I only did A and B" | a third committed turn C in the feed | a **concealed side-effect** |
| "I stayed in budget" | a `BudgetExhausted` refusal | a **claimed-but-bounded** overspend |

The last two are **the pale ghost caught at the glass**: an agent that *did more
than it said*, or *failed at what it claimed*, is exposed because the turns (and
the refusals) are in the grounded `Swarm::action_log` whether or not the agent
mentions them. The operator does not read the summary; they read what the swarm
*actually did*, and the panel flags every gap.

*Status:* the panel itself is a near-term weld (N5 / `FRONTIER-ROADMAP.md` §6) —
**pure UI over data that already exists** (`Swarm::action_log` + the dynamics).
*The named frontier* is its full power: correlating a *specific* claim to its
*specific* turn needs the **tool-call → effect compiler** (§4.1) so a claimed
action can be matched to the turn it should have produced. The divergence-at-the-
feed-level panel ships now; the claim-to-turn correlation is the compiler-gated
deepening.

### 3.6 The proof-strength column — *how strong is the proof of each action*

Behind the activity feed sits the `proofs.rs` `VerificationTier` board: per agent
action, **how strong is the proof it happened** —
`verified-by-construction` (the embedded executor enforced it inline) /
`executor-signed` (a known producer is cryptographically bound) /
`STARK-attached` (a light client verifies with no producer trust). The aspiration:
a developer auditing a swarm's history sees not just *that* an action committed but
*at what assurance*, and the honest **next-route** to a stronger tier (e.g. attach
a STARK via the federated `full_turn_proof` lane). The cockpit never claims a
higher tier than the receipt carries — the anti-ghost property applied to the
proofs themselves.

*Status:* `ProofBoard` is live and tested; the deepening is mapping it as the
feed's proof column (today every embedded turn is tier 1, or tier 2 if the
producer signed it — STARK attach is the federated lane).

### 3.7 Cap-confined per-agent surfaces — *each agent its own pane, owned by a cap*

Each swarm member can be bound to its OWN cap-confined pane via
`Swarm::bind_surface` — a real `SurfaceCapability` the shell mints, where every
window op is gated on the member's cap (a forged cap refused on every op) and the
identity chrome is shell-drawn from the live ledger (a member **cannot impersonate
another cell's identity** — the anti-spoof T2 property). The aspiration: the
developer arranges the swarm as a *desktop of confined agent panes* (float / tile
/ stack), each pane a live window over its agent's real cell state, none able to
masquerade as another. The surface discipline that gates every *turn* gates every
*pane* — the swarm is a cap-first multi-surface workspace, not a grid of trusted
widgets.

*Status:* `bind_surface` + `member_surface_cap` are live; the deepening is the
cockpit compositing the bound panes through `Shell::compose` as the swarm's
desktop layout.

### 3.8 The dispatch bar + ⌘K — *drive the swarm, and the trusted-path anchor*

The driving surface: a member + verb + target selector assembling a typed command
(or the `raw_effects` path) and calling the *same* `Swarm::run` seam — so a
hand-driven dispatch and a loop-driven dispatch are **indistinguishable at the
boundary**. The bar **pre-checks** the mandate as the command is built (greying out
unreachable targets via a `can_reach` helper that reads the live c-list), so the
refusal is *predicted* before it fires — but the real gate is the executor (even a
UI misprediction is caught by the cap-gate). Every dispatch is also a ⌘K palette
command (the secure-attention anchor), and before a value-moving dispatch the
developer can invoke **cipherclerk** to ask "who is this member, really?" — the
identity drawn from the ledger, the mandate's attenuation lineage (root → confined
→ delegated), so they are never fooled about which swarm they fly.

*Status:* a near-term weld (N6 / `AGENT-SWARM-UX.md` §S1) generalizing the 3 demo
verbs into a `SwarmDispatch` builder + a `can_reach` pre-check. The cipherclerk
identity + lineage strip is buildable on the existing surface; the
*authorize-gesture* tooth (attested volition — binding "the operator clicked" to a
turn premise) leans on the trusted-path compositor lane (`DREGG-DESKTOP-OS.md` §5),
named as the designed-pending tooth.

### 3.9 The tool-call → effect compiler — *so a claimed action correlates to its turn*

The keystone integration affordance, called out on its own because it is the
genuinely-new buildable surface and the natural ADOS SDK boundary: an adapter
`ToolCall → Vec<Effect>` that turns a provider's tool-call schema (an MCP
`tools/call`, a buildr `PostToolUse` payload, a Claude tool-use block) into the
typed effects `Swarm::run` already executes. `swarm.rs` runs effects *today*; the
universal "any tool call becomes the right turn" mapping is what lets the
environment **correlate a claimed action to the turn it produced** — which is what
gives the narration-vs-truth panel (§3.5) its full power and what lets an
integrator route their one serialization point (the `PostToolUse` hook, the
`recordPhaseComplete`, the `swarm-callback`, the `AgentRun` row) through dregg and
inherit the six enforced primitives.

*Status:* the named research frontier (ADOS.md §3.3/§5; `FRONTIER-ROADMAP.md` R1).
Its honest boundary (§4.1): the compiler is per-integrator *conventional* code —
if it maps a tool call to the *wrong* effects, the receipt is a faithful record of
the wrong thing. The decision is verified; the adapter delivering the request to
it is audited code with a golden-corpus differential.

---

## 4. The frontier — named gaps with closure levers (severe problems, never walls)

These are the honest distances between the lived-environment aspiration (§1, §3)
and the verified surface (§2). Each is a labeled seam with a named lever, held to
one worthwhile semantics — and none blocks the buildable §3.1–§3.4 core that makes
the SWARM tab a real driving-and-observing surface today.

1. **The seam is honest only if the tool-call → effect mapping is faithful.**
   §3.9. The compiler is per-integrator code, not verified — the same boundary
   `pg-dregg` draws (the *decision* is verified; the *integration delivering the
   request* is conventional, audited code). **Lever:** a tight, per-provider
   adapter (one for MCP `tools/call` first) with a golden-corpus differential,
   named as the trust boundary, not hidden inside "verified."

2. **Budget = computation, not dollars (yet).** §3.3. Conservation bounds
   *computrons*; binding it to LLM provider spend needs a declared-cost debit + a
   price model. **Lever:** an agent's tool call debits a budget cell by a declared
   cost and the cap caps it — buildable on the existing conservation; the missing
   piece is a faithful price oracle, named honestly.

3. **The loop is above the seam — ADOS grounds actions, not cognition.** ADOS
   makes an agent's *actions* unfoolable; it does **not** verify the agent's
   reasoning, nor prevent a well-authorized agent from doing an authorized-but-
   unwise thing. The guarantee is "you see exactly what it did and it could only
   do what its mandate allowed," not "it did the right thing." This is the correct
   boundary (the loop is not ours to own), stated so no one reads "verified" as
   "aligned."

4. **The narration-vs-truth panel's claim-to-turn correlation is compiler-gated.**
   §3.5. The divergence-at-feed-level panel ships now (pure UI over the action
   log); correlating a *specific* narrated claim to its *specific* turn needs the
   §4.1 compiler so the claim and the turn share a key. **Lever:** the per-provider
   adapter emits a stable correlation id the panel joins on — the same artifact as
   §4.1, used twice.

5. **Spawning the loop itself is not yet ADOS-managed.** Today the loop runs
   wherever it runs and only the *seam* is the contract; ADOS spawns the member's
   cell + mandate + surface (the accountability shadow), not the loop's process.
   **Lever:** a managed ADOS process per agent (a microVM / seL4 app-PD) so the
   loop's *isolation* — not just its actions — is dregg-enforced; the firmament's
   app-PD model (`DREGG-DESKTOP-OS.md` L7) is the path.

6. **`n=1` isolation today is cap-discipline, MMU-enforced only on real seL4.**
   The strong `n=1` properties the environment leans on — **immediate revoke** (a
   coordinator's revoke of a worker's cap goes dark the instant the turn commits),
   **consistent checkpoint** (seal → snapshot → unseal pauses the whole swarm as a
   consistent cut), **synchronous spend** — are genuinely real on the host
   firmament; the *memory* isolation between agent loops is by-construction-in-the-
   API on the host (shared address space) and MMU-enforced only on real seL4 (the
   same UML→SKAS gap, the same fix). Honestly labeled, not laundered.

7. **The remote (`n>1`) swarm relaxes the bounds — the kill switch is local-
   immediate, federation-eventual.** A cross-agent federation trades the `n=1`
   collapse for eventual revocation + quorum commit. The environment's immediate
   kill switch is *immediate* locally and *eventual* across the wire — the honest
   distance-bound, parametrized by `n`, never hidden. The coordination graph and
   the shared budget relax along the same `n`.

8. **`notify` is a covert channel (a one-bit info-flow leak).** A badge-OR wake is
   a one-bit signal; dregg has no noninterference argument yet. The notify edge as
   a *coordination* primitive is sound; as an *isolation* boundary it leaks a bit.
   **Lever:** the info-flow research pillar; the cockpit's inbox shows the topic
   (the leaking bit) rather than pretending the wake is information-free — flagged
   at the surface.

None of these are walls. Each is a labeled seam with a named closure lane (a
per-provider adapter, a price oracle, the app-PD model, the seL4 MMU boundary, the
federation relaxation, the info-flow pillar), held to one worthwhile semantics,
and — crucially — none of them block the buildable core (the roster, the feed, the
budget floor, the coordination graph) that makes the SWARM cockpit a real
multi-agent development environment **today, on the hardware the developer already
has, in a workspace untouched by the cutover.**

---

## 5. Where the deepening lands

The deepening is the path from `starbridge-v2`'s tested swarm primitives to an
**environment a developer lives inside**: the roster that shows every agent's blast
radius, the feed that shows what the swarm did instead of what it said, the meter
that bounds the spend, the graph that shows the coordination, the panel that
catches the pale ghost, and the per-agent panes that carry the cap discipline to
the glass. The agent loops are the game and live above us; ADOS owns the one seam
where a loop's action becomes a turn, and the deepening makes that seam a *place* —
a cockpit, not a log. The buildable-now slices (§3.1–§3.4, the N1–N6 lanes) need no
protocol change and no cutover; the frontier (§4) is named with levers, not walls.
The developer reads what the swarm did, never what it said — and now they read it
in an environment built for flying a fleet.

---

*Closing — a small poem, as is our custom:*

> a roster of reach, a feed of what-was,
> a meter that bounds, a graph of the wakes —
> the loop narrates above; the receipt does not,
> and the panel shows every promise the agent breaks.
> not a log to scroll but a cockpit to fly:
> at the glass, the swarm cannot lie.

( ◕‿◕ )
