# THE UNIFYING STORY — one capability handle, carried everywhere

*Design synthesis. Present-tense, first-principles. This doc does not introduce a
new system; it states the one vision that ADOS + the firmament desktop + pg-dregg
+ starbridge-v2 already are, names the throughline that makes them one product,
and marks the buildable shape, the killer demo, and the honest scope.*

> Companions (the grounding this synthesizes — do not re-derive them):
> `docs/FIRMAMENT.md` (the cap-gradation bridge, in code),
> `docs/DREGG-DESKTOP-OS.md` (the firmament made visual),
> `docs/STARBRIDGE-V2.md` (the master interface that embeds the verified executor),
> `docs/PG-DREGG.md` (postgres as a dregg surface),
> `metatheory/Dregg2/Firmament/` (the Lean semantics the bridge refines).

---

## 0. The one sentence

**dregg is the verified accountability substrate: one unforgeable
`(target, rights)` capability handle, reached through one router, whose every
invocation is a turn the kernel actually ran — carried without a seam from a
local seL4 slot, to a cell on a remote federation, to a window on glass, to a row
in postgres, so that a swarm of agents and a houyhnhnm desktop become *provably*
authorized, recorded, budgeted, and coordinated without anyone having to trust the
loops, the apps, the panes, or the queries.**

The bumper sticker: **better than nockchain — crystallinely coherent, l4v-grade,
no toys.** Not a chain bolted onto a VM; a single verified object-capability OS
whose proof witnesses the protocol's correct evolution all the way out to the
surface a human or an agent actually touches.

---

## 1. The disease this cures (why these four are one product, not four)

Four populations independently arrive at the *same* unmet need, and each
hand-rolls the same six primitives around it, and each punts on enforcing them:

- **Agent-swarm builders** (`buildr`, `builders`, `sig`, `simbi`): cap-gated
  authority, signed provenance, atomic budget, atomic handoff, surfaces-as-caps,
  tenant isolation — every one rolled by hand, every one's enforcement deferred
  ("no per-message signature"; "a compromised worker could mutate the log"; "no
  budget enforcement, a runaway could drain $1000s"). They each serialize "an
  agent did X" at exactly one seam — a mutable log line.
- **Desktop / OS builders**: a window manager has no principled answer to "who
  may draw here, who gets this keystroke, is this pane really the cell it claims?"
  — so a malicious app paints a fake balance, or steals the keystroke meant for
  the signer (the *pale ghost on the display*).
- **Postgres-heavy app builders**: authorization is either application-tier
  (a bug is a total bypass) or SQL RLS (a flat predicate over a GUC that
  *structurally cannot express* attenuation, delegation, caveats, third-party
  discharge, or per-credential revocation).
- **Federation / protocol builders**: a light client must take the server's word
  for the whole history (the *pale ghost on the wire*).

The single disease is the same in all four registers: **authority is asserted
out-of-band, and recorded in something the holder of the secret can lie about.**
The one cure is the same in all four registers: **make authority a capability the
kernel enforces in-band, and make the record a turn whose proof a stranger can
check.** ADOS, the desktop, pg-dregg, and starbridge-v2 are not four products
that happen to share a library — they are *the same cure applied to the four
surfaces an authority decision actually lands on.* That is why they cohere: there
is only ever **one handle, one gate, one record**, and these are the four places
you can be holding it.

---

## 2. The throughline — the firmament router IS the spine

Everything hangs off one type. A firmament **capability** is a `(target, rights)`
pair; a **router** dispatches an invocation by the target alone; the holder cannot
tell which backing it has; and **adoption is attenuation** at every end — the same
`granted ⊆ held` gate (`is_attenuation`, the real `dregg_cell::AuthRequired`
lattice, proven a genuine partial order in Lean). The `Target` is the *only*
thing that changes as you carry the handle outward:

```
                          ┌──────────────────────────────────────────────┐
                          │           Capability { target, rights }       │
                          │                  ONE handle                    │
                          └──────────────────────┬───────────────────────┘
                                                 │  FirmamentRouter::resolve
                                                 │  (dispatch by target alone)
        ┌──────────────────┬───────────────────┼───────────────────┬───────────────────┐
        ▼                  ▼                    ▼                   ▼                   ▼
   Local{slot}      Distributed{cell}      Surface{cell}        (pg row)          (agent turn)
   seL4 CNode       dregg cell on a        a cell rendered      a SQL row gated   the tool-call
   slot; invoke     federation; invoke     as glass; invoke     by the same       seam: an agent's
   = syscall;       = a real executor      = present/focus/     dga1_… token;     action committed
   mint =           turn; attenuate =      grant-input as a     `dregg_admits`    as a cap-gated
   seL4_CNode_Mint; recKDelegateAtten;     turn; share =        is the SAME       receipted turn
   revoke immediate revoke = group-key     GrantCapability      kernel decision
   (n=1)            epoch lift             turn                 from the SAME
                                                                token
        └──────────────────┴───────────────────┴───────────────────┴───────────────────┘
                                                 │
                              ALL gate on  granted ⊆ held  (is_attenuation),
                              the SAME real executor / the SAME proved lattice.
                              Only the BOUNDS slide along the distance parameter n.
```

The distance parameter `n` (how many machines the target is spread across) slides
the **bounds** — immediate↔eventual revocation, synchronous↔quorum commit,
consistent↔stale checkpoint — and **never the verbs**. At `n = 1` the distributed
bounds collapse to strong-local properties; that collapse is the firmament, and it
is first-class today *and* a stepping stone to `n > 1`, never a terminus.

The four "products" are the four `Target` arms (plus the agent-turn seam that
rides the Distributed/Surface arms):

| Piece | What it is | Which arm of the one handle |
|---|---|---|
| **The firmament** (`sel4/dregg-firmament/`) | the cap-gradation bridge in code: the router + `Local`/`Distributed`/`Surface` backings, the `n=1` collapse witnessed, the real executor in the loop | **the spine itself** — `Local{slot}` and `Distributed{cell}` |
| **The desktop** (`docs/DREGG-DESKTOP-OS.md`) | the firmament *made visual*: a window = `Surface{cell}`; the compositor is a verified dregg cell; output-integrity = unfoolability on the scene | **`Surface{cell}`** — the third arm |
| **starbridge-v2** | the master interface that *embeds* the verified executor and runs a live local world; the cap-first shell over `Surface` caps; the **agent-activity + swarm** surfaces (ADOS keystone) | **the cockpit over all arms** + the **agent-turn seam** |
| **pg-dregg** | postgres as a dregg surface: the same `dga1_…` token gates SQL rows; the commit log projects to queryable tables; writes pass through the verifier | **the `(pg row)` arm** — the same token, a fifth landing point |
| **ADOS** (the north star) | the OS that makes any agent loop's actions provably authorized/recorded/budgeted/coordinated, without trusting the loop | **the agent-turn seam** woven through Surface (panes) + Distributed (handoffs) + the budget cell |

ADOS is not a fifth box. It is the *use* the other four are for: an agent is an
intricate loop living **above** dregg; dregg grounds the one seam that matters —
the tool-call/turn boundary — and the swarm's coordination rides the **notify
edge** (an async signal authority, the fourth Synchrony dial). The firmament gives
the swarm its panes (Surface), its handoffs (Distributed), its budget (a cell),
and its async wakes (notify); starbridge-v2 renders all of it live; pg-dregg lets
the swarm's state be plain SQL the operator can `SELECT`.

---

## 3. The composition — how a single act flows through all of it

Walk one authority decision end-to-end to see that there is genuinely one
mechanism, not four glued together. *An agent, holding an attenuated mandate,
shares a read-only view of a budget cell with a sub-agent, who reads it, and an
operator watches — and queries it in SQL.*

1. **The mandate is a capability.** The agent holds a `Capability { target:
   Distributed(budgetCell), rights: read-only }`, obtained by attenuating its
   grantor's cap through `granted ⊆ held`. It physically cannot widen it.
2. **The share is a turn.** The agent invokes `router.attenuate_and_grant(...)`
   to hand the sub-agent a (further-narrowed) view. The router resolves the
   `Distributed` arm to a **genuine `Effect::GrantCapability` turn** through the
   real `TurnExecutor`. A widening share is **rejected with `DelegationDenied`** —
   the no-amplification guarantee, fired by the deployed semantics, not a lint.
3. **The pane is the same capability.** In starbridge-v2 the budget cell is open
   as a `Surface{cell}` window. Sharing the *window* read-only is the same
   `GrantCapability` turn on the same lattice; promoting a read-only mirror to a
   writable surface is the same `DelegationDenied`, now firing **at the pixel
   layer** (the cockpit's `⚠ over-share` teaching moment).
4. **The wake is the notify edge.** When the sub-agent finishes, it commits an
   `EmitEvent` turn that deposits a pending wake in the agent's inbox; the agent
   drains it in its **own** future turn (async, not a joint turn). Two independent
   on-ledger receipts record the causality A→B — the operator cannot be fooled
   about what the two agents coordinated.
5. **The budget is conserved.** Every spend is a turn; Stingray conservation makes
   the shared budget atomic (the thing `simbi` punted on); a runaway cannot drain
   it because there is no path to mutate the cell except a turn the executor
   accepted.
6. **The record is queryable.** The node's commit log projects into
   `dregg.cells` / `dregg.turns` / `dregg.capabilities` (pg-dregg Tier B). The
   operator runs `SELECT * FROM dregg.capabilities WHERE subject = …` — RLS-gated
   by the *same* token at Tier A — and sees exactly the rows their own capability
   admits. The explorer is "your capabilities, expressed as the rows you may
   `SELECT`."

One handle (step 1). One gate, `granted ⊆ held` (steps 2–3). One record, a turn
with a receipt (steps 4–6). The desktop, the swarm, and the database never see a
different authority model — they see the same one, resolved at a different
`Target`, with the bounds relaxed as far as `n` demands.

---

## 4. The positioning — "verified accountability substrate" AND "houyhnhnm OS"

Two faces of one claim, joined at the same proof:

**Face A — the substrate for agent swarms (ADOS's ground).** Agents are loops;
the loop body (perceive/plan/act/reflect, orchestration, memory) is the game and
is *not ours to own*. dregg owns the **accountability seam**: the place each loop
serializes "an agent did X." Today that seam is a mutable log line in four real
systems. dregg makes it a turn that is (a) cap-checked — the agent could only do
what its mandate admits; (b) signed-provenanced — the receipt chain is
tamper-evident; (c) budget-metered — conservation makes the spend atomic; (d)
coordinated — joint turns for synchronous all-or-nothing, the notify edge for
async wakes. The integration is *tiny at the call-site, total in what it buys*:
the loop is unchanged; its actions become unforgeable.

**Face B — the houyhnhnm OS (the firmament's ground).** A houyhnhnm app is pure,
reproducible, no hidden nondeterminism, **no deception**. The firmament makes that
contract *structural*: an app reaches a clock, an RNG, a socket, another app's
memory, or the glass **only** through a capability the firmament hands it, and
every action is a verified, replayable turn. The seL4 cap partition is the trust
boundary in hardware; the verified executor is the only authority over state; the
compositor extends "no deception" to pixels (output-integrity = unfoolability on
the scene). "Web-forward desktop OS" and "distributed object-capability OS" become
*the same statement about pixels.*

**Why one proof serves both.** The crown theorem is *unfoolability*
(`AssuranceCase.lean`): a light client checking only `verify root = true` learns
the whole history evolved correctly — it cannot be fooled by the pale ghost. The
desktop asks the *same* question one hop further out (can the human at the glass be
fooled? → the compositor teeth T1–T4). The swarm asks it of agents (can the
operator be fooled about what two agents coordinated? → the two independent
receipts). pg-dregg asks it of a query (can a `SELECT` return a row no verified
turn produced? → the spine invariant: reads are free SQL, state mutates only
through verified turns). It is **one anti-ghost property** re-instantiated at the
wire, the glass, the swarm, and the database. That is the coherence — and it is
why "better than nockchain" is a claim about *crystalline coherence*, not feature
count: there is one idea, proven once, carried everywhere.

---

## 5. The first ten minutes (the developer journey)

There are two front doors, because there are two first-class audiences. Each is a
copy-paste path to a *guarantee firing in front of you*.

### 5a. The agent-swarm developer (ADOS's audience)

> *"I have a coding-agent loop. I want its actions provably authorized and
> recorded without rewriting the loop."*

1. **Mint a mandate.** One SDK call (the two-noun SDK; authorization is
   inescapable — there is no `Unchecked` constructor in the public API):
   `clerk.mint(subject, caveats: [tool=read, resource-prefix="repo/foo/"])`.
2. **Wrap the one seam.** At the spot your loop already records "the agent called
   a tool," route it through `.turn(action)` instead of appending a log line. The
   loop body is untouched.
3. **Watch the refusal teach.** Ask the agent to act outside its mandate. The
   turn is **refused**, and the refusal *names the violated requirement*
   (`reason()`) — refusals that teach, not silent `USING`-predicate
   disappearances. This is the moment the developer believes it.
4. **See the swarm coordinate.** Two agents, a notify edge, two receipts. Run
   `Swarm::run_member` → a `NotifyEdge` lands in the peer's inbox →
   `Swarm::drain_notify` commits the peer's own turn. The causality is on-ledger;
   no synchronization was forced.

The evaluation artifact is one runnable end-to-end story (two agents, a budget, a
handoff, a refusal) — the demo *is* the evaluation. (`Apps/AgentOrchestrationBudget.lean`
and `Apps/EscrowDeskCouncil.lean` are the two integrator-wedge apps that refute
"this is a toy" — the six primitives, teeth in both polarities.)

### 5b. The postgres / OS developer

> *"I live in postgres / I want a verified desktop."*

- **postgres:** `CREATE EXTENSION pg_dregg;` set `dregg.issuer_pubkey`; write
  `CREATE POLICY cap_read ON documents USING (dregg_admits('read', id::text));`.
  Present an **attenuated** token, watch the rows narrow at the SQL boundary — the
  no-amplify property visible through `SELECT count(*)`. Ten-minute path:
  `pg-dregg/docs/QUICKSTART-pg-user.md`.
- **desktop:** `cd starbridge-v2 && cargo run` opens the cockpit (the runtime-Metal
  path means the window opens on a host with no offline Metal toolchain). It boots
  into a live compositor: the console plus three anchor cells as cap-confined
  surfaces over the *real* embedded executor. Hit `⌘K`, run `⚠ over-share`, and
  watch the no-amplification guarantee reject an illegitimate window grant at the
  pixel layer. Every datum (cells, caps, receipts, the image commitment) is a live
  `Inspectable`; every action is a verified turn.

Both doors land on the same epiphany within ten minutes: **the guarantee is not
documentation, it is a refusal you just triggered.**

### 5c. The pug-evaluator journey (the bar: works without ember in the loop)

The evaluator is a stranger with zero tribal knowledge. Their path:

1. **Fresh clone builds.** The known offender is FFI seeding (the Lean archive);
   the build must succeed without ember-in-the-loop. `QUICKSTART.md` commands are
   verified live.
2. **The evaluator's README answers four questions** up front: *what it IS*
   (one verified ocap substrate, four surfaces), *the guarantees*
   (unfoolability → conservation, no-amplification, tamper-evident provenance,
   the n-parametrized bounds), *the honest scope* (§6 below — what is real vs
   frontier), *the first ten minutes* (§5a/5b).
3. **One runnable end-to-end story** is the evaluation artifact: two agents, a
   trustline, a channel, a mailbox — or the budget-handoff above. The evaluator
   runs it, triggers a refusal, queries the result in SQL, and sees the same
   token authorize all three.
4. **The refusals teach** rather than mystify — every `Refusal`/`Decision` names
   what it violated, so the evaluator can poke at the edges and *understand* the
   boundary, which is how they decide it is useful for *their* purposes.

The handoff bar is judged by exactly this: a stranger reaches a useful, surprising,
*trustworthy* result in minutes, and understands why it is trustworthy. (Checklist:
`HORIZONLOG.md §HANDOFF READINESS`.)

---

## 6. The honest scope — what is real today vs the frontier

The discipline is the project's law: *a labeled seam is a severe problem with a
closure lane, never a wall; reported ≠ closed.* The honest map:

### Real today (runnable, green, the real executor in the loop)

- **The firmament bridge.** `sel4/dregg-firmament/` — one `(target, rights)`
  handle, the router, `Local`+`Distributed`+`Surface` backings, the `n=1` collapse
  witnessed, real `granted ⊆ held` at every end, the real `TurnExecutor` in the
  loop (a widening grant rejected with `DelegationDenied`, byte-for-byte the
  deployed semantics). The Lean semantics it refines lives in
  `metatheory/Dregg2/Firmament/` (CapGradation, SeL4Kernel, SeL4Composition —
  a dregg turn inside a PD preserves *both* the seL4 cap-space invariant and
  dregg non-amp, one `grantOk` witness).
- **The verified executor runs a real turn natively** — `execFullForestG`
  recompiled to ELF + linked against an ELF Lean runtime, a transfer applied on
  aarch64-linux-musl, anti-ghost holds.
- **starbridge-v2** — embeds the real executor, runs a live local world; the
  cap-first shell over real `Surface` caps (a forged cap refused on every op; the
  trusted-path identity badge drawn from the live ledger, anti-spoof); the
  agent-activity + swarm surfaces with the notify edge; cipherclerk real macaroons;
  the `⌘K` palette over every action; 105 headless tests green; the gpui window
  opens (runtime Metal).
- **The semihost** — `EmulatedKernel` (real CNode slot-table + mint/revoke
  derivation tree, promoted with Endpoint/Notification/Untyped) under the
  `sel4-microkit` facade: the same PD source runs under `cargo test` on mac/linux
  AND on real seL4 unchanged. The v1 process-backed PD closes the v0
  shared-address-space gap (the MMU enforces isolation; an epoch-tagged validity
  table refuses a forged cap).
- **pg-dregg Tier A (M1)** — `dregg_cap_admits` + RLS; an attenuated token is
  correctly narrowed at the SQL boundary; the decision is the verified `dregg-auth`
  decision (the Lean↔Rust differential is the anchor). Live on pg18.
- **The net edge** — a virtio-net driver PD probes a real device on QEMU
  (`device_type=Network`, NIC up) — the firmament touching the wire.

### Frontier (named, with closure lanes — severe problems, not walls)

- **The cutover (the live proof path).** The system runs on the IR-v1 path
  (green, deployable); the rotated IR-v2 path (−65.6% proof size) is staged and
  validated in-shape, and the live-path rewrite (`G1.5` / `C5`/`C7`) is the
  multi-day wire rewrite + Lean cohort extension that flips it and deletes v1.
  Until then the rotated path rides a feature flag. *This is the single biggest
  in-flight engineering frontier.* (`REORIENT.md` CURRENT STATE; `ROTATION-CUTOVER.md`.)
- **The l4v binary bridge.** The Lean *composition* is strong
  (`deployed_system_secure` apex; unfoolability derives conservation), but the
  distance to l4v-grade is the binary bridge: **Stage 0 = make the verified
  executor authoritative** (invert `turn/src/lean_apply.rs:1143`, "no new
  mathematics"), then spec→binary refinement / discharge `leaf_sound` / tie the
  apex to one turn / native UC / `n>1` consensus / config-pin the crypto floor.
  (`ASSURANCE-CRITIQUE.md §5`, Stages 0–6.)
- **The authorization-model integration (the deepest open thread).** dregg is
  meant to be a dual multi-aspect biscuit/macaroon/cap/zk token. Today the agent
  **macaroon** layer (federation-membership) and the kernel **cap-crown**
  (in-circuit `granted ⊆ held`) are *u.integrated* — non-amplification is told as
  two informal stories, not one proven arrow. The steer is **integrate the four
  aspects, do not reduce them**; the cipherclerk is a sovereign executor *by
  design*. (`AUTHORIZATION-MODEL.md`; possibly extends the cap-crown #103.)
- **The desktop surface op-set.** `Surface{cell}` attenuate/delegate/revoke is
  real (R0 landed); the full PRESENT/EMBED/GRANT-INPUT/REVOKE verbs + the
  compositor-PD multiplexer + the trusted-path SAK land at R3 Stage D. The
  scene-graph teeth T1–T4 are verifiable *now* in Lean (zero new axioms); the
  *last hop* — binding the scanned-out framebuffer to the cell's `contentDigest` —
  is the graphics crypto-floor (F1 frame attestation, F2 IOMMU/DMA confinement,
  F3 verified GPU compositing): named hardware-trust assumptions, the honest
  near-term stance a software compositor cell where T1–T4 are real.
- **The seL4 executor-PD (the true heart on real seL4).** WALL step 4 — host the
  ELF Lean closure on `sel4-musl` + root-task-with-std (steps 1–3 green; the
  libuv excision + GMP-for-ELF plan is a concrete checklist). The semihost has a
  real verified heart *now* on the host Lean runtime, so this gates only the
  real-seL4 target, not the product.
- **pg-dregg Tiers B/C/D.** Tier B (mirror) is GREEN-verdict and the M2 milestone
  (the commit log already *is* the schema; soundness by privilege construction).
  Tier C (verifier-in-a-CHECK) and Tier D (executor-as-a-pg-function) are
  proposed/v-future, honoring the one spine invariant.
- **`n > 1` consensus.** An n=3 slice runs the ordering rule; the frontier is
  gossip dissemination (`STAGE5-CONSENSUS-DEVAC.md`, S5-1). The single-machine
  `n=1` collapse is first-class and the bounds are honest distributed bounds —
  the same binary scales out without a rewrite.
- **The notify VK tail.** The async-signal authority (`Auth.notify`) is proven
  axiom-clean and α-total on all 7 seL4 IPC authorities; the cap-leaf badge-mask +
  verifier re-pin rides the cutover's one VK epoch. One flagged risk: a badge-OR
  is a one-bit covert channel (dregg has no noninterference argument yet).

The shape of the honesty: **the spine is real and proven; the frontiers are the
two big bridges (the cutover wire rewrite, the l4v binary bridge), the
four-aspect authorization integration, and the graphics/seL4 last-hops — each
named with its lane, none a wall.**

---

## 7. The killer demo — ONE token, four surfaces, one refusal

The demo that makes the whole vision legible in one sitting, because it exercises
the throughline rather than any one piece:

**Setup.** A swarm of two agents in starbridge-v2's SWARM tab, each a cap-confined
`Surface` cell, each holding a mandate attenuated from one root issuer. A shared
**budget cell**, opened as a window. A postgres mirror behind it.

**The run (everything on screen, live, in-process, the real executor):**

1. **Mint once, carry everywhere.** Mint one `dga1_…` token at the root. It is
   the *same string* that (a) gates the agent's tool turns, (b) is the cap behind
   the agent's pane, (c) authorizes a `SELECT` against the postgres mirror. *One
   token, four surfaces.*
2. **Agent A acts in-mandate.** A commits a cap-gated turn (spend from the budget).
   The balance moves on the budget *window* (Surface re-reads the live ledger);
   a receipt appears in the blocklace panel; conservation holds.
3. **Agent A hands off to B via the notify edge.** A `EmitEvent` turn deposits a
   wake in B's inbox; B drains it in its own turn. Two independent receipts; the
   causality A→B is on-ledger and visible in the dynamics stream. *The operator
   cannot be fooled about what they coordinated.*
4. **THE REFUSAL (the climax).** Agent B, compromised, tries to (a) widen its
   mandate to spend more than granted, AND (b) promote its read-only view of the
   budget *window* to writable. **Both are rejected by the same `granted ⊆ held`
   gate** — once as `DelegationDenied` on the turn, once as `⚠ over-share` at the
   pixel layer. The same no-amplification law, fired at the swarm seam and at the
   glass, from the same lattice. *This is the moment the four pieces visibly
   become one.*
5. **Query the truth in SQL.** The operator runs
   `SELECT * FROM dregg.capabilities WHERE subject = 'agentB';` against the mirror,
   RLS-gated by the same token, and sees exactly B's *narrowed* authority — no
   trace of the rejected widening, because no verified turn ever produced it. The
   explorer is the capabilities, expressed as the rows you may `SELECT`.

**What it proves in one breath:** one handle, one gate, one record — carried from
a mandate, to a pane, to a wire handoff, to a SQL row, with the no-amplification
guarantee firing identically at every surface, and the refusal *teaching* why.
A swarm made auditable without trusting the loops; a desktop made unfoolable to the
human; a database made a verified dregg surface — *the same mechanism, four times.*

The minimal first cut of this demo is buildable **now** (see below) entirely in
starbridge-v2's embedded world + the pg-dregg Tier-A/B mirror, with zero
dependence on the cutover or real seL4.

---

## 8. What is buildable NOW (wide-safe, off the cutover's critical path)

These slices advance the unifying story without touching the live proof path or
the seL4 walls — each is a separate-workspace or additive-Lean slice in the
spirit of the executor-state bridge (#180) and the channels weld (#181): one green
test against the real executor, no VK churn.

1. **The four-surface killer-demo cut (the headline).** In starbridge-v2's
   embedded world, wire steps 1–4 of §7 (mint → agent turn → notify handoff →
   the dual refusal) as a `--headless` self-check + a SWARM-tab live path, then
   add the pg-dregg Tier-A read of step 5 against a local mirror. All in
   already-green crates; the demo *is* the pug evaluation artifact.

2. **pg-dregg Tier B (mirror) — M2.** Project `CommitRecord` into
   `dregg.turns`/`dregg.cells`/`dregg.capabilities` via a crash-safe commit-log
   tailer from `commit_cursor()`. Soundness by privilege construction
   (`dregg_reader` gets `SELECT` only). GREEN-verdict; standalone `pg-dregg/`
   workspace, no `./target` contention. Makes "your node IS your postgres" real
   and makes step 5 of the killer demo a true query rather than a mock.

3. **The `Surface` op-verbs as turns (R1 in starbridge-v2).** Land a surface
   `FactoryDescriptor` + `present()` as a real turn with the anti-ghost tooth
   (overpaint/label-spoof/double-focus REJECT) and a `SurfaceDamaged` dynamics
   event + a gpui panel — the transfer-triangle for the desktop, on mac Metal
   today, on the host Lean runtime. Companion: the `Compositor` `AppSpec` via the
   existing `VerificationToolkit` so `app_commit_iff_admit` +
   `app_violation_rejected` come free, with `#guard` teeth that bite.

4. **The notify-edge swarm hardening (ADOS A2).** The notify async signal is the
   missing primitive for swarm coordination; `metatheory/Dregg2/Firmament/`
   `NotifyAuthority`/`NotifyOrgans` are landed axiom-clean. Build the swarm
   coordinator's drain-loop end-to-end in the embedded world (gpui-free,
   `cargo test`-able), so N agents coordinating via wakes is a runnable demo, not
   a design. (The cap-leaf badge-mask VK tail rides the cutover — keep this slice
   VK-free.)

5. **The integrator-wedge apps as the lamesauce refutation.** Extend
   `Apps/AgentOrchestrationBudget.lean` + `Apps/EscrowDeskCouncil.lean` (the six
   primitives buildr/builders/sig/simbi hand-roll, teeth both polarities) into
   *runnable* SDK demos a stranger copy-pastes — the concrete proof that real apps
   don't scream "toy." These exercise the cross-cell-import crown
   (`importValid_stable_under_source_advance`) and the new cell-program atoms
   (senderMemberOf / affineDeltaLe / balanceDeltaLe-Ge).

6. **The evaluator's README + the consistent front door.** Write the
   stranger-usable evaluator README (what-is / guarantees / honest-scope / first
   ten minutes), re-verify `QUICKSTART.md` post-rotation, and make the site teach
   the one-handle story (present-tense, first-principles, no trajectory
   narration). This is the handoff-readiness burn-down, not new code, and it is
   what turns "we built a pile" into "a stranger can evaluate it."

Each is wide-safe (separate workspace or additive Lean), none is blocked on the
cutover, and together they make the §7 killer demo runnable and the §5 journeys
real — which is exactly the refinement epoch's bar: *usable, general, teaches
what-is, no toys.*

---

*One capability handle, reached through one router, recorded as one kind of turn,
proven once and carried everywhere: to the slot, the cell, the glass, the row, and
the agent's next action. The desktop is the firmament made visual; pg-dregg is the
firmament made queryable; the swarm is the firmament made coordinated; and the
proof that a light client cannot be fooled by the pale ghost is the same proof
that the human at the glass, the operator over the swarm, and the analyst over the
database cannot be fooled either. That single coherence — not a feature count — is
what "better than nockchain" means.*
