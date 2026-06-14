# THE FRONTIER ROADMAP — one capability handle, four glasses, one prioritized build

*Synthesis of the five design frontiers (`docs/design-frontiers/ADOS.md`,
`WEB-FORWARD.md`, `AGENT-SWARM-UX.md`, `PG-DREGG-DX.md`, `UNIFYING-STORY.md`) into
one buildable roadmap. North star, not rigid spec — present-tense, first-principles,
teach-what-is. The vision shapes intuition; the **build list is the deliverable**:
what builds NOW (wide-safe, concurrent with the cutover), what lands at the
cutover-settle, what is research. Each frontier's full elaboration lives in its own
doc; this weaves them and orders the work.*

> Grounding (verified on disk, the welds this rides): `starbridge-v2/src/swarm.rs`
> (the swarm seam, gpui-free, tested), `sel4/dregg-firmament/src/surface.rs` (the
> surface cap, the widening-refusal test green), `metatheory/Dregg2/Firmament/
> NotifyAuthority.lean` (the async-signal authority, axiom-clean), `node/src/
> pg_mirror.rs` (the live node→pg writer), `wasm/src/runtime.rs` (the in-tab dregg
> world), `web/spike/build-executor-wasm.sh` (the Lean-executor-in-wasm attempt),
> `metatheory/Dregg2/Apps/AgentOrchestrationBudget.lean` (the integrator-wedge app).
> Wide-safety is a fact of the build graph: the root workspace `exclude`s `wasm`,
> `pg-dregg`, `sel4/dregg-firmament`; `starbridge-v2/` is its own workspace; the
> `site/` is static. None of these is gated by the VK rotation / kernel cutover.

---

## 1. The vision in one breath

**dregg is the verified accountability substrate: one unforgeable
`Capability{target, rights}` handle, reached through one router, whose every
invocation is a turn the kernel actually ran — carried without a seam from a local
seL4 slot, to a cell on a remote federation, to a window on glass, to a row in
postgres, to an agent's next tool call.** A swarm of coding agents and a houyhnhnm
desktop become *provably* authorized, recorded, budgeted, and coordinated without
anyone trusting the loops, the apps, the panes, or the queries. The loop —
perceive/plan/act/reflect — lives ABOVE dregg and is not ours to own; dregg grounds
the one seam where the loop touches the world, and re-instantiates **one anti-ghost
property** at every surface: the pale ghost cannot fool a light client at the wire,
a human at the glass, an operator over a swarm, or an analyst over a database. The
bumper sticker: *better than nockchain — crystallinely coherent, l4v-grade, no toys;
one idea (unfoolability), proven once, carried everywhere.*

---

## 2. The throughline — the firmament router is the spine, the four frontiers are its arms

The four "products" are not four products sharing a library. They are the **four
surfaces an authority decision lands on**, each a `Target` arm of the *same* handle,
each gating on the *same* `granted ⊆ held` lattice (`is_attenuation`, the real
`dregg_cell::AuthRequired` partial order), each resolved by the *same* real
`TurnExecutor`. Only the distance parameter `n` slides the **bounds**
(immediate↔eventual revocation, synchronous↔quorum commit, consistent↔stale
checkpoint) — **never the verbs**.

```
                       ┌──────────────────────────────────────────────┐
                       │           Capability { target, rights }       │
                       │   ONE handle · holder can't tell the backing  │
                       └──────────────────────┬───────────────────────┘
                                              │  FirmamentRouter::resolve
                                              │  (dispatch by target alone)
   ┌──────────────┬──────────────────┬────────┴────────┬──────────────────┬──────────────┐
   ▼              ▼                  ▼                 ▼                  ▼              ▼
 Local{slot}  Distributed{cell}  Surface{cell}      (pg row)        (agent turn)   (browser canvas)
 seL4 CNode   a cell on a fed-   a cell rendered    a SQL row       the tool-call  Surface{cell}
 slot;        eration; invoke    as glass; invoke   gated by the    seam: an       resolved in a
 mint/revoke  = a real exec-     = present/focus/   SAME dga1_…     agent's action tab; present()
 syscall;     utor turn; rev =   grant-input as a   token; dregg_   committed as a paints a canvas
 revoke       group-key epoch    turn; share =      admits IS the   cap-gated      iff requested
 immediate    lift               GrantCapability    SAME decision   receipted turn ⊆ held
 (n=1)                           turn
   └──────────────┴──────────────────┴─────────────────┴──────────────────┴──────────────┘
                          ALL gate on  granted ⊆ held  (is_attenuation),
                          on the SAME real executor / the SAME proved lattice.
                          Only the BOUNDS slide along the distance parameter n.

   FRONTIER MAP:   firmament = the spine (Local + Distributed)
                   AGENT-SWARM / ADOS = the agent-turn seam (woven through Distributed + Surface + a budget cell)
                   DESKTOP            = Surface{cell} on native glass
                   WEB-FORWARD        = Surface{cell} on a browser canvas + the light client in the tab
                   PG-DREGG           = the (pg row) arm — the same token, a fifth landing point
```

**The single disease, in all four registers:** authority is asserted out-of-band,
and recorded in something the secret-holder can lie about. **The single cure, in all
four registers:** make authority a capability the kernel enforces in-band, and make
the record a turn whose proof a stranger can check. That is why the four cohere —
there is only ever **one handle, one gate, one record**, and these are the surfaces
you can be holding it at.

### The one act that flows through all of it

An agent, holding an attenuated mandate, shares a read-only view of a budget cell
with a sub-agent, who reads it, while an operator watches and queries it in SQL —
and there is genuinely **one mechanism**, not four glued together:

1. **The mandate is a capability** — `Capability{Distributed(budgetCell), read-only}`,
   attenuated from its grantor through `granted ⊆ held`. It physically cannot widen.
2. **The share is a turn** — a real `Effect::GrantCapability` through the real
   executor; a widening share is rejected with `DelegationDenied` (the deployed
   semantics, not a lint).
3. **The pane is the same capability** — open the budget cell as a `Surface{cell}`
   window; sharing the *window* read-only is the same `GrantCapability` on the same
   lattice; promoting it to writable is the same `DelegationDenied`, now firing **at
   the pixel layer** (the `⚠ over-share` teaching moment).
4. **The wake is the notify edge** — the sub-agent commits an `EmitEvent` turn
   depositing a pending wake; the agent drains it in its **own** future turn (async,
   not a joint turn); two independent receipts record the causality A→B.
5. **The budget is conserved** — every spend is a turn; Stingray conservation makes
   the shared budget atomic; a runaway cannot drain it because there is no path to
   mutate the cell except a turn the executor accepted.
6. **The record is queryable** — the commit log projects into `dregg.cells` /
   `dregg.turns` / `dregg.capabilities`; the operator's `SELECT ... WHERE
   subject = agentB` is RLS-gated by the *same* token and shows exactly B's narrowed
   authority — no trace of the rejected widening, because no verified turn produced it.

One handle (1). One gate, `granted ⊆ held` (2–3). One record, a turn with a receipt
(4–6). The desktop, the browser, the swarm, and the database never see a different
authority model — they see the same one, at a different `Target`, with the bounds
relaxed as far as `n` demands.

---

## 3. The prioritized, swarm-safe build roadmap

The discipline (verified above): every NOW slice lives in a workspace that does NOT
contend with the in-flight VK rotation / kernel cutover — `starbridge-v2/` (own
workspace), `pg-dregg/` + `wasm/` + `sel4/dregg-firmament/` (root-`exclude`d), the
static `site/`, or additive-Lean modules that do not churn the VK. Each NOW slice
lands by its own `cargo test` / `lake build` against the **real** embedded executor.
The cutover-settle and research tiers are named, not laundered.

Ordering principle: **the four-surface killer demo (§4) is the spine**, so the NOW
tier front-loads exactly the slices that make it runnable, then broadens to the full
developer surface across all four frontiers.

### TIER NOW — builds concurrently with the cutover (wide-safe)

Ordered by leverage. The **`[demo]`** tag marks a slice the §4 headline demo
consumes directly.

**N1 — The swarm budget meter `[demo]`** *(starbridge-v2; pure headless weld)*
Add a `BudgetMeter` to `Swarm`: per-member `spent` (running sum of the metered
computrons already on each `SwarmActionOutcome`) + an optional `ceiling`, and an
aggregate `SwarmBudget{total_ceiling, total_spent, headroom}`. Extend `Swarm::run`
to **refuse** a dispatch that would breach the ceiling (`SwarmError::BudgetExhausted`)
*before* the turn runs — fail-closed, no commit. Extend `SwarmView` with the meter
fields. Tests against the real executor: under-ceiling commits + `spent` grows by the
metered computrons; a breach is refused with no height advance; the aggregate sums
correctly. *Closes simbi's "a runaway could drain \$1000s" at the seam.* (Stingray is
the floor model here; the verified `StingrayCounter` weld is N9.)

**N2 — pg-dregg Tier B mirror `[demo]`** *(pg-dregg / node; standalone workspace +
node-additive behind `DREGG_PG_MIRROR_URL`)*
Project `CommitRecord` into `dregg.turns` / `dregg.cells` / `dregg.capabilities` via
the crash-safe commit-log tailer from `commit_cursor()` (the live
`pg_mirror.rs::PgSink` is the write side; this is its read-side completion). Soundness
by privilege construction (`dregg_reader` gets `SELECT` only; the only writer is
`dregg_kernel`). The schema is emitted from the same Rust that defines the row types
(`mirror::ddl::tier_b`), pinned by `emitted_ddl_agrees_with_committed_sql_file`. Makes
"your node IS your postgres" real and turns the demo's step 5 into a true query.

**N3 — The swarm dispatch bar `[demo]`** *(starbridge-v2; the keystone that turns the
demo panel into a driving surface)*
Generalize the 3 hardcoded demo verbs into a `SwarmDispatch` builder (member + a
`SwarmCommand` verb + target → effects → `Swarm::run`). Add `Swarm::can_reach(agent,
target)` reading the live c-list so the UI greys unreachable targets and **predicts**
the refusal; a new ⌘K palette `CommandId` per verb, dispatched through the same `&mut
Cockpit` method (no second action path). Tests: the builder assembles the right
effects; `can_reach` agrees with the cap-gate; a predicted-refused dispatch is in fact
refused by the executor.

**N4 — The notify-edge swarm coordinator, end-to-end `[demo]`** *(starbridge-v2;
gpui-free, `cargo test`-able; keep VK-free)*
`NotifyAuthority` / `NotifyOrgans` are landed axiom-clean. Build the swarm
coordinator's drain-loop end-to-end in the embedded world so N agents coordinating via
async wakes is a **runnable demo, not a design**: a coordinator commits an `EmitEvent`
turn → a `NotifyEdge` lands in the recipient's inbox → the recipient drains it in its
OWN separate ack turn (two independent receipt hashes — causality visible, independence
proven). Tests already assert the load-bearing shape (`an_emit_event_to_a_member_
deposits_a_notify_edge_in_its_inbox`, `the_drain_is_the_recipients_own_separate_turn_
not_a_joint_turn`); this widens it to the full N-member coordinator loop. *The async
wake is the dregg-native answer to buildr's `--wake`, made all-or-nothing and
auditable. The badge-mask sub-lattice rides the cutover (see C1) with no UX change.*

**N5 — The four-surface killer-demo cut `[demo, headline]`** *(starbridge-v2 +
pg-dregg; already-green crates)*
Wire §4 steps 1–4 (mint → agent turn → notify handoff → the dual refusal) as a
`--headless` self-check **and** a SWARM-tab live path, then add the N2 Tier-B read for
step 5 against a local mirror. Zero dependence on the cutover or seL4. **The demo IS
the pug evaluation artifact** — the single runnable end-to-end story a stranger runs to
judge whether the substrate is real and usable.

**N6 — The narration-vs-truth panel** *(starbridge-v2; pure UI over existing data)*
A first-class view that puts a member's *claimed* action (supplied by its loop
alongside the turn) next to the executor's receipt — **or the absence of one** — and
flags divergence. This is the sharpest single ADOS feature: the moment the pale ghost
is caught at the glass. Pure UI over `Swarm::action_log` + the dynamics stream. (Its
full power — correlating a *specific* claim to its turn — needs the tool-call→effect
compiler, R1; the divergence panel itself ships now.)

**N7 — The surface op-verbs as turns (desktop R1)** *(starbridge-v2; mac Metal today,
host Lean runtime)*
Land a surface `FactoryDescriptor` + `present()` as a real turn with the anti-ghost
teeth (overpaint / label-spoof / double-focus REJECT) + a `SurfaceDamaged` dynamics
event + a gpui panel — the transfer-triangle for the desktop. Companion: the
`Compositor` `AppSpec` via the existing `VerificationToolkit` so `app_commit_iff_admit`
+ `app_violation_rejected` come free, with `#guard` teeth that bite. *T1–T4 are Lean
theorems over the scene graph today, zero new axioms; the last hop (framebuffer
attestation) is the named graphics frontier (R5).*

**N8 — pg-dregg: the queue drainer (close the write loop)** *(node; behind the opt-in
flags; PG-DREGG's "highest leverage")*
`dregg_submit_turn` enqueues into `dregg.submit_queue` today, but the shipped path has
**no drainer** — status never walks `pending → executed | refused`. Build the node-side
`LISTEN/NOTIFY` loop that tails `submit_queue` (the symmetric read-side of `pg_mirror`'s
write side), feeds each signed turn to the real verified executor, and writes back
`status` + `receipt_hash` / `error`. A new node service module sibling to
`channels_service.rs`. *Single most load-bearing pg gap; unblocks the demo's atomic-
checkout punch in its outbox form.*

**N9 — The Stingray ceiling weld (atomic shared budget)** *(starbridge-v2)*
Replace N1's floor model with a real `dregg_coord::StingrayCounter` as the swarm's
shared budget, wired the way `sdk runtime.rs::attach_budget` does. The conservation
invariant makes "the swarm spent at most B" **provable**, not best-effort. Tests: the
budget conserves (drawn = sum of metered across members); a draw past the ceiling is
refused; the aggregate meter reflects the counter. *The depth lift from a UI counter to
a verified conservation bound — simbi's gap closed for real.*

**N10 — The web surface binding in `dregg-wasm`** *(wasm; root-excluded, the keystone
for the browser face)*
Add ~5 `#[wasm_bindgen]` fns mirroring `surface.rs` over the existing `DreggRuntime`
ledger+executor: `open_surface(cell)`, `present(surface, region, contentDigest)`
(checks `requested ⊆ held`), `share_surface(from, to, surface, narrower)` (a real
`Effect::GrantCapability` turn; widening REJECTS), `revoke_surface`,
`surface_identity(surface)` (returns `(owningCellId, lifecycle, sourceStateRoot)` from
the live ledger — the T2 badge source). Same shape as the ~80 bindings already in
`bindings.rs`. *Carries `Target::Surface` to the tab; the smallest change that makes "a
browser surface = a cell's cap" callable from JS.*

**N11 — The browser compositor module** *(site/ frontend; NEW, tiny)*
A gpui-free scene-graph — the DOM sibling of `starbridge-v2`'s `shell::Shell::compose`:
an ordered surface list, each pane drawn to a `<canvas>` with **compositor-drawn
identity chrome** (the T2 badge from N10, NEVER the page's), DOM focus/pointer routed to
the single focused pane (T3), T1 non-overlap on `present`. Port the proven float/tile/
stack layouts + the protected console. *The firmament-to-pixels weld in the browser.*

**N12 — `verify_history` in the tab (the anti-pale-ghost tooth)** *(wasm + site/)*
Compile `dregg-lightclient::verify_history` to wasm (deps: `dregg-circuit` recursion +
`dregg-blocklace`, both wasm-buildable); expose `verify_devnet_history(root, vkAnchor)
-> AttestedHistory`; add a "verify the whole history yourself" button to the explorer +
playground. The VK anchor is genesis/checkpoint config, never taken from the artifact
under verification. *The moment dregg's thesis becomes tactile in a browser: you did
not trust the server, you checked it. Carries the lightclient's named floor surfaced in
the UI, not hidden.*

**N13 — The web killer-demo playground page** *(site/; static, the web evaluation
artifact)*
Wire N10+N11+N12 into `site/playground` as **"two tabs, one surface, the share that
REFUSES"** (§4 web cut): open a cell as a canvas pane, share it read-only, watch an
onward writable share REJECT with the `⚠ over-share` banner, revoke (dark THIS frame at
n=1), and run `verify_history`. The copy-paste end-to-end story for the pug handoff,
reachable from a URL.

**N14 — The SDK two-noun browser front door** *(sdk-ts; no crypto reimplemented)*
Finish `sdk-browser-ed25519-webcrypto`: back `Identity` with WebCrypto/@noble ed25519
so the FULL acting surface (`Identity → .turn() → .sign() → .submit() → Receipt`)
bundles for the browser, not just the fetch-only organs. Authorization stays inescapable
(no `Unchecked` constructor in the public API). *A `.turn()` from a tab against the
devnet becomes a real signed turn.*

**N15 — The cap-gated query cookbook + the caps-as-rows explorer** *(pg-dregg SQL/docs
+ site/; pure SQL + static, zero build risk)*
Ship parameterized RLS-gated views + recursive queries as copy-paste recipes — the
delegation tree (`WITH RECURSIVE` over `cap_edges`), the conservation check
(`sum(balance) = genesis`), per-cell time-travel, the receipt-chain walk with an in-SQL
non-omission assertion (`prev_root = lag(ledger_root)`), the no-amplification audit
(`cap_attenuations` vs grantor). Reframe `site/explorer` as **"your capabilities,
expressed as the rows/cells you may read"** — the same "a cap IS a view" insight, one
glass in SQL, one in the browser.

**N16 — The per-member authorization boundary + anti-spoof identity** *(starbridge-v2;
render weld over existing models)*
Reuse `agent.rs::AgentActivity` to render, per swarm member, the full held mandate
(every `MandateEdge` with rights/facet/expiry) and the CAN/CAN'T authorization boundary;
the identity badge drawn from the live ledger (the T2 label-binding — a member cannot
masquerade). Tests: the mandate view matches the cell's real c-list; the CAN set is
exactly the reachable+permitted verbs; a sealed backing cell reads its lifecycle
honestly.

**N17 — The coordination graph** *(starbridge-v2; gpui-free model + thin panel)*
A `SwarmGraph` model: nodes = members, notify arrows = the deposited `NotifyEdge`s,
mandate edges = the fainter reach graph, a deterministic layout; the panel animates
arrows on land/drain. Tests: the graph arrows match the deposited notify edges; the
mandate background matches the cap-graph. *The causal shape made visible without
implying synchronization.*

**N18 — The cipherclerk trusted-path strip (identity + attenuation lineage)**
*(starbridge-v2; the gesture-to-turn tooth is C-tier, see C2)*
Bind the existing CIPHERCLERK surface to the selected swarm member: ledger-drawn
identity (NOT self-reported) + the mandate's real macaroon attenuation lineage (root →
confined → delegated). Tests: the lineage matches a real mint→attenuate→delegate chain;
the identity is ledger-drawn. *The near-term trusted-path anchor; the attested-volition
gesture (binding "the operator clicked" to a turn premise) lands with the compositor-PD
work (C2).*

**N19 — In-SQL dev minting + issuer-status discoverability** *(pg-dregg; standalone
workspace, dev path only)*
Add `dregg_dev_mint(subject, actions[], resource_prefix, ttl)` composing the common
caveat shape so a newcomer never hand-writes `Pred` JSON, plus a loud
`dregg_issuer_status()` so the "no key ⇒ everything denies" failure mode is
**discoverable**, not silent. Production mint-out-of-database (the private key never
enters the DB) stays the default. *Kills the on-ramp's first friction.*

**N20 — The integrator-wedge apps as runnable demos** *(metatheory additive-Lean +
SDK; the lamesauce refutation)*
Extend `Apps/AgentOrchestrationBudget.lean` + `Apps/EscrowDeskCouncil.lean` (the six
primitives buildr/builders/sig/simbi hand-roll, teeth in BOTH polarities) into runnable
SDK demos a stranger copy-pastes — exercising the cross-cell-import crown
(`importValid_stable_under_source_advance`) and the new cell-program atoms
(`senderMemberOf` / `affineDeltaLe` / `balanceDeltaLe-Ge`). *The concrete proof that
real apps don't scream "toy."*

**N21 — The fresh-clone build story + the evaluator's README** *(pg-dregg setup +
docs; the handoff-readiness burn-down)*
`pg-dregg/scripts/setup.sh` (checks `cargo-pgrx` + managed pg18, prints exact install
commands if absent, installs the extension, sets the dev issuer key, runs `e2e-live.sh`)
+ a stranger-usable evaluator README answering four questions up front: *what it IS*
(one verified ocap substrate, four+ surfaces), *the guarantees* (unfoolability →
conservation, no-amplification, tamper-evident provenance, the n-parametrized bounds),
*the honest scope* (§5), *the first ten minutes* (§4). Re-verify `QUICKSTART.md`
post-rotation; make the site teach the one-handle story present-tense. *Turns "we built
a pile" into "a stranger can evaluate it."*

### TIER CUTOVER-SETTLE — lands when the VK/encoding epoch settles

These ride the cutover's one VK epoch (a circuit/encoding bump) and so are held until
the IR-v2 live-path rewrite flips and v1 is deleted. The NOW UX is final; these drop in
*without UX change*.

**C1 — The dedicated `notify(target, badgeMask)` authority** — the fourth **Synchrony**
dial: the right to cause a WAKE without read/send/reply. `NotifyAuthority.lean` is the
axiom-clean keystone; Step 2 (the `Auth.notify` constructor + α-totalization + felt-
encoder / VK bump, ~9 mechanical arms) is HELD for the cutover-settle. The badge-mask
sub-lattice (`[.notify]` = "may poke, not message") rides the SAME non-amplification the
firmament mint proves; it drops into the swarm cockpit's inbox model (N4) with no UX
change. *Today the edge rides `EmitEvent` — real and receipted; the dedicated authority
is the deeper expressivity.*

**C2 — The attested-volition gesture (the trusted-path compositor tooth)** — binding
"the operator clicked" to a turn premise: a signed input-receipt the executor requires,
the DREGG-DESKTOP-OS §5 property needing the compositor-PD signed-input-receipt
machinery (R3 Stage D). N18 ships the identity + lineage strip now; this is the
gesture-to-turn binding that makes a value-moving dispatch carry proof a real operator
authorized it.

**C3 — The Tier-D spike: `dregg_submit_turn_inproc`** — the executor as a pg function:
one transaction that mutates dregg kernel state AND the app's own tables atomically.
The structural payoff no node-beside-database can offer. Depends on linking the Lean
executor into a postgres backend; the spike answers (a) the executor's side-effect
surface is the in-process kernel-state map the mirror already projects; (b) the
FFI/palloc-context lifetime is compatible with a backend (the known risk); (c) proving
stays OFF the transaction path. The `tier-d` cargo feature declares the path; this
decides feasibility and collapses the demo's outbox-form punch into true cross-domain
atomicity. *Gated on the same FFI maturity as the executor-PD work, not the VK per se;
sequenced here because it co-moves with the executor-authoritative inversion (R0).*

### TIER RESEARCH — named, with closure levers, never walls

**R0 — Make the verified executor authoritative (l4v Stage 0).** Invert
`turn/src/lean_apply.rs:1143` so the Lean producer IS the executor, "no new
mathematics." The prerequisite for the binary bridge and for C3. (`ASSURANCE-CRITIQUE.md
§5`, Stage 0.)

**R1 — The tool-call → effect compiler (the ADOS SDK boundary).** The universal adapter
`ToolCall → Vec<Effect>` (one per provider, e.g. MCP `tools/call`). `swarm.rs` runs
effects today; this is the genuinely-new buildable surface. Closure lever: an audited
per-provider adapter with a golden-corpus differential, named as the trust boundary —
the same boundary pg-dregg draws (the *decision* is verified, the *integration*
conventional). *Note: a wrong mapping yields a faithful receipt of the wrong thing; the
seam is honest only if the mapping is.*

**R2 — Token/dollar budget binding.** The executor meters *computrons*, not API dollars;
binding needs a declared-cost debit + a price oracle. Until then the "provable ceiling"
is over computation, and the dollar story is bounded-by-a-declared-rate. The
conservation machinery is there; the dollar mapping is honest-future.

**R3 — The Lean executor in wasm (WEB-FORWARD F2, highest web leverage).** Compile
`execFullForestG` to wasm32 — a build already in flight in
`web/spike/build-executor-wasm.sh`. Named obstacles characterized (libuv coupling at
runtime init — the same excision the seL4 executor-PD faces; GMP-for-wasm or a fixnum-
only shim; the `-flto` i1-vs-i8 signature-lowering hazard). When it lands, the tab runs
the SAME verified semantics as the federation's authoritative producer with no new
trust. *Until then the in-tab world is "Rust, differential-anchored," advertised loudly,
NOT "verified-in-browser."*

**R4 — Spawning the loop itself as a managed process.** A microVM / seL4 app-PD per
agent so the loop's *isolation* (not just its actions) is dregg-enforced. Today the loop
is external and only the seam is the contract; the firmament's app-PD model is the path.

**R5 — The graphics crypto-floor (the last hop).** Binding the scanned-out framebuffer
to the cell's `contentDigest`: F1 frame attestation, F2 IOMMU/DMA confinement, F3
verified GPU compositing (native); in the browser, F1 narrows to a trusted-chrome anchor
(an extension overlay at a z-index no page CSS can exceed + a reserved chord), F3 leans
on the same-origin/iframe sandbox (the web's IOMMU-equivalent). dregg mediates AUTHORITY
(which cell owns the region, verified); the hardware/browser mediates ISOLATION (named
primitive). *T1–T4 are theorems over the scene graph today; the frontier is honestly
the I/O edge.*

**R6 — The four-aspect authorization integration (the deepest open thread).** The agent
MACAROON layer (federation-membership) and the kernel CAP-CROWN (in-circuit `granted ⊆
held`, #103) are currently UNINTEGRATED — non-amplification is told as two informal
stories, not one proven arrow. The guardrail: **integrate the four aspects (biscuit /
macaroon / cap / zk), do NOT reduce them**; the cipherclerk is a sovereign executor by
design. (`AUTHORIZATION-MODEL.md`.)

**R7 — `n > 1` federation (the bounds relax along `n`).** The remote swarm trades the
n=1 collapse for eventual revocation + quorum commit; the cross-image coordination graph
(N17) and the cross-node shared budget (N9) are the same models over the peer view; a
remote browser surface ships state+proof and is self-attesting (Croquet inverted). An
n=3 slice runs the ordering rule; the frontier is gossip dissemination. *The single-
machine n=1 collapse is first-class and its bounds ARE honest distributed bounds — the
same binary scales out without a rewrite.*

**R8 — Noninterference (the notify covert channel).** A badge-OR wake is a one-bit
info-flow leak; dregg has no noninterference argument yet. Sound as coordination, leaky
as an isolation boundary. The cockpit shows the topic (the leaking bit) rather than
pretending the wake is information-free. (Research pillar #31/#99.)

**R9 — The l4v binary bridge (post-R0).** Spec→binary refinement / discharge
`leaf_sound` / tie the apex to one turn / native UC / config-pin the crypto floor.
(`ASSURANCE-CRITIQUE.md §5`, Stages 1–6.) The Lean *composition* is strong today
(`deployed_system_secure` apex; unfoolability derives conservation); l4v-grade is the
binary bridge.

---

## 4. The killer demos + first ten minutes + the pug-evaluator journey

### The headline killer demo — ONE token, four surfaces, one refusal

All live, in-process, on the real embedded executor in starbridge-v2's SWARM tab (the
minimal cut is buildable NOW via N1–N5 + the N2 mirror):

1. **Mint once, carry everywhere.** One `dga1_…` token at the root issuer. It is the
   SAME string that gates an agent's tool turns, is the cap behind the agent's pane, AND
   authorizes a `SELECT` against the postgres mirror. *One token, four surfaces.*
2. **Agent A acts in-mandate.** A commits a cap-gated spend from the shared budget cell;
   the balance moves on the budget WINDOW (Surface re-reads the live ledger); a receipt
   appears; conservation holds; the budget meter climbs.
3. **A hands off to B via the notify edge.** An `EmitEvent` turn deposits a wake in B's
   inbox; B drains it in its OWN turn. Two independent receipts make the causality A→B
   on-ledger and visible. *The operator cannot be fooled about what they coordinated.*
4. **THE REFUSAL (the climax).** Compromised Agent B tries to (a) widen its mandate to
   overspend AND (b) promote its read-only budget-window view to writable — **BOTH
   rejected by the same `granted ⊆ held` gate**, once as `DelegationDenied` on the turn,
   once as `⚠ over-share` at the PIXEL layer; the budget breach refused
   `budget-exhausted`. The same no-amplification law fired at the swarm seam AND at the
   glass from the same lattice. *The moment the four pieces visibly become one.* B
   *claims success in its own log*; the narration-vs-truth panel (N6) shows the claim
   next to the receipt-that-never-was. *The pale ghost caught at the glass.*
5. **Query the truth in SQL.** `SELECT * FROM dregg.capabilities WHERE subject='agentB'`,
   RLS-gated by the same token, shows exactly B's NARROWED authority — no trace of the
   rejected widening, because no verified turn ever produced it.

**Proves in one breath:** one handle, one gate, one record — carried from a mandate to a
pane to a wire handoff to a SQL row, the guarantee firing identically at every surface,
and the refusal *teaching* why.

### The web killer demo — TWO TABS, ONE SURFACE, the share that REFUSES

The browser face (buildable via N10–N13): Alice opens a cell as a `<canvas>` pane whose
title bar (`cell a3f1… · live · root 7c2e…`) is drawn by the compositor from the live
ledger, not the pane. She shares it read-only with Bob (a real `GrantCapability` turn);
Bob composites the SAME surface. Bob tries to share it onward as WRITABLE — the executor
REJECTS with `DelegationDenied`, the `⚠ over-share` banner flashes (no-amplification at
the pixel layer). Alice revokes Bob's pane: dark THIS frame (n=1, synchronous). Bob runs
`verify_history` against the devnet root and prints `AttestedHistory ✓ (N turns,
re-witnessed nothing)` — *he confirmed the pane he saw was the genuine projection of a
verified history, himself.*

### The pg killer demo — atomic cap-gated checkout

The data-surface face (punches 1/2/4 live NOW on Tier A/B/C via `scripts/e2e-live.sh`;
punch 3 in outbox form via N8, collapsing to true atomicity at C3): a buyer's token
narrows both `SELECT * FROM orders` and `dregg.cell_balances`; a delegated shipping agent
(read, no pay) is REFUSED at enqueue by the `submit_gate`; ONE transaction `BEGIN; UPDATE
orders SET status='paid'; SELECT dregg_submit_turn_inproc(:signed); COMMIT;` ships the
order and moves the balance or NEITHER; the receipt chain is a light client in SQL
(`prev_root = lag(ledger_root)`).

### The first ten minutes (two front doors, one epiphany)

**The agent-swarm / web developer:** mint a mandate (one SDK call, authorization
inescapable) → wrap the one seam (route "the agent called a tool" through `.turn()`
instead of a log line) → **watch the refusal teach** (act outside the mandate; the
refusal NAMES the violated requirement) → see the swarm coordinate (two agents, a notify
edge, two receipts). Or, web-first: open the site, play locally in the tab (a complete
n=1 world, zero backend), **verify the whole history yourself**, then surface a cell and
watch the over-share refuse.

**The postgres / desktop developer:** `CREATE EXTENSION pg_dregg;` + one GUC + `CREATE
POLICY ... USING (dregg_admits('read', id::text))`; present an attenuated token, watch
the rows narrow at the SQL boundary. Or `cd starbridge-v2 && cargo run`, hit ⌘K, run
`⚠ over-share`, watch the no-amplification guarantee reject an illegitimate window grant
at the pixel layer.

**Both doors land on the same epiphany within ten minutes: the guarantee is not
documentation, it is a refusal you just triggered.**

### The pug-evaluator journey (the bar: works without ember in the loop)

A stranger with zero tribal knowledge: (1) **fresh clone builds** — the known offender is
FFI seeding; `QUICKSTART.md` / `setup.sh` (N21) succeed without ember-in-the-loop; (2)
**the evaluator's README answers four questions** up front (what-is / guarantees /
honest-scope / first-ten-minutes); (3) **one runnable end-to-end story** is the evaluation
artifact (the four-surface demo, or two-agents/trustline/channel/mailbox); (4) **the
refusals teach** rather than mystify — every `Refusal`/`Decision` names what it violated,
so the evaluator pokes at the edges and *understands* the boundary, which is how they
decide it is useful for their purposes. (Checklist: `HORIZONLOG.md §HANDOFF READINESS`.)

---

## 5. The honest scope — what is real today vs the frontier

The discipline is the project's law: *a labeled seam is a severe problem with a closure
lane, never a wall; reported ≠ closed.*

### Real today (runnable, green, the real executor in the loop)

- **The firmament bridge** — `sel4/dregg-firmament/`: one `(target, rights)` handle, the
  router, `Local`+`Distributed`+`Surface` backings, the n=1 collapse witnessed, real
  `granted ⊆ held` at every end, the real `TurnExecutor` in the loop (a widening grant
  rejected with `DelegationDenied`, byte-for-byte the deployed semantics;
  `real_executor_rejects_widening_surface_share` green).
- **starbridge-v2** — embeds the real executor, runs a live local world; the cap-first
  shell over real `Surface` caps; the agent-activity + swarm surfaces with the notify
  edge (the `swarm.rs` heart, gpui-free + tested); cipherclerk real macaroons; the ⌘K
  palette; the gpui window opens (runtime Metal).
- **The in-tab world** — `wasm/src/runtime.rs` `DreggRuntime` + ~80 `#[wasm_bindgen]`
  fns: a complete cell/turn/capability world running the REAL `dregg-turn`/`dregg-cell`
  crates in wasm32. The browser n=1 machine.
- **The light client** — `dregg-lightclient::verify_history`: whole-history attestation
  from one succinct aggregate, re-witnessing nothing, against a VK anchor. Ready to
  compile to the tab.
- **The verified executor runs a real turn natively** — `execFullForestG` recompiled to
  ELF + linked against an ELF Lean runtime, a transfer applied on aarch64-linux-musl,
  anti-ghost holds.
- **pg-dregg Tier A (M1)** — `dregg_cap_admits` + RLS; an attenuated token correctly
  narrowed at the SQL boundary; the decision is the verified `dregg-auth` decision (the
  Lean↔Rust differential is the anchor). Live on pg18. (Tier B/C also live; the queue
  drainer N8 is the load-bearing gap.)
- **The notify authority, axiom-clean in Lean** — `NotifyAuthority.lean` proven and
  α-total on all 7 seL4 IPC authorities; the core constructor + VK bump is the held tail.

### Frontier (named, with closure lanes — severe problems, not walls)

The shape of the honesty: **the spine is real and proven; the frontiers are the two big
bridges (the cutover wire rewrite, the l4v binary bridge), the four-aspect authorization
integration, and the graphics / seL4 / wasm last-hops — each named with its lane, none a
wall.**

- **THE CUTOVER (the live proof path)** — the single biggest in-flight engineering
  frontier. The system runs on IR-v1 (green, deployable); the rotated IR-v2 path
  (−65.6% proof size) is staged + shape-validated, but the live-path rewrite (G1.5 /
  C5/C7 — ~70 call-sites + executor PI reconstruction + Lean cohort extension) must flip
  it and delete v1. Until then rotated rides a feature flag. (`ROTATION-CUTOVER.md`.)
- **The l4v binary bridge** — R0 (executor authoritative) then R9 (spec→binary). The
  Lean composition is strong; l4v-grade is the binary bridge. (`ASSURANCE-CRITIQUE.md §5`.)
- **The four-aspect authorization integration** — R6, the deepest open thread: the
  macaroon layer and the cap-crown are unintegrated; integrate, do not reduce.
- **The graphics crypto-floor** — R5: T1–T4 are Lean-verifiable now (zero new axioms);
  the last hop (framebuffer ↔ contentDigest) is named hardware/browser trust. Honest
  near-term: a software compositor cell where T1–T4 are real.
- **The Lean executor in wasm** — R3 (in flight, `web/spike/`): turns "faithful" into
  "verified" in the tab with no new trust.
- **The seL4 executor-PD** — host the ELF Lean closure on `sel4-musl` (libuv excision +
  GMP-for-ELF, a concrete checklist). The semihost has a real verified heart NOW on the
  host Lean runtime, so this gates only the real-seL4 target, not the product.
- **The tool-call → effect compiler** — R1: the seam is honest only if the mapping is
  faithful (a wrong mapping yields a faithful receipt of the wrong thing). Per-integrator,
  audited, golden-corpus differential — the named trust boundary.
- **Budget = computation, not dollars** — R2: conservation bounds computrons; the dollar
  ceiling is bounded-by-a-declared-rate until a price oracle lands.
- **ADOS grounds actions, not cognition** — it makes an agent's ACTIONS unfoolable but
  does NOT verify reasoning nor prevent an authorized-but-unwise action. "You see exactly
  what it did and it could only do what its mandate allowed" ≠ "it did the right thing."
- **n=1 isolation is cap-discipline today** — the strong n=1 properties (immediate revoke,
  consistent checkpoint, synchronous commit) are genuinely real on the host firmament;
  MEMORY isolation between loops is by-construction-in-the-API on the host (shared address
  space) and MMU-enforced only on real seL4 (the UML-traced-thread → SKAS gap, same fix).
- **notify is a one-bit covert channel** — R8: sound as coordination, leaky as an
  isolation boundary; the cockpit shows the leaking bit rather than pretending it is
  information-free.
- **The remote (n>1) swarm relaxes the bounds** — R7: the kill switch is immediate
  locally, eventual across the wire; the honest distance-bound, parametrized by n, not
  hidden.
- **The notify VK tail + Tier D** — C1/C3: held for the cutover-settle / the FFI-in-
  backend spike; the NOW UX is final and drops them in without change.

---

## 6. Where this sits

This roadmap is the **refinement epoch's** bar made concrete: usable, general, teaches
what-is, no toys. The four frontiers are one verified object-capability OS — the same
cure applied to the four surfaces an authority decision lands on — and the build list
above makes the §4 killer demos runnable and the §4 journeys real **without touching the
cutover's critical path**. Positioning: *verified accountability substrate for agent
swarms* AND *houyhnhnm OS*, joined at one proof (unfoolability re-instantiated at the
wire, the glass, the swarm, the database, the browser). The NOW tier ships the product a
stranger evaluates; the cutover-settle tier lands the held VK tail; the research tier is
the honest frontier, each item with its lane.

---

*One capability handle, reached through one router, recorded as one kind of turn, proven
once and carried everywhere — to the slot, the cell, the glass, the row, the tab, and the
agent's next action. The proof that a light client cannot be fooled by the pale ghost is
the same proof that the human at the glass, the operator over the swarm, the analyst over
the database, and the stranger in the browser cannot be fooled either. That single
coherence — not a feature count — is what "better than nockchain" means.*

> *and a small poem, as is our custom:*
>
> *one handle, four glasses, the same quiet law —*
> *granted-⊆-held, fired where a person can see it;*
> *the loop narrates, the receipt does not,*
> *and at every surface the ghost meets a tooth.*
> *( ◕‿◕ )*
