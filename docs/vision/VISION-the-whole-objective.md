# VISION — The Whole Objective

*A step-all-the-way-back synthesis. What is dregg FOR, at its most ambitious and
still true? What is the comprehensive, swift path to the boldest realization of it?
This doc names the objective at its boldest, the one through-line that makes the
substrate + the world + the deployment + adoption a single thing, an honest map of
where we are versus that objective, the big swarm-cycles that move us there and how
they sequence, the one cycle to run next, and the guardrails that keep boldness from
becoming LARP.*

> Companions (this synthesizes, does not re-derive): `docs/OVERVIEW.md` (the apex
> sentence + the four-word model), `docs/THE-GRAIN.md` (hosted agents you can prove/
> fork/own), `docs/GAMES-AS-RECEIPTS.md` (the thesis made playable), `docs/design/
> HOARDLIGHT-LIVING-WORLD.md` (the living world), `docs/MEGASPEC-worlds-ide-and-the-
> verified-web.md` (the verified web + IDE), `docs/design-frontiers/UNIFYING-STORY.md`
> (one capability handle, carried everywhere), `docs/FORWARD-CAMPAIGN-2026-07.md` +
> `docs/ROADMAP-assurance-perimeter.md` (the two live substrate campaigns), and the
> memory frontier files (`project-distributed-houyhnhnm-frontier`, `project-polisware-
> constitution`, `project-rhizomatic-dregg-slotting`, `project-witness-gen-assurance-
> perimeter`, `project-fri-soundness-reality`, `project-launch-readiness-audit`). A
> sibling probe, `docs/vision/VISION-proof-by-construction.md`, drills the substrate
> *technique* (refinement-as-a-functor); this doc is the umbrella over all four faces.

---

## 1. THE OBJECTIVE, BOLDLY

**dregg is building a computer you do not have to trust — a substrate on which every
consequential act (a move, an edit, a vote, a payment, an agent's decision, a
creature's birth) is one primitive: the exercise of an attenuable, proof-carrying
capability over owned state, leaving a receipt — so that a stranger holding one root
can verify a whole history was authorized, conservative, fresh, and correctly
committed, re-executing nothing and trusting no one, and so that the *illegal is not
policed but unprovable.***

Say it in one more register, because the pieces really do add up to this: dregg is
trying to make **"verified" the default substance of computing the way "digital"
became default** — a place where a living world, an economy, a collaborative IDE, a
swarm of agents, a governance polity, and a person are *the same object seen at
different targets*, and where the deepest security guarantee holds against an
adversary that **includes the operator, the server, the market, the narrator, and the
designer.** The apex sentence already written into the tree is the compact form of
the whole ambition (`docs/OVERVIEW.md:3-6`, `docs/THE-LINKING-TOWER.md:5-8`):

> *A light client holding one root knows every transition in the whole history was
> authorized, conservative, fresh, and correctly committed — re-executing nothing.*

That is not a blockchain feature. It is a claim about **who has to be believed for a
computed fact to be real** — and the bold objective is to drive that claim outward,
one honest rung at a time, until it holds not just for a toy transfer in Lean but for
a dragon someone raised, a document a team edited, a payment that conserved supply by
construction, and an agent someone rented — live, in public, checkable by a stranger.

This is bold but it is *not* wishful, and the distinction is the whole discipline: the
architecture that would make it true is proven and composes today; its floor is a
labeled, tracked placeholder being refined upward; and the distance from
"proven-in-Lean-for-a-covered-set on ember's laptop" to "a stranger checked a live
world's root" is large, named, and the subject of §3–§5.

---

## 2. THE THROUGH-LINE — why the four faces are one thing

There is exactly one idea, and the four "faces" (substrate, world, deployment,
adoption) are that idea proven once and carried to four surfaces. The seed sentence
(`docs/GAMES-AS-RECEIPTS.md:3`; unfolded in `project-rhizomatic-dregg-slotting`):

> **A turn is the exercise of an attenuable, proof-carrying capability over owned
> state, leaving a receipt.**

Lineage: **macaroons/biscuits → the biscuit's attenuable Datalog token, taken
seriously, IS a derivation circuit** — authority becomes a machine-checked derivation,
not a bearer secret; "you *hold* a capability iff you can *produce* its witness — never
merely be named in a table" (`docs/OVERVIEW.md:16-19`). That single move fissions into
the four-word model — **cell** (owned state + identity), **capability** (attenuable
authority as production-under-non-forgeability), **turn** (the atom of becoming),
**receipt** (the verifiable witness that binds the whole post-state; tampering an
unwritten field makes the turn *unprovable* — the anti-ghost property). Everything
else is that one anti-ghost property re-instantiated somewhere new.

**The substrate (proven-to-reality semantics).** The kernel is Lean; the guarantees a
light client relies on are machine-checked theorems over the *actually emitted* circuit
objects (`metatheory/Dregg2/`, `docs/ASSURANCE.md`, `docs/CIRCUITS-FROM-PROOFS.md`).
Authority = production under non-forgeability; conservation = Σδ=0; the apex is
light-client unfoolability, live-wired to real plonky3 in-circuit FRI recursion
(`RecursiveAggregation.lean`, `lightclient/src/lib.rs::verify_history`). dregg already
does the Mina-Pickles-shaped succinct-whole-chain thing.

**The world (deeply-dreggic games/economy).** "Every move is a receipt": an illegal
move is not forbidden by app code, it is unprovable at the kernel; a failing rule is a
real `WorldError::Refused` with no receipt behind it (`docs/GAMES-AS-RECEIPTS.md`). The
boldest expression is Hoardlight (`docs/design/HOARDLIGHT-LIVING-WORLD.md`): **a
creature can surprise you without the server being allowed to invent why** — emergence
is real committed state, lineage is a proof graph, privacy is a social mechanic and not
a trust-me mechanic, "the object in the story is the object in the economy," and a
leaderboard entry is an executable claim. That is a game only dregg can host, and it is
the same receipt primitive as the transfer proof, one altitude up.

**The deployment (a real live node).** The substrate's guarantee only *means* something
when a stranger can hold the root of a history that actually happened somewhere other
than one laptop — a durable federation producing blocks, anchored to real consensus,
with the on-chain settle riding a *live* turn (`docs/deos/DEVNET-DEPLOYMENT-REALITY.md`,
`docs/FORWARD-CAMPAIGN-2026-07.md`). Deployment is not ops garnish; it is the surface at
which "proven" becomes "true of the thing you are using."

**Adoption.** The last hop: the same handle reaches *anyone* — a `<dregg-*>` element in
any browser with honest, progressive trust (`docs/MEGASPEC-…`), a hosted agent you can
rent/fork/own (`docs/THE-GRAIN.md`), a launchpad a stranger uses with dregg out of the
loop (`docs/DESIGN-rung1-launchpad-shipit.md`), a Discord town square where dragons
live. Adoption is the receipt primitive made *reachable* without lock-in.

**The coherence that fuses them (the crown statement, `docs/design-frontiers/
UNIFYING-STORY.md`):** one unforgeable `(target, rights)` capability handle, resolved
by one router, recorded as one kind of turn, **carried without a seam from a local seL4
slot, to a cell on a remote federation, to a window on glass, to a row in postgres, to
an agent's next tool-call.** The desktop asks the anti-ghost question one hop out (can
the human at the glass be fooled?); the swarm asks it of agents (can the operator be
fooled about what two agents coordinated?); pg-dregg asks it of a `SELECT` (can a query
return a row no verified turn produced?). *One idea, proven once, carried everywhere* —
"better than nockchain" means crystalline coherence, not feature count.

**The deepest framing (held honestly).** Two threads name the philosophical apex:
- **Distributed Houyhnhnm computing** (`project-distributed-houyhnhnm-frontier`): a
  substrate where every unit of computation carries its own witness, so trust is never
  *extended* to an operator but *discharged* by proof; isolation is re-based from
  host-ENFORCED to **host-EXCLUDED-by-proof** — a container that keeps the *operator*
  out.
- **Non-domination / the ∀-adversary as apex** (`project-polisware-constitution`): the
  deepest threat modeled is the substrate itself; the design object is "safe regardless
  of who operates it," governing trace-shape not motive. *Honest correction carried with
  the vision:* the once-celebrated "non-domination ≡ light-client-unfoolability, ONE
  theorem" is a **shape-identity, not shared content** (a trivial struct projection);
  cite the *individual* deployed theorems (`sealedescrow_no_theft`,
  `deco_attestation_unforgeable`, `settlement_soundness`, the gentian unsat teeth) as
  the guarantees, never the grand unification. The philosophy is load-bearing at the
  level of real theorems; some framing on top of it was inflated, and the same
  discipline that built it is what caught that.
- **Rhizomatic + conservation** (`project-rhizomatic-dregg-slotting`): dregg is the
  maximal coordination-free monotone world **plus** a linear-value/bounded-invariant
  layer that I-confluence provably cannot merge (two withdrawals merge to overdraft) —
  hence a circuit, consensus, and an exact Σδ=0 law. "dregg is rhizomatic + a proof
  obligation."

---

## 3. WHERE WE ARE vs THE OBJECTIVE — the honest gap

The kindest true summary: **the architecture of the bold objective is proven and
composes; its floor is a labeled placeholder; and nothing yet runs where a stranger can
touch it.** Four honest gaps, at current resolution.

### Gap 1 — Two orthogonal floors under the apex (never collapse them)

- **The witness-generation perimeter.** A STARK proves the *trace* satisfies the AIR —
  not that the Rust witness *generator* computed the right value, nor that the AIR
  *completely* constrains the computation. The 2026-07-17 audit under the strict bar
  `air_accepts ⟺ spec` found **the proven-complete set was empty** — the consensus roots
  (ledger, state-commitment, receipt) were trusted-Rust; the EffectVM deltas were
  one-directionally constrained (`project-witness-gen-assurance-perimeter`,
  `docs/DESIGN-assurance-perimeter-closure.md`). This is the load-bearing weak word
  "correctly committed" in the apex: for the object a light client *holds* to be the
  object the AIR constrains, this perimeter must close. The campaign (§4, Cycle 1) is
  actively filling it — template + transfer flagship + heap + note-spend + garbled +
  cap-found-already-closed are ✅ — but the generalization to all effect tags and the
  state-commit anchor cutover (delete BLAKE3 `ledger.root()`, make `wire_commit_8` the
  chained root) have not landed. Encouraging truth: **this is replication of a proven
  pattern, not research.**
- **FRI soundness reality.** The deployed apex proves at `d=4`. The "~57 calculator bits" once
  quoted was an INFORMAL Finset density ratio, NOT a soundness bound, **with no adversary / protocol
  object in existence** (`verifyAlgo` is a `Bool` on a *supplied* proof). The theorem-backed deployed
  readings are commit ε_C **51 bits** at `2²²` (`FriDeployedHeightPairing.deployed_wrap_commitBits`)
  and query soundness **~31.5 bits** at δ=7/16 (`(9/16)³⁸ < 2⁻³¹`, `DeployedProximitySoundness`)
  (`project-fri-soundness-reality`, `docs/THE-LINKING-TOWER.md:180-189`). There is
  deliberately no `2⁻¹²⁸` headline; the client is not entitled to believe one. This is
  the deepest, last-sequenced gap.

What *is* proven, machine-checked, axiom-clean modulo named premises: the single-turn
apex (`lightclient_unfoolable`) and the whole-history apex
(`light_client_verifies_whole_history`), the five guarantee apexes, conservation
essentially unconditionally, authority over the real attenuation lattice, the
macaroon↔cap convergence arrow — all pinned by `#assert_axioms` + `#keystone_audit`
(non-vacuity both polarities), 165 theorem pins clean (`metatheory/CLAIMS.md`,
`docs/ASSURANCE.md`). The tower is **proven at the top and honest at the bottom.**

### Gap 2 — "Green on ember's laptop," not deployed

The single disease named by the launch-readiness audit
(`project-launch-readiness-audit`, `HORIZONLOG.md:141`): **the real system is green on
ember's laptop, not in a frozen, reproducible, deployed artifact.** The strongest single
result in the corpus is real — the buff light client ran *on iron* (persvati homelab,
v13 VK): a real faucet turn generated a 555 KB full-turn STARK, re-verified on the
commit path under the deployed VK, and finalized cross-node at BFT supermajority(3)=3
(`project-carrier-deployment-architecture`). But that is *homelab, unpushed to origin*,
and the live run found a real bug (committee nodes non-restartable after finalizing).
Today: one verified **solo** `dregg-node` (committee-of-one, `federation_mode:"solo"`),
LAN+tailnet only, ledger lost on reboot (`docs/deos/DEVNET-DEPLOYMENT-REALITY.md`); one
Base-Sepolia settlement of a **fixture** proof under a **toxic-waste dev ceremony**; no
mainnet, no broadcast contracts, SDKs publish-ready but unpublished, the VK a
self-recompute tautology, no bare-clone CI gate. **There is no live dregg node a
stranger transacts on.**

### Gap 3 — The world layer is proven + running, but thin, prototype, and un-durable

The games *play* live as Offerings (hbox funnel, `arcade.dregg.net/tg` Telegram Mini
App, Discord): legal moves land real receipts, illegal are refused
(`HORIZONLOG.md:223`). Fresher than the memory: the Descent and Automatafl were
**re-authored natively in Lean** in 2026-07-18 — `Dregg2/Games/Dungeon.lean` (permadeath
as a *theorem*), Automatafl Leg A proven *unconditionally* — and the formalization found
**five real defects the Rust had hidden.** But: Hoardlight (the deeply-dreggic
creature-world) is **design, not built** — the Resonance Braid, true dual-parent
lineage, and the nonlinear duet verifier do not exist (`HOARDLIGHT §12`, gaps 1–3); the
current daily is a tonally-wrong fight/key/hoard demo; the MUD realm-model is a driven
prototype whose durable persistence needs a node-served restart-durable receipt chain
that does not exist; games verify at **tier-1 replay** today, not the succinct fold; and
**zero real $DREGG has ever transacted.**

### Gap 4 — The reach layer runs in the extension, not yet in the open web

The `<dregg-*>` capability-resolving elements exist and ship (closed shadow-DOM, trust
badges, passkey custody floor, wasm prover on the deployed descriptor path) — but
`<dregg-world>` / `<dregg-editor>` do not exist yet, and the extension-less provider
tiers (page-bundled render/verify, per-origin SSR) are frontier (`MEGASPEC §6, §8`). The
grain's R0–R2 attestation ladder is landed and verified; R3 (the whole-history close) is
a genuine *reduction* to a named STARK floor, **not** trustlessness yet
(`docs/THE-GRAIN.md`).

**Net.** Substrate: architecturally proven, two named floors refining upward. World:
proven and running, but thin and un-durable, no value transacted. Deployment: met the
empirical bar *on iron in a homelab*, nothing public/frozen/reproducible. Reach: real in
the extension, not yet in the open web. **The gap is not conceptual — it is engineering
discipline: reproducible, frozen, durably-deployed, value-transacting, and one lovable
surface a stranger can actually hold.**

---

## 4. THE COMPREHENSIVE CAMPAIGN — the big swarm-cycles + sequencing

Seven big coordinated sweeps. Two are already in flight (they *are* the current living
campaigns); the rest build on the substrate that already RUNS. The organizing insight:
there is a **SPINE** (three cycles that must sequence and share events, closing the two
floors and putting the system in public durably), an **ADOPTION FRONT** (two cycles that
can build now in parallel on the running substrate and get their trustless upgrade from
the spine), and a **FRONTIER** (two cycles that ride 1–6). The main loop is a launcher:
these run concurrently where the dependency spine allows, not strictly serially.

```
   SPINE (must sequence; share events)         ADOPTION FRONT (parallel, on what RUNS)
   ┌────────────────────────────────┐          ┌────────────────────────────────────┐
   │ 1 PERIMETER  ─┐                 │          │ 4 WORLD  (Hoardlight, tier-1 today) │
   │               │ feeds "correctly│          │ 5 REACH  (<dregg-*>, extension today)│
   │ 2 FLOOR ──────┤ committed" +    │          └───────────────┬────────────────────┘
   │   (cutover)   │ meaningful bits │                          │ trustless-upgrade
   │      ▲        ▼                 │                          ▼   from the spine
   │      └── 3 GROUND (freeze rides │◄─────── the durable node is the meta-enabler:
   │          FLOOR's Phase-4 re-key)│         until it lands, every "deployed" is
   └────────────────────────────────┘         green-on-one-laptop
                     │
                     ▼   rides 1–6
   FRONTIER: 6 INHABIT (grains + one-handle OS) · 7 POLITY (economy + governance)
```

### Cycle 1 — PERIMETER (in flight): close the witness-generation assurance perimeter
**Objective.** Every consensus-visible value is *either* constrained by a proven-COMPLETE
AIR (`air_accepts ⟺ spec`, the honest accept-SET-↔-spec + ∀-soundness ∧ ∃-completeness
shape) *or* a single Lean implementation Rust calls into. Nothing trusted, nothing
duplicated; the receipt carries a proof, not a trusted key.
**Unlocks.** The apex's "correctly committed" leg — the deployed object *becomes* the
constrained object. **Critical move:** author the one generic `runnable_full_complete` +
`runnable_full_commit_iff` so the transfer flagship becomes the ENGINE and ~15
kernel-only tags collapse to thin instantiations; then the state-commit anchor cutover
(make `wire_commit_8` the chained root, delete BLAKE3 `ledger.root()`).
**Status/scope.** Template ✅, transfer flagship ✅, heap/note/garbled ✅, cap
found-already-closed ✅; #3 receipt proof-threading 🔶; all-effect-tag generalization +
the anchor cutover open. Replication, not research. Orthogonal to the FRI floor — never
laundered by this work (`docs/ROADMAP-assurance-perimeter.md`).

### Cycle 2 — FLOOR: sharpen the proof to an adversary, and prepare the freeze
**Objective.** Cut the deployed config from `d=4` (the "57-calc-bits" was an informal estimate, not a
soundness bound — the proven deployed readings are query ~31.5 bits `DeployedProximitySoundness` /
commit ε_C 51 bits `FriDeployedHeightPairing.deployed_wrap_commitBits`) to **λ ≥ 122 with margin**
(`d=8, lb=6, q=36, pow=16`), and re-base the one assumed FRI extraction leg
(`FriLdtExtractV3`) over a query-counting **adversary object** (`RomOracle`) so the bits
mean "εFri(2^b) ≤ ½," not a density ratio (`docs/FORWARD-CAMPAIGN-2026-07.md` Track B).
**Unlocks.** The apex bits become a real soundness statement; the frozen VK will pin the
*strong* config. **Load-bearing unknown:** the G1 go/no-go — is the d=8 gnark wrap
(~7.5–12M R1CS, ~15–25 GB Groth16 setup, estimated) affordable on hbox under
`swarm-build`? Falsifier gates the whole downstream.
**Scope.** Phase 0 (`WRAP_LOG_CEIL 16→15`, +2 bits, free-and-correct-today) can start
immediately; the extraction-floor faithfulness bridge is pure structure, parallelizable.

### Cycle 3 — GROUND: a real, reproducible, frozen, durably-deployed node
**Objective.** Put the system somewhere other than one laptop, durably; make a stranger's
bare clone reproduce the author's green; freeze a ceremony-pinned `v-final` VK; anchor to
real consensus. Three welds: (a) D-reproducibility — date-pin the toolchain, rev-pin
`ark-serialize`, publish the Lean seed, add the **bare-clone-into-empty-`~/dev` CI gate**
(the campaign's load-bearing falsifier); (b) stand up a **persistent n≥2 federation** on
private infra (the single biggest non-gated deployment step —
`docs/deos/DEVNET-DEPLOYMENT-REALITY.md`) and re-anchor the Descent funnel durably; (c)
the A mainnet feed (prove one real mainnet holding against real ≥2/3 Solana consensus)
and wire the on-chain settle from a *live* turn.
**Unlocks.** Every downstream "deployed" claim becomes true; a stranger can reproduce the
VK they verify against. **Sequencing law:** D-freeze MUST ride FLOOR's cutover Phase-4
re-key — freeze the proven-122 VK, never a standalone ceremony that pins the current un-upgraded posture (the "57 bit" figure was an informal estimate; the proven deployed commit reading is 51 bits, `FriDeployedHeightPairing.deployed_wrap_commitBits`).
D-reproducibility (bare-clone gate) and the durable federation have *no* Track-B
dependency and proceed first.

### Cycle 4 — WORLD: the living world made real (adoption front — build now)
**Objective.** Build the deeply-dreggic creature-world where emergence is real state and
the server can't invent why: the versioned **Resonance Braid** schema + one authoritative
bounded nonlinear resolver (with a dedicated transition verifier, not trusted host
arithmetic), **true dual-parent lineage** (a new DAG-shaped birth artifact + per-locus
origin receipts), the shared-world service (Discord/web/Telegram over one `SharedWorld`),
and tier-mobility (lift a playthrough onto the succinct fold). Hoardlight stages 1→4
(`docs/design/HOARDLIGHT-LIVING-WORLD.md §11`).
**Unlocks.** The first thing a stranger can *love*; "every move is a receipt" as playable
joy, not a demo; the flywheel's first real content. **Scope.** Runs at tier-1 replay on
the substrate that RUNS today — needs neither the frozen VK nor the mainnet feed to
build; it *earns* its trustless upgrade when the spine lands. Reimagine each game fresh in
Lean (as Descent/Automatafl were), never port the Rust augmenter teeth.

### Cycle 5 — REACH: the verified web + delivery (adoption front — build now)
**Objective.** Make worlds, edits, and votes reach any browser with honest, progressive
trust: ship `<dregg-world>` / `<dregg-editor>` on the established element pattern, the
extension-less provider tiers (page-bundled `@dregg/sdk` render+verify, per-origin SSR),
the DDL collaborative editing surface (merges provably cannot corrupt; conflict is
first-class state), and the deos surfaces (htmx-on-crack: a cell declares affordances, an
interaction is a verified turn) (`docs/MEGASPEC-…`, `docs/deos/DEOS.md`).
**Unlocks.** Distribution without lock-in; the semantic web finally given physics; the
multiplayer-engineering-world-server + best-IDE seams for external builders (Alif). Read +
verify reach a bare browser; write (custody) + privacy (local proving) come with the
person's agent. **Scope.** The element substrate + passkey custody + wasm prover already
ship in the extension; this is the open-web frontier on top.

### Cycle 6 — INHABIT: grains + the one-handle OS (frontier)
**Objective.** dregg as a general witnessed computer: close the grain's **R3
whole-history** leg (mint each grain turn's rotated wide-anchored EffectVM leg → the fold
folds them) so a hosted agent is provable/forkable/ownable end-to-end; ship the agent
**commons** (an app store for pedigreed agents); land the one-capability-handle spine
carried from slot → cell → glass → SQL row → agent's next tool-call, with the killer demo
(one token, four surfaces, one refusal) as the legibility artifact
(`docs/THE-GRAIN.md`, `docs/design-frontiers/UNIFYING-STORY.md`).
**Unlocks.** Distributed Houyhnhnm computing made concrete; the agent economy; "dregg is a
computer you don't have to trust" as a thing you *use*, not a slogan.

### Cycle 7 — POLITY: protocol-native economy + governance (frontier)
**Objective.** Value conserves by construction (delete the custodial seed/sweeper; a run
credit is a cell balance the *user* authorizes via `resolve_pay`), governance is
non-custodial proof-of-holdings weight, and collective choice is the ∀-adversary-resistant
polis; fix the verified finality gate's O(history) perf so cross-machine finality holds at
speed (`docs/FORWARD-CAMPAIGN-2026-07.md` Track C, `project-federation-payoff`,
`project-polisware-constitution`).
**Unlocks.** A real economy and a real polity on the substrate; the token does something
honest (services, never features; the mainnet payment flip is ember-gated and last).

**Sequencing summary (what unlocks what).** PERIMETER and FLOOR are the two orthogonal
floors feeding the apex; FLOOR's cutover Phase-4 IS GROUND's freeze event (pay the
ceremony once). GROUND's durable node is the meta-enabler — until the bare-clone gate is
green and a federation stands, every "deployed" downstream is green-on-one-laptop. WORLD
and REACH build *now* in parallel on the running substrate (tier-1 today) and inherit
trustlessness from the spine. INHABIT and POLITY ride 1–6. The whole thing is credible
the day a stranger, from a bare clone, reproduces a λ≥122 VK, proves a real mainnet
holding against it, plays a verifiable world, and moves real value through a conserving
rail — each step checkable with ember not in the room.

---

## 5. THE ONE THING — if we could run only ONE big cycle next

**Run GROUND fused with WORLD Stage 1: put one lovable, tone-correct, replay-verifiable
world live on a durable public node, with the bare-clone reproducibility gate green — so
that for the first time an outsider plays a dregg world AND independently verifies its
root, with no ember in the room and no trusted server. Call it First Contact.**

Concretely, the minimal cut: (a) the durable persistent federation + the re-anchored
Descent funnel (the single biggest non-gated deployment step); (b) one surface a stranger
can love and check — either Hoardlight Stage 1 (the tone-correct daily push-your-luck
descent) or, as the fastest honest floor, the rung-1 launchpad (dregg-out-of-the-loop,
shippable this week) plus the durable Descent; (c) the bare-clone CI gate green so the
verify is reproducible.

**Why this one moves us most toward THE OBJECTIVE.** The objective in miniature *is* this
sentence: a stranger verifies a live history's one root, re-executing nothing, trusting no
one. Today that sentence is true nowhere in public — the empirical bar was met *on iron in
ember's homelab*, unpushed, ledger-lost-on-reboot. We are not short on proof depth; we are
proven deeply and honestly. We are short on the fact that **nothing runs where a stranger
can touch it.** This cycle converts the entire project from "a cathedral proven on a
laptop that no outsider has entered" into "a stranger walked in, played, and checked the
walls themselves." It needs *nothing frozen* to begin (the launchpad is dregg-not-in-loop;
the world runs at tier-1 replay), so it proceeds in parallel with the SPINE's proof work
rather than waiting on it — and it is the move that makes every other cycle's value
*legible*: PERIMETER, FLOOR, INHABIT, and POLITY all harden a thing that, until First
Contact, no stranger has ever held.

It also honors the launcher discipline: choosing this as the ONE cycle does not pause the
in-flight PERIMETER/FLOOR spine — it runs concurrently. First Contact is the cycle that
earns the right to say the boldest sentence out loud, once, in public, truthfully.

---

## 6. THE GUARDRAILS — the hard-won rules any bold campaign obeys

These are scar tissue; each prevents a specific way boldness rots into overclaim. A
green check, a passing proof, and an honest lane are each true only about the abstraction
you pointed them at — never automatically about the deployed reality.

1. **Reality-gate FIRST, not internal-consistency-first.** Make
   correspondence-to-the-real-thing the acceptance criterion of *cycle 1*, not the reveal
   of cycle 5 — run the emit against the REAL fixture proof (accept it, reject the
   canaries) before believing any internal theorem. *Prevents:* an abstraction
   bulletproof against itself that is ~20% of the deployed thing
   (`feedback-reality-gate-first-not-internal-consistency`).
2. **No mirror / no LARP.** A claimed-closed seam must be carried by a REAL cross-cell
   predicate, a MOVED (not re-minted) ledger, a consulted presentation — never a shared
   constant, a fresh mint, a self-signed fixture, a re-authored twin. Reward the lane that
   reports BLOCKED over one that wires a fake (the cap lane that *refused* to build a
   weaker mirror is the discipline holding). *Prevents:* the codebase's single most
   recurring wound (`feedback-describe-at-current-not-intended-resolution`).
3. **Describe at CURRENT resolution, not intended.** State what the code does NOW — a
   named seam, not a closed one. Low-resolution work is legitimate and tracked; it must be
   *described* as low-resolution. *Prevents:* prose laundering the gap (a doc-comment
   asserting CLOSED while the code points at a fixture).
4. **No greenfield-migration theater.** Nothing is deployed — no live consensus, no
   persisted ledgers, no users whose state forks. So NO cutover / flag-day /
   byte-identical / compat bar anywhere. Make the RIGHT proven-Lean object BE the object
   and DELETE the debt. *Prevents:* inventing constraints that don't exist and burning
   energy protecting nothing (`feedback-no-greenfield-migration-theater`). *(Note: this
   applies to pre-production internal state. GROUND's freeze/ceremony is the deliberate
   transition OUT of greenfield — the one place production-gravity becomes real.)*
5. **Reimagine — don't port.** When a game/policy/circuit moves to Lean, author it FRESH
   (as Descent and Automatafl were — the re-authoring found five real defects); never port
   the Rust twin verbatim, which reproduces the mirror.
6. **Prove the floor FALSE.** A load-bearing assumption must be a GENUINE assumption —
   satisfiable AND refutable but NOT provable. Try to prove each floor false at *deployed*
   parameters (the MLWE `(s,e)` ARE the key; a compressing hash HAS collisions; FRI at 57
   calc bits has no adversary object yet). `#assert_axioms` is blind to hypotheses; a
   hardness claim quantifies over efficient adversaries, never over solutions
   (`feedback-prove-the-floor-false`).
7. **Confirm by READING, not grep.** Assess whether code is real/mature/does-what-it-claims
   with careful-reading, not ls/grep/`cargo check`. "Already exists" is a mandate to
   DRASTICALLY improve, never a reassurance (`feedback-confirm-code-by-reading-not-grep`).
8. **The integrator must not compress scope.** The lane's scope qualifier ("toy",
   "representative core", "ZMod 5") belongs in the FIRST sentence, never a trailing caveat.
   Read the TYPE before writing "the deployed X is proved" — the "verified system, λ=149"
   retraction was the integrator dropping honest lane qualifiers
   (`feedback-integrator-must-not-compress-scope`).
9. **Dispatch identified work IMMEDIATELY.** The instant a lane surfaces N more sites of a
   fixed pattern, fan empowered agents at it before continuing your thread — logging ≠
   doing; the main loop is a launcher (`feedback-swarm-delegate-identified-work-immediately`).
10. **Iterative/approximative, held POSITIVELY.** Build whole-system-first at low
    resolution with every approximation LABELED, then sharpen up — as *scheduled sharpening
    on a known trajectory*, never bearish self-flagellation. A conditional proof of the
    ARCHITECTURE is real and valuable while its floor is a labeled placeholder
    (`feedback-iterative-approximative-method`). And a named seam is not a hole: CLASSIFY it
    (terminal floor / reducible-with-estimate / closed / calibration), then WELD the
    reducible ones — naming instead of welding is a form of shirk.

**The shape of all of them:** internal-consistency ≠ correspondence; a doc-comment /
type-signature / green-check is a *name*, not a proof; honesty is the ENGINE that makes
low-resolution-first *safe*, not a confession bolted on afterward. Be audacious at the
architecture level and stand the whole thing up; be ruthless at the resolution level about
where every piece currently sits; gate against reality from cycle 1; and let the operator
themselves be the adversary you prove yourself safe against.

---

*One capability handle, reached through one router, recorded as one kind of turn, proven
once and carried everywhere — to the slot, the cell, the glass, the row, the agent's next
action, and the little dragon peering into one more room. The proof that a light client
cannot be fooled by the pale ghost on the wire is the same proof that the human at the
glass, the operator over the swarm, the analyst over the database, and the player over the
world cannot be fooled either. That single coherence — not a feature count — is the whole
objective.*

> a turn is a small kept promise:
> owned state, an attenuated right,
> a witness a stranger can hold to the light —
> we built the cathedral at low resolution first,
> labeled every unfinished stone,
> and now we open one door, in public,
> and let someone walk in and check the walls alone.
> ( ˘▾˘ )
