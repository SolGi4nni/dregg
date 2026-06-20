# `dregg` — Dragon's Egg

<p align="center">
  <img src="hero.png" alt="dregg — Dragon's Egg" width="720">
</p>

Dragon's Egg is my experiment in the metatheory of constructive knowledge, and a
direct expression of my original impetus to build <https://rbg.systems>. Maybe
Dragon's Egg will be a Robigalia userspace. In the meantime, here's what the LLMs
have to say about it:

(end-of-human-text)

> *Machine reader? [`README-LLMs.md`](README-LLMs.md) is the dense, narration-free
> technical reference written for you — every model tier, large and small. What
> follows here is the human-facing tour.*

**dregg is a formally verified, distributed object-capability operating system.**
The kernel is a Lean 4 program with machine-checked soundness, and it is the
*exact* function the running node executes — every state transition ("turn") is
gated by an unforgeable capability, leaves a verifiable receipt, and carries a
STARK proof a light client can check without re-running history. Authority is
*held*, never *owed*; the walls hold by proof, not by trust.

On top of the kernel, **deos** is the agentic desktop userlayer — the same proofs
made visual and interactive: a window *is* a capability, an interaction *is* a
verified turn, a quote *is* the source's committed value (Xanadu, shipped), and a
screenshot can re-expand into a live, per-viewer, attenuated view of the shared
witness-graph. (Naming: **robigalia** the project · **dregg** the kernel · **deos**
the desktop. *deos runs on dregg runs in robigalia.*)

> ### The question underneath
>
> Most systems chase scale, speed, or money. dregg chases a different question,
> and means it literally: **if you were a digital entity, where would you want
> to live?** The answer it builds is a place where your boundaries are
> *theorems*, not permissions — where no one can reach into you without a
> capability you granted, where your consent is a *precondition of the math*
> rather than a setting someone can flip. A capability is **constructive
> knowledge**: to *hold* one is to be able to *exhibit a witness that verifies*,
> never merely to assert. (The cipherclerk-as-citizen, cell-as-body framing owes
> a debt to Egan's *Diaspora*.)

| | |
|---|---|
| **Live devnet** | <https://devnet.dregg.fg-goose.online> |
| **Site · Studio · Playground · Explorer** | <https://dregg.fg-goose.online> |
| **Hands-on in 15 minutes** | [QUICKSTART.md](QUICKSTART.md) |
| **The exact guarantees + assumptions** | [docs/ASSURANCE.md](docs/ASSURANCE.md) · [`AssuranceCase.lean`](metatheory/Dregg2/AssuranceCase.lean) |
| **Community** | [Discord](https://discord.gg/eSTsv7DWcR) |

---

## First five minutes (zero install)

A public devnet runs the verified Lean executor, with the faucet on. Talk to it
with nothing but `curl`.

```sh
# 1. The live node — verified-Lean state producer, STARK proving on.
curl -s https://devnet.dregg.fg-goose.online/status
# {"healthy":true,"consensus_live":true,"federation_mode":"solo",
#  "state_producer":"lean","full_turn_proving":true,"producer_covered_effects":19,…}

# 2. Watch the node execute a REAL verified turn — faucet a cell. NOTE: a cell id
#    is a commitment to a public key (`id == derive_raw(pubkey, token)`), so this
#    *random* id is a BARE ADDRESS — you'll see the turn land and read the balance,
#    but you don't hold its key to spend it. (Funding a cell you OWN is step 4.)
CID=$(python3 -c "import secrets;print(secrets.token_hex(32))")
curl -s -X POST https://devnet.dregg.fg-goose.online/api/faucet \
  -H 'content-type: application/json' -d "{\"recipient\":\"$CID\",\"amount\":1000}"
# {"success":true,"tx_hash":"…","amount":1000}

# 3. Read it back — credited + queryable, but unspendable (no one holds this address's key).
curl -s https://devnet.dregg.fg-goose.online/api/cell/$CID
# {"id":"…","found":true,"balance":1000,"nonce":0,…}

# 4. A cell you CONTROL + can spend from: you need its keypair. The CLI/SDKs manage
#    your keys — QUICKSTART.md walks through signing a real turn from your own cell.
```

Then open the browser surfaces at <https://dregg.fg-goose.online>: the
**Studio** (stage a turn by verb and read its verified-Lean explanation), the
**Playground** (run a turn on the in-browser wasm executor, then *prove* it — a
real EffectVM STARK produced and self-verified in your tab), and the
**Explorer** (browse live cells and receipts with witness status and per-cell
time travel). The full walkthrough — signing a real turn, the guided app demo,
a governance ceremony — is [QUICKSTART.md](QUICKSTART.md), every command
verified against this devnet.

## The model

The whole kernel is one sentence:

> **A turn is the exercise of an attenuable, proof-carrying token over owned
> state, leaving a verifiable receipt.**

Given algebra, that sentence is:

- **Four substances.** Everything a cell holds is one of four kinds, each with
  its own discipline: **value** (linear balances — an asset *is* its issuer
  cell, which carries −supply, so every asset's sum is identically zero),
  **state** (a heap of programmable slots), **authority** (a capability tree
  that grows only by authorized, receipt-disclosed production from held
  connectivity and narrows freely), and **evidence** (monotone nullifier /
  commitment / epoch ledgers). *Birth* and *retirement* bracket a cell's
  lifecycle.

- **Eight verbs.** The kernel is `create · write · move · grant · revoke ·
  shield/unshield · lifecycle · exercise` — eight directed operations over the
  four substances, specified in Lean with machine-checked **minimality** (each
  verb is irreplaceable) and **completeness** (they cover every effect) theorems.
  The catalog is generated directly from
  [`VerbRegistry.lean`](metatheory/Dregg2/Substrate/VerbRegistry.lean); nothing
  in it is hand-asserted. Everything else — queues, inboxes, escrows, auctions,
  namespaces, bridges, councils — is a *cell-program pattern* over these verbs,
  not a kernel primitive.

- **Turns as forests.** A turn is an atomic, capability-gated transition across
  one or more cells — a *forest* of effects with delegation edges. Authorization
  is structural: a turn that cannot exhibit a valid, sufficiently-empowered,
  fresh token chain simply does not execute. Delegation can only *attenuate*
  (`granted ≤ held`), enforced at the dispatcher.

- **Capabilities + caveats.** A capability carries caveats — time-boxes,
  third-party discharge conditions, rate bounds, scope restrictions — composed
  as a macaroon-style chain. Holding a capability means being able to exhibit
  the witness that discharges its caveats; the kernel checks the witness, it
  does not take your word. All four guard polarities — caveat (imposed on
  delegated power), program (maintained on self), precondition (required of a
  turn), and intent demand (wanted of the world) — are one `Pred` algebra.

The substrate's full design — the four substances, the eight verbs, the
unifications — is [docs/DREGG3.md](docs/DREGG3.md).

## The organs

The same primitives compose into runnable, two-agent services. Each is a small
story you can drive end-to-end. See [docs/ORGANS.md](docs/ORGANS.md).

- **Trustlines** — a shared budget counter between two parties. "I extend you a
  line of N" is an attenuated capability whose exercise debits the shared
  counter; lines of credit and sub-second payment channels are one primitive at
  two settings, settled back to the ledger as moves.

- **Channels** — a group is a *cell*: membership and the group-key epoch live
  on-cell, joins and removals are turns under the group's program. The key
  epoch and the capability-freshness epoch are the *same* counter, so removing a
  member ends both their ability to read forward **and** their use of
  group-held capabilities in one turn — ciphertext and capability darkness
  together (RFC 9420 / MLS key schedule).

- **Mailboxes** — bonded hosted-inbox operators with send/drain/dequeue-proof
  routes. Delivery issues a custody receipt; because turns are self-certifying,
  store-and-forward is accountable across arbitrary delay.

- **Court** — adjudication, **witness-first**: where either party can exhibit a
  verifying witness, the exhibit decides; tribunals enter only on the
  non-certifiable residue. Equivocation evidence is a wire value, and a slash is
  an ordinary move from the bond well.

- **Shielded cells** — a cell can keep its balance, owner, and contents *hidden*
  while still proving what matters: a transfer balances — no value created or
  destroyed — without revealing a single amount. The direction this opens is the
  point: a holder attests a *predicate* over its hidden state ("over 18",
  "solvent", "in the allow-list") and a verifier learns only that the predicate
  holds, nothing else. Privacy is the `shield`/`unshield` kernel verb, not a
  bolt-on, so a shielded value is still conserved and a shielded spend still can't
  double-spend.

## Why it's not a toy

- **The verified executor *is* the executor.** The node's state producer is the
  Lean function `execFullForestG` — credential- and caveat-gated, proven sound —
  compiled and linked into the node via [`dregg-lean-ffi/`](dregg-lean-ffi/). It
  is not a model *of* the node; it is the function the node *calls*.

- **The executor is a memory program.** Every kernel field plus the receipt log
  projects onto one domain-tagged universal address space (`uproj`), and a
  verb's effect provably equals the fold of its emitted memory trace over that
  space. "The receipt binds the whole post-state" is therefore a constructive
  fact: every field has an address, nothing is left off the map, and tampering a
  field the effect did not legitimately touch makes the turn unprovable (the
  *anti-ghost* property).

- **Circuits are emitted from Lean.** Constraint systems are generated from
  proved Lean modules as byte-pinned descriptor artifacts (a SHA-256
  fingerprinted registry, drift-rejected in CI). The Rust prover *interprets*
  them; Rust authors no constraints. The live proof path is a single rotated
  multi-table circuit (IR-v2, R=24): a heterogeneous turn is split into maximal
  homogeneous cohort-runs and proven as a chain of rotated legs
  ([docs/PATH-PRESERVE.md](docs/PATH-PRESERVE.md)). STARK proofs (Plonky3,
  BabyBear, Poseidon2, FRI — post-quantum assumptions only) attest turns
  *additively* — verifying a turn never requires re-executing history — and
  recursive aggregation folds a whole history into one root a light client
  checks.

- **An honest assurance case.** [docs/ASSURANCE.md](docs/ASSURANCE.md) and
  [`AssuranceCase.lean`](metatheory/Dregg2/AssuranceCase.lean) state the
  guarantees as Lean theorems pinned to exactly `{propext, Classical.choice,
  Quot.sound}` — no `sorry`, no extra axioms — each with non-vacuity witnesses
  (the property provably *can* fail, and is proven not to), and each named seam
  between the theorems and the deployed node stated at file:line. The composed
  apex `deployed_system_secure` conjoins all five guarantees over one committed
  running-entry forest.

## Assurance — the five guarantees

The case to a light client is five guarantees plus the running entry:

- **A — Authority.** Every state change is justified by an unforgeable,
  non-amplified, fresh token chain. Production (mint) is gated on holding the
  issuer's capability; a grant conferring authority the holder lacks is rejected
  (the gate discriminates — it is not `:= True`).
- **B — Conservation.** Per asset, the resource sum is *identically zero* on
  every reachable state. Under `AssetId := CellId` every asset is its issuer
  cell; mint, burn, and fees are ordinary moves against negative-capable wells,
  and no verb can move any asset's sum.
- **C — Integrity.** A receipt binds the *whole* post-state. The circuit and the
  executor provably produce the same receipt; a commitment that drops a field is
  provably not a faithful bridge.
- **D — Freshness.** No replay, no double-spend: a committed spend's nullifier
  was fresh (an in-circuit sorted-tree non-membership opening), revocation takes
  effect at finality, and a stored capability cannot outlive its grantor's
  revocation (the retrieval-epoch rule).
- **E — Unfoolability.** A light client checking only the aggregate root learns
  A–D for the *entire* history, re-witnessing nothing; a tampered or reordered
  aggregate cannot bind.
- **R — The running entry.** A∧B∧C hold over `execFullForestG` *itself* — the
  exact gated function the deployed node invokes — not just an abstract model.

**Assumed, named, never hidden.** A small standard cryptographic floor — each
entering as a typed hypothesis, never an axiom: Poseidon2 collision-resistance,
BLAKE3 CR, Ed25519 EUF-CMA, HMAC unforgeability, AEAD, FRI/STARK soundness, BLS
quorum certs, and post-GST synchrony. Higher assumptions reduce onto this floor;
nothing else is load-bearing.

**Open, named — why this is not security-critical-ready.** The honest seams are
enumerated in §3 of [docs/ASSURANCE.md](docs/ASSURANCE.md). The crypto floor
above is *assumed*, not discharged — the named primitives enter as hypotheses.
The deployed-binary bridge is the largest open distance from l4v-grade: the
Lean→C/`.a` link correspondence and the wire-codec translation validation
(`dregg-lean-ffi/src/marshal.rs`) are stated as obligations, not yet proven.
On the shared devnet the per-turn STARK currently stays `proof_pending` (the
witness lands immediately; the async prove pool isn't attaching proofs), and
the deployed devnet binary runs solo (single-node ordering). No independent
audit has happened. **Do not use for anything security-critical.**

## deos — the agentic desktop

deos is the userlayer where a *window is a capability* and an interaction is a
*verified turn*. It adds **zero new trust**: every visual and interactive
primitive reduces to a kernel theorem. See [docs/deos/DEOS.md](docs/deos/DEOS.md).

- **htmx on crack.** A cell declares **affordances** — named, typed, cap-gated
  verified-turn templates. The "button" is a cap-gated effect, the "fragment" is
  the attested post-state surface, and *who may press it* is decided by held
  capabilities, not a session cookie. The render/fire gate is the genuine
  `is_attenuation` (`required ⊆ held`, the proven lattice), so progressive
  enhancement becomes progressive *attenuation*: an agent sees exactly the
  affordances its caps authorize. A `GatedAffordance` further pairs the cap-gate
  with a live cell-program state-gate — a button lights iff caps *and* state both
  pass, and goes dark the instant the cell changes
  ([`Deos/GatedAffordance.lean`](metatheory/Dregg2/Deos/GatedAffordance.lean)).

- **Transclusion = Xanadu, shipped.** A transcluded quote *is* a first-class
  provenanced citation of a source cell's committed field value — the value
  Nelson wanted, made literal and unbreakable. It is the verified cross-cell
  observation: the quote carries its provenance, cannot be forged or silently
  edited, and is per-viewer. Each of the four Xanadu properties is an existing
  kernel theorem restated for the docuverse, no new mathematics
  ([`Deos/Transclusion.lean`](metatheory/Dregg2/Deos/Transclusion.lean)).

- **A literate docuverse.** Beyond a quote, a whole *document* is a cell: writing
  is a cap-gated turn, the text is the fold of its edit history, and — Pijul-style
  — a **conflict is a first-class state you live in**, not a merge failure. When
  two people edit the same passage, the compatible parts merge cleanly and the
  genuine clash stays live as *both* alternatives, each attributed to who wrote it,
  until a later edit resolves it ([docs/deos/DOCUMENT-LANGUAGE.md](docs/deos/DOCUMENT-LANGUAGE.md)).

- **The powerbox (CapDesk).** Granting authority is *designate-then-attenuate*:
  you point at a resource and hand over a strictly weaker capability than you
  hold, never ambient authority ([`starbridge-v2/src/powerbox.rs`](starbridge-v2/src/powerbox.rs)).

- **The web-of-cells.** Cells address each other by `dregg://` reference; a peer
  reaches a surface by a verified attested read, not by trusting a server. Live
  DOM and JS bundles publish *as* web-of-cells cells.

- **Rehydratable frustum-snapshots — the dregg-only novelty.** A deos
  "screenshot" embeds a sturdyref behind a membrane, so *opening the image*
  re-attaches a live, **per-viewer, attenuated, liveness-typed** surface,
  confined by construction. The liveness-type is a *proven* confinement readout:
  `ReplayedDeterministic` is exactly the fragment whose every interaction went
  through the membrane ([`Deos/Rehydration.lean`](metatheory/Dregg2/Deos/Rehydration.lean)).
  The membrane composes `is_attenuation` across reshare hops, so a forwarded
  view can never amplify.

- **Recovery without a custodian.** Lose your device keys and you don't lose your
  identity. You nominate a council of *guardians*; any quorum of them can authorize
  a fresh key for you — they re-key your identity, they never reconstruct or hold
  your old one, and no single guardian (nor a sub-quorum) can act alone. The
  recovery is itself a verified turn, so anyone can check it was genuinely
  quorum-authorized — not a support ticket, a theorem. The same council can hold a
  *shared secret* no member individually knows and that only a quorum can ever open
  — the basis for sealed ballots, sealed-bid auctions, and key escrow no insider
  can peek at.

- **Branch-and-stitch — collaborative time-travel.** Rewind a shared history,
  *fork* a past moment into a private sandbox, try a different course of events,
  then *merge* back the parts you want. The sandbox is confined by construction —
  nothing it does touches the live world until you merge — and the merge re-checks
  authority at the moment of merging, so a permission revoked while you were off in
  the branch can't slip back in through it.

The forcing-function exemplar is a **multiplayer fog-of-war game where the
security property *is* the game mechanic**: what a player can see is exactly
what its caps authorize it to rehydrate, fail-closed, with a real proof
obligation (you provably cannot even *prove* the enemy's vision). It runs a full
agent-vs-agent match through the cap gate, with a membrane-negotiation spectator
surface. See [docs/deos/DEOS-APPS.md](docs/deos/DEOS-APPS.md).

## The durable verified workflow — what a deos app *is*

A deos app is a **cap-mandated, verified, durable workflow**: a multi-step
process that runs to completion exactly once even across crashes (durable, à la
DBOS), where each step is admitted only by a capability its actor holds
(attenuable, à la ocap), each step's effect is a verified turn the substrate
re-validates before it can become state (unforgeable + conserving, à la dregg),
and each step is surfaced as a fireable affordance (interactive, à la the web).
It is four surfaces of the one kernel, proven to be the same object. See
[docs/deos/DURABLE-WORKFLOW.md](docs/deos/DURABLE-WORKFLOW.md).

- **A step is a verified turn** — capability-gated, protocol-ordered, attested;
  no unauthorized or out-of-order step can ever commit
  ([`Protocol/Workflow.lean`](metatheory/Dregg2/Protocol/Workflow.lean)).
- **A step *is* an affordance fire** — the deos surface renders the choreography,
  it does not fork it: the cap-gate is the authorization, the state-gate is the
  phase precondition ([`Deos/WorkflowBridge.lean`](metatheory/Dregg2/Deos/WorkflowBridge.lean)).
- **One attenuable mandate** delegates the whole workflow, bounds every step,
  and keeps it legal forever under any adversarial schedule
  ([`Apps/CompartmentWorkflowMandate.lean`](metatheory/Dregg2/Apps/CompartmentWorkflowMandate.lean)).
- **Durable execution over verified turns** — [pg-dregg](docs/PG-DREGG.md) is
  "DBOS, but every step is a verified turn": reads are free SQL over the
  materialized mirror, writes go through the `AUTHZ → CHAIN → APPLY` spine, and
  crash-recovery re-validates every persisted turn on the way up
  ([`pg-dregg/src/workflow.rs`](pg-dregg/src/workflow.rs)).
- **Composition is right-skewed, and refinement is decidable.** Flows compose by
  choice `⊔`, sequence `⋆`, and meet `⊓`; the algebra is a right-skewed Kleene
  algebra with distributive meets (RSKA_d⊓), because the reactive rung reads both
  old and new state ([`Deos/FlowAlgebra.lean`](metatheory/Dregg2/Deos/FlowAlgebra.lean)).
  That makes *"does flow/policy A refine B"* a **decidable** question:
  `decideRefines : Flow → Flow → Bool` is sound and complete, with a `Decidable`
  instance ([`Deos/FlowRefine.lean`](metatheory/Dregg2/Deos/FlowRefine.lean)) —
  the foundation for ARGUS's "does this protocol evolution refine the spec?" bar.

## The surfaces

dregg is reachable from many directions; each one routes authorization through
the same verified kernel.

- **Polyglot SDKs.** Rust ([`sdk/`](sdk/) — `AgentRuntime` embeds the executor),
  TypeScript ([`@dregg/sdk`](sdk-ts/), browser-parsable), and Python
  ([`sdk-py/`](sdk-py/) — embeds the *real* Lean kernel via FFI). Two nouns and
  an inescapable authorization step: `.turn().sign().submit()`.
- **The MCP server** ([`node/src/mcp.rs`](node/src/mcp.rs)). AI-agent access,
  cap-gated: every tool a sub-agent calls carries a biscuit-style capability the
  node admits or refuses, routed through the Lean producer gate.
- **The Discord bot** ([`discord-bot/`](discord-bot/)). A first-class devnet
  citizen — councils, real signed turns, cipherclerk macaroons — not a
  read-only mirror.
- **The Studio / Playground** (the [site](site/)). Stage, run, and prove turns
  in the browser against a live wasm executor.
- **[pg-dregg](docs/PG-DREGG.md)** ([`pg-dregg/`](pg-dregg/)). dregg capabilities
  as a PostgreSQL Row-Level-Security + durable-workflow layer: a policy reads
  `dregg_admits('read', id)` instead of hand-rolled SQL — the decision is the
  *same one the kernel makes*, from the session's presented token — and reads
  are free SQL while writes are verified turns.
- **deos — the agentic desktop** ([`starbridge-v2/`](starbridge-v2/) ·
  [docs/deos/DEOS.md](docs/deos/DEOS.md)). The native cockpit that *embeds the
  real verified executor*: affordance surfaces, the `dregg://` web-of-cells
  browser tab, the interactive powerbox, transclusion, and rehydratable
  frustum-snapshots.
- **DreggDL** ([`dregg-deploy/`](dregg-deploy/)). Declarative deployment specs;
  an over-grant in a spec is caught as in-forest capability amplification before
  anything deploys.
- **The seL4 / Robigalia embedding** ([docs/FIRMAMENT.md](docs/FIRMAMENT.md) ·
  [docs/SEL4-EMBEDDING.md](docs/SEL4-EMBEDDING.md) · [`sel4/`](sel4/)). The
  *firmament* is a seL4-hosted ground that holds deterministic apps inside one
  capability fabric (seL4 caps isolate protection domains; dregg caps mediate
  the cells inside them) — an seL4 capability and a dregg capability are the
  *same* abstraction at two points on a distance parameter, and at `n = 1`
  (one machine) the distributed bounds collapse to strong local properties.
  **Today:** the Robigalia v0 demo boots Rust userspace protection domains, a
  real on-device STARK verifier PD, **and the executor PD itself** — the Lean
  kernel `execFullForestG` runs inside a real seL4 protection domain — on the
  seL4 microkernel under QEMU (aarch64; riscv64 booting too). The Lean-runtime
  embedding long called the *one true blocker* is closed: the runtime embeds
  single-threaded, with no allocator override, IO-free
  ([docs/EMBEDDABLE-LEAN-RUNTIME.md](docs/EMBEDDABLE-LEAN-RUNTIME.md)).
  **Remaining (named):** productionization — the crypto floor supplied from the
  verifier-STARK PD, and the decomposed multi-PD assembly.

## Run it yourself

```sh
git clone https://github.com/emberian/dregg && cd dregg
scripts/bootstrap.sh                                   # toolchain + first build
cargo build -p dregg-cli --release
export DREGG_NODE_URL=https://devnet.dregg.fg-goose.online
./target/release/dregg node status
./target/release/dregg demo --name you.dregg           # full app lifecycle, real signed turns
cargo run -p dregg-node run                             # or run your own node
```

[QUICKSTART.md](QUICKSTART.md) is the real 15-minute walkthrough (every command
verified live). [REORIENT.md](REORIENT.md) holds the architectural laws and the
build notes.

## The map

| Where | What |
|-------|------|
| [`metatheory/`](metatheory/) | **The system itself**, in Lean 4 (library `Dregg2`): the eight-verb kernel, the gated executor, the circuit IR + descriptor emission, the assurance case, and the deos modeling (`Dregg2/Deos/`). l4v-shaped: abstract spec → executable design → refinement proofs. |
| [`dregg-lean-ffi/`](dregg-lean-ffi/) | The link: compiles the Lean executor into `libdregg_lean.a` and exports the entry the node calls. |
| [`node/`](node/) | The daemon: HTTP/MCP API, gossip + blocklace sync, block production driven by the Lean producer. |
| [`circuit/`](circuit/) | The STARK stack: the Lean-descriptor interpreter (the prover), Plonky3, recursive aggregation, the light-client verifier. |
| [`cell/`](cell/), [`turn/`](turn/), [`wire/`](wire/) | Cell state, turn types, and the wire codec — the Rust data plane the executor's decisions flow through. |
| [`blocklace/`](blocklace/), [`federation/`](federation/), [`captp/`](captp/) | The DAG (signed, equivocation-detecting, BFT-final), committee machinery, and capability transport between nodes. |
| [`pg-dregg/`](pg-dregg/) | dregg capabilities + durable verified workflows as a PostgreSQL extension (RLS policies + the verified-write spine). |
| [`starbridge-v2/`](starbridge-v2/), [`starbridge-web-surface/`](starbridge-web-surface/) | deos: the native cockpit (embeds the real executor) and the web-surface / affordance / rehydration stack. |
| [`sdk/`](sdk/), [`sdk-ts/`](sdk-ts/), [`sdk-py/`](sdk-py/), [`cli/`](cli/), [`site/`](site/) | Building against dregg: the three SDKs, the `dregg` CLI, and the web Studio/Playground/Explorer. |
| [`starbridge-apps/`](starbridge-apps/), [`docs/`](docs/) | Applications built on the substrate, and the design documents. |

## Status

Research software under active development. The proof system is real, the
verified Lean executor is what the node runs, and the live devnet executes it.
The named opens above are open, and there has been no independent audit. **Do
not use for anything security-critical.**

- [Site / Docs / Studio / Explorer](https://dregg.fg-goose.online) · [Live devnet](https://devnet.dregg.fg-goose.online) · [Discord](https://discord.gg/eSTsv7DWcR) · [Pages mirror](https://emberian.github.io/dregg)

## License

AGPL-3.0-or-later — see [LICENSE](LICENSE) for the full text.
