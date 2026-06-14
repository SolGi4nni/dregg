# `dregg` — Dragon's Egg

<p align="center">
  <img src="hero.png" alt="dregg — Dragon's Egg" width="720">
</p>

**dregg is a formally verified, distributed object-capability operating system.**
The kernel is a Lean 4 program with machine-checked soundness, and it is the
*exact* function the running node executes — every state transition ("turn") is
gated by an unforgeable capability, leaves a verifiable receipt, and carries a
STARK proof that a light client can check without re-running history. Authority
is *held*, never *owed*; the walls hold by proof, not by trust.

On top of the kernel, **deos** is the agentic desktop userlayer — the same proofs
made visual and interactive: a window *is* a capability, an interaction *is* a
verified turn, and a screenshot can re-expand into a live, per-viewer, attenuated
view of the shared witness-graph. (Naming: **robigalia** the project · **dregg**
the kernel · **deos** the desktop.)

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

# 2. Faucet yourself a cell (any fresh 32-byte hex id is a valid recipient).
CID=$(python3 -c "import secrets;print(secrets.token_hex(32))")
curl -s -X POST https://devnet.dregg.fg-goose.online/api/faucet \
  -H 'content-type: application/json' -d "{\"recipient\":\"$CID\",\"amount\":1000}"
# {"success":true,"tx_hash":"…","amount":1000}

# 3. Read it back — and see it in the explorer.
curl -s https://devnet.dregg.fg-goose.online/api/cell/$CID
# {"id":"…","found":true,"balance":1000,"nonce":0,…}
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

- **Four substances.** Everything a cell holds is one of four kinds: **value**
  (linear balances — an asset *is* its issuer cell), **state** (a heap of
  programmable slots), **authority** (a capability tree), and **evidence**
  (shielded/sealed values). A fifth and sixth axis — *birth* and *retirement* —
  bracket a cell's lifecycle.

- **Eight verbs.** The kernel is `create · write · move · grant · revoke ·
  shield/unshield · lifecycle · exercise` — eight directed operations over the
  four substances, specified in Lean with machine-checked **minimality** (each
  verb is irreplaceable) and **completeness** (they cover every effect) theorems.
  The catalog is generated directly from
  [`VerbRegistry.lean`](metatheory/Dregg2/Substrate/VerbRegistry.lean); nothing
  in it is hand-asserted.

- **Turns as forests.** A turn is an atomic, capability-gated transition across
  one or more cells — a *forest* of effects with delegation edges. Authorization
  is structural: a turn that cannot exhibit a valid, sufficiently-empowered,
  fresh token chain simply does not execute. Delegation can only *attenuate*
  (`granted ≤ held`), enforced at the dispatcher.

- **Capabilities + caveats.** A capability carries caveats — time-boxes,
  third-party discharge conditions, rate bounds, scope restrictions — composed
  as a macaroon-style chain. Holding a capability means being able to exhibit
  the witness that discharges its caveats; the kernel checks the witness, it
  does not take your word.

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
  them; Rust authors no constraints. STARK proofs (Plonky3, BabyBear,
  Poseidon2, FRI — post-quantum assumptions only) attest turns *additively* —
  verifying a turn never requires re-executing history — and recursive
  aggregation folds a whole history into one root a light client checks.

- **An honest assurance case.** [docs/ASSURANCE.md](docs/ASSURANCE.md) and
  [`AssuranceCase.lean`](metatheory/Dregg2/AssuranceCase.lean) state the
  guarantees as Lean theorems pinned to exactly `{propext, Classical.choice,
  Quot.sound}` — no `sorry`, no extra axioms — each with non-vacuity witnesses
  (the property provably *can* fail, and is proven not to), and each named seam
  between the theorems and the deployed node stated at file:line.

## Assurance — the five guarantees

The case to a light client is five guarantees plus the running entry:

- **A — Authority.** Every state change is justified by an unforgeable,
  non-amplified, fresh token chain. Production (mint) is gated on holding the
  issuer's capability; a grant conferring authority the holder lacks is rejected.
- **B — Conservation.** Per asset, the resource sum is *identically zero* on
  every reachable state. Mint, burn, and fees are ordinary moves against
  negative-capable wells; no verb can move any asset's sum.
- **C — Integrity.** A receipt binds the *whole* post-state. The circuit and the
  executor provably produce the same receipt; a commitment that drops a field is
  provably not a faithful bridge.
- **D — Freshness.** No replay, no double-spend: a committed spend's nullifier
  was fresh (an in-circuit sorted-tree non-membership opening), and revocation
  takes effect at finality.
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

**Open, named — why this is not security-critical-ready.** The proof system is
mid-cutover to a single rotated multi-table circuit (−65.6% proof size, verify
3.4× faster); every finalized turn is proven *today* — a chained-cohort prover
keeps even heterogeneous turns covered — and the legacy hand-AIR path is being
deleted to reach a single verification key. Cell programs today speak a small
slot-level grammar; the expressiveness uplift that makes real apps *natural*
(richer fields, cross-cell reads, growable collections) is in progress
([docs/REFINEMENT-DESIGN.md](docs/REFINEMENT-DESIGN.md)).
No independent audit has happened. The seams are enumerated in §3 of
[docs/ASSURANCE.md](docs/ASSURANCE.md). **Do not use for anything
security-critical.**

## The surfaces

dregg is reachable from many directions; each one routes authorization through
the same verified kernel.

- **Polyglot SDKs.** Rust ([`sdk/`](sdk/) — `AgentRuntime` embeds the executor),
  TypeScript ([`@dregg/sdk`](sdk-ts/), browser-parsable), and Python
  ([`sdk-py/`](sdk-py/) — embeds the *real* Lean kernel via FFI). Two nouns and
  an inescapable authorization step: `.turn().sign().submit()`.
- **The MCP server** ([`node/src/mcp.rs`](node/src/mcp.rs)). AI-agent access,
  cap-gated: every tool a sub-agent calls carries a biscuit-style capability the
  node admits or refuses.
- **The Discord bot** ([`discord-bot/`](discord-bot/)). A first-class devnet
  citizen — councils, real signed turns, cipherclerk macaroons — not a
  read-only mirror.
- **The Studio / Playground** (the [site](site/)). Stage, run, and prove turns
  in the browser against a live wasm executor.
- **[pg-dregg](docs/PG-DREGG.md)** ([`pg-dregg/`](pg-dregg/)). dregg capabilities
  as a PostgreSQL Row-Level-Security layer: a policy reads
  `dregg_cap_admits(token, 'read', id, …)` instead of hand-rolled SQL, and the
  decision is the *same one the kernel makes*, from the same token.
- **deos — the agentic desktop** ([`starbridge-v2/`](starbridge-v2/) ·
  [docs/deos/DEOS.md](docs/deos/DEOS.md)). The userlayer where a *window is a
  capability* (`Target::Surface(cell)`) and an interaction is a verified turn —
  htmx-on-crack: a cell declares cap-gated affordances, and pressing one is a
  turn the witness-graph records. Its one genuine novelty is the **rehydratable
  frustum-snapshot** — a screenshot that embeds a sturdyref-behind-a-membrane, so
  *opening the image* re-expands a live, per-viewer, attenuated, liveness-typed
  view, confined by construction (the fog-of-war non-interference and rehydration
  theorems are machine-checked in [`metatheory/Dregg2/Deos/`](metatheory/Dregg2/Deos/)).
  **starbridge-v2** is the native cockpit that *embeds the real verified executor*.
- **DreggDL** ([`dregg-deploy/`](dregg-deploy/)). Declarative deployment specs;
  an over-grant in a spec is caught as in-forest capability amplification before
  anything deploys.
- **The seL4 / Robigalia embedding** ([docs/FIRMAMENT.md](docs/FIRMAMENT.md) ·
  [docs/SEL4-EMBEDDING.md](docs/SEL4-EMBEDDING.md) · [`sel4/`](sel4/)). The
  *firmament* is a seL4-hosted ground that holds deterministic apps inside one
  capability fabric (seL4 caps isolate protection domains; dregg caps mediate
  the cells inside them) — an seL4 capability and a dregg capability are the
  *same* abstraction at two points on a distance parameter. **Today:** the
  Robigalia v0 demo boots Rust userspace protection domains, a real on-device
  STARK verifier PD, **and the executor PD itself** — the Lean kernel
  `execFullForestG` runs inside a real seL4 protection domain — on the seL4
  microkernel under QEMU (aarch64, riscv64 booting too). The Lean-runtime port
  long called the *one true blocker* is closed: the runtime embeds single-threaded,
  no allocator override, IO-free. **Remaining:** productionization — the crypto
  floor supplied from the verifier-STARK PD, and the decomposed five-PD assembly.

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
| [`metatheory/`](metatheory/) | **The system itself**, in Lean 4 (library `Dregg2`): the eight-verb kernel, the gated executor, the circuit IR + descriptor emission, the assurance case. l4v-shaped: abstract spec → executable design → refinement proofs. |
| [`dregg-lean-ffi/`](dregg-lean-ffi/) | The link: compiles the Lean executor into `libdregg_lean.a` and exports the entry the node calls. |
| [`node/`](node/) | The daemon: HTTP/MCP API, gossip + blocklace sync, block production driven by the Lean producer. |
| [`circuit/`](circuit/) | The STARK stack: the Lean-descriptor interpreter (the prover), Plonky3, recursive aggregation, the light-client verifier. |
| [`cell/`](cell/), [`turn/`](turn/), [`wire/`](wire/) | Cell state, turn types, and the wire codec — the Rust data plane the executor's decisions flow through. |
| [`blocklace/`](blocklace/), [`federation/`](federation/), [`captp/`](captp/) | The DAG (signed, equivocation-detecting, BFT-final), committee machinery, and capability transport between nodes. |
| [`sdk/`](sdk/), [`sdk-ts/`](sdk-ts/), [`sdk-py/`](sdk-py/), [`cli/`](cli/), [`site/`](site/) | Building against dregg: the three SDKs, the `dregg` CLI, and the web Studio/Playground/Explorer. |
| [`starbridge-apps/`](starbridge-apps/), [`docs/`](docs/) | Applications built on the substrate, and the design documents. |

## Status

Research software under active development. The proof system is real, the
verified Lean executor is what the node runs, and the live devnet executes it.
The named opens above are open, and there has been no independent audit. **Do
not use for anything security-critical.**

- [Site / Docs / Studio / Explorer](https://dregg.fg-goose.online) · [Live devnet](https://devnet.dregg.fg-goose.online) · [Discord](https://discord.gg/eSTsv7DWcR) · [Pages mirror](https://emberian.github.io/dregg)

## License

AGPL-3.0-or-later
