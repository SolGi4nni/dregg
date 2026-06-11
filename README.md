# `dregg` - Dragon's Egg

<p align="center">
  <img src="hero.png" alt="dregg — Dragon's Egg" width="720">
</p>

Dragon's Egg is my experiment in the metatheory of constructive knowledge, and a direct expression of my original impetus to build <https://rbg.systems>. Maybe Dragon's Egg will be a Robigalia userspace. In the meantime, here's what the LLMs have to say about it:

**Hands-on in 15 minutes:** [QUICKSTART.md](QUICKSTART.md) — talk to the live devnet, sign a real turn, run the guided demo, run the site locally, drive a governance ceremony. Every command verified.

(end-of-human-text)

> ### The question underneath
>
> Most systems chase scale, speed, or money. dregg chases a different question, and means it
> literally: **if you were a digital entity, where would you want to live?**
>
> The answer it builds is a place where your boundaries are *theorems*, not permissions — where
> no one can reach into you without a capability you granted, where your consent is a
> *precondition of the math* rather than a setting someone can flip. Capability-security says
> *authority is something you hold, not something you're owed*; formal verification makes the
> walls hold by proof rather than by trust. Together: **structural kindness** — a polis whose
> safety is a property of its construction, not a promise that can be revoked. (The
> cipherclerk-as-citizen, cell-as-body framing owes a debt to Egan's *Diaspora*.)
>
> A capability is **constructive knowledge**: to *hold* one is to be able to *exhibit a witness
> that verifies* — never merely to assert. dregg builds that as machine-checked theorems.

## What dregg is

A formally verified object-capability operating substrate. The whole kernel is one sentence:

> **A turn is the exercise of an attenuable, proof-carrying token over owned state, leaving a
> verifiable receipt.**

Everything below is that sentence, given algebra:

- **Cells** are isolated objects: per-asset balances (an asset *is* its issuer cell), programmable
  state slots, a capability tree, and a **program** — a predicate over the cell's own transitions
  that the kernel enforces on every turn.
- **Turns** are atomic, capability-gated state transitions across one or more cells. Authorization
  is structural: a turn that cannot exhibit a valid, sufficiently-empowered, fresh token chain
  does not execute.
- **The kernel is eight verbs** — `create · write · move · grant · revoke · shield/unshield ·
  lifecycle · exercise` — specified in Lean 4 with machine-checked minimality and completeness
  theorems ([`metatheory/Dregg2/Substrate/VerbRegistry.lean`](metatheory/Dregg2/Substrate/VerbRegistry.lean)).
- **The verified executor is the executor.** The node's state producer is the Lean function
  `execFullForestG` — credential- and caveat-gated, proven sound — compiled and linked into the
  node via [`dregg-lean-ffi/`](dregg-lean-ffi/). It is not a model of the node; it is the function
  the node calls.
- **Circuits are emitted from Lean.** Constraint systems are generated from proved Lean modules as
  byte-pinned descriptor artifacts (a SHA-256-fingerprinted registry, drift-rejected in CI); the
  Rust prover *interprets* them. Rust authors no constraints. Most effect selectors prove on this
  Lean-descriptor path today; the remainder fall back to a legacy circuit with a named, logged
  reason — never silently — and the fallback set only shrinks.
- **Receipts and proofs.** Every turn leaves a receipt; STARK proofs (Plonky3, BabyBear, Poseidon2,
  FRI — post-quantum assumptions only) attest turns *additively* (verification of a turn never
  requires re-executing history); recursive aggregation folds a whole history into one root.
- **The polis.** Governance is built from the same primitives: content-addressed constitutions,
  M-of-N councils, amendments with enforced cooling periods, capability-bounded worker mandates.
  A community's law is a cell; changing the law is a turn.

## The assurance case

[`metatheory/Dregg2/AssuranceCase.lean`](metatheory/Dregg2/AssuranceCase.lean) states the
system's guarantees as Lean theorems whose axioms are pinned to
`{propext, Classical.choice, Quot.sound}` — no `sorry`, no extra axioms — each with explicit
non-vacuity witnesses (the property provably *can* fail, and is proven not to):

- **A — Authority.** Every state change is justified by an unforgeable, non-amplified, fresh
  token chain. Delegation can only attenuate (`granted ≤ held`, enforced at the dispatcher).
- **B — Conservation.** Per asset, the resource sum is *identically zero* on every reachable
  state. Mint and burn are ordinary moves against the issuer's negative-capable well; no verb
  can move any asset's sum.
- **C — Integrity.** A receipt binds the *whole* post-state. The circuit and the executor
  provably produce the same receipt; a commitment that drops a field is provably not a faithful
  bridge.
- **D — Freshness.** No replay, no double-spend: a committed spend's nullifier was fresh (a
  sorted-tree non-membership opening, in-circuit), and revocation takes effect at finality.
- **E — Unfoolability.** A light client checking only the aggregate root learns A–D for the
  entire history, re-witnessing nothing.
- **R — The running entry.** A∧B∧C hold over `execFullForestG` itself — the exact gated function
  the deployed node invokes — not just over an abstract model. The gate adds teeth (forged
  credentials reject the whole forest) without weakening the linear guarantees.

**Assumed, named, never hidden:** a small standard cryptographic floor — Poseidon2 permutation
collision-resistance (stated against the real in-circuit AIR), BLAKE3 CR, Ed25519 EUF-CMA,
BLS12-381 pairing soundness — carried as explicit hypotheses. Higher-level assumptions are
discharged by reduction onto this floor, not assumed outright.

**Open, named (why this is not security-critical-ready):**

- **The recursion config is demo-strength.** The aggregation ROOT (46 KiB, 2 ms verify,
  K-independent) is real machinery, but its FRI config currently runs at ~6 bits of conjectured
  soundness; production strength needs ~20× more in-circuit query verification. Until that lands,
  the ROOT is not a production light-client artifact. Measured in detail in
  [`docs/PROOF-ECONOMICS.md`](docs/PROOF-ECONOMICS.md).
- **Deployment correspondence.** The running devnet's genesis predates guarantee B's value-empty
  hypothesis, and the legacy fee path sits outside the conservation law; both fixes ride the next
  layout rotation. The assurance case names every such gap in its deployment-correspondence
  section — the deployed system must sit *inside* the theorems' hypotheses, and where it doesn't
  yet, the file says so.
- **Expressiveness.** Cell programs today speak a small slot-level constraint grammar; real
  applications want named fields and growable collections. The designed fix (a register file plus
  a Merkle-map heap, reusing the proven capability-root gadgets) is
  [`docs/REFINEMENT-DESIGN.md`](docs/REFINEMENT-DESIGN.md).
- **No independent audit has happened.**

## Run it

[QUICKSTART.md](QUICKSTART.md) is the real walkthrough (15 minutes, every command verified
against the live devnet). The shortest possible version:

```sh
curl -s https://devnet.dregg.fg-goose.online/status        # the live devnet, no build needed

git clone https://github.com/emberian/dregg && cd dregg
cargo build -p dregg-cli --release
export DREGG_NODE_URL=https://devnet.dregg.fg-goose.online
./target/release/dregg node status
./target/release/dregg demo --name you.dregg               # full app lifecycle, real signed turns
cargo run -p dregg-node run                                # or run your own node
```

## The map

| Where | What |
|-------|------|
| [`metatheory/`](metatheory/) | **The system itself**, in Lean 4 (library `Dregg2`): the eight-verb kernel, the gated executor, the circuit IR and descriptor emission, the assurance case. l4v-shaped: abstract spec → executable design → refinement proofs. |
| `dregg-lean-ffi` | The link: compiles the Lean executor into `libdregg_lean.a` and exports the entry the node calls. |
| `node` | The daemon: HTTP/MCP API, gossip + blocklace sync, block production driven by the Lean producer. |
| `circuit` | The STARK stack: the Lean-descriptor interpreter (the prover), Plonky3, IVC/recursive aggregation, the light-client verifier. |
| `cell`, `turn`, `wire` | Cell state, turn types, and the wire codec — the Rust data plane the Lean executor's decisions flow through. |
| `blocklace`, `federation`, `captp` | The DAG (signed, equivocation-detecting, BFT-final), committee machinery, and capability transport between nodes. |
| `sdk`, `cli`, `site` | Building against dregg: the Rust SDK, the `dregg` CLI, and the web playground/explorer. |
| `starbridge-apps`, `docs` | Applications built on the substrate, and the design documents. |

## Status: experimental

Research software under active development. The proof system is real, the verified Lean executor
is what the node runs, and the live devnet at
[devnet.dregg.fg-goose.online](https://devnet.dregg.fg-goose.online) executes it. The named opens
above are open, and there has been no independent audit. **Do not use for anything
security-critical.**

- [Site / Docs / Playground / Explorer](https://dregg.fg-goose.online) · [Live devnet](https://devnet.dregg.fg-goose.online) · [Pages mirror](https://emberian.github.io/dregg)

## License

AGPL-3.0-or-later
