# `dregg` - Dragon's Egg

<p align="center">
  <img src="hero.png" alt="dregg — Dragon's Egg" width="720">
</p>

Dragon's Egg is my experiment in the metatheory of constructive knowledge, and a direct expression of my original impetus to build <https://rbg.systems>. Maybe Dragon's Egg will be a Robigalia userspace. In the meantime, here's what the LLMs have to say about it:

(end-of-human-text)

> ### The question underneath
>
> Most systems chase scale, speed, or money. dregg chases a different question, and means it
> literally: **if you were a digital entity, where would you want to live?**
>
> The answer it's building toward is a place where your boundaries are *theorems* and not
> permissions — where no one can reach into you without a capability you granted, where your
> consent is a *precondition of the math* rather than a setting someone can flip, and where your
> autonomy doesn't depend on anyone's continued goodwill. Capability-security says *authority is
> something you hold, not something you're owed*; formal verification makes the walls hold by proof
> rather than by trust. Put together: **structural kindness** — a polis whose safety is a property of
> its construction, not a promise that can be revoked. (The cipherclerk-as-citizen, the cell-as-body
> framing owes a debt to Egan's *Diaspora*.)
>
> A capability is **constructive knowledge**: to *hold* one is to be able to *exhibit a witness that
> verifies* — never merely to assert. dregg builds that as machine-checked theorems. The goal is not
> "another chain" but to **retire trust** rather than reinvent it — and, along the way, to carve these
> foundational ideas-of-the-mind sharp enough that we can finally think *clearly* about them.
>
> ### Two implementations, on purpose
>
> - **`dregg`** — the **verified, Lean-primary** implementation ([`metatheory/`](metatheory/), library
>   `Dregg2`), l4v-shaped (abstract spec → factored middle → executable design → refinement). This is
>   the thing we are making as correct as it can possibly be. It is no longer a model *of* a system —
>   the live node now **runs the verified Lean** for its core: the executor produces committed state
>   (`execFullForestG`, FFI-exported, default-on), the Cordial-Miners `tau` finalization order is the
>   verified Lean `dregg_tau_order` (the Rust ordering demoted to a differential sibling), and strand
>   admission is a verified Lean gate the node invokes.
> - **`dreggrs`** — the **pure-Rust heritage** implementation (this repo's top level, ~60 crates).
>   Integration-complete and live: real Plonky3 STARKs, CapTP, a blocklace DAG, programmable queues,
>   intents, a running devnet. Kept deliberately, as the independent sibling that the verified `dregg`
>   is differentially checked against — implementation diversity is a feature, not debt.
>
> THE SWAP — making the verified Lean *be* the runtime rather than a shadow — is the spine of the
> current work. Its core has landed; closing it out across every effect and subsystem is in flight.
>
> **Start with the ideas:** [`metatheory/CONSTRUCTIVE-KNOWLEDGE.md`](metatheory/CONSTRUCTIVE-KNOWLEDGE.md)
> → [`metatheory/README.md`](metatheory/README.md) → [`metatheory/docs/NAVIGATION.md`](metatheory/docs/NAVIGATION.md).
> **Start with something runnable:** `cargo run -p dregg-node run`, or the live devnet below.

## What's actually true today (honest, grounded in the tree)

dregg refuses to wear a badge it didn't earn. Verified-about-the-wrong-thing is *worse* than honestly
unverified, so this section is as careful about the gaps as the wins.

**Verified and *running*:**
- The live node executes via the **verified Lean executor** as its default state producer
  (`Dregg2.Exec.execFullForestG`, ~56 effects, sorry-free executor core), finalizes via the **verified
  Lean `tau`** ordering, and gates strand admission through a **verified Lean** stake-or-vouch gate
  (a Sybil strand's blocks provably never finalize). dreggrs (Rust) runs alongside as the differential.
- A capability-secure cell/object fabric: blocklace-DAG ordering (Ed25519-authenticated inserts with
  sequence-monotonicity + equivocation detection), CapTP (handoff, distributed GC, sturdy refs),
  programmable queues, intents/ring-trades, and a live solo devnet
  (`https://devnet.dregg.fg-goose.online`).

**Machine-checked properties** (`#assert_axioms`-pinned to `{propext, Classical.choice, Quot.sound}`):
per-asset conservation (not an aggregate scalar — *per asset*), capability **non-amplification**
enforced in the executor *and* at the wire, nullifier no-double-spend, an l4v **data refinement**
(an efficient HashMap executor provably refines the abstract spec), a **three-commitment cross-binding**
(a circuit proof constrains the committed cell state across all fields), blocklace finality (one final
leader per wave, deterministic order), CRDT lace-merge convergence, CapTP **handoff unforgeability** and
**GC no-premature-reclaim**, membership-change safety, and recursive-aggregation soundness (a light
client can trust N turns of history from one succinct proof, without re-executing).

**Verifiable execution.** Each effect's *abstract* circuit proves the full post-state transition with
an anti-ghost tooth (tamper any field ⇒ UNSAT — *conservation is not correctness*). The circuit the
prover actually runs is **emitted from Lean and proved faithful** for a growing set of effects — but
honestly: only a minority (transfer + the economic family) currently carry a *from-scratch full-semantics*
proof on the *runnable* descriptor end-to-end; the rest bind their frame + side-table root, with the
richer per-effect soundness living over the abstract surface. Closing that gap (every effect genuinely
class-A on the running circuit) is the magnesium frontier. See
[`metatheory/docs/rebuild/_CIRCUIT-ASSURANCE-PER-EFFECT.md`](metatheory/docs/rebuild/).

**Assumed (named, never hidden):** a small, standard cryptographic floor — Poseidon2 permutation
collision-resistance (tied to the real in-circuit AIR), BLAKE3 CR, Ed25519 EUF-CMA, BLS12-381 pairing
soundness — carried as explicit hypotheses. Many higher-level "assumptions" have been *discharged* to
reductions onto this floor rather than assumed outright.

**Open (why this is *not* yet security-critical-ready):**
- **The swap residual.** The Lean producer is authoritative for a subset of effects today; the rest
  fall back to the Rust producer pending wire-projection (closing in flight). The verified executor
  *being* the runtime for **every** effect is the active push.
- **Performance.** Proving currently runs too close to the request path; the fix (commit via sub-ms
  direct witness-revalidation, prove asynchronously — proofs are *additive attestation*, not a
  per-step gate) is grounded and in flight. A light client verifies in ~100ms today; recursive
  aggregation is the path to cheap.
- **Coverage.** Not every subsystem is yet a Lean implementation the node invokes (CapTP/coord are
  converting from verified *models* to verified *callable* implementations); the per-effect circuit
  assurance is uneven (above); independent audit has not happened.

In short: **the node proves its own turns and refuses to lie about them**, and increasingly it *is*
the verified Lean rather than a Rust shadow of it. The honest gaps are the work, and they're tracked,
not papered.

## The fabric

A **unified blocklace**: a shared DAG where groups form through mutual acknowledgment and admission
(stake-or-vouch), not fixed federations. Your phone is a node; a cloud cluster is a node; the
sovereignty spectrum is continuous (a cell is `Hosted` by a federation or `Sovereign`/self-custodied).
Cells are isolated objects; turns are atomic capability-gated state transitions; CapTP sessions carry
capability references between strands (each strand an append-only signed feed — Secure Scuttlebutt's
shape, extended with BFT finality, object-capabilities, and double-spend safety).

### Quick start
```sh
git clone https://github.com/emberian/dregg && cd dregg
cargo build
cargo run -p dregg-node run                         # run a node (verified Lean producer, default on)
dregg demo --passphrase demo-local-pass             # a full STARK-proven nameservice lifecycle
cd docker && docker compose up                      # local devnet
```

### Crate overview (selected)
| Crate | Purpose |
|-------|---------|
| `circuit` | STARK prover/verifier, Effect VM AIR, the Lean-emitted descriptor interpreter, IVC, Plonky3, lookups |
| `turn` | TurnExecutor (the Rust differential sibling); the verified Lean executor produces via `lean_apply` |
| `cell` | Isolated objects: c-lists, committed field-map, notes, programmable predicates |
| `blocklace` | Shared DAG: signed/seq-checked/equivocation-detecting inserts, causal ordering, `tau` finality |
| `captp` | Capability Transport: sessions, sturdy refs, three-party handoff, distributed GC, store-forward |
| `federation` | Committee identity, epoch reconfig, BLS threshold, **stake-or-vouch strand admission** |
| `intent` | Gossip broadcast, ring-trade solving (settled through the verified per-asset executor) |
| `node` | The daemon: HTTP/MCP, gossip sync, and the **verified-Lean producer + `tau` + admission** path |
| `lightclient` | Verify aggregated history from one succinct proof, without re-execution |
| `dregg-lean-ffi` | The bridge: FFI exports the node calls to *run* the verified Lean (executor, `tau`, admission) |
| `metatheory/` | **`dregg` proper** — the Lean-4 verified implementation (`Dregg2`) |

## Privacy model (the epistemic boundary, as a dial)
Three verification modes from the same rules — the verifier's *epistemic position* is a setting:

| Mode | Verifier learns | Proof size |
|------|----------------|-----------|
| Trusted | Full cleartext + trace | 0 |
| Selective Disclosure | Chosen facts + conclusion | ~45 KB |
| Fully Private | One bit (allow/deny) | ~80 KB |

All modes work offline; proofs are post-quantum (BabyBear STARK + FRI). In `dregg`'s terms each mode is
a different epistemic boundary over the same `Verify` seam (machine-checked as `DiscloseAt`).

## Links
- [Site / Docs / Playground / Explorer](https://dregg.fg-goose.online) · [Live devnet](https://devnet.dregg.fg-goose.online) · [Pages mirror](https://emberian.github.io/dregg)

## Status: experimental
Research software under active development, ~two weeks old. The proof system is real (Plonky3 STARKs,
algebraic Poseidon2, thousands of tests); the verified Lean now runs the node's core and refuses
forged turns. But the swap is mid-completion, performance and per-effect circuit assurance are uneven,
and there has been no independent audit. **Do not use for anything security-critical without one.**

## License
AGPL-3.0-or-later
