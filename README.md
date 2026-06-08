# `dregg` - Dragon's Egg

<p align="center">
  <img src="hero.png" alt="dregg — Dragon's Egg" width="720">
</p>

Dragon's Egg is my experiment in the metatheory of constructive knowledge, and a direct expression of my original impetus to build <https://rbg.systems>. Maybe Dragon's Egg will be a Robigalia userspace. In the meantime, here's what the LLMs have to say about it:

(end-of-human-text)

> **Two layers here, and it matters which you're looking at.**
>
> 1. **dregg1 — the running Rust fabric** (~60 crates, this repo's top level). Integration-complete
>    and live: a real Plonky3 STARK proof system, CapTP, a blocklace DAG, programmable queues,
>    intents, a running devnet. It *works* — but its executor enforces authority in plain Rust,
>    outside any proof. This is the **Silver Vision**: everything connected, trust-based at the core.
> 2. **dregg2 — the verified successor, in Lean 4** ([`metatheory/`](metatheory/)). The semantic core
>    *as proof*, l4v-shaped (Abstract Spec → factored middle → executable Design → refinement). It is
>    no longer just a seed: the verified executor *models the real one*, ~49 effects carry an
>    end-to-end `execute → prove → verify` path with real STARK proofs and forged-state rejection,
>    and the **node commit path proves every finalized turn** (per-cell, flag-gated, on by default in
>    the devnet). The active frontier is **hardening the executable boundary** and **the swap**
>    (making the verified executor *be* the runtime).
>
> **Start with dregg2 for the ideas:** [`metatheory/CONSTRUCTIVE-KNOWLEDGE.md`](metatheory/CONSTRUCTIVE-KNOWLEDGE.md)
> → [`metatheory/README.md`](metatheory/README.md). **Start with dregg1 to run something:**
> [`STATUS.md`](STATUS.md) + `cargo run -p dregg-sdk --example hello_receipt_chain`. Root-level design
> `*.md` now live in [`docs-old/`](docs-old/) and are **not** authoritative — trust the code.

## What's actually true today (honest, grounded in the current tree)

A capability is **constructive knowledge**: to *hold* one is to be able to *exhibit a witness that
verifies* — never merely to assert. dregg2 builds that as theorems, and the goal is not "another
chain" but to **retire trust** rather than reinvent it.

**Real and runnable:**
- A capability-secure cell/object fabric with blocklace-DAG ordering, CapTP, programmable queues, and
  a live solo devnet (`https://devnet.dregg.fg-goose.online`).
- A verified Lean executor (`Dregg2.Exec.execFullForestG`, ~56 effects, sorry-free in the executor
  core) that models the Rust `apply.rs`.
- **Verifiable execution.** Each effect's circuit proves the *full* post-state transition — every
  kernel field, with an anti-ghost tooth (tamper any field ⇒ UNSAT, not just balance-conservation).
  ~49 effects have an executor-derived witness generator + real Plonky3 STARK prove/verify (forged
  post-state rejected, in tests); whole-turn proofs bind a turn's effects to **one authenticated
  state root** (per cell); and with `--prove-turns` the node produces + *verify-gates* a real STARK
  proof for **every committed turn** (devnet enables it).
- **Machine-checked properties** (`#assert_axioms`-pinned): per-asset conservation (modulo an explicit
  fee-burn), capability **non-amplification** enforced in the executor *and* at the wire, nullifier
  no-double-spend, range-bound shielded value-creation, and an l4v **data refinement** (an efficient
  HashMap executor provably refines the abstract spec — so soundness transfers to the fast version).

**Assumed (named, never hidden):** collision-resistance of Poseidon2 (one explicit assumption, tied
to the real in-circuit Poseidon2 AIR — never "proved" in Lean), plus the §8 crypto carriers (ed25519
EUF-CMA, STARK extractability, DLog binding) as explicit hypotheses across a clean portal.

**Open — why this is *not* yet security-critical-ready:**
- **The executable boundary.** The gated FFI entry today (a) derives admission context — expiry,
  budget, freeze, receipt-head — from the *untrusted turn envelope* instead of node state, and
  (b) maps a turn whose body fails-but-fee-prologue-commits to a success bit. Both must be fixed
  (host-fed context; a three-way `Rejected | PrologueCommitted-BodyFailed | BodyCommitted` result).
  A second, *ungated* handler export exists and must be removed or fenced.
- **Canonical semantics.** For a few effects (notably `exercise`) the executor and the handler model
  disagree on required authority; the source-of-truth must be decided and a real facet classifier wired.
- **Concrete crypto surfaces.** The per-turn *demo* witnesses use toy hash folds; the abstract proofs
  carry the real injectivity hypotheses, but the concrete surfaces aren't yet Poseidon2 end-to-end.
- **Composition & scale.** Whole-turn/coordinated proof composition has tracked `sorry` portals;
  cross-cell aggregation (Silver→Gold) is future; consensus isn't yet connected to the verified
  executor; ~35 effects aren't yet in the Rust↔Lean differential (the remaining "swap" surface,
  mapped in [`metatheory/docs/rebuild/_RUST-LEAN-DIVERGENCE-LEDGER.md`](metatheory/docs/rebuild/_RUST-LEAN-DIVERGENCE-LEDGER.md)).

In short: **the kernel proves its own turns and refuses to lie about them**, and where the Lean
executor is exercised it *agrees* with the Rust one — but the trust boundary around it, and the path
to making the verified executor *be* the runtime, are the active work.

## dregg1 — the running fabric (Rust)

A **unified fabric**: a shared blocklace (DAG) where groups form emergently through mutual
acknowledgment — no fixed federations. Your phone is a node; a cloud cluster is a node; the
sovereignty spectrum is continuous. Cells are isolated objects; turns are atomic state transitions;
CapTP sessions carry capability references; intents broadcast needs and ring trades solve them
trustlessly. (Semantic-core verification is dregg2's job; the algebraic/circuit debt is tracked
separately, *not* this README.)

### Key capabilities
- **CapTP** — sessions, sturdy refs, distributed GC, three-party handoff, store-and-forward.
- **Programmable Queues** — Merkle queues with attached DSL programs, enforced by the executor.
- **DFA Routing** — governance-controlled route tables compiled to prefix-trie state machines.
- **Nameservice** — hierarchical names, rent-based anti-squatting, cross-federation resolution.
- **Intent Solving** — privacy-preserving marketplace; commit-reveal; coordinator-free ring trades.
- **Effect VM** — an abstract instruction set proven per-turn in one STARK; the Lean executor's
  per-turn proving (above) is its verified successor.

### Quick start (dregg1)
```sh
git clone https://github.com/emberian/dregg && cd dregg
cargo build
cargo run -p dregg-node run                       # run a node
cargo run -p dregg-demo-agent                      # full pipeline: token + STARK + turn
cd docker && docker compose up                     # local devnet
```

### Crate overview (dregg1)
| Crate | Purpose |
|-------|---------|
| `circuit` | STARK prover/verifier, Effect VM AIR, specialized AIRs, IVC, Plonky3, LogUp lookups |
| `turn` | TurnExecutor: call forests, journal rollback, pipeline execution, queue programs |
| `cell` | Isolated objects with c-lists, notes, programs, oblivious transfer |
| `blocklace` | Shared DAG consensus. Content-addressed blocks, causal ordering, finality |
| `captp` | Capability Transport Protocol: sessions, sturdy refs, handoff, distributed GC |
| `federation` | Ed25519 BFT, state roots in blocks, epoch reconfig, LightClientProof |
| `intent` | Gossip broadcast, local Datalog matching, commit-reveal, IT-PIR discovery |
| `storage` | Programmable queues, relay operators, inboxes, erasure-coded availability |
| `bridge` | Token-to-circuit pipeline, blinded membership, predicate proofs |
| `cli` | User-facing CLI: cell, turn, cap, namespace, route, storage, cclerk |
| `sdk` | AgentCipherclerk, AgentRuntime, HD keys, verification modes, IT-PIR client; `verify_full_turn` |
| `node` | Federation daemon: HTTP API, MCP server, gossip sync; full-turn proving on the commit path |
| `net` | Quinn QUIC, Plumtree gossip, topic-based dissemination |
| `commit` | 4-ary Merkle trees (BLAKE3 fast / Poseidon2 ZK), fold deltas |
| `token` | AuthToken: Macaroon HMAC-SHA256 + Biscuit Ed25519+Datalog |
| `dregg-lean-ffi` | The bridge to the verified Lean executor (shadow differential; the swap target) |

## Privacy model (the epistemic boundary, in practice)
Three verification modes from the same Datalog rules — the verifier's *epistemic position* is a dial:

| Mode | Verifier learns | Proof size |
|------|----------------|-----------|
| Trusted | Full cleartext + trace | 0 |
| Selective Disclosure | Chosen facts + conclusion | ~45 KB |
| Fully Private | One bit (allow/deny) | ~80 KB |

All modes work offline; proofs are post-quantum (BabyBear STARK + FRI). In dregg2's terms: each mode
is a different *epistemic boundary* over the same `Verify` seam (now machine-checked as `DiscloseAt`).

## Links
- [Site / Docs / Playground / Explorer](https://dregg.fg-goose.online) · [Live devnet](https://devnet.dregg.fg-goose.online) · [Pages mirror](https://emberian.github.io/dregg)

## Status: experimental
Research software under active development. dregg1's proof system is real (Plonky3 STARKs, algebraic
Poseidon2, 2000+ tests); its networking/consensus are functional but not battle-tested. dregg2 (the
Lean verification) now proves real per-turn execution and refuses forged turns — but the executable
boundary, the canonical-semantics questions, and the swap to make the verified executor *the* runtime
are open work. **Do not use for anything security-critical without independent audit.**

## License
AGPL-3.0-or-later
