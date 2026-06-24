# `metatheory/` — dregg's verified core

This directory is the formal heart of dregg: a Lean 4 library, named **`Dregg2`**, that is
not a *model* of the system sitting beside it but the system's *executor*, its *circuits*,
and its *assurance case*, all in one corpus.

Three facts orient everything else.

1. **The Lean kernel IS the executor.** The body the deployed node runs to apply a turn —
   `execFullForestG`, behind the `dregg_exec_full_forest_auth` FFI export
   (`Dregg2/Exec/FFI.lean`, reached through `dregg-lean-ffi`) — is the same definition the
   theorems are proved about. There is no Rust executor to keep in sync with a Lean spec;
   the verified definition *is* the production code path.

2. **Circuits are emitted from Lean** (architectural **law #1: zero Rust-authored
   constraints or AIRs, ever**). Every constraint set the prover enforces is a byte-pinned
   artifact emitted from a proved Lean module (the Argus IR and the descriptor JSONs); Rust
   only *interprets* those artifacts. A coverage gap is closed by emitting from a new proved
   module, never by hand-authoring a constraint.

3. **The assurance case is an artifact you can read.** `Dregg2/AssuranceCase.lean` states
   the five guarantees the system makes to a light client and, under each, assembles exactly
   the theorems that discharge it — *and* names its own boundary seams. It is meant to be the
   document a verification-literate evaluator reads to decide whether to trust the core.

A capability here is **constructive knowledge**: to *hold* one is to be able to *exhibit a
witness that verifies*, never merely to assert it. Authority, conservation, and integrity are
all projections of that single idea.

---

## The five guarantees

`Dregg2/AssuranceCase.lean` is organized by guarantee, not by module. Each is a small
theorem-DAG whose apex is `#assert_axioms`-clean and whose leaves are independently pinned in
their home modules.

| | Guarantee | Apex |
|---|---|---|
| **A** | **Authority** — no effect confers more authority than was held; every change rides an unforgeable, non-amplified, fresh token chain | `authority_guarantee` (over the real `List Auth` attenuation lattice, with teeth: an amplifying grant is *rejected*) |
| **B** | **Conservation** — per asset, the resource sum is identically zero on every reachable state | `conservation_guarantee` / `reachable_total_zero` (W1: every asset is its issuer cell; the issuer well carries −supply; mint/burn/bridge are ordinary moves) |
| **C** | **Integrity** — a receipt binds the *whole* post-state; a tampered field is rejected | `integrity_guarantee_memory_program` (the executor is a memory program: `uproj` of all 17 kernel fields equals the fold of the verb's emitted Blum trace) |
| **D** | **Freshness** — no replay / double-spend; a spent nullifier was fresh; revocation takes effect at finality | `freshness_guarantee` (anti-replay is the noteSpend term's own `interp`, not a side table) + the R7 stored-cap retrieval-epoch rule |
| **E** | **Unfoolability** — a light client checking only `verify agg.root` learns A–D for the whole history, re-witnessing nothing | `light_client_verifies_whole_history` (proofs as additive attestation; a reordered chain forces `ChainBound = False`) |
| **R** | **The running entry** — A∧B∧C hold over the executor the node *actually invokes* | `running_entry_sound` (over `execFullForestG`, the FFI body — not a sibling abstraction) |

Each guarantee carries an explicit **floor** (what it rests on) and, where the deployed node
sits outside a theorem's hypotheses, a named **deployment-correspondence** note. The case does
not launder a seam it cannot close — it names it (the prover partition, the host-fed
`ShadowHostCtx` admission inputs, producer coverage; see *Honest open items* below).

---

## The architecture

### The substrate — eight verbs (`Dregg2/Substrate/VerbRegistry.lean`)

The kernel signature is **eight survivor verbs** — `create · write · move · grant · revoke ·
shield/unshield · lifecycle` — each the structural rule of exactly one of the four substances
(linear value, non-forgeable authority, monotone evidence, guarded-mutable state) plus birth
and retirement. The registry reifies this as Lean data with two theorems that make it
load-bearing:

- **Completeness** — the live 27-variant wire `Effect` enum is reified one-tag-per-variant, so
  the compiler's exhaustiveness check on `classify` *is* the completeness proof: a new wire
  variant with no registry entry will not compile. `no_live_factory_tags` proves the doomed
  families (escrow, bridge-3phase, queue, seal/swiss/sturdyref…) are *deleted*, not
  reclassified — they re-land as verified factory cell-programs (`Dregg2/Apps/*Factory.lean`).
- **Minimality** — `verbBehavior` assigns each verb a (substance, polarity) and is proved
  *injective* (`minimality`, `each_verb_irreplaceable`): drop any one verb and a behavior no
  other verb provides is lost. The eight are independent.

### The executor — `execFullForestG` (`Dregg2/Exec/`)

`execFullForestG` is the credential-and-caveat-**gated** whole-forest step. The gate
`gateOK = credentialValid ∧ capAuthorityG ∧ caveatsDischarged` fires fail-closed in front of
the ungated executor; the linear guarantees ride an `eraseG` bridge onto the existing
`FullForest` theorems, so the gate *adds teeth* (a forged credential, an unauthorized cap, or
a false caveat ⇒ the whole forest rejects) without weakening conservation or non-amplification.
The `credentialValid` leg is the §8 portal (routed to ed25519 / HMAC carriers); the
`capAuthorityG` leg (`granted ≤ held`) is verified *in Lean* — it is exactly the
`is_attenuation` check dregg1's CapTP delivery failed to perform.

### The Argus circuit — emitted from Lean (`Dregg2/Circuit/Argus/`)

Every effect is one term of the **Argus IR**. The term's `interp` *is* the verified executor;
its `compile` *is* the runnable circuit; the two are proved to agree, so the circuit cannot
drift from what the system does. The agreement is not a per-effect grind: `compile` is a
**fold** over the IR (`CompileFold`), so executor⟺circuit agreement on the finite set of
constructors lifts to agreement on *all* terms by initiality (the N²→1 collapse). The
effect-annotated fold (`CompileE`) carries the genuine per-effect circuits at the leaves
(~29 effect welds under `Argus/Effects/`, transfer/mint/burn each proven distinct). Each weld
carries an executor-derived witness through a real Plonky3 STARK `prove`/`verify`, with the
**anti-ghost tooth**: tampering an absorbed state-block column makes the constraint UNSAT.

Above the per-effect layer sit the five apex layers — the **descriptor circuit** (`Receipt`:
a turn binds to one authenticated state root, `argus_commits_to_one_receipt`), coeffects,
joint turns, disclosure, and the **light-client theorem** (`Aggregate` /
`RecursiveAggregation`: checking one aggregate root attests the whole history). The whole
circuit library builds as one coherent anchor (`Dregg2/Circuit/Argus.lean`).

### The distributed layer (`Dregg2/Distributed/`, `Dregg2/Coord/`, `Dregg2/Consensus/`)

The federation is *Secure-Scuttlebutt-on-crack*: a **blocklace** (block-DAG-lace) where each
author's blocks form a **strand** (an SSB feed). The live Rust consensus engine
(Cordial-Miners-style DAG + a Stingray budget) is pinned by an executable Lean model + golden
differential: blocklace finality (`finalLeaders_one_per_wave`), strand fork-freedom
(`forkFree_iff_seqMonotone`), CRDT lace-merge as a semilattice join (`LaceMerge.*`), CapTP
handoff-unforgeability + leased GC, cross-cell atomic joint turns
(`jointApplyAll_atomic`), threshold decryption, and cell migration across federations
conserving balance + caps.

### The apps — verified on the gated executor (`Dregg2/Apps/`)

The application layer is verified *over `execFullForestG`* (the `*Gated.lean` modules:
nameservice, shielded payment, identity, governed namespace, privacy voting, compute exchange,
bounty board, and more), not over an ungated escape hatch. The doomed kernel verb families are
re-provided here as factory cell-programs (`EscrowFactory`, `ObligationFactory`, `QueueFactory`,
`InboxFactory`, `PubsubFactory`, `BridgeCell`, `CapSlotFactory`), each carrying its own safety
keystones — the land-before-kill replacements the verb registry cross-references by name.

---

## The proof discipline

**Every keystone is pinned to the kernel-clean axiom triple**
`{propext, Classical.choice, Quot.sound}` — and *nothing else*. The mechanism lives in
`Dregg2/Tactics.lean` (`docs/AXIOM-HYGIENE.md` is the prose):

- `#assert_axioms foo` / `#assert_clean foo` — pin one keystone; errors at build time if its
  transitive axiom set escapes the triple (notably on the kernel open-hole axiom, i.e. a leaked open hole).
- `#assert_all_clean [a, b, c]` — pin a list in one command.
- `#assert_namespace_axioms NS (except …)?` — pin *every* theorem under a namespace; strictly
  stronger than a hand-curated block because it cannot miss one someone forgot to add.

These are **pure rejectors**: a checker can only error, never close or weaken a goal, so adding
one can never make a false theorem look true. They were validated non-vacuous against a planted
`axiom bad : True`. `Dregg2/Claims.lean` is the corpus-wide CI net (~190 per-keystone pins);
`Dregg2/AssuranceCase.lean` is the by-guarantee reading artifact. A textual whole-corpus open-hole grep
(`scripts/axiom-hygiene-guard.sh`) is the second guard layer.

**Non-vacuity is tested in both polarities.** A guarantee is not just *true* — its teeth are
exhibited: a tampered receipt is UNSAT, an amplifying grant is rejected, a replayed nullifier
fails closed, a field-dropping commitment is *not* a faithful bridge. Spot-checks use `#guard`
/ `by decide` — never `native_decide` on a non-decidable prop, and never an `#eval -- expected`
comment masquerading as a test.

**The honest seams are named crypto primitives, and only those.** Cryptographic soundness is
the circuit/portal's job, never Lean's. The trust floor is a small, explicit set —
Poseidon2-permutation CR, BLAKE3 CR, ed25519 EUF-CMA, HMAC, AEAD, discrete-log hardness, the
FRI/STARK soundness chain, and post-GST progress for liveness — each entering as a `Prop`
typeclass parameter or hypothesis (a *carrier*), **never as an `axiom` keyword**, which is
precisely why they do not appear in `collectAxioms` and do not trip the hygiene guards. If a
genuine `axiom`-keyword oracle were ever introduced it would surface there and require a
commented allow-list entry. The floor never widens to silence a failure.

---

## How to build

The toolchain is pinned (`leanprover/lean4`, mathlib via a local `path` require in
`lakefile.toml`).

```sh
lake build Dregg2                 # the whole verified corpus (executor + circuits + distributed + apps)
lake build Dregg2.Claims          # the corpus-wide axiom-hygiene CI net (~190 pins)
lake build Dregg2.AssuranceCase   # the five guarantee apexes, by guarantee
```

For a single file during concurrent work, `lake env lean Dregg2/<Module>.lean` is race-free
(reads oleans, writes none) — never run `lake build` mid-swarm. The `Metatheory/*` sibling
library (the candidate-independent logic of constructive knowledge and authority) is its own
`lean_lib`.

**Becoming the node's executor.** After Lean changes, reseed the FFI closure with
`../dregg-lean-ffi/scripts/rebuild-dregg2-closure.sh` *before* running any lean-shadow tests.
That closure links the `@[export] dregg_exec_full_forest_auth` entry into `dregg-lean-ffi`; the
node calls it as `produce_via_lean` / `lean_shadow`. The thing the theorems are about is the
thing the binary runs.

---

## Map — navigating the corpus

`Dregg2/` is large (~790 Lean modules). The high-value groups:

| Group | What lives there |
|---|---|
| `Substrate/` | the 8-verb registry + minimality/completeness theorems (the kernel signature) |
| `Exec/` | the executor: `FullForestAuth` (`execFullForestG`), `RecordKernel`, `UniversalBridge` (the memory-program proof), `ConcreteKernel` (the HashMap-backed l4v refinement), `FFI` |
| `Circuit/`, `Circuit/Argus/` | the emitted circuits: the IR, the `interp`=executor / `compile`=circuit welds, the descriptor + aggregation apexes, the light-client theorem |
| `Distributed/`, `Coord/`, `Consensus/` | blocklace / strand / CapTP / joint-turn / migration — the federation, model + differential |
| `Authority/`, `Crypto/` | the capability/caveat model; the §8 portals (Poseidon2 / Pedersen / Merkle / non-membership) as dischargeable layered contracts |
| `Apps/` | applications verified on the gated executor + the factory cell-programs (escrow/queue/bridge/…) |
| `Spec/` | the factored abstract spec the executor refines (guards, conservation, the generative capability graph, the hyperedge turn) |
| `Proof/`, `Calculus/`, `DSL.lean`, `Catalog.lean` | the program logic (WP/VCG), the developer-facing eDSL, the codegen spine |
| `Metatheory/` | the candidate-independent logic of constructive knowledge + authority (the abstract theory dregg instances) |
| `AssuranceCase.lean`, `Claims.lean`, `Tactics.lean` | the assurance artifact, the CI net, the axiom-hygiene commands |

The navigation docs (`docs/NAVIGATION.md`, `docs/guides/`) carry the fuller where-is-X map.

---

## Honest open items — the named research frontier

The corpus is free of open holes; an open obligation enters as an explicit interface hypothesis,
never a silent gap. Three are worth naming up front so an evaluator can find them rather than
discover them:

- **Userspace-escrow ⊒ kernel-escrow** (`Dregg2/Apps/SealedBidAuction.lean §7`). The headline
  refinement `kernelEscrow ⊑ userspaceEscrow` is a **carried hypothesis**
  (`UserspaceDominatesKernel`), not a proved guarantee. The corollary `escrow_refinement_sound`
  *consumes* it (so the inequality is one line once the refinement is supplied), but the only
  inhabitant proved is the trivial reflexive one. The non-trivial witness — a userspace-escrow
  cell-program with its own release/refund semantics, against an executor that currently lacks a
  block-height/clock dimension — does not yet exist in the green tree. The app ships its proved
  guarantees (no-frontrunning, settle-conserves, settle-cannot-mint, one-shot, loser-refunded)
  green around it; this is the deliberate open call.

- **The prover partition** (`AssuranceCase.lean`, Named boundary seams §1). The Lean-emitted
  descriptor circuit is the default for the graduated turn shapes; every other shape falls back
  — *logged, never silent* — to a hand-written AIR that enforces the same PI bindings and is
  adversarially tested but is not yet Lean-derived. For non-graduated shapes, circuit⟺kernel
  agreement is test-attested, not theorem-attested. The graduation lane closes this by emptying
  the fallback set.

- **Host-side correspondence** (Named boundary seams §2–§3). The verified admission check reads
  values the host supplies (`ShadowHostCtx`: block height, freeze set, receipt-chain head,
  budget); the theorems say *if these are the node's true values then* admission is decided
  correctly. Their fidelity is a host obligation outside the Lean statement — engineering-shaped
  rather than cryptography-shaped, and a host lying to itself harms only admission, never the
  A–C invariants (which hold over whatever state the executor actually runs on). Producer
  coverage (which turn shapes route through the verified executor by default) burns down toward
  total in `lean_shadow.rs`.

Reported here so the case says what it covers. Each has a closure lane; none is a wall.
