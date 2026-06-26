# Rhizomatic ⇄ dregg — the metabolize verdict

`~/dev/rhizomatic` (github.com/mbilokonsky/rhizomatic) is a separate project:
*"a portable format for arbitrarily relational data — composable, forkable,
mergeable, federate-able by default."* Mathematically it is a Merkle-CRDT /
G-Set CvRDT over content-addressed, Ed25519-signed n-ary role-labelled
assertions ("deltas"), with a closed 8-operator read algebra and a decidable
quantifier-free predicate language; arbitrary compute is exiled to a derivation
layer (content-addressed function + keypair, outputs re-enter as signed deltas
— "computation as authorship").

dregg and rhizomatic are the **same machine** at the assertion / CRDT /
predicate-algebra / write-back layer, diverging on **exactly one axis:
conservation** (the full framing is `docs/deos/DISTRIBUTED-TIMETRAVEL-SEMANTICS.md`
§3.8 and the memory `project-rhizomatic-dregg-slotting`). This file records the
*current* upstream state and the per-idea verdict on what dregg should
metabolize — not blindly slot in, but metabolize: only what genuinely fits a
substrate that *carries a conservation law*.

## Upstream now-true state

Since the fragment was last surveyed, upstream grew an application and an upper
tier (the most recent `origin/main` was a history rewrite that mostly preserved
already-present content; the new material is real, not the rewrite):

- **Chorus** (`apps/chorus`) — agent memory built on the substrate. An agent is
  a keypair + a reactor + a policy; every session is a distinct author bound to
  its model by a signed identity claim; concurrent sessions converge by union.
  On top: a briefing that surfaces what the record *disagrees about*, decisions
  replayable byte-for-byte against exactly what was known, retroactive distrust
  of an author / session / model in one signed edit, a librarian that converges
  vocabularies through negatable judgment claims, an MCP server (25 tools), and
  a web console with an as-of scrubber.
- **Persistence tier** — a `Store` interface (append idempotent-by-id, snapshot,
  deltas-since-watermark), a JSONL backend and a SQLite backend passing one
  shared conformance harness, indexed backlinks read, lossless JSONL→SQLite
  migration.
- **GraphQL on demand** — a schema synthesised from a *pinned* snapshot, so the
  memory graph is queryable without a maintained schema (the OLTP/OLAP pin).
- **MX slices (J–Q)** — author mail + disposition artifacts, messages (ephemeral
  salience / permanent record), recast (re-encoded, not re-decided), plurality
  declarations (divergence-as-union), a remote node over streamable HTTP.
- **SPEC-9 alias (proposal, vectored in both witnesses)** — concepts with
  oriented slots + mapping claims + the `aliased` StrMatch closure: accountable,
  deterministic, negatable semantic convergence, with fuzzy similarity exiled to
  a derived author (the librarian).
- **SPEC-11 federation-as-query (note)** — a federation relationship is a *pair
  of queries* (publish ∩ subscribe); a subscription is a continuous query
  (incremental materialisation); privacy is read off as the relevance closure of
  the published query (default-deny); persistence and federation are the same
  deltas-since-watermark shape.

Two witnesses (TypeScript ~211 tests, Rust 50+), 149/149 cross-witness
conformance in-browser (Rust as WASM), cross-implementation HTTP federation
proven to identical canonical digests.

## Per-idea verdict (grounded at dregg HEAD)

| rhizomatic idea | dregg homolog at HEAD | verdict |
|---|---|---|
| **delta** = signed n-ary assertion, grow-only | Evidence substance — the monotone camera (`metatheory/Metatheory/Dynamics/Substance.lean`); the receipt chain **Q** (`metatheory/Dregg2/Exec/Receipt.lean`, `chain_tamper_evident`) | **metabolized + one-bettered.** dregg's Q is a *totally-ordered* prevHash chain (it must order, because it carries Σδ=0); rhizomatic's delta is an order-blind Set (it needn't). The conservation axis, cashed out at the data structure. |
| **merge-is-union** (G-Set CvRDT) | `metatheory/Dregg2/Distributed/LaceMerge.lean` (blocklace keyset join CRDT, axiom-clean) + `metatheory/Dregg2/Confluence.lean` (`IConfluent`, `Tier1Eligible`) | **metabolized + proven.** dregg independently re-proved the same convergence *and* added the I-confluence **gate** deciding which merges are sound coordination-free vs must escalate to consensus. Rhizomatic is this fragment with the escalation path removed. |
| **8-operator read algebra**, decidable Pred | `dregg-query` — conjunctive queries + safe negation (`dregg-query/src/query.rs`), the CALM `classify` (`dregg-query/src/classify.rs`), the non-omission certificate (`dregg-query/src/attested.rs`, MMR range opening) | **metabolized + one-bettered.** dregg-query answers carry a *certificate* that the answer is computed from exactly the committed receipt range — rhizomatic queries don't. The CALM grade (monotone vs finalized-dependent) **is** the per-query I-confluence price. |
| **persistence / Store** (deltas-since-watermark) | Ledger + receipt-index MMR + snapshot/ship; `AttestedSlice` coverage (`dregg-query/src/attested.rs`) | **metabolized + one-bettered.** MMR range-opening is a proof-carrying "deltas since watermark"; rhizomatic's append-idempotent log is the same shape *without* the non-omission proof. |
| **federation = publish ∩ subscribe**; privacy = published-query relevance closure (default-deny, but **irrevocable** grow-only, SPEC-6 §7) | capabilities — default-deny by cap, cryptographic, **revocable at settlement** (`metatheory/Metatheory/SettlementSoundness.lean`); the branch-and-stitch lens is itself a Pred/query; the CALM classifier grades published queries | **dregg already answers stronger.** dregg's privacy perimeter is the *capability*, not a query closure, and dregg's revocation is settlement-live where rhizomatic candidly admits it cannot un-send. The "lens = query, publish ∩ subscribe" framing is convergent and already expressible over dregg-query; it needs no import. |
| **Chorus** = agent memory on the substrate | the umem-as-primitive epoch + the agent-memory revolution (`turn/src/umem.rs`; `deos-hermes/tests/agent_memory_as_umem.rs`) | **convergent evolution, already metabolized independently.** Both projects built agent memory on their own substrate; dregg's is a *witnessed* portable projection (`UProjection`) with per-cell heaps and continuity proofs. |
| **SPEC-9 alias** = accountable, deterministic, negatable **semantic convergence**, fuzzy match exiled to a derived author | dregg's stance matches *exactly* — the camera is blind to caveats; `witnessed(vk)` is the derived author *with a proof attached* (the memory's "derived-author homolog"). dregg identifiers are content-derived (asset = issuer-cell Σδ=0; caps content-addressed; cell ids canonical), so vocabulary **drift mostly vanishes at the identity layer**. | **metabolized + one-bettered (formal gate proven).** The concept-layer `aliased` closure now lives at `metatheory/Dregg2/Confluence/SemanticConvergence.lean`: grow-only `mapping(name,slot,frag,by)` + a one-hop closure that is **monotone-mod-negation** and, in the no-negation fragment, exactly `Confluence.Tier1Eligible` — the *same* gate as a G-Set (`aliasedRaw_tier1`). Content-derived identity **discharges the same-entity case** (`sameEntity_dedup_by_content`), so dregg carries only the same-concept half. The one-better: a `trust`-gated mapping demands `witnessed(vk)` — a proof-carrying judge decidable over `Pred`, which only ever *narrows* aliasing (`trustedReach_subset`). `#assert_axioms`-clean. |

### Headline

The bulk of the new upstream work is **application-layer** (Chorus) or is
something dregg already proves a **stronger** version of: merge → I-confluence-
gated (`Confluence.lean`), read → MMR-attested (`dregg-query`), persistence →
MMR range opening, privacy → capabilities + settlement-live revocation. The
single genuinely-new *idea* worth metabolizing was **accountable semantic
convergence (SPEC-9)** — and dregg metabolized it one-better than the source:
the formal gate is proven (`Dregg2/Confluence/SemanticConvergence.lean`,
`#assert_axioms`-clean), `aliased`-in-the-monotone-fragment *is* `Tier1Eligible`,
and the judge is proof-carrying (decidable over `Pred`, accountable-never-amplifying)
where rhizomatic's is a bare keypair with fuzzy matching exiled to a derived author.

## Why SPEC-9 is the metabolize target, and why content-addressing makes it *small*

Rhizomatic needs the `aliased` closure because two independently-authored
vocabularies drift: `employer`/`employees` vs `job`/`staff` for the same
relation. Its resolution is the principle dregg already lives by: *judgment*
("these two names mean the same thing") is produced above the read boundary by
accountable authors as **signed, negatable claims**; *evaluation* of those
claims is closed, total, byte-deterministic; semantic similarity never
participates in evaluation except through this vocabulary. Fuzzy matching is
given an identity — an embedding-model **derived author**, one model version =
one author = one rankable track record — and its outputs re-enter as ordinary
claims.

dregg's content-derived identity makes **half** of this problem disappear: there
is no *same-entity* drift, because the same asset / cap / cell has the same
content-derived id for everyone. What remains is the *same-concept* half — when
two parties mint human-meaningful **labels or concepts** (the agent-memory /
Chorus territory) and want to converge them accountably. That is exactly, and
only, where SPEC-9 metabolizes into dregg.

## Scope of metabolizing-more (precise)

Per dregg's own discipline (`project-house-capacities`: build capacities **in
the formal setup**, not the Rust periphery; `feedback-be-thoughtful-not-trigger-
happy`: no kernel/effect/VK change from a read-layer idea), metabolizing SPEC-9
means:

1. **Where.** The agent-memory / concept layer (umem working-memory + concept/
   label cells). **Not** dregg-query's closed EDB (`Created/Transfer/Balance/
   Granted/Revoked` — a content-derived schema with no drift). **Not** any
   kernel effect, `sel::*`, or VK column — this is a read-face / concept-layer
   addition.
2. **Shape.** A grow-only `mapping(fragment, slot, by=author)` claim plus an
   `aliased(name, via?, trust?)` closure that (a) walks `name → slots →
   fragments` **one hop, no transitivity** (slots are the hubs that keep the
   judgment space O(n), not O(n²), and prevent wrong-end gluing); (b) is
   computed deterministically over the *surviving* (un-negated) mappings —
   exactly the existing `mask(negation)` semantics; (c) reuses the existing CALM
   classifier verbatim — **monotone** when no negation participates,
   **finalized-dependent** when it does (a negated mapping is "absence not stable
   under append," the classifier's existing single non-monotone reason).
3. **The one-better.** The `trust` predicate may demand `witnessed(vk)` mappings
   — a **proof-carrying judge**, not a bare keypair — and the judge is a dregg
   derived-author leaving a *receipt*, so a mapping's provenance is the same
   audited object as any turn. The closure is decidable inside dregg's
   quantifier-free `Pred`, and the *embedding vectors never enter the substrate*
   (the librarian boundary) — only the judgment persists.
4. **The proof obligation (dregg-currency, before the Rust face).** A small
   `Confluence.lean`-shaped lemma: the `aliased` closure is monotone in the
   mapping set modulo negation (so the monotone fragment is genuinely
   coordination-free), and content-derived identity discharges the same-entity
   case so dregg need only carry the same-concept half.

### The formal half — DONE (`Dregg2/Confluence/SemanticConvergence.lean`)

The proof obligation above is discharged. The module (`#assert_axioms`-clean,
`#eval` non-vacuity, in the default `lake build` target via the root anchor):

- **`Mapping (name, slot, frag, auth, vk, proof)`** + a `Store` of grow-only
  `asserted` / `negated` finsets; `survivors = asserted \ negated` is exactly the
  `mask(negation)` semantics of `dregg-query/src/classify.rs`.
- **`reach` / `aliased`** — the one-hop closure (`name → slot → frag`, no
  transitivity). Decidable by construction (a bounded `Finset` existential):
  convergence is *decided*, never fuzzy.
- **Monotone-mod-negation** — `aliased_mono` (append asserted ⇒ aliasing only
  grows). In the no-negation fragment `aliasedRaw` is `Confluence.IConfluent` and
  hence `Tier1Eligible` (`aliasedRaw_tier1`) — *the same static gate a G-Set
  passes*. The CALM classifier is reused verbatim (`classifyAliased`,
  `classify_sound`); both polarities are witnessed concretely (`append_creates_alias`
  / `negation_retracts` — negation is the single non-monotone reason).
- **Content-derived identity discharges same-entity** — `sameEntity_dedup_by_content`:
  mappings agreeing on the fields and sharing a content id (injective `idOf`) are
  *literally equal*, so a G-Set union already converges them. dregg carries only
  the same-concept half.
- **The one-better — a proof-carrying judge** — a `trust`-gated `witnessed verify m`
  (decidable, `verify` a *parameter* not an `axiom`). `trustedReach_subset` proves
  trust-gating only ever *narrows* aliasing (accountable, never amplifies); it stays
  `Tier1Eligible` (`aliasedTrustedRaw_tier1`); `trust_gate_both_polarities` shows a
  forged judge EXCLUDED and a witnessed one INCLUDED.

Where it lives: the umem/concept layer — **not** dregg-query's closed EDB, **not**
any kernel effect / `sel::*` / VK column. Everything else rhizomatic shipped this
cycle is already metabolized in dregg, frequently with a proof rhizomatic does not
carry; SPEC-9 now joins them, with its own.
