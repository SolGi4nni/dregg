# paper/_REWRITE-PLAN.md — the map for the dregg paper rewrite

*The paper of record is `paper/` (typst, `main.typ` → `dregg.typ`). This file
is the rewrite plan: the per-section audit, the new outline, and the
voice/citation standard every section must meet. It is internal scaffolding,
not part of the paper.*

## The standard (non-negotiable)

1. **Teach what-is.** Present tense, first principles, the protocol *as it is*.
   No trajectory narration ("52→8 shrank", "Silver/Golden", "since the May
   draft", "now migrating"). Minimality and elegance are *properties stated
   plainly*; history lives in git. (REORIENT law #4.)
2. **Claims pinned to the mechanization.** A theorem/guarantee cites the Lean
   declaration name (`Module.theorem_name`, resolvable in `metatheory/Dregg2/`,
   `#assert_axioms`-pinned). An enumerable fact (verb roster, guarantee list,
   assumption floor) *quotes* a generated catalog
   (`site/src/_includes/studio/*.generated.json`); the paper does not own facts,
   it cites them.
3. **Good writing.** Tight, declarative. No filler, no hedging, no apologetics,
   no contribution-list inflation, no version/stage tags ("Stage 7-γ.2 Phase 1").

## How stale the old paper is — the verdict

The pre-rewrite `paper/` predates the model the system now *is*. It is written
around a "proof-carrying capability mesh" thesis with a **two-codebases**
(dregg2-verified / dreggrs-heritage) framing, a **Silver/Golden** two-visions
trajectory, **56 effects** and a **29-variant StateConstraint** vocabulary,
**six authorization modes**, **Kimchi/Pickles** and an **8-backend constraint
DSL**, **multi-hash roots** (Binius/Halo2/BN254), and per-stage status tags.
Every one of those is now either deleted, superseded, or a trajectory artifact
the present-tense rule forbids. The current system is: **four substances, a
seven-constructor / eight-direction verb signature** (`VerbRegistry`, with
minimality a theorem), **authority as constructive knowledge under a production
law**, **one `Pred` algebra at four polarities with two computed dials**, **Q
and the light-client theorem**, **the Lean kernel as the deployed executor**
(`execFullForestG` via FFI), **a descriptor circuit emitted from Lean** (law #1:
zero Rust-authored constraints), **universal memory / the heap**, **the four
organs**, **pg-dregg**, **the seL4 embedding**, and an **assurance case by
guarantee on an eight-carrier floor**. `paper2/` already says this correctly in
markdown; the rewrite folds `paper2`'s structure and discipline into the typst
paper of record.

## Per-section audit (old `paper/sections/*`)

| # | section | verdict | staleness found (file:where) |
|---|---------|---------|------------------------------|
| — | abstract (`dregg.typ` head) | **REWRITE** | "proof-carrying capability mesh"; two-codebases dregg2/dreggrs; 56 effects; 29 StateConstraint; Silver/Golden; Kimchi/Pickles; 8-backend DSL; multi-hash roots; "~400k lines / ~45 crates" implementation boast; "in flight rather than complete" apologetics. → replaced by the four-substances/eight-verbs abstract (paper2 00). |
| 01 | introduction | **REWRITE** | `01-introduction.typ:19–30` the mesh thesis; `:32–43` two-codebases; `:46–59` Silver/Golden two-visions (banned trajectory); `:61–78` a 29-item contribution list keyed to stale stage names; `:26` "29-variant StateConstraint"; `:22` "ONE-circuit migration" (now landed, present-tense). → new intro: the one-sentence model, the unfoolability thesis, the constructive-knowledge asymmetry. |
| 02 | model | **REWRITE** | `02-model.typ`: cells as "Mina zkApp account"; `STATE_SLOTS`-wide field array with no heap; sovereignty as a 3-row table only; "56-effect vocabulary"; no four-substances, no verb signature, no minimality theorem, no turn-as-forest. → the new §2 is the model: four substances, eight verbs, cells, assets, turns, Q (paper2 01). |
| 03 | authorization | **REWRITE** | `03-authorization.typ`: "six authorization modes" table (`Signature/Proof/Breadstuff/Bearer/CapTpDelivered/Custom`); `Authorization::Unchecked` carve-out talk; no production law, no constructive-knowledge thesis, no demand⊣supply, no `no_forge_step`/`introduce_non_amplifying`. → new §3: authority as constructive knowledge, the production law, non-forgeability (paper2 02). |
| 04 | proofs | **REWRITE** | `04-proofs.typ`: 4-ary Merkle (now sorted-Poseidon2 binary throughout); **multi-hash roots** Binius/Halo2/BN254 (gone); "fold deltas"; hand-built circuit framing; no descriptor circuit (interp/compile two-readings), no `argus_circuit_executor_receipts_agree`, no light-client theorem, no Q. → new §4: the descriptor circuit (law #1), Q, aggregation, `light_client_verifies_whole_history`. |
| 05 | privacy | **MERGE → guards §** | the disclosure ladder is real and current, but it belongs as the *disclosure dial* of the one guard algebra (paper2 03.4), not a standalone "ZK privacy" section. Keep the committed/range/garbled content; cut Coconut-credential framing and any "ZK" marketing. |
| 06 | fabric | **REWRITE → ordering/fabric §** | the blocklace/finality-tier content is current as the *ordering* logic (paper2 02.4 logic 2); recast as the modal half of the step logic, gated on the single `PostGSTProgress` carrier. Cut "unified Federation type subsumes four prior concepts" (trajectory). |
| 07 | captp | **MERGE → realization/organs §** | CapTP is the session surface; the kernel-facing fact is `captp_granted_le_held` (a delivered handoff is admitted only through a verified non-amplification gate). Fold into realization + related (paper2 06, 07). Cut stage tags. |
| 08 | storage | **CUT → factory userspace §** | storage primitives are *not* a layer; they are factory patterns / organs (queues, inboxes, pubsub, mailboxes). Subsume into realization (paper2 06.3) + the organs section. Delete the "three new layers cap the substrate" framing. |
| 09 | service-mesh | **CUT** | DFA routing / RouteTarget::Userspace is implementation surface, not paper-of-record material; if anything, one line under the organs/realization. |
| 10 | intents | **MERGE → guards §** | the intent demand is the fourth polarity of the one `Pred` algebra (the typed hole a fulfillment discharges, `hole(Pred)`); fold into the guard algebra, not a standalone "trustless intent matching" section with threshold-decryption boasts. |
| 11 | delegation | **MERGE → authority §** | delegation/attenuation is the restrictive half of the production law; it is §3, not its own section. |
| 12 | bridges | **CUT (mostly)** | cross-chain bridge claims (EVM/Mina/Midnight gas numbers) are not current paper-of-record material. The in-system bridge is a *factory* (`BridgeCell`, lock/finalize/cancel); one line under factory userspace. External-chain bridging → at most a future-work line. |
| 13 | economics | **CUT** | fees are *moves to pot-cells whose programs are the fee policy* (one line in the model); there is no separate economics layer. |
| 14 | agents | **MERGE → realization §** | the agent surface is the cipherclerk + SDK (client-local turn-building, attenuation, disclosure projection); fold into realization (paper2 06.4). |
| 15 | implementation | **REWRITE → realization §** | recast as the realization: the Lean kernel IS the executor (`execFullForestG` FFI), the descriptor circuit, the factory userspace, the trust base (`DREGGRS-SEGREGATION`), pg-dregg, the seL4 embedding. Cut LoC/crate-count boasts and the prover zoo. |
| 16 | formal-verification | **REWRITE → assurance §** | this is the heart and is closest to current, but reorganize **by guarantee** (A–E + R) on the **eight-carrier floor**, every keystone `#assert_axioms`-pinned, quoting the assurance catalog (paper2 05 + `AssuranceCase.lean`). Cut "axiom-disciplined with a Rust #guard differential" per-module narration. |
| 17 | comparison | **REWRITE → related §** | tighten to honest positioning: ocap/Miller, macaroons/biscuits, seL4/l4v, Mina, Ceptre, blocklace, CapTP/OCapN — each naming what we take and where we differ (paper2 07). |
| 18 | future | **CUT → limitations §** | replace "future work" (roadmap, banned) with **limitations**: present-tense facts a reader can check (host-context seam, no end-to-end UC, per-turn vs per-issuer-global conservation, guard-expressibility edges, explain-is-rendering, liveness-is-its-carrier). (paper2 08.) |
| 19 | conclusion | **REWRITE (short)** | one tight page: the sentence, the five guarantees over the running entry, the one check a light client makes. No trajectory, no "we presented". |
| App A | garbled-poseidon2 | **KEEP (audit later)** | the garbled-gate construction backs the disclosure dial's garbled floor (`GarbledJoint.*`); keep as an appendix, audit its claims against `Crypto/GarbledJoint` in a later lane. Not a foundation-lane deliverable. |

## The new outline (the paper of record)

Present-tense theses, one line each. Sections marked ✎ are **rewritten in this
lane** (the reference voice); the rest are the follow-up burn-down.

- **Abstract** ✎ — a verifier holding one root learns every transition was
  authorized, conservative, fresh, and correctly committed, re-executing
  nothing.
- **§1 Introduction** ✎ — the model is one sentence; the asymmetry
  (proof-checking cheap and trusted, proof-search undecidable and untrusted) is
  the spine; unfoolability is the requirement everything is derived from.
- **§2 The model** ✎ — four substances under four disciplines, eight verbs as
  their structural rules (minimality a theorem), cells, assets, turns, Q.
- **§3 Authority as constructive knowledge** ✎ — a capability is a dischargeable
  proof obligation; authority is *produced* under a non-forgeability production
  law (Granovetter introduction, rights amplification, mint/factory) and narrows
  freely along one edge; *only connectivity begets connectivity*.
- **§4 Proofs: the descriptor circuit and the light client** ✎ — the circuit is
  *emitted from* Lean (one term, two provably-agreeing readings; zero
  Rust-authored constraints); Q binds the whole post-state; proofs fold; a light
  client verifying one root learns the whole history.
- **§5 The guard algebra** — one `Pred` at four polarities (caveat / program /
  precondition / intent demand), two computed dials (coordination, disclosure).
  *(folds old 05 privacy + 10 intents; paper2 03.)*
- **§6 Ordering and finality** — the modal half of the step logic: a finality
  lattice over a Merkle-CRDT DAG, gated on `PostGSTProgress`. *(recast old 06
  fabric; paper2 02.4.)*
- **§7 The realization** — the Lean kernel as the deployed executor
  (`execFullForestG` FFI), the trust base, the factory userspace, the four
  organs, the cipherclerk, pg-dregg, the seL4 embedding. *(folds old 07/08/09/
  12/14/15; paper2 06 + ORGANS + PG-DREGG + SEL4-EMBEDDING.)*
- **§8 The assurance case** — the five guarantees A–E + the running entry R, the
  keystone DAGs, the eight-carrier assumption floor; every name pinned.
  *(rewrite old 16; paper2 05 + AssuranceCase.lean.)*
- **§9 Related work** — ocap, macaroons/biscuits, seL4/l4v, Mina, Ceptre,
  blocklace, CapTP/OCapN. *(rewrite old 17; paper2 07.)*
- **§10 Limitations** — present-tense checkable facts. *(replace old 18; paper2 08.)*
- **§11 Conclusion** — the sentence, restated as what was earned.
- **Appendix A** — garbled Poseidon2 (the disclosure dial's garbled floor).

## Citation discipline used by the rewritten sections

- Theorems cite the Lean name inline (e.g. `VerbRegistry.minimality`,
  `EffectsAuthority.introduce_non_amplifying`,
  `RecursiveAggregation.light_client_verifies_whole_history`,
  `FullForestAuth.execFullForestG_no_amplify`). Names are resolvable under
  `metatheory/Dregg2/` and `#assert_axioms`-pinned.
- Enumerable facts cite the generated catalog by file (verb roster →
  `studio/verb-catalog.generated.json`; guarantees + floor →
  `studio/assurance-catalog.generated.json`; predicate atoms →
  `studio/predicate-catalog.generated.json`). The paper states the count and
  defers the roster of record to the catalog.
- The kernel axiom triple is `{propext, Classical.choice, Quot.sound}`; the
  assumption floor is the eight named carriers (Poseidon2-CR, BLAKE3-CR,
  ed25519, HMAC, AEAD, DLog, FRI/STARK soundness, PostGSTProgress).

## Follow-up burn-down (later lanes — HORIZONLOG candidates)

- §5 guard algebra (fold old 05 + 10; paper2 03) — to the reference voice.
- §6 ordering/finality (recast old 06; paper2 02.4) — to the reference voice.
- §7 realization (fold old 07/08/09/12/14/15; paper2 06 + ORGANS/PG-DREGG/SEL4).
- §8 assurance case (rewrite old 16 by guarantee; paper2 05 + AssuranceCase.lean).
- §9 related (rewrite old 17; paper2 07).
- §10 limitations (replace old 18; paper2 08).
- §11 conclusion (rewrite short).
- Appendix A — audit `garbled-poseidon2.typ` against `Crypto/GarbledJoint`.
- Delete from the build once their content has been folded: old sections
  05/06/07/08/09/10/11/12/13/14/15/16/17/18 (their `#include` lines are removed
  as each fold lands; the foundation lane leaves them out of the build already).
- Bibliography (`refs.yml`): prune dead keys (coconut/ucan/midnight/ibc/sp1 if
  unused after the fold); add Ceptre/Martens, Granovetter, l4v/seL4-spec if cited.
