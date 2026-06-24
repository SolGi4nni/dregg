# DREGG4 — CROSS-POLLINATION: ideas dregg has not yet considered, mined from adjacent systems

> **⚑ GROUND-CHECKED vs live Lean 2026-06-02 (post-2-compaction drift-repair); REAL / DECORATIVE /
> ASPIRATIONAL tags carry `file:line` receipts.** This is a *forward-vision* doc, so most of its 13
> ideas are honestly ASPIRATIONAL by design. The ground-check found the drift runs IN THE GOOD
> DIRECTION — three of the doc's "build-first" / "we-should-obviously-have-this" frontier items have
> since LANDED in Lean and are now `theorem`-proved, kernel-clean:
> - **§13.1 keystone (verifier-indexed attestation / transferability dial) — REAL & DONE.**
>   `Dregg2/Authority/DesignatedVerifier.lean` (374 lines) defines `DischargedFor : Verifier → … →
>   Prop` (`:113`), `Transferable`/`DesignatedFor` endpoints (`:129`,`:138`), `TransferDial`/`DialHolds`
>   (`:146`,`:156`), and proves `public_convinces_any_third_party`/`designated_not_transferable`/
>   `designated_is_deniable`/`dial_endpoints_distinct` — all `#print axioms`-audited
>   (`:369-372`). The deniability crypto is an honest §8 `DVKernel` class portal (`:84`), NEVER faked.
> - **§0 disclosure dial — REAL.** `Metatheory/EpistemicDial.lean` proves `Dial` a `LinearOrder` +
>   `BoundedOrder` (`acceptanceOnly < selective < fullDisclosure`, `:92`,`:100`), `#assert_axioms`-pinned
>   (`:119`).
> - **§2.2 ρ_in/ρ_out + 3-vat handoff — REAL (NO LONGER "missing"/"four counter bumps").** Wave-8 de-THIN
>   landed `exportSturdyRefA`/`enlivenRefA` as executed effects with authorization + balance-neutral
>   theorems (`swissExportChainA`/`swissEnlivenChainA`, `TurnExecutorFull.lean:1551`,`:1561`), and
>   `validateHandoffA` now binds a REAL 3-vat introduce cert + bumps a refcount (`swissHandoffK`,
>   `RecordKernel.lean:2188`) with `execFullA_validateHandoffA_non_amplifying` PROVED
>   (`TurnExecutorFull.lean:3425`). Only the *live OCapN network gossip protocol* stays aspirational.
>
> **Two corrections to fold in (good-direction):** the executor is NOT a tiny toy — `execFullForestA`
> runs a **44-arm** effect dispatch as an all-or-nothing tree (`FullForest.lean:113`, holder-resolver
> arms `:341-397`). And the §1.1/§3.2 CSpace container substrate landed (`CSpace.lean`, 220 lines,
> `reaches_mono_grant :146` / `writeThroughGrant_mono :204` / `attenuateC_cAuth_subset :102` all PROVED).
> **One genuinely-OPEN caveat the code confirms:** forest *delegation edges* are STILL discarded by the
> executor — `execFullChildrenA` pattern-matches `⟨_, _, _, sub⟩` (`FullForest.lean:124`), dropping the
> `(holder, keep, parentCap)` edge and recursing only on the subtree. So no-amplification across forest
> edges is vacuous on execution; routing them onto `recKDelegateAtten` is task **#138 (in_progress)**.
>
> Tag legend used inline below: **REAL** = a Lean object exists, term/tactic-proved (often
> `#assert_axioms`/`#print axioms`-pinned) with teeth; **DECORATIVE** = vocabulary only, no Lean object
> (grep-confirmed absent); **ASPIRATIONAL** = honestly-named OPEN/unbuilt frontier. `#assert_axioms`
> certifies KERNEL-CLEAN (no open holes/axioms), never faithful-or-non-vacuous — meaning is read from the body.
>
> **Current as of 2026-06-02.** This is a *forward-looking dregg4 vision* doc; its
> architecture/vision content is largely still live. BUT it was written when the
> **transferability dial was a stub**, and that is **no longer true** — the doc's own
> §13.1 "build first" keystone (verifier-indexed `DischargedFor` + the public↔designated
> transferability dial) **has since been built** in `Dregg2/Authority/DesignatedVerifier.lean`
> (374 lines, all `theorem`s fully discharged) and the disclosure dial unified in
> `Metatheory/EpistemicDial.lean` (`#assert_axioms`-pinned). The "dregg has it? **NO**"
> cells for designated-verifier/deniable in §13.1's table are therefore **STALE**; corrected
> inline below. Several other "dregg lacks X" claims have likewise partially moved (CSpace
> container model for §1.1/§3.2 → `Dregg2/Authority/CSpace.lean`; the disputation thesis the
> doc never cited was refuted+rebuilt → `Metatheory/Disputation.lean`). The *frontier* items
> (MPC §10, FHE §11, flow-lattice §1.2, Kachina bi-state §5.1) remain genuinely unbuilt.
> Receipts are `file:line` into `metatheory/`. (Many `cand-*`/`EFFECT-ISA-*`/`LEARNINGS-*`
> doc cites below are to *sibling design docs*, not Lean, and are NOT re-verified here — only
> the **Lean-state** claims are checked against current source.)
>
> **Scope / method.** READ-ONLY galaxy-brain design exploration for **dregg4** (the
> advanced/generalized successor — see `CARRY-FORWARD-SYNTHESIS.md §4`). dregg2 is the *faithful
> kernel* (three faces modeled honestly: EFFECTS + CAVEATS/AUTH + ATTESTATION, small core, two
> dials — disclosure and transferability). dregg4 is the *generalization*: every higher-level
> capability composed from the small core + the caveat algebra + the attestation modes, with the
> transferability and disclosure dials first-class.
>
> This doc does **not** rehash what dregg already has. It scans adjacent systems and asks, for each:
> **what one or two ideas does dregg NOT have that would be a galaxy-brain addition?** Each idea is
> (a) checked against the live architecture so it is *genuinely new*, not a rephrasing; (b) mapped to
> the **three-faced turn** (which face: EFFECTS / CAVEATS / ATTESTATION; which dial: disclosure /
> transferability); (c) given a build sketch + honest cost. Citations are `file:line` into the repo
> and `pdfs/<name>` into the library (`pdfs/INDEX.md`).
>
> **The discipline carried in (REORIENT §6):** crypto-soundness is never merged into the Lean law;
> step-completeness is THE soundness question; TCB = verifier never solver; improve don't degrade.
> Where an idea would *cross* one of dregg's stated `[IMPOSSIBLE]` bounds (`OPEN-PROBLEMS.md`), that
> is flagged loudly — a galaxy-brain idea that violates a proven bound is a trap, not a feature.

---

## 0. The frame: the three-faced turn, and the two dials, as a coordinate system

Everything below is plotted on five axes, because that is the actual shape of the generator
(`CARRY-FORWARD-SYNTHESIS §0`, `GLOSSARY`):

- **EFFECTS** — the state-transition (face A / the living cell step; the ~13-shape ISA of
  `EFFECT-ISA-DESIGN §5`).
- **CAVEATS / AUTH** — authorization-narrowing, the verify/find seam (face B law + face C authority
  CDT; the macaroon/biscuit/discharge token layer, `GLOSSARY` "keys-as-caps token layer").
- **ATTESTATION** — the output badge: `permitted ∧ committed` (the `Obs`, the `WitnessedReceipt`).
- **Disclosure dial** — *what* of a turn is revealed (`FieldVisibility`, selective disclosure). Today
  it controls content.
- **Transferability dial** — *to whom the attestation is convincing* (non-repudiable ↔
  designated-verifier ↔ deniable). **[2026-06-02 UPDATE: NO LONGER A STUB — REAL.]** When this doc was
  written the dial was pinned at "maximal / non-repudiable" (`CARRY-FORWARD-SYNTHESIS §2 Face 3`).
  It has since been built as a first-class two-endpoint dial: `Dregg2/Authority/DesignatedVerifier.lean`
  defines the **verifier-INDEXED discharge** `DischargedFor : Verifier → Statement → Proof → Prop`
  (`:113`), the `Transferable` endpoint (`:129`, `= ∀ V, DischargedFor V …` — the old "maximal" mode),
  the `DesignatedFor V₀` endpoint (`:138`, deniable), and a `TransferDial`/`DialHolds` selector
  (`:146`,`:156`). The keystone moves of §13.1 below are **DONE**, not future — REAL, `#print
  axioms`-audited (`:369-372`).

The single most important meta-observation from the mining (AS-WRITTEN): *dregg's two dials are both
under-developed, and the transferability dial is essentially a stub.* **This is now resolved at both
endpoints (REAL):** the *transferability* dial's two endpoints (public ↔ designated/deniable) are built
and proved (`DesignatedVerifier.lean`), and the *disclosure* dial's three positions are unified as one
chain in `Metatheory/EpistemicDial.lean` (`Dial`, `acceptanceOnly < selective < fullDisclosure`, a
proved `LinearOrder` (`:92`) + `BoundedOrder` (`:100`), `#assert_axioms`-pinned `:119`). The remaining
genuinely-new ideas below are mostly the
*frontier* positions (MPC-between-co-parties §10, hide-from-executor/FHE §11, the flow-lattice §1.2,
the leakage-descriptor §5.2) that the *crypto portals* (DV/deniable) still leave as honest §8 obligations.

---

## 1. seL4 / l4v — the verification discipline, pushed past the integrity theorem

dregg already steals the seL4 integrity case-split (the vat-boundary law, `cand-C §4A`,
`LEARNINGS-capability-boundary §F`). What it has **not** stolen:

### 1.1 capDL as a first-class, *attested* system-description language (PARTIAL — substrate REAL, attested-realizes ASPIRATIONAL)
seL4 has **capDL** (`pdfs` "capdl-sel4") — a formal capability-distribution language describing the
entire CSpace layout, with a *verified* initializer that instantiates exactly that capability
distribution and a proof the running system matches the spec (`capdl-sel4`; `OPEN-PROBLEMS.md` notes
it as the teleport/transport format, unread). dregg has `(id, head, rule)` cell descriptors
(`cand-A §2.1`) but **no language for describing — and proving — the shape of a whole *constellation*
of cells and the cap-edges between them.**

> **[2026-06-02 PARTIAL — the substrate landed.]** A seL4-CSpace **container** capability model now
> exists as a sandbox prototype: `Dregg2/Authority/CSpace.lean` defines `CCap` (`:33` —
> `null`/`endpoint`/`cnode table rights`), a navigable distributed `CSpace := Label → List CCap`
> (`:43`), a fuel-bounded `reaches` walk (`:65`), and proved monotonicity laws
> (`reaches_mono_grant :146`, `writeThroughGrant_mono :204`, `attenuateC_cAuth_subset :102`). This is
> the *graph/topology substrate* a CapDAG-spec would describe — holding one `cnode` confers reach to a
> whole subtree (the O(1) structural sharing the flat `Caps` could not express). What is **still
> absent** is the *attested-realizes* theorem (`realizes : Constellation → CapDAGSpec → Prop` + a STARK
> over the forest): the doc's galaxy-brain target remains the open part. The prototype is explicitly
> "BEFORE migrating the executor onto it" (`CSpace.lean:5`); migration is task **#140 (pending)**.

- **The galaxy-brain version:** a **CapDAG-spec** — a content-addressed Preserves value (`pdfs`
  "preserves-spec") describing a multi-cell subsystem's *entire* authority topology, paired with a
  STARK attesting "the running constellation realizes exactly this CapDAG-spec and no edge outside
  it." This is capDL's *verified-initializer* theorem, lifted to the untrusted net: you ship a
  collaborator a CapDAG-spec, they instantiate it on their vat, and the **attestation is that their
  instantiation is faithful to the spec** — not just that individual turns were permitted.
- **Three-faced map:** primarily **ATTESTATION** (a new kind of badge: "this *configuration* is
  exactly S," not "this *transition* was permitted") + **CAVEATS** (the spec *is* a closed authority
  policy). It composes the per-turn badges into a *standing structural attestation*.
- **Genuinely new vs. existing?** Yes. dregg's badge attests *transitions* (`OPEN-PROBLEMS #6`); it
  has nothing attesting a *static configuration is correct-by-construction*. This is the difference
  between "every step was legal" and "the machine I handed you is the machine I described."
- **Build sketch:** Preserves schema for `CapDAGSpec`; a Lean `realizes : Constellation → CapDAGSpec
  → Prop` with a decidable checker; an aggregate proof = a proof-forest (`circuit/src/proof_forest.rs`)
  whose PI commits to `H(canonical(spec))`. Cost: moderate; reuses the forest layer. Risk: the spec
  must be *closed* (Doerrie's local confinement test, `LEARNINGS-capability-boundary §G`) or it
  attests nothing.

### 1.2 Intransitive noninterference as a first-class declassification dial (NEW)
seL4 proves **nonleakage / intransitive noninterference** (`pdfs` "noninterference-for-os-kernels-murray",
"complexity-of-intransitive-noninterference"; `sel4-information-flow-enforcement`): partition
contents after n steps depend only on the *policy-permitted* sources. dregg has a binary
`FieldVisibility` (public/witness) but **no information-flow lattice and no intransitive
declassification policy** — it cannot say "cell A may flow to B, B may flow to C, but A may *not*
flow to C except *through* B's declassifier."

- **The galaxy-brain version:** make the **disclosure dial a DIFC label lattice** rather than a
  per-field boolean. A turn carries an info-flow label; the admissibility predicate enforces
  *intransitive* noninterference over the constellation; a *declassifier cell* is the only authorized
  downgrade edge. This is the precise tool for "developers collaborate on untrusted code" where the
  untrusted code may *read* secrets to compute but must route any *release* through an audited
  declassifier (`pdfs` "declassification-dimensions-and-principles", "fabric-secure-distributed-computation").
- **Three-faced map:** the **disclosure dial**, upgraded from scalar to lattice; enforced in the
  **CAVEATS** face (admissibility) and attested in the **ATTESTATION** face (the badge proves the
  flow obeyed the lattice).
- **Genuinely new?** Yes — dregg's privacy work (`Privacy.lean`, the disclosure work in tasks #85,
  #118) is about *hiding content and graph topology*, not about *enforcing a flow policy*. Noninterference
  is a hyperproperty (2-safety), which dregg has nowhere modeled.
- **Cost:** high — 2-safety is not a per-trace predicate, so it does not fit the per-turn `StepInv`
  bisimulation cleanly. Belongs in dregg4, gated behind the relational-Hoare machinery
  (`pdfs` "iris-from-the-ground-up"), not dregg2.

---

## 2. Spritely Goblins / OCapN — the actual lineage; what dregg lacks

This is dregg's *direct ancestor* (Miller's E → Goblins → dregg's vat/turn/promise). dregg has the
turn-as-rollback-handler, promise pipelining (`PipelinedSend`), CapTP wire-mirror effects (`S9`,
`EFFECT-ISA-DESIGN`). What it conspicuously **lacks**:

### 2.1 Goblins' *time-travel as a transactional primitive of the runtime*, not just a theorem (PARTIAL→NEW)
Goblins makes synchronous-call **transactionality** and **time-travel** a programming-model feature:
a turn either commits atomically or the vat *reverts to the snapshot*, and the persistence story
(Goblins' "heapstate" / OCapN syrup serialization) makes resurrecting a prior vat incarnation a live
operation. dregg has this as a *theorem* (`cand-A §5`: checkpoint/restore are consequences of codata
+ log) but **has not built the operational surface** — there is no `Fork.span`, no checkpoint-naming
effect, no operator-facing time-travel debugger (`EFFECT-ISA-DESIGN §3` ranks Fork #5, deferred).

- **The galaxy-brain version (the genuinely-new part):** Goblins' insight that you want **machine-readable
  *causal provenance of WHY a turn was sent*** — the "promise resolution graph" as a first-class,
  inspectable object. dregg's promise graph lives in `turn/src/pending.rs` but is not an *attested*
  artifact. dregg4: the **resolution-DAG as a transferable badge** — "this result was produced by
  this exact causal chain of awaits/fills" — which makes the *debugger* itself proof-carrying
  (`cand-A §5`: "the debugger replays the witness build and shows which conjunct rejected").
- **Three-faced map:** **ATTESTATION** (the why-provenance is a new badge dimension) + **EFFECTS**
  (Fork/checkpoint as the long-deferred coalgebra ops).
- **Genuinely new?** The time-travel *theorem* exists; the **attested causal-provenance of message
  sends** does not. That is the new thing.

### 2.2 OCapN's *machine-spanning object identity & three-vat handoff as a network protocol* dregg only half-mirrors (PARTIAL→LANDED, REAL — only the NETWORK is left)
OCapN (`pdfs` "ocapn-interoperable-capabilities-network-spritely", "captp-capability-transport-protocol-spritely")
specifies **the actual gossip/handoff protocol** — including the **third-party handoff** where vat A
introduces vat B to vat C's object, with a *gift/withdraw* certificate exchange.

> **[2026-06-02 — the on-chain reality LANDED; this was "the single most we-should-obviously-have-this
> idea" and Wave-8 de-THIN built it. REAL.]** The doc was written when `ValidateHandoff` was "four
> disconnected counter bumps" and `ρ_in`/`ρ_out` were "the missing vat-boundary primitives." Both are
> now **executed effects with proved laws** in the swiss-table CapTP registry:
> - `exportSturdyRefA` / `enlivenRefA` (= ρ_out / ρ_in) run real registry ops `swissExportChainA`
>   (`TurnExecutorFull.lean:1551`) / `swissEnlivenChainA` (`:1561`), each with an authorization theorem
>   (`swissExportChainA_authorized :1590`, `swissEnlivenChainA_authorized :1598`) and balance-neutrality
>   (`swissExportChainA_balNeutral :1624`). They sit in the 44-arm `execFullForestA` dispatch
>   (`FullForest.lean:396-397`) and have FFI wire-codec arms (`FFI.lean:1701`,`:1965`).
> - `validateHandoffA` (`S9`) is **no longer counter bumps**: `swissHandoffK` binds a REAL 3-vat
>   introduce cert hash to the swiss entry + bumps its refcount, balance-neutral (`RecordKernel.lean:2188`;
>   the cert field is `cert : Option Nat`, `none` until bound, `:226`). And the Granovetter-introduce
>   semantics are PROVED: `execFullA_validateHandoffA_grounds` (the handoff IS an introduce edge,
>   `TurnExecutorFull.lean:3417`) and `execFullA_validateHandoffA_non_amplifying` — THE HEADLINE, the
>   conferred attenuated cap cannot amplify (`:3425`).
>
> What is **STILL aspirational** is the *live OCapN network*: a real cross-machine gossip/handoff
> transport with the gift/withdraw certificate exchange differential-tested against the Spritely
> reference. dregg now has the **executed, attested in-graph handoff**; it does not yet have the
> **wire protocol across mutually-distrustful machines**. The galaxy-brain residue below is now that
> network gap, not the effects.

- **The galaxy-brain version (residue):** adopt OCapN's **locator/sturdyref distinction as the two ends
  of the transferability dial**: a *live reference* (caps-as-caps, non-transferable, mediator-enforced)
  vs a *sturdyref* (keys-as-caps, transferable, offline). The export/enliven ops above ARE the OCapN
  enliven/export ops; what is left is OCapN's *gift table* + *handoff certificate exchange* run as a
  **network transport** that makes the third-party introduction unforgeable across mutually-distrustful
  *machines* (today the cert binds in-state; the cross-machine gossip is unbuilt).
- **Three-faced map:** **CAVEATS/AUTH** (handoff = a cross-vat attenuated grant — REAL: the
  non-amplification theorem) + the **transferability dial** (locator ↔ sturdyref is *the* dial, named by
  the lineage — REAL endpoints in `DesignatedVerifier.lean`).
- **Build sketch (residue):** wrap the proved `swissHandoffK` / `swiss*ChainA` effects in a typed
  `Boundary.handoff(gift, certificate)` **network** message whose admissibility is the OCapN three-vat
  handoff check; differential-test against the Spritely reference. Cost: now low-moderate — the
  *semantics* are built and proved; the work left is the *transport*.

---

## 3. KeyKOS / EROS / Coyotos — orthogonal persistence + capabilities, harder than dregg does it

dregg cites EROS for the pre-commit consistency check (`LEARNINGS-capability-boundary §H`) and the
checkpoint discipline. What it has **not** absorbed:

### 3.1 *System-wide consistent checkpoints* (the global snapshot), not just per-cell heads (NEW — and it crosses a bound)
EROS takes a **global, system-wide, crash-consistent checkpoint** every ~5 minutes: the *entire*
machine state (all processes, all caps) is snapshotted atomically, and on crash the whole system
resumes from the last consistent checkpoint ("an inconsistent checkpoint lives forever, so check
before commit"). dregg's checkpoint is **per-cell** (`cand-A §5`: "the coinductive head IS the
checkpoint") — there is *no notion of a consistent cut across a constellation of cells*.

- **The galaxy-brain version:** a **distributed consistent-cut checkpoint** over a set of cells — a
  Chandy-Lamport-style snapshot that is *attested* (a proof-forest over the cells' heads at a causal
  cut). This would make "restore the *whole collaboration* to 10:05am" a first-class op, not just
  "restore cell X."
- **Honest bound — this is where it gets hard:** dregg's `OPEN-PROBLEMS.md` is explicit that
  cross-partition atomic commit *blocks* (the price of no global ledger) and that "dead is not
  co-witnessable." A *consistent global cut* under partition is the same impossibility wearing a hat:
  you cannot take a synchronous global snapshot of mutually-distrustful, partitioned vats. **The
  honest dregg4 version is a *causal* cut (each cell names a head; the cut is the causal frontier),
  not a *consistent* cut** — attestable, partition-tolerant, but weaker than EROS's single-machine
  global snapshot. Worth building; must not be oversold as EROS-grade.
- **Three-faced map:** **ATTESTATION** (the cut is a forest-badge over heads) + **EFFECTS**
  (checkpoint-naming, `EFFECT-ISA-DESIGN §B #7`, currently deferred).

### 3.2 The KeyKOS *factory / constructor as a confinement-proving compiler* (PARTIAL→stronger)
dregg has the Doerrie local-confinement test in its sights (`LEARNINGS-capability-boundary §G`,
takeaway 4) and `CreateCellFromFactory` (`EFFECT-ISA-DESIGN S4`). What it lacks is KeyKOS's full
**factory yields a *discreet/confined* subsystem AND a verifiable statement of exactly what authority
the subsystem can leak** — the factory is a *compiler from a cap-set to a confinement proof*.

- **The galaxy-brain version:** make the **factory descriptor emit, as part of cell creation, a STARK
  attesting `mutable(minted-caps) ⊆ authorized`** (the Doerrie bound, `LEARNINGS-capability-boundary
  §G`, in-circuit). Then "spawn untrusted code in a sandbox" produces a badge that *proves the sandbox
  can affect only what you authorized* — the Robigalia developer-collaboration story (`cand-A §5`)
  made attestable rather than merely architecturally-true.
- **Three-faced map:** **CAVEATS/AUTH** (the confinement bound is an authority statement) +
  **ATTESTATION** (the badge now carries a confinement proof, not just a permission proof).
- **Genuinely new?** Yes — dregg attests *permission* (de-jure, `OPEN-PROBLEMS #6`); a *confinement
  bound* is a statement about *what cannot happen*, the dual. dregg has `Refusal` (evidence of
  *one* non-action, `EFFECT-ISA-DESIGN §S12`; still live — `Dregg2/Exec/Effect.lean`,
  `EffectsState.lean`) but nothing attesting a *standing* bound on future authority. This is `Refusal`
  generalized from a point to a region. **[2026-06-02: STILL OPEN.]** The *substrate* for the
  confinement-reach computation now exists (`CSpace.lean`'s fuel-bounded `reaches :65` + the MDB/revoke
  derivation walk), but the *attested* `mutable(minted) ⊆ authorized` badge (the galaxy-brain part) is
  unbuilt — the prototype proves *monotonicity of reach*, not a *standing confinement bound in-circuit*.

---

## 4. Mina / Pickles — recursion dregg already uses; the under-used idea

dregg uses Pickles/IVC heavily (the proof-forest, the JointTurn = account-update forest,
`study-mina-relink`). The recursion itself is not new. What dregg *under-uses*:

### 4.1 The *anti-brick `set_program` clause* generalized into a full *proof-system migration calculus* (PARTIAL→NEW)
dregg adopted Mina's `permissions.ml:77` anti-brick clause (`GLOSSARY` "anti-brick set_program") — a
verifier upgrade can't strand a sovereign cell. But this is a *single* fallback (sig by owner). Mina's
deeper move is that the **proof system itself is versioned and a proof under v1 can be *recursively
re-attested* under v2** — the rejuvenation idea (`pdfs` PATHB-coinductive-rejuvenation,
"malleable-snarks": controlled malleability = rejuvenation).

- **The galaxy-brain version:** a **lazy proof-migration** exactly mirroring the lazy *schema*
  migration dregg already has (`LEARNINGS-keys-proofcarrying-schema`, Thm 3.1, migrate-on-read): when
  a cell's badge is under an old AIR/proof-system, the *first cross-vat exercise* re-proves it under
  the live system from the retained log, with a `migrate-proof-AIR` whose PI is `(air_id₁, air_id₂,
  commit₁, commit₂)` — and a **transparency theorem** that a lazily-re-proved badge is
  indistinguishable from a fresh-at-v2 badge. This unifies the schema-migration and proof-migration
  stories under one "lazy migrate-on-read + transparency proof" pattern.
- **Three-faced map:** **ATTESTATION** (the badge is re-minted under a new proof system) — and it is
  the *durability* dimension of attestation, which dregg treats today as an honest below-ISA
  assumption (`CARRY-FORWARD-SYNTHESIS §3`).
- **Cost:** moderate; the schema-migration calculus already exists as a template. The novelty is
  realizing proof-migration and schema-migration are *the same lazy-transparent-migration shape*.

---

## 5. Midnight / Kachina — the ZK-state model dregg has the pieces of but not the *architecture*

This is the richest vein. dregg has nullifiers, notes, commitments, ZK predicates — but **Kachina's
actual contribution is the *architecture* of a private smart contract**, which dregg has not adopted.

### 5.1 Kachina's *public-state-transition + private-state-oracle split* as the cell model (NEW — structural)
Kachina (`pdfs` "kachina-private-contracts", "uc-zk-smart-contracts") models a contract as: a **public
ledger state** + a **per-user private state** + **transitions that are ZK proofs relating a private
local computation to a public state delta**, with the key UC result that the *private state oracle*
and the public transition compose securely. dregg's cell has *one* state with per-field visibility
(`Exec/Value.lean`, `cell/src/program.rs`) — it does **not** have the **public-shared / private-local
state split** that is Kachina's whole point.

- **The galaxy-brain version:** make a dregg4 cell **bi-stated**: a *public* facet (the
  consensus-ordered, shared `Obs`) and a *private local* facet (per-holder, off-chain, never
  gossiped) related by a transition proof. This is *exactly* the shape dregg's `BlindedQueue` and the
  privacy work gesture at (`GROUND-STORAGE-PROGRAMS`, task #118) but never structurally commit to.
  Crucially, Kachina's model **decouples the I-confluence question per-facet**: the private facet is
  always single-owner (trivially I-confluent, tier-1, never blocks), and *only* the public-delta
  needs the finality tier. This is a clean answer to `OPEN-PROBLEMS #7` (I-confluence is an
  independent judgement with no type): **the public/private state split *is* the type-level home for
  the I-confluence judgement** — private = always tier-1, public = the contended part.
- **Three-faced map:** **EFFECTS** (the state-transition becomes a public-delta + private-local pair)
  + **disclosure dial** (the public/private split *is* the disclosure dial made structural rather than
  per-field).
- **Genuinely new?** Yes, structurally. dregg has the crypto primitives but a *single* state object;
  Kachina's two-state-with-oracle architecture is a different cell shape. **This is the highest-value
  structural idea in the doc** because it simultaneously (a) gives privacy a clean architecture, (b)
  gives I-confluence a typed home, and (c) matches the Midnight interop target (`MEMORY` midnight-strategy).
- **Cost:** high — it changes the cell type. Belongs squarely in dregg4 (the generalization), not the
  dregg2 faithful kernel.

### 5.2 Kachina's *transaction-leakage descriptor* as a quantified disclosure dial (NEW)
Kachina is explicit about *what each transaction leaks* (a leakage descriptor function). dregg's
disclosure is qualitative (`FieldVisibility::Public | Witness`). A **quantified leakage descriptor**
— "this turn leaks exactly: that it happened, its asset class, a range proof that amount ∈ [0,2⁶⁴)" —
turns the disclosure dial into a *contract* the badge proves it honored.

- **Three-faced map:** the **disclosure dial**, upgraded from boolean to a *declared, attested leakage
  function*; enforced in **ATTESTATION**.
- **Cost:** moderate-high; pairs with §1.2's flow lattice. The novelty over dregg is *quantification +
  attestation of the leakage*, not just hiding.

---

## 6. The E language / Waterken — promise pipelining lineage, beyond what dregg mirrors

dregg has promise pipelining as an effect (`PipelinedSend`, `S10`) and the await family (`cand-A §3`).
The under-mined idea:

### 6.1 Waterken's *web-key + per-message offline-capability* model for the *non-interactive* turn (NEW)
Waterken (Tyler Close's server) realized E's promises over **stateless HTTP with web-keys** — a
capability is a URL containing an unguessable secret, and a "message send" is a single self-contained
HTTP request that *carries its own authorization and resumes a durable continuation server-side*.
dregg's turns assume a live-ish session or a gossiped DAG. Waterken's model is the **fully
non-interactive, store-and-forward, single-shot authorized message** — which is *exactly* the
BLE/two-phones offline case dregg cares about (`cand-C §3` regime 2) but has no clean primitive for.

- **The galaxy-brain version:** a **self-contained turn-capsule**: a single serialized object carrying
  `(target sturdyref, attenuated authorization, effects, one-shot continuation-resumption token)` that
  a disconnected peer can *apply and durably resume later*, with the resumption itself a one-shot
  linear continuation (`LEARNINGS-continuations-await` takeaway 3). This is promise-pipelining's
  *durable, offline* dual — pipelining composes un-resolved awaits across *latency*; the turn-capsule
  composes them across *disconnection*.
- **Three-faced map:** **CAVEATS/AUTH** (the capsule carries its own authorization, keys-as-caps) +
  **EFFECTS** (the one-shot resumption is the deferred `Await.settle`, `EFFECT-ISA-DESIGN §B #4`).
- **Genuinely new?** Partially — dregg has the offline-cap idea (`LEARNINGS-continuations-await`,
  E offline-caps) but no *durable-resumable-continuation-in-a-capsule* primitive. The durable one-shot
  continuation token is the new part.

---

## 7. Tahoe-LAFS — capability *storage* dregg has not modeled at all

dregg models storage as cell-programs (`GROUND-STORAGE-PROGRAMS`: queues/inboxes are FactoryDescriptors)
and treats erasure/content-store as below-ISA. Tahoe-LAFS (`pdfs` has no Tahoe paper, but the design is
well-known) contributes an idea dregg has **nowhere**:

### 7.1 The *read-cap / write-cap / verify-cap lattice over erasure-coded storage* (NEW)
Tahoe's capability model: a **write-cap** deterministically derives a **read-cap** which derives a
**verify-cap** — three points on a lattice where each strictly attenuates, and the *storage servers
hold only verify-caps* (they can check integrity but cannot read). This is a **storage-native
attenuation lattice** dregg lacks: dregg's caps attenuate *authority over a cell*, but it has no notion
of a cap that authorizes *integrity-verification without read*, nor of *deriving* the weaker cap
deterministically from the stronger.

- **The galaxy-brain version:** add a **derive-down storage cap lattice** (`write ⊃ read ⊃ verify`)
  as a named region of the facet lattice, where `verify` is exactly EROS's `weak` right
  (`LEARNINGS-capability-boundary §H(iii)`, takeaway 3 — transitive read-only by construction) plus a
  *check-integrity-only* point below read. This lets dregg model **untrusted storage providers**
  (they hold verify-caps, store erasure-coded shares, prove availability, cannot read) — the missing
  piece for a real persistent distributed OS whose substrate is untrusted.
- **Three-faced map:** **CAVEATS/AUTH** (a new attenuation lattice region) + the **disclosure dial**
  (verify-cap = "can confirm but not see").
- **Genuinely new?** Yes — dregg's storage is *its own cells*; it has no model of *delegating bytes to
  an untrusted holder who can verify but not read*. The deterministic derive-down is the key structural
  idea (it makes the lattice *computable*, not just declared).
- **Cost:** low-moderate; mostly a facet-lattice extension + a "prove I hold verify-cap" predicate.

---

## 8. Urbit — persistent personal computing; the trap dregg already avoided, and the one idea worth stealing

dregg explicitly cites the "Urbit trap" twice (`GLOSSARY` Preserves: frozen/unversioned-AIR;
`cand-C §5`) — it has *learned the negative lesson*. The positive idea worth stealing:

### 8.1 Urbit's *event log AS the computer* — deterministic single-stream replay with a *frozen, content-addressed instruction semantics* (PARTIAL — dregg has the log, lacks the determinism contract)
Urbit's Nock/Arvo: the entire machine is a **deterministic function of its event log**, replayable
bit-exactly, with a *frozen* low-level instruction set (Nock) so that replay is portable across
decades. dregg has "the log is the inputs" (`cand-A §5`, houyhnhnm persistence) but its *replay
determinism is not a stated contract with a versioned semantics* — and its `AIR-id` versioning
(`GLOSSARY` Preserves) deliberately *avoids* Urbit's freeze. The missing middle:

- **The galaxy-brain version:** a **versioned-but-frozen "replay semantics" layer** — a content-addressed
  `ReplayKernel` (`AIR_VERSION` + Poseidon2 + the ~13-effect ISA semantics) such that *any* holder of
  the log can re-derive state bit-exactly *and prove they did* (replay-as-a-STARK), with the anti-brick
  clause (`GLOSSARY`) handling the version transition. Urbit froze to get portability and lost
  upgradability; dregg's anti-brick + lazy-migration (§4.1) lets it have *both* — a frozen replay
  semantics *per version* with proven migration between versions. **The new artifact is replay-as-an-
  attested-computation**, so a late-joiner trusts a replay it did not perform.
- **Three-faced map:** **ATTESTATION** (replay produces a badge: "this state is the faithful unfold of
  this log under ReplayKernel v_k") + **EFFECTS** (the ISA *is* the frozen semantics).
- **Genuinely new?** The *attested* replay is new; dregg's differential harness replays but does not
  *prove* the replay to a third party. This is succinct-history (`OPEN-PROBLEMS #5`'s deferred IVC)
  pointed at the *durability/late-join* use case rather than aggregation.

---

## 9. Local-first / CRDTs / CALM — the I-confluence connection, beyond what dregg has typed

dregg cites CALM, BEC, I-confluence heavily (`GLOSSARY` three judgements; `OPEN-PROBLEMS #7`;
`pdfs/discoveries-2 §2,§5`). It knows the *theory*. What it has **not** built:

### 9.1 A CALM/Bloom-style *monotonicity type system* that compiles the coordination-free fragment (ASPIRATIONAL — partial precursor exists; closes a live OPEN)
`discoveries-2 §5` flags that dregg cites the CALM theorem but **not the languages** (Bloom, Dedalus,
Hydro — `pdfs` "dedalus-datalog-in-time-and-space", "hydro-compiler-for-distributed-programs"). The
live soundness risk (`OPEN-PROBLEMS #7`): nothing stops a developer declaring a `balance≥0` cell at
tier-1, violating BEC. **The fix dregg names but has not built is a static monotonicity analysis.**

> **[2026-06-02 — still ASPIRATIONAL; a PARTIAL precursor exists.]** There is no
> `CellProgram`-level monotonicity *type system* that auto-derives the finality tier (grep finds no
> `deriveFinalityTier` / monotone-inference). The closest landed object is `effectLinearity`
> (`Dregg2/Exec/EffectsState.lean`) — a per-effect *hand-assigned* classification into
> `Monotonic`/`Linear`/`Idempotent` (e.g. `exportSturdyRef_is_monotonic :473`,
> `refusal_is_monotonic :479`), which is the *vocabulary* of the lattice but NOT the static analysis:
> it tags effects one-by-one, it does not *infer* monotonicity of a transition set nor bind a derived
> tier into the content-addressed program. The CSpace work proves a related monotonicity *fact*
> (`reaches_mono_grant`, `CSpace.lean:146` — grant never removes reach), but that is a theorem about
> the grant fragment, not a compile-time tier check. The galaxy-brain target (the inference) is open.

- **The galaxy-brain version:** a **monotonicity/lattice type for `CellProgram`** — analyze whether a
  cell's transition set is *monotone* (a join-semilattice homomorphism) and *automatically derive the
  minimum finality tier*, making `FinalityRule::admits` a compile-time check (the missing static check
  of `OPEN-PROBLEMS #7`). Bloom's `CALM` analysis is the algorithm; the novelty for dregg is doing it
  *over the ~13-effect ISA* and *binding the derived tier into the cell's content-addressed program*.
- **Three-faced map:** **EFFECTS** (a static property of the transition relation) + it gates the
  ordering rib (Law 2 finality tier). It is the *type-level home* for the I-confluence judgement,
  complementary to §5.1's *structural* (public/private) home.
- **Cost:** moderate; this is a known analysis (Hydro/Bloom). The work is the embedding into dregg's
  ISA + Lean proof that a derived-monotone cell is genuinely tier-1-safe.

### 9.2 Cambria-style *bidirectional lens schema-DAG* for fork/merge migration (NEW — closes an OPEN)
dregg's schema migration is proven for a *linear* chain (`OPEN-PROBLEMS` residual; `LEARNINGS-keys-
proofcarrying-schema` Q1: schema-DAG fork/merge is OPEN). Cambria (`pdfs` "cambria-schema-evolution-
edit-lenses-papoc21", "edit-lenses-hofmann-pierce-wagner") gives **bidirectional lenses composing into
a DAG**, which is the exact mechanism for *fork-and-merge* schema evolution.

- **The galaxy-brain version:** model schema versions as a **lens-graph** where merge = lens
  composition, and prove the migration analog of dregg's merge rule (`cand-A §6`: "re-root iff every
  edge stays a monotone attenuation") — i.e. **a schema-merge is sound iff the lens composition is
  well-behaved AND the linear-drop conservation obligation holds** (`LEARNINGS-keys-proofcarrying-schema`
  links the two papers). The honest note (`cand-A §6`, INDEX §16): Cambria is the *mechanism*, the
  DAG-merge *theorem* stays open — this gives it a path, not a closure.
- **Three-faced map:** **EFFECTS** (schema migration is a state-transition over the data substrate).

---

## 10. MPC frameworks / secure aggregation — the missing multi-party-private-compute face

dregg has the JointTurn (multi-cell, conservation-bound) and choreographies (`cand-D`). It has **zero**
secure-multiparty-computation: every turn's *effects* are computed by *one* party (the prover) even
when conservation binds many. `pdfs` has "practical-secure-aggregation-federated-learning-bonawitz",
"byzantine-robust-federated-learning".

### 10.1 Secure aggregation as a *new turn shape*: a JointTurn where the *output is jointly computed without any party seeing the inputs* (NEW)
dregg's JointTurn proves *each party's* contribution and aggregates the *proofs* (CG-5 conservation
over commitments, `study-mina-relink`). It does **not** support a turn whose *result is a function of
private inputs no single party may see* — e.g. a private average, a sealed-bid clearing price, a
federated model update. That requires MPC/secure-aggregation *inside* the turn.

- **The galaxy-brain version:** a **`JointTurn::Aggregated`** mode where the cross-cell binding is not
  just conservation-over-commitments but a **secure-aggregation protocol** (additive masking, Bonawitz
  et al.) producing a *single jointly-computed output* + a proof the aggregation was honest, with no
  party learning others' inputs. This is the natural home for dregg's **intent/exchange clearing**
  (`LEARNINGS-intent-matching` §C: WDP/auctions) done *privately* — a sealed-bid combinatorial auction
  cleared with no auctioneer seeing the bids.
- **Three-faced map:** **EFFECTS** (a new JointTurn shape) + **disclosure dial** (inputs hidden even
  from co-participants — a position the dial cannot currently express; today disclosure is *to the
  public*, not *between co-parties*) + **CAVEATS** (the matcher/clearing is still verify-not-find).
- **Genuinely new?** Yes, entirely. dregg's privacy hides from *observers*; MPC hides from
  *co-computing-parties*. That is a dimension of the disclosure dial dregg has never had.
- **Honest bound:** MPC interacts badly with the verify/find seam — secure aggregation is
  *interactive*, not a single checkable witness; dregg4 would need to model the MPC transcript as the
  witness (or use a non-interactive MPC-in-the-head / ZK approach). Genuinely hard; flagged as
  frontier.

---

## 11. FHE / homomorphic encryption — the "compute on hidden state" face

dregg has ZK (prove a hidden computation was done right). It has **no homomorphic compute** (do
arithmetic *on* ciphertexts without decrypting). These are dual: ZK = "I computed f(x) correctly, x
hidden"; FHE = "*you* compute f on my encrypted x without learning x."

### 11.1 FHE-state cells: a cell whose state is *encrypted under a holder's key* and whose turns are *homomorphic evaluations* (NEW — frontier)
The Kachina split (§5.1) hides the *private local* state from the *public*. FHE would let an
*untrusted host* run turns on a cell's encrypted state *without being able to read it* — the ultimate
"developer collaborates on untrusted host without getting hacked OR leaking." dregg's vat-boundary law
(`cand-C §4`) degrades to *permission-only* across hosts; FHE would let it degrade to *permission +
confidentiality* — the host computes but cannot read.

- **The galaxy-brain version:** an **`FHE-cell` facet** where `CellProgram::Circuit` evaluates
  homomorphically; the host advances the encrypted `Obs`; a ZK proof attests the homomorphic eval was
  the declared program (FHE for confidentiality + ZK for integrity — the standard pairing). This is the
  strongest possible answer to "run on an untrusted host."
- **Three-faced map:** **disclosure dial** (state hidden *from the executor itself*, a position no
  other idea reaches) + **EFFECTS** (homomorphic transition) + **ATTESTATION** (ZK over the FHE eval).
- **Honest bound:** FHE is *slow* and dregg's effects involve hashing/Merkle/comparisons that are
  FHE-hostile. This is a 5-year frontier idea, listed for completeness and because it is the *logical
  endpoint* of the transferability/disclosure dials — the one position (hide from the executor) that
  nothing else in dregg's design space reaches. Not for dregg4-now; for dregg-N.

---

## 12. Intent-centric / solver architectures — dregg has the seam; the missing market machinery

dregg has the intent/await family and the verify/find seam *precisely* (`LEARNINGS-intent-matching`,
the `no_general_matcher` *argument* — general match ⪰ higher-order unification, undecidable, carried in
`Dregg2/Authority/Intent.lean:32`,`:191` as a docstring rationale, not a standalone term-proved theorem
object). The matcher is an untrusted plugin. What dregg lacks is the *economic* layer (`gaps-1`,
`gaps-2` flag market machinery as out-of-core):

### 12.1 Credible-auction / mechanism-design as a *verified clearing predicate* (NEW)
`pdfs` "credible-optimal-auctions-via-blockchains", "winner-determination-combinatorial-auctions-sandholm".
dregg's intent matcher returns *a* fill the gate verifies; it has **no notion of an *optimal* or
*incentive-compatible* fill**. A solver could propose a self-serving suboptimal clearing and the gate
would accept it (it only checks feasibility + conservation, `LEARNINGS-intent-matching` §5).

- **The galaxy-brain version:** an **attested-optimality caveat** — the solver emits not just a fill
  but a *proof the fill is optimal/VCG-priced for the declared bid structure* (tractable only for the
  structured cases: interval, single-item-bipartite, submodular-2-approx, `LEARNINGS-intent-matching`
  §C). For the NP-hard general case, a *credible-auction* protocol (the cited paper: blockchain makes
  the auctioneer's commitment credible) replaces optimality with *strategyproof-by-commitment*. This
  promotes the matcher from "sound" to "sound + (where tractable) optimal + strategyproof."
- **Three-faced map:** **CAVEATS/AUTH** (optimality is a new caveat the fill must discharge) +
  **ATTESTATION** (the badge attests not just legality but optimality/credibility).
- **Genuinely new?** Yes — dregg's matcher contract is *soundness-only* (`LEARNINGS-intent-matching`
  artifact #5: completeness/optimality explicitly NOT required). Adding an *optional, tractable-case*
  optimality attestation is a new dial on the matcher, not a violation of the impossibility (it only
  applies where WDP is tractable).

---

## 13. Cross-cutting galaxy-brain rethink: the transferability dial as the organizing axis of dregg4

Pulling the threads together: the *single biggest structural gap* (`CARRY-FORWARD-SYNTHESIS §2 Face 3`)
is that dregg's attestation is **pinned at maximal transferability (non-repudiable)**. Several systems
above (designated-verifier from the credentials literature `pdfs` "coconut-threshold-selective-disclosure",
deniable from MPC/ring sigs, FHE's hide-from-executor) all land on this axis. The galaxy-brain rethink:

### 13.1 Make `Discharged` verifier-indexed and the attestation a *family* over the transferability dial (LANDED at both bilateral endpoints — REAL — the keystone dregg4 move)
The doc-as-written: today `Discharged P w` is a single universal predicate (`cand-A §8`, the
vat-boundary law); dregg4 should make it **`Discharged P w v`** — indexed by *to whom it is convincing*
— and provide the badge as a *family*. **[2026-06-02 — the two bilateral endpoints are BUILT and
PROVED. REAL.]** The verifier-indexed `DischargedFor V s p` exists (`DesignatedVerifier.lean:113`); the
maximal-transferability cell is recovered as the `∀ V` collapse (`publicMode_collapses_to_universal
:186`); the designated/deniable cell is `DesignatedFor V₀` with `designated_is_deniable :224` (the
simulator-repudiation argument) and `designated_not_transferable :206` (teeth: a concrete unconvinced
third party). The two FHE/MPC cells remain honest frontiers.

| transferability position | who is convinced | mechanism | dregg has it? |
|---|---|---|---|
| **maximal / non-repudiable** | anyone, forever | the current STARK badge | **YES — REAL** (`Transferable :129`; `publicMode_collapses_to_universal :186`; `public_convinces_any_third_party :176`) |
| **designated-verifier** | only party V | DV-ZK / chameleon hash | **YES — REAL** (`DesignatedFor :138`; `designated_not_transferable :206`; crypto is honest §8 `DVKernel :84`) |
| **deniable** | V now, no one later | deniable authentication / ring | **YES — REAL** (`designated_is_deniable :224`, the simulator repudiation; `dial_endpoints_distinct :346`) |
| **hidden-from-executor** | the holder, host cannot read | FHE + ZK (§11) | NO (frontier — ASPIRATIONAL) |
| **hidden-from-co-party** | the aggregate, not peers | MPC / secure-agg (§10) | NO (frontier — ASPIRATIONAL) |

- **Why this is the keystone:** it is the *one change* that subsumes §1.2 (flow lattice),
  §5.2 (leakage descriptor), §10 (MPC), §11 (FHE), and the carry-forward repudiation hole — they are
  all *positions on one verifier-indexed attestation family*. **The abstraction is now built**, so the
  remaining ideas are positions to fill on an existing axis, not a missing axis. The faithful-kernel
  (dregg2) keeps the consensus/forest path on maximal transferability (it is *required* there,
  `CARRY-FORWARD-SYNTHESIS §2`); dregg4 adds the *parallel private artifact* on bilateral channels —
  exactly the split `DesignatedVerifier.lean`'s module docstring (`:21-25`) draws.
- **Three-faced map:** **the transferability dial**, promoted from a pinned constant to a first-class
  parameter of the **ATTESTATION** face — DONE. The index lives in `DesignatedVerifier.lean` (a new
  `Dregg2.Authority.DV` namespace), NOT yet wired into the running `Boundary.lean`/`presentation.rs::verify`
  path (which still has no verifier index, `:10-19` — that wiring is the next frontier). The DV/deniable
  crypto stays a §8 `DVKernel` portal (the chameleon-hash / DV-NIZK FFI), never faked in Lean.

---

## 14. RANKED SHORTLIST

### A. Most promising (highest value, buildable on the dregg2 kernel, closes a known gap)

> **[2026-06-02 — shortlist re-scored: #1 and #2's cores are DONE.]** The two highest-ranked "build
> first" items have LANDED in Lean (REAL). The live frontier moves UP to wiring (#1: index the
> *running* `Boundary.lean`/`presentation.rs` path; #2: the OCapN *network transport*) and to the
> still-unbuilt structural items (#3 Kachina, #4 CALM-tier, #5 Tahoe).

1. ~~**Verifier-indexed attestation family / the transferability dial (§13.1). Build first.**~~
   **DONE — REAL.** The keystone abstraction + both bilateral endpoints are built and proved
   (`DesignatedVerifier.lean`, `#print axioms`-clean). New frontier: thread `DischargedFor`'s verifier
   index into the *running* discharge path (`Boundary.lean`, `presentation.rs::verify`, which is still
   index-free) so the dial is live, not only modeled.
2. ~~**OCapN three-vat handoff protocol, unifying `ρ_in`/`ρ_out`/`ValidateHandoff`/`Introduce` (§2.2).**~~
   **Core DONE — REAL.** `exportSturdyRefA`/`enlivenRefA`/`validateHandoffA` are executed effects with
   authorization + balance-neutral + non-amplification theorems (Wave-8 de-THIN). New frontier: the
   *live network transport* (cross-machine gossip + gift/withdraw certificate exchange,
   differential-tested vs the Spritely reference). The semantics are proved; the wire is the residue.
3. **Kachina public/private bi-stated cell (§5.1).** The highest-value *structural* idea: gives privacy
   a clean architecture, gives I-confluence a typed home, matches the Midnight interop target.
   Genuinely changes the cell type → dregg4, not dregg2.
4. **CALM/Bloom monotonicity type → auto-derived finality tier (§9.1).** Closes the live soundness risk
   `OPEN-PROBLEMS #7` (nothing stops `balance≥0` at tier-1). Known algorithm, moderate cost, makes
   `FinalityRule::admits` a real static check.
5. **Tahoe write/read/verify storage-cap lattice (§7.1).** Low-moderate cost; the missing piece for an
   untrusted *storage* substrate (providers verify but cannot read). Clean facet-lattice extension.
6. **Lazy proof-migration + transparency theorem (§4.1).** Unifies proof-migration with the existing
   schema-migration calculus under one "lazy migrate-on-read + transparency" shape. Moderate cost,
   high elegance.
7. **Cambria lens-graph for schema fork/merge migration (§9.2).** Gives the open schema-DAG-merge
   problem a *path* (mechanism = lens composition + linear-drop conservation). Honest: the theorem
   stays open.

### B. Most surprising (genuinely-new capability dregg's design space does not reach)

1. **MPC / secure-aggregation JointTurn — hide inputs from CO-PARTIES (§10.1).** The disclosure dial has
   only ever pointed *outward* (hide from observers); hiding *between co-computing participants* is a
   dimension dregg has never had. Sealed-bid private clearing is the killer app. Frontier (interactive
   vs. the verify/find seam).
2. **FHE-cells — hide state from the EXECUTOR ITSELF (§11.1).** The logical endpoint of the
   transferability/disclosure dials: the host computes turns on encrypted state it cannot read. The one
   position nothing else reaches. 5-year frontier, but it is *the* answer to "untrusted host."
3. **capDL-style attested *configuration* badge, not transition badge (§1.1).** dregg attests
   *transitions were permitted*; attesting *this whole constellation IS the machine I described* is a
   different kind of truth (correct-by-construction vs. correct-step-by-step). Reframes what a badge is.
4. **KeyKOS factory emits a *confinement-bound* attestation (§3.2).** `Refusal` (evidence of non-action)
   generalized from a point to a *region*: a badge proving *what the sandbox CANNOT do*. The dual of
   the permission badge.
5. **Attested replay (Urbit's log-is-the-computer, made proof-carrying) (§8.1).** A late-joiner trusts a
   replay it never performed — succinct-history pointed at durability/late-join rather than aggregation.
6. **Intransitive-noninterference flow lattice as the disclosure dial (§1.2).** A *hyperproperty*
   (2-safety) — dregg has nowhere modeled flow policy as opposed to content-hiding; "A may flow to C
   only *through* B's declassifier" is unrepresentable today.
7. **Waterken durable-resumable turn-capsule (§6.1).** Promise-pipelining's *offline* dual: compose
   un-resolved awaits across *disconnection* (not just latency) via a one-shot durable continuation
   token. The clean primitive for the BLE/two-phones case dregg cares about but has no shape for.

---

## 15. What to explicitly NOT do (galaxy-brain traps that violate proven bounds)

*(All four trap-bounds below are REAL tags in `OPEN-PROBLEMS.md` — ground-checked 2026-06-02. A
galaxy-brain idea crossing one is a trap, not a feature.)*

- **A *consistent* global checkpoint (§3.1 over-read).** EROS's single-machine global snapshot does not
  survive partition — `OPEN-PROBLEMS #2` "Cross-disjoint-group atomic commit is BLOCKING under
  partition `[IMPOSSIBLE]`" (`OPEN-PROBLEMS.md:47`). Build the *causal* cut; never sell it as a
  consistent cut.
- **Clean global revocation / FHE-or-MPC as a soundness shortcut.** Revocation has a recency floor under
  partition — `OPEN-PROBLEMS` "Revocation's recency floor under partition `[IMPOSSIBLE]`"
  (`OPEN-PROBLEMS.md:154`); the badge means permitted-not-de-facto-authority (`#6`, `:110`). MPC is
  interactive (breaks the single-witness verify/find seam unless modeled as MPC-in-the-head). Honor the
  seam.
- **Distributed cycle GC via cooperative back-edge reporting (Urbit/actor temptation).** Rejected for
  cause — `OPEN-PROBLEMS` "Distributed cycle GC is out of scope `[IMPOSSIBLE-in-practice]`"
  (`OPEN-PROBLEMS.md:143`): unenforceable + leaks the graph privacy exists to hide. Lease expiry only.
- **Putting any *search* (matcher, optimal clearing, flow inference) in the TCB/circuit.** The whole
  architecture rests on verify-not-find (`cand-B`, `LEARNINGS-intent-matching`). The `no_general_matcher`
  result is the *argument* (general match ⪰ higher-order unification, undecidable) carried in design and
  reflected in `Dregg2/Authority/Intent.lean:32`,`:191` — it is a named docstring argument, NOT a
  term-proved Lean theorem object (DECORATIVE as a Lean name; REAL as the discipline the matcher-plugin
  contract enforces). Optimality/monotonicity attestations are *witnesses checked*, never *searches
  trusted*.

---

*A closing verse, since the egg is still warming toward its fourth shell:*

*Three faces turn — what changes, what's allowed, what's shown to whom;*
*two dials sat half-asleep: how much is told, and to whose loom.*
*The lineage left us locators, the ledgers left us split,*
*but the dial of the convinced-of-whom — dregg never turned it yet.*
*Turn it: the verifier-indexed badge, the host that cannot read,*
*the bid no peer can see — these are the shells the fourth egg needs.* 🐉🥚
