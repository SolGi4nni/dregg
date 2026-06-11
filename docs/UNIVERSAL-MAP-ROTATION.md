# THE UNIVERSAL-MAP ROTATION — the one VK epoch, the master spec

*(design/synthesis, 2026-06-11. This consolidates what the session PROVED into
the single actionable spec for the next layout rotation. Supersedes the
sequencing notes scattered across `docs/EPOCH-DESIGN.md` §"What rides",
`REORIENT.md` §"EPOCH STATUS", and `docs/CONVERGENT-CIRCUIT.md` §5 where they
overlap — each remains authoritative for its own technical content and is
cited below. DESIGN doc: the rotation builder follows this; no code rides this
document.)*

## §1 — What the rotation IS

One VK/commitment epoch that carries, together, (a) the already-deferred
flag-day items (`REORIENT.md:72-77`: registers 8→16, RESERVED removal,
descriptor regen, VK bump, PI v3, heap_root) and (b) the structural upgrades
this session proved sound (universal memory, the convergent 3-verb circuit,
the MMR receipt-index limb). They are designed as one bump because each item
alone forces a VK/commitment version change, and the proven results now tell
us what the FINAL layout shape is — so we rotate once, into that shape.

**The design goal that makes it the LAST layout rotation:** after this epoch,
a future state component is a **new collection id in the one memory domain
space, never a new column** (`docs/EPOCH-DESIGN.md:53-55`,
`docs/UNIVERSAL-MEMORY.md:27-29` — `Domain × κ` is the address space;
extending state = a new `Domain` value). The commitment layout
(`EPOCH-DESIGN.md:50-57`) places the map roots adjacent and uniform precisely
so this holds. Subsequent evolution (new effects, new collections, new guard
atoms) is data: a new guard list + a `decide` lemma on the circuit side
(`docs/CONVERGENT-CIRCUIT.md:184-186`), a new domain value on the state side.
VK changes after this rotation should come only from proof-system-level
choices (FRI config, recursion), not from state layout.

Two standing refusals carry over unchanged (`EPOCH-DESIGN.md:16-20`): edges
stay hash-based and post-quantum (Poseidon2-BabyBear, the one CR floor
actually discharged), and all tables/relations are emitted from Lean — Rust
interprets, authoring no constraints (`circuit/src/descriptor_ir2.rs:53-58`).

## §2 — The bundle, sequenced

Status legend: **DONE** (landed, committed) · **PROVEN, needs impl** (the
Lean theorem exists; the circuit/executor realization does not) ·
**DESIGNED** (spec'd, no proof or code) · **OPEN** (a named decision or
unfixed measurement).

### 2.1 Registers 8→16 + FactoryDescriptor named fields

- **WHY:** the register file is the one state structure that is correctly NOT
  a map — direct limbs in the commitment (`EPOCH-DESIGN.md:34-36`). 8 is
  cramped; the rotation is the only time widening is free.
- **WHAT:** 16 named registers; `FactoryDescriptor` gains the `fields` name
  declaration, compilation resolves indices (`EPOCH-DESIGN.md:34-36`,
  `REORIENT.md:73`).
- **STATUS: DESIGNED** (deferred flag-day item; mechanical).

### 2.2 The universal-memory restructure (5 tables → main + chip + range + ONE memory)

- **WHY — proven this session.** The four map roots (cap, nullifier, heap,
  index) are **derived boundary views** over one Blum multiset:
  - `universal_memory_sound` (`metatheory/Dregg2/Crypto/UniversalMemory.lean:197`)
    — ONE LogUp/grand-product balance over `(domain, key)` addresses implies
    every domain's projection is a consistent standalone memory, with zero
    intra-proof hashing. Workhorses: `consistentFrom_filter` (:118),
    `consistentFrom_strip` (:154). The domain tag is load-bearing, witnessed
    both polarities (cross-domain tuple-steal refused; flat untagged space
    genuinely aliases — `docs/UNIVERSAL-MEMORY.md:52-57`).
  - `memcheck_pins_final` (:281) via `chains_pin_fold` (:231) — the prover's
    claimed final column is FORCED to the genuine fold; the boundary view is
    derived from a forced column, not a chosen one.
  - `boundary_root_derived` (:416) + `boundary_root_from_memcheck` (:429) —
    the committed map root EQUALS the root derived from the final memory
    cells, by canonicity (`Substrate/Heap.lean` `ext_get` :271,
    `root_deterministic` :425), no crypto hypothesis. Materializing roots at
    the boundary is **a refactor, not a semantic change**
    (`docs/UNIVERSAL-MEMORY.md:79-83`).
  - **THE NULLIFIER WIN** — `nullifier_fresh_sound` (:526) under
    `InsertOnlyAt` (:480): intra-proof freshness is ONE memory-read row
    returning `none` — **no Merkle path, no gap opening, no hashing
    intra-proof**. Cross-proof persistence: `nullifier_fresh_binds_root`
    (:544) composes with `Heap.root_injective` (:421). The sorted-tree gap
    machinery (`Crypto/NonMembership.lean` `sorted_gap_excludes`) survives
    exactly at the boundary — once per touched address per proof, never per
    access (`docs/UNIVERSAL-MEMORY.md:84-103`).
- **WHY conservation stays OUT — also proven.** The memory argument is
  per-address (rectangular). `Calculus/BiorthTensor.lean`
  `conservation_not_behaviour_rectangular` (generic mix law
  `rect_mix_in_biorth`): Σδ=0 is NOT expressible by any per-component test
  family; it needs the correlated pair
  (`linearity_recovered_from_orthogonality`,
  `metatheory/docs/TRANSCENDENTAL-SYNTAX-BRIDGE.md:64-82`). Conservation
  stays an **in-row paired-write constraint on the move row** — by theorem,
  not taste (`docs/UNIVERSAL-MEMORY.md:107-112`). Any future proposal to
  "absorb conservation into the multiset" is refuted in advance.
- **WHAT:** the EPOCH's five tables (`EPOCH-DESIGN.md:22-31`) collapse to
  main + poseidon2 chip + range + ONE memory table, with the map-ops table's
  role narrowed to boundary reconciliation of the derived roots
  (`docs/UNIVERSAL-MEMORY.md:13-18`). The chip and range tables are untouched
  (lookup relations, not state accesses — `UNIVERSAL-MEMORY.md:113-115`).
- **The named adapters this needs (the honest obstruction list,
  `UNIVERSAL-MEMORY.md:123-149`):**
  1. the **cap-leaf value-codec adapter** — today's live cap leaf is
     `hash[holder, target, rights, op]`
     (`EffectVmEmitCapRoot.siteCapEdgeLeaf`), not the generic
     `hash[addr, value]` (`Heap.leafOf`, `Substrate/Heap.lean:362`); encode
     the cap tuple as the cell value — a value-codec lemma, no new
     combinatorics (`UNIVERSAL-MEMORY.md:138-144`);
  2. the **MMR boundary-derivation analogue** — the index domain's boundary
     commitment is the MMR root (`Lightclient/MMR.lean` `mroot_injective`
     :313), not a sorted-map root; the `boundary_root_derived` analogue is
     stated, not proved — an adapter lemma, not a soundness gap
     (`UNIVERSAL-MEMORY.md:115-121`);
  3. the **touched-only coverage regime** — `boundary_root_derived` assumes
     declared addresses cover the live cells; the per-key map-op update path
     (today's sorted-insert gates) is the production regime, with the
     derivation theorem as the semantic anchor that both regimes commit to
     the same object (`UNIVERSAL-MEMORY.md:132-137`);
  4. the **`absent` map-op realization** — declared in the IR, refused by
     assembly today (`descriptor_ir2.rs:62-68`); needed by the
     nullifier-insert lane regardless of this design.
- **STATUS: PROVEN, needs impl** (Lean keystones all landed, axiom-clean
  with crypto only as the named `Poseidon2SpongeCR` hypothesis —
  `UNIVERSAL-MEMORY.md:153-160`; circuit emission + interpreter assembly +
  the four adapters do not exist).

### 2.3 The convergent 3-verb circuit + guard-atom lookups

- **WHY — the session's verdict (`docs/CONVERGENT-CIRCUIT.md` §0, §5).**
  IR-v2's endpoint and the verb-ISA endpoint are the same circuit;
  finishing the convergence collapses the per-effect Lean trusted surface
  **≈26 bespoke soundness chains (~50 emit modules) → 3 verb-shape theorems
  + ~28 one-time per-atom realization theorems + 26 `decide`-class
  correspondence lemmas** (`CONVERGENT-CIRCUIT.md:157-172, 226-235`). The
  semantics side is proved: `compressed_kernel_three`
  (`Substrate/VerbCompression.lean:998`) — three verbs (create · gwrite ·
  move) with the strict 4-strata guard algebra; the two separations the
  circuit must keep are theorems (`gwrite_conservation_trivializes` :773,
  `move_not_single_write` :876, `create_birth_not_single_write` :916 — move
  and create stay distinct row shapes forever). The two landed exemplars
  (`setFieldDynVmDescriptor2`, `attenuateVmDescriptor2` —
  `CONVERGENT-CIRCUIT.md:139-151`) demonstrate the shape works.
- **WHAT:** main table 3 row shapes instead of 29 selectors; a `guardAtom`
  IR constraint kind whose elaboration onto the EXISTING tables is proven
  once per atom (order⇒range table, heap⇒map/memory, hash⇒chip, submask⇒
  per-bit decomposition — `CONVERGENT-CIRCUIT.md:118-137`); descriptors
  become `(verb, guard-atom list, PI-binding map)` data. Honest non-claims,
  stated once so nobody re-sells them: Rust AIRs 6→6, proof size neutral,
  prover neutral (`CONVERGENT-CIRCUIT.md:188-201`); epistemic atoms are
  reserved vocabulary, not realized (`:213-216`).
- **THE NAMED DEPENDENCY: the 3-verb executor.** A 3-verb circuit proving
  against a 50-effect executor has nothing to AGREE with — the differential
  gauntlets anchor on the executor's shape. The executor-state bridge
  (interpreting `RecordKernelState` into the one map) "rides THE ONE
  ROTATION" (`Substrate/VerbCompression.lean:87-89`,
  `CONVERGENT-CIRCUIT.md:217-224`). This is the rotation's real cost center,
  and it is an executor cost, not a circuit cost.
- **STATUS: DESIGNED** (semantics proven in `VerbCompression.lean`; the IR
  grammar extension, the ~28 atom theorems, the 3 verb-shape theorems, the
  descriptor regeneration into verb form, and above all the executor
  rotation, do not exist).

### 2.4 heap_root register + the iroot MMR limb

- **WHY:** whole-history non-omission. `server_cannot_omit`
  (`Lightclient/AttestedQuery.lean:358`) gives the root-face guarantee;
  `CommitBindsIndex` (`AttestedQuery.lean:382`) NAMES the rotation
  obligation — `recStateCommit` must absorb `iroot` as a sponge limb;
  `CommitBindsMMR` (`Lightclient/MMR.lean`, summarized `Dregg2.lean:498`) is
  the same obligation with `iroot := mroot`, and `mroot_injective`
  (`MMR.lean:313`) makes the root bind the whole log (tamper / truncate /
  extend / reorder all move it). Heap state entered `RecordKernelState` this
  session (`REORIENT.md:109-110`) and needs its commitment limb.
- **WHAT:** the commitment layout of `EPOCH-DESIGN.md:50-57` — map limbs
  adjacent and uniform (cap_root, nullifier_root, heap_root), receipt-index
  root last. Under §2.2 these limbs are *derived* boundary views, but they
  remain materialized in the commitment — derivation changes where they are
  computed, never what they commit to. The **derivability invariant**
  (`EPOCH-DESIGN.md:58-66`) is stated as part of the assurance case: every
  global root derivable from the receipt record alone.
- **STATUS: PROVEN, needs impl** (the Lean obligations are named and the MMR
  theory is landed; the commitment layout change is flag-day work).

### 2.5 RESERVED removal + column compaction

- **WHY/WHAT:** RESERVED dies; the frozen 54-wide selector block
  (`circuit/src/effect_vm/columns.rs:40-42`) dies into the verb tag (§2.3);
  the old 186→159 target is **obsolete** — the post-LogUp main table is far
  thinner (~40-60 cols, `EPOCH-DESIGN.md:26, 78-79`), and the measured truth
  is that column compaction was never the lever anyway (27 cols ≈ 7 KiB ≈
  1.6% — `docs/PROOF-ECONOMICS.md:78-85`). **The table count and per-table
  width are now the lever, not the base-column count.** This item is mostly
  *dissolved* by §2.2/§2.3 rather than executed as its own change.
- **STATUS: DESIGNED** (subsumed; no independent work beyond the regen).

### 2.6 PI v3

- **WHY/WHAT:** committed-height column closes the temporal gate's
  prover-chosen-height note; rateBound + challengeWindow caveat tags;
  selector binding carried into the verb-tag world
  (`EPOCH-DESIGN.md:83-85`, `REORIENT.md:75-76`). The challengeWindow tag is
  also what the optimistic proving mode reads (task #169 description) —
  the tag ships now, the mode ships later.
- **STATUS: DESIGNED** (flag-day item; mechanical once the layout is fixed).

### 2.7 The blowup-degree lever (task #174)

- **WHY:** Poseidon2's degree-7 S-box forces `log_blowup ≥ 3`; blowup
  multiplies the whole LDE/commit/opening. Expressing Poseidon2 at degree ≤4
  in the SHARED chip table (more rows per permutation — cheap, proved once)
  drops global blowup to 2, ~halving the dominant cost of EVERY committed
  matrix (task #174). The chip lever itself is measured to WORK: 8 chip rows
  versus 1,408 inline aux columns for transfer
  (`docs/PROOF-ECONOMICS.md:105-109`).
- **WHAT:** low-degree chip AIR + `create_config` log_blowup 3→2; keep the
  CR floor discharged against whatever Poseidon2 AIR the chip uses (task
  #174; task #175 item 1 — confirm the chip reuses the audited
  p3-poseidon2-air, swap if hand-rolled). Changes proof shape ⇒ rides this
  rotation naturally (the rotation changes proof shape anyway).
- **STATUS: OPEN** (designed direction, unmeasured; explicitly gated "after
  the IR-v2 size-fix lands" — task #174).

### 2.8 Signed wells / genesis-as-moves / fees-as-moves

- **STATUS: DONE** (`ac01f9b7b`, `REORIENT.md:66-70`): i64 two-limb signed
  balance value model + genesis-as-issuer-moves + fees-as-moves + full
  consumer sweep; guarantee B holds over the deployed chain; the
  AssuranceCase deployment-correspondence legs CLOSED. Nothing rides the
  rotation here — noted so nobody re-schedules it. (The range table gives
  signed wells their two-limb discipline in-circuit —
  `EPOCH-DESIGN.md:28`.)

### 2.9 Cap-crown phase B (in-circuit granted ⊆ held), riding along

- **STATUS: PROVEN, needs impl** — `attenuateV2_non_amp`
  (`metatheory/Dregg2/Circuit/Emit/EffectVmEmitV2.lean:754-779`, committed
  `6f23f5467`): held-cap membership against the before cap_root + genuine
  sorted MapOp write + bitwise-submask lookup. The math of #103's circuit
  leg is DISCHARGED; live wiring rides this flag-day (task #103 metadata —
  do NOT claim live in-circuit non-amp closed until the flag-day lands).
  Under §2.2 the membership check becomes a memory read + boundary
  reconciliation; the submask lookup is unchanged.

### 2.10 The closing ceremony

- **WHAT:** ONE descriptor regeneration (EmitAllJson currently still emits
  v1; the 26 v2 descriptors live in `EffectVmEmitV2.v2Registry` —
  `REORIENT.md:74-75`, `EffectVmEmitV2.lean` `#guard v2Registry.length == 26`)
  → ONE VK/commitment bump → the succession drill → the persvati workspace
  gauntlet (`REORIENT.md:77`, `EPOCH-DESIGN.md:100-108`). Graduation
  completes here: `CutoverFallback` and the legacy AIR path die
  (`EPOCH-DESIGN.md:73-75`).
- **STATUS: DESIGNED** (the machinery exists; it fires exactly once, last).

## §3 — The dependency graph and ordering

```
GATE 0 (hard, BEFORE anything earns the bump):
  IR-v2 size regression GREEN
  (docs/PROOF-ECONOMICS.md §2b: measured 7.3x LARGER / 3.8x slower prove /
   8.7x slower verify than v1. Fix direction in-flight in circuit/src/
   descriptor_ir2.rs: empty-table elision landed (:45-51) + MAP_WIDTH
   12,007 → 71 via the chip bus (:902). GREEN = circuit/tests/
   effect_vm_ir2_size_measure.rs re-measured at-or-under the v1 350.5 KiB
   baseline, on the path to the predicted ~100-200 KiB.)
        │
        ├──► #174 low-degree chip (blowup 3→2) ──┐   [#175 item 1: confirm
        │      (explicitly sequenced after the    │    p3-poseidon2-air,
        │       size fix; measure the delta)      │    same moment]
        │                                         │
        ├──► LEAN ADAPTERS (parallel, pure Lean, no VK risk):
        │      a. cap-leaf value-codec lemma   (UNIVERSAL-MEMORY.md:138-144)
        │      b. MMR boundary-derivation lemma (UNIVERSAL-MEMORY.md:115-121)
        │      c. guardAtom IR kind + 3 verb templates
        │         + ~28 atom-realization theorems (CONVERGENT-CIRCUIT.md §5.3)
        │                                         │
        ├──► 3-VERB EXECUTOR (the long pole):     │
        │      RecordKernelState → the ONE universal map
        │      (VerbCompression.lean:87-89 — "rides THE ONE ROTATION")
        │           │                             │
        │           ▼                             │
        │    3-verb circuit descriptors           │
        │    (gated on the executor — never before it:
        │     circuit semantics must not run ahead of runtime semantics)
        │           │                             │
        ├──► `absent` map-op realization (descriptor_ir2.rs:62-68;
        │     needed by the nullifier lane regardless)
        │           │                             │
        ▼           ▼                             ▼
  LAYOUT FLAG-DAY (one motion): registers 8→16 + FactoryDescriptor.fields ·
  heap_root + iroot limbs (CommitBindsIndex/CommitBindsMMR) · PI v3 ·
  RESERVED/selector-block death · universal-memory table assembly
        │
        ▼
  ONE descriptor regen → differential gauntlets (cell≡circuit per map ·
  per-effect AGREE · the memory-argument adversarial suite: a tampered
  read must refuse — EPOCH-DESIGN.md:105-107) → VK/commitment bump →
  succession drill → persvati gauntlet → deploy when ember says deploy
```

Ordering notes:

- **Nothing before GATE 0.** A 7.3x-larger proof must not be what the VK
  bump ships; v1 stays the only prover on the wire until the measurement is
  green (`PROOF-ECONOMICS.md:130-132` — no opt-in flag exists, on purpose).
- **The Lean adapters and the executor rotation can run in parallel** (the
  adapters are pure Lean; the executor work is `turn/`+`cell/` shaped). The
  3-verb circuit waits for the executor; the universal-memory tables wait
  for adapters a+b and the `absent` realization.
- **#174 is detachable.** If the low-degree chip slips, the rotation ships
  at lb=3 and #174 becomes a config-only change later — it does NOT touch
  state layout, so it does not violate the last-rotation property. Riding
  together is preferred (one gauntlet), not required.
- **Two descriptors should converge early** as proofs-of-shape, before the
  flag-day, on the existing IR (the `setFieldDyn`/`attenuate` pattern —
  `CONVERGENT-CIRCUIT.md:327-331`): the template machinery grows by use,
  not big-bang.

## §4 — NOT in this rotation (honest scope)

- **Per-turn / per-block proving amortization + the proving-modality dial**
  (#169, #175 item 2): policy + witness-retention work in
  `node/src/prove_pool.rs`; no circuit change; separate lane.
- **Recursion config work** (the in-circuit verifier, aggregation
  manifests): the chip-table substrate is the right one and is already
  landed; the verb reshape contributes nothing additional
  (`CONVERGENT-CIRCUIT.md` §4). The fork follow-ups on the ROOT
  (child-circuit identity pinning, public-value propagation —
  `PROOF-ECONOMICS.md:159-163`) stay their own lane.
- **The organ welds** (`docs/ORGANS.md`): post-rotation.
- **The self-certifying-receipt horizon** (per-strand recursive
  attestation): explicitly deferred; the derivability invariant is the whole
  cost of keeping that door open (`EPOCH-DESIGN.md:62-66`).
- **Epistemic guard atoms in-circuit**: design-stage
  (`Authority/Epistemic.lean`); the descriptor language reserves the
  modality, nothing more (`CONVERGENT-CIRCUIT.md:213-216`).
- **The transcendental-syntax program S1-S5**
  (`metatheory/docs/TRANSCENDENTAL-SYNTAX-BRIDGE.md:138-159`): foundational
  research; its one load-bearing contribution to THIS rotation is already
  banked (conservation stays in-row, §2.2).

## §5 — The honest risk, and the safety

This is the biggest single change in the system's history: executor state
representation, circuit table architecture, commitment layout, descriptor
language, and the VK all move in one epoch. The compensating discipline:

1. **The measurement gate is BEFORE the irreversible bump.** Two numbers
   must be green first: the IR-v2 size test (GATE 0 — the regression is
   measured fact, `PROOF-ECONOMICS.md:99-103`, and its fix is arithmetic
   once empty tables are elided and map-ops rides the chip bus,
   `:123-129`) and, if riding, the #174 blowup delta. Predicted landings
   are hope until `effect_vm_ir2_size_measure.rs` says otherwise.
2. **The differential gauntlets are the semantic safety**: cell≡circuit per
   map, per-effect AGREE against the rotated executor, and the
   memory-argument adversarial suite (a tampered read must refuse; the
   non-vacuity guards in `UniversalMemory.lean` §6 are the Lean templates
   for the Rust adversarial cases) — `EPOCH-DESIGN.md:105-107`.
3. **The succession drill + persvati gauntlet** are the operational safety:
   the VK bump is rehearsed, and the whole workspace is verified on the
   build node before deploy (`REORIENT.md:77`).
4. **The refactor theorems are the rollback story in proof form**:
   `boundary_root_derived` says the derived roots commit to the same object
   as today's maps — the commitment's *meaning* does not move even though
   everything around it does. Divergence in the gauntlet therefore always
   localizes to an implementation, never to an ambiguity about which answer
   is right.

## §6 — The first step, when it's time

After GATE 0 is green: **build the executor-state bridge in Lean —
interpret `RecordKernelState` into the ONE universal map
(`VerbCompression.lean:87-89`), starting with the cap-leaf value-codec
adapter lemma (`UNIVERSAL-MEMORY.md:138-144`).** It is the long pole, it
gates the 3-verb circuit, it is pure Lean (zero VK risk, can land and soak
before any flag-day motion), and it is the piece every other lane's AGREE
anchor points at.
