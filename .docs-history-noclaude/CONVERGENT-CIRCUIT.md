# THE CONVERGENT CIRCUIT — does the verb compression cash out at the circuit level?

*(design/analysis lane, 2026-06-11; no implementation. Companion to
`docs/EPOCH-DESIGN.md` (the IR-v2 epoch spec) and
`metatheory/Dregg2/Substrate/VerbCompression.lean` (the 3-verb theorem).
The deliverable is a verdict, and the verdict is at the end of §0 and in §5.)*

## §0 — The question, and the answer up front

**The hypothesis under test:** descriptor IR v2 ("thin main row + shared lookup
tables") and the verb compression ("3 verb shapes + a stratified guard algebra")
converge on the same circuit — a tiny main table with 3 row shapes
(create / guarded-write / move) plus a family of shared tables where guard atoms
become lookups — and the question is whether finishing that convergence is a
real reduction of the trusted surface or just a renaming of what IR-v2 already
built.

**The verdict, in three sentences.** The convergence is real and is roughly
half-landed already: IR-v2's endpoint and the verb-ISA endpoint are the same
five-table circuit, and `EPOCH-DESIGN.md:113-116` says so explicitly ("the
guard-ISA rearrangement (verb-compression as circuit architecture) available
later WITHOUT another flag-day, because the guard atoms are already first-class
lookups"). The remaining step — replacing 26 per-effect free-form descriptors
with 3 verb templates + per-effect guard-atom lists — is a genuine reduction,
but it lands in the **Lean/descriptor layer** (per-effect hard circuit-soundness
proofs, ≈26 of them across ~50 emit modules, collapse to 3 verb-shape theorems +
~28 one-time per-atom theorems + trivial per-effect list checks), **not** in the
Rust AIR count (6 AIRs today, 6 AIRs after), **not** in proof size or prover
cost (IR-v2 already took that win), and **not** in the form the hypothesis
imagined ("27 selectors → 3 AIRs" is a category error — the 26/29 per-effect
things are *descriptors and selectors*, which are data, not AIRs; the AIR
collapse already happened when IR-v2 made Rust a constraint-free interpreter).
Recommendation (§5): **keep per-effect IR-v2 through the imminent epoch; adopt
the convergent circuit as the circuit leg of the universal-map rotation, riding
that future VK epoch** — it is real enough to schedule, not urgent enough to be
its own flag-day.

## §1 — The convergence, concretely

### 1.1 What IR-v2 already is

The current architecture (`circuit/src/descriptor_ir2.rs:1-58`,
`docs/EPOCH-DESIGN.md:22-31`):

* **One trusted interpreter, six AIRs total.** The Rust side has exactly six
  AIR variants — `Ir2Air::{Main, Chip, ByteTable, Memory, MemBoundary, MapOps}`
  (`descriptor_ir2.rs:920-941`) — and the law "Rust authors NO constraints"
  (`descriptor_ir2.rs:53-58`): every enforced relation is the realization of a
  declared descriptor element. The five non-main tables are *shared*: one
  Poseidon2 chip (every hash = an `(input, output)` lookup,
  `descriptor_ir2.rs:14-18`), one byte/range table (`:19-22`), the
  offline-memory-checking table (`:23-32`, Blum / `memcheck_sound`), and the
  map-ops boundary-reconciliation table (`:33-43` — whose rows now carry only
  the opening's spine because every permutation rides the chip bus; the fix
  lane took `MAP_WIDTH` from the in-row-aux 12,007 shape to **71**,
  `descriptor_ir2.rs:902`). Descriptor-empty tables are elided from the batch
  (`:45-51`).
* **Per-effect content is data.** 26 descriptors in the v2 registry
  (`metatheory/Dregg2/Circuit/Emit/EffectVmEmitV2.lean:951-973`,
  `#guard v2Registry.length == 26`), emitted from Lean; the runtime selector
  regime is 29 live selectors out of a frozen 54-wide column block
  (`circuit/src/effect_vm/columns.rs:40-42`). A descriptor is a list of
  embedded v1 constraint forms plus lookups/mem-ops/map-ops — e.g. graduated
  transfer = 36 base constraints + 4 chip lookups + 2 range lookups
  (`EffectVmEmitV2.lean:977`).
* **Per-effect trust is Lean proof mass.** Each effect carries its own
  faithfulness theorem chain (`transferV2_pins_intent`
  `EffectVmEmitV2.lean:608-620`, `burnV2_full_sound` `:625-639`, …) over
  free-form `LeanExpr` constraint polynomials, anchored through
  `graduateV1_sound`.

### 1.2 What the verb compression proved

`Dregg2/Substrate/VerbCompression.lean` settles the semantics side:

* **Three verbs** — `create · gwrite · move`
  (`compressed_kernel_three`, `VerbCompression.lean:998-1000`); five of the
  seven survivor verb constructors dissolve into the one guarded write
  (`:1024-1028`).
* **A proven-strict guard stratification** (`:69-74`):
  local `(actor, old, new)` ⊂ literal atoms ⊂ +absence ⊂ +order-relational,
  with each inclusion proper (`freshness_not_positive` `:648-674`,
  `grant_guard_not_literal` `:473-540`).
* **Two separations the circuit must keep.** Move's conservation is a *shape*
  property, outside every guard class (`gwrite_conservation_trivializes`
  `:773-786`: any conservation-respecting single-key guarded write is
  value-trivial; `move_not_single_write` `:876-882`). Create's bundle birth is
  multi-address atomic (`create_birth_not_single_write` `:916-924`), though its
  existence leg is the same absence-guarded fresh write as unshield (`:901-911`).
* The guard modalities are named and housed: actor
  (`Exec/Program.lean:56-90`, `SimpleConstraint`, 12 forms), heap
  (`Substrate/HeapKernel.lean:145-150`, `HeapAtom` 2 forms + the `absent`
  extension), temporal (`Authority/TemporalAlgebra.lean:111+`, 6 forms;
  `TemporalAlgebra2.lean:142-150`, the UNTIL/SINCE pair), epistemic
  (`Authority/Epistemic.lean:966-975`, 4 forms — **design-stage**, installation
  not landed), order (`VerbCompression.grantGuard` `:397-398`, the one
  `new ⊑ get(k)` atom). Total: **≈27-28 atom forms** across the five families
  (`Calculus/DreggCalculus.lean:133-149` is the modality index).

### 1.3 The convergent circuit, sketched

The two endpoints meet in one circuit. Concretely:

**Main table: 3 row shapes instead of 29 selectors.** A main row carries a verb
tag (2 bits / one 3-hot selector triple) instead of the 54-wide selector block:

| verb shape | row content | table interactions |
|---|---|---|
| **create** | born-cell key bundle, init values | k× fresh-insert map-ops (`absent`+insert) into the cells/heap collections; chip lookups for the commitment |
| **gwrite** | actor, target key, old/new value, guard-list ref | 1× map-op or mem-op write; guard-atom interactions (below) |
| **move** | src, dst, amount, two old/new pairs | 2× paired mem-ops/map-ops + the in-row cancelling-delta constraint Σδ=0; range lookups for the signed wells |

The conservation pairing and the birth arity stay **in the row shape** — exactly
where `VerbCompression` §6/§7 proved they must live. They are the irreducible
"more than one opening changes" rows; no guard table absorbs them.

**The guard-atom "table" is not one table — it is a guard-atom CONSTRAINT KIND
that elaborates onto the existing tables.** This is the most important honest
correction to the hypothesis. Per atom family:

| modality | atoms | realization in the convergent circuit |
|---|---|---|
| actor (local) | `fieldEquals/fieldDelta/immutable/writeOnce` … | one canonical linear base constraint each (no table — equalities over row values) |
| actor/temporal (order) | `fieldGe/fieldLe/monotonic/strictMono/inRangeTwoSided/deltaBounded`, `afterHeight/beforeHeight/withinWindow/cooledSince` | **the existing range table**: `a ≤ b` ⇝ range-decompose `b − a` (`descriptor_ir2.rs:19-22, 992-1010`). The range table *is* the guard table for the order stratum |
| heap (literal) | `heapContains/heapGetEq` | **the existing map-ops/memory tables** — already first-class (`descriptor_ir2.rs:23-43`) |
| heap (absence) | `absent` / freshness | map-op kind `absent` — declared in the IR, realization pending on the nullifier-insert lane (`descriptor_ir2.rs:62-68`); needed regardless of this design |
| order-relational | `new ⊑ get(k)` submask | the subset "table" (`EffectVmEmitV2.lean:680-707`) — **virtual**: at 30 bits it has ~3³⁰ ≈ 2×10¹⁴ rows and is realized by per-bit decomposition, not a materialized lookup (`descriptor_ir2.rs:69-73`) |
| temporal (event) | `untilEvent/sinceEvent` | a register read = mem-op + zero/nonzero gate |
| epistemic | `knownBy/distributedAmong/commonAt/privateTo` | chip lookups (signature hashing) + threshold counting; design-stage in Lean (`Epistemic.lean:964-966`), partly consensus-layer — honest scope: not a circuit row today |

So "guard atoms become lookups instead of per-effect constraints" is true in
the load-bearing cases (order ⇒ range table, heap ⇒ map/memory tables, hashing
⇒ chip) — and those are *already lookups in IR-v2*. The genuinely new circuit
element is **zero new AIRs**. What is new is IR grammar: a `guardAtom`
constraint kind whose elaboration into lookups/base-forms is defined once in
Lean and proven once per atom, replacing the free-form `LeanExpr` constraint
lists each descriptor carries today.

**The descriptor IR in this world.** Today: 26 descriptors, each ~30-45
free-form constraints (`EffectVmEmitV2.lean:951-977`). Converged: **3 verb
templates** (fixed, proven once) + per-effect entries of the shape
`(verb, guard-atom list, PI-binding map)` — the per-effect content shrinks from
"a bag of polynomials whose meaning needs a per-effect theorem" to "a list of
atoms whose meaning is the atom catalog." The precedent rows already exist:
`setFieldDynVmDescriptor2` is ONE descriptor of 4 constraints replacing 8
per-slot descriptors (`EffectVmEmitV2.lean:887-900`), and
`attenuateVmDescriptor2` is base + exactly 3 declared ops (held-read map-op,
keep-write map-op, submask lookup — `EffectVmEmitV2.lean:743-747`) whose
soundness theorem (`attenuateV2_non_amp` `:754-779`) reads like a per-atom
composition rather than a bespoke polynomial argument. Those two are the
convergent circuit in miniature; the proposal is "do that to everything."

## §2 — THE HONEST VERDICT: what shrinks, what does not

### 2.1 What genuinely shrinks

1. **The per-effect Lean proof mass (the big one).** Today every effect has an
   emit module with a bespoke soundness chain (~50 files in
   `metatheory/Dregg2/Circuit/Emit/`; 26 registry descriptors each with
   `*_pins_intent`/`*_full_sound`-class theorems over free-form exprs).
   Converged: **3 verb-shape soundness theorems** (one per row shape, stating
   "a satisfied create/gwrite/move row is the kernel's
   `recKCreateCell`/`stateStepGuarded`/`moveStep` step") **+ ~28 per-atom
   realization theorems** (one-time: "this atom's elaboration holds iff the
   atom's `eval` is true" — the `subsetTable_mem_iff` /
   `gSlotRange_holds_iff` shape, already demonstrated) **+ 26 per-effect
   correspondence lemmas that are near-syntactic** ("effect e's guard list =
   the kernel's guard list for e", a `decide`-class check against
   `VerbCompression.cfate` `:987-994`). The hard, per-effect, polynomial-level
   reasoning collapses from O(effects) to O(verbs) + O(atoms). This is a real
   trusted-surface reduction: the thing a auditor must *believe* per effect
   becomes a data correspondence, not a proof.
2. **The descriptor-language surface.** The free-form `LeanExpr` gate/transition
   vocabulary in shipped descriptors narrows to a closed atom catalog + the 3
   templates + PI bindings. Auditing a shipped descriptor today means reading
   ~40 polynomials; converged, it means reading an atom list against the atom
   catalog. The grammar first *grows* by one constraint kind (`guardAtom`),
   then most uses of raw `gate`/`transition` forms retire.
3. **The selector regime.** 29 live one-hot selectors in a frozen 54-wide block
   (`columns.rs:40-42`) become a verb tag + a guard-list binding; the
   RETIRED_SELECTORS pinning machinery dies with it. Modest width win on main
   (which EPOCH already thins to ~40-60 cols, `EPOCH-DESIGN.md:26`).
4. **Forward cost of new effects.** A new effect = a new guard list (data + one
   `decide` lemma), not a new emit module + descriptor + soundness chain + AIR
   harness arm. This is the durable payoff: the marginal cost of kernel
   evolution drops to near-zero on the circuit side.

### 2.2 What does NOT shrink (and must not be claimed)

1. **The Rust trusted interpreter: 6 AIRs → 6 AIRs.** The hypothesis's
   "27 selectors → 3 + a guard table" miscounts what exists: there are not 27
   AIRs today. IR-v2 already collapsed the per-effect AIR surface into one
   constraint-free interpreter + five shared table AIRs
   (`descriptor_ir2.rs:53-58, 920-941`). The convergent circuit keeps exactly
   those six. The expr evaluator in main must stay (PI bindings, state
   commitment plumbing, the move delta constraint). Rust shrinks marginally at
   best (fewer base-form arms exercised).
2. **Proof size and prover cost: neutral.** Same tables, same lookup buses,
   similar row counts. The ~452→100-200 KiB landing belongs to the EPOCH tables
   (`EPOCH-DESIGN.md:110-113`), not to this reshape. Anyone selling the
   convergent circuit as a performance win is wrong.
3. **Move and create stay distinct row shapes.** Per
   `gwrite_conservation_trivializes` (`VerbCompression.lean:773`) and
   `create_birth_not_single_write` (`:916`), conservation and birth-arity are
   shape obligations. The main table has 3 row forms, not 1; the move form
   carries its paired-delta constraint in-row forever. The circuit honors the
   separations the Lean file proved — it cannot be "one guarded write + tables."
4. **The guard-atom table is plural and partly virtual.** No single new lookup
   table exists or should: order atoms ride the range table, heap atoms ride
   map/memory, the submask relation is enforced by decomposition because its
   table is unmaterializable at 30 bits (`descriptor_ir2.rs:69-73`). "Atoms
   become lookups" is accurate as architecture, inaccurate as "one new table."
5. **Epistemic atoms are not circuit-ready.** The family is design-stage
   (`Epistemic.lean:964-966`); `commonAt` lives partly at the consensus layer.
   The convergent descriptor language should reserve the modality, not promise
   its realization.
6. **The prerequisite is the executor rotation, and it is large.**
   `VerbCompression.lean:88-89`: "the executor-state bridge (interpreting
   `RecordKernelState` itself into the one map) rides THE ONE ROTATION." A
   3-verb circuit proving against a 50-effect executor has nothing to AGREE
   with — the differential gauntlets (cell≡circuit, per-effect AGREE) anchor on
   the executor's shape. The convergent circuit is only honest *after* (or
   exactly alongside) the universal-map rotation of the executor. This is the
   real cost center, and it is not a circuit cost.

### 2.3 The quantified summary

| surface | today (IR-v2) | convergent | verdict |
|---|---|---|---|
| Rust AIRs (trusted constraint code) | 6 | 6 | **no change** |
| shipped descriptors | 26 free-form (`EffectVmEmitV2.lean:973`) | 3 templates + 26 guard lists | **real**: per-effect content becomes data |
| per-effect hard soundness theorems | ≈26 chains (~50 emit modules) | 3 + ~28 atoms + 26 `decide` lemmas | **real**: the largest single reduction |
| selector columns | 29 live / 54 frozen (`columns.rs:40-42`) | 3-shape tag | real, modest |
| proof size / prover time | EPOCH landing | same | **no change** |
| guard semantics proofs | done (`VerbCompression.lean`) | reused | already paid |

So: **a real enhancement, not aesthetic — but its entire payoff is
auditability + Lean proof mass + forward marginal cost, located above the Rust
AIR line, and the size/performance win it is adjacent to was already taken by
IR-v2.** If one asks only "does the trusted *Rust* interpreter shrink?" the
honest answer is "no, and it already shrank as far as it goes." If one asks
"does the per-effect trusted surface (descriptors + their proofs) shrink?" the
answer is "yes, by roughly an order of magnitude in count, and the two
already-landed exemplars (`setFieldDyn`, `attenuate` phase-B) demonstrate the
shape works."

## §3 — The zkVM framing: useful north star or vocabulary?

Precisely stated: the IR-v2 interpreter **already is** dregg's zkVM in the
proved-once sense — one interpreter, proven faithful once
(`graduateV1_sound` et al.), executing programs that are data (descriptors).
What the convergent circuit changes is the **ISA**: from "programs are
arbitrary constraint lists" to "programs are (verb, guard-atom list) pairs over
a fixed 3-verb + ~28-atom instruction set," with the instruction set *derived
from the kernel theorems* (`compressed_kernel_three` + the strata) rather than
accreted.

Is that framing useful? **Partially — useful as a closure milestone, misleading
as an architecture promise.** Useful: a closed ISA is exactly what makes the
audit story compositional ("trust the 3 shapes + the atom catalog once; every
effect is then data"), and it gives the upper layers (SDK, descriptor
regeneration, the assurance case) a stable vocabulary that matches the
calculus (`DreggCalculus.lean:95-106` — `CTerm` is literally this ISA). 
Misleading: there is no fetch/decode loop, no program counter, no general
recursion of programs — it remains one row per effect in a batch STARK, and
calling it a zkVM invites comparisons (RISC-V zkVMs, universal circuits) whose
properties dregg neither has nor wants (a universal interpreter loop would
*cost* performance for nothing — dregg's "programs" are 8-verb-bounded kernel
steps, not arbitrary code). Recommended usage: "the descriptor interpreter with
a kernel-derived ISA" internally; avoid the bare "zkVM" externally.

## §4 — Recursion (brief, by instruction)

The in-circuit FRI verifier's dominant cost is hashing (Merkle path checks per
query, transcript hashing). The chip-table architecture — every permutation a
row, every hash site a lookup (`descriptor_ir2.rs:14-18`) — is exactly the
right substrate for it, and that substrate is **IR-v2's, already landed**. The
verb/guard reshape contributes nothing additional to recursion: guard atoms do
not hash, and the 3-shape main table is neither easier nor harder to verify
recursively than the 26-descriptor one (same batch shape, same tables). The
proving-modality dial (#169) is the adjacent lane that owns recursion
trade-offs; this design neither blocks nor advances it, and the two should not
be entangled. One genuine but second-order synergy: fewer distinct descriptors
means fewer distinct VKs for a recursive aggregator to carry, which simplifies
the aggregation manifest — a bookkeeping win, not a cryptographic one.

## §5 — Verdict and recommendation

**Verdict: REAL, upper-half-of-the-stack.** The convergence hypothesis is
correct as architecture — IR-v2 and the verb compression do converge on the
same five-table circuit, and the guard strata map cleanly onto the tables
IR-v2 already has (order⇒range, heap⇒map/memory, hash⇒chip, submask⇒the one
custom relation). Finishing it is a significant reduction of the
**descriptor-language and Lean-proof trusted surface** (26 free-form
descriptors + ≈26 bespoke soundness chains → 3 templates + ~28 atom theorems +
data), and a near-elimination of the marginal circuit cost of kernel
evolution. It is **size-neutral, prover-neutral, and Rust-AIR-neutral**, and
the "27→3 AIR" version of the claim is false because the AIR collapse already
happened. Not aesthetic — but not a second size revolution either.

**Recommendation: KEEP per-effect IR-v2 through the imminent epoch; REBUILD
toward the convergent circuit as the circuit leg of the universal-map rotation,
riding that future VK epoch.** Specifically:

1. **Do not entangle with the imminent IR-v2 flag-day.** The epoch as specced
   (`EPOCH-DESIGN.md:68-99`) graduates everything, kills the fallbacks, and
   re-anchors faithfulness onto IR v2. Ship it as is. The epoch already
   guarantees the convergent reshape needs no new constraint-kind flag-day
   (`EPOCH-DESIGN.md:113-116`) — that promise is the design's permission to
   wait.
2. **Gate the rebuild on the executor rotation.** The 3-verb circuit is only
   meaningful against the 3-verb executor (the `RecordKernelState`→universal-map
   bridge, `VerbCompression.lean:88-89`); sequencing it earlier would re-create
   the divergence disease (circuit semantics ahead of runtime semantics, no
   AGREE anchor).
3. **The rebuild's honest cost**, when scheduled: one IR grammar extension
   (`guardAtom` kind + 3 verb templates), ~28 one-time atom-realization
   theorems (the `subsetTable_mem_iff`/`gSlotRange_holds_iff` pattern), 3
   verb-shape soundness theorems, regeneration of the 26 descriptors into
   (verb, guard-list) form with `decide`-class correspondence lemmas, the
   differential gauntlets replayed, one VK/commitment bump — *shared with the
   rotation's own mandatory regeneration*, which is why it rides that epoch for
   free. Comparable in size to the current graduation sweep; strictly smaller
   than the IR-v2 build. The `absent` map-op realization is on the critical
   path regardless (nullifier insert lane) and should not be booked as a cost
   of this design.
4. **Two descriptors should converge early as proofs-of-shape, without waiting:**
   the next effect that would need a new emit module should be authored as a
   (verb, guard-list) descriptor against the existing IR (the
   `setFieldDyn`/`attenuate` pattern), so the template machinery grows by use
   rather than by big-bang.

The size win was IR-v2's. The auditability win is this one's, and it is worth
taking — at the rotation, not before.
