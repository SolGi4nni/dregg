# dregg's logic compiler — a structural assessment (READ + ASSESS, 2026-08-01)

*Scope: map the pipeline from high-level dregg logic (turns / effects / verbs /
biscuit-Datalog) down to emitted AIR, treat it AS a compiler, and assess how far it
is from a full DSL/compiler approach and what the new Pickles-epoch tools (WitnessBuilder,
KimchiPlacement, AirBuilder, the gate emitters) buy us. READ-ONLY structural map — no code
changed. All citations are `path:line` into `metatheory/`.*

---

## TL;DR verdict

**(c) — in between, and the interesting part is WHERE.** dregg has a *real* compiler
spine with proven, general lowering — but it is **split across two backends that do not meet**,
and the deployed one is the hand-authored side.

1. There is a genuine **spec-first lowering framework** on the effect surface
   (`EffectCommit2`: `EffectSpec2` → derived circuit → derived apex → two-sided refinement
   proven ONCE; ~29 effects are thin instances). This is a real compiler.
2. There is a genuine **logic → IR compiler** on the Datalog/predicate surface
   (`FiniteRelationalFOLDescriptorIR2` self-describes as "an end-to-end, kernel-checked
   compiler for a genuine finite first-order language into the live `EffectVmDescriptor2`
   relation"). This is a real compiler, lowering THROUGH `DescriptorIR2`.
3. **But the deployed AIR rail** — the 76 checked-in `EffectVmDescriptor2` descriptors that
   Rust's `Ir2Air` actually runs — is fed by **~hundreds of hand-authored `Circuit/Emit/*.lean`
   emitters that hand-roll raw `VmConstraint2` list-literals in one mechanical skeleton**, and
   the clean `EffectSpec2` framework's *own* emission targets a **RETIRED IR-v1 rail with no
   deployed Rust interpreter**.

So the spine exists; it is just wired to the wrong backend, while the live backend grew the
barnacles. The refactor ember is sensing is real and its shape is precise: **rebase the
existing spec-first spine onto `DescriptorIR2`, and grow ONE lowering pass that consumes the
hand-authored `*Emit.lean` skeleton.** The new tools (AirBuilder, WitnessBuilder, KimchiPlacement)
are the correct primitives for that pass but are, today, thinly adopted and mostly on the *other*
(Kimchi/Pasta) substrate.

---

## Two substrates first (this is the thing to hold in your head)

The word "circuit" covers two disjoint arithmetization targets in this tree. Conflating them
is the main way to misread the map.

| | **BabyBear AIR / EffectVM** | **Kimchi / Pasta PLONK** |
|---|---|---|
| purpose | dregg's own effect/turn prover | the Mina recursion / bridge verifier |
| IR | `EffectVmDescriptor2` (multi-table), v1 `EffectVmDescriptor` | 15-column gate grid + copy-permutation |
| gate expr | `EmittedExpr` (var/const/add/mul), `Head` | `PGate` / cell placements |
| shared builder | **`AirBuilder`** (`Head` vocabulary) | **`WitnessBuilder` + `KimchiPlacement`** |
| deployed by | `emitVmJson2` → Rust `Ir2Air` (`descriptor_ir2.rs`) | o1js verifier / Pickles-in-Lean |

`AirBuilder.lean:2-37` (BabyBear) and `WitnessBuilder.lean:33-38` (Kimchi) are **different tools
for different substrates**. ember's framing ("WitnessBuilder converging toward pulling dregg's
AIR out of per-effect emitters") is directionally right about the *pattern* but the specific tool,
WitnessBuilder, lives on the Kimchi grid, not the BabyBear AIR where the per-effect effect emitters
live. The BabyBear analogue of WitnessBuilder is **`AirBuilder` + the per-effect witness encoders**,
and that is where an effect-lowering refactor actually lands.

---

## 1. The pipeline, drawn end-to-end

Boundary type at each `→`. The **deployed** path is the top spine; the **refinement/spec** path
is the parallel proof spine; they are stitched per-effect, not fused.

```
 TURN LAYER            JointTurn.JointTurn / JointFamily         (JointTurn.lean:1-20  — cross-cell
   │                   = equalizer/pullback of participants'      atomic turn, Mina zkapp_command forest)
   │  : List step
   ▼
 EXECUTOR             FullActionA  (30 live constructors)         (Exec/TurnExecutorFull/PerAsset.lean:1551)
   │  execFullTurnA / execFullA                                   routed, NOT EffectKind
   ▼
 NAME DISPATCH        actionAirName : FullActionA → String        (EffectEmitRegistry.lean:90-124, cover=30)
   │                  effectEmitRegistry : String → Option _      (EffectEmitRegistry.lean:131, cover=32,
   │                  fail-closed; escrow/obligation/bridge = HOLE  #guard holeAirNames ↦ none :138)
   ▼
 ┌─────────────────────────── the split ───────────────────────────┐
 │                                                                   │
 ▼  DEPLOYED RAIL (law #1)                    ▼  SPEC / REFINEMENT RAIL (proof)
 EffectVmDescriptor2                          EffectSpec2  (EffectCommit2.lean:196, ~8 fields)
  (DescriptorIR2.lean:510, multi-table)         │  emittedEffect2 = emit ∘ effectCircuit2
   │  hand-authored in Circuit/Emit/*.lean       │            (EffectCommit2.lean:484)
   │  (234 files ref it; 76 checked-in)          ▼
   │  emitVmJson2 → String                     EmittedDescriptor  (Exec/CircuitEmit.lean:81, flat lhs=rhs)
   ▼                                             │  → Rust LeanDescriptorAir
 Rust Ir2Air (circuit/src/descriptor_ir2.rs)     ▼  ⚠ RETIRED IR-v1, NO deployed path
 the AIR the prover runs                        (circuit/src/lean_descriptor_air.rs:3)
 └───────────────── stitched per-effect: "delegateVmDescriptor := attenuateVmDescriptor" +
                    unify_delegate connector (EffectVmEmitDelegate.lean:93, :23-29) ────────────┘

 WITNESS: Assignment (= Var → ℤ) / TraceFamily / VmTrace   (DescriptorIR2.lean:539-546)
   general per-effect encoder encodeE2 (EffectCommit2.lean:258); general adversarial
   extractor WitnessExtract.effect2_extract retargeted per effect (WitnessExtractPerEffect.lean:23-25)
```

**The graph, in one sentence:** turns fold into `FullActionA` steps; each step name-dispatches
to an AIR; the AIR the prover actually runs is a **hand-authored `EffectVmDescriptor2`**; a
**separately-derived `EffectSpec2`** proves that descriptor refines the executor and the human
spec, but the framework's *own* serializer emits to a retired rail. The IR is real; two of them are.

Boundary types, named:
- turn: `JointTurn.JointTurn` / `TurnWitness` (`TurnWitness.lean:49-58`)
- action: `FullActionA` (`Exec/TurnExecutorFull/PerAsset.lean:1551`)
- effect catalog: `EffectKind`, 53 closed constructors (`CatalogInstances.lean:273`) — **used
  only for conservation coloring**, not routing
- spec: `EffectSpec2` (`EffectCommit2.lean:196`)
- deployed IR: `VmConstraint2` / `EffectVmDescriptor2` (`DescriptorIR2.lean:497,510`)
- gate expr: `EmittedExpr` (`Exec/CircuitEmit.lean:64`), `AirBuilder.Head` (`AirBuilder.lean:54`)
- wire: `emitVmJson2 : EffectVmDescriptor2 → String` (`DescriptorIR2.lean:1755`), decoded by `Ir2Air`
- witness: `Assignment`, `TraceFamily`, `VmTrace` (`DescriptorIR2.lean:539-546`)

---

## 2. DSL: how expressive, how used

There are **three "effect" vocabularies**, and none of them is an open, composable term
language. Each is a **fixed, exhaustively-enumerated catalog**:

- **`EffectKind`** — 53 closed constructors (`CatalogInstances.lean:273`). Purpose: conservation
  coloring only. `CatalogEffects.lean` colors all 53 onto six `LinearityClass` colors and proves
  totality three ways (`effectLinearity_total` :175, `every_effect_classified` :184, the `Regime`
  discriminator :230). It does **not** wire to circuits.
- **`FullActionA`** — 30 live constructors (`EffectEmitRegistry.lean:90`, `actionAirNameCoverage=30`).
  The executor's action type — the thing actually routed to AIRs.
- **`Verb`** — the 8-verb kernel signature (`VerbRegistry.lean:98`), a *census/signature* reified
  as data with a proven-exhaustive `classify` and a minimality proof (`VerbRegistry.lean:35-44`).
  Explicitly "a SIGNATURE, not an instantiation" (`VerbRegistry.lean:59`) — the anchor the dispatch
  table and descriptor table *reconcile against by name*, not a term language they are generated from.

**`DSLEffect.lean` is a real eDSL, but a narrow one.** `dregg_effect <name> (args) : <Color>`
(`DSLEffect.lean:101-129`) is a genuine surface-syntax macro that **generates** (not hand-writes)
an effect's conservation obligation and discharges it from one proved fact (`obligation_holds`
:73). That is a parser-onto-proved-primitives DSL in the textbook sense — but its semantic target
is the **conservation lattice**, not the circuit. It generates `<name>.color/.regime/.args/
.obligation`; it does not generate a gate, a witness, or a descriptor.

**Authoring path of three real effects (all READ):**
- **transfer** — `dregg_effect transfer (…) : Conservative` (`DSLEffect.lean:137`) fixes only its
  color. Its circuit is the hand-authored full-state `StateCommit`/`Transfer` descriptor; its spec
  side is `transferE : EffectSpec2` with the diamond in `EffectRefinement.lean §6`.
- **a map-op (heapWriteA)** — routed by `actionAirName … heapWriteA ↦ HeapWriteA.heapWriteAAirName`
  (`EffectEmitRegistry.lean:124`); the deployed row is a hand-authored `EffectVmDescriptor2` whose
  `.mapOp` denotation opens the deployed arity-3 IMT (`DescriptorIR2.lean:593-611`).
- **an Automatafl move** — hand-authored in a *game* module; `AutomataflStepEmit`/`ResolveEmit`
  carry their **own private `Head` copies** and are named as un-migrated debt
  (`AirBuilder.lean:28-32`).

Verdict on the DSL: **a fixed, well-disciplined catalog with a conservation-only front-end macro,
not a circuit-authoring language.** Effects do NOT flow through a DSL into circuits; they are
routed by name and their circuits are authored (or spec'd) per-effect.

---

## 3. ⚑ Is `DescriptorIR2` a real IR the compiler lowers through, or a refinement target?

**Decisively: it is BOTH, on two different surfaces — and that duality is the whole finding.**

- **As a lowering target it is REAL and USED.** The `*DescriptorIR2` family are genuine lowering
  passes that *consume a source and produce IR2*:
  - `FiniteRelationalFOLDescriptorIR2.lean:1-13` — "end-to-end, kernel-checked compiler for a
    genuine finite first-order language into the live `EffectVmDescriptor2`," grounding quantifiers,
    statically evaluating terms, lowering through `FiniteLogicDescriptorIR2`, with soundness/
    completeness composed against the actual `Satisfied2` semantics.
  - `DirectLogicBoolGraphDescriptorIR2.lean:1-17` — materializes a Boolean graph into explicit
    witness columns + flat degree-≤2 `windowGate`s (one of two backends the direct-logic optimizer
    emits).
  - `IntensionalCCCInteractionDescriptorIR2.lean:1-26` — lowers a typed STLC local step → executable
    Boolean interaction receipt → one-row IR-v2 descriptor with two hash-site commitments.
  - Also `FiniteSignatureFOLDescriptorIR2`, `GabbayDescriptorIR2*`, `TypedLinearPredicateDescriptorIR2`.
  - 78 Lean files `import DescriptorIR2`; `Satisfied2` (`DescriptorIR2.lean:831`) is its denotation;
    `Ir2Air` (110 Rust consumers per `Exec/CircuitEmit.lean:44`) is its deployed interpreter. This is
    a real IR by every structural test: a data type, a denotation, multiple front-ends lowering into
    it, one backend running it.
  - **⚠ but every one of these logic modules is a "standalone additive module; no integration
    imports are changed"** (stated verbatim in each header, e.g. `IntensionalCCC…:24-25`,
    `DirectLogicBoolGraph…:17`, `FiniteRelationalFOL…:24-27`). They demonstrate the lowering exists
    and is sound; they are **not wired into the turn/effect executor.**

- **As the EFFECT surface it is a HAND-AUTHORED TARGET, not lowered-through.** For transfer / mint /
  delegate / heapWrite, the `EffectVmDescriptor2` is written by hand in `Circuit/Emit/*.lean` (raw
  `VmConstraint2` list-literals — see §4), and the `EffectSpec2` is proven to *correspond* to it via
  a per-effect bridge. The connector modules make this explicit: `delegateVmDescriptor :=
  attenuateVmDescriptor` (`EffectVmEmitDelegate.lean:93`) reuses a hand-authored descriptor, and
  `unify_delegate` (`:23-29`) is a hand proof that the runnable row equals universe-A's validated
  transition — **not** a general `lower : EffectSpec2 → EffectVmDescriptor2`.

So the `feedback-lean-must-be-the-implementation` distinction resolves cleanly: **for logic,
IR2 is lowered-through (real passes); for effects, IR2 is a hand-authored object that the spec
is proven to refine.** No general pass takes a dregg *effect* to its deployed IR2 descriptor. That
missing pass is precisely the refactor.

The `IntensionalCCCInteraction` calculus (`Calculus/IntensionalCCC*`) is **metatheoretic**: it is a
load-bearing SOURCE for the one CCC→IR2 demonstration module, but it is not on the deployed effect
path (that module is additive-only).

---

## 4. `AirBuilder`: one real builder, or one of many — quantified

**`AirBuilder` is one *nascent, thinly-adopted, forward-only* builder; the dominant idiom is
hand-rolled IR literals.** Numbers (census over `Dregg2/Circuit/Emit/`, 383 `.lean` files):

- `AirBuilder` (`AirBuilder.lean`) is the game-free `Head = Σ(coeff·∏cols)+const` vocabulary
  (`:54`) with the one semantic bridge `headToExpr_eval` (`:158`) proven once, plus gadget families
  `binGate/condNonzero/rangeNonneg/forcedGe0/pinPi` (`:294-378`). It was **just hoisted** from two
  duplicated Rust builders and *explicitly names its own non-adoption as debt*: "`AutomataflStepEmit`/
  `ResolveEmit` still carry their own `Head` copies … NOT done here" (`:28-32`); "What this module
  DOES close is the forward direction" (`:31`).
- **Adoption is thin and off to one side:** 7 direct importers, 36 `open`s, 15 qualified call sites —
  and they cluster in the **crypto-gadget / Pasta-MSM / hash-fold** corner (`Sha256Gadget`,
  `Ed25519Gadget`, `PastaMsmAir`, `LightClient*HashFold`), *not* the effect/membership emitters.
- **Of the 78 `*Emit.lean` files, only 4 reference `AirBuilder`; 74 do not; 63 hand-roll** raw
  `.base (.gate …)` / `.base (.piBinding …)` / `.lookup …` `VmConstraint2` literals directly.

**And the hand-rolled emitters ARE a mechanical skeleton** (the Pickles-gates smell, at scale).
Across the 78 `*Emit.lean`: **61 define an `EffectVmDescriptor2`, 46 carry a `#guard emitVmJson2 …`
byte-golden, 51 prove a `_zero_iff`/`_forces` "the gate bites" lemma.** The skeleton is:
(1) column-index constants → (2) gate bodies as `EmittedExpr` → (3) a `List VmConstraint2` of raw
literals → (4) the `EffectVmDescriptor2` record → (5) a serialization golden → (6) a refinement
lemma. Side by side (agent-verified):

```
-- MerkleMembershipEmit.lean:122            -- AdjacencyMembershipEmit.lean:236
def merkleMembershipDesc : EffectVmDescriptor2 :=   def adjacencyDesc : EffectVmDescriptor2 :=
 { name := "merkle-membership-…"             { name := "dregg-membership-adjacency-…"
 , traceWidth := MEMBERSHIP_WIDTH            , traceWidth := ADJ_WIDTH
 , constraints := [level0Lookup, …]          , constraints := adjacencyConstraints
 , … }                                       , … }
```

Both pair a `.base (.gate …)` transition gate with a `.base (.boundary VmRow.last …)` "last-row
fix" for the identical reason (transition gates are vacuous on the final row), documented near-
verbatim in both. **This is one skeleton instantiated with different column layouts — exactly the
"5 copies of compose-and-place" smell, at ~60× scale.** The bespoke content is the column layout
and the gate *polynomials*; the framing is repeated by hand.

The full-state effect emitters have a *better* story: `EffectCommit`/`EffectCommit2` DO abstract the
commitment skeleton once (`EffectCommit.lean:1-63`: two ~500-line bespoke proofs → one framework +
~29 ~100-line instances; the 4 anti-ghost teeth proved once). But (a) that framework targets the
retired rail (§1), and (b) it abstracts the *commitment/binding*, not the per-effect *guard gates*,
which remain hand-authored `ConstraintSystem` values per effect (`EffectSpec2.guardGates`).

---

## 5. ⚑ The refactor opportunity — concretely

**What fraction of the hand-authored per-effect emitters could a general lowering pass replace?**
A defensible estimate, by bucket:

- **The framing/skeleton of the ~61 membership/gate `*Emit.lean` descriptors (steps 1,3,4,5,6
  above): mostly mechanizable.** The `EffectVmDescriptor2` record assembly, the `.boundary`
  last-row fixes, the `emitVmJson2` golden, and the `_zero_iff` proof obligation are the *same shape*
  every time. A builder that takes (columns, gate `Head`s, lookups, PI pins) and produces the
  descriptor + the bridge lemma would absorb this. Call it **~50-70% of the *lines*, ~0% of the
  *gate polynomials*.**
- **The gate polynomials and column layouts: genuinely per-effect, NOT generalizable.** `x·(x−1)`
  vs `sel·(1−val·inv)` vs a Merkle continuity gate vs an IMT relink is real per-effect arithmetic.
  This is the irreducible core and should stay authored (in Lean, per law #1) — but authored *through
  `AirBuilder.Head` combinators* rather than raw `EmittedExpr`, so the `headToExpr_eval` bridge
  discharges the "gate bites" lemma mechanically.
- **The full-state effect commitment: already abstracted** (`EffectCommit2`), just on the wrong
  backend. Rebasing it is the highest-leverage single move.

**Where the new tools slot in (BabyBear AIR side):**
- `AirBuilder.Head` + `headToExpr_eval` (`AirBuilder.lean:158`) → the constraint-authoring layer:
  replace raw `.base (.gate <EmittedExpr>)` literals with `cgH (Head…)`, getting the semantic bridge
  for free. **This is the ready primitive; it just needs to be adopted by the 74 emitters that ignore
  it, and to absorb the two Automatafl `Head` copies it already names as debt.**
- `AirBuilder`'s gadget families (`binGate/rangeNonneg/condNonzero/forcedGe0`) → the reusable gate
  vocabulary a lowering pass emits from.
- A **`lower : EffectSpec2 → EffectVmDescriptor2`** does not exist and is the missing spine piece.
  Today `emittedEffect2` (`EffectCommit2.lean:484`) lowers `EffectSpec2` to the *retired* flat
  `EmittedDescriptor`. Retargeting it to build a `VmConstraint2`/`EffectVmDescriptor2` (via
  `AirBuilder`) is the single edit that fuses the two rails.

**Where the Kimchi tools slot in (the OTHER substrate):** `WitnessBuilder`
(`WitnessBuilder.lean:78-88`, `toGrid`/`compose`) and `KimchiPlacement` (placement + copy-permutation
σ) are the *witness-assembly* analogue for the 15-column PLONK grid. They generalize the 5 hand-rolled
`KimchiRender*.witAt` copies (`WitnessBuilder.lean:12-16`) and are the right primitives for the
Pickles-in-Lean step/wrap witness assembly — **but they do not touch the BabyBear effect emitters.**
On the BabyBear side the witness analogue already exists and is already general: `encodeE2`
(`EffectCommit2.lean:258`) and the single adversarial extractor `WitnessExtract.effect2_extract`
retargeted per effect (`WitnessExtractPerEffect.lean:23-25`). So **witness generation is already
uniform on both substrates**; it is *constraint authoring* (BabyBear) and *rail fusion* that are not.

**Reusable core vs. genuinely per-effect:**
- Reusable (proved/abstracted once): full-state commitment binding + 4 anti-ghost teeth
  (`EffectCommit2`); the `Head→EmittedExpr` bridge + gadgets (`AirBuilder`); witness encode/extract;
  turn-level fold (`TurnWitness.foldStepRoots`, `TurnEmit`); the logic→IR2 passes (`*DescriptorIR2`).
- Irreducibly per-effect: the guard/admissibility gate polynomials, the column layout, the specific
  `.mapOp`/`.lookup`/hash-site denotation an effect touches, and the `apex ↔ human-spec` bridge.

---

## 6. "Logic arithmetization isn't fully appropriate" — the seam, one honest paragraph

The seam where relational/Boolean **logic** becomes field **arithmetic** is the `*DescriptorIR2`
logic family, and the mismatch is real and named in-tree. Two structural symptoms: **(i) quantifiers
are GROUNDED, not proven succinctly** — `FiniteRelationalFOLDescriptorIR2.lean:11-18` "grounds the
finite quantifiers … every quantifier ranges over all `q` elements," so a `∀`/`∃` over a domain of
size `q` is *unrolled* into `q` copies (no relational join, no witness-selected subset, no succinct
quantifier protocol — explicitly disclaimed, `:24-27`); **(ii) the same logic has two incomparable
arithmetizations and the tool must CHOOSE** — `FiniteLogicDescriptorIR2` emits "one nested
polynomial" (deep, high-degree) while `DirectLogicBoolGraphDescriptorIR2.lean:4-9` materializes
"every zero test and Boolean connective" as explicit witness columns + flat degree-≤2 gates (wide,
many aux wires), with an `ArithmetizationCost` ledger counting the mults/aux-witnesses of each. That
is the paradigm mismatch in a sentence: **Boolean/relational structure has no native field encoding,
so it is re-expressed either as one high-degree polynomial or as a wide flat gate-graph, and
quantification is paid for by unrolling.** A third symptom is *lossiness w.r.t. source syntax*: the
CCC lowering "cannot recover information already erased by `layout`" — two distinct beta-redexes share
one receipt (`IntensionalCCCInteractionDescriptorIR2.lean:17-22`). ember flagged this as known; it is
the one part of the compiler that is a genuine research seam rather than an engineering barnacle, and
the rest of this document is about the barnacles.

---

## 7. Honest verdict + phased picture

**Spectrum placement: (c), specifically "a real spine, split across two backends, with the deployed
backend hand-authored."** Not (a) — the clean spine does not currently reach the deployed AIR. Not
(b) — the IR is real and genuinely lowered-through on the logic surface, and the effect surface has a
proven general framework, so it is not merely "emitters beside an aspirational IR." It is the precise
in-between: **the compiler was built, then the deployed rail was authored by hand next to it, and the
two are stitched per-effect instead of fused.**

Evidence anchors: clean framework exists (`EffectCommit2.lean:1-63`, ~29 thin instances) ·
framework emits to retired rail (`Exec/CircuitEmit.lean:35-46`, `circuit/src/lean_descriptor_air.rs:3`)
· deployed rail is 76 hand-authored `EffectVmDescriptor2` (`EmitByName.lean:133,353`) · emitters are
one mechanical skeleton, 63/78 hand-rolling raw literals · `AirBuilder` real but adopted by 4/78
effect emitters (`AirBuilder.lean:28-32`) · logic→IR2 compilers real but additive-only
(`FiniteRelationalFOLDescriptorIR2.lean:1`).

**Phased refactor toward a full DSL/compiler (roughly swarmcycle-scaled):**

- **Phase 1 — Fuse the rails (highest leverage, ~1 swarmcycle).** Write
  `lower : EffectSpec2 → EffectVmDescriptor2` (via `AirBuilder`), retargeting `emittedEffect2` off
  the retired flat `EmittedDescriptor` onto the deployed `EffectVmDescriptor2`. Prove the deployed
  descriptor for one effect (start with a full-state one, transfer/setField) is now the *lowered*
  spec, not a hand-authored sibling. Payoff: the clean spine reaches the prover; one effect stops
  being two artifacts stitched by a `unify_*` lemma. **This is the phase that changes the answer from
  (c) toward (a).**

- **Phase 2 — Adopt `AirBuilder` across the 74 hand-rolling emitters (~1-2 swarmcycles, embarrassingly
  parallel).** Mechanical per-file: replace raw `.base (.gate <EmittedExpr>)` with `cgH (Head…)`, so
  `headToExpr_eval` discharges the `_zero_iff` lemmas uniformly; fold the two Automatafl `Head` copies
  in (the debt `AirBuilder.lean:28` already names). Payoff: the gate-bite proof obligation becomes
  boilerplate; the emitters shrink to (columns, `Head`s, lookups) data.

- **Phase 3 — Lift the descriptor skeleton to a builder (~1 swarmcycle).** A `descriptorOf`
  combinator that takes (name, columns, gates, lookups, PI pins, last-row fixes) and produces the
  `EffectVmDescriptor2` + the `emitVmJson2` golden + the refinement obligation — absorbing steps
  1,3,4,5,6 of the §4 skeleton. Payoff: ~50-70% of each membership emitter's lines vanish; only the
  gate polynomials remain, authored in `Head`.

- **Phase 4 — A real front-end (the DSL ember wants; larger, later).** Extend the `dregg_effect` macro
  (today conservation-only) so an effect *declaration* also names its touched set, guard predicate,
  and gate `Head`s, and *generates* the `EffectSpec2` + (via Phase 1's `lower`) the descriptor. This
  is where "turns/effects/verbs" become a genuine composable circuit-authoring language rather than a
  routed catalog. Prereq: Phases 1-3. The logic-arithmetization seam (§6) stays a separate research
  track and is out of scope for the front-end.

**Payoff of the whole arc:** the ~hundreds of `*Emit.lean` collapse toward *data* (columns +
polynomials) behind one lowering pass; witness gen is already uniform; the deployed AIR becomes the
*image of the spec* rather than a hand-authored sibling proven equal to it; and the front-end macro
becomes a real DSL over the same proved primitives. The tools to start (AirBuilder, the EffectCommit2
framework) already exist — they are on the shelf next to the work, not yet threaded through it.

---

*Method note: this is a structural read of HEAD's Lean sources + the Rust interpreter headers, not a
build. Counts are from filename/grep census (383 Emit files; 78 `*Emit.lean`; 76 deployed
descriptors; AirBuilder 7 import / 36 open / 15 call). The two-rail claim is verified at source:
`circuit/src/lean_descriptor_air.rs:3` self-labels the flat rail RETIRED, and `EmitByName.lean`
serves only `EffectVmDescriptor2`. The "logic compiler is real but additive" claim is verified by the
verbatim "standalone additive module; no integration imports are changed" in each `*DescriptorIR2`
header.*
