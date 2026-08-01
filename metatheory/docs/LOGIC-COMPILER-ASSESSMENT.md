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

---

# ⚑ PHASE 1 EXECUTED — 2026-08-01. The pass exists; the rails did NOT fuse, and the reason is the SOURCE.

*`Dregg2/Circuit/Emit/EffectLower.lean` (NEW, rooted in `Dregg2.lean`, `lake build` green,
`#assert_axioms`-clean on all ten theorems). This section supersedes §7's Phase-1 sketch on one
point: the sketch said retargeting `emittedEffect2` "is the single edit that fuses the two rails."
It is not. The edit is real and is named precisely in P1.4 — but fusing the rails needs a change to
`EffectSpec2` itself, and the sketch did not see that.*

## P1.1 — what was built

`lowerEffect : String → EffectSpec2 St Args → EffectVmDescriptor2` (`EffectLower.lean`), through
`AirBuilder`, in three stages:

- **`exprToHead`** — a real polynomial normalizer from `Circuit.Expr` (an arbitrary var/const/+/×
  tree) into `AirBuilder.Head` (`Σ coeff·∏cols + const`). `mulHead` distributes; `evalH_mulHead`
  and `evalH_exprToHead` are its proved semantics. This is the step the 63 hand-rolling emitters
  skip by writing the normal form by hand.
- **`lowerConstraint`** — `lhs = rhs` ↦ the residual head `lhs − rhs` emitted as `cgH`, so
  `headToExpr_eval` (`AirBuilder.lean:158`) discharges the gate-bite obligation once instead of
  per effect.
- **`lowerEffect`** — descriptor assembly over the framework's own 72-column layout, with a PI
  surface that REALIZES `WitnessExtract.PIBindsDigests` (`WitnessExtract.lean:54`) as actual
  `piBinding` pins rather than leaving it a carried `Prop`.

Two-sided faithfulness: `lowered_of_satisfied` is UNCONDITIONAL; `satisfied_of_lowered` carries the
deployed canonicality envelope, because `VmConstraint.holdsVm` asserts `body ≡ 0 [ZMOD p]` while
`Constraint.holds` is ℤ equality. That asymmetry is inherent to the rail change, not slack.

## P1.2 — ⚑ THE DIFFERENTIAL: **REFINEMENT-EQUAL, NOT BYTE-EXACT.** Measured, both sides.

`transferLoweredDesc` **is** `lowerEffect` applied to transfer's `EffectSpec2` — `rfl`
(`transferLoweredDesc_is_lowering`), for every carried digest `D`. So the numbers below are about
the general pass, not a lookalike.

| | lowered (the pass's output) | `transferVmDescriptor` (bare v1 `def`) | LIVE `transferVmDescriptor2R24` |
|---|---|---|---|
| trace width | **72** | 188 | **1874** |
| PI count | 7 | 42 | 50 |
| constraints | **11** (4 gate + 7 pi) | 36 (15 gate + 14 transition + 7 pi) | **663** (340 lookup · 294 window · 14 transition · 15 pi) |
| tables / hash sites / ranges | 0 / 0 / 0 | 0 / 4 / 2 | 6 / 0 / 0 |

Sources: `#guard`s in `EffectLower.lean` §4a/§5 (executed); `circuit/descriptors/
dregg-effectvm-transfer-v1.json`; the `transferVmDescriptor2R24` row of `circuit/descriptors/
rotation-v3-staged-registry.tsv`. **Byte-equality is REFUTED as a theorem**
(`lowered_json_ne_deployed_json`), not noted as a gap.

**What DOES hold — and it is the real result.** `transferLowered_refines_balanceMovement`: a
witness of the descriptor **the pass emitted** forces the complete declarative
`BalanceMovementSpec` — the same apex the hand-authored rung reaches — via
`effect2_circuit_full_sound`. Both polarities are toothed: `demoEnv_satisfies_lowered` (the
premise is inhabited, PI pins included) and `lowered_rejects_component_forge` (the emitted gate
REFUSES a forged component digest).

⚑ **It deliberately does NOT route through `Inst.Transfer.transfer_full_sound`.** That carries
`logHashInjective`, which `StateCommit.lean:251` PROVES FALSE at deployed BabyBear — a theorem
under it is vacuous at deployment, and `check-floor-baseline-preflight` refused the first draft of
this commit for exactly that. The keystone was PORTED (option (a), not the escape hatch) onto the
`_or_collides` side condition `¬ LogColl S.LH s'.log (t :: s.log)` — named, refutable, at the ONE
pair of logs the witness supplies — which `LogCommitRegrounded.noLogColl_of_inj` shows is implied
by the old carrier, so the ported statement is strictly STRONGER. Remaining portals
(`RestIffNoBal`, `Function.Injective D`, the canonicality envelope) are not on the refuted list.
So: **the lowering is sound; it is not a replacement for the deployed AIR.**

## P1.3 — ⚑ WHY, exactly. The gap is in `EffectSpec2`, not in the emitter.

`EffectSpec2` cannot express the deployed descriptor because it never held the content:

1. `Inst/transfer.lean:99` commits the whole 6-conjunct `admitGuardA` as ONE `propBit` column
   ASSERTED `= 1`. The deployed AIR COMPUTES its guard (the §11.7 15-bit borrow chain).
   **A `propBit` is a claim; the borrow chain is a proof.**
2. The commitment is an ABSTRACT `digest`/`RH`/`LH` (`EffectCommit2.lean:120,183`) — a carried
   portal, never an emitted hash site. The deployed AIR BUILDS `state_commit` from 4 ordered `H4`
   sites in-circuit.
3. `EffectSpec2` is SINGLE-ROW: no `transition`, no `boundary`, no `windowGate`.
4. `EffectSpec2` has **no vocabulary at all** for lookups, tables, or ranges.

None of these is a defect of `lowerEffect`. Each is absent from the source language.

## P1.4 — the serializer retarget, named precisely (NOT done here)

- **Boundary**: `emittedEffect2` (`EffectCommit2.lean:484`) and its four arity siblings —
  `emittedEffect2Dual` (`EffectCommit2Dual.lean:314`), `…Triple` (`EffectCommit3.lean:321`),
  `…Quad` (`EffectCommit4.lean:354`), `…Quint` (`EffectCommit5.lean:388`).
- **Edit 1 — imports.** `EffectCommit2.lean` gains `import Dregg2.Circuit.Emit.AirBuilder`.
  Verified acyclic: `DescriptorIR2.lean:39-46` imports `EffectVmEmit`/`Lookup`/`Heap`/
  `MapMerkleRoot`/`DeployedMapDenotation`/`MemoryChecking`/`UniversalMemory` and reaches
  `EffectCommit2` from none of them.
- **Edit 2 — the body.** `emittedEffect2 name E : EffectVmDescriptor2 := lowerEffect name E`
  (move `lowerEffect` in, or keep it in `EffectLower` and import it).
- **Edit 3 — the theorem that DOWNGRADES.** `emitEffect2Faithful` (`EffectCommit2.lean:489`) is a
  free `↔`. Its replacement is the §3 PAIR: `lowered_of_satisfied` (free) plus
  `satisfied_of_lowered` (canonicality envelope). **The retarget costs a biconditional.** Any
  write-up that reports the retarget without reporting this is over-claiming.
- **Edit 4 — the 27 artifacts.** The `<x>Emitted : EmittedDescriptor` defs in `Inst/*.lean` and
  `Witness/*.lean` change type to `EffectVmDescriptor2`; their `#guard <x>Emitted.name == …` pins
  survive verbatim (the field exists on both records).
- **Edit 5 — the registry.** `effectEmitRegistry` (`EffectEmitRegistry.lean:132`, 32-way name
  dispatch) and `TurnEmit.defaultDescriptorLookup` (`TurnEmit.lean:166`) re-type. This is the
  retarget's real scope: **the whole `TurnEmit` refinement spine currently sits on the retired
  rail.**
- **Edit 6 — the consumers.** ~20 statements of the form `satisfiedEmitted (emittedEffect2 …)`
  (`WitnessExtractPerEffect.lean` ×11, `TurnEmit.lean`, `EffectRefinement.lean:87`,
  `WitnessExtract.lean:192`, `EffectEmittedRefinement.lean:107`, `LogCommitCutoverCheck.lean:391`)
  restate over `Satisfied2` / the row denotation.
- **Edit 7 — Rust, and DELETE rather than keep both.** `circuit/src/lean_descriptor_air.rs`
  becomes dead. It already is: all 10 `LeanDescriptorAir` references in `circuit/src/` are inside
  that one file, against 59 files touching `descriptor_ir2`/`Ir2Air`. Greenfield law: delete it.

## P1.5 — generality readout over the deployed set (this is what sizes Phase 2)

Measured over all 76 checked-in `circuit/descriptors/by-name/*.json` by constraint kind. The
capability ladder, cumulative:

| emitter capability | reach | Δ |
|---|---|---|
| gate + first-row PI — **what `lowerEffect` emits today** | **12 / 76** | +12 |
| + last-row PI | 12 / 76 | +0 |
| + boundary first/last | 12 / 76 | +0 |
| + ranges | 12 / 76 | +0 |
| + `windowGate` | 25 / 76 | +13 |
| + **lookup + tables** | **76 / 76** | **+51** |
| + hash sites | 76 / 76 | +0 (**no by-name descriptor uses one**) |

The 12 reachable today: the 10 automatafl descriptors, `field-delta-result-range.json`,
`quantified-absence.json`. **51 of 76 carry a lookup/table leg** and 50 carry row-coupling
(boundary / window / last-row PI).

**The sizing conclusion, and it inverts §7's Phase 2.** §7 proposed "adopt `AirBuilder` across the
74 hand-rolling emitters" as the next move. That is worth doing, but it is not what unblocks the
compiler: the emitter side is mechanical in every one of these kinds, while **the source side
cannot say them at all.** One capability — a lookup/table leg on `EffectSpec2` — moves reach from
25/76 to 76/76. Widening the SOURCE is Phase 2; the `AirBuilder` sweep is bookkeeping that can run
in parallel.

Transfer is not in the by-name 76 at all (its live face is `EmitRotationV3.lean:135` →
`AvailWireMembers.transferV3AvailWire`), and its 340 lookups + 294 window gates put it firmly in
the +51 bucket.

## P1.6 — the honest verdict on the prior lane's hypothesis

*"The two rails are structurally disjoint"* — **CONFIRMED at transfer, and now with numbers.** They
share a denotation target (`BalanceMovementSpec`) and nothing else: 11 constraints against 663, and
no lookup, table, range, hash site, transition, boundary or window gate in common — because
`EffectSpec2` has no name for any of them. The spine is real, the pass is real, and the pass now
PRODUCES a live-rail descriptor rather than modelling one. What it produces is a sound but
arithmetic-free skeleton, and closing that is a source-language change.

---

# ⚑ PHASE 2 EXECUTED — 2026-08-01. The SOURCE was widened; one deployed descriptor is now BYTE-EXACT.

*NEW `Dregg2/Circuit/EffectAirIR.lean` (the vocabulary) + `EffectSpec2` gains ONE defaulted field
`air` + `Dregg2/Circuit/Emit/EffectLower.lean` extended. `lake build` green over the whole tree,
`#assert_axioms`-clean on all 29 pinned theorems (25 in `EffectLower`, 4 in `EffectAirIR`) with 57 executed `#guard`s. This section executes P1.5's own conclusion —
"widening the SOURCE is Phase 2; the `AirBuilder` sweep is bookkeeping".*

## P2.1 — what was added, in the priority order the measurement demanded

`EffectAirIR.EffectAir`, carried by `EffectSpec2.air := {}` (defaulted, so all ~29 existing
instances compile unchanged and lower byte-identically — `lowerEffect_air_empty`, a theorem over
ALL specs, not a spot check):

| capability | the leg | measured demand |
|---|---|---|
| **(a) lookup + declared tables** | `AirLeg.lookup (LookupLeg)` + `EffectAir.tables` | **+51 / 76** |
| (b) ranges | `EffectAir.ranges : List RangeLeg` | +0 on the by-name set; transfer's v1 carries 2 |
| (c) window / row-selected gates | `AirLeg.window (WindowLeg)` = `TableAirIR.RowSel` × `WindowExpr` | +13 / 76 |
| (d) boundary + last-row PI | `AirLeg.pin (PiPinLeg)` carrying `VmRow` | +0 alone, required by (a)+(c) descriptors |

**It is `TableAirIR`'s vocabulary, reused, not re-derived** — `RowSel`, `WindowExpr`, the
multiplicity EXPRESSION on a lookup, and `BusOp` (`.query`/`.provide`/`.receive`/`.send`), plus its
refusal of a `nxt` read outside `.transition`.

⚑ **The legs are ONE ORDERED LIST (`AirLeg`), not four parallel ones.** The target's `constraints`
is a single ordered array and the deployed descriptors interleave (`merkle-membership-depth2.json`
is lookup · lookup · gate · pi_binding · boundary); four parallel lists could only ever emit
gates-then-lookups-then-windows-then-pins. Measured: **4/76 byte-reachable with parallel lists,
8/76 with the ordered list.** This was caught by measuring the pass's own first design, and fixed
in it — the same class of defect the phase exists to close, one level down.

## P2.2 — ⚑ THE REFUSAL, which is the load-bearing half

`EffectAir` can SAY strictly more than the deployed MAIN rail can take, and the three gaps are
named rather than dropped:

1. **Non-unit multiplicity.** `DescriptorIR2.Lookup` is `⟨table, tuple⟩` — no `mult` field, because
   `Ir2Air::Main` pushes every lookup at multiplicity 1.
2. **The serving side.** `.provide`/`.receive`/`.send` are the shared-TABLE side of a bus.
3. **`nxt` outside `.transition`.** Under `.all` this is TableAirIR's refusal verbatim (p3's `next`
   on the last row is the WRAP row); under `.first`/`.last` the reason is stronger and
   rail-specific — those lower to `VmConstraint.boundary`, whose body reads `env.loc` only.

A leg the rail cannot take lowers to `refuseConstraints` — the UNSATISFIABLE pair
`boundary first (1) , boundary last (1)` — **never to silence.** Dropping the leg is the fail-open
move: a descriptor missing a constraint accepts strictly MORE and no byte-golden can see the loss
(`TableAirIR.rowHolds_of_sublist` is that direction as a theorem). It is a `.boundary` PAIR and not
a `.gate` because `holdsVm_gate_true` makes a `.gate` vacuous on the last row, so `gate (const 1)`
would be a refusal a one-row trace satisfies — a refusal that cannot go red.
`EffectAir.mainRailOk` is the DECIDABLE verdict, `#guard`-pinned at both poles.

## P2.3 — ⚑ THE FALSIFIABLE RUNG: byte-exact, Δ = 0 on every row

**`dregg-dfa-routing-table::exact-public-v1`** (`circuit/descriptors/by-name/dfa-routing-table-exact-public-v1.json`,
Lean-side `Emit/DfaRoutingTableEmit.lean:389`). Chosen because its gap was PURELY vocabulary: one
table-generic `lookup` against a declared `exactPublicRows` table, one `.transition` `window_gate`,
a FIRST-row and a LAST-row PI pin — every one in the +51/+13 buckets, and no guard to collapse and
no commitment portal, i.e. nothing semantic.

| | `lowerAir dfaAir` (the pass) | deployed | Δ |
|---|---|---|---|
| trace width | 3 | 3 | **0** |
| PI count | 2 | 2 | **0** |
| constraints | 4 | 4 | **0** |
| tables / hash sites / ranges | 1 / 0 / 0 | 1 / 0 / 0 | **0** |
| `emitVmJson2` bytes | — | — | **identical** |

`DfaRung.dfaLowered_eq_deployed : dfaLowered = demoRoutingDesc` is **`rfl`** — the same term, not a
sibling proven equivalent. The byte-golden is pinned against the literal transcribed from the
checked-in JSON (an INDEPENDENT source, not the Lean emitter's own def). Both polarities ride on
the compiler's output rather than on the hand-written twin: `dfaLowered_witness` (the deployed
witness satisfies it), `dfaLowered_rejects_offtable` (an off-table transition is refused), and
`dfaLowered_refines_classify` (the deployed GENERAL refinement — exposed `final_state` IS
`classifyFrom` of the read word — is a theorem about the pass's output).

⚠ Reached through `lowerAir`, not `lowerEffect`: this descriptor is not a full-state effect and has
no digest wires, so bolting the framework's `PIBindsDigests` surface on would emit a descriptor
nobody deployed. The two entry points share the normalizer, the leg lowerings and the emission
order and differ ONLY in that surface (`assemble`).

**And the refusal on this very rung.** Re-authoring the same lookup on the SERVING side is a
one-token edit; the emitted descriptor then has 5 constraints instead of 4, is `≠` the deployed
one, and `dfaLoweredServed_unsatisfiable` proves it has **no witness at all** — for any hash, any
boundary, any non-empty trace.

## P2.4 — the generality readout, RE-MEASURED by P1.5's method

Method reproduced exactly (a descriptor is reachable iff every constraint kind it uses, plus
tables / hash sites / ranges, is in the level's vocabulary). The first six rows are P1.5's,
recomputed and **identical to the digit** — including the same named 12 — which is what makes the
last row comparable:

| emitter capability | reach | Δ |
|---|---|---|
| gate + first-row PI | 12 / 76 | +12 |
| + last-row PI | 12 / 76 | +0 |
| + boundary first/last | 12 / 76 | +0 |
| + ranges | 12 / 76 | +0 |
| + `windowGate` | 25 / 76 | +13 |
| + lookup + tables | 76 / 76 | +51 |
| + hash sites | 76 / 76 | +0 |
| **PHASE 2 — `lowerAir`'s ACTUAL emission set** | **76 / 76** | **+51 from 25/76** |

**Generality moved 25/76 → 76/76 (MEASURED, same method).** Zero of the 76 are now unreachable for
want of a word.

## P2.5 — ⚑ THE NUMBER THE KIND LADDER FLATTERS, and why it is not a deferral

Kind coverage answers "can the source SAY this descriptor's kinds". It does not answer "could the
pass emit these bytes". Measured over the same 76:

    kinds expressible by `lowerAir`                        76 / 76
    + every `gate` body already in builder normal form      8 / 76   ← BYTE-reachable today
    gate bodies NOT in the normal form the pass emits   12745 / 13983

The residual is a RENDERING difference, not a semantic one — `headToExpr_eval` proves the
normalized body means what the source meant. **And there is no form to normalize TO**: across the
76, **37 descriptors render a unit coefficient as `mul(const 1, x)`, 58 render it as a bare `x`,
and 25 carry BOTH shapes inside one descriptor.** The hand-authored set is not internally
consistent, so byte-agreement with it is not a well-posed target for any canonical renderer.

So the greenfield answer is the right one and is not a hedge: **the deployed descriptors are the
thing to RE-EMIT from the compiler, not to imitate** — a by-name JSON re-emission plus the VK epoch
it implies, ordinary work, held out of this commit only because the descriptor artifacts and the
rotation are another lane's, not because it is expensive.
⚠ The move deliberately NOT made: bending `AirBuilder.headToExpr` toward one of the two shapes. It
buys 8/76 → 21/76 (measured) while making the shared builder mimic an inconsistent target and
breaking the goldens of the 10 emitters that already ride the current form. Wrong direction of fit.

## P2.6 — what still resists: SYNTAX vs SEMANTICS, separated

**Closed by this phase (vocabulary).** Lookups against declared tables, ranges, `.transition`
continuity, first/last boundary fixes, last-row PI pins. All five were unsayable; §8 exhibits one
deployed descriptor reached byte-exact through them.

**NOT closed, and no amount of syntax closes them (semantics).** These are transfer's, which is why
§5's byte-refutation stands untouched — `transferLoweredDesc` still lowers a spec whose `air` is
EMPTY, and its numbers are unchanged at 72 / 7 / 11 against the live 1874 / 50 / 663:

1. **The collapsed guard.** `Inst/transfer.lean:99` commits the 6-conjunct `admitGuardA` as ONE
   `propBit` asserted `= 1`. A `RangeLeg` does not turn that into the deployed 15-bit borrow chain;
   what is missing is that the spec never DECOMPOSES the guard into arithmetic. **A `propBit` is a
   claim; the borrow chain is a proof.** The repair is a change to what the spec SAYS.
2. **The commitment as a carried portal.** `EffectCommit2.lean:120,183` carries `digest`/`RH`/`LH`
   as abstract functions; the deployed AIR builds `state_commit` from 4 ordered `H4` sites
   in-circuit. `EffectAir` deliberately has NO hash-site leg — one would let a spec declare a site
   while `effectStateCommit2` still reads the portal, i.e. two commitments that agree today and
   disagree later. The repair is that `Surface2` must denote an emitted site. ⚠ Measured, and it is
   why the omission costs nothing on the deployed set: **no by-name descriptor uses a hash site.**
3. **Single-row-ness of the ENCODER.** `WindowLeg` lets a spec ASSERT across two rows, but
   `encodeE2` still produces ONE `Assignment`. A spec can now state a continuity gate and cannot
   yet state the multi-row witness satisfying it. `TableAirIR.Coherent` is the shape of the missing
   hypothesis; the encoder-side counterpart is not built.
4. **Multiplicity / serving side.** Sayable by the source, REFUSED by the main rail, legal on the
   `TableAir` rail. Neither a vocabulary gap nor a spec-semantics gap — a rail seam, made a loud
   refusal instead of a silence (P2.2).

## P2.7 — the honest verdict

Widening the source moved the reachable KIND coverage of the deployed set **25/76 → 76/76** and
produced **the first deployed descriptor a general `EffectSpec2`-vocabulary pass emits BYTE-EXACT**
— `DfaRoutingTableEmit`'s hand-written `VmConstraint2` list-literals (`:112-137`) are now derivable
output rather than authored input. Byte reach across the whole set is **8/76**, and it is bounded
by the deployed set's own rendering inconsistency, not by the source language. Transfer moved by
zero, which is correct: it was never blocked on syntax, and P1.3's four root causes reduce to
three, all semantic.

---

# PHASE 3 — ⚑ THE FIRST RAIL FUSION (2026-08-01)

**The gate: is a deployed descriptor now COMPILER-AUTHORED with the hand-written copy deleted, and
did any byte move? YES, and NO.**

## P3.1 — what changed

`Dregg2/Circuit/Emit/DfaRoutingTableEmit.lean` §2 used to define the deployed
`dregg-dfa-routing-table::exact-public-v1` family as a hand-written `EffectVmDescriptor2` literal:
four `VmConstraint2` `def`s (`transitionLookup`, `continuityWindow`, `b1InitialPin`, `b2FinalPin`)
and a `constraints := [...]` list. It now reads

    def dfaAir (tbl : List (List Nat)) : EffectAir := { tables := …, legs := [.lookup …, .window …, .pin …, .pin …] }
    def tableRoutingDesc (name : String) (tbl : List (List Nat)) : EffectVmDescriptor2 :=
      EffectLower.lowerAir name TRT_WIDTH TRT_PI_COUNT [] (dfaAir tbl)

**The four `VmConstraint2` `def`s and the literal record are DELETED** — 14 lines of deployed-IR
authorship (the four `def`s with their docstrings) plus the 8-line hand-written
`EffectVmDescriptor2` record, replaced by an 8-line `EffectAir` source block. What is hand-written in this
file is now SOURCE (`AirLeg` / `RowSel` / `PiPinLeg` / a `WindowExpr` body); every `VmConstraint2`
in the shipped descriptor is emitted by `lowerLookupLeg` / `lowerWindowLeg` / `lowerPiPinLeg`.

Phase 2's `DfaRung.dfaLowered_eq_deployed : dfaLowered = demoRoutingDesc := rfl` is what made this
safe — and it is DELETED too, along with the four theorems that restated the witness, the canary
and the refinement on the second copy. With one object they would be `P = P`. ⚑ **A `rfl` between
the compiler's output and a hand-written twin is evidence only while the twin exists; cashing it
means deleting the twin, not keeping the theorem.**

## P3.2 — the back end moved DOWN, and the import edge is the evidence

`EffectLower.lean` imports `Inst/transfer.lean`, `EffectCommit2` and `WitnessExtract` for §4–§6's
differential. A deployed descriptor cannot import that and stay cheap, and it must import the
compiler to be defined by it. So the back end — the normalizer, `lowerConstraint`, the four leg
lowerings, `refuseConstraints`, `assemble`, `lowerAir` — is now
`Dregg2/Circuit/Emit/EffectLowerCore.lean` (`AirBuilder` + `EffectAirIR` + `DescriptorIR2`, nothing
else), in the SAME namespace so no name moved and no consumer changed its `open`.

    EffectLowerCore  →  DfaRoutingTableEmit  →  EffectLower
    (the compiler)      (a deployed descriptor)   (the transfer differential)

That edge is what makes the fusion STRUCTURAL rather than a claim: a descriptor below the compiler
cannot hand-write its own constraints, because the constraints are the compiler's output type.

## P3.3 — the gate, MEASURED

* **Bytes: ZERO moved.** `emitVmJson2 demoRoutingDesc` — now the compiler's output — is checked by
  the file's own `#guard` against the 587-byte golden transcribed from
  `circuit/descriptors/by-name/dfa-routing-table-exact-public-v1.json`, and the golden equals the
  committed file byte-for-byte: **sha256 `31bea51b322bb38fa7167eaf3ce69dd280728b012bdac6b9fd7b531b62e5c97a`**
  on both sides (the file carries no trailing newline; the three hashes — Lean literal, file
  newline-stripped, file as-is — agree). Nothing re-emits, nothing re-genesises, no VK rotates.
* **Guards: all green.** Every `#guard` and `#assert_axioms` in `DfaRoutingTableEmit` and in the six
  consumer modules elaborates. New pins replace the old unfolding: `tableRoutingDesc_constraints`
  / `_tables` / `_ranges` / `_shape`, all `rfl`, are the compiler's emission checked against the
  deployed IR-v2 shape transcribed from `circuit/src/descriptor_ir2.rs`. A change to a leg
  lowering, to the leg ORDER, or to `assemble` goes RED there — one module above the compiler,
  where the descriptor is deployed from.
* **No new floor carrier**: `scripts/check-floor-baseline-preflight.sh` — OK, 23 floor names,
  1967 baseline entries, no unbaselined carrier.

## P3.4 — the honest fusion readout

**Compiler-sourced deployed descriptors: 1 of 76.** Not 8. The 8/76 of P2.5 is BYTE-REACHABILITY —
"the pass could emit these bytes" — and reachability is not authorship. Exactly one by-name
descriptor is now DEFINED as `lowerAir`/`lowerEffect` output with its hand-written body deleted;
the other 75 are still hand-authored `VmConstraint2` literals that a compiler run merely agrees
with. ⚑ The number that matters for house law #1's endpoint is the authorship one, and it is 1/76.

**Why this one was first.** It carries NO plain `gate` at all (lookup + window + two pins), so it
asked nothing of `headToExpr` and fused at zero byte cost. That property is measurable directly off
the committed artifacts, and doing so turns P2.5's byte-reach figure from a ladder number into a
NAMED LIST — below.

**Next cheapest — MEASURED, not guessed.** A descriptor fuses at ZERO byte cost exactly when it
asks nothing of the `Head` normalizer, i.e. when it carries no `gate` constraint: lookups, window
gates, boundaries and PI pins are all STRUCTURAL lowerings (`lowerLookupLeg` copies the tuple
through `emitExpr`; `lowerWindowLeg`'s `.first`/`.last` uses `windowToLocal?`, not `exprToHead`).
Counting `t` fields across all 76 committed `circuit/descriptors/by-name/*.json`:

    kinds present:  gate 68 · pi_binding 69 · lookup 51 · boundary 37 · window_gate 29
    GATE-FREE:      8 / 76   ← the zero-byte-cost fusion class, and it IS the 8/76 of P2.5

The eight, with `(gate, boundary, window_gate, lookup, pi_binding, total)`:

    dfa-routing-table-exact-public-v1     (0, 0,   1,    1,    2,    4)   ← FUSED, this phase
    mina-fixture                          (0, 0,   2,    0,    2,    4)
    poseidon2-hash-arity2                 (0, 0,   0,    1,    3,    4)
    turn-chain-binding                    (0, 3,   6,    1,    4,   14)
    bound-presentation                    (0, 0,   0,    1,   20,   21)
    guarded-hiding-span-m0-wide-…-blind5  (0, 0,   0,    3,   24,   27)
    bridge-action                         (0, 0,  26,    0,   26,   52)
    shielded-whole-note-swap-substrate-v1 (0, 399, 0, 1105,  100, 1604)

⚑ **The two counts coincide at 8 and the mechanism explains why — but read the label.** P2.5's
8/76 is a byte-reach measurement; the gate-free 8/76 above is a fresh count of `t` fields in the
committed JSON. That they are the SAME EIGHT is an INFERENCE from the lowering code (only `.gate`
goes through `exprToHead`; every other leg is structural), not a re-measurement, and only
`dfa-routing-table-exact-public-v1` has been byte-confirmed — by fusing it. For the other seven,
"the golden survives" is a PREDICTION with a stated mechanism, and the way to settle it is to fuse
the next one, not to assert it here. Ordered by source size, the next three are `mina-fixture` (2 window gates + 2 pins — a two-leg `EffectAir`),
`poseidon2-hash-arity2` (1 lookup + 3 pins), and `turn-chain-binding` (14 constraints across four
kinds, the first to exercise `.first`/`.last` boundary legs at scale). `bridge-action` (52) and
`bound-presentation` (21) are mechanical repeats. `shielded-whole-note-swap-substrate-v1` is 1604
constraints and is the one that will need the source to GENERATE legs rather than list them — which
is the next real capability question, not a transcription question.

⚠ Everything OUTSIDE those eight moves bytes when fused, because its gate bodies re-render through
`exprToHead`. 68 of 76 carry at least one `gate`. For those the greenfield answer is a re-emit of
the JSON (and the VK epoch it implies), not a smaller fusion — and NOT bending the builder.

## P3.5 — what a reader six weeks out needs to know broke

* `DfaRoutingTableEmit.transitionLookup`, `.continuityWindow`, `.b1InitialPin`, `.b2FinalPin` — GONE.
  Use `mem_transitionLookup` / `mem_continuityWindow` / `mem_b1InitialPin` / `mem_b2FinalPin`,
  whose STATEMENTS now carry the emitted shape.
* `simp only [tableRoutingDesc]` no longer unfolds to a constraint list. Use
  `tableRoutingDesc_constraints` / `_tables` / `_ranges`. Updated in
  `DfaRoutingSubsetTableCost`, `TinyAutomataCompose`, `TinyAutomataSatisfiable`.
* `EffectLower.DfaRung.dfaAir` / `.dfaLowered` / `.dfaLowered_eq_deployed` / `.dfaLowered_json_eq_deployed`
  / `.dfaLowered_witness` / `.dfaLowered_rejects_offtable` / `.dfaLowered_refines_classify` — GONE.
  The source block is `DfaRoutingTableEmit.dfaAir`; the object is `demoRoutingDesc`; the theorems
  are `routeWit_satisfies`, `badTrace_not_satisfied`, `tableRouting_refines_classify`.
  §8b's refusal rung (`dfaAirServed` / `dfaLoweredServed_unsatisfiable` / `_ne_deployed`) SURVIVES —
  it has no counterpart there and is the one thing a byte-golden cannot see.
* **Nothing re-emits and nothing re-genesises.** The descriptor bytes, the VK epoch and the
  registry are untouched — which is the whole claim.

---

# ⚑ PHASE 3 EXECUTED — 2026-08-01. The compiler is now the SOURCE for a batch of deployed
descriptors, and the corpus has a normal form.

*NEW `Dregg2/Circuit/Emit/AirNormalForm.lean` (the invariant + its decidable verdict) and NEW
`scripts/measure-descriptor-normal-form.py` (the measurement, committed so `N/76` is a command
rather than a claim). Ten by-name emitters re-authored: their hand-written `VmConstraint2` list
literals are DELETED and their descriptors are `EffectLower.lowerAir` of an `EffectAir` source.
This section executes P2.5's own conclusion — "the deployed descriptors are the thing to RE-EMIT
from the compiler, not to imitate".*

## P3.1 — ⚑ THE CANONICAL NORMAL FORM, chosen and stated once

`AirNormalForm.lean`'s header is the corpus invariant; this is its summary. Every arithmetic body
of a compiler-authored descriptor — `.gate`, `.boundary`, `windowGate` — is what a polynomial HEAD
lowers to:

    body ::= atom | add(body, atom)          -- LEFT-nested spine, source order
    atom ::= mul(const c, prod) | const k    -- EVERY term carries its coefficient
    prod ::= leaf | mul(prod, leaf)          -- LEFT-nested; leaf = var / loc / nxt

**The load-bearing decision: a unit coefficient renders `mul(const 1, x)`, never bare `x`.** Three
reasons, in weight order:

1. It is what `AirBuilder.headToExpr` produces, and P2.5 already measured the alternative — bending
   the shared builder toward the bare form buys 8/76 → 21/76 while breaking the ten emitters whose
   committed goldens ride the current form. Wrong direction of fit, and the goal explicitly forbids
   touching `headToExpr` to chase bytes.
2. **Uniformity is what makes the invariant DECIDABLE by a two-line predicate.** If bare leaves were
   legal atoms, `add(var 5, var 6)` — a body whose coefficients were *dropped* — would be
   indistinguishable from one that meant `1·x₅ + 1·x₆`. Every term carrying its coefficient is what
   turns "is this the compiler's output" into a question a machine answers.
3. ⚑ **The Rust interpreter is INDIFFERENT, and this was checked at the source, both legs.**
   `LeanExpr::eval_expr` (`circuit/src/lean_descriptor_air.rs:127`) sends `Mul` to a field multiply
   and `Const(1)` to `F::one()` — the evaluated polynomial is identical. `LeanExpr::degree` (`:116`)
   is `Const => 0`, `Var => 1`, `Mul => sum`, so `mul(const 1, x)` has degree **1**, exactly as bare
   `x` does; `WindowExpr::degree` (`descriptor_ir2.rs:742`) is the same function. `Ir2Air::Main`'s
   `max_constraint_degree` returns `None` (`descriptor_ir2.rs:2829`) and lets p3's symbolic analysis
   infer the bound from that same algebra. **So the FRI blowup, and therefore the VK geometry, do
   not move.** The rendering costs bytes and nothing else.

Three further rules the shape does not by itself say:

* **No like-term combination, no reassociation, no reordering.** The head is exactly what
  `exprToHead` built, in source order — so the emitted object stays a transcription of what the
  author wrote and a source edit's byte-diff stays local.
* **A zero head-constant is ELIDED; a zero-coefficient TERM the source wrote is NOT.** Dropping a
  term removes a column reference, which is the fail-open direction and invisible to a byte-golden.
* ⚑ **…but the normalizer does not INVENT one.** `EffectLowerCore.mulHead` now guards its two
  constant cross-products on a nonzero constant. Unguarded, the one degree-2 gate in the batch
  (`predicate-arith-neq`'s `DIFF · DIFF_INV = 1`) distributed to the genuine `1·DIFF·DIFF_INV`
  **plus a spurious `0·DIFF` and `0·DIFF_INV`** — terms no source wrote, which would have landed in
  the wire bytes of every product gate the compiler emits. `evalH_mulHead` still holds
  unconditionally: the dropped branches are exactly the ones whose value is `0`.

**What the invariant deliberately does NOT cover: LOOKUP TUPLES.** A tuple is not a polynomial
asserted to vanish; it is the identity of the queried row, and the chip bus is keyed on the bare
shape. `AirNormalForm.liftTuple` + `liftTuple_emit` let a descriptor feed its EXISTING
`chipLookupTuple*` builder to the compiler and proves the round trip lands on the same bytes — which
is why re-emission moved only these descriptors' GATE and BOUNDARY bytes.

**And it is a gate, not a paragraph.** `AirNormalForm.normalFormOk : EffectVmDescriptor2 → Bool` is
the decidable verdict, `#guard`-pinned at BOTH poles in `§4a` (a bare-unit body and a right-nested
spine are REFUSED, with `demoBareUnit_same_polynomial` proving the refused body means the same
thing) and once per re-emitted descriptor at its author. `headToExpr_isNormal` and
`wHeadToWindow_isNormalW` make it true BY CONSTRUCTION on both rails, for every head.

⚑ `AirBuilder.Head` is over COLUMNS and cannot name a next-row leaf, so a window/boundary body had
no canonical renderer at all — a re-emitted descriptor mixing a Head-normalized gate with a
hand-shaped boundary would have reproduced, inside the compiler's own output, exactly the
inconsistency P2.5 measured in the hand-authored corpus. `AirNormalForm.WHead` closes that: same
shape, same rules, leaves widened to `loc`/`nxt`, with `wHeadToWindow_eval` as its meaning bridge.

## P3.2 — ⚑ WHAT IS NOW COMPILER-AUTHORED, and WHAT RE-EMITS. Say it loudly.

**Ten deployed by-name descriptors.** For each, the `EffectVmDescriptor2` is now literally
`EffectLower.lowerAir <name> <width> <piCount> [] <air>` and the hand-written `VmConstraint2`
list-literal is **DELETED** (not kept beside — greenfield law). The gates are authored as
EQUATIONS in `Circuit.Expr`; turning `lhs = rhs` into a canonical vanishing polynomial is the
compiler's job, not the author's.

| descriptor (`circuit/descriptors/by-name/…`) | Lean author | what moved |
|---|---|---|
| `merkle-membership-depth2.json` | `MerkleMembershipEmit` | gate + last-row boundary |
| `attested-fact-membership.json` | `AttestedFactMembershipEmit` | gate + last-row boundary |
| `blinded-membership.json` | `BlindedMembershipEmit` | gate + last-row boundary |
| `presentation-freshness.json` | `PresentationEmit` | 2 gates + 2 last-row boundaries |
| `predicate-arith.json` (`≥`) | `PredicatesArithmeticEmit` | 2 gates |
| `predicate-arith-gt.json` | `PredicatesGtEmit` | 2 gates |
| `predicate-arith-le.json` | `PredicatesLeEmit` | 2 gates |
| `predicate-arith-lt.json` | `PredicatesLtEmit` | 2 gates |
| `predicate-arith-neq.json` | `PredicatesNeqEmit` | 3 gates (one DEGREE-2) |
| `predicate-arith-inrange.json` | `PredicatesInRangeEmit` | 3 gates |

**Every moved artifact, named:**

* **The 10 by-name JSONs above.** They are regenerated by `scripts/emit-descriptors.sh` from
  `EmitByName.lean`; each descriptor's `#guard emitVmJson2 <desc> == "<literal>"` in its authoring
  module is the byte pin, and those literals were replaced with the compiler's output.
* **`circuit/descriptors/PROVENANCE.json`** — the `by_name_sha256` entry of each of the 10.
* **Two Rust `GOLDEN_JSON` literals** that embed a descriptor's bytes verbatim rather than
  `include_str!`-ing the artifact: `circuit-prove/tests/merkle_membership_emit_gate.rs:41` and
  `circuit-prove/tests/presentation_emit_gate.rs:59`. Both updated.
* **NOTHING ELSE.** Measured, not assumed: no `*_FP` constant in any of the five `RUST_FP_FILES`
  (`effect_vm_descriptors.rs`, `cap_delegation_nonamp_descriptor.rs`, `cap_reshape_descriptor.rs`,
  `bilateral_aggregation_air.rs`, `lean_descriptor_air.rs`) names any of these ten; every other
  consumer reaches them through `descriptor_by_name.rs`'s `include_str!`, which re-reads the file.

**Does a VK epoch follow? NO — and this is the one claim in the section that needed checking rather
than assuming.** A descriptor's bytes feed the AIR fingerprint, and a fingerprint change re-keys the
recursive VK. But **none of these ten is a member of the rotation registry** — they are the
`descriptor_by_name` predicate-dispatch surface, not `rotation-v3-staged-registry.tsv`, and no
`*_FP` constant pins them. What changes for a verifier is the *sha256 of the artifact it loads*,
which `PROVENANCE.json` records and `--verify-provenance` checks. **A rebuild, not a re-genesis.**
What now REFUSES to load: nothing silently — a stale copy of any of the ten fails
`scripts/check-descriptor-drift.sh` (Lean re-derives and diffs) and `--verify-provenance` (sha
mismatch), both loudly and by name.

## P3.3 — ⚑ THE GATE THAT DID NOT WEAKEN: every `_zero_iff` re-established over the COMPILED object

Re-emission changes bytes. It must not change semantics, and "the theorem still compiles" is not
evidence of that unless the theorem is about the NEW object. The discipline used, at every one of
the ten:

1. **The theorem STATEMENT is literally unchanged.** `continuity_body_zero_iff`,
   `c3_body_zero_iff`, `c5_body_zero_iff`, `c5Lo/​c5Hi_body_zero_iff`, `cNz_body_zero_imp_ne`,
   `diffBind_body_zero_iff`, `bound_body_zero_iff` — every one reads exactly as before. What moved
   is the DEFINITION of the body it quantifies over: from a hand-written `EmittedExpr` literal to
   `AirNormalForm.gateBody <src>`, the compiler's rendering. A reader diffing the file sees the
   obligation preserved and the object replaced, which is the direction that cannot hide a loss.
2. **The proofs now run through the generic tooth.** `AirNormalForm.gateBody_zero_iff` says the
   compiled body vanishes EXACTLY when the source equation holds, for every constraint — proved
   once, from `headToExpr_eval` + `evalH_constraintHead`, instead of once per descriptor by `omega`
   on a hand-written tree.
3. **`<desc>_constraints : <desc>.constraints = [<the named constraints>] := rfl`** at each
   descriptor. Not "equivalent" — the SAME TERM. So every downstream statement that quantifies over
   `<desc>.constraints` (the refinement rungs in `MerkleMembershipRefine` / `MerkleMembershipRung2`,
   the witness and forgery canaries) is, unchanged, a statement about the compiler's output.
4. **`#guard normalFormOk <desc> == true`** at each descriptor — the corpus invariant decided on the
   emitted object, a gate that goes red the moment a hand-shaped body re-enters.
5. **The byte pin stayed a pin.** Each module keeps its `#guard emitVmJson2 <desc> == "<literal>"`.
   The literal is the only thing that moved, and it moved to the compiler's output.

⚠ **No descriptor was re-emitted whose obligations could not be re-established.** The ones left
hand-written are named in P3.5, with the reason.

## P3.4 — RE-MEASURED, with the script committed this time

⚠ **Phase 2's byte-reachability number was produced by a script nobody committed**, so it could not
be re-derived and this phase could not confirm it moved. `scripts/measure-descriptor-normal-form.py`
is that measurement, committed — `N/76` is now a command. It implements the same predicate the Lean
side decides (`AirNormalForm.isNormal` / `isNormalW`), in Python, over the checked-in artifacts.

It answers TWO questions, and the difference matters:

| | before Phase 3 | after Phase 3 |
|---|---|---|
| **whole invariant** — every `gate` + `boundary` + `window_gate` body canonical | **3 / 76** | **13 / 76** |
| Phase 2's question — every `gate` body in builder normal form | **9 / 76** | **19 / 76** |
| arithmetic bodies not canonical (whole invariant) | 18345 / 18821 | 18321 / 18821 |
| gate bodies not in builder normal form (Phase 2's count) | 13515 / 13983 | 13496 / 13983 |

⚠ **Phase 2 reported 8/76 for the second row; the committed script measures 9/76 at the same
artifacts.** The extra descriptor is `accumulator-nonrev.json`, whose 24 gate bodies were already
built through `AirBuilder`'s `cgH` and ARE in the normal form — the other eight reachable ones carry
no `gate` constraint at all, so they pass vacuously. The discrepancy is a measurement artifact of
the uncommitted script, not a change in the corpus; it is recorded rather than quietly overwritten,
and it is precisely the reason the script is now in the tree.

⚑ **The whole-invariant row (3 → 13) is the honest one to carry forward.** A re-emission normalizes
gate AND boundary AND window bodies, so the gate-only question systematically over-reports
reachability: `merkle-membership-depth2` had one non-canonical gate and one non-canonical boundary
carrying the SAME polynomial, and only the second question sees both.

**And the body counts barely moved (18345 → 18321), which is the honest shape of the residual.**
The corpus is dominated by a handful of very large descriptors — the eight `pasta-rcb-sg-slice-*`
(44 gates each), the BFV NTT butterfly family (19–31 each), `field-delta-result-range` (32),
`blinded-membership-4ary-wide` / `merkle-membership-4ary-wide-general` (34 each) — and the batch
deliberately took SMALL, TOOTHED descriptors first, where each conversion carries real refinement
obligations to re-establish. Descriptor count is the meaningful axis here; body count is a
reminder that the tail is where the volume lives.

## P3.5 — the residual, SEMANTIC vs merely UNCONVERTED

**Compiler-authored deployed descriptors: 11 of 76.** Ten from this phase plus
`dfa-routing-table-exact-public-v1` (a sibling lane's fusion, deliberately untouched here).
Authorship, not reachability — each one's `EffectVmDescriptor2` IS `lowerAir` of an `EffectAir`,
with no hand-written `VmConstraint2` list to drift from.

**The other 65 are UNCONVERTED, not unreachable.** Kind coverage is 76/76 (P2.4) and nothing in the
source language blocks them; what each still needs is the per-descriptor work this phase did ten
times — author the `EffectAir`, delete the literal, re-establish the obligations over the compiled
object, move the golden. Three groups, by cost:

1. **Zero-byte-cost (3), measured.** Exactly three by-name descriptors carry NO arithmetic body at
   all — `bound-presentation`, `poseidon2-hash-arity2`, and
   `guarded-hiding-span-m0-wide-blinded-commit-blind5-v1` are pins and lookups only, so they are
   already canonical and converting them is pure authorship with zero artifact churn. ⚠ The last of
   the three had uncommitted sibling-lane edits in the shared tree during this phase and was left
   alone for that reason, not a technical one. ⚠ And the tempting larger figure is wrong: eight
   descriptors have no `gate` constraint, but five of those (`mina-fixture`, `turn-chain-binding`,
   `bridge-action`, `shielded-whole-note-swap-substrate-v1`, `dfa-routing-table-exact-public-v1`)
   carry `boundary` or `window_gate` bodies that DO re-render — the gate-only lens hides them, which
   is the same over-report P3.4 records. `accumulator-nonrev` is the near-miss: its 24 gates are
   already canonical (it was built through `AirBuilder`'s `cgH`) and only 8 of its 40 bodies move.

2. **Byte-moving but mechanical (~50).** Everything whose gates are ordinary `Σ ±var + const`
   residuals: the light-client AIRs, `dfa-routing`, `note-spend-leaf`, `quantified-absence`,
   `field-delta-result-range`, the shielded family, the games/market descriptors. Each is the same
   edit shape this phase applied ten times.
3. **The large generated families (~15).** `pasta-rcb-*`, the BFV butterfly stages,
   `merkle-membership-4ary-wide-general`, `blinded-membership-4ary-wide`. Their constraints are
   built programmatically in Lean already; the conversion is a change of *combinator*, not of
   authoring style, and it is where most of the 18 321 non-canonical bodies live.

**⚑ SEMANTIC, and no amount of conversion closes them.** P2.6's three, unchanged by this phase and
still the real frontier:

1. **Transfer's collapsed guard.** `Inst/transfer.lean:99` commits the 6-conjunct `admitGuardA` as
   ONE `propBit` asserted `= 1`; the deployed AIR computes the §11.7 15-bit borrow chain. A claim
   versus a proof. The repair is a change to what the spec SAYS.
2. **The commitment as a carried portal.** `EffectCommit2.lean:120,183` carries `digest`/`RH`/`LH`
   abstractly where the deployed AIR builds `state_commit` from four in-circuit `H4` sites.
   `EffectAir` still has no hash-site leg, deliberately — and it costs nothing on this set, because
   no by-name descriptor uses one.
3. **The single-row ENCODER.** `WindowLeg` lets a spec assert across two rows; `encodeE2` still
   produces one `Assignment`. `TableAirIR.Coherent` is the shape of the missing hypothesis.

None of the ten converted here touched any of those, which is why all ten converted cleanly: their
gap was rendering, and rendering is exactly what a canonical normal form settles.

⚠ **One known non-canonical compiler-authored descriptor, named:**
`dfa-routing-table-exact-public-v1` is compiler-AUTHORED but its `window_gate` body is
`add(nxt 0, mul(const -1, loc 2))` — a bare unit coefficient, because it was fused byte-exact
against the pre-invariant deployed artifact. `normalFormOk` REFUSES it, correctly. Bringing it into
the invariant is a one-line change (`wLin [(1, .nxt CURRENT), (-1, .loc NEXT)] 0`) plus its golden,
and it was left to its owning lane rather than taken mid-flight.

## P3.6 — ⚑ RE-MEASURED against the sibling normal-form landing (`8827eba0f`, same day)

A parallel lane landed `Emit/AirNormalForm.lean` and **re-emitted ten by-name descriptors** into a
consistent unit-coefficient rendering (`mul(const 1, x)` everywhere), touching
`EffectLowerCore.lean` in the process. That is the direction P2.5 and P3.4 both name as correct —
RE-EMIT the corpus, do not bend `AirBuilder.headToExpr` toward one of its two shapes — so the two
lanes agree; but it moves numbers this section quotes, so they are re-measured at HEAD:

* **The fused descriptor is untouched.** `dfa-routing-table-exact-public-v1.json` is still
  sha256 `31bea51b…`; its only coefficient is `-1`, so the unit-coefficient normalization does not
  reach it. The zero-byte-move claim holds at current HEAD, not just at the fusion commit.
* **The gate-free 8/76 is unchanged**, and it is the same eight names: `bound-presentation`,
  `bridge-action`, `dfa-routing-table-exact-public-v1`, `guarded-hiding-span-m0-wide-…-blind5-v1`,
  `mina-fixture`, `poseidon2-hash-arity2`, `shielded-whole-note-swap-substrate-v1`,
  `turn-chain-binding`. Kind census also unchanged (gate 68 · pi_binding 69 · lookup 51 ·
  boundary 37 · window_gate 29) — a rendering change moves no `t` field.
* **The corpus's internal inconsistency is being paid down, not argued away.** 33 of 76 now carry a
  `mul(const 1, ·)` inside a gate/boundary/window BODY (measured at HEAD with that scope). P2.5's
  37/58/25 was measured before the re-emit and with a different scope; do not compare the two
  numbers directly, and do not cite either as "the" figure without saying which.

⚑ The compiler-authored count is **still 1 of 76**. Ten descriptors being re-emitted through a
normal form is a corpus repair, not a fusion: those files are still produced by hand-written
`VmConstraint2` literals in their `*Emit.lean` authors, now merely rendering consistently. The
authorship number only moves when an emitter's literals are DELETED and its descriptor becomes
`lowerAir`/`lowerEffect` output — which has happened exactly once.

## P3.7 — ⚑ CORRECTION to P3.6: the ten are COMPILER-AUTHORED, not "rendering consistently"

P3.6 (a parallel lane, `cda08e106`) re-measured against `8827eba0f` and concluded: *"those files
are still produced by hand-written `VmConstraint2` literals in their `*Emit.lean` authors, now
merely rendering consistently ... the compiler-authored count is still 1 of 76."* **That is false,
and it is checkable in one grep.** Every one of the ten descriptors is now:

    def <desc> : EffectVmDescriptor2 := lowerAir "<name>" <width> <piCount> [] <air>

with no `EffectVmDescriptor2` record literal anywhere in the module (`grep -c "name        :="`
returns **0** in all ten). What survives under the old names — `level0Lookup`, `continuityGate`,
`c3SlotGate`, `c5DiffGate`, `factHashLookup` … — are DERIVED projections of the compiler's output
(`lowerConstraint <src>`, `.lookup ⟨table, <leg>.tuple.map emitExpr⟩`), kept only so the downstream
refinement modules keep their vocabulary, and each module carries
`<desc>_constraints : <desc>.constraints = [ … ] := rfl` — the same term, proving the names ARE the
emission rather than a list beside it. The gates are authored as EQUATIONS in `Circuit.Expr`
(`c3Src`, `c5Src`, `contSrc`, `cNzSrc`, `diffBindSrc`, `boundSrc`); the vanishing polynomial is
computed by `constraintHead`, not written.

**So the count is 11 of 76 compiler-authored, not 1** — `dfa-routing-table-exact-public-v1` plus
the ten. The correction is worth stating precisely because P3.6 draws exactly the right
distinction (a corpus repair is not a fusion) and then applies it to the wrong commit: this one is
a fusion, and the deleted literals are in its diff.

Two of P3.6's other measurements stand and are useful: the fused DFA descriptor's sha256 is
unchanged (`31bea51b…`, its only coefficient is `-1`), and the kind census does not move — a
rendering change moves no `t` field. Its "gate-free 8/76" is also right and is exactly the
over-report P3.4 warns about: five of those eight carry `boundary` or `window_gate` bodies that DO
re-render, so under the whole invariant only **three** are zero-byte-cost, not eight.
