# The effect algebra, reckoned — `SetField` and its siblings as an algebra

*2026-07-26. A read-only audit of dregg's effect vocabulary as an algebraic structure rather than
a list of cases. Every claim is anchored to `file:line` at HEAD (`b7f7f249e`). No build was run.*

---

## SUBSTRATE DECLARATION (house law, stated before the first line of analysis)

**AIR / constraints / gadgets / circuit logic are AUTHORED IN LEAN.** Rust only calls into the Lean
artifact via the `@[export]` / emit path. Rust never hand-writes AIR constraints, `Builder` gadgets,
or `air_accepts` predicates. An existing Rust AIR is **DEBT, not a foundation**, and extending it IS
the drift. Everything in this document that touches "does the prover accept X" is discussed as a
**Lean-authored** object; the accompanying sketch (`metatheory/EffectAlgebraSketch.lean`) is Lean.
No Rust AIR was written or proposed here.

**What I did not do:** no `cargo`, no `lake build`, no `git` mutation. Consequently every theorem
named below is one I *read*, not one I *checked*; and the sketch file is **UNELABORATED** — see
§4.0. Two findings below (§2.3.D) are **derivations from two definitions I read**, not measurements.
They are labelled as such and each carries the witness pair that would settle it.

---

## 0. The one-paragraph verdict

**`SetField`'s denotation is right and should survive. Three things around it are wrong.**

A guarded, named-field, whole-value write is a good primitive — it is the structural rule of the
`state` substance and `VerbRegistry` is correct that it is irreplaceable
(`metatheory/Dregg2/Substrate/VerbRegistry.lean:435`). What is broken is:

1. **`SetField` has three mutually non-isomorphic types across the three layers**, for *both* of its
   arguments. Address: `u64` over a 16-slot array ∪ an unbounded `BTreeMap` (Rust) / `String` over an
   association list (Lean) / `Fin 8` (the AIR — and the *dynamic* descriptor is `Fin 8` too, by a
   degree-8 range product). Value: `[u8;32]` (Rust) / `Int` (Lean) / **one BabyBear felt** (AIR).
   The value mismatch is a *named, measured, deployed* completeness hole; the address mismatch is not
   named anywhere.
2. **The guard lives in a separate language (`SlotCaveat`) whose relationship to the write is never
   stated as a law**, and the two layers evaluate it at different granularities — Lean per write,
   Rust per action. That is not a bug in either; it is the absence of a compositionality law that
   would force them to agree. I derive the witness pairs where they diverge, in *both* directions.
3. **The one composition law that exists — `execFullTurnA_append` — is false of the deployed
   executor**, because Rust applies a stable partition (`regular ++ permission`) that Lean does not
   model at all, and `N(xs ++ ys) ≠ N(xs) ++ N(ys)` for that normalization.

The refactoring that follows from (2) and (3) is small, local, and already half-built elsewhere in
the tree. It is in §3.

---

# PART 1 — SCHOLAR: what the vocabulary *is*

## 1.1 There are four vocabularies, not one

| layer | the type | count | where |
|---|---|---|---|
| **Wire / executed** | `enum Effect` (Rust) | **36** | `turn/src/action.rs:1063` |
| **Reified roster** | `inductive EffectTag` (Lean) | **36** | `metatheory/Dregg2/Substrate/VerbRegistry.lean:224` |
| **Denoted / kernel** | `inductive FullActionA` (Lean) | **31** | `metatheory/Dregg2/Exec/TurnExecutorFull/PerAsset.lean:1551` |
| **Constrained / AIR** | `Rfix` descriptor rungs | **29 of 36** | `metatheory/Dregg2/Circuit/CircuitSoundnessAssembled.lean:400` |

Plus a fifth that is a **toy and should not be cited as the vocabulary**: `Dregg2/Spec/Conservation.lean:154`
defines `inductive Effect` with **three** constructors (`transfer`, `mint`, `setField`). Its own
docstring says so — *"`Effect` is an ABSTRACT carrier — we do NOT port dregg1's 50-variant enum"*
(`Conservation.lean:147-150`). Every colouring theorem in that file
(`linearity_examples:171`, `paired_and_disclosed_exclusive:139`) is about the 3-constructor toy.

These do not line up, and the gaps are load-bearing:

- **36 vs 31.** `FullActionA` has no `Promise`/`Notify`/`React`/`ShieldedTransfer`/`Custom`/
  `CreateHybridCell`/`RotatePqIdentity`, and *has* two constructors with no wire variant:
  `heapWriteA` (`PerAsset.lean:1726`) and `delegateAttenA`. `heapWriteA` has a full AIR family and a
  refinement theorem (`heapWrite_descriptorRefines_sat`,
  `Dregg2/Circuit/RotatedKernelRefinementExercise.lean:388`) and **there is no `Effect::HeapWrite`** —
  `circuit/tests/heap_write_deployed_root_forced.rs:38` says it outright: *"is STRANDED at HEAD — no
  producer emits its geometry (there is no `Effect::HeapWrite` variant)."* A tooth with no verb.
- **29 of 36 have an AIR rung.** The catch-all is `actionTagToPos | _ => 1000`
  (`CircuitSoundnessAssembled.lean:392`), commented *"off-range: past the registry → transfer
  fallback."* The seven with no rung: `Promise`, `Notify`, `React`, `ShieldedTransfer`, `Custom`,
  `CreateHybridCell`, `RotatePqIdentity`.

⚑ **`docs/reference/effect-vocabulary.md` is wrong on exactly this point and should be corrected.**
It says (`:120-124`) that the two variants lacking a descriptor rung are `SetProgram` and
`ShieldedTransfer`. `SetProgram` **has** a rung at HEAD — `actionTagToPos | 13 => 51`
(`CircuitSoundnessAssembled.lean:390`), `Rfix 13 = setProgramV3` proved by `rfl` at `:544`, and
`setProgram_descriptorRefines_sat` (`Dregg2/Circuit/RotatedKernelRefinementProgram.lean:164`). The
doc also says "33 variants" (`:52`) and tabulates **33** rows against an enum of **36** — the three
with no row at all are exactly `Custom`, `CreateHybridCell` and `RotatePqIdentity`, i.e. the doc
predates the last three enum appends and nobody re-counted. (It also anchors the enum at
`action.rs:1061`; it is at `:1063`.) `Dregg2.lean:1008` carries the matching
stale prose ("needs a `setProgramA` constructor on `FullActionA`") — that constructor exists at
`Dregg2/Circuit/ActionDispatch.lean:118`.

## 1.2 The denotation

The kernel state is `RecChainedState` (`Dregg2/Exec/RecordKernel.lean:840`) = a 19-field
`RecordKernelState` (`:309`) plus a receipt `log : List Turn`. A cell's mutable state is
`cell : CellId → Value` (`:313`), and `Value` (`Dregg2/Exec/Value.lean:61`) is
`int | dig | sym | record : List (FieldName × Value)` with `abbrev FieldName := String` (`:38`).

**So a cell's fields are an association list keyed by strings, unbounded, order-preserving on
existing keys, appending on absent.** `setField` walks it
(`Dregg2/Exec/EffectsState.lean:73-81`); the read-back law is `setField_fieldOf` (`:89`).

Every verb is a `def : RecChainedState → … → Option RecChainedState`, dispatched by a 31-arm
`execFullA` (`PerAsset.lean:1918`). The denotation of `setFieldA` is the three-layer gate stack:

```
.setFieldA actor cell f v  ⟼  stateStepDev s f actor cell v        -- PerAsset.lean:1937
  stateStepDev     = reservedField bar    ∘ …                       -- EffectsState.lean:321
    stateStepGuarded = caveatsAdmit gate  ∘ …                       -- EffectsState.lean:258
      stateStep      = authority ∧ membership ∧ liveness, then write -- EffectsState.lean:205
```

⚑ **Five arms of `execFullA` are literally the same function at different field names:**

```lean
| .setFieldA actor cell f v     => stateStepDev s f actor cell v          -- PerAsset.lean:1937
| .setPermissionsA actor cell p => stateStep s permsField   actor cell (.int p)     -- :1946
| .setVKA actor cell vk         => stateStep s vkField      actor cell (.int vk)    -- :1947
| .setProgramA actor cell prog  => stateStep s programField actor cell (.int prog)  -- :1948
| .refusalA actor cell          => stateStep s refusalField actor cell (.int 1)     -- :1989
```

and a sixth, `incrementNonceA`, is `stateStep` on `nonceField` behind a monotone gate
(`incrementNonceStep`, `EffectsState.lean:381`). `Refusal` is `SetField refusalField 1` with a
constant. `VerbRegistry` already knows this: `SetField`, `SetPermissions`, `SetVerificationKey`,
`SetProgram` and `Custom` are all `.survivor .write` (`VerbRegistry.lean:266-283`).

⚑ **Note what the three protocol writes bypass.** `setPermissionsA` / `setVKA` / `setProgramA`
route to the **bare** `stateStep` — *not* `stateStepGuarded`. They never consult `caveatsAdmit`. This
is deliberate and documented (`PerAsset.lean:1943-1945`), and its consequence is not: **a factory
cannot bind a `SlotCaveat` to `"permissions"`/`"verification_key"`/`"program"` and have it
enforced.** `caveatsAdmit` filters `slotCaveats` by field name (`EffectsState.lean:248-250`) on a
code path those three verbs never take. Such a caveat is accepted, stored, committed into
`slotCaveats`, and **silently inert** — the `GATING DEFAULTS TO SILENCE` shape exactly.

## 1.3 Is the set closed under composition? **No — and the identity is not an effect.**

Two effects in a turn are **not** an effect. There is no `Effect` constructor denoting a composite,
and no combinator. What exists is a *free monoid acting partially on state*:

```lean
def execFullTurnA (s : RecChainedState) : List FullActionA → Option RecChainedState
  | []        => some s                                  -- PerAsset.lean:2303  ← the identity
  | a :: rest => match execFullA s a with
                 | some s' => execFullTurnA s' rest
                 | none    => none                       -- PerAsset.lean:2302
```

and the composition law is **proved**:

```lean
theorem execFullTurnA_append (s : RecChainedState) (xs ys : List FullActionA) :
    execFullTurnA s (xs ++ ys)
      = (match execFullTurnA s xs with
         | some s' => execFullTurnA s' ys
         | none    => none)                              -- PerAsset.lean:2426
```

Its declarative twin is `turnSpec_append` (`Dregg2/Circuit/Spec/Turn.lean:55`) with the unit
`turnSpec_nil` (`:40`) and the bridge `execFullTurnA_iff_turnSpec` (`:81`).

**So the honest statement is:** `execFullTurnA` is a monoid action of the **free monoid**
`(List FullActionA, ++, [])` on `RecChainedState` in the Kleisli category of `Option`. Identity `[]`;
composition `++`; associativity and unit both hold. **Nothing is quotiented.** There are no relations
on the generators. The "algebra" is free — which is another way of saying there isn't one yet.

⚑ **And `execFullTurnA_append` is FALSE of the deployed executor.** Rust does not fold in
declaration order. It applies a stable two-bucket partition, per action:

```rust
let (regular_effects, permission_effects): (Vec<&Effect>, Vec<&Effect>) = action
    .effects.iter().partition(|e| !e.is_permission_effect());
                                        // turn/src/executor/execute_tree.rs:845-848
```

regular first (`:892-936`), permission effects last (`:939-964`). The rationale is a real security
fix (`:833-840`: *"prevents an action from SetPermissions -> exploit weakened perms"*).
`is_permission_effect` covers **four** variants — `SetPermissions`, `SetVerificationKey`,
`SetProgram`, **`RotatePqIdentity`** (`turn/src/action.rs:2744-2752`); the doc says three.

Write `N` for that normalization. `N` is idempotent, so the deployed semantics factors through a
normal form. But `N(xs ++ ys) ≠ N(xs) ++ N(ys)` in general — a permission effect in `xs` is moved
*behind* regular effects in `ys`. Concretely with `xs = [SetPermissions p]`, `ys = [SetField c f v]`:
Lean runs `SetPermissions` then `SetField`; Rust on the concatenation runs `SetField` then
`SetPermissions`. And `apply_set_field`'s cross-cell gate reads permissions
(`turn/src/executor/apply.rs:531-541`), so the order is observable.

**Nothing in Lean models this.** Grepping the whole `metatheory/` tree for
`is_permission_effect` / `partition` / "applied LAST" returns zero hits in the executor layer. The
associativity law the entire forest lift rests on (`Dregg2/Exec/FullForest.lean:269`,
`FullForestAuth.lean:697`) describes an execution order the deployed executor does not use whenever
an action mixes a permission effect with anything else.

Two further consequences worth recording: `effects_hash` is accumulated over the **reordered**
sequence (`execute_tree.rs:931`, `:961`), so the receipt commits to `N(xs)`, not to what the author
signed; and `ExerciseViaCapability` inner effects are **not** partitioned — they run in strict
declaration order (`apply.rs:2749-2758`). So the normalization is not even uniform across nesting
depth.

## 1.4 What are the equations? **There are none. And absorption provably fails.**

Searched exhaustively: **no** `setField (setField …)` law, no `_overwrite` theorem anywhere in the
tree, no `_idem` theorem about the effect denotation, no `execFullA_comm`, no `execFullTurnA_perm`.
The eleven `_idem` theorems in `metatheory/` are about CRDT joins, verification closures, box
projections and directory laws — none about effects.

So `SetField x a ; SetField x b = SetField x b` is **not a law, not folklore, and not true.** It
fails for two independent reasons:

1. **The log.** Every committed step extends the receipt chain: `execFullA_log_suffix`
   (`s.log <:+ s1.log`, `PerAsset.lean:2652`), lifted to `execFullTurnA_logMono`
   (`Dregg2/Exec/CellCarry.lean:95`). The two sides differ in `log` length. The receipt chain makes
   the denotation *faithful on the length of the effect list* — which is exactly what makes the tape
   a tape, and exactly what forbids absorption.
2. **The guard.** `caveatsAdmit` evaluates against the *current* value
   (`EffectsState.lean:248-250`). With a `monotonicSeq` caveat on `f` (`new = old + 1`,
   `Dregg2/Exec/RecordKernel.lean:87` ff.) and `old = 0`, the pair `[SetField f 1, SetField f 2]`
   commits and the single `SetField f 2` refuses. The composite is *strictly more permissive* than
   its last element.

What the tree *does* have, richly, is the **relational** theory: every verb has a declarative
full-state `*Spec` with an explicit frame clause and a proved `execFullA_*_iff_spec` bridge.
`SetFieldSpec` (`Dregg2/Circuit/Spec/cellstatefield.lean:116`) conjoins 18 literal field equalities;
`writeFieldCellMap_correct` (`:93`) validates the touched-cell map; `setFieldSpec_cell_frame` (`:260`)
gives cell-disjointness; `fieldOf_setField_ne` (`Dregg2/Substrate/HeapKernel.lean:87`) gives
field-disjointness; `Heap.get_set_frame` (`Dregg2/Substrate/Heap.lean:149`) gives key-disjointness.

**Frames yes, equations no.** That is the shape of the whole thing: *this effect changes nothing
else* is stated per-effect and per-field, 31 times, instead of once as a law about the algebra.

The single genuine commutation theorem in the tree is
`applyHalfOut_comm_disjoint` (`Dregg2/Proof/ContendedCrossCell.lean:176`) — two committed debits on
disjoint cells commute — and it is over the **toy scalar** `Exec.Kernel.KernelState`, not
`RecordKernelState`/`FullActionA`.

## 1.5 Where the vocabulary is REDUNDANT

Building on `project-verb-registry-reduction` (which established that "8 verbs" is a registry
abstraction with a real minimality theorem at `VerbRegistry.lean:435`, not a deployed count):

- **Six wire variants share one denotation shape** (§1.2): `SetField`, `SetPermissions`,
  `SetVerificationKey`, `SetProgram`, `Refusal`, `IncrementNonce` are all `stateStep` at a field name.
  They are separated by *which name they may target* and *which gate runs* — data, not structure.
- **`IncrementNonce` is the single monomorphic instance of an operation the model already has
  generically.** `Dregg2/Exec/RecordCell.lean:37` defines `inductive RecOp` with **two**
  constructors: `setScalar (field) (value)` and **`addScalar (field) (delta)`** (`:39`, `:41`), with
  `applyOp` at `:64-65`. `IncrementNonce` *is* `addScalar "nonce" 1`. The delta operation exists in
  Lean, is not in the effect vocabulary, and is not in the AIR.
- **`setFieldV3` is eight descriptors and `setFieldDyn` is a ninth**, all refining the *same* kernel
  leaf `SetFieldSpec` (`RotatedKernelRefinementSetField.lean:258`,
  `RotatedKernelRefinementMisc.lean:304`). One effect, nine teeth. See §2.3.
- `SetProgram` rides the `setVK` AIR name by design (`Dregg2/Circuit/EffectEmitRegistry.lean:102-103`).
- `bridgeMintA` reuses `recCMintAsset` verbatim (`PerAsset.lean:1976`).

## 1.6 Where the vocabulary is INCOMPLETE — four escape hatches, one per layer

Building on `project-circuit-custom-effect-carveout` (which established `Effect::Custom` as the
honest-named carve-out at the *effect* layer). The finding here is that **the same escape-hatch shape
has grown independently at four layers, because each layer below is a fixed finite enumeration:**

| layer | the hatch | where | what it admits |
|---|---|---|---|
| effect | `Effect::Custom` | `turn/src/action.rs:1594` | an externally-proven state advance; classical apply refuses fail-closed (`apply.rs:506-509`) |
| caveat | `SlotCaveat.admitTable (transitions : List (Int × Int))` | `Dregg2/Exec/RecordKernel.lean:87` ff. | *"the EXECUTABLE realization of an arbitrary per-slot admission predicate the six prior caveats CANNOT express"* — its own docstring |
| caveat (again) | `SlotCaveat.clearanceGe` | same inductive | added because precomputing the clearance lattice into an `admitTable` was inadequate — a hatch on the hatch |
| AIR | `setFieldDyn` | `Dregg2/Circuit/Emit/EffectVmEmitV2.lean:1404` | a dynamic address, escaping the 8 static per-slot descriptors — bound by an *uncommitted memory readback*, not the committed write column |

`admitTable` is the tell. A caveat language that needs "an arbitrary finite relation" as a
constructor is a language that failed to find its own algebra — the same confession `Custom` makes
one layer up.

**And there is a fifth incompleteness with no hatch at all: the value type.** `SetField` writes
`.int v` (`SetFieldSpec … (v : Int)`, `cellstatefield.lean:116`), but `Value` also has `.dig` and
`.record`. A cell field can *hold* a digest — `makeSovereign` writes one
(`Dregg2.lean:1027`: `[(commitmentField, .dig (stateCommitment …))]`) — and **no developer verb can
write one.** Nested records are likewise unreachable. The state model is strictly richer than the
write verb.

## 1.7 What `SetField` presumes — and what cannot be said with it

`SetField { cell: CellId, index: u64, value: FieldElement }` (`turn/src/action.rs:1065-1073`)
presumes:

**(a) A named field.** True in Lean (`FieldName = String`), *false* in Rust (`index: u64`), *false*
in the AIR (`Fin 8`). `Value.lean:39` states the design intent — *"Names, not bit positions — the
`dregg2 §5` fix"* — and the wire never got the fix.

**(b) A flat address space.** Nearly true, and the exceptions are the interesting part.
`apply_set_field` (`turn/src/executor/apply.rs:557`) branches on `index < STATE_SLOTS` (= 16,
`cell/src/state.rs:57`): below, the fixed array `fields: [FieldElement; 16]` (`state.rs:180`); above,
`fields_map: BTreeMap<u64, FieldElement>` (`state.rs:278`) with a `fields_root` recompute. **There is
no upper bound and no rejection path** — any `u64` up to `u64::MAX` is a legal key. There are no
namespaces; the only discipline is convention, e.g. `REFUSAL_AUDIT_EXT_KEY = 0x1_0000_0000`
(`state.rs:67`), keyed high "to avoid clashing with app ext-field usage." The genuine namespace
(`system_roots`, `state.rs:73`, indices `ESCROW…SEALED_BOXES` at `:85-107`) exists precisely because
the IR extension once **stole `fields[1..7]` from apps and collided with their data** — the comment
at `state.rs:77-80` records it. A structured address space *does* exist one layer up
(`UDomain{Registers,Heap,Caps,Nullifiers,Index,Working}`, `turn/src/umem.rs:~100`) — it is the
*proving* address space, not the effect address space.

⚑ **A live drift, worth someone's afternoon:** `Dregg2/Exec/FieldsMap.lean:47` sets
`reservedKeys := 8` and its header asserts *"The Rust cell has exactly 8 `FieldElement` slots
(`cell/src/state.rs:STATE_SLOTS = 8`)"*. Rust says **16**. Lean's `userTail` filters keys ≥ 8; Rust's
`fields_map` holds keys ≥ 16; the two `fields_root` preimages disagree on keys 8..15.
`cell/src/commitment.rs:1099` also splits at 8 (`for field in &st.fields[8..STATE_SLOTS]`) for a
*third* reason — `fields[0..8]` are welded to rotated registers `r3..r10`. The number 8 is
load-bearing in three different senses and the number 16 in one, and one file believes 8 is 16.

**(c) A total write.** True, and this is the real limit. **There is no partial-update verb anywhere
in the effect vocabulary** — no `Increment`, `Append`, `Delete`, `CompareAndSwap`, `Patch`, `Diff`,
`Merge`. `IncrementNonce` takes no value and no index. Read-modify-write is the only increment, done
in userspace: `grain-turn/src/lib.rs:551` literally writes `SetField { calls_made : c → c+1 }`, and
`cell/src/state.rs` carries `encode_i64`/`decode_i64` so apps can do the arithmetic themselves.

**So: what cannot be said with `SetField`?**

- **Relations.** Nothing relating two fields, or a field to a peer cell's field, except through
  `Preconditions` (`cell/src/preconditions.rs:42`) — signed assertions, not state changes.
- **A delta.** You must know `old` to express `new`, so a concurrent or blind increment is
  inexpressible. This is the source of every downstream problem in §2.
- **Ownership transfer.** Proved impossible, in-tree: `gwrite_conservation_trivializes`
  (`Dregg2/Substrate/VerbCompression.lean:772`) shows that for **every** guard, a committed
  single-key write preserving the total must write the value already there — conservation is not
  expressible as a guard on a write. `move_not_single_write` (`:875`) and
  `create_birth_not_single_write` (`:915`) complete it. **This is exactly the right kind of negative
  result and there should be more of them.**
- **An inverse.** See §2.2.
- **A large value.** See §2.4 — and this one is *deployed*.

---

# PART 2 — THE BROKEN SYMMETRIES

## 2.1 Read versus write — **structurally absent, and it is an accident, not a principle**

**Writes are effects; reads are nothing.** There is no `ReadField`, no read set on `Turn`/`Action`/
`Effect`/`TurnReceipt`, no observation record. The executor reads live cell state straight out of the
`Ledger` (`apply.rs:542`, `:624`, `:656`) and records nothing.

Three near-misses, each of which makes the asymmetry look accidental rather than designed:

1. **`ReadSet` exists and is inert.** `cell/src/program/types.rs:391` —
   `{new_slots, old_slots, reads_height, reads_epoch, reads_sender, reads_preimage}`. Its own doc
   says it is there so tools *"and (eventually) AIR enforcement"* can reason about footprint. **Every
   construction in the tree is `ReadSet::default()`** (`tests/src/state_constraint_variants.rs:1622`,
   `:1642`, `protocol-tests/src/invariants/sentinel_variants_reject.rs:75`,
   `preflight/src/checks/state_constraints.rs:118`, and two more). Zero readers.
2. **The Blum memory bus is fully built and emits writes only.** The theory is complete —
   `Dregg2/Crypto/MemoryChecking.lean` with `Kind.read | Kind.write`, `memcheck_sound`;
   `Dregg2/Crypto/UniversalMemory.lean` with `universal_memory_sound`, `nullifier_fresh_sound`.
   The emitter is not: `turn/src/umem.rs:2403` `emit_trace` re-reads **the undo journal** as the write
   trace (`umem.rs:18`), and **`UmemKind::Read` is never constructed by it**. The descriptor builder
   hardcodes `kind: MemKind::Write` (`umem.rs:1306`) with the justification at `:1282` — *"A
   disciplined read folds identically to a same-value write."* In the deployed registries there is
   **exactly one** `"kind":"read"` op, and it is `setFieldDynVmDescriptor2R24` reading back **the slot
   it is itself writing** (`Dregg2/Circuit/AlgoStarkSoundFanoutMemory.lean:7`: *"SetFieldDyn — the
   sole `.memOp` effect"*).
3. **The scheduler computes a read set and throws it away.** `conflict.rs:164` `extract_access_sets`
   produces one; every caller binds it to `_read_set` (`execution_path.rs:66`,
   `fast_path.rs:269,359,475`, `executor/execute.rs:520`).

⚑ **And the fog feature that needs it exists.** `Dregg2/Deos/FogOfWar.lean` proves `noninterference`
— a low viewer's projection is a function of the low-authorized state alone — with
`hidden_change_invisible`, `vision_monotone`, axiom-clean. The Rust realization
(`starbridge-web-surface/src/game.rs:462`) makes hidden tiles *structurally absent*, and
`vision_predicate.rs` was promoted into the real `WitnessedPredicateRegistry` after its own header
confessed the earlier version was an inert identity tag. **But all of that is about what a viewer is
SHOWN.** Nothing constrains what a *turn* read. A prover computing a fogged move's legality reads the
whole board in the clear, and neither the receipt, the AIR, nor the memory bus records or bounds it.
`dregg-automatafl`'s fog is commit-reveal with the plaintext in the session
(`dregg-automatafl/src/surface.rs:47`, `:417`); `dregg-multiway-tug/src/hidden_hand.rs` is honest that
its non-replay is *"an exact-card host ratchet"*, not an executor-proven theorem.

**Verdict: an accident of implementation order.** The type (`ReadSet`), the constraint system
(`MemoryChecking`/`UniversalMemory`), the bus (`BUS_UMEM_*`), and the consumer (`FogOfWar`) are all
built. The *emitter* is write-only because it was derived from the undo journal, which is write-only
because it is an undo journal. One producer change stands between here and first-class reads.

## 2.2 Do versus undo — **the inverse exists, in Rust, unproven; the algebra is in Lean, without it**

⚑ This is the sharpest structural inversion in the whole audit.

**`turn/src/reversible.rs` is a genuine effect-algebra inverse.** `Effect::invert(&self, pre: &Ledger)
-> Inversion` (`:235`) is an **exhaustive match with no `_ =>` arm** — every new `Effect` variant is
forced by rustc to answer. `Inversion` (`:193`) is three-tier:

- `Clean(Effect)` — a genuine inverse needing no context: `Transfer{from,to}` ↦ `Transfer{to,from}`;
  `GrantCapability` ↦ `RevokeCapability`; `CellSeal` ↔ `CellUnseal`.
- `Contextual(Effect)` — an inverse that needs the pre-state. **`SetField` is here** (`:271`):
  `SetField{cell,index}` ↦ `SetField{cell,index, value: pre.get(cell).state.get_field_ext(index)}`.
- `Committed(CommittedReason)` — irreversible, with **eight named reasons** (`:142`):
  `NullifierConsumed, ValueBurned, FreshnessRatchet, AuthorityRevoked, TerminalLifecycle,
  MonotoneNarrowing, GenerativeOrProofCarrying, NonLocalEffect`.

`Turn::invert` at `:489`; `undo_to(k)` at `:827` builds the inverse turns and applies them **forward
through the real executor**. The honest caveat is enforced, not hidden:
`ledgers_agree_modulo_nonce` (`:1165`) — undo restores value and state exactly but leaves the nonce
ratchet advanced.

**And there is nothing like it in Lean.** Searching `metatheory/` for
`Reversib|RCCS|invert|undo|inverse` returns NTT inverses, the `revert` tactic, and prose. The
faithfulness obligation `apply(invert(e,pre), apply(e,pre)) == pre` is a doc comment
(`reversible.rs:~230`) exercised by unit tests (`:1274`, `:1465`, `:1559`) and **never proved.**
`Dregg2/Exec/CellRuntime.lean:38/41` has `checkpoint`/`restore` with a `rfl` round-trip — that is a
snapshot, not an inverse.

**Is replay a faithful functor from tape to trajectory? No, and the tree says so.**

- There is **no** `replay_sound` / `replay_faithful` / `receipt_determines` theorem anywhere.
- Every `replay_deterministic*` is `rfl` or `Option.some.inj` — `Dregg2/Exec/Receipt.lean:192` (whose
  own docstring says *"Trivial by `rfl` because the replay builder is a pure total function"*),
  `:211`, `Dregg2/Exec/Cell.lean:155`, `Dregg2/Exec/CellRuntime.lean:56`,
  `Dregg2/Deos/ReplayMembrane.lean:95`. These say "the function is a function."
- The nearest soundness statement, `Dregg2/Crypto/TurnSoundness.lean:~155` `turn_sound`, holds under
  the named hypothesis `CircuitSound` (`:~125`) — the claim in question, hoisted to a premise.
- ⚑ **And the tree states the negative outright.** `Dregg2/Verify/ReceiptContract.lean:~140`:
  *"a receipt-property is NOT in general carried by the receipt ALONE — the receipt does not
  determine the next receipt; the full state does."*

**Where replay loses information — precisely.** `TurnReceipt` (`turn/src/turn.rs:837`) carries
`turn_hash`, `effects_hash`, `pre_state_hash`, `post_state_hash` — **hashes, not contents**. It does
not carry the `Turn`, the effects, or the pre-state. So a receipt proves *"some turn moved commitment
A to commitment B and I was authorized"*; it does not let you recompute B and it does not tell you
what happened. The chain verifier takes the endpoints as **caller-trusted arguments** —
`verify_rotated_replay_chain(legs, expected_old_commit, expected_new_commit)`
(`verifier/src/rotated_replay.rs:254`), documented at `:245` as *"the canonical pre/post state
commitments the verifier trusts …, NOT taken from the proof."* Re-execution needs the full pre-state
and the input `Turn`; `ReversibleStep::Committed` (`reversible.rs:596`) stores the `Turn` explicitly
*"so replay RE-EXECUTES it."*

**Verdict: principled in one respect, accidental in another.** That some effects are irreversible is
*principled* — `Committed`'s eight reasons are exactly the `Terminal`/`Monotonic`/`Generative`
colours, and monotone evidence must not be invertible. That the classification is **exhaustive in
Rust and absent in Lean**, and that the whole inverse structure is unproven, is an accident of
implementation order. `Effect::invert` is a better piece of algebra than anything in the Lean effect
layer, and it is on the wrong side of the substrate line.

## 2.3 Effect versus constraint — **the correspondence is not one-to-one in either direction**

| | count | evidence |
|---|---|---|
| effects with **no** AIR rung | **7 of 36** | `actionTagToPos | _ => 1000`, `CircuitSoundnessAssembled.lean:392` |
| effects with **nine** teeth | 1 (`SetField`) | 8 × `setFieldV3 slot` + `setFieldDyn` |
| teeth with **no** effect | ≥ 2 | `heapWriteA`; `pqIdentityRotationDesc` (`Dregg2/Circuit/Emit/PqIdentityAuthorityEmit.lean:64`, not in any registry) |
| descriptors built but unrouted | ≥ 4 | the shielded family, reachable only via `EmitByName.lean:249-255`, *"the L4 route (not yet live)"* |

**A. The seven missing teeth.** `Promise`, `Notify`, `React`, `ShieldedTransfer`, `Custom`,
`CreateHybridCell`, `RotatePqIdentity` have no `Rfix` rung. `Custom` is the subtle one: it **has** a
cohort descriptor (`customVmDescriptor2R24`, `EffectVmEmitRotationV3.lean:6048`) but **no
`actionTag`**, so `Rfix` never reaches it and it rides the `| (n+1) => rds.other (n+1)` catch-all at
`ClosureFanoutGenuine.lean:1186`. This is `project-circuit-custom-effect-carveout`'s finding,
regrounded: the Lean half is closed under `CustomApex.lean`; the deployed gate flip is not, and
`proofBind.holdsAt` is still `True` (`DescriptorIR2.lean:664`).

⚑ **A contradiction to resolve.** `docs/deos/EFFECTVM-AIR-VERIFICATION-CENSUS.md:50` (updated
`606a87245`, today) says the deployed fold now backs `proofBind` in-circuit. The Lean source comment
at `DescriptorIR2.lean:651-656` says the opposite — *"this arm is VACUOUS for a pure light client
as-shipped (`CustomCarrierAttack.deployed_admits_unbacked`) … Do NOT read this `True` as 'compensated
like memOp'."* One of these is stale. The census's own line numbers have all drifted (it cites
`DescriptorIR2.lean:390` for `VmConstraint2`, which is at `:420`), so I would trust the Lean comment
until someone re-reads the fold.

**B. `SetField`'s nine teeth, and what each forces.** The deployed write gate is

```
gFieldWrite slot = s_set_field · (fields[slot]_after − param1) = 0
                                  -- Dregg2/Circuit/Emit/EffectVmEmitSetField.lean:127-128
```

column `79 + slot` (`saCol (FIELD_BASE + slot)`, `#guard` at `:582`) against `param1` = column 69
(`:583`). Thirteen per-row gates (`setFieldRowGates`, `:140-142`): the write, four freezes, and seven
other-field passthroughs. **The address is not a circuit variable — it is a descriptor index**, and
there are eight descriptors, generated at `EffectVmEmitRotationV3.lean:6067-6069`. The Lean address
is the string `slotName slot = s!"slotfield{slot.val}"` (`EffectVmEmitSetField.lean:470`).

The dynamic escape, `setFieldDynVmDescriptor2` (`EffectVmEmitV2.lean:1404-1415`), has exactly four
constraints: a degree-8 range product `∏_{j<8}(slot − j)` (`gSlotRange`, `:1343-1345`), a selector
gate, a write `memOp` at the dynamic address, and a readback `memOp` at the same address
(`setFieldDyn_readback_genuine`, `:1438` — a genuine Blum readback, no hashing).

⚑ **So the dynamic path is `Fin 8` too.** `gSlotRange` restricts the address to `{0..7}`. There is no
descriptor, static or dynamic, that can address slot 8, let alone key 16, let alone key 2³². The AIR
address space for `SetField` is **eight slots**, against Rust's 16-slot array plus an unbounded
`BTreeMap<u64, _>`.

⚑ **And the dynamic path's reserved-slot bar is off-AIR.** `setFieldDyn_descriptorRefines_sat`
(`RotatedKernelRefinementMisc.lean:629`) takes

```lean
(hnr : Dregg2.Exec.EffectsState.reservedField f = false)
```

as a **carried hypothesis**, not something derived from `Satisfied2`. On the static path the bar is
free — `reservedField_slotName` (`RotatedKernelRefinementSetField.lean:247`) holds because
`"slotfield{i}"` is never one of the four reserved names. On the dynamic path it is an assumption the
theorem consumes, enforced off-circuit by `stateStepDev`. Since the reserved bar is exactly what
closes the nonce-reset replay vector (`EffectsState.lean:305-311`: *"a `SetField` of 'nonce' used to
commit; the freshness premise was FALSE"*), **a light client running only the STARK does not witness
that bar on the dynamic path.** Honestly named in the code, absent from the soundness census.

**C. A hole in the effect↔tooth correspondence at `ExerciseViaCapability`.** Inner effects are
applied for real (`apply.rs:2749-2758`) but **emit no AIR row** — they are only folded into
`exercise_hash`. `effect_vm_bridge.rs:763-773` says so while declining to recurse the wide-index
guard: *"An inner effect is never lowered to a `VmEffect::SetField` (it is hash-bound into
`exercise_hash`), so there is no truncation to refuse."* The reasoning is sound *for that guard*; the
consequence is that N inner state changes are constrained by one hash column. The same file
demonstrates the danger is not theoretical — the nested `RotatePqIdentity` refusal exists precisely
because *"the identity op would ride an `exerciseVmDescriptor2R24` proof that constrains nothing
about the rotation"* (`:757-760`).

**D. ⚑ Two derived divergences between the Lean guard and the Rust guard.**

*Labelled honestly: these are derivations from two definitions I read, not measurements. I could not
run them (no cargo). Each carries the witness pair that would settle it.*

Lean evaluates the caveat **per write**, filtered to the written field, against the value *currently*
in the cell:

```lean
def caveatsAdmit (k) (f) (actor target) (new : Int) : Bool :=
  ((k.slotCaveats target).filter (fun cav => cav.field == f)).all
    (fun cav => cav.eval actor (fieldOf f (k.cell target)) new)   -- EffectsState.lean:248-250
```

Rust evaluates the cell program **once per touched cell per action**, over the whole
`(old_state, new_state)` transition, where `old_state` is the **pre-action** snapshot taken at
`execute_tree.rs:827-831` and passed at `:1153` into `evaluate_cell_program_for_executor`
(`:175`, → `evaluate_full`, `:211`).

Per-write and per-action guards coincide only when at most one effect touches the field. When two do:

- **Rust admits what Lean refuses.** Caveat `monotonic` (`new ≥ old`), `old = 0`, effects
  `[SetField f 5, SetField f 1]`. Lean: step 1 admits (0→5), step 2 refuses (5→1) ⇒ `none`. Rust:
  one check, 0→1, `1 ≥ 0` ⇒ commits.
- **Lean admits what Rust refuses.** Caveat `monotonicSeq` (`new = old + 1`), `old = 0`, effects
  `[SetField f 1, SetField f 2]`. Lean: both steps admit ⇒ commits. Rust: one check, 0→2,
  `2 ≠ 0 + 1` ⇒ refuses.

The first direction is the one that matters: **the deployed executor admitting a turn the verified
kernel refuses** is an authority inversion in the wrong direction for a project whose bar is *the
verified artifact IS the running artifact*.

**And there is an algebraic reason this happens, which §3 turns into the fix.** Per-step admission
implies whole-transition admission exactly when the caveat's relation is **transitive**. Sorting
`SlotCaveat`'s eight constructors on that one axis:

| caveat | relation `R(old,new)` | transitive? |
|---|---|---|
| `immutable` | `new = old` | ✅ |
| `monotonic` | `old ≤ new` | ✅ |
| `boundedBy lo hi` | `lo ≤ new ≤ hi` | ✅ (independent of `old`) |
| `writeOnce` | `old = 0 ∨ new = old` | ✅ |
| `senderAuthorized` | actor ∈ set | ✅ (independent of both) |
| `clearanceGe` | actor clearance dominates | ✅ |
| **`monotonicSeq`** | `new = old + 1` | ❌ |
| **`admitTable`** | arbitrary finite relation | ❌ in general |

**Six of eight are transitive. The exact two that are not are the exact two where the divergence
lives — and one of them is the escape hatch.** That is the algebra telling you where the bug is.
(The converse — whole ⟹ per-step — fails for nearly everything, including `monotonic`, so the two
semantics are genuinely incomparable, not merely differently strict.)

## 2.4 The felt — **what is the right type of a value here?**

Owning the algebraic question, not the adoption lane. Building on `project-felt-width-repair-campaign`
(width bounds the image, it does not price the attack; 3 of 4 encoders non-injective; the 1-felt MapOp
key at the root).

**`SetField`'s value has three types and they are not related by any injection:**

| layer | type | cardinality |
|---|---|---|
| Rust wire | `FieldElement = [u8; 32]` (`cell/src/state.rs:35`) | 2²⁵⁶ |
| Lean kernel | `Int` (`SetFieldSpec … (v : Int)`) | ℤ, unbounded |
| deployed AIR | `param1`, one BabyBear felt | 2013265921 ≈ 2³¹ |

⚑ **The narrowing is authored at the type level, in Lean, in one line.**
`Dregg2/Exec/Value.lean:76-79`:

```lean
def width : Ty → Nat
  | .scalar   => 1
  | .digest   => 1     -- ← a 32-byte hash / commitment / cell-reference is ONE wire
  | .symbol   => 1
```

`Ty.digest`'s own doc calls it *"A 32-byte hash / commitment / cell-reference — one wire in the field
stand-in."* That is the felt-width wound stated as a *type*, upstream of every encoder in the
campaign's catalogue. Everything downstream inherits it: `flatten .digest (.dig d) = [(d : Int)]`
(`:117`), and `flatten` additionally sends every ill-typed value to zeros (`:120`), so
`flatten .digest (.int 5) = [0] = flatten .digest (.dig 0)` — **`flatten` is not injective even
before the mod-p reduction.** Two distinct `Value`s have the same wire image, provably, at width 1.

**And the AIR's map/memory ops agree.** `Dregg2/Circuit/DescriptorIR2.lean:301`:

```lean
structure MapOp where
  guard   : EmittedExpr
  root    : Fin 8 → EmittedExpr     -- 8-felt, faithful
  key     : EmittedExpr             -- ONE felt
  value   : EmittedExpr             -- ONE felt
  newRoot : Fin 8 → EmittedExpr     -- 8-felt, faithful
```

with `UMemOp` (`:269`) the same shape. The roots were widened; the key and value were not. The
staged repair `MapOpW` (`Dregg2/Circuit/MapOpWideKey.lean:129`) widens **the key only** — its
`value` stays one felt, flagged in its own doc as a named residual.

**What breaks because it is a felt — the deployed, measured instance.** The `SetField` write column
binds lane 0; the written slot's other seven "completion lanes" (in-block offsets
`113 + 7·slot .. 119 + 7·slot`, `setFieldCompletionBase`, `EffectVmEmitRotationV3.lean:5650`) are
**frozen to the pre-state** by the deployed `v3OfFrozen` wrap (`:6067-6069`). Consequences, both
proved by tests:

- The **forge is UNSAT** — arbitrary high bits cannot be written, because the freeze bites.
  `circuit/tests/setfield_completion_lane_forge.rs` is 3/3 (`docs/audit/TIER3.md:79`).
- The **honest large write cannot prove** —
  `setfield_completion_lane_forge::honest_large_value_setfield_fails_the_deployed_freeze` (`:286`).
  `docs/audit/TRUST-BASE-CENSUS.md:50` classifies it correctly: *a completeness seam, not a soundness
  forge*, `reducible-open`.

So: **the deployed protocol cannot express an honest 32-byte field write.** That is not a subtle
soundness risk; it is a stated functional limit. The fix is authored and staged —
`withSetFieldCompletionPins slot (setFieldV3 slot)` (`EffectVmEmitRotationV3.lean:5656`), emitted by
`metatheory/EmitRotationV3SetFieldValue8.lean`, bumping `piCount` 46 → 53, with the positive tooth
`honest_large_value_setfield_proves_under_value8`
(`circuit/tests/setfield_value8_epoch_flip.rs:164`). **Not deployed** — additive, beside
`v3RegistryBare`, VK byte-untouched.

**The algebraic answer to "what is the right type of a value here?"**

A cell field's value is a member of a **schema-declared type**, and the schema already exists
(`Ty`, `Value.lean:44`). The mistake is not "we used a felt" — it is that **`width` is a function of
the constructor, not of the declared semantic content**, so `digest` and `scalar` get the same
answer. The right type is a *limbed* value whose limb count is part of the type:

- `Ty.scalar` should carry its bit budget: `scalar (bits : Nat)`, with `width = ⌈bits / 26⌉` in the
  deployed base (`Dregg2/Bignum.lean` uses `Base = 2^26`).
- `Ty.digest` should be `width = 8` (the `Faithful8` octet), full stop.
- Injectivity then becomes a *theorem about the schema*, not a hope about a hash:
  `Dregg2/Bignum/DigitInjective.lean:42` `bignumVal_injective` already proves limb-vectors inject at
  any width, and `Dregg2/Bignum.lean:517` `legs_noWrap_conservation` already proves that under a
  range bound a mod-p field equation **is** the integer equation.

⚑ **`Dregg2/Bignum.lean` is exactly the right library and its adoption is worse than "~3%": it is
zero in the layer that matters.** Its real importers are seven files —
`Market/{QuantizedConservation:34, ExactGapNoWrap:47, PackedBookFamily:33}`,
`Dregg2/Shielded/{RealCrypto:66, WideNativePqCommitment:26}`,
`Dregg2/Deos/VaultSatDescriptor:51`, plus the root aggregator. **No file under `Dregg2/Exec/` imports
it.** The executor works over unbounded `ℤ` and hands the narrowing problem to the emit layer, which
has no type to catch it with. The four anti-exploit keystones (`antiExploit_no_underflow_wrap:630`,
`_no_overflow:637`, `_field_vs_integer:645`, `_canonical:652`) are proved and unused by the effect
algebra.

---

# PART 3 — THE RE-FACTORING

## 3.0 Read this first: the dead end, and the live prior art

`project-adjunction-thesis-verdict` is marked BROKEN with a replacement BUILT. The dead end was
"agreement and adjudication are the two adjoints of one Predicate⊣Witness adjunction" — a
**single-agent preorder closure** being mistaken for a knowledge structure. **I am not going near it.**
Nothing below claims an adjunction. The corrected structure that replaced it (a Lawvere
hyperdoctrine, `Dregg2/Metatheory/Lawvere.lean`, with the linear rung in `IndexedMonoidal.lean`) is
about *knowledge*, not about *state updates*, and is orthogonal to this document.

The live prior art that **is** relevant is one directory over, and it is better than anything in the
effect layer.

## 3.1 ⚑ The category we want already exists — for documents

`metatheory/Dregg2/Deos/PatchCategory.lean` is a full Mimram–Di Giusto categorical patch theory over
the `dregg-doc` graph, `#assert_axioms`-clean. Its op grammar (`:69`) is:

```lean
inductive Op where
  | add (id after : AtomId)   | del (id : AtomId)
  | connect (x y : AtomId)    | setField (n : Name) (v : Val)
  | resurrect (id : AtomId)   | disconnect (x y : AtomId)
  | retractField (n : Name)
```

**dregg has two `setField`s.** The document one has:

| property | `PatchCategory.Op.setField` | `Effect::SetField` |
|---|---|---|
| an inverse | ✅ `retractField` (`:69`), `patch.rs:272` `invert` | ❌ (Rust-only `Contextual`, unproven) |
| a `Category` instance | ✅ `categoryP` (`:147`) | ❌ |
| identity + associativity | ✅ free `List`-monoid laws | ✅ `execFullTurnA_append`, `turnSpec_nil` |
| a functoriality theorem | ✅ `applyPatch_functor_id:359`, `_comp:365` | ❌ (the action is proved; nobody calls it a functor) |
| commutation on disjoint parts | ✅ `DocPatch.lean:120-194` (six laws, plus the load-bearing **non**-commutation at `:178`) | ❌ (only the toy scalar kernel) |
| conflict as a first-class object | ✅ `no_conflictFree_pushout`, `conflict_object_is_pushout` (§5) | ❌ (last-writer-wins, silently) |
| non-degeneracy witnesses | ✅ `hom_not_thin:177`, `isoP_nontrivial:263` | ❌ |

**The effect layer was built as a case list; the document layer was built as an algebra.** The
document layer is *not* a model of cell state — `DocGraph.fields : Name → Finset Val` is multi-valued
so concurrent assigns clash into a conflict object, which is a genuinely different design. But it
demonstrates that this house can build the structure when it decides to, and it supplies the shape.

## 3.2 The factoring I would argue for

**Claim: `SetField` should be `Act`, and the slot should declare its own algebra.**

Right now a write carries a *value* and the slot carries a *predicate on (old, new)*, in two
unrelated languages. Factor it the other way: the slot declares a structure, and the write carries an
element of it.

```
current:   SetField (addr) (v : Value)     +  slotCaveats addr : List SlotCaveat
proposed:  Act      (addr) (m : M addr)    where M addr is the slot's declared update algebra
```

Read `SlotCaveat` as data about an algebra and it almost falls out:

| caveat | the algebra it is trying to declare |
|---|---|
| `immutable` | the trivial monoid `{0}` |
| `monotonicSeq` | ℕ, generated by `+1` |
| `monotonic` | ℕ under `+` (non-negative deltas) |
| `boundedBy lo hi` | the interval, as a subobject |
| `writeOnce` | a two-element poset (fresh ⊑ written) |
| `senderAuthorized`, `clearanceGe` | **misfiled** — these are about the *actor*, not the value |
| `admitTable` | the confession: "an arbitrary relation" |

Five of eight are "the new value is reachable from the old by an element of a declared monoid of
deltas." Two are authority conditions that belong to a different substance — and `VerbRegistry`
already says so: `authority` and `state` are distinct substances (`VerbRegistry.lean:~55-75`), so a
`SlotCaveat` gating on the actor is a capability facet wearing a state-caveat's clothes.

**What this buys, stated as checkable propositions rather than vibes:**

1. **Per-step and whole-transition admission agree by construction.** For a submonoid `M ⊆ (ℤ, +)`:
   `m₁, m₂ ∈ M ⟹ m₁ + m₂ ∈ M`, and conversely the composite delta of a run *is* the sum. §2.3.D's
   divergence class cannot be written down. (Weaker sufficient condition, if you keep predicates
   rather than deltas: **transitivity**. Six of the eight caveats already have it.)
2. **Same-slot writes commute.** `+` is commutative, so `Act f d₁ ; Act f d₂ = Act f d₂ ; Act f d₁`
   on the record. **This is the law the deployed permission-partition reordering
   (`execute_tree.rs:845`) silently needs and cannot currently state.** Today reordering is justified
   by a comment; under deltas it would be justified by a theorem.
3. **The AIR constrains membership, not comparison.** `d ∈ M` is a range check or a sign check — a
   `Lookup.rangeCheck`, which `Dregg2/Bignum.lean:568` `rangeClause_is_lookup` already emits. The
   `MA_DECOMP`/`MA_CMP` comparison blocks that the wide-key work plans to **delete** (not extend —
   extending is a house-law violation) are exactly the blocks that exist to compare *values*.
4. **The value width question decouples from the guard.** A delta's width is `M`'s business; the
   slot's width is the schema's. `Dregg2/Bignum.lean`'s add/sub keystones (`add_iff:241`,
   `add_overflow_unsat:299`, `sub_underflow_unsat:176`) are precisely the theorems an `Act` needs,
   and they hold at any width.
5. **`IncrementNonce` stops being a special case.** It becomes `Act nonceField 1` over `M = ℕ`, and
   `RecOp.addScalar` (`RecordCell.lean:41`) — which already exists — becomes the general form.

**And `SetField` survives**, as `Act` over the free monoid `M = ℤ` acting by *replacement* rather
than addition, i.e. the slot that declares "any value, any time." Most slots are that slot. The point
is that it becomes *one instance of a declared structure* instead of the only primitive with a
bolted-on predicate language.

## 3.3 What I will and will not call a functor

⚑ **A name is a claim.** Precisely what holds:

**PROVED, and it is a monoid action.** `execFullTurnA` is an action of the free monoid
`(List FullActionA, ++, [])` on `RecChainedState` in `Kleisli(Option)`. The unit law is definitional
(`PerAsset.lean:2303`); the composition law is `execFullTurnA_append` (`:2426`). Equivalently: a
monoid homomorphism into the monoid of partial endomaps under Kleisli composition. **I checked the
statements; I did not run the proofs.** This is the same content as `applyPatch_functor_id` /
`applyPatch_functor_comp` in `PatchCategory.lean:359,365`, which *is* stated as functoriality —
so the naming asymmetry between the two layers is purely rhetorical.

**PROVED, and it is not a functor.** The map `FullActionA → descriptor` (`Rfix`,
`CircuitSoundnessAssembled.lean:400`) is a **partial function on objects with a catch-all**
(`| _ => 1000`, `:392`). It has no action on morphisms because the descriptor side has no
composition — the AIR is per-row, and multi-effect composition happens in the trace, not the
descriptor. Calling `Rfix` a functor would be laundering. What the per-effect closure theorems
(`*_descriptorRefines_sat`, 25 of them) establish is a **family of refinement squares**, one per
effect, not a natural transformation.

**ASSUMED, not checked, and I flag it as the sketch's obligation.** That the deployed executor's
normalization `N` is a monoid *quotient* rather than an arbitrary reshuffle. `N` is idempotent and
order-preserving within each bucket, which makes it a normal form; whether the induced relation is a
congruence is exactly the commutation question in §3.2(2), and **it is currently open**. This is the
one place where the refactoring is not merely cleaner but load-bearing for a deployed security fix.

**NOT claimed:** no adjunction, no limit/colimit story, no pushout. dregg's cell state is
single-writer within a totally-ordered turn; there is no span to complete and no conflict object to
find. `PatchCategory`'s pushout machinery is right for documents and would be cargo-culting here.

---

# PART 4 — THE PLAN

Ranked by (value ÷ cost). Every item marked **Lean-authored** or **Rust-mirror**, and every item that
would change the **emitted** program flagged ⚑EMIT — those need a re-emit, a re-proof, a VK epoch, and
an archived-run check against `~/dev/dregg-devnet-archives`.

### Tier 0 — free, today, no emit change

**P0.1 — Fix `docs/reference/effect-vocabulary.md`.** *Docs. Hours.* It names the wrong two effects
as lacking a rung (`SetProgram` has one: `CircuitSoundnessAssembled.lean:544`), says 33 where the enum
says 36, tabulates 32 rows, and omits `Custom`/`CreateHybridCell`/`RotatePqIdentity` entirely. Also
`Dregg2.lean:1008`'s stale `setProgramA` residual. The real count of rung-less effects is **7**.

**P0.2 — Resolve the `proofBind` contradiction.** *Docs + one read.* `EFFECTVM-AIR-VERIFICATION-CENSUS.md:50`
and `DescriptorIR2.lean:651-656` say opposite things about whether the fold backs `proofBind`
in-circuit. Re-read the fold; correct whichever is stale. The census's line anchors have all drifted
and should be re-pinned.

**P0.3 — Settle §2.3.D with a differential test.** *Rust-mirror. A day.* Two turns, run through both
executors: `monotonic` + `[SetField f 5, SetField f 1]` (predicted: Rust commits, Lean refuses) and
`monotonicSeq` + `[SetField f 1, SetField f 2]` (predicted: Lean commits, Rust refuses). If the
prediction holds, the first is an authority inversion in the wrong direction and should be logged as
a wound. **I derived these; I did not run them.**

**P0.4 — Fix or explain `FieldsMap.lean:47`.** *Lean-authored. Hours.* `reservedKeys := 8` with a
header asserting `STATE_SLOTS = 8` against Rust's 16 (`cell/src/state.rs:57`). Either the Lean
`fields_root` preimage is wrong on keys 8..15, or the three separate meanings of "8" need
disentangling in one comment.

### Tier 1 — high value, additive, no emit change

**P1.1 — ⚑ Port `Effect::invert` into Lean and prove it.** *Lean-authored. ~1 week.* The best piece of
effect algebra in the tree is in Rust (`turn/src/reversible.rs:235`), exhaustive-by-rustc and
unproven. In Lean it becomes: `invert : FullActionA → RecChainedState → Inversion`, with
`Clean`/`Contextual`/`Committed` and the eight reasons, plus the theorem the doc comment claims —
`execFullA s (invert e s) ∘ execFullA s e = id` **modulo the log and the nonce ratchet**
(`ledgers_agree_modulo_nonce`, `reversible.rs:1165`, is the honest statement of the quotient). This
also gives the *first* formal content to "a turn is replayable", which currently has none (§2.2).
Directly closes a `minted-census-from-the-lean-side` instance: a whole subsystem with no Lean twin.

**P1.2 — Make the read set real.** *Rust-mirror first, then Lean.* Everything is built except the
emitter: `ReadSet` (`cell/src/program/types.rs:391`, inert), `MemoryChecking.Kind.read`,
`UniversalMemory`, the `BUS_UMEM_*` buses, and `FogOfWar.noninterference` as the consumer. Change
`turn/src/umem.rs:2403` `emit_trace` to source reads from something other than the undo journal, and
`UmemKind::Read` starts appearing. This is the prerequisite for any fog claim that binds the *prover*
rather than the *viewer*. ⚑EMIT once the read rows enter a deployed descriptor.

**P1.3 — State the composition laws that are currently comments.** *Lean-authored. ~1 week.*
Three theorems that should exist and do not:
  - `execFullA_comm_disjoint` — two effects on disjoint cells commute, over `RecordKernelState`
    (today only the toy scalar kernel has it: `ContendedCrossCell.lean:176`).
  - `setField_overwrite` — `run [a, b] = run [b]` **modulo the log**, under a transitive caveat. This
    is the absorption law, correctly qualified.
  - `perStep_implies_whole` — per-write admission implies whole-transition admission when the caveat
    relation is transitive, plus the refutation that `monotonicSeq` is not.
  These are the sketch in `metatheory/EffectAlgebraSketch.lean` (§4.0), promoted to the real types.

**P1.4 — Model the permission partition in Lean, or delete it from Rust.** *Lean-authored + Rust-mirror.*
`execute_tree.rs:845-848` reorders; Lean does not know. Either (a) add `N` to the Lean fold and
re-derive `execFullTurnA_append` for `N`-normalized lists, or (b) prove the reorder unnecessary
because permission effects commute with the rest under the *original* snapshot semantics (the comment
at `:836-838` claims the checks already use the original permissions, which if true means the reorder
is belt-and-braces). ⚑ Until one of these lands, the associativity law the forest lift rests on is
false of the deployed executor whenever an action mixes a permission effect with anything else.

### Tier 2 — the emit-changing repairs

**P2.1 — ⚑EMIT Deploy the staged `setFieldValue8`.** *Lean-authored, already written.* The R1
large-value completeness seam is closed on disk and not deployed:
`withSetFieldCompletionPins` (`EffectVmEmitRotationV3.lean:5656`), emitted by
`metatheory/EmitRotationV3SetFieldValue8.lean`, `piCount` 46→53, positive tooth at
`circuit/tests/setfield_value8_epoch_flip.rs:164`. Additive beside `v3RegistryBare`; old epochs stay
verifiable. **This is the cheapest real win in the document** — the work is done. ⚑ VK epoch,
re-emit, archived-run check.

**P2.2 — ⚑EMIT Force the reserved-slot bar on the dynamic path.** *Lean-authored.*
`setFieldDyn_descriptorRefines_sat` (`RotatedKernelRefinementMisc.lean:629`) carries
`reservedField f = false` as a hypothesis. Since `gSlotRange` already pins the address to `{0..7}` by
a degree-8 product (`EffectVmEmitV2.lean:1343`), forcing "not one of the four reserved names" is a
small additional gate on the same column. Closes the last off-AIR leg of the nonce-reset vector.

**P2.3 — ⚑EMIT Reconcile the three address spaces.** *Lean-authored, and it is a rewrite.* Today:
`u64` over 16+map (Rust), `String` over an assoc list (Lean), `Fin 8` (AIR, both static and dynamic).
Any honest resolution picks one and derives the others with an injection theorem. Note the AIR is the
binding constraint — **eight slots** — so "make the AIR match Rust" is a real widening (56 completion
lanes already exist for 8 slots; 16 would double them), and "make Rust match the AIR" is a breaking
wire change. Do not start this without deciding which layer is canonical. Related and already scoped:
`docs/DESIGN-wide-mapop-keys.md` (16 surfaces, assessed DO IT, one epoch).

**P2.4 — ⚑EMIT Give `ExerciseViaCapability`'s inner effects rows.** *Lean-authored.* Today N inner
state changes are constrained by one `exercise_hash` column (`effect_vm_bridge.rs:763-773`). A light
client sees which effects were *claimed*, not that the state moved accordingly.

### Tier 3 — the refactoring proper

**P3.1 — `Ty` carries its width.** *Lean-authored. ⚑EMIT.* Replace `width .digest => 1`
(`Dregg2/Exec/Value.lean:78`) with a schema-declared limb count, and make injectivity a theorem via
`Dregg2/Bignum/DigitInjective.lean:42` rather than a hope about a hash. **This is the root of the
felt-width class**, upstream of every encoder in the catalogue, and it is one definition.

**P3.2 — `Act` over a declared slot algebra.** *Lean-authored. ⚑EMIT. This is a rewrite.* §3.2. Add
the delta form (`RecOp.addScalar` already exists at `RecordCell.lean:41`), let a slot declare its
update monoid, and the per-step/whole divergence, the reordering justification, and the value-width
coupling all resolve at once. Land it *beside* `SetField` — `SetField` is `Act` over the free
replacement monoid, so this is additive until the day you decide it isn't.

**P3.3 — Move `senderAuthorized` and `clearanceGe` out of `SlotCaveat`.** *Lean-authored + Rust-mirror.*
They gate on the actor, not the value. `VerbRegistry` already says authority and state are distinct
substances. They belong on the capability facet, where the `EFFECT_SET_FIELD` mask already lives
(`turn/src/action.rs:2759`).

**P3.4 — Retire the toy.** *Lean-authored. Hours.* `Dregg2/Spec/Conservation.lean:154`'s
3-constructor `Effect` should say `ExampleEffect` in its name, so no future reader or agent cites
`linearity_examples` as a statement about the vocabulary.

---

## Appendix A — the honest ledger of this document

**Checked by reading the definition:** every `file:line` above. All Lean type signatures, all Rust
struct/enum shapes, the partition site, the caveat dispatch on both sides, the AIR column arithmetic.

**Read but not run:** every theorem cited. `execFullTurnA_append`, the 25 `*_descriptorRefines_sat`,
`minimality`, `noninterference`, the `Bignum` keystones — I read their statements and their
`#assert_axioms` annotations. I did not elaborate them.

**Derived, not measured:** §2.3.D's two divergence witnesses. They follow from `caveatsAdmit`
(per-write, `EffectsState.lean:248`) and `evaluate_cell_program_for_executor` (per-action, whole
transition, `execute_tree.rs:175/1175`, with the pre-action snapshot at `:827-831`). P0.3 settles them.

**Asserted on a subagent's reading, not my own:** the exact contents of
`producer_root_agreeing_effects` (`exec-lean/src/lean_shadow.rs:493`, 18 entries) and
`producer_root_gap_effects` (`:625`, three entries: `NoteSpend`, `NoteCreate`, `RevokeCapability`);
the `@[export]` census (175 attributes, 31 files, **none** on any semantic step function — the
production turn entry is `dregg_exec_full_forest_auth`, `Dregg2/Exec/FFI.lean:2380`); the deployed
`"kind":"read"` counts per registry TSV.

**Not investigated:** the `effect_kind` catch-all at `exec-lean/src/lean_shadow.rs:432-433`
(`_ => "Unknown"`) reportedly swallows 9 of 36 variants. If true that is a `GATING DEFAULTS TO
SILENCE` instance on the Lean-shadow boundary and deserves its own look.

## Appendix B — the sketch

`metatheory/EffectAlgebraSketch.lean` — a **standalone, unimported, UNELABORATED** Lean model of the
argument in §2.3.D and §3.2. It is self-contained (no mathlib, no `Dregg2` imports) so it can be
checked with a bare `lake env lean`. It proves, in a toy model:

- absorption fails, on the log and on the guard, separately;
- per-step ⇏ whole (`monotonicSeq`) and whole ⇏ per-step (`monotonic`) — both directions;
- **transitivity is exactly the condition** that repairs the first direction;
- under the delta factoring, per-step ⟺ whole, and same-slot writes commute.

⚑ It has **not been run** (no `lake build`, task constraint). Treat every proof script in it as a
proposal, not a result.

---

*Companion documents: `docs/reference/effect-vocabulary.md` (needs P0.1),
`docs/deos/EFFECTVM-AIR-VERIFICATION-CENSUS.md` (needs P0.2),
`docs/audit/TRUST-BASE-CENSUS.md` §S1 (the setField completeness seam),
`docs/WOUND-felt-width-boundaries-2026-07-19.md` (the width catalogue),
`docs/DESIGN-wide-mapop-keys.md` (the key-widening epoch).*
