# The Semantic Lean Boundary — where the constraint vocabulary actually lives

**Status:** audit, 2026-07-17. Not committed. No source edited. This is a map + a
migration plan for ember to approve before any refactor.

**The thesis under test (ember, verbatim spirit):** "There should be NO semantic
objects, especially load-bearing ones, that are only implemented in Rust." The
project rule (CLAUDE.md): AIR / circuits / CONSTRAINTS / gadgets are AUTHORED IN
LEAN; Rust only CALLS INTO the Lean artifact. A *constraint vocabulary* is
exactly "constraints" — it MUST be Lean-sourced.

**Verdict up front:** the thesis holds, at full force, for the entire
program/constraint semantic layer. The object every cell program, every game,
and every turn is written in — `CellProgram` / `StateConstraint` /
`SimpleStateConstraint` / `HeapAtom` / `TransitionCase` — is **defined in Rust**
(`cell/src/program/types.rs`) and its **meaning is authored in Rust**
(`cell/src/program/eval.rs`), enforced on the live admission path
(`turn/src/executor/execute_tree.rs:1023`). The Lean holds a large, genuine,
axiom-clean **parallel** vocabulary that **never reaches** the deployed object.
Nothing machine-checks Rust-enum == Lean-inductive or Rust-evaluator ==
Lean-evaluator. The one genuinely Lean-sourced corner in the whole layer is the
**fixed effect-VM descriptor registry** (Lean-emitted JSON, drift-gated) — which
is a different path and does not touch the CellProgram/StateConstraint bridge.

Ground-truth checks run for this audit (all confirmed):
- `cell/Cargo.toml`, `turn/Cargo.toml`: **no** lean/ffi dependency.
- `metatheory/Dregg2/Exec/Program.lean`: **zero** `@[export]`.
- `cell/src/program/`: **no** `include_str!` / `include_bytes!` / `emitVmJson` / `extern` artifact load.
- `cell/src/`: **zero** `ConstraintExpr::` references (the AIR-lowering vocabulary never touches the caveat vocabulary).
- `cell/src/program/eval.rs:2842` `field_gte(a,b) = a >= b` — **unsigned** 256-bit big-endian `FieldElement` compare.
- `metatheory/Dregg2/Exec/Program.lean:456` `.fieldGe f val => intLe val x` over `Value.scalar` — **signed** unbounded `Int`, absent-if-zero. **The two FieldGte definitions differ in data model and operator.**
- `scripts/check-descriptor-drift.sh` + `metatheory/EmitAllJsonV2.lean`: the effect-VM descriptor registry **is** Lean-emitted and drift-gated (the one bright spot).

---

## 1. THE ROT MAP

Three classes. Ranked within each by: (a) does deployed soundness depend on it,
(b) is that dependence machine-checked-to-the-deployed-object.

### Class A — RUST-CANONICAL (Rust-defined semantic object, no Lean source). THE ROT.

The type/semantics is the source of truth in Rust; Lean has no emit for it.

| Object | Where (Rust) | Deployed-soundness-depends | Machine-checked to deployed object |
|---|---|---|---|
| `StateConstraint` — the 40–60-variant constraint alphabet (FieldEquals/FieldGte/FieldLte/FieldLteOther/SumEquals/WriteOnce/Immutable/Monotonic/StrictMonotonic/AnyOf/AllOf/AffineLe/AffineEq/Witnessed/HeapField/Custom/…) | `cell/src/program/types.rs:970` | **MAXIMAL** — every cell program/game/turn is written in it | **NO** — dead-ends at the hand-written enum |
| The constraint TEETH (what each variant enforces): `evaluate_constraint_full` / `evaluate_simple_constraint` / `evaluate_heap_atom` | `cell/src/program/eval.rs:264`, `:2627`, `:2322`; helpers `field_gte`@`:2842` | **TOTAL** — this Rust `match` IS the enforcement | **NO** — checked object is a different Lean function on a different state model |
| `CellProgram` (None / Predicate / Cases / Circuit) — the top-level program shape | `cell/src/program/types.rs:6` | **TOTAL** — the per-cell law gate, re-evaluated every state-modifying turn | **NO** — Lean `RecordProgram`/`Exec.CellProgram` are different shapes, never linked |
| `SimpleStateConstraint` (SenderIs/SenderInSlot/SenderMemberOf/BalanceGte/BalanceLte/BalanceDelta*/PreimageGate/HeapField/DelegationEpochEquals/CountGe + the Heyting `Not` smart-ctor) | `cell/src/program/types.rs:535`, ctor `:848`, eval `eval.rs:2627` | **YES** — the composition fragment (per-slot actor binding, polis quorum shapes) | **NO** |
| `HeapAtom` (Equals/Gte/Lte/Immutable/WriteOnce/Monotonic/StrictMonotonic/MemberOf/InRangeTwoSided/DeltaBounded/DeltaEquals) — the heap/app-state lane with fail-closed absence semantics | `cell/src/program/types.rs:468`, eval `eval.rs:2322` | **YES** — the "apps live in the heap" rung (Bazaar purses); absent≠present-zero is load-bearing | **NO** |
| `TransitionCase` / `TransitionGuard` (Always/MethodIs/EffectKindIs/SlotChanged/AnyOf/AllOf) + default-deny rule (`is_method_dispatching`) | `cell/src/program/types.rs:62`, `:84`, matches `:213`, `:258` | **YES** — default-deny is the security-critical gate (stapleable-slot class) | **NO** |
| `ConstraintExpr` — the 21-variant custom-leaf AIR vocabulary (Equality/Multiplication/Hash2to1/4to1/3Cap/MerkleHash/MerkleHash8/ChainedHash2to1/TableFunction/Lookup/…) | `circuit/src/dsl/circuit.rs:125` | **YES** — every custom-VK cell program is lowered from this | **NO** — Lean has only a re-authored 9-of-21 subset (`CellLocal`) |
| `lower_cellprogram` / `cellprogram_to_descriptor2` / `gate_body` — the ConstraintExpr→VmConstraint2 lowering | `circuit/src/custom_leaf_lowering.rs:524`, `:516`, `:36` | **CRITICAL** — a dropped/weakened gate lets a forged trace re-prove and fold | **NO** — Rust-only for hash/lookup/table, mirror-only for the 9 algebraic kinds |
| The cryptographically HARD lowerings: `chip_lookup_site` (Poseidon2→TID_P2 lookup), `merkle_children_exprs` (Lagrange child reconstruction), `table_function_body` (bivariate Lagrange), `fill_chain_columns`/ChainedHash2to1 (copy-forward accumulator) | `circuit/src/custom_leaf_lowering.rs:204`, `:295`, `:377`, `:482`, `:720` | **CRITICAL** — carries the actual cryptographic content (Merkle-open, running-hash) | **NO** — not even a disconnected Lean mirror exists; correctness is doc-prose + roundtrip tests |
| SDK program producer: `CellProgramBuilder` / `programmed_cell_descriptor` — hand-assembles Rust atoms into `CellProgram::Predicate` and content-addresses with a Rust blake3 over postcard | `sdk/src/program.rs:164`, `:136` | **YES** — how custom cells get their law; a mirror-free Rust producer | **NO** (n/a — no Lean in the loop) |
| `StateConstraintView` / `to_view` — the self-describing live projection served by `node get_cell_detail` / `wasm get_cell_state` | `cell/src/program/view.rs:69`, `:737`, `:619` | inspection/audit UIs depend on shown==enforced | **NO** — Rust-only, no Lean twin even claimed |
| **Deployed game/app policies** (all author `CellProgram::Cases`/`Predicate` directly in Rust): multiway-tug `state.rs:253` / `hidden_hand.rs:783`; automatafl `game.rs:174`; `dregg-schema::emit_program` `emit.rs:150`; spween-dregg `compiler.rs:412`; dungeon-on-dregg `combat.rs:678`+7 more; faction `dreggnet-faction/src/lib.rs:265`; quest `dreggnet-quest/src/lib.rs:217`; governed-namespace `governed-namespace/src/lib.rs:369` | (see slice 4) | **YES** — each IS the deployed referee | **NO** for all; **faction / quest / spween / dungeon have no Lean spec at any resolution** |

**Postcard-by-variant-index is the tell.** The `StateConstraint`/`HeapAtom`
docstrings repeatedly say "APPEND-ONLY: postcard variant indices … factory VKs /
content addresses byte-identical." That means the **Rust enum layout literally
defines the wire identity and the content address.** The wire identity of the
constraint language is a property of the Rust definition, not of any Lean object.

### Class B — PARALLEL-DISCONNECTED-PROOF (real Lean proof that never reaches the deployed Rust). THE MOST DANGEROUS.

It *looks* verified (green `#assert_axioms`, `_iff` lemmas, "refines" theorems)
while the deployed arm is free to drift with nothing red.

| Object | Where (Lean) | Proves about | Missing link |
|---|---|---|---|
| `evalConstraint`/`evalSimple` + admit-char theorems (`evalConstraint_affineDeltaLe_iff`, `evalSimpleCtx_senderMemberOf_iff`, `evalHeap_*_iff`, …) + `#assert_axioms` — the "Lean twin (LAW #1, the source of truth)" the Rust docstrings cite | `metatheory/Dregg2/Exec/Program.lean:520`, `:454`, `:806`, `:819`, `:1043` | Lean `evalConstraint` over name-keyed `Value` records | No `@[export]`; no Rust loader; **substrate mismatch** (Rust `[FieldElement;16]`+`fields_map` vs Lean `FieldName→Value`); **variant-set divergence** (Lean has `affineDeltaLeField` Rust lacks; Rust has `Renounced`/`ClearanceDominates`/`SettleEscrow`/`VaultDeposit` Lean omits). Link is the docstring string only. |
| **FieldGte semantic divergence** (a concrete, confirmed disagreement, not hypothetical) | Rust `eval.rs:2842` `a >= b` unsigned-256; Lean `Program.lean:456` `intLe val x` signed `Int`, absent-if-zero | — | The two definitions **disagree** near the field modulus, on the sign boundary, and on absent-vs-zero. Nothing checks agreement; nothing *can*, because the Lean is never invoked and the program never crosses the wire. |
| `CustomLeafEncoding.lean` — `encodeLocal_holdsAt_iff` / `cell_to_descriptor_faithful` (the "faithful-encoding twin" that looks like it proves the lowering) | `metatheory/Dregg2/Circuit/CustomLeafEncoding.lean:128`, `:212`, `:88`, `:100`, `:119` | A re-authored 9-of-21 `CellLocal`/`gateBody` mirror | (1) `gateBody` is "term-for-term the Rust" *by prose*, no emit, no differential pin. (2) `CellLocalHolds` is *defined as* `gateBody` vanishing → the "faithfulness iff" is a **carrier-reduction tautology** (`simp [holdsVm]`). (3) omits every hard kind. (4) **not imported into `Dregg2.lean`** — an island outside the main theorem graph. |
| `Exec.CellProgram` + `Guard` DSL + `denote_conserves` (the "developer-facing coalgebra") | `metatheory/Dregg2/Exec/CellProgram.lean:76`, `:39`, `:116`, `:177` | An 8-constructor toy `Guard` (tt/ff/authorized/amountLe/reserveSrc/selfOnly/and/or) | Shares only the **name** `CellProgram` with the deployed 40-variant enum; different arity; the module itself flags the real coalgebra instance as **OPEN** (`:177`). |
| `MultiwayTug.lean` `applyAction` + conservation/win-safety + `AirSpec` | `metatheory/Dregg2/Games/MultiwayTug.lean:203`, `:234`, `:456`, `:463` | A Lean multiset model of Hanamikoji rules | `multiwayTug_air_refines_applyAction` is literally `h o p a n` — an **application of a carried hypothesis**; header says "the AIR predicate is HYPOTHESIZED … NOT yet discharged — Lane-D-gated." Deployed object is `state.rs::program()` (register counters + `SumEquals==21`), which the Lean **does not model** (Lean uses per-player `Multiset` + Merkle hand). |
| `MultiwayTugAir.lean` `airPlay` + `airPlay_iff_applyAction` (titled "THE CONNECTED REFINEMENT") | `metatheory/Dregg2/Games/MultiwayTugAir.lean:105`, `:117`, `:81` | Non-vacuous within Lean (MerkleSound is load-bearing) | `airPlay`↔`fold.rs::membership_leaf_for_play` is **pure doc-comment prose** ("the Lean shadow of fold.rs"); carries **two** undischarged hypotheses (`MerkleSound` `:81`, `AirSpec` `:138`). The "CONNECTED" in the title is a claim, not a checked link. |
| `AutomataflAir.lean` `airAutomatafl` + `airAutomatafl_iff_applyTurn` + `concreteAutomataflAIR_refines` (titled "TRANSLATION VALIDATION … discharges air.Refines for the emitted circuit") | `metatheory/Dregg2/Games/AutomataflAir.lean:107`, `:117`, `:145`, `:85`, `:97` | Abstract `MoveGadget`/`StepGadget` structures (opaque resolve/step) | `MoveSound`/`StepSound` discharged only for `idealMoveGadget`/`idealStepGadget` **by rfl**; the **deployed** `air.rs::automaton_gadget`/`moves.rs` is never shown to satisfy them. Still parametric, not the emitted circuit. |
| `governed-namespace` `nsCaveats` (a re-authored mirror of the deployed `governance_program()`) | `metatheory/Dregg2/Apps/GovernedNamespace.lean:44` | A second, independent Lean declaration of "the same" constitution | Connected to Rust `governance_program()` only by matching slot-name **strings** ("governance_committee_root"). Representative of the whole `Dregg2/Apps/*` deos-app family (Identity, Subscription, StorageGatewayMandate, EscrowDeskCouncil, …). |
| `Circuit/Spec` effect specs (`SetProgramSpec`, `SetFieldSpec`) + `StateWriteAbstractBinding` + `stateStep`/`execFullA` executor model | `metatheory/Dregg2/Circuit/Spec/cellstateprogram.lean:100`, `:226`; `StateWriteAbstractBinding.lean:80` | The Lean `execFullA` executor MODEL (re-authored parallel to `turn/src/executor/apply.rs`) | Nothing checks `execFullA` == the Rust `apply.rs`. **Critically:** `SetProgramSpec` treats the program slot as `.int prog` (an opaque integer) — so the constraint-checking semantics are **modelled nowhere** here. |
| `Turn.lean` `turnSpec` fold; `UniversalBridge` `*_is_memory_program`; `CrossCellBisim` `xcellCoalg` confluence | `metatheory/Dregg2/Circuit/Spec/Turn.lean:33`; `Exec/UniversalBridge.lean:483/589/729`; `metatheory/Metatheory/Open/CrossCellBisim.lean` | Lean-model ↔ Lean-model bridges (exec-model ↔ memcheck-spec; cross-cell confluence over `applyHalfOut`) | Both ends are Lean; never bridged to the Rust executor/emitter. `CrossCellBisim` is honestly self-labeled **OPEN**. |

### Class C — LEAN-SOURCED (authored in Lean, emitted, Rust loads/calls). THE TARGET — and today it is nearly empty for this layer.

| Object | Where | Note |
|---|---|---|
| Effect-VM descriptor registry (`transferVmDescriptor2`, `setFieldVmDescriptor2-*`, `burnVmDescriptor2R24`, rotation/umem-cohort registries) — the FIXED effect descriptors | `circuit/src/effect_vm_descriptors.rs:567` + `circuit/descriptors/*.json`; emitted by `metatheory/EmitAllJsonV2.lean` (`EffectVmEmitV2.v2Registry`); drift-gated by `scripts/check-descriptor-drift.sh` | **The one bright spot.** The descriptor *bytes* are the byte-exact output of the Lean executable, checked in as a cache, regenerate-and-diff gated with SHA-256 freshness pins. Rust `parse_vm_descriptor2` loads them. **Caveats:** (a) it is a FIXED effect set (transfer/setField/…), **NOT** the CellProgram custom-leaf lowering — "the game says FieldGte" never flows through here; (b) the AIR that gives the bytes meaning (`Ir2Air`/`VmConstraint2` eval, `descriptor_ir2.rs:654/605`) is still Rust, with the Lean `holdsVm` a mirror. |
| Layout: `layout_generated` (cited by memory as an example) | (per project record) | Lean-emitted layout artifact; same shape as descriptors — proof the emit-and-load pattern already works in this codebase. |

**Bottom line of the map.** Of the program/constraint semantic layer:
- **~90–95% RUST-CANONICAL** — the constraint vocabulary, its teeth, the program
  structure, the AIR lowering, and every deployed policy.
- **A large PARALLEL-DISCONNECTED shadow** — a full Lean re-implementation
  (`Program.lean`), per-game refinements, per-app mirrors — all real, all
  axiom-clean, **none machine-checked to the deployed Rust object**.
- **Essentially 0% genuinely LEAN-SOURCED** for the *constraint* semantics. The
  only Lean-sourced artifact in the layer is the **fixed effect descriptor set**,
  which is a different path.

The most dangerous items are the Class-B "titled-as-connected" ones —
`MultiwayTugAir.lean` ("THE CONNECTED REFINEMENT"), `AutomataflAir.lean`
("discharges air.Refines for the emitted circuit"), and
`CustomLeafEncoding.lean` (`cell_to_descriptor_faithful`) — because the header
prose narrates a discharged connection where the machine-checked chain actually
terminates at a carried hypothesis or a re-authored mirror.

---

## 2. THE DEAD-ENDS — where "the system is verified" rests on nothing that reaches deployment

### 2a. The constraint semantics has THREE independent sources that could disagree

For a single tooth like **FieldGte**, there are three definitions of what it means,
and **no machine-checked agreement between any pair**:

1. **Executor (Rust):** `evaluate_constraint_full` → `field_gte(&new_state.fields[idx], value)` = `a >= b`, **unsigned** 256-bit big-endian, over `[FieldElement;16]` + `fields_map`. `cell/src/program/eval.rs:280`,`:2842`. *This is what actually admits/rejects a turn* (`turn/src/executor/execute_tree.rs:1023`).
2. **AIR lowering (Rust):** for the *Circuit* variant, a `CellProgram` is lowered via `ConstraintExpr`→`VmConstraint2` in `circuit/src/custom_leaf_lowering.rs` — **but `StateConstraint::FieldGte` is never lowered to an AIR at all** (zero `ConstraintExpr::` in `cell/src`). The Predicate/Cases teeth have **no** in-circuit enforcement; the STARK path is the separate effect-VM (transfer/setField). So this "source" is *absent* for the caveat vocabulary — the caveats are Rust-admission-only.
3. **Lean spec:** `evalConstraint … .fieldGe f val => intLe val x`, **signed** unbounded `Int`, absent-field-if-zero, over `FieldName→Value` records. `metatheory/Dregg2/Exec/Program.lean:456`.

Sources 1 and 3 **provably differ** (unsigned-256 vs signed-`Int`, `[16]`+map vs
record, present-zero vs absent). Source 2 doesn't exist for this vocabulary. The
Lean `_iff` theorems prove properties of source 3, which the deployment never
runs. **A bug in `eval.rs`'s FieldGte arm is a pure-Rust soundness hole with no
proof above it, and the Lean "twin" would stay green.**

### 2b. The airPlay-vs-program() gap, enumerated per game/policy

"Does a Lean spec reach the deployed program?" — for every policy family found:

| Policy family | Deployed program (Rust) | Lean spec? | Reaches deployed via machine-checked refinement? |
|---|---|---|---|
| multiway-tug (counter-model) | `state.rs:253` `CellProgram::Cases` | `MultiwayTug.lean` + `MultiwayTugAir.lean` | **NO** — `AirSpec`/`MerkleSound` carried hypotheses; Lean models multisets, Rust deploys counters |
| multiway-tug (Merkle-fold) | `hidden_hand.rs:783`, `fold.rs::membership_leaf_for_play` | `MultiwayTugAir.lean` `airPlay` | **NO** — `airPlay`↔`fold.rs` is doc-comment prose + two undischarged hyps |
| automatafl | `game.rs` `Cases`; the oracle is the LEAN (`rules.rs` → `@[export] dregg_automatafl_rules`, 2026-07-25 — `reference.rs` deleted) | `AutomataflRules.lean` (spec) + the emitted `automatafl{Resolve,Step}DescN` | **PARTLY** — the off-circuit ORACLE now IS the Lean spec (no Rust twin left to diverge). The in-circuit leg is a Lean-EMITTED descriptor refined against `roundStep`; what carries no proof is the Rust WITNESS GENERATOR that fills its trace |
| generic schema games (Descent, …) | `dregg-schema::emit_program` `emit.rs:150` | `RotatedLayout.lean` (pattern only) | **NO** — correctness by Rust driven test (`dregg-schema/tests/refinement.rs`), not Lean |
| governed-namespace | `governed-namespace/src/lib.rs:369` | `GovernedNamespace.lean` | **NO** — re-authored mirror linked by slot-name strings |
| deos-app family (Identity/Subscription/StorageGatewayMandate/EscrowDeskCouncil/…) | `starbridge-apps/*` | `Dregg2/Apps/*.lean` | **NO** — same re-authored-mirror shape |
| faction | `dreggnet-faction/src/lib.rs:265` | **none** | n/a — Rust-only, no Lean at any resolution |
| quest | `dreggnet-quest/src/lib.rs:217`, `giver.rs:179` | **none** | n/a — Rust-only |
| spween-dregg stories | `spween-dregg/src/compiler.rs:412` | **none** | n/a — Rust-only compiler for all story/dungeon/dialogue content |
| dungeon-on-dregg (combat/spells/skills/meta/overworld/progression/dialogue/dsl) | `dungeon-on-dregg/src/*.rs` (8 sites) | **none** | n/a — Rust-only |

**Count:** ~10 deployed policy families. **4** have a Lean spec (multiway-tug,
automatafl, governed-namespace, deos-apps). **0** reach the deployed program via
a machine-checked refinement. **~50%** of families have **no Lean at any
resolution**. Not one deployed policy has its correctness machine-checked to the
deployed object.

### 2c. The prompt's canonical example is worse than rot — it doesn't exist

"FieldGte in a CellProgram produces an AIR that admits iff x≥y" — **there is no
such bridge.** `StateConstraint` is Rust-defined and Rust-*evaluated* (admission
predicate), never lowered to any AIR (zero `ConstraintExpr::` in `cell/`). The
STARK-provable circuit path (`ConstraintExpr`/`lower_cellprogram`) is a *separate*
lower-level vocabulary for the *Circuit* variant, and even there the hard kinds
(Merkle/hash/table) have no Lean mirror at all.

---

## 3. THE TARGET — the constraint layer authored IN LEAN and EMITTED

Not verify-the-mirror (a byte-pin blessing the Rust). Not codegen-from-a-DSL (a
new mirror). **The semantic object IS the emitted Lean artifact; the Rust
definition is DELETED; Rust loads/dispatches the artifact.** This is exactly the
pattern that already works for `effect_vm_descriptors` + `layout_generated`.

What Lean must define/emit, and what Rust gets deleted:

**T1 — The constraint vocabulary as the emitted type.**
- **Lean authors:** one canonical `StateConstraint` / `SimpleStateConstraint` /
  `HeapAtom` / `TransitionCase` / `TransitionGuard` / `CellProgram` inductive,
  over ONE canonical state substrate that matches deployment
  (`[FieldElement;16]` + heap map — **not** name-keyed `Value` records; the
  substrate unification is the load-bearing part, see §5).
- **Lean emits:** the variant tag ↔ postcard-index table + the field/type schema
  as an `@generated` artifact (the way descriptors emit JSON). Because postcard
  variant indices ARE the wire identity, the emitted table *becomes* the wire
  spec.
- **Rust deletes:** the hand-written `enum StateConstraint` (`types.rs:970`) et
  al.; Rust generates its (de)serialization from the emitted schema or loads a
  generated `.rs`. The enum is no longer hand-maintained; drift is impossible by
  construction, gated like `check-descriptor-drift.sh`.

**T2 — The teeth (constraint semantics) as a proven Lean function, exported.**
- **Lean authors:** `evalConstraint`/`evalSimple`/`evalHeap` over the canonical
  substrate, with the FieldGte/WriteOnce/Monotonic/… semantics that today live in
  `eval.rs` — but as the *source*, with the `_iff` characterization theorems now
  stated about **the same function Rust runs**.
- **Lean emits/exports:** `@[export]` the evaluator (or emit it as a proven
  lowering to a small decision artifact Rust can execute), so the admission
  decision is *computed by the Lean-sourced object*.
- **Rust deletes:** `evaluate_constraint_full` / `evaluate_simple_constraint` /
  `evaluate_heap_atom` (the ~2900 lines of `eval.rs` match arms). Rust's
  `evaluate_full` becomes a thin caller into the exported evaluator.
- **Payoff:** the `#assert_axioms`-clean `_iff` theorems finally constrain the
  *deployed* decision. §2a's three-sources-that-disagree collapses to one.

**T3 — The AIR lowering as a proven Lean function.**
- **Lean authors:** `ConstraintExpr` (the 21-variant circuit vocabulary) and
  `lower_cellprogram`/`gate_body` — including the hard kinds (Poseidon2→TID_P2
  lookup, Merkle-Lagrange, ChainedHash2to1, TableFunction) — as a **proven Lean
  function** whose output is the emitted descriptor, with a theorem "the emitted
  AIR admits iff the CellProgram semantics hold."
- **Lean emits:** the per-CellProgram descriptor bytes (the way effect
  descriptors already emit).
- **Rust deletes:** `circuit/src/custom_leaf_lowering.rs`'s
  `lower_cellprogram`/`gate_body`/`chip_lookup_site`/`merkle_children_exprs`/
  `table_function_body`/`fill_chain_columns`, plus the duplicate re-implementations
  at `note_spend_witness.rs:180` and `shielded_spend_leaf_adapter.rs:206`. Rust
  loads the emitted descriptor.
- This is the hardest target (the hard kinds have *no* Lean today) and the highest
  cryptographic value (forged-trace-folds).

**T4 — Programs produced FROM Lean values.**
- **Lean authors** each game/app policy as a Lean `CellProgram` value
  (`multiwayTugProgram`, `automataflProgram`, …), proven to refine its
  already-existing Lean `applyAction`/`applyTurn` model.
- **Lean emits** each program (bytes + content address computed in Lean).
- **Rust deletes** the hand-rolled `state.rs::program()` / `game.rs::program()` /
  `emit_program` / per-app `*_program()` and `include_str!`s the emitted program.
- **Payoff:** the airPlay↔program() gap **closes** — the deployed program *is*
  the object `airPlay_iff_applyAction` is about, because it was emitted from it.

---

## 4. THE MIGRATION PLAN — ranked, incremental, each step independently landable

Ordering principle: highest-value-lowest-cost first; keep the deployed system
green throughout; the substrate-unification (§5) is the long pole, so front-load
steps that don't need it.

**Keeping deployed green during migration:** every step is *staged-additive-then-
cutover* (a minted method): emit the Lean artifact, add a drift gate that
regenerates-and-diffs against the current Rust output (proving byte-identity at
the current resolution), and only *then* delete the Rust definition and load the
artifact. No step flips behavior; each either adds a gate or swaps a source for a
proven-identical one. The `check-descriptor-drift.sh` pattern is the template.

**Step 0 (cheap, immediate) — Stop the bleeding: a drift CANARY, not yet a
source-swap.** Add a differential test that runs the Lean `evalConstraint`
(Program.lean) and the Rust `evaluate_constraint_full` on a shared corpus and
asserts agreement. It will **fail** on FieldGte (§2a) — that failure is the
point: it converts a silent Class-B disconnect into a red gate. Cost: days.
Value: exposes exactly where the two sources already disagree, before any deletion.
*Does not need substrate unification if the corpus is restricted to the agreeing
subset first, then widened.*

**Step 1 (cheap early win) — Emit ONE game's program from its already-proven Lean
model.** multiway-tug or automatafl: author the Lean `CellProgram` value,
emit it, drift-gate against `state.rs::program()`, then delete the Rust
`program()` and `include_str!` the artifact. This is T4 for one game, and it is
the smallest thing that makes an airPlay-style theorem reach the deployed object.
Cost: 1–2 weeks per game. Value: first genuinely-Lean-sourced *policy*; template
for the rest. **Prereq honesty:** requires the Lean program value to be over the
same substrate the Rust `Cases` teeth use (counters + `SumEquals`), i.e. a
partial substrate touch — but for one game, scoped.

**Step 2 (medium) — Emit the constraint-vocabulary SCHEMA (T1), Rust generates
its codec from it.** The tag↔postcard-index table is a small artifact; emitting
it and generating the Rust (de)serialization from it makes the wire identity
Lean-sourced without yet touching the evaluator. Drift-gate, then delete the
hand-maintained variant list. Cost: 2–4 weeks. Value: the *wire spec* of the
constraint language becomes Lean-sourced; kills the append-only-by-hand hazard.

**Step 3 (the big one, HARD) — Unify the substrate and export the evaluator
(T2).** This is the load-bearing campaign. Re-author Lean `evalConstraint` over
`[FieldElement;16]`+heap-map (not `Value` records), reconcile
unsigned-256-vs-signed-`Int` and present-zero-vs-absent (a *semantic decision*, not
a mechanical port — ember must rule on each edge), prove the `_iff` theorems over
the new substrate, `@[export]` it, and cut `evaluate_full` over to call it.
Delete the ~2900 lines of `eval.rs`. Cost: **2–4 months.** Value: the deployed
admission decision becomes machine-checked; §2a collapses.

**Step 4 (the crypto pole, HARDEST) — Author the AIR lowering in Lean (T3).** The
hard kinds (Merkle/Poseidon2/table/chained-hash) have *no* Lean today, and this
is where forged-trace-fold soundness lives. Author `lower_cellprogram` as a proven
Lean function, emit per-program descriptors, delete
`custom_leaf_lowering.rs` + the two duplicate re-impls. Cost: **3–6 months**
(this is real circuit-authoring-in-Lean, adjacent to the FRI-soundness work).
Value: closes the deepest cryptographic dead-end.

**Step 5 (mop-up) — Emit the remaining policies (T4 for the rest).** Once T1–T3
land, each game/app is mechanical: multiway-tug fold, automatafl, deos-apps
(convert the re-authored mirrors into emitted values — deleting the mirror), and
give faction/quest/spween/dungeon a Lean model + emit (these have *none* today, so
they need authoring first). Cost: 1–2 weeks each, many of them, parallelizable
across a swarm. Value: every deployed policy Lean-sourced.

**Suggested first cut for approval:** Step 0 + Step 1-on-one-game. Together they
(a) turn the most dangerous silent disconnect (FieldGte) into a red gate and (b)
ship the first policy that is genuinely emitted-from-its-proof — a concrete,
landable proof-of-pattern before committing to the multi-month Steps 3–4.

---

## 5. HONEST SCOPE + SIZE

**This is a very large campaign — plausibly the largest single soundness campaign
in the tree.** It is not a refactor; it is relocating the *source of truth* of the
entire program/constraint semantic layer from Rust to Lean.

**Estimate.** Steps 0–2 (canary + one game + schema emit): ~6–10 weeks, mostly
parallelizable, low risk, each independently landable. Steps 3–4 (evaluator
export + AIR lowering, the two hard poles): **~5–10 months of focused work**,
because they each require *authoring in Lean what only exists in Rust today*, over
a substrate that must first be unified. Step 5 (remaining policies): weeks each,
swarm-parallelizable, but faction/quest/spween/dungeon need a Lean model authored
from scratch.

**What is genuinely HARD (not a mechanical port):**
- **Substrate unification** (`[FieldElement;16]`+map vs `Value` records) is a
  prerequisite for T2/T3 and forces *semantic rulings*: unsigned-vs-signed compare,
  present-zero-vs-absent. These are real behavior decisions ember must make; they
  are the exact edges where the current two sources already silently disagree.
- **The hard AIR lowerings have no Lean at all.** Merkle-Lagrange, Poseidon2→lookup,
  chained-hash copy-forward, table-function interpolation — authoring these as
  *proven* Lean functions is circuit-authoring-in-Lean, adjacent to the
  FRI-soundness frontier, not a port.

**What is a CHEAP early win:**
- Emitting **one game's program** from its already-proven Lean `applyAction`
  model (Step 1) — the Lean model already exists; the missing piece is emit +
  cutover, ~1–2 weeks, and it demonstrates the whole pattern.
- The **differential canary** (Step 0) — days, and it immediately converts the
  most dangerous silent Class-B disconnect into a red gate.

**The priority — load-bearing-AND-unverified-today** (deployed-soundness-depends =
YES, machine-checked-to-deployed = NO), ranked:
1. **`evaluate_constraint_full` + the whole caveat evaluator** (`eval.rs:264`) —
   TOTAL dependency, zero deployed-checking, and *already provably divergent* from
   its Lean "twin" (FieldGte). This is the single highest-value target. → T2/Step 3.
2. **`lower_cellprogram` hard kinds** (`custom_leaf_lowering.rs:204/295/377/482/720`)
   — CRITICAL (forged-trace-fold soundness), no Lean mirror at all. → T3/Step 4.
3. **`StateConstraint`/`CellProgram` enum + wire identity** (`types.rs:970/6`) —
   the vocabulary itself; postcard-index-defined wire spec. → T1/Step 2.
4. **Deployed default-deny in `TransitionGuard`** (`types.rs:213/258`) —
   security-critical gate (stapleable-slot class), Rust-only. → folds into T2.
5. **The ~10 deployed policies**, especially the 6 with **no Lean at any
   resolution** (faction, quest, spween, dungeon) — Rust-only referees. → T4/Step 5.

**The most dangerous thing to fix first is not code — it is the narration.** Three
Lean files carry headers that assert a *discharged connection* to deployment that
does not exist: `MultiwayTugAir.lean` ("THE CONNECTED REFINEMENT"),
`AutomataflAir.lean` ("discharges air.Refines for the emitted circuit"), and
`CustomLeafEncoding.lean` (`cell_to_descriptor_faithful`). Until the emit-and-cut
lands, these read as verification of the deployed object while proving about an
abstraction the deployment never instantiates. If the migration is not approved
immediately, the minimum honest action is to demote these headers from
"connected/discharged" to "parallel model; deployed link is a carried hypothesis"
— so no future reader (or agent) cites them as covering the deployed program.

---

*Prepared for ember's approval. Nothing here is committed; no source was edited.
Every file:line was read or grep-confirmed during this audit; the FieldGte
divergence, the absence of `@[export]`/lean-dep/`ConstraintExpr` in the cell
layer, and the Lean-sourced descriptor drift gate were each independently
ground-truthed.*
