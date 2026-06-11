# The Dregg Predicate Language — one core, three provably-agreeing readings

A predicate in dregg answers one question: *does this turn get to do this to this
cell?* The protocol asks that question in three places — the executor (a Rust
evaluator runs the predicate against the proposed post-state), the metatheory
(a Lean term denotes the predicate and carries its conservation/authority/
confluence proofs), and the circuit (an AIR enforces the predicate inside the
turn proof). Today those three places speak **four different Rust ontologies
and a Lean stack that mirrors only one of them well**. This document specifies
the single language that replaces the sprawl: the cell-program constraint core
is THE language; everything else is either a surface syntax that parses onto
it, a named crypto gadget it calls through the witnessed seam, or dead.

Companion documents: `docs/CELL-PROGRAM-LANGUAGE.md` (the constraint-core
grammar itself — the turn-context atoms, the staged layout rotation) and
`docs/DREGGRS-SEGREGATION.md` (the workspace-wide load/heritage verdicts this
census sharpens).

## Contents

1. [The census — what exists](#1-the-census)
   * 1.1 The four Rust predicate ontologies
   * 1.2 The Lean semantics stack
   * 1.3 The consumer table (every live use, file:line)
2. [The two-ontology map](#2-the-two-ontology-map)
3. [The core decision](#3-the-core-decision)
4. [The core language — specification sketch](#4-the-core-language)
5. [The three readings and the agreement obligations](#5-the-three-readings)
6. [Consumer migrations](#6-consumer-migrations)
7. [What dies](#7-what-dies)
8. [The kimchi `from_dsl` question](#8-the-kimchi-question)
9. [Staging](#9-staging)

---

## 1. The census

### 1.1 The four Rust predicate ontologies

**O1 — the proc-macro DSL** (`dregg-dsl`, 4.2k lines). `#[dregg_caveat]` /
`#[dregg_effect]` / `#[dregg_circuit]` parse a restricted Rust function body
(`require!(a <= b)`, `merkle_member!`, `poseidon2_assert!`, `in_range!`,
mutations, `match` arms — `dregg-dsl/src/ir.rs::RequirementKind`) into a
`ConstraintIr` and fan it out through **eight** code generators: a Rust
evaluator, an `AirConstraintSet` topology descriptor, a Datalog rule string, a
`KimchiCircuitDescriptor`, a compile-time STARK `impl`, a Midnight ZKIR v3
program, a native Plonky3 `Air`, and an SP1 guest source. The macro surface is
invoked **only** by the test tier (`dregg-dsl-tests/src/*`, twenty-plus
exhibit modules; `dregg-dsl-differential/src/predicates.rs`). No production
crate expands a `#[dregg_caveat]`.

**O2 — the descriptor runtime** (`circuit/src/dsl/circuit.rs`, re-exported as
`dregg-dsl-runtime`). `CircuitDescriptor` is a *data-level* AIR: columns,
`ConstraintExpr` (Equality / Multiplication / Binary / Polynomial / Gated /
Hash2to1 / Hash4to1 / MerkleHash / Lookup / …), boundaries, lookup tables.
`DslCircuit` interprets a descriptor as a runnable `StarkAir`; `CellProgram` =
a deployed descriptor + VK hash; `ProgramRegistry` = the VK→program map the
executor dispatches through. This is the **live smart-contract runtime**: a
user deploys a serialized descriptor (`node/src/api.rs:5474`), the registry
validates and stores it, and the turn proof verifier runs
`program.verify_transition(...)` for any cell whose `verification_key_hash`
names it (`turn/src/executor/proof_verify.rs:385,476`). Alongside it,
`circuit/src/dsl/descriptors.rs` is a **fixed registry of named gadget AIRs**
(`dregg-merkle-poseidon2-v1`, `dregg-blinded-merkle-v1`,
`dregg-non-revocation-v1`, `dregg-derivation-v1`, the three predicate-DSL
AIRs) dispatched by `circuit_for_air_name`.

**O3 — the cell-program constraint grammar** (`cell/src/program.rs`:
`CellProgram::{None, Predicate, Cases, Circuit}` over `StateConstraint` /
`SimpleStateConstraint`). This is the language `docs/CELL-PROGRAM-LANGUAGE.md`
specifies and the uplift lane is extending (turn-context atoms `SenderIs` /
`SenderInSlot` / `BalanceGte` / `BalanceLte`, composable `PreimageGate`). The
executor evaluates it on every touched cell; the slot-caveat projection puts
the context-free fragment in the proof's public-input manifest. Its
`Circuit { circuit_hash }` variant is the **escape hatch into O2**: the
constraint says "a proof verified by the deployed program with this VK must
accompany the turn" (`ProgramError::CircuitProofRequired`,
`cell/src/program.rs:1252`).

**O4 — the predicate gadget families** (`circuit/src/dsl/predicates/{base,
relational,arithmetic,compound}.rs` plus `note_spending`, `revocation`,
`accumulator`, `derivation`, `garbled`, `temporal_absence`, `membership`,
`fold`). Hand-built prove/verify pairs for caveat-shaped facts — comparisons
against committed values, relational and arithmetic predicates with blinding,
set membership/non-membership, credential derivation. These are the *crypto
gadgets* behind the witnessed seam, not a language: each has a fixed AIR, a
trace generator, and a Rust verifier.

### 1.2 The Lean semantics stack

* **`Dregg2/Exec/Program.lean` (912 lines) — the constraint-core semantics.**
  `SimpleConstraint` / `StateConstraint` are the *name-keyed* mirror of O3
  (fieldEquals/Ge/Le, immutable, writeOnce, monotonic, strictMono, fieldDelta,
  memberOf, prefixOf, inRangeTwoSided, deltaBounded, Heyting `not`, the new
  ctx atoms senderIs/senderInField/balanceGe/balanceLe/preimageGate;
  state-level fieldLeField, sumEquals, sumEqualsAcross, fieldDeltaInRange,
  allowedTransitions, anyOf, boundDelta (fail-closed), clearanceGe, affineLe,
  affineEq, reachable). `evalSimple`/`evalConstraint` are the ctx-less
  evaluators; `evalSimpleCtx`/`evalConstraintCtx`/`RecordProgram.admitsCtx`
  the context-aware ones, with conservative-extension keystones
  (`evalConstraintCtx_empty`) and per-atom admit-characterizations.
* **`Dregg2/DSL.lean` — the `dregg_program { … }` surface.** A
  `declare_syntax_cat` eDSL elaborating *directly to* `RecordProgram` smart
  constructors — the existence proof that surface syntax over the core needs
  **no new metatheory**.
* **The §8 guard ladder** — the closure algebra the core is growing toward:
  `Authority/RelationalClosure.lean` (`RelPred`: affine half-spaces
  `Σ cᵢ·record[fᵢ] ≤ k` closed under ∧/∨/¬, SUBSUMING FieldLteOther /
  FieldLteField / AffineLe / SumEquals as one-line instances);
  `ArithmeticClosure.lean` (`ArithPred`: bounded-degree polynomial atoms —
  the PLONK-native quadratic fragment — with `ofRelPred_eval_eq` proving the
  affine embedding exact); `QuantifiedPredicate.lean` (bounded ∀/∃
  de-quantify into `RelPred` folds — `forall_eq_andFold` — and committed-set
  membership is the one quantifier that does NOT de-quantify: it routes to
  the witnessed seam); `ConfluenceClassifier.lean` (every guard gets a
  decidable coordination-cost verdict: monotone floor = free, bounded ceiling
  = forces ordering, relational = decided-by-merge).
* **The witnessed seam** — `Authority/Predicate.lean`: `WitnessedKind`
  (dfa | temporal | merkleMembership | nonMembership | pedersen | blindedSet
  | bridge | custom(vk)) mirroring `cell/src/predicate.rs::
  WitnessedPredicateKind`; registry dispatch + soundness-by-verification; the
  crypto soundness of each kind is a §8 `CryptoKernel` portal, never a Lean
  law. This is the Lean name for O4 + the `Witnessed`/`Custom` constraint
  variants.
* **The caveat algebra** — `Authority/Caveat.lean` (+ `CaveatChain`,
  `MacaroonDischarge`, `ThirdPartyDischarge`, `Discharge`): token = RootSeal
  + append-only caveat chain; `attenuate_narrows`; third-party caveat =
  discharge/`ConditionalTurn` isomorphism. The kernel-side per-slot twin is
  `Exec/RecordKernel.lean::SlotCaveat` (immutable | monotonicSeq | monotonic
  | writeOnce | senderAuthorized | boundedBy | admitTable) enforced by
  `Exec/EffectsState.lean::stateStepGuarded` with the fail-closed keystones.
* **The circuit reading** — `Dregg2/Circuit.lean` (verified IR: `Expr` =
  var/const/add/mul, `ConstraintSystem`, the `bridge` theorem `satisfied
  kernelCircuit (encode s t s') ↔ fullStepInv s t s'`) and
  `Exec/CircuitEmit.lean` (`emit_faithful`: the wire-form descriptor denotes
  the same constraint system), decoded on the Rust side by
  `dregg-lean-ffi/src/circuit_decode.rs` into a real O2 `CircuitDescriptor`
  with an AIR-fingerprint binding.

### 1.3 The consumer table

Every production consumer of `dregg-dsl` / `dregg-dsl-runtime`, verified by
grep (test/demo tier listed separately):

| Consumer | What it uses | Role |
|---|---|---|
| `turn/src/executor/mod.rs:66,409,1249` | `ProgramRegistry` | executor holds the deployed-program map |
| `turn/src/executor/proof_verify.rs:385,476` | `ProgramRegistry::get` → `verify_transition` | **load-bearing**: VK-dispatched verification of custom cell programs inside turn proof verification |
| `turn/src/executor/atomic.rs:568,850` | same | atomic-batch arm of the same dispatch |
| `turn/src/conditional.rs:342,398` | `descriptors::circuit_for_air_name` | **caveat role, live**: `ConditionalTurn`/`ProofCondition` discharge verifies a named-AIR STARK (federation/local proofs) |
| `node/src/state.rs:22,235` | `ProgramRegistry` | node state carries the registry |
| `node/src/api.rs:5474-78` | `CircuitDescriptor`, `CellProgram::new` | the deploy endpoint: serialized descriptor → validated program |
| `sdk/src/verify.rs:157,268` | `circuit_for_air_name` | SDK-side proof verification |
| `sdk/src/privacy.rs:26-27,704,791` | `note_spending`, `revocation`, blinded-merkle descriptor | privacy proving APIs (gadget tier) |
| `sdk/src/full_turn_proof.rs:75-76` | `composition::{compose_aggregate,…}` | sub-proof aggregation |
| `sdk/src/error.rs:4`, `sdk/src/cipherclerk.rs:6130,6208` | `ProgramError`, `CircuitDescriptor`, `CellProgram` | error/type plumbing for the deploy path |
| `bridge/src/verifier.rs:40,193,408,437,488` | `ProgramRegistry`, `DslCircuit`, descriptors | bridge-presentation proof verification |
| `bridge/src/present.rs:29,294,2107-3534` | `fold::build_shared_tree`, descriptors | presentation/fold proofs |
| `wire/src/server.rs:102`, `wire/src/bin/cross_node_auth.rs:78` | `merkle_poseidon2_circuit` | cross-node auth membership proof |
| `cell/Cargo.toml:20,50` | optional, `zkvm` feature only | feature-gated; no unconditional use |
| `commit/Cargo.toml:10` | dep declared | no `dregg_dsl_runtime` use sites in `commit/src` (dead dep, flagged) |
| `circuit/Cargo.toml:39` | `dregg-dsl` proc-macro dep | **zero use sites** in circuit/src,tests,benches — the comment itself says the one intended consumer (`temporal_predicate_dsl.rs`) is *manually expanded* (dead dep, flagged) |
| `sdk/Cargo.toml:34` | `dregg-dsl-tests` dep | **zero use sites** in sdk (dead dep, flagged) |

Test/demo tier (stays per the segregation manifest): `dregg-dsl-tests` (the
only `#[dregg_caveat]`/`#[dregg_effect]` invoker), `dregg-dsl-differential`
(the cross-backend agreement harness), `tests/src/{dsl_pipeline,
full_pipeline,fully_private_e2e}.rs`, `teasting/tests/proof_round_trip.rs`,
`demo-agent/examples/bench_summary.rs`, `circuit/benches/*`. The `apps/`
consumers (`compute-exchange`, `gallery`) are R-herit, marked delete in the
segregation manifest — they do not bind this design.

**Negative result (the missing leg):** no Lean `@[export]` evaluates a
serialized cell program. The export surface covers kernel steps, transfers,
blocklace, CapTP, coordination — `dregg_record_kernel_step` exercises
`stateStepGuarded`, but nothing takes O3 program bytes and answers
`admitsCtx`. The Rust-evaluator⟺Lean-semantics differential for the
constraint core **does not exist yet** (§5 makes it obligation A1).

## 2. The two-ontology map

For each predicate concept: where it lives on each side, and which reading it
has today (E = Rust evaluator, C = circuit compilation, L = Lean semantics).

| Concept | Rust | Lean | Readings today |
|---|---|---|---|
| Field comparison vs literal | O3 `FieldEquals/FieldGte/FieldLte` (`cell/src/program.rs:646-650`); O1 `require!(a <= b)` | `SimpleConstraint.fieldEquals/Ge/Le` | E+L; C via slot-caveat PI manifest (context-free fragment) |
| Field vs field / relational | O3 `FieldLteField`, `FieldLteOther` | `StateConstraint.fieldLeField`; subsumed by `RelPred.lift1` | E+L; C partial |
| Affine forms | O3 `AffineLe/AffineEq { terms, c }` (`:910,914`) | `StateConstraint.affineLe/affineEq`; THE `RelPred` atom | E+L; C partial |
| Conservation sums | O3 `SumEquals`, `SumEqualsAcross` | `sumEquals`, `sumEqualsAcross`; `RelPred.affineEq` instance | E+L; C (effect-VM conservation columns for the kernel's own sums) |
| Polynomial (quadratic+) relations | **absent** in O3; O2 `ConstraintExpr::{Multiplication, Polynomial}` express it at AIR level only | `ArithPred` (bounded-degree monomials) — **proved, unshipped** | L only as a *language*; C only as raw AIR |
| Boolean structure | O3 `AnyOf` (simple-only), `AllOf`, `Not` via simple, `Cases` guards | Heyting `not`, `anyOf`, `TransitionCase`; full ∧/∨/¬ closure in `RelPred`/`ArithPred` | E+L; C partial (`AtLeastOne`, `Gated` exist in O2) |
| Witnessed-branch disjunction | **absent** (CELL-PROGRAM-LANGUAGE §6.4 `AnyOfBound`, staged) | absent (deferred in DSL.lean) | — |
| Temporal gates | O3 `TemporalGate`, `FieldGteHeight/LteHeight`, `RateLimit*` | `SlotCaveat.boundedBy` family; `Authority/CausalGuard` axis; temporal kinds via witnessed seam | E+L; C deferred (context-dependent) |
| Monotone / write-discipline | O3 `Monotonic/StrictMonotonic/WriteOnce/Immutable/MonotonicSequence` | `SimpleConstraint` twins + `SlotCaveat` kernel twins + I-confluence verdicts | E+L+C (slot-caveat manifest) — the best-aligned row |
| State machines | O3 `AllowedTransitions` | `allowedTransitions`, `SlotCaveat.admitTable` | E+L; C partial |
| Membership (cleartext set) | O3 `MemberOf { set: Vec<u64> }` | `memberOf` | E+L |
| Membership (committed set) | O3 `SenderAuthorized { AuthorizedSet::{PublicRoot, BlindedSet, CredentialSet} }`, O4 merkle/blinded gadgets, O2 named AIRs | `WitnessedKind.merkleMembership/blindedSet`; `QuantifiedPredicate` membership escape | E+C (gadget AIRs); L models dispatch, crypto = §8 portal |
| Non-revocation | O4 `revocation` gadget + O2 `dregg-non-revocation-v1` | `WitnessedKind.nonMembership` | E+C; L dispatch-only |
| Preimage/commitment gates | O3 `PreimageGate` (now composable) | `SimpleConstraint.preimageGate` + iff keystone | E+L; C = hash gadget (Poseidon2 in-AIR, BLAKE3 executor-side) |
| Sender/actor binding | O3 `SenderIs/SenderInSlot` (uplift) | `senderIs/senderInField` + actor-binding keystone triple; `SlotCaveat.senderAuthorized` singleton | E+L; C deferred to rotation PI layout |
| Balance atoms | O3 `BalanceGte/BalanceLte` (uplift) | `balanceGe/balanceLe` | E+L; C deferred |
| Quantifiers (bounded ∀/∃) | **absent** — apps unroll by hand over 8 slots | `QuantifiedPredicate` with de-quantification keystones — **proved, unshipped** | L only |
| Caveats (token layer) | `macaroon`/`token` crates; discharge via `ConditionalTurn` STARKs (O2 named AIRs) | `Authority/Caveat` + chain + discharge isomorphism | E+C (discharge proofs); L algebra |
| Caveats (kernel per-slot) | factory-descriptor programs → executor slot checks | `SlotCaveat` + `stateStepGuarded` fail-closed keystones | E+L; C via slot-caveat manifest |
| Coordination cost | **absent** (no Rust classifier) | `ConfluenceClassifier` — decidable verdict per guard | L only; doc-level in CELL-PROGRAM-LANGUAGE §5 |
| Effects/mutations | O1 `#[dregg_effect]` mutations; **superseded** by effect-VM | effect semantics live in `Exec/EffectsState`, not the predicate language | dead as DSL |
| Arbitrary AIR | O2 `CircuitDescriptor` (deploy path); O1 `#[dregg_circuit]` | `Circuit.lean` IR + `CircuitEmit` faithful wire | E (interpreted) + C; L for the *kernel* circuit only |

**Same idea, different names** (the alignment debts): `AffineLe` ≡ `RelPred`
atom ≡ (degree-1) `ArithPred` ≡ O2 `Polynomial` row; `SenderAuthorized
{singleton}` ≡ `senderIs` ≡ `SlotCaveat.senderAuthorized [a]`; O1
`merkle_member!` ≡ O4 `membership` gadget ≡ `WitnessedKind.merkleMembership`;
O3 slot **index `u8`** vs Lean **`FieldName` string** (the rotation closes
this); O1's eight backends vs the protocol's actual two (evaluator, Plonky3
circuit) plus interop emitters.

**What each side can express that the other cannot, today:** Lean has the
polynomial closure, bounded quantifiers, and the confluence classifier with
proofs; Rust O3 cannot name any of them. Rust O2 can express arbitrary AIRs
(lookup tables, Merkle gadgets, hash chains) that the Lean *predicate*
surfaces don't model (only the kernel circuit is Lean-verified); O1 can emit
Datalog/Midnight/SP1, which nothing else can — and nothing in production
consumes.

## 3. The core decision

**The (post-uplift) cell-program constraint core — `cell/src/program.rs`'s
`StateConstraint` grammar, name-keyed after the layout rotation — is THE
predicate language.** Everything else aligns to it:

1. **`Dregg2/Exec/Program.lean` is its semantics.** The Lean inductive is
   already the constraint-for-constraint mirror with the ctx evaluator and
   the conservative-extension discipline; the lockstep contract of
   CELL-PROGRAM-LANGUAGE §9 (every grammar change lands with its Lean twin
   and keystones in the same change) is the *definition* of the language,
   not a mirror of it. Where the two disagree, the Lean reading wins and the
   Rust evaluator is the bug.
2. **The DSL becomes surface syntax, not a parallel ontology.** O1's macro
   front-end retargets: `#[dregg_caveat]` bodies parse to *core terms*
   (`StateConstraint` values), exactly as `dregg_program { … }` already
   elaborates to `RecordProgram` on the Lean side. The `ConstraintIr` and its
   eight per-backend generators dissolve: a surface parser may keep emitting
   the interop formats (Datalog/Midnight/SP1) as *additional outputs from the
   core term*, but the core term is the single meaning-carrier. One grammar,
   two elaborators (Rust `syn` → `StateConstraint`; Lean `macro_rules` →
   `RecordProgram`), one semantics.
3. **The circuit reading is compilation from the core, on the two lanes that
   already exist.** (a) The *kernel-enforced fragment* rides the slot-caveat
   PI manifest and the effect-VM one-circuit — context-free atoms today,
   sender/balance columns at the rotation. (b) The *app-defined remainder*
   compiles core terms to an O2 `CircuitDescriptor` (the `ArithPred` atom is
   precisely a `Polynomial` constraint row; `anyOf` is `AtLeastOne` over
   indicator columns; membership atoms *link* the named gadget AIRs), which
   the existing `ProgramRegistry` deploy/verify path runs unchanged. The Lean
   `Circuit.lean` `bridge` + `CircuitEmit.emit_faithful` + the
   `circuit_decode.rs` fingerprint binding are the proof pattern this
   compilation is held to.
4. **The grammar's growth target is the §8 closure algebra, not more atoms.**
   At the rotation, the per-shape menu (FieldLteOther, SumEquals, …) becomes
   the proved-subsumed instances of `RelPred`/`ArithPred` (+ the bounded
   quantifiers, which de-quantify; + the membership escape to the witnessed
   seam). The Rust core gains the closure constructors; the legacy atoms
   remain as parse sugar. Every constraint carries its
   `ConfluenceClassifier` verdict as a queryable cost annotation.
5. **The witnessed seam stays a seam.** Committed-set membership,
   non-revocation, derivation, blinded predicates — the O4 gadget families
   and the O2 named-AIR registry — are *vocabulary the language calls by
   name* (`WitnessedKind`), never inlined into the core grammar. Their
   soundness is the §8 crypto floor on both sides.

The shape rejected: making O2's `CircuitDescriptor` the core. It is the right
*compilation target* and the right *deploy artifact*, but it is column-level
(meaningless to the executor's state semantics and the confluence
classifier), and the proven Lean semantics exists at the state-constraint
level, not the AIR level.

## 4. The core language

The specification, present-state and rotation-state:

* **Carrier**: a predicate over `(old, new : CellState, ctx : TurnCtx,
  witnesses)`. Pre-rotation `CellState` is the 8-slot array (`index : u8`);
  post-rotation it is the name-keyed record (`FieldName`), matching
  `Exec/Value.lean` — the Lean side is already name-keyed and is the spec.
* **Atoms** (the simple fragment, composable under `not`/`anyOf`/`implies`):
  field comparisons vs literals; write-discipline (immutable, writeOnce,
  monotonic, strictMono, fieldDelta, deltaBounded, inRangeTwoSided);
  cleartext membership; turn-context atoms (senderIs, senderInField,
  balanceGe, balanceLe); the preimage gate. Fail-closed everywhere: an
  unevaluable atom rejects, `not` propagates unevaluability (the Heyting
  contract of `evaluate_simple_constraint` ≙ `evalSimpleCtx`).
* **State-level forms**: fieldLeField, sumEquals/sumEqualsAcross,
  fieldDeltaInRange, allowedTransitions, affineLe/affineEq, anyOf,
  clearance/reachability, cases (guarded transition arms), invariant blocks.
* **Closure constructors** (rotation): the affine atom generalizes to the
  bounded-degree polynomial atom (`ArithPred`); bounded ∀/∃ over named
  regions compile away by `forall_eq_andFold`/`exists_eq_orFold`; equality =
  two half-spaces (no bespoke conservation primitives in the grammar).
* **Seam calls**: `witnessed(kind, …)` with explicit per-branch witness
  binding when placed under disjunction (the `AnyOfBound` design,
  CELL-PROGRAM-LANGUAGE §6.4); `circuit(vk)` deferring to a deployed O2
  program.
* **Cost annotation**: every term has a computable coordination verdict
  (free / ordering / decided-by-merge) — the `ConfluenceClassifier` verdict
  surfaced through `dregg explain` and the SDK builders.
* **Encoding**: postcard, variant-index appended-only (the live
  compatibility discipline); the serialized core term is what deploys,
  hashes into content addresses, and crosses the FFI to Lean.

## 5. The three readings

| Reading | Artifact | Agreement obligation |
|---|---|---|
| Rust evaluator | `evaluate_constraint_full` (executor) | **A1 — evaluator ⟺ semantics differential**: a Lean `@[export] dregg_program_admits` taking (serialized core term, old, new, ctx) and answering `admitsCtx`; the harness drives both evaluators over generated programs/states (the `dregg-lean-ffi` golden-oracle cascade pattern, `state_differential.rs` precedent). Does not exist today; first new artifact of this design. |
| Lean semantics | `RecordProgram.admitsCtx` + the keystone library | **A2 — lockstep-by-construction**: grammar changes land with Lean twins, `#assert_axioms`-clean, non-vacuity `#guard` pairs (already the §9 contract; this doc makes it the language definition). |
| Circuit | slot-caveat manifest + effect-VM (kernel fragment); compiled `CircuitDescriptor` via `ProgramRegistry` (app fragment) | **A3 — compile ⟺ evaluator**: per-construct, the descriptor-cutover-harness discipline (the effect-VM graduation gauntlet) applied to the core→descriptor compiler: prove-accept/prove-reject/tamper-UNSAT against the Rust evaluator verdicts. **A4 — the theorem where feasible**: the Lean-side pattern already exists end-to-end for the kernel circuit (`bridge` + `emit_faithful` + fingerprint binding in `circuit_decode.rs`); the compiled-program lane reuses it by emitting the descriptor *from the Lean term* for the proved fragment, so circuit ⟺ semantics is a theorem and Rust agreement reduces to A1+A3. |

The upgrade over today's `dregg-dsl-differential`: that harness proves the
*eight O1 backends* agree with each other on toy caveats — agreement among
copies of the wrong ontology. The replacement triangle is evaluator ⟺
semantics ⟺ circuit over *deployed program bytes*, with the Lean term as the
apex. The differential crate's harness/agreement-matrix machinery
(`AgreementMatrix`, curated boundary inputs) is reusable; its subject changes.

## 6. Consumer migrations

* **`ProgramRegistry` dispatch** (`turn/proof_verify.rs`, `atomic.rs`,
  `node/api.rs` deploy, `sdk/cipherclerk.rs`): unchanged interface. The
  registry keeps accepting raw `CircuitDescriptor`s (expert path) and
  additionally accepts core terms, compiling them server-side (A3-gated).
  `CellProgram::Circuit { circuit_hash }` keeps meaning "deployed program
  required".
* **Conditional-turn / discharge proofs** (`turn/conditional.rs`,
  `bridge/{present,verifier}.rs`, `sdk/verify.rs`, `wire`): unchanged — these
  verify *named gadget AIRs* (`circuit_for_air_name`), which §3.5 keeps as
  the witnessed seam's vocabulary. One cleanup lands with the migration: the
  `unwrap_or_else(merkle_poseidon2_circuit)` fallbacks on unknown AIR names
  become hard rejections (an unknown AIR silently verified against the
  membership circuit is fail-open shape).
* **Privacy proving APIs** (`sdk/privacy.rs`, gadget families): unchanged;
  they are gadgets, not language. Their crate-home can move out of
  `dregg-dsl-runtime`'s re-export shim (the shim exists only to break a
  legacy dependency cycle; `dregg_circuit::dsl` is the real home).
* **`composition`** (`sdk/full_turn_proof.rs`): unchanged; proof aggregation
  is orthogonal to the predicate language.
* **`dregg-dsl-tests` / `dregg-dsl-differential`**: retarget per §5. The
  macro crate shrinks to one parser (`syn` body → core term) plus optional
  interop emitters; the exhibit modules become golden tests of the parser;
  the differential harness becomes the A1/A3 runner.
* **Lean `DSL.lean`**: gains the uplift atoms (`sender is`, `balance >=`,
  `reveals` — CELL-PROGRAM-LANGUAGE §10.6) and stays the Lean-side
  elaborator of the *same* surface grammar.

## 7. What dies

Census-verified dead, with evidence:

* **The per-effect circuit role of `#[dregg_effect]`** — superseded. The turn
  proof path verifies `EffectVmAir` (one circuit,
  `turn/proof_verify.rs:403`) with Lean-emitted descriptors graduating
  through the cutover harness; zero production expansions of the macro
  exist. The effect/mutation fragment of O1's IR (`Statement::Mutate`,
  `MatchArm`, `EffectDescriptor`) has no successor in the core — effects are
  the effect-VM's job, not the predicate language's.
* **`circuit → dregg-dsl` dependency** (`circuit/Cargo.toml:39`): zero
  `dregg_dsl::` use sites in circuit/{src,tests,benches}; the dep comment
  itself records that the intended consumer was manually expanded
  (`circuit/src/temporal_predicate_dsl.rs`). Removal belongs to the circuit
  lane (file owned there).
* **`sdk → dregg-dsl-tests` dependency** (`sdk/Cargo.toml:34`): zero use
  sites in sdk. Removal belongs to the sdk lane.
* **`commit → dregg-dsl-runtime` dependency** (`commit/Cargo.toml:10`): zero
  use sites in commit/src.
* **`dregg-dsl-runtime/kimchi_bridge`** (`lib.rs:242`): gated on the
  `kimchi-bridge` feature, which **no crate in the workspace enables**; §8.
* **Five of O1's eight backends as meaning-carriers**: `gen_air` (the
  `AirConstraintSet` topology descriptor — descriptive metadata nothing
  verifies against), `gen_datalog`, `gen_kimchi`, `gen_midnight`, `gen_sp1`
  survive, if at all, as interop *emitters from the core term* under the
  interop lane's ownership; none participates in the agreement triangle.

Not dead (named explicitly because the segregation manifest hedged):
`ProgramRegistry`/`CircuitDescriptor`/`DslCircuit` (the deploy path is
load-bearing in turn proof verification), the named gadget AIR registry (the
caveat/discharge role is live in `turn/conditional.rs`), and the gadget
proving families.

## 8. The kimchi question

`circuit/src/backends/kimchi_native/from_dsl.rs` converts O1's
`KimchiCircuitDescriptor` into real Kimchi gates and proves via Pickles. Its
only reachable consumers are circuit-internal tests
(`dsl_backend.rs:1697-1762`); the `dregg-dsl-runtime::kimchi_bridge` re-export
is feature-dead (no enabler). The kimchi backend itself is load-bearing
*elsewhere* (`stark_in_pickles`, the Mina interop heritage) — so the verdict
splits: the **DSL-facing bridge** (`kimchi_bridge`, `gen_kimchi`, and
`from_dsl`'s descriptor-conversion entry) transfers to the interop lane as a
"compile the core term to a Kimchi circuit" emitter if Mina interop demands
it, and is otherwise deletable with the rest of O1's backend fan-out. Nothing
in the agreement triangle depends on it.

## 9. Staging

* **S0 — now, independent of the uplift lane**: (a) the A1 export —
  `dregg_program_admits` in `Dregg2/Exec/FFI.lean` + a program-differential
  module in `dregg-lean-ffi` (serialized O3 term ⟶ Lean `admitsCtx` vs Rust
  `evaluate_constraint_full`), seeded with the existing exhibit programs;
  (b) dead-dep removals (each in its owning lane: circuit, sdk, commit);
  (c) the unknown-AIR fail-open fallback fix.
* **S1 — at the uplift's landing**: freeze the post-uplift O3 grammar as the
  core v1; retarget `#[dregg_caveat]` to parse to core terms; convert
  `dregg-dsl-differential` to the A1 runner over the curated boundary-input
  battery; mothball the per-backend generators (interop lane takes custody
  of any it wants).
* **S2 — the layout rotation** (rides the same VK/commitment v-bump as
  CELL-PROGRAM-LANGUAGE §6): name-keyed records — the Rust core's `index: u8`
  becomes `FieldName`, structurally identical to `RecordProgram`; the closure
  constructors land (`ArithPred` polynomial atom, bounded quantifiers,
  `AnyOfBound` witnessed branches) with the §8 modules as their pre-proved
  semantics; the confluence verdict surfaces in tooling.
* **S3 — the circuit reading of the core**: the core→`CircuitDescriptor`
  compiler (Rust), descriptor-cutover-gauntlet per construct (A3); the
  Lean-emission path (`CircuitEmit` pattern) for the proved fragment (A4);
  sender/balance PI columns per the rotation layout, retiring the last
  executor-only context atoms.
* **S4 — surface polish**: `dregg_program`-equivalent sugar in the Rust SDK
  builders; `dregg explain` renders core terms with cost verdicts; the
  deploy path accepts core terms end-to-end.

---

## AMENDMENT (ember, 2026-06-11 — supersedes any contrary reading above)

**Zero Rust-authored constraints or AIRs, ever. All circuits and all constraint
semantics are EMITTED FROM LEAN and represented formally.** Where this document
frames a "differential" between a Rust evaluator and the Lean semantics, read
that as a TRANSITIONAL check only — never the architecture. The end state:

- The Lean kernel is already the program evaluator: `stateStepGuarded` runs
  inside `execFullForestG`, which IS the node's state producer. The Rust
  `evaluate_constraint_full` is legacy-executor machinery that dies with the
  remainder of THE SWAP — it is not a peer semantics to be reconciled.
- The constraint language is DEFINED in Lean and EMITTED (the descriptor
  pattern: Lean emits, Rust interprets, a byte-pinned registry gates drift).
  `cell/src/program.rs`'s grammar is a deserialization target for the emitted
  form, not an independent definition.
- Circuit readings of program predicates are Lean-emitted descriptors like
  every other circuit. No hand-written AIR is ever the answer to a coverage
  gap; the answer is emitting the descriptor from the proved Lean module.
