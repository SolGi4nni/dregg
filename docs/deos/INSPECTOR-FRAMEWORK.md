# The Moldable Inspector & Gadget Framework for the dregg Desktop (starbridge-v2)

> **STATUS — SHIPPED (framework + the whole L1–L10 ladder landed).** This began as a
> forward design + build plan; it is now the delivered record. The framework spine lives
> in `starbridge-v2/src/presentable.rs`: `trait Presentable`, `trait Gadget`,
> `trait CommittingGadget`, `enum PresentationKind` (all seven kinds), `Registry`, and
> `Spotter` — the L1 spine landed in commit `800945db6` ("L1 — the Presentation Spine").
> Note the `Gadget`/`CommittingGadget` traits landed *inside* `presentable.rs`, not a
> separate `gadget.rs` (the `gadget.rs` filename in §1.2's code block never became a real
> file). Every planned lane shipped as its own module: **L2** `predicate_composer.rs`,
> **L3** `turn_builder.rs`, **L4** `cap_inspector.rs`, **L6** `receipts_inspector.rs`,
> **L7** `token_inspector.rs`, **L8** `federation_inspector.rs`, **L9** `circuit_inspector.rs`,
> **L10** `settlement_inspector.rs`; 27 `impl Presentable` blocks now span every lane. Read
> Part 3 as the delivered index (each lane names its real module), and the **~74-None
> coverage matrix in Part 2 as the authoring-time census** — the formerly-all-None blocks
> (slice 3 predicates, slice 9 federation, slices 7 & 11 circuit/commitment) now have real
> inspectors. Part 1 remains the accurate design rationale.

## Executive summary

starbridge-v2 today has ONE reflective shape — `reflect.rs`'s `Inspectable`: a flat, uniform field-tree projected from a live protocol object, with seven `ObjectKind`s and four cross-cutting axes (ocap edges, verification, provenance, image commitment). The census shows ~120 protocol types and ~95% of them have NO inspector at all. The framework generalizes the single field-tree into Pharo's moldable multiplicity: a `Presentable` trait where each protocol object offers MULTIPLE named **presentations** (the existing `Inspectable` becomes the mandatory `raw-fields` presentation; `graph`/`domain-visual`/`affordances`/`provenance`/`invariant`/`source` join it), and a `Gadget` trait for interactive value CONSTRUCTION that reuses the established `IntentDraft → simulate() → commit()` predict-then-commit spine so every gadget emits a REAL protocol value flowing through the verified executor. Both layers stay gpui-free and `cargo test`-able exactly as `reflect.rs`/`wonder.rs`/`inspect_act.rs` already are — the model is pure data; a thin gpui layer renders presentation kinds and gadget field-kinds generically. A `Spotter` universal search indexes every `Presentable` by its presentations' searchable text, and the existing `Halo` ring (wonder.rs) becomes the per-object direct-manipulation layer whose commands open presentations and arm gadgets. Complete coverage is a 12-slice × {presentations, gadgets, coverage} ledger covering every census type, with NO type left without at least the `raw-fields` floor.

The shape of complete coverage: the protocol's whole surface decomposes into seven presentation kinds and ~10 gadget families; every census type maps onto a subset, and the matrix below visibly accounts for all of them, flagging the ~80 currently-`none` types. The three highest-value first lanes are **(L1) the Presentation Spine** (the `Presentable` trait + registry + the seven kinds + Spotter — the framework primitive everything else needs first, and the only lane with no additive parallelism), **(L2) the Predicate/Caveat Composer** (the richest, most-requested, entirely-`none` surface — the `StateConstraint`/`Pred`/`WitnessedPredicate` builder + cost/coordination + anti-strip safety, the "lamesauce language uplift" from the Refinement Epoch), and **(L3) the Effect/CallForest/Turn Builder** (the universal construction gadget — it produces the values every other gadget composes into, and `simulate.rs`'s `IntentDraft` is already 80% of it).

---

## Part 1 — THE FRAMEWORK

### 1.1 `Presentable` — moldable multiplicity over the existing field-tree

The current `reflect_cell` / `reflect_receipt` / … functions each produce exactly one `Inspectable`. Pharo's `gtViewsFor:` instead lets a type offer a *set* of named views, each a different lens on the same live object. We generalize without discarding `reflect.rs`: the existing `Inspectable` becomes the body of the **`RawFields` presentation kind**, and a type registers additional kinds beside it.

```rust
// presentable.rs — the moldable core (gpui-free, pure projection of the live World).

/// The named kinds of presentation a protocol object can offer. Mirrors Pharo-GT's
/// view multiplicity, molded to the dregg domain's four axes.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PresentationKind {
    RawFields,    // the existing Inspectable field-tree — the MANDATORY floor.
    Graph,        // a node/edge view (ocap web, effect DAG, Merkle tree, lattice).
    DomainVisual, // a domain-specific rendering (state machine, gauge, ladder, timeline).
    Affordances,  // "the messages it understands" — the InspectAct Message list.
    Provenance,   // time-travel / receipt-chain / lineage (the History scrubber face).
    Invariant,    // conservation / commitment-binding / cost-coordination readouts.
    Source,       // the program/constraint-set/Datalog "what-is" text the object enforces.
}

/// One presentation: a kind + a renderable payload + searchable text for the Spotter.
#[derive(Clone, Debug)]
pub struct Presentation {
    pub kind: PresentationKind,
    pub label: String,           // operator-legible tab name ("Cell State", "ocap Graph").
    pub body: PresentationBody,  // the data the thin gpui layer renders.
    pub search_text: String,     // flattened content the Spotter indexes.
}

/// The renderable payloads. Each variant is pure data; the gpui layer maps each to a
/// widget. New visual kinds are added here ONCE and every type that emits them renders.
#[derive(Clone, Debug)]
pub enum PresentationBody {
    Fields(Inspectable),                 // REUSES reflect.rs verbatim — no parallel model.
    Graph(GraphView),                    // nodes + typed edges (reuses graph.rs primitives).
    StateMachine(StateMachineView),      // states + transitions + current (lifecycle, escrow).
    Gauge(GaugeView),                    // bounded value: drawn/ceiling, ratchet rungs, finality.
    Timeline(TimelineView),              // ordered events (receipt chain, epoch history, attenuation).
    MerkleTree(MerkleTreeView),          // leaves + path + root (nullifier set, cap-crown, MMR).
    Lattice(LatticeView),                // partial order (AuthRequired, Auth rights, finality tiers).
    Trace(TraceView),                    // step-by-step evaluation (HMAC chain, constraint eval, hash absorb).
    Prose(String),                       // the Source/explain face (program text, Datalog, "what-is").
}

/// THE trait. A protocol object implements it to offer its presentation set. The blanket
/// requirement: `RawFields` is always present (the floor that guarantees universal coverage).
pub trait Presentable {
    fn present(&self, ctx: &PresentCtx) -> Vec<Presentation>;
    fn object_kind(&self) -> ObjectKind;
}
```

`PresentCtx` carries the read-only `&World`, the viewer principal, and the current block height — exactly the inputs `reflect.rs` and `inspect_act.rs` already take. A type's `present()` reads the live ledger and builds its set; **it never copies protocol types into a parallel schema** (the `reflect.rs` invariant, preserved). Registration is by impl: `impl Presentable for Cell`, `impl Presentable for CapabilityRef`, etc. Because most census types are foreign (`turn`, `cell`, `federation` crates), we register via thin newtype wrappers in starbridge-v2 (`ReflectedCap(&CapabilityRef)`) exactly as the census's `TrustlineReflection`/`FlashWellReflection` already do — the established "reflect a foreign struct into a starbridge view" pattern.

The seven kinds map onto the census's repeated proposal vocabulary:
- **RawFields** ← every census "raw-*" / "*-attributes" / "*-details" presentation. The floor.
- **Graph** ← "ocap graph", "effect-graph", "DAG visualization", "vouch graph", "blocklace DAG", "causal graph".
- **DomainVisual** ← "lifecycle diagram", "rung ladder", "capacity gauge", "finality ladder", "attenuation lattice" (when drawn as a picture), "tree visualization".
- **Affordances** ← "messages understood", "affordances view", "verb buttons" — the `InspectAct` `Message` list, reused.
- **Provenance** ← "receipt chain", "attenuation lineage", "transfer history", "causal history scrubber", "epoch history", "create-spend lifecycle".
- **Invariant** ← "conservation inspector", "commitment binder", "non-amplification proof-sketch", "cost/coordination classifier", "anti-ghost checker".
- **Source** ← "predicate tree browser", "Datalog derivation", "program pretty-print", "constraint catalog".

### 1.2 `Gadget` — interactive value construction with the verified-executor spine

`reflect.rs` reads; the census's "proposed gadgets" all WRITE — they construct a protocol value (a `StateConstraint`, an `Effect`, an `AttenuatedCap`, a `Turn`) that must flow through the verified executor. starbridge-v2 already has the canonical write spine: `simulate.rs`'s `IntentDraft` (compose effects) → `simulate()` (predict on a fork → `SimOutcome` verdict) → `commit()` (run the identical turn). Every gadget reuses it. We do NOT invent a parallel construction path.

```rust
// gadget.rs — interactive construction. Gpui-free; the value it yields is REAL.

/// A gadget builds ONE protocol value through a uniform field-form, then (for gadgets
/// that emit a turn) predicts-then-commits via the established simulate.rs spine.
pub trait Gadget {
    type Output;                         // the protocol value built (StateConstraint, Effect, Turn, AttenuatedCap…).
    fn fields(&self) -> Vec<GadgetField>;        // the form the thin gpui layer renders.
    fn set(&mut self, field: &str, v: GadgetInput); // edit one field (validated live).
    fn validate(&self) -> GadgetValidation;      // live fail-closed check (e.g. is_attenuation, non-empty condition).
    fn build(&self) -> Result<Self::Output, GadgetError>; // materialize the protocol value.
}

/// A gadget that emits a Turn additionally offers predict-then-commit — the SAME
/// IntentDraft → simulate → commit flow wonder.rs's DragValue already uses. This is the
/// uniform "produces a real value that flows through the verified executor" shape.
pub trait CommittingGadget: Gadget {
    fn to_draft(&self, world: &World) -> Result<IntentDraft, GadgetError>;
    fn predict(&self, world: &World) -> SimOutcome {           // reuses simulate::simulate.
        simulate::simulate(world, &self.to_draft(world).unwrap_or_default())
    }
    fn commit(&self, world: &mut World) -> CommitOutcome {     // reuses simulate::commit.
        simulate::commit(world, &self.to_draft(world).expect("validated"))
    }
}

/// The uniform field kinds the gpui layer renders generically (one widget per kind).
#[derive(Clone, Debug)]
pub enum GadgetField {
    HexBytes { key: String, len: usize },        // pubkey/token/hash/commitment input.
    U64 { key: String, min: u64, max: u64 },     // amount/height/slot spinner.
    I64 { key: String },                          // signed balance dial (issuer wells).
    CellPicker { key: String },                   // autocomplete over live ledger cells.
    Enum { key: String, variants: Vec<String> },  // AuthRequired tier, collateral mode, finality.
    BitMask { key: String, bits: Vec<String> },   // EffectMask facets, permission matrix.
    SubGadget { key: String, kind: GadgetKind },  // recursive: Pred AnyOf/AllOf, CallTree children.
    List { key: String, item: GadgetKind },       // Vec<Effect>, Vec<StateConstraint>, caveat chain.
}
```

The **uniform shape** the prompt asks for: a gadget is `fields() → set() → validate() → build()`; a turn-emitting gadget adds `to_draft → predict → commit`. Three concrete classes the census demands all fit this:

1. **Pure value gadgets** (build a non-turn value): `Predicate Composer` → `StateConstraint`, `Cap Attenuator` → `AttenuatedCap`, `Caveat Builder` → `WireCaveat`. `validate()` runs the real predicate (`is_attenuation` for the attenuator; `evaluate_simple_constraint` for the caveat editor's live preview). The output then feeds a `SubGadget`/`List` slot of a committing gadget.
2. **Committing gadgets** (emit a turn): `Transfer Composer`, `Cell Genesis Builder`, `Lifecycle Transition Trigger`, `Capability Grant Composer`, the organ verbs. These implement `CommittingGadget`; `predict()` shows the pre/post ledger diff via `SimOutcome` BEFORE `commit()` runs the identical turn — the census's "Compose → Simulate → Review → Commit flow" is literally `IntentDraft → simulate → commit`.
3. **Verifier gadgets** (build a value AND check it against live machinery, read-only): `Receipt Hash Recomputer`, `Q-Chain Verifier`, `Non-Membership Prover`, `Conservation Checker`, `HMAC Chain Replayer`. These implement `Gadget` with `Output = VerificationResult`; `build()` runs the real recompute (`receipt_hash()`, `recompute_root()`, `verify_range`) and returns green/red — no commit, but real cryptographic machinery.

### 1.3 gpui-free + cargo-test-able, with a thin render layer

The established discipline (every doc comment in `reflect.rs`/`wonder.rs`/`inspect_act.rs` states it): the MODEL is pure data, proven by `cargo test`; the gpui layer is a thin renderer. The framework holds the line:

- `Presentation`/`PresentationBody` and `GadgetField`/`GadgetInput` are plain enums of data. `present()` and `build()` take `&World`/`&mut World` and return data — no gpui types cross the boundary.
- The thin gpui layer is a single dispatch: `match presentation.body { Fields(i) => render_field_tree(i), Graph(g) => render_graph(g), StateMachine(sm) => render_sm(sm), … }`. Adding a new census type adds NO gpui code if it reuses existing `PresentationBody` variants; adding a genuinely new visual kind adds ONE arm.
- Tests assert the model, exactly as `reflect.rs`'s tests do: `assert!(cell.present(&ctx).iter().any(|p| p.kind == Graph))`, `let out = grant_gadget.predict(&w); assert!(out.would_commit())`, `assert!(attenuator.validate().is_fail_closed_on_amplification())`. The census's per-type "gpui-free + cargo-test-able" requirement is met by construction.

### 1.4 Spotter — universal search over the presentation index

Pharo's Spotter searches every object by every view. Here: a `Spotter` indexes every live `Presentable`'s presentations by their `search_text` (the flattened field labels, hashes, hex ids, constraint names, Datalog facts). It reuses the existing `dreggverse_map.rs`/`links_here.rs` navigation primitives for "jump to result".

```rust
pub struct Spotter<'w> { world: &'w World }
impl<'w> Spotter<'w> {
    /// Search every live object's every presentation. Returns ranked hits, each naming
    /// the object, the presentation kind that matched, and a navigable focus.
    pub fn search(&self, query: &str) -> Vec<SpotterHit>;
}
pub struct SpotterHit {
    pub focus: InspectFocus,          // reuses inspect_act.rs's focus (extend variants per kind).
    pub matched_kind: PresentationKind,
    pub snippet: String,
}
```

The index is built lazily off the live `World` (cells, receipts, factories, organs, nullifiers) — never a stale cache, matching the `ProofBoard::build`/`OrganSurvey::build` "scan the live ledger every render" pattern.

### 1.5 Halo — the direct-manipulation layer, generalized

wonder.rs already seeds a 3-command `Halo` ring (`Inspect`/`Grab`/`Explain`) over `GlowingCell`s. The framework promotes `Halo` to the universal direct-manipulation layer over ANY `Presentable`:

- `Halo::Inspect` opens the object's presentation set (the tabbed `Presentable::present` result) — generalizing today's single-`Inspectable` open.
- `Halo::Grab` arms a `CommittingGadget` (the `DragValue` intent generalizes: dragging cap→cell arms the `Capability Grant Composer`; dragging value arms the `Transfer Composer`).
- `Halo::Explain` speaks from the `RawFields` + `DomainVisual` presentations (already its source).
- New halo commands are per-`ObjectKind` (a receipt's halo carries `VerifyChain`; a cap's carries `Attenuate`) — the ring is data, extended per kind exactly as `Message` vocabularies extend per `InspectFocus`.

### 1.6 What is reused, not replaced

| Existing module | Role in the framework | Reuse, not replace |
|---|---|---|
| `reflect.rs` | `RawFields` presentation body verbatim; `Inspectable`/`Field`/`FieldValue`/`ObjectKind`/`short_hex` are the floor types | `present()`'s first element is always the existing `reflect_*` output |
| `affordance.rs` | `Affordances` presentation = `AffordanceSurface` projected; `CellAffordance::authorized_for` is the cap badge | gadgets that emit turns route through `AffordanceSurface::fire` where applicable |
| `inspect_act.rs` | `InspectAct`/`Message`/`SendResult`/`InspectFocus` ARE the Affordances kind + the act loop; `InspectFocus` is the Spotter's navigation target | the loop's shape is the framework's act half, unchanged |
| `wonder.rs` | `Halo` ring + `DragValue` = the direct-manipulation layer; `GlowingCell` liveliness feeds presentation freshness | `Halo` generalizes; `DragValue` is the first `CommittingGadget` |
| `simulate.rs` | `IntentDraft`/`simulate`/`commit`/`SimOutcome` = the `CommittingGadget` spine; `EffectKind` is the Effect gadget's variant set | EVERY committing gadget reuses this predict-then-commit path |
| `graph.rs` | `Graph` presentation body primitives | graph views emit `GraphView`, rendered by the existing graph renderer |
| `proofs.rs` / `organs.rs` / `organ_ops.rs` | `ProofBoard`/`ProofEntry`, `TrustlineReflection`/`FlashWellReflection`/`OrganSurvey`/`OrganDriver` are already presentation+gadget pairs — they become `impl Presentable` / `impl CommittingGadget` | wrap, don't rewrite |
| `workspace.rs` | hosts the tabbed presentation panes + gadget forms | the moldable inspector lives here |

---

## Part 2 — THE COMPLETE COVERAGE MATRIX

Legend — Coverage: **L**ive (a real projection/driver exists today), **P**artial (a field appears in `reflect.rs` but no dedicated view), **N**one. Presentations use the seven kinds (RF=RawFields, G=Graph, DV=DomainVisual, AF=Affordances, PV=Provenance, IV=Invariant, SRC=Source). Gadgets name the family.

### Slice 1 — kernel nouns & verbs

| Type | Presentations | Gadgets | Cov |
|---|---|---|---|
| Verb (kernel enum) | RF, DV(substance ledger), SRC(minimality), G(effect tree) | Verb Constructor, Effect Classifier, Attenuation-Lattice (value) | **N** |
| Cell | RF, DV(state tabs/lifecycle), G(ocap), AF, PV, IV(commitment), SRC(program) | Cell Genesis (commit), State Slot Editor (commit), Lifecycle Trigger (commit), Cap Grant Composer (commit) | **L** (RF) / P (rest) |
| Cap (CapabilityRef) | RF, DV(facet mask), G(attenuation lineage), IV(non-amp), AF(exercise sim) | Cap Attenuator (value), Expiry Setter, Breadstuff Binder, Freshness Checker (verifier) | **P** (CapEdge only) |
| Asset (issuer-cell) | RF, DV(ledger/holders), G(transfer history), PV, IV(conservation Σδ=0) | Transfer Composer (commit), Mint Gating (commit), Burn Disclosure (commit) | **P** (balance) |
| Pred + WitnessedPredicate | SRC(tree), RF, AF(auth gate seq), IV(witness verify) | Predicate Composer (value), Caveat Editor (value), Witness Packager, Test Harness (verifier) | **N** |
| Turn | RF, G(forest/effect DAG), AF(auth trace), PV(receipt lineage), IV(conservation) | Turn Composer (commit), Action Builder (value), Signature Verifier, Conservation Checker (verifier) | **N** |
| Q (TurnReceipt) | RF, DV(card), PV(chain), IV(verification status) | Receipt Hash Recomputer (verifier), State Commitment Verifier, Finality Watcher, Q-Chain Verifier | **L** (RF via `reflect_receipt`) |

### Slice 2 — effects & call-forest

| Type | Presentations | Gadgets | Cov |
|---|---|---|---|
| Effect (28 variants) | RF(tree), DV(linearity badges), G(effect graph), IV(bytewise cost), AF(proof-bind) | Effect Picker, Effect Composer (value), Conservation Checker (verifier), Proof Uploader, Sim Button (commit), Mask Editor | **P** (`EffectSummary`/`EffectKind`) |
| Action | RF, AF(auth audit), SRC(precondition tree), DV(delegation/commitment badges) | Action Builder (value), Witness-Blob Manager, Authorization Composer, Precondition Composer | **P** (`CellAffordance` template) |
| Authorization (9 variants) | RF, IV(verification cascade), G(bearer chain), SRC(token caveats) | Variant Picker, Signature Signer, Bearer Builder, Token Decoder, WitnessedPred Picker | **P** (`required_rights`) |
| CallTree | RF, G(tree visual), DV(depth/cost), MerkleTree(path) | Tree Builder (value), Tree Reorderer, Tree Validator (verifier) | **P** (`IntentDraft`) |
| CallForest | RF(overview), G(tree), PV(exec order), IV(atomicity) | Forest Composer (value), Forest Simulator (commit), Forest Committer (commit) | **L** (`IntentDraft`) |
| LinearityClass | RF(badge), IV(conservation audit) | — (read-only enum) | **P** |
| DelegationMode | RF(badge) | Delegation-Mode Picker (value) | **N** |
| CommitmentMode | RF(badge) | Commitment-Mode Picker (value) | **N** |
| WitnessBlob | RF(list), Trace(bytes preview) | Witness-Blob Uploader (value) | **N** |
| Turn (full) | RF(summary), RF(metadata), G(forest), PV | Turn Builder (commit), Turn Signer | **P** (`simulate`) |
| TurnReceipt (full) | RF, PV(chain), IV(verification) | Receipt Navigator | **L** |

### Slice 3 — predicate-caveat language

| Type | Presentations | Gadgets | Cov |
|---|---|---|---|
| WitnessedPredicateKind | RF(enum), G(verifier dispatch), SRC(commitment anchor) | Kind Picker (value), Verifier Selector | **N** |
| WitnessedPredicate | RF(declaration), Trace(verification), RF(proof artifact) | WP Builder (value), Input Resolver (verifier) | **N** |
| InputRef | RF(source), IV(type-check) | Input-Source Selector (value) | **N** |
| PredicateInput | RF(value display) | — (runtime ephemeral) | **N** |
| WitnessedPredicateRegistry | DV(dashboard), RF(custom catalog) | Registry Config Panel (dev), Verifier Installer | **N** |
| WitnessedPredicateVerifier trait | RF(identity card), Trace(audit) | — | **N** |
| WitnessProducer(Registry/trait) | RF(registry view) | — | **N** |
| StateConstraint (50+) | SRC(tree), Trace(eval), IV(cost/coordination), SRC(sugar decode) | Constraint Builder (value), Validator (verifier), Simple Lifter | **N** |
| SimpleStateConstraint (~30) | RF(atom quick-view), SRC(negation) | Simple Builder (value), Not Wrapper | **N** |
| AuthorizedSet | RF(source card) | AuthorizedSet Selector (value) | **N** |
| RenouncedSet | RF(non-membership card) | RenouncedSet Selector (value) | **N** |
| NonMembershipNeighborProof / V2 | RF(neighbor card), MerkleTree(adjacency) | Neighbor Proof Builder (value) | **N** |
| CredentialSetMembershipProof | RF(card), IV(anonymity), IV(issuer-binding) | Credential Proof Builder (value) | **N** |
| DeltaRelation | RF(binding card) | DeltaRelation Picker (value) | **N** |
| ReadSet & CustomDescriptor | RF(metadata card) | ReadSet Builder (value) | **N** |
| BoundBranch (anyOfBound) | RF(branch list) | BoundBranch Adder (value) | **N** |
| NeighborAdjacency/IssuerRoot/FinalizedRoot authorities | DV(authority dashboard) | — (host-installed) | **N** |

### Slice 4 — capabilities & authority

| Type | Presentations | Gadgets | Cov |
|---|---|---|---|
| AuthRequired | Lattice(order diagram), RF, G(narrowing trace), SRC(predicate affordances) | Lattice Picker (value), Narrowing Validator (verifier), Witness Matcher | **L** (`reflect`/`affordance`) |
| CapabilityRef | RF(details), G(lineage), DV(c-list grid) | Cap Attenuation Composer (value), Breadstuff Input, Expiry Setter | **P** (CapEdge) |
| CapabilitySet | DV(c-list table), MerkleTree(tombstone tree), IV(cap-root proof) | Grant Wizard (commit), Attenuation Wizard (value), Revoke Tool (commit) | **P** (count) |
| CanonicalCapTree | MerkleTree(tree viz), MerkleTree(membership), DV(stats) | Membership Prover (verifier) | **N** |
| SurfaceCapability | RF(window card), G(delegation tree), IV(cap-vs-cell) | Window Share Wizard (commit), Embed Tool (commit), Revoke Button (commit) | **L** (`shell.rs`/`surface.rs`) |
| is_attenuation (law) | IV(attenuation judge), IV(non-amp sketch) | Attenuation Validator (verifier), Lattice Path Finder | **L** (gate in `affordance`/`shell`) |
| revocation (tombstone) | PV(revocation log), MerkleTree(tombstone overlay), IV(witness-across-revoke) | Revoke Tool (commit) | **P** (`shell.rs`) |

### Slice 5 — cell-state structure

| Type | Presentations | Gadgets | Cov |
|---|---|---|---|
| CellState | DV(ledger/field cartography/heap/kernel-roots), IV(authority binding), DV(lifecycle), PV, AF | Balance Dial, Nonce Spinner, Field Visibility Chooser, Field Editor, Ext-Map, Heap Editor, System-Root, Lifecycle SM, Epoch Bumper, Commit-Height (all via semantic verbs → commit) | **P** (subset of fields) |
| Cell | RF(overview), RF(identity), DV(permissions matrix), RF(VK/program), RF(delegation), G(c-list), IV(commitment), DV(lifecycle), RF(mode), PV(authority sandwich) | Cell Constructor (commit), Permissions Editor (commit), Lifecycle Panel (commit), C-List Attenuator (value), VK Updater (commit), Remote Stub Minter | **L** (RF) / P |
| FieldVisibility | DV(visibility table) | Visibility Setter (commit) | **N** |
| CellLifecycle | DV(state machine), RF(payload), PV(audit trail) | Seal/Unseal/Destroy/Migrate/Archive Dialogs (commit) | **P** (`format!`) |
| CapabilityRef (cell view) | DV(c-list table), MerkleTree(leaf), G(graph), DV(facet), IV(R7 freshness) | Grant Composer (commit), Attenuation Refiner (value), Revoke (commit), Freshness Refresh (commit) | **P** (CapEdge) |
| HeapLeaf | DV(heap browser/cartography), MerkleTree(path) | Heap Entry Editor (commit) | **N** |
| DelegatedRef | RF(snapshot inspector), DV(staleness) | Snapshot Refresher (commit) | **P** (bool) |
| VerificationKey | RF(VK card), IV(integrity) | VK Setter (commit) | **N** |
| Permissions | DV(8×6 matrix) | Permissions Batch Editor (commit) | **N** |
| CellMode | RF(mode indicator) | Mode Toggler (refuses — content-addressed) | **P** (`format!`) |

### Slice 6 — receipts, provenance, forests

| Type | Presentations | Gadgets | Cov |
|---|---|---|---|
| TurnReceipt | RF(ledger/detail), PV(causal scrubber/chain diagram), IV(conservation audit), AF(consumed-cap witness), IV(sig verify) | Receipt Picker, Hash Navigator, Merkle Path Viz, Chain Composer, Finality Badge, Disclosure Toggle, Replay Scrubber, Routing Viz | **L** (`reflect_receipt`) |
| WitnessedReceipt | RF(summary), Trace(trace witness), RF(recursive proof), DV(scope toggle), RF(bilateral schedule) | Scope Selector, Witness-Hash Validator (verifier), Trace-Row Selector | **P** (`replay.rs` implicit) |
| CallForest | G(tree/DAG), RF(action detail), PV(effect stream), MerkleTree(forest proof) | Action Picker, Action Composer (value), Effect-Type Selector, Depth Gauge | **P** (`RecordedStep` carries it) |
| ConsumedCapWitness | RF(inspector), MerkleTree(path widget), AF(per-action), IV(authority audit) | Cap-Witness Validator (verifier), Leaf Displayer, Path Direction Encoder | **L** (count via `reflect_nullifiers`) |
| RecordedStep | PV(timeline scrubber/replay log), DV(checkpoint browser), IV(replay verification) | Scrub Slider, Root-Tooth Displayer, Replay Status Badge | **L** (`replay.rs`) |
| Checkpoint | DV(marker), DV(quick-save) | Checkpoint Marker | **L** (`replay.rs`) |
| Mmr | IV(root), MerkleTree(peak frontier), IV(range verifier), MerkleTree(position search) | Range Query Composer, Merkle Path Widget, Peak Breakdown | **N** |
| RangeOpening | RF(proof inspector), IV(batch) | RangeOpening Validator (verifier), Path Siblings List | **N** |
| Block (blocklace) | G(DAG), RF(detail), PV(consensus timeline) | Block Node, Finality Badge | **N** |

### Slice 7 — commitments, nullifiers, conservation

| Type | Presentations | Gadgets | Cov |
|---|---|---|---|
| StateCommitment | RF(raw hex), RF(component digest), IV(authority coverage), DV(canonical-vs-rotated), PV(binding chain) | State Mutator, Component Absorber (verifier), Collision Searcher, Rotated Reconstructor | **P** (`state_root` field) |
| Nullifier | DV(lifecycle), MerkleTree(tree), MerkleTree(non-membership), IV(double-spend), DV(audit) | Nullifier Generator (verifier), Non-Membership Prover, Membership Tracer, Set Mutation Viz | **P** (`reflect_nullifiers`) |
| NullifierSet | DV(roster), MerkleTree(structure), IV(proof verify), DV(cardinality) | Inserter (verifier), Merkle Path Builder, Non-Membership Prover, Rollback Reverter | **N** |
| V9RotationContext | RF(source), Trace(pre-limb assembler), Trace(wire-commit chain), DV(cell-vs-context) | Context Mutator, Ledger Extractor, Pre-Limb Reconstructor, Wire-Commit Sim | **N** |
| CrossCellDelta | DV(roster), DV(per-asset), Trace(trace builder), IV(forgery detector) | PI Extractor, Supply Converter, Aggregation Builder (verifier), Conservation Attacker | **N** |
| NoteCommitment | Trace(creation), MerkleTree(tree), IV(spend validation), DV(audit), DV(create-spend graph) | Commitment Hasher (verifier), Merkle Path Builder, Create-Spend Linker, Tree Mutation Viz | **N** |
| HeapRoot | MerkleTree(structure), IV(entry mutation), RF(empty ref), MerkleTree(path) | Entry Setter (commit), Entry Remover (commit), Path Builder, Commitment Binder (verifier) | **N** |
| CapabilityRoot | DV(roster), MerkleTree(tree), MerkleTree(membership), PV(revocation), IV(binding) | Leaf Hasher, Cap Granter (commit), Revoker (commit), Path Builder, Binder (verifier) | **N** |

### Slice 8 — tokens (macaroon/biscuit)

| Type | Presentations | Gadgets | Cov |
|---|---|---|---|
| Macaroon | G(chain), Trace(integrity replay), IV(authority narrowing), G(discharge), RF(wire) | Caveat Builder, Chain Replayer (verifier), Discharge Binder, Authority Narrower, KeyId Lookup | **N** |
| Caveat (trait) | SRC(type decode), IV(enforcement), G(narrowing) | Caveat Decoder, First-Party Maker, Third-Party Maker, Request Matcher (verifier) | **N** |
| WireCaveat | RF(hex dump), SRC(decoded), Trace(HMAC link) | WireCaveat Inspector, Hex Encoder | **N** |
| CaveatSet | G(chain), IV(set semantics), IV(difference) | Caveat List Editor, Set Simulator (verifier) | **N** |
| ThirdPartyCaveat | G(gateway), RF(discharge status), IV(suspension) | 3P Maker, Discharge Checker (verifier), Gateway Client | **N** |
| DreggGrant | DV(grant table), IV(cumulative authority), DV(per-type) | Grant Decoder, Grant Builder, Grant Intersector | **N** |
| AuthToken (trait) | RF(format detect), IV(verification report), PV(attenuation path) | Token Decoder, Token Verifier, Token Attenuator, RoundTrip | **N** |
| MacaroonToken | RF(root), PV(attenuation history), RF(discharge) | Root Minter, HMAC Replayer (verifier), Attenuation Chain | **N** |
| BiscuitToken | G(authority blocks), Trace(Datalog derivation), G(pubkey chain) | Biscuit Minter, Datalog Editor, Authorizer Sim (verifier), Delegation Builder | **N** |
| HeldToken | DV(roster), PV(attenuation), MerkleTree(membership), G(delegation), IV(authority compare) | Token Minter (commit), Attenuator (value), Delegation Envelope Builder, Receiver, Membership Viz | **L** (`cipherclerk.rs`) |
| DelegatedToken | RF(envelope), IV(authority transfer), G(chain of trust) | Delegation Signer, Verifier, Envelope Inspector | **L** (`cipherclerk.rs`) |
| AgentCipherclerk | RF(identity), DV(wallet), PV(receipt chain), G(key derivation) | Clerk Generator, Sub-Agent Deriver, Turn Signer (commit), Receipt Monitor, Wallet Browser | **L** (`cipherclerk.rs`) |
| AppCipherclerk | RF(action builder), RF(turn preview) | Action Builder (value), Turn Builder (commit) | **N** |
| Token / Macaroon / ExecAuth / Cap (Lean) | RF, Lattice(rights), SRC | Abstract Token Viz, Chain Replay Sim, Rights Lattice Viz, Cap Creator, Invoke Checker | **N** (Lean models) |

### Slice 9 — federation & consensus

Every type in this slice is **None** in starbridge-v2 today (the census states "ZERO inspector coverage").

| Type | Presentations | Gadgets | Cov |
|---|---|---|---|
| Federation | DV(committee), RF(identity), RF(seat), IV(verification) | Committee Builder, Epoch Transition, Seat Setter | **N** |
| Block / Blocklace | RF(detail), G(DAG/timeline), Trace(merge diff), IV(equivocation) | Block Signer, Predecessor Linker, Block Inserter, Merge Sim, Round Explorer | **N** |
| FinalityLevel | DV(ladder), PV(history) | Finality Threshold Dial | **N** |
| BlockId | RF(detail), G(cross-ref) | ID Search | **N** |
| RevocationBlock | RF(body), RF(events), IV(proof) | Event Adder, State Root Computer (verifier) | **N** |
| QuorumCertificate | RF(summary), Lattice(threshold), RF(votes), IV(committee alignment) | Vote Collector, BLS Aggregator | **N** |
| AttestedRoot | RF(detail), IV(signature), G(cross-fed) | Root Certifier | **N** |
| FederationReceipt | RF(overview), IV(QC), PV(cross-fed chain) | Receipt Builder, Verifier | **N** |
| FederationCommittee / BeaconCommittee | RF(pubkeys), RF(KZG/randomness) | Committee Serializer, Beacon Dealer, Partial Collector | **N** |
| BeaconOutput | RF(value), SRC(usage) | Randomness Inspector | **N** |
| Checkpoint (fed) | DV(snapshot), IV(QC), IV(pruning) | Creator, Verifier | **N** |
| Vouch / Bond / AdmissionRegistry / Admission | RF, G(vouch graph), DV(registry), PV(slash) | Vouch Creator, Bond Poster, Admission Checker, Slash Executor | **N** |
| EquivocationEvidence / Court | RF(fork proof), DV(docket), PV(resolution) | Evidence Finder, Verdict Executor | **N** |
| NullifierLog / SoloConsensusState | DV(sequence), RF(solo status) | Entry Inspector, Merge Sim, Solo Dashboard | **N** |
| CausalDag | G(causal graph), PV(happened-before) | Path Finder | **N** |
| Consensus / Finality / BFT (concepts) | SRC(algorithm), PV(order timeline), IV(safety/liveness) | Tau Sim, Conflict Detector, Safety Verifier | **N** |
| quorum_threshold | DV(quorum table), IV(safety) | Quorum Calculator | **N** |
| DKG / Epoch | DV(progress), PV(epoch history) | DKG Sim, Epoch Planner | **N** |
| LocalSeat / KnownFederations | RF(role), DV(registry), G(cross-fed map) | Seat Manager, Federation Adder, Receipt Verifier | **N** |
| Turn (blocklace payload) | RF(payload), SRC(decode) | Turn Inspector | **N** |

### Slice 10 — organs

| Type | Presentations | Gadgets | Cov |
|---|---|---|---|
| TrustlineTerms / TrustlineReflection | DV(live position/gauge), G(bilateral), DV(state machine), PV(conservation ledger), DV(capacity) | Issue Trustline (commit), Draw/Repay/Settle/Close (commit) | **L** (`organs.rs`/`organ_ops.rs`) |
| TrustlineCollateral | RF(mode indicator), DV(settlement table) | Collateral Picker (value, at open) | **L** (slot 7) |
| FlashWellTerms / FlashWellReflection | DV(live position/rung ladder/accrual), IV(net-delta envelope) | Open/Borrow/Close (commit) | **L** (`organs.rs`) |
| ChannelTerms | DV(roster/epoch timeline), IV(governance gates), IV(epoch-tying cert) | Group Creator, Membership Editor, Rekey, Council Gate (all commit, behind captp) | **N** (RemoteOrgan stub) |
| EscrowTerms | DV(deal summary), DV(release-vs-refund) | Escrow Creator, Release/Refund Initiator (commit) | **N** |
| ObligationTerms | RF(bond escrow), DV(dual-resolution) | Obligation Poster, Fulfillment/Slash (commit) | **N** |
| BridgeTerms | DV(bridge lock) | Bridge Locker, Finalize/Cancel (commit) | **N** |
| OrganSurvey | DV(organs tab), RF(summary stats) | Organ Creator Menu, Sort/Filter Toolbar | **L** (`organs.rs`) |
| OrganDriver | PV(activity feed), IV(error diagnostics) | All organ verb buttons (commit) | **L** (`organ_ops.rs`) |
| StateConstraint (organ view) | SRC(program pretty-print), Trace(debugger) | Constraint Builder DSL (value) | **L** (evaluated) |
| CellProgram | RF(variant), SRC(predicate/cases tree), AF(guard) | Program Installer (commit) | **P** |

### Slice 11 — proofs & circuit verification

| Type | Presentations | Gadgets | Cov |
|---|---|---|---|
| VerificationTier | DV(tier badge/spectrum/economics), IV(attestation source) | Tier Selector Dial, Upgrade Button, Status Breadcrumb | **L** (`proofs.rs`) |
| EffectVmDescriptor2 | DV(table layout), G(constraint dependency), RF(wire bytes), IV(fidelity) | Table Selector, Constraint Filter, Bus-Diagram Builder | **N** |
| TableDef2 | RF(card/registry), SRC(semantics glossary) | Table Factory, Card Expander | **N** |
| VmConstraint2 | RF(catalog), G(dependency tracer), IV(degree analyzer), IV(guard coverage) | Constraint-Form Picker, Lookup/Mem-Op/Map-Op Forms | **N** |
| AirDescriptor | RF(shape card), DV(PI layout), IV(fingerprint), IV(VK composition) | Descriptor Form, PI-Slot Editor, Fingerprint Preview | **N** |
| ProofBoard | PV(timeline), DV(tier distribution), RF(entry detail), AF(upgrade lane) | Entry Selector, Tier Filter, Upgrade Menu | **L** (`proofs.rs`) |
| ProofEntry | RF(row/detail), IV(evidence breakdown) | Entry Card, Upgrade Button, Hash Copier | **L** (`proofs.rs`) |
| AttachStatus | RF(badge), IV(verification affordance) | Attach Toggle (federated) | **L** (`proofs.rs`) |
| BatchProof / Ir2BatchProof | RF(metadata), Trace(FRI query) | Proof Inspector (opaque) | **N** |
| Inspectable (Proof) | RF(tree), PV(provenance link) | Inspectable Navigator | **L** (`reflect_proof_status`) |
| RecursionVk / RecursionConfig | RF(VK badge), DV(FRI config) | — | **N** |
| VerificationTier+AttachStatus | IV(2D matrix) | — | **L** |

### Slice 12 — factories, identity, intents

| Type | Presentations | Gadgets | Cov |
|---|---|---|---|
| FactoryDescriptor | RF(summary), RF(detail tree), IV(constraint viz), G(children gallery), IV(VK derivation) | Descriptor Builder (value), Constraint Composer, Cap-Template Editor, Field-Constraint Picker, VK-Strategy Selector | **L** (`reflect_factory`) |
| StateConstraint (factory) | SRC(list/matrix), Trace(simulator), G(dependency) | State-Constraint Picker, Batch Builder, Allowed-Transitions Editor, Temporal-Gate Composer, Affine-Inequality Builder | **N** (shared with slice 3) |
| EscrowTerms/ObligationTerms/BridgeTerms/TrustlineTerms | DV(deal summary/detail), DV(capacity gauge), DV(state machine editor) | Escrow/Obligation/Trustline Builders (value→commit), Condition-Commitment Builder | **N** (shared with slice 10) |
| CellProgram | RF(variant), SRC(predicate/cases tree), AF(guard viz) | Program Builder, Case Editor, Guard Composer | **P** (`has_program`) |
| FactoryCreationParams | RF(summary/detail) | Params Builder (commit) | **P** (executor-internal) |
| AffordanceSurface / CellAffordance | AF(message list), RF(affordance detail), PV(recent fires) | Affordance Designer, Effect-Template Composer, Surface Editor | **L** (`affordance.rs`) |
| InspectAct / Message / SendResult | AF(dual-panel), RF(firing panel), RF(result) | Message Sender (commit), Prediction Preview (predict) | **L** (`inspect_act.rs`) |

**Coverage census across all 12 slices:** ~120 types. **Live (any real projection/driver):** ~24 (cell-RF, receipt, image, proof-status, factory, nullifier-count, ProofBoard/Entry/Tier/Attach, trustline/flashwell/organ-survey/driver, HeldToken/DelegatedToken/AgentCipherclerk, AffordanceSurface/InspectAct, SurfaceCapability, AuthRequired, RecordedStep/Checkpoint, replay scrubber). **Partial (a field surfaces in `reflect.rs` but no dedicated presentation):** ~22. **None — the gap to close:** **~74 types**, concentrated in three blocks the matrix makes visible: the entire **predicate-caveat language** (slice 3, ~17 types, all None), the entire **federation-consensus** layer (slice 9, ~30 types, all None), and the entire **commitments/circuit** internals (slices 7 & 11, ~20 types, all None). No census type lacks the `RawFields` floor under this framework — every type at minimum gets the existing `Inspectable` projection plus a registry entry, so the completeness ledger has no holes; "None" means "no presentation richer than RawFields yet," and the build plan below closes the high-value ones.

**Flagged: types the census found with NO inspector anywhere today** (the true zeros, not even RF): all of slice 3 (predicates), all of slice 9 (federation), `NullifierSet`/`V9RotationContext`/`CrossCellDelta`/`NoteCommitment`/`HeapRoot`/`CapabilityRoot` (slice 7), all macaroon/biscuit wire types (slice 8), `CanonicalCapTree`/`Mmr`/`RangeOpening`/`Block` (slices 4/6), `EffectVmDescriptor2`/`TableDef2`/`VmConstraint2`/`AirDescriptor`/`BatchProof` (slice 11), `EscrowTerms`/`ObligationTerms`/`BridgeTerms`/`ChannelTerms` (slice 10), `FieldVisibility`/`HeapLeaf`/`VerificationKey`/`Permissions` (slice 5). These are the burn-down targets of the lanes below.

---

## Part 3 — THE BUILD PLAN (delivered — this is now the module index)

Originally ordered by value × independence; every lane below has since landed as a coherent,
gpui-free, `cargo test`-able module in `starbridge-v2/src/`. The `[…]` tags and "needs primitive
first" notes are the original dependency planning, kept as rationale; the **→ module** pointer on
each lane names where it actually shipped.

### L1 — The Presentation Spine `[FRAMEWORK PRIMITIVE — must land first]` → shipped: `presentable.rs` (commit `800945db6`)
**Build:** `presentable.rs` (the `Presentable` trait, `Presentation`, `PresentationKind`, the seven `PresentationBody` variants), the registry, and `Spotter`. Make `reflect.rs`'s existing `Inspectable` the `RawFields` body verbatim, and re-house `inspect_act.rs`'s `Message` list as the `Affordances` body. Ship `impl Presentable` for the already-Live types (Cell, Receipt, Factory, Proof, Image, the organs) as the proof-of-shape.
**Reuses:** `reflect.rs` (RawFields), `inspect_act.rs` (Affordances), `graph.rs` (Graph body), `dreggverse_map.rs`/`links_here.rs` (Spotter navigation).
**Primitive needed:** none — it IS the primitive. **Pure-additive?** No — every other lane depends on it. This lane unblocks the rest.

### L2 — The Predicate/Caveat Composer `[needs L1]` → shipped: `predicate_composer.rs`
**Build:** the `StateConstraint`/`SimpleStateConstraint`/`Pred`/`WitnessedPredicate` builder (slice 3 + slice 12's constraint half): `Constraint Composer` (value gadget over the 50+ atoms), the `SRC(tree)` + `IV(cost/coordination §8 classifier)` + `Trace(eval)` presentations, the anti-strip `AnyOfBound` safety checker, and the live `evaluate_simple_constraint` test-harness verifier gadget.
**Reuses:** `cell/src/program.rs` + `cell/src/predicate.rs` (the real evaluators — gadget `validate()` calls them), `cell/src/witness.rs`. The "lamesauce language uplift" the Refinement Epoch memory names.
**Primitive needed:** L1's `Gadget`/`SubGadget`/`List` field kinds (predicates are recursively composed). **Pure-additive?** Mostly — it adds new gadgets/presentations; the only shared primitive is the recursive `SubGadget`. Highest value: the richest entirely-`None` surface, and the one the project's vision (`project-dregg3-campaign`, "one Pred algebra") most wants legible.

### L3 — The Effect/CallForest/Turn Builder `[needs L1; partially exists]` → shipped: `turn_builder.rs`
**Build:** generalize `simulate.rs`'s `IntentDraft` into the universal `Effect Composer` / `Action Builder` / `CallTree`/`CallForest` builder / `Turn Composer` (slices 1, 2, 6) as `CommittingGadget`s, with the `Compose→Simulate→Review→Commit` flow (already `IntentDraft→simulate→commit`), the `Conservation Checker` verifier, and the `Authorization Composer`.
**Reuses:** `simulate.rs` verbatim (`IntentDraft`, `EffectKind`, `simulate`, `commit`, `SimOutcome`), `affordance.rs` (`AffordanceSurface::fire`), `inspect_act.rs` (the act loop).
**Primitive needed:** L1 + the `CommittingGadget` trait (lands in L1). **Pure-additive?** Yes — extends the existing `IntentDraft` rather than replacing it. Foundational: it produces the values every other committing gadget composes.

### L4 — Capabilities, Attenuation & the Cap-Crown `[needs L1]` → shipped: `cap_inspector.rs`
**Build:** the full `CapabilityRef`/`CapabilitySet`/`CanonicalCapTree`/`AuthRequired` surface (slices 4, 5-cap): `Cap Attenuator` (value, `validate` = real `is_attenuation`), `Grant/Revoke Wizards` (commit), the `Lattice` presentation for `AuthRequired`, the `MerkleTree(tombstone)` cap-crown view + `Membership Prover` verifier, the R7 `Freshness Checker`.
**Reuses:** `affordance.rs`/`shell.rs` (`is_attenuation` gate, already Live), `circuit/src/cap_root.rs` (`CanonicalCapTree`), `cell/src/capability.rs`.
**Primitive needed:** L1 + L3's grant/revoke `CommittingGadget`s. **Pure-additive?** Yes. High value: the ocap web is the protocol's spine and the ARGUS linchpin (`project-cap-reshape-plan`).

### L5 — Cell-State Deep Inspector `[needs L1; partially exists]`
**Build:** the complete `CellState`/`Cell`/`FieldVisibility`/`CellLifecycle`/`VerificationKey`/`Permissions`/`HeapLeaf`/`DelegatedRef` surface (slice 5): the field-cartography + kernel-roots + commitment-binding presentations, the `Permissions 8×6 matrix`, the `Lifecycle state machine` (commit dialogs), the heap editor — all through semantic verbs (commit), respecting the P0-1 sealing (no raw field writes).
**Reuses:** `reflect.rs` (extends `reflect_cell`), `cell/src/state.rs`/`lifecycle.rs`/`commitment.rs`.
**Primitive needed:** L1 + L3 (semantic-verb commits). **Pure-additive?** Yes — deepens the already-Live cell view.

### L6 — Receipts, Provenance & Time-Travel `[needs L1; partially exists]` → shipped: `receipts_inspector.rs`
**Build:** the `TurnReceipt`/`WitnessedReceipt`/`ConsumedCapWitness`/`RecordedStep`/`Checkpoint`/`Mmr`/`RangeOpening` surface (slice 6): the `PV(causal scrubber)` over the already-Live `replay.rs` History, the `MerkleTree(consumed-cap path)` verifier, the `Q-Chain Verifier`, the MMR range-proof verifier.
**Reuses:** `replay.rs` (History/Checkpoint, Live), `reflect.rs` (`reflect_receipt`/`reflect_nullifiers`), `dregg-query/src/mmr.rs`, `dregg-analyzer/src/receipts.rs`.
**Primitive needed:** L1 only (verifiers are read-only `Gadget`s). **Pure-additive?** Yes.

### L7 — Tokens & Cipherclerk `[needs L1; partially exists]` → shipped: `token_inspector.rs`
**Build:** the macaroon/biscuit/cipherclerk surface (slice 8): `HMAC Chain Replayer` + `Datalog Authorizer Sim` (verifiers), `Token Attenuator`, `Delegation Envelope Builder/Receiver`, the `Wallet` presentation over the already-Live `cipherclerk.rs`, and the `narrowed_authority ⊆ kernel-cap` comparison (`IV`).
**Reuses:** `cipherclerk.rs` (Live — HeldToken/DelegatedToken/AgentCipherclerk), `macaroon/`/`token/` crates, `sdk/src/cipherclerk.rs`.
**Primitive needed:** L1 + L4 (the cap-comparison reuses `is_attenuation`). **Pure-additive?** Yes.

### L8 — Federation & Consensus `[needs L1; entirely new]` → shipped: `federation_inspector.rs`
**Build:** the whole slice-9 surface (~30 types, all `None`): `Blocklace DAG` (Graph), `Finality ladder` (DV), `QuorumCertificate`/`AttestedRoot`/`Checkpoint`/`Beacon` (RF + IV verifiers), `Vouch graph` + `AdmissionRegistry` (G + DV), `EquivocationCourt` docket (PV), the `Quorum Calculator` + `Tau Sim` + `Safety Verifier`.
**Reuses:** `federation/`, `blocklace/`, `coord/`, `node/` crates; the differential tests (`bls_quorum_diff` etc.) as the correctness hooks. Needs a `NodeClient` bridge (the census notes channel/mailbox/court are "behind captp").
**Primitive needed:** L1 + the remote-node bridge (the `RemoteOrgan` → live transition the census flags). **Pure-additive?** Yes, but largest and most independent — a whole new object family. Lower priority only because it's federated (the embedded single-custody world is the daily surface); high standalone value when the N=3 devnet panel lands.

### L9 — Circuit & Commitment Internals `[needs L1; entirely new]` → shipped: `circuit_inspector.rs`
**Build:** slices 7 & 11 internals (~20 types, all `None`): `EffectVmDescriptor2`/`TableDef2`/`VmConstraint2` (table-layout + constraint-dependency presentations), `AirDescriptor` (fingerprint + VK-composition IV), `StateCommitment`/`V9RotationContext`/`CrossCellDelta`/`NoteCommitment`/`NullifierSet`/`HeapRoot`/`CapabilityRoot` (Merkle-tree + conservation-aggregation + anti-ghost verifiers). Read-only/verifier-heavy.
**Reuses:** `circuit/src/descriptor_ir2.rs`/`air_descriptor.rs`/`cap_root.rs`/`heap_root.rs`, `cell/src/commitment.rs`/`note.rs`/`nullifier_set.rs`. Serves the Circuit-Soundness Apex campaign (`project-circuit-soundness-apex`).
**Primitive needed:** L1 + the `MerkleTree`/`Trace` presentation bodies (land in L1). **Pure-additive?** Yes. Specialist surface — the audit/soundness lane, lower daily-UX value but high correctness value.

### L10 — Settlement Families & Factory Authoring `[needs L1, L2, L3]` → shipped: `settlement_inspector.rs`
**Build:** the settlement organ builders (slices 10-settlement, 12-factory): `Escrow/Obligation/Bridge/Channel` deal builders (value→commit), the `FactoryDescriptor Builder` + `CellProgram Builder`/`Case Editor`/`Guard Composer`, the deal `state-machine editor`, `Condition-Commitment Builder`.
**Reuses:** `cell/src/blueprint.rs` (the settlement Lean keystones), `cell/src/factory.rs`, `organ_ops.rs`/`organs.rs` (the trustline/flash-well drivers as the template), `edit.rs` (`FactoryBuilder`/`ProgramBuilder` already exist).
**Primitive needed:** L1 + L2 (constraint composer — settlement terms ARE constraint sets) + L3 (commit spine). **Pure-additive?** Yes, but it composes L2's predicate gadgets and L3's commit gadgets — it's the capstone that fuses the language uplift with the construction spine into "build a verified userspace app," the Refinement-Epoch "not-a-toy apps" goal.

**Lane summary:** L1 is the sole must-land-first framework primitive (the `Presentable`/`Gadget`/`CommittingGadget` traits + seven presentation bodies + Spotter). L2/L3 are the two highest-value additive lanes that depend only on L1 and unlock the rest. L4–L7 are pure-additive deepenings of already-Live surfaces. L8/L9 are independent new object families (federation, circuit) — high standalone value, lower daily-UX priority. L10 is the capstone fusing L2+L3 into verified app authoring. The three first lanes — **L1 (spine), L2 (predicate composer), L3 (effect/turn builder)** — are the critical path: with them landed, every census type has its `RawFields` floor, the richest `None` surface (predicates) becomes legible, and the universal construction gadget is live.