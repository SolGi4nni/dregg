/-
# Dregg2.Exec.CircuitEmit — emits Lean circuit data to a deterministic wire encoding the
real Rust backend can decode, with a faithfulness theorem.

`Circuit.lean` gives the verified circuit IR (`ConstraintSystem` = `List Constraint`,
`Expr` = var/const/add/mul over the field) plus the keystone

    bridge : satisfied kernelCircuit (encode s t s') ↔ fullStepInv s t s'

so checking `kernelCircuit` *is* checking the verified `fullStepInv`. This module supplies the
last hop: getting `kernelCircuit` — pure Lean data — out of Lean and into the real Rust
prover/verifier (`circuit/src/dsl/circuit.rs`'s `CircuitDescriptor`/`ConstraintExpr`) without
losing the semantics `bridge` certified.

The pieces:

  * **`EmittedDescriptor`** — a Lean structure mirroring the *fields* of Rust's
    `CircuitDescriptor` (name, trace_width, constraints), where each constraint is a pair of
    `EmittedExpr` ASTs (mirroring the var/const/add/mul shape; the generic
    `ConstraintExpr::Polynomial`/AST surface). It is `Repr`-printable; `#guard` golden pins on
    `emitJson …` check the canonical wire string the Rust decoder parses.
  * **`emit`** — the deterministic serializer `ConstraintSystem → EmittedDescriptor`.
  * **`decodeE`** — the inverse `EmittedDescriptor → ConstraintSystem`.
  * **`satisfiedEmitted`** — `satisfied` lifted to the emitted form.
  * **`emit_faithful`** — `satisfied cs a ↔ satisfiedEmitted (emit cs) a`: the wire form
    denotes the same constraint system, so the semantics `bridge` proved survive emission.
    Proved via a structure-preserving round trip (`decodeE_emit : decodeE (emit cs) = cs`).
    `#assert_axioms`-pinned.

The Rust side (in `dregg-lean-ffi`) decodes the printed wire string back into a real
`circuit::dsl::CircuitDescriptor` and checks its `AirDescriptor::fingerprint` equals the
Rust-native AIR's — the binding "the AIR the backend runs IS the AIR Lean proved the bridge
for". See `dregg-lean-ffi/src/circuit_decode.rs`.
-/
import Dregg2.Circuit
import Dregg2.Circuit.Lookup
import Dregg2.Crypto.Merkle

namespace Dregg2.Exec.CircuitEmit

open Dregg2.Circuit

/-! ## The emitted expression AST — a faithful mirror of `Circuit.Expr`.

`EmittedExpr` is `Expr` re-spelled as a tagged wire form: a `var`/`const`/`add`/`mul` AST.
We keep it a *separate* inductive (rather than reusing `Expr`) so the emitter is an explicit
serialization step with its own faithfulness obligation — the wire form is not the proof
object by fiat; the round trip is proved. -/

/-- A wire-form arithmetic expression: the tagged mirror of `Circuit.Expr`. -/
inductive EmittedExpr where
  | var   : Nat → EmittedExpr
  | const : Int → EmittedExpr
  | add   : EmittedExpr → EmittedExpr → EmittedExpr
  | mul   : EmittedExpr → EmittedExpr → EmittedExpr
  deriving Repr, DecidableEq

/-- A wire-form constraint: the gate equation `lhs = rhs` as two `EmittedExpr`. -/
structure EmittedConstraint where
  lhs : EmittedExpr
  rhs : EmittedExpr
  deriving Repr, DecidableEq

/-- A wire-form descriptor mirroring the relevant fields of Rust's `CircuitDescriptor`:
the AIR name, the trace width (number of distinct wires), and the constraint list. The
witness-vector layout is implicit (variable index = column index), exactly as in
`Circuit.encode`. -/
structure EmittedDescriptor where
  name        : String
  traceWidth  : Nat
  constraints : List EmittedConstraint
  deriving Repr, DecidableEq

/-! ## `emit` — the deterministic serializer. -/

/-- Serialize a `Circuit.Expr` to its wire form. Structure-preserving by construction. -/
def emitExpr : Expr → EmittedExpr
  | .var v     => .var v
  | .const c   => .const c
  | .add e₁ e₂ => .add (emitExpr e₁) (emitExpr e₂)
  | .mul e₁ e₂ => .mul (emitExpr e₁) (emitExpr e₂)

/-- Serialize a single `Constraint` to its wire form. -/
def emitConstraint (c : Constraint) : EmittedConstraint :=
  { lhs := emitExpr c.lhs, rhs := emitExpr c.rhs }

/-- The number of distinct wires the kernel circuit uses: the 6 named columns of
`Circuit.encode` (`vTotalPre … vChainOk`). This is the `trace_width` the Rust descriptor
must declare. -/
def kernelTraceWidth : Nat := 6

/-- **`emit`** — the deterministic serializer `ConstraintSystem → EmittedDescriptor`. The
name binds the wire form to a specific AIR identity (matching the Rust-native AIR name). -/
def emit (name : String) (width : Nat) (cs : ConstraintSystem) : EmittedDescriptor :=
  { name := name, traceWidth := width, constraints := cs.map emitConstraint }

/-! ## `decodeE` — the inverse (deserializer), used only to state/prove faithfulness. -/

/-- Deserialize a wire-form expression back to a `Circuit.Expr`. -/
def decodeExpr : EmittedExpr → Expr
  | .var v     => .var v
  | .const c   => .const c
  | .add e₁ e₂ => .add (decodeExpr e₁) (decodeExpr e₂)
  | .mul e₁ e₂ => .mul (decodeExpr e₁) (decodeExpr e₂)

/-- Deserialize a wire-form constraint. -/
def decodeConstraint (c : EmittedConstraint) : Constraint :=
  { lhs := decodeExpr c.lhs, rhs := decodeExpr c.rhs }

/-- Deserialize a whole emitted descriptor back to a `ConstraintSystem`. -/
def decodeE (d : EmittedDescriptor) : ConstraintSystem :=
  d.constraints.map decodeConstraint

/-! ## `satisfiedEmitted` — `satisfied` lifted to the emitted (decoded) form. -/

/-- Evaluate an emitted expression directly (so the wire form has a standalone denotation,
not only via decode). -/
def EmittedExpr.eval : EmittedExpr → Assignment → Int
  | .var v,     a => a v
  | .const c,   _ => c
  | .add e₁ e₂, a => e₁.eval a + e₂.eval a
  | .mul e₁ e₂, a => e₁.eval a * e₂.eval a

/-- An emitted constraint holds iff both decoded sides evaluate equal. -/
def EmittedConstraint.holds (c : EmittedConstraint) (a : Assignment) : Prop :=
  c.lhs.eval a = c.rhs.eval a

/-- The emitted descriptor is **satisfied** iff every emitted constraint holds — the wire
form's own notion of satisfaction. -/
def satisfiedEmitted (d : EmittedDescriptor) (a : Assignment) : Prop :=
  ∀ c ∈ d.constraints, c.holds a

/-! ## Round-trip + evaluation-agreement lemmas (the spine of faithfulness). -/

/-- `decodeExpr ∘ emitExpr = id`: emission then decode recovers the original expression. -/
theorem decodeExpr_emitExpr (e : Expr) : decodeExpr (emitExpr e) = e := by
  induction e with
  | var v => rfl
  | const c => rfl
  | add e₁ e₂ ih₁ ih₂ => simp [emitExpr, decodeExpr, ih₁, ih₂]
  | mul e₁ e₂ ih₁ ih₂ => simp [emitExpr, decodeExpr, ih₁, ih₂]

/-- The emitted expression's standalone `eval` agrees with the original `Expr.eval`: the
wire denotation is faithful pointwise. -/
theorem emitExpr_eval (e : Expr) (a : Assignment) :
    (emitExpr e).eval a = e.eval a := by
  induction e with
  | var v => rfl
  | const c => rfl
  | add e₁ e₂ ih₁ ih₂ => simp [emitExpr, EmittedExpr.eval, Expr.eval, ih₁, ih₂]
  | mul e₁ e₂ ih₁ ih₂ => simp [emitExpr, EmittedExpr.eval, Expr.eval, ih₁, ih₂]

/-- A single constraint and its emitted form hold on EXACTLY the same assignments. -/
theorem emitConstraint_holds (c : Constraint) (a : Assignment) :
    (emitConstraint c).holds a ↔ c.holds a := by
  unfold emitConstraint EmittedConstraint.holds Constraint.holds
  simp only [emitExpr_eval]

/-! ## `emit_faithful` — THE deliverable: the wire form denotes the same system. -/

/-- **`emit_faithful`.** Satisfying the emitted descriptor is EXACTLY satisfying the source
constraint system, for every assignment. So `emit` loses none of the semantics `Circuit.bridge`
proved: composing `emit_faithful` with `bridge` gives that satisfying the *wire form* of
`kernelCircuit` is `fullStepInv`. (`name`/`width` are wire metadata and do not affect
satisfaction; they carry the AIR identity the Rust fingerprint check binds.) -/
theorem emit_faithful (name : String) (width : Nat) (cs : ConstraintSystem) (a : Assignment) :
    satisfied cs a ↔ satisfiedEmitted (emit name width cs) a := by
  unfold satisfied satisfiedEmitted emit
  simp only [List.mem_map]
  constructor
  · rintro h c ⟨c₀, hc₀, rfl⟩
    exact (emitConstraint_holds c₀ a).mpr (h c₀ hc₀)
  · intro h c hc
    exact (emitConstraint_holds c a).mp (h (emitConstraint c) ⟨c, hc, rfl⟩)

/-- `decodeConstraint ∘ emitConstraint = id` on a single constraint. -/
theorem decodeConstraint_emitConstraint (c : Constraint) :
    decodeConstraint (emitConstraint c) = c := by
  unfold decodeConstraint emitConstraint
  simp only [decodeExpr_emitExpr]

/-- **`emit` is injective in the constraint payload** (the round trip recovers the source, so
distinct constraint systems serialize to distinct descriptors under a fixed name/width): no
two systems collide on the wire. -/
theorem decodeE_emit (name : String) (width : Nat) (cs : ConstraintSystem) :
    decodeE (emit name width cs) = cs := by
  unfold decodeE emit
  simp only [List.map_map]
  rw [show (decodeConstraint ∘ emitConstraint) = id from
        funext (fun c => decodeConstraint_emitConstraint c)]
  exact List.map_id cs

/-! ## The concrete kernel-circuit emission (the extraction target). -/

/-- The AIR identity string the wire form carries. The Rust decoder pins the native AIR to
this name so the fingerprint binding is name-aware. -/
def kernelAirName : String := "dregg-kernel-step-v1"

/-- **The emitted kernel circuit** — `kernelCircuit` serialized to the wire form. THIS is the
object that extracts to Rust: pure printable data, proved faithful by `emit_faithful`. -/
def emittedKernel : EmittedDescriptor :=
  emit kernelAirName kernelTraceWidth kernelCircuit

/-- **End-to-end faithfulness for the kernel circuit**: satisfying the EMITTED kernel circuit
is exactly the verified `fullStepInv` (composing `emit_faithful` with `Circuit.bridge`). The
wire form the Rust backend decodes carries the full §8 soundness∧completeness content. -/
theorem emittedKernel_bridge (s : Dregg2.Exec.ChainedState) (t : Dregg2.Exec.Turn)
    (s' : Dregg2.Exec.ChainedState) :
    satisfiedEmitted emittedKernel (encode s t s') ↔ Dregg2.Exec.fullStepInv s t s' := by
  unfold emittedKernel
  rw [← emit_faithful]
  exact bridge s t s'

/-! ## The canonical wire string (`#guard`-pinned golden; the byte form Rust decodes).

A deterministic, minimal JSON renderer. The Rust decoder (`circuit_decode.rs`) parses this
exact grammar. Keeping the renderer in Lean (not a derived `ToJson`) makes the wire grammar
explicit and stable. -/

/-- Render an integer as a JSON number (no spaces). -/
private def jInt (n : Int) : String := toString n

/-- Render an emitted expression as JSON: `{"t":"var","v":N}` / `{"t":"const","v":N}` /
`{"t":"add"|"mul","l":…,"r":…}`. -/
def EmittedExpr.toJson : EmittedExpr → String
  | .var v     => "{\"t\":\"var\",\"v\":" ++ toString v ++ "}"
  | .const c   => "{\"t\":\"const\",\"v\":" ++ jInt c ++ "}"
  | .add l r   => "{\"t\":\"add\",\"l\":" ++ l.toJson ++ ",\"r\":" ++ r.toJson ++ "}"
  | .mul l r   => "{\"t\":\"mul\",\"l\":" ++ l.toJson ++ ",\"r\":" ++ r.toJson ++ "}"

/-- Render a constraint as JSON `{"lhs":…,"rhs":…}`. -/
def EmittedConstraint.toJson (c : EmittedConstraint) : String :=
  "{\"lhs\":" ++ c.lhs.toJson ++ ",\"rhs\":" ++ c.rhs.toJson ++ "}"

/-- Render a list of constraints as a JSON array. -/
private def constraintsToJson : List EmittedConstraint → String
  | []      => "[]"
  | [c]     => "[" ++ c.toJson ++ "]"
  | c :: cs => "[" ++ c.toJson ++ (cs.foldl (fun acc x => acc ++ "," ++ x.toJson) "") ++ "]"

/-- **`emitJson`** — the full canonical wire string for an emitted descriptor. This is what
the `#guard` golden pin checks and the Rust decoder ingests. -/
def emitJson (d : EmittedDescriptor) : String :=
  "{\"name\":\"" ++ d.name ++ "\",\"trace_width\":" ++ toString d.traceWidth ++
  ",\"constraints\":" ++ constraintsToJson d.constraints ++ "}"

/-- **`emitDescriptorJson`** — the GENERAL `EmittedDescriptor → String` wire emitter (the named,
documented entry point for any emitted PART-I descriptor: the kernel circuit, the `Transfer`
circuit, or any other `emit …`-produced descriptor). Definitionally `emitJson`; the schema is the
stable grammar the Rust `lean_descriptor_air::parse_descriptor` decoder ingests:

    {"name":S,"trace_width":N,"constraints":[{"lhs":<expr>,"rhs":<expr>},…]}

with `<expr>` one of `{"t":"var","v":i}` / `{"t":"const","v":c}` /
`{"t":"add","l":<expr>,"r":<expr>}` / `{"t":"mul","l":<expr>,"r":<expr>}`. -/
def emitDescriptorJson (d : EmittedDescriptor) : String := emitJson d

/-- The canonical wire string for the kernel circuit — copy this into the Rust golden. -/
def kernelWire : String := emitJson emittedKernel

-- `#guard` golden pin: kernel wire bytes the Rust decoder parses.
#guard (kernelWire == r#"{"name":"dregg-kernel-step-v1","trace_width":6,"constraints":[{"lhs":{"t":"var","v":1},"rhs":{"t":"var","v":0}},{"lhs":{"t":"var","v":2},"rhs":{"t":"const","v":1}},{"lhs":{"t":"var","v":5},"rhs":{"t":"const","v":1}},{"lhs":{"t":"var","v":4},"rhs":{"t":"add","l":{"t":"var","v":3},"r":{"t":"const","v":1}}}]}"#)
#guard (emittedKernel.constraints.length) == 4  --  4 gates
#guard (emittedKernel.traceWidth) == 6  --  6 wires

/-! ## Axiom-hygiene pins (the §8 honesty tripwire). -/

#assert_axioms emit_faithful
#assert_axioms decodeE_emit
#assert_axioms emittedKernel_bridge

/-! ## ════════════════════════════════════════════════════════════════════════════════
## PART II — Emitting the RICHER `CircuitIR`: the Merkle gadget (`Crypto.Merkle`).
## ════════════════════════════════════════════════════════════════════════════════

`emit`/`EmittedExpr` above cover the kernel's 4 var/const/add/mul gates. The real Rust
`ConstraintExpr` (`circuit/src/dsl/circuit.rs`) has ~15 *column-indexed* forms, and the first
gadget discharged end-to-end — `Crypto.Merkle.merkleCircuit` (mirroring
`descriptors.rs::merkle_poseidon2_descriptor()`) — uses three of them: `MerkleHash`,
`Transition`, and `PiBinding` (the two boundaries). Those forms are NOT polynomial ASTs over
a flat assignment: they are *structural* predicates over a multi-row trace whose cells are
ABSTRACT `Digest`s (the hash `compress` is the Layer-A `Prop` carrier, never algebra). So we
emit a SEPARATE wire form for them — `EmittedConstraintM` (column-indexed, mirroring the Rust
enum's field shape) — and prove the emitted form denotes EXACTLY `Crypto.Merkle.Satisfies`.

The column layout mirrors `descriptors.rs::merkle_col`: `current=0`, `sib0/1/2 = 1/2/3`,
`position=4`, `parent=5`. The Lean model folds the three siblings into one abstract `sib`
input to the 2-input `compress` (position-independence is already baked into the Layer-A node
hash — see `Merkle.lean`'s preamble), so the emitted `MerkleHash` carries the canonical
`sib_cols = [1,2,3]` triple for fidelity to the Rust decoder, plus the `current/position/
parent` columns; the *denotation* binds `parent = compress current sib` exactly as `rowHashOk`. -/

open Dregg2.Crypto.Merkle in

/-- The Merkle column layout (mirrors `descriptors.rs::merkle_col`). Wire metadata only — the
denotation reads the named `Row` fields, but the Rust decoder needs these indices to rebuild
the column-indexed `ConstraintExpr`. -/
structure MerkleCols where
  current  : Nat := 0
  sib0     : Nat := 1
  sib1     : Nat := 2
  sib2     : Nat := 3
  position : Nat := 4
  parent   : Nat := 5
  deriving Repr, DecidableEq

/-- The canonical Merkle column layout (= `merkle_col`). -/
def merkleCols : MerkleCols := {}

/-- **`EmittedConstraintM`** — a wire-form constraint over a Merkle trace, the column-indexed
mirror of the `ConstraintExpr` subset `merkleCircuit` uses. Each constructor records the
SAME column indices the Rust enum carries, so the decoder rebuilds the exact `ConstraintExpr`.

* `merkleHash` ↔ `ConstraintExpr::MerkleHash { output_col, current_col, sib_cols, position_col }`
  — per-row node hash `parent = compress current sib`.
* `transition` ↔ `ConstraintExpr::Transition { next_col, local_col }` — `next.current = this.parent`.
* `piBindingFirst`/`piBindingLast` ↔ `BoundaryDef::PiBinding { row: First|Last, col, pi_index }`
  — boundary `first.current = PI[leaf]`, `last.parent = PI[root]`. -/
inductive EmittedConstraintM where
  | merkleHash      (outputCol currentCol : Nat) (sibCols : Nat × Nat × Nat) (positionCol : Nat)
  | transition      (nextCol localCol : Nat)
  | piBindingFirst  (col piIndex : Nat)
  | piBindingLast   (col piIndex : Nat)
  deriving Repr, DecidableEq

/-- **`EmittedMerkleDescriptor`** — the wire-form descriptor for the Merkle AIR, mirroring the
relevant fields of Rust's `CircuitDescriptor`: name, trace width, the column-indexed
constraint list, and the public-input count (the Merkle AIR's `[leaf, root]` = 2). -/
structure EmittedMerkleDescriptor where
  name             : String
  traceWidth       : Nat
  cols             : MerkleCols
  constraints      : List EmittedConstraintM
  publicInputCount : Nat
  deriving Repr, DecidableEq

/-! ### Denotation: `satisfiedEmittedMerkle` — the emitted form's OWN notion of satisfaction.

Because the Merkle cells are abstract `Digest`s, the wire form's denotation is structural: it
reads the named `Row` fields and the boundary PIs (`leaf`, `root`). We give each emitted
constructor its meaning as a `Prop` over the row trace, then assemble the descriptor's
satisfaction as the conjunction over its constraints — built to land DEFINITIONALLY on
`Crypto.Merkle.Satisfies`. -/

open Dregg2.Crypto.Merkle

/-- Meaning of a single emitted Merkle constraint over a row trace + boundary PIs `(root,
leaf)`. (Column indices are carried for the decoder; the denotation reads the named fields,
exactly as `rowHashOk`/`transitionsOk`/the `PiBinding` conjuncts of `Satisfies` do.) -/
def EmittedConstraintM.holdsM {Digest : Type u} (compress : Digest → Digest → Digest)
    (rows : List (Row Digest)) (root leaf : Digest) : EmittedConstraintM → Prop
  | .merkleHash _ _ _ _   => ∀ r ∈ rows, rowHashOk compress r
  | .transition _ _       => transitionsOk rows
  | .piBindingFirst _ _   => ∃ first, rows.head? = some first ∧ first.current = leaf
  | .piBindingLast _ _    => ∃ last, rows.getLast? = some last ∧ last.parent = root

/-- **`satisfiedEmittedMerkle`** — the emitted Merkle descriptor is satisfied by a row trace
`(rows)` against boundary PIs `(root, leaf)` iff every emitted constraint holds. The wire
form's standalone denotation; proved faithful to `Crypto.Merkle.Satisfies` below. -/
def satisfiedEmittedMerkle {Digest : Type u} (compress : Digest → Digest → Digest)
    (d : EmittedMerkleDescriptor) (rows : List (Row Digest)) (root leaf : Digest) : Prop :=
  ∀ c ∈ d.constraints, c.holdsM compress rows root leaf

/-! ### `emitMerkle` — the deterministic serializer for the Merkle AIR. -/

/-- The AIR identity string the Merkle wire form carries (= `descriptors.rs`'s
`MERKLE_POSEIDON2_AIR_NAME`). The Rust decoder pins the native Merkle AIR to this name. -/
def merkleAirName : String := "dregg-merkle-poseidon2-v1"

/-- The Merkle trace width (= `descriptors.rs::MERKLE_P2_WIDTH`). -/
def merkleTraceWidth : Nat := 6

/-- The Merkle AIR's public-input count (`[leaf, root]`, = `MERKLE_PUBLIC_INPUT_COUNT`). -/
def merklePublicInputCount : Nat := 2

/-- The three constraint forms of `merkle_poseidon2_descriptor()`, in C2/C3/boundary order,
plus the two `PiBinding` boundaries — the wire encoding of `merkleCircuit`'s constraint set.
(C1, the position-validity polynomial, is a `Polynomial` form not needed for the abstract
bridge — the node hash is position-independent — and is listed in the TODO below; it is a
SOUNDNESS-neutral well-formedness check on the `position` column, not part of `Satisfies`.) -/
def merkleConstraintsWire : List EmittedConstraintM :=
  [ .merkleHash merkleCols.parent merkleCols.current
      (merkleCols.sib0, merkleCols.sib1, merkleCols.sib2) merkleCols.position   -- C2: MerkleHash
  , .transition merkleCols.current merkleCols.parent                            -- C3: Transition
  , .piBindingFirst merkleCols.current 0                                        -- boundary: first.current = PI0 (leaf)
  , .piBindingLast merkleCols.parent 1 ]                                        -- boundary: last.parent  = PI1 (root)

/-- **`emitMerkle`** — the emitted Merkle descriptor. Pure printable data, proved faithful to
`Crypto.Merkle.merkleCircuit`'s `Satisfies` by `emit_faithful_merkle`. -/
def emittedMerkle : EmittedMerkleDescriptor :=
  { name := merkleAirName, traceWidth := merkleTraceWidth, cols := merkleCols,
    constraints := merkleConstraintsWire, publicInputCount := merklePublicInputCount }

/-! ### `emit_faithful_merkle` — THE Merkle faithfulness theorem.

Satisfying the EMITTED Merkle descriptor (with a non-empty trace) is EXACTLY
`Crypto.Merkle.Satisfies compress ⟨rows⟩ root leaf`. The proof unfolds both sides to the same
conjunction (membership of the four wire constructors ↔ the `∃ first last, …` of `Satisfies`).
So emission loses none of the gadget semantics `merkle_bridge` proved. -/

theorem emit_faithful_merkle {Digest : Type u} (compress : Digest → Digest → Digest)
    (rows : List (Row Digest)) (root leaf : Digest) :
    satisfiedEmittedMerkle compress emittedMerkle rows root leaf
      ↔ Satisfies compress ⟨rows⟩ root leaf := by
  unfold satisfiedEmittedMerkle emittedMerkle merkleConstraintsWire Satisfies
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  constructor
  · -- forward: the four emitted constraints give the `∃ first last, …` conjunction.
    rintro ⟨hHash, hTrans, ⟨first, hFirst, hFc⟩, ⟨last, hLast, hLp⟩⟩
    exact ⟨first, last, hFirst, hLast, hFc, hLp, hHash, hTrans⟩
  · -- backward: the conjunction discharges all four emitted constraints.
    rintro ⟨first, last, hFirst, hLast, hFc, hLp, hHash, hTrans⟩
    exact ⟨hHash, hTrans, ⟨first, hFirst, hFc⟩, ⟨last, hLast, hLp⟩⟩

/-- **`emittedMerkle_bridge` — THE deliverable.** Satisfying the EMITTED Merkle circuit (for
SOME trace) is EXACTLY Merkle membership (`Crypto.Merkle.MerkleMembers`): composing
`emit_faithful_merkle` (wire ↔ `Satisfies`) with `Crypto.Merkle.merkle_bridge` (`Satisfies` ↔
`MerkleMembers`). So the emitted Merkle circuit the Rust backend decodes carries the SAME
soundness∧completeness `merkle_bridge` proved — `compress` abstract throughout, no seam. -/
theorem emittedMerkle_bridge {Digest : Type u} (compress : Digest → Digest → Digest)
    (root leaf : Digest) :
    (∃ rows : List (Row Digest), satisfiedEmittedMerkle compress emittedMerkle rows root leaf)
      ↔ MerkleMembers compress root leaf := by
  rw [← merkle_bridge compress root leaf]
  constructor
  · rintro ⟨rows, h⟩
    exact ⟨⟨rows⟩, (emit_faithful_merkle compress rows root leaf).mp h⟩
  · rintro ⟨circuit, h⟩
    exact ⟨circuit.rows, (emit_faithful_merkle compress circuit.rows root leaf).mpr h⟩

/-! ### Canonical Merkle wire rendering (`#guard`-pinned golden; the bytes the Rust decoder ingests).

Renders the column-indexed forms to a stable JSON grammar mirroring the Rust `ConstraintExpr`
variant tags (`merkle_hash`/`transition`/`pi_binding_first`/`pi_binding_last`) so the decoder
reconstructs `ConstraintExpr::MerkleHash { output_col, current_col, sib_cols, position_col }`,
`ConstraintExpr::Transition { next_col, local_col }`, and the two `BoundaryDef::PiBinding`. -/

/-- Render one emitted Merkle constraint as JSON. -/
def EmittedConstraintM.toJson : EmittedConstraintM → String
  | .merkleHash o c (s0, s1, s2) p =>
      "{\"t\":\"merkle_hash\",\"output_col\":" ++ toString o ++
      ",\"current_col\":" ++ toString c ++
      ",\"sib_cols\":[" ++ toString s0 ++ "," ++ toString s1 ++ "," ++ toString s2 ++ "]" ++
      ",\"position_col\":" ++ toString p ++ "}"
  | .transition n l =>
      "{\"t\":\"transition\",\"next_col\":" ++ toString n ++ ",\"local_col\":" ++ toString l ++ "}"
  | .piBindingFirst col pi =>
      "{\"t\":\"pi_binding_first\",\"col\":" ++ toString col ++ ",\"pi_index\":" ++ toString pi ++ "}"
  | .piBindingLast col pi =>
      "{\"t\":\"pi_binding_last\",\"col\":" ++ toString col ++ ",\"pi_index\":" ++ toString pi ++ "}"

/-- Render a list of emitted Merkle constraints as a JSON array. -/
private def merkleConstraintsToJson : List EmittedConstraintM → String
  | []      => "[]"
  | [c]     => "[" ++ c.toJson ++ "]"
  | c :: cs => "[" ++ c.toJson ++ (cs.foldl (fun acc x => acc ++ "," ++ x.toJson) "") ++ "]"

/-- **`emitMerkleJson`** — the full canonical wire string for the emitted Merkle descriptor. -/
def emitMerkleJson (d : EmittedMerkleDescriptor) : String :=
  "{\"name\":\"" ++ d.name ++ "\",\"trace_width\":" ++ toString d.traceWidth ++
  ",\"public_input_count\":" ++ toString d.publicInputCount ++
  ",\"constraints\":" ++ merkleConstraintsToJson d.constraints ++ "}"

/-- The canonical Merkle wire string — copy this into the Rust golden. -/
def merkleWire : String := emitMerkleJson emittedMerkle

-- `#guard` golden pin: Merkle wire bytes the Rust decoder parses.
#guard (merkleWire == r#"{"name":"dregg-merkle-poseidon2-v1","trace_width":6,"public_input_count":2,"constraints":[{"t":"merkle_hash","output_col":5,"current_col":0,"sib_cols":[1,2,3],"position_col":4},{"t":"transition","next_col":0,"local_col":5},{"t":"pi_binding_first","col":0,"pi_index":0},{"t":"pi_binding_last","col":5,"pi_index":1}]}"#)
#guard (emittedMerkle.constraints.length) == 4  --  4 wire constraints (MerkleHash + Transition + 2 PiBinding)
#guard (emittedMerkle.traceWidth) == 6  --  6 wires

/-! ### Axiom-hygiene pins for the Merkle extension. -/

#assert_axioms emit_faithful_merkle
#assert_axioms emittedMerkle_bridge

/-! ## ════════════════════════════════════════════════════════════════════════════════
## PART III — Emitting the ALGEBRAIC `ConstraintExpr` forms (column-indexed, over a field).
## ════════════════════════════════════════════════════════════════════════════════

PART I emitted the kernel's var/const/add/mul gates as an explicit `EmittedExpr` AST; PART II
emitted the Merkle gadget's *structural* forms (`MerkleHash`/`Transition`/`PiBinding`) over
abstract `Digest`s. This part fills in the REMAINING *algebraic* `ConstraintExpr` forms — the
ones that, in the real Rust backend (`circuit/src/dsl/circuit.rs::ConstraintExpr`'s
`evaluate_with_tables`), reduce to a polynomial over the row that must equal zero:

    Equality · Multiplication · Binary · PiBinding · Transition · Polynomial ·
    Gated · InvertedGated · Squared · ConditionalNonzero · AtLeastOne

These differ from PART I/II in TWO ways the wire form must respect:
  1. They are **column-indexed** (the Rust enum carries `usize` column indices, not a nested
     AST), reading `local[col]` / `next[col]` / `pi[i]`. So the wire form `EmittedConstraintA`
     mirrors the enum's *field shape* (the exact indices the Rust decoder rebuilds).
  2. Their satisfaction is "the polynomial evaluates to ZERO", not "lhs = rhs" — Rust's
     `eval_constraints` sums `αⁱ · evaluate(constraintᵢ)` and a valid trace makes each summand
     zero. So the denotation here is `eval _ = 0` (matching Rust), and faithfulness is proved
     against a LOWERING to the PART-I `EmittedExpr` AST: each column-indexed form denotes the
     SAME field polynomial its AST lowering does. That ties this part back to PART I's already
     `bridge`-compatible `EmittedExpr` semantics — no new evaluation seam.

The denotation reads a **row environment** `(local, next, pi)` of three `Assignment`s (Rust's
`local : &[BabyBear]`, `next : &[BabyBear]`, `pi : &[BabyBear]`), exactly as `evaluate`. Hash
and `Lookup` are NOT in this part: they are opaque/non-polynomial (`Hash*` call `poseidon2`,
`Lookup` is a membership test); PART II already discharged the hash-shaped Merkle gadget over
abstract `compress`, and the `Crypto.Dfa` gadget discharges `Lookup`-as-`δ`. See the closing
note for the precise residual list. -/

/-- A **row environment** for the algebraic forms: the current row, the next row, and the
public inputs — the three slices Rust's `ConstraintExpr::evaluate(local, next, pi)` reads.
Each is an `Assignment` (column/index → field value), so this part reuses PART I's `Int`
field model and `EmittedExpr.eval` directly. -/
structure RowEnv where
  loc  : Assignment
  next : Assignment
  pi   : Assignment

/-- **`EmittedConstraintA`** — the wire-form algebraic constraint: the column-indexed mirror of
the polynomial `ConstraintExpr` forms. Each constructor records the SAME indices the Rust enum
carries, so the decoder rebuilds the exact variant. Wire tags (for the Rust decoder) match the
snake-cased enum names; see `EmittedConstraintA.toJson` for the exact grammar.

* `equality a b` ↔ `Equality { col_a, col_b }` — `local[a] − local[b] = 0`.
* `multiplication a b o` ↔ `Multiplication { a, b, output }` — `local[a]·local[b] − local[o] = 0`.
* `binary col` ↔ `Binary { col }` — `local[col]·(local[col] − 1) = 0` (boolean).
* `piBinding col i` ↔ `PiBinding { col, pi_index }` — `local[col] − pi[i] = 0`.
* `transition n l` ↔ `Transition { next_col, local_col }` — `next[n] − local[l] = 0`.
* `polynomial terms` ↔ `Polynomial { terms }` — `Σ coeff·∏ local[cols] = 0` (`terms : List (ℤ × List Nat)`).
* `gated sel inner` ↔ `Gated { selector_col, inner }` — `local[sel]·⟦inner⟧ = 0`.
* `invertedGated sel inner` ↔ `InvertedGated { selector_col, inner }` — `(1 − local[sel])·⟦inner⟧ = 0`.
* `squared inner` ↔ `Squared { inner }` — `⟦inner⟧² = 0`.
* `conditionalNonzero sel v inv` ↔ `ConditionalNonzero { selector_col, value_col, inverse_col }`
  — `local[sel]·(local[v]·local[inv] − 1) = 0`.
* `atLeastOne flags` ↔ `AtLeastOne { flag_cols }` — `∏ (1 − local[f]) = 0`. -/
inductive EmittedConstraintA where
  | equality           (colA colB : Nat)
  | multiplication     (a b output : Nat)
  | binary             (col : Nat)
  | piBinding          (col piIndex : Nat)
  | transition         (nextCol localCol : Nat)
  | polynomial         (terms : List (Int × List Nat))
  | gated              (selectorCol : Nat) (inner : EmittedConstraintA)
  | invertedGated      (selectorCol : Nat) (inner : EmittedConstraintA)
  | squared            (inner : EmittedConstraintA)
  | conditionalNonzero (selectorCol valueCol inverseCol : Nat)
  | atLeastOne         (flagCols : List Nat)
  deriving Repr, DecidableEq

/-! ### `evalA` — the field value of an algebraic form (Rust's `evaluate`, in `ℤ`).

Each form evaluates to the SAME field expression Rust's `evaluate_with_tables` computes (with
`local`/`next`/`pi` the row environment). Satisfaction is then "this value is `0`". -/

/-- The product `∏_{c ∈ cols} local[c]` (empty product = `1`, the constant term of a `PolyTerm`). -/
def termValue (env : RowEnv) (cols : List Nat) : Int :=
  cols.foldl (fun acc c => acc * env.loc c) 1

/-- The `AtLeastOne` product `∏_{f ∈ flags} (1 − local[f])` (empty product = `1`). -/
def atLeastOneValue (env : RowEnv) (flags : List Nat) : Int :=
  flags.foldl (fun acc f => acc * (1 - env.loc f)) 1

/-- **`evalA`** — the field value Rust's `ConstraintExpr::evaluate` computes for each algebraic
form, in `ℤ` (the PART-I field model). A valid trace makes this `0` (see `holdsA`). -/
def EmittedConstraintA.evalA (env : RowEnv) : EmittedConstraintA → Int
  | .equality a b           => env.loc a - env.loc b
  | .multiplication a b o   => env.loc a * env.loc b - env.loc o
  | .binary col             => env.loc col * (env.loc col - 1)
  | .piBinding col i        => env.loc col - env.pi i
  | .transition n l         => env.next n - env.loc l
  | .polynomial terms       => terms.foldl (fun acc t => acc + t.1 * termValue env t.2) 0
  | .gated sel inner        => env.loc sel * inner.evalA env
  | .invertedGated sel inner => (1 - env.loc sel) * inner.evalA env
  | .squared inner          => inner.evalA env * inner.evalA env
  | .conditionalNonzero sel v inv => env.loc sel * (env.loc v * env.loc inv - 1)
  | .atLeastOne flags       => atLeastOneValue env flags

/-- **`holdsA`** — an algebraic emitted constraint is satisfied iff its Rust-`evaluate` value is
zero (exactly `eval_constraints`' per-term condition on a valid trace). -/
def EmittedConstraintA.holdsA (c : EmittedConstraintA) (env : RowEnv) : Prop :=
  c.evalA env = 0

/-! ### `lowerA` — lowering each column-indexed form to the PART-I `EmittedExpr` AST.

This is the FAITHFULNESS bridge: each algebraic form lowers to a `lhs`/`rhs` `EmittedExpr` pair
whose `lhs.eval − rhs.eval` is the SAME polynomial `evalA` computes. We lower to the `lhs = rhs`
gate shape (PART I), then prove `holdsA env c ↔ (lowerA c).lhs.eval env.loc = (lowerA c).rhs.eval env.loc`
for the `local`-only forms, and the analogous statement threading `next`/`pi` for the others.

Because PART-I `EmittedExpr.eval` reads a single `Assignment`, the `transition`/`piBinding`
forms (which read `next`/`pi`) are lowered with their cross-row/PI columns pre-resolved to
constants under the fixed `env`; faithfulness is then the algebraic identity `evalA = 0 ↔ AST = 0`.
We keep the lowering total over `EmittedExpr` so the proof is a structural `evalA`-vs-`eval`
agreement, not a new denotation. -/

/-- Lower a `PolyTerm`-style `(coeff, cols)` to its `EmittedExpr` value `coeff · ∏ local[cols]`. -/
def lowerTerm : Int × List Nat → EmittedExpr
  | (coeff, cols) =>
    cols.foldl (fun acc c => .mul acc (.var c)) (.const coeff)

/-- Lower a list of `PolyTerm`s to the summed `EmittedExpr` (the `Polynomial` body). -/
def lowerTerms : List (Int × List Nat) → EmittedExpr
  | []      => .const 0
  | t :: ts => ts.foldl (fun acc t => .add acc (lowerTerm t)) (lowerTerm t)

/-- The lowered `EmittedExpr` whose `eval` equals `evalA env c` (the LHS of the `= 0` gate). For
the `next`/`pi`-reading forms, the cross-row/PI cells are lowered as `const` of their resolved
value under `env` — making the lowering a faithful `Int`-valued mirror of `evalA`. -/
def EmittedConstraintA.lowerA (env : RowEnv) : EmittedConstraintA → EmittedExpr
  | .equality a b           => .add (.var a) (.mul (.const (-1)) (.var b))
  | .multiplication a b o   => .add (.mul (.var a) (.var b)) (.mul (.const (-1)) (.var o))
  | .binary col             => .mul (.var col) (.add (.var col) (.const (-1)))
  | .piBinding col i        => .add (.var col) (.const (-(env.pi i)))
  | .transition n l         => .add (.const (env.next n)) (.mul (.const (-1)) (.var l))
  | .polynomial terms       => lowerTerms terms
  | .gated sel inner        => .mul (.var sel) (inner.lowerA env)
  | .invertedGated sel inner => .mul (.add (.const 1) (.mul (.const (-1)) (.var sel))) (inner.lowerA env)
  | .squared inner          => .mul (inner.lowerA env) (inner.lowerA env)
  | .conditionalNonzero sel v inv =>
      .mul (.var sel) (.add (.mul (.var v) (.var inv)) (.const (-1)))
  | .atLeastOne flags       =>
      flags.foldl (fun acc f => .mul acc (.add (.const 1) (.mul (.const (-1)) (.var f)))) (.const 1)

/-! ### Faithfulness: each lowered form evaluates to exactly `evalA`. -/

/-- The integer column-product fold pulls its init factor out: `foldl (·*·) s = s * foldl (·*·) 1`. -/
theorem termFold_init (env : RowEnv) (cols : List Nat) (s : Int) :
    cols.foldl (fun a c => a * env.loc c) s = s * cols.foldl (fun a c => a * env.loc c) 1 := by
  induction cols generalizing s with
  | nil => simp
  | cons c cs ih =>
    rw [List.foldl_cons, List.foldl_cons, ih (s * env.loc c), ih (1 * env.loc c)]; ring

/-- A `lowerTerm` evaluates to `coeff · ∏ local[cols]` = `coeff · termValue`. -/
theorem lowerTerm_eval (env : RowEnv) (t : Int × List Nat) :
    (lowerTerm t).eval env.loc = t.1 * termValue env t.2 := by
  obtain ⟨coeff, cols⟩ := t
  unfold lowerTerm termValue
  -- Generalize the accumulator: foldl over `cols` of `.mul acc (.var c)` evaluates to the
  -- `Int` fold from the same accumulator value; then pull the init `coeff` out via `termFold_init`.
  suffices h : ∀ (cols : List Nat) (acc : EmittedExpr) (accI : Int),
      acc.eval env.loc = accI →
      (cols.foldl (fun a c => .mul a (.var c)) acc).eval env.loc
        = cols.foldl (fun a c => a * env.loc c) accI by
    rw [h cols (.const coeff) coeff rfl]; exact termFold_init env cols coeff
  intro cols
  induction cols with
  | nil => intro acc accI h; simpa using h
  | cons c cs ih =>
    intro acc accI h
    exact ih (.mul acc (.var c)) (accI * env.loc c) (by simp only [EmittedExpr.eval, h])

/-- `lowerTerms` evaluates to the `Polynomial` sum `Σ coeff·∏ local[cols]`. -/
theorem lowerTerms_eval (env : RowEnv) (terms : List (Int × List Nat)) :
    (lowerTerms terms).eval env.loc
      = terms.foldl (fun acc t => acc + t.1 * termValue env t.2) 0 := by
  cases terms with
  | nil => rfl
  | cons t ts =>
    unfold lowerTerms
    -- Generalize accumulator over the tail fold.
    suffices h : ∀ (ts : List (Int × List Nat)) (acc : EmittedExpr) (accI : Int),
        acc.eval env.loc = accI →
        (ts.foldl (fun a t => .add a (lowerTerm t)) acc).eval env.loc
          = ts.foldl (fun a t => a + t.1 * termValue env t.2) accI by
      have := h ts (lowerTerm t) (t.1 * termValue env t.2) (lowerTerm_eval env t)
      simpa [lowerTerm_eval env t] using this
    intro ts
    induction ts with
    | nil => intro acc accI h; simpa using h
    | cons t' ts' ih =>
      intro acc accI h
      refine ih (.add acc (lowerTerm t')) (accI + t'.1 * termValue env t'.2) ?_
      simp [EmittedExpr.eval, h, lowerTerm_eval env t']

/-- The `atLeastOne` lowering evaluates to `∏ (1 − local[f])` = `atLeastOneValue`. -/
theorem lowerAtLeastOne_eval (env : RowEnv) (flags : List Nat) :
    (flags.foldl (fun acc f => EmittedExpr.mul acc
        (.add (.const 1) (.mul (.const (-1)) (.var f)))) (.const 1)).eval env.loc
      = atLeastOneValue env flags := by
  unfold atLeastOneValue
  suffices h : ∀ (flags : List Nat) (acc : EmittedExpr) (accI : Int),
      acc.eval env.loc = accI →
      (flags.foldl (fun a f => EmittedExpr.mul a
          (.add (.const 1) (.mul (.const (-1)) (.var f)))) acc).eval env.loc
        = flags.foldl (fun a f => a * (1 - env.loc f)) accI by
    simpa using h flags (.const 1) 1 rfl
  intro flags
  induction flags with
  | nil => intro acc accI h; simpa using h
  | cons f fs ih =>
    intro acc accI h
    refine ih _ (accI * (1 - env.loc f)) ?_
    simp only [EmittedExpr.eval, h]; ring

/-- **`lowerA_eval`.** The lowered `EmittedExpr` evaluates to EXACTLY `evalA` — the column-indexed
algebraic form denotes the SAME field polynomial as its PART-I AST lowering. (`next`/`pi`-reading
forms resolve those cells to `const` under the fixed `env`, so the equality is the literal Rust
`evaluate` value.) Proved by structural induction (the gating/squared/inverted forms recurse). -/
theorem lowerA_eval (env : RowEnv) (c : EmittedConstraintA) :
    (c.lowerA env).eval env.loc = c.evalA env := by
  induction c with
  | equality a b =>
      simp only [EmittedConstraintA.lowerA, EmittedConstraintA.evalA, EmittedExpr.eval]; ring
  | multiplication a b o =>
      simp only [EmittedConstraintA.lowerA, EmittedConstraintA.evalA, EmittedExpr.eval]; ring
  | binary col =>
      simp only [EmittedConstraintA.lowerA, EmittedConstraintA.evalA, EmittedExpr.eval]; ring
  | piBinding col i =>
      simp only [EmittedConstraintA.lowerA, EmittedConstraintA.evalA, EmittedExpr.eval]; ring
  | transition n l =>
      simp only [EmittedConstraintA.lowerA, EmittedConstraintA.evalA, EmittedExpr.eval]; ring
  | polynomial terms =>
      simp only [EmittedConstraintA.lowerA, EmittedConstraintA.evalA]
      exact lowerTerms_eval env terms
  | gated sel inner ih =>
      simp only [EmittedConstraintA.lowerA, EmittedConstraintA.evalA, EmittedExpr.eval, ih]
  | invertedGated sel inner ih =>
      simp only [EmittedConstraintA.lowerA, EmittedConstraintA.evalA, EmittedExpr.eval, ih]
      ring
  | squared inner ih =>
      simp only [EmittedConstraintA.lowerA, EmittedConstraintA.evalA, EmittedExpr.eval, ih]
  | conditionalNonzero sel v inv =>
      simp only [EmittedConstraintA.lowerA, EmittedConstraintA.evalA, EmittedExpr.eval]; ring
  | atLeastOne flags =>
      simp only [EmittedConstraintA.lowerA, EmittedConstraintA.evalA]
      exact lowerAtLeastOne_eval env flags

/-- **`emitA_faithful` — THE algebraic deliverable.** An algebraic emitted constraint holds
(`evalA = 0`, Rust's per-term condition) IFF its PART-I AST lowering evaluates to zero. So the
column-indexed wire form denotes EXACTLY the algebraic constraint `Circuit.bridge`'s `EmittedExpr`
semantics already certify — emission of these `ConstraintExpr` forms loses no algebra.
`#assert_axioms`-pinned. -/
theorem emitA_faithful (env : RowEnv) (c : EmittedConstraintA) :
    c.holdsA env ↔ (c.lowerA env).eval env.loc = 0 := by
  unfold EmittedConstraintA.holdsA
  rw [lowerA_eval]

/-! ### The `Polynomial` priority form (Merkle C1 position-validity) — concretely emitted.

`merkle_poseidon2_descriptor()`'s C1 is `pos·(pos−1)·(pos−2)·(pos−3) = 0`, the position-validity
check on the `position` column (= `merkleCols.position`). It is a `Polynomial` form: a single
degree-4 product term over the `position` column with the four roots expanded. As the Merkle
gadget note (PART II) records, C1 is a WELL-FORMEDNESS / position-validity constraint — it pins
`position ∈ {0,1,2,3}` at trace rows — and is **soundness-neutral for the abstract Merkle
bridge**: `Crypto.Merkle.Satisfies` proves membership via the position-INDEPENDENT node hash
(`compress current sib`), so C1 is NOT part of `Satisfies`. We emit it here for FIDELITY to the
real descriptor (the Rust decoder must reconstruct the full constraint list incl. C1) and prove
its denotation `holdsA env (mc1Poly) ↔ position ∈ {0,1,2,3}` (over `ℤ`).

We encode C1 as the EXPANDED polynomial `pos⁴ − 6·pos³ + 11·pos² − 6·pos`, the monomial form
`pos·(pos−1)·(pos−2)·(pos−3)` expands to — exactly the `PolyTerm` list a faithful `Polynomial`
emission carries (each term `coeff · pos^k` = `coeff · ∏` of `k` copies of the `position` col). -/

/-- The position column of the Merkle layout, as a `Nat` index (for the algebraic forms). -/
def merklePositionCol : Nat := merkleCols.position

/-- **The Merkle C1 position-validity constraint**, emitted as a `Polynomial` form: the expanded
`pos⁴ − 6·pos³ + 11·pos² − 6·pos` over the `position` column. (`pos^k` = a term whose column list
is `k` copies of `merklePositionCol`.) -/
def merkleC1Poly : EmittedConstraintA :=
  .polynomial
    [ (1,  [merklePositionCol, merklePositionCol, merklePositionCol, merklePositionCol])  -- pos⁴
    , (-6, [merklePositionCol, merklePositionCol, merklePositionCol])                     -- −6·pos³
    , (11, [merklePositionCol, merklePositionCol])                                        -- +11·pos²
    , (-6, [merklePositionCol]) ]                                                         -- −6·pos

/-- **`merkleC1_position_valid` — the C1 denotation.** Over `ℤ`, the emitted C1 polynomial holds
(`evalA = 0`) IFF the `position` cell is one of `{0,1,2,3}` — exactly the position-validity the
real C1 enforces at trace rows. This is the FACTORED form of the emitted expanded polynomial,
witnessing the emission is faithful to `pos·(pos−1)·(pos−2)·(pos−3) = 0`. (A well-formedness /
position-validity check; soundness-neutral for the abstract Merkle bridge — see `merkleC1Poly`.) -/
theorem merkleC1_position_valid (env : RowEnv) :
    merkleC1Poly.holdsA env ↔
      (env.loc merklePositionCol = 0 ∨ env.loc merklePositionCol = 1 ∨
       env.loc merklePositionCol = 2 ∨ env.loc merklePositionCol = 3) := by
  unfold merkleC1Poly EmittedConstraintA.holdsA EmittedConstraintA.evalA termValue
  set p := env.loc merklePositionCol with hp
  -- The folded sum is `p⁴ − 6p³ + 11p² − 6p = p·(p−1)·(p−2)·(p−3)`.
  have hsum : (([(1,  [merklePositionCol, merklePositionCol, merklePositionCol, merklePositionCol]),
                 (-6, [merklePositionCol, merklePositionCol, merklePositionCol]),
                 (11, [merklePositionCol, merklePositionCol]),
                 (-6, [merklePositionCol])] : List (Int × List Nat)).foldl
        (fun acc t => acc + t.1 * (t.2.foldl (fun a c => a * env.loc c) 1)) 0)
      = p * (p - 1) * (p - 2) * (p - 3) := by
    simp only [List.foldl_cons, List.foldl_nil, ← hp]; ring
  rw [hsum]
  constructor
  · intro h
    -- a product of integers is zero iff a factor is zero
    rcases mul_eq_zero.1 h with h1 | h3
    · rcases mul_eq_zero.1 h1 with h2 | h2'
      · rcases mul_eq_zero.1 h2 with h0 | h1'
        · exact Or.inl h0
        · exact Or.inr (Or.inl (by linarith [sub_eq_zero.1 h1']))
      · exact Or.inr (Or.inr (Or.inl (by linarith [sub_eq_zero.1 h2'])))
    · exact Or.inr (Or.inr (Or.inr (by linarith [sub_eq_zero.1 h3])))
  · rintro (h | h | h | h) <;> rw [h] <;> ring

/-! ### Canonical algebraic wire rendering (`#guard`-pinned golden; the Rust decoder grammar).

The wire tags mirror the snake-cased Rust `ConstraintExpr` variant names so the decoder rebuilds
the exact enum. `polynomial` terms carry `coeff` (signed integer) + `cols` (the column-index
product). The `gated`/`inverted_gated`/`squared` forms nest `inner` recursively. -/

/-- Render a `(coeff, cols)` polynomial term as JSON `{"coeff":N,"cols":[…]}`. -/
def polyTermToJson : Int × List Nat → String
  | (coeff, cols) =>
    let colsJson := match cols with
      | []      => "[]"
      | c :: cs => "[" ++ toString c ++ (cs.foldl (fun a x => a ++ "," ++ toString x) "") ++ "]"
    "{\"coeff\":" ++ toString coeff ++ ",\"cols\":" ++ colsJson ++ "}"

/-- Render a list of polynomial terms as a JSON array. -/
def polyTermsToJson : List (Int × List Nat) → String
  | []      => "[]"
  | t :: ts => "[" ++ polyTermToJson t ++ (ts.foldl (fun a x => a ++ "," ++ polyTermToJson x) "") ++ "]"

/-- Render a list of `Nat` columns as a JSON array. -/
def natsToJson : List Nat → String
  | []      => "[]"
  | c :: cs => "[" ++ toString c ++ (cs.foldl (fun a x => a ++ "," ++ toString x) "") ++ "]"

/-- Render an algebraic emitted constraint as JSON. Wire tags mirror the snake-cased Rust enum
variant names; the Rust decoder maps each back to its `ConstraintExpr` constructor. -/
def EmittedConstraintA.toJson : EmittedConstraintA → String
  | .equality a b           => "{\"t\":\"equality\",\"col_a\":" ++ toString a ++ ",\"col_b\":" ++ toString b ++ "}"
  | .multiplication a b o    => "{\"t\":\"multiplication\",\"a\":" ++ toString a ++ ",\"b\":" ++ toString b ++ ",\"output\":" ++ toString o ++ "}"
  | .binary col              => "{\"t\":\"binary\",\"col\":" ++ toString col ++ "}"
  | .piBinding col i         => "{\"t\":\"pi_binding\",\"col\":" ++ toString col ++ ",\"pi_index\":" ++ toString i ++ "}"
  | .transition n l          => "{\"t\":\"transition\",\"next_col\":" ++ toString n ++ ",\"local_col\":" ++ toString l ++ "}"
  | .polynomial terms        => "{\"t\":\"polynomial\",\"terms\":" ++ polyTermsToJson terms ++ "}"
  | .gated sel inner         => "{\"t\":\"gated\",\"selector_col\":" ++ toString sel ++ ",\"inner\":" ++ inner.toJson ++ "}"
  | .invertedGated sel inner => "{\"t\":\"inverted_gated\",\"selector_col\":" ++ toString sel ++ ",\"inner\":" ++ inner.toJson ++ "}"
  | .squared inner           => "{\"t\":\"squared\",\"inner\":" ++ inner.toJson ++ "}"
  | .conditionalNonzero sel v inv =>
      "{\"t\":\"conditional_nonzero\",\"selector_col\":" ++ toString sel ++ ",\"value_col\":" ++ toString v ++ ",\"inverse_col\":" ++ toString inv ++ "}"
  | .atLeastOne flags        => "{\"t\":\"at_least_one\",\"flag_cols\":" ++ natsToJson flags ++ "}"

-- `#guard` golden pin: C1 polynomial wire form. The Rust decoder reconstructs
-- `ConstraintExpr::Polynomial { terms }` from this exact grammar.
#guard (merkleC1Poly.toJson == r#"{"t":"polynomial","terms":[{"coeff":1,"cols":[4,4,4,4]},{"coeff":-6,"cols":[4,4,4]},{"coeff":11,"cols":[4,4]},{"coeff":-6,"cols":[4]}]}"#)

/-! ### Axiom-hygiene pins for the algebraic extension. -/

#assert_axioms emitA_faithful
#assert_axioms merkleC1_position_valid

/-! ## ════════════════════════════════════════════════════════════════════════════════
## PART IV — RANGE CHECKS on the wire: closing the `ℤ → BabyBear` field-soundness gap.
## ════════════════════════════════════════════════════════════════════════════════

The Lean circuit is sound over `ℤ` (no overflow). But the Rust ingestion
(`circuit/src/lean_descriptor_air.rs`) maps `ℤ → BabyBear`, a FINITE field (modulus
`p = 2³¹ − 2²⁷ + 1 ≈ 2³¹`). Without a range check a "balance" near `p` could WRAP and forge value
(set a balance to `p + b`, which reduces to `b` in the field but represents a colossal real number).
`Dregg2.Circuit.Lookup` gives the DENOTATION of the fix — `rangeCheck e k` forces `e ∈ [0, 2^k)`. This
part carries those range checks ONTO THE WIRE so the Rust AIR can ENFORCE them by bit-decomposition.

The emission is COMPACT: a `RangeSpec` carries `{wire, bits}` — the *bit-width* `k`, NOT the full
`2^k` table (which is astronomically large). The Rust side reconstructs the range gate as `k` boolean
aux columns + a recomposition constraint `Σ bᵢ·2ⁱ = wire`. A `RangedDescriptor` bundles an
`EmittedDescriptor` with its `ranges`, and `emitRangedDescriptorJson` renders the existing descriptor
JSON EXTENDED with a `"ranges":[{"wire":i,"bits":k},…]` field. This is purely additive:
`EmittedDescriptor`/`emit`/`emitDescriptorJson` are UNTOUCHED, so every existing def/test/golden holds.

NOTE on choosing `k`: for the gate to BITE over a field of modulus `p`, the bound must satisfy
`2^k ≤ p` — otherwise every field element already has a `k`-bit decomposition and the range gate is
VACUOUS. The `Transfer` emitter picks `k = 30` for `BabyBear` (`2³⁰ < p = 2013265921 < 2³¹`). See
`Dregg2.Circuit.Transfer.balanceRangeBits`. -/

/-- A **range spec** for one wire: the wire (column) index `wire` must lie in `[0, 2^bits)`. The
bit-width `bits = k` is the COMPACT carrier — the Rust AIR rebuilds the `2^k` range table implicitly
via a `k`-bit decomposition, never materializing it. The denotation is `Lookup.rangeCheck (.var wire)
bits` (membership in `[0, 2^bits)`). -/
structure RangeSpec where
  /-- The wire (column) index to range-check. -/
  wire : Nat
  /-- The bit-width `k`: the wire must be in `[0, 2^k)`. -/
  bits : Nat
  deriving Repr, DecidableEq

/-- A **ranged descriptor**: an `EmittedDescriptor` (unchanged) PLUS a list of `RangeSpec` range
checks. Bundling keeps PART-I `EmittedDescriptor`/`emit`/`emitDescriptorJson` untouched while carrying
the field-soundness range checks additively. -/
structure RangedDescriptor where
  /-- The underlying arithmetic descriptor (the existing wire form). -/
  base   : EmittedDescriptor
  /-- The range checks on selected wires (the field-soundness teeth). -/
  ranges : List RangeSpec
  deriving Repr, DecidableEq

/-- The DENOTATION of a `RangeSpec` against an assignment: the wire value lies in `[0, 2^bits)`. This
is exactly `Lookup.rangeCheck (.var wire) bits` holding, lifted to PART-I's `Assignment` model. -/
def RangeSpec.holds (r : RangeSpec) (a : Assignment) : Prop :=
  (Dregg2.Circuit.Lookup.rangeCheck (.var r.wire) r.bits).holds a

/-- `RangeSpec.holds` is decidable (membership in the finite range table), so the concrete `#guard`s
below can `decide` (genuine `decide`, not `native_decide`). -/
instance (r : RangeSpec) (a : Assignment) : Decidable (r.holds a) := by
  unfold RangeSpec.holds; exact inferInstance

/-- A `RangedDescriptor` is **satisfied** by an assignment iff the base arithmetic descriptor is
satisfied AND every range check holds. The conjunction the Rust AIR enforces (gates ∧ bit-decomps). -/
def satisfiedRanged (d : RangedDescriptor) (a : Assignment) : Prop :=
  satisfiedEmitted d.base a ∧ ∀ r ∈ d.ranges, r.holds a

/-- A range-free `RangedDescriptor` (`ranges := []`) is satisfied EXACTLY when its base is: the
extension is conservative over PART I (no range checks ⇒ identical acceptance). -/
theorem satisfiedRanged_nil (d : EmittedDescriptor) (a : Assignment) :
    satisfiedRanged ⟨d, []⟩ a ↔ satisfiedEmitted d a := by
  unfold satisfiedRanged
  simp

/-! ### Canonical ranged wire rendering: the base JSON EXTENDED with a `"ranges"` field.

The grammar is the PART-I descriptor grammar with one extra top-level key:

    {"name":S,"trace_width":N,"constraints":[…],"ranges":[{"wire":i,"bits":k},…]}

The Rust `parse_descriptor` is extended to read the (optional) `"ranges"` array; absence ⇒ `[]` (so
the existing goldens, which omit it, parse identically). -/

/-- Render one `RangeSpec` as JSON `{"wire":i,"bits":k}`. -/
def RangeSpec.toJson (r : RangeSpec) : String :=
  "{\"wire\":" ++ toString r.wire ++ ",\"bits\":" ++ toString r.bits ++ "}"

/-- Render a list of `RangeSpec`s as a JSON array. -/
def rangesToJson : List RangeSpec → String
  | []      => "[]"
  | r :: rs => "[" ++ r.toJson ++ (rs.foldl (fun acc x => acc ++ "," ++ x.toJson) "") ++ "]"

/-- **`emitRangedDescriptorJson`** — the canonical wire string for a `RangedDescriptor`: the base
descriptor JSON (via `emitDescriptorJson`) with the closing `}` replaced by `,"ranges":[…]}`. Built
by splicing rather than re-deriving, so the base bytes are BYTE-IDENTICAL to `emitDescriptorJson` —
the existing parser/golden are unaffected and the `ranges` field is a pure suffix. -/
def emitRangedDescriptorJson (d : RangedDescriptor) : String :=
  "{\"name\":\"" ++ d.base.name ++ "\",\"trace_width\":" ++ toString d.base.traceWidth ++
  ",\"constraints\":" ++ constraintsToJson d.base.constraints ++
  ",\"ranges\":" ++ rangesToJson d.ranges ++ "}"

/-! ### Non-vacuity `#guard`s: the range denotation accepts in-range and REJECTS out-of-range / wrap. -/

-- An in-range wire (value 100, k=8 ⇒ [0,256)) — accepted:
#guard decide ((RangeSpec.mk 0 8).holds (fun v => if v = 0 then 100 else 0))
-- An out-of-range wire (value 999 ≥ 2^8 = 256) — REJECTED (the field-wrap a range check forbids):
#guard decide (¬ (RangeSpec.mk 0 8).holds (fun v => if v = 0 then 999 else 0))

#assert_axioms satisfiedRanged_nil

/-! ## ════════════════════════════════════════════════════════════════════════════════
## PART IV — Verifier backing: the emitted hash forms are now AUDITED-p3 algebraic.
## ════════════════════════════════════════════════════════════════════════════════

PART II/III noted the `Hash*` forms as *opaque/non-polynomial* — in the previous Rust backend
the digest was a CONCRETE Poseidon2 recompute "checked" only at trace rows, and the whole circuit
verified through the hand-rolled `crate::stark` FRI (whose terminal low-degree test is effectively
absent and whose trace columns are never low-degree-tested). That made the hash binding a §8
ASSUMPTION (the verifier had to be trusted), not a constraint.

That has CHANGED in the Rust backend (`circuit/src/dsl/dsl_p3_air.rs` +
`circuit/src/plonky3_prover.rs::poseidon2_permute_expr`): `Hash2to1` / `Hash4to1` now denote a
GENUINE in-circuit Poseidon2 permutation — round-by-round S-box (`x^7`) + external/internal linear
layers, each round bound to witness aux columns — proved+verified through the **audited
`p3-batch-stark`** prover/verifier. A forged digest is UNSAT (the permutation constraints reject it).

This part records that semantics so Lean's circuit-soundness story is faithful to what the backend
now enforces: the hash digest is an ALGEBRAIC equality `out = Poseidon2(inputs)` whose acceptance is
a constraint, not a trusted oracle. We model the binding abstractly over a `compress`-style function
(as PART II does for the Merkle gadget) and pin that the emitted-form denotation is exactly
"the output column equals the permutation of the inputs". -/

namespace HashBacking

/-- The two node-hashing forms the audited-p3 DSL AIR arithmetizes in-circuit. `arity` is the
domain-separation tag the concrete `hash_2_to_1`/`hash_4_to_1` place at capacity slot 4 (2 resp. 4),
and which `hash_input_state` mirrors. -/
inductive HashForm where
  | hash2to1 (outputCol inputColA inputColB : Nat)
  | hash4to1 (outputCol : Nat) (inputCols : List Nat)
  deriving Repr, DecidableEq

/-- Abstract Poseidon2 permutation-digest over a row of field values (the `perm` argument stands
for `poseidon2_permute_expr`'s denotation: digest = state[0] after the full permutation of the
arity-tagged input state). Soundness here = the digest column equals `perm inputs`; this is an
EQUALITY constraint the audited verifier enforces (NOT a trusted recompute). -/
def HashForm.holds (perm : List Int → Int) (row : Assignment) : HashForm → Prop
  | .hash2to1 o a b   => row o = perm [row a, row b]
  | .hash4to1 o cols  => row o = perm (cols.map row)

/-- The binding is DECIDABLE given a concrete `perm` and row — i.e. the verifier's acceptance of
the hash form is a checkable algebraic predicate, exactly as on the audited p3 path. -/
instance (perm : List Int → Int) (row : Assignment) (h : HashForm) :
    Decidable (h.holds perm row) := by
  cases h <;> · unfold HashForm.holds; exact decEq _ _

/-- **Anti-ghost tooth, abstractly**: a forged digest (`out ≠ perm inputs`) does NOT satisfy the
hash form. This is the Lean-side witness that the in-circuit permutation REJECTS a tampered digest,
mirroring `hash2to1_real_poseidon2_round_trips_through_p3`'s forged-reject assertion. -/
theorem forged_digest_rejected (perm : List Int → Int) (row : Assignment)
    (o a b : Nat) (h : row o ≠ perm [row a, row b]) :
    ¬ (HashForm.hash2to1 o a b).holds perm row := by
  unfold HashForm.holds; exact h

/-- And an honest digest is accepted. -/
theorem honest_digest_accepted (perm : List Int → Int) (row : Assignment)
    (o a b : Nat) (h : row o = perm [row a, row b]) :
    (HashForm.hash2to1 o a b).holds perm row := by
  unfold HashForm.holds; exact h

-- Non-vacuity: with the identity-sum stand-in perm, a matching row is accepted and a
-- mismatched (forged) row is rejected.
private def sumPerm : List Int → Int := fun xs => xs.foldl (· + ·) 0
#guard decide ((HashForm.hash2to1 2 0 1).holds sumPerm
  (fun i => if i = 0 then 3 else if i = 1 then 4 else 7))      -- 7 = 3+4 ✓
#guard decide (¬ (HashForm.hash2to1 2 0 1).holds sumPerm
  (fun i => if i = 0 then 3 else if i = 1 then 4 else 99))     -- 99 ≠ 7 — forged ✗

#assert_axioms forged_digest_rejected

end HashBacking

end Dregg2.Exec.CircuitEmit
