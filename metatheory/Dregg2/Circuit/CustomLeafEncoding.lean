/-
# Dregg2.Circuit.CustomLeafEncoding — the faithful-encoding twin of `custom_leaf_adapter.rs`.

## What this formalizes (the Lean side of Fork X / G2)

`circuit-prove/src/custom_leaf_adapter.rs` adapts a `CellProgram`'s `CircuitDescriptor` into an
IR-v2 `EffectVmDescriptor2` (`cellprogram_to_descriptor2`), so a custom sub-proof re-proves as a
recursion-foldable IR-v2 leaf and folds into the SAME aggregate tree a light client verifies. For
that re-proof to MEAN anything, the encoding must PRESERVE the constraint semantics: a trace
satisfies the original `CellProgram`'s pure-local algebraic constraints IFF it satisfies the encoded
`EffectVmDescriptor2` constraints. This module is that faithfulness statement, in Lean, over the
EXACT denotations the deployed AIR carries (`Emit.EffectVmEmit.VmConstraint.holdsVm` and
`DescriptorIR2.VmConstraint2.holdsAt`).

It is the encoding-side companion to `CustomApex.lean`: that file binds the Custom row's `proofBind`
op to a VERIFYING sub-proof under the named `EngineBinding` carrier (the in-AIR recursion verifier);
THIS file shows the sub-proof's own algebraic constraints survive the `CellProgram → VmConstraint2`
lowering, so the `EngineBinding` carrier is realized over the FAITHFUL descriptor — not a descriptor
that silently dropped or weakened a `CellProgram` gate.

## The mapping mirrored (the Rust `gate_body` / `cellprogram_to_descriptor2` table)

Each PURE-LOCAL `ConstraintExpr` lowers to ONE `VmConstraint2.base (.gate body)` whose polynomial
`body` (an `EmittedExpr`) must vanish per row. `Transition` lowers to a two-row `windowGate`;
`PiBinding` to a row-tag-guarded `base (.piBinding First ..)` — a NAMED NARROWING (every-row →
first-row) the Rust adapter documents.

## Proof obligations (and what is closed vs. labelled)

1. `encodeLocal_holdsAt_iff` — CLOSED: each pure-local gate's encoded `holdsAt` (on a transition
   row) is EXACTLY its body-vanishes semantics. This is the algebraic core: equality / multiply /
   binary / polynomial / gated / inverted-gated / squared / conditional-nonzero / at-least-one all
   ride the single `base (.gate _)` carrier, so faithfulness is the `holdsVm .gate` reduction.
2. `encodeTransition_holdsAt_iff` — CLOSED: the `windowGate` carrier is the cross-row equality.
3. `encodePiBinding_narrows` — the every-row→first-row narrowing is SOUND one way (`sorry`-labelled
   on the converse gap — it is a genuine narrowing, not an equivalence; the follow-up is a per-row
   PI gate in the IR-v2 main AIR, exactly as the Rust adapter's module note says).
4. `cell_to_descriptor_faithful` — the descriptor-level packaging (`sorry`-labelled: the full
   `Satisfied2` row-quantification over a mixed constraint list — mechanical but long).
5. `engineBinding_over_faithful_encoding` — the bridge to `CustomApex` (`sorry`-labelled: it rests
   on the staged `boundAt` + `EngineBinding` carrier that `CustomApex.lean` owns; stated here so the
   encoding's role in the apex is explicit).

NO new axioms; `sorry` only on the labelled arms above. Import-clean. NOT added to `Dregg2.lean`
(the main loop wires imports).
-/

import Dregg2.Circuit.DescriptorIR2

namespace Dregg2.Circuit.CustomLeafEncoding

open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.DescriptorIR2

/-! ## §1 — The `EmittedExpr` lowering (mirrors Rust `gate_body`). -/

/-- `x − y` with no subtraction node: `x + (−1)·y` (the Rust `sub`). -/
def subE (x y : EmittedExpr) : EmittedExpr := .add x (.mul (.const (-1)) y)

/-- A polynomial monomial: a coefficient times a product of columns (the Rust `PolyTerm`). -/
structure PolyTerm where
  coeff : ℤ
  cols  : List Nat

/-- `∏ var cⱼ` (empty product = `1`). -/
def prodCols : List Nat → EmittedExpr
  | []      => .const 1
  | c :: cs => .mul (.var c) (prodCols cs)

/-- `Σ coeffᵢ · ∏ colⱼ` (empty sum = `0`) — the Rust `Polynomial` lowering (algebraically the same
fold; the head term is `coeff · prod` summed onto the rest). -/
def polyBody : List PolyTerm → EmittedExpr
  | []      => .const 0
  | t :: ts => .add (.mul (.const t.coeff) (prodCols t.cols)) (polyBody ts)

/-- `∏ (1 − flagᵢ)` (empty = `1`) — the Rust `AtLeastOne` lowering. -/
def atLeastOneBody : List Nat → EmittedExpr
  | []      => .const 1
  | c :: cs => .mul (subE (.const 1) (.var c)) (atLeastOneBody cs)

/-- The PURE-LOCAL `ConstraintExpr` subset the adapter lowers to ONE `Base(Gate(body))`. -/
inductive CellLocal where
  | equality           (a b : Nat)
  | multiplication     (a b output : Nat)
  | binary             (col : Nat)
  | polynomial         (terms : List PolyTerm)
  | gated              (sel : Nat) (inner : CellLocal)
  | invertedGated      (sel : Nat) (inner : CellLocal)
  | squared            (inner : CellLocal)
  | conditionalNonzero (sel value inverse : Nat)
  | atLeastOne         (flags : List Nat)

/-- The polynomial body that must vanish — term-for-term the Rust `gate_body`. -/
def gateBody : CellLocal → EmittedExpr
  | .equality a b              => subE (.var a) (.var b)
  | .multiplication a b o      => subE (.mul (.var a) (.var b)) (.var o)
  | .binary c                  => .mul (.var c) (.add (.var c) (.const (-1)))
  | .polynomial ts             => polyBody ts
  | .gated s inner             => .mul (.var s) (gateBody inner)
  | .invertedGated s inner     => .mul (subE (.const 1) (.var s)) (gateBody inner)
  | .squared inner             => .mul (gateBody inner) (gateBody inner)
  | .conditionalNonzero s v iv => .mul (.var s) (subE (.mul (.var v) (.var iv)) (.const 1))
  | .atLeastOne flags          => atLeastOneBody flags

/-! ## §2 — The encoding into `VmConstraint2` (mirrors `cellprogram_to_descriptor2`). -/

/-- A pure-local cell constraint encodes to a single per-row main gate. -/
def encodeLocal (c : CellLocal) : VmConstraint2 := .base (.gate (gateBody c))

/-- The `CellProgram`'s own per-row semantics for a pure-local gate: the body vanishes on the row.
This is exactly what the DSL evaluator enforces for these algebraic kinds. -/
def CellLocalHolds (env : VmRowEnv) (c : CellLocal) : Prop := (gateBody c).eval env.loc = 0

/-! ## §3 — Faithfulness of the pure-local encoding (the CLOSED algebraic core). -/

/-- **The faithful-encoding core.** On any ACTIVE (transition) row (`isLast = false`), the encoded
constraint's IR-v2 denotation is EXACTLY the cell gate's body-vanishes semantics. Every pure-local
kind rides the single `base (.gate _)` carrier, so there is no per-kind gap: the lowering preserves
satisfaction. -/
theorem encodeLocal_holdsAt_iff (hash : List ℤ → ℤ) (tf : TraceFamily) (env : VmRowEnv)
    (isFirst : Bool) (c : CellLocal) :
    (encodeLocal c).holdsAt hash tf env isFirst false ↔ CellLocalHolds env c := by
  simp [encodeLocal, CellLocalHolds, VmConstraint2.holdsAt, VmConstraint.holdsVm]

/-- A whole pure-local program faithfully encodes: a row satisfies the encoded gates iff it
satisfies every cell gate. (Active-row form — the form the leaf's transition rows take.) -/
theorem encodeLocal_list_holdsAt_iff (hash : List ℤ → ℤ) (tf : TraceFamily) (env : VmRowEnv)
    (isFirst : Bool) (cs : List CellLocal) :
    (∀ c ∈ cs, (encodeLocal c).holdsAt hash tf env isFirst false)
      ↔ (∀ c ∈ cs, CellLocalHolds env c) := by
  constructor
  · intro h c hc; exact (encodeLocal_holdsAt_iff hash tf env isFirst c).1 (h c hc)
  · intro h c hc; exact (encodeLocal_holdsAt_iff hash tf env isFirst c).2 (h c hc)

/-! ## §4 — The two-row `Transition` carrier (CLOSED). -/

/-- The Rust `Transition{next,local}` lowering: a `windowGate` whose body is `nxt next − loc local`,
asserted on the transition domain. -/
def encodeTransition (next locCol : Nat) : VmConstraint2 :=
  .windowGate ⟨.add (.nxt next) (.mul (.const (-1)) (.loc locCol)), true⟩

/-- **The transition carrier is the cross-row equality.** On an active row the encoded `windowGate`
holds iff `nxt[next] = loc[local]` — the faithful, column-general continuity a `CellProgram`
cross-row constraint asks for (the deployed `base .transition` form hard-codes the EffectVM state
window bases, so it cannot carry a generic column pair; `windowGate` can). -/
theorem encodeTransition_holdsAt_iff (hash : List ℤ → ℤ) (tf : TraceFamily) (env : VmRowEnv)
    (isFirst : Bool) (next locCol : Nat) :
    (encodeTransition next locCol).holdsAt hash tf env isFirst false
      ↔ env.nxt next = env.loc locCol := by
  simp [encodeTransition, VmConstraint2.holdsAt, WindowConstraint.holdsAt, WindowExpr.eval]
  omega

/-! ## §5 — The `PiBinding` NARROWING (sound one way — labelled). -/

/-- The Rust `PiBinding{col,pi}` lowering: a FIRST-row-guarded `base .piBinding`. The `CellProgram`
semantics is EVERY row (`loc[col] = pi[idx]` on all rows); the IR-v2 carrier binds only the first
row — a documented narrowing. -/
def encodePiBinding (col piIndex : Nat) : VmConstraint2 := .base (.piBinding .first col piIndex)

/-- The `CellProgram`'s every-row PI gate. -/
def CellPiEveryRow (env : VmRowEnv) (col piIndex : Nat) : Prop := env.loc col = env.pub piIndex

/-- **The narrowing is SOUND (every-row ⟹ first-row).** A trace satisfying the `CellProgram`'s
every-row PI binding also satisfies the encoded first-row binding. The CONVERSE is the genuine gap
(first-row alone does NOT recover every-row) — the named follow-up is a per-row PI gate in the IR-v2
main AIR, after which this becomes an `↔`. -/
theorem encodePiBinding_narrows (hash : List ℤ → ℤ) (tf : TraceFamily) (env : VmRowEnv)
    (isLast : Bool) (col piIndex : Nat)
    (hEvery : CellPiEveryRow env col piIndex) :
    (encodePiBinding col piIndex).holdsAt hash tf env true isLast := by
  simp [encodePiBinding, VmConstraint2.holdsAt, VmConstraint.holdsVm]
  exact hEvery

/-- The narrowing GAP, stated honestly: a first-row binding does NOT imply the every-row binding on
an interior row. (The witness is any trace agreeing on the first row but differing on a later one;
left as the documented `sorry` — the IR-v2 per-row PI gate closes it.) -/
theorem encodePiBinding_not_complete :
    ∃ (env₀ env₁ : VmRowEnv) (col piIndex : Nat),
      env₀.loc col = env₀.pub piIndex ∧
      ¬ CellPiEveryRow env₁ col piIndex := by
  sorry -- LABELLED: the genuine every-row→first-row narrowing; closed by a per-row IR-v2 PI gate.

/-! ## §6 — Descriptor-level faithfulness + the `EngineBinding` bridge (labelled). -/

/-- A custom leaf's pure-local constraint program (the subset this spike proves; hash/lookup/
table-function kinds are REFUSED by the Rust adapter, not encoded). -/
abbrev CellProgramLocal := List CellLocal

/-- The encoded IR-v2 constraint list. -/
def encodeProgram (p : CellProgramLocal) : List VmConstraint2 := p.map encodeLocal

/-- **Descriptor-level faithful encoding.** A multi-row trace satisfies every encoded gate on every
active row iff it satisfies every cell gate on every active row. The per-row equivalence is
`encodeLocal_list_holdsAt_iff`; the row-quantified packaging over the trace is mechanical.

LABELLED `sorry`: the full `Satisfied2`-shaped quantification (including the wrap-row `isLast` arm,
where the deployed `.gate` is vacuously `True` on the last row — so the encoded descriptor is, if
anything, WEAKER on the wrap row, never stronger; faithfulness on the active rows is the load-bearing
direction and is closed above). -/
theorem cell_to_descriptor_faithful (hash : List ℤ → ℤ) (tf : TraceFamily)
    (envs : List VmRowEnv) (isFirst : Bool) (p : CellProgramLocal) :
    (∀ env ∈ envs, ∀ c ∈ encodeProgram p,
        c.holdsAt hash tf env isFirst false)
      ↔ (∀ env ∈ envs, ∀ c ∈ p, CellLocalHolds env c) := by
  sorry -- LABELLED: mechanical row×constraint re-quantification over `encodeLocal_list_holdsAt_iff`.

-- (Retired: `engineBinding_over_faithful_encoding` was a `True := trivial` placeholder whose only
-- role was to name the encoding's part in the now-deleted vacuous `CustomApex.lightclient_unfoolable
-- _custom`. The deployed custom binding is real-as-deployed via the FOLD — `CustomBindingFromFold.
-- custom_binding_from_fold` (the leg's exposed commitment is `connect`-bound to a verifying sub-proof
-- the aggregate re-verifies) + the biting tooth in `joint_turn_recursive::prove_custom_binding_node`.
-- This file supplies only the faithful-encoding leg; the binding leg is the fold, not a row carrier.)

end Dregg2.Circuit.CustomLeafEncoding
