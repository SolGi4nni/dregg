/-
# Dregg2.Circuit.CustomLeafEncoding — faithful encoding of a Lean MIRROR of `custom_leaf_adapter.rs`.

⚠ RESOLUTION (see `docs/audit/SEMANTIC-LEAN-BOUNDARY.md`, Class B). This proves faithfulness of a
RE-AUTHORED Lean model, NOT of the deployed Rust lowering. `CellLocal`/`gateBody` are a hand-copy
of the Rust `gate_body` / `cellprogram_to_descriptor2` table (`circuit/src/custom_leaf_lowering.rs`,
`circuit-prove/src/custom_leaf_adapter.rs`), connected to it by PROSE ("term-for-term the Rust")
only — no `@[export]`, no emit, no differential/byte pin (cell/ carries no Lean ffi). It covers
just the 9-of-21 PURE-LOCAL kinds.

⚠ CORRECTED 2026-07-26 (this header previously said the uncovered kinds "are omitted (REFUSED by
the Rust adapter, not encoded here)" — that reads as "unreachable", and it is FALSE at HEAD).
Re-read against `circuit/src/custom_leaf_lowering.rs::lower_cellprogram`, the Rust adapter LOWERS,
and this file does NOT encode or prove, EIGHT further kinds: `Hash2to1` / `Hash4to1` / `Hash3Cap` /
`MerkleHash` (single-output `TID_P2` chip lookups with 7 allocated lane columns), `MerkleHash8`
(the 8-lane multi-output site), `ChainedHash2to1` + its paired `SeedHash2to1` (a copy-forward
accumulator column + `WindowGate` + first-row PI pin), and `TableFunction` (a bivariate-Lagrange
gate body, `table_function_body`). Plus `BoundaryDef::PiBinding` / `Fixed`. The kinds the adapter
genuinely REFUSES are only four: `Hash` (the capacity-tagged fact-sponge), a standalone
`SeedHash2to1` no chain accumulates, an arbitrary-entry `Lookup`, and `BoundaryRow::Index`. So the
uncovered surface is REACHABLE AND UNPROVEN, not refused — the Poseidon2 chip-lookup lowering in
particular is where the cryptographic content of a custom leaf lives.

And `CellLocalHolds` is DEFINED as the
same `gateBody` vanishing that the encoded gate denotes, so `encodeLocal_holdsAt_iff` /
`cell_to_descriptor_faithful` are a CARRIER-REDUCTION over the Lean model (proving the `.gate`
carrier loses no info) — NOT an independent comparison of the Lean `gateBody` to the deployed Rust
`gate_body`. "The deployed lowering IS faithful" therefore remains UNPROVEN future work
(author-the-lowering-in-Lean-and-emit — Step 4/T3 of the boundary doc).

## What this formalizes (the Lean side of Fork X / G2)

`circuit-prove/src/custom_leaf_adapter.rs` adapts a `CellProgram`'s `CircuitDescriptor` into an
IR-v2 `EffectVmDescriptor2` (`cellprogram_to_descriptor2`), so a custom sub-proof re-proves as a
recursion-foldable IR-v2 leaf and folds into the SAME aggregate tree a light client verifies. For
that re-proof to MEAN anything, the encoding must PRESERVE the constraint semantics: a trace
satisfies the original `CellProgram`'s pure-local algebraic constraints IFF it satisfies the encoded
`EffectVmDescriptor2` constraints. This module is that faithfulness statement, in Lean, over the
Lean denotations `Emit.EffectVmEmit.VmConstraint.holdsVm` and `DescriptorIR2.VmConstraint2.holdsAt`
— which are themselves Lean MIRRORS of the deployed AIR's evaluator, not the deployed AIR (see the
resolution note atop this file).

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
3. `encodePiBinding_narrows` — the every-row→first-row narrowing is SOUND one way; the converse
   gap is a GENUINE narrowing (witnessed non-vacuous by `encodePiBinding_not_complete`), not an
   equivalence — the follow-up is a per-row PI gate in the IR-v2 main AIR, exactly as the Rust
   adapter's module note says.
4. `cell_to_descriptor_faithful` — CLOSED: the descriptor-level row×constraint re-quantification
   of the per-row core.

All denotations are the field-faithful mod-p residues (`≡ 0 [ZMOD 2013265921]`) — the DSL evaluator
computes over BabyBear, so this IS the cell semantics, not an envelope.

(The former item 5, `engineBinding_over_faithful_encoding`, was a `True := trivial` placeholder for
the now-deleted vacuous `CustomApex.lightclient_unfoolable_custom`; it is RETIRED. The deployed custom
binding is real-as-deployed via the FOLD — `CustomBindingFromFold.custom_binding_from_fold` — not a row
carrier. This file supplies only the faithful-encoding leg; the binding leg is the fold.)

NO new axioms; sorry-free. Import-clean. NOT added to `Dregg2.lean` (the main loop wires imports).
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

/-- One `PolyTerm`'s body, folded LEFT from the coefficient exactly as the Rust does
(`prod = LeanExpr::Const(coeff)`, then `prod = mul(prod, Var(ci))` per column): `[c₀, c₁]` gives
`((coeff · c₀) · c₁)`, and no columns gives the bare `coeff`.

⚠ 2026-07-26: this WAS `.mul (.const coeff) (prodCols cols)` over a RIGHT-nested `prodCols` that
appended a `.const 1` terminator — algebraically the same polynomial, but a DIFFERENT `EmittedExpr`
tree, so the header's "term-for-term the Rust `gate_body`" was false here and at `atLeastOneBody`.
Since the emitted descriptor JSON *is* the serialized tree, that drift is exactly what would have
blocked ever turning this mirror into a byte pin. Re-shaped to the Rust fold. -/
def polyTermBody (coeff : ℤ) : List Nat → EmittedExpr
  | []      => .const coeff
  | c :: cs => polyTermBodyAux (.mul (.const coeff) (.var c)) cs
where
  /-- The left-fold tail: `acc` already holds `coeff · c₀ · … `, multiply the remaining columns on. -/
  polyTermBodyAux (acc : EmittedExpr) : List Nat → EmittedExpr
    | []      => acc
    | c :: cs => polyTermBodyAux (.mul acc (.var c)) cs

/-- The left-fold tail of the term SUM: `acc` already holds `t₀ + … `, add the remaining terms on. -/
def polySumAux (acc : EmittedExpr) : List PolyTerm → EmittedExpr
  | []      => acc
  | t :: ts => polySumAux (.add acc (polyTermBody t.coeff t.cols)) ts

/-- `Σ coeffᵢ · ∏ colⱼ` — the Rust `Polynomial` lowering, LEFT-folded, with the FIRST term seeding
the accumulator (so a single-term polynomial is the bare term, never `term + 0`) and an empty
polynomial the zero constraint (`acc.unwrap_or(LeanExpr::Const(0))`). -/
def polyBody : List PolyTerm → EmittedExpr
  | []      => .const 0
  | t :: ts => polySumAux (polyTermBody t.coeff t.cols) ts

/-- One `AtLeastOne` factor `1 − flag`. -/
def atLeastOneFactor (c : Nat) : EmittedExpr := subE (.const 1) (.var c)

/-- The left-fold tail of the factor PRODUCT. -/
def atLeastOneAux (acc : EmittedExpr) : List Nat → EmittedExpr
  | []      => acc
  | c :: cs => atLeastOneAux (.mul acc (atLeastOneFactor c)) cs

/-- `∏ (1 − flagᵢ)` — the Rust `AtLeastOne` lowering, LEFT-folded, first factor seeding the
accumulator; an empty flag list is the constant-`1` (unsatisfiable) gate, mirroring
`acc.unwrap_or(LeanExpr::Const(1))`. -/
def atLeastOneBody : List Nat → EmittedExpr
  | []      => .const 1
  | c :: cs => atLeastOneAux (atLeastOneFactor c) cs

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

/-- The `CellProgram`'s own per-row semantics for a pure-local gate: the body vanishes on the row
IN THE FIELD — the DSL evaluator computes over BabyBear, so the faithful denotation is
`≡ 0 [ZMOD p]` (`p = 2013265921`), matching the deployed `holdsVm .gate` residue exactly. -/
def CellLocalHolds (env : VmRowEnv) (c : CellLocal) : Prop :=
  (gateBody c).eval env.loc ≡ 0 [ZMOD 2013265921]

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
      ↔ env.nxt next ≡ env.loc locCol [ZMOD 2013265921] := by
  simp [encodeTransition, VmConstraint2.holdsAt, WindowConstraint.holdsAt, WindowExpr.eval,
    Int.ModEq]
  omega

/-! ## §5 — The `PiBinding` NARROWING (sound one way; the gap witnessed non-vacuous). -/

/-- The Rust `PiBinding{col,pi}` lowering: a FIRST-row-guarded `base .piBinding`. The `CellProgram`
semantics is EVERY row (`loc[col] = pi[idx]` on all rows); the IR-v2 carrier binds only the first
row — a documented narrowing. -/
def encodePiBinding (col piIndex : Nat) : VmConstraint2 := .base (.piBinding .first col piIndex)

/-- The `CellProgram`'s every-row PI gate (field congruence — the DSL evaluator is BabyBear). -/
def CellPiEveryRow (env : VmRowEnv) (col piIndex : Nat) : Prop :=
  env.loc col ≡ env.pub piIndex [ZMOD 2013265921]

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
an interior row. Witnessed: a row satisfying the binding (all-zero) and a row violating it
(`loc = 1`, `pub = 0` — not congruent mod p). The IR-v2 per-row PI gate is what would close the
narrowing itself. -/
theorem encodePiBinding_not_complete :
    ∃ (env₀ env₁ : VmRowEnv) (col piIndex : Nat),
      env₀.loc col = env₀.pub piIndex ∧
      ¬ CellPiEveryRow env₁ col piIndex := by
  refine ⟨⟨fun _ => 0, fun _ => 0, fun _ => 0⟩, ⟨fun _ => 1, fun _ => 0, fun _ => 0⟩, 0, 0,
    rfl, ?_⟩
  simp only [CellPiEveryRow, Int.ModEq]
  omega

/-! ## §6 — Descriptor-level faithfulness (CLOSED). -/

/-- A custom leaf's pure-local constraint program (the subset this spike proves; hash/lookup/
table-function kinds are REFUSED by the Rust adapter, not encoded). -/
abbrev CellProgramLocal := List CellLocal

/-- The encoded IR-v2 constraint list. -/
def encodeProgram (p : CellProgramLocal) : List VmConstraint2 := p.map encodeLocal

/-- **Descriptor-level faithful encoding (of the Lean MIRROR — ⚠ NOT the deployed Rust lowering; see
the resolution note atop this file; `CellLocalHolds` is defined as the encoded gate's own body
vanishing, so this is a carrier-reduction).** A multi-row trace satisfies every encoded gate on every
active row iff it satisfies every cell gate on every active row. The per-row equivalence is
`encodeLocal_holdsAt_iff`; this is its row×constraint re-quantification over the trace. (The
wrap-row `isLast` arm is not quantified: the deployed `.gate` is vacuously `True` on the last row —
so the encoded descriptor is, if anything, WEAKER on the wrap row, never stronger; faithfulness on
the active rows is the load-bearing direction.) -/
theorem cell_to_descriptor_faithful (hash : List ℤ → ℤ) (tf : TraceFamily)
    (envs : List VmRowEnv) (isFirst : Bool) (p : CellProgramLocal) :
    (∀ env ∈ envs, ∀ c ∈ encodeProgram p,
        c.holdsAt hash tf env isFirst false)
      ↔ (∀ env ∈ envs, ∀ c ∈ p, CellLocalHolds env c) := by
  constructor
  · intro h env henv c hc
    exact (encodeLocal_holdsAt_iff hash tf env isFirst c).1
      (h env henv (encodeLocal c) (List.mem_map_of_mem hc))
  · intro h env henv c hc
    obtain ⟨c', hc', rfl⟩ := List.mem_map.mp hc
    exact (encodeLocal_holdsAt_iff hash tf env isFirst c').2 (h env henv c' hc')

-- (Retired: `engineBinding_over_faithful_encoding` was a `True := trivial` placeholder whose only
-- role was to name the encoding's part in the now-deleted vacuous `CustomApex.lightclient_unfoolable
-- _custom`. The deployed custom binding is real-as-deployed via the FOLD — `CustomBindingFromFold.
-- custom_binding_from_fold` (the leg's exposed commitment is `connect`-bound to a verifying sub-proof
-- the aggregate re-verifies) + the biting tooth in `joint_turn_recursive::prove_custom_binding_node`.
-- This file supplies only the faithful-encoding leg; the binding leg is the fold, not a row carrier.)

end Dregg2.Circuit.CustomLeafEncoding
