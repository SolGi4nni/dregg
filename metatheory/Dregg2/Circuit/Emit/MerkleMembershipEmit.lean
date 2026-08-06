/-
# Dregg2.Circuit.Emit.MerkleMembershipEmit — the emit-from-Lean TEMPLATE, one family: 4-ary
Poseidon2 Merkle membership (fixed depth 2).

## What this file IS (the copyable template for the emit swarm)

A MINIMAL but REAL `EffectVmDescriptor2` that DECLARES, in the IR-v2 grammar, the statement
"a leaf sits under a public root in a depth-2, 4-ary Poseidon2 Merkle tree". It replaces the
hand-written `MerklePoseidon2StarkAir` (`circuit/src/poseidon2_air.rs`) SEMANTICS with an emitted
descriptor whose per-level `child → parent` step is a `Poseidon2Chip` lookup (arity-4 absorb,
project lane 0 = parent — the `hash_4_to_1` shape, `circuit/src/poseidon2.rs:349`), whose levels are
tied by a chain-continuity Base gate (`next-level path input == this-level parent`), and whose last
parent is `PiBinding`-pinned to the public root PI.

The emitted JSON (`emitVmJson2`) is BYTE-PINNED below (`#guard`). The Rust equality gate
(`circuit-prove/tests/merkle_membership_emit_gate.rs`) DECODES this exact string via
`parse_vm_descriptor2`, proves an honest witness through `prove_vm_descriptor2_for_config`
(ACCEPT), and mutates the leaf / a sibling / the claimed root to force a real UNSAT (the mutation
canary). Emitted descriptor ≡ hand-AIR membership semantics.

## The Poseidon2Chip lookup mapping this validates (the ~15-family dependency)

A `TID_P2_NARROW` chip lookup with arity tag `4` and inputs `[c0,c1,c2,c3]` is served by the chip table's
narrow rate-4 seeding: `state[0..4] = c0..c3`, `state[4] = 4` (the arity tag), `state[5..] = 0`,
`out0 = permute(state)[0]`. That is EXACTLY `poseidon2::hash_4_to_1([c0,c1,c2,c3])`
(`circuit/src/descriptor_ir2.rs:3353` `chip_absorb_all_lanes(4, ..)[0]` — the Rust gate KATs this).
The chip AIR binds `out0` (and lanes 1..7) to the real permutation, and the NARROW bus is served by
the 18-prefix of those SAME rows (`descriptor_ir2.rs::narrow_hist`, modelled by
`ChipNarrowLookup.narrowTable_sound`), so a lookup that names a forged parent has no serving chip
row → UNSAT. Every hash-carrying family (heap/fields/accumulator/cap/…)
depends on THIS arity→seeding→digest correspondence; here it is exercised end-to-end.

## ⚑ COMPILER-SOURCED (2026-08-01, Phase 3 of `docs/LOGIC-COMPILER-ASSESSMENT.md`)

This descriptor is no longer a hand-written `VmConstraint2` list literal. Its source is the
`EffectAir` in §2 (`merkleAir`) and its bytes are `EffectLower.lowerAir` of that source —
`merkleMembershipDesc_is_lowering` is `rfl`, and the hand-written list is DELETED, not kept beside.

**Its bytes MOVED, and the reason is exactly the one Phase 2 measured.** The continuity residual
`CUR1 − PARENT0` was hand-rendered `add(var 5, mul(const -1, var 4))` — a bare unit coefficient on
one term and an explicit `const -1` on the other, inside ONE body. The compiler renders both terms
the same way (`AirNormalForm`'s corpus invariant), so the gate and the last-row boundary are now
`add(mul(const 1, var 5), mul(const -1, var 4))`. The polynomial is identical
(`AirNormalForm.gateBody_eval`), the p3 symbolic degree is identical (`Const => 0`, `Mul => sum`),
and `continuity_body_zero_iff` is re-established VERBATIM over the compiled body.

RE-EMITS: `circuit/descriptors/by-name/merkle-membership-depth2.json` (+ its PROVENANCE sha) and
the `GOLDEN_JSON` literal in `circuit-prove/tests/merkle_membership_emit_gate.rs`.

## Axiom hygiene

Compiler-lowered descriptor + a byte-pinned `#guard` on its wire string + one genuinely-proven,
non-vacuous semantic lemma (`continuity_body_zero_iff`, TRUE iff the levels chain, FALSE otherwise).
`#assert_axioms continuity_body_zero_iff ⊆ {}`. Imports read-only.
-/
import Dregg2.Circuit.ChipNarrowLookup
import Dregg2.Circuit.Emit.AirNormalForm
import Dregg2.Circuit.Emit.EffectLowerCertified

namespace Dregg2.Circuit.Emit.MerkleMembershipEmit

open Dregg2.Circuit (Assignment Constraint Expr)
open Dregg2.Exec.CircuitEmit (EmittedExpr emitExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow)
open Dregg2.Circuit.DescriptorIR2
  (EffectVmDescriptor2 VmConstraint2 Lookup TableId chipLookupTupleNarrow poseidon2narrow
   CHIP_RATE CHIP_OUT_LANES emitVmJson2 WindowExpr)
open Dregg2.Circuit.EffectAirIR (EffectAir AirLeg LookupLeg WindowLeg PiPinLeg)
open Dregg2.Circuit.Emit.EffectLower (lowerAir lowerConstraint)
open Dregg2.Circuit.Emit.AirNormalForm
  (liftTuple wLinLoc gateBody gateBody_zero_iff normalFormOk)

set_option autoImplicit false

/-! ## §1 — The trace column layout (depth 2, 4-ary; a single logical row).

The whole membership fits ONE row (repeated to a power-of-two height on the Rust side); the two
Merkle levels live side by side, tied by the continuity gate. -/

/-- Level-0 path element (the membership leaf). -/
def LEAF : Nat := 0
/-- Level-0 siblings (the three other children of the leaf's parent). -/
def SIB0A : Nat := 1
def SIB0B : Nat := 2
def SIB0C : Nat := 3
/-- Level-0 parent digest = `hash_4_to_1(leaf, sib0a, sib0b, sib0c)` (chip lookup out0). -/
def PARENT0 : Nat := 4
/-- Level-1 path element (the chained input; the continuity gate forces `CUR1 = PARENT0`). -/
def CUR1 : Nat := 5
/-- Level-1 siblings. -/
def SIB1A : Nat := 6
def SIB1B : Nat := 7
def SIB1C : Nat := 8
/-- Level-1 parent digest = the ROOT = `hash_4_to_1(cur1, sib1a, sib1b, sib1c)` (chip lookup out0). -/
def PARENT1 : Nat := 9

/-- Total main-trace width: 10 base columns. The 2 x 7 exposed permutation lane columns the WIDE
`TID_P2` tuples carried are GONE (E7 narrowing, `ChipNarrowLookup.lean`) — they were referenced only
at lane positions 18..24 of the 25-wide tuples and entered no soundness conclusion. -/
def MEMBERSHIP_WIDTH : Nat := 10

/-- The public root is the single PI slot. -/
def ROOT_PI : Nat := 0

/-! ## §2 — ⚑ THE SOURCE: an `EffectAir` the compiler lowers (child→parent chip lookups ·
continuity · root pin · last-row fix).

This is the descriptor's AUTHORSHIP. Nothing below hand-writes a `VmConstraint2`; §2a names the
lowered forms so the downstream refinement modules (`MerkleMembershipRefine`,
`MerkleMembershipRung2`) keep their vocabulary, and `merkleDesc_constraints` proves by `rfl` that
those names ARE the compiler's output in order. -/

/-- The level-0 `child → parent` step: an arity-4 `Poseidon2Chip` lookup absorbing
`[leaf, sib0a, sib0b, sib0c]`, binding out0 to `PARENT0`.

⚠ The tuple is the EXISTING `chipLookupTupleNarrow` builder, lifted into the compiler's source
grammar by `AirNormalForm.liftTuple`. Lookup tuples are deliberately OUTSIDE the normal form (the
chip bus is keyed on the bare tuple shape), and `liftTuple_emit` proves the lift emits the same
bytes — so re-emission moves this descriptor's GATE bytes and nothing else. -/
def level0Leg : LookupLeg :=
  { table := poseidon2narrow
  , tuple := liftTuple
      (chipLookupTupleNarrow [.var LEAF, .var SIB0A, .var SIB0B, .var SIB0C] PARENT0) }

/-- The level-1 `child → parent` step, binding out0 to `PARENT1` (the root). -/
def level1Leg : LookupLeg :=
  { table := poseidon2narrow
  , tuple := liftTuple
      (chipLookupTupleNarrow [.var CUR1, .var SIB1A, .var SIB1B, .var SIB1C] PARENT1) }

/-- **The chain-continuity SOURCE equation**: `CUR1 = PARENT0` — the next level's path input equals
this level's parent (the emitted twin of `poseidon2_air.rs`'s chain-continuity constraint). Written
as an EQUATION, not as a pre-normalized residual: turning `lhs = rhs` into a vanishing polynomial in
canonical form is the compiler's job (`EffectLower.constraintHead`). -/
def contSrc : Constraint := ⟨.var CUR1, .var PARENT0⟩

/-- The SAME residual on the window rail (`.loc` leaves), canonically rendered by
`AirNormalForm.wLinLoc`. The last-row fix lowers through `windowToLocal?`, which is structure-
preserving, so this is where the boundary body's canonical shape is chosen. -/
def contWindow : WindowExpr := wLinLoc [(1, CUR1), (-1, PARENT0)] 0

/-- ⚑ **THE AIR SOURCE.** Five legs, IN EMISSION ORDER — lookup · lookup · gate · pin · window.
This descriptor is the one `EffectAirIR` names as the reason the leg list is ONE ORDERED list: it
interleaves a gate and a PI pin between and after its lookups, which four parallel lists could not
express. -/
def merkleAir : EffectAir :=
  { legs := [ .lookup level0Leg
            , .lookup level1Leg
            , .gate contSrc
            , .pin ⟨VmRow.first, PARENT1, ROOT_PI⟩
            , .window ⟨.last, contWindow⟩ ] }

-- The source block is main-rail expressible, decided on the emitted predicate.
#guard merkleAir.mainRailOk == true
#guard merkleAir.legs.length == 5
#guard merkleAir.lookupCount == 2
#guard merkleAir.pinsFit 1 == true

/-- ⚑ **THE TIED SOURCE** — `merkleAir` carrying its two decidable verdicts in its TYPE:
`mainRailOk` (main-rail expressible) and `pinsTied` (every published column is DERIVED by another
leg). A `TiedAir` cannot be built for a block that publishes a column nothing else constrains, so a
decorative pin is unrepresentable here rather than detectable by a census afterwards. -/
def merkleTiedAir : Dregg2.Circuit.Emit.EffectLower.TiedAir where
  air := merkleAir

/-- **`merkleMembershipDesc`** — the depth-2, 4-ary Poseidon2 Merkle-membership descriptor,
**COMPILED from `merkleAir`**. Two child→parent chip lookups, the level-tying continuity gate, the
root pin, and the last-row fix. The chip table (`TID_P2_NARROW`) is IMPLICITLY present
(Presence-detected from the lookups), so `tables` is empty exactly as the working `node8`/`deco`
descriptors leave it. The level-tie is enforced on EVERY row: the transition gate covers rows
`0..n-2` and the last-row boundary covers the last row (so a height-1 trace is not
under-constrained). -/
def merkleMembershipDesc : EffectVmDescriptor2 :=
  (Dregg2.Circuit.Emit.EffectLower.lowerTiedAir
    "merkle-membership-depth2-4ary::poseidon2-v1" MEMBERSHIP_WIDTH 1 [] merkleTiedAir).val

/-- ⚑ **THE CERTIFICATE, produced by the emit.** Every leg of the source is FORCED by the emitted
descriptor's constraints on any row window that satisfies them — `AirLeg.forces`, stated in the
SOURCE's vocabulary and never mentioning the lowering, so it is not `P → P`. Not re-derived here.

**Zero bytes move**: `lowerTiedAir … |>.val` is `lowerAir …` by `rfl`. -/
theorem merkleMembershipDesc_certified :
    Dregg2.Circuit.Emit.EffectLower.CertifiedRefines merkleMembershipDesc [] merkleAir :=
  (Dregg2.Circuit.Emit.EffectLower.lowerTiedAir
    "merkle-membership-depth2-4ary::poseidon2-v1" MEMBERSHIP_WIDTH 1 [] merkleTiedAir).property

/-- ⚑ **THE ZERO.** The certified lowering emits the term the bare lowering emitted, by `rfl` — so
the migration changed what this definition PROVES, not what it PRODUCES. No re-emit, no VK rotation.
Also the unfolding lemma for the cost/shape proofs below, which reason through `lowerAir`. -/
theorem merkleMembershipDesc_eq_lowerAir :
    merkleMembershipDesc = Dregg2.Circuit.Emit.EffectLower.lowerAir "merkle-membership-depth2-4ary::poseidon2-v1" MEMBERSHIP_WIDTH 1 [] merkleAir := rfl

/-! ### §2a — the lowered constraints, NAMED (no hand-written literal survives). -/

/-- The chain-continuity gate body, **as the compiler renders it**: `1·CUR1 + (−1)·PARENT0`. -/
def contBody : EmittedExpr := gateBody contSrc

/-- The level-0 chip lookup, as lowered. -/
def level0Lookup : VmConstraint2 := .lookup ⟨poseidon2narrow, level0Leg.tuple.map emitExpr⟩
/-- The level-1 chip lookup, as lowered. -/
def level1Lookup : VmConstraint2 := .lookup ⟨poseidon2narrow, level1Leg.tuple.map emitExpr⟩

/-- The chain-continuity Base gate — a `when_transition` constraint (vacuous on the LAST row). It
binds `CUR1 = PARENT0` on rows `0..n-2`. -/
def continuityGate : VmConstraint2 := lowerConstraint contSrc

/-- **The last-row continuity fix** (`merkleLastContFix`, the `adjLastOrderFix` shape from commit
`0f8d478b2`). The transition `.gate` above is VACUOUS on the last row (`holdsVm … isLast=true (.gate _)
= True`, `EffectVmEmit.lean:465`), so on a height-1 trace — where row 0 IS the last row — `CUR1` is
FREE, decoupling the level-0 (leaf) side from the level-1 (root) side and admitting a forged
non-member leaf (`MerkleMembershipRung2.forgeTrace`). This `.boundary VmRow.last` counterpart fires on
the last row, so together with the transition `.gate` the level-tie `CUR1 = PARENT0` is enforced on
EVERY row — matching the deployed every-row `assert_zero` lowering. -/
def continuityLastFix : VmConstraint2 := .base (.boundary VmRow.last contBody)

/-- The root pin: `PARENT1` (last parent) equals the public root PI on the first row. -/
def rootPin : VmConstraint2 := .base (.piBinding VmRow.first PARENT1 ROOT_PI)

/-- ⚑ **THE COMPILER'S OUTPUT IS THAT LIST** — by `rfl`, the same term, not a sibling proved equal.
Every downstream statement quantifying over `merkleMembershipDesc.constraints` is therefore a
statement about the compiled object, and the `.boundary` body the window leg lowered to IS the gate
body the `Head` normalizer produced (the two rails agree on the rendering, which is the whole point
of the corpus invariant). -/
theorem merkleDesc_constraints :
    merkleMembershipDesc.constraints
      = [level0Lookup, level1Lookup, continuityGate, rootPin, continuityLastFix] := rfl

/-- …and the descriptor IS `lowerAir` of the source. -/
theorem merkleMembershipDesc_is_lowering :
    merkleMembershipDesc
      = lowerAir "merkle-membership-depth2-4ary::poseidon2-v1" MEMBERSHIP_WIDTH 1 [] merkleAir :=
  rfl

-- ⚑ THE CORPUS INVARIANT, DECIDED ON THIS DESCRIPTOR: every arithmetic body is in the canonical
-- normal form — the gate the hand-written literal could not pass.
#guard normalFormOk merkleMembershipDesc == true

/-! ## §3 — The byte-pinned wire golden (the Rust decoder ingests THIS string).

THE EQUALITY-GATE ANCHOR: this exact string is embedded verbatim in
`circuit-prove/tests/merkle_membership_emit_gate.rs` (`GOLDEN_JSON`), decoded there via
`parse_vm_descriptor2`, and proven. A drift on either side breaks THIS `#guard` (Lean) or the Rust
`assert_eq!(decoded, hand_built)` — neither can silently diverge. -/

#guard emitVmJson2 merkleMembershipDesc ==
  "{\"name\":\"merkle-membership-depth2-4ary::poseidon2-v1\",\"ir\":2,\"trace_width\":10,\"public_input_count\":1,\"challenges\":0,\"tables\":[],\"constraints\":[{\"t\":\"lookup\",\"table\":8,\"tuple\":[{\"t\":\"const\",\"v\":4},{\"t\":\"var\",\"v\":0},{\"t\":\"var\",\"v\":1},{\"t\":\"var\",\"v\":2},{\"t\":\"var\",\"v\":3},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"var\",\"v\":4}]},{\"t\":\"lookup\",\"table\":8,\"tuple\":[{\"t\":\"const\",\"v\":4},{\"t\":\"var\",\"v\":5},{\"t\":\"var\",\"v\":6},{\"t\":\"var\",\"v\":7},{\"t\":\"var\",\"v\":8},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"var\",\"v\":9}]},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"var\",\"v\":5}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":4}}}},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":9,\"pi_index\":0},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"var\",\"v\":5}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":4}}}}],\"hash_sites\":[],\"ranges\":[]}"

/-! ## §4 — A genuinely-proven, non-vacuous semantic lemma (the continuity gate teeth).

The gate body is zero EXACTLY when the levels chain (`CUR1 = PARENT0`) — TRUE when they agree,
FALSE when they do not. This is the Lean face of the chain-continuity the emitted `.gate` enforces
row-for-row in the Rust Ir2 main AIR (`descriptor_ir2.rs:2210`).

⚑ RE-ESTABLISHED OVER THE COMPILED BODY. The statement is LITERALLY unchanged from the
hand-written era; only `contBody`'s definition moved (hand-written `EmittedExpr` → `gateBody
contSrc`, the compiler's rendering). The proof now runs through `AirNormalForm.gateBody_zero_iff`,
which is the generic tooth — so this obligation is discharged against the object the wire bytes
carry, not against a lookalike. -/

theorem continuity_body_zero_iff (a : Assignment) :
    contBody.eval a = 0 ↔ a CUR1 = a PARENT0 := by
  simp only [contBody]
  rw [gateBody_zero_iff]
  simp [contSrc, Expr.eval]

-- Non-vacuity witnesses: the gate ACCEPTS a chained assignment and REJECTS an unchained one.
#guard decide (contBody.eval (fun i => if i = CUR1 ∨ i = PARENT0 then 7 else 0) = 0)
#guard decide (¬ (contBody.eval (fun i => if i = CUR1 then 7 else 0) = 0))

-- Shape pins.
#guard merkleMembershipDesc.traceWidth == MEMBERSHIP_WIDTH
#guard merkleMembershipDesc.piCount == 1
#guard merkleMembershipDesc.constraints.length == 5
#guard (chipLookupTupleNarrow [.var LEAF, .var SIB0A, .var SIB0B, .var SIB0C] PARENT0).length
         == CHIP_RATE + 1 + 1
-- The narrowing dropped exactly 2 x (CHIP_OUT_LANES - 1) = 14 main columns for the same two forced
-- digest equations.
#guard MEMBERSHIP_WIDTH + 2 * (CHIP_OUT_LANES - 1) == 24
#guard poseidon2narrow.wireId == 8

#assert_axioms continuity_body_zero_iff

end Dregg2.Circuit.Emit.MerkleMembershipEmit
