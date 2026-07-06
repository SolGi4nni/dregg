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

A `TID_P2` chip lookup with arity tag `4` and inputs `[c0,c1,c2,c3]` is served by the chip table's
narrow rate-4 seeding: `state[0..4] = c0..c3`, `state[4] = 4` (the arity tag), `state[5..] = 0`,
`out0 = permute(state)[0]`. That is EXACTLY `poseidon2::hash_4_to_1([c0,c1,c2,c3])`
(`circuit/src/descriptor_ir2.rs:3353` `chip_absorb_all_lanes(4, ..)[0]` — the Rust gate KATs this).
The chip AIR binds `out0` (and lanes 1..7) to the real permutation, so a lookup that names a forged
parent has no serving chip row → UNSAT. Every hash-carrying family (heap/fields/accumulator/cap/…)
depends on THIS arity→seeding→digest correspondence; here it is exercised end-to-end.

## Axiom hygiene

Definitional descriptor + a byte-pinned `#guard` on its wire string + one genuinely-proven,
non-vacuous semantic lemma (`continuity_body_zero_iff`, TRUE iff the levels chain, FALSE otherwise).
`#assert_axioms continuity_body_zero_iff ⊆ {}` (pure `omega`). NEW file; imports read-only.
-/
import Dregg2.Circuit.DescriptorIR2

namespace Dregg2.Circuit.Emit.MerkleMembershipEmit

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow)
open Dregg2.Circuit.DescriptorIR2
  (EffectVmDescriptor2 VmConstraint2 Lookup TableId chipLookupTuple CHIP_RATE CHIP_OUT_LANES
   emitVmJson2)

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

/-- The seven exposed permutation lane columns 1..7 of the level-`k` chip lookup (out0 is the
digest column above; the lanes are witnessed by the chip's `out[i] == lane[i]` equalities). -/
def LEVEL0_LANES : List Nat := [10, 11, 12, 13, 14, 15, 16]
def LEVEL1_LANES : List Nat := [17, 18, 19, 20, 21, 22, 23]

/-- Total main-trace width: 10 base columns + 7 + 7 chip lanes. -/
def MEMBERSHIP_WIDTH : Nat := 24

/-- The public root is the single PI slot. -/
def ROOT_PI : Nat := 0

/-! ## §2 — The constraint list (child→parent chip lookups · continuity · root pin). -/

/-- The level-0 `child → parent` step: an arity-4 `Poseidon2Chip` lookup absorbing
`[leaf, sib0a, sib0b, sib0c]`, binding out0 to `PARENT0`. -/
def level0Lookup : VmConstraint2 :=
  .lookup ⟨TableId.poseidon2,
    chipLookupTuple [.var LEAF, .var SIB0A, .var SIB0B, .var SIB0C] PARENT0 LEVEL0_LANES⟩

/-- The level-1 `child → parent` step: an arity-4 `Poseidon2Chip` lookup absorbing
`[cur1, sib1a, sib1b, sib1c]`, binding out0 to `PARENT1` (the root). -/
def level1Lookup : VmConstraint2 :=
  .lookup ⟨TableId.poseidon2,
    chipLookupTuple [.var CUR1, .var SIB1A, .var SIB1B, .var SIB1C] PARENT1 LEVEL1_LANES⟩

/-- The chain-continuity gate body: `CUR1 - PARENT0` (the next level's path input equals this
level's parent — the emitted twin of `poseidon2_air.rs`'s chain-continuity constraint). -/
def contBody : EmittedExpr := .add (.var CUR1) (.mul (.const (-1)) (.var PARENT0))

/-- The chain-continuity Base gate. -/
def continuityGate : VmConstraint2 := .base (.gate contBody)

/-- The root pin: `PARENT1` (last parent) equals the public root PI on the first row. -/
def rootPin : VmConstraint2 := .base (.piBinding VmRow.first PARENT1 ROOT_PI)

/-- **`merkleMembershipDesc`** — the depth-2, 4-ary Poseidon2 Merkle-membership descriptor.
Constraints: two child→parent chip lookups, the level-tying continuity gate, and the root pin.
The chip table (`TID_P2`) is IMPLICITLY present (Presence-detected from the lookups), so `tables`
is empty exactly as the working `node8`/`deco` descriptors leave it. -/
def merkleMembershipDesc : EffectVmDescriptor2 :=
  { name        := "merkle-membership-depth2-4ary::poseidon2-v1"
  , traceWidth  := MEMBERSHIP_WIDTH
  , piCount     := 1
  , tables      := []
  , constraints := [level0Lookup, level1Lookup, continuityGate, rootPin]
  , hashSites   := []
  , ranges      := [] }

/-! ## §3 — The byte-pinned wire golden (the Rust decoder ingests THIS string).

THE EQUALITY-GATE ANCHOR: this exact string is embedded verbatim in
`circuit-prove/tests/merkle_membership_emit_gate.rs` (`GOLDEN_JSON`), decoded there via
`parse_vm_descriptor2`, and proven. A drift on either side breaks THIS `#guard` (Lean) or the Rust
`assert_eq!(decoded, hand_built)` — neither can silently diverge. -/

#guard emitVmJson2 merkleMembershipDesc ==
  "{\"name\":\"merkle-membership-depth2-4ary::poseidon2-v1\",\"ir\":2,\"trace_width\":24,\"public_input_count\":1,\"tables\":[],\"constraints\":[{\"t\":\"lookup\",\"table\":1,\"tuple\":[{\"t\":\"const\",\"v\":4},{\"t\":\"var\",\"v\":0},{\"t\":\"var\",\"v\":1},{\"t\":\"var\",\"v\":2},{\"t\":\"var\",\"v\":3},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"var\",\"v\":4},{\"t\":\"var\",\"v\":10},{\"t\":\"var\",\"v\":11},{\"t\":\"var\",\"v\":12},{\"t\":\"var\",\"v\":13},{\"t\":\"var\",\"v\":14},{\"t\":\"var\",\"v\":15},{\"t\":\"var\",\"v\":16}]},{\"t\":\"lookup\",\"table\":1,\"tuple\":[{\"t\":\"const\",\"v\":4},{\"t\":\"var\",\"v\":5},{\"t\":\"var\",\"v\":6},{\"t\":\"var\",\"v\":7},{\"t\":\"var\",\"v\":8},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"var\",\"v\":9},{\"t\":\"var\",\"v\":17},{\"t\":\"var\",\"v\":18},{\"t\":\"var\",\"v\":19},{\"t\":\"var\",\"v\":20},{\"t\":\"var\",\"v\":21},{\"t\":\"var\",\"v\":22},{\"t\":\"var\",\"v\":23}]},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":5},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":4}}}},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":9,\"pi_index\":0}],\"hash_sites\":[],\"ranges\":[]}"

/-! ## §4 — A genuinely-proven, non-vacuous semantic lemma (the continuity gate teeth).

The gate body is zero EXACTLY when the levels chain (`CUR1 = PARENT0`) — TRUE when they agree,
FALSE when they do not. This is the Lean face of the chain-continuity the emitted `.gate` enforces
row-for-row in the Rust Ir2 main AIR (`descriptor_ir2.rs:2210`). -/

theorem continuity_body_zero_iff (a : Assignment) :
    contBody.eval a = 0 ↔ a CUR1 = a PARENT0 := by
  simp only [contBody, EmittedExpr.eval]
  constructor <;> intro h <;> omega

-- Non-vacuity witnesses: the gate ACCEPTS a chained assignment and REJECTS an unchained one.
#guard decide (contBody.eval (fun i => if i = CUR1 ∨ i = PARENT0 then 7 else 0) = 0)
#guard decide (¬ (contBody.eval (fun i => if i = CUR1 then 7 else 0) = 0))

-- Shape pins.
#guard merkleMembershipDesc.traceWidth == MEMBERSHIP_WIDTH
#guard merkleMembershipDesc.piCount == 1
#guard merkleMembershipDesc.constraints.length == 4
#guard (chipLookupTuple [.var LEAF, .var SIB0A, .var SIB0B, .var SIB0C] PARENT0 LEVEL0_LANES).length
         == CHIP_RATE + 1 + CHIP_OUT_LANES

#assert_axioms continuity_body_zero_iff

end Dregg2.Circuit.Emit.MerkleMembershipEmit
