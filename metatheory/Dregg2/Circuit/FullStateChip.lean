import Dregg2.Circuit.DescriptorIR2

/-
# FullStateChip — the arbitrary 16-in / 16-out Poseidon2 permutation bus

The deployed `hash_many_8` sponge cannot be replayed from the legacy chip's eight exposed output
lanes: after every four-felt absorb, the next permutation depends on all sixteen lanes of the prior
state.  This file gives that exact transition a fixed additive table identity and derives its
lookup soundness from `DescriptorIR2.chip_lookup_sound_N`.

The wire tuple is `16 :: state₁₆ ++ permutation(state₁₆)`: the leading literal is a fixed width tag,
not a variable absorb arity.  Consequently every state lane is genuine input — including capacity
lanes — and all sixteen next-state lanes are forced.  Rust serves this relation from a separately
present `ChipState16` AIR, so descriptors that never mention this table retain their existing AIR
family and verifier-key shape.
-/

namespace Dregg2.Circuit.DescriptorIR2

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)

/-- The full permutation state width.  Pinned to the existing chip's deployed width. -/
def CHIP_STATE_LANES : Nat := CHIP_RATE

/-- The state16 bus uses the next free fixed custom slot: `.custom 4` serializes to wire id 9.
Wire id 8 (`.custom 3`) is already the narrow single-output chip bus. -/
def poseidon2state16 : TableId := .custom 4

/-- One genuine full-state permutation row.  `chipRowN` supplies the fixed length tag and the
same padding convention; under `state.length = 16 = CHIP_RATE` the padding suffix is empty. -/
def chipRowState16 (permOut : List ℤ → List ℤ) (state : List ℤ) : List ℤ :=
  chipRowN permOut state

/-- The corresponding lookup tuple over main-trace expressions and sixteen next-state columns. -/
def chipLookupTupleState16 (state : List EmittedExpr) (nextStateCols : List Nat) :
    List EmittedExpr :=
  chipLookupTupleN state nextStateCols

/-- Semantic soundness of the fixed state16 table.  Both sides have exactly sixteen lanes; every
row is the genuine permutation transition for its complete input state. -/
def ChipTableSoundState16 (permOut : List ℤ → List ℤ) (tbl : Table) : Prop :=
  ∀ r ∈ tbl, ∃ state : List ℤ,
    state.length = CHIP_STATE_LANES ∧
    (permOut state).length = CHIP_STATE_LANES ∧
    r = chipRowState16 permOut state

/-- A state16-sound table is in particular sound for the generic full-output chip lever. -/
theorem ChipTableSoundState16.toSoundN {permOut : List ℤ → List ℤ} {tbl : Table}
    (h : ChipTableSoundState16 permOut tbl) : ChipTableSoundN permOut tbl := by
  intro r hr
  obtain ⟨state, hstate, _hout, hrow⟩ := h r hr
  exact ⟨state, by simpa [CHIP_STATE_LANES] using hstate.le, hrow⟩

/-- **THE FULL-STATE LEVER.** Membership of a fixed 33-felt lookup forces all sixteen output
columns to equal the genuine permutation of all sixteen evaluated input-state expressions.  In
particular a mutation of any high capacity/output lane is excluded, not merely a mutation of the
first eight squeezed lanes exposed by the legacy bus. -/
theorem chip_lookup_sound_state16 (permOut : List ℤ → List ℤ) (tbl : Table)
    (hSound : ChipTableSoundState16 permOut tbl)
    (a : Assignment) (state : List EmittedExpr) (nextStateCols : List Nat)
    (hstate : state.length = CHIP_STATE_LANES)
    (hmem : (chipLookupTupleState16 state nextStateCols).map (·.eval a) ∈ tbl) :
    nextStateCols.map a = permOut (state.map (·.eval a)) := by
  apply chip_lookup_sound_N permOut tbl hSound.toSoundN a state nextStateCols
  · simpa [CHIP_STATE_LANES] using hstate.le
  · exact hmem

/-- The declared table carried by a state16-using descriptor.  Rust validates this exact name,
wire id, arity, and Poseidon2 parameter semantics before assembly. -/
def poseidon2State16ChipTableDef : TableDef :=
  ⟨poseidon2state16, "poseidon2_state16_chip",
    1 + CHIP_STATE_LANES + CHIP_STATE_LANES, .permutation⟩

-- Wire/shape tripwires: id 9, sixteen full input lanes, sixteen full output lanes, 33 total.
#guard CHIP_STATE_LANES == 16
#guard poseidon2state16.wireId == 9
#guard poseidon2State16ChipTableDef.arity == 33
#guard poseidon2State16ChipTableDef.arity == 1 + CHIP_STATE_LANES + CHIP_STATE_LANES
#guard (chipRowState16 (fun _ => List.range CHIP_STATE_LANES |>.map Int.ofNat)
  (List.replicate CHIP_STATE_LANES 0)).length == 33
#guard (chipLookupTupleState16
  ((List.range CHIP_STATE_LANES).map .var)
  (List.range CHIP_STATE_LANES |>.map (32 + ·))).length == 33

-- The new table identity is disjoint from the legacy wide and narrow chip receivers.
#guard poseidon2state16.wireId != TableId.poseidon2.wireId
#guard poseidon2state16.wireId != 8

#assert_axioms ChipTableSoundState16.toSoundN
#assert_axioms chip_lookup_sound_state16

end Dregg2.Circuit.DescriptorIR2
