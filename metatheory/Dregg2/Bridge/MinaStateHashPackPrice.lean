/-
# `Dregg2.Bridge.MinaStateHashPackPrice` — **what `pack_to_fields` would cost as an AIR**, measured
on the real block and stated as named theorems.

## ⚑ WHY THIS FILE EXISTS, AND THE ANSWER IT GIVES

The phase-1 (Fp) transcript leg was briefed with an unpriced item:

> *"phase-1 absorbs group coordinates, and the state-hash preimage is `Random_oracle.Input.Chunked`
> … **The `pack_to_fields` bit-packing has no AIR.** Phase-2 never needed it — it absorbs whole
> field elements. Price this first; it may dominate."*

Priced. **Two answers, and the first one is the load-bearing one.**

  1. ⚑⚑ **`pack_to_fields` IS NOT ON THE PHASE-1 TRANSCRIPT PATH AT ALL.** Phase 1 absorbs WHOLE
     field elements: `DefaultFqSponge::absorb_g` pushes a point's `x` then its `y` as base-field
     elements (`poseidon/src/sponge.rs`), so the tape is 37 + 2 + 14 = 53 `Fp` elements and not one
     bit is packed. `the_phase1_tape_is_whole_field_elements` is that fact about the deployed tape,
     and `MinaRealBlockTranscript.wrapPhase1` reproducing block 539508's published β/γ/α′/ζ′/digest
     from exactly those 53 numbers is the reality gate on it: no packing step could be missing from
     a derivation that already lands on o1-labs' own oracle output.
  2. **Where it DOES live — the STATE-HASH preimage — it costs 3.8% of the object it belongs to.**
     `Body.to_input` on the real devnet block is **38 whole field elements + 819 packed chunks
     (2 381 bits)**, packing to **49 field elements** (38 + 11), absorbed at rate 2 as **26 Kimchi
     permutations**. On the deployed machine a permutation is **1 650 instructions**
     (`MinaWrapVerifierSponge.ROWS_PER_ROUND = 30`), so the sponge is **42 900 rows** and the
     packing's shift-and-add chain is **2 × 819 = 1 638**. `pack_to_fields_does_not_dominate`.

⚑ **AND THE PACKING IS A STRAIGHT-LINE PROGRAM, WHICH IS WHY 1 638 IS THE WHOLE ANSWER.**
`packStep`'s boundary test is `n + accN < 255` on the DECLARED WIDTH, evaluated before the item is
placed — it never reads the item's VALUE or the accumulator. `the_packing_control_flow_reads_only_
the_width` is that, generally. So the chunk boundaries are fixed by the block's SHAPE, the emitted
program has no branches, and the AIR is `acc := acc·2^n` then `acc := acc + x` per item on the
machine that already exists. **No new gate shape, no bit-decomposition rung, no chip.**

⚑ **WHAT WOULD STILL BE OWED** is the injectivity side, and it is small: each chunk must be shown
`< 2^n` or the packing is not injective and a prover smuggles high bits across a boundary.
`the_chunk_widths_are_almost_all_boolean` measures the distribution — **781 of the 819 chunks are
ONE BIT** (the two 32-byte digests' 512 bits and the VRF output's 253), 26 are 32-bit and 12 are
64-bit. A one-bit assertion is `x(x−1) = 0`; the 38 wide ones are `n % 8 == 0`, so on this machine
they are "the high limbs are zero" and cost no decomposition at all. The range machinery's nibble
path is not needed.

## ⚑ SUBSTRATE

This file authors **NO AIR**. It is a MEASUREMENT of an existing `List Nat → List Nat` function
(`MinaStateHashDerive.packToFields`, itself a transcription of `random_oracle_input.ml:59-75` and
openmina's `poseidon/src/hash.rs:139-163`) and an arithmetic comparison against a row count the
Pasta cone already emits. Every figure is a named theorem; there is no `#guard` here.
-/
import Dregg2.Bridge.MinaStateHashRealBlock
import Dregg2.Circuit.Emit.MinaWrapVerifierSponge
import Dregg2.Circuit.Emit.MinaRealBlockTranscript

namespace Dregg2.Bridge.MinaStateHashPackPrice

open Dregg2.Bridge.MinaBinprot
open Dregg2.Bridge.MinaStateHashDerive
open Dregg2.Bridge.MinaStateHashRealBlock

set_option autoImplicit false
-- ⚑ A `set_option` does not cross an import: the Poseidon-free reductions here are the parser and
-- the SHA-256, and `MinaStateHashDerive`'s own note measures those at 4.3 s inside this depth.
set_option maxRecDepth 1000000

/-! ## §1 — THE CONTROL FLOW READS ONLY THE WIDTHS.

⚑ This is the structural half of the price, and it is general — not a fact about this block. -/

/-- ⚑⚑ **THE PACKING'S BRANCH NEVER READS A VALUE.** One step of `pack_to_fields`' fold emits a
field element exactly when `n + accN` reaches `fieldSizeInBits`, and the new accumulator width is a
function of `(n, accN)` alone. The item's value `x` and the accumulator `acc` appear in the DATA and
never in the CONTROL.

Consequence, and it is the whole reason §2's number is the whole answer: the chunk boundaries of a
Mina protocol state are fixed by its SHAPE, so the emitted program is STRAIGHT-LINE — two
instructions per chunk on the machine that already exists, no branch, no new gate. -/
theorem the_packing_control_flow_reads_only_the_width (out : List Nat) (acc accN x n : Nat) :
    (packStep (out, acc, accN) (x, n)).1.length
        = (if n + accN < fieldSizeInBits then out.length else out.length + 1)
    ∧ (packStep (out, acc, accN) (x, n)).2.2
        = (if n + accN < fieldSizeInBits then n + accN else n) := by
  unfold packStep
  by_cases h : n + accN < fieldSizeInBits <;> simp [h]

/-- …and the same step at a DIFFERENT value with the SAME width takes the SAME branch. Stated
separately so "data-independent" is a comparison between two runs rather than a reading of one. -/
theorem the_packing_step_is_width_determined (out : List Nat) (acc accN x y n : Nat) :
    (packStep (out, acc, accN) (x, n)).1.length = (packStep (out, acc, accN) (y, n)).1.length
    ∧ (packStep (out, acc, accN) (x, n)).2.2 = (packStep (out, acc, accN) (y, n)).2.2 := by
  refine ⟨?_, ?_⟩ <;>
    [ rw [(the_packing_control_flow_reads_only_the_width out acc accN x n).1,
          (the_packing_control_flow_reads_only_the_width out acc accN y n).1];
      rw [(the_packing_control_flow_reads_only_the_width out acc accN x n).2,
          (the_packing_control_flow_reads_only_the_width out acc accN y n).2] ]

/-! ## §2 — THE SHAPE OF THE REAL BLOCK'S PREIMAGE. -/

/-- `Body.to_input` of the real devnet block (540221), decoded from its own wire bytes. -/
def bodyInput : Inp :=
  match decodeProtocolStateRaw devnetParent with
  | some (ps, _) => bodyI ps
  | none => Inp.nil

/-- The declared widths of the packed stream, in append order. -/
def chunkWidths : List Nat := bodyInput.packeds.map Prod.snd

/-- ⚑ **38 WHOLE FIELD ELEMENTS AND 819 PACKED CHUNKS, 2 381 BITS.** The figure
`MinaStateHashDerive`'s header quotes, now a theorem rather than a docblock number. -/
theorem the_body_preimage_is_38_fields_and_819_chunks :
    bodyInput.fields.length = 38
    ∧ bodyInput.packeds.length = 819
    ∧ chunkWidths.foldl (· + ·) 0 = 2381 := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

/-- ⚑⚑ **781 OF THE 819 CHUNKS ARE ONE BIT.** The two 32-byte digests contribute 8 bits each
(`bytesI` on `nonSnarkDigest` and `body_reference` — 512 chunks), the VRF output 253, and the rest
are the scattered booleans (`Sgn`, `is_odd`, `success`, `has_ancestor`, …). Only **38** chunks are
wide: 26 at 32 bits and 12 at 64.

This is the number that decides the injectivity cost. A one-bit range assertion is `x(x−1) = 0`;
the 38 wide ones have `n % 8 == 0`, so on the deployed 8-bit-limb machine they are "the high limbs
are zero" and need no decomposition. **The nibble/range machinery is not on this critical path.** -/
theorem the_chunk_widths_are_almost_all_boolean :
    (chunkWidths.filter (fun w => w == 1)).length = 781
    ∧ (chunkWidths.filter (fun w => w == 32)).length = 26
    ∧ (chunkWidths.filter (fun w => w == 64)).length = 12
    ∧ (chunkWidths.filter (fun w => !(w == 1 || w == 32 || w == 64))).length = 0
    ∧ 781 + 26 + 12 = 819
    ∧ 781 * 1 + 26 * 32 + 12 * 64 = 2381 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> native_decide

/-- ⚑ **AND THE 2 381 BITS PACK INTO 11 FIELD ELEMENTS**, for 49 absorbed in total. Not 10: the
boundary rule is `< 255` tested BEFORE the item is placed, so a 254-bit chunk is the most that ever
lands and the tail is short. -/
theorem the_preimage_packs_to_49_field_elements :
    (packToFields bodyInput).length = 49
    ∧ (packToFields bodyInput).length - bodyInput.fields.length = 11 := by
  refine ⟨?_, ?_⟩ <;> native_decide

/-! ## §3 — THE PRICE, AGAINST THE ROW COUNT THE PASTA CONE ALREADY EMITS. -/

open Dregg2.Circuit.Emit.MinaWrapVerifierSponge (ROWS_PER_ROUND ROWS_PER_PERM_MEASURED)

/-- Absorbing `n` elements at rate 2 costs `⌈n/2⌉` permutations plus the closing squeeze. -/
def PERMS_FOR_BODY : Nat := (49 + 1) / 2 + 1

/-- The sponge half of a state-body hash, in emitted instructions. -/
def SPONGE_ROWS : Nat := PERMS_FOR_BODY * ROWS_PER_PERM_MEASURED

/-- ⚑ `acc := acc · 2^n` (a multiply by a ROM immediate) then `acc := acc + x` — **two instructions
per chunk on the machine that already exists.** No branch, by §1; no new gate shape. -/
def PACK_ROWS : Nat := 2 * 819

/-- ⚑⚑ **THE ANSWER: `pack_to_fields` DOES NOT DOMINATE — it is 3.8% of the sponge it feeds.**
26 permutations at 1 650 instructions is 42 900 rows; the packing is 1 638. Stated as the two
brackets rather than a rounded percentage, so the claim is checkable in the kernel. -/
theorem pack_to_fields_does_not_dominate :
    PERMS_FOR_BODY = 26
    ∧ ROWS_PER_PERM_MEASURED = 1650
    ∧ SPONGE_ROWS = 42900
    ∧ PACK_ROWS = 1638
    ∧ 100 * PACK_ROWS < 4 * SPONGE_ROWS
    ∧ 3 * SPONGE_ROWS < 100 * PACK_ROWS := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- ⚑ **AND THE COMPARISON THAT MATTERS MORE**: the whole state-hash derivation, packing included,
is **comparable to the phase-1 transcript chain this cone just emitted** — 27 links at 1 650 is
44 550 rows against 44 538. So the state-hash leg is not a different order of magnitude from a leg
that proves in minutes; it is the same size. -/
theorem the_state_hash_is_the_size_of_the_phase1_chain :
    SPONGE_ROWS + PACK_ROWS = 44538
    ∧ 27 * ROWS_PER_PERM_MEASURED = 44550
    ∧ SPONGE_ROWS + PACK_ROWS < 27 * ROWS_PER_PERM_MEASURED := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-! ## §4 — AND IT IS NOT ON THE PHASE-1 PATH.

⚑ The reason the price above is a note and not a blocker. -/

open Dregg2.Circuit.Emit.MinaRealBlockTranscript (fpTape ZCOMM_XY TCOMM_XY)

/-- ⚑⚑ **THE PHASE-1 TAPE IS 53 WHOLE FIELD ELEMENTS.** `absorb_g` pushes a commitment's `x` then
its `y` as base-field elements; nothing is packed, nothing is chunked, and every entry is a full
`Fp` element rather than a `(value, width)` pair. So the chunked-input machinery this file prices
belongs to the STATE-HASH preimage and has no part in the transcript leg.

The reality gate on the claim is `MinaRealBlockTranscript.wrapPhase1`, which reproduces block
539508's published β/γ/α′/ζ′ and `fq_digest` from exactly these 53 numbers: a derivation that lands
on o1-labs' own oracle output cannot be missing a packing step. -/
theorem the_phase1_tape_is_whole_field_elements :
    fpTape.length + ZCOMM_XY.length + TCOMM_XY.length = 53
    ∧ fpTape.length = 37
    ∧ (fpTape.all (fun x => decide (2 ^ 128 < x))) = true := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

#assert_axioms the_packing_control_flow_reads_only_the_width
#assert_axioms the_packing_step_is_width_determined
#assert_axioms pack_to_fields_does_not_dominate
#assert_axioms the_state_hash_is_the_size_of_the_phase1_chain
#assert_axioms the_phase1_tape_is_whole_field_elements

-- ⚑ COMPILER-TRUSTED, and said out loud: each reduces the 1 544-byte binprot parse, a two-block
-- SHA-256 and the whole 819-chunk assembly. `MinaStateHashDerive` §7 measures the kernel path for
-- the SAME object at 9.2 s, so these are convertible; they are compiled because a per-width tally
-- over 819 chunks is a `filter` the `decide` proof-term path has no reason to carry.
#assert_compiled the_body_preimage_is_38_fields_and_819_chunks
#assert_compiled the_chunk_widths_are_almost_all_boolean
#assert_compiled the_preimage_packs_to_49_field_elements

end Dregg2.Bridge.MinaStateHashPackPrice
