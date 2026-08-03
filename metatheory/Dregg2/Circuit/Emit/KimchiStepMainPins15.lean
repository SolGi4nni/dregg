/-
`KimchiStepMain` pins — §20: **`multiscale_known`'s PER-WORD SCALAR WIDTHS**, the retirement of
simplification #2.

⚑ NAMED THEOREMS, NOT `#guard` (`metatheory/docs/GUARD-DISCIPLINE.md`): a `#guard` is the same
`unsafe evalExpr` a `native_decide` theorem runs, minus the name, the term and the axiom record.
This module adds no guard, so no baseline row moves.

## WHAT §20 IS ABOUT

Until 2026-08-03 `StepShape` carried a single `msmChunks = 26` and R3 ran all forty `var_base_mul`
ladders at it. `multiscale_known`'s scalars are the previous proof's PACKED WRAP STATEMENT
(`step_verifier.ml:543-544,1236-1251`) and `Spec.pack` gives every word its own width
(`spec.ml:305-395`), so a uniform 26 was two errors at once: twenty-five chunks of LEADING ZEROS on
every challenge-shaped word would be needed to reach 51, and the eight 255-bit words were running at
half their width. The width vector is `msmBits` / `msmChunksAt` in `…Core` §1b, read off
`Types.Wrap.Statement.In_circuit.spec` (`composition_types.ml:785-823`).

## ⚑ THE REALITY GATE — WHY THIS IS NOT A DERIVATION CHECKING ITSELF

`msmBits` is derived from OCaml *source*. `x_hat_widths_are_minas_own_compiled_ladders` compares it
against the ladder widths of **`step-zkapp-proved`**, an o1-labs CIRCUIT BLOB — Mina's own compiled
step circuit, the same artifact `bridge/mina-zkapp/scripts/stepmain-region-conformance.mjs` grades
against. Measured there, the `x_hat` cluster is **31 ladders**, chunk widths in row order

    51,51,51,51,51, 26,26,26,26,26, 51,51,51, 26×16, 2, 26        (982 chunks)

and the list below is that sequence, element for element. Two independent objects: an OCaml `spec`
read by hand, and a compiled circuit measured by a script that has never seen this file.

⚑ **AND WHAT WAS STILL NOT CLOSED IS CLOSED — §21, `…Pins16`, 2026-08-03.** This paragraph read:
"Term `i`'s scalar is still `vN (msmChal i) emsRows` — a shared transcript challenge — and NOT Wrap
statement word `i`; a 255-bit width over a value that is structurally `< 2¹²⁸` is shape-faithful and
semantically empty until the provenance lands too. And the nine one-bit words … still carry their
seed `CompleteAdd` and their fold add here." Both halves landed: `StepShape.msmChal` is DELETED and
`vSN i (msmChunksAt i)` is `stmtVar i` (Core §2c), and `msmRows` runs `multiscale_known`'s
NON-CONSTANT partition, so the nine emit no base, no seed and no add. The residue §21 leaves is
THREE words with no in-circuit source (10, 11, 39), named at their own cells.
-/
import Dregg2.Circuit.Emit.KimchiStepMainFixture

namespace Dregg2.Circuit.Emit.KimchiStepMain

open Dregg2.Circuit.Emit.KimchiTarget (KGateType)

set_option autoImplicit false
set_option maxRecDepth 100000

/-! ### `chunks_needed`, and the four widths it is applied to. -/

/-- ⚑ `Ops.chunks_needed ~num_bits` at `bits_per_chunk = 5` (`plonk_curve_ops.ml:64-68`), on the
four `num_bits:(n − 1)` values the statement's basics produce. **`0` at one bit** — that is the
whole reason a faithful `x_hat` has 31 ladders and not 40, and it falls out of upstream's own
formula rather than out of a special case. -/
theorem chunks_needed_is_upstreams_own_at_the_four_widths :
    (chunksNeeded (W_FIELD - 1) = 51 ∧ chunksNeeded (W_CHAL - 1) = 26
     ∧ chunksNeeded (W_BRANCH - 1) = 2 ∧ chunksNeeded (W_BOOL - 1) = 0) := by
  native_decide
#assert_compiled chunks_needed_is_upstreams_own_at_the_four_widths

/-- The four widths are `Spec.pack`'s own: `Field`/`Digest` at `Field.size_in_bits`, `Challenge`
(and `Scalar Challenge`, and `Bulletproof_challenge`) at `Challenge.length = 64 · 2`, `Branch_data`
at `length_in_bits`, `Bool` at one. -/
theorem the_four_packed_widths :
    (W_FIELD = 255 ∧ W_CHAL = 64 * 2 ∧ W_BRANCH = 10 ∧ W_BOOL = 1) := by
  native_decide
#assert_compiled the_four_packed_widths

/-! ### The forty-word census. -/

/-- ⚑ THE WIDTH VECTOR, word for word, in `In_circuit.spec`'s own order: five `Field`, two
`Challenge` and three `Scalar Challenge` (which pack identically — `spec.ml:94-99` sends `Scalar
chal` to `p.pack chal`), three `Digest`, **sixteen** `Bulletproof_challenge` (`Backend.Tick.Rounds.n`
= `Rounds.Step` = `Nat.N16`), one `Branch_data`, eight feature flags, the lookup `Opt`'s own flag
bit, and the lookup `Opt`'s inner `Scalar Challenge`. -/
theorem statement_word_widths_are_the_packed_spec :
    (List.range 40).map msmBits =
      [255, 255, 255, 255, 255, 128, 128, 128, 128, 128, 255, 255, 255,
       128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128,
       10, 1, 1, 1, 1, 1, 1, 1, 1, 1, 128] := by
  native_decide
#assert_compiled statement_word_widths_are_the_packed_spec

/-- …and it really is FORTY words, which is the devnet Wrap verifier key's own `public = 40` and
therefore `shapeStep.msmTerms`. A census that summed to anything else would be a different statement.
⚑ Stated as an equality on the shape, so a shape change has to move this line. -/
theorem the_statement_is_forty_words :
    (shapeStep.msmTerms = 40 ∧ (List.range 40).length = 40) := by
  native_decide
#assert_compiled the_statement_is_forty_words

/-! ### ⚑ THE REALITY GATE. -/

/-- ⚑ **MINA'S OWN COMPILED CIRCUIT.** The `x_hat` ladder cluster of `step-zkapp-proved` — measured
off the o1-labs blob with the conformance gate's own `vbmLadders` primitive — is 31 ladders whose
chunk widths in row order are the list on the right. The list on the left is this file's census with
the zero-chunk words dropped, which is what "emits no `VarBaseMul` row" means. They are EQUAL.

If `msmBits` were wrong ANYWHERE — a fifteenth bulletproof challenge, a ninth feature flag, a
`Scalar_challenge` basic at some other width — this list would differ from Mina's in that position. -/
theorem x_hat_widths_are_minas_own_compiled_ladders :
    ((List.range 40).filter (fun i => msmChunksAt i != 0)).map msmChunksAt =
      [51, 51, 51, 51, 51, 26, 26, 26, 26, 26, 51, 51, 51,
       26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 2, 26] := by
  native_decide
#assert_compiled x_hat_widths_are_minas_own_compiled_ladders

/-- …that list has **31** entries and sums to **982** — Mina's own ladder count and chunk sum. -/
theorem thirty_one_ladders_nine_hundred_eighty_two_chunks :
    (((List.range 40).filter (fun i => msmChunksAt i != 0)).length = 31
     ∧ msmChunkPrefix 40 = 982) := by
  native_decide
#assert_compiled thirty_one_ladders_nine_hundred_eighty_two_chunks

/-- ⚑ AND THE EMITTED CIRCUIT AGREES WITH THE CENSUS — not just the census with itself. The
`VarBaseMul` rows R3 schedules at the committed shape are exactly `msmChunkPrefix msmTerms`, so a
row schedule that quietly kept a uniform width would red here even with `msmBits` correct. -/
theorem r3_schedules_exactly_the_census_ladder_rows :
    ((msmRows shapeSmoke tS.msm true).filter (fun r => r.kind == KGateType.varBaseMul)).length
      = msmChunkPrefix shapeSmoke.msmTerms := by
  native_decide
#assert_compiled r3_schedules_exactly_the_census_ladder_rows

/-! ### ⚑ THE FLOOR: a uniform width is REFUTED, in both directions. -/

/-- ⚑ **NOT UNIFORM, AND THE OLD CONSTANT IS WRONG BOTH WAYS.** Word 0 is a `Field` at 51 chunks and
word 5 a `Challenge` at 26, so no single number is right; the retired `msmChunks = 26` was 25 chunks
SHORT on eight words, and widening everything to 51 would have emitted 25 chunks of leading zeros on
twenty-two. The honest per-word total (982) is BELOW the uniform 26 the file used to run (1040) and
far below a uniform 51 (2040) — so the fix is not even a widening. -/
theorem a_uniform_msm_width_is_refuted :
    (msmChunksAt 0 = 51 ∧ msmChunksAt 5 = 26 ∧ msmChunksAt 29 = 2 ∧ msmChunksAt 30 = 0
     ∧ msmChunkPrefix 40 < 40 * 26 ∧ msmChunkPrefix 40 < 40 * 51) := by
  native_decide
#assert_compiled a_uniform_msm_width_is_refuted

/-! ### The variable space really is cumulative now. -/

/-- ⚑ The per-term point block is `msmChunksAt i + 2` wide and the bases are the PREFIX SUM, so no
two terms share a point index and the region is exactly `nMsmPts` wide. Stated as strict monotonicity
of `pT` plus the closing identity — a stride that stayed constant would collide two terms' cells,
which MERGES two σ classes and is invisible to a row-count pin. -/
theorem msm_point_indices_are_cumulative_and_disjoint :
    ((List.range (shapeStep.msmTerms - 1)).all (fun i =>
        pT shapeStep (i + 1) == pT shapeStep i + msmChunksAt i + 2)
     ∧ nMsmPts shapeStep == pT shapeStep shapeStep.msmTerms + shapeStep.msmTerms) = true := by
  native_decide
#assert_compiled msm_point_indices_are_cumulative_and_disjoint

/-- …and so is the counter region: term `i`'s own cells are `msmChunkPrefix i ..< msmChunkPrefix
(i+1)` and `baseIpa` starts immediately after the last of them, so R4's points cannot land on R3's
counters. -/
theorem msm_counter_region_ends_where_the_ipa_region_begins :
    baseIpa shapeStep = baseSN shapeStep + msmChunkPrefix shapeStep.msmTerms := by
  rfl
-- ⚑ `#assert_axioms`, not `#assert_compiled`: this one is KERNEL-CLEAN (`rfl` on the definitions),
-- so the stronger pin is the one that says it rests on no compiled-evaluation oracle at all.
#assert_axioms msm_counter_region_ends_where_the_ipa_region_begins

/-! ### ⚑ THE ZERO-CHUNK TERMS, and the pin that stops them pinning a challenge. -/

/-- ⚑ **A ZERO-CHUNK TERM HAS NO COUNTER CELL OF ITS OWN.** `vSN i 0` and `vSN i (msmChunksAt i)`
are the same expression there, so the `n_acc = 0` half `msmNZeroRows` emits for every OTHER term
would, on those nine, be a `w₀ = 0` row over the term's CHALLENGE variable — and challenges are
shared round-robin, so it would pin R2's decode chain, R4's fold and the deferred values with it.
`msmNZeroRows` filters them out, and this is the theorem that says the filter is load-bearing: the
row count is the NON-ZERO term count, not `msmTerms`. -/
theorem n_acc_pins_skip_the_zero_chunk_terms :
    ((msmNZeroRows shapeStep).length
       = (((List.range shapeStep.msmTerms).filter (fun i => msmChunksAt i != 0)).length + 1) / 2
     ∧ vSN shapeStep 30 0 = stmtVar shapeStep 30) := by
  native_decide
#assert_compiled n_acc_pins_skip_the_zero_chunk_terms

/-- ⚑ **RETIRED 2026-08-03 by §21 — and it went red exactly as it said it would.** This carried
`the_constant_words_still_carry_a_seed_and_an_add`: "`msmDblRow` runs for ALL `msmTerms` and the
`complete_add` chain is still `msmTerms − 1` long… nine points Mina never adds in-circuit… this
theorem is what will red when it is closed." It is closed — `msmRows` runs the NON-CONSTANT
partition — and the replacement is `…Pins16.the_constant_words_emit_no_base_no_seed_and_no_add`,
whose 30-add fold chain is Mina's own compiled run length. What survives here is the census the
partition is taken on. -/
theorem nine_of_the_forty_words_are_the_constant_partition :
    (((List.range shapeStep.msmTerms).filter (fun i => msmChunksAt i == 0)).length = 9
     ∧ (msmLive shapeStep).length + 9 = shapeStep.msmTerms) := by
  native_decide
#assert_compiled nine_of_the_forty_words_are_the_constant_partition

end Dregg2.Circuit.Emit.KimchiStepMain
