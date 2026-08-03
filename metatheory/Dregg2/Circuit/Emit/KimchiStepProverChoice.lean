/-
`KimchiStepMain` — ⚑⚑ **THE PROVER-CHOICE CENSUS, STEP SIDE.**

## Why this module exists

Every free witness this assembly has found was found **by tripping over it**: `verified` was an
`AOp.wit 1` that `Boolean.all` forced to 1; six ladder seeds were free and one was seeded at the
wrong point; `qPrime` was scheduled and absent from `circuitEnv`; three `lowest_128_bits` had
unconstrained high halves; the MSM scalars were transcript challenges where the statement's words
belong. Each cost a debugging session. **This module enumerates them instead**, and states the
enumeration as NAMED THEOREMS over the emitted objects rather than as prose that goes stale
(`metatheory/docs/GUARD-DISCIPLINE.md`).

⚑ NAMED THEOREMS, NOT `#guard`. This module adds no guards.

## ⚑ WHAT "PROVER-CHOSEN" MEANS HERE, AND WHAT IT DOES NOT

A circuit HAS inputs; a census that called every input a defect would say nothing. The question this
module answers is narrower and is the one that matters: **which cells does the prover supply, and for
each, is the choice (a) a forgery surface, (b) a fidelity gap against Mina, or (c) benign because a
named row pins it.** The three mechanical instruments are:

  * **`AOp.wit`** — the compiled straight-line programs' own declaration that a slot has NO defining
    row (`aHalfSlots` skips `.wit` by construction, `…Core` §8b). This is exact, not a heuristic.
  * **`envVarsNoRowReads`** — an environment entry no emitted row wires at all. A cell the witness
    supplies and the grid never reads.
  * **`occCount`** — how many permutation cells a variable owns across the emitted schedule. An
    equality here is a gate: a rung that starts or stops consuming a cell reds rather than passes a
    floor. ⚠ `occCount = 1` does NOT by itself mean free — a single read can still determine the
    cell (`vDomLog2` below) — so every (c) verdict names its pin instead of inferring one.

## ⚠ THE CORRECTION THIS MODULE LANDS

`…Pins11`'s `.wit` census pins **9**, and 9 is R8's program alone. **`ftBuild` has two more**
(`…Core:3442,3458`), so the assembly's free-witness count is **11**, at both committed shapes. One of
those two — `permClaimed` — occupies **exactly one cell**, so `eEq perm permClaimed` is an assert
nothing can fail: it forces a variable no other row reads. `…Core`'s own docblock at §12's `ftCfgRaw`
says of both witnesses "CHECKED by a row … so a wrong witness is a refusal rather than an accept";
that is true of `denomInv` and **false of `permClaimed`**.
-/
import Dregg2.Circuit.Emit.KimchiStepMainFixture

namespace Dregg2.Circuit.Emit.KimchiStepMain

open Dregg2.Circuit.Emit.KimchiTarget (KGateType K_PERMUTS)
open Dregg2.Circuit.Emit.KimchiPlacement
open Dregg2.Circuit.Emit.WitnessBuilder (VarEnv envIxBound)

set_option autoImplicit false
set_option maxRecDepth 100000

/-! ## §C1 — the three instruments. -/

/-- A straight-line slot with NO defining row (`…Core` §8b: `aHalfSlots` filters `.wit` out, so no
`Generic` half is ever emitted for one). -/
def AOp.isWit : AOp → Bool
  | .wit _ => true
  | _ => false

/-- The `.wit` slot INDICES of a compiled program, in emission order. -/
def witSlots (prog : Array AOp) : List Nat :=
  (List.range prog.size).filter (fun i => (prog.getD i default).isWit)

/-- How many permutation cells `v` owns across a row schedule. Cells, not classes — a variable read
twice by one row counts twice, which is what "how much of the circuit reads this" means. -/
def occCount (rows : List SRow) (v : PVar) : Nat :=
  rows.foldl (fun n r => n + (r.perm.take K_PERMUTS).countP (fun o => o == some v)) 0

/-- The wired-variable bitmap, `varIx`-indexed — one pass over the schedule, so the census below is
linear in the row count rather than quadratic. -/
def wiredIxs (bound : Nat) (rows : List SRow) : Array Bool :=
  rows.foldl (fun a r =>
    (r.perm.take K_PERMUTS).foldl (fun a o =>
      match o with
      | none => a
      | some v => if varIx v < bound then a.set! (varIx v) true else a) a)
    (Array.replicate bound false)

/-- **THE CELLS THE GRID NEVER READS.** Environment variables no row of the schedule wires. -/
def envVarsNoRowReads (env : VarEnv) (rows : List SRow) : List PVar :=
  let bound := envIxBound env + 1
  let w := wiredIxs bound rows
  ((env.map (·.1)).dedup).filter (fun v => !(w.getD (varIx v) false))

/-- The top rung at the COMMITTED shape. `…Fixture` carries `tStep`; the row list is this module's. -/
def rowsStep : List SRow := rungRows tStep .opening true

/-! ## §C2 — ⚑⚑ THE FREE-WITNESS COUNT IS ELEVEN, NOT NINE.

`…Pins11` pins `(finS.fp.prog.filter isWit).length == 4 * 2 + 1`. That is R8's program. The assembly
compiles TWO straight-line programs and R6's has two more `.wit` slots, so the census that has been
quoted as the assembly's is a census of one of its two programs. -/

/-- ⚑ **ELEVEN, and the split is 2 + 9** — at BOTH committed shapes, so this is a fact about the
emitter and not about a fixture. R6's two are `denomInv` and `permClaimed` (`…Core:3442,3458`); R8's
nine are `lowest_128_bits`' high part plus four `Field.equal` `(inverse, bit)` pairs
(`…Core:4314,4321-4322`). -/
theorem the_assembly_compiles_eleven_free_witness_slots :
    ((witSlots tS.ft.fp.prog).length = 2
     ∧ (witSlots tS.fin.fp.prog).length = 9
     ∧ (witSlots tStep.ft.fp.prog).length = 2
     ∧ (witSlots tStep.fin.fp.prog).length = 9) := by
  native_decide
#assert_compiled the_assembly_compiles_eleven_free_witness_slots

/-- …and the R8 nine are exactly the slots `…Pins11`'s guard counts, named rather than totalled:
`xiHi`, then `(eqInv, eqBit)` at each of the four `Field.equal` gadgets. An equality against the
slot record, so a rung that added a tenth witness would red here. -/
theorem r8s_nine_witnesses_are_xiHi_and_four_equality_gadgets :
    (witSlots tS.fin.fp.prog).headD 0 = tS.fin.fp.slots.xiHi
      ∧ (witSlots tS.fin.fp.prog).length = 1 + 4 * 2 := by
  native_decide
#assert_compiled r8s_nine_witnesses_are_xiHi_and_four_equality_gadgets

/-! ### ⚑ R6's TWO — one pinned, one an assert that cannot fail. -/

/-- R6's first witness is the `denomInv` of §9b's witnessed-inverse device, and it IS pinned: the
slot immediately after it multiplies `denom` by it, and the slot after that asserts the product
against the program's `1` literal (`…Core:3442-3444`). Given `denom ≠ 0` that fixes the witness, and
`denom = 0` makes the assert unsatisfiable rather than free. **(c) benign, and this is its pin.** -/
theorem ft_denom_inverse_is_multiplied_and_asserted_against_one :
    (let w := (witSlots tS.ft.fp.prog).headD 0
     (tS.ft.fp.prog.getD (w + 1) default = AOp.mul (w - 1) w
      ∧ tS.ft.fp.prog.getD (w + 2) default = AOp.aeq (w + 1) 0
      ∧ tS.ft.fp.prog.getD 0 default = AOp.lit 1)) := by
  native_decide
#assert_compiled ft_denom_inverse_is_multiplied_and_asserted_against_one

/-- ⚑⚑ **R6's SECOND WITNESS IS AN ASSERT THAT CANNOT FAIL.** `permClaimed` (`…Core:3458`) is
followed by `eEq perm permClaimed`, and `permClaimed` **occupies exactly one permutation cell in the
whole emitted schedule** — that assert's own. A row whose only novel operand is a variable no other
row reads constrains the prover not at all: he sets `permClaimed := perm` and the row closes.

⚠ This is NOT a forgery surface, because the check upstream actually wants IS emitted elsewhere —
R8's `permActual` reads `slots.perm`, the COMPUTED slot, and `pc` compares it against the statement's
`vPermShift` (`…Core:4270,4336`). `permClaimed` is a vestige of the design before R8 existed. What it
costs is one `Generic` half and one false sentence in `ftCfgRaw`'s docblock. -/
theorem ft_perm_claimed_is_an_assert_that_cannot_fail :
    (let w := (witSlots tS.ft.fp.prog).getD 1 0
     tS.ft.fp.prog.getD (w + 1) default = AOp.aeq tS.ft.fp.slots.perm w
      ∧ occCount rowsS (aVarAt (baseFtS shapeSmoke) tS.ft.fp.prog w) = 1
      ∧ occCount rowsStep (aVarAt (baseFtS shapeStep) tStep.ft.fp.prog w) = 1) := by
  native_decide
#assert_compiled ft_perm_claimed_is_an_assert_that_cannot_fail

/-- …and the pin that says the REAL check is elsewhere, so the paragraph above is not an excuse: R8's
`permActual` is the ft program's COMPUTED `perm` slot, and the slot `permClaimed` sits in is a
different one. -/
theorem r8_checks_the_computed_perm_and_not_the_claimed_one :
    ((finWireOf shapeSmoke tS.ft).permActual
        = AOp.inp (aVarAt (baseFtS shapeSmoke) tS.ft.fp.prog tS.ft.fp.slots.perm)
     ∧ tS.ft.fp.slots.perm ≠ (witSlots tS.ft.fp.prog).getD 1 0) := by
  native_decide
#assert_compiled r8_checks_the_computed_perm_and_not_the_claimed_one

/-! ## §C3 — THE CELLS THE GRID NEVER READS.

Every one of these is an environment entry the witness supplies and no row wires. They cannot be a
forgery surface — nothing reads them — but each is either a dead entry (which a future rung will
trip over exactly as the `qPrime` regression did, in the other direction) or a cell whose consumer
this shape does not instantiate. -/

/-- ⚑ **NINETEEN at the committed shape, TWENTY-ONE at the smoke one**, and the difference is the two
sourceless statement words: at `shapeSmoke` there are three MSM terms, so words 11 and 39 have no
ladder to be read by, and at `shapeStep` they do (§C4). The other nineteen are the same at both. -/
theorem the_grid_never_reads_nineteen_environment_cells :
    ((envVarsNoRowReads (circuitEnv tStep) rowsStep).length = 19
     ∧ (envVarsNoRowReads (circuitEnv tS) rowsS).length = 21) := by
  native_decide
#assert_compiled the_grid_never_reads_nineteen_environment_cells

/-- …and they are accounted for, family by family, so "nineteen" is a census and not a number.
**Eighteen are `.aeq` output slots** — `aHalf` gives an `.aeq` no cell of its own (`…Core:2957`), so
the inert slot every assert produces is an environment entry with no row, three in R6's program and
fifteen in R8's. **The nineteenth is `vDHi 0`**, the high half of §8g's ξ chain, which `xiDefRows`
never emits because ξ's source is already a `Challenge.t` and upstream splits nothing there either
(simplification #1). ⚠ It is carried at value 0 by `circuitEnv`'s `vDHi` map (`…Core:4941`) for both
chains where only chain 1 has a split. -/
theorem the_nineteen_are_eighteen_assert_outputs_and_one_dead_split :
    (occCount rowsStep (vDHi shapeStep 0) = 0
     ∧ occCount rowsStep (vDHi shapeStep 1) = 2
     ∧ ((tStep.ft.fp.prog.toList ++ tStep.fin.fp.prog.toList).countP
          (fun o => match o with | .aeq _ _ => true | _ => false)) = 18) := by
  native_decide
#assert_compiled the_nineteen_are_eighteen_assert_outputs_and_one_dead_split

/-! ## §C4 — THE STATEMENT WORDS WITH NO IN-CIRCUIT SOURCE.

§2c's table names two: word 11 `messages_for_next_wrap_proof` and word 39 the lookup `Opt`'s inner
scalar challenge. Nine more — the eight feature flags and the `Opt`'s own flag — are the CONSTANT
partition `multiscale_known` folds outside the circuit, so they own no variable at all. -/

/-- ⚑ **WORDS 11 AND 39 REACH EXACTLY ONE CELL EACH** — their own `var_base_mul` counter, and
nothing else. That is what "no in-circuit source" means as a measurement: the ladder READS the word,
so `x_hat` moves with it, and no row WRITES it.

⚠ **THE TWO ARE NOT THE SAME FINDING.** Word 11 is `exists … ~request:Req.Messages_for_next_wrap_
proof` at `step_main.ml:364-366` over `Digest.typ`, which is a bare `Field.typ` transport emitting
ZERO constraints (`composition_types/digest.ml:60-63`) — so it is a witness of the whole step circuit
upstream too, and this assembly is FAITHFUL. Word 39 is the lookup `Opt`'s inner scalar; with
`lookup_verification_enabled = false` upstream packs it as a dummy variable and derives it nowhere
either, so the honest label is the same — **what this assembly does not model is the sub-circuit that
would derive it if lookups were ON.** -/
theorem the_two_sourceless_statement_words_reach_only_their_own_ladder :
    (occCount rowsStep (vStmtWrapMsgs shapeStep) = 1
     ∧ occCount rowsStep (vStmtLookup shapeStep) = 1
     ∧ stmtVar shapeStep 11 = vStmtWrapMsgs shapeStep
     ∧ stmtVar shapeStep 39 = vStmtLookup shapeStep) := by
  native_decide
#assert_compiled the_two_sourceless_statement_words_reach_only_their_own_ladder

/-- …and the nine one-bit words reach NO cell, because `multiscale_known` partitions them out
(`step_verifier.ml:133-152`) and `msmChunksAt` is 0 there. Stated as an `all`, so a rung that
accidentally gave one a ladder reds. -/
theorem the_nine_constant_statement_words_reach_no_cell :
    ((List.range 9).all (fun k =>
        occCount rowsStep (vStmtFlag shapeStep k) == 0 && msmChunksAt (30 + k) == 0)) = true := by
  native_decide
#assert_compiled the_nine_constant_statement_words_reach_no_cell

/-! ## §C5 — THE SUPPLIED CELLS THAT ARE READ, ranked by what choosing them buys.

Each of these IS wired — some row reads it — and none is written by any row. The occurrence count is
pinned as an EQUALITY so a rung that starts (or stops) consuming one reds here. -/

/-- ⚑⚑ **(a) FORGERY SURFACE — `z₁`, `z₂` and `G`.** `equal_g` is emitted since §19 and `verified` is
its output cell, but `rhs = z₁·(G + b·u) + z₂·H` reads three cells the prover supplies:
`z₁`/`z₂` own **one cell each** (their `Shifted_value.Type2` split row — one equation in three
unknowns, all three the prover's) and `G` owns **five and four** (`assert_on_curve`'s `x² = x·x` and
`x³ = x²·x` halves read `x` twice, `y` once in the `assert_square`, plus segment D's absorb and the
ladder base). `…Pins14`'s `substituted_assembly_still_closes_equal_g` is the consequence:
`tSwapAbs.bp.ver = 1`, ACCEPTED.

⚠ Upstream these three are free too — `openings_proof` is `exists ~request:Req.Openings_proof`
(`wrap_main.ml:357-383`), and `wrap_proof.opening.challenge_polynomial_commitment` is a field of the
step circuit's own `exists ~request:Req.Proof_with_datas` (`per_proof_witness.ml:52-99`). **The
refusal is the accumulator check, which is not a gate in either implementation at this rung.** -/
theorem the_opening_response_scalars_own_one_cell_each :
    (occCount rowsS (bpZ1 shapeSmoke) = 1
     ∧ occCount rowsS (bpZ2 shapeSmoke) = 1
     ∧ occCount rowsS (vGx shapeSmoke) = 5
     ∧ occCount rowsS (vGy shapeSmoke) = 4
     ∧ occCount rowsStep (bpZ1 shapeStep) = 1
     ∧ occCount rowsStep (vGx shapeStep) = 5) := by
  native_decide
#assert_compiled the_opening_response_scalars_own_one_cell_each

/-- ⚑ **(a/b) THE `combined_inner_product` BIT.** `absorb sponge Scalar advice.combined_inner_product`
absorbs the FIELD half and then a `Bits [b]` (`step_verifier.ml:79-81,256`). Here the field half is
`vCipShift`, a statement word R8 binds; the BIT is `vCipBit`, and its four gate cells are the three
of `Boolean.typ`'s own `b² = b` and the transcript absorb. **Booleanity is all that constrains it**,
so a prover has TWO transcripts to choose between — every squeeze after `combined_inner_product`
(`u`, the fifteen prechallenges, `c`) moves with the bit.

⚠ ONE BIT is not a grind. It is named here because upstream's bit is not free: `Other_field.Packed`
is `(Field.t, Boolean.var)` and the pair is the SPLIT of the shifted value, so the bit is its parity
and is derived. **(b) fidelity gap**, and a one-bit forgery surface at the transcript's input. -/
theorem the_cip_bit_is_boolean_constrained_and_absorbed_and_nothing_else :
    (occCount (rowsS.filter (fun r => !r.probe)) (vCipBit shapeSmoke) = 4
     ∧ occCount rowsS (vCipBit shapeSmoke) = 5
     ∧ CIP_BIT = 0) := by
  native_decide
#assert_compiled the_cip_bit_is_boolean_constrained_and_absorbed_and_nothing_else

/-- ⚑ **(b) `branch_data`'s TWO MASK BITS ARE PROVER-CHOSEN AMONG FOUR, AND UPSTREAM ADMITS THREE.**
`branchRows` (`…Core:4003-4009`) emits `Boolean.typ`'s `b² = b` on each bit and
`Branch_data.Checked.pack`'s `4·domain_log2 + (m₀ + 2·m₁) = branch_data`. That is ONE equation over
`(m₀, m₁, domain_log2, branch_data)` with `branch_data` a statement word and `vDomLog2` occurring
**in exactly that one cell** — so the prover picks the two bits freely and solves for `domLog2`.
`Prefix_mask.there` admits only `[0,0]`, `[0,1]`, `[1,1]` (`pickles_base/proofs_verified.ml:75-81`);
`[1,0]` closes here.

⚠ It is a CLAIM, not a hidden choice: the mask moves `combined_inner_product` (§12l) and the
opt-sponge digest (§14a), and `branch_data` is Wrap statement word 29, which the x_hat ladder reads.
⚠ And `vDomLog2` carries no range check, where `per_proof_witness.ml:166-168` allocates `Branch_data`
with `~assert_16_bits:(Step_verifier.assert_n_bits ~n:16)`. -/
theorem the_branch_mask_bits_are_only_boolean_and_domain_log2_owns_one_cell :
    (occCount rowsS (vDomLog2 shapeSmoke) = 1
     ∧ occCount rowsStep (vDomLog2 shapeStep) = 1
     ∧ occCount rowsS (vMaskPack shapeSmoke) = 3
     ∧ MASK_BITS = [0, 1]) := by
  native_decide
#assert_compiled the_branch_mask_bits_are_only_boolean_and_domain_log2_owns_one_cell

/-- ⚑ **(b, faithful) `prev_challenges`.** Each of the `2·bRounds` carried challenges owns FOUR cells
— segment A's absorb, segment C's absorb, and its two `f_c` ladder reads (§8i) — and no row writes
one. That is upstream's shape exactly: `prev_challenges` is a `Per_proof_witness` field
(`per_proof_witness.ml:90-92`), absorbed at `step_verifier.ml:956` and `step_main.ml:80`, and bound
only by the accumulator check. **(c) faithful-but-unbound**, and the bound is `verified`. -/
theorem every_carried_challenge_owns_four_cells_and_is_written_by_none :
    ((List.range (2 * shapeSmoke.bRounds)).all (fun i =>
        occCount rowsS (vPrevChal shapeSmoke i) == 4)) = true := by
  native_decide
#assert_compiled every_carried_challenge_owns_four_cells_and_is_written_by_none

/-- ⚑ **(b, faithful) THE APP-STATE WORDS.** `to_field_elements_without_index` puts
`state_to_field_elements app_state` at the head of both `hash_messages_for_next_step_proof` calls,
and the app state is the INDUCTIVE RULE's own statement — `exists input_typ ~request:Req.App_state`
(`step_main.ml:286`). No `verify_one` sub-circuit derives it in either implementation. Each of the
four owns exactly its one absorb cell. -/
theorem the_four_app_state_words_own_one_absorb_cell_each :
    ((List.range N_HM_APP).all (fun i =>
        occCount rowsS (vHm shapeSmoke i) == 1 && occCount rowsS (vHmO shapeSmoke i) == 1)) = true := by
  native_decide
#assert_compiled the_four_app_state_words_own_one_absorb_cell_each

/-- ⚑ **(c) THE ONE STRUCTURAL PAD LANE.** `verify_one` feeds 117 sponge items and this file models
one commitment per rate-2 block, so block `oDigest`'s second lane carries nothing upstream feeds. It
owns exactly one cell — the absorb — and `UNWIRED_ITEMS` is empty, i.e. every OTHER absorbed word is
a variable some sub-circuit reads. ⚠ Since §22 that lane is PINNED by a `w = 0` `Generic` half, so
its one gate cell is a constant pin and not a free absorb. -/
theorem the_transcript_residue_is_one_pinned_pad_lane :
    (occCount rowsStep (vMsg shapeStep 0 1) = 1
     ∧ msgVar shapeStep oDigest 1 = vMsg shapeStep oDigest 1
     ∧ ((List.range shapeStep.absorbs).flatMap (fun a =>
          (List.range 2).filter (fun j => msgVar shapeStep a j == vMsg shapeStep a j))).length = 1
     ∧ UNWIRED_ITEMS = ([] : List (String × Nat))) := by
  native_decide
#assert_compiled the_transcript_residue_is_one_pinned_pad_lane

/-! ## §C6 — THE EVALUATION COLUMNS, and why they are the right kind of free.

`vEz k` / `vEw k` are the previous proof's 43 evaluation columns at ζ and ζω plus `combine`'s
four-entry prefix. Upstream they are `prev_proof_evals : Plonk_types.All_evals.In_circuit.t`
(`per_proof_witness.ml:84-88`), a field of the same `exists ~request:Req.Proof_with_datas` — supplied,
and bound only by `combined_inner_product` reaching a statement word R8 checks. Four of them are
DERIVED here where upstream also derives them: `vEz 0/1`/`vEw 0/1` are §8i's `f_c` ladders and
`vEz 3` is R6's `ft_eval0` output. -/

/-- ⚑ The prefix is derived and the columns are supplied, and the count says which is which: the
`sg_evals` slots and `ft_eval0` own MORE cells than an absorbed column does, because a ladder writes
them. Stated as the exact vector for the first four so a lane that re-fixtured one reds. -/
theorem the_combine_prefix_is_derived_and_the_columns_are_supplied :
    ((List.range 4).map (occCount rowsS ∘ vEz shapeSmoke) = [3, 3, 3, 2]
     ∧ (List.range 4).map (occCount rowsS ∘ vEw shapeSmoke) = [3, 3, 2, 2]
     ∧ EV_PREFIX = 4) := by
  native_decide
#assert_compiled the_combine_prefix_is_derived_and_the_columns_are_supplied

/-! ## §C7 — ⚑ THE HEADLINE, as one theorem.

The three instruments, at the committed shape, in one statement — so a rung that moves any of them
without saying so reds in one place. -/

/-- ⚑⚑ **THE CENSUS.** Eleven declared free-witness slots (2 in R6, 9 in R8); nineteen environment
cells the grid never reads; two statement words with no in-circuit source, each reaching exactly its
own ladder; nine statement words with no cell at all; and the opening's three free cells
(`z₁`, `z₂`, `G`) still standing between a substituted commitment and acceptance. -/
theorem the_step_prover_choice_census :
    ((witSlots tStep.ft.fp.prog).length + (witSlots tStep.fin.fp.prog).length = 11
     ∧ (envVarsNoRowReads (circuitEnv tStep) rowsStep).length = 19
     ∧ occCount rowsStep (vStmtWrapMsgs shapeStep) = 1
     ∧ occCount rowsStep (vStmtLookup shapeStep) = 1
     ∧ occCount rowsStep (bpZ1 shapeStep) = 1
     ∧ occCount rowsStep (bpZ2 shapeStep) = 1) := by
  native_decide
#assert_compiled the_step_prover_choice_census

end Dregg2.Circuit.Emit.KimchiStepMain
