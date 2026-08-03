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

## ⚠ THE CORRECTION THIS MODULE LANDED, AND WHAT WAS DONE ABOUT IT

`…Pins11`'s `.wit` census pins **9**, and 9 is R8's program alone — `ftBuild` compiles a second
program. When this module was written that made the assembly's count **11**; one of R6's two,
`permClaimed`, occupied **exactly one cell**, so `eEq perm permClaimed` was an assert nothing could
fail. **It is DELETED (2026-08-03)** together with the sentence in `ftCfgRaw`'s docblock that claimed
both witnesses were checked by a row. The assembly's count is now **10 = 1 + 9**, and §C2 states it
against both programs so the number cannot again be quoted off one of them.

## ⚠ WHAT ELSE MOVED ON 2026-08-03, and why the numbers below are not the ones first published

  * **`vCipBit` is DERIVED.** It is `bpOdd s 0` — §19 ladder 0's `s_odd` — because upstream absorbs
    and scales ONE `Other_field.Packed` pair (`step_verifier.ml:256-259`, `:317`). Zero new rows.
  * **`branch_data` is PINNED.** `branchRows` gained `Prefix_mask`'s suffix half `m₀·(1−m₁) = 0` and
    `Branch_data.typ`'s own `~assert_16_bits` chain on `domain_log2`
    (`per_proof_witness.ml:166-168`).
  * **Word 39 carries upstream's dummy (`0`)** instead of an invented `Challenge`-width fixture.
-/
import Dregg2.Circuit.Emit.KimchiStepMainFixture

namespace Dregg2.Circuit.Emit.KimchiStepMain

open Dregg2.Circuit.Emit.KimchiTarget (KGateType K_PERMUTS)
open Dregg2.Circuit.Emit.KimchiPlacement
open Dregg2.Circuit.Emit.WitnessBuilder (VarEnv envIxBound)
open Dregg2.Circuit.Emit.KimchiRenderVarBaseMul (fAdd fMul fInv)

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

/-! ## §C2 — ⚑⚑ THE FREE-WITNESS COUNT IS TEN — IT WAS ELEVEN, AND NINE IS ONE PROGRAM'S.

`…Pins11` pins `(finS.fp.prog.filter isWit).length == 4 * 2 + 1`. That is R8's program. The assembly
compiles TWO straight-line programs, so the census that has been quoted as the assembly's is a census
of one of its two. R6's had TWO; one of them, `permClaimed`, was an assert that could not fail and is
**deleted**, so R6 has one and the assembly has **ten**. -/

/-- ⚑ **TEN, and the split is 1 + 9** — at BOTH committed shapes, so this is a fact about the emitter
and not about a fixture. R6's one is `denomInv` (`ftBuild`'s witnessed-inverse device); R8's nine are
`lowest_128_bits`' high part plus four `Field.equal` `(inverse, bit)` pairs. -/
theorem the_assembly_compiles_ten_free_witness_slots :
    ((witSlots tS.ft.fp.prog).length = 1
     ∧ (witSlots tS.fin.fp.prog).length = 9
     ∧ (witSlots tStep.ft.fp.prog).length = 1
     ∧ (witSlots tStep.fin.fp.prog).length = 9) := by
  native_decide
#assert_compiled the_assembly_compiles_ten_free_witness_slots

/-- …and the R8 nine are exactly the slots `…Pins11`'s guard counts, named rather than totalled:
`xiHi`, then `(eqInv, eqBit)` at each of the four `Field.equal` gadgets. An equality against the
slot record, so a rung that added a tenth witness would red here. -/
theorem r8s_nine_witnesses_are_xiHi_and_four_equality_gadgets :
    (witSlots tS.fin.fp.prog).headD 0 = tS.fin.fp.slots.xiHi
      ∧ (witSlots tS.fin.fp.prog).length = 1 + 4 * 2 := by
  native_decide
#assert_compiled r8s_nine_witnesses_are_xiHi_and_four_equality_gadgets

/-! ### ⚑ R6's ONE — pinned; the second was an assert that could not fail and is gone. -/

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

/-- ⚑⚑ **R6'S SECOND WITNESS WAS AN ASSERT THAT COULD NOT FAIL, AND IT IS GONE.** `permClaimed` was
an `eWit` followed by `eEq perm permClaimed`, and it occupied **exactly one permutation cell in the
whole emitted schedule** — that assert's own. A row whose only novel operand is a variable no other
row reads constrains the prover not at all: he set `permClaimed := perm` and the row closed.

This states the deletion rather than the defect, so a rung that puts a second witness back reds here:
R6's program has ONE `.wit`, its next slot is the `denom · denomInv` multiplication (not an `aeq`),
and the program's LAST slot is the `perm` scalar itself rather than an assert.

⚠ It was never a forgery surface, because the check upstream actually wants is emitted elsewhere —
R8's `permActual` reads `slots.perm`, the COMPUTED slot, and `pc` compares it against the statement's
`vPermShift`. What it cost was one `Generic` half and one false sentence in `ftCfgRaw`'s docblock;
both are retired. -/
theorem r6_has_one_witness_and_no_assert_that_cannot_fail :
    ((witSlots tS.ft.fp.prog).length = 1
      ∧ (let w := (witSlots tS.ft.fp.prog).headD 0
         tS.ft.fp.prog.getD (w + 1) default = AOp.mul (w - 1) w)
      ∧ tS.ft.fp.prog.getD (tS.ft.fp.prog.size - 1) default
          = tS.ft.fp.prog.getD tS.ft.fp.slots.perm default) := by
  native_decide
#assert_compiled r6_has_one_witness_and_no_assert_that_cannot_fail

/-- …and the pin that says the REAL check is elsewhere, so the deletion removed no check: R8's
`permActual` is the ft program's COMPUTED `perm` slot. -/
theorem r8_checks_the_computed_perm_and_not_a_claimed_one :
    ((finWireOf shapeSmoke tS.ft).permActual
        = AOp.inp (aVarAt (baseFtS shapeSmoke) tS.ft.fp.prog tS.ft.fp.slots.perm)
     ∧ tS.ft.fp.slots.perm ≠ (witSlots tS.ft.fp.prog).headD 0) := by
  native_decide
#assert_compiled r8_checks_the_computed_perm_and_not_a_claimed_one

/-! ## §C3 — THE CELLS THE GRID NEVER READS.

Every one of these is an environment entry the witness supplies and no row wires. They cannot be a
forgery surface — nothing reads them — but each is either a dead entry (which a future rung will
trip over exactly as the `qPrime` regression did, in the other direction) or a cell whose consumer
this shape does not instantiate. -/

/-- ⚑ **TWENTY at the committed shape, TWENTY-TWO at the smoke one**, and the difference is the two
sourceless statement words: at `shapeSmoke` there are three MSM terms, so words 11 and 39 have no
ladder to be read by, and at `shapeStep` they do (§C4). ⚠ It was nineteen/twenty-one when this
module landed; `permClaimed`'s deletion took ONE assert output out, and the lazy-sponge rung's
post-absorb lanes put two dead lanes in. -/
theorem the_grid_never_reads_twenty_environment_cells :
    ((envVarsNoRowReads (circuitEnv tStep) rowsStep).length = 20
     ∧ (envVarsNoRowReads (circuitEnv tS) rowsS).length = 22) := by
  native_decide
#assert_compiled the_grid_never_reads_twenty_environment_cells

/-- …and they are accounted for, family by family, so "twenty" is a census and not a number.
**Seventeen are `.aeq` output slots** — `aHalf` gives an `.aeq` no cell of its own, so the inert slot
every assert produces is an environment entry with no row, TWO in R6's program (it was three, and the
third was `permClaimed`'s) and fifteen in R8's. **One is `vDHi 0`**, the high half of §8g's ξ chain,
which `xiDefRows` never emits because ξ's source is already a `Challenge.t` and upstream splits
nothing there either (simplification #1); it is carried at value 0 by `circuitEnv`'s `vDHi` map for
both chains where only chain 1 has a split. **The remaining two are post-absorb lanes** the lazy
sponge no longer reads. -/
theorem the_twenty_are_seventeen_assert_outputs_and_a_dead_split_and_two_lanes :
    (occCount rowsStep (vDHi shapeStep 0) = 0
     ∧ occCount rowsStep (vDHi shapeStep 1) = 2
     ∧ ((tStep.ft.fp.prog.toList).countP
          (fun o => match o with | .aeq _ _ => true | _ => false)) = 2
     ∧ ((tStep.fin.fp.prog.toList).countP
          (fun o => match o with | .aeq _ _ => true | _ => false)) = 15) := by
  native_decide
#assert_compiled the_twenty_are_seventeen_assert_outputs_and_a_dead_split_and_two_lanes

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
`lookup_verification_enabled = false` upstream packs it as a dummy and derives it nowhere either, so
the honest label is the same — **what this assembly does not model is the sub-circuit that would
derive it if lookups were ON.**

⚑ **SINCE 2026-08-03 word 39 at least carries UPSTREAM'S NUMBER.** `STMT_LOOKUP_VAL` was an invented
`Challenge`-width fixture; it is now `0`, which is what
`~lookup_parameters:{ zero = { var = { challenge = Field.zero } } }` (`step_main.ml:90-95`) and
`Common.Lookup_parameters.tick_zero` (`common.ml:105-118`) make the `Opt`'s dummy scalar challenge.
That pins the VALUE and nothing else: the cell count is unchanged and no row writes it. -/
theorem the_two_sourceless_statement_words_reach_only_their_own_ladder :
    (occCount rowsStep (vStmtWrapMsgs shapeStep) = 1
     ∧ occCount rowsStep (vStmtLookup shapeStep) = 1
     ∧ stmtVar shapeStep 11 = vStmtWrapMsgs shapeStep
     ∧ stmtVar shapeStep 39 = vStmtLookup shapeStep
     ∧ STMT_LOOKUP_VAL = 0) := by
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

/-- ⚑⚑ **(CLOSED 2026-08-03) THE `combined_inner_product` BIT IS DERIVED.**
`absorb sponge Scalar advice.combined_inner_product` absorbs the FIELD half and then a `Bits [b]`
(`step_verifier.ml:79-81,256-259`). This module first measured the bit as a cell whose ONLY
constraints were `Boolean.typ`'s `b² = b` and the absorb — **booleanity is not a derivation**, so a
prover had two transcripts and every squeeze after `combined_inner_product` (`u`, the fifteen
prechallenges, `c`) moved with the bit.

**The closure cost no row**, because upstream's two uses are ONE object: `:256-259` destructures the
same `Other_field.t = (Field.t * Boolean.var)` pair that `scale_fast2 u advice.combined_inner_product`
(`:317`) consumes, and `plonk_curve_ops.ml:251-253` names it `(s_div_2, s_odd)`. §19's ladder 0
already emitted that pair and its `Field.Assert.equal (2·s_div_2 + s_odd) s` split row
(`:290-291`, the `split_field` shape of `wrap_main.ml:69-81`). So `vCipBit = bpOdd 0`, and the
absorbed bit IS the parity that row forces off `vCipShift`.

⚠ **SAY THE RESIDUAL.** The split row plus the ladder's `bits_lsb.(254) = 0` gives
`h < 2^254`, which does NOT make the parity unique: `2h + b ≡ x (mod p)` admits the wrong parity at
`h = (x − b + p)/2 < 2^254` for all but a ~2^−128 fraction of `x`. What changed is that the bit is no
longer free OF THE ASSEMBLY — flipping it moves `bpDiv2 0`, hence `uc`, `q` and `lhs`, so the second
transcript costs a re-solved `G`. **Upstream's gadget carries the same residual**
(`wrap_main.ml:64-67` defers the fit-check to `scale_fast2`, which checks 254 bits, not `< p/2`), so
this is a fidelity match and not a proof that one transcript remains. -/
theorem the_cip_bit_is_ladder_zeros_derived_parity :
    (vCipBit shapeSmoke = bpOdd shapeSmoke 0
     ∧ vCipBit shapeStep = bpOdd shapeStep 0
     ∧ msgVar shapeStep (oCip shapeStep) 1 = bpOdd shapeStep 0
     ∧ bpScalV shapeStep 0 = vCipShift shapeStep
     ∧ (cipWordOf tS).2 = tS.fin.cipShift % 2
     ∧ fAdd (fAdd (tS.bp.scals.headD 0 / 2) (tS.bp.scals.headD 0 / 2)) ((cipWordOf tS).2)
         = tS.fin.cipShift) := by
  native_decide
#assert_compiled the_cip_bit_is_ladder_zeros_derived_parity

/-- ⚑⚑ **(CLOSED 2026-08-03) `branch_data`'s TRIPLE IS PINNED.** `branchRows` used to emit only
`Boolean.typ`'s `b² = b` on each bit and `Branch_data.Checked.pack`'s
`4·domain_log2 + (m₀ + 2·m₁) = branch_data`. That is ONE equation over four unknowns with
`branch_data` a statement word and `vDomLog2` occurring **in exactly that one cell** — so the prover
picked the two bits freely and solved for `domLog2`, and `Prefix_mask.there` admits only `[0,0]`,
`[0,1]`, `[1,1]` (`pickles_base/proofs_verified.ml:75-81`) while `[1,0]` closed here.

Two rows landed and each refuses a different thing:

  * **the suffix half `m₀ − m₀·m₁ = 0`** (`m₀ ≤ m₁`) — this is what refuses the illegal `[1,0]`;
  * **`Branch_data.typ`'s own `~assert_16_bits`** on `domain_log2`
    (`per_proof_witness.ml:166-168`), a `to_field_checked ~num_bits:16` = ONE `EndoMulScalar` row —
    this is what refuses the two LEGAL masks that are not the honest one, because
    `(branch_data − maskPack)·4⁻¹` is a 16-bit integer for exactly one of `{0, 2, 3}` and a
    full-width field element for the other two.

`vDomLog2` now owns TWO cells (the pack row and the chain's `Field.Assert.equal n scalar` tie), and
the mask bits carry a third gate row. -/
theorem the_branch_triple_is_pinned_by_the_suffix_row_and_the_16_bit_chain :
    (occCount rowsS (vDomLog2 shapeSmoke) = 2
     ∧ occCount rowsStep (vDomLog2 shapeStep) = 2
     ∧ occCount rowsS (vMaskPack shapeSmoke) = 3
     ∧ MASK_BITS = [0, 1]
     ∧ RNG_DOMLOG2_ROWS = 1
     ∧ 16 * RNG_DOMLOG2_ROWS = 16) := by
  native_decide
#assert_compiled the_branch_triple_is_pinned_by_the_suffix_row_and_the_16_bit_chain

/-- ⚑ **THE ILLEGAL MASK, MEASURED IN BOTH POLARITIES.** `[1,0]` satisfies booleanity and, with
`domain_log2` re-solved, `Checked.pack` — so the pre-fix row set admitted it. The suffix half
`m₀·(1 − m₁) = 0` is zero on the three `Prefix_mask.there` masks and NONZERO on `[1,0]`, which is the
whole content of the refusal; and the `domain_log2` the other two legal masks imply is not a 16-bit
integer, which is the whole content of the second. Stated over the coefficients rather than over a
re-emitted grid, so it is a fact about the ROW and not about one witness. -/
theorem the_illegal_mask_is_the_only_one_the_suffix_row_rejects :
    (([(0, 0), (0, 1), (1, 1)]).all (fun m => fSub m.1 (fMul m.1 m.2) == 0)
     ∧ fSub 1 (fMul 1 0) ≠ 0
     ∧ (branchPacked - 2) / 4 = BRANCH_DOMAIN_LOG2
     ∧ ¬ (fMul (fSub branchPacked 0) (fInv 4) < 2 ^ 16)
     ∧ ¬ (fMul (fSub branchPacked 3) (fInv 4) < 2 ^ 16)) := by
  native_decide
#assert_compiled the_illegal_mask_is_the_only_one_the_suffix_row_rejects

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

/-- ⚑⚑ **THE CENSUS, 2026-08-03.** TEN declared free-witness slots (1 in R6, 9 in R8); twenty
environment cells the grid never reads; two statement words with no in-circuit source, each reaching
exactly its own ladder; nine statement words with no cell at all; and the opening's three free cells
(`z₁`, `z₂`, `G`) still standing between a substituted commitment and acceptance.

⚑ **WHAT MOVED, AND WHAT DID NOT.** Three cells left the "prover chooses, and the choice changes what
the circuit accepts" list this rung: `vCipBit` (derived — ladder 0's `s_odd`), and both
`proofs_verified_mask` bits with `vDomLog2` behind them (pinned by the suffix row and the 16-bit
chain). `permClaimed` left the free-witness list without ever having been on the changes-acceptance
one. **`z₁`, `z₂` and `G` did not move, and `equal_g` still accepts a substituted commitment** —
their binder is the accumulator opening leg, which is a discrete-log assumption in BOTH
implementations and is not a rung. -/
theorem the_step_prover_choice_census :
    ((witSlots tStep.ft.fp.prog).length + (witSlots tStep.fin.fp.prog).length = 10
     ∧ (envVarsNoRowReads (circuitEnv tStep) rowsStep).length = 20
     ∧ occCount rowsStep (vStmtWrapMsgs shapeStep) = 1
     ∧ occCount rowsStep (vStmtLookup shapeStep) = 1
     ∧ occCount rowsStep (bpZ1 shapeStep) = 1
     ∧ occCount rowsStep (bpZ2 shapeStep) = 1
     ∧ vCipBit shapeStep = bpOdd shapeStep 0
     ∧ occCount rowsStep (vDomLog2 shapeStep) = 2) := by
  native_decide
#assert_compiled the_step_prover_choice_census

end Dregg2.Circuit.Emit.KimchiStepMain
