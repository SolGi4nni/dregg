/-
# `MinaWrapProofDeferredWords` — ⚑ the SIX **Fq** deferred words of devnet block 539508's **WRAP**
proof: the values a step statement's live `unfinalized_proofs` block must publish.

## ⚑ SAY THE SUBSTRATE OUT LOUD

**This is Lean-authored data, not a constraint.** Nothing here emits a gate. It is the VALUE layer
`KimchiStepMainCore` §24 publishes at the live per-proof block's five `B Field` words and its
`Scalar Challenge` ξ, and that `KimchiWrapMainField`'s `FIN_DEFERRED_*` are now *defined* as
projections of — one copy of each number, not two. House Law #1 is untouched: the AIR stays
Lean-authored.

## ⚑⚑ WHY THIS FILE EXISTS — the aliasing it retires, stated as the defect it was

Until 2026-08-07 `KimchiStepMainCore.stepStmtVar` published the live block's `unfinalized_proofs`
deferred words **out of cells that already held a different statement's deferred values**:

    step-statement slot   was                        which is
    0,1  cip   hi/parity  `bpDiv2 0` / `bpOdd 0`     the split of `vCipShift`  — WRAP statement w0
    2,3  b     hi/parity  `bpDiv2 1` / `bpOdd 1`     the split of `vBShift`    — WRAP statement w1
    4..7 ζ^n   hi/parity  `ftcDiv2 1` / `ftcOdd 1`   §6b's own `ζ^n` scalar    — WRAP statement w2/3
    8,9  perm  hi/parity  `ftcDiv2 0` / `ftcOdd 0`   §6b's own `perm` scalar   — WRAP statement w4
    15   ξ                `vXiStmt`                  R8's `xi_correct` input   — WRAP statement w9

⚑ **ONE SET OF CELLS, TWO STATEMENTS.** Those are R5/R6/R8's outputs: the **Fp** deferred values of
the *Wrap proof-state* the step circuit verifies (`Shifted_value.Type1` over Fp,
`KimchiStepMainCore` §8f), whose checker IS the step circuit. What belongs in a step statement's
`unfinalized_proofs` block is the **Fq** deferred values *about that wrap proof*
(`Shifted_value.Type2`, the same-field shift — `impls.ml:135`), which the step circuit cannot
compute at all and therefore DEFERS: their checker is the next `wrap_main`'s `finalize_other_proof`
(`wrap_main.ml:335`), i.e. `KimchiWrapMainCore` §19/§20.

Two objects with the same six names, in two different fields, sharing ten cells. Nothing could see
it: every word was a legal field element of the right width, R8 bound its own four, and §19/§20's
`Field.equal` legs simply had no satisfying witness — which read as a missing derivation rather than
as a wiring defect.

## Where these numbers come from

They are §19/§20's own derivation over Mina devnet block 539508's Wrap proof, **with `finZW0`'s bend
removed** — i.e. at the fixed point this file creates. Each is
`Shifted_value.Type2.of_field x = x − 2^255` in Fq (`FIN_SHIFT2`), except ξ, which is the RAW
128-bit prechallenge (`spec.ml:374-392` packs a `Scalar Challenge` at `Challenge.length`).

  * `W_CIP` — `combined_inner_product`. ⚑ Its unshifted value is
    `MinaRealBlockGate.CIP`, the number **kimchi's own verifier** computed for that block
    (`real_cip`), reached here by §20's own `fnHorner` fold at ξ′ = `V_CHAL` and r′ = `U_CHAL`.
  * `W_B` — `challenge_polynomial ζ′ + r′ · challenge_polynomial ζ′ω` over the block's own fifteen
    lifted `bulletproof_challenges`, by §20's own `fnChalPoly`.
  * `W_ZETA_TO_SRS_LENGTH` — `ζ′^(2^15)`. ⚠ The exponent is `Common.Max_degree.wrap_log2`, NOT the
    step SRS's 16: openmina computes the tock deferred values at
    `srs_length_log2 = COMMON_MAX_DEGREE_WRAP_LOG2` (`step.rs:2416`, `wrap.rs:63-64`).
    `MinaWrapDeferred.SRS_LOG2 = 16` is the OTHER direction's constant and is not this one.
  * `W_ZETA_TO_DOMAIN_SIZE` — `ζ′^(2^14)`, that proof's own evaluation domain
    (`MinaRealBlockGate.N = 16384`). ⚑ **These two are DIFFERENT numbers**, where the aliased
    cells made them one; a 2^14 domain under a 2^15 SRS is exactly the case
    `MinaWrapDeferredWords.zeta_to_srs_length_and_zeta_to_domain_size_differ` names.
  * `W_PERM` — §19's own `perm` slot on the RAW evaluations, the derivation
    `finalize_reproduces_minas_own_ft_eval0` grounds against `FT0`/`LCT`/`PVP`.
  * `W_XI` — `MinaRealBlockTranscript.V_CHAL`, that proof's own first phase-2 squeeze. It is a
    literal here rather than a re-export so that this file's six read as one object; `the_xi_word_is
    _the_blocks_own_first_squeeze` is the tie and would red on a drift.

⚠ **THEY ARE PINNED WHERE THE DERIVATION LIVES, NOT HERE.** `KimchiWrapMainPins12`'s
`fin_deferred_words_are_the_derivation` and `the_step_block_deferred_words_are_the_wrap_derivation`
close all six against `finSpDerivedWords` / `finProbeData`, and `EmitWrapMainJson` refuses to emit a
tree where they disagree. This module carries no derivation because the derivation imports the
emitter and the step emitter imports this.

Axiom-clean: `by decide` only.
-/
import Dregg2.Circuit.Emit.PastaField

namespace Dregg2.Circuit.Emit.MinaWrapProofDeferredWords

open Dregg2.Circuit.Emit.PastaField (qN pN)

set_option autoImplicit false

/-! ## §1 — the six words. -/

/-- `combined_inner_product`, `Shifted_value.Type2`. -/
def W_CIP : Nat :=
  4948131480779179767533860900716273684010679778258760290444080737653528451353
/-- `b`, `Shifted_value.Type2`. -/
def W_B : Nat :=
  20846775326728031180490951156371883396580735244757996335468777305275483421443
/-- `zeta_to_srs_length` = `ζ′^(2^15)`, `Shifted_value.Type2`. -/
def W_ZETA_TO_SRS_LENGTH : Nat :=
  15199112795516872416106212443861736900027722155263374109965725473374133477727
/-- `zeta_to_domain_size` = `ζ′^(2^14)`, `Shifted_value.Type2`. -/
def W_ZETA_TO_DOMAIN_SIZE : Nat :=
  20843391792192674096379110139698302699652793514591289293589015707367300678770
/-- `plonk.perm`, `Shifted_value.Type2`. -/
def W_PERM : Nat :=
  20751602151633737401462851548350130147583075324153608851655296296922853366235
/-- ξ — the RAW 128-bit prechallenge, `MinaRealBlockTranscript.V_CHAL`. -/
def W_XI : Nat := 330305781815358857211111367912836029937

/-- ⚑ Packed per-proof word `k` of the live block (`composition_types.ml:1268-1276`): `0` cip,
`1` b, `2` zeta_to_srs_length, `3` zeta_to_domain_size, `4` perm, `10` xi. Every other word of the
block is derived elsewhere in the step assembly (the digest, the four challenges, the fifteen
prechallenges, `should_finalize`) and this map does not answer for them — a `0` here would be a
value, so the caller reads it by the named slot. -/
def WORD (k : Nat) : Nat :=
  if k == 0 then W_CIP
  else if k == 1 then W_B
  else if k == 2 then W_ZETA_TO_SRS_LENGTH
  else if k == 3 then W_ZETA_TO_DOMAIN_SIZE
  else if k == 4 then W_PERM
  else W_XI

/-- The five `B Field` words, in per-proof word order. -/
def FIELD_WORDS : List Nat :=
  [W_CIP, W_B, W_ZETA_TO_SRS_LENGTH, W_ZETA_TO_DOMAIN_SIZE, W_PERM]

/-! ## §2 — the checks that make this a statement about the right OBJECT. -/

/-- ⚑ **`the_five_field_words_are_fq_elements_and_their_halves_are_fp_ones`** — the two-field fact
this whole file turns on, discharged rather than asserted.

A `Shifted_value.Type2` word is an **Fq** element, and `q > p`, so it does NOT fit one Fp cell —
which is the entire reason `Spec.pack` splits a `B Field` into `(hi, is_odd)`
(`spec.ml:374-392`, `impls.ml:94-101`). Leg 1 is that the words really are Fq elements; leg 2 is
that the `hi` half a step circuit publishes really is an Fp one; leg 3 is that leg 2 is not free —
`q` itself has no Fp `hi` half, so a word wider than `q` would fail it.

⚠ The old aliased cells satisfied leg 1 for a different reason — they were **Fp** values, which are
Fq elements too. That is why no width instrument ever saw the defect. -/
theorem the_five_field_words_are_fq_elements_and_their_halves_are_fp_ones :
    FIELD_WORDS.all (fun w => decide (w < qN)) = true
    ∧ FIELD_WORDS.all (fun w => decide (w / 2 < pN)) = true
    ∧ FIELD_WORDS.all (fun w => decide (w / 2 < 2 ^ 254)) = true
    -- ⚑ …and the halving is not vacuous: an Fq element at the top of the range still has an Fp
    -- half, but an Fp-sized bound on the WORD would be false of at least one of them.
    ∧ (qN - 1) / 2 < pN
    ∧ FIELD_WORDS.length = 5 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- ⚑ **`the_xi_word_is_a_raw_prechallenge_and_the_field_words_are_not`** — the width signature, the
same discrimination `MinaWrapDeferredWords.the_width_signature_is_minas_own_layout` runs on the
forty. `spec.ml:374-392` packs a `Scalar Challenge` at `Challenge.length = 128`; a 255-bit endo lift
parked here is the classic defect and nothing but this inequality sees it. -/
theorem the_xi_word_is_a_raw_prechallenge_and_the_field_words_are_not :
    W_XI < 2 ^ 128
    ∧ FIELD_WORDS.all (fun w => decide (2 ^ 128 ≤ w)) = true := by
  refine ⟨?_, ?_⟩ <;> decide

/-- ⚑⚑ **`the_two_zeta_powers_differ`** — and that they differ is the REPAIR, not decoration.

The aliased map gave `zeta_to_srs_length` and `zeta_to_domain_size` ONE cell (`ftcDiv2 1`), on the
argument that upstream they agree at `log2n = srs_length_log2`. This proof does not sit there: its
domain is `2^14` (`MinaRealBlockGate.N`) and the tock SRS is `2^15`
(`Common.Max_degree.wrap_log2`), so they are two different field elements and a single cell could
not have carried both. `KimchiStepStatementPins.the_statement_slots_are_all_distinct` is the other
end of this. -/
theorem the_two_zeta_powers_differ : W_ZETA_TO_SRS_LENGTH ≠ W_ZETA_TO_DOMAIN_SIZE := by decide

/-- **`the_six_are_pairwise_distinct`** — the anti-vacuity. Six aliases of one number would satisfy
every other check in this file, and the defect this module exists to retire was *exactly* an
aliasing. -/
theorem the_six_are_pairwise_distinct :
    [W_CIP, W_B, W_ZETA_TO_SRS_LENGTH, W_ZETA_TO_DOMAIN_SIZE, W_PERM, W_XI].Nodup := by decide

/-- **`WORD_is_the_named_slots`** — the map and the names agree, so a reader can see it and a
re-index cannot pass silently. -/
theorem WORD_is_the_named_slots :
    WORD 0 = W_CIP ∧ WORD 1 = W_B ∧ WORD 2 = W_ZETA_TO_SRS_LENGTH
    ∧ WORD 3 = W_ZETA_TO_DOMAIN_SIZE ∧ WORD 4 = W_PERM ∧ WORD 10 = W_XI
    ∧ (List.range 5).map WORD = FIELD_WORDS := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  decide

#assert_namespace_axioms Dregg2.Circuit.Emit.MinaWrapProofDeferredWords

end Dregg2.Circuit.Emit.MinaWrapProofDeferredWords
