/-
# Dregg2.Circuit.Emit.PicklesStepStatement — `Types.Step.Statement`, DERIVED, not transcribed.

⚑ **WHAT THIS MODULE IS FOR.** `KimchiStepWrapChain`'s retired
`the_chain_stops_at_split_because_there_is_no_packed_statement` said the wrap ladder above `w6_xhat`
reads the packed words of a `Types.Step.Statement` and *"dregg's step proof has no such statement —
its public input is twelve unconstrained `Fp` elements."* The repair was on the STEP side: the step
circuit's public input has to **be** a step statement. ⚑ **It is, since 2026-08-06** — the ceiling
moved to `the_chain_stops_at_the_statements_derived_words`, which is about six WORDS and not about
the object's shape. This module is the statement's SHAPE, derived
from the OCaml spec and cross-checked against openmina's Rust, so that neither the step emitter nor
the wrap-side x_hat table has to carry a transcribed constant.

⚠ ⚑ **THE CLASS OF DEFECT THIS EXISTS TO KILL** is the one that cost `w4_bind` slot 29 two weeks:
`chainBranch.logs` was hardcoded **16** because 16 is Mina's `step-transaction` domain, so
`branch_data` packed `4·16+3 = 67` against the measured `51 = 4·12+3`. A packed statement is exactly
where a borrowed constant lives. Every number below is either read at a cited line or computed from
ones that are, and the totals are theorems rather than literals.

## §0 — AT SOURCE

### The type (`mina/src/lib/pickles/composition_types/composition_types.ml`)

`module Step.Statement` (`:1414-1425`)

    type ('unfinalized_proofs, 'messages_for_next_step_proof, 'messages_for_next_wrap_proof) t =
      { proof_state : ('unfinalized_proofs, 'messages_for_next_step_proof) Proof_state.t
      ; messages_for_next_wrap_proof : 'messages_for_next_wrap_proof }

`Step.Proof_state` (`:1359-1367`) is `{ unfinalized_proofs; messages_for_next_step_proof }`, and the
LAYOUT is `Statement.spec` (`:1453-1459`):

    let spec proofs_verified bp_log2 =
      let per_proof = Proof_state.Per_proof.In_circuit.spec bp_log2 in
      Spec.T.Struct [ Vector (per_proof, proofs_verified) ; B Digest ; Vector (B Digest, proofs_verified) ]

with `Per_proof.In_circuit.spec` (`:1265-1274`)

    Spec.T.Struct
      [ Vector (B Field, Nat.N5.n)          (* combined_inner_product, b,
                                               zeta_to_srs_length, zeta_to_domain_size, perm *)
      ; Vector (B Digest, Nat.N1.n)         (* sponge_digest_before_evaluations *)
      ; Vector (B Challenge, Nat.N2.n)      (* beta, gamma *)
      ; Vector (Scalar Challenge, Nat.N3.n) (* alpha, zeta, xi *)
      ; Vector (B Bulletproof_challenge, bp_log2)
      ; Vector (B Bool, Nat.N1.n) ]         (* should_finalize *)

The FIELD ORDER inside a block is `Per_proof.In_circuit.to_data` (`:1279-1315`), which is what fixes
`combined_inner_product` at 0 and `should_finalize` last; the STATEMENT order is `Statement.to_data`
(`:1427-1436`), `[unfinalized_proofs; messages_for_next_step_proof; messages_for_next_wrap_proof]`.

`bp_log2` is **`Backend.Tock.Rounds.n`**, hardcoded at `Per_proof.typ` (`:1352`,
`Spec.typ impl fq ~assert_16_bits (spec Backend.Tock.Rounds.n)`) — the WRAP proof's IPA rounds,
**15**, and NOT `Backend.Tick.Rounds.n = 16`, which is the STEP proof's own and is what
`Step_bp_vec` / `StepShape.bRounds` count. ⚑ Those two numbers differ by one and name different
objects; conflating them is the borrowed-constant class in its purest form.

### The width of one word, in the STEP circuit (`mina/src/lib/pickles/impls.ml`)

`Impls.Step.input` (`:128-142`) is `Spec.packed_typ (module Impl) (T (Shifted_value.Type2.typ
Other_field.typ_unchecked, …)) spec`. So under `packed_typ_basic`
(`composition_types/spec.ml:435-488`) every basic is ONE `Field` wire —

    Digest ↦ Digest.typ · Challenge ↦ Challenge.typ · Bulletproof_challenge ↦ (transport of
    Challenge.typ) · Bool ↦ Boolean.typ

— and the ONE exception is `Field`, which is the `field` ETyp the caller supplies:
`Step.Other_field.typ_unchecked` (`impls.ml:90-101`)

    Typ.transport (Typ.tuple2 Field.typ Boolean.typ)
      ~there:(fun x -> match Tock.Field.to_bits x with
                       | low :: high -> (Field.Constant.project high, low))

⚑ **THAT IS `(x >> 1, x land 1)` — `split_field`'s pair, not "low bits, high bit".** The comment
above the type at `impls.ml:56` says *"Low bits, high bit"* and the transport says otherwise; the
transport is what the circuit gets. It is why the wrap side's `split_field`
(`wrap_main.ml:51-81`, `2·y + is_odd = x`) recomposes the step proof's own public words rather than
re-encoding them, and why one `B Field` is TWO step public words.

### The same layout, in openmina's Rust — an INDEPENDENT implementation

* `ledger/src/proofs/unfinalized.rs:371-435`, `impl<F: FieldWitness> ToFieldElements<F> for
  Unfinalized`: pushes `combined_inner_product.shifted`, `b.shifted`, `zeta_to_srs_length.shifted`,
  `zeta_to_domain_size.shifted`, `perm.shifted`, then the digest, then `beta`/`gamma`, then
  `alpha`/`zeta`/`xi`, then `bulletproof_challenges`, then `should_finalize`. Same order as
  `to_data`.
* `ledger/src/proofs/to_field_elements.rs:213-233`, `impl<F> ToFieldElements<F> for Fq`: when `F`
  is not `Fq`,
  `let [low, high @ ..] = field_to_bits::<Fq, 255>(fq); [field_of_bits(&high), F::from(low)]` —
  **hi first, then the parity bit**, citing `impls.ml:94-105` for it. Two field elements per `Fq`.
* `ledger/src/proofs/to_field_elements.rs:834-849`, `impl ToFieldElements<Fp> for StepMainStatement`:
  `unfinalized_proofs`, then `messages_for_next_step_proof`, then `messages_for_next_wrap_proof`.
* `ledger/src/proofs/constants.rs:39,46,53,84,113,120`: every compiled STEP circuit has
  `const PRIMARY_LEN: usize = 67`, and every WRAP one has `40` (`:91,106`). **67 is the number this
  module has to reproduce, and it is reproduced by `step_statement_words_is_minas_primary_len`
  rather than written down.**

## §1 — WHAT THIS MODULE DOES NOT SAY

It says nothing about which circuit variable holds a slot, nothing about whether a slot is derived
or witnessed, and nothing about any proof. Those are `KimchiStepMainCore`'s (§24) and the wrap
side's. This is the SHAPE alone, so that both sides read one source.
-/
import Dregg2.Tactics

namespace Dregg2.Circuit.Emit.PicklesStepStatement

set_option autoImplicit false

/-! ## §2 — the counts, each at a cited line. -/

/-- `Nat.N5.n` — `Vector (B Field, Nat.N5.n)` (`composition_types.ml:1268`). -/
def PP_FIELDS : Nat := 5
/-- `Nat.N1.n` — `Vector (B Digest, Nat.N1.n)` (`:1269`), `sponge_digest_before_evaluations`. -/
def PP_DIGESTS : Nat := 1
/-- `Nat.N2.n` — `Vector (B Challenge, Nat.N2.n)` (`:1270`), `beta` and `gamma`. -/
def PP_CHALLENGES : Nat := 2
/-- `Nat.N3.n` — `Vector (Scalar Challenge, Nat.N3.n)` (`:1271`), `alpha`, `zeta`, `xi`. -/
def PP_SCALAR_CHALLENGES : Nat := 3
/-- `bp_log2 = Backend.Tock.Rounds.n` (`:1272` at `:1352`) — the WRAP proof's IPA rounds. ⚠ NOT
`Backend.Tick.Rounds.n = 16`. -/
def PP_BP_LOG2 : Nat := 15
/-- `Nat.N1.n` — `Vector (B Bool, Nat.N1.n)` (`:1273`), `should_finalize`. -/
def PP_BOOLS : Nat := 1
/-- `Max_proofs_verified.n` — `Statement.spec`'s `proofs_verified` (`:1453`), which for every
compiled Mina step rule and for the wrap circuits that verify them is **2**
(`wrap_main.ml:96-105`; `KimchiWrapMainField.XHAT_PREVS`). -/
def STMT_PREVS : Nat := 2

/-- ⚑ How many STEP public words one `B Field` occupies: `Step.Other_field.typ_unchecked` is a
`Typ.tuple2 Field.typ Boolean.typ` (`impls.ml:90-101`), so **two** — the `hi` and the parity. -/
def FIELD_WORDS : Nat := 2

/-! ## §3 — the derived layout. -/

/-- Words one `per_proof` block occupies in the STEP circuit's public input. **Computed**, from §2. -/
def PP_WORDS : Nat :=
  FIELD_WORDS * PP_FIELDS + PP_DIGESTS + PP_CHALLENGES + PP_SCALAR_CHALLENGES + PP_BP_LOG2 + PP_BOOLS

/-- ⚑ **The step statement's width** — `Struct [Vector (per_proof, prevs); B Digest;
Vector (B Digest, prevs)]` (`composition_types.ml:1455-1458`). **Computed.** -/
def STMT_WORDS : Nat := PP_WORDS * STMT_PREVS + 1 + STMT_PREVS

/-- Where `messages_for_next_step_proof` sits — one `B Digest` after the blocks. -/
def SLOT_MSG_NEXT_STEP : Nat := PP_WORDS * STMT_PREVS
/-- …and `messages_for_next_wrap_proof j`. -/
def slotMsgNextWrap (j : Nat) : Nat := SLOT_MSG_NEXT_STEP + 1 + j

/-- The packed-WORD count of the same object — what `Spec.pack` produces in the WRAP circuit, where
an `Fq` value is native and occupies ONE wire (`impls.ml:167-217`). `wrap_main.ml:406-411` then
`split_field`s each of them back into the two the step published. ⚑ Stated here so the 57 and the 67
have one source and cannot drift apart. -/
def PP_PACKED_WORDS : Nat :=
  PP_FIELDS + PP_DIGESTS + PP_CHALLENGES + PP_SCALAR_CHALLENGES + PP_BP_LOG2 + PP_BOOLS
/-- **57.** -/
def STMT_PACKED_WORDS : Nat := PP_PACKED_WORDS * STMT_PREVS + 1 + STMT_PREVS

/-! ### §3a — which FIELD a slot is. -/

/-- The named position of one step-statement public word. -/
inductive Slot where
  /-- `per_proof` block `b`, `B Field` number `f` (0 = `combined_inner_product`, 1 = `b`,
  2 = `zeta_to_srs_length`, 3 = `zeta_to_domain_size`, 4 = `perm`), `hi` half. -/
  | fieldHi   (b f : Nat)
  /-- …and its parity half — `split_field`'s `is_odd`. -/
  | fieldOdd  (b f : Nat)
  /-- `sponge_digest_before_evaluations` of block `b`. -/
  | digest    (b : Nat)
  /-- `beta` (`c = 0`) / `gamma` (`c = 1`) of block `b`. -/
  | challenge (b c : Nat)
  /-- `alpha` (`c = 0`) / `zeta` (`c = 1`) / `xi` (`c = 2`) of block `b`. -/
  | scalarChallenge (b c : Nat)
  /-- `bulletproof_challenges.(k)` of block `b`, `k < PP_BP_LOG2`. -/
  | bpChallenge (b k : Nat)
  /-- `should_finalize` of block `b`. -/
  | shouldFinalize (b : Nat)
  /-- `messages_for_next_step_proof`. -/
  | msgNextStep
  /-- `messages_for_next_wrap_proof.(j)`. -/
  | msgNextWrap (j : Nat)
  /-- Past the end of the statement. -/
  | outOfRange
  deriving Repr, DecidableEq, Inhabited

/-- ⚑ Slot `i`'s field, decoded from §3's arithmetic. -/
def slotOf (i : Nat) : Slot :=
  if i ≥ STMT_WORDS then .outOfRange
  else if i = SLOT_MSG_NEXT_STEP then .msgNextStep
  else if i > SLOT_MSG_NEXT_STEP then .msgNextWrap (i - SLOT_MSG_NEXT_STEP - 1)
  else
    let b := i / PP_WORDS
    let j := i % PP_WORDS
    if j < FIELD_WORDS * PP_FIELDS then
      (if j % FIELD_WORDS = 0 then .fieldHi b (j / FIELD_WORDS)
       else .fieldOdd b (j / FIELD_WORDS))
    else
      let j := j - FIELD_WORDS * PP_FIELDS
      if j < PP_DIGESTS then .digest b
      else
        let j := j - PP_DIGESTS
        if j < PP_CHALLENGES then .challenge b j
        else
          let j := j - PP_CHALLENGES
          if j < PP_SCALAR_CHALLENGES then .scalarChallenge b j
          else
            let j := j - PP_SCALAR_CHALLENGES
            if j < PP_BP_LOG2 then .bpChallenge b j
            else .shouldFinalize b

/-! ### §3b — the WIDTH of a slot, and it is the whole load-bearing half.

The wrap circuit scales lagrange base `i` by step public word `i` under `Ops.scale_fast2'
~num_bits` (`wrap_verifier.ml:539-609`), and `scale_fast2` ASSERTS the top
`actual_bits_used − (num_bits − 1)` bits zero (`plonk_curve_ops.ml:262-265`). So a step public word
wider than the slot's declared width is a proof the wrap circuit refuses, and a one-bit slot that is
not boolean fails `Constraint.boolean` at `wrap_verifier.ml:574`. These widths are therefore an
obligation on the STEP emitter, not a description of the wrap. -/

/-- `Field.size_in_bits` — `B Field`'s `hi` half and every `B Digest`. -/
def W_FIELD : Nat := 255
/-- `Challenge.length = 64 · Nat.to_int N2` (`limb_vector/constant.ml`) — `B Challenge`,
`Scalar Challenge`, `B Bulletproof_challenge`. -/
def W_CHAL : Nat := 128
/-- `B Bool`, and the parity half of every split `B Field`. -/
def W_BOOL : Nat := 1

/-- Slot `i`'s packed bit width. -/
def slotBits (i : Nat) : Nat :=
  match slotOf i with
  | .fieldHi _ _ => W_FIELD
  | .fieldOdd _ _ => W_BOOL
  | .digest _ => W_FIELD
  | .challenge _ _ => W_CHAL
  | .scalarChallenge _ _ => W_CHAL
  | .bpChallenge _ _ => W_CHAL
  | .shouldFinalize _ => W_BOOL
  | .msgNextStep => W_FIELD
  | .msgNextWrap _ => W_FIELD
  | .outOfRange => 0

/-- ⚑ **WHICH PACKED WORD SLOT `i` CAME OUT OF** — the inverse of `wrap_verifier.ml:542-548`. A
`B Field` contributes two slots and one packed word, everything else one of each, so the map is
many-to-one on exactly the split pairs and injective elsewhere. -/
def packedWordOf (i : Nat) : Nat :=
  if i ≥ SLOT_MSG_NEXT_STEP then PP_PACKED_WORDS * STMT_PREVS + (i - SLOT_MSG_NEXT_STEP)
  else
    let b := i / PP_WORDS
    let j := i % PP_WORDS
    PP_PACKED_WORDS * b + (if j < FIELD_WORDS * PP_FIELDS then j / FIELD_WORDS
                           else j - PP_FIELDS)

/-! ## §4 — the totals, as THEOREMS. -/

/-- **`step_statement_words_is_minas_primary_len`** — ⚑ the number this module exists to reproduce.
`67` is not written anywhere above: it is `2·(2·5 + 1 + 2 + 3 + 15 + 1) + 1 + 2`, and openmina's
`constants.rs:39,46,53,84,113,120` gives the same figure for six independently declared step
circuits. The `40` beside it is the WRAP `PRIMARY_LEN` (`constants.rs:91,106`) and is stated only so
that a future edit that confused the two goes red here. -/
theorem step_statement_words_is_minas_primary_len :
    PP_WORDS = 32
    ∧ STMT_WORDS = 67
    ∧ STMT_PACKED_WORDS = 57
    ∧ PP_PACKED_WORDS = 27
    ∧ SLOT_MSG_NEXT_STEP = 64
    ∧ slotMsgNextWrap 0 = 65 ∧ slotMsgNextWrap 1 = 66
    ∧ STMT_WORDS ≠ 40 := by decide

#assert_axioms step_statement_words_is_minas_primary_len

/-- **`the_bp_log2_is_tocks_rounds_not_ticks`** — ⚑ the borrowed-constant tripwire, named. `bp_log2`
is `Backend.Tock.Rounds.n = 15` (`composition_types.ml:1352`); the step proof's own IPA has
`Backend.Tick.Rounds.n = 16` rounds (`Step_bp_vec`, `StepShape.bRounds`). Off by one, and the two
totals they produce differ by two. -/
theorem the_bp_log2_is_tocks_rounds_not_ticks :
    PP_BP_LOG2 = 15
    ∧ PP_BP_LOG2 + 1 = 16
    ∧ (FIELD_WORDS * PP_FIELDS + PP_DIGESTS + PP_CHALLENGES + PP_SCALAR_CHALLENGES
        + (PP_BP_LOG2 + 1) + PP_BOOLS) * STMT_PREVS + 1 + STMT_PREVS = 69
    ∧ STMT_WORDS ≠ 69 := by decide

#assert_axioms the_bp_log2_is_tocks_rounds_not_ticks

/-- **`the_slot_decoder_is_total_and_the_census_closes`** — every slot below `STMT_WORDS` decodes to
a real field, the field census has exactly the multiplicities `Statement.spec` declares, and slot
`STMT_WORDS` is out of range. A decoder that silently folded two fields onto one name would still be
total; the census is what refuses it. -/
theorem the_slot_decoder_is_total_and_the_census_closes :
    ((List.range STMT_WORDS).filter (fun i => slotOf i = .outOfRange)).length = 0
    ∧ slotOf STMT_WORDS = .outOfRange
    ∧ ((List.range STMT_WORDS).filter (fun i =>
        match slotOf i with | .fieldHi _ _ => true | _ => false)).length
       = PP_FIELDS * STMT_PREVS
    ∧ ((List.range STMT_WORDS).filter (fun i =>
        match slotOf i with | .fieldOdd _ _ => true | _ => false)).length
       = PP_FIELDS * STMT_PREVS
    ∧ ((List.range STMT_WORDS).filter (fun i =>
        match slotOf i with | .digest _ => true | _ => false)).length
       = PP_DIGESTS * STMT_PREVS
    ∧ ((List.range STMT_WORDS).filter (fun i =>
        match slotOf i with | .challenge _ _ => true | _ => false)).length
       = PP_CHALLENGES * STMT_PREVS
    ∧ ((List.range STMT_WORDS).filter (fun i =>
        match slotOf i with | .scalarChallenge _ _ => true | _ => false)).length
       = PP_SCALAR_CHALLENGES * STMT_PREVS
    ∧ ((List.range STMT_WORDS).filter (fun i =>
        match slotOf i with | .bpChallenge _ _ => true | _ => false)).length
       = PP_BP_LOG2 * STMT_PREVS
    ∧ ((List.range STMT_WORDS).filter (fun i =>
        match slotOf i with | .shouldFinalize _ => true | _ => false)).length
       = PP_BOOLS * STMT_PREVS
    ∧ ((List.range STMT_WORDS).filter (fun i => slotOf i = .msgNextStep)).length = 1
    ∧ ((List.range STMT_WORDS).filter (fun i =>
        match slotOf i with | .msgNextWrap _ => true | _ => false)).length = STMT_PREVS := by
  decide

#assert_axioms the_slot_decoder_is_total_and_the_census_closes

/-- **`the_slot_decoder_is_injective`** — and it names each occurrence ONCE. Without this the census
above is consistent with `slotOf` handing every block-1 slot block 0's index, which is precisely how
a two-proof statement silently becomes one proof twice. -/
theorem the_slot_decoder_is_injective :
    ((List.range STMT_WORDS).map slotOf).eraseDups.length = STMT_WORDS := by decide

#assert_axioms the_slot_decoder_is_injective

/-- **`the_first_block_is_to_datas_order`** — ⚑ the ORDER, spelled out slot by slot for block 0
against `Per_proof.In_circuit.to_data` (`composition_types.ml:1279-1315`) and openmina's
`ToFieldElements for Unfinalized` (`unfinalized.rs:396-434`). This is where a permuted field list
would be caught: every count above is invariant under permutation. -/
theorem the_first_block_is_to_datas_order :
    slotOf 0 = .fieldHi 0 0            -- combined_inner_product
    ∧ slotOf 1 = .fieldOdd 0 0
    ∧ slotOf 2 = .fieldHi 0 1          -- b
    ∧ slotOf 3 = .fieldOdd 0 1
    ∧ slotOf 4 = .fieldHi 0 2          -- zeta_to_srs_length
    ∧ slotOf 5 = .fieldOdd 0 2
    ∧ slotOf 6 = .fieldHi 0 3          -- zeta_to_domain_size
    ∧ slotOf 7 = .fieldOdd 0 3
    ∧ slotOf 8 = .fieldHi 0 4          -- perm
    ∧ slotOf 9 = .fieldOdd 0 4
    ∧ slotOf 10 = .digest 0            -- sponge_digest_before_evaluations
    ∧ slotOf 11 = .challenge 0 0       -- beta
    ∧ slotOf 12 = .challenge 0 1       -- gamma
    ∧ slotOf 13 = .scalarChallenge 0 0 -- alpha
    ∧ slotOf 14 = .scalarChallenge 0 1 -- zeta
    ∧ slotOf 15 = .scalarChallenge 0 2 -- xi
    ∧ slotOf 16 = .bpChallenge 0 0
    ∧ slotOf 30 = .bpChallenge 0 14
    ∧ slotOf 31 = .shouldFinalize 0
    ∧ slotOf 32 = .fieldHi 1 0         -- block 1 starts here
    ∧ slotOf 63 = .shouldFinalize 1
    ∧ slotOf 64 = .msgNextStep
    ∧ slotOf 65 = .msgNextWrap 0
    ∧ slotOf 66 = .msgNextWrap 1 := by decide

#assert_axioms the_first_block_is_to_datas_order

/-- **`the_width_census_is_minas_var_base_mul_partition`** — the widths, counted. ⚑ This is the leg
that reaches OUTSIDE this module: Mina's own compiled `wrap-transaction` circuit reports
**`VarBaseMul 2417`**, of which W-XHAT's share is `15 × chunks_needed 254 + 40 × chunks_needed 127 =
15 × 51 + 40 × 26 = 1805` (`KimchiWrapMainField` §15). `15` is the count of 255-bit slots here and
`40` the count of 128-bit ones, so a wrong `PP_BP_LOG2`, a wrong `PP_FIELDS` or a wrong `STMT_PREVS`
misses a number measured off a third-party artifact. -/
theorem the_width_census_is_minas_var_base_mul_partition :
    (((List.range STMT_WORDS).map slotBits).filter (· = W_FIELD)).length = 15
    ∧ (((List.range STMT_WORDS).map slotBits).filter (· = W_CHAL)).length = 40
    ∧ (((List.range STMT_WORDS).map slotBits).filter (· = W_BOOL)).length = 12
    ∧ 15 + 40 + 12 = STMT_WORDS
    ∧ 15 * ((254 + 4) / 5) + 40 * ((127 + 4) / 5) = 1805 := by decide

#assert_axioms the_width_census_is_minas_var_base_mul_partition

/-- **`the_packed_word_map_is_many_to_one_on_exactly_the_split_pairs`** — `packedWordOf` is the
inverse of the wrap's `` `Field `` expansion. It hits every packed word, it is two-to-one on a slot
pair iff that pair is a `B Field`, and it is injective everywhere else. ⚑ `w7_split`'s `2·hi +
is_odd = x` is an identity on the STEP proof's own public words exactly because of this map. -/
theorem the_packed_word_map_is_many_to_one_on_exactly_the_split_pairs :
    ((List.range STMT_WORDS).map packedWordOf).eraseDups.length = STMT_PACKED_WORDS
    ∧ (List.range STMT_PACKED_WORDS).all (fun w =>
        ((List.range STMT_WORDS).map packedWordOf).contains w) = true
    ∧ (List.range STMT_WORDS).all (fun i => decide (packedWordOf i < STMT_PACKED_WORDS)) = true
    ∧ (List.range STMT_WORDS).all (fun i =>
        (((List.range STMT_WORDS).filter (fun k => packedWordOf k == packedWordOf i)).length == 2)
          == (match slotOf i with | .fieldHi _ _ | .fieldOdd _ _ => true | _ => false)) = true
    ∧ (List.range STMT_WORDS).all (fun i =>
        match slotOf i with
        | .fieldHi _ _ => packedWordOf (i + 1) = packedWordOf i
        | _ => true) = true
    -- ⚑ and the three trailing digests land on the packed words `wrap_main.ml:350-351` ties.
    ∧ packedWordOf SLOT_MSG_NEXT_STEP = 54
    ∧ packedWordOf (slotMsgNextWrap 0) = 55
    ∧ packedWordOf (slotMsgNextWrap 1) = 56 := by decide

#assert_axioms the_packed_word_map_is_many_to_one_on_exactly_the_split_pairs

/-! ## §5 — the DUMMY block, at source.

⚠ `Max_proofs_verified.n = 2` and a rule that recursively verifies fewer proofs still publishes two
`per_proof` blocks: `step_main.ml:568-570` is
`Vector.extend_front unfinalized_proofs_unextended lte (Unfinalized.Constant.dummy ())`, and the
padding block's `should_finalize` is `Boolean.false_` (`step_main.ml:405-425`'s `should_verify`
vector). `wrap_main.ml:333` then discharges it — `Boolean.(Assert.any [finalized; not
should_finalize])` — so a padding block's other 31 words carry no obligation UPSTREAM either.

⚑ **`extend_front`, so the padding block is block 0 and the real one is the LAST.** That is the same
suffix convention `Proofs_verified.Prefix_mask` uses (`pickles_base/proofs_verified.ml:75-81`,
`N1 ↦ [ff;tt]`), and getting it backwards would put the derived block where the verifier expects the
dummy. -/

/-- Which block a `proofs_verified = n` rule's REAL proofs occupy — the SUFFIX, by
`Vector.extend_front`. -/
def realBlocks (actual : Nat) : List Nat :=
  (List.range STMT_PREVS).filter (fun b => b + actual ≥ STMT_PREVS)

/-- **`the_padding_block_is_the_front`** — with one actual previous proof the real block is 1 and
the dummy is 0; with two, both are real; with none, neither. -/
theorem the_padding_block_is_the_front :
    realBlocks 0 = []
    ∧ realBlocks 1 = [1]
    ∧ realBlocks 2 = [0, 1] := by decide

#assert_axioms the_padding_block_is_the_front

end Dregg2.Circuit.Emit.PicklesStepStatement
