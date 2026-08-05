/-
# `MinaWrapDeferredWords` — the forty words Pickles hands the wrap circuit, MEASURED

## ⚑ SAY THE SUBSTRATE OUT LOUD

**This is Lean-authored data, not a constraint.** Nothing here emits a gate. It is the VALUE layer
that `KimchiWrapMain`'s W-FTCOMM / W-COMBINE / W-BULLET read where upstream reads the public words,
and House Law #1 is untouched: the AIR stays Lean-authored and Rust only produced the measurement.

## Where these numbers come from

`metatheory/fixtures/pickles-extractors/src/bin/pickles_kimchi_marshal.rs` proves a **step** rung on
Vesta over **Mina's own SRS** (`get_srs::<Fp>()`, 65,536 generators), reads its Fiat-Shamir
transcript, computes the IPA accumulator, and hands the assembled statement to openmina's own
`PreparedStatement::to_public_input(40)`
(`/Users/ember/dev/mina-rust/crates/ledger/src/proofs/public_input/prepared_statement.rs:53-182`).
That is Mina's function, not ours. It writes `wrap-public-input.json`; this list is that file.

⚑ **THE PROVER'S BLINDING RNG IS SEEDED, WHICH IS WHAT MAKES THIS A FIXTURE AND NOT A SNAPSHOT.**
It was `OsRng` until 2026-08-05, so every run produced a different step proof and therefore a
different forty. A constant carrying them would have been stale the moment the binary was re-run,
and the loop (run -> read -> bake -> re-emit) would have had no fixed point at all. Two consecutive
runs are now byte-identical in `wrap-public-input.json`, `marshalled.binprot` and the o1js proof.
Re-derive with:

    cargo run --release --manifest-path metatheory/fixtures/pickles-extractors/Cargo.toml \
      --bin pickles_kimchi_marshal -- <out-dir>

## ⚠ What these are, and what they are NOT

They ARE a real instance of the right object: `expand_deferred`'s recomputation over a real step
proof's transcript, in Mina's own slot order and Mina's own encodings. They are NOT a devnet block's
-- `MinaWrapPublicCommGate.PUBLIC_INPUT` is that, and it is a different proof. And baking them here
does NOT make the wrap assembly a wrap proof OF that step proof: the assembly's own transcript runs
over fixture commitments, so the twenty-four slots this circuit DERIVES are its own transcript's and
do not agree with the ones below. **Only slots 0-4 and 9 -- the six `wrap_main` never derives --
come from here.** The rest of this list is carried so the width signature and the tail can be
checked against the same source.

## ⚑ The object at each slot, which is the thing a slot map gets wrong

Widths are the tell, and they are checked below rather than asserted. `spec.ml:374-392` packs
`Challenge` / `Scalar Challenge` / `Bulletproof_challenge` at `Challenge.length = 128` -- the RAW
prechallenge -- where `Digest` packs at `Field.size_in_bits`. A slot carrying the 255-bit endo lift
where the raw prechallenge belongs is the classic defect: the right name over the wrong object, and
nothing but the width sees it. `the_width_signature_is_minas_own_layout` is that check.

⚑ **And slots 0-4 are each `.shifted`** (`prepared_statement.rs:99-103`), a `Shifted_value.Type1`
and NOT the raw field value. `KimchiWrapMainCore` consumes them in exactly that representation
(`:1973`, `:4145-4147`), so the number below is fed straight in with no un-shift.

Axiom-clean: `by decide` only; no `sorry`, no `native_decide`.
-/
import Dregg2.Tactics
import Dregg2.Circuit.Emit.PastaField

namespace Dregg2.Circuit.Emit.MinaWrapDeferredWords

open Dregg2.Circuit.Emit.PastaField (qN)

set_option autoImplicit false

/-! ## §1 -- the measurement -/

/-- `PreparedStatement::to_public_input(40)` on the step proof `pickles_kimchi_marshal` produces,
in Mina's own slot order. Every entry is an `Fq` element (the wrap circuit's native field). -/
def WRAP_PUBLIC_INPUT_MEASURED : List Nat :=
  [
   22284869044986469162165098211143316880523564756208830887002609545233449709446, --  0  combined_inner_product
   13138257128309824195628490709153312727165455573086445095212006788559341811944, --  1  b
   17646684539304096018870193388803846013630819028633179290622047878493315030214, --  2  zeta_to_srs_length
   11386279513587971191748895242014232601053572938200655488959140299127364359282, --  3  zeta_to_domain_size
   4119809465672603210119019427635453518306039812352285018016230252043794300351, --  4  perm
   228091183824791458622477481012809112668, --  5  beta
   229844152023682967515058356043050111612, --  6  gamma
   87115020008985166254378102357021179438, --  7  alpha
   274655810511566526597833994141723415532, --  8  zeta
   37084778632474038076316230091337377002, --  9  xi
   12778630524400508899448310503899219714586482561901003028569595051141072387594, -- 10  sponge_digest_before_evaluations
   2868530536923998789278655683977242909031588136711256025047245098003286435411, -- 11  messages_for_next_wrap_proof(hash)
   2140974966619622776015189267648243586732098598200249976162061600531359395435, -- 12  messages_for_next_step_proof(hash)
   206975714924955411806414103767889774892, -- 13  bulletproof_challenges[0]
   214234567061884437040978835446943480776, -- 14  bulletproof_challenges[1]
   272248178881407795576080583746709917475, -- 15  bulletproof_challenges[2]
   210262521791379005236999258511519247003, -- 16  bulletproof_challenges[3]
   211109081016354306462347821041088602604, -- 17  bulletproof_challenges[4]
   76767095381540916290922187518605199502, -- 18  bulletproof_challenges[5]
   247474208164094391585246920932061768883, -- 19  bulletproof_challenges[6]
   295798671929014582191134444595467554178, -- 20  bulletproof_challenges[7]
   191011485585866353382736447935909259894, -- 21  bulletproof_challenges[8]
   43020380821041210689848935156583728976, -- 22  bulletproof_challenges[9]
   247891321502998741152651741725275976783, -- 23  bulletproof_challenges[10]
   203560448917541712120939695610833012508, -- 24  bulletproof_challenges[11]
   116273666763829858738777886559161594845, -- 25  bulletproof_challenges[12]
   75391901764763883520229387704456941279, -- 26  bulletproof_challenges[13]
   78146419354457781626921553661725160800, -- 27  bulletproof_challenges[14]
   329435979011588804437253985159792020670, -- 28  bulletproof_challenges[15]
   51, -- 29  branch_data((domain_log2<<2)|proofs_verified)
   0, -- 30  feature_flags.range_check0
   0, -- 31  feature_flags.range_check1
   0, -- 32  feature_flags.foreign_field_add
   0, -- 33  feature_flags.foreign_field_mul
   0, -- 34  feature_flags.xor
   0, -- 35  feature_flags.rot
   0, -- 36  feature_flags.lookup
   0, -- 37  feature_flags.runtime_tables
   0, -- 38  uses_lookup
   0  -- 39  joint_combiner_or_zero
  ]

/-! ## §2 -- the six `wrap_main` READS and never DERIVES

`wrap_main.ml:405-414` passes these through as `~advice` / `~plonk` / `~xi`. It reads all six --
`combined_inner_product` and `b` in `check_bulletproof`, `perm` / `zeta_to_srs_length` /
`zeta_to_domain_size` in `ft_comm`, `xi` in `Split_commitments.combine` -- and CHECKS none. Their
checker is the NEXT proof's `finalize_other_proof`.

⚠ **Named by SLOT and defined by index into the measurement**, so a reader can see the two agree;
`the_deferred_six_are_the_named_slots` is what makes that agreement checked rather than claimed. -/
def DEF_CIP : Nat := WRAP_PUBLIC_INPUT_MEASURED.getD 0 0
def DEF_B : Nat := WRAP_PUBLIC_INPUT_MEASURED.getD 1 0
def DEF_ZETA_TO_SRS_LENGTH : Nat := WRAP_PUBLIC_INPUT_MEASURED.getD 2 0
def DEF_ZETA_TO_DOMAIN_SIZE : Nat := WRAP_PUBLIC_INPUT_MEASURED.getD 3 0
def DEF_PERM : Nat := WRAP_PUBLIC_INPUT_MEASURED.getD 4 0
def DEF_XI : Nat := WRAP_PUBLIC_INPUT_MEASURED.getD 9 0

/-- The slots whose object is a RAW 128-bit prechallenge (`Challenge` / `Scalar Challenge` /
`Bulletproof_challenge`, `spec.ml:374-392`). -/
def CHALLENGE_SLOTS : List Nat := [5, 6, 7, 8, 9] ++ (List.range 16).map (fun r => 13 + r)

/-- The slots whose object is a full `Fq` element: the five `.shifted` deferred values and the
three `Digest`s, which pack at `Field.size_in_bits`. -/
def FIELD_SLOTS : List Nat := [0, 1, 2, 3, 4, 10, 11, 12]

/-! ## §3 -- ⚑ THE CHECKS -/

/-- **`the_measurement_is_forty_reduced_words`** -- Mina's own width, and every entry reduced in the
wrap circuit's field. A word at or above `qN` is not an `Fq` element and could not have come from
`to_public_input`. -/
theorem the_measurement_is_forty_reduced_words :
    WRAP_PUBLIC_INPUT_MEASURED.length = 40
    ∧ WRAP_PUBLIC_INPUT_MEASURED.all (fun x => decide (x < qN)) = true := by
  refine ⟨?_, ?_⟩ <;> decide

/-- ⚑ **`the_width_signature_is_minas_own_layout`** -- THE OBJECT CHECK, slot by slot.

Every challenge slot is under `2^128` and every field slot is over `2^250`. This is what separates
"the right number at the right index" from "the right name over the wrong object": exposing the
255-bit endo lift where `spec.ml` packs the raw prechallenge moves no index and no count, and this
inequality is the only instrument in the file that sees it. The two sets are disjoint and together
with slots 29-39 they exhaust the forty. -/
theorem the_width_signature_is_minas_own_layout :
    CHALLENGE_SLOTS.all (fun i =>
      decide (WRAP_PUBLIC_INPUT_MEASURED.getD i 0 < 2 ^ 128)) = true
    ∧ FIELD_SLOTS.all (fun i =>
      decide (2 ^ 250 < WRAP_PUBLIC_INPUT_MEASURED.getD i 0)) = true
    ∧ CHALLENGE_SLOTS.length = 21 ∧ FIELD_SLOTS.length = 8 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- **`the_deferred_six_are_the_named_slots`** -- the six accessors are slots 0, 1, 2, 3, 4 and 9,
and no two of them coincide. The second half is the anti-vacuity: six aliases of one number would
satisfy every other check in this file. -/
theorem the_deferred_six_are_the_named_slots :
    DEF_CIP = WRAP_PUBLIC_INPUT_MEASURED.getD 0 0
    ∧ DEF_B = WRAP_PUBLIC_INPUT_MEASURED.getD 1 0
    ∧ DEF_ZETA_TO_SRS_LENGTH = WRAP_PUBLIC_INPUT_MEASURED.getD 2 0
    ∧ DEF_ZETA_TO_DOMAIN_SIZE = WRAP_PUBLIC_INPUT_MEASURED.getD 3 0
    ∧ DEF_PERM = WRAP_PUBLIC_INPUT_MEASURED.getD 4 0
    ∧ DEF_XI = WRAP_PUBLIC_INPUT_MEASURED.getD 9 0
    ∧ [DEF_CIP, DEF_B, DEF_ZETA_TO_SRS_LENGTH, DEF_ZETA_TO_DOMAIN_SIZE, DEF_PERM,
       DEF_XI].Nodup := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  decide

/-- ⚑ **`zeta_to_srs_length_and_zeta_to_domain_size_differ`** -- and that they differ is a FACT
ABOUT THIS PROOF, not a generality. They are `ζ^(2^16)` and `ζ^(2^domain_log2)`; the devnet block
`MinaWrapPublicCommGate.PUBLIC_INPUT` carries them EQUAL, because that step proof sits at
`domain_log2 = 16` and the SRS is 2^16. This one sits at `domain_log2 = 12`, so they must not be
equal, and if they ever became equal here the measurement would have silently come from the wrong
proof. -/
theorem zeta_to_srs_length_and_zeta_to_domain_size_differ :
    DEF_ZETA_TO_SRS_LENGTH ≠ DEF_ZETA_TO_DOMAIN_SIZE := by decide

/-- **`branch_data_is_two_proofs_at_domain_log2_twelve`** -- slot 29 DECOMPOSED rather than quoted.
`(domain_log2 <<< 2) ||| proofs_verified` with `N2 = 0b11` (`prepared_statement.rs:131-139`), so 51
says two recursion slots at a 2^12 step domain -- which is what the marshaller builds. A `51` that
matched nothing would be a number in a dump. -/
theorem branch_data_is_two_proofs_at_domain_log2_twelve :
    WRAP_PUBLIC_INPUT_MEASURED.getD 29 0 = 12 * 4 + 3
    ∧ WRAP_PUBLIC_INPUT_MEASURED.getD 29 0 = 51 := by
  refine ⟨?_, ?_⟩ <;> decide

/-- **`the_tail_is_ten_zeros`** -- the eight feature flags, `uses_lookup` and the lookup value. The
wrap emit path ties none of these to a variable, and this is what says a zero there is the value
Mina's own function produces rather than a placeholder we chose. -/
theorem the_tail_is_ten_zeros :
    ((List.range 10).map (fun j => WRAP_PUBLIC_INPUT_MEASURED.getD (30 + j) 0)).all
      (fun x => decide (x = 0)) = true := by
  decide

/-- ⚑ **`the_six_fit_the_cells_that_will_carry_them`** -- the consumers' own width pins, checked on
the MEASURED values before they are wired in.

`ftcSVal`'s three feed `scale_fast`, whose bit decomposition is `FTC_BITS = 255` wide and whose
second admissible string is `v + qN` (`ftc_scale_fast_admits_two_decompositions`); that string must
still fit 255 bits or the pin's own statement stops being about this circuit. `combXiVal` feeds a
`ENDO_BITS = 128` endo ladder whose counter reconstructs exactly 128 bits, so a wider ξ makes
`Field.Assert.equal !n_acc scalar` unsatisfiable. -/
theorem the_six_fit_the_cells_that_will_carry_them :
    DEF_PERM + qN < 2 ^ 255
    ∧ DEF_ZETA_TO_SRS_LENGTH + qN < 2 ^ 255
    ∧ DEF_ZETA_TO_DOMAIN_SIZE + qN < 2 ^ 255
    ∧ DEF_XI < 2 ^ 128
    ∧ DEF_CIP < qN ∧ DEF_B < qN := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

#assert_namespace_axioms Dregg2.Circuit.Emit.MinaWrapDeferredWords

end Dregg2.Circuit.Emit.MinaWrapDeferredWords
