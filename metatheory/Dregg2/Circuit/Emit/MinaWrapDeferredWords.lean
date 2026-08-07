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
-- ⚑ slot 11's preimage IS the step statement's own packed words since 2026-08-06 — see §1b.
import Dregg2.Circuit.Emit.KimchiStepWrapChainFixture

namespace Dregg2.Circuit.Emit.MinaWrapDeferredWords

open Dregg2.Circuit.Emit.PastaField (qN)

set_option autoImplicit false

/-! ## §1 -- the measurement -/

/-- `PreparedStatement::to_public_input(40)` on the step proof `pickles_kimchi_marshal` produces,
in Mina's own slot order. Every entry is an `Fq` element (the wrap circuit's native field). -/
def WRAP_PUBLIC_INPUT_MEASURED : List Nat :=
  [
   12010004765547201391409773201776305824185784783142434645351208320839742421461, --  0  combined_inner_product
   21987440263382699106234655418705855994583597503208492352139017174211654280979, --  1  b
   22051207486587639100263459519095348568734180902877797050992882206841041429320, --  2  zeta_to_srs_length
   14368984712825284049469800690161569863435482780405288332326486915433631288783, --  3  zeta_to_domain_size
   28229100965319782673857324829617936688280380769070774810971917298114340743540, --  4  perm
   252061977007684458868830594869018987781, --  5  beta
   333629593314957037425799072664795190945, --  6  gamma
   267119716335365228061221312319142614248, --  7  alpha
   233160729297248762727356644471301995827, --  8  zeta
   52104976899629910080081611182797329399, --  9  xi
   14158778653870066323259593856319550182737353536659615185740413704409907277844, -- 10  sponge_digest_before_evaluations
   410502603941333976604122738542936331683417571668670974113177062977848852425, -- 11  messages_for_next_wrap_proof(hash)
   18791908833463912602354670461025321774885842588314200243344231754906943671830, -- 12  messages_for_next_step_proof(hash)
   295607823032412332951449448243682232864, -- 13  bulletproof_challenges[0]
   148524814111790243896767045259254594024, -- 14  bulletproof_challenges[1]
   309216611095717609290388670299723671767, -- 15  bulletproof_challenges[2]
   206132936125452045865591174969915449245, -- 16  bulletproof_challenges[3]
   257788283300068897365212540061323569851, -- 17  bulletproof_challenges[4]
   103501831101324576155928935693582391466, -- 18  bulletproof_challenges[5]
   189990642246632253129902537876597800077, -- 19  bulletproof_challenges[6]
   295234837996079882137279194043543132969, -- 20  bulletproof_challenges[7]
   18834911767234354924973933256531420301, -- 21  bulletproof_challenges[8]
   84062693367477061942501662008107401900, -- 22  bulletproof_challenges[9]
   244259855895162990960653420688968068764, -- 23  bulletproof_challenges[10]
   307789436103332222467124911021158425522, -- 24  bulletproof_challenges[11]
   86217098500326653122989520443917640714, -- 25  bulletproof_challenges[12]
   6960595105215369732213989987576085939, -- 26  bulletproof_challenges[13]
   236634424326075149610160513484320610465, -- 27  bulletproof_challenges[14]
   147872090630400403780785042262034838918, -- 28  bulletproof_challenges[15]
   59, -- 29  branch_data((domain_log2<<2)|proofs_verified)
   0, -- 30  feature_flags.range_check0
   0, -- 31  feature_flags.range_check1
   0, -- 32  feature_flags.foreign_field_add
   0, -- 33  feature_flags.foreign_field_mul
   0, -- 34  feature_flags.xor
   0, -- 35  feature_flags.rot
   0, -- 36  feature_flags.lookup
   0, -- 37  feature_flags.runtime_tables
   0, -- 38  uses_lookup
   0, -- 39  joint_combiner_or_zero
  ]

/-! ## §1b -- ⚑⚑⚑ SLOT 11's PREIMAGE IS THE STEP STATEMENT'S OWN WORDS, AND UNTIL 2026-08-06
IT WAS A SECOND VECTOR NOBODY HAD NOTICED WAS A SECOND VECTOR

Slot 11 is `MessagesForNextWrapProof::hash()` (`gates.rs:272-284`), computed over exactly two things:
the record's `challenge_polynomial_commitment` and its `old_bulletproof_challenges` --
`Vector (Vector Fq 15) 2`, flattened.

⚠ ⚑⚑ **WHERE THOSE THIRTY CAME FROM WAS THE DEFECT.** `pickles_kimchi_marshal` CHOSE them, as
limbs `k·0x9E3779B97F4A7C15 | 1` / `(k+7)·0xBF58476D1CE4E5B9 | 1`, and handed the same ladder to the
wrap proof's `create_recursive`. Upstream there is no choice to make: `wrap_main.ml:421-431` takes
`old_bulletproof_challenges` from
`prev_statement.proof_state.unfinalized_proofs.(p).deferred_values.bulletproof_challenges` -- the
**step statement's own fifteen per block**, packed words `27·p + 11 … 25`. So this pipeline had TWO
vectors where Pickles has ONE, and **every instrument agreed with itself**: `expand_prechallenge`
matched the proof it was checked against, the accumulator matched the challenge polynomial of the
numbers it was built from, and `MessagesForNextWrapProof::hash()` hashed whatever it was given.
Nothing could go red. What it cost is that Lean's `whCloseDigest` -- which hashes the step
statement's words, as upstream does -- disagreed with slot 11 in **all thirty inputs**, and the
disagreement read as a Lean-side gap.

⚑ **THE LIST IS DERIVED NOW AND NOT TRANSCRIBED**, which is why the thirty literals that used to
sit here are deleted rather than re-baked: `wrap_verifier.ml:542-548` expands packed word `27·p + k`
into published entry `32·p + (k+5)` for `k ≥ 5`, so word `27·p + 11 + j` is entry `32·p + 16 + j` of
`STEP_PUBLIC_IN` -- and `step_statement_prechallenges` in the marshaller reads the same entries.
A transcription can be wrong; a recomposition of the emitted artifact cannot be wrong about anything
except the index arithmetic, which the width leg below grades.

⚠ These are the RAW 128-bit prechallenges, not the lifts. The lift is
`Scalar_challenge.to_field_checked` at `ENDO_Q`, i.e. `KimchiWrapMain.liftValQ`, and keeping the raw
form here is what lets that lift be the thing under test. -/

/-- Packed statement word `27·p + 11 + j`'s published entry (`wrap_verifier.ml:542-548`). -/
def prechalEntry (p j : Nat) : Nat := 32 * p + 16 + j

/-- The thirty, instance-major, as `composition_types.ml:411-418` flattens them. -/
def WRAP_MSG_NEXT_WRAP_PRECHALS : List Nat :=
  (List.range 30).map (fun k =>
    Dregg2.Circuit.Emit.KimchiStepWrapChainFixture.STEP_PUBLIC_IN.getD
      (prechalEntry (k / 15) (k % 15)) 0)

/-- ⚑ **THIRTY OF THEM, TWO VECTORS OF FIFTEEN, EACH WITHIN `Challenge.length` AND ALL DISTINCT.**
The width is the object check `the_width_signature_is_minas_own_layout` runs on the forty, applied to
slot 11's preimage: a 255-bit lift where a 128-bit prechallenge belongs is the classic defect and
nothing but the width sees it. `Nodup` is the anti-vacuity -- thirty aliases of one number would
satisfy `KimchiWrapMain.wraphack_closing_sponge_reproduces_minas_slot_eleven` just as well and mean
nothing.

⚠ ⚑⚑ **AND THE OLD `2^125 < x` LEG IS GONE, BECAUSE HALF THE VECTOR IS THE PADDING BLOCK'S.**
`Vector.extend_front` puts the dummy `per_proof` block at the FRONT, so the first fifteen are block
0's -- `KimchiStepMainCore.vStmtDummy` filler, small structured numerals -- and only the last fifteen
are `bullet_reduce` prechallenges. The old leg held because the marshaller's invented ladder made all
thirty look alike; keeping it would have hidden exactly the fact that makes this vector honest. The
split is stated instead, as the count, so a filler that leaked into block 1 (or a real challenge
mis-indexed into block 0) reds here.

⚠ **THAT SPLIT IS A FIDELITY GAP AND IT IS NOT CLOSED.** Upstream a padding block carries
`Unfinalized.Constant.dummy ()`, whose challenges are `Ipa.Wrap.compute_challenge` of
`Ro.scalar_chal ()` -- full-width 128-bit draws, not `19 + 4000037·i`-shaped filler. What this pass
fixed is that both sides now hash the SAME thirty, not that all thirty are upstream-shaped. -/
theorem the_slot_eleven_preimage_is_thirty_distinct_prechallenges :
    WRAP_MSG_NEXT_WRAP_PRECHALS.length = 30
    ∧ WRAP_MSG_NEXT_WRAP_PRECHALS.all (fun x => decide (x < 2 ^ 128)) = true
    -- ⚑ …and the two halves are SEPARATED rather than each pinned to a threshold someone can
    -- slide: EVERY word of the real block exceeds EVERY word of the padding block. That is the
    -- shape claim -- filler at the front, `bullet_reduce` prechallenges at the back -- and it reds
    -- if a filler leaks into block 1 or a challenge is mis-indexed into block 0, without naming a
    -- bound that a re-bake can nudge. (The old leg was `2^125 < x` on all thirty; it held only
    -- because the marshaller's invented ladder made both halves look alike.)
    ∧ ((List.range 15).all (fun j =>
        (List.range 15).all (fun i =>
          decide (WRAP_MSG_NEXT_WRAP_PRECHALS.getD i 0
                    < WRAP_MSG_NEXT_WRAP_PRECHALS.getD (15 + j) 0)))) = true
    ∧ WRAP_MSG_NEXT_WRAP_PRECHALS.Nodup := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

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

This is what separates "the right number at the right index" from "the right name over the wrong
object": exposing the 255-bit endo lift where `spec.ml` packs the raw prechallenge moves no index and
no count, and this inequality is the only instrument in the file that sees it. The two sets are
disjoint and together with slots 29-39 they exhaust the forty.

⚑ **THE DISCRIMINATING BOUND IS `2^128`, AND IT IS NOW STATED AS SUCH.** A packed
`Challenge`/`Scalar Challenge`/`Bulletproof_challenge` is `Challenge.length = 128` bits, so `2^128 ≤
x` is exactly "x cannot be one" -- leg 2 is the check the docblock above has always described.

⚠ ⚑⚑ **THE TWO MARGIN LEGS ARE DELETED (2026-08-06, second re-bake), AND THE DELETION IS THE
POINT.** They read `FIELD_SLOTS.all (2^249 < ·)` and "exactly one field slot sits below `2^250`", and
the paragraph that stood here defended having nudged the threshold from `2^250` to `2^249` because a
re-bake had put slot 0 one bit under it. That was the tell and it was written down and shipped
anyway: **a `Field` slot is an arbitrary `Fq` element and nothing bounds it from below.** The next
re-bake -- this one, off a step proof whose words 55/56 became the wrap's own squeezes -- put the
field slots at 247, 248, 251, 252 and 254 bits, and a third nudge to `2^246` would have been the same
coincidence a third time.

⚑ **WHAT SURVIVES IS THE CHECK THE DOCBLOCK ALWAYS DESCRIBED, AND IT IS STRUCTURAL ON ONE SIDE.**
`spec.ml:374-392` packs a `Challenge` / `Scalar Challenge` / `Bulletproof_challenge` at
`Challenge.length = 128`, so leg 1 is a property of the LAYOUT: a slot holding a 255-bit endo lift
where the raw prechallenge belongs cannot satisfy it. Leg 2 is its converse and is a SAMPLE fact --
an honest `Fq` element falls under `2^128` with probability `2^-126` -- kept because it is the
instrument that sees a raw prechallenge parked in a `Field` slot, and said to be a sample fact rather
than dressed as a bound. Legs 3 and 4 are new and are the reason the pair GRADES the twenty-nine:
the two sets are disjoint and they exhaust slots 0-28, so neither leg can be satisfied by looking at
a convenient subset. -/
theorem the_width_signature_is_minas_own_layout :
    CHALLENGE_SLOTS.all (fun i =>
      decide (WRAP_PUBLIC_INPUT_MEASURED.getD i 0 < 2 ^ 128)) = true
    ∧ FIELD_SLOTS.all (fun i =>
      decide (2 ^ 128 ≤ WRAP_PUBLIC_INPUT_MEASURED.getD i 0)) = true
    -- ⚑ …and the two sets are DISJOINT and EXHAUST the twenty-nine slots `wrap_main` reads, so the
    -- two legs above grade every one of them rather than a subset that happens to pass.
    ∧ CHALLENGE_SLOTS.filter (fun i => FIELD_SLOTS.contains i) = []
    ∧ (List.range 29).all (fun i =>
        CHALLENGE_SLOTS.contains i || FIELD_SLOTS.contains i) = true
    ∧ CHALLENGE_SLOTS.length = 21 ∧ FIELD_SLOTS.length = 8 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

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

/-- **`branch_data_is_two_proofs_at_domain_log2_fourteen`** -- slot 29 DECOMPOSED rather than quoted.
`(domain_log2 <<< 2) ||| proofs_verified` with `N2 = 0b11` (`prepared_statement.rs:131-139`), so 59
says two recursion slots at a 2^14 step domain -- which is what the marshaller builds. A `59` that
matched nothing would be a number in a dump.

⚠ ⚑ **IT WAS 51 AT `2^12` UNTIL 2026-08-06, AND THE MOVE IS THE STEP CIRCUIT'S.** The forty are
`PreparedStatement::to_public_input(40)` on whatever step proof the marshaller made; that proof is
`stepmain_step_r8_finalize` now — 10 347 rows at 67 public words, so its evaluation domain is `2^14`
where `stepmain_smoke_r8_finalize` sat at `2^12`. `KimchiWrapMain.mkWrapWith` reads
`KimchiStepWrapChainFixture.STEP_DOMAIN_LOG2` for the same reason, so this number and the one the
assembly DERIVES follow one source and cannot drift apart silently. -/
theorem branch_data_is_two_proofs_at_domain_log2_fourteen :
    WRAP_PUBLIC_INPUT_MEASURED.getD 29 0 = 14 * 4 + 3
    ∧ WRAP_PUBLIC_INPUT_MEASURED.getD 29 0 = 59 := by
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
