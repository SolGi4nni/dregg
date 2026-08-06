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
   1117645832111364878683857204788714449840860772346495449428610585539693137167, --  0  combined_inner_product
   21777777234232217860821360887121611618288927319335688664328246535554721523720, --  1  b
   8149239663751596801662678693302821294394998295243361602830765183121890662110, --  2  zeta_to_srs_length
   13754637000960282899699529053766972504264385824296256138307852822773767922204, --  3  zeta_to_domain_size
   8593722480541502673495264527951508995759096174473186282076668487031666439767, --  4  perm
   193434172244141145548481111131525554009, --  5  beta
   14611295132465104478110401651760541530, --  6  gamma
   128824226505427250820816902487251758556, --  7  alpha
   49764862543162710842432820270994491928, --  8  zeta
   238028948094493284007588209949128471000, --  9  xi
   13363709624839189624729053474885468137854461440653564568955298336522016580644, -- 10  sponge_digest_before_evaluations
   14487526077498829597225611381866255782252406825040604733580765573935450872395, -- 11  messages_for_next_wrap_proof(hash)
   2140974966619622776015189267648243586732098598200249976162061600531359395435, -- 12  messages_for_next_step_proof(hash)
   193413021763088679378346223800452572014, -- 13  bulletproof_challenges[0]
   211497503736393113809876588853595421377, -- 14  bulletproof_challenges[1]
   65562840999573818458670249776743061639, -- 15  bulletproof_challenges[2]
   95996046518973242036019614846661742708, -- 16  bulletproof_challenges[3]
   73907839716720835025479147802246695639, -- 17  bulletproof_challenges[4]
   77623633289130501347820137490767714972, -- 18  bulletproof_challenges[5]
   280492384813645995475067781368985441736, -- 19  bulletproof_challenges[6]
   55371934463937073510985154106716719151, -- 20  bulletproof_challenges[7]
   300077920515855457750918930666510292264, -- 21  bulletproof_challenges[8]
   274182238000232084153684845036035137968, -- 22  bulletproof_challenges[9]
   331563109375578417372038715052717228647, -- 23  bulletproof_challenges[10]
   10319218948555694921762899643910912343, -- 24  bulletproof_challenges[11]
   117679627433170027353577543684584321946, -- 25  bulletproof_challenges[12]
   155875792560497771807557655150773723741, -- 26  bulletproof_challenges[13]
   167894599541559745617214839948604366193, -- 27  bulletproof_challenges[14]
   271258881347124905993567886492750457261, -- 28  bulletproof_challenges[15]
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

This is what separates "the right number at the right index" from "the right name over the wrong
object": exposing the 255-bit endo lift where `spec.ml` packs the raw prechallenge moves no index and
no count, and this inequality is the only instrument in the file that sees it. The two sets are
disjoint and together with slots 29-39 they exhaust the forty.

⚑ **THE DISCRIMINATING BOUND IS `2^128`, AND IT IS NOW STATED AS SUCH.** A packed
`Challenge`/`Scalar Challenge`/`Bulletproof_challenge` is `Challenge.length = 128` bits, so `2^128 ≤
x` is exactly "x cannot be one" -- leg 2 is the check the docblock above has always described.

⚠ ⚑ **THE MARGIN LEG MOVED FROM `2^250` TO `2^249` ON 2026-08-06, AND LEG 4 IS WHY THAT IS NOT A
WIDENED PIN.** The re-baked forty came off `stepmain_step_r8_finalize`, and its slot 0
(`combined_inner_product`, `Shifted_value.Type1`) is a **250-bit** field element -- one bit under the
old threshold. `2^250` was a comfortable margin, not a property of the object, and a margin that
happens to hold on one sample is a coincidence dressed as a check. So the margin is kept, one bit
lower, and leg 4 NAMES how many slots sit in the bit that was given up: exactly one. A second slot
falling below reds here rather than being absorbed by a further nudge. -/
theorem the_width_signature_is_minas_own_layout :
    CHALLENGE_SLOTS.all (fun i =>
      decide (WRAP_PUBLIC_INPUT_MEASURED.getD i 0 < 2 ^ 128)) = true
    ∧ FIELD_SLOTS.all (fun i =>
      decide (2 ^ 128 ≤ WRAP_PUBLIC_INPUT_MEASURED.getD i 0)) = true
    ∧ FIELD_SLOTS.all (fun i =>
      decide (2 ^ 249 < WRAP_PUBLIC_INPUT_MEASURED.getD i 0)) = true
    ∧ (FIELD_SLOTS.filter (fun i =>
        decide (WRAP_PUBLIC_INPUT_MEASURED.getD i 0 < 2 ^ 250))).length = 1
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
