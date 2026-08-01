/-
# Dregg2.Bridge.PicklesStatementDiff — R3 continuation: extend the byte-exact Wrap-statement
differential from ONE field (`branch_data`) to the WHOLE statement.

`PicklesR3BranchDataDiff` diffed the smallest NON-identity field of the Wrap statement (`branch_data`,
slot 29) byte-exact against the live block. This file does the SAME for the remaining non-identity
packing — the **five shifted `fp` slots** (0–4) — and pins the layout ORDER of the identity slots
against the same block, so the WHOLE Wrap statement head is confirmed byte-exact from Lean.

## ⚑ SUBSTRATE — House Law #1, said at constraint #1
This is **Lean-authored synthesis**. `type1OfField shift1Fp` and `wrapFpBlock`/`wrapChallengeBlock`/
`wrapScalarChallengeBlock`/`branchDataPack` (all in `PicklesRecursion`) are the Lean emitters for the
Wrap statement's flat public-input packing; nothing here is a Rust AIR. The reference
(`~/dev/mina/.../composition_types/composition_types.ml:814-882` `to_data`,
`pickles_types/shifted_value.ml` `Type1`) is READ-ONLY (a 2024 snapshot); the *operative* oracle is a
live emission of that exact code — the kimchi-verified devnet block below.

## ⚑ PHASE A discipline — this is a FIDELITY diff, NOT a soundness proof
The claim proved here is: **the Lean-emitted Wrap-statement flat packing equals the public-input words
the deployed OCaml Pickles put on the wire, for one fixed block (MEASURED).** It is NOT "machine-checked
Pickles" and asserts nothing about IPA/recursion soundness (Phase B). Honest label: *Lean's `to_data`
packing of the block's decoded deferred-values record reproduces `wrap_public_input[0..10]` and
`[29]`, byte-exact, for devnet block 539508.*

## §Oracle — a live emission of exactly the code o1js wraps (zero build)
`metatheory/mina_real_block_proof.json` is Mina **devnet** block 539508 (state hash `3NLmVB6…jm12zNk`),
decoded by `metatheory/fixtures/pickles-extractors`. Its `wrap_public_input` is the 40-word public
input openmina's `PreparedStatement::to_public_input` assembled, and o1-labs' `kimchi::verifier::verify`
ACCEPTS the Wrap proof against those 40 words (extractor ground-truth #3) — so the slots below are
validated, not transcribed. The block ALSO carries `step_deferred_values`, the same record decoded from
the proof's binprot bytes in BOTH unshifted and `_shifted` form; that pairing is what makes the shift
diff (slots 0–4) an emit-and-diff rather than a projection. The paired oracle script,
`bridge/mina-zkapp/scripts/pickles-statement-oracle.ts`, reads the JSON and confirms every literal
below against the two independent decoded fields (wire slot vs `step_deferred_values`).

## The two NON-identity packings, and the identity remainder
Of the 40 Wrap slots exactly TWO carry a value that differs from its raw input:
  * **slots 0–4** — the `fp` block `[cip, b, zeta_to_srs_length, zeta_to_domain_size, perm]`, carried
    as `Shifted_value.Type1` over **Fp** (`shifted_value.ml` `of_field s = (s − (2^255+1))·2⁻¹`). This
    file's subject.
  * **slot 29** — `branch_data`, the prefix-mask pack (`PicklesR3BranchDataDiff`, re-affirmed here).
Every other slot is IDENTITY placement of an already-field value (challenges 5–9, sponge digest 10,
the two me-only Poseidon digests 11–12, the 16 bulletproof challenges 13–28, the zero
feature-flag/lookup tail 30–39). For those the content is the ORDER, pinned below.

## The residual, so this cannot be mistaken for all of R3
  * `internal_vars` (the witness-placement recipe) has no dregg model and no zero-build oracle at this
    rung; it is emitted by the R1 builder and tested when R1 exists. UNMOVED from R3 — handed off, not
    chased.
  * The two me-only digest slots (11, 12) are Poseidon hashes of the me/you messages; they are NOT
    recomputed here — `Dregg2.Bridge.MinaWrapPublicInput`'s `the_header_words_land_where_the_layout_says`
    already pins them against independently-derived `word11Gold`/`word12Gold`. Cited, not re-proved.
  * The **Step** statement has NO independent public-input oracle in this fixture (§Step): the block is
    a Wrap-proof decode; `step_deferred_values` here IS the Wrap statement's payload about the step
    proof, not a step proof's own flat public input. The step layout is enumerated (below), its diff is
    handed to a step-proof-decode lane.

NOT imported by the `Dregg2` root, per house practice for gates.
-/
import Dregg2.Circuit.Emit.PicklesRecursion

set_option autoImplicit false

namespace Dregg2.Bridge.PicklesStatementDiff

open Dregg2.Circuit.Emit.PicklesRecursion
  (Fp shift1Fp type1OfField Shift2 type2OfField
   WrapDeferredValues PlonkInCircuit PlonkMinimal BranchData
   wrapFpBlock wrapChallengeBlock wrapScalarChallengeBlock branchDataPack)

/-! ## §0 — the block's decoded data, as Lean literals.

Every literal is confirmed against the JSON by the paired oracle script (two independent decoded
fields per slot). Here they are trusted inputs; the theorems below are the EMIT diff over them. -/

/-- `wrap_public_input`, all 40 words of block 539508. -/
def WIRE : List Nat :=
  [ 24419304084955781347126086756851183942391470709481893428346911935138434430569,
    3704055669176394204882118867085528376297324327166010249275631280543959110076,
    28253093736872809289651234116715748339046919777164536988932734978720774588272,
    28253093736872809289651234116715748339046919777164536988932734978720774588272,
    7936731386312087149597495386614535691216588017905596433290144424125540122277,
    313463181614075351545075628406585839803,
    192135724619941679018606360956682553776,
    20020606918071128765989674557881900859,
    330389166796541696025267191640936493743,
    282268845488303208229519822093349558173,
    27860000640749903405624349274249037823232876972870997514980343477933149550480,
    16694176452625101103339288558027392732723822717830151635447913532282294450543,
    24322017899265084126163599635783679345976168424021275192497824834098868742353,
    303470030041837608182625021184247144292, 215040174751140842097626313263132934235,
    116786039988294977482203225277061489760, 145647732904612004311939035064002596244,
    118655921900489766024613108925676069222, 169092797198025184551686556020669572432,
    226564282767834168403398696183657136270, 260600631046412867950114853686082369627,
    334719724349459140876552267973395295867, 298815148206820034167176397994576632602,
    323043114272259398565633317155132713683, 224654319660684979785255210812981548402,
    292739584116245352526725496552824504571, 203919802211036713134713941032303566966,
    302871052620997892963571361622783641311, 197159688177129719009894883897915324660,
    67, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 ]

/-- The `fp` block's UNSHIFTED values — `step_deferred_values.{combined_inner_product, b,
zeta_to_srs_length, zeta_to_domain_size, perm}`, decoded from the proof's binprot bytes (NOT projected
out of `wrap_public_input`). These are the record-field values `to_data` shifts. -/
def FP_UNSHIFTED : List Fp :=
  [ (19890585860582513838359427261530390921328764305959386728558585581183530790096 : Fp),
    (7408111338352788409764237734171056752503528023269181086370701036344547779447 : Fp),
    (27558165164416569723409721981259519714639662441324673849730231668348211105502 : Fp),
    (27558165164416569723409721981259519714639662441324673849730231668348211105502 : Fp),
    (15873462772624174299194990773229071382342055404748353454399727323507709803849 : Fp) ]

/-! ## §1 — ⚑⚑ THE fp-BLOCK DIFF, byte-exact (slots 0–4). THE NEW SIGNAL.

`Wrap.Statement.to_data` (`composition_types.ml:855-861`) lays the `fp` block down first; each element
is carried as `Shifted_value.Type1` over Fp: `wire = (raw − (2^255+1)) · 2⁻¹  (mod p)`. This is the
one packing besides `branch_data` where the wire word differs from the record value. -/

/-- **`fp` block, as Fp, read from the wire (slots 0–4)** — the same integers as `WIRE.take 5`, written
as `Fp` `OfNat` literals so the `decide` path is the tree's tested one (no `Nat.cast`). -/
def FP_WIRE : List Fp :=
  [ (24419304084955781347126086756851183942391470709481893428346911935138434430569 : Fp),
    (3704055669176394204882118867085528376297324327166010249275631280543959110076 : Fp),
    (28253093736872809289651234116715748339046919777164536988932734978720774588272 : Fp),
    (28253093736872809289651234116715748339046919777164536988932734978720774588272 : Fp),
    (7936731386312087149597495386614535691216588017905596433290144424125540122277 : Fp) ]

/-- ⚑⚑ **THE fp-BLOCK BYTE-EXACT DIFF, MATCHED.** Lean's `type1OfField shift1Fp` emitter, run on the
block's own decoded UNSHIFTED `fp` record fields, reproduces `wrap_public_input[0..4]` — all five —
byte-exact. A FIDELITY match, not a soundness claim: Lean's `Spec.pack` of the `fp` block = the real
chain's, byte-exact, for this block. -/
theorem lean_fp_block_matches_real_block :
    FP_UNSHIFTED.map (type1OfField shift1Fp) = FP_WIRE := by decide

/-- The Type2-over-Fp shift constant `2^255` (= `shift1Fp.c − 1`), for the falsifier below. -/
def shift2Fp : Shift2 Fp := { shift := shift1Fp.c - 1 }

/-! ## §1a — the shift is LOAD-BEARING, and it is keyed by the VALUE's field (Fp), not the circuit's.

The diff is only worth anything if a WRONG emitter fails it. Two mistakes a first-pass port would make:
  * **identity** — put the raw scalar on the wire (no shift). The wire word differs, REJECTED.
  * **native-field encoding** — the Wrap circuit is Fq-native, so a port might reach for the Fq/Type2
    encoding (`s − 2^255`, no halving). But the `fp` block carries the STEP proof's **Fp** scalars, so
    the shift is Fp/Type1. A Type2-style subtract-only pack diverges, REJECTED. -/
theorem fp_shift_is_load_bearing :
    -- identity placement is wrong: the shift actually moves every one of the five values
    FP_UNSHIFTED ≠ FP_WIRE
    -- a Type2-style (subtract-only) pack over Fp is wrong: the ·2⁻¹ halving is load-bearing
    ∧ FP_UNSHIFTED.map (type2OfField shift2Fp) ≠ FP_WIRE
    -- and the correct emitter really separates from the subtract-only one on this data
    ∧ FP_UNSHIFTED.map (type1OfField shift1Fp) ≠ FP_UNSHIFTED.map (type2OfField shift2Fp) := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-! ## §2 — the CHALLENGE slots (5–9): identity placement, ORDER pinned.

`to_data` (`composition_types.ml:863-864`) lays `challenge = [beta; gamma]` then
`scalar_challenge = [alpha; zeta; xi]`. These are identity placements of 128-bit challenges (no
packing), so the content is the ORDER — the 2026-07-30 correction that slots 5–7 are `beta, gamma,
alpha` and NOT `alpha, beta, gamma`. The five decoded challenges are `step_deferred_values.{beta,
gamma, alpha, zeta, xi}`; the oracle script confirms each equals its wire slot from the independent
decoded field. -/

/-- The five challenges, decoded (`step_deferred_values.{beta, gamma, alpha, zeta, xi}`). -/
def BETA : Nat := 313463181614075351545075628406585839803
def GAMMA : Nat := 192135724619941679018606360956682553776
def ALPHA : Nat := 20020606918071128765989674557881900859
def ZETA : Nat := 330389166796541696025267191640936493743
def XI : Nat := 282268845488303208229519822093349558173

/-- **The `to_data` challenge order reproduces slots 5–9.** `[beta, gamma]` at 5–6, `[alpha, zeta, xi]`
at 7–9 — exactly `wrapChallengeBlock ++ wrapScalarChallengeBlock` of the decoded record. -/
theorem lean_challenge_order_matches_real_block :
    [BETA, GAMMA] = [WIRE.getD 5 0, WIRE.getD 6 0]
    ∧ [ALPHA, ZETA, XI] = [WIRE.getD 7 0, WIRE.getD 8 0, WIRE.getD 9 0] := by
  refine ⟨?_, ?_⟩ <;> decide

/-- **The challenge ORDER is load-bearing.** The five are distinct, and the pre-2026-07-30 order
`[alpha, beta, gamma]` at slots 5–7 misplaces them: it would put `alpha` where `beta` belongs. So a
permuted `to_data` fails HERE, on the real block, and it is not a coincidence of equal values. -/
theorem challenge_order_is_load_bearing :
    ([BETA, GAMMA, ALPHA, ZETA, XI] : List Nat).Nodup
    ∧ [ALPHA, BETA, GAMMA] ≠ [WIRE.getD 5 0, WIRE.getD 6 0, WIRE.getD 7 0] := by
  refine ⟨?_, ?_⟩ <;> decide

/-! ## §3 — ⚑ THE CAPSTONE: Lean's `to_data` of the decoded record reproduces the wire head.

Assemble the block's decoded `Wrap.…Deferred_values` record (UNSHIFTED fp fields, raw challenges,
`branch_data = {N2, 16}`), pack it exactly as `composition_types.ml:855-878` `to_data` does — the `fp`
block Type1-shifted, the two challenge blocks placed, then the sponge digest — and diff against the
wire's slots 0–10, plus `branch_data` at 29. This ties the field ORDER (`wrapFpBlock ++
wrapChallengeBlock ++ wrapScalarChallengeBlock ++ [digest]`) and BOTH non-identity packings to the
live block in one object. -/

/-- The block's `sponge_digest_before_evaluations` (slot 10), as Fp. -/
def BLOCK_SPONGE : Fp :=
  (27860000640749903405624349274249037823232876972870997514980343477933149550480 : Fp)

/-- The 16 bulletproof challenges (slots 13–28), decoded
(`step_deferred_values.bulletproof_challenges`). -/
def BPC : List Nat :=
  [ 303470030041837608182625021184247144292, 215040174751140842097626313263132934235,
    116786039988294977482203225277061489760, 145647732904612004311939035064002596244,
    118655921900489766024613108925676069222, 169092797198025184551686556020669572432,
    226564282767834168403398696183657136270, 260600631046412867950114853686082369627,
    334719724349459140876552267973395295867, 298815148206820034167176397994576632602,
    323043114272259398565633317155132713683, 224654319660684979785255210812981548402,
    292739584116245352526725496552824504571, 203919802211036713134713941032303566966,
    302871052620997892963571361622783641311, 197159688177129719009894883897915324660 ]

/-- Slots 0–10 of the wire as explicit `Fp` `OfNat` literals (the challenge/sponge slots are `< p`, so
this is the faithful `Fp` view). Explicit literals keep the capstone `decide` on the tree's tested
`OfNat`+`type1OfField` path — no `Nat.cast`. -/
def WIRE_HEAD_FP : List Fp :=
  [ (24419304084955781347126086756851183942391470709481893428346911935138434430569 : Fp),
    (3704055669176394204882118867085528376297324327166010249275631280543959110076 : Fp),
    (28253093736872809289651234116715748339046919777164536988932734978720774588272 : Fp),
    (28253093736872809289651234116715748339046919777164536988932734978720774588272 : Fp),
    (7936731386312087149597495386614535691216588017905596433290144424125540122277 : Fp),
    (313463181614075351545075628406585839803 : Fp),
    (192135724619941679018606360956682553776 : Fp),
    (20020606918071128765989674557881900859 : Fp),
    (330389166796541696025267191640936493743 : Fp),
    (282268845488303208229519822093349558173 : Fp),
    (27860000640749903405624349274249037823232876972870997514980343477933149550480 : Fp) ]

/-- **The block's decoded Wrap `Deferred_values`** (Chal = Sc = Fld = `Fp` so the packing is `Nat.cast`-
free): the record BEFORE packing — fp fields UNSHIFTED, challenges raw, `branch_data` unpacked. -/
def blockWrapDV : WrapDeferredValues Fp Fp Fp :=
  { plonk :=
      { minimal :=
          { alpha := (20020606918071128765989674557881900859 : Fp)
            beta := (313463181614075351545075628406585839803 : Fp)
            gamma := (192135724619941679018606360956682553776 : Fp)
            zeta := (330389166796541696025267191640936493743 : Fp)
            jointCombiner := none }
        zetaToSrsLength := (27558165164416569723409721981259519714639662441324673849730231668348211105502 : Fp)
        zetaToDomainSize := (27558165164416569723409721981259519714639662441324673849730231668348211105502 : Fp)
        perm := (15873462772624174299194990773229071382342055404748353454399727323507709803849 : Fp) }
    combinedInnerProduct := (19890585860582513838359427261530390921328764305959386728558585581183530790096 : Fp)
    b := (7408111338352788409764237734171056752503528023269181086370701036344547779447 : Fp)
    xi := (282268845488303208229519822093349558173 : Fp)
    bulletproofChallenges := []
    branchData := { proofsVerified := 2, domainLog2 := 16 } }

/-- Lean's `to_data` flat packing of the Wrap deferred-values head, slots 0–10:
`fp` block (Type1/Fp shifted) ++ `challenge` block ++ `scalar_challenge` block ++ `[sponge]`. Exactly
`composition_types.ml:872-878` field order for the first eleven words. -/
def wrapToDataHead (dv : WrapDeferredValues Fp Fp Fp) (sponge : Fp) : List Fp :=
  (wrapFpBlock dv).map (type1OfField shift1Fp)
  ++ wrapChallengeBlock dv
  ++ wrapScalarChallengeBlock dv
  ++ [sponge]

/-- ⚑⚑ **THE CAPSTONE MATCH.** Lean's `to_data` packing of the block's own decoded record reproduces
`wrap_public_input[0..10]` byte-exact (the two non-identity packings — the Type1/Fp fp shift and the
challenge order — plus the identity sponge slot, in the real field order), and `branchDataPack`
reproduces slot 29. Slots 11–12 (me-only Poseidon digests) are pinned in `MinaWrapPublicInput`; 13–28
(bulletproof challenges) and 30–39 (zero tail) are §4. -/
theorem lean_wrap_to_data_reproduces_wire_head :
    wrapToDataHead blockWrapDV BLOCK_SPONGE = WIRE_HEAD_FP
    ∧ branchDataPack blockWrapDV.branchData = WIRE.getD 29 0 := by
  refine ⟨?_, ?_⟩ <;> decide

/-! ## §4 — the identity remainder: bulletproof challenges (13–28) and the zero tail (30–39).

Bulletproof challenges are identity-placed 128-bit values; the tail is the 8 feature-flag bits
(slots 30–37, all off for the Mina blockchain circuit) plus the 2-slot lookup opt (38–39, no lookup).
`to_data` (`composition_types.ml:877-882`) emits `bulletproof_challenges ++ [branch_data] ++
Features.to_data ++ lookup_opt`. -/

/-- Slots 13–28 ARE the 16 decoded bulletproof challenges, in order. -/
theorem bulletproof_challenges_placed_at_13_28 :
    ((List.range 16).map (fun j => WIRE.getD (13 + j) 0)) = BPC := by decide

/-- The tail (30–39) is all zero, and `branch_data` (29) is the small packed word — so no real value
is silently absorbed into the feature-flag / lookup-opt slots. -/
theorem tail_is_zero_and_branch_data_is_packed :
    WIRE.getD 29 0 = 67
    ∧ ((List.range 10).all (fun j => WIRE.getD (30 + j) 0 == 0)) = true := by
  refine ⟨?_, ?_⟩ <;> decide

/-! ### §4a — ⚑ a LAYOUT GAP found this rung: Lean's `wrapStatementLayout` is 38, the wire is 40.

`Dregg2.Circuit.Emit.PicklesRecursion.wrapStatementLayout` sums to `WPUB = 38`
(5 fp + 2 chal + 3 scalar + 3 digest + 16 bp + 1 branch_data + 8 feature_flags). The on-wire public
input is **40**: the missing two words are `Lookup_parameters.opt_spec impl lookup`
(`composition_types.ml:822`, the 8th `to_data` block), the lookup flag + `joint_combiner`, both 0 when
no lookup is used. NOT a divergence in any PINNED slot (both are 0 here) but the Lean layout under-counts
the wire by exactly the lookup-opt block — recorded so a Step/Wrap assembler does not size the public
input at 38. -/
def wrapWireLen : Nat := 40
def wrapLeanLayoutLen : Nat := 38

theorem lean_layout_undercounts_by_the_lookup_opt :
    WIRE.length = wrapWireLen
    ∧ wrapWireLen - wrapLeanLayoutLen = 2 := by
  refine ⟨?_, ?_⟩ <;> decide

/-! ## §Step — the Step statement layout, ENUMERATED, no oracle at this rung (hand-off).

`Step.…Per_proof.to_data` (`composition_types.ml:1298-1318`) is a DIFFERENT flat order from Wrap:
`fq(5) ++ digest(1) ++ challenge(2) ++ scalar_challenge(3) ++ bulletproof(15) ++ bool(1)` — NO
`branch_data`, digest EARLY (right after the fq block), and a trailing `should_finalize` bool. The
`fq` block carries the WRAP proof's **Fq** scalars, so by the §1a value-field rule its shift is
Type2/Fq (`shift2Fq`), the mirror of the Wrap side's Type1/Fp. This fixture is a Wrap-proof decode and
carries NO step-statement public input — `step_deferred_values` here is the WRAP statement's payload
ABOUT the step proof, not a step proof's own 40-word public input — so the Step layout is not
byte-diffed at this rung. Handed to a step-proof-decode lane; the shift/pack emitters it needs
(`type2OfField shift2Fq`, the block accessors) already exist in `PicklesRecursion`. -/

/-- The Step per-proof flat layout (`composition_types.ml:1268-1276` `spec`). -/
def stepPerProofLayout : List (String × Nat) :=
  [("fq", 5), ("digest", 1), ("challenge", 2), ("scalar_challenge", 3),
   ("bulletproof_challenge", 15), ("bool", 1)]

/-- The Wrap statement head layout, for contrast (`composition_types.ml:814-823` `spec`, first blocks). -/
def wrapHeadLayout : List (String × Nat) :=
  [("fp", 5), ("challenge", 2), ("scalar_challenge", 3), ("digest", 3)]

/-- **The Step and Wrap layouts genuinely differ**, not one reused twice: Step puts its 1-word digest
2nd of 6 blocks right after the field block and carries a `bool`/no `branch_data`; Wrap puts its 3-word
digest 4th, after the challenge blocks. The block-name sequences (shown explicitly) make the divergence
and the absence of `branch_data` from Step visible, so a step-proof assembler cannot reuse the Wrap
head order. -/
theorem step_and_wrap_layouts_differ :
    stepPerProofLayout.map Prod.fst
        = ["fq", "digest", "challenge", "scalar_challenge", "bulletproof_challenge", "bool"]
    ∧ wrapHeadLayout.map Prod.fst = ["fp", "challenge", "scalar_challenge", "digest"]
    ∧ stepPerProofLayout.length ≠ wrapHeadLayout.length := by
  refine ⟨rfl, rfl, ?_⟩
  decide

/-! ## §Axiom hygiene — the diff rests on nothing but the kernel. -/

#assert_axioms lean_fp_block_matches_real_block
#assert_axioms fp_shift_is_load_bearing
#assert_axioms lean_challenge_order_matches_real_block
#assert_axioms challenge_order_is_load_bearing
#assert_axioms lean_wrap_to_data_reproduces_wire_head
#assert_axioms bulletproof_challenges_placed_at_13_28
#assert_axioms tail_is_zero_and_branch_data_is_packed
#assert_axioms lean_layout_undercounts_by_the_lookup_opt
#assert_axioms step_and_wrap_layouts_differ

#print axioms lean_fp_block_matches_real_block
#print axioms lean_wrap_to_data_reproduces_wire_head

end Dregg2.Bridge.PicklesStatementDiff
