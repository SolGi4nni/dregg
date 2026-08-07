/-
# Dregg2.Circuit.PiDeclarationBite — the ARMED canary: an undeclared / falsely-declared PI REFUSES.

`Emit.PiDeclaration` puts a side condition on the emit: a descriptor routed through
`withPiManifest` does not elaborate unless every published slot carries exactly one disposition
and every disposition is TRUE of the descriptor.

⚑ **THIS FILE IS THE PART THAT CAN GO RED.** A side condition every honest emitter discharges
silently is INVISIBLE, and "the emitters all still build" is exactly what a DELETED condition
also looks like. `ChipArityBite` exists because `eaf64969a` demonstrated a bite in an
UNCOMMITTED scratch file and three rails then sat unchecked for a day. So each of the five ways a
PI declaration can be false is asserted at build time, plus positive controls, so a condition that
refused EVERYTHING would not read as a pass.

The five refusals, each one a real failure mode measured in this tree:

| # | the false declaration | the wound it is |
|---|---|---|
| 1 | a slot in `0..piCount` with NO declaration | the 1,787 unbound slots — nobody chose |
| 2 | `.bound` naming a pin the descriptor does not carry | `PI[TURN_HASH]` today: a slot the producer fills and the AIR never reads |
| 3 | `.bound` naming a pin whose COLUMN nothing else reads | the `withDfaRcPins` quartet — `UnforcedPiPins.dropUnforcedPins` deletes it and the fold that located its slot BY the pin refused every deployed leg |
| 4 | `.transcriptOnly` with an empty reason | the choice made and not recorded |
| 5 | `.transcriptOnly` on a slot the descriptor DOES pin | a manifest describing a different object |

⚠ `#guard_msgs` compares message TEXT. If a Lean upgrade rewords "could not synthesize default
value", update the expected text — do NOT delete the canary, and do not weaken it to
`drop error`: dropping the errors is the same as deleting the file.
-/
import Dregg2.Circuit.Emit.PiDeclaration

namespace Dregg2.Circuit.PiDeclarationBite

open Dregg2.Circuit.DescriptorIR2
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (EffectVmDescriptor VmHashSite HashInput VmRow)
open Dregg2.Circuit.Emit.PiDeclaration

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The fixtures.

`forcedM` — two published slots. Column 5 is FORCED (a gate reads it) and pinned to slot 0;
slot 1 carries no pin at all. This is the honest shape: one bound slot, one transcript-only slot.

`unforcedM` — the same, except the pin on slot 0 lands on column 9, which NOTHING else reads.
That pin is exactly what `UnforcedPiPins.unforcedPins` censuses and `dropUnforcedPins` deletes. -/

/-- A descriptor whose pinned column 5 is genuinely read (by a gate). -/
def forcedM : EffectVmDescriptor2 :=
  { name := "pi-decl-bite-forced", traceWidth := 16, piCount := 2, tables := []
  , constraints :=
      [ .base (.gate (.add (.var 5) (.const (-3))))     -- FORCES column 5
      , .base (.piBinding .first 5 0) ]                 -- publishes it at slot 0
  , hashSites := [], ranges := [] }

/-- The same descriptor with the pin moved to a column nothing else reads. -/
def unforcedM : EffectVmDescriptor2 :=
  { name := "pi-decl-bite-unforced", traceWidth := 16, piCount := 2, tables := []
  , constraints :=
      [ .base (.gate (.add (.var 5) (.const (-3))))
      , .base (.piBinding .first 9 0) ]                 -- column 9 is read by NOTHING else
  , hashSites := [], ranges := [] }

/-- The honest manifest for `forcedM`. -/
def goodManifest : PiManifest :=
  [ ⟨0, "STATE_COMMIT", .bound .first 5⟩
  , ⟨1, "NONCE_ECHO", .transcriptOnly
      "verifier-supplied comparand; the AIR compares nothing to it and the executor \
       re-derives it from the turn header"⟩ ]

/-! ## Positive controls — the honest shapes elaborate, silently. -/

example : EffectVmDescriptor2 := withPiManifest forcedM goodManifest

/-- The census sees the same object: the gate is the identity on the emitted descriptor. -/
theorem gate_changes_no_byte :
    withPiManifest forcedM goodManifest (by pi_manifest_admitted) = forcedM := rfl

/-- The honest manifest really is admitted (so the refusals below are not vacuous). -/
theorem goodManifest_admitted : manifestAdmitted forcedM goodManifest = true := by decide

/-- …and its bound slot generates the producer's fill obligation — the fourth source, derived. -/
theorem goodManifest_obligations :
    producerObligations goodManifest = [(0, VmRow.first, 5)] := by decide

/-- …and the transcript-only class is REPORTED, with its reason, rather than silently permitted. -/
theorem goodManifest_transcript_only_is_one_slot :
    (transcriptOnlySlots goodManifest).map (fun e => e.1) = [1] := by decide

/-! ## The bite. -/

/--
error: could not synthesize default value for parameter 'h' using tactics
---
error: PI DISPOSITION MISSING OR FALSE — every published public input must carry EXACTLY ONE declaration, and the declaration must be TRUE of this descriptor. Either (a) a slot in 0..piCount has no declaration (or two), or (b) a `.bound row col` names a pin the descriptor does not carry, or names a column no NON-PIN constraint reads (an unforced pin — the prover chooses both sides, and `UnforcedPiPins` deletes it), or (c) a `.transcriptOnly` carries an empty reason, or was declared for a slot the descriptor DOES pin. An unbound public input is either a value a verifier must check — so bind it — or not a public input at all — so delete it. It is not a thing you may leave unsaid.
⊢ PiManifestAdmitted forcedM [{ index := 0, slot := "STATE_COMMIT", disp := PiDisposition.bound VmRow.first 5 }]
-/
#guard_msgs (error, drop info, drop warning) in
-- ① THE UNBOUND MAJORITY: slot 1 is published and undeclared. Silence is not an answer.
example : EffectVmDescriptor2 :=
  withPiManifest forcedM [⟨0, "STATE_COMMIT", .bound .first 5⟩]

/--
error: could not synthesize default value for parameter 'h' using tactics
---
error: PI DISPOSITION MISSING OR FALSE — every published public input must carry EXACTLY ONE declaration, and the declaration must be TRUE of this descriptor. Either (a) a slot in 0..piCount has no declaration (or two), or (b) a `.bound row col` names a pin the descriptor does not carry, or names a column no NON-PIN constraint reads (an unforced pin — the prover chooses both sides, and `UnforcedPiPins` deletes it), or (c) a `.transcriptOnly` carries an empty reason, or was declared for a slot the descriptor DOES pin. An unbound public input is either a value a verifier must check — so bind it — or not a public input at all — so delete it. It is not a thing you may leave unsaid.
⊢ PiManifestAdmitted forcedM
    [{ index := 0, slot := "STATE_COMMIT", disp := PiDisposition.bound VmRow.first 5 },
      { index := 1, slot := "TURN_HASH", disp := PiDisposition.bound VmRow.first 7 }]
-/
#guard_msgs (error, drop info, drop warning) in
-- ② `PI[TURN_HASH]` TODAY: declared bound, and there is no pin. The producer fills it, the AIR
-- never looks, and before this condition nothing in the tree could say so.
example : EffectVmDescriptor2 :=
  withPiManifest forcedM
    [ ⟨0, "STATE_COMMIT", .bound .first 5⟩
    , ⟨1, "TURN_HASH", .bound .first 7⟩ ]

/--
error: could not synthesize default value for parameter 'h' using tactics
---
error: PI DISPOSITION MISSING OR FALSE — every published public input must carry EXACTLY ONE declaration, and the declaration must be TRUE of this descriptor. Either (a) a slot in 0..piCount has no declaration (or two), or (b) a `.bound row col` names a pin the descriptor does not carry, or names a column no NON-PIN constraint reads (an unforced pin — the prover chooses both sides, and `UnforcedPiPins` deletes it), or (c) a `.transcriptOnly` carries an empty reason, or was declared for a slot the descriptor DOES pin. An unbound public input is either a value a verifier must check — so bind it — or not a public input at all — so delete it. It is not a thing you may leave unsaid.
⊢ PiManifestAdmitted unforcedM
    [{ index := 0, slot := "STATE_COMMIT", disp := PiDisposition.bound VmRow.first 9 },
      { index := 1, slot := "NONCE_ECHO",
        disp :=
          PiDisposition.transcriptOnly
            "verifier-supplied comparand; the AIR compares nothing to it and the executor re-derives it from the turn header" }]
-/
#guard_msgs (error, drop info, drop warning) in
-- ③ THE UNFORCED PIN. The pin EXISTS at (first, 9, 0) — a census that only asked "is there a
-- `pi_binding`?" would pass this. Column 9 is read by nothing else, so the prover picks both
-- sides, and `dropUnforcedPins` deletes the pin at the next compaction. `.bound` may not name it.
example : EffectVmDescriptor2 :=
  withPiManifest unforcedM
    [ ⟨0, "STATE_COMMIT", .bound .first 9⟩
    , ⟨1, "NONCE_ECHO", .transcriptOnly
        "verifier-supplied comparand; the AIR compares nothing to it and the executor \
         re-derives it from the turn header"⟩ ]

/--
error: could not synthesize default value for parameter 'h' using tactics
---
error: PI DISPOSITION MISSING OR FALSE — every published public input must carry EXACTLY ONE declaration, and the declaration must be TRUE of this descriptor. Either (a) a slot in 0..piCount has no declaration (or two), or (b) a `.bound row col` names a pin the descriptor does not carry, or names a column no NON-PIN constraint reads (an unforced pin — the prover chooses both sides, and `UnforcedPiPins` deletes it), or (c) a `.transcriptOnly` carries an empty reason, or was declared for a slot the descriptor DOES pin. An unbound public input is either a value a verifier must check — so bind it — or not a public input at all — so delete it. It is not a thing you may leave unsaid.
⊢ PiManifestAdmitted forcedM
    [{ index := 0, slot := "STATE_COMMIT", disp := PiDisposition.bound VmRow.first 5 },
      { index := 1, slot := "NONCE_ECHO", disp := PiDisposition.transcriptOnly "" }]
-/
#guard_msgs (error, drop info, drop warning) in
-- ④ THE UNRECORDED CHOICE. Transcript-only is permitted; transcript-only-because-nobody-said is
-- not. An empty reason is an unbound slot with a checkbox ticked.
example : EffectVmDescriptor2 :=
  withPiManifest forcedM
    [ ⟨0, "STATE_COMMIT", .bound .first 5⟩
    , ⟨1, "NONCE_ECHO", .transcriptOnly ""⟩ ]

/--
error: could not synthesize default value for parameter 'h' using tactics
---
error: PI DISPOSITION MISSING OR FALSE — every published public input must carry EXACTLY ONE declaration, and the declaration must be TRUE of this descriptor. Either (a) a slot in 0..piCount has no declaration (or two), or (b) a `.bound row col` names a pin the descriptor does not carry, or names a column no NON-PIN constraint reads (an unforced pin — the prover chooses both sides, and `UnforcedPiPins` deletes it), or (c) a `.transcriptOnly` carries an empty reason, or was declared for a slot the descriptor DOES pin. An unbound public input is either a value a verifier must check — so bind it — or not a public input at all — so delete it. It is not a thing you may leave unsaid.
⊢ PiManifestAdmitted forcedM
    [{ index := 0, slot := "STATE_COMMIT", disp := PiDisposition.transcriptOnly "it is only a transcript value" },
      { index := 1, slot := "NONCE_ECHO", disp := PiDisposition.transcriptOnly "same" }]
-/
#guard_msgs (error, drop info, drop warning) in
-- ⑤ THE OTHER DIRECTION. Slot 0 IS pinned; calling it transcript-only would let the class absorb
-- a real binding and make the census under-report what the AIR forces.
example : EffectVmDescriptor2 :=
  withPiManifest forcedM
    [ ⟨0, "STATE_COMMIT", .transcriptOnly "it is only a transcript value"⟩
    , ⟨1, "NONCE_ECHO", .transcriptOnly "same"⟩ ]

/-! ## The other half of the evidence: what each class MEANS, on these fixtures.

The refusals above show the condition bites. These show the two classes are not the same thing —
a `.bound` slot's value is forced by the trace, and a slot with no pin admits ANY value. Without
this pair, "declared" would be a label rather than a claim. -/

/-- Slot 1 of `forcedM` carries no pin: `unpinned_pi_admits_any_value` applies to it, so every
satisfying witness has a sibling publishing an arbitrary value there. -/
theorem slot_one_is_unpinned : (1 : Nat) ∉ pinnedSlots forcedM := by decide

/-- Slot 0 IS pinned, so the same statement is NOT available for it — which is the difference the
whole module is about. -/
theorem slot_zero_is_pinned : (0 : Nat) ∈ pinnedSlots forcedM := by decide

/-- The unforced fixture's pin is exactly what the existing census condemns — stated here so the
composition in `bound_decl_pin_survives_subtraction` is checked against a live instance rather
than only in the abstract. -/
theorem unforcedM_pin_is_censused :
    (Dregg2.Circuit.Emit.UnforcedPiPins.unforcedPins unforcedM).map (fun p => p.2.2) = [0] := by
  decide

/-- …and `forcedM`'s is not. -/
theorem forcedM_has_no_unforced_pin :
    Dregg2.Circuit.Emit.UnforcedPiPins.unforcedPins forcedM = [] := by decide

#assert_axioms goodManifest_admitted
#assert_axioms gate_changes_no_byte
#assert_axioms unforcedM_pin_is_censused
#assert_axioms forcedM_has_no_unforced_pin

end Dregg2.Circuit.PiDeclarationBite
