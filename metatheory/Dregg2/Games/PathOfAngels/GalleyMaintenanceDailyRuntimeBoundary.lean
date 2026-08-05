/-
# GalleyMaintenanceDailyRuntimeBoundary — privacy teeth over the thing that SHIPS

`docs/poa/GALLEY-LAYER-CONTRACT.md` **G8** said: the deleted
`GalleyMaintenanceDailyBoundary` ratcheted the *kernel's* privacy, while the
Runtime — the module `@[export dregg_poa_galley_daily_judge]` actually runs — had
no equivalent, so nothing prevented a future edit from publishing `nextEvent`,
`commandPayload?` or `AdmittedBetaSponsor.mk`.  This module is that ratchet, on
the module that ships.  G8 is closed by moving the teeth, not by deleting them.

Every theorem here is `True`-valued and proved by `fail_if_success`.  That is the
point: each one can only go RED, and it goes red exactly when a `private` marker
is dropped.  The mutations that refute them are named at each theorem.
-/
import Dregg2.Games.PathOfAngels.GalleyMaintenanceDailyRuntime
import Dregg2.Tactics

namespace Dregg2.Games.PathOfAngels.GalleyMaintenanceDailyRuntimeBoundary

open Dregg2.Games.PathOfAngels.GalleyMaintenanceDailyRuntime

set_option autoImplicit false

/-- ⚑ THE AUTHORITY GATE.  `no_authority_cannot_form_holder_payload` proves only
that `authority = none` cannot reach the sponsor branch — which is what the
export passes.  It says nothing about a caller that *mints* an authority.  The
constructor being private is the whole reason no such caller exists.

Refutation: delete `private mk ::` from `AdmittedBetaSponsor` and this goes red;
today nothing else in the tree would notice, because the sponsor branch is
reachable the instant an `AdmittedBetaSponsor` value exists. -/
theorem sponsor_authority_constructor_is_private : True := by
  fail_if_success (have _ := AdmittedBetaSponsor.mk)
  trivial

/-- The action tokens a player signs against are minted here and nowhere else.
`requestedAction?` requires the requested `(kind, token)` to be one this judge
would have offered; publishing the minters would let a caller name a token the
offer set never contained.

Refutation: publish `tokenPreimage`, `publicAction` or `sponsorAction`. -/
theorem action_token_minters_are_private : True := by
  fail_if_success (have _ := tokenPreimage)
  fail_if_success (have _ := publicAction)
  fail_if_success (have _ := sponsorAction)
  fail_if_success (have _ := authorityMatchesB)
  trivial

/-- ⚑ THE UNCHECKED TRANSITION SURFACE.  `judgeInput?` is the only public way to
move the Galley, and every check it performs — prefix validation against the
claimed projection, offer membership, `applyEvent`'s structural gates — lives in
these five.  Any of them public is a second entrance that skips the others.

Refutation: publish `validatedPrefix?`, `commandPayload?`, `requestedAction?`,
`nextEvent`, `receiptOf` or `outputOf`. -/
theorem unchecked_transition_surface_is_private : True := by
  fail_if_success (have _ := validatedPrefix?)
  fail_if_success (have _ := commandPayload?)
  fail_if_success (have _ := requestedAction?)
  fail_if_success (have _ := nextEvent)
  fail_if_success (have _ := receiptOf)
  fail_if_success (have _ := outputOf)
  fail_if_success (have _ := anchorsExactB)
  trivial

/-- ⚑ CANONICALITY IS THE DECODER'S CONTRACT (contract doc §2.5).  The public
decoders are `decodeInput` / `decodeOutput` / `decodePolicy` /
`decodeBetaHolderSeal`, each of which parses and then demands byte equality
against a re-encode.  The raw `Json → Except String _` parsers do NOT: a consumer
holding one could accept a non-canonical spelling that the round-trip refuses,
and `decodeInput_reencodes` would still be green.

Refutation: publish any `parse*`. -/
theorem raw_parsers_are_private : True := by
  fail_if_success (have _ := parseInputJson)
  fail_if_success (have _ := parseOutputJson)
  fail_if_success (have _ := parsePolicy)
  fail_if_success (have _ := parseEvent)
  fail_if_success (have _ := parseEvents)
  fail_if_success (have _ := parseProjection)
  fail_if_success (have _ := parsePayload)
  fail_if_success (have _ := parseStatement)
  fail_if_success (have _ := parseViewer)
  fail_if_success (have _ := parseActionRequest)
  fail_if_success (have _ := parseBetaHolderSealJson)
  fail_if_success (have _ := parseView)
  fail_if_success (have _ := parseReceipt)
  fail_if_success (have _ := parseReplay)
  fail_if_success (have _ := parseActionToken)
  fail_if_success (have _ := parseActionTokens)
  fail_if_success (have _ := exactKeys)
  trivial

/-- The adversarial fixtures are test seeds, not an API.  `fixtureAuthority` in
particular is a fully-formed `AdmittedBetaSponsor`: public, it would hand every
importer the authority the theorem above exists to withhold.

Refutation: publish `fixtureAuthority`, `fixturePolicy` or any `fixture*`. -/
theorem adversarial_fixtures_are_private : True := by
  fail_if_success (have _ := fixtureAuthority)
  fail_if_success (have _ := fixtureCarrier)
  fail_if_success (have _ := fixturePolicy)
  fail_if_success (have _ := fixtureViewer)
  fail_if_success (have _ := fixtureState0)
  fail_if_success (have _ := fixtureViewInput)
  fail_if_success (have _ := fixturePublicCommand)
  fail_if_success (have _ := fixtureSponsorCommand)
  fail_if_success (have _ := fixtureForgedSponsor)
  trivial

/-- Encoding internals: the canonical JSON spelling is `*.toJson`, and the
byte-level helpers that build it are not a second encoder anyone may call. -/
theorem encoder_internals_are_private : True := by
  -- ⚠ `optionJson` is deliberately NOT probed here: it takes an implicit `{T : Type}`,
  -- so `have _ := optionJson` fails to elaborate on an unassigned metavariable whether or
  -- not it is private.  A `fail_if_success` that would succeed anyway is decoration, not a
  -- tooth.  Every name below is closed and resolves the moment its `private` is dropped.
  fail_if_success (have _ := jsonString)
  fail_if_success (have _ := jsonArray)
  fail_if_success (have _ := zeroDigest)
  fail_if_success (have _ := insertDigest)
  fail_if_success (have _ := u32le)
  fail_if_success (have _ := stringBytes)
  trivial

/-! ## The exported surface — deliberately public, and now welded

`judgeFFI` is the one `@[export]`.  `reduce` is the one state machine, and the
three theorems below are what make that sentence a theorem rather than a naming
convention: they say the projection `judgeInput?` publishes is `reduce`'s
successor of the caller's claimed projection.  Before them, a judge that
published a projection of its own invention passed every check in the tree. -/
#check judgeFFI
#check reduce
#check judge_command_projection_is_reduce
#check judge_view_projection_is_claimed
#check judge_output_preserves_advantage_anchors
#check decodeInput
#check decodeOutput
#check decodePolicy

#assert_axioms sponsor_authority_constructor_is_private
#assert_axioms action_token_minters_are_private
#assert_axioms unchecked_transition_surface_is_private
#assert_axioms raw_parsers_are_private
#assert_axioms adversarial_fixtures_are_private
#assert_axioms encoder_internals_are_private

end Dregg2.Games.PathOfAngels.GalleyMaintenanceDailyRuntimeBoundary
