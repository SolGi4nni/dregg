/-
# CrewFieldMissionRuntimeBoundary — constructor-privacy regression teeth

`CrewRelayExpeditionBoundary` used to ratchet the *relay kernel*, whose state
machine had no consumer anywhere in the tree; both were deleted on 2026-08-06.
Nothing ratcheted the module that a host would actually call.  This is that
ratchet, over `CrewFieldMissionRuntime`.

It exists because the runtime's safety rests entirely on which names a caller
cannot reach.  A future edit that drops a `private` on any name below hands an
importer the ability to mint an activation with a chosen replay authority, to
fabricate a field record without the wire codec, to forge a run or successor
digest, to parse wire bytes while skipping the re-encode equality that makes
`canonicalDecode` canonical, or to authorize a salvage mint directly.  None of
those would fail to compile; this module is what turns them red.

⚑ 2026-08-06 — this warning USED to read: "`deriveRecord?` reconstructs a
terminal `CrewFieldMission.StateSnapshot` by *asserting* `phase := .extracted`;
it never drives `CrewFieldMission.execute`."  That is fixed.  `deriveRecord?`
now returns `RunSeal.replay?`, so the record is the one the kernel reached.

⚠ Read what that does and does not buy.  The runtime no longer fabricates a
terminal state, and a record it emits is one `CrewFieldMission.execute` produced
from signed handoffs.  That is a real weld and these teeth keep the seal
unreachable.  It is still NOT a refinement theorem: nothing here proves the
runtime's judgements agree with the kernel's on all inputs, and the fixture
signature suite is non-cryptographic.  The evidence is the weld plus the
`native_decide` cases in `CrewFieldMissionRuntime`, at that resolution.
-/
import Dregg2.Games.PathOfAngels.CrewFieldMissionRuntime
import Dregg2.Tactics

namespace Dregg2.Games.PathOfAngels.CrewFieldMissionRuntimeBoundary

open Dregg2.Games.PathOfAngels.CrewFieldMissionRuntime

set_option autoImplicit false

/-! ## The pinned activation

`Activation` is the only value that ties a `RawActivation` to the replay
authority trusted to verify it.  Its constructor and its verifier field are
private so that no importer can pair an authored activation with a verifier of
its own choosing, nor read the verifier back out to compare against one. -/

theorem activation_constructor_is_private : True := by
  fail_if_success (have _ := Activation.mk)
  trivial

/-- ⚑ 2026-08-06 — replaces `activation_replay_authority_field_is_private`.  The
field is now the `CrewFieldMission.RunSeal` that replays the run, and hiding it
matters more than hiding its predecessor did: a reachable seal is a reachable
`replay?`, and a caller could obtain the kernel's record for a transcript without
`judge`'s cursor, admission, officer and custody checks. -/
theorem activation_run_seal_field_is_private : True := by
  fail_if_success (have _ := Activation.runSeal)
  trivial

/-! ## The record derivation

`deriveRecord?` maps a caller-supplied `CommandWire` to the
`CrewFieldMission.RawCombinedFieldRecord` the kernel reached.  Exposed, it would
let a caller obtain that record without passing through `judge`'s cursor,
admission, officer and custody checks. -/

theorem raw_record_reconstructor_is_private : True := by
  fail_if_success (have _ := deriveRecord?)
  trivial

/-! ⚑ `transcript_structural_checker_is_private` and
`final_counter_projection_is_private` were DELETED here, not left standing.
`tracesStructurallyValidB` and `finalCounters` went with the weld — the kernel
enforces those checks now — and `fail_if_success (have _ := <deleted name>)`
SUCCEEDS for a name that does not exist.  Kept, they would have gone on passing
while guarding nothing, which is how a falsifier stops falsifying. -/

/-! ## The wire encoder

`TraceWire.ofSemantic` is fixture scaffolding, not host ABI: the host sends
`TraceWire`.  Public, it would read as a supported way to author a transcript
from semantic traces the caller assembled. -/

theorem wire_encoder_is_private : True := by
  fail_if_success (have _ := TraceWire.ofSemantic)
  trivial

/-! ## Digest minters

`runDigest` binds the run into the successor head and `successorDigest` is the
head a durable host CASes to.  A caller able to compute either could present a
state whose head it chose.

(`runDigest` used to key a `consumedRuns` ledger; that ledger was deleted on
2026-08-06 because its membership test could not fire — see the argument in
`CrewFieldMissionRuntime` beside `StateWire.validB`.  The digest still binds the
command into the successor, so this tooth still guards something.) -/

theorem run_digest_minter_is_private : True := by
  fail_if_success (have _ := runDigest)
  trivial

theorem successor_digest_minter_is_private : True := by
  fail_if_success (have _ := successorDigest)
  trivial

/-! ## Raw parsers that skip the re-encode equality

`decodeCommand` and `decodeState` are canonical: they parse, re-encode, and
demand byte equality (`canonicalDecode_reencodes`).  The underlying parsers do
not.  Exposing them would give a caller a non-canonical decode path and make
`decodeCommand_reencodes` a statement about a function nobody has to use. -/

theorem raw_command_parser_is_private : True := by
  fail_if_success (have _ := parseCommandJson)
  trivial

theorem raw_state_parser_is_private : True := by
  fail_if_success (have _ := parseStateJson)
  trivial

theorem raw_transcript_parser_is_private : True := by
  fail_if_success (have _ := parseTranscript)
  trivial

theorem raw_exact_key_checker_is_private : True := by
  fail_if_success (have _ := exactKeys)
  trivial

/-! ## Settlement authorizers

The two salvage namespaces are the point of the module: ordinary parts may mint
and reach a market, provenance relics may not.  Both producers are private so
the taxonomy cannot be re-labelled by a caller. -/

theorem ordinary_mint_authorizer_is_private : True := by
  fail_if_success (have _ := ordinaryMints)
  trivial

theorem relic_custody_authorizer_is_private : True := by
  fail_if_success (have _ := relicCustody?)
  trivial

/-! ## Adversarial fixtures

The hostile activations exist to be refused inside this module.  Importable,
they become a supply of pre-built invalid values — including the rekeyed crew
whose whole purpose is to share an `activationId` with the authored one. -/

theorem authored_fixture_activation_is_private : True := by
  fail_if_success (have _ := fixtureActivation)
  trivial

theorem rekeyed_crew_fixture_is_private : True := by
  fail_if_success (have _ := rekeyedRawActivation)
  trivial

theorem rekeyed_crew_activation_is_private : True := by
  fail_if_success (have _ := rekeyedActivation)
  trivial

theorem hostile_market_content_fixture_is_private : True := by
  fail_if_success (have _ := hostileMarketContent)
  trivial

/-! ## What stays reachable

A ratchet that forbade everything would also forbid the module being used.  The
canonical decoders, the judge, the exported ABI shape and the wire encoders are
deliberately public; this theorem fails if one of them is ever made private,
which would silently strand the organ. -/

theorem canonical_surface_stays_public : True := by
  have _ := @decodeCommand
  have _ := @decodeState
  have _ := @judge
  have _ := @process
  have _ := @StateWire.toJson
  have _ := @CommandWire.toJson
  have _ := @rosterBindingOf
  trivial

#assert_axioms activation_constructor_is_private
#assert_axioms activation_run_seal_field_is_private
#assert_axioms raw_record_reconstructor_is_private
#assert_axioms wire_encoder_is_private
#assert_axioms run_digest_minter_is_private
#assert_axioms successor_digest_minter_is_private
#assert_axioms raw_command_parser_is_private
#assert_axioms raw_state_parser_is_private
#assert_axioms raw_transcript_parser_is_private
#assert_axioms raw_exact_key_checker_is_private
#assert_axioms ordinary_mint_authorizer_is_private
#assert_axioms relic_custody_authorizer_is_private
#assert_axioms authored_fixture_activation_is_private
#assert_axioms rekeyed_crew_fixture_is_private
#assert_axioms rekeyed_crew_activation_is_private
#assert_axioms hostile_market_content_fixture_is_private
#assert_axioms canonical_surface_stays_public

end Dregg2.Games.PathOfAngels.CrewFieldMissionRuntimeBoundary
