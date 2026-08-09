/-
# SignalFeedbackRuntime — the mid-run feedback oracle, and the ONLY thing it may say

Substrate note: this is Lean-authored game semantics behind a canonical byte wire.
Nothing here is an AIR, a constraint system or a gadget.  Rust carries bytes to this
module and back; it computes nothing, and in particular it does not compute
LOCKED/DRIFT.

## Why this export exists

Judged Signal was a SLOT MACHINE.  A public `SignalClaimV1` carries one code, the judge
scores it against an instance the player has never been told anything about, and
`SignalTriangulation.judge` returns `none` unless the transcript is SOLVED — so an
on-chain play was a blind 1-in-216 guess.  The actual game — 216 codes, LOCKED/DRIFT
feedback, an information floor of three rounds — existed only in the browser's practice
mode, drawn from `HiddenInstance.practiceRunSeed`, which no judge will ever score.

A judged session needs the rule applied to the JUDGED instance mid-run.  The rule is
`SignalTriangulation.feedback` and it stays here: a Rust `exactCount`/`presentCount`
would be a twin of the scoring function, and a twin that disagrees by one on a
duplicate band hands players a different game than the one that settles.

## ⚠ The one thing this wire must never do

`SlotDeriveRuntime` returns the RUN SEED and the TARGET.  Its docblock says plainly that
the reply "is the puzzle solution" and that nothing rendering it may reach a route.  This
export is the opposite posture — it is *made* to be reached from a route — so it must
carry strictly less.

`Reply` therefore has exactly two fields, `exact` and `present`, and no constructor
anywhere in this module puts a secret, a run seed, a commitment or a target into one.
That is a type-level fact, visible in the structure below.  What is PROVED, because it is
not visible, is that the served BYTES separate no more than the classification does:

* `reply_bytes_are_a_function_of_the_feedback_alone` — two requests whose feedback
  agrees serve byte-identical replies, however much else differs (secret, slot, player,
  mission, the target itself).
* `served_transcript_cannot_separate_feedback_equivalent_targets` — over a whole
  session, two targets consistent with the guesses played serve identical bytes.  A
  reader of a complete unsolved session transcript is therefore in exactly the position
  of the player who produced it, and no further along.
* `SignalTriangulation.one_round_never_determines_the_target` — and after one round that
  position is never "solved", for any opening.  The invariance is not vacuous.

## The commitment is CHECKED here, not echoed

The request carries the node's INSTALLED slot commitment and Lean refuses (the `""`
sentinel) unless `HiddenInstance.commit secret slot` reproduces it.  Two reasons it is an
input rather than an output:

* a node whose secret does not open the published commitment must serve NOTHING, not a
  classification against an instance no curator promised; and
* echoing it would put a value in the reply that is not the classification, which is the
  exact door this module exists to keep shut — even though that particular value is
  already public (`poa_signal_slot_api` publishes it, curator-signed).

## The wire

Request (`POA-SIGNAL-FEEDBACK-1`), key order pinned by `Request.toJson`:

    {"format":"POA-SIGNAL-FEEDBACK-1","slot":<u64>,"secret":"<64 lowercase hex>",
     "mission_id":<u64>,"epoch":<u64>,"federation_id":"<64 lowercase hex>",
     "content_session":"<64 lowercase hex>","player_key":"<64 lowercase hex>",
     "commitment":"<64 lowercase hex>","guess":{"low":<0..5>,"mid":<0..5>,"high":<0..5>}}

Reply (`POA-SIGNAL-FEEDBACK-OUT-1`):

    {"format":"POA-SIGNAL-FEEDBACK-OUT-1","exact":<0..3>,"present":<0..3>}

`exact` is LOCKED and `present` is DRIFT; the names are `SignalTriangulation.Feedback`'s
own field names rather than the UI's rendering, so there is one spelling of each number
between the rule and the browser.

The first eight request fields are byte-identical to `POA-SLOT-DERIVE-1`'s, deliberately:
`request_derives_the_judged_instance` is `rfl` against `SlotDeriveRuntime.derive`, which
is what makes the feedback a player is served feedback about the instance that will
SETTLE, rather than about a second instance that happens to agree today.

⚠ The SECRET crosses this wire, as it does the derivation wire.  It is node-held state,
never a client claim, and the reply deliberately does not echo it.

Acceptance is `NetworkJudgeWire.canonicalDecode` — the same seal `decodeSignalInput` and
`SlotDeriveRuntime.decodeRequest` use, imported rather than re-typed.  An unknown field,
a missing field, a transposed key, an uppercase digit, an out-of-range band, a trailing
byte or a re-spelled integer all fail the byte comparison and the export returns `""`.
-/
import Lean.Data.Json
import Dregg2.Games.PathOfAngels.SlotDeriveRuntime
import Dregg2.Tactics

namespace Dregg2.Games.PathOfAngels.SignalFeedbackRuntime

open Lean (Json)
open Dregg2.Games.PathOfAngels

set_option autoImplicit false

abbrev INPUT_FORMAT : String := "POA-SIGNAL-FEEDBACK-1"
abbrev OUTPUT_FORMAT : String := "POA-SIGNAL-FEEDBACK-OUT-1"

/-- Outer allocation fuse.  Mirrors `MAX_POA_SIGNAL_FEEDBACK_WIRE_BYTES` in
`dregg-lean-ffi/src/poa_signal_feedback_ffi.rs`. -/
abbrev WIRE_BYTE_LIMIT : Nat := 64 * 1024

abbrev WIRE_NAT_LIMIT : Nat := 2 ^ 64 - 1

/-! ## The two wire records -/

/-- One mid-run classification request.

The first seven fields are `SlotDeriveRuntime.Request` exactly; `commitment` is the
installed publication the derivation must reproduce, and `guess` is the player's move. -/
structure Request where
  slot : Nat
  secret : Digest32
  missionId : Nat
  epoch : Nat
  federationId : Digest32
  contentSession : Digest32
  playerKey : Digest32
  commitment : Digest32
  guess : SignalTriangulation.Code
deriving DecidableEq

/-- ⚠ **THE WHOLE REPLY.**  Two counts.  There is no field here for a seed, a target, a
commitment or a secret, and adding one would be the wound this module exists to prevent
rather than a convenience. -/
structure Reply where
  feedback : SignalTriangulation.Feedback
deriving DecidableEq

private def jsonString (s : String) : String := String.quote s

private def codeJson (c : SignalTriangulation.Code) : String :=
  "{\"low\":" ++ toString c.low.val ++
    ",\"mid\":" ++ toString c.mid.val ++
    ",\"high\":" ++ toString c.high.val ++ "}"

def Request.toJson (request : Request) : String :=
  "{\"format\":" ++ jsonString INPUT_FORMAT ++
    ",\"slot\":" ++ toString request.slot ++
    ",\"secret\":" ++ jsonString (Emit.bytes32Hex request.secret) ++
    ",\"mission_id\":" ++ toString request.missionId ++
    ",\"epoch\":" ++ toString request.epoch ++
    ",\"federation_id\":" ++ jsonString (Emit.bytes32Hex request.federationId) ++
    ",\"content_session\":" ++ jsonString (Emit.bytes32Hex request.contentSession) ++
    ",\"player_key\":" ++ jsonString (Emit.bytes32Hex request.playerKey) ++
    ",\"commitment\":" ++ jsonString (Emit.bytes32Hex request.commitment) ++
    ",\"guess\":" ++ codeJson request.guess ++ "}"

def Reply.toJson (reply : Reply) : String :=
  "{\"format\":" ++ jsonString OUTPUT_FORMAT ++
    ",\"exact\":" ++ toString reply.feedback.exact ++
    ",\"present\":" ++ toString reply.feedback.present ++ "}"

/-! ## Strict parse -/

private def exactKeys (j : Json) (allowed : List String) : Except String Unit := do
  let object ← j.getObj?
  if object.size == allowed.length && allowed.all object.contains then
    pure ()
  else
    throw "missing or unknown field"

private def objectNat (j : Json) (key : String) : Except String Nat := do
  let value ← j.getObjValAs? Nat key
  if value ≤ WIRE_NAT_LIMIT then pure value else throw "integer exceeds wire bound"

private def objectDigest (j : Json) (key : String) : Except String Digest32 := do
  let spelling ← j.getObjValAs? String key
  match Emit.parseBytes32Hex? spelling with
  | some digest => pure digest
  | none => throw "digest must be exactly 64 lowercase hexadecimal digits"

private def objectBand (j : Json) (key : String) : Except String (Fin 6) := do
  let value ← j.getObjValAs? Nat key
  if h : value < 6 then pure ⟨value, h⟩ else throw "band exceeds the base-six bound"

private def parseCode (j : Json) : Except String SignalTriangulation.Code := do
  exactKeys j ["low", "mid", "high"]
  pure {
    low := ← objectBand j "low"
    mid := ← objectBand j "mid"
    high := ← objectBand j "high"
  }

private def parseRequestJson (j : Json) : Except String Request := do
  exactKeys j ["format", "slot", "secret", "mission_id", "epoch", "federation_id",
    "content_session", "player_key", "commitment", "guess"]
  let format ← j.getObjValAs? String "format"
  if format != INPUT_FORMAT then throw "wrong Signal feedback request format"
  pure {
    slot := ← objectNat j "slot"
    secret := ← objectDigest j "secret"
    missionId := ← objectNat j "mission_id"
    epoch := ← objectNat j "epoch"
    federationId := ← objectDigest j "federation_id"
    contentSession := ← objectDigest j "content_session"
    playerKey := ← objectDigest j "player_key"
    commitment := ← objectDigest j "commitment"
    guess := ← parseCode (← j.getObjVal? "guess")
  }

def decodeRequestWithLimit (byteLimit : Nat) (bytes : String) : Option Request :=
  if bytes.length ≤ byteLimit then
    NetworkJudgeWire.canonicalDecode parseRequestJson Request.toJson bytes
  else none

def decodeRequest (bytes : String) : Option Request :=
  decodeRequestWithLimit WIRE_BYTE_LIMIT bytes

/-! ## The classification -/

/-- The first seven fields of a feedback request ARE a derivation request.  This is the
projection that makes the weld below `rfl` rather than a coincidence of two encoders. -/
def deriveRequestOf (request : Request) : SlotDeriveRuntime.Request where
  slot := request.slot
  secret := request.secret
  missionId := request.missionId
  epoch := request.epoch
  federationId := request.federationId
  contentSession := request.contentSession
  playerKey := request.playerKey

/-- The instance this request is answerable to, as `SlotDeriveRuntime` derives it.

⚠ `none` when the run seed draws no instance.  The oracle then serves nothing rather
than classifying against a substitute — a mid-run oracle that answered against a target
the judge would not score is worse than one that refuses. -/
def derivedOf? (request : Request) : Option SlotDeriveRuntime.Reply :=
  SlotDeriveRuntime.derive? (deriveRequestOf request)

/-- The hidden target — **internal, and it reaches no output.**  `Reply` has no field it
could occupy and `classifyBytes?` never mentions it except through `feedback`. -/
def targetOf? (request : Request) : Option SignalTriangulation.Code :=
  (derivedOf? request).map SlotDeriveRuntime.Reply.target

/-- Whether the node's secret opens the commitment it says the curator published.
A request whose seed draws nothing opens nothing: `Option.any` is `false` on `none`. -/
def commitmentOpens (request : Request) : Bool :=
  (derivedOf? request).any (fun d => d.commitment = request.commitment)

/-- The classification, and nothing else: `SignalTriangulation.feedback` of the derived
target and the submitted guess. -/
def classify? (request : Request) : Option SignalTriangulation.Feedback :=
  (targetOf? request).map (fun t => SignalTriangulation.feedback t request.guess)

def replyOf? (request : Request) : Option Reply :=
  (classify? request).map (fun f => { feedback := f })

/-- Fail-closed on three legs now: a wire that is not canonical, a secret that does not
open the stated commitment, and a run seed that draws no instance — each produces `none`
and therefore the `""` sentinel. -/
def classifyBytes? (bytes : String) : Option String :=
  match decodeRequest bytes with
  | none => none
  | some request =>
      if commitmentOpens request then (replyOf? request).map Reply.toJson else none

/-- **`@[export dregg_poa_signal_feedback]`** — the mid-run LOCKED/DRIFT oracle.

This export confers no authority and reads no state.  It is a pure function of the bytes
it is handed, and the node must obtain those bytes — the slot secret above all — from
its own authenticated state.  Unlike `dregg_poa_signal_slot_derive`, its reply is
DELIBERATELY reachable from an authenticated route, which is only sound because the
reply is the classification and provably nothing else. -/
@[export dregg_poa_signal_feedback]
def signalFeedbackFFI (bytes : String) : String :=
  (classifyBytes? bytes).getD ""

/-! ## What the export is, stated generally

None of the theorems in this section mentions a concrete digest, so neither side of any
equation reduces the Poseidon2 sponge. -/

/-- The seal: accepted bytes are the bytes this module would have written. -/
theorem decodeRequest_reencodes {bytes : String} {request : Request}
    (accepted : decodeRequest bytes = some request) : request.toJson = bytes := by
  simp only [decodeRequest, decodeRequestWithLimit] at accepted
  split at accepted
  · exact NetworkJudgeWire.canonicalDecode_reencodes parseRequestJson Request.toJson accepted
  · contradiction

theorem decodeRequest_accepted_bytes_injective {left right : String} {request : Request}
    (hleft : decodeRequest left = some request)
    (hright : decodeRequest right = some request) : left = right := by
  rw [← decodeRequest_reencodes hleft, ← decodeRequest_reencodes hright]

theorem decodeRequest_refuses_oversized {bytes : String} (h : WIRE_BYTE_LIMIT < bytes.length) :
    decodeRequest bytes = none := by
  simp [decodeRequest, decodeRequestWithLimit, Nat.not_le.mpr h]

theorem signalFeedbackFFI_refuses_uncanonical {bytes : String}
    (h : decodeRequest bytes = none) : signalFeedbackFFI bytes = "" := by
  simp [signalFeedbackFFI, classifyBytes?, h]

/-- ⚑ A node whose secret does not open the stated commitment is served nothing.  The
oracle is not merely "the operator's classification"; it is a classification against the
instance the curator committed to in advance, or it is a refusal. -/
theorem signalFeedbackFFI_refuses_an_unopened_commitment {bytes : String} {request : Request}
    (accepted : decodeRequest bytes = some request) (h : commitmentOpens request = false) :
    signalFeedbackFFI bytes = "" := by
  have refused : classifyBytes? bytes = none := by
    unfold classifyBytes?
    rw [accepted]
    simp only [h, Bool.false_eq_true, if_false]
  unfold signalFeedbackFFI
  rw [refused]
  rfl

/-- ⚑ **THE CLASSIFICATION IS LEAN'S RULE.**  Not a Rust `exactCount`, not a second
spelling of Mastermind: `SignalTriangulation.feedback`, the function
`SignalTriangulation.step` scores a judged transcript with. -/
theorem classify_is_the_triangulation_rule (request : Request) :
    classify? request =
      (targetOf? request).map (fun t => SignalTriangulation.feedback t request.guess) := rfl

/-- ⚑ **THE WELD.**  The target this oracle classifies against IS the target
`SlotDeriveRuntime.derive?` hands the judge for the same slot, secret, context and
player — and it REFUSES on exactly the seeds that one refuses.  Feedback served mid-run
and the verdict that settles are about ONE instance, including when there is none. -/
theorem request_derives_the_judged_instance (request : Request) :
    targetOf? request =
      (SlotDeriveRuntime.derive? (deriveRequestOf request)).map
        SlotDeriveRuntime.Reply.target := rfl

/-- The seed the oracle draws against carries the JUDGED purpose tag, not
`practiceRunSeed`.  A practice run and a judged run are different draws, so a practice
transcript can never be replayed as a judged one. -/
theorem judged_run_seed_is_the_judged_draw (request : Request) :
    SlotDeriveRuntime.runSeedOf (deriveRequestOf request) =
      HiddenInstance.runSeedFor
        { secret := ⟨request.secret⟩, slot := ⟨request.slot⟩, playerKey := request.playerKey }
        (SlotDeriveRuntime.contextOf (deriveRequestOf request)) := rfl

/-- The oracle's instance is the DRAW of that seed — the same partial draw the judge
applies, with no substitution anywhere between them. -/
theorem judged_target_is_from_the_judged_run_seed (request : Request) :
    targetOf? request =
      SignalTriangulation.targetFromSeed?
        (SlotDeriveRuntime.runSeedOf (deriveRequestOf request)) := by
  unfold targetOf? derivedOf? SlotDeriveRuntime.derive?
  generalize SignalTriangulation.targetFromSeed?
    (SlotDeriveRuntime.runSeedOf (deriveRequestOf request)) = t
  cases t <;> rfl

/-- ⚑ **THE REPLY IS THE FEEDBACK AND NOTHING ELSE.**  Two requests whose classification
agrees serve byte-identical replies — whatever else differs between them: the secret,
the slot, the player, the mission, the run seed, the target.  The served bytes are a
function of the classification alone, so no field of the request is recoverable from a
reply beyond what the classification itself says. -/
theorem reply_bytes_are_a_function_of_the_feedback_alone {left right : Request}
    (h : classify? left = classify? right) :
    (replyOf? left).map Reply.toJson = (replyOf? right).map Reply.toJson := by
  simp only [replyOf?, h]

/-- The bytes served for one guess against one target.  This is the whole observable of
a judged session round. -/
def servedBytes (target guess : SignalTriangulation.Code) : String :=
  (Reply.mk (SignalTriangulation.feedback target guess)).toJson

/-- ⚑ **NO OVER-REVEAL, OVER A WHOLE SESSION.**  If two targets agree on the guesses
PLAYED, the session serves byte-identical bytes for both, round for round.

This is the precise form of "a reader cannot reconstruct the target faster than
playing": everything a session emits is invariant across the feedback-consistency class
of its own transcript, so a reader's information is exactly that class — which is what
the player who produced the transcript has, and nothing more.  Combined with
`SignalTriangulation.one_round_never_determines_the_target`, that class is never a
singleton after one round, so the invariance is over a genuinely non-trivial set. -/
theorem served_transcript_cannot_separate_feedback_equivalent_targets
    (t₁ t₂ : SignalTriangulation.Code) (guesses : List SignalTriangulation.Code)
    (agree : ∀ g ∈ guesses, SignalTriangulation.feedback t₁ g =
      SignalTriangulation.feedback t₂ g) :
    guesses.map (servedBytes t₁) = guesses.map (servedBytes t₂) := by
  refine List.map_congr_left ?_
  intro g hg
  simp [servedBytes, agree g hg]

/-- A solved round is exactly a solved round: the reply says `exact = 3` iff the guess
IS the target, which is the same predicate `SignalTriangulation.step` sets `solved` by.
A session cannot call a run solved on any other evidence. -/
theorem reply_reports_solved_iff_the_guess_is_the_target {request : Request}
    {t : SignalTriangulation.Code} (htarget : targetOf? request = some t) :
    (classify? request).any (fun f => f.exact == 3) = true ↔ request.guess = t := by
  rw [classify?, htarget]
  simp only [Option.map_some, Option.any_some, beq_iff_eq]
  exact SignalTriangulation.exactCount_eq_three_iff _ _

/-- Both served numbers are bounded by three, so the wire's integers are single digits
and the reply length is fixed.  A length side channel would be a field by another name.

⚠ Stated with `Option.all`, which is `true` on `none` — that is not a hole here: a
refusal serves no bytes at all, so there is no reply for a bound to be about. -/
theorem served_counts_are_bounded (request : Request) :
    (classify? request).all (fun f => decide (f.exact + f.present ≤ 3)) = true := by
  unfold classify?
  generalize targetOf? request = t
  cases t with
  | none => rfl
  | some target =>
      simp only [Option.map_some, Option.all_some, decide_eq_true_eq]
      exact SignalTriangulation.feedback_match_bound _ _

/-! ## Concrete requests, and why these are compiled pins

Each fixture below names a real digest, so kernel reduction would have to run the
Poseidon2 permutation.  The pins are `native_decide` and pinned with `#assert_compiled`.
What they buy is that the general statements above are not vacuous over an empty
accepted set: the wire really does decode, the sponge really does run, and the refusals
really are reachable.

⚑ **THE PINS NO LONGER EVALUATE IN THIS MODULE (2026-08-08).** This module is in the
`Dregg2.FFI` closure — the crypto archive's build root — and the twenty `native_decide`
pins below ran at elaboration, so a stale feedback fixture was a hard failure of every
Rust proving target in the workspace (the compilation-unit coupling the stale-fixture
outage measured). The pins' STATEMENTS stay here, each as an evaluation-free
`check_* : Bool` definition (a `def` body elaborates without running).  The EVALUATION —
each `check_* = true`, pinned by `native_decide` + `#assert_compiled` — lives in
`SignalFeedbackRuntimeFixtures.lean`, rooted in the `PathOfAngelsGuards` library: a plain
`lake build` still runs every pin, and a stale fixture reds the guard library instead of
the archive.

Named residue: NONE — no construction here demands a proof as data.  In particular
`fixtureTarget` is a carried literal, and the measurement tying it to the draw
(`fixtureTarget_is_the_drawn_instance`) is a pin like any other, not constructor data —
unlike its namesake in `NetworkJudgeWire`, which discharges `Config.target_eq` and had to
stay put. -/

private def hexDigest (hex : String) : Digest32 :=
  (Emit.parseBytes32Hex? hex).getD ⟨List.replicate 32 0, by simp⟩

/-- The commitment `SlotDeriveRuntime.fixtureRequest`'s secret and slot open.

⚠ It names `HiddenInstance.commit` directly rather than projecting the derivation,
because the derivation is now partial and this field is not: a commitment does not
depend on the draw at all (`SlotDeriveRuntime.derive_commitment_is_the_commit`).  It is
still tied to the other export's fixture rather than typed in — by
`fixtureCommitment_is_the_derived_commitment` below, which is what stops the two
drifting apart. -/
def fixtureCommitment : Digest32 :=
  HiddenInstance.commit ⟨SlotDeriveRuntime.fixtureRequest.secret⟩
    ⟨SlotDeriveRuntime.fixtureRequest.slot⟩

/-- (Pinned `= true` in `SignalFeedbackRuntimeFixtures`.) -/
def check_fixtureCommitment_is_the_derived_commitment : Bool :=
  decide ((SlotDeriveRuntime.derive? SlotDeriveRuntime.fixtureRequest).map
    SlotDeriveRuntime.Reply.commitment = some fixtureCommitment)

def fixtureRequest : Request where
  slot := SlotDeriveRuntime.fixtureRequest.slot
  secret := SlotDeriveRuntime.fixtureRequest.secret
  missionId := SlotDeriveRuntime.fixtureRequest.missionId
  epoch := SlotDeriveRuntime.fixtureRequest.epoch
  federationId := SlotDeriveRuntime.fixtureRequest.federationId
  contentSession := SlotDeriveRuntime.fixtureRequest.contentSession
  playerKey := SlotDeriveRuntime.fixtureRequest.playerKey
  commitment := fixtureCommitment
  guess := { low := 0, mid := 1, high := 2 }

def fixtureRequestBytes : String := fixtureRequest.toJson

/-- (Pinned `= true` in `SignalFeedbackRuntimeFixtures`.) -/
def check_fixture_request_roundtrips : Bool :=
  decide (decodeRequest fixtureRequestBytes = some fixtureRequest)

/-- ⚑ **THE FIXTURE'S SEED DRAWS, AND THIS IS THE INSTANCE.**  Carried as a literal and
measured, not derived: every pin below is a statement about a `some`, and without this
one they could all be satisfied by a refusal while reading green. -/
def fixtureTarget : SignalTriangulation.Code := { low := 2, mid := 5, high := 1 }

/-- (Pinned `= true` in `SignalFeedbackRuntimeFixtures`.) -/
def check_fixtureTarget_is_the_drawn_instance : Bool :=
  decide (targetOf? fixtureRequest = some fixtureTarget)

/-- The bytes this fixture is served, once. -/
def fixtureReplyJson? : Option String := (replyOf? fixtureRequest).map Reply.toJson

/-- (Pinned `= true` in `SignalFeedbackRuntimeFixtures`.) -/
def check_fixture_export_answers : Bool :=
  decide (some (signalFeedbackFFI fixtureRequestBytes) = fixtureReplyJson?)

/-- (Pinned `= true` in `SignalFeedbackRuntimeFixtures`.) -/
def check_fixture_export_is_not_the_refusal : Bool :=
  decide (signalFeedbackFFI fixtureRequestBytes ≠ "")

/-- (Pinned `= true` in `SignalFeedbackRuntimeFixtures`.) -/
def check_fixture_reply_is_canonical_and_states_the_format : Bool :=
  fixtureReplyJson?.any
    (fun j => j.startsWith ("{\"format\":\"" ++ OUTPUT_FORMAT ++ "\""))

/-- ⚠ The reply does not echo the SECRET.
(Pinned `= true` in `SignalFeedbackRuntimeFixtures`.) -/
def check_fixture_reply_does_not_carry_the_secret : Bool :=
  decide (fixtureReplyJson?.map
    (fun j => (j.splitOn SlotDeriveRuntime.FIXTURE_SECRET_HEX).length) = some 1)

/-- The `do`-block scrutinee of the run-seed absence pin, hoisted so the check below is a
plain equality on an `Option Nat`. -/
private def fixtureReplyRunSeedSplitCount? : Option Nat := do
  let j ← fixtureReplyJson?
  let d ← derivedOf? fixtureRequest
  pure (j.splitOn (Emit.bytes32Hex d.runSeed)).length

/-- ⚠ The reply does not echo the RUN SEED — the value the draw reads to pick the
answer. (Pinned `= true` in `SignalFeedbackRuntimeFixtures`.) -/
def check_fixture_reply_does_not_carry_the_run_seed : Bool :=
  decide (fixtureReplyRunSeedSplitCount? = some 1)

/-- ⚠ The reply does not echo the COMMITMENT either, though that value is public.
(Pinned `= true` in `SignalFeedbackRuntimeFixtures`.) -/
def check_fixture_reply_does_not_carry_the_commitment : Bool :=
  decide (fixtureReplyJson?.map
    (fun j => (j.splitOn (Emit.bytes32Hex fixtureCommitment)).length) = some 1)

/-- ⚠ The reply does not spell the TARGET.  A three-band code has a canonical JSON
spelling on this very wire (it is how the guess arrives); the served bytes do not
contain it. (Pinned `= true` in `SignalFeedbackRuntimeFixtures`.) -/
def check_fixture_reply_does_not_carry_the_target : Bool :=
  decide (fixtureReplyJson?.map
    (fun j => (j.splitOn (codeJson fixtureTarget)).length) = some 1)

/-- ⚑ THE ORACLE IS NOT CONSTANT.  Two guesses against the same instance get different
answers — so the export really is classifying, and the invariance theorems above are not
statements about a function that says the same thing to everyone. -/
def fixtureOtherGuess : Request :=
  { fixtureRequest with guess := { low := 3, mid := 4, high := 5 } }

/-- (Pinned `= true` in `SignalFeedbackRuntimeFixtures`.) -/
def check_fixture_two_guesses_are_classified_differently : Bool :=
  decide (signalFeedbackFFI fixtureRequestBytes ≠ signalFeedbackFFI fixtureOtherGuess.toJson)

/-- ⚑ THE TARGET SOLVES, AND IT IS THE ONLY THING THAT DOES on this instance.  The
session's solved bit is `exact = 3` and this is a live witness that the bit is
reachable. -/
def fixtureSolvingRequest : Request :=
  { fixtureRequest with guess := fixtureTarget }

/-- (Pinned `= true` in `SignalFeedbackRuntimeFixtures`.) -/
def check_fixture_the_target_locks_all_three : Bool :=
  decide (signalFeedbackFFI fixtureSolvingRequest.toJson =
    (Reply.mk { exact := 3, present := 0 }).toJson)

/-- ⚑ A DIFFERENT PLAYER IS A DIFFERENT GAME.  The same slot, secret, mission and guess
under another player key is classified against another instance — which is why a
per-player action budget cannot be farmed by opening sessions under other keys, and why
a session must be bound to the key that will sign the settling turn. -/
def fixtureOtherPlayer : Request :=
  { fixtureRequest with playerKey := SlotDeriveRuntime.otherPlayerRequest.playerKey }

/-- (Pinned `= true` in `SignalFeedbackRuntimeFixtures`.) -/
def check_fixture_another_player_draws_another_instance : Bool :=
  decide (targetOf? fixtureRequest ≠ targetOf? fixtureOtherPlayer)

/-- A secret that does not open the stated commitment is refused, not classified. -/
def fixtureWrongCommitment : Request :=
  { fixtureRequest with
    commitment := hexDigest
      "0000000000000000000000000000000000000000000000000000000000000000" }

/-- A secret that does not open the stated commitment is refused, not classified.
(Pinned `= true` in `SignalFeedbackRuntimeFixtures`.) -/
def check_fixture_unopened_commitment_refused : Bool :=
  decide (signalFeedbackFFI fixtureWrongCommitment.toJson = "")

/-- (Pinned `= true` in `SignalFeedbackRuntimeFixtures`.) -/
def check_fixture_trailing_byte_refused : Bool :=
  decide (signalFeedbackFFI (fixtureRequestBytes ++ "\n") = "")

/-- (Pinned `= true` in `SignalFeedbackRuntimeFixtures`.) -/
def check_fixture_unknown_field_refused : Bool :=
  decide (signalFeedbackFFI
    (fixtureRequestBytes.replace "\"slot\":9" "\"slot\":9,\"extra\":0") = "")

/-- (Pinned `= true` in `SignalFeedbackRuntimeFixtures`.) -/
def check_fixture_uppercase_digest_refused : Bool :=
  decide (signalFeedbackFFI
    (fixtureRequestBytes.replace SlotDeriveRuntime.FIXTURE_FEDERATION_HEX
      (String.toUpper SlotDeriveRuntime.FIXTURE_FEDERATION_HEX)) = "")

/-- (Pinned `= true` in `SignalFeedbackRuntimeFixtures`.) -/
def check_fixture_wrong_format_refused : Bool :=
  decide (signalFeedbackFFI
    (fixtureRequestBytes.replace INPUT_FORMAT "POA-SIGNAL-FEEDBACK-2") = "")

/-- An out-of-range band is refused rather than reduced modulo six — a wrapped band
would be a second spelling of a legal guess and would hand the player a free round.
(Pinned `= true` in `SignalFeedbackRuntimeFixtures`.) -/
def check_fixture_out_of_range_band_refused : Bool :=
  decide (signalFeedbackFFI (fixtureRequestBytes.replace "\"high\":2}}" "\"high\":6}}") = "")

/-- Key ORDER is pinned by the seal, not merely key membership. -/
def transposedRequestBytes : String :=
  "{\"format\":" ++ jsonString INPUT_FORMAT ++
    ",\"secret\":" ++ jsonString SlotDeriveRuntime.FIXTURE_SECRET_HEX ++
    ",\"slot\":9" ++
    ",\"mission_id\":1,\"epoch\":1" ++
    ",\"federation_id\":" ++ jsonString SlotDeriveRuntime.FIXTURE_FEDERATION_HEX ++
    ",\"content_session\":" ++ jsonString SlotDeriveRuntime.FIXTURE_SESSION_HEX ++
    ",\"player_key\":" ++ jsonString SlotDeriveRuntime.FIXTURE_PLAYER_HEX ++
    ",\"commitment\":" ++ jsonString (Emit.bytes32Hex fixtureCommitment) ++
    ",\"guess\":{\"low\":0,\"mid\":1,\"high\":2}}"

/-- (Pinned `= true` in `SignalFeedbackRuntimeFixtures`.) -/
def check_fixture_transposed_keys_refused : Bool :=
  decide (signalFeedbackFFI transposedRequestBytes = "")

#assert_axioms decodeRequest_reencodes
#assert_axioms decodeRequest_accepted_bytes_injective
#assert_axioms decodeRequest_refuses_oversized
#assert_axioms signalFeedbackFFI_refuses_uncanonical
#assert_axioms signalFeedbackFFI_refuses_an_unopened_commitment
#assert_axioms classify_is_the_triangulation_rule
#assert_axioms request_derives_the_judged_instance
#assert_axioms judged_run_seed_is_the_judged_draw
#assert_axioms judged_target_is_from_the_judged_run_seed
#assert_axioms reply_bytes_are_a_function_of_the_feedback_alone
#assert_axioms served_transcript_cannot_separate_feedback_equivalent_targets
#assert_axioms reply_reports_solved_iff_the_guess_is_the_target
#assert_axioms served_counts_are_bounded

-- The twenty fixture pins (`native_decide` + `#assert_compiled`) live in
-- `SignalFeedbackRuntimeFixtures.lean`, rooted in `PathOfAngelsGuards` — see the
-- concrete-requests header above.

end Dregg2.Games.PathOfAngels.SignalFeedbackRuntime
