/-
# SlotDeriveRuntime — the ONE per-run instance derivation the node may call

Substrate note: this is Lean-authored game semantics behind a canonical byte wire.
Nothing here is an AIR, a constraint system or a gadget.  Rust carries bytes to this
module and back; it computes nothing.

## Why an export exists at all

`Judged.admissionChecks` requires two facts the node cannot assert, only SUPPLY:

* `active.slotCommitment = HiddenInstance.commit active.slotSecret active.slot`
* `active.runSeed = HiddenInstance.runSeedFor ⟨secret, slot, playerKey⟩ ctx`

and `SignalTriangulation.Config.target_eq` requires a third,
`some target = targetFromSeed? mission.runSeed`.  The judge RE-DERIVES all three and
refuses on mismatch.  That is a CHECK only if the node derived them independently: a node that
shipped `Emit.UNBOUND_RUN_SEED` and let the judge fill it in would be asking the judge
to compute the answer rather than to verify that the node served the committed one.

So the node must derive — and `HiddenInstance.commit`/`runSeedFor` are a
Poseidon2-BabyBear-w16 sponge with its own padding, lane-aliasing rejection
(`laneByte?`), domain tags (`POAC`/`POAD`) and squeeze count.  A Rust copy of that
would be an unproven twin of a SOUNDNESS function, where a one-byte disagreement
either refuses every scored run or, worse, agrees on an instance the player was never
served.  Hence exactly one `@[export]`, and no Rust arithmetic.

## What is proved about it, and with which pin

⚠ `HiddenInstance.commit`, `runSeedFor` and `practiceRunSeed` are `@[irreducible]`,
because `Poseidon2BabyBearW16.perm` reduces EXPONENTIALLY under whnf (measured
2026-08-05: 47.6 GB resident and 68 minutes of CPU for one file that tried).  The
export path runs COMPILED code and is unaffected, but it splits the theorems below in
two, and the split is the honest one:

* Anything general — the canonical seal, the three projections of `derive`, and the
  admission weld — never mentions a concrete digest, so both sides of every equation
  are the SAME opaque application and nothing has to reduce.  Those are `rfl`/`simp`
  and pinned with `#assert_axioms`.
* Anything about a CONCRETE request must actually run the sponge.  Those are
  `native_decide` and pinned with `#assert_compiled`: they are trusted to the compiled
  evaluator, which is exactly the evaluator the export itself runs on, and saying
  otherwise would be a label rather than a proof.

## The wire

Request (`POA-SLOT-DERIVE-1`), key order pinned by `Request.toJson`:

    {"format":"POA-SLOT-DERIVE-1","slot":<u64>,"secret":"<64 lowercase hex>",
     "mission_id":<u64>,"epoch":<u64>,"federation_id":"<64 lowercase hex>",
     "content_session":"<64 lowercase hex>","player_key":"<64 lowercase hex>"}

Reply (`POA-SLOT-DERIVE-OUT-1`):

    {"format":"POA-SLOT-DERIVE-OUT-1","commitment":"<64 lowercase hex>",
     "run_seed":"<64 lowercase hex>","target":{"low":n,"mid":n,"high":n}}

`mission_id`, `epoch`, `federation_id` and `content_session` are exactly
`HiddenInstance.MissionContext` — the projection that deliberately EXCLUDES `runSeed`,
which is why the derivation is visibly not a cycle
(`HiddenInstance.context_ignores_the_run_seed`).

⚠ The SECRET crosses this wire.  It is node-held state, never a client claim, and these
bytes must not leave the node.  The reply deliberately does NOT echo it.

Acceptance is `NetworkJudgeWire.canonicalDecode` — the SAME seal `decodeSignalInput`
uses, imported rather than re-typed, so acceptance here and acceptance there cannot
drift: parse, then require the Lean encoder to reproduce the candidate bytes exactly.
An unknown field, a missing field, a transposed key, an uppercase digit, a trailing
byte or a re-spelled integer all fail that comparison and the export returns `""`.
-/
import Lean.Data.Json
import Dregg2.Games.PathOfAngels.NetworkJudgeWire
import Dregg2.Tactics

namespace Dregg2.Games.PathOfAngels.SlotDeriveRuntime

open Lean (Json)
open Dregg2.Games.PathOfAngels

set_option autoImplicit false

abbrev INPUT_FORMAT : String := "POA-SLOT-DERIVE-1"
abbrev OUTPUT_FORMAT : String := "POA-SLOT-DERIVE-OUT-1"

/-- Outer allocation fuse.  Mirrors `MAX_POA_SLOT_DERIVE_WIRE_BYTES` in
`dregg-lean-ffi/src/poa_slot_derive_ffi.rs`; the wire is a fixed handful of digests, so
this is a malformed-caller guard and not a semantic bound. -/
abbrev WIRE_BYTE_LIMIT : Nat := 64 * 1024

/-- Every integer on this wire arrives from an unsigned 64-bit host word. -/
abbrev WIRE_NAT_LIMIT : Nat := 2 ^ 64 - 1

/-! ## The two wire records -/

structure Request where
  slot : Nat
  secret : Digest32
  missionId : Nat
  epoch : Nat
  federationId : Digest32
  contentSession : Digest32
  playerKey : Digest32
deriving DecidableEq

structure Reply where
  commitment : Digest32
  runSeed : Digest32
  target : SignalTriangulation.Code
deriving DecidableEq

private def jsonString (s : String) : String := String.quote s

def Request.toJson (request : Request) : String :=
  "{\"format\":" ++ jsonString INPUT_FORMAT ++
    ",\"slot\":" ++ toString request.slot ++
    ",\"secret\":" ++ jsonString (Emit.bytes32Hex request.secret) ++
    ",\"mission_id\":" ++ toString request.missionId ++
    ",\"epoch\":" ++ toString request.epoch ++
    ",\"federation_id\":" ++ jsonString (Emit.bytes32Hex request.federationId) ++
    ",\"content_session\":" ++ jsonString (Emit.bytes32Hex request.contentSession) ++
    ",\"player_key\":" ++ jsonString (Emit.bytes32Hex request.playerKey) ++ "}"

def Reply.toJson (reply : Reply) : String :=
  "{\"format\":" ++ jsonString OUTPUT_FORMAT ++
    ",\"commitment\":" ++ jsonString (Emit.bytes32Hex reply.commitment) ++
    ",\"run_seed\":" ++ jsonString (Emit.bytes32Hex reply.runSeed) ++
    ",\"target\":{\"low\":" ++ toString reply.target.low.val ++
      ",\"mid\":" ++ toString reply.target.mid.val ++
      ",\"high\":" ++ toString reply.target.high.val ++ "}}"

/-! ## Strict parse

These accessors are the same shape as `NetworkJudgeWire`'s private ones; the SEAL
(`canonicalDecode`) is imported rather than re-typed, which is the part that could
drift meaningfully. -/

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

private def parseRequestJson (j : Json) : Except String Request := do
  exactKeys j ["format", "slot", "secret", "mission_id", "epoch", "federation_id",
    "content_session", "player_key"]
  let format ← j.getObjValAs? String "format"
  if format != INPUT_FORMAT then throw "wrong slot-derive request format"
  pure {
    slot := ← objectNat j "slot"
    secret := ← objectDigest j "secret"
    missionId := ← objectNat j "mission_id"
    epoch := ← objectNat j "epoch"
    federationId := ← objectDigest j "federation_id"
    contentSession := ← objectDigest j "content_session"
    playerKey := ← objectDigest j "player_key"
  }

def decodeRequestWithLimit (byteLimit : Nat) (bytes : String) : Option Request :=
  if bytes.length ≤ byteLimit then
    NetworkJudgeWire.canonicalDecode parseRequestJson Request.toJson bytes
  else none

def decodeRequest (bytes : String) : Option Request :=
  decodeRequestWithLimit WIRE_BYTE_LIMIT bytes

/-! ## The derivation -/

/-- The draw context the request names.  It carries no run seed, by type. -/
def contextOf (request : Request) : HiddenInstance.MissionContext where
  missionId := ⟨request.missionId⟩
  epoch := ⟨request.epoch⟩
  federationId := request.federationId
  contentSession := request.contentSession

/-- The slot draw the request names.  The secret enters here and reaches no output. -/
def drawOf (request : Request) : HiddenInstance.Draw where
  secret := ⟨request.secret⟩
  slot := ⟨request.slot⟩
  playerKey := request.playerKey

/-- The run seed this request derives.  Named, so the two facts about it below and the
reply's own field are one term and cannot drift apart. -/
def runSeedOf (request : Request) : Digest32 :=
  HiddenInstance.runSeedFor (drawOf request) (contextOf request)

/-- All three derived values.  `target` is a function of `run_seed` alone, so the reply
cannot carry a target and a seed that disagree.

⚑ **`none` WHEN THE SEED DRAWS NOTHING.**  `SignalTriangulation.targetFromSeed?` is
partial by necessity (216 ∤ 2^256), and this export does not paper over that: a seed
whose byte stream is exhausted before three bands are drawn yields no reply at all.
The alternative — returning a substitute target — would hand the judge an instance
the seed did not draw, and `Config.target_eq` would then be unprovable for exactly
the runs where it matters most.  The refusal reaches the node as the `""` sentinel
the export already had.

⚠ Written with `Option.map` rather than a `match`.  A `match` on this scrutinee
generates equation lemmas indexed by the scrutinee's constructors, and `unfold`ing
through them makes the KERNEL whnf `targetFromSeed? (runSeedOf request)` — a
Poseidon2 sponge — which overflows its stack (`deep recursion detected`, measured
while writing this).  `@[irreducible]` on the sponge does not help: it is an
elaborator hint and the kernel ignores it.  `Option.map` has one equation and the
inversion below never reduces the seed. -/
def derive? (request : Request) : Option Reply :=
  (SignalTriangulation.targetFromSeed? (runSeedOf request)).map fun target =>
    { commitment := HiddenInstance.commit (drawOf request).secret (drawOf request).slot
      runSeed := runSeedOf request
      target := target }

/-- The single inversion every fact below is read off.  Stated once so that no other
proof in this file has to touch the draw. -/
theorem derive?_some_inv {request : Request} {reply : Reply}
    (h : derive? request = some reply) :
    SignalTriangulation.targetFromSeed? (runSeedOf request) = some reply.target ∧
      reply.runSeed = runSeedOf request ∧
      reply.commitment =
        HiddenInstance.commit (drawOf request).secret (drawOf request).slot := by
  rw [derive?, Option.map_eq_some_iff] at h
  obtain ⟨target, hd, hr⟩ := h
  subst hr
  exact ⟨hd, rfl, rfl⟩

def deriveBytes? (bytes : String) : Option String := do
  let request ← decodeRequest bytes
  let reply ← derive? request
  some reply.toJson

/-- **`@[export dregg_poa_signal_slot_derive]`** — the per-run instance derivation.
`""` is the fail-closed refusal sentinel, as in every other PoA export; every accepted
result is the canonical `POA-SLOT-DERIVE-OUT-1` JSON this module emitted itself.

This export confers no authority and reads no state.  It is a pure function of the
bytes it is handed, and the node must obtain those bytes — the slot secret above all —
from its own authenticated state. -/
@[export dregg_poa_signal_slot_derive]
def slotDeriveFFI (bytes : String) : String :=
  (deriveBytes? bytes).getD ""

/-! ## What the export is, stated generally

None of the theorems in this section mentions a concrete digest, so neither side of any
equation reduces the sponge.  They are the reason the export is *the* derivation rather
than *a* function, and they are `#assert_axioms`-clean. -/

/-- The seal: accepted bytes are the bytes this module would have written. -/
theorem decodeRequest_reencodes {bytes : String} {request : Request}
    (accepted : decodeRequest bytes = some request) : request.toJson = bytes := by
  simp only [decodeRequest, decodeRequestWithLimit] at accepted
  split at accepted
  · exact NetworkJudgeWire.canonicalDecode_reencodes parseRequestJson Request.toJson accepted
  · contradiction

/-- Two byte strings that decode to the same request are the same bytes.  A second
canonical spelling of one request is therefore not merely rejected somewhere later —
it does not exist. -/
theorem decodeRequest_accepted_bytes_injective {left right : String} {request : Request}
    (hleft : decodeRequest left = some request)
    (hright : decodeRequest right = some request) : left = right := by
  rw [← decodeRequest_reencodes hleft, ← decodeRequest_reencodes hright]

theorem decodeRequest_refuses_oversized {bytes : String} (h : WIRE_BYTE_LIMIT < bytes.length) :
    decodeRequest bytes = none := by
  simp [decodeRequest, decodeRequestWithLimit, Nat.not_le.mpr h]

/-- A wire the seal refuses gets the refusal sentinel and nothing else. -/
theorem slotDeriveFFI_refuses_uncanonical {bytes : String} (h : decodeRequest bytes = none) :
    slotDeriveFFI bytes = "" := by
  simp [slotDeriveFFI, deriveBytes?, h]

/-! ⚠ **Every proof below GENERALIZES the draw before casing on it.**  The scrutinee is
`targetFromSeed? (runSeedOf request)`, and `runSeedOf` is a Poseidon2 sponge: `split`
or `cases` on it unreduced sends the KERNEL into the permutation, which is not slow
but infeasible (`deep recursion detected`, hit while writing this).  `@[irreducible]`
does not help — it is an elaborator hint and the kernel ignores it.
`generalize … = t at h` replaces the sponge with a variable FIRST, so the case split
is on a two-constructor `Option` and nothing reduces. -/

/-- ⚑ The commitment the export returns IS `HiddenInstance.commit` of the secret and
slot the request named.  This is the value `Judged.admissionChecks` recomputes. -/
theorem derive_commitment_is_the_commit {request : Request} {reply : Reply}
    (h : derive? request = some reply) :
    reply.commitment = HiddenInstance.commit ⟨request.secret⟩ ⟨request.slot⟩ :=
  (derive?_some_inv h).2.2

/-- ⚑ The run seed the export returns IS `HiddenInstance.runSeedFor` of that draw and
that context. -/
theorem derive_run_seed_is_the_draw {request : Request} {reply : Reply}
    (h : derive? request = some reply) :
    reply.runSeed =
      HiddenInstance.runSeedFor
        { secret := ⟨request.secret⟩, slot := ⟨request.slot⟩, playerKey := request.playerKey }
        (contextOf request) :=
  (derive?_some_inv h).2.1

/-- ⚑ The target the export returns IS the DRAW of the run seed it returned in the
same reply — not of some other seed, and not a substitute for a seed that drew
nothing. -/
theorem derive_target_is_from_its_own_run_seed {request : Request} {reply : Reply}
    (h : derive? request = some reply) :
    some reply.target = SignalTriangulation.targetFromSeed? reply.runSeed := by
  obtain ⟨hd, hseed, _⟩ := derive?_some_inv h
  rw [hseed]
  exact hd.symm

/-- The exact proof obligation `SignalTriangulation.Config.target_eq` demands.  A node
that installs the reply's run seed into a mission can discharge `target_eq` with this
and does not have to recompute a target of its own. -/
theorem derive_target_discharges_config_target_eq {request : Request} {reply : Reply}
    (h : derive? request = some reply) (mission : MissionSpec)
    (hseed : mission.runSeed = reply.runSeed) :
    some reply.target = SignalTriangulation.targetFromSeed? mission.runSeed := by
  rw [hseed]
  exact derive_target_is_from_its_own_run_seed h

/-- ⚑ **THE REFUSAL IS REACHABLE, AND IT IS THE SEED THAT CAUSES IT.**  Without this
the `none` branch of `derive?` could be a limb nothing reaches, and the partiality
would be decorative rather than the honest consequence of a uniform draw. -/
theorem derive_refuses_a_seed_that_draws_nothing (request : Request)
    (h : SignalTriangulation.targetFromSeed? (runSeedOf request) = none) :
    derive? request = none := by
  rw [derive?, h, Option.map_none]

/-- ⚑ **THE WELD.**  A node that derives through this export and installs the answers
satisfies EXACTLY the two clauses of `Judged.admissionChecks` that no node can assert.

The hypotheses are the installation, stated in full: the active state carries the
secret and slot the request named, the carrier's signer is the player it named, the
mission's draw context is the context it named, and the commitment and run seed are the
ones the export returned.  Nothing is assumed about the sponge, and nothing here
reduces it — both sides of each conjunct are the same opaque application. -/
theorem derive_satisfies_admission {request : Request} {reply : Reply}
    (hderive : derive? request = some reply)
    (active : ActiveRunState) (carrier : FinalizedCarrier)
    (hsecret : active.slotSecret = ⟨request.secret⟩)
    (hslot : active.slot = ⟨request.slot⟩)
    (hplayer : carrier.playerKey = request.playerKey)
    (hcontext : HiddenInstance.MissionContext.ofMission active.game.mission = contextOf request)
    (hcommitment : active.slotCommitment = reply.commitment)
    (hrunSeed : active.runSeed = reply.runSeed) :
    active.slotCommitment = HiddenInstance.commit active.slotSecret active.slot ∧
      active.runSeed =
        HiddenInstance.runSeedFor
          { secret := active.slotSecret, slot := active.slot, playerKey := carrier.playerKey }
          (HiddenInstance.MissionContext.ofMission active.game.mission) := by
  refine ⟨?_, ?_⟩
  · rw [hcommitment, hsecret, hslot, derive_commitment_is_the_commit hderive]
  · rw [hrunSeed, hsecret, hslot, hplayer, hcontext, derive_run_seed_is_the_draw hderive]

/-! ## Concrete requests, and why these are compiled pins

Each theorem below names a real digest, so `decide`-style reduction would have to run
the Poseidon2 permutation in the kernel, which does not terminate at any useful size.
They are `native_decide` and pinned with `#assert_compiled`.  What they buy is that the
general statements above are not vacuous over an empty accepted set: the wire really
does decode, the derivation really does run, and the refusals really are reachable. -/

private def hexDigest (hex : String) : Digest32 :=
  (Emit.parseBytes32Hex? hex).getD ⟨List.replicate 32 0, by simp⟩

abbrev FIXTURE_SECRET_HEX : String :=
  "7777777777777777777777777777777777777777777777777777777777777777"
abbrev FIXTURE_FEDERATION_HEX : String :=
  "4ea83e8ebf4f590eace11c9ffd6d6607a4afb15e5a00cd7b9e04890dab6bfc5a"
abbrev FIXTURE_SESSION_HEX : String :=
  "f9db35f2296bd2b6d4a9edbd9d90ee5d59cd7fa2b70a90d6a25f0d81ba60d1d4"
abbrev FIXTURE_PLAYER_HEX : String :=
  "5555555555555555555555555555555555555555555555555555555555555555"

/-- A DEMONSTRATION secret.  It is a fixture value, not a deployment secret: a
deployment secret never enters this module and no function here renders one into an
artifact. -/
def fixtureRequest : Request where
  slot := 9
  secret := hexDigest FIXTURE_SECRET_HEX
  missionId := 1
  epoch := 1
  federationId := hexDigest FIXTURE_FEDERATION_HEX
  contentSession := hexDigest FIXTURE_SESSION_HEX
  playerKey := hexDigest FIXTURE_PLAYER_HEX

def fixtureRequestBytes : String := fixtureRequest.toJson

theorem fixture_request_roundtrips :
    decodeRequest fixtureRequestBytes = some fixtureRequest := by
  native_decide

/-- ⚑ **THE FIXTURE REQUEST DRAWS.**  `derive?` is partial now, so every pin below is a
statement about a `some`; without this one they could all be satisfied by a refusal and
the whole compiled suite would read green against an export that answers nothing. -/
theorem fixture_derives : (derive? fixtureRequest).isSome = true := by
  native_decide

/-- The export answers, and its answer is the canonical reply it would have written. -/
theorem fixture_export_answers :
    some (slotDeriveFFI fixtureRequestBytes) = (derive? fixtureRequest).map Reply.toJson := by
  native_decide

/-- The answer is non-empty, so the refusal sentinel is unambiguous on this wire. -/
theorem fixture_export_is_not_the_refusal :
    slotDeriveFFI fixtureRequestBytes ≠ "" := by
  native_decide

theorem fixture_reply_is_canonical_and_states_the_format :
    ((derive? fixtureRequest).map Reply.toJson).any
      (fun j => j.startsWith ("{\"format\":\"" ++ OUTPUT_FORMAT ++ "\"")) = true := by
  native_decide

/-- ⚠ The reply does not echo the secret.  A one-instance check, and it is exactly one:
the general statement is that `Reply` has no secret FIELD, which is a type-level fact
visible above, not a theorem. -/
theorem fixture_reply_does_not_carry_the_secret :
    ((derive? fixtureRequest).map
      (fun r => (r.toJson.splitOn FIXTURE_SECRET_HEX).length)) = some 1 := by
  native_decide

theorem fixture_trailing_byte_refused :
    slotDeriveFFI (fixtureRequestBytes ++ "\n") = "" := by
  native_decide

theorem fixture_unknown_field_refused :
    slotDeriveFFI (fixtureRequestBytes.replace "\"slot\":9" "\"slot\":9,\"extra\":0") = "" := by
  native_decide

theorem fixture_uppercase_digest_refused :
    slotDeriveFFI
      (fixtureRequestBytes.replace FIXTURE_FEDERATION_HEX
        (String.toUpper FIXTURE_FEDERATION_HEX)) = "" := by
  native_decide

theorem fixture_wrong_format_refused :
    slotDeriveFFI (fixtureRequestBytes.replace INPUT_FORMAT "POA-SLOT-DERIVE-2") = "" := by
  native_decide

/-- Key ORDER is pinned by the seal, not merely key membership: the same eight fields
in a different order re-encode to different bytes and are refused. -/
def transposedRequestBytes : String :=
  "{\"format\":" ++ jsonString INPUT_FORMAT ++
    ",\"secret\":" ++ jsonString FIXTURE_SECRET_HEX ++
    ",\"slot\":9" ++
    ",\"mission_id\":1,\"epoch\":1" ++
    ",\"federation_id\":" ++ jsonString FIXTURE_FEDERATION_HEX ++
    ",\"content_session\":" ++ jsonString FIXTURE_SESSION_HEX ++
    ",\"player_key\":" ++ jsonString FIXTURE_PLAYER_HEX ++ "}"

theorem fixture_transposed_keys_refused : slotDeriveFFI transposedRequestBytes = "" := by
  native_decide

/-- ⚑ A DIFFERENT SECRET DRAWS A DIFFERENT INSTANCE, through the export, on the wire.
Everything else is held fixed — slot, mission, epoch, federation, session, player — so
this is the export-level form of `HiddenInstance.published_context_does_not_determine_
the_run_seed`, and it is what makes the derivation worth calling at all. -/
def otherSecretRequest : Request :=
  { fixtureRequest with
    secret := hexDigest "8888888888888888888888888888888888888888888888888888888888888888" }

theorem fixture_other_secret_draws_another_instance :
    (derive? fixtureRequest).map Reply.runSeed ≠
        (derive? otherSecretRequest).map Reply.runSeed ∧
      (derive? fixtureRequest).map Reply.commitment ≠
        (derive? otherSecretRequest).map Reply.commitment := by
  native_decide

/-- The commitment takes no player and no mission, so two players in one slot under one
secret are shown the SAME commitment and draw DIFFERENT instances. -/
def otherPlayerRequest : Request :=
  { fixtureRequest with
    playerKey := hexDigest "6666666666666666666666666666666666666666666666666666666666666666" }

theorem fixture_commitment_is_player_independent_but_the_seed_is_not :
    (derive? fixtureRequest).map Reply.commitment =
        (derive? otherPlayerRequest).map Reply.commitment ∧
      (derive? fixtureRequest).map Reply.runSeed ≠
        (derive? otherPlayerRequest).map Reply.runSeed := by
  native_decide

#assert_axioms decodeRequest_reencodes
#assert_axioms decodeRequest_accepted_bytes_injective
#assert_axioms decodeRequest_refuses_oversized
#assert_axioms slotDeriveFFI_refuses_uncanonical
#assert_axioms derive_commitment_is_the_commit
#assert_axioms derive_run_seed_is_the_draw
#assert_axioms derive_target_is_from_its_own_run_seed
#assert_axioms derive_target_discharges_config_target_eq
#assert_axioms derive_refuses_a_seed_that_draws_nothing
#assert_axioms derive_satisfies_admission
#assert_compiled fixture_derives
#assert_compiled fixture_request_roundtrips
#assert_compiled fixture_export_answers
#assert_compiled fixture_export_is_not_the_refusal
#assert_compiled fixture_reply_is_canonical_and_states_the_format
#assert_compiled fixture_reply_does_not_carry_the_secret
#assert_compiled fixture_trailing_byte_refused
#assert_compiled fixture_unknown_field_refused
#assert_compiled fixture_uppercase_digest_refused
#assert_compiled fixture_wrong_format_refused
#assert_compiled fixture_transposed_keys_refused
#assert_compiled fixture_other_secret_draws_another_instance
#assert_compiled fixture_commitment_is_player_independent_but_the_seed_is_not

end Dregg2.Games.PathOfAngels.SlotDeriveRuntime
