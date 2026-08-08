/-
# HiddenInstance — the instance a descriptor commits to but does not carry

Substrate note: this is Lean-authored game semantics.  Nothing here is an AIR, a
constraint system or a gadget.  Rust and TypeScript dispatch what this module and
`Emit` produce; they do not carry a second copy of the derivation.

## The wound this module closes

Every shipped POAG1 descriptor stated its own answer.  `signal-triangulation.json`
carried `"target":[2,4,1]` as a top-level field.  `salvage-lock.json` carried the
glyph under each plate in `glyph_id`, and — unavoidably, in a tabulated machine —
in the successors of its transition table.  `relay-repair.json` carried
`instance.selected`.  The execution floor of Signal as emitted was ONE guess
against an information floor of four, and a Salvage run needed six exposures
against the ten a genuinely hidden board costs.

Deleting those fields alone would have closed NOTHING, and it is worth being
exact about why, because it is the trap this module exists to avoid.  Each game
derived its instance from `MissionSpec.runSeed`, and the run seed was published
in the descriptor AND in the catalog.  A client that reads `run_seed` and runs
`targetFromSeed` gets `[2,4,1]` whether or not the JSON spells it out.  Removing
the field would have silenced the gate that reported the hole while leaving the
hole exactly where it was.

So the run seed itself has to stop being a published constant.

## The split

* The descriptor publishes the RULES — the complete oracle, over the whole
  instance family — and a per-slot COMMITMENT.  It publishes no instance and no
  value from which one can be computed.
* The live `MissionSpec.runSeed` a judge uses is DERIVED, at judge time, from
  `(slot secret, slot, mission, player)`.  The curator draws the slot secret
  off-line, commits to it before the slot opens, and opens it after the slot
  closes.  The game kernels are untouched: they still bind their instance to
  `mission.runSeed` (`Config.target_eq`, `Config.seed_eq`, `Config.board_eq`),
  and that seed is now a per-run value nobody can predict.
* A browser plays PRACTICE against an instance it draws for ITSELF, under a
  client-chosen seed and the `practice` domain tag.  A practice stream is not a
  judged stream for any input, so a practice transcript can never be a judged
  one.

## What this is and is not

BINDING is what the commitment buys, and it is the property that makes a score
mean something between players: a curator cannot look at a transcript and then
choose the instance it was played against.  The strength of that binding is the
sponge capacity — eight lanes, about 248 bits, so roughly 2^124 for a collision.
That is the number, not the 2^248 of the output width.

HIDING from the OPERATOR is NOT bought and is not claimed.  Whoever holds the
slot secret knows every player's instance for that slot, in advance.  That is a
real residual and it is UNDONE WORK, not a theorem of the model: removing it
needs a beacon nobody can predict — a threshold or delay construction — feeding
the slot secret instead of a curator draw.  This module is written so that swap
is a change of where `SlotSecret` comes from and nothing else.

UNIFORMITY of the derived instance rests on the Poseidon2 permutation behaving
as a PRF.  That is an assumption, not a theorem, and no theorem below claims it.
What IS discharged here is the arithmetic that would otherwise sit UNDER that
assumption and quietly spoil it: the lane-to-byte projection rejects the one
value that would give byte 0 an extra preimage (`P = 256 * LANE_FIBRE + 1`), so
the byte stream `SeedDraw` consumes is exactly uniform GIVEN uniform lanes, and
`SeedDraw.draw_is_uniform_on_every_bound` carries it from there.  A counting
theorem over the 2^31 lane domain is deliberately absent: it would be a proof
about the inside of an assumption we cannot discharge, and its presence would
read as more assurance than exists.

## Hard facts respected

`Poseidon2BabyBearW16.perm` has NO length guard: over sixteen lanes it silently
TRUNCATES and under sixteen it zero-fills.  `permute` therefore pads its argument
to exactly sixteen before every call and pads the result back, so no call site
can hand it a concatenation of digests.  Absorption is a rate-8 / capacity-8
sponge over 8-lane blocks, one byte per lane, and `digestBlocks` writes its four
slices out rather than recursing, so there is no chunking function whose
termination could drift.

`SeedDraw.drawBelow?` is the only draw used IN THIS MODULE.  `SalvageCrate.
unbiasedIndex?` cannot stream — `find?` then modulo re-reads the same byte — and
nothing here calls it.

⚠ **CORRECTED 2026-08-07 — the sentence above used to have no qualifier, and it
was FALSE of the pipeline it appeared to describe.**  A consumer draws its own
instance out of the seed this module hands it, and one of them does not use
`SeedDraw`: `SignalTriangulation.targetFromSeed` folds three of these bytes with
`% 6`.  `256 = 42*6 + 4`, so the four low band symbols come back 43/256 against
42/256 — a 1.073x spread across the 216 targets, 0.0070 in total variation from
uniform.  The lane-to-byte projection above rejects ONE value to keep the byte
stream uniform and the very next hop folds FOUR back in.  Measured, WARNed by
`scripts/poa-design-gate.py` as `signal-triangulation/seed-modulo-bias`, and NOT
yet repaired — the repair is `targetFromSeed? : Digest32 → Option Code`, which is
a flag day through Signal's fixture layer.  `BlackBoxReconstruction` and
`VentCrawl` do go through `SeedDraw`; Signal is the one that does not.

The lesson for this docblock: a claim about what "is used" reaches past the module
it is written in, and nobody re-checks it when a consumer is added.

## ⚑ `commit`, `runSeedFor` and `practiceRunSeed` are `@[irreducible]`, and why

MEASURED 2026-08-05, on hbox: `BazaarGameExamples` carried
`archived := by simp [archive, acquire]`, whose goal reaches `judgeActive` and therefore
`admissionChecks`, which mentions both functions.  With a run seed that was a literal
digest that `simp` was cheap.  With a DERIVED one it dragged seventeen Poseidon2
permutations through Lean's INTERPRETER: **47.6 GB resident and 68 minutes of CPU on one
file**, climbing into the 48 GB cgroup cap.

That is a property of the whole design, not of that one proof: every future `simp`,
`rfl` or `decide` that happens to reach a live seed would do the same, and it would look
like a slow build rather than a mistake.  `@[irreducible]` makes the elaborator treat a
draw as opaque — which is what it is, a sponge output — while `native_decide`, `#eval`
and the compiled export evaluate it exactly as before, because irreducibility is an
elaborator notion and the compiler ignores it.  ⚠ The KERNEL also ignores it, so a plain
`by decide` over a live seed is still a bomb; there is none in the tree and there should
never be one.
-/
import Dregg2.Games.PathOfAngels.Core
import Dregg2.Games.PathOfAngels.SeedDraw
import Dregg2.Circuit.Poseidon2BabyBearW16
import Dregg2.Tactics

namespace Dregg2.Games.PathOfAngels.HiddenInstance

open Dregg2.Games.PathOfAngels
open Dregg2.Circuit.Poseidon2BabyBearW16

set_option autoImplicit false

/-! ## Fixed-width lane plumbing

Every list handed to `perm` is exactly `W` long by construction, never by a
comment. -/

/-- Permutation width.  `perm` truncates above it and zero-fills below it. -/
abbrev W : Nat := 16

/-- Sponge rate.  The remaining `W - RATE` lanes are the capacity and are never
written by an absorbed block or read by a squeeze. -/
abbrev RATE : Nat := 8

/-- Truncate or zero-fill to exactly `n` lanes.  Total, and its length is a
theorem rather than an invariant a caller has to maintain. -/
def pad (n : Nat) (xs : List Nat) : List Nat := (xs ++ List.replicate n 0).take n

theorem pad_length (n : Nat) (xs : List Nat) : (pad n xs).length = n := by
  simp only [pad, List.length_take, List.length_append, List.length_replicate]
  omega

/-- The permutation, with the width obligation discharged on both sides.  This is
the ONLY call site of `perm` in this module. -/
def permute (xs : List Nat) : List Nat := pad W (perm (pad W xs))

theorem permute_length (xs : List Nat) : (permute xs).length = W := pad_length W _

/-- Lane addition in the deployed field. -/
def addLane (a b : Nat) : Nat := (a + b) % P

/-- Absorb one rate block: add it into the first `RATE` lanes and permute.  The
capacity lanes are untouched by the block, which is what a rate-8 / capacity-8
sponge means. -/
def absorbBlock (state block : List Nat) : List Nat :=
  let s := pad W state
  permute (List.zipWith addLane (s.take RATE) (pad RATE block) ++ s.drop RATE)

def absorbAll (state : List Nat) : List (List Nat) → List Nat
  | [] => state
  | block :: rest => absorbAll (absorbBlock state block) rest

/-- Squeeze `blocks` rate blocks, permuting between them.  Only the rate lanes
are ever read. -/
def squeeze (state : List Nat) : Nat → List Nat
  | 0 => []
  | n + 1 => (pad W state).take RATE ++ squeeze (permute state) n

def initialState : List Nat := List.replicate W 0

theorem initialState_length : initialState.length = W := by
  simp [initialState]

/-! ## Lane to byte, with the aliasing class rejected

`P = 2013265921 = 256 * 7864320 + 1`.  Folding a whole lane with `% 256` would
therefore hand residue 0 one extra preimage.  The extra value is DISCARDED
instead, exactly as `SeedDraw` discards its incomplete high block, so the byte
stream the draws consume is uniform given uniform lanes. -/

/-- `P - 1`: the largest whole number of byte classes below the field size. -/
abbrev LANE_ACCEPT : Nat := 2013265920

/-- How many accepted lane values land on each byte. -/
abbrev LANE_FIBRE : Nat := 7864320

theorem lane_accept_is_whole_byte_classes : LANE_ACCEPT = 256 * LANE_FIBRE := by
  decide

theorem lane_accept_is_the_field_minus_one : LANE_ACCEPT + 1 = P := by
  decide

/-- One byte per accepted lane; the single aliasing value refuses rather than
folding.  `none` is not a failure mode a caller has to handle specially — the
stream simply carries one byte fewer, and every remaining byte is still uniform. -/
def laneByte? (v : Nat) : Option (Fin 256) :=
  if v < LANE_ACCEPT then some ⟨v % 256, Nat.mod_lt _ (by omega)⟩ else none

def laneBytes (lanes : List Nat) : List (Fin 256) := lanes.filterMap laneByte?

theorem laneByte_accepts_below_the_whole_classes (v : Nat) (h : v < LANE_ACCEPT) :
    laneByte? v = some ⟨v % 256, Nat.mod_lt _ (by omega)⟩ := by
  simp [laneByte?, h]

/-- The one rejection, named.  This is the value whose acceptance would bias
byte 0, and nothing else is rejected. -/
theorem laneByte_rejects_exactly_the_aliasing_value :
    laneByte? LANE_ACCEPT = none ∧ ∀ v : Nat, v < LANE_ACCEPT → (laneByte? v).isSome = true := by
  refine ⟨by simp [laneByte?], ?_⟩
  intro v hv
  simp [laneByte?, hv]

/-! ## Digests in and out of the sponge -/

/-- A 32-byte digest as exactly four eight-lane rate blocks, one byte per lane.
The four slices are written out: there is no chunking recursion whose termination
could drift, and no lane can exceed 255, so no lane is ever non-canonical. -/
def digestBlocks (d : Digest32) : List (List Nat) :=
  let lanes := d.bytes.map (·.val)
  [ pad RATE (lanes.take 8)
  , pad RATE ((lanes.drop 8).take 8)
  , pad RATE ((lanes.drop 16).take 8)
  , pad RATE ((lanes.drop 24).take 8) ]

/-- Exactly 32 bytes from a squeezed stream, zero-filled if a lane was rejected.
Total by construction. -/
def digestOfStream (bs : List (Fin 256)) : Digest32 where
  bytes := (bs ++ List.replicate 32 0).take 32
  length_eq := by
    simp only [List.length_take, List.length_append, List.length_replicate]
    omega

/-! ## Domains

Four-character ASCII tags read big-endian, all below `P`, in the spelling
`DarkBazaar.V1` already uses for its descriptor session. -/

/-- `"POAC"` — the slot commitment. -/
abbrev COMMIT_DOMAIN : Nat := 0x504F4143

/-- `"POAD"` — the per-run instance draw. -/
abbrev DERIVE_DOMAIN : Nat := 0x504F4144

theorem domains_are_distinct_and_canonical :
    COMMIT_DOMAIN ≠ DERIVE_DOMAIN ∧ COMMIT_DOMAIN < P ∧ DERIVE_DOMAIN < P := by
  refine ⟨by decide, by decide, by decide⟩

/-- Which stream a draw is.  The tag enters the sponge preimage, so a practice
instance is not a judged instance for any input: `practice_is_not_judged` is the
concrete refutation, and the judge refuses a practice claim by construction
because it never derives one. -/
inductive Purpose where
  | judged
  | practice
deriving DecidableEq, Repr

def Purpose.tag : Purpose → Nat
  | .judged => 1
  | .practice => 2

theorem Purpose.tags_are_distinct : Purpose.judged.tag ≠ Purpose.practice.tag := by decide

/-! ## The slot secret and its commitment -/

/-- The curator's per-slot secret.  It is drawn off-line, committed to before the
slot opens, and opened after it closes.  `Emit` has NO function that renders it:
the only thing that reaches an artifact is `commit`. -/
structure SlotSecret where
  value : Digest32
deriving DecidableEq

/-- The whole context a live instance is drawn from.  `slot` is the beacon slot,
`playerKey` the run's signer.  A `Draw` is assembled by the node from
authenticated state; nothing in it is client-supplied. -/
structure Draw where
  secret : SlotSecret
  slot : EpochId
  playerKey : Digest32

/-- How many rate blocks the commitment squeezes.  Four would already fill the
32-byte output; six leaves slack for the (roughly 2^-31 per lane) rejections. -/
abbrev SQUEEZE_BLOCKS : Nat := 6

/-- The per-slot commitment published in the descriptor.  It is a function of the
secret and the slot ALONE — it takes no player and no mission — so publishing it
tells a reader nothing about any particular run beyond which slot it belongs to.

Its binding strength is the sponge capacity, eight lanes, about 248 bits: roughly
2^124 to find a colliding secret.  That is the number to quote, not 2^248. -/
@[irreducible] def commit (secret : SlotSecret) (slot : EpochId) : Digest32 :=
  digestOfStream (laneBytes (squeeze
    (absorbAll initialState
      (pad RATE [COMMIT_DOMAIN, slot.value % P, 0, 0, 0, 0, 0, 0]
        :: digestBlocks secret.value))
    SQUEEZE_BLOCKS))

/-! ## The per-run draw

The preimage names every value the run is answerable to: the domain, the purpose,
the slot, the mission and its epoch, the secret, the federation, the content
session, and the player.  Changing any of them changes the instance, and none of
them is reconstructible from the published descriptor without the secret. -/

/-- The part of a mission the draw reads.  ⚠ It deliberately EXCLUDES `runSeed`.

Taking a whole `MissionSpec` would have been a definitional cycle at every
construction site — `runSeed := runSeedFor draw mission` inside the very mission
being defined — and, worse, it would have left the reader unable to see at a
glance that the seed does not depend on itself.  A separate context type makes
that a type-level fact. -/
structure MissionContext where
  missionId : MissionId
  epoch : EpochId
  federationId : Digest32
  contentSession : Digest32
deriving DecidableEq

/-- ⚠ This is NOT `MissionSpec.context` and must not be renamed to it.  `MissionSpec`
lives in `Dregg2.Games.PathOfAngels`; a `MissionSpec.context` declared inside THIS
namespace has the full name `…HiddenInstance.MissionSpec.context`, which generalized
field notation on a `MissionSpec` value cannot resolve, so every `mission.context`
in the tree fails to elaborate.  That exact shape was the hard compile break of the
previous cycle.  One name, spelled out at every call site. -/
def MissionContext.ofMission (mission : MissionSpec) : MissionContext where
  missionId := mission.missionId
  epoch := mission.epoch
  federationId := mission.federationId
  contentSession := mission.contentSession

/-- The context a mission carries does not mention its seed: substituting any run
seed leaves it unchanged.  This is the statement that the derivation is
well-founded, made about the actual projection rather than asserted in prose. -/
theorem context_ignores_the_run_seed (mission : MissionSpec) (seed : Digest32) :
    MissionContext.ofMission { mission with runSeed := seed } =
      MissionContext.ofMission mission := rfl

def headerBlock (purpose : Purpose) (slot : EpochId) (ctx : MissionContext) : List Nat :=
  pad RATE
    [ DERIVE_DOMAIN
    , purpose.tag
    , slot.value % P
    , ctx.missionId.value % P
    , ctx.epoch.value % P
    , 0, 0, 0 ]

/-- The raw byte stream a game draws its instance from. -/
def streamFor (purpose : Purpose) (entropy : Digest32) (slot : EpochId)
    (ctx : MissionContext) (playerKey : Digest32) : List (Fin 256) :=
  laneBytes (squeeze
    (absorbAll initialState
      (headerBlock purpose slot ctx
        :: (digestBlocks entropy
          ++ digestBlocks ctx.federationId
          ++ digestBlocks ctx.contentSession
          ++ digestBlocks playerKey)))
    SQUEEZE_BLOCKS)

/-- **The live run seed.**  This is what a judge puts in `MissionSpec.runSeed`,
and therefore what `SignalTriangulation.Config.target_eq`,
`SalvageLock.Config.seed_eq` and `RelayRepair.Config.board_eq` bind their
instance to.  The kernels did not have to change: what changed is that the seed
they read is no longer a published constant. -/
@[irreducible] def runSeedFor (draw : Draw) (ctx : MissionContext) : Digest32 :=
  digestOfStream (streamFor .judged draw.secret.value draw.slot ctx draw.playerKey)

/-- The rehearsal seed a browser draws for ITSELF.  There is no secret and no
slot: a client picks `clientSeed`, the `practice` tag separates the stream, and
the resulting instance is a real instance of the same family that no judge will
ever score. -/
@[irreducible] def practiceRunSeed (clientSeed : Digest32) (ctx : MissionContext) : Digest32 :=
  digestOfStream (streamFor .practice clientSeed ⟨0⟩ ctx clientSeed)

/-! ## Fixtures

Concrete witnesses, so the claims above are refutable rather than decorative. -/

private def taggedDigest (tag : List Nat) : Digest32 where
  bytes := List.ofFn fun i : Fin 32 =>
    match tag[i.val]? with
    | some n => ⟨n % 256, Nat.mod_lt _ (by decide)⟩
    | none => 0
  length_eq := by simp

private def fixtureFederation : Digest32 := taggedDigest [70, 69, 68, 45, 49]
private def fixtureSession : Digest32 := taggedDigest [83, 69, 83, 83, 45, 49]
private def fixtureContentRoot : Digest32 := taggedDigest [82, 79, 79, 84]
private def fixtureActivation : Digest32 := taggedDigest [65, 67, 84]
private def fixtureSourceDigest : Digest32 := taggedDigest [83, 82, 67]

private def secretA : SlotSecret := ⟨taggedDigest [83, 69, 67, 45, 65]⟩
private def secretB : SlotSecret := ⟨taggedDigest [83, 69, 67, 45, 66]⟩
private def alice : Digest32 := taggedDigest [65, 76, 73, 67, 69]
private def bob : Digest32 := taggedDigest [66, 79, 66]

private def fixtureBudget : ContributionBudget where
  intel := ⟨1, by decide⟩
  supplies := ⟨1, by decide⟩
  cohesion := ⟨1, by decide⟩
  influence := ⟨1, by decide⟩
  score := ⟨1, by decide⟩
  relics := ⟨1, by decide⟩

private def fixtureMission : MissionSpec where
  missionId := ⟨1⟩
  artifact :=
    { missionId := ⟨1⟩, artifactId := ⟨1⟩
      sourceDigest := fixtureSourceDigest, contentDigest := fixtureContentRoot }
  epoch := ⟨1⟩
  federationId := fixtureFederation
  contentRoot := fixtureContentRoot
  activationDigest := fixtureActivation
  contentSession := fixtureSession
  runSeed := taggedDigest []
  budget := fixtureBudget
  allowedRelics := {⟨1⟩}
  privacy := .public
  ballot := .none
  artifact_matches := rfl
  allowed_relics_bounded := by simp [MISSION_RELIC_LIMIT]

private def slotSeven : EpochId := ⟨7⟩
private def slotEight : EpochId := ⟨8⟩

/-- **Binding.**  Two secrets, one slot, two commitments.  A curator cannot
publish one commitment and open it to a different secret without finding a sponge
collision. -/
theorem commit_separates_secrets :
    commit secretA slotSeven ≠ commit secretB slotSeven := by
  native_decide

/-- The commitment is slot-scoped: reusing a secret across slots does not reuse
its commitment. -/
theorem commit_separates_slots :
    commit secretA slotSeven ≠ commit secretA slotEight := by
  native_decide

/-- **The descriptor does not determine the instance.**  Everything an artifact
carries is fixed here — mission, federation, content session, slot, player — and
the run seed still moves when the secret does.  This is the statement the old
`signalTarget_literal` could not make, because there the seed WAS the artifact. -/
theorem published_context_does_not_determine_the_run_seed :
    runSeedFor ⟨secretA, slotSeven, alice⟩ (MissionContext.ofMission fixtureMission) ≠
      runSeedFor ⟨secretB, slotSeven, alice⟩ (MissionContext.ofMission fixtureMission) := by
  native_decide

/-- **Per player.**  Two players in the same slot, under the same secret, draw
different instances, so a solved run tells its neighbour nothing.  The cost of
this choice is that two scores are draws from one distribution rather than
attempts at one puzzle; the benefit is that the first finisher cannot hand the
answer to the rest of the slot. -/
theorem two_players_draw_different_instances :
    runSeedFor ⟨secretA, slotSeven, alice⟩ (MissionContext.ofMission fixtureMission) ≠
      runSeedFor ⟨secretA, slotSeven, bob⟩ (MissionContext.ofMission fixtureMission) := by
  native_decide

/-- **Per slot.**  The same player in two slots draws two instances, so yesterday
does not answer today. -/
theorem two_slots_draw_different_instances :
    runSeedFor ⟨secretA, slotSeven, alice⟩ (MissionContext.ofMission fixtureMission) ≠
      runSeedFor ⟨secretA, slotEight, alice⟩ (MissionContext.ofMission fixtureMission) := by
  native_decide

/-- **Practice is not the live game.**  Handing the practice draw the slot secret
itself — the most favourable possible confusion — still does not reproduce a
judged seed, because the purpose tag is in the preimage. -/
theorem practice_is_not_judged :
    practiceRunSeed secretA.value (MissionContext.ofMission fixtureMission) ≠
      runSeedFor ⟨secretA, ⟨0⟩, secretA.value⟩ (MissionContext.ofMission fixtureMission) := by
  native_decide

/-- The commitment does not repeat the run seed: publishing it is not publishing
a value one draw away from the instance. -/
theorem commitment_is_not_the_seed :
    commit secretA slotSeven ≠ runSeedFor ⟨secretA, slotSeven, alice⟩ (MissionContext.ofMission fixtureMission) := by
  native_decide

/-! ## Generic draws over a derived stream

The three games draw their own instance out of `MissionSpec.runSeed` with their
own functions.  These are the helpers a caller uses when it wants to draw
directly from a stream rather than through a digest. -/

/-- One consuming draw below `bound` from a stream, discarding the remainder.
Present so that a caller with one value to draw does not hand-roll a `find?`. -/
def drawOne? (bound : Nat) (hb : 0 < bound) (stream : List (Fin 256)) : Option (Fin bound) :=
  (SeedDraw.drawBelow? bound hb stream).map Prod.fst

theorem drawOne_is_the_consuming_draw (bound : Nat) (hb : 0 < bound)
    (stream : List (Fin 256)) :
    drawOne? bound hb stream = (SeedDraw.drawBelow? bound hb stream).map Prod.fst := rfl

#assert_axioms pad_length
#assert_axioms permute_length
#assert_axioms initialState_length
#assert_axioms lane_accept_is_whole_byte_classes
#assert_axioms lane_accept_is_the_field_minus_one
#assert_axioms laneByte_accepts_below_the_whole_classes
#assert_axioms laneByte_rejects_exactly_the_aliasing_value
#assert_axioms domains_are_distinct_and_canonical
#assert_axioms Purpose.tags_are_distinct
#assert_axioms context_ignores_the_run_seed
#assert_axioms drawOne_is_the_consuming_draw
#assert_compiled commit_separates_secrets
#assert_compiled commit_separates_slots
#assert_compiled published_context_does_not_determine_the_run_seed
#assert_compiled two_players_draw_different_instances
#assert_compiled two_slots_draw_different_instances
#assert_compiled practice_is_not_judged
#assert_compiled commitment_is_not_the_seed

end Dregg2.Games.PathOfAngels.HiddenInstance
