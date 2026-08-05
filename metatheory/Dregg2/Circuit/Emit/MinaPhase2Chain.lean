/-
# `Dregg2.Circuit.Emit.MinaPhase2Chain` — the WHOLE 46-permutation phase-2 transcript of a real
Mina block, as a CHAIN of AIR instances whose state is carried from link to link.

## ⚑ SAY THE SUBSTRATE OUT LOUD

**This is Lean-authored AIR.** Not one gate, column or constraint is authored here or in Rust: the
emitted descriptor is `MinaWrapVerifierSponge.absorbProg` — the SAME 2 048-instruction program, the
SAME `programAir qLimb`, the SAME instruction ROM as `MinaBlockFqTranscript.linkDesc` — with an
EIGHTH boundary-pin block. Rust proves the artifacts, folds them, and authors nothing. House Law #1.

## THE RESIDUAL THIS CLOSES

`MinaBlockFqTranscript` §6.1 named it exactly:

> *"One permutation of 46 is in the AIR. … Emitting all 46 is 75 900 rows / ~207 MB against a
> repository whose largest tracked file is 10 MB; **a chain of 46 instances welded by input/output
> pin equality is the shape that closes it, and it is not built here.**"*

It is built here. And the weld is NOT a host-side comparison of two printed numbers: the emitted
descriptor exposes its FULL outgoing state, so a recursion fold can `connect` link `j`'s outgoing
lanes to link `j+1`'s incoming lanes **inside the recursion circuit**
(`circuit-prove/src/mina_phase2_chain_leaf.rs`). That is the whole difference between 46 proofs and
one claim.

## ⚑ WHY THE OLD DESCRIPTOR COULD NOT BE CHAINED — the one real defect this file fixes

`MinaBlockFqTranscript.linkPins` pins SEVEN blocks: three incoming state lanes, the absorbed
element, the zero second slot, and the two SQUEEZED lanes (`allocAt 55 0 = 4`, `allocAt 55 1 = 5`).
Those two are the challenge outputs — but a Poseidon state has THREE lanes, and the third
(`allocAt 55 2 = 0`, by `the_allocation_hands_off`) was never exposed. A chain welded on that
descriptor could pin only 2/3 of the state it hands on, so the successor's third lane would be a
free prover scalar and the chain would prove nothing about the transcript.

⇒ `chainPins` pins EIGHT blocks: `in(3) ++ out(3) ++ absorbed(2)`, 256 public inputs. The layout is
deliberate: `in ++ out` is CONTIGUOUS at `[0, 6*SK)`, so a recursion leaf re-exposes the whole
continuity claim as ONE public-input slice.

## ⚑ THE ABSORBED PAIR IS IN THE CLAIM, OR THE CHAIN IS VACUOUS

A fold that connects `out j = in (j+1)` and exposes only the endpoints proves *"46 honest links
chain from (0,0,0) to this state"* — and says NOTHING about what was absorbed. A prover would be
free to absorb 91 numbers of its choice. So the absorbed pair is pinned too (blocks 6 and 7), the
leaf commits to it in-circuit, and the fold carries an ordered digest of the whole absorbed stream
up the tree. `the_chain_absorbs_the_tape_in_order` below is the statement the host checks that
digest against.

## WHAT IS AND IS NOT ESTABLISHED

  * **General, kernel-clean:** `the_chain_step_is_the_kimchi_permutation` — for EVERY link index,
    the emitted machine's output register file IS `Core.perm` of the absorbed incoming state. It is
    an instance of `MinaBlockFqTranscript.the_absorb_program_permutes_the_absorbed_state`, which
    carries no hypotheses.
  * **Compiler-trusted, and said out loud:** the tape-specific evaluations (46 Poseidon
    permutations of a 255-bit state) are `native_decide` + `#assert_compiled`.
  * **NOT established here:** that block 539508's phase-2 transcript is the transcript of a head
    this chain's consumer is tracking. The chain proves the tape absorbs to the published
    challenges; relating `TIP_STATE` to it is `LightClientMinaAir`'s business, not this file's.

Import line for the root: `import Dregg2.Circuit.Emit.MinaPhase2Chain`
-/
import Dregg2.Circuit.Emit.MinaBlockFqTranscript

namespace Dregg2.Circuit.Emit.MinaPhase2Chain

open Dregg2.Circuit.DescriptorIR2 (EffectVmDescriptor2)
open Dregg2.Circuit.EffectAirIR (EffectAir AirLeg)
open Dregg2.Circuit.Emit.EffectVmEmit (VmRow)
open Dregg2.Circuit.Emit.EffectLower (lowerAir)
open Dregg2.Circuit.Emit.PastaField (qN)
open Dregg2.Circuit.Emit.PastaFieldSound (SK limbAt qLimb)
open Dregg2.Circuit.Emit.MinaWrapVerifierProgram
open Dregg2.Circuit.Emit.MinaWrapVerifierSponge
open Dregg2.Circuit.Emit.PastaPoseidonFq (fqParams)
open Dregg2.Circuit.Emit.MinaBlockFqTranscript

set_option autoImplicit false
set_option maxRecDepth 400000

/-! ## §1 — THE 46 LINKS, DERIVED FROM THE TAPE.

⚑ The machine's shape is `perm (s0 + x0, s1 + x1, s2)` — "add two, then permute". Kimchi's
`ArithmeticSponge` defers instead: it permutes on the ARRIVAL of the element that overflows a full
rate block. The two agree link for link, and `the_chain_meets_the_emitted_link` is the weld:
absorbing `tape[0..2j)` and permuting lands exactly on `chainState j`.

The 91-element tape at rate 2 is 45 full pairs `(t 0, t 1) … (t 88, t 89)` plus the odd tail
`t 90`, which the closing squeeze absorbs alone — the second slot is `0`, which is the identity the
sponge's own lane counter already implies. 46 links. -/

/-- The pair link `j` absorbs. Links `0 … 44` take `(tape[2j], tape[2j+1])`; link `45` — the closing
squeeze — takes `(tape[90], 0)`. -/
def linkX (j : Nat) : Nat × Nat :=
  if j = 45 then (WRAP_TAPE2.getD 90 0, 0)
  else (WRAP_TAPE2.getD (2 * j) 0, WRAP_TAPE2.getD (2 * j + 1) 0)

/-- One link of the reference sponge: absorb the pair into lanes 0 and 1, then permute. -/
def linkStep (s : List Nat) (j : Nat) : List Nat :=
  PastaPoseidonFq.Core.perm fqParams
    [(s.getD 0 0 + (linkX j).1) % qN, (s.getD 1 0 + (linkX j).2) % qN, s.getD 2 0]

/-- ⚑ **THE CHAIN STATE.** `chainState j` is the sponge state entering link `j`. `chainState 0` is
the fresh sponge; `chainState 46` is the state whose lanes 0 and 1 are the block's raw `v′`/`u′`. -/
def chainState : Nat → List Nat
  | 0 => [0, 0, 0]
  | (j + 1) => linkStep (chainState j) j

/-- The chain starts at a FRESH Kimchi sponge — not at a state the emitter chose. -/
theorem the_chain_starts_fresh : chainState 0 = PastaPoseidonFq.newSponge.st := rfl

/-- ⚑ **EVERY TAPE ELEMENT IS ABSORBED EXACTLY ONCE, IN ORDER.** Concatenating the 46 links'
absorbed pairs reproduces the block's 91-element tape followed by the single padding zero the odd
tail forces. Without this the chain could be 46 honest permutations of values nobody checked; this
is the statement the in-circuit transcript digest is folded against. -/
theorem the_chain_absorbs_the_tape_in_order :
    ((List.range 46).flatMap (fun j => [(linkX j).1, (linkX j).2])) = WRAP_TAPE2 ++ [0] := by
  native_decide

/-! ## §2 — THE MACHINE COMPUTES THE CHAIN STEP, AT EVERY LINK.

⚑ This is the general, hypothesis-free half, and it is the reason the chain is 46 WITNESSES rather
than 46 new statements: one theorem covers every link. -/

/-- The register file link `j` starts from: the three incoming state lanes, then the absorbed pair,
then the unused scratch. -/
def chainInitVec (j : Nat) : List Nat :=
  [ (chainState j).getD 0 0, (chainState j).getD 1 0, (chainState j).getD 2 0
  , (linkX j).1, (linkX j).2, 0 ]

/-- The register file link `j` ends in, run on the STRICT generator. -/
def chainOutVec (j : Nat) : List Nat := runProgVecAt qN (chainInitVec j) absorbCore

/-- The three outgoing state lanes, read from the allocation the permutation ends on:
`allocAt 55 = (4, 5, 0)`. Computed by the interpreter; never asserted. -/
def chainOut (j : Nat) : List Nat :=
  [ regsOf (chainOutVec j) (allocAt PastaPoseidon.rounds 0)
  , regsOf (chainOutVec j) (allocAt PastaPoseidon.rounds 1)
  , regsOf (chainOutVec j) (allocAt PastaPoseidon.rounds 2) ]

/-- ⚑⚑ **THE LINK'S MACHINE OUTPUT IS THE NEXT LINK'S INPUT — AT EVERY `j`, WITH NO HYPOTHESES.**
This is the fact the recursion fold enforces on the wire by connecting pin blocks; here it is a
theorem about the emitted program, kernel-clean, and general over the whole chain rather than
checked at the 46 points that happen to be emitted. -/
theorem the_chain_step_is_the_kimchi_permutation (j : Nat) : chainOut j = chainState (j + 1) := by
  have hregs : regsOf (chainOutVec j) = runProgAt qN (regsOf (chainInitVec j)) absorbCore := by
    rw [chainOutVec, regsOf_runProgVecAt]
  -- The six register reads are structural: `chainInitVec j` is a literal six-cons list whatever
  -- its (unevaluated) entries are, so each projection is `rfl` at a VARIABLE `j`.
  have h0 : regsOf (chainInitVec j) 0 = (chainState j).getD 0 0 := rfl
  have h1 : regsOf (chainInitVec j) 1 = (chainState j).getD 1 0 := rfl
  have h2 : regsOf (chainInitVec j) 2 = (chainState j).getD 2 0 := rfl
  have h3 : regsOf (chainInitVec j) 3 = (linkX j).1 := rfl
  have h4 : regsOf (chainInitVec j) 4 = (linkX j).2 := rfl
  have hperm := the_absorb_program_permutes_the_absorbed_state (regsOf (chainInitVec j))
  rw [h0, h1, h2, h3, h4] at hperm
  show [ regsOf (chainOutVec j) (allocAt PastaPoseidon.rounds 0)
       , regsOf (chainOutVec j) (allocAt PastaPoseidon.rounds 1)
       , regsOf (chainOutVec j) (allocAt PastaPoseidon.rounds 2) ] = chainState (j + 1)
  rw [hregs, hperm]
  simp only [chainState, linkStep]

/-! ## §3 — AND THE CHAIN IS THE BLOCK'S OWN PHASE-2 TRANSCRIPT.

The two ends. `chainState 45` is the state `MinaBlockFqTranscript` DERIVED from the tape and put on
the machine as `LINK_S`, so the 46th link of this chain IS the already-deployed wrap link; and
`chainState 46`'s first two lanes truncate to the challenges `proof.oracles(…)` returned. -/

/-- ⚑ **THE 46th LINK OF THIS CHAIN IS THE DEPLOYED WRAP LINK.** `LINK_S` was derived from the
91-element tape by `absorbMany` + one permutation; `chainState 45` is reached by 45 machine steps.
They are the same state, so the chain does not quietly re-found the transcript on its own arithmetic. -/
theorem the_chain_meets_the_emitted_link : chainState 45 = LINK_S := by native_decide

/-- …and the 46th link absorbs exactly what the deployed one absorbs. -/
theorem the_last_link_is_the_closing_squeeze : linkX 45 = (LINK_X, 0) := by native_decide

/-- ⚑⚑ **THE CHAIN IS `absorbMany` OVER THE WHOLE 91-ELEMENT TAPE.** Discharged from the deployed
`the_link_input_is_the_real_tape_prefix` by rewriting through `the_chain_meets_the_emitted_link` —
so the chain inherits the tape weld rather than asserting a second one. -/
theorem the_chain_is_the_whole_phase2_transcript :
    PastaPoseidonFq.absorbMany fqParams PastaPoseidonFq.newSponge WRAP_TAPE2
      = ⟨PastaPoseidonFq.Core.absorbAt fqParams (chainState 45) 0 (linkX 45).1,
         PastaPoseidonFq.Mode.absorbed 1⟩ := by
  rw [the_chain_meets_the_emitted_link, the_last_link_is_the_closing_squeeze]
  exact the_link_input_is_the_real_tape_prefix

/-- ⚑⚑ **AND THE CHAIN ENDS ON THE BLOCK'S OWN CHALLENGES.** The two high-entropy limbs
`challenge()` keeps of `chainState 46`'s first two lanes are the `v′` (polyscale) and `u′`
(evalscale) Mina devnet block 539508's proof committed to. -/
theorem the_chain_ends_at_the_blocks_challenges :
    (chainState 46).getD 0 0 % 2 ^ 128 = WRAP_V_CHAL
    ∧ (chainState 46).getD 1 0 % 2 ^ 128 = WRAP_U_CHAL := by
  native_decide

/-- Non-vacuity of the CHAIN, not of the reference sponge: perturbing the head of the tape — the
phase-1 digest, absorbed by link 0 and 45 permutations away from the answer — moves the challenges.
So the chain genuinely carries state end to end rather than re-deriving the tail. -/
theorem a_tampered_tape_head_moves_the_chains_end :
    (let lx : Nat → Nat × Nat := fun j =>
       if j = 0 then (0, (linkX 0).2) else linkX j
     let st : Nat → List Nat := fun n => Nat.rec ([0, 0, 0] : List Nat)
       (fun j ih => PastaPoseidonFq.Core.perm fqParams
         [(ih.getD 0 0 + (lx j).1) % qN, (ih.getD 1 0 + (lx j).2) % qN, ih.getD 2 0]) n
     (st 46).getD 0 0 % 2 ^ 128) ≠ WRAP_V_CHAL := by
  native_decide

/-! ## §4 — THE EMITTED CHAIN-LINK DESCRIPTOR.

⚑ **EIGHT pin blocks, 256 public inputs**, laid out `in(3) ++ out(3) ++ absorbed(2)` so the
continuity claim `in ++ out` is the CONTIGUOUS slice `[0, 6*SK)` a recursion leaf re-exposes in one
piece, and the absorbed pair is the contiguous slice `[6*SK, 8*SK)` the transcript digest commits to.

⚑ **AND THE PROGRAM IS THE DEPLOYED ONE.** `chainAir` is `programAir qLimb absorbProg` — the same
2 048 instructions as `MinaBlockFqTranscript.linkAir` and `MinaWrapVerifierSponge.absorbAir`, hence
the same instruction ROM, hence the same 55×3 `fq_kimchi` round constants as descriptor cells. The
Rust harness asserts the ROM manifests are equal row for row against `pasta-fq-wraplink.json`. -/

def CHAIN_PI_COUNT : Nat := 8 * SK

theorem CHAIN_PI_COUNT_eq : CHAIN_PI_COUNT = 256 := rfl

/-- ⚑ **THE THIRD OUTGOING LANE IS REGISTER 0** — the fact the seven-block descriptor was missing.
`allocAt 55 = (4, 5, 0)`, so pinning `VmRow.last 4/5/0` pins the WHOLE outgoing Poseidon state. -/
theorem the_outgoing_lanes_are_registers_4_5_0 :
    (allocAt PastaPoseidon.rounds 0, allocAt PastaPoseidon.rounds 1,
     allocAt PastaPoseidon.rounds 2) = (4, 5, 0) := by decide

/-- The pins: incoming state, OUTGOING STATE IN FULL, and the absorbed pair. -/
def chainPins : List AirLeg :=
  pinBlock VmRow.first 0 0 ++ pinBlock VmRow.first 1 SK ++ pinBlock VmRow.first 2 (2 * SK)
    ++ pinBlock VmRow.last 4 (3 * SK) ++ pinBlock VmRow.last 5 (4 * SK)
    ++ pinBlock VmRow.last 0 (5 * SK)
    ++ pinBlock VmRow.first 3 (6 * SK) ++ pinBlock VmRow.first 4 (7 * SK)

def chainAir : EffectAir :=
  { programAir qLimb absorbProg with legs := (programAir qLimb absorbProg).legs ++ chainPins }

theorem chainAir_mainRailOk : chainAir.mainRailOk = true := by
  unfold chainAir EffectAir.mainRailOk
  simp only [List.all_append, Bool.and_eq_true]
  refine ⟨programAir_mainRailOk qLimb absorbProg, ?_⟩
  simp only [chainPins, pinBlock, List.all_append, List.all_map, Bool.and_eq_true, List.all_eq_true]
  repeat' apply And.intro
  all_goals (intro _ _; rfl)

/-- ⚑ **THE EMITTED CHAIN-LINK DESCRIPTOR.** ONE descriptor for all 46 links — the residual really
was witnesses and not an algebra, and this is the object that says so. -/
def chainDesc : EffectVmDescriptor2 :=
  lowerAir "dregg-pasta-fq-chainlink::v1" PROG_WIDTH CHAIN_PI_COUNT [] chainAir

/-- ⚑ **AND IT PINS A STRICT SUPERSET OF THE DEPLOYED WRAP LINK.** The seven-block descriptor's
legs are the program's plus `linkPins`; this one's are the program's plus `chainPins`. Both start
from the SAME `programAir qLimb absorbProg`, so the ROM, the width and the constraint core are
literally the same object and only the boundary changes. -/
theorem the_chain_air_extends_the_program_air :
    chainAir.legs = (programAir qLimb absorbProg).legs ++ chainPins
    ∧ linkAir.legs = (programAir qLimb absorbProg).legs ++ linkPins := by
  exact ⟨rfl, rfl⟩

/-! ## §5 — THE 46 WITNESSES. -/

/-- The INCOMING-state public-input block of link `j` — PI slots `[0, 3*SK)`. -/
def inBlock (j : Nat) : List ℤ :=
  (List.range SK).map (limbAt ((chainState j).getD 0 0))
    ++ (List.range SK).map (limbAt ((chainState j).getD 1 0))
    ++ (List.range SK).map (limbAt ((chainState j).getD 2 0))

/-- The OUTGOING-state public-input block of link `j` — PI slots `[3*SK, 6*SK)`. Read from the
interpreter's own final register file, never from the reference. -/
def outBlock (j : Nat) : List ℤ :=
  (List.range SK).map (limbAt ((chainOut j).getD 0 0))
    ++ (List.range SK).map (limbAt ((chainOut j).getD 1 0))
    ++ (List.range SK).map (limbAt ((chainOut j).getD 2 0))

/-- The absorbed pair's block — PI slots `[6*SK, 8*SK)`. -/
def absorbedBlock (j : Nat) : List ℤ :=
  (List.range SK).map (limbAt (linkX j).1) ++ (List.range SK).map (limbAt (linkX j).2)

/-- The 256 public inputs of link `j`, every one computed from the tape or from the interpreter. -/
def chainPIs (j : Nat) : List ℤ := inBlock j ++ outBlock j ++ absorbedBlock j

theorem chainPIs_length (j : Nat) : (chainPIs j).length = 256 := by
  simp [chainPIs, inBlock, outBlock, absorbedBlock, SK]

/-- ⚑⚑ **CONTINUITY IN THE EMITTED CLAIMS.** Link `j`'s outgoing PI block IS link `j+1`'s incoming
PI block, limb for limb — a corollary of `the_chain_step_is_the_kimchi_permutation`, so it holds at
every `j` rather than at the 46 points that were emitted. This is the equality the fold's
`cb.connect` enforces in-circuit; here it is why an HONEST chain satisfies it. -/
theorem the_emitted_claims_are_continuous (j : Nat) : outBlock j = inBlock (j + 1) := by
  simp only [outBlock, inBlock, the_chain_step_is_the_kimchi_permutation]

/-- The trace of link `j`, from the STRICT generator `runRowsVecAt` — the one
`runRowsVecAt_is_runRowsAt` welds to `runRowsAt`. Rust fills no cell. -/
def chainTrace (j : Nat) : List (List ℤ) :=
  runRowsVecAt qN qLimb (chainInitVec j) 0 absorbProg

/-- ⚑ **AND EVERY EMITTED TRACE IS `runRowsAt`'s** — the object every denotation above is a
statement about, at every link. -/
theorem chainTrace_is_the_program_run (j : Nat) :
    chainTrace j = runRowsAt qN qLimb (regsOf (chainInitVec j)) 0 absorbProg := by
  rw [chainTrace, runRowsVecAt_is_runRowsAt]

/-! ## §6 — RESIDUALS, NAMED.

1. **The chain is phase-2 only.** A Wrap verification is six stages; this is the Fr-sponge one.
   The five MSM stages need curve arithmetic that is not programmed here
   (`pasta-msm-bucketed-vesta-c2` is that frontier).
2. **`native_decide` carries the tape-specific facts**, and says so via `#assert_compiled`. The
   GENERAL step (`the_chain_step_is_the_kimchi_permutation`) is kernel-clean.
3. **The endomorphism lift is not here.** `v′ ↦ v` and `u′ ↦ u` is `ScalarChallenge::to_field`.
4. **Not that the transcript is a tracked head's.** This chain proves the tape absorbs to the
   published challenges; no gate here relates a light client's `TIP_STATE` to it.
-/

#assert_axioms the_chain_starts_fresh
#assert_axioms the_chain_step_is_the_kimchi_permutation
#assert_axioms CHAIN_PI_COUNT_eq
#assert_axioms the_outgoing_lanes_are_registers_4_5_0
#assert_axioms chainAir_mainRailOk
#assert_axioms the_chain_air_extends_the_program_air
#assert_axioms chainPIs_length
#assert_axioms the_emitted_claims_are_continuous
#assert_axioms chainTrace_is_the_program_run

-- ⚑ COMPILER-TRUSTED, and said out loud: each is up to 46 Kimchi permutations of a 255-bit state.
#assert_compiled the_chain_absorbs_the_tape_in_order
#assert_compiled the_chain_meets_the_emitted_link
#assert_compiled the_last_link_is_the_closing_squeeze
#assert_compiled the_chain_ends_at_the_blocks_challenges
#assert_compiled a_tampered_tape_head_moves_the_chains_end
-- …and the tape weld, which INHERITS the two compiled facts it is rewritten through.
#assert_compiled the_chain_is_the_whole_phase2_transcript

end Dregg2.Circuit.Emit.MinaPhase2Chain
