/-
# `Dregg2.Circuit.Emit.MinaPhase1Chain` — the **PHASE-1** (Fp) transcript of a real Mina block as a
chain of AIR instances, and **the gate that ties `fq_digest` to the block**.

## ⚑ SAY THE SUBSTRATE OUT LOUD

**This is Lean-authored AIR.** The emitted descriptor is `MinaWrapVerifierSpongeFp.fpAbsorbProg` on
`MinaWrapVerifierProgram.programAir pLimb` with an eighth boundary-pin block — the same 2 048
instructions, the same 469 columns, the same `chainPins` layout `MinaPhase2Chain` deploys. Rust
proves the artifacts and authors no constraint. House Law #1.

## ⚑⚑ THE HOLE THIS CLOSES, STATED PLAINLY

`MinaPhase2Chain` folds 46 links and ends on Mina devnet block 539508's own `v′`/`u′`. Its tape's
**element 0 is `fq_digest`**, and until this file **nothing in the tree derived it in a circuit**:

> *"the transcript chain proves a tape absorbs to the published challenges without proving whose
> tape."*

`fq_digest` is the OUTPUT of phase 1. This file puts phase 1 on the machine, and
`the_phase1_digest_is_the_phase2_tapes_head` is the equality that welds the two chains:

  * **link 26's OUTGOING LANE 1** — PI slots `[4·SK, 5·SK)` of `dregg-pasta-fp-chainlink::v1`, and
  * **link 0's ABSORBED[0]** — PI slots `[6·SK, 7·SK)` of `dregg-pasta-fq-chainlink::v1`

are the same **32 felts, elementwise, at full limb width**. ⚑ **No digest, so no birthday bound**:
a forger must match all 32 eight-bit limbs of a 254-bit value, which is exact equality — not a
`2^31` one-felt tie, and not a hash the two sides could collide on. This is the encoding the ξ-basis
weld already uses, and the reason it is right here is the same: both sides publish at `SK = 32`
eight-bit limbs, so a batch verifier compares two slices and does **no arithmetic**.

## THE 27 LINKS, AND WHY THE PAIRING IS A THEOREM

Phase 1 is not a flat absorption: it INTERLEAVES absorbs and squeezes
(`verifier.rs:159-283`) — absorb 37 coordinates, squeeze β, squeeze γ, absorb `z_comm`, squeeze α′,
absorb `t_comm`, squeeze ζ′, take the digest. Between two consecutive PERMUTATIONS the sponge
accumulates at most two additions into lanes 0 and 1, so every permutation event is
`perm (s₀ + a₀, s₁ + a₁, s₂)` — **exactly the shape `absorbProg` computes.** One descriptor, every
link, both phases.

`the_pairs_are_the_absorb_schedule` proves that pairing is the upstream state machine's own, at
EVERY parameter set and EVERY segment — so the 27 is derived, not counted:

| segment | elements | links |
|---|---|---|
| `fpTape` (index digest ‖ 2 prev-challenge comms ‖ public comm ‖ 15 witness comms) → β, γ | 37 | **19** |
| `z_comm` → α′ | 2 | **1** |
| `t_comm` (7 chunks) → ζ′, digest | 14 | **7** |

⚑ **γ AND THE DIGEST COST NO LINK.** `squeeze` from `Squeezed 1` reads lane 1 and does NOT permute
(`poseidon.rs:128-146`), so γ is lane 1 of β's state and `fq_digest` is lane 1 of ζ′'s. Both are
already pinned: the chain link exposes all THREE outgoing lanes.

## WHAT IS AND IS NOT ESTABLISHED

  * **General, kernel-clean:** `the_chain_step_is_the_kimchi_permutation` (every link, no
    hypotheses — an instance of `MinaWrapVerifierSpongeFp.the_absorb_program_permutes_gen`), and
    `the_pairs_are_the_absorb_schedule` (every `Params`, every segment).
  * **Compiler-trusted, said out loud:** the tape-specific evaluations — up to 27 Kimchi
    permutations of a 255-bit state — are `native_decide` + `#assert_compiled`.
  * **NOT established:** that the 53 absorbed coordinates are the commitments they claim to be.
    They enter the transcript as `(x, y)` field elements; nothing here checks a point is on the
    curve or that `public_comm` commits to the public input. That is the Wrap group check and it
    bottoms out at the IPA `msm == 0` floor (P10). Deriving `fq_digest` removes a CARRIER; it does
    not verify Mina.
  * **NOT established:** that the verifier-index digest (tape element 0) is the VK's. It is itself a
    sponge over every commitment of the verifier index and is absorbed here as a value.

Import line for the root: `import Dregg2.Circuit.Emit.MinaPhase1Chain`
-/
import Dregg2.Circuit.Emit.MinaWrapVerifierSpongeFp
import Dregg2.Circuit.Emit.MinaPhase2Chain
import Dregg2.Circuit.Emit.MinaRealBlockTranscript

namespace Dregg2.Circuit.Emit.MinaPhase1Chain

open Dregg2.Circuit.DescriptorIR2 (EffectVmDescriptor2)
open Dregg2.Circuit.EffectAirIR (EffectAir AirLeg)
open Dregg2.Circuit.Emit.EffectVmEmit (VmRow)
open Dregg2.Circuit.Emit.EffectLower (lowerAir)
open Dregg2.Circuit.Emit.PastaField (pN qN)
open Dregg2.Circuit.Emit.PastaFieldSound (SK limbAt pLimb)
open Dregg2.Circuit.Emit.MinaWrapVerifierProgram
open Dregg2.Circuit.Emit.MinaWrapVerifierSponge
open Dregg2.Circuit.Emit.MinaWrapVerifierSpongeFp
open Dregg2.Circuit.Emit.PastaPoseidonFq (Params fpParams)

set_option autoImplicit false
-- ⚑ A `set_option` does not cross an import.
set_option maxRecDepth 4000000

/-! ## §1 — THE PAIRING IS THE SPONGE'S OWN SCHEDULE, AT EVERY PARAMETER SET.

⚑ This section is what makes "27 links" a DERIVED number rather than a counted one. It is stated
over an arbitrary `Params` and an arbitrary segment, so it covers phase 2's 46 as well. -/

/-- Chunk a segment into the pairs the rate-2 sponge absorbs between permutations. An odd tail is
padded with a `0` second slot — which is the identity the lane counter already implies, and which
the machine's second absorb instruction performs as `s₁ + 0`. -/
def pairsOf : List Nat → List (Nat × Nat)
  | [] => []
  | [x] => [(x, 0)]
  | x :: y :: rest => (x, y) :: pairsOf rest

/-- One link: add the pair into lanes 0 and 1, then permute. `MinaPhase2Chain.linkStep` at
`fqParams` is this. -/
def linkStepOf (P : Params) (s : List Nat) (x : Nat × Nat) : List Nat :=
  PastaPoseidonFq.Core.perm P
    [ (s.getD 0 0 + x.1) % P.modulus, (s.getD 1 0 + x.2) % P.modulus, s.getD 2 0 ]

/-- Every lane a round writes is reduced. -/
theorem round_output_is_canonical (P : Params) (hP : 0 < P.modulus) (rc hs : List Nat) :
    ∀ v ∈ PastaPoseidonFq.Core.round P rc hs, v < P.modulus := by
  intro v hv
  simp only [PastaPoseidonFq.Core.round, List.mem_map] at hv
  obtain ⟨j, _, hj⟩ := hv
  exact hj ▸ Nat.mod_lt _ hP

theorem round_output_has_three_lanes (P : Params) (rc hs : List Nat) :
    (PastaPoseidonFq.Core.round P rc hs).length = 3 := by
  simp [PastaPoseidonFq.Core.round]

/-- ⚑ **A PERMUTATION'S OUTPUT IS A CANONICAL THREE-LANE STATE.** The invariant the chain carries,
and the reason the odd tail's `s₁ + 0` really is the identity. -/
theorem perm_output_is_canonical (P : Params) (hP : 0 < P.modulus) (hs : List Nat) :
    (∀ v ∈ PastaPoseidonFq.Core.perm P hs, v < P.modulus)
      ∧ (PastaPoseidonFq.Core.perm P hs).length = 3 := by
  have hsplit : PastaPoseidonFq.Core.perm P hs
      = PastaPoseidonFq.Core.round P (P.rcs.getD 54 [])
          (PastaPoseidonFq.Core.permFrom P 0 54 hs) := by
    show PastaPoseidonFq.Core.permFrom P 0 PastaPoseidon.rounds hs = _
    simp [PastaPoseidonFq.Core.permFrom, show PastaPoseidon.rounds = 54 + 1 from rfl,
      List.range_succ]
  exact ⟨hsplit ▸ round_output_is_canonical P hP _ _, hsplit ▸ round_output_has_three_lanes P _ _⟩

theorem linkStepOf_is_canonical (P : Params) (hP : 0 < P.modulus) (s : List Nat) (x : Nat × Nat) :
    (∀ v ∈ linkStepOf P s x, v < P.modulus) ∧ (linkStepOf P s x).length = 3 :=
  perm_output_is_canonical P hP _

/-! ### §1b — the four sponge-step equations, stated so `Core.perm` stays OPAQUE.

⚠ Every one of these is `rfl`, but proving the schedule lemma by a single `rfl` makes the
elaborator whnf a symbolic 55-round permutation and it times out. Naming the steps keeps `perm` a
head the unifier never opens. -/

theorem absorb1_partial (P : Params) (s : List Nat) (n x : Nat) (h : n ≠ PastaPoseidon.rate) :
    PastaPoseidonFq.absorb1 P ⟨s, PastaPoseidonFq.Mode.absorbed n⟩ x
      = ⟨PastaPoseidonFq.Core.absorbAt P s n x, PastaPoseidonFq.Mode.absorbed (n + 1)⟩ := by
  simp [PastaPoseidonFq.absorb1, h]

theorem absorb1_full (P : Params) (s : List Nat) (x : Nat) :
    PastaPoseidonFq.absorb1 P ⟨s, PastaPoseidonFq.Mode.absorbed PastaPoseidon.rate⟩ x
      = ⟨PastaPoseidonFq.Core.absorbAt P (PastaPoseidonFq.Core.perm P s) 0 x,
         PastaPoseidonFq.Mode.absorbed 1⟩ := by
  simp [PastaPoseidonFq.absorb1]

theorem squeeze1_absorbed_state (P : Params) (s : List Nat) (n : Nat) :
    (PastaPoseidonFq.squeeze1 P ⟨s, PastaPoseidonFq.Mode.absorbed n⟩).1.st
      = PastaPoseidonFq.Core.perm P s := rfl

theorem absorbAt_lane0 (P : Params) (a b c x : Nat) :
    PastaPoseidonFq.Core.absorbAt P [a, b, c] 0 x = [(a + x) % P.modulus, b, c] := rfl

theorem absorbAt_lane1 (P : Params) (a b c y : Nat) :
    PastaPoseidonFq.Core.absorbAt P [a, b, c] 1 y = [a, (b + y) % P.modulus, c] := rfl

theorem linkStepOf_triple (P : Params) (a b c x y : Nat) :
    linkStepOf P [a, b, c] (x, y)
      = PastaPoseidonFq.Core.perm P [(a + x) % P.modulus, (b + y) % P.modulus, c] := rfl

/-- ⚑ `fpParams.modulus` IS `pN`. Written through `congrArg` so the unifier never opens
`Core.perm` — a plain `rfl` here makes the elaborator whnf a symbolic 55-round permutation. -/
theorem linkStepOf_fp (s : List Nat) (x : Nat × Nat) :
    linkStepOf fpParams s x
      = PastaPoseidonFq.Core.perm fpParams
          [(s.getD 0 0 + x.1) % pN, (s.getD 1 0 + x.2) % pN, s.getD 2 0] :=
  congrArg (PastaPoseidonFq.Core.perm fpParams) rfl

/-- ⚑⚑ **THE PAIRING IS THE UPSTREAM STATE MACHINE'S.** Absorbing a NON-EMPTY segment into a sponge
that is at lane 0 — a fresh sponge, or one just after a squeeze, which `absorb1`'s `.squeezed` arm
resets to lane 0 — and then SQUEEZING lands on exactly `pairsOf` folded through `linkStepOf`.

General over the parameter set and over the segment, so it is the reason phase 1 is 27 links and
phase 2 is 46, rather than two counted numbers. -/
theorem the_pairs_are_the_absorb_schedule (P : Params) (hP : 0 < P.modulus) :
    ∀ (xs s : List Nat), xs ≠ [] → s.length = 3 → (∀ v ∈ s, v < P.modulus) →
      (PastaPoseidonFq.squeeze1 P
          (PastaPoseidonFq.absorbMany P ⟨s, PastaPoseidonFq.Mode.absorbed 0⟩ xs)).1.st
        = (pairsOf xs).foldl (linkStepOf P) s := by
  intro xs
  induction xs using pairsOf.induct with
  | case1 => intro _ hne; exact absurd rfl hne
  | case2 x =>
      intro s _ h3 hc
      match s, h3 with
      | [a, b, c], _ =>
          have hb : b < P.modulus := hc b (by simp)
          -- one absorb into lane 0, then the squeeze's permutation
          rw [pairsOf, List.foldl_cons, List.foldl_nil, linkStepOf_triple, Nat.add_zero,
            Nat.mod_eq_of_lt hb, PastaPoseidonFq.absorbMany, List.foldl_cons, List.foldl_nil,
            absorb1_partial P _ 0 x (by decide), absorbAt_lane0, squeeze1_absorbed_state]
  | case3 x y rest ih =>
      intro s _ h3 hc
      match s, h3 with
      | [a, b, c], _ =>
          -- absorbing `x` then `y` fills the rate block
          have hxy : PastaPoseidonFq.absorbMany P ⟨[a, b, c], PastaPoseidonFq.Mode.absorbed 0⟩
              (x :: y :: rest)
              = PastaPoseidonFq.absorbMany P
                  ⟨[(a + x) % P.modulus, (b + y) % P.modulus, c],
                   PastaPoseidonFq.Mode.absorbed PastaPoseidon.rate⟩ rest := by
            rw [PastaPoseidonFq.absorbMany, List.foldl_cons, List.foldl_cons,
              absorb1_partial P _ 0 x (by decide), absorbAt_lane0,
              absorb1_partial P _ 1 y (by decide), absorbAt_lane1]
            rfl
          by_cases hr : rest = []
          · -- both lanes fill, and the SQUEEZE supplies the one permutation
            subst hr
            rw [hxy, pairsOf, pairsOf, List.foldl_cons, List.foldl_nil, linkStepOf_triple,
              PastaPoseidonFq.absorbMany, List.foldl_nil, squeeze1_absorbed_state]
          · -- ⚑ the NEXT element ARRIVES at a full rate block and permutes — which is the same
            -- sponge as starting fresh from the permuted state, because `absorb1` from
            -- `Absorbed 0` and from `Absorbed rate` both land on `Absorbed 1` over the same state.
            have hstep : PastaPoseidonFq.absorbMany P
                ⟨[(a + x) % P.modulus, (b + y) % P.modulus, c],
                 PastaPoseidonFq.Mode.absorbed PastaPoseidon.rate⟩ rest
                = PastaPoseidonFq.absorbMany P
                    ⟨linkStepOf P [a, b, c] (x, y), PastaPoseidonFq.Mode.absorbed 0⟩ rest := by
              cases rest with
              | nil => exact absurd rfl hr
              | cons z zs =>
                  rw [PastaPoseidonFq.absorbMany, PastaPoseidonFq.absorbMany, List.foldl_cons,
                    List.foldl_cons, absorb1_full, absorb1_partial P _ 0 z (by decide),
                    linkStepOf_triple]
            rw [hxy, hstep, pairsOf, List.foldl_cons]
            obtain ⟨hcan, hlen⟩ := linkStepOf_is_canonical P hP [a, b, c] (x, y)
            exact ih _ hr hlen hcan

/-! ## §2 — THE REAL BLOCK'S PHASE-1 TAPE, and its 27 links.

⚑ **THE TAPE IS NOT RE-TRANSCRIBED.** `fpTape`, `ZCOMM_XY` and `TCOMM_XY` are
`MinaRealBlockTranscript`'s own lists — the ones whose `#guard`ed run reproduces the block's
published β/γ/α′/ζ′/digest, assembled from `verifier.rs` order by the pickles extractor with
o1-labs' own verifier asserting `verify = Ok(())` before a number was emitted. This file adds no
decimal. -/

open Dregg2.Circuit.Emit.MinaRealBlockTranscript (fpTape ZCOMM_XY TCOMM_XY BETA_N GAMMA_N
  ALPHA_CHAL ZETA_CHAL FQ_DIGEST wrapPhase1)

/-- The absorbed pairs of all three segments, in transcript order. -/
def linkXs : List (Nat × Nat) := pairsOf fpTape ++ pairsOf ZCOMM_XY ++ pairsOf TCOMM_XY

/-- ⚑ **27 LINKS, AND THE SPLIT IS 19 + 1 + 7** — derived from the segment lengths by `pairsOf`,
not counted. The 19 is where β and γ come out, the 20th is α′, and the 27th is ζ′ AND the digest. -/
theorem the_chain_is_twenty_seven_links :
    linkXs.length = 27
    ∧ (pairsOf fpTape).length = 19
    ∧ (pairsOf ZCOMM_XY).length = 1
    ∧ (pairsOf TCOMM_XY).length = 7 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

def linkX (j : Nat) : Nat × Nat := linkXs.getD j (0, 0)

/-- ⚑ **THE CHAIN STATE.** `chainState j` is the sponge state entering link `j`; `chainState 0` is
the fresh Kimchi sponge. -/
def chainState : Nat → List Nat
  | 0 => [0, 0, 0]
  | (j + 1) => linkStepOf fpParams (chainState j) (linkX j)

/-- The chain starts at a FRESH Kimchi sponge — not at a state the emitter chose. -/
theorem the_chain_starts_fresh : chainState 0 = PastaPoseidonFq.newSponge.st := rfl

/-- ⚑ **EVERY TAPE ELEMENT IS ABSORBED EXACTLY ONCE, IN ORDER.** Concatenating the 27 links'
absorbed pairs reproduces the three segments in `verifier.rs` order, followed by the single padding
zero the odd 37-element first segment forces. Without this the chain could be 27 honest
permutations of values nobody checked. -/
theorem the_chain_absorbs_the_tape_in_order :
    ((List.range 27).flatMap (fun j => [(linkX j).1, (linkX j).2]))
      = (fpTape ++ [0]) ++ ZCOMM_XY ++ TCOMM_XY := by
  native_decide

/-! ## §3 — THE MACHINE COMPUTES THE CHAIN STEP, AT EVERY LINK. -/

/-- The register file link `j` starts from. -/
def chainInitVec (j : Nat) : List Nat :=
  [ (chainState j).getD 0 0, (chainState j).getD 1 0, (chainState j).getD 2 0
  , (linkX j).1, (linkX j).2, 0 ]

def chainOutVec (j : Nat) : List Nat := runProgVecAt pN (chainInitVec j) fpAbsorbCore

/-- The three outgoing state lanes, read from `allocAt 55 = (4, 5, 0)`. Computed by the
interpreter; never asserted. -/
def chainOut (j : Nat) : List Nat :=
  [ regsOf (chainOutVec j) (allocAt PastaPoseidon.rounds 0)
  , regsOf (chainOutVec j) (allocAt PastaPoseidon.rounds 1)
  , regsOf (chainOutVec j) (allocAt PastaPoseidon.rounds 2) ]

/-- ⚑⚑ **THE LINK'S MACHINE OUTPUT IS THE NEXT LINK'S INPUT — AT EVERY `j`, WITH NO HYPOTHESES.**
An instance of `MinaWrapVerifierSpongeFp.the_absorb_program_permutes_gen` at `fpParams`, so the
whole chain rests on ONE kernel-clean theorem rather than on 27 checked points. -/
theorem the_chain_step_is_the_kimchi_permutation (j : Nat) : chainOut j = chainState (j + 1) := by
  have hregs : regsOf (chainOutVec j) = runProgAt pN (regsOf (chainInitVec j)) fpAbsorbCore := by
    rw [chainOutVec, regsOf_runProgVecAt]
  have h0 : regsOf (chainInitVec j) 0 = (chainState j).getD 0 0 := rfl
  have h1 : regsOf (chainInitVec j) 1 = (chainState j).getD 1 0 := rfl
  have h2 : regsOf (chainInitVec j) 2 = (chainState j).getD 2 0 := rfl
  have h3 : regsOf (chainInitVec j) 3 = (linkX j).1 := rfl
  have h4 : regsOf (chainInitVec j) 4 = (linkX j).2 := rfl
  have hperm := the_fp_absorb_program_permutes (regsOf (chainInitVec j))
  rw [h0, h1, h2, h3, h4] at hperm
  show [ regsOf (chainOutVec j) (allocAt PastaPoseidon.rounds 0)
       , regsOf (chainOutVec j) (allocAt PastaPoseidon.rounds 1)
       , regsOf (chainOutVec j) (allocAt PastaPoseidon.rounds 2) ] = chainState (j + 1)
  rw [hregs, hperm]
  show _ = linkStepOf fpParams (chainState j) (linkX j)
  rw [linkStepOf_fp]

/-! ## §4 — AND THE CHAIN IS THE BLOCK'S OWN PHASE-1 TRANSCRIPT.

⚑ Four squeezes and a digest come off THREE states of this chain, and no others:

| output | where it is read | permutes? |
|---|---|---|
| β | `chainState 19` lane 0 | the 19th link IS its permutation |
| γ | `chainState 19` lane 1 | **no** — `Squeezed 1 → Squeezed 2` reads lane 1 |
| α′ | `chainState 20` lane 0 | the 20th link |
| ζ′ | `chainState 27` lane 0 | the 27th link |
| `fq_digest` | `chainState 27` lane 1 | **no** — same free-lane read as γ | -/

/-- ⚑⚑ **THE CHAIN REPRODUCES EVERY PHASE-1 OUTPUT OF THE REAL BLOCK.** `wrapPhase1` is
`MinaRealBlockTranscript`'s run of the upstream `DefaultFqSponge` state machine over the block's own
commitment coordinates, and its five outputs are the values `proof.oracles(...)` returned on Mina
devnet block 539508. Every one of them is a lane of this chain. -/
theorem the_chain_is_the_blocks_phase1_transcript :
    ((chainState 19).getD 0 0 % 2 ^ 128
    , (chainState 19).getD 1 0 % 2 ^ 128
    , (chainState 20).getD 0 0 % 2 ^ 128
    , (chainState 27).getD 0 0 % 2 ^ 128
    , (chainState 27).getD 1 0) = wrapPhase1 := by
  native_decide

/-- ⚑⚑ **AND THE 27th LINK'S SECOND OUTGOING LANE IS `fq_digest`** — the element phase 2's tape
starts with. Stated on its own because it is the one this whole file exists for. -/
theorem the_chain_ends_on_the_fq_digest : (chainState 27).getD 1 0 = FQ_DIGEST := by native_decide

/-- Non-vacuity of the CHAIN, not of the reference sponge: perturbing the head of the tape — the
verifier-index digest, absorbed by link 0 and twenty-seven permutations away from the answer — moves
the digest. So the chain carries state end to end rather than re-deriving the tail. -/
theorem a_tampered_tape_head_moves_the_digest :
    (let lx : Nat → Nat × Nat := fun j => if j = 0 then (0, (linkX 0).2) else linkX j
     let st : Nat → List Nat := fun n => Nat.rec ([0, 0, 0] : List Nat)
       (fun j ih => linkStepOf fpParams ih (lx j)) n
     (st 27).getD 1 0) ≠ FQ_DIGEST := by
  native_decide

/-- …and so does perturbing a WITNESS-COMMITMENT coordinate in the middle of the tape — link 10's
first slot is `fpTape[20]`. A control that only ever moves the head would not show the middle of the
tape is inside the digest.

⚠ **THE FIRST DRAFT OF THIS FALSIFIER DID NOT FALSIFY**, and `native_decide` said so: it aimed at
link 18's SECOND slot, which is the odd tail's padding `0` — moving a zero into a zero. The refuted
draft is the useful part; the tamper below moves a value that is actually on the tape, which
`the_tamper_target_is_a_real_tape_element` checks rather than assumes. -/
theorem a_tampered_witness_coordinate_moves_the_digest :
    (let lx : Nat → Nat × Nat := fun j => if j = 10 then (0, (linkX 10).2) else linkX j
     let st : Nat → List Nat := fun n => Nat.rec ([0, 0, 0] : List Nat)
       (fun j ih => linkStepOf fpParams ih (lx j)) n
     (st 27).getD 1 0) ≠ FQ_DIGEST := by
  native_decide

/-- ⚑ **AND THE TAMPER TARGETS ARE NON-ZERO TAPE ELEMENTS.** Both controls above set a slot to `0`;
if that slot were already `0` the control would be a tautology about an unchanged chain. Link 0's
first slot is the verifier-index digest and link 10's is a witness-commitment coordinate — checked,
not assumed, because the first draft of the second control was exactly that tautology. -/
theorem the_tamper_targets_are_real_tape_elements :
    (linkX 0).1 ≠ 0 ∧ (linkX 10).1 ≠ 0
    ∧ (linkX 0).1 = fpTape.getD 0 0 ∧ (linkX 10).1 = fpTape.getD 20 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-! ## §5 — THE EMITTED PHASE-1 CHAIN-LINK DESCRIPTOR.

⚑ **EIGHT pin blocks, 256 public inputs**, the SAME layout `MinaPhase2Chain.chainPins` deploys:
`in(3) ++ out(3) ++ absorbed(2)`, so `in ++ out` is the contiguous slice `[0, 6·SK)` a recursion
leaf re-exposes in one piece and the absorbed pair is `[6·SK, 8·SK)`.

⚠ **THREE LANES, NOT TWO.** The seven-block `pasta-fq-wraplink` descriptor pinned only two of a
Poseidon state's three outgoing lanes, so a chain welded on it would hand a third of its state on as
a free prover scalar. Phase 1 needs all three for a second reason: **the digest is lane 1** and γ is
lane 1, so a two-lane descriptor could not even state this file's result. -/

def CHAIN_PI_COUNT : Nat := 8 * SK

theorem CHAIN_PI_COUNT_eq : CHAIN_PI_COUNT = 256 := rfl

def chainAir : EffectAir :=
  { programAir pLimb fpAbsorbProg with
    legs := (programAir pLimb fpAbsorbProg).legs ++ MinaPhase2Chain.chainPins }

/-- ⚑ **THE PIN LAYOUT IS THE DEPLOYED ONE, NOT A COPY.** `chainPins` is
`MinaPhase2Chain.chainPins` itself — the pins are column/PI indices and carry no field, so the two
phases genuinely share one boundary. -/
theorem the_pin_layout_is_the_deployed_one :
    chainAir.legs = (programAir pLimb fpAbsorbProg).legs ++ MinaPhase2Chain.chainPins := rfl

theorem chainAir_mainRailOk : chainAir.mainRailOk = true := by
  unfold chainAir EffectAir.mainRailOk
  simp only [List.all_append, Bool.and_eq_true]
  refine ⟨programAir_mainRailOk pLimb fpAbsorbProg, ?_⟩
  simp only [MinaPhase2Chain.chainPins, pinBlock, List.all_append, List.all_map, Bool.and_eq_true,
    List.all_eq_true]
  repeat' apply And.intro
  all_goals (intro _ _; rfl)

/-- ⚑ **THE EMITTED PHASE-1 CHAIN-LINK DESCRIPTOR.** ONE descriptor for all 27 links. -/
def chainDesc : EffectVmDescriptor2 :=
  lowerAir "dregg-pasta-fp-chainlink::v1" PROG_WIDTH CHAIN_PI_COUNT [] chainAir

/-! ## §6 — THE 27 WITNESSES. -/

def inBlock (j : Nat) : List ℤ :=
  (List.range SK).map (limbAt ((chainState j).getD 0 0))
    ++ (List.range SK).map (limbAt ((chainState j).getD 1 0))
    ++ (List.range SK).map (limbAt ((chainState j).getD 2 0))

/-- The OUTGOING-state block — read from the interpreter's own final register file, never from the
reference. -/
def outBlock (j : Nat) : List ℤ :=
  (List.range SK).map (limbAt ((chainOut j).getD 0 0))
    ++ (List.range SK).map (limbAt ((chainOut j).getD 1 0))
    ++ (List.range SK).map (limbAt ((chainOut j).getD 2 0))

def absorbedBlock (j : Nat) : List ℤ :=
  (List.range SK).map (limbAt (linkX j).1) ++ (List.range SK).map (limbAt (linkX j).2)

def chainPIs (j : Nat) : List ℤ := inBlock j ++ outBlock j ++ absorbedBlock j

theorem chainPIs_length (j : Nat) : (chainPIs j).length = 256 := by
  simp [chainPIs, inBlock, outBlock, absorbedBlock, SK]

/-- ⚑⚑ **CONTINUITY IN THE EMITTED CLAIMS.** Link `j`'s outgoing PI block IS link `j+1`'s incoming
PI block, limb for limb — a corollary of the kernel-clean step theorem, so it holds at every `j`.
This is the equality the fold's `cb.connect` enforces in-circuit. -/
theorem the_emitted_claims_are_continuous (j : Nat) : outBlock j = inBlock (j + 1) := by
  simp only [outBlock, inBlock, the_chain_step_is_the_kimchi_permutation]

def chainTrace (j : Nat) : List (List ℤ) :=
  runRowsVecAt pN pLimb (chainInitVec j) 0 fpAbsorbProg

/-- ⚑ **AND EVERY EMITTED TRACE IS `runRowsAt`'s** — the object every denotation above is a
statement about, at every link. -/
theorem chainTrace_is_the_program_run (j : Nat) :
    chainTrace j = runRowsAt pN pLimb (regsOf (chainInitVec j)) 0 fpAbsorbProg := by
  rw [chainTrace, runRowsVecAt_is_runRowsAt]

/-! ## §7 — ⚑⚑ THE WELD: PHASE-1's DIGEST IS PHASE-2's TAPE HEAD.

This is the point of the leg. Phase 2's chain begins by absorbing `WRAP_TAPE2[0]`; phase 1's chain
ends by producing it in outgoing lane 1 of link 26. Both are published as 32 eight-bit limbs, so
the tie is a slice comparison with **no arithmetic, no digest and no birthday bound**. -/

/-- The index of the link whose OUTGOING lane 1 is the digest — the last one. -/
def DIGEST_LINK : Nat := 26

/-- ⚑ **THE VALUE TIE.** Link 26's second outgoing lane is the first element of the phase-2 tape.
The only compiled step; everything below is kernel, rewritten through it. -/
theorem the_phase1_digest_is_the_phase2_tape_head :
    (chainOut DIGEST_LINK).getD 1 0 = MinaBlockFqTranscript.WRAP_TAPE2.getD 0 0 := by
  rw [the_chain_step_is_the_kimchi_permutation]
  exact the_chain_ends_on_the_fq_digest

/-- ⚑⚑ **THE WIRE TIE, ELEMENTWISE AT FULL LIMB WIDTH.** The 32 felts phase 1 publishes at PI slots
`[4·SK, 5·SK)` ARE the 32 felts phase 2 publishes at `[6·SK, 7·SK)`. A batch verifier compares two
slices; it does no arithmetic and it hashes nothing, so there is no collision bound to state — a
forger must match all 32 limbs of a 254-bit value.

⚑ Kernel-clean: `congrArg` over the one compiled value equality above. -/
theorem the_wire_slice_is_the_outgoing_second_lane (j : Nat) :
    ((chainPIs j).drop (4 * SK)).take SK
      = (List.range SK).map (limbAt ((chainOut j).getD 1 0)) := rfl

/-- …and phase 2's `[6·SK, 7·SK)` slice is its first ABSORBED element, which is the tape head. -/
theorem the_phase2_wire_slice_is_the_tape_head :
    ((MinaPhase2Chain.chainPIs 0).drop (6 * SK)).take SK
      = (List.range SK).map (limbAt (MinaBlockFqTranscript.WRAP_TAPE2.getD 0 0)) := rfl

theorem the_wire_blocks_are_equal :
    ((chainPIs DIGEST_LINK).drop (4 * SK)).take SK
      = ((MinaPhase2Chain.chainPIs 0).drop (6 * SK)).take SK := by
  rw [the_wire_slice_is_the_outgoing_second_lane, the_phase2_wire_slice_is_the_tape_head,
    the_phase1_digest_is_the_phase2_tape_head]

/-- ⚑ **AND THE TIE IS NOT VACUOUS.** The block is 32 felts, it is not the zero vector, and it is
not the block phase 2's OTHER absorbed slot carries — so `the_wire_blocks_are_equal` is an equality
between two things that could have differed, not two copies of a constant. -/
theorem the_wire_block_is_not_trivial :
    (((chainPIs DIGEST_LINK).drop (4 * SK)).take SK).length = 32
    ∧ ((chainPIs DIGEST_LINK).drop (4 * SK)).take SK ≠ List.replicate 32 (0 : ℤ)
    ∧ ((chainPIs DIGEST_LINK).drop (4 * SK)).take SK
        ≠ ((MinaPhase2Chain.chainPIs 0).drop (7 * SK)).take SK := by
  native_decide

/-- ⚑ **A ONE-FELT TIE WOULD BE `2^31`, AND THIS IS NOT ONE.** Stated as arithmetic so the strength
claim is checkable rather than asserted: the wire block carries `SK` felts of `SB` bits each, which
is the whole 254-bit element — every limb is on the wire, so a forger who changes the digest must
change at least one published felt. -/
theorem the_tie_is_the_whole_element :
    SK * PastaFieldSound.SB = 256 ∧ 2 ^ 254 < pN ∧ pN < 2 ^ (SK * PastaFieldSound.SB) := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-! ## §8 — RESIDUALS, NAMED.

1. **The coordinates are not checked to be commitments.** Nothing here says a `(x, y)` pair is on
   the curve, that `public_comm` commits to the 40-element public input, or that a
   `RecursionChallenge`'s `comm` is `⟨b_poly_coefficients(chals), G⟩`. Phase 1 derives `fq_digest`
   FROM those coordinates; it does not authenticate them.
2. **The verifier-index digest is an input.** It is itself a sponge over every commitment of the
   Wrap VK (`verifier_index.rs:399-450`) and is absorbed here as a value.
3. **The endomorphism lifts are not on the machine.** β and γ are used raw, but α′/ζ′ reach the gate
   through `ScalarChallenge::to_field`, which is `MinaWrapXiEndoLift`'s business.
4. **`pack_to_fields` is not here and does not need to be.** Phase 1 absorbs WHOLE field elements
   (`absorb_g` pushes `x` then `y`); the chunked `Random_oracle.Input` packing belongs to the
   STATE-HASH derivation (`Bridge.MinaStateHashDerive`), a different preimage. Its price is in that
   file's §1 and in `docs/`, and it is 3.7% of the permutation cost of the object it belongs to.
5. **27 witnesses, one descriptor.** As with phase 2, the residual is witnesses, not algebra.
-/

#assert_axioms round_output_is_canonical
#assert_axioms round_output_has_three_lanes
#assert_axioms perm_output_is_canonical
#assert_axioms linkStepOf_is_canonical
#assert_axioms absorb1_partial
#assert_axioms absorb1_full
#assert_axioms squeeze1_absorbed_state
#assert_axioms absorbAt_lane0
#assert_axioms absorbAt_lane1
#assert_axioms linkStepOf_triple
#assert_axioms linkStepOf_fp
#assert_axioms the_pairs_are_the_absorb_schedule
#assert_axioms the_chain_is_twenty_seven_links
#assert_axioms the_chain_starts_fresh
#assert_axioms the_chain_step_is_the_kimchi_permutation
#assert_axioms CHAIN_PI_COUNT_eq
#assert_axioms the_pin_layout_is_the_deployed_one
#assert_axioms chainAir_mainRailOk
#assert_axioms chainPIs_length
#assert_axioms the_emitted_claims_are_continuous
#assert_axioms chainTrace_is_the_program_run
#assert_axioms the_tie_is_the_whole_element
#assert_axioms the_tamper_targets_are_real_tape_elements
#assert_axioms the_wire_slice_is_the_outgoing_second_lane
#assert_axioms the_phase2_wire_slice_is_the_tape_head

-- ⚑ COMPILER-TRUSTED, and said out loud: each is up to 27 Kimchi permutations of a 255-bit state,
-- where the `decide` proof-term path overflows.
#assert_compiled the_chain_absorbs_the_tape_in_order
#assert_compiled the_chain_is_the_blocks_phase1_transcript
#assert_compiled the_chain_ends_on_the_fq_digest
#assert_compiled a_tampered_tape_head_moves_the_digest
#assert_compiled a_tampered_witness_coordinate_moves_the_digest
#assert_compiled the_wire_block_is_not_trivial
-- …and the two welds, which INHERIT the compiled fact they are rewritten through.
#assert_compiled the_phase1_digest_is_the_phase2_tape_head
#assert_compiled the_wire_blocks_are_equal

end Dregg2.Circuit.Emit.MinaPhase1Chain
