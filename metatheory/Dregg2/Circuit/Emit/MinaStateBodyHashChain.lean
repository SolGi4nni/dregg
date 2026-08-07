/-
# `Dregg2.Circuit.Emit.MinaStateBodyHashChain` — **`BODYHASH` STOPS BEING A PROVER-CHOSEN VALUE.**

## ⚑ SAY THE SUBSTRATE OUT LOUD

**This is Lean-authored AIR, and it authors NO NEW AIR.** `bodyChainDesc` **is**
`MinaPhase1Chain.chainDesc` — `dregg-pasta-fp-chainlink::v1`, by `rfl`
(`the_descriptor_is_the_deployed_phase1_link`). Same 2 048 instructions, same 469 columns, same
`chainPins` layout, same `fp_kimchi` ROM. Twenty-five more witnesses, not a twenty-sixth descriptor.
Rust proves the artifacts and authors no constraint. House Law #1.

## ⚑⚑ THE HOLE THIS CLOSES

`LightClientMinaLinkAir` derived `OWNHASH` on 2026-08-06 and named what was left in the same breath:

> *"**WHAT IT CAN STILL CHOOSE IS `BODYHASH`** … `state_body_hash`'s own preimage (~38 field
> elements under a second salt) is **the next rung**."*

This is that rung. `BODYHASH` is now the terminal lane 0 of a 25-link chain whose head state is the
`MinaProtoStateBody` salt and whose absorbed stream is the block body's own packed preimage.

## ⚑ THE PRICE, RE-DERIVED — AND THE INHERITED FIGURE WAS OFF BY ONE

The standing number was **26 permutations** (`MinaStateHashPackPrice.PERMS_FOR_BODY`, written
`(49 + 1) / 2 + 1`). It is **25**, and the `+ 1` is a double-counted squeeze:

  * `Body.to_input` on the real devnet block is 38 whole field elements + 819 packed chunks
    (2 381 bits), packing to **49** field elements (`the_preimage_packs_to_49_field_elements`).
  * ⚑ The upstream absorb loop permutes **only when an element ARRIVES and finds the rate full**
    (`PastaPoseidonFq.Core.absorbFrom`, the lane-counter transcription). A final partial block is
    left unpermuted and the **squeeze supplies its permutation** — it does not add one after a
    completed block. So 49 elements are `⌈49/2⌉ = 25` rate blocks and **25 permutations**, not
    25 + 1.
  * ⚑ **And it is derived, not counted.** `pairsOf_length` proves `(pairsOf xs).length =
    (xs.length + 1) / 2` at every list, and `the_pairs_are_the_absorb_schedule`
    (`MinaPhase1Chain`, general over every `Params` and every segment) proves that pairing IS the
    upstream state machine's. `the_body_chain_is_twenty_five_links` instantiates both.

⚠ The off-by-one is exactly the shape `PastaPoseidon`'s §5 warns about — the double-permute bug the
absorb loop was restructured to make inexpressible in 2026-07-27. It survived in a *price* because a
price is arithmetic nobody runs the sponge for. `MinaStateHashPackPrice.PERMS_FOR_BODY` is corrected
and `the_price_files_count_is_the_schedules` welds the two files so they cannot drift apart again.

## ⚑ AND THE 26 THAT WAS RIGHT WAS ABOUT A DIFFERENT OBJECT

`LightClientMinaLinkAir`'s header records that the *state-hash* chain's "~26 permutations a block"
was the **transcript** chain's link count. That correction stands. What this file adds is that the
`26` is not the body hash's count either: the body hash is **25**, and the two numbers being one
apart is a coincidence of `⌈49/2⌉` against 27-minus-one, not a shared derivation.

## THE CHAIN

    bodyChainState 0   = salt "MinaProtoStateBody"          -- ⚑ NOT a prover-chosen head
    bodyChainState j+1 = perm( bodyChainState j + [x₂ⱼ, x₂ⱼ₊₁, 0] )
    stateBodyHash ps   = (bodyChainState 25).getD 0 0       -- the_body_chain_derives_the_body_hash

Every step is `perm(state + [a, b, 0])` — **exactly the shape `fpAbsorbProg` computes**, which is
why one descriptor serves 27 phase-1 links, 28 VK-digest links and these 25.

## ⚑ WHAT BINDS THE BODY — SAID PLAINLY, BECAUSE THE HONEST ANSWER IS PARTIAL

A `BODYHASH` derived from a preimage the prover also chooses would be *"the same vacuity one layer
down"*. It is not that, and it is not fully closed either. Three things are true and each is a
theorem below rather than a paragraph:

1. ⚑ **The head is not free.** `bodyChainState 0` is `saltProtoStateBody`, which is itself pinned to
   openmina's own regression constants. `the_body_chain_head_is_the_protocol_state_body_salt` and
   `the_body_salt_is_not_the_state_salt` say so. A free head makes the whole chain vacuous — `perm`
   is a permutation, so any target is reachable by choosing the head — and that is the trap the
   sibling rung's `.const` salt lanes close for `state_hash`. Here the head is a PI and the
   consumer compares it against the salt's limbs; the comparison is a slice, not arithmetic.

2. ⚑ **The absorbed stream is not free either — each link commits to its own absorbed pair**, and
   the fold's ordered accumulator is compared host-side against the block's real packed preimage.
   `the_body_chain_absorbs_the_preimage_in_order` is the statement that comparison is about.

3. ⚠ **AND WHAT MOVED IS THE CHOICE, NOT ITS DISAPPEARANCE.** Nothing here says the 49 packed field
   elements are a Mina block body — no gate relates them to a `Protocol_state.Body`'s wire bytes,
   and no gate relates them to the block whose `PARENT`/`HEIGHT` the link rung carries. **The value
   a prover chooses moved from one felt (`BODYHASH`) to its 2 381-bit preimage** — which is 819
   width-declared chunks and 38 whole elements, each of which the *daemon's* consensus rules
   constrain and *this* circuit does not. That is progress of a specific kind: the preimage's fields
   are now individually addressable by a gate, where a felt was not. It is not the claim that a body
   is real. That remains `PICKLES_OPENING_WITNESSED`.

## Import line for the root: `import Dregg2.Circuit.Emit.MinaStateBodyHashChain`
-/
import Dregg2.Circuit.Emit.MinaPhase1Chain
import Dregg2.Bridge.MinaStateHashPackPrice

namespace Dregg2.Circuit.Emit.MinaStateBodyHashChain

open Dregg2.Circuit.DescriptorIR2 (EffectVmDescriptor2)
open Dregg2.Circuit.Emit.PastaField (pN)
open Dregg2.Circuit.Emit.PastaFieldSound (SK limbAt pLimb)
open Dregg2.Circuit.Emit.MinaWrapVerifierProgram
open Dregg2.Circuit.Emit.MinaWrapVerifierSponge
open Dregg2.Circuit.Emit.MinaWrapVerifierSpongeFp
open Dregg2.Circuit.Emit.PastaPoseidonFq (Params fpParams)
open Dregg2.Circuit.Emit.MinaPhase1Chain (pairsOf linkStepOf perm_output_is_canonical
  absorb1_partial absorb1_full squeeze1_absorbed_state the_pairs_are_the_absorb_schedule)
open Dregg2.Bridge.MinaBinprot (decodeProtocolStateRaw)
open Dregg2.Bridge.MinaStateHashDerive
open Dregg2.Bridge.MinaStateHashRealBlock (devnetParent)

set_option autoImplicit false
-- ⚑ A `set_option` does not cross an import; these reductions are the 1 544-byte binprot parse, a
-- two-block SHA-256 and up to 25 Kimchi permutations.
set_option maxRecDepth 4000000

/-! ## §1 — ⚑ THE PRICE, DERIVED FROM THE ACTUAL PACKING SCHEDULE.

Two facts, and the first is GENERAL: it is about `pairsOf` at every list, so the 25 below is an
instance of a law rather than a count of a printout. -/

/-- ⚑⚑ **`pairsOf` EMITS `⌈n/2⌉` PAIRS.** The rate-2 sponge's own chunking, counted once and for
all: an odd tail contributes ONE pair whose second slot is the padding zero the lane counter already
implies. This is the theorem that turns every chain length in this cone — 19, 1, 7, 28, and the 25
below — into a derivation from a segment length. -/
theorem pairsOf_length : ∀ xs : List Nat, (pairsOf xs).length = (xs.length + 1) / 2 := by
  intro xs
  induction xs using pairsOf.induct with
  | case1 => simp [pairsOf]
  | case2 _ => simp [pairsOf]
  | case3 _ _ rest ih => simp only [pairsOf, List.length_cons, ih]; omega

/-- The block body's packed preimage — `Random_oracle.pack_input (Body.to_input body)` on the real
devnet block (540221), decoded from its own wire bytes. ⚑ Not re-transcribed:
`MinaStateHashPackPrice.bodyInput` is the object that file already measured at 38 fields and 819
chunks. -/
def bodyPacked : List Nat :=
  packToFields Dregg2.Bridge.MinaStateHashPackPrice.bodyInput

/-- ⚑ **49 FIELD ELEMENTS**, and ⚑ **IN THE KERNEL.** `MinaStateHashPackPrice`'s own measurement of
this number is `native_decide` — right for a per-width tally over 819 chunks, wrong to inherit here,
because the link count below is the whole point of this file and a compiled premise would make the
derived 25 compiler-trusted. This is the same object at kernel resolution: the 1 544-byte binprot
parse, the two-block SHA-256 and the 819-chunk assembly, with no Poseidon in it. -/
theorem the_preimage_is_forty_nine_field_elements : bodyPacked.length = 49 := by decide

/-- The absorbed pairs of the body preimage, in `Body.to_input` order. -/
def bodyLinkXs : List (Nat × Nat) := pairsOf bodyPacked

/-- The number of permutations a `state_body_hash` costs. -/
def BODY_LINKS : Nat := 25

/-- ⚑⚑ **TWENTY-FIVE LINKS, DERIVED — AND THE STANDING FIGURE WAS 26.** `pairsOf_length` at 49.
The inherited `(49 + 1) / 2 + 1` added a permutation for the closing squeeze; the squeeze is the
permutation of the LAST partial block, not an extra one after it, which is what
`Core.absorbFrom`'s `[]` clause says and what `the_pairs_are_the_absorb_schedule` proves. -/
theorem the_body_chain_is_twenty_five_links : bodyLinkXs.length = BODY_LINKS := by
  rw [bodyLinkXs, pairsOf_length, the_preimage_is_forty_nine_field_elements]
  decide

/-- ⚑ **AND THE TWO FILES AGREE BY THEOREM, NOT BY TRANSCRIPTION.** The price file's corrected
permutation count IS this chain's link count. A future edit that moves one without the other goes
red here. -/
theorem the_price_files_count_is_the_schedules :
    Dregg2.Bridge.MinaStateHashPackPrice.PERMS_FOR_BODY = bodyLinkXs.length := by
  rw [the_body_chain_is_twenty_five_links]; decide

def bodyLinkX (j : Nat) : Nat × Nat := bodyLinkXs.getD j (0, 0)

/-! ## §2 — ⚑ THE HEAD IS THE SALT, AND THAT IS THE LOAD-BEARING PART.

⚠ With a FREE incoming state the whole chain is vacuous and not weakly so: `perm` is a permutation,
so for any target a prover picks a head that reaches it. The sibling rung closes this for
`state_hash` by making the salt lanes descriptor `.const`s; here the head is link 0's incoming PI
block and the consumer compares it against the salt's limbs — a slice comparison, no arithmetic. -/

/-- ⚑ **THE HEAD.** `Random_oracle.salt "MinaProtoStateBody"`, which
`Bridge.MinaStateHashDerive` §3 pins to openmina's OWN regression constants
(`poseidon/tests/test_hash_params.rs:28-51`). -/
def bodySalt : List Nat := saltProtoStateBody

/-- The salt is one permutation of the padded prefix — so it is a canonical three-lane state, which
is the hypothesis the schedule theorem needs. Stated through `Core.perm` so the unifier never opens
a 55-round permutation. -/
theorem the_body_salt_is_one_permutation :
    bodySalt = Dregg2.Circuit.Emit.PastaPoseidonFq.Core.perm fpParams
      (Dregg2.Circuit.Emit.PastaPoseidonFq.Core.absorbAt fpParams [0, 0, 0] 0
        (prefixField "MinaProtoStateBody")) := rfl

theorem the_body_salt_is_a_canonical_state :
    bodySalt.length = 3 ∧ ∀ v ∈ bodySalt, v < pN := by
  rw [the_body_salt_is_one_permutation]
  obtain ⟨hc, hl⟩ := perm_output_is_canonical fpParams (by decide) _
  exact ⟨hl, hc⟩

/-- ⚑ **AND IT IS NOT THE OTHER SALT.** Mina's whole domain separation between a body hash and a
state hash rests on this, and a chain welded on the wrong one would compute a different chain's
hash function with every gate green. -/
theorem the_body_salt_is_not_the_state_salt : bodySalt ≠ saltProtoState :=
  fun h => the_two_salts_differ h.symm

/-- …and it is not the fresh sponge either, which is the head every OTHER chain in this cone starts
from. A copy-paste that forgot the salt would land exactly there. -/
theorem the_body_salt_is_not_the_fresh_sponge :
    bodySalt ≠ Dregg2.Circuit.Emit.PastaPoseidonFq.newSponge.st := by native_decide

/-! ## §3 — THE CHAIN STATE, AND ITS TERMINAL IS MINA'S OWN `state_body_hash`. -/

/-- ⚑ **THE CHAIN STATE.** `bodyChainState j` is the sponge state entering link `j`. -/
def bodyChainState : Nat → List Nat
  | 0 => bodySalt
  | (j + 1) => linkStepOf fpParams (bodyChainState j) (bodyLinkX j)

theorem the_body_chain_head_is_the_protocol_state_body_salt :
    bodyChainState 0 = saltProtoStateBody := rfl

/-- ⚑ **THE RECURSION IS A PREFIX FOLD** — the bridge that lets the general schedule theorem apply
to the recursion the machine actually runs. -/
theorem the_body_chain_is_the_prefix_fold (n : Nat) (h : n ≤ BODY_LINKS) :
    bodyChainState n = (bodyLinkXs.take n).foldl (linkStepOf fpParams) bodySalt := by
  induction n with
  -- ⚠ `List.take_zero` by NAME, not `rfl`: the matcher for `take` splits on the LIST, so a bare
  -- `rfl` whnfs `bodyLinkXs` and drags the whole binprot parse through the elaborator.
  | zero => rw [List.take_zero, List.foldl_nil]; rfl
  | succ k ih =>
    have hk : k < bodyLinkXs.length := by
      rw [the_body_chain_is_twenty_five_links]; omega
    -- ⚠ Stated as an explicit rewrite chain rather than a `simp`: `bodyLinkXs` is
    -- `pairsOf (packToFields bodyInput)`, so any tactic that tries to EVALUATE it drags the
    -- 1 544-byte binprot parse and the 819-chunk assembly through `whnf` and times out.
    have hget : bodyLinkX k = bodyLinkXs[k] := by
      rw [bodyLinkX, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]; rfl
    have hstep : bodyChainState (k + 1)
        = linkStepOf fpParams (bodyChainState k) (bodyLinkX k) := rfl
    rw [hstep, ih (by omega), List.take_add_one, List.foldl_append,
      List.getElem?_eq_getElem hk, Option.toList_some, List.foldl_cons, List.foldl_nil, hget]

/-- ⚑ **THE SPONGE STATE MACHINE'S SQUEEZE IS THE ABSORB LOOP'S `[]` CLAUSE.** `absorbMany` then
`squeeze1` IS `Core.absorbFrom` at the same lane counter, at every parameter set, every input and
every counter — so `MinaStateHashDerive`'s `hashFrom` (which is `Ref.absorbFrom`) and this cone's
chain schedule are ONE function, not two spellings that happen to agree on 49 elements. -/
theorem squeeze_of_absorbMany_is_absorbFrom (P : Params) :
    ∀ (xs s : List Nat) (n : Nat),
      (Dregg2.Circuit.Emit.PastaPoseidonFq.squeeze1 P
          (Dregg2.Circuit.Emit.PastaPoseidonFq.absorbMany P
            ⟨s, Dregg2.Circuit.Emit.PastaPoseidonFq.Mode.absorbed n⟩ xs)).1.st
        = Dregg2.Circuit.Emit.PastaPoseidonFq.Core.absorbFrom P s n xs := by
  intro xs
  induction xs with
  | nil => intro s n; exact squeeze1_absorbed_state P s n
  | cons x rest ih =>
    intro s n
    have hstep : Dregg2.Circuit.Emit.PastaPoseidonFq.absorbMany P
        ⟨s, Dregg2.Circuit.Emit.PastaPoseidonFq.Mode.absorbed n⟩ (x :: rest)
        = Dregg2.Circuit.Emit.PastaPoseidonFq.absorbMany P
            (Dregg2.Circuit.Emit.PastaPoseidonFq.absorb1 P
              ⟨s, Dregg2.Circuit.Emit.PastaPoseidonFq.Mode.absorbed n⟩ x) rest := by
      rw [Dregg2.Circuit.Emit.PastaPoseidonFq.absorbMany,
        Dregg2.Circuit.Emit.PastaPoseidonFq.absorbMany, List.foldl_cons]
    rw [hstep]
    by_cases h : n = PastaPoseidon.rate
    · subst h
      rw [absorb1_full, ih]
      simp [Dregg2.Circuit.Emit.PastaPoseidonFq.Core.absorbFrom]
    · rw [absorb1_partial P s n x h, ih]
      simp [Dregg2.Circuit.Emit.PastaPoseidonFq.Core.absorbFrom, h]

/-- ⚑ `MinaStateHashDerive.hashFrom` IS the parametric core at `fpParams` — the anti-drift bridge
`PastaPoseidonFq.absorbFrom_at_fp` provides, applied at the shape this file needs. -/
theorem hashFrom_is_the_core (st xs : List Nat) :
    hashFrom st xs
      = (Dregg2.Circuit.Emit.PastaPoseidonFq.Core.absorbFrom fpParams st 0 xs).getD 0 0 := by
  rw [Dregg2.Circuit.Emit.PastaPoseidonFq.absorbFrom_at_fp]; rfl

/-- ⚑⚑ **THE TERMINAL LANE 0 IS MINA'S OWN `state_body_hash`, AT EVERY BODY.** General over the
protocol state: the chain this file runs and `Bridge.MinaStateHashDerive.stateBodyHash` are the same
function of the same preimage, by the sponge's own schedule. No block-specific evaluation. -/
theorem the_fold_is_the_state_body_hash (xs s : List Nat)
    (hne : xs ≠ []) (h3 : s.length = 3) (hc : ∀ v ∈ s, v < pN) :
    ((pairsOf xs).foldl (linkStepOf fpParams) s).getD 0 0 = hashFrom s xs := by
  rw [hashFrom_is_the_core, ← squeeze_of_absorbMany_is_absorbFrom fpParams xs s 0,
    the_pairs_are_the_absorb_schedule fpParams (by decide) xs s hne h3 hc]

/-- ⚑⚑⚑ **`BODYHASH` IS THE CHAIN'S TERMINAL LANE 0.** The value the link rung carried as a free
witness nonet is the 25th permutation's lane 0, from the pinned salt over the block's own packed
preimage. -/
theorem the_body_chain_derives_the_body_hash :
    (bodyChainState BODY_LINKS).getD 0 0 = hashFrom saltProtoStateBody bodyPacked := by
  rw [the_body_chain_is_the_prefix_fold BODY_LINKS le_rfl,
    List.take_of_length_le (le_of_eq the_body_chain_is_twenty_five_links)]
  refine the_fold_is_the_state_body_hash bodyPacked bodySalt ?_
    the_body_salt_is_a_canonical_state.1 the_body_salt_is_a_canonical_state.2
  have h49 := the_preimage_is_forty_nine_field_elements
  intro h
  rw [h] at h49
  simp at h49

/-- The real devnet block's `state_body_hash`, as `MinaStateHashDerive` computes it. -/
def realBodyHash : Nat :=
  match decodeProtocolStateRaw devnetParent with
  | some (ps, _) => stateBodyHash ps
  | none => 0

/-- ⚑ **AND ON THE REAL BLOCK, THE CHAIN LANDS ON THE DAEMON'S VALUE.** `realBodyHash` feeds
`stateHash`, whose derivation from these same bytes IS the hash the Mina chain recorded
(`MinaStateHashRealBlock.the_derived_state_hash_is_the_one_the_chain_recorded`, block
540221 → 540222). So the reality gate on the ORDER covers this chain's absorbed stream too. -/
theorem the_body_chain_lands_on_the_real_blocks_body_hash :
    (bodyChainState BODY_LINKS).getD 0 0 = realBodyHash := by
  rw [the_body_chain_derives_the_body_hash]; native_decide

/-- ⚑ **AND THE VALUE IS NOT DEGENERATE.** A terminal that was `0`, or that coincided with the
block's `previous_state_hash`, would make the tie below satisfiable by an object nobody computed. -/
theorem the_real_body_hash_is_not_trivial :
    realBodyHash ≠ 0 ∧ realBodyHash < pN
      ∧ realBodyHash ≠ Dregg2.Bridge.MinaStateHashRealBlock.childPreviousStateHash := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

/-! ## §4 — THE MACHINE COMPUTES THE CHAIN STEP, AT EVERY LINK.

The SAME `fpAbsorbCore` program, the SAME `allocAt` read, the SAME kernel-clean generic theorem the
phase-1 and VK-digest chains rest on. -/

def bodyChainInitVec (j : Nat) : List Nat :=
  [ (bodyChainState j).getD 0 0, (bodyChainState j).getD 1 0, (bodyChainState j).getD 2 0
  , (bodyLinkX j).1, (bodyLinkX j).2, 0 ]

def bodyChainOutVec (j : Nat) : List Nat := runProgVecAt pN (bodyChainInitVec j) fpAbsorbCore

/-- The three outgoing state lanes, read from `allocAt 55 = (4, 5, 0)`. Computed by the
interpreter; never asserted. -/
def bodyChainOut (j : Nat) : List Nat :=
  [ regsOf (bodyChainOutVec j) (allocAt PastaPoseidon.rounds 0)
  , regsOf (bodyChainOutVec j) (allocAt PastaPoseidon.rounds 1)
  , regsOf (bodyChainOutVec j) (allocAt PastaPoseidon.rounds 2) ]

/-- ⚑⚑ **THE LINK'S MACHINE OUTPUT IS THE NEXT LINK'S INPUT — AT EVERY `j`, WITH NO HYPOTHESES.**
An instance of `MinaWrapVerifierSpongeFp.the_absorb_program_permutes_gen` at `fpParams`, so the
whole chain rests on ONE kernel-clean theorem rather than on 25 checked points. -/
theorem the_body_chain_step_is_the_kimchi_permutation (j : Nat) :
    bodyChainOut j = bodyChainState (j + 1) := by
  have hregs : regsOf (bodyChainOutVec j) = runProgAt pN (regsOf (bodyChainInitVec j)) fpAbsorbCore := by
    rw [bodyChainOutVec, regsOf_runProgVecAt]
  have h0 : regsOf (bodyChainInitVec j) 0 = (bodyChainState j).getD 0 0 := rfl
  have h1 : regsOf (bodyChainInitVec j) 1 = (bodyChainState j).getD 1 0 := rfl
  have h2 : regsOf (bodyChainInitVec j) 2 = (bodyChainState j).getD 2 0 := rfl
  have h3 : regsOf (bodyChainInitVec j) 3 = (bodyLinkX j).1 := rfl
  have h4 : regsOf (bodyChainInitVec j) 4 = (bodyLinkX j).2 := rfl
  have hperm := the_fp_absorb_program_permutes (regsOf (bodyChainInitVec j))
  rw [h0, h1, h2, h3, h4] at hperm
  show [ regsOf (bodyChainOutVec j) (allocAt PastaPoseidon.rounds 0)
       , regsOf (bodyChainOutVec j) (allocAt PastaPoseidon.rounds 1)
       , regsOf (bodyChainOutVec j) (allocAt PastaPoseidon.rounds 2) ] = bodyChainState (j + 1)
  rw [hregs, hperm]
  show _ = linkStepOf fpParams (bodyChainState j) (bodyLinkX j)
  rw [Dregg2.Circuit.Emit.MinaPhase1Chain.linkStepOf_fp]

/-! ## §5 — ⚑ THE EMITTED DESCRIPTOR: THE DEPLOYED ONE, UNCHANGED.

## ⚑ WHY `pasta-fp-chainlink` AND NOT `pasta-fp-absorb`, WHICH IS THE ONE THE SEAM PINS

Both are `programAir pLimb fpAbsorbProg` — the SAME 2 048 instructions, the same `fp_kimchi` ROM,
the same `perm(state + [x₀, x₁, 0])`. They differ only in their PIN BLOCKS, and the difference is
load-bearing here:

* `dregg-pasta-fp-absorb::v1` publishes **192** PIs — seven blocks — and **does not expose the third
  outgoing lane** (`allocAt 55 2`). One permutation is all `LightClientMinaLinkAir`'s state-hash seam
  needs, so that is the right descriptor there.
* ⚠ **A CHAIN WELDED ON IT WOULD HAND A THIRD OF ITS STATE ON AS A FREE PROVER SCALAR.** That is the
  measured defect `MinaPhase2Chain` was built to fix. `dregg-pasta-fp-chainlink::v1` publishes
  **256** — `in(3) ‖ out(3) ‖ absorbed(2)` — with `in ‖ out` contiguous so a recursion leaf
  re-exposes the continuity claim as ONE slice.

So the brief's *"a salted sponge is the same descriptor with different public inputs"* is right about
the PROGRAM and picks the wrong one of its two pin layouts for a 25-link object. Nothing new is
authored either way. -/

/-- ⚑⚑ **NO NEW AIR.** The phase-1 chain-link descriptor, at 256 public inputs. -/
def bodyChainDesc : EffectVmDescriptor2 := Dregg2.Circuit.Emit.MinaPhase1Chain.chainDesc

/-- ⚑ `dregg-pasta-fp-chainlink::v1`, unchanged — so this rung emits NOTHING, rotates NO VK and
re-genesises nothing. Twenty-five witnesses is the whole artifact cost.

⚑ **AND IT ADDS NO PROVENANCE ROW.** `circuit/descriptors/PROVENANCE.json` carries
`pasta-fp-chainlink.json → 5ad8bbcd6a99e107fa38bfee5b08a8fa4d6c93538730acc6d6500e6958475646` and
the file on disk still hashes to it. **A clean stamp for this rung would cover nothing** — which is
what "no new AIR" actually buys, said as a checkable fact rather than as reassurance. The four rows
already awaiting the operator's ceremony are untouched. -/
theorem the_descriptor_is_the_deployed_phase1_link :
    bodyChainDesc = Dregg2.Circuit.Emit.MinaPhase1Chain.chainDesc := rfl

def bodyInBlock (j : Nat) : List ℤ :=
  (List.range SK).map (limbAt ((bodyChainState j).getD 0 0))
    ++ (List.range SK).map (limbAt ((bodyChainState j).getD 1 0))
    ++ (List.range SK).map (limbAt ((bodyChainState j).getD 2 0))

/-- The OUTGOING-state block — read from the interpreter's own final register file, never from the
reference. -/
def bodyOutBlock (j : Nat) : List ℤ :=
  (List.range SK).map (limbAt ((bodyChainOut j).getD 0 0))
    ++ (List.range SK).map (limbAt ((bodyChainOut j).getD 1 0))
    ++ (List.range SK).map (limbAt ((bodyChainOut j).getD 2 0))

def bodyAbsorbedBlock (j : Nat) : List ℤ :=
  (List.range SK).map (limbAt (bodyLinkX j).1) ++ (List.range SK).map (limbAt (bodyLinkX j).2)

def bodyChainPIs (j : Nat) : List ℤ := bodyInBlock j ++ bodyOutBlock j ++ bodyAbsorbedBlock j

theorem bodyChainPIs_length (j : Nat) : (bodyChainPIs j).length = 256 := by
  simp [bodyChainPIs, bodyInBlock, bodyOutBlock, bodyAbsorbedBlock, SK]

/-- ⚑⚑ **CONTINUITY IN THE EMITTED CLAIMS** — link `j`'s outgoing PI block IS link `j+1`'s incoming
block, limb for limb. A corollary of the kernel-clean step theorem, so it holds at every `j`; this
is the equality the fold's 96 in-circuit `cb.connect`s enforce on the wire. -/
theorem the_body_emitted_claims_are_continuous (j : Nat) : bodyOutBlock j = bodyInBlock (j + 1) := by
  simp only [bodyOutBlock, bodyInBlock, the_body_chain_step_is_the_kimchi_permutation]

def bodyChainTrace (j : Nat) : List (List ℤ) :=
  runRowsVecAt pN pLimb (bodyChainInitVec j) 0 fpAbsorbProg

/-- ⚑ **AND EVERY EMITTED TRACE IS `runRowsAt`'s** — the object every denotation above is a
statement about, at every link. -/
theorem bodyChainTrace_is_the_program_run (j : Nat) :
    bodyChainTrace j = runRowsAt pN pLimb (regsOf (bodyChainInitVec j)) 0 fpAbsorbProg := by
  rw [bodyChainTrace, runRowsVecAt_is_runRowsAt]

/-! ## §6 — ⚑⚑ THE TWO WELDS: THE HEAD IS THE SALT, THE TAIL IS `BODYHASH`. -/

/-- The link whose OUTGOING lane 0 is the body hash — the last one. -/
def BODY_HASH_LINK : Nat := 24

theorem BODY_HASH_LINK_is_the_last : BODY_HASH_LINK + 1 = BODY_LINKS := rfl

/-- ⚑ **PI slots `[0, SK)` ARE the incoming lane 0**, `[SK, 2·SK)` lane 1, `[2·SK, 3·SK)` lane 2 —
`rfl` at every link, so the head weld below is a slice comparison and no arithmetic. -/
theorem the_body_wire_incoming_lanes (j : Nat) :
    (bodyChainPIs j).take (3 * SK) = bodyInBlock j := by
  have hlen : (bodyInBlock j).length = 3 * SK := by simp [bodyInBlock, SK]
  rw [bodyChainPIs, List.append_assoc]
  exact List.take_left' hlen

/-- ⚑⚑ **THE HEAD WELD: LINK 0'S INCOMING STATE IS THE `MinaProtoStateBody` SALT**, all 96 felts,
elementwise at full limb width. ⚠ This is what makes the chain a *Mina body* hash rather than a
generic Poseidon run: with a free head, `perm` being a permutation means every target is reachable
by choosing the head, and the whole rung would be vacuous. No digest is taken, so there is no
birthday bound — a forger must match 96 eight-bit limbs of three 254-bit lanes. -/
theorem the_body_chain_head_is_the_salt :
    (bodyChainPIs 0).take (3 * SK)
      = (List.range SK).map (limbAt (saltProtoStateBody.getD 0 0))
        ++ (List.range SK).map (limbAt (saltProtoStateBody.getD 1 0))
        ++ (List.range SK).map (limbAt (saltProtoStateBody.getD 2 0)) := by
  rw [the_body_wire_incoming_lanes]; rfl

/-- …and the head block is 96 felts and is NOT the zero vector, so the weld above is an equality
between two things that could have differed rather than two copies of a constant. ⚑ A fresh-sponge
head — the head every other chain in this cone starts from — IS the zero vector, which is exactly
the copy-paste this refutes. -/
theorem the_head_weld_is_not_trivial :
    ((bodyChainPIs 0).take (3 * SK)).length = 96
      ∧ (bodyChainPIs 0).take (3 * SK) ≠ List.replicate 96 (0 : ℤ) := by
  refine ⟨?_, ?_⟩ <;> native_decide

/-- ⚑ **PI slots `[3·SK, 4·SK)` ARE the OUTGOING lane 0** — the lane the squeeze reads. -/
theorem the_body_wire_outgoing_lane0 (j : Nat) :
    ((bodyChainPIs j).drop (3 * SK)).take SK
      = (List.range SK).map (limbAt ((bodyChainOut j).getD 0 0)) := rfl

/-- ⚑⚑⚑ **THE TAIL WELD: THE LAST LINK'S OUTGOING LANE 0 IS `state_body_hash`.** The value
`LightClientMinaLinkAir.BODYHASH` carried as a free witness nonet, now published as the FRI-bound
output of a chain from the pinned salt. Kernel-clean: `congrArg` over the one compiled value
equality. -/
theorem the_body_chain_ends_on_the_state_body_hash :
    (bodyChainOut BODY_HASH_LINK).getD 0 0 = realBodyHash := by
  rw [the_body_chain_step_is_the_kimchi_permutation]
  exact the_body_chain_lands_on_the_real_blocks_body_hash

/-- ⚑ **THE WIRE FORM OF THE TAIL WELD**, elementwise at full limb width: 32 felts, no digest,
therefore no birthday bound. -/
theorem the_body_hash_wire_block_is_the_body_hash :
    ((bodyChainPIs BODY_HASH_LINK).drop (3 * SK)).take SK
      = (List.range SK).map (limbAt realBodyHash) := by
  rw [the_body_wire_outgoing_lane0, the_body_chain_ends_on_the_state_body_hash]

/-- ⚑ **A ONE-FELT TIE WOULD BE `2^31`, AND THIS IS NOT ONE.** Stated as arithmetic so the strength
claim is checkable rather than asserted: `SK` felts of `SB` bits is the whole 254-bit element, so a
forger who changes the body hash must change at least one published felt. -/
theorem the_body_tie_is_the_whole_element :
    SK * PastaFieldSound.SB = 256 ∧ 2 ^ 254 < pN ∧ pN < 2 ^ (SK * PastaFieldSound.SB) := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- ⚑ **THE `Faithful9` FORM — the encoding the link rung's `BODYHASH` nonet uses.** ⚠ The chain
publishes 32 eight-bit limbs and `LightClientMinaLinkAir.bodyHashValue` reads nine base-`2^29`
lanes, so the tie between the two spellings is an EXECUTOR re-limbing and NOT a constraint — the
same obligation `LightClientMinaLinkAir.StateHashEngine`'s docblock already names for the state-hash
seam, one object over. Naming the nonet here keeps the two apart rather than letting the chain's
closure launder it. -/
def bodyHashNonet : List ℤ :=
  (List.range 9).map (fun i => ((realBodyHash / 2 ^ (29 * i)) % 2 ^ 29 : Nat))

/-- …and the nonet really recomposes to the body hash, base `2^29`, low lane first — so the
executor's re-limbing has a target that is checkable rather than asserted. -/
theorem the_body_hash_nonet_recomposes :
    (List.range 9).foldr (fun i acc => (bodyHashNonet.getD i 0) + 2 ^ 29 * acc) 0
      = (realBodyHash : ℤ) := by native_decide

/-! ## §7 — ⚑ THE ABSORBED STREAM, AND BOTH POLARITIES. -/

/-- ⚑⚑ **EVERY PACKED ELEMENT IS ABSORBED EXACTLY ONCE, IN ORDER.** Concatenating the 25 links'
absorbed pairs reproduces the block's packed preimage followed by the single padding zero the odd
49-element stream forces. ⚠ Without this the chain could be 25 honest permutations of values nobody
checked — which is the "co-occurrence is not derivation" shape, and this is the theorem that
refuses it. -/
theorem the_body_chain_absorbs_the_preimage_in_order :
    ((List.range BODY_LINKS).flatMap (fun j => [(bodyLinkX j).1, (bodyLinkX j).2]))
      = bodyPacked ++ [0] := by native_decide

/-- ⚑ **THE FORGERY: A BODY WHOSE HASH IS RIGHT AND WHICH IS NOT THIS BLOCK'S.** Perturbing ONE
element of the packed preimage — element 0, which is the body's FIRST whole field element and
therefore twenty-five permutations away from the answer — moves the body hash. So the chain carries
state end to end rather than re-deriving the tail, and a substituted body cannot keep the hash. -/
theorem a_tampered_body_element_moves_the_body_hash :
    (let lx : Nat → Nat × Nat := fun j => if j = 0 then (0, (bodyLinkX 0).2) else bodyLinkX j
     let st : Nat → List Nat := fun n => Nat.rec bodySalt
       (fun j ih => linkStepOf fpParams ih (lx j)) n
     (st BODY_LINKS).getD 0 0) ≠ realBodyHash := by native_decide

/-- …and so does perturbing an element in the MIDDLE of the stream — link 12's first slot is
`bodyPacked[24]`, one of the 38 WHOLE field elements. A control that only ever moves the head would
not show the middle of the preimage is inside the hash. -/
theorem a_tampered_body_field_in_the_middle_moves_the_body_hash :
    (let lx : Nat → Nat × Nat := fun j => if j = 12 then (0, (bodyLinkX 12).2) else bodyLinkX j
     let st : Nat → List Nat := fun n => Nat.rec bodySalt
       (fun j ih => linkStepOf fpParams ih (lx j)) n
     (st BODY_LINKS).getD 0 0) ≠ realBodyHash := by native_decide

/-- ⚑ **AND IN THE PACKED HALF, WHICH IS A DIFFERENT OBJECT.** `bodyPacked` is 38 whole field
elements followed by **11 packed fields** carrying the 819 chunks; the two halves come from
different streams of `Random_oracle.Input.Chunked` and a falsifier that only ever hit the field half
would leave the 2 381 bits untested. Link 19's first slot is `bodyPacked[38]` — the FIRST packed
field, where the two 32-byte digests and the VRF output live. -/
theorem a_tampered_packed_chunk_field_moves_the_body_hash :
    (let lx : Nat → Nat × Nat := fun j => if j = 19 then (0, (bodyLinkX 19).2) else bodyLinkX j
     let st : Nat → List Nat := fun n => Nat.rec bodySalt
       (fun j ih => linkStepOf fpParams ih (lx j)) n
     (st BODY_LINKS).getD 0 0) ≠ realBodyHash := by native_decide

/-- ⚑⚑ **AND THE FALSIFIERS FALSIFY.** All three controls above set a slot to `0`; if that slot were
already `0` the control would be a tautology about an unchanged chain, which is exactly how a
sibling lane's first draft died. Checked, not assumed — and each target is shown to be the packed
element it claims to be, on the right side of the field/chunk boundary at index 38. -/
theorem the_body_tamper_targets_are_real_preimage_elements :
    (bodyLinkX 0).1 ≠ 0 ∧ (bodyLinkX 12).1 ≠ 0 ∧ (bodyLinkX 19).1 ≠ 0
      ∧ (bodyLinkX 0).1 = bodyPacked.getD 0 0
      ∧ (bodyLinkX 12).1 = bodyPacked.getD 24 0
      ∧ (bodyLinkX 19).1 = bodyPacked.getD 38 0
      ∧ Dregg2.Bridge.MinaStateHashPackPrice.bodyInput.fields.length = 38 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> native_decide

/-- ⚑ **AND A CHANGED HEAD MOVES IT TOO** — the vacuity §2 warns about, exhibited. Running the SAME
25 absorbed pairs from the fresh sponge instead of the salt lands somewhere else, so the head weld
is load-bearing rather than decorative. -/
theorem the_fresh_sponge_head_gives_a_different_body_hash :
    (let st : Nat → List Nat := fun n => Nat.rec ([0, 0, 0] : List Nat)
       (fun j ih => linkStepOf fpParams ih (bodyLinkX j)) n
     (st BODY_LINKS).getD 0 0) ≠ realBodyHash := by native_decide

/-! ## §8 — ⚑ RESIDUALS, NAMED — AND THE FIRST IS THE ANSWER TO "WHAT DOES A PROVER STILL CHOOSE".

1. ⚑⚑ **THE PACKED PREIMAGE.** Nothing here says the 49 absorbed field elements are a
   `Protocol_state.Body`'s packing. `Bridge.MinaStateHashDerive.bodyI`/`packToFields` compute them
   from the block's WIRE BYTES and the derivation lands on the hash the Mina chain recorded
   (`MinaStateHashRealBlock`), but that is a fact about a fixture, not a gate on a witness. **The
   value a prover chooses moved from `BODYHASH` — one felt — to its 2 381-bit preimage.** Say it in
   those words: this rung did not eliminate the choice, it relocated it to an object 38 + 819 pieces
   wide, each of which the daemon's consensus rules constrain and this circuit does not.
2. ⚠ **`pack_to_fields` IS NOT IN CIRCUIT.** The chunk-to-field packing is a straight-line program
   whose price `MinaStateHashPackPrice` measures (1 638 instructions, 3.8% of the sponge), and it is
   NOT emitted. The chain absorbs the packed elements; nothing gates that they are the packing of
   819 width-declared chunks, and in particular **nothing forces each chunk `< 2^n`**, without which
   the packing is not injective. That is the next rung and it is cheap: 781 of the 819 chunks are
   ONE BIT (`the_chunk_widths_are_almost_all_boolean`).
3. ⚠ **THE LIMB RE-ENCODING IS AN EXECUTOR CHECK.** This chain publishes 32 eight-bit limbs;
   `LightClientMinaLinkAir.BODYHASH` reads nine base-`2^29` lanes. The node re-limbs and refuses a
   mismatch. Not a constraint — the same obligation the state-hash seam already carries.
4. ⚠ **THE RECURSION BOUNDARY.** That a verifying STARK implies its statement is the FRI obligation
   this whole stack carries (`RecursiveAggregation.EngineSound.recursive_sound`). This rung stands
   at exactly that resolution; not weaker and not stronger.
5. **25 witnesses, one descriptor.** As with phases 1 and 2 and the VK-digest chain, the residual is
   witnesses, not algebra.
-/

#assert_axioms pairsOf_length
#assert_axioms the_preimage_is_forty_nine_field_elements
#assert_axioms the_body_chain_is_twenty_five_links
#assert_axioms the_price_files_count_is_the_schedules
#assert_axioms the_body_salt_is_one_permutation
#assert_axioms the_body_salt_is_a_canonical_state
#assert_axioms the_body_salt_is_not_the_state_salt
#assert_axioms the_body_chain_head_is_the_protocol_state_body_salt
#assert_axioms the_body_chain_is_the_prefix_fold
#assert_axioms squeeze_of_absorbMany_is_absorbFrom
#assert_axioms hashFrom_is_the_core
#assert_axioms the_fold_is_the_state_body_hash
#assert_axioms the_body_chain_derives_the_body_hash
#assert_axioms the_body_chain_step_is_the_kimchi_permutation
#assert_axioms the_descriptor_is_the_deployed_phase1_link
#assert_axioms bodyChainPIs_length
#assert_axioms the_body_emitted_claims_are_continuous
#assert_axioms bodyChainTrace_is_the_program_run
#assert_axioms BODY_HASH_LINK_is_the_last
#assert_axioms the_body_wire_incoming_lanes
#assert_axioms the_body_wire_outgoing_lane0
#assert_axioms the_body_tie_is_the_whole_element
#assert_axioms the_body_chain_head_is_the_salt

-- ⚑ COMPILER-TRUSTED, and said out loud: each reduces the 1 544-byte binprot parse, a two-block
-- SHA-256, the 819-chunk assembly and up to 25 Kimchi permutations of a 255-bit state — where the
-- `decide` proof-term path overflows. `MinaStateHashDerive` §7 measures the KERNEL path for the
-- same derivation at 9.2 s, so these are convertible; the sponge chain is what is not.
#assert_compiled the_body_salt_is_not_the_fresh_sponge
#assert_compiled the_body_chain_lands_on_the_real_blocks_body_hash
#assert_compiled the_real_body_hash_is_not_trivial
#assert_compiled the_head_weld_is_not_trivial
#assert_compiled the_body_hash_nonet_recomposes
#assert_compiled the_body_chain_absorbs_the_preimage_in_order
#assert_compiled a_tampered_body_element_moves_the_body_hash
#assert_compiled a_tampered_body_field_in_the_middle_moves_the_body_hash
#assert_compiled a_tampered_packed_chunk_field_moves_the_body_hash
#assert_compiled the_body_tamper_targets_are_real_preimage_elements
#assert_compiled the_fresh_sponge_head_gives_a_different_body_hash
-- …and the two welds, which INHERIT the compiled facts they are rewritten through.
#assert_compiled the_body_chain_ends_on_the_state_body_hash
#assert_compiled the_body_hash_wire_block_is_the_body_hash

end Dregg2.Circuit.Emit.MinaStateBodyHashChain
