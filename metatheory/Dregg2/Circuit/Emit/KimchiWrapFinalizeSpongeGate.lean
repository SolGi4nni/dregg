/-
# KimchiWrapFinalizeSpongeGate — ⚑ the REALITY GATE for `KimchiWrapMain` §20.

`finalize_other_proof`'s sponge half, checked against a REAL accepted Mina block rather than against
a second spelling of `wrap_verifier.ml`. It is a separate module for a MEASURED reason: closing these
in the kernel means whnf-ing 46 Fq permutations and a 47-entry Horner over 254-bit literals, and
inside `KimchiWrapMain` — already the largest module in the tree — that took the elaborator past this
box's memory (`Lean exited with code 137`, twice, 2026-08-04). Splitting the checks out costs nothing
and keeps the emitter module buildable on a saturated box.

NEW standalone file. Import line for the root (do NOT edit `Dregg2.lean` from a lane):
`import Dregg2.Circuit.Emit.KimchiWrapFinalizeSpongeGate`
-/
import Dregg2.Circuit.Emit.KimchiWrapMain

namespace Dregg2.Circuit.Emit.KimchiWrapFinalizeSpongeGate

open Dregg2.Circuit.Emit.KimchiWrapMain

set_option maxRecDepth 8000

/-! ### §12a′ — ⚑ **THE SECOND REALITY GATE: this file's FINALIZE sponge is upstream's too.**

§12a runs the emitter's state machine on a real accepted proof's PHASE-1 tape. §20 runs the SAME
machine on the PHASE-2 one — `finalize_other_proof`'s — and `MinaRealBlockTranscript` already holds
that tape for Mina devnet block 539508 (`openmina BlockVerifier + accumulator_check + kimchi verify
= Ok`): `CHALS_FLAT` is the 2 × 15 carried IPA challenges the NESTED sponge absorbs, `fqTape2` the
**91** elements the finalize sponge absorbs, and `V_CHAL`/`U_CHAL` the ξ′ and r′ that proof was
actually built with.

⚑ **TWO IMPLEMENTATIONS, ONE PAIR OF NUMBERS.** There the sponge is `PastaPoseidonFq`'s
`absorbMany`/`challenge`, a state fold with no circuit in it; here it is `runSpongeQ`, the trajectory
that EMITS `Poseidon` rows and allocates a variable per absorbed word. If §20's schedule put a
permutation anywhere else — and the two squeezes sharing ONE permutation is exactly where a block
model goes wrong — these would not agree. -/

/-- The nested challenge-digest sponge, driven on the real block's own carried challenges. -/
def blockFinChalSp : SpAcc :=
  finChalSpongeOf 0 Dregg2.Circuit.Emit.MinaRealBlockTranscript.CHALS_FLAT
/-- …and the finalize sponge, on its own 91-element tape. -/
def blockFinSp : SpAcc := finFrSpongeOf 0 Dregg2.Circuit.Emit.MinaRealBlockTranscript.fqTape2
/-- ξ′ and r′ as THIS file's emitter squeezes them. -/
def blockFinChals : List Nat := (chalSqueezes blockFinSp).map (fun e => e.2 % 2 ^ 128)
/-- the two squeeze EVENTS, for the permutation-placement pin. -/
def blockFinSqEvs : List SpEvt := blockFinSp.evs.filter (fun e => !e.isAbs)

/-- ⚑ **THE PREV-CHALLENGE DIGEST AND BOTH SQUEEZES OF A REAL ACCEPTED BLOCK, OUT OF §20's OWN
EMITTER.** Closed in the KERNEL. -/
theorem finalize_sponge_reproduces_the_accepted_block :
    whDigestVal blockFinChalSp = Dregg2.Circuit.Emit.MinaRealBlockTranscript.PREV_CHAL_DIGEST
    ∧ blockFinChals = [ Dregg2.Circuit.Emit.MinaRealBlockTranscript.V_CHAL
                      , Dregg2.Circuit.Emit.MinaRealBlockTranscript.U_CHAL ]
    ∧ Dregg2.Circuit.Emit.MinaRealBlockTranscript.fqTape2.length = 91
    ∧ Dregg2.Circuit.Emit.MinaRealBlockTranscript.CHALS_FLAT.length = WH_MLMB * WH_ROUNDS := by
  refine ⟨rfl, rfl, rfl, rfl⟩

/-- ⚑ **AND ξ′ AND r′ COME OUT OF ONE PERMUTATION, AT LANES 0 AND 1.** `wrap_verifier.ml:892-894`
squeezes twice in a row; the rate-2 machine permutes for the first and reads lane 1 for the second.
A one-permutation-per-squeeze model would put them two permutations apart and every value below
would be a different number wearing the right name — which is the defect `SegSpec.blocks` carries on
the step side and the reason this is a pin and not a comment. -/
theorem finalize_sponge_squeezes_share_one_permutation :
    blockFinSqEvs.length = 2
    ∧ (blockFinSqEvs.getD 0 default).didPerm = true
    ∧ (blockFinSqEvs.getD 1 default).didPerm = false
    ∧ (blockFinSqEvs.getD 0 default).lane = 0
    ∧ (blockFinSqEvs.getD 1 default).lane = 1
    ∧ (blockFinSqEvs.getD 0 default).midV = (blockFinSqEvs.getD 1 default).midV := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- ⚑ RED CONTROL. Bending the LAST absorbed evaluation moves both squeezes — so the pins above
measure a derivation over all 91 elements and not the first few. -/
def blockFinBent : List Nat :=
  (chalSqueezes (finFrSpongeOf 0
      (Dregg2.Circuit.Emit.MinaRealBlockTranscript.fqTape2.set 90 0))).map
    (fun e => e.2 % 2 ^ 128)

theorem finalize_sponge_bends_on_one_absorbed_evaluation :
    (blockFinBent == blockFinChals) = false := rfl

/-! ### §12a″ — ⚑ **AND THE `combined_inner_product` FOLD IS THE SAME BLOCK'S.**

`fnHorner` is the combinator `combined_inner_product_correct` is built out of, and
`Pcs_batch.combine_split_evaluations`'s DIRECTION is the one thing about it prose gets wrong
silently. `MinaRealBlockGate`'s `EVZ`/`EVZW` are that block's 47 C8 entries in
`wrap_verifier.ml:951-1009`'s own order — the two recursion challenge polynomials, the public
evaluation, `ft`, then the 43 columns — and `real_cip` already grounds the fold's VALUE there. This
grounds §20's compiled PROGRAM against the same number: the emitted rows, not a second spelling. -/

/-- §20's fold, over a supplied ξ, r and the two 47-entry evaluation lists. -/
def cipFoldProg (xi r : Nat) (ez ew : List Nat) : FM Nat := do
  let x ← fnLit xi
  let rr ← fnLit r
  let a ← ez.foldlM (fun acc v => do let t ← fnLit v; pure (acc ++ [t])) []
  let b ← ew.foldlM (fun acc v => do let t ← fnLit v; pure (acc ++ [t])) []
  let hz ← fnHorner x a
  let hw ← fnHorner x b
  let rh ← fnMul rr hw
  fnAdd hz rh

/-- …evaluated. Every op is a `.lit`, so the lookup is never called. -/
def cipFoldVal (xi r : Nat) (ez ew : List Nat) : Nat :=
  let res := (cipFoldProg xi r ez ew).run #[]
  (fnEval (fun _ => 0) res.2).getD res.1 0

/-- ξ and r as §5's `to_field_checked` chain lifts the block's own prechallenges. -/
def blockXiField : Nat := liftValQ shapeWrap Dregg2.Circuit.Emit.MinaRealBlockTranscript.V_CHAL
def blockRField : Nat := liftValQ shapeWrap Dregg2.Circuit.Emit.MinaRealBlockTranscript.U_CHAL

/-- ⚑ **THE FOLD, THE LIFT AND THE ENTRY COUNT, ALL AGAINST BLOCK 539508.** The first two conjuncts
are also the pin that §5's `EndoMulScalar` chain IS `ScalarChallenge::to_field` at `ENDO_Q` — a
second implementation (`KimchiVerify.endoMap`, through `MinaRealBlockGate`'s own constants) of the
map this file emits eight `EndoMulScalar` rows for. -/
theorem cip_fold_reproduces_the_accepted_block :
    blockXiField = Dregg2.Circuit.Emit.MinaRealBlockGate.VV.val
    ∧ blockRField = Dregg2.Circuit.Emit.MinaRealBlockGate.UU.val
    ∧ Dregg2.Circuit.Emit.MinaRealBlockTranscript.EVZ_N.length = FIN_NCOLS + 4
    ∧ cipFoldVal blockXiField blockRField
        Dregg2.Circuit.Emit.MinaRealBlockTranscript.EVZ_N
        Dregg2.Circuit.Emit.MinaRealBlockTranscript.EVZW_N
      = Dregg2.Circuit.Emit.MinaRealBlockGate.CIP.val := by
  refine ⟨rfl, rfl, rfl, rfl⟩

/-- ⚑ RED CONTROL — the fold is over EVERY entry and in ONE direction. Reversing the ζ list, or
bending one column, moves the result. A Horner whose direction is wrong reproduces nothing, which is
what makes the theorem above a measurement of `fnHorner` and not of the constants. -/
theorem cip_fold_direction_and_every_entry_are_load_bearing :
    (cipFoldVal blockXiField blockRField
        Dregg2.Circuit.Emit.MinaRealBlockTranscript.EVZ_N.reverse
        Dregg2.Circuit.Emit.MinaRealBlockTranscript.EVZW_N
      == Dregg2.Circuit.Emit.MinaRealBlockGate.CIP.val) = false
    ∧ (cipFoldVal blockXiField blockRField
        (Dregg2.Circuit.Emit.MinaRealBlockTranscript.EVZ_N.set 46 0)
        Dregg2.Circuit.Emit.MinaRealBlockTranscript.EVZW_N
      == Dregg2.Circuit.Emit.MinaRealBlockGate.CIP.val) = false
    ∧ (cipFoldVal blockXiField blockRField
        Dregg2.Circuit.Emit.MinaRealBlockTranscript.EVZ_N
        (Dregg2.Circuit.Emit.MinaRealBlockTranscript.EVZW_N.set 0 0)
      == Dregg2.Circuit.Emit.MinaRealBlockGate.CIP.val) = false := by
  refine ⟨rfl, rfl, rfl⟩


#assert_namespace_axioms Dregg2.Circuit.Emit.KimchiWrapFinalizeSpongeGate

end Dregg2.Circuit.Emit.KimchiWrapFinalizeSpongeGate
