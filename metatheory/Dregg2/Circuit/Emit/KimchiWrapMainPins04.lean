/-
# Dregg2.Circuit.Emit.KimchiWrapMainPins04 — §14b — W-KEY

⚑ **ONE MODULE OF THE `KimchiWrapMain` SPLIT.** The namespace is unchanged
(`Dregg2.Circuit.Emit.KimchiWrapMain`), so nothing here is renamed and no consumer moves; the file
boundary exists only so a pin re-elaborates without the emitter's 5,000 lines of `def` behind it.
The in-file rule that keeps it stable is the step side's: **a `def` goes in `…Core`/`…Fixture`, a
pin goes in its section's `…PinsNN`.**

⚠ The `set_option` block below is VERBATIM `KimchiWrapMain`'s and must stay that way. `set_option`
does not cross an import, and `KimchiWrapFinalizeSpongeGate` shipped four proofs as `sorryAx` --
each still landing in the environment with the right statement -- because a split dropped it.

Pins only. Every `def` this section had is in `…Fixture`; the namespace-wide axiom pin is in the
`KimchiWrapMain` umbrella, which imports every one of these.

-/
import Dregg2.Circuit.Emit.KimchiWrapMainFixture

namespace Dregg2.Circuit.Emit.KimchiWrapMain
open Dregg2.Circuit.Emit.KimchiTarget (KGateType K_PERMUTS)
open Dregg2.Circuit.Emit.KimchiPlacement
open Dregg2.Circuit.Emit.WitnessBuilder
  (VarEnv GateWitness gridAt envIndex envLookupAt gateVarWitnessAt compose)
open Dregg2.Circuit.Emit.PastaField (pN qN)
open Dregg2.Circuit.Emit.PastaPoseidonFq (fqParams rcsQ mdsQ)

set_option autoImplicit false
set_option maxRecDepth 100000
-- ⚠ §12/§14b reduce whole sponge trajectories IN THE KERNEL (`rfl`/`decide`), which is strictly
-- stronger than the `#guard`s they replace and correspondingly slower to elaborate.
set_option maxHeartbeats 4000000

/-! ### §14b — ⚑ **W-KEY'S PINS, AS NAMED THEOREMS.**

`metatheory/docs/GUARD-DISCIPLINE.md`: a fact worth asserting is worth naming, and where the KERNEL
can reach it, `rfl`/`decide` is strictly stronger than the `#guard` would have been. Every fact below
is kernel-clean — `#assert_namespace_axioms` at the foot of the file accounts for all of them, and
none of them is a `native_decide` oracle. (§24 has the file's one exception; it is named there.) -/

/-- The flattening's SHAPE — `Permuts.n = 7`, `Columns.n = 15`, six singletons, 28 points, and a
fixture list that is exactly `~g`'s output length and not a truncation of it. -/
theorem key_index_shape :
    KEY_SIGMA = 7 ∧ KEY_COLS = 15 ∧ KEY_SINGLES = 6
    ∧ KEY_POINTS = 28 ∧ KEY_COORDS = 56 ∧ STEP_VK_XY.length = KEY_COORDS := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_⟩
  decide

/-- ⚑⚑ **NO COMMITMENT OF THIS KEY IS THE IDENTITY, AND EVERY ONE OF THE 28 IS ON VESTA.** This is
the property W-COMBINE needs and the one the previous fixture did not have: `index_to_field_elements`
flattens infinity as the fake point `(0,0)` (`poseidon/src/sponge.rs:332-345`), `Ops.add_fast` is the
INCOMPLETE add, and a chord through `(0,0)` leaves `y² = x³ + 5` — so a single identity commitment
put `combined_polynomial`, `p_prime`, `q`, `cq` and `lhs` off the curve and made
`Boolean.Assert.is_true bulletproof_success` unsatisfiable. The old key had seven.

⚠ The zero-count leg is not decoration: `(0,0)` is the ONLY off-curve pair the flattening can
produce from a well-formed `PolyComm`, so it and the on-curve leg are the same fact approached from
both sides — and the first is what a regression would trip. -/
theorem key_index_has_no_identity_and_is_on_vesta :
    (STEP_VK_XY.filter (fun x => x == 0)).length = 0
    ∧ (List.range KEY_POINTS).all (fun p =>
        onCurveQ (STEP_VK_XY.getD (2 * p) 0, STEP_VK_XY.getD (2 * p + 1) 0)) = true := by
  refine ⟨?_, ?_⟩ <;> decide

/-- The index sponge is 56 absorbs and ONE squeeze — `wrap_verifier.ml:524-530`'s `Array.iter … ~f:
Sponge.absorb` then `Sponge.squeeze_field`, at rate 2, which is 28 permutations. -/
theorem key_sponge_schedule :
    ((keySponge shapeSmoke tKey.sp KEY_REAL_BRANCH).evs.filter (fun e => e.isAbs)).length = KEY_COORDS
    ∧ ((keySponge shapeSmoke tKey.sp KEY_REAL_BRANCH).evs.filter (fun e => !e.isAbs)).length = 1
    ∧ ((keySponge shapeSmoke tKey.sp KEY_REAL_BRANCH).evs.filter (fun e => e.didPerm)).length = 28 := by
  refine ⟨?_, ?_, ?_⟩ <;> rfl

/-- ⚑⚑ **THE REALITY GATE, AND THE POINT OF THE WHOLE RUNG.** Driving THIS FILE'S OWN Fq sponge
over the 56 coordinates of **Mina's `step-transaction` verification key**, in
`index_to_field_elements` order, reproduces the digest that RUST KIMCHI computed for that index
(`verifier_index.rs:407-533`) — and the extractor re-derives it a third time by an independent
`absorb_fq` replay. Two implementations, three computations, one number.

⚑ **So the wrap transcript's first absorbed item is DERIVED here, not fixtured.** -/
theorem key_digest_is_the_index_digest :
    keyDigestVal shapeSmoke tKey.sp KEY_REAL_BRANCH = STEP_VK_DIGEST := by rfl

/-- …and it is the value the TRANSCRIPT absorbs first (`wrap_verifier.ml:537`), so `RC_DIGEST` is no
longer standing in for anything: the tie row in `keyRows` puts the two in one σ class and this puts
them at one value. -/
theorem key_digest_is_the_transcript_input :
    itemVal T_DIGEST 0 = keyDigestVal shapeSmoke tKey.sp KEY_REAL_BRANCH := by rfl

/-- ⚑ **RED CONTROL — the digest is a function of EVERY coordinate.** Bending any one of the 56
inputs by `+1` moves it: the first, one in `coefficients_comm`, one in the six singles, and the last.
Without this the theorem above is a number agreeing with a number. -/
theorem key_digest_bends_at_every_probed_coordinate :
    [0, 20, 41, 55].all (fun k =>
      keyDigestValOf (keySpongeBent shapeSmoke tKey.sp KEY_REAL_BRANCH k 1) != STEP_VK_DIGEST) = true := by rfl

/-- ⚑ **AND THE ONE-HOT SELECTION MATTERS.** `choose_key` at a DIFFERENT branch produces a different
key and therefore a different `index_digest`; the real key is at `KEY_REAL_BRANCH` and
`mkWrapWith` witnesses exactly that branch. If the witnessed branch ever moved off it, the reality
gate above would red rather than quietly digest a fixture. -/
theorem key_selection_is_the_branch_selection :
    tKey.br.idx = KEY_REAL_BRANCH
    ∧ (mkWrap shapeWrap).br.idx = KEY_REAL_BRANCH
    ∧ (List.range KEY_COORDS).all (fun k => keyConst KEY_REAL_BRANCH k == STEP_VK_XY.getD k 0) = true
    ∧ ((List.range KEY_COORDS).filter (fun k => keyConst 0 k != STEP_VK_XY.getD k 0)).length = 56 := by
  refine ⟨rfl, rfl, ?_, ?_⟩ <;> decide

/-- ⚑⚑ **THE INDEX SPONGE ABSORBS THE SELECTED BRANCH'S KEY, AND UNTIL 2026-08-05 IT DID NOT.**
`keySchedule` took no branch at all: it absorbed `keyConst KEY_REAL_BRANCH` while `keyEnv`'s one-hot
fold outputs `keyConst t.br.idx` and `keyRows`' `sealHalves` ties the two — so W-KEY was satisfiable
at branch 1 and NOWHERE ELSE, and `choose_key`'s whole five-entry fold was decoration. This says the
sponge's `k`-th absorbed word is the SELECTED branch's `k`-th coordinate, at every branch. -/
theorem key_sponge_absorbs_the_selected_branch :
    (List.range shapeSmoke.branches).all (fun i =>
      (List.range KEY_COORDS).all (fun k =>
        ((keySponge shapeSmoke tKey.sp i).evs.getD k default).word == keyConst i k)) = true := by
  decide

/-- ⚑ **RED CONTROL FOR THAT: the digest MOVES with the branch selection.** Five branches, five
distinct `index_digest`s — so the one-hot selection reaches the transcript's first absorbed word and
a wrap circuit cannot verify a step proof made against a key it did not choose. Without this,
`key_sponge_absorbs_the_selected_branch` is consistent with a sponge that reads the branch and
throws it away. -/
theorem key_digest_moves_with_the_branch_selection :
    ((List.range shapeSmoke.branches).map (fun i =>
      keyDigestVal shapeSmoke tKey.sp i)).eraseDups.length = shapeSmoke.branches := by
  decide

/-- ⚑ **AND THE LAYOUT DOES NOT MOVE WITH IT.** Every base above `w5_key` is `baseKeySp + nKeySpVars`,
so a branch-dependent sponge WIDTH would slide the whole variable space under a branch selection.
`runSpongeQ` allocates per EVENT, and `keySchedule i` has the same events at every `i`; this is that
fact, measured across the branches rather than argued. -/
theorem key_sponge_width_is_branch_independent :
    (List.range shapeSmoke.branches).all (fun i =>
      (keySponge shapeSmoke tKey.sp i).next == nKeySpVars shapeSmoke tKey.sp) = true := by
  decide

/-- ⚑⚑ **DREGG'S OWN STEP RULE IS IN `step_keys`, AND IT IS A DIFFERENT RULE FROM MINA'S.**
`KEY_CHAIN_BRANCH` holds the 56 `index_to_field_elements` coordinates of
`stepmain_smoke_r8_finalize`'s verifier index, and its digest is
`KimchiStepWrapChainKey.STEP_OWN_VK_DIGEST` — which the Rust exporter derived from the SAME
`VerifierIndex`, in the SAME run, that produced the tape whose first word it is.

⚠ The disjointness leg is the one that makes this a check: not one of the 56 coordinates is shared
with Mina's `step-transaction` key, so "dregg's branch" and "Mina's branch" are not the same key
under two names. -/
theorem chain_step_rule_is_a_second_real_key :
    (List.range KEY_COORDS).all (fun k =>
      keyConst KEY_CHAIN_BRANCH k
        == Dregg2.Circuit.Emit.KimchiStepWrapChainKey.STEP_OWN_VK_XY.getD k 0) = true
    ∧ keyDigestVal shapeSmoke tKey.sp KEY_CHAIN_BRANCH
        = Dregg2.Circuit.Emit.KimchiStepWrapChainKey.STEP_OWN_VK_DIGEST
    ∧ Dregg2.Circuit.Emit.KimchiStepWrapChainKey.STEP_OWN_VK_DIGEST ≠ STEP_VK_DIGEST
    ∧ ((List.range KEY_COORDS).filter (fun k =>
        STEP_VK_XY.contains
          (Dregg2.Circuit.Emit.KimchiStepWrapChainKey.STEP_OWN_VK_XY.getD k 0))).length = 0 := by
  refine ⟨?_, rfl, ?_, ?_⟩ <;> decide

/-- ⚑ **AND NO COMMITMENT OF DREGG'S OWN KEY IS THE IDENTITY EITHER** — the property W-COMBINE's
incomplete `Ops.add_fast` fold needs, which kimchi's `create_circuit(0,5)` test key did NOT have
(seven of 28). Asserted in Rust before the module was written and re-derived here. -/
theorem chain_step_key_has_no_identity_and_is_on_vesta :
    (Dregg2.Circuit.Emit.KimchiStepWrapChainKey.STEP_OWN_VK_XY.filter (fun x => x == 0)).length = 0
    ∧ (List.range KEY_POINTS).all (fun p =>
        onCurveQ (Dregg2.Circuit.Emit.KimchiStepWrapChainKey.STEP_OWN_VK_XY.getD (2 * p) 0,
                  Dregg2.Circuit.Emit.KimchiStepWrapChainKey.STEP_OWN_VK_XY.getD (2 * p + 1) 0))
       = true := by
  refine ⟨?_, ?_⟩ <;> decide

/-- ⚑ **DEFECT CLASS 1 IN A NEW PLACE: the index sponge's INITIAL STATE IS PINNED.**
`Sponge.create sponge_params` (`wrap_verifier.ml:522`) starts at the zero state. Leaving those three
lanes free witnesses would let a prover choose `index_digest` outright — the same shape as the step
side's free `acc₀`/`n₀` (`plonk_curve_ops.ml:157-158`). `transcriptRowsQ`'s two `init` rows pin all
three by `Generic` constant halves, and this reads them off the EMITTED rows. -/
theorem key_sponge_seed_is_pinned :
    ((keyRows tKey true).getD 0 default).coeffs = cConst 0 ++ cConst 0
    ∧ ((keyRows tKey true).getD 1 default).coeffs = cConst 0 ++ cNil
    ∧ ((keyRows tKey true).getD 0 default).kind = KGateType.generic
    ∧ ((keyRows tKey true).getD 1 default).kind = KGateType.generic := by
  refine ⟨rfl, rfl, rfl, rfl⟩

/-- **DEFECT CLASS 3, MOVED BY ONE.** `index_digest` leaves `WRAP_UNCONSUMED`, and it leaves because
a row reads it — not because the entry was deleted. The other eight stay, unpadded. -/
theorem key_closes_one_unconsumed_entry :
    WRAP_UNCONSUMED.length = 8
    ∧ WRAP_UNCONSUMED_KEYS.contains "index_digest" = false
    ∧ WRAP_UNCONSUMED_KEYS.head? = some "sg_old" := by
  refine ⟨rfl, ?_, rfl⟩
  decide

/-- The `w5_key` rung is a strict superset of `w4_bind` and its length is the sum of its parts — the
§12b shape, so a dropped `keyRows` is a red and not a silence. -/
theorem key_rung_is_a_ladder_step :
    (rungRows tKey .key true).length
      = (rungRows tKey .bind true).length + (keyRows tKey true).length
    ∧ (rungRows tKey .bind true).length < (rungRows tKey .key true).length
    ∧ rungPub shapeSmoke .key = WRAP_PRIMARY_LEN := by
  refine ⟨rfl, ?_, rfl⟩
  decide

/-- The WIRED and UNWIRED `w5_key` circuits differ ONLY in the probe rows' permutation columns —
the control that makes "rejected" mean "rejected BY THE WIRE" at this rung too. -/
theorem key_rung_control_differs_only_in_probes :
    (rungRows tKey .key true).length = (rungRows tKey .key false).length
    ∧ ((rungRows tKey .key true).zip (rungRows tKey .key false)).all
        (fun p => p.1.kind == p.2.kind && p.1.coeffs == p.2.coeffs && p.1.probe == p.2.probe) = true
    ∧ (((rungRows tKey .key true).zip (rungRows tKey .key false)).filter
        (fun p => p.1.perm != p.2.perm)).length
        = ((rungRows tKey .key true).filter (fun r => r.probe)).length := by
  refine ⟨rfl, rfl, rfl⟩

/-- `placeChecked` ACCEPTS the `w5_key` rung and no public word is inert — the fail-closed placement
still holds with W-KEY's 56 folds and its second sponge in the grid. -/
theorem key_rung_places :
    refusalOf shapeSmoke .key (rungPub shapeSmoke .key)
        (wrapGates (rungRows tKey .key true)) = none
    ∧ inertSlotsAt shapeSmoke .key (wrapGates (rungRows tKey .key true))
        = wrapInertOk shapeSmoke .key
    ∧ (placedOf shapeSmoke .key (rungPub shapeSmoke .key)
        (wrapGates (rungRows tKey .key true))).length
        = WRAP_PRIMARY_LEN + (rungRows tKey .key true).length := by
  refine ⟨rfl, rfl, rfl⟩

/-- W-KEY's Poseidon rows come in 11-row permutations, and it adds NO curve gate — `choose_key` over
`Inner_curve.constant` keys is `Generic` arithmetic, which is the substantive reading of
`wrap_main.ml:218-219` and the reason this sub-circuit is cheap. -/
theorem key_rows_are_generic_and_poseidon_only :
    ((keyRows tKey true).filter (fun r => r.kind == KGateType.poseidon)).length = 28 * 11
    ∧ ((keyRows tKey true).filter (fun r => r.kind == KGateType.varBaseMul)).length = 0
    ∧ ((keyRows tKey true).filter (fun r => r.kind == KGateType.endoMul)).length = 0
    ∧ ((keyRows tKey true).filter (fun r => r.kind == KGateType.completeAdd)).length = 0
    ∧ ((keyRows tKey true).filter (fun r => r.kind == KGateType.endoMulScalar)).length = 0 := by
  refine ⟨rfl, rfl, rfl, rfl, rfl⟩

end Dregg2.Circuit.Emit.KimchiWrapMain
