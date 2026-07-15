/-
# Market.ProtocolAssurance — the honest STARK ↔ Market ↔ settlement seam.

`Dregg2.Circuit.CircuitSoundness` and the Market tower were previously imported by the same root file,
but no theorem connected them.  In particular, an accepted batch exposed only
`(effect, pre, post, turn)`, while `DrexClearing` was handed directly to `settleDrex`; neither the STARK
extractor nor a modeled settlement-proof verifier produced that clearing.

This module makes the seam explicit without inventing it:

* `MarketBoundaryBinding` is the smallest faithful endpoint relation: the accepted batch's public roots
  are exactly the commitments of a real `DrexClearing`.  Commitment binding then forces the decoded
  STARK endpoints to be that clearing's endpoints.
* `MarketEffectStepExtractsClearing` is the maximally narrow endpoint fact: the kernel endpoints of a
  step extracted for the designated effect are realized by a proof-carrying clearing.  The ordinary
  STARK extraction, witness decode, and commitment binding are no longer hidden in a second accept-level
  hypothesis; the theorems below invoke `lightclient_unfoolable` themselves.
* The exact clearing-allocation lowering is now proved by `drexClearing_refines_turnSpec`.  The former
  proposal to recover that two-leg allocation from tag zero's single `dispatchArm` is refuted by
  `not_marketEffectApexLiftResidual_balance`: their receipt-log arities differ.  The direct ring
  descriptor must retain/extract the fused ring and its endpoints instead.
* `starkMarketClaimExtraction_of_effect_step`, `lightclient_market_seam`, and
  `accepted_market_settles_on_same_commitment_surface` prove everything above that exact descriptor
  fact: the decoded STARK transition is the fair, kernel-real clearing; it conserves every asset; and
  the cross-chain register advances from the same pre-commitment to the same post-commitment.
* `SettlementVerifier25Refines` names the second missing theorem over the exact canonical 25-lane ABI.
  The current `settleDrex` consumes a pre-proved `DrexClearing` and models only continuity plus register
  update.  Groth16 soundness must imply existence of the clearing whose eight-lane roots and turn count
  it accepted; the byte packing below is no longer generic prose.

The repaired cross-chain witness is also shown to satisfy `AccountsWF`, the structural invariant
required by `StateDecode`.  Previously its `cell` function was non-default outside `{1,2}`, so the
Market demo could not inhabit the light-client boundary at all.

At HEAD the single-effect dispatcher has no `DrexClearing` constructor: a clearing contains at least
two settlement legs, while `BatchPublicInputs.effect` selects one `FullActionA`.  The direct ring-
descriptor route below has the right theorem shape, but the current six-lane note apex omits creators,
kernel endpoints, turn count, and receipt-chain output.  Therefore only that endpoint-carrying
descriptor/whole-turn extraction remains named; it cannot be manufactured from the note claim.

Pure.  No axioms; the two missing links remain named propositions.
-/
import Market.CrossChainSettlement
import Dregg2.Circuit.CircuitSoundness
import Dregg2.Tactics

namespace Market.ProtocolAssurance

open Market
open Dregg2.Exec
open Dregg2.Intent.Ring
open Dregg2.Circuit.StateCommit (AccountsWF)
open Dregg2.Circuit.CircuitSoundness
open Dregg2.Circuit.DescriptorIR2 (EffectVmDescriptor2 Satisfied2)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Circuit.ActionDispatch (actionTag fullActionStep turnSpec)
open Dregg2.Circuit.Spec.BalanceMovement (BalanceMovementSpec recCexecAsset_iff_spec)
open Dregg2.Exec.TurnExecutorFull
  (FullActionA acceptsEffects acceptsEffects_eq_cellLifecycleLive recCexecAsset)

set_option autoImplicit false

/-! ## 1. Structural compatibility: Market settlement preserves `StateDecode` well-formedness. -/

/-- Per-asset execution changes only `bal`, so it preserves the dead-cell/default invariant required
by the state-commitment binding theorem. -/
theorem recKExecAsset_preserves_accountsWF {k k' : RecordKernelState} {t : Turn} {a : AssetId}
    (hwf : AccountsWF k) (h : recKExecAsset k t a = some k') : AccountsWF k' := by
  rw [recKExecAsset_shape h]
  exact hwf

/-- A successfully settled Market ring preserves `AccountsWF` through every real `recKExecAsset` leg. -/
theorem settleRing_preserves_accountsWF :
    ∀ {r : Ring} {k k' : RecordKernelState}, AccountsWF k →
      settleRing k r = some k' → AccountsWF k' := by
  intro r
  induction r with
  | nil =>
      intro k k' hwf hsettle
      simp only [settleRing_nil, Option.some.injEq] at hsettle
      subst k'
      exact hwf
  | cons l rest ih =>
      intro k k' hwf hsettle
      rw [settleRing_cons] at hsettle
      cases hstep : recKExecAsset k l.toTurn l.asset with
      | none => simp [hstep] at hsettle
      | some mid =>
          rw [hstep] at hsettle
          exact ih (recKExecAsset_preserves_accountsWF hwf hstep) hsettle

/-! ## 1a. The concrete settlement-list lowering.

There is one important guard distinction at this seam.  `settleRing` folds the kernel-only
`recKExecAsset`, whereas the ordinary `.balanceA` action uses `recCexecAsset`: the latter additionally
requires the destination to be Live and prepends the movement receipt to `RecChainedState.log`.
Consequently the standalone implication from a raw kernel step to `BalanceMovementSpec` is false
without the destination-liveness premise.  A successfully settled *cycle* supplies that premise:
every receiver is another leg's sender, and every successfully executing sender is Live.  The lemmas
below make those two facts explicit and then perform the exact fold, including the receipt log. -/

/-- The receipt-chain suffix produced by executing a ring left-to-right.  Each action prepends its
receipt, so the final log contains the ring's turns in reverse execution order before the old log. -/
def ringReceiptLog (r : Ring) (log : List Turn) : List Turn :=
  (r.map RingLeg.toTurn).reverse ++ log

/-- The ordinary full-action lowering of a kernel ring. -/
def ringActions (r : Ring) : List FullActionA :=
  r.map fun l => .balanceA l.toTurn l.asset

/-- A committed raw per-asset step forces its source lifecycle to be Live.  This is the seventh
conjunct of `recKExecAsset`'s real acceptance guard, retained here because the older public
`recKExecAsset_committed` projection deliberately exposes only its first six conjuncts. -/
theorem recKExecAsset_source_live {k k' : RecordKernelState} {t : Turn} {a : AssetId}
    (h : recKExecAsset k t a = some k') : cellLifecycleLive k t.src = true := by
  unfold recKExecAsset at h
  by_cases hg : authorizedB k.caps t = true ∧ 0 ≤ t.amt ∧ t.amt ≤ k.bal t.src a
      ∧ t.src ≠ t.dst ∧ t.src ∈ k.accounts ∧ t.dst ∈ k.accounts
      ∧ cellLifecycleLive k t.src = true
  · exact hg.2.2.2.2.2.2
  · rw [if_neg hg] at h
    exact absurd h (by simp)

/-- Every sender appearing in a successfully settled ring was Live in the ring's pre-state.  Prior
legs change only `bal`, so the lifecycle fact extracted at a later fold state transports back to the
initial state. -/
theorem settleRing_sources_live :
    ∀ {r : Ring} {k k' : RecordKernelState}, settleRing k r = some k' →
      ∀ l ∈ r, cellLifecycleLive k l.from_ = true := by
  intro r
  induction r with
  | nil =>
      intro k k' _ l hl
      simp at hl
  | cons head rest ih =>
      intro k k' hsettle l hl
      rw [settleRing_cons] at hsettle
      cases hhead : recKExecAsset k head.toTurn head.asset with
      | none => simp [hhead] at hsettle
      | some mid =>
          rw [hhead] at hsettle
          rcases List.mem_cons.mp hl with rfl | hlrest
          · exact recKExecAsset_source_live hhead
          · have hlive := ih hsettle l hlrest
            rw [recKExecAsset_shape hhead] at hlive
            exact hlive

/-- In a balanced settled ring, every destination accepts effects in the pre-state.  Cycle closure
provides a leg sending from the destination, and successful settlement makes that sender Live. -/
theorem settled_balanced_ring_destinations_live {r : Ring} {k k' : RecordKernelState}
    (hbalanced : RingBalanced r) (hsettle : settleRing k r = some k') :
    ∀ l ∈ r, acceptsEffects k l.to_ = true := by
  intro l hl
  obtain ⟨sender, hsender, hfrom⟩ := hbalanced.recvImpSend l hl
  calc
    acceptsEffects k l.to_ = cellLifecycleLive k l.to_ :=
      acceptsEffects_eq_cellLifecycleLive k l.to_
    _ = cellLifecycleLive k sender.from_ := by rw [hfrom]
    _ = true := settleRing_sources_live hsettle sender hsender

/-- **The concrete per-step lowering.**  A raw `recKExecAsset` commit plus the chained executor's
destination-liveness guard is exactly a `.balanceA` `BalanceMovementSpec` step.  The post-state pins
the whole kernel and prepends the truthful movement receipt. -/
theorem recKExecAsset_refines_balanceMovement {k k' : RecordKernelState} {t : Turn} {a : AssetId}
    (log : List Turn) (hdst : acceptsEffects k t.dst = true)
    (h : recKExecAsset k t a = some k') :
    BalanceMovementSpec ⟨k, log⟩ t a ⟨k', t :: log⟩ := by
  apply (recCexecAsset_iff_spec ⟨k, log⟩ t a ⟨k', t :: log⟩).mp
  simp [recCexecAsset, hdst, h]

/-- Concrete witness for why `recKExecAsset_refines_balanceMovement` must mention destination
liveness: the raw kernel accepts a funded move into sealed cell `2`, while `.balanceA` fails closed. -/
def rawDstSealedPre : RecordKernelState :=
  { demoSettlePre with lifecycle := fun c => if c = 2 then 1 else 0 }

def rawDstSealedTurn : Turn := { actor := 1, src := 1, dst := 2, amt := 7 }

#guard (recKExecAsset rawDstSealedPre rawDstSealedTurn 10).isSome
#guard acceptsEffects rawDstSealedPre rawDstSealedTurn.dst == false

/-- The hostile pole paired with the concrete per-step lowering: no full-action post-state can satisfy
`BalanceMovementSpec` for the raw move into a sealed destination, even though the raw kernel commits. -/
theorem rawDstSealed_not_balanceMovement (k' : RecordKernelState) (log : List Turn) :
    ¬ BalanceMovementSpec ⟨rawDstSealedPre, log⟩ rawDstSealedTurn 10
      ⟨k', rawDstSealedTurn :: log⟩ := by
  intro hspec
  have hdst := hspec.1.2.2.2.2.2.2.2
  simp [rawDstSealedPre, rawDstSealedTurn, acceptsEffects,
    Dregg2.Exec.TurnExecutorFull.lcLive] at hdst

/-- Fold the concrete per-step lowering over any settled ring whose destinations are Live. -/
theorem settleRing_refines_turnSpec_of_destinations_live :
    ∀ {r : Ring} {k k' : RecordKernelState} (log : List Turn),
      (∀ l ∈ r, acceptsEffects k l.to_ = true) →
      settleRing k r = some k' →
      turnSpec ⟨k, log⟩ (ringActions r) ⟨k', ringReceiptLog r log⟩ := by
  intro r
  induction r with
  | nil =>
      intro k k' log _ hsettle
      simp only [settleRing_nil, Option.some.injEq] at hsettle
      subst k'
      simp [ringActions, ringReceiptLog, turnSpec]
  | cons head rest ih =>
      intro k k' log hdsts hsettle
      rw [settleRing_cons] at hsettle
      cases hhead : recKExecAsset k head.toTurn head.asset with
      | none => simp [hhead] at hsettle
      | some mid =>
          rw [hhead] at hsettle
          have hheadDst : acceptsEffects k head.to_ = true :=
            hdsts head (by simp)
          have hstep : fullActionStep ⟨k, log⟩ (.balanceA head.toTurn head.asset)
              ⟨mid, head.toTurn :: log⟩ :=
            recKExecAsset_refines_balanceMovement log hheadDst hhead
          have hrestDst : ∀ l ∈ rest, acceptsEffects mid l.to_ = true := by
            intro l hl
            have hpre : acceptsEffects k l.to_ = true := hdsts l (by simp [hl])
            rw [recKExecAsset_shape hhead]
            exact hpre
          have htail := ih (head.toTurn :: log) hrestDst hsettle
          have hlog : ringReceiptLog rest (head.toTurn :: log) =
              ringReceiptLog (head :: rest) log := by
            simp [ringReceiptLog, List.append_assoc]
          change ∃ st1, fullActionStep ⟨k, log⟩ (.balanceA head.toTurn head.asset) st1 ∧
            turnSpec st1 (ringActions rest) ⟨k', ringReceiptLog (head :: rest) log⟩
          exact ⟨⟨mid, head.toTurn :: log⟩, hstep, hlog ▸ htail⟩

/-- **THE LOWERING, closed.**  A balanced kernel ring that settles lowers to the exact ordinary
`.balanceA` action list under `turnSpec`, with no extra trusted liveness premise: balance + successful
cycle settlement derive it. -/
theorem settleRing_refines_turnSpec {r : Ring} {k k' : RecordKernelState} (log : List Turn)
    (hbalanced : RingBalanced r) (hsettle : settleRing k r = some k') :
    turnSpec ⟨k, log⟩ (ringActions r) ⟨k', ringReceiptLog r log⟩ :=
  settleRing_refines_turnSpec_of_destinations_live log
    (settled_balanced_ring_destinations_live hbalanced hsettle) hsettle

#assert_axioms recKExecAsset_source_live
#assert_axioms settleRing_sources_live
#assert_axioms settled_balanced_ring_destinations_live
#assert_axioms recKExecAsset_refines_balanceMovement
#assert_axioms rawDstSealed_not_balanceMovement
#assert_axioms settleRing_refines_turnSpec_of_destinations_live
#assert_axioms settleRing_refines_turnSpec

/-- The concrete cross-chain Market witness now genuinely satisfies the light-client structural
boundary invariant (its cells outside the live account set are default). -/
theorem demoSettlePre_accountsWF : AccountsWF demoSettlePre := by
  intro c hc
  change c ∉ ({1, 2} : Finset CellId) at hc
  have hc1 : c ≠ 1 := fun h => hc (by simp [h])
  have hc2 : c ≠ 2 := fun h => hc (by simp [h])
  simp [demoSettlePre, hc1, hc2]

/-- The concrete Market post-state is also `AccountsWF`, derived through the actual settled ring. -/
theorem demoSettlePost_accountsWF : AccountsWF demoFill.post :=
  settleRing_preserves_accountsWF demoSettlePre_accountsWF demoFill.settled

#assert_axioms recKExecAsset_preserves_accountsWF
#assert_axioms settleRing_preserves_accountsWF
#assert_axioms demoSettlePre_accountsWF
#assert_axioms demoSettlePost_accountsWF

/-! ## 2. The endpoint binding and its fail-closed tooth. -/

/-- **The minimum STARK↔Market endpoint seam.**  A proof-carrying Market clearing is bound to the
batch's public pre/post commitments under the same state-commitment surface.  `preWF` is structural;
post well-formedness follows from the clearing's real `settleRing` execution. -/
structure MarketBoundaryBinding (S : CommitSurface) (pi : BatchPublicInputs)
    (c : DrexClearing) : Prop where
  preWF : AccountsWF c.pre
  preRoot : pi.pre = S.commit c.pre pi.turn
  postRoot : pi.post = S.commit c.post pi.turn

/-- A bound clearing's post-state has the well-formedness needed for commitment faithfulness. -/
theorem MarketBoundaryBinding.postWF {S : CommitSurface} {pi : BatchPublicInputs} {c : DrexClearing}
    (h : MarketBoundaryBinding S pi c) : AccountsWF c.post :=
  settleRing_preserves_accountsWF h.preWF c.settled

/-- The public inputs generated from a concrete clearing and commitment surface.  This is an honest
witness that `MarketBoundaryBinding` is satisfiable; it does not claim that the deployed verifier
currently constructs these inputs from fhEgg or a serialized Market claim. -/
def publicInputsOfClearing (S : CommitSurface) (effect : EffectIdx) (turn : BoundaryTurn)
    (c : DrexClearing) : BatchPublicInputs :=
  { effect := effect
    pre := S.commit c.pre turn
    post := S.commit c.post turn
    turn := turn }

/-- The boundary relation is inhabited whenever the clearing's pre-state is structurally well formed. -/
theorem marketBoundaryBinding_realizable (S : CommitSurface) (effect : EffectIdx)
    (turn : BoundaryTurn) (c : DrexClearing) (hwf : AccountsWF c.pre) :
    MarketBoundaryBinding S (publicInputsOfClearing S effect turn c) c :=
  ⟨hwf, rfl, rfl⟩

/-- A post-root changed by one cannot be smuggled through the boundary relation.  This is the negative
tooth: the binding is not merely existence of a `DrexClearing`; both public endpoints are load-bearing. -/
theorem marketBoundaryBinding_rejects_wrong_post (S : CommitSurface) (effect : EffectIdx)
    (turn : BoundaryTurn) (c : DrexClearing) :
    ¬ MarketBoundaryBinding S
      { effect := effect
        pre := S.commit c.pre turn
        post := S.commit c.post turn + 1
        turn := turn }
      c := by
  intro h
  have := h.postRoot
  simp at this

/-- A concrete, nonempty Market clearing inhabits the repaired boundary for every real commitment
surface.  Its ring has two legs and genuinely changes the demo root (proved in `CrossChainSettlement`). -/
theorem demo_market_boundary_realizable (S : CommitSurface) :
    MarketBoundaryBinding S
      (publicInputsOfClearing S 0 ⟨0, 0, 0, 0⟩ demoFill) demoFill :=
  marketBoundaryBinding_realizable S 0 ⟨0, 0, 0, 0⟩ demoFill demoSettlePre_accountsWF

#guard demoFill.nodes.length == 2
#guard demoRoot demoFill.post != demoRoot demoFill.pre

#assert_axioms MarketBoundaryBinding.postWF
#assert_axioms marketBoundaryBinding_realizable
#assert_axioms marketBoundaryBinding_rejects_wrong_post
#assert_axioms demo_market_boundary_realizable

/-! ## 3. The precisely named Market-effect semantic extraction. -/

/-- **The maximal endpoint-level fragment at the current apex.**  The designated single effect's
kernel endpoints admit a fair, kernel-real clearing.  Because `DrexClearing.settled` executes the
allocation's settlement list, this is a real state-transition statement, but it deliberately does NOT
claim that the single `FullActionA` retained the allocation identity. -/
def MarketEffectStepExtractsClearing (marketEffect : EffectIdx) : Prop :=
  ∀ (pre post : RecChainedState), dispatchArm marketEffect pre post →
    ∃ c : DrexClearing, c.pre = pre.kernel ∧ c.post = post.kernel

/-- The endpoint extraction hypothesis consumed by the outward composition. -/
abbrev MarketEffectEndpointExtractionResidual := MarketEffectStepExtractsClearing

/-- The exact ordinary effect list induced by a clearing allocation. -/
def clearingActions (c : DrexClearing) : List FullActionA :=
  ringActions (settlementsOf c.nodes)

/-- **The DrEX allocation lowering, unconditional.**  Every proof-carrying clearing already contains
the facts needed by `settleRing_refines_turnSpec`: `CycleValid` plus positive wants make its settlement
ring `RingBalanced`, and `c.settled` is the real kernel fold.  Thus its exact allocation lowers to the
ordinary action list, including the uniquely determined receipt-chain post-state. -/
theorem drexClearing_refines_turnSpec (c : DrexClearing) (log : List Turn) :
    turnSpec ⟨c.pre, log⟩ (clearingActions c)
      ⟨c.post, ringReceiptLog (settlementsOf c.nodes) log⟩ := by
  apply settleRing_refines_turnSpec log
  · exact cycleValid_settlement_balanced c.valid c.wantPos
  · exact c.settled

/-! ### The one remaining apex object.

The deployed shielded-ring leaf is intended to witness more than an arbitrary `DrexClearing`: its
hidden-note legs are fused to the matcher rows.  We retain that object explicitly so the remaining
descriptor theorem cannot discard `LegFused` while claiming the shielded theorem. -/

/-- A two-leg DrEX clearing together with the shielded member-spend ring whose rows it clears. -/
structure FusedDrexClearing where
  poolOf : AssetId → CellId
  ring : ShieldedRing poolOf
  clearing : DrexClearing
  nodes_eq : clearing.nodes = matchNodes ring
  fused : ∀ leg ∈ ring, LegFused leg
  twoLeg : clearing.nodes.length = 2

/-- The semantic step the shielded-ring apex must extract.  Besides the fused fair clearing and exact
kernel endpoints, the receipt log is the one forced by lowering that clearing's settlement list. -/
def ShieldedRingApexStep (pre post : RecChainedState) : Prop :=
  ∃ f : FusedDrexClearing,
    f.clearing.pre = pre.kernel ∧
    f.clearing.post = post.kernel ∧
    post.log = ringReceiptLog (settlementsOf f.clearing.nodes) pre.log

/-- **The exact remaining descriptor refinement.**  A satisfying shielded-ring descriptor whose
*own trace publication* is the commitment decoded as `pre/post` must yield the whole fused clearing
above.  The explicit `tracePublishedCommit t = pc` premise is load-bearing: without it a descriptor
theorem could decode an unrelated public commitment.  This is stronger than recognizing six
`[nullifier, root, value_binding]` lanes: it binds creators, allocation rows, kernel endpoints, and
the receipt chain. -/
def ShieldedRingDescriptorRefines (S : CommitSurface) (hash : List Int → Int)
    (d : EffectVmDescriptor2) : Prop :=
  Poseidon2SpongeCR hash →
  ∀ minit mfin maddrs t pc pre post,
    Satisfied2 hash d minit mfin maddrs t →
    tracePublishedCommit t = pc →
    StateDecode S pc pre post →
    ShieldedRingApexStep pre post

abbrev ShieldedRingApexRefinementResidual := ShieldedRingDescriptorRefines

/-- The apex semantic object is inhabited by a genuine fused, funded bilateral swap. -/
def fusedSettlePre : RecordKernelState where
  accounts := {1, 2}
  cell := fun c =>
    if c ∈ ({1, 2} : Finset CellId) then Value.record [("balance", Value.int 0)] else default
  caps := fun _ => []
  bal := fun c a => if c = 1 ∧ a = 0 then 3 else if c = 2 ∧ a = 1 then 4 else 0

def fusedSettlePost : RecordKernelState :=
  (settleRing fusedSettlePre (settlementsOf fusedCycle)).get (by decide)

theorem fusedSettle_settles :
    settleRing fusedSettlePre (settlementsOf fusedCycle) = some fusedSettlePost :=
  (Option.some_get (by decide)).symm

def fusedDrexClearing : DrexClearing where
  pre := fusedSettlePre
  post := fusedSettlePost
  nodes := fusedCycle
  valid := fusedCycle_valid
  wantPos := by decide
  settled := fusedSettle_settles

def fusedDrexWitness : FusedDrexClearing where
  poolOf := Dregg2.Shielded.poolDemo
  ring := fusedRing
  clearing := fusedDrexClearing
  nodes_eq := by
    change fusedCycle = matchNodes fusedRing
    exact fusedRing_nodes.symm
  fused := fusedRing_all_fused
  twoLeg := rfl

theorem shieldedRingApexStep_realizable :
    ShieldedRingApexStep ⟨fusedSettlePre, []⟩
      ⟨fusedSettlePost, ringReceiptLog (settlementsOf fusedCycle) []⟩ :=
  ⟨fusedDrexWitness, rfl, rfl, rfl⟩

/-- A shielded-ring apex is observably a two-action transition: its truthful receipt chain grows by
exactly two entries.  This is the structural tooth that separates the ring apex from the ordinary
single-action dispatcher. -/
theorem ShieldedRingApexStep.log_length {pre post : RecChainedState}
    (h : ShieldedRingApexStep pre post) : post.log.length = pre.log.length + 2 := by
  obtain ⟨f, _hcpre, _hcpost, hlog⟩ := h
  rw [hlog]
  simp [ringReceiptLog, settlementsOf, chainedRing, f.twoLeg]
  omega

#guard (settlementsOf fusedDrexWitness.clearing.nodes).length == 2
#guard fusedDrexWitness.ring.all fun leg => leg.node.offerAmount > 0
#assert_axioms fusedSettle_settles
#assert_axioms shieldedRingApexStep_realizable
#assert_axioms ShieldedRingApexStep.log_length

/-- **`DrexClearingEffectRefinementResidual` (OPEN):** the missing per-effect/whole-turn descriptor
theorem.  Besides matching kernel endpoints, the extracted step must denote the exact list of ordinary
balance effects lowered from `c.nodes`; thus the allocation, not merely its final roots, is retained.

A faithful implementation can discharge this by adding a genuine clearing action whose descriptor
carries the allocation, or by lifting the apex to the emitted effect list.  At HEAD a public input names
one `FullActionA`, so this statement is named and not fabricated.

TRIAGE (2026-07-15, `assurance-audit`): the fair allocation is NOT trusted — it is CIRCUIT-ENFORCED. The
deployed `circuit-prove/src/shielded_ring_clearing_air.rs` binds each leg's cleared offer to a spent member
note by an in-circuit `connect` (forged leg ⇒ UNSAT), enforces the matching descriptor, nullifier
distinctness, and BOTH coordinate + range-checked INTEGER conservation; and `LedgerRealizationExt.
shielded_ring_fused_clears` proves the `CycleValid`+`LegFused` ring that settles via `settleRing` is
conserving + `RingBalanced`-fair + fused.

The LOWERING is now CLOSED by `drexClearing_refines_turnSpec`.  The raw per-leg implication originally
suggested here was slightly too weak: `recKExecAsset` omits the chained destination-liveness gate and
receipt append.  `recKExecAsset_refines_balanceMovement` states the exact step; cycle closure plus whole-
ring success derive destination liveness, and `settleRing_refines_turnSpec` performs the fold with the
exact reverse-prepended receipt log.

The viable remaining bridge is the DIRECT APEX-LIFT: the verifying ring descriptor must extract the
whole `CycleValid`+`LegFused` ring and its kernel endpoints.  It cannot pass through one `FullActionA`:
`not_marketEffectApexLiftResidual_balance` proves the tag-zero route inconsistent with the two-receipt
ring transition.  The current Rust-authored
`shielded-ring-clear-2` leaf cannot discharge that proposition: its public claim is exactly the six
note lanes `[nf₀,root₀,vb₀,nf₁,root₁,vb₁]`; neither creator, eight-lane kernel pre/post commitments,
turn count, authorization/lifecycle state, nor receipt-chain output is present.  It proves the hidden-
note fusion/cycle/conservation algebra, but not an executor transition.  Closure therefore requires a
Lean-authored endpoint-carrying outer descriptor (architectural law #1), binding these note rows to the
two ordinary balance actions and the batch's decoded pre/post commitment surface. -/
def MarketEffectAllocationIdentity (marketEffect : EffectIdx) : Prop :=
  ∀ (pre post : RecChainedState), dispatchArm marketEffect pre post →
    ∃ c : DrexClearing,
      c.pre = pre.kernel ∧ c.post = post.kernel ∧
      turnSpec pre (clearingActions c) post

abbrev DrexClearingEffectRefinementResidual := MarketEffectAllocationIdentity

/-- **The historical dispatch-level apex lift.**  This proposition records the once-proposed route
through the ordinary single-action registry arm.  The negative theorem below shows that route is
actually impossible for the deployed balance tag `0`: a balance arm appends one receipt, whereas a
fused clearing appends two.  The viable route is therefore the direct endpoint-carrying ring
descriptor `ShieldedRingDescriptorRefines`, not a coercion of the ring to one `FullActionA`. -/
def MarketEffectExtractsShieldedRing (marketEffect : EffectIdx) : Prop :=
  ∀ (pre post : RecChainedState), dispatchArm marketEffect pre post →
    ShieldedRingApexStep pre post

abbrev MarketEffectApexLiftResidual := MarketEffectExtractsShieldedRing

/-- If a registry arm did retain the fused clearing and its endpoint/log binding,
`drexClearing_refines_turnSpec` would supply the exact ordinary action list.  The implication is useful
as a shape theorem, but `not_marketEffectApexLiftResidual_balance` below proves that its tag-zero
premise cannot hold; the direct ring-descriptor route is the deployable one. -/
theorem marketEffectAllocationIdentity_of_apex_lift (marketEffect : EffectIdx)
    (h : MarketEffectApexLiftResidual marketEffect) :
    MarketEffectAllocationIdentity marketEffect := by
  intro pre post hstep
  obtain ⟨f, hcpre, hcpost, hlog⟩ := h pre post hstep
  refine ⟨f.clearing, hcpre, hcpost, ?_⟩
  have hlower := drexClearing_refines_turnSpec f.clearing pre.log
  simpa [hcpre, hcpost, ← hlog] using hlower

/-- Tag zero names exactly the ordinary per-asset balance constructor. -/
theorem actionTag_eq_zero_iff (fa : FullActionA) :
    actionTag fa = 0 ↔ ∃ t a, fa = .balanceA t a := by
  cases fa <;> simp [actionTag]

/-- Every successful tag-zero dispatcher arm is one receipt long. -/
theorem dispatchArm_balance_log_length {pre post : RecChainedState}
    (h : dispatchArm 0 pre post) : post.log.length = pre.log.length + 1 := by
  obtain ⟨fa, htag, hstep⟩ := h
  obtain ⟨t, a, rfl⟩ := (actionTag_eq_zero_iff fa).mp htag
  change BalanceMovementSpec pre t a post at hstep
  rw [hstep.2.2.1]
  simp

/-- **The dispatch route is refuted, not merely unfinished.**  The funded fused witness supplies a
real first balance step, whose log grows by one.  If tag zero extracted a whole fused ring, the same
post-log would have to grow by two.  Thus `MarketEffectApexLiftResidual 0` is uninhabited; an honest
APEX-LIFT must use the direct ring descriptor and its whole-turn endpoints. -/
theorem not_marketEffectApexLiftResidual_balance : ¬ MarketEffectApexLiftResidual 0 := by
  intro hlift
  have hlower := drexClearing_refines_turnSpec fusedDrexWitness.clearing ([] : List Turn)
  have hlen : (settlementsOf fusedDrexWitness.clearing.nodes).length = 2 := by
    simp [settlementsOf, chainedRing, fusedDrexWitness.twoLeg]
  cases hr : settlementsOf fusedDrexWitness.clearing.nodes with
  | nil => simp [hr] at hlen
  | cons leg rest =>
      simp only [clearingActions, ringActions, hr, List.map_cons, turnSpec] at hlower
      obtain ⟨mid, hstep, _htail⟩ := hlower
      have hdispatch : dispatchArm 0 ⟨fusedDrexWitness.clearing.pre, []⟩ mid :=
        ⟨.balanceA leg.toTurn leg.asset, rfl, hstep⟩
      have hone := dispatchArm_balance_log_length hdispatch
      have htwo := ShieldedRingApexStep.log_length (hlift _ _ hdispatch)
      omega

/-- Exact allocation refinement implies the endpoint fragment used by the current commitment-surface
composition.  The converse is intentionally absent. -/
theorem marketEffectStepExtractsClearing_of_allocation_identity
    (marketEffect : EffectIdx) (h : MarketEffectAllocationIdentity marketEffect) :
    MarketEffectStepExtractsClearing marketEffect := by
  intro pre post hstep
  obtain ⟨c, hcpre, hcpost, _⟩ := h pre post hstep
  exact ⟨c, hcpre, hcpost⟩

#guard (clearingActions demoFill).length == 2
#guard ringReceiptLog (settlementsOf demoFill.nodes) [] ==
  (settlementsOf demoFill.nodes).reverse.map RingLeg.toTurn
#assert_axioms drexClearing_refines_turnSpec
#assert_axioms marketEffectAllocationIdentity_of_apex_lift
#assert_axioms actionTag_eq_zero_iff
#assert_axioms dispatchArm_balance_log_length
#assert_axioms not_marketEffectApexLiftResidual_balance
#assert_axioms marketEffectStepExtractsClearing_of_allocation_identity

/-- The historical outward statement: for the registry's designated Market effect, an accepted STARK
extracts a real `DrexClearing` whose executor endpoints are the public roots.

This is stronger than importing both towers and weaker than revealing the private order book.  The
clearing can remain existential/zero-knowledge; its `valid`, `wantPos`, and `settled` proofs ensure
fairness and kernel-real conservation.  It is retained as the convenient outward interface, but the
theorem below derives it from the ordinary STARK floors plus only the narrowly named
`MarketEffectStepExtractsClearing` descriptor fact. -/
def StarkMarketClaimExtraction (S : CommitSurface) (R : Registry) (marketEffect : EffectIdx) : Prop :=
  ∀ (pi : BatchPublicInputs) (π : BatchProof), pi.effect = marketEffect →
    verifyBatch (vkOfRegistry R) pi π = Verdict.accept →
    ∃ c : DrexClearing, MarketBoundaryBinding S pi c

/-- A compact alias used by the horizon ledger: this is an obligation, not an assumption or axiom. -/
abbrev StarkMarketClaimExtractionResidual := StarkMarketClaimExtraction

/-- **The accept-level extractor, factored honestly.**  The deployed STARK apex supplies a satisfying
trace and decoded kernel step; the sole Market-specific input is that the designated step's endpoints
admit a proof-carrying clearing.  Commitment roots are inherited from `StateDecode` rather than assumed
by the Market fact.  Allocation identity remains the stronger named residual above. -/
theorem starkMarketClaimExtraction_of_effect_step
    (hash : List Int → Int) (S : CommitSurface) (R : Registry) (marketEffect : EffectIdx)
    (hCR : Poseidon2SpongeCR hash) [StarkSound hash R]
    (hrefines : ∀ e, descriptorRefines S hash (R e) (dispatchArm e))
    (hmarket : MarketEffectEndpointExtractionResidual marketEffect)
    (hwitdec : ∀ pi : BatchPublicInputs, WitnessDecodes hash R S pi) :
    StarkMarketClaimExtraction S R marketEffect := by
  intro pi π heffect hacc
  obtain ⟨pre, post, hdecode, hstep, _hpre, _hpost⟩ :=
    lightclient_unfoolable hash S R hCR dispatchArm hrefines pi π (hwitdec pi) hacc
  have hmarketStep : dispatchArm marketEffect pre post := by
    simpa only [heffect] using hstep
  obtain ⟨c, hcpre, hcpost⟩ := hmarket pre post hmarketStep
  refine ⟨c, ?_⟩
  refine ⟨hcpre ▸ hdecode.preWF, ?_, ?_⟩
  · calc
      pi.pre = S.commit pre.kernel pi.turn := hdecode.preBinds
      _ = S.commit c.pre pi.turn := by rw [hcpre]
  · calc
      pi.post = S.commit post.kernel pi.turn := hdecode.postBinds
      _ = S.commit c.post pi.turn := by rw [hcpost]

#assert_axioms starkMarketClaimExtraction_of_effect_step

/-! ### The direct shielded-descriptor route.

The generic single-action `dispatchArm` is not needed once the market registry entry itself refines to
`ShieldedRingApexStep`.  This is the faithful apex shape for a ring descriptor: STARK extraction gives
its satisfying trace, state decode gives the committed endpoints, and the descriptor theorem gives the
whole fused clearing. -/

/-- A verifying proof of the designated shielded-ring descriptor extracts decoded endpoints and the
whole fused clearing directly. -/
theorem shieldedRingApexStep_of_accept
    (hash : List Int → Int) (S : CommitSurface) (R : Registry) (marketEffect : EffectIdx)
    (hCR : Poseidon2SpongeCR hash) [StarkSound hash R]
    (hmarket : ShieldedRingApexRefinementResidual S hash (R marketEffect))
    (pi : BatchPublicInputs) (π : BatchProof) (heffect : pi.effect = marketEffect)
    (hwitdec : WitnessDecodes hash R S pi)
    (hacc : verifyBatch (vkOfRegistry R) pi π = Verdict.accept) :
    ∃ pre post : RecChainedState,
      StateDecode S pi.toPublished pre post ∧ ShieldedRingApexStep pre post := by
  obtain ⟨minit, mfin, maddrs, t, hsat, hpub⟩ :=
    (inferInstance : StarkSound hash R).extract pi π hacc
  obtain ⟨pre, post, hdecode⟩ := hwitdec minit mfin maddrs t hsat hpub
  have hsatMarket : Satisfied2 hash (R marketEffect) minit mfin maddrs t := by
    simpa only [heffect] using hsat
  have hapex : ShieldedRingApexStep pre post :=
    hmarket hCR minit mfin maddrs t pi.toPublished pre post hsatMarket hpub hdecode
  exact ⟨pre, post, hdecode, hapex⟩

/-- The historical accept-level Market extraction follows from the exact shielded descriptor
refinement, without an opaque endpoint extractor or the ordinary single-action dispatcher. -/
theorem starkMarketClaimExtraction_of_shielded_descriptor
    (hash : List Int → Int) (S : CommitSurface) (R : Registry) (marketEffect : EffectIdx)
    (hCR : Poseidon2SpongeCR hash) [StarkSound hash R]
    (hmarket : ShieldedRingApexRefinementResidual S hash (R marketEffect))
    (hwitdec : ∀ pi : BatchPublicInputs, WitnessDecodes hash R S pi) :
    StarkMarketClaimExtraction S R marketEffect := by
  intro pi π heffect hacc
  obtain ⟨pre, post, hdecode, f, hcpre, hcpost, _hlog⟩ :=
    shieldedRingApexStep_of_accept hash S R marketEffect hCR hmarket pi π heffect
      (hwitdec pi) hacc
  refine ⟨f.clearing, ?_⟩
  refine ⟨hcpre ▸ hdecode.preWF, ?_, ?_⟩
  · calc
      pi.pre = S.commit pre.kernel pi.turn := hdecode.preBinds
      _ = S.commit f.clearing.pre pi.turn := by rw [hcpre]
  · calc
      pi.post = S.commit post.kernel pi.turn := hdecode.postBinds
      _ = S.commit f.clearing.post pi.turn := by rw [hcpost]

#assert_axioms shieldedRingApexStep_of_accept
#assert_axioms starkMarketClaimExtraction_of_shielded_descriptor

/-! ## 4. What the two verified towers prove from the narrowed effect-refinement residual. -/

/-- **The STARK↔Market composition theorem.**  The ordinary light-client floors derive decoded endpoints
and a real dispatcher step; only the narrowly Market-specific effect-refinement fact is supplied.
Commitment binding then identifies those endpoints with the extracted fair, kernel-settled Market
clearing.  The same post-state therefore conserves every asset. -/
theorem lightclient_market_seam
    (hash : List Int → Int) (S : CommitSurface) (R : Registry) (marketEffect : EffectIdx)
    (hCR : Poseidon2SpongeCR hash) [StarkSound hash R]
    (hrefines : ∀ e, descriptorRefines S hash (R e) (dispatchArm e))
    (hmarket : MarketEffectEndpointExtractionResidual marketEffect)
    (pi : BatchPublicInputs) (π : BatchProof)
    (heffect : pi.effect = marketEffect)
    (hwitdec : WitnessDecodes hash R S pi)
    (hacc : verifyBatch (vkOfRegistry R) pi π = Verdict.accept) :
    ∃ (c : DrexClearing) (pre post : RecChainedState),
      MarketBoundaryBinding S pi c ∧
      StateDecode S pi.toPublished pre post ∧
      dispatchArm pi.effect pre post ∧
      pre.kernel = c.pre ∧ post.kernel = c.post ∧
      ∀ b : AssetId, recTotalAsset post.kernel b = recTotalAsset pre.kernel b := by
  obtain ⟨pre, post, hdecode, hstep, _hpre, _hpost⟩ :=
    lightclient_unfoolable hash S R hCR dispatchArm hrefines pi π hwitdec hacc
  have hmarketStep : dispatchArm marketEffect pre post := by
    simpa only [heffect] using hstep
  obtain ⟨c, hcpre, hcpost⟩ := hmarket pre post hmarketStep
  have hbound : MarketBoundaryBinding S pi c := by
    refine ⟨hcpre ▸ hdecode.preWF, ?_, ?_⟩
    · calc
        pi.pre = S.commit pre.kernel pi.turn := hdecode.preBinds
        _ = S.commit c.pre pi.turn := by rw [hcpre]
    · calc
        pi.post = S.commit post.kernel pi.turn := hdecode.postBinds
        _ = S.commit c.post pi.turn := by rw [hcpost]
  have hpreCommit : S.commit pre.kernel pi.turn = S.commit c.pre pi.turn := by
    calc
      S.commit pre.kernel pi.turn = pi.pre := hdecode.preBinds.symm
      _ = S.commit c.pre pi.turn := hbound.preRoot
  have hpostCommit : S.commit post.kernel pi.turn = S.commit c.post pi.turn := by
    calc
      S.commit post.kernel pi.turn = pi.post := hdecode.postBinds.symm
      _ = S.commit c.post pi.turn := hbound.postRoot
  have hpreEq : pre.kernel = c.pre :=
    S.commit_binds pre.kernel c.pre pi.turn hdecode.preWF hbound.preWF hpreCommit
  have hpostEq : post.kernel = c.post :=
    S.commit_binds post.kernel c.post pi.turn hdecode.postWF hbound.postWF hpostCommit
  refine ⟨c, pre, post, hbound, hdecode, hstep, hpreEq, hpostEq, ?_⟩
  intro b
  rw [hpreEq, hpostEq]
  exact no_minting_drex_clearing c b

/-- **The direct STARK↔Market seam at the correct ring apex.**  Compared with the historical
`lightclient_market_seam`, this consumes only the exact descriptor refinement, extracts the fused ring
itself, and exports the proved exact `turnSpec` allocation lowering as part of the conclusion. -/
theorem lightclient_market_seam_of_shielded_descriptor
    (hash : List Int → Int) (S : CommitSurface) (R : Registry) (marketEffect : EffectIdx)
    (hCR : Poseidon2SpongeCR hash) [StarkSound hash R]
    (hmarket : ShieldedRingApexRefinementResidual S hash (R marketEffect))
    (pi : BatchPublicInputs) (π : BatchProof)
    (heffect : pi.effect = marketEffect)
    (hwitdec : WitnessDecodes hash R S pi)
    (hacc : verifyBatch (vkOfRegistry R) pi π = Verdict.accept) :
    ∃ (f : FusedDrexClearing) (pre post : RecChainedState),
      MarketBoundaryBinding S pi f.clearing ∧
      StateDecode S pi.toPublished pre post ∧
      ShieldedRingApexStep pre post ∧
      turnSpec pre (clearingActions f.clearing) post ∧
      ∀ b : AssetId, recTotalAsset post.kernel b = recTotalAsset pre.kernel b := by
  obtain ⟨pre, post, hdecode, f, hcpre, hcpost, hlog⟩ :=
    shieldedRingApexStep_of_accept hash S R marketEffect hCR hmarket pi π heffect hwitdec hacc
  have hbound : MarketBoundaryBinding S pi f.clearing := by
    refine ⟨hcpre ▸ hdecode.preWF, ?_, ?_⟩
    · calc
        pi.pre = S.commit pre.kernel pi.turn := hdecode.preBinds
        _ = S.commit f.clearing.pre pi.turn := by rw [hcpre]
    · calc
        pi.post = S.commit post.kernel pi.turn := hdecode.postBinds
        _ = S.commit f.clearing.post pi.turn := by rw [hcpost]
  have hlower := drexClearing_refines_turnSpec f.clearing pre.log
  have hturn : turnSpec pre (clearingActions f.clearing) post := by
    simpa [hcpre, hcpost, ← hlog] using hlower
  refine ⟨f, pre, post, hbound, hdecode, ⟨f, hcpre, hcpost, hlog⟩, hturn, ?_⟩
  intro b
  rw [← hcpre, ← hcpost]
  exact no_minting_drex_clearing f.clearing b

/-- **The full outward composition on one commitment surface.**  If a target-chain register is anchored
at the accepted batch's public pre-root, the extracted Market clearing advances it to exactly the
accepted public post-root, while that transition is the same decoded STARK transition and conserves
every asset.  The former accept-level extractor is no longer assumed; its one Market-specific
hypothesis is the endpoint fragment `MarketEffectEndpointExtractionResidual`.  Exact allocation
identity remains `DrexClearingEffectRefinementResidual`. -/
theorem accepted_market_settles_on_same_commitment_surface
    (hash : List Int → Int) (S : CommitSurface) (R : Registry) (marketEffect : EffectIdx)
    (hCR : Poseidon2SpongeCR hash) [StarkSound hash R]
    (hrefines : ∀ e, descriptorRefines S hash (R e) (dispatchArm e))
    (hmarket : MarketEffectEndpointExtractionResidual marketEffect)
    (pi : BatchPublicInputs) (π : BatchProof)
    (heffect : pi.effect = marketEffect)
    (hwitdec : WitnessDecodes hash R S pi)
    (hacc : verifyBatch (vkOfRegistry R) pi π = Verdict.accept)
    (target : ProvenState Int) (hanchor : target.provenRoot = pi.pre) :
    ∃ (c : DrexClearing) (target' : ProvenState Int),
      MarketBoundaryBinding S pi c ∧
      settleDrex (fun k => S.commit k pi.turn) target c = some target' ∧
      target'.provenRoot = pi.post ∧
      target'.provenHeight = target.provenHeight + c.nodes.length ∧
      ∀ b : AssetId, recTotalAsset c.post b = recTotalAsset c.pre b := by
  obtain ⟨pre, post, hdecode, hstep, _hpre, _hpost⟩ :=
    lightclient_unfoolable hash S R hCR dispatchArm hrefines pi π hwitdec hacc
  have hmarketStep : dispatchArm marketEffect pre post := by
    simpa only [heffect] using hstep
  obtain ⟨c, hcpre, hcpost⟩ := hmarket pre post hmarketStep
  have hbound : MarketBoundaryBinding S pi c := by
    refine ⟨hcpre ▸ hdecode.preWF, ?_, ?_⟩
    · calc
        pi.pre = S.commit pre.kernel pi.turn := hdecode.preBinds
        _ = S.commit c.pre pi.turn := by rw [hcpre]
    · calc
        pi.post = S.commit post.kernel pi.turn := hdecode.postBinds
        _ = S.commit c.post pi.turn := by rw [hcpost]
  have hcont : S.commit c.pre pi.turn = target.provenRoot := by
    calc
      S.commit c.pre pi.turn = pi.pre := hbound.preRoot.symm
      _ = target.provenRoot := hanchor.symm
  obtain ⟨target', hsettle, hroot, hheight, hconserve, _⟩ :=
    drex_fill_cross_chain_settleable (fun k => S.commit k pi.turn) target c hcont
  refine ⟨c, target', hbound, hsettle, ?_, hheight, hconserve⟩
  calc
    target'.provenRoot = S.commit c.post pi.turn := hroot
    _ = pi.post := hbound.postRoot.symm

#assert_axioms lightclient_market_seam
#assert_axioms lightclient_market_seam_of_shielded_descriptor
#assert_axioms accepted_market_settles_on_same_commitment_surface

/-! ## 5. The deployed 25-lane settlement-verifier obligation (also open).

The old residual used generic scalar `Root` arguments and therefore hid two load-bearing deployed
facts: Groth16 verifies exactly 25 BabyBear public inputs, and Solidity records a keccak of the tight
big-endian encoding of each eight-lane root.  The exact codec and accept-path checks are executable
below; only the cryptographic/extraction implication remains a residual. -/

/-- One deployed Poseidon/BabyBear digest, with width fixed by the ABI rather than a list-length
premise. -/
abbrev Lane8 := Fin 8 → Nat

def babyBearP : Nat := 2013265921

/-- Array order as used by gnark and Solidity. -/
def lane8List (x : Lane8) : List Nat := List.ofFn x

/-- The Solidity `uint32` tight big-endian byte encoding (`abi.encodePacked(uint32)`). -/
def u32be (x : Nat) : List Nat :=
  [x / 16777216 % 256, x / 65536 % 256, x / 256 % 256, x % 256]

/-- The exact 32-byte preimage passed to `keccak256` by `DreggSettlement.packLanes`. -/
def packLaneBytes (x : Lane8) : List Nat := (lane8List x).flatMap u32be

/-- The public statement of the deployed Groth16 wrapper. -/
structure SettlementPublics25 where
  genesisRoot : Lane8
  finalRoot : Lane8
  numTurns : Nat
  chainDigest : Lane8

/-- Pinned gnark/Solidity order:
`genesis[0..8) ++ final[8..16) ++ numTurns[16] ++ chainDigest[17..25)`. -/
def SettlementPublics25.toInputs (pub : SettlementPublics25) : List Nat :=
  lane8List pub.genesisRoot ++ lane8List pub.finalRoot ++ [pub.numTurns] ++
    lane8List pub.chainDigest

def lane8Canonical (x : Lane8) : Bool :=
  (lane8List x).all fun v => decide (v < babyBearP)

/-- The canonical-field checks performed by `DreggSettlement.settle` before the pairing call. -/
def SettlementPublics25.canonical (pub : SettlementPublics25) : Bool :=
  lane8Canonical pub.genesisRoot && lane8Canonical pub.finalRoot &&
    decide (pub.numTurns < babyBearP) && lane8Canonical pub.chainDigest

/-- The proof-dependent portion of the deployed accept path: canonical 25-lane public inputs,
strictly positive turn count, and a successful pairing check.  Continuity against `_provenLanes` is
the subsequent state-machine gate already modeled by `settleDrex`. -/
def settlementVerifierAccept
    (verifyProof : List Nat → List Nat → Bool) (proofBytes : List Nat)
    (pub : SettlementPublics25) : Bool :=
  pub.canonical && decide (0 < pub.numTurns) && verifyProof proofBytes pub.toInputs

theorem lane8List_length (x : Lane8) : (lane8List x).length = 8 := by
  simp [lane8List]

theorem packLaneBytes_length (x : Lane8) : (packLaneBytes x).length = 32 := by
  simp [packLaneBytes, lane8List, u32be]

theorem settlementPublicInputs_length (pub : SettlementPublics25) : pub.toInputs.length = 25 := by
  simp [SettlementPublics25.toInputs, lane8List]

theorem settlementVerifierAccept_numTurns_pos
    (verifyProof : List Nat → List Nat → Bool) (proofBytes : List Nat)
    (pub : SettlementPublics25) (hacc : settlementVerifierAccept verifyProof proofBytes pub = true) :
    0 < pub.numTurns := by
  simp [settlementVerifierAccept] at hacc
  exact hacc.1.2

/-- **`SettlementVerifierRefinementResidual` (OPEN, tightened):** successful verification of the exact
25-lane statement must extract a fair, kernel-real `DrexClearing`, whose kernel states encode to the
published eight-lane roots and whose ring length is the published `numTurns`.  The chain digest is not
dropped: it is present in `pub.toInputs`, so the same pairing acceptance binds it even though the
Market conclusion does not consume history here.

This is precisely what `settleDrex` cannot establish: `settleDrex` starts after extraction, with `c`
already supplied.  Closing it requires the Groth16 knowledge/soundness bridge through the recursive
STARK wrapper plus the Market shielded-apex extraction above, and a faithful `stateLanes` codec for the
deployed eight-lane state commitment. -/
def SettlementVerifier25Refines
    (verifyProof : List Nat → List Nat → Bool)
    (stateLanes : RecordKernelState → Lane8) : Prop :=
  ∀ (proofBytes : List Nat) (pub : SettlementPublics25),
    settlementVerifierAccept verifyProof proofBytes pub = true →
    ∃ c : DrexClearing,
      stateLanes c.pre = pub.genesisRoot ∧
      stateLanes c.post = pub.finalRoot ∧
      c.nodes.length = pub.numTurns

abbrev SettlementVerifierRefinementResidual := SettlementVerifier25Refines

/-- Solidity's recorded root, parameterized only by the deployed `keccak256` byte hash. -/
def packedLaneRoot {Root : Type} (keccak : List Nat → Root) (x : Lane8) : Root :=
  keccak (packLaneBytes x)

/-- **Eight-lane packing reduction.**  Exact lane extraction immediately binds the two roots recorded
by EVM/CosmWasm/Solana clients; no injectivity of the compressing keccak is fabricated or needed. -/
theorem accepted_settlement_binds_packed_roots {Root : Type}
    (verifyProof : List Nat → List Nat → Bool)
    (stateLanes : RecordKernelState → Lane8)
    (hverify : SettlementVerifierRefinementResidual verifyProof stateLanes)
    (keccak : List Nat → Root) (proofBytes : List Nat) (pub : SettlementPublics25)
    (hacc : settlementVerifierAccept verifyProof proofBytes pub = true) :
    ∃ c : DrexClearing,
      packedLaneRoot keccak (stateLanes c.pre) = packedLaneRoot keccak pub.genesisRoot ∧
      packedLaneRoot keccak (stateLanes c.post) = packedLaneRoot keccak pub.finalRoot ∧
      c.nodes.length = pub.numTurns := by
  obtain ⟨c, hpre, hpost, hnum⟩ := hverify proofBytes pub hacc
  exact ⟨c, by rw [hpre], by rw [hpost], hnum⟩

def demoLanes (a b : Nat) : Lane8 := fun i =>
  if i = 0 then a else if i = 1 then b else 0

def demoSettlementPublics : SettlementPublics25 where
  genesisRoot := demoLanes 7 5
  finalRoot := demoLanes 0 0
  numTurns := 2
  chainDigest := demoLanes 11 13

#guard u32be 0x01020304 == [1, 2, 3, 4]
#guard (packLaneBytes (demoLanes 0x01020304 0x05060708)).take 8 ==
  [1, 2, 3, 4, 5, 6, 7, 8]
#guard demoSettlementPublics.toInputs.length == 25
#guard settlementVerifierAccept (fun _ _ => true) [42] demoSettlementPublics == true
#guard settlementVerifierAccept (fun _ _ => true) [42]
  { demoSettlementPublics with numTurns := 0 } == false

#assert_axioms lane8List_length
#assert_axioms packLaneBytes_length
#assert_axioms settlementPublicInputs_length
#assert_axioms settlementVerifierAccept_numTurns_pos
#assert_axioms accepted_settlement_binds_packed_roots

end Market.ProtocolAssurance
