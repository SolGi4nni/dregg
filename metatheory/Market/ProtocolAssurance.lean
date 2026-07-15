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
* `DrexClearingEffectRefinementResidual` names the strictly stronger fact still absent: the clearing's
  exact allocation lowers to the ordinary balance-action list that the extracted step denotes.  This
  distinction prevents endpoint equivalence from being mislabeled as trace/allocation identity.
* `starkMarketClaimExtraction_of_effect_step`, `lightclient_market_seam`, and
  `accepted_market_settles_on_same_commitment_surface` prove everything above that exact descriptor
  fact: the decoded STARK transition is the fair, kernel-real clearing; it conserves every asset; and
  the cross-chain register advances from the same pre-commitment to the same post-commitment.
* `SettlementVerifierRefines` names the second missing theorem.  The current `settleDrex` consumes a
  pre-proved `DrexClearing` and models only continuity plus register update.  The deployed Groth16
  verifier consumes bytes.  Its soundness must imply existence of the `DrexClearing` whose roots and
  turn count it accepted.

The repaired cross-chain witness is also shown to satisfy `AccountsWF`, the structural invariant
required by `StateDecode`.  Previously its `cell` function was non-default outside `{1,2}`, so the
Market demo could not inhabit the light-client boundary at all.

At HEAD the single-effect dispatcher has no `DrexClearing` constructor: a clearing contains at least
two settlement legs, while `BatchPublicInputs.effect` selects one `FullActionA`.  The operated DrEX
path lowers a clearing to a list of ordinary effects, but that list/allocation is not part of this
single-effect apex.  Therefore the final descriptor/whole-turn extraction remains named precisely
below; it cannot honestly be manufactured from the four public-input fields.

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
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Circuit.ActionDispatch (turnSpec)
open Dregg2.Exec.TurnExecutorFull (FullActionA)

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
  (settlementsOf c.nodes).map fun l => .balanceA l.toTurn l.asset

/-- **`DrexClearingEffectRefinementResidual` (OPEN):** the missing per-effect/whole-turn descriptor
theorem.  Besides matching kernel endpoints, the extracted step must denote the exact list of ordinary
balance effects lowered from `c.nodes`; thus the allocation, not merely its final roots, is retained.

A faithful implementation can discharge this by adding a genuine clearing action whose descriptor
carries the allocation, or by lifting the apex to the emitted effect list.  At HEAD a public input names
one `FullActionA`, so this statement is named and not fabricated. -/
def MarketEffectAllocationIdentity (marketEffect : EffectIdx) : Prop :=
  ∀ (pre post : RecChainedState), dispatchArm marketEffect pre post →
    ∃ c : DrexClearing,
      c.pre = pre.kernel ∧ c.post = post.kernel ∧
      turnSpec pre (clearingActions c) post

abbrev DrexClearingEffectRefinementResidual := MarketEffectAllocationIdentity

/-- Exact allocation refinement implies the endpoint fragment used by the current commitment-surface
composition.  The converse is intentionally absent. -/
theorem marketEffectStepExtractsClearing_of_allocation_identity
    (marketEffect : EffectIdx) (h : MarketEffectAllocationIdentity marketEffect) :
    MarketEffectStepExtractsClearing marketEffect := by
  intro pre post hstep
  obtain ⟨c, hcpre, hcpost, _⟩ := h pre post hstep
  exact ⟨c, hcpre, hcpost⟩

#guard (clearingActions demoFill).length == 2
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
#assert_axioms accepted_market_settles_on_same_commitment_surface

/-! ## 5. The deployed settlement-verifier obligation (also open). -/

/-- **`SettlementVerifierRefinementResidual` (OPEN):** the semantic soundness statement required of
the deployed Groth16 verifier.  Any accepted proof bytes/public roots/turn count must imply existence
of a fair, kernel-real `DrexClearing` with exactly those roots and count.  `settleDrex` does not prove
this: it starts after this implication, with `c` already supplied as a structure.

`Root` is deliberately generic because the EVM/CosmWasm/Solana boundary uses packed eight-lane roots,
whereas `CommitSurface.commit` is the scalar metatheory surface.  A faithful deployment theorem must
instantiate `rootOf` with the actual lane packing and hash, not `demoRoot`. -/
def SettlementVerifierRefines {Root : Type}
    (verifyProof : List Nat → Root → Root → Nat → Bool)
    (rootOf : RecordKernelState → Root) : Prop :=
  ∀ (proofBytes : List Nat) (preRoot postRoot : Root) (numTurns : Nat),
    verifyProof proofBytes preRoot postRoot numTurns = true →
    ∃ c : DrexClearing,
      rootOf c.pre = preRoot ∧ rootOf c.post = postRoot ∧ c.nodes.length = numTurns

abbrev SettlementVerifierRefinementResidual {Root : Type} :=
  SettlementVerifierRefines (Root := Root)

end Market.ProtocolAssurance
