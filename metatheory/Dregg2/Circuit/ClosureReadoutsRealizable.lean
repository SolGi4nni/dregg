/-
# Dregg2.Circuit.ClosureReadoutsRealizable — survey finding #3: the uninstantiable refinement floor,
machine-checked, and its REALIZABLE restriction.

`ClosureFanoutGenuine.ClosureReadouts` carries a field

    other : ∀ e, ClosedLogExtract (S_live …) LH hash Rfix e

universally quantified over ALL effect indices. At the EMPTY tags (15, 21–26, 29–37, 41–46, 48–51)
`actionTagToPos` maps past the registry, so `Rfix e` falls back to the TRANSFER descriptor
(`transferDescr = transferV3`) while `kstepAll e` is the EMPTY relation
(`DescriptorRefinesComplete.kstepAll_not_total`: no `FullActionA` has `actionTag = 15`). So `other 15`
asserts: every honest transfer witness whose published commitments decode is a proof of `False`. The
honest transfer witness EXISTS (`FloorsNonVacuous.satisfied2_faithfulTrace`, for EVERY hash), and a
decodable boundary EXISTS (the empty-cell kernel), so the bundle is UNINSTANTIABLE whenever the two
named crypto floors (`Poseidon2SpongeCR hash`, `logHashInjective LH`) hold — which is exactly the
regime the whole tower lives in, and both are CONCRETELY inhabited (`encodeSponge`/`refLH`).

This module delivers:

  * **The finding, machine-checked** — `closedLogExtract_emptyTag_false` (any `ClosedLogExtract` at
    tag 15 refutes itself on the honest transfer witness), `closureReadouts_uninstantiable` (hence NO
    `ClosureReadouts` bundle exists under the realizable floors), and the FIRE tooth
    `closureReadouts_uninstantiable_concrete` (at the CONCRETE injective `encodeSponge`/`refLH`, with
    no crypto hypotheses left).
  * **`LiveTag`** — `e` is live iff some `FullActionA` carries it (`∃ fa, actionTag fa = e`). The old
    apex's conclusion already forces liveness (`liveTag_of_kstepAll`), so restricting to live tags
    loses NOTHING.
  * **`ClosureReadoutsLive`** — `ClosureReadouts` with the false member REMOVED: the same named
    per-effect readouts + shared carriers, NO `other` field at all. Every live tag is covered by a
    NAMED cohort readout, so the off-range fallback slot is simply gone (nothing to discharge, not
    even an UNSAT stub).
  * **The fanout still assembles** — `closedLogExtract_all_genuine_live` discharges
    `∀ e, LiveTag e → ClosedLogExtract … e` by the same 31-way case split, each slot CALLING its
    proven `closedLogExtract_<e>_closed` discharger; and the apex goes through:
    `lightclient_unfoolable_closed_final_live` (with the light client's tag-liveness check made
    explicit — the published `pi.effect` at a dead tag could never satisfy the old conclusion anyway).
  * **The gap is CLOSED, teeth on both sides** — the dead slot's conclusion relation is EMPTY
    (`kstepAll_not_total`, whence the falsity), while a live slot's conclusion relation is INHABITED
    (`kstepAll_live_inhabited_47`): the live floor has no member refutable the way `other 15` is.

NEW file; imports read-only. `#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound} throughout.
-/
import Dregg2.Circuit.ClosureFanoutGenuine
import Dregg2.Circuit.DescriptorRefinesComplete
import Dregg2.Circuit.FloorsNonVacuous
import Dregg2.Circuit.WitnessRealizing

namespace Dregg2.Circuit.ClosureReadoutsRealizable

open Dregg2.Circuit.CircuitSoundness
open Dregg2.Circuit.CircuitSoundnessAssembled
open Dregg2.Circuit.ClosureAll
open Dregg2.Circuit.ClosureFanoutGenuine
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Circuit.StateCommit (compressInjective compressNInjective cellLeafInjective
  RestHashIffFrame logHashInjective)
open Dregg2.Circuit.ClosureSurface (S_live)
open Dregg2.Circuit.ClosureLog (StateDecodeLog)
open Dregg2.Circuit.DescriptorIR2 (VmTrace Satisfied2)
open Dregg2.Circuit.ActionDispatch (actionTag)
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull (authReceipt)

set_option autoImplicit false

/-! ## §1 — `LiveTag`: the effect indices that name a real action. -/

/-- **`LiveTag e`** — the effect index `e` is LIVE: some `FullActionA` carries it as its `actionTag`.
These are exactly the 31 cohort tags {0–14, 16–20, 27, 28, 38–40, 47, 52–56}; everything else
(15, 21–26, 29–37, 41–46, 48–51, and all indices > 56) is DEAD — `kstepAll` is empty there. -/
def LiveTag (e : EffectIdx) : Prop :=
  ∃ fa : Dregg2.Exec.TurnExecutorFull.FullActionA, actionTag fa = e

/-- The old apex's CONCLUSION already forces liveness: `kstepAll e pre post` names an action of tag
`e`. So an apex hypothesis family quantified over live tags only loses NOTHING — at a dead tag the
old conclusion was unsatisfiable to begin with. -/
theorem liveTag_of_kstepAll {e : EffectIdx} {pre post : RecChainedState}
    (h : kstepAll e pre post) : LiveTag e :=
  Dregg2.Circuit.DescriptorRefinesComplete.kstepAll_discriminates h

/-- Tag 15 is DEAD: no `FullActionA` carries it (the same census as `kstepAll_not_total`). -/
theorem not_liveTag_15 : ¬ LiveTag 15 := by
  rintro ⟨fa, htag⟩
  cases fa <;> simp_all [actionTag]

/-- FIRE (liveness is inhabited): the transfer tag is live. -/
theorem liveTag_transfer : LiveTag 0 := ⟨.balanceA ⟨0, 0, 0, 0⟩ 0, rfl⟩

/-- FIRE (liveness is inhabited): the pipelinedSend tag is live. -/
theorem liveTag_pipelinedSend : LiveTag 47 := ⟨.pipelinedSendA 0, rfl⟩

/-! ## §2 — the finding: `Rfix` at the dead tag 15 is the (satisfiable) transfer descriptor, while
`kstepAll 15` is empty — so ANY `ClosedLogExtract … Rfix 15` refutes itself on the honest witness. -/

/-- At the dead tag 15 the registry lookup falls off the end (`actionTagToPos 15 = 1000`, past the
61-entry `v3RegistryHeap`), so `Rfix 15` IS the transfer fallback `transferV3`. -/
theorem Rfix_emptyTag_transfer :
    Rfix 15 = Dregg2.Circuit.RotatedKernelRefinement.transferV3 := by
  have hnone : v3RegistryHeap[actionTagToPos 15]? = none :=
    List.getElem?_eq_none (by rw [v3RegistryHeap_length]; decide)
  unfold Rfix
  rw [hnone]
  rfl

/-- **The honest witness EXISTS at the dead tag** — for EVERY hash: the faithful transfer trace
satisfies `Rfix 15` (= the transfer fallback). This is what makes `other 15` a FALSE member, not a
vacuously-dischargeable one. -/
theorem satisfied2_emptyTag_15 (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) :
    Satisfied2 hash (Rfix 15) minit mfin [] Dregg2.Circuit.FloorsNonVacuous.faithfulTrace := by
  rw [Rfix_emptyTag_transfer]
  exact Dregg2.Circuit.FloorsNonVacuous.satisfied2_faithfulTrace hash minit mfin

section Falsity

variable {CH : CellId → Value → ℤ} {RH : RecordKernelState → ℤ}
variable {cmb compress : ℤ → ℤ → ℤ} {compressN : List ℤ → ℤ}
variable {hCmb : compressInjective cmb} {hCompress : compressInjective compress}
variable {hCompressN : compressNInjective compressN} {hLeaf : cellLeafInjective CH}
variable {hRest : RestHashIffFrame RH}

local notation "Slive" => S_live CH RH cmb compress compressN hCmb hCompress hCompressN hLeaf hRest

/-- **The dead slot is FALSE.** Any `ClosedLogExtract Slive LH hash Rfix 15` — in particular the
`other 15` member every `ClosureReadouts` bundle carries — yields `False`, given ANY decodable
boundary: feed it the honest transfer witness (`satisfied2_emptyTag_15`) and the decode; it must
produce `kstepAll 15 pre post`, which is EMPTY (`kstepAll_not_total`).

⚑ STRENGTHENED by the `ClosedLogExtract` port (2026-07-25): this refutation used to carry
`hCR : Poseidon2SpongeCR hash` solely to feed the bundle's now-deleted antecedent. With the antecedent
gone the hypothesis is gone, so the dead slot is refuted with NO crypto floor assumed at all — which
matters, because `Poseidon2SpongeCR` is FALSE at deployed BabyBear parameters and a refutation resting
on a false hypothesis would have proved nothing. -/
theorem closedLogExtract_emptyTag_false
    {LH : List Turn → ℤ} {hash : List ℤ → ℤ}
    {pc : PublishedCommit} {pubLogPre pubLogPost : ℤ} {pre post : RecChainedState}
    (hdec : StateDecodeLog Slive LH pc pubLogPre pubLogPost pre post)
    (hext : ClosedLogExtract Slive LH hash Rfix 15) : False :=
  Dregg2.Circuit.DescriptorRefinesComplete.kstepAll_not_total pre post
    (hext (fun _ => 0) (fun _ => (0, 0)) []
      Dregg2.Circuit.FloorsNonVacuous.faithfulTrace pc pubLogPre pubLogPost pre post
      (satisfied2_emptyTag_15 hash (fun _ => 0) (fun _ => (0, 0))) hdec)

end Falsity

/-- **The decodable boundary EXISTS** (so `closedLogExtract_emptyTag_false`'s decode hypothesis is
genuinely satisfiable): the empty-cell `AccountsWF` kernel, its own commitments published, the empty
receipt log bound through `LH`. Works for ANY surface and any injective `LH`. -/
theorem stateDecodeLog_inhabited (S : CommitSurface) (LH : List Turn → ℤ)
    (hLog : logHashInjective LH) (t : Turn) :
    ∃ (pc : PublishedCommit) (pubLogPre pubLogPost : ℤ) (pre post : RecChainedState),
      StateDecodeLog S LH pc pubLogPre pubLogPost pre post :=
  ⟨⟨S.commit Dregg2.Circuit.WitnessRealizing.emptyKernel t,
    S.commit Dregg2.Circuit.WitnessRealizing.emptyKernel t, t⟩,
   LH [], LH [],
   Dregg2.Circuit.WitnessRealizing.emptyState, Dregg2.Circuit.WitnessRealizing.emptyState,
   { toDecode :=
      { preBinds := rfl
      , postBinds := rfl
      , preWF := Dregg2.Circuit.WitnessRealizing.emptyKernel_wf
      , postWF := Dregg2.Circuit.WitnessRealizing.emptyKernel_wf }
   , hLogInj := hLog
   , logPreBinds := rfl
   , logPostBinds := rfl }⟩

/-! ## §3 — the headline finding: `ClosureReadouts` is UNINSTANTIABLE under the realizable floors. -/

/-- **Survey finding #3, machine-checked.** Under the ONE named realizable crypto floor — the log-CR
carrier `logHashInjective LH`, needed only to inhabit the decodable boundary — NO `ClosureReadouts`
bundle exists, for ANY surface/`Scap`/`compressN` parameterization: its `other 15` member is refuted by
the honest transfer witness on the empty-cell boundary. The apexes that consume the bundle only at
`pi.effect` are untouched; but "the floor is realizable" was false as stated.

⚑ The `Poseidon2SpongeCR hash` hypothesis this finding used to carry is GONE with the
`ClosedLogExtract` port — it was only ever passed through to the bundle's deleted antecedent. -/
theorem closureReadouts_uninstantiable
    {CH : CellId → Value → ℤ} {RH : RecordKernelState → ℤ}
    {cmb compress : ℤ → ℤ → ℤ} {compressN : List ℤ → ℤ}
    {hCmb : compressInjective cmb} {hCompress : compressInjective compress}
    {hCompressN : compressNInjective compressN} {hLeaf : cellLeafInjective CH}
    {hRest : RestHashIffFrame RH}
    {LH : List Turn → ℤ} {hash : List ℤ → ℤ} {State : Type}
    {Scap : Dregg2.Circuit.DeployedCapTree.Cap8Scheme}
    {cnCellSeal cnLife cnPermsVK cnBirth cnNotes cnMisc}
    (hLog : logHashInjective LH)
    (rds : @ClosureReadouts CH RH cmb compress compressN hCmb hCompress hCompressN hLeaf hRest
      LH hash State Scap cnCellSeal cnLife cnPermsVK cnBirth cnNotes cnMisc) : False := by
  obtain ⟨pc, pubLogPre, pubLogPost, pre, post, hdec⟩ :=
    stateDecodeLog_inhabited
      (S_live CH RH cmb compress compressN hCmb hCompress hCompressN hLeaf hRest) LH hLog
      ⟨0, 0, 0, 0⟩
  exact closedLogExtract_emptyTag_false hdec (rds.other 15)

/-- **FIRE.** At the CONCRETE injective floors — `encodeSponge` (proved CR) and `refLH` (proved
injective) — the uninstantiability holds with NO crypto hypotheses left: for every surface, there is
no bundle. The hypotheses of the finding are genuinely satisfiable; the refutation is unconditional at
a realizable point. -/
theorem closureReadouts_uninstantiable_concrete
    {CH : CellId → Value → ℤ} {RH : RecordKernelState → ℤ}
    {cmb compress : ℤ → ℤ → ℤ} {compressN : List ℤ → ℤ}
    {hCmb : compressInjective cmb} {hCompress : compressInjective compress}
    {hCompressN : compressNInjective compressN} {hLeaf : cellLeafInjective CH}
    {hRest : RestHashIffFrame RH} {State : Type}
    {Scap : Dregg2.Circuit.DeployedCapTree.Cap8Scheme}
    {cnCellSeal cnLife cnPermsVK cnBirth cnNotes cnMisc}
    (rds : @ClosureReadouts CH RH cmb compress compressN hCmb hCompress hCompressN hLeaf hRest
      Dregg2.Circuit.Poseidon2Binding.Reference.refLH
      Dregg2.Circuit.FloorsNonVacuous.encodeSponge
      State Scap cnCellSeal cnLife cnPermsVK cnBirth cnNotes cnMisc) : False :=
  closureReadouts_uninstantiable
    (Dregg2.Circuit.Poseidon2Binding.logHashInjective_of_realization
      Dregg2.Circuit.Poseidon2Binding.Reference.refLogRealization)
    rds

/-! ## §4 — `ClosureReadoutsLive`: the realizable restriction (the false member REMOVED).

Identical to `ClosureReadouts` field-for-field, EXCEPT: no `other`. Every live tag is covered by a
named cohort readout (+ the pre-built transfer extract), so the off-range fallback slot — the one
false member — is simply gone. Nothing else changes: same shared carriers, same per-effect
`Satisfied2 ⟹ encode` decode-extraction floors. -/

structure ClosureReadoutsLive
    {CH : CellId → Value → ℤ} {RH : RecordKernelState → ℤ}
    {cmb compress : ℤ → ℤ → ℤ} {compressN : List ℤ → ℤ}
    {hCmb : compressInjective cmb} {hCompress : compressInjective compress}
    {hCompressN : compressNInjective compressN} {hLeaf : cellLeafInjective CH}
    {hRest : RestHashIffFrame RH}
    (LH : List Turn → ℤ) (hash : List ℤ → ℤ) (State : Type)
    (Scap : Dregg2.Circuit.DeployedCapTree.Cap8Scheme)
    (cnCellSeal : List Dregg2.Circuit.RotatedKernelRefinementCellSeal.FieldElem
      → Dregg2.Circuit.RotatedKernelRefinementCellSeal.FieldElem)
    (cnLife : List Dregg2.Circuit.RotatedKernelRefinementLifecycle.FieldElem
      → Dregg2.Circuit.RotatedKernelRefinementLifecycle.FieldElem)
    (cnPermsVK : List Dregg2.Circuit.RotatedKernelRefinementPermsVK.FieldElem
      → Dregg2.Circuit.RotatedKernelRefinementPermsVK.FieldElem)
    (cnBirth : List Dregg2.Circuit.RotatedKernelRefinementBirth.FieldElem
      → Dregg2.Circuit.RotatedKernelRefinementBirth.FieldElem)
    (cnNotes : List Dregg2.Circuit.RotatedKernelRefinementNotes.FieldElem
      → Dregg2.Circuit.RotatedKernelRefinementNotes.FieldElem)
    (cnMisc : List Dregg2.Circuit.RotatedKernelRefinementMisc.FieldElem
      → Dregg2.Circuit.RotatedKernelRefinementMisc.FieldElem) : Type 1 where
  hNCellSeal : compressNInjective cnCellSeal
  hNLife : compressNInjective cnLife
  hNPermsVK : compressNInjective cnPermsVK
  hNBirth : compressNInjective cnBirth
  hNNotes : compressNInjective cnNotes
  -- the transfer slot: pre-built by `ClosureTransfer.closedLogExtract_transfer_closed`.
  transfer : ClosedLogExtract
    (S_live CH RH cmb compress compressN hCmb hCompress hCompressN hLeaf hRest) LH hash Rfix 0
  -- NO `other` field: the dead tags are NOT quantified over — that member was FALSE
  -- (`closureReadouts_uninstantiable`); the live tags below cover everything the apex can reach.
  -- the per-effect NAMED decode-extraction readouts (Satisfied2 ⟹ encode), grouped by family.
  rdMint : ∀ minit mfin maddrs t pubLogPost pre post,
    MintTraceReadout (LH := LH) (hash := hash) minit mfin maddrs t pubLogPost pre post
  rdBurn : ∀ minit mfin maddrs t pubLogPost pre post,
    BurnTraceReadout (LH := LH) (hash := hash) minit mfin maddrs t pubLogPost pre post
  rdBridgeMint : ∀ minit mfin maddrs t pubLogPost pre post,
    BridgeMintTraceReadout (LH := LH) (hash := hash) minit mfin maddrs t pubLogPost pre post
  rdIncNonce : ∀ minit mfin maddrs t pubLogPost pre post,
    IncNonceTraceReadout (LH := LH) (hash := hash) minit mfin maddrs t pubLogPost pre post
  rdSetField : ∀ (slot : Fin 8) minit mfin maddrs t pubLogPost pre post,
    SetFieldTraceReadout (LH := LH) (hash := hash) slot minit mfin maddrs t pubLogPost pre post
  rdHeapWrite : ∀ minit mfin maddrs t pubLogPost pre post,
    HeapWriteTraceReadout (LH := LH) (hash := hash) minit mfin maddrs t pubLogPost pre post
  rdDelegate : ∀ minit mfin maddrs t pubLogPost pre post,
    Satisfied2 hash (Rfix 1) minit mfin maddrs t →
    Dregg2.Circuit.DescriptorIR2.ChipTableSoundN (Dregg2.Circuit.DeployedCapOpen.capPermOut Scap) (t.tf .poseidon2) ×'
    Σ' (del rec tt : CellId), PLift (pubLogPost = LH (authReceipt del :: pre.log)) ×'
      (post.log = authReceipt del :: pre.log →
        Σ' (henc : Dregg2.Circuit.RotatedKernelRefinementCapFamily.DelegateCapsTreeEncodes
              Scap pre post del rec tt),
          Dregg2.Circuit.RotatedKernelRefinementCapFamily.DelegateWriteAnchor
            Scap pre post del rec tt hash minit mfin maddrs t henc)
  rdIntroduce : ∀ minit mfin maddrs t pubLogPost pre post,
    Satisfied2 hash (Rfix 10) minit mfin maddrs t →
    Dregg2.Circuit.DescriptorIR2.ChipTableSoundN (Dregg2.Circuit.DeployedCapOpen.capPermOut Scap) (t.tf .poseidon2) ×'
    Σ' (intro rec tt : CellId), PLift (pubLogPost = LH (authReceipt intro :: pre.log)) ×'
      (post.log = authReceipt intro :: pre.log →
        Σ' (henc : Dregg2.Circuit.RotatedKernelRefinementCapFamily.DelegateCapsTreeEncodes
              Scap pre post intro rec tt),
          Dregg2.Circuit.RotatedKernelRefinementCapFamily.IntroduceWriteAnchor
            Scap pre post intro rec tt hash minit mfin maddrs t henc)
  rdAttenuate : ∀ minit mfin maddrs t pubLogPost pre post,
    Satisfied2 hash (Rfix 12) minit mfin maddrs t →
    Dregg2.Circuit.DescriptorIR2.ChipTableSoundN (Dregg2.Circuit.DeployedCapOpen.capPermOut Scap) (t.tf .poseidon2) ×'
    Σ' (actor : CellId) (idx : Nat) (keep : List Dregg2.Authority.Auth),
      PLift (t.tf (.custom Dregg2.Circuit.Emit.EffectVmEmitV2.SUBMASK_TID)
        = Dregg2.Circuit.Emit.EffectVmEmitV2.subsetTable Dregg2.Circuit.Emit.EffectVmEmitV2.MASK_BITS) ×'
      PLift (pubLogPost = LH (authReceipt actor :: pre.log)) ×'
      (post.log = authReceipt actor :: pre.log →
        Σ' (henc : Dregg2.Circuit.RotatedKernelRefinementCapFamily.AttenuateCapsTreeEncodes
              Scap pre post actor idx keep),
          Dregg2.Circuit.RotatedKernelRefinementCapFamily.AttenuateWriteAnchor
            Scap pre post actor idx keep hash minit mfin maddrs t henc)
  rdDelegateAtten : ∀ minit mfin maddrs t pubLogPost pre post,
    Satisfied2 hash (Rfix 11) minit mfin maddrs t →
    Dregg2.Circuit.DescriptorIR2.ChipTableSoundN (Dregg2.Circuit.DeployedCapOpen.capPermOut Scap) (t.tf .poseidon2) ×'
    Σ' (del rec tt : CellId) (keep : List Dregg2.Authority.Auth),
      PLift (t.tf (.custom Dregg2.Circuit.Emit.EffectVmEmitV2.SUBMASK_TID)
        = Dregg2.Circuit.Emit.EffectVmEmitV2.subsetTable Dregg2.Circuit.Emit.EffectVmEmitV2.MASK_BITS) ×'
      PLift (pubLogPost = LH (authReceipt del :: pre.log)) ×'
      (post.log = authReceipt del :: pre.log →
        Σ' (henc : Dregg2.Circuit.RotatedKernelRefinementCapFamily.DelegateAttenCapsTreeEncodes
              Scap pre post del rec tt keep),
          Dregg2.Circuit.RotatedKernelRefinementCapFamily.DelegateAttenWriteAnchor
            Scap pre post del rec tt keep hash minit mfin maddrs t henc)
  rdRevokeDelegation : ∀ minit mfin maddrs t pubLogPost pre post,
    Satisfied2 hash (Rfix 14) minit mfin maddrs t →
    Dregg2.Circuit.DescriptorIR2.ChipTableSoundN (Dregg2.Circuit.DeployedCapOpen.capPermOut Scap) (t.tf .poseidon2) ×'
    Σ' (holder tt : CellId), PLift (pubLogPost = LH (authReceipt holder :: pre.log)) ×'
      (post.log = authReceipt holder :: pre.log →
        Σ' (henc : Dregg2.Circuit.RotatedKernelRefinementCapFamily.RevokeDelegationFullEncodes
              Scap pre post holder tt),
          Dregg2.Circuit.RotatedKernelRefinementCapFamily.RevokeDelegationWriteAnchor
            Scap pre post holder tt hash minit mfin maddrs t henc.capRemove)
  rdRevoke : ∀ minit mfin maddrs t pubLogPost pre post,
    Satisfied2 hash (Rfix 2) minit mfin maddrs t →
    Dregg2.Circuit.DescriptorIR2.ChipTableSoundN (Dregg2.Circuit.DeployedCapOpen.capPermOut Scap) (t.tf .poseidon2) ×'
    Σ' (holder tt : CellId), PLift (pubLogPost = LH (authReceipt holder :: pre.log)) ×'
      (post.log = authReceipt holder :: pre.log →
        Σ' (henc : Dregg2.Circuit.RotatedKernelRefinementCapFamily.RevokeCapsTreeEncodes
              Scap pre post holder tt),
          Dregg2.Circuit.RotatedKernelRefinementCapFamily.RevokeDelegationWriteAnchor
            Scap pre post holder tt hash minit mfin maddrs t henc)
  rdRefreshDelegation : ∀ minit mfin maddrs t pubLogPost pre post,
    Satisfied2 hash (Rfix 55) minit mfin maddrs t →
    Dregg2.Circuit.DescriptorIR2.ChipTableSoundN (Dregg2.Circuit.DeployedCapOpen.capPermOut Scap) (t.tf .poseidon2) ×'
    Σ' (actor child : CellId),
      PLift (pubLogPost = LH (Dregg2.Circuit.Spec.RefreshDelegation.refreshDelegationReceipt actor child :: pre.log)) ×'
      (post.log = Dregg2.Circuit.Spec.RefreshDelegation.refreshDelegationReceipt actor child :: pre.log →
        Σ' (henc : Dregg2.Circuit.RotatedKernelRefinementCapFamily.RefreshDelegationCapsTreeEncodes
              Scap pre post actor child),
          Dregg2.Circuit.RotatedKernelRefinementCapFamily.RefreshDelegationWriteAnchor
            Scap pre post actor child hash minit mfin maddrs t henc)
  rdCellSeal : ∀ minit mfin maddrs t pubLogPost pre post,
    Satisfied2 hash (Rfix 52) minit mfin maddrs t →
    Σ' (actor cell : CellId) (permOut : List ℤ → List ℤ),
      Dregg2.Circuit.RotatedKernelRefinement.RotTableSide permOut hash t ×'
      PLift (pubLogPost = LH (Dregg2.Circuit.Spec.CellLifecycle.cellLifecycleReceipt actor cell :: pre.log)) ×'
      (post.log = Dregg2.Circuit.Spec.CellLifecycle.cellLifecycleReceipt actor cell :: pre.log →
        Dregg2.Circuit.RotatedKernelRefinementCellSeal.CellSealTraceReadout
          hash minit mfin maddrs t pre post actor cell)
  rdCellUnseal : ∀ minit mfin maddrs t pubLogPost pre post,
    Satisfied2 hash (Rfix 53) minit mfin maddrs t →
    Σ' (actor cell : CellId) (permOut : List ℤ → List ℤ),
      Dregg2.Circuit.RotatedKernelRefinement.RotTableSide permOut hash t ×'
      PLift (pubLogPost = LH (Dregg2.Circuit.Spec.CellLifecycle.cellLifecycleReceipt actor cell :: pre.log)) ×'
      (post.log = Dregg2.Circuit.Spec.CellLifecycle.cellLifecycleReceipt actor cell :: pre.log →
        Dregg2.Circuit.RotatedKernelRefinementLifecycle.CellUnsealTraceReadout hash t pre post actor cell)
  rdCellDestroy : ∀ minit mfin maddrs t pubLogPost pre post,
    Satisfied2 hash (Rfix 54) minit mfin maddrs t →
    Σ' (actor cell : CellId) (certHash : Nat) (permOut : List ℤ → List ℤ),
      Dregg2.Circuit.RotatedKernelRefinement.RotTableSide permOut hash t ×'
      PLift (pubLogPost = LH (Dregg2.Circuit.Spec.CellLifecycle.cellLifecycleReceipt actor cell :: pre.log)) ×'
      (post.log = Dregg2.Circuit.Spec.CellLifecycle.cellLifecycleReceipt actor cell :: pre.log →
        Dregg2.Circuit.RotatedKernelRefinementLifecycle.CellDestroyTraceReadout cnLife hash t pre post actor cell certHash)
  rdRefusal : ∀ minit mfin maddrs t pubLogPost pre post,
    Satisfied2 hash (Rfix 39) minit mfin maddrs t →
    Σ' (actor cell : CellId) (permOut : List ℤ → List ℤ),
      Dregg2.Circuit.RotatedKernelRefinement.RotTableSide permOut hash t ×'
      PLift (pubLogPost = LH ({ actor := actor, src := cell, dst := cell, amt := (0 : ℤ) } :: pre.log)) ×'
      (post.log = { actor := actor, src := cell, dst := cell, amt := (0 : ℤ) } :: pre.log →
        Dregg2.Circuit.RotatedKernelRefinementLifecycle.RefusalTraceReadout cnLife hash t pre post actor cell)
  rdReceiptArchive : ∀ minit mfin maddrs t pubLogPost pre post,
    Satisfied2 hash (Rfix 40) minit mfin maddrs t →
    Σ' (actor cell : CellId) (permOut : List ℤ → List ℤ),
      Dregg2.Circuit.RotatedKernelRefinement.RotTableSide permOut hash t ×'
      PLift (pubLogPost = LH ({ actor := actor, src := cell, dst := cell, amt := (0 : ℤ) } :: pre.log)) ×'
      (post.log = { actor := actor, src := cell, dst := cell, amt := (0 : ℤ) } :: pre.log →
        Dregg2.Circuit.RotatedKernelRefinementLifecycle.ReceiptArchiveTraceReadout
          hash t pre post actor cell)
  rdSetPermissions : ∀ minit mfin maddrs t pubLogPost pre post,
    Satisfied2 hash (Rfix 8) minit mfin maddrs t →
    Σ' (actor cell : CellId) (p : ℤ) (permOut : List ℤ → List ℤ),
      Dregg2.Circuit.RotatedKernelRefinement.RotTableSide permOut hash t ×'
      PLift (pubLogPost = LH ({ actor := actor, src := cell, dst := cell, amt := (0 : ℤ) } :: pre.log)) ×'
      (post.log = { actor := actor, src := cell, dst := cell, amt := (0 : ℤ) } :: pre.log →
        Dregg2.Circuit.RotatedKernelRefinementPermsVK.SetPermsTraceReadout hash minit mfin maddrs t pre post actor cell p)
  rdSetVK : ∀ minit mfin maddrs t pubLogPost pre post,
    Satisfied2 hash (Rfix 9) minit mfin maddrs t →
    Σ' (actor cell : CellId) (vk : ℤ) (permOut : List ℤ → List ℤ),
      Dregg2.Circuit.RotatedKernelRefinement.RotTableSide permOut hash t ×'
      PLift (pubLogPost = LH ({ actor := actor, src := cell, dst := cell, amt := (0 : ℤ) } :: pre.log)) ×'
      (post.log = { actor := actor, src := cell, dst := cell, amt := (0 : ℤ) } :: pre.log →
        Dregg2.Circuit.RotatedKernelRefinementPermsVK.SetVKTraceReadout hash minit mfin maddrs t pre post actor cell vk)
  rdSetProgram : ∀ minit mfin maddrs t pubLogPost pre post,
    Satisfied2 hash (Rfix 13) minit mfin maddrs t →
    Σ' (actor cell : CellId) (prog : ℤ) (permOut : List ℤ → List ℤ),
      Dregg2.Circuit.RotatedKernelRefinement.RotTableSide permOut hash t ×'
      PLift (pubLogPost = LH ({ actor := actor, src := cell, dst := cell, amt := (0 : ℤ) } :: pre.log)) ×'
      (post.log = { actor := actor, src := cell, dst := cell, amt := (0 : ℤ) } :: pre.log →
        Dregg2.Circuit.RotatedKernelRefinementProgram.SetProgramTraceReadout compressN hash t pre post actor cell prog)
  rdMakeSovereign : ∀ minit mfin maddrs t pubLogPost pre post,
    Satisfied2 hash (Rfix 38) minit mfin maddrs t →
    Σ' (actor cell : CellId) (permOut : List ℤ → List ℤ),
      Dregg2.Circuit.RotatedKernelRefinement.RotTableSide permOut hash t ×'
      PLift (pubLogPost = LH ({ actor := actor, src := cell, dst := cell, amt := (0 : ℤ) } :: pre.log)) ×'
      (post.log = { actor := actor, src := cell, dst := cell, amt := (0 : ℤ) } :: pre.log →
        Dregg2.Circuit.RotatedKernelRefinementMisc.MakeSovereignTraceReadout hash minit mfin maddrs t pre post actor cell)
  rdCreateCell : ∀ minit mfin maddrs t pubLogPost pre post,
    Satisfied2 hash (Rfix 17) minit mfin maddrs t →
    Σ' (actor newCell : CellId),
      PLift (pubLogPost = LH (Dregg2.Circuit.Spec.AccountGrowth.createReceipt actor newCell :: pre.log)) ×'
      (post.log = Dregg2.Circuit.Spec.AccountGrowth.createReceipt actor newCell :: pre.log →
        Dregg2.Circuit.RotatedKernelRefinementBirth.CreateCellTraceReadout hash minit mfin maddrs t pre post actor newCell)
  rdCreateCellFromFactory : ∀ minit mfin maddrs t pubLogPost pre post,
    Satisfied2 hash (Rfix 18) minit mfin maddrs t →
    Σ' (actor newCell : CellId) (vk : ℤ),
      PLift (pubLogPost = LH (Dregg2.Circuit.Spec.FactoryCreation.factoryReceipt actor newCell :: pre.log)) ×'
      (post.log = Dregg2.Circuit.Spec.FactoryCreation.factoryReceipt actor newCell :: pre.log →
        Dregg2.Circuit.RotatedKernelRefinementBirth.CreateFromFactoryTraceReadout hash minit mfin maddrs t pre post actor newCell vk)
  rdSpawn : ∀ minit mfin maddrs t pubLogPost pre post,
    Satisfied2 hash (Rfix 19) minit mfin maddrs t →
    Dregg2.Circuit.DescriptorIR2.ChipTableSoundN (Dregg2.Circuit.DeployedCapOpen.capPermOut Scap) (t.tf .poseidon2) ×'
    Σ' (actor child target : CellId),
      PLift (pubLogPost = LH (Dregg2.Circuit.Spec.AccountGrowth.createReceipt actor child :: pre.log)) ×'
      (post.log = Dregg2.Circuit.Spec.AccountGrowth.createReceipt actor child :: pre.log →
        Σ' (rd : Dregg2.Circuit.RotatedKernelRefinementBirth.SpawnTraceReadout
              Scap hash minit mfin maddrs t pre post actor child target),
          Dregg2.Circuit.RotatedKernelRefinementBirth.SpawnWriteAnchor
            Scap hash minit mfin maddrs t pre post actor child target rd)
  rdNoteSpend : ∀ minit mfin maddrs t pubLogPost pre post,
    Satisfied2 hash (Rfix 27) minit mfin maddrs t →
    Σ' (nf : Nat) (actor : CellId) (spendProof : Bool),
      PLift (pubLogPost = LH (Dregg2.Circuit.Spec.NoteNullifier.noteSpendReceipt actor :: pre.log)) ×'
      (post.log = Dregg2.Circuit.Spec.NoteNullifier.noteSpendReceipt actor :: pre.log →
        Dregg2.Circuit.RotatedKernelRefinementNotes.NoteSpendTraceReadout hash minit mfin maddrs t pre post nf actor spendProof)
  rdNoteCreate : ∀ minit mfin maddrs t pubLogPost pre post,
    Satisfied2 hash (Rfix 28) minit mfin maddrs t →
    Σ' (cm : Nat) (actor : CellId),
      PLift (pubLogPost = LH (Dregg2.Circuit.Spec.NoteCommitment.noteCreateReceipt actor :: pre.log)) ×'
      (post.log = Dregg2.Circuit.Spec.NoteCommitment.noteCreateReceipt actor :: pre.log →
        Dregg2.Circuit.RotatedKernelRefinementNotes.NoteCreateTraceReadout hash minit mfin maddrs t pre post cm actor)
  rdEmitEvent : ∀ minit mfin maddrs t pubLogPost pre post,
    Satisfied2 hash (Rfix 6) minit mfin maddrs t →
    Σ' (actor cell : CellId) (_topic _data : ℤ),
      PLift (pubLogPost = LH (Dregg2.Circuit.Spec.CellStateLog.emitReceipt actor cell :: pre.log)) ×'
      (post.log = Dregg2.Circuit.Spec.CellStateLog.emitReceipt actor cell :: pre.log →
        Dregg2.Circuit.RotatedKernelRefinementPermsVK.emitEventEncodes pre post actor cell)
  rdPipelinedSend : ∀ minit mfin maddrs t pubLogPost pre post,
    Satisfied2 hash (Rfix 47) minit mfin maddrs t →
    Σ' (actor : CellId),
      PLift (pubLogPost = LH (Dregg2.Circuit.Spec.QueuePipelinedSend.pipelinedSendReceipt actor :: pre.log)) ×'
      (post.log = Dregg2.Circuit.Spec.QueuePipelinedSend.pipelinedSendReceipt actor :: pre.log →
        Dregg2.Circuit.RotatedKernelRefinementMisc.pipelinedSendEncodes pre post actor)
  rdExercise : ∀ minit mfin maddrs t pre post,
    Satisfied2 hash (Rfix 16) minit mfin maddrs t →
    Σ' (actor target : CellId) (inner : List Dregg2.Exec.TurnExecutorFull.FullActionA),
      Dregg2.Circuit.RotatedKernelRefinementExerciseAuth.exerciseEncodesAuthV3
        pre post actor target inner

/-- `ClosureReadoutsLive` is a RESTRICTION of `ClosureReadouts`: dropping the (false) `other` member is
the only change. (The converse map cannot exist under the realizable floors —
`closureReadouts_uninstantiable`.) -/
def ClosureReadoutsLive.of
    {CH : CellId → Value → ℤ} {RH : RecordKernelState → ℤ}
    {cmb compress : ℤ → ℤ → ℤ} {compressN : List ℤ → ℤ}
    {hCmb : compressInjective cmb} {hCompress : compressInjective compress}
    {hCompressN : compressNInjective compressN} {hLeaf : cellLeafInjective CH}
    {hRest : RestHashIffFrame RH}
    {LH : List Turn → ℤ} {hash : List ℤ → ℤ} {State : Type}
    {Scap : Dregg2.Circuit.DeployedCapTree.Cap8Scheme}
    {cnCellSeal cnLife cnPermsVK cnBirth cnNotes cnMisc}
    (rds : @ClosureReadouts CH RH cmb compress compressN hCmb hCompress hCompressN hLeaf hRest
      LH hash State Scap cnCellSeal cnLife cnPermsVK cnBirth cnNotes cnMisc) :
    @ClosureReadoutsLive CH RH cmb compress compressN hCmb hCompress hCompressN hLeaf hRest
      LH hash State Scap cnCellSeal cnLife cnPermsVK cnBirth cnNotes cnMisc where
  hNCellSeal := rds.hNCellSeal
  hNLife := rds.hNLife
  hNPermsVK := rds.hNPermsVK
  hNBirth := rds.hNBirth
  hNNotes := rds.hNNotes
  transfer := rds.transfer
  rdMint := rds.rdMint
  rdBurn := rds.rdBurn
  rdBridgeMint := rds.rdBridgeMint
  rdIncNonce := rds.rdIncNonce
  rdSetField := rds.rdSetField
  rdHeapWrite := rds.rdHeapWrite
  rdDelegate := rds.rdDelegate
  rdIntroduce := rds.rdIntroduce
  rdAttenuate := rds.rdAttenuate
  rdDelegateAtten := rds.rdDelegateAtten
  rdRevokeDelegation := rds.rdRevokeDelegation
  rdRevoke := rds.rdRevoke
  rdRefreshDelegation := rds.rdRefreshDelegation
  rdCellSeal := rds.rdCellSeal
  rdCellUnseal := rds.rdCellUnseal
  rdCellDestroy := rds.rdCellDestroy
  rdRefusal := rds.rdRefusal
  rdReceiptArchive := rds.rdReceiptArchive
  rdSetPermissions := rds.rdSetPermissions
  rdSetVK := rds.rdSetVK
  rdSetProgram := rds.rdSetProgram
  rdMakeSovereign := rds.rdMakeSovereign
  rdCreateCell := rds.rdCreateCell
  rdCreateCellFromFactory := rds.rdCreateCellFromFactory
  rdSpawn := rds.rdSpawn
  rdNoteSpend := rds.rdNoteSpend
  rdNoteCreate := rds.rdNoteCreate
  rdEmitEvent := rds.rdEmitEvent
  rdPipelinedSend := rds.rdPipelinedSend
  rdExercise := rds.rdExercise

/-! ## §5 — the assembled fanout STILL GOES THROUGH on live tags only.

The 31-way split is now by `cases` on the witnessing `FullActionA` (the liveness witness), not by a
numeric match with an `other` fallback — so no dead tag is ever consulted, and each slot CALLS the
same proven genuine discharger as before. -/

theorem closedLogExtract_all_genuine_live
    {CH : CellId → Value → ℤ} {RH : RecordKernelState → ℤ}
    {cmb compress : ℤ → ℤ → ℤ} {compressN : List ℤ → ℤ}
    {hCmb : compressInjective cmb} {hCompress : compressInjective compress}
    {hCompressN : compressNInjective compressN} {hLeaf : cellLeafInjective CH}
    {hRest : RestHashIffFrame RH}
    {LH : List Turn → ℤ} {hash : List ℤ → ℤ} {State : Type}
    {Scap : Dregg2.Circuit.DeployedCapTree.Cap8Scheme}
    {cnCellSeal cnLife cnPermsVK cnBirth cnNotes cnMisc}
    (rds : @ClosureReadoutsLive CH RH cmb compress compressN hCmb hCompress hCompressN hLeaf hRest
      LH hash State Scap cnCellSeal cnLife cnPermsVK cnBirth cnNotes cnMisc) :
    ∀ e, LiveTag e → ClosedLogExtract
      (S_live CH RH cmb compress compressN hCmb hCompress hCompressN hLeaf hRest) LH hash Rfix e := by
  rintro e ⟨fa, rfl⟩
  cases fa with
  | balanceA _ _ => exact rds.transfer
  | delegate _ _ _ => exact closedLogExtract_delegate_closed Scap rds.rdDelegate
  | revoke _ _ => exact closedLogExtract_revoke_closed Scap rds.rdRevoke
  | mintA _ _ _ _ => exact closedLogExtract_mint_closed rds.rdMint
  | burnA _ _ _ _ => exact closedLogExtract_burn_closed rds.rdBurn
  | setFieldA _ _ _ _ => exact closedLogExtract_setField_closed 0 (rds.rdSetField 0)
  | emitEventA _ _ _ _ => exact closedLogExtract_emitEvent_closed rds.rdEmitEvent
  | incrementNonceA _ _ _ => exact closedLogExtract_incrementNonce_closed rds.rdIncNonce
  | setPermissionsA _ _ _ => exact closedLogExtract_setPermissions_closed rds.rdSetPermissions
  | setVKA _ _ _ => exact closedLogExtract_setVK_closed rds.rdSetVK
  | setProgramA _ _ _ => exact closedLogExtract_setProgram_closed compressN hCompressN rds.rdSetProgram
  | introduceA _ _ _ => exact closedLogExtract_introduce_closed Scap rds.rdIntroduce
  | delegateAttenA _ _ _ _ => exact closedLogExtract_delegateAtten_closed Scap rds.rdDelegateAtten
  | attenuateA _ _ _ => exact closedLogExtract_attenuate_closed Scap rds.rdAttenuate
  | revokeDelegationA _ _ => exact closedLogExtract_revokeDelegation_closed Scap rds.rdRevokeDelegation
  | exerciseA _ _ _ => exact closedLogExtract_exercise_closed rds.rdExercise
  | createCellA _ _ => exact closedLogExtract_createCell_closed rds.rdCreateCell
  | createCellFromFactoryA _ _ _ =>
      exact closedLogExtract_createCellFromFactory_closed rds.rdCreateCellFromFactory
  | spawnA _ _ _ => exact closedLogExtract_spawn_closed Scap rds.rdSpawn
  | bridgeMintA _ _ _ _ => exact closedLogExtract_bridgeMint_closed rds.rdBridgeMint
  | noteSpendA _ _ _ => exact closedLogExtract_noteSpend_closed rds.rdNoteSpend
  | noteCreateA _ _ => exact closedLogExtract_noteCreate_closed rds.rdNoteCreate
  | makeSovereignA _ _ => exact closedLogExtract_makeSovereign_closed rds.rdMakeSovereign
  | refusalA _ _ => exact closedLogExtract_refusal_closed cnLife rds.hNLife rds.rdRefusal
  | receiptArchiveA _ _ => exact closedLogExtract_receiptArchive_closed rds.rdReceiptArchive
  | pipelinedSendA _ => exact closedLogExtract_pipelinedSend_closed rds.rdPipelinedSend
  | cellSealA _ _ => exact closedLogExtract_cellSeal_closed rds.rdCellSeal
  | cellUnsealA _ _ => exact closedLogExtract_cellUnseal_closed rds.rdCellUnseal
  | cellDestroyA _ _ _ => exact closedLogExtract_cellDestroy_closed cnLife rds.hNLife rds.rdCellDestroy
  | refreshDelegationA _ _ =>
      exact closedLogExtract_refreshDelegation_closed Scap rds.rdRefreshDelegation
  | heapWriteA _ _ _ _ _ => exact closedLogExtract_heapWrite_closed rds.rdHeapWrite

/-! ## §6 — the closed apex on the LIVE floor.

`lightclient_unfoolable` consumes its per-effect family ONLY at `pi.effect`; we restate it needing the
extract only at live tags, with the light client's tag-liveness check explicit (`hlive`). This costs
nothing: a `pi` at a dead tag could never satisfy the conclusion (`liveTag_of_kstepAll`), so the old
total-`∀ e` hypothesis was doing IMPOSSIBLE work at exactly the slots where it was false. -/

/-- The apex at a single (live) effect: the mirrored `lightclient_unfoolable`, consuming the
per-effect extract only at `pi.effect` and the log-enrichment `mkLog`. -/
theorem lightclient_unfoolable_live
    (hash : List ℤ → ℤ) (S : CommitSurface) (LH : List Turn → ℤ)
    [StarkSound hash Rfix]
    (hext : ∀ e, LiveTag e → ClosedLogExtract S LH hash Rfix e)
    (mkLog : ∀ (_e : EffectIdx) (pc : PublishedCommit) (pre post : RecChainedState),
      StateDecode S pc pre post →
      ∃ pubLogPre pubLogPost, StateDecodeLog S LH pc pubLogPre pubLogPost pre post)
    (pi : BatchPublicInputs) (π : BatchProof)
    (hlive : LiveTag pi.effect)
    (hwitdec : WitnessDecodes hash Rfix S pi)
    (hacc : verifyBatch (vkOfRegistry Rfix) pi π = Verdict.accept) :
    ∃ pre post : RecChainedState,
      StateDecode S pi.toPublished pre post ∧
      kstepAll pi.effect pre post ∧
      pi.pre = S.commit pre.kernel pi.turn ∧
      pi.post = S.commit post.kernel pi.turn := by
  obtain ⟨minit, mfin, maddrs, t, hsat, hpub⟩ :=
    (inferInstance : StarkSound hash Rfix).extract pi π hacc
  obtain ⟨pre, post, hdecode⟩ := hwitdec minit mfin maddrs t hsat hpub
  obtain ⟨pubLogPre, pubLogPost, hdecLog⟩ := mkLog pi.effect pi.toPublished pre post hdecode
  have hstep : kstepAll pi.effect pre post :=
    hext pi.effect hlive minit mfin maddrs t pi.toPublished pubLogPre pubLogPost pre post
      hsat hdecLog
  refine ⟨pre, post, hdecode, hstep, ?_, ?_⟩
  · simpa using hdecode.preBinds
  · simpa using hdecode.postBinds

/-- **The final closed apex on the LIVE readout bundle** — the analogue of
`lightclient_unfoolable_closed_final_genuine`, from `ClosureReadoutsLive` (no false member) instead of
`ClosureReadouts` (uninstantiable). Every cohort slot is discharged by CALLING its proven
`<e>_closedLog` rung, exactly as before; the only new hypothesis is the light client's explicit
tag-liveness check `hlive` — which the OLD conclusion forced anyway (`liveTag_of_kstepAll`). -/
theorem lightclient_unfoolable_closed_final_live
    {CH : CellId → Value → ℤ} {RH : RecordKernelState → ℤ}
    {cmb compress : ℤ → ℤ → ℤ} {compressN : List ℤ → ℤ}
    {hCmb : compressInjective cmb} {hCompress : compressInjective compress}
    {hCompressN : compressNInjective compressN} {hLeaf : cellLeafInjective CH}
    {hRest : RestHashIffFrame RH}
    (hash : List ℤ → ℤ) (LH : List Turn → ℤ) {State : Type}
    {Scap : Dregg2.Circuit.DeployedCapTree.Cap8Scheme}
    {cnCellSeal cnLife cnPermsVK cnBirth cnNotes cnMisc}
    [StarkSound hash Rfix]
    (rds : @ClosureReadoutsLive CH RH cmb compress compressN hCmb hCompress hCompressN hLeaf hRest
      LH hash State Scap cnCellSeal cnLife cnPermsVK cnBirth cnNotes cnMisc)
    (mkLog : ∀ (_e : EffectIdx) (pc : PublishedCommit) (pre post : RecChainedState),
      StateDecode (S_live CH RH cmb compress compressN hCmb hCompress hCompressN hLeaf hRest)
        pc pre post →
      ∃ pubLogPre pubLogPost, StateDecodeLog
        (S_live CH RH cmb compress compressN hCmb hCompress hCompressN hLeaf hRest)
        LH pc pubLogPre pubLogPost pre post)
    (pi : BatchPublicInputs) (π : BatchProof)
    (hlive : LiveTag pi.effect)
    (hwitdec : WitnessDecodes hash Rfix
      (S_live CH RH cmb compress compressN hCmb hCompress hCompressN hLeaf hRest) pi)
    (hacc : verifyBatch (vkOfRegistry Rfix) pi π = Verdict.accept) :
    ∃ pre post : RecChainedState,
      StateDecode (S_live CH RH cmb compress compressN hCmb hCompress hCompressN hLeaf hRest)
        pi.toPublished pre post ∧
      kstepAll pi.effect pre post ∧
      pi.pre = (S_live CH RH cmb compress compressN hCmb hCompress hCompressN hLeaf hRest).commit
        pre.kernel pi.turn ∧
      pi.post = (S_live CH RH cmb compress compressN hCmb hCompress hCompressN hLeaf hRest).commit
        post.kernel pi.turn :=
  lightclient_unfoolable_live hash
    (S_live CH RH cmb compress compressN hCmb hCompress hCompressN hLeaf hRest) LH
    (closedLogExtract_all_genuine_live rds) mkLog pi π hlive hwitdec hacc

/-! ## §7 — the gap is closed, teeth on both sides.

The dead slot at 15 is refuted through the EMPTINESS of its conclusion relation; a live slot's
conclusion relation is INHABITED, so no member of the live bundle is refutable by that route. -/

/-- FIRE (the live side): the conclusion relation at the LIVE tag 47 (pipelinedSend) is INHABITED — a
genuine `kstepAll 47` step exists (the receipt-prepend on the empty-cell state). Contrast
`kstepAll_not_total` at the dead tag 15: the emptiness that makes `other 15` false has no analogue at
the tags `ClosureReadoutsLive` quantifies over. -/
theorem kstepAll_live_inhabited_47 :
    ∃ pre post : RecChainedState, kstepAll 47 pre post := by
  refine ⟨Dregg2.Circuit.WitnessRealizing.emptyState,
    { kernel := Dregg2.Circuit.WitnessRealizing.emptyKernel
    , log := [Dregg2.Circuit.Spec.QueuePipelinedSend.pipelinedSendReceipt 0] },
    .pipelinedSendA 0, rfl, ?_⟩
  simp only [Dregg2.Circuit.ActionDispatch.fullActionStep,
    Dregg2.Circuit.Spec.QueuePipelinedSend.PipelinedSendSpec]
  and_intros <;> rfl

/-! ## §8 — axiom hygiene. -/

#assert_axioms liveTag_of_kstepAll
#assert_axioms not_liveTag_15
#assert_axioms liveTag_transfer
#assert_axioms liveTag_pipelinedSend
#assert_axioms Rfix_emptyTag_transfer
#assert_axioms satisfied2_emptyTag_15
#assert_axioms closedLogExtract_emptyTag_false
#assert_axioms stateDecodeLog_inhabited
#assert_axioms closureReadouts_uninstantiable
#assert_axioms closureReadouts_uninstantiable_concrete
#assert_axioms ClosureReadoutsLive.of
#assert_axioms closedLogExtract_all_genuine_live
#assert_axioms lightclient_unfoolable_live
#assert_axioms lightclient_unfoolable_closed_final_live
#assert_axioms kstepAll_live_inhabited_47

end Dregg2.Circuit.ClosureReadoutsRealizable
