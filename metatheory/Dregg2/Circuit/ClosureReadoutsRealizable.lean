/-
# Dregg2.Circuit.ClosureReadoutsRealizable — survey finding #3: the uninstantiable refinement floor,
machine-checked TWICE — through the dead-tag member, and (2026-08-03) through the LIVE one that the
"realizable restriction" kept. The restriction is deleted; the module now carries its own refutation.

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
    loses NOTHING — which is what made the restriction below look like a repair.

⚑⚑ **AND THE RESTRICTION WAS NOT ONE. `ClosureReadoutsLive` IS DELETED (2026-08-03).** It was
`ClosureReadouts` with `other` removed, and §4 now proves it could never have had an inhabitant
either — through `transfer`, a field BOTH bundles carry, refuted with no crypto floor assumed at all.
The tell was already in the code: `ClosureReadoutsLive.of`, its only entry point, took a
`ClosureReadouts` as its SOURCE, so it supplied no inhabitant and nothing else ever built one.
Deleted with it: `.of`, `closedLogExtract_all_genuine_live`, `lightclient_unfoolable_live`,
`lightclient_unfoolable_closed_final_live` — nothing outside this file referred to any of them.

  * **§4, the finding** — `ClosureAll.ClosedLogExtract` quantifies the CIRCUIT WITNESS and the STATE
    DECODE INDEPENDENTLY (no publication link), the EMPTY trace satisfies EVERY descriptor, and
    `StateDecode` is LOG-BLIND. So `ClosedLogExtract S LH hash R 0` forces the transfer step between
    endpoints whose logs it never saw, and is FALSE wherever a decode exists:
    `not_closedLogExtract_transfer_refLH`, `not_nonempty_closureReadouts_refLH` — both CLOSED, no
    hypotheses. It is not a tag-range problem, so no tag-range restriction can fix it.
  * **§4 also replaces `ClosureAll.closedLogExtract_no_strength_lost`** (deleted the same day):
    `closedLogExtract_port_detectably_stronger` exhibits ONE sponge at which the pre-port shape holds
    vacuously and the ported shape is FALSE — a strength difference the old tooth could not detect.

NEW file; imports read-only. `#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound} throughout.
-/
import Dregg2.Circuit.ClosureFanoutGenuine
import Dregg2.Circuit.ApexFloorFree
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
variable {hRest : Dregg2.Circuit.RestFrameFin.RestHashIffFrameFin RH}

local notation "Slive" => S_live CH RH cmb compress compressN hRest

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
    {hRest : Dregg2.Circuit.RestFrameFin.RestHashIffFrameFin RH}
    {LH : List Turn → ℤ} {hash : List ℤ → ℤ} {State : Type}
    {Scap : Dregg2.Circuit.DeployedCapTree.Cap8Scheme}
    {cnCellSeal cnLife cnPermsVK cnBirth cnNotes cnMisc}
    (hLog : logHashInjective LH)
    (rds : @ClosureReadouts CH RH cmb compress compressN hRest
      LH hash State Scap cnCellSeal cnLife cnPermsVK cnBirth cnNotes cnMisc) : False := by
  obtain ⟨pc, pubLogPre, pubLogPost, pre, post, hdec⟩ :=
    stateDecodeLog_inhabited
      (S_live CH RH cmb compress compressN hRest) LH hLog
      ⟨0, 0, 0, 0⟩
  exact closedLogExtract_emptyTag_false hdec (rds.other 15)

/-- **FIRE.** At the CONCRETE injective floors — `encodeSponge` (proved CR) and `refLH` (proved
injective) — the uninstantiability holds with NO crypto hypotheses left: for every surface, there is
no bundle. The hypotheses of the finding are genuinely satisfiable; the refutation is unconditional at
a realizable point. -/
theorem closureReadouts_uninstantiable_concrete
    {CH : CellId → Value → ℤ} {RH : RecordKernelState → ℤ}
    {cmb compress : ℤ → ℤ → ℤ} {compressN : List ℤ → ℤ}
    {hRest : Dregg2.Circuit.RestFrameFin.RestHashIffFrameFin RH} {State : Type}
    {Scap : Dregg2.Circuit.DeployedCapTree.Cap8Scheme}
    {cnCellSeal cnLife cnPermsVK cnBirth cnNotes cnMisc}
    (rds : @ClosureReadouts CH RH cmb compress compressN hRest
      Dregg2.Circuit.Poseidon2Binding.Reference.refLH
      Dregg2.Circuit.FloorsNonVacuous.encodeSponge
      State Scap cnCellSeal cnLife cnPermsVK cnBirth cnNotes cnMisc) : False :=
  closureReadouts_uninstantiable
    (Dregg2.Circuit.Poseidon2Binding.logHashInjective_of_realization
      Dregg2.Circuit.Poseidon2Binding.Reference.refLogRealization)
    rds

/-! ## §4 — ⚑ THE SUCCESSOR WAS UNINHABITED TOO, FOR A REASON THE LIVE RESTRICTION CANNOT REACH.

§3 refutes `ClosureReadouts` through its `other 15` member, and this module's answer was
`ClosureReadoutsLive` — the same bundle with that one member deleted. **It de-vacuumed nothing**, and
the shape of the code already said so: the only entry point `ClosureReadoutsLive.of` took a
`ClosureReadouts` as its SOURCE, so it could never supply an inhabitant, and nothing else ever built
one. `ClosureReadoutsLive`, `.of`, `closedLogExtract_all_genuine_live`, `lightclient_unfoolable_live`
and `lightclient_unfoolable_closed_final_live` are DELETED (2026-08-03); this section is what replaces
them.

The falsity is not about the dead tag at all. Read `ClosureAll.ClosedLogExtract`'s telescope:

    ∀ minit mfin maddrs t   pc pubLogPre pubLogPost pre post,
      Satisfied2 hash (R e) minit mfin maddrs t →
      StateDecodeLog S LH pc pubLogPre pubLogPost pre post →
      kstepAll e pre post

The CIRCUIT WITNESS (`minit`/`mfin`/`maddrs`/`t`) and the STATE DECODE (`pc`, the two published log
commitments, `pre`, `post`) are quantified INDEPENDENTLY. Nothing says `t` is a trace OF that
boundary — the publication link `tracePublishedCommit t = pc` that `ApexFloorFree.descriptorRefinesFree`
restored is exactly what this def still drops. So ONE satisfying trace forces `kstepAll e` between
EVERY decodable pair, and all three ingredients are already in the tree:

  * the EMPTY trace satisfies EVERY descriptor at EVERY hash (`ApexFloorFree.satisfied2_emptyTrace`:
    the three per-row legs are `∀ i < 0` and `memLog`/`mapLog` are `rows.flatMap`), the deployed
    `Rfix 0` included — no peel, no honest-prover data;
  * `StateDecode` is LOG-BLIND: it reads `pre.kernel`, `post.kernel` and their `AccountsWF`, and
    NOTHING else. So any decode of `(pre, post)` is also a decode of `(pre, ⟨post.kernel, pre.log⟩)`,
    and the two published log commitments are free variables we may set to `LH pre.log`. (This is the
    collapse `Market.ProtocolAssurance.shieldedRingDescriptorRefinesFree_forces_no_decode` runs on the
    shielded rung; the same hole, one def over.)
  * the transfer step ADVANCES the log (`BalanceMovementSpec`'s `st'.log = t :: st.log`), so
    `kstepAll 0 pre ⟨post.kernel, pre.log⟩` unfolds to `pre.log = t :: pre.log`.

Hence `ClosedLogExtract S LH hash R 0` is FALSE at every surface, log hash, hash and registry for which
a decode exists at all — and `stateDecodeLog_inhabited` (§2) supplies a decode at EVERY surface from
`logHashInjective LH` alone, which `refLH` discharges outright. `transfer` is a field of BOTH bundles,
so the live restriction was never going to help: the false field it kept is not tag-ranged.

⚠ **WHAT THIS IS NOT.** It is not a claim that the deployed circuit is unsound, and it is not a claim
about any `<e>TraceReadout`. It is a claim that `ClosedLogExtract` AS WRITTEN asserts something no
prover-witness extraction could establish, so every theorem carrying it is vacuous — including this
module's own former apex.

⚠ **AND THE OBVIOUS REPAIR IS NOT SUFFICIENT, WHICH THE TREE HAS ALREADY MEASURED.** Adding
`descriptorRefinesFree`'s link `tracePublishedCommit t = pc` closes the KERNEL half and NOT the log
half: `Market.ProtocolAssurance.shieldedRingDescriptorRefinesFree_forces_no_decode` refutes the LINKED
rung too, at a log-reading conclusion, because `StateDecodeC` is log-blind and the collapse survives
the link. The `ClosedLogExtract` shape has the same gap one level down — `pubLogPre`/`pubLogPost` are
FREE `∀`-variables here, so even a `pc`-link leaves the two published log commitments unconstrained by
the trace, which is the degree of freedom §4's proof actually spends. So the repair is: bind the
published log commitments to the TRACE the way `pc` is bound (not merely to `pre.log`/`post.log`,
which `StateDecodeLog` already does), or take `ProtocolAssurance`'s route — weaken the conclusion to
its kernel-endpoint half and NAME the log advance as a per-instance residual. Either is a design
choice with a cost; neither is this commit, and neither is a tag restriction. -/

/-- **THE ENGINE.** `ClosedLogExtract … 0` and a decodable boundary cannot both exist — at every
surface, log hash, hash and registry. Feed the extract the EMPTY trace (which satisfies `R 0`
whatever `R 0` is) against the LOG-COLLAPSED reading of the given decode; the transfer step's own
`log` clause then says `pre.log = t :: pre.log`. -/
theorem closedLogExtract_transfer_excludes_every_decode
    (S : CommitSurface) (LH : List Turn → ℤ) (hash : List ℤ → ℤ) (R : Registry) :
    ¬ (ClosedLogExtract S LH hash R 0
        ∧ ∃ (pc : PublishedCommit) (pubLogPre pubLogPost : ℤ) (pre post : RecChainedState),
            StateDecodeLog S LH pc pubLogPre pubLogPost pre post) := by
  rintro ⟨hext, pc, _pubLogPre, _pubLogPost, pre, post, hdec⟩
  have hstep : kstepAll 0 pre ⟨post.kernel, pre.log⟩ :=
    hext (fun _ => 0) (fun _ => (0, 0)) [] Dregg2.Circuit.ApexFloorFree.emptyTrace
      pc (LH pre.log) (LH pre.log) pre ⟨post.kernel, pre.log⟩
      (Dregg2.Circuit.ApexFloorFree.satisfied2_emptyTrace hash (R 0) _ _)
      { toDecode :=
          { preBinds := hdec.toDecode.preBinds
          , postBinds := hdec.toDecode.postBinds
          , preWF := hdec.toDecode.preWF
          , postWF := hdec.toDecode.postWF }
      , hLogInj := hdec.hLogInj
      , logPreBinds := rfl
      , logPostBinds := rfl }
  obtain ⟨fa, htag, hfa⟩ := hstep
  cases fa
  case balanceA t a =>
    have hspec : Dregg2.Circuit.Spec.BalanceMovement.BalanceMovementSpec pre t a
        ⟨post.kernel, pre.log⟩ := hfa
    have hlen := congrArg List.length hspec.2.2.1
    simp only [List.length_cons] at hlen
    omega
  all_goals simp [Dregg2.Circuit.ActionDispatch.actionTag] at htag

/-- **CLOSED — no hypotheses.** At the reference log hash `refLH` (proved injective, so §2's decode
fires) the transfer slot of `ClosedLogExtract` is FALSE, at every surface, hash and registry. This is
the field `ClosureReadouts.transfer` and `ClosureReadoutsLive.transfer` both carried. -/
theorem not_closedLogExtract_transfer_refLH
    (S : CommitSurface) (hash : List ℤ → ℤ) (R : Registry) :
    ¬ ClosedLogExtract S Dregg2.Circuit.Poseidon2Binding.Reference.refLH hash R 0 := fun hext =>
  closedLogExtract_transfer_excludes_every_decode S _ hash R
    ⟨hext, stateDecodeLog_inhabited S _
      (Dregg2.Circuit.Poseidon2Binding.logHashInjective_of_realization
        Dregg2.Circuit.Poseidon2Binding.Reference.refLogRealization) ⟨0, 0, 0, 0⟩⟩

/-- **THE ANSWER TO §4's QUESTION, on the bundle that SURVIVES.** `ClosureReadouts` is uninhabited at
the reference log hash with NO crypto hypothesis assumed anywhere — through `transfer`, not through
`other`. `ClosureReadoutsLive` differed from it in exactly one field and that field was not this one,
so the deleted successor was uninhabited by this same proof. Compare
`closureReadouts_uninstantiable_concrete` (§3): same verdict, different member, and THAT one is the
member the successor removed. -/
theorem not_nonempty_closureReadouts_refLH
    {CH : CellId → Value → ℤ} {RH : RecordKernelState → ℤ}
    {cmb compress : ℤ → ℤ → ℤ} {compressN : List ℤ → ℤ}
    {hRest : Dregg2.Circuit.RestFrameFin.RestHashIffFrameFin RH}
    (hash : List ℤ → ℤ) (State : Type)
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
      → Dregg2.Circuit.RotatedKernelRefinementMisc.FieldElem) :
    ¬ Nonempty (@ClosureReadouts CH RH cmb compress compressN hRest
      Dregg2.Circuit.Poseidon2Binding.Reference.refLH hash State Scap
      cnCellSeal cnLife cnPermsVK cnBirth cnNotes cnMisc) := by
  rintro ⟨rds⟩
  exact not_closedLogExtract_transfer_refLH _ hash Rfix rds.transfer

/-- **THE `no_strength_lost` REPLACEMENT** (that tooth is DELETED from `ClosureAll`, 2026-08-03: its
conclusion was `Poseidon2SpongeCR hash → (the old body)`, which holds for free wherever the antecedent
fails — i.e. at deployed parameters — so it could not detect a strength loss).

Here is the same claim with teeth. At the CONSTANT sponge the CR floor FAILS
(`FloorsNonVacuous.poseidon2SpongeCR_separates`'s witness), so the PRE-port shape
`Poseidon2SpongeCR hash → …` holds there vacuously — and the POST-port shape, the same statement with
that antecedent deleted, is FALSE there. One point, both verdicts: the port is strictly stronger and
the difference is OBSERVABLE, which is exactly what the old tooth could not show.

Its sibling `ClosureAll.closedLogExtract_converse_costs_the_floor` is untouched: it is correctly
self-labelled ("recoverable ONLY by paying the refuted floor") and remains the model. -/
theorem closedLogExtract_port_detectably_stronger (S : CommitSurface) (R : Registry) :
    ¬ Dregg2.Circuit.Poseidon2Binding.Poseidon2SpongeCR (fun _ => (0 : ℤ))
    ∧ ¬ ClosedLogExtract S Dregg2.Circuit.Poseidon2Binding.Reference.refLH
          (fun _ => (0 : ℤ)) R 0 :=
  ⟨by
    intro h
    have hbad : ([0] : List ℤ) = [1] := h [0] [1] rfl
    simp at hbad,
   not_closedLogExtract_transfer_refLH S (fun _ => (0 : ℤ)) R⟩

/-! ## §5 — the dead tag's route is genuinely SPECIAL, and that is why §4 had to find another one.

The `other 15` refutation runs on the EMPTINESS of the conclusion relation at a dead tag. That route
really does stop at the live tags — a live slot's conclusion relation is INHABITED. Which is exactly
why the live restriction looked like a fix, and exactly why §4 does not use that route at all: `kstepAll 0`
is inhabited, and `ClosedLogExtract … 0` is false anyway, because the extract asserts `kstepAll 0`
between endpoints its trace never mentioned. -/

/-- FIRE (the live side): the conclusion relation at the LIVE tag 47 (pipelinedSend) is INHABITED — a
genuine `kstepAll 47` step exists (the receipt-prepend on the empty-cell state). Contrast
`kstepAll_not_total` at the dead tag 15. ⚑ Read with §4: an inhabited conclusion relation is NOT
enough to make a slot true, because `ClosedLogExtract` demands that relation at boundaries the
witness does not constrain. -/
theorem kstepAll_live_inhabited_47 :
    ∃ pre post : RecChainedState, kstepAll 47 pre post := by
  refine ⟨Dregg2.Circuit.WitnessRealizing.emptyState,
    { kernel := Dregg2.Circuit.WitnessRealizing.emptyKernel
    , log := [Dregg2.Circuit.Spec.QueuePipelinedSend.pipelinedSendReceipt 0] },
    .pipelinedSendA 0, rfl, ?_⟩
  simp only [Dregg2.Circuit.ActionDispatch.fullActionStep,
    Dregg2.Circuit.Spec.QueuePipelinedSend.PipelinedSendSpec]
  and_intros <;> rfl

/-! ## §6 — axiom hygiene. -/

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
#assert_axioms closedLogExtract_transfer_excludes_every_decode
#assert_axioms not_closedLogExtract_transfer_refLH
#assert_axioms not_nonempty_closureReadouts_refLH
#assert_axioms closedLogExtract_port_detectably_stronger
#assert_axioms kstepAll_live_inhabited_47

end Dregg2.Circuit.ClosureReadoutsRealizable
