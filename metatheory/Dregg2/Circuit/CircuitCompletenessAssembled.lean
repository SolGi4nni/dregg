/-
# Dregg2.Circuit.CircuitCompletenessAssembled — the COMPLETENESS CAPSTONE (converse of
`CircuitSoundnessAssembled` / `ClosureFanoutGenuine`).

`CircuitCompleteness.lightclient_complete` is the apex: from a genuine kernel transition `kstep e pre post`
+ the per-effect SATISFIABILITY rung `descriptorComplete S hash (R e) (kstep e)` AT the published effect +
the dual STARK floor `[StarkComplete hash R]` + the named hash CR carrier, it concludes an accepting batch
proof committing to `(pre, post)`. It carries the per-effect `descriptorComplete` as an OPAQUE hypothesis
at ONE claimed effect. This module DISCHARGES that hypothesis — value-leg-UNCONDITIONALLY, for EVERY live
effect tag — and composes the AUTHORITY dichotomy honestly, mirroring the soundness-side assembly
(`Rfix`/`kstepAll` + `closedLogExtract_all_genuine`'s 36-way actionTag dispatch + the
`lightclient_unfoolable_*_assembled` headlines) rung-for-rung in the converse direction.

## What is assembled (the dual of `ClosureFanoutGenuine`)

  1. **`CompletenessWitnesses` — the per-effect prover-floor bundle (`Type 1`).** The DUAL of
     `ClosureReadouts`: where soundness bundles per-effect `Satisfied2 (Rfix e) ⟹ <e>Encode` decode-
     READOUTS, completeness bundles per-effect `buildWitness` prover floors — for each live effect, the
     honest prover's CONSTRUCTION of a satisfying trace of `Rfix e` whose published commitment is the
     kernel's own `commitOf S pre post turn`. Every field is a NAMED realizable prover floor (the dual of
     `StarkSound`'s extraction — here a CONSTRUCTION), never an axiom, never `:= True`.

  2. **`descriptorComplete_all` — the `∀ e` VALUE-LEG discharge.** From the bundle, `∀ e,
     descriptorComplete S hash (Rfix e) (kstepAll e)` — the apex's per-effect SATISFIABILITY obligation,
     ENUMERATED over the live tags. The 36-way `match e` mirrors `closedLogExtract_all_genuine`: each tag
     LOWERS the kernel step `kstepAll e = dispatchArm e` to its leaf `Spec` (`dispatchArm_<e>` — the
     `fullActionStep` arm IS the leaf spec definitionally) and DISPATCHES to its proven `<e>_descriptor
     Complete` rung. This leg is UNCONDITIONAL in authority: `descriptorComplete` is purely the value/state
     SATISFIABILITY (a kernel-valid step HAS a satisfying trace); the authority lives INSIDE `kstepAll e`
     (the executor guard `dispatchArm` already carries) — discharged separately by the §3 dichotomy.

  3. **The AUTHORITY dichotomy (`authorityComplete_dichotomy`, re-composed).** The cap-gated effects'
     KERNEL-VALIDITY is authority-conditional: `kstepAll e pre post` is reachable iff the turn passes the
     deployed two-axis gate, which is EXACTLY (owner ∨ cap) — `authorityComplete_dichotomy`. We do NOT
     fold authority into a single clean `∀ e` value rung (that would be FALSE — the cap-open descriptor
     does not witness an owner-authorized turn, and the owner rung opens no cap). The honest composition:
     the value leg is `∀ e` unconditional; the authority leg is the dichotomy, covering every authorized
     turn through its OWN of the two disjuncts.

  4. **`lightclient_complete_assembled` — THE COMPLETENESS HEADLINE.** The apex at `Rfix`/`kstepAll`/the
     discharged `descriptorComplete_all`: a genuine kernel transition `kstepAll e pre post` (with
     `AccountsWF` boundary kernels) ⟹ ∃ an accepting batch proof against `vkOfRegistry Rfix` committing to
     `(pre, post)`. The value-leg premise is GONE from the signature; what remains is the named realizable
     floors (`StarkComplete`, the `Poseidon2SpongeCR` hash carrier, the `CompletenessWitnesses` prover
     bundle) — the dual of the soundness `lightclient_unfoolable_*_assembled`'s carried floors.

  5. **The BIDIRECTIONAL pairing (`verifyBatch_iff_kernel_valid`).** Stated side-by-side with the soundness
     headline `lightclient_unfoolable_assembled`: verifyBatch-acceptable ⟺ kernel-valid (each direction mod
     its OWN named floors). The two directions are NOT symmetric in their floors — soundness carries
     `StarkSound`/`WitnessDecodes`/the decode bridges; completeness carries `StarkComplete`/the prover
     bundle — so the honest statement names the floor difference rather than forcing a single ⟺.

## The honest characterization — IS the circuit complete?

The VALUE leg is UNCONDITIONALLY complete (mod the realizable prover/STARK floors): for EVERY live effect
tag, a kernel-valid step HAS a satisfying circuit witness — `descriptorComplete_all` is a total `∀ e`. The
AUTHORITY leg is STRUCTURALLY a dichotomy, NOT a uniform rung: completeness of a cap-gated turn's authority
holds via owner-OR-cap (`authorityComplete_dichotomy`), and this is the TRUE shape — there is no honest
single `∀ e` that witnesses both the owner and cap disjuncts with one descriptor. So the assembled
completeness is: **value-leg-unconditional ∀ e, composed with the two-disjunct authority dichotomy** — an
honest conditional in exactly one place (which authority disjunct a given turn rides), which is the right
answer, not a forced green.

## Axiom hygiene

`#assert_axioms` on the capstone theorems ⊆ {propext, Classical.choice, Quot.sound}. The named carriers
(`StarkComplete`, `Poseidon2SpongeCR`, the `CompletenessWitnesses` prover floors) are HYPOTHESES/instances,
not axioms — they do not appear in the axiom set. No `sorry`, no `native_decide`, no `:= True`, no fresh
axiom. NEW file; imports read-only.
-/
import Dregg2.Circuit.CircuitCompletenessValue
import Dregg2.Circuit.CircuitCompletenessRecord
import Dregg2.Circuit.CircuitCompletenessLifecycle
import Dregg2.Circuit.CircuitCompletenessAuthority
import Dregg2.Circuit.CircuitCompletenessSetInsert
import Dregg2.Circuit.CircuitCompletenessSatFloor
import Dregg2.Circuit.CircuitSoundnessAssembled

namespace Dregg2.Circuit.CircuitCompletenessAssembled

open Dregg2.Circuit.CircuitSoundness
open Dregg2.Circuit.CircuitSoundnessAssembled (Rfix kstepAll actionTagToPos transferDescr)
open Dregg2.Circuit.CircuitCompleteness (commitOf descriptorComplete stateDecode_construct
  lightclient_complete StarkComplete)
open Dregg2.Circuit.CircuitCompletenessSatFloor (SatFloor descriptorComplete_of_satFloor)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Circuit.DescriptorIR2 (EffectVmDescriptor2 VmTrace Satisfied2)
open Dregg2.Circuit.StateCommit (AccountsWF compressInjective compressNInjective cellLeafInjective
  RestHashIffFrame)
open Dregg2.Circuit.ClosureSurface (S_live)
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Circuit.ActionDispatch (actionTag fullActionStep fullActionStep_exec_iff)

set_option autoImplicit false

/-! ## §1 — `dispatchArm_<e>`: LOWER the kernel step to its leaf `Spec` (the converse of the soundness
`<spec>_to_dispatchArm`).

`kstepAll e pre post = dispatchArm e pre post = ∃ fa, actionTag fa = e ∧ fullActionStep pre fa post`. For a
FIXED live tag `e`, the `actionTag fa = e` constraint PINS the constructor of `fa`, and `fullActionStep pre
fa post` is THEN definitionally the leaf `Spec` for that constructor (the `fullActionStep` `match`). These
lemmas perform that case-pin once per effect, delivering the leaf spec the per-effect `<e>_descriptor
Complete` rung consumes. They are the EXACT inverse of soundness's `<spec>_to_dispatchArm` (which packs the
leaf spec INTO a `dispatchArm`). -/

/-- Generic case-pinner: a `dispatchArm e` at a tag with a UNIQUE constructor whose `fullActionStep` arm is
`leafSpec` yields that leaf spec. We state per-effect instances below (the constructor identification is
effect-specific). -/
theorem dispatchArm_transfer (pre post : RecChainedState)
    (h : kstepAll 0 pre post) :
    ∃ (tr : Turn) (a : AssetId),
      Dregg2.Circuit.Spec.BalanceMovement.BalanceMovementSpec pre tr a post := by
  obtain ⟨fa, htag, hstep⟩ := h
  cases fa <;> simp only [actionTag] at htag <;>
    first | (rw [fullActionStep] at hstep; exact ⟨_, _, hstep⟩) | omega

theorem dispatchArm_burn (pre post : RecChainedState)
    (h : kstepAll 4 pre post) :
    ∃ (actor cell : CellId) (a : AssetId) (amt : ℤ),
      Dregg2.Circuit.Spec.SupplyDestruction.BurnSpec pre actor cell a amt post := by
  obtain ⟨fa, htag, hstep⟩ := h
  cases fa <;> simp only [actionTag] at htag <;>
    first | (rw [fullActionStep] at hstep; exact ⟨_, _, _, _, hstep⟩) | omega

theorem dispatchArm_mint (pre post : RecChainedState)
    (h : kstepAll 3 pre post) :
    ∃ (actor cell : CellId) (a : AssetId) (amt : ℤ),
      Dregg2.Circuit.Spec.SupplyCreation.MintASpec pre actor cell a amt post := by
  obtain ⟨fa, htag, hstep⟩ := h
  cases fa <;> simp only [actionTag] at htag <;>
    first | (rw [fullActionStep] at hstep; exact ⟨_, _, _, _, hstep⟩) | omega

theorem dispatchArm_bridgeMint (pre post : RecChainedState)
    (h : kstepAll 20 pre post) :
    ∃ (actor cell : CellId) (a : AssetId) (amt : ℤ),
      Dregg2.Circuit.Spec.SupplyCreation.MintASpec pre actor cell a amt post := by
  obtain ⟨fa, htag, hstep⟩ := h
  cases fa <;> simp only [actionTag] at htag <;>
    first | (rw [fullActionStep] at hstep; exact ⟨_, _, _, _, hstep⟩) | omega

theorem dispatchArm_setField (pre post : RecChainedState)
    (h : kstepAll 5 pre post) :
    ∃ (actor cell : CellId) (f : FieldName) (v : ℤ),
      Dregg2.Circuit.Spec.CellStateField.SetFieldSpec pre actor cell f v post := by
  obtain ⟨fa, htag, hstep⟩ := h
  cases fa <;> simp only [actionTag] at htag <;>
    first | (rw [fullActionStep] at hstep; exact ⟨_, _, _, _, hstep⟩) | omega

theorem dispatchArm_incrementNonce (pre post : RecChainedState)
    (h : kstepAll 7 pre post) :
    ∃ (actor cell : CellId) (n : ℤ),
      Dregg2.Circuit.Spec.CellStateMonotone.IncrementNonceSpec pre actor cell n post := by
  obtain ⟨fa, htag, hstep⟩ := h
  cases fa <;> simp only [actionTag] at htag <;>
    first | (rw [fullActionStep] at hstep; exact ⟨_, _, _, hstep⟩) | omega

theorem dispatchArm_emitEvent (pre post : RecChainedState)
    (h : kstepAll 6 pre post) :
    ∃ (actor cell : CellId) (topic data : ℤ),
      Dregg2.Circuit.Spec.CellStateLog.EmitEventSpec pre actor cell topic data post := by
  obtain ⟨fa, htag, hstep⟩ := h
  cases fa <;> simp only [actionTag] at htag <;>
    first | (rw [fullActionStep] at hstep; exact ⟨_, _, _, _, hstep⟩) | omega

theorem dispatchArm_pipelinedSend (pre post : RecChainedState)
    (h : kstepAll 47 pre post) :
    ∃ (actor : CellId),
      Dregg2.Circuit.Spec.QueuePipelinedSend.PipelinedSendSpec pre actor post := by
  obtain ⟨fa, htag, hstep⟩ := h
  cases fa <;> simp only [actionTag] at htag <;>
    first | (rw [fullActionStep] at hstep; exact ⟨_, hstep⟩) | omega

theorem dispatchArm_makeSovereign (pre post : RecChainedState)
    (h : kstepAll 38 pre post) :
    ∃ (actor cell : CellId),
      Dregg2.Circuit.Spec.SovereignCommitment.MakeSovereignSpec pre actor cell post := by
  obtain ⟨fa, htag, hstep⟩ := h
  cases fa <;> simp only [actionTag] at htag <;>
    first | (rw [fullActionStep] at hstep; exact ⟨_, _, hstep⟩) | omega

theorem dispatchArm_setPermissions (pre post : RecChainedState)
    (h : kstepAll 8 pre post) :
    ∃ (actor cell : CellId) (p : ℤ),
      Dregg2.Circuit.Spec.CellStatePermissions.SetPermissionsSpec pre actor cell p post := by
  obtain ⟨fa, htag, hstep⟩ := h
  cases fa <;> simp only [actionTag] at htag <;>
    first | (rw [fullActionStep] at hstep; exact ⟨_, _, _, hstep⟩) | omega

theorem dispatchArm_setVK (pre post : RecChainedState)
    (h : kstepAll 9 pre post) :
    ∃ (actor cell : CellId) (vk : ℤ),
      Dregg2.Circuit.Spec.CellStateVK.SetVKSpec pre actor cell vk post := by
  obtain ⟨fa, htag, hstep⟩ := h
  cases fa <;> simp only [actionTag] at htag <;>
    first | (rw [fullActionStep] at hstep; exact ⟨_, _, _, hstep⟩) | omega

theorem dispatchArm_cellSeal (pre post : RecChainedState)
    (h : kstepAll 52 pre post) :
    ∃ (actor cell : CellId),
      Dregg2.Circuit.Spec.CellLifecycle.CellSealSpec pre actor cell post := by
  obtain ⟨fa, htag, hstep⟩ := h
  cases fa <;> simp only [actionTag] at htag <;>
    first | (rw [fullActionStep] at hstep; exact ⟨_, _, hstep⟩) | omega

theorem dispatchArm_cellUnseal (pre post : RecChainedState)
    (h : kstepAll 53 pre post) :
    ∃ (actor cell : CellId),
      Dregg2.Circuit.Spec.CellLifecycle.CellUnsealSpec pre actor cell post := by
  obtain ⟨fa, htag, hstep⟩ := h
  cases fa <;> simp only [actionTag] at htag <;>
    first | (rw [fullActionStep] at hstep; exact ⟨_, _, hstep⟩) | omega

theorem dispatchArm_cellDestroy (pre post : RecChainedState)
    (h : kstepAll 54 pre post) :
    ∃ (actor cell : CellId) (certHash : Nat),
      Dregg2.Circuit.Spec.CellLifecycle.CellDestroySpec pre actor cell certHash post := by
  obtain ⟨fa, htag, hstep⟩ := h
  cases fa <;> simp only [actionTag] at htag <;>
    first | (rw [fullActionStep] at hstep; exact ⟨_, _, _, hstep⟩) | omega

theorem dispatchArm_refusal (pre post : RecChainedState)
    (h : kstepAll 39 pre post) :
    ∃ (actor cell : CellId),
      Dregg2.Circuit.Spec.CellStateAudit.RefusalSpec pre actor cell post := by
  obtain ⟨fa, htag, hstep⟩ := h
  cases fa <;> simp only [actionTag] at htag <;>
    first | (rw [fullActionStep] at hstep; exact ⟨_, _, hstep⟩) | omega

theorem dispatchArm_receiptArchive (pre post : RecChainedState)
    (h : kstepAll 40 pre post) :
    ∃ (actor cell : CellId),
      Dregg2.Circuit.Spec.CellStateAudit.ReceiptArchiveSpec pre actor cell post := by
  obtain ⟨fa, htag, hstep⟩ := h
  cases fa <;> simp only [actionTag] at htag <;>
    first | (rw [fullActionStep] at hstep; exact ⟨_, _, hstep⟩) | omega

theorem dispatchArm_noteSpend (pre post : RecChainedState)
    (h : kstepAll 27 pre post) :
    ∃ (nf : Nat) (actor : CellId) (spendProof : Bool),
      Dregg2.Circuit.Spec.NoteNullifier.NoteSpendSpec pre nf actor spendProof post := by
  obtain ⟨fa, htag, hstep⟩ := h
  cases fa <;> simp only [actionTag] at htag <;>
    first | (rw [fullActionStep] at hstep; exact ⟨_, _, _, hstep⟩) | omega

theorem dispatchArm_noteCreate (pre post : RecChainedState)
    (h : kstepAll 28 pre post) :
    ∃ (cm : Nat) (actor : CellId),
      Dregg2.Circuit.Spec.NoteCommitment.NoteCreateASpec pre cm actor post := by
  obtain ⟨fa, htag, hstep⟩ := h
  cases fa <;> simp only [actionTag] at htag <;>
    first | (rw [fullActionStep] at hstep; exact ⟨_, _, hstep⟩) | omega

theorem dispatchArm_createCell (pre post : RecChainedState)
    (h : kstepAll 17 pre post) :
    ∃ (actor newCell : CellId),
      Dregg2.Circuit.Spec.AccountGrowth.CreateCellSpec pre actor newCell post := by
  obtain ⟨fa, htag, hstep⟩ := h
  cases fa <;> simp only [actionTag] at htag <;>
    first | (rw [fullActionStep] at hstep; exact ⟨_, _, hstep⟩) | omega

theorem dispatchArm_createCellFromFactory (pre post : RecChainedState)
    (h : kstepAll 18 pre post) :
    ∃ (actor newCell : CellId) (vk : ℤ),
      Dregg2.Circuit.Spec.FactoryCreation.CreateFromFactorySpec pre actor newCell vk post := by
  obtain ⟨fa, htag, hstep⟩ := h
  cases fa <;> simp only [actionTag] at htag <;>
    first | (rw [fullActionStep] at hstep; exact ⟨_, _, _, hstep⟩) | omega

theorem dispatchArm_spawn (pre post : RecChainedState)
    (h : kstepAll 19 pre post) :
    ∃ (actor child target : CellId),
      Dregg2.Circuit.Spec.AccountGrowth.SpawnSpec pre actor child target post := by
  obtain ⟨fa, htag, hstep⟩ := h
  cases fa <;> simp only [actionTag] at htag <;>
    first | (rw [fullActionStep] at hstep; exact ⟨_, _, _, hstep⟩) | omega

/-! ## §2 — `CompletenessWitnesses`: the per-effect UNIFORM `SatFloor` bundle (DUAL of `ClosureReadouts`).

For each VALUE/RECORD/LIFECYCLE/SET-INSERT live effect, the realizable `SatFloor`-class prover floor: from
the leaf kernel `Spec` the honest prover CONSTRUCTS a satisfying trace of `Rfix e` publishing the kernel's
own `commitOf S pre post turn` — and NOTHING ELSE. The fat per-effect `<e>TraceProver`/`<e>RootProver`
bundles (the trace rows, the boundary `CellState`s, the FIX-root insert data) are GONE: they were
spec-DETERMINED (built by `<e>_rotatedEncodes_construct`, consumed only into an unused `_henc`), so the
rung never needed them. Each field is now the SAME uniform shape — `Satisfied2 hash (Rfix e) … ∧
publication` — the descriptor-AGNOSTIC StarkComplete-class realizability, the dual of the soundness
`<e>TraceReadout` extraction (soundness READS a trace; completeness BUILDS one). This is the value-leg
analog of the authority-leg slim `CapOpenTraceFloor`.

Every field is at the SAME descriptor `Rfix e` (the value tags' `Rfix e = <e>V3` is `rfl`, the `Rfix_*`
identities); the dispatchers (§4) lower the kernel step to its leaf `Spec` and feed the slim field. -/

/-- The per-effect slim `Satisfied2`-publication floor, uniform over effects — `SatFloor` specialized to a
fixed effect's leaf `Spec` antecedent. (Stated inline per field for the leaf-spec antecedent each tag
carries; the realizability shape is identical across all 21.) -/
structure CompletenessWitnesses (S : CommitSurface) (hash : List ℤ → ℤ)
    (compressN : List ℤ → ℤ) : Type 1 where
  /-- transfer (tag 0). -/
  bwTransfer : ∀ (pre post : RecChainedState) (tr : Turn) (a : AssetId) (turn : BoundaryTurn),
    Dregg2.Circuit.Spec.BalanceMovement.BalanceMovementSpec pre tr a post →
    ∃ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace),
      Satisfied2 hash Dregg2.Circuit.RotatedKernelRefinement.transferV3 minit mfin maddrs t ∧
      tracePublishedCommit t = commitOf S pre post turn
  /-- burn (tag 4). -/
  bwBurn : ∀ (pre post : RecChainedState) (actor cell : CellId) (a : AssetId) (amt : ℤ)
      (turn : BoundaryTurn),
    Dregg2.Circuit.Spec.SupplyDestruction.BurnSpec pre actor cell a amt post →
    ∃ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace),
      Satisfied2 hash Dregg2.Circuit.RotatedKernelRefinementMintBurn.burnV3 minit mfin maddrs t ∧
      tracePublishedCommit t = commitOf S pre post turn
  /-- mint (tag 3) — also re-exported to bridgeMint (tag 20). -/
  bwMint : ∀ (pre post : RecChainedState) (actor cell : CellId) (a : AssetId) (amt : ℤ)
      (turn : BoundaryTurn),
    Dregg2.Circuit.Spec.SupplyCreation.MintASpec pre actor cell a amt post →
    ∃ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace),
      Satisfied2 hash Dregg2.Circuit.Emit.EffectVmEmitRotationV3.mintV3 minit mfin maddrs t ∧
      tracePublishedCommit t = commitOf S pre post turn
  /-- setField (tag 5) — GENERIC field name, at the live `Rfix 5` descriptor (the `setFieldDyn` rung). -/
  bwSetFieldDyn : ∀ (pre post : RecChainedState) (actor cell : CellId) (f : FieldName) (v : ℤ)
      (turn : BoundaryTurn),
    Dregg2.Circuit.Spec.CellStateField.SetFieldSpec pre actor cell f v post →
    ∃ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace),
      Satisfied2 hash (Rfix 5) minit mfin maddrs t ∧
      tracePublishedCommit t = commitOf S pre post turn
  /-- incrementNonce (tag 7). -/
  bwIncNonce : ∀ (pre post : RecChainedState) (actor cell : CellId) (n : ℤ) (turn : BoundaryTurn),
    Dregg2.Circuit.Spec.CellStateMonotone.IncrementNonceSpec pre actor cell n post →
    ∃ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace),
      Satisfied2 hash Dregg2.Circuit.RotatedKernelRefinementIncNonce.incNonceV3 minit mfin maddrs t ∧
      tracePublishedCommit t = commitOf S pre post turn
  /-- emitEvent (tag 6) — LIVE descriptor. -/
  bwEmitEvent : ∀ (pre post : RecChainedState) (actor cell : CellId) (topic data : ℤ)
      (turn : BoundaryTurn),
    Dregg2.Circuit.Spec.CellStateLog.EmitEventSpec pre actor cell topic data post →
    ∃ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace),
      Satisfied2 hash (Rfix 6) minit mfin maddrs t ∧
      tracePublishedCommit t = commitOf S pre post turn
  /-- pipelinedSend (tag 47) — LIVE descriptor. -/
  bwPipelinedSend : ∀ (pre post : RecChainedState) (actor : CellId) (turn : BoundaryTurn),
    Dregg2.Circuit.Spec.QueuePipelinedSend.PipelinedSendSpec pre actor post →
    ∃ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace),
      Satisfied2 hash (Rfix 47) minit mfin maddrs t ∧
      tracePublishedCommit t = commitOf S pre post turn
  /-- makeSovereign (tag 38). -/
  bwMakeSovereign : ∀ (pre post : RecChainedState) (actor cell : CellId) (turn : BoundaryTurn),
    Dregg2.Circuit.Spec.SovereignCommitment.MakeSovereignSpec pre actor cell post →
    ∃ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace),
      Satisfied2 hash (Rfix 38) minit mfin maddrs t ∧
      tracePublishedCommit t = commitOf S pre post turn
  /-- setPermissions (tag 8). -/
  bwSetPermissions : ∀ (pre post : RecChainedState) (actor cell : CellId) (p : ℤ) (turn : BoundaryTurn),
    Dregg2.Circuit.Spec.CellStatePermissions.SetPermissionsSpec pre actor cell p post →
    ∃ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace),
      Satisfied2 hash (Rfix 8) minit mfin maddrs t ∧
      tracePublishedCommit t = commitOf S pre post turn
  /-- setVK (tag 9). -/
  bwSetVK : ∀ (pre post : RecChainedState) (actor cell : CellId) (vk : ℤ) (turn : BoundaryTurn),
    Dregg2.Circuit.Spec.CellStateVK.SetVKSpec pre actor cell vk post →
    ∃ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace),
      Satisfied2 hash (Rfix 9) minit mfin maddrs t ∧
      tracePublishedCommit t = commitOf S pre post turn
  /-- cellSeal (tag 52). -/
  bwCellSeal : ∀ (pre post : RecChainedState) (actor cell : CellId) (turn : BoundaryTurn),
    Dregg2.Circuit.Spec.CellLifecycle.CellSealSpec pre actor cell post →
    ∃ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace),
      Satisfied2 hash (Rfix 52) minit mfin maddrs t ∧
      tracePublishedCommit t = commitOf S pre post turn
  /-- cellUnseal (tag 53). -/
  bwCellUnseal : ∀ (pre post : RecChainedState) (actor cell : CellId) (turn : BoundaryTurn),
    Dregg2.Circuit.Spec.CellLifecycle.CellUnsealSpec pre actor cell post →
    ∃ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace),
      Satisfied2 hash (Rfix 53) minit mfin maddrs t ∧
      tracePublishedCommit t = commitOf S pre post turn
  /-- cellDestroy (tag 54). -/
  bwCellDestroy : ∀ (pre post : RecChainedState) (actor cell : CellId) (certHash : Nat)
      (turn : BoundaryTurn),
    Dregg2.Circuit.Spec.CellLifecycle.CellDestroySpec pre actor cell certHash post →
    ∃ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace),
      Satisfied2 hash (Rfix 54) minit mfin maddrs t ∧
      tracePublishedCommit t = commitOf S pre post turn
  /-- refusal (tag 39). -/
  bwRefusal : ∀ (pre post : RecChainedState) (actor cell : CellId) (turn : BoundaryTurn),
    Dregg2.Circuit.Spec.CellStateAudit.RefusalSpec pre actor cell post →
    ∃ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace),
      Satisfied2 hash (Rfix 39) minit mfin maddrs t ∧
      tracePublishedCommit t = commitOf S pre post turn
  /-- receiptArchive (tag 40). -/
  bwReceiptArchive : ∀ (pre post : RecChainedState) (actor cell : CellId) (turn : BoundaryTurn),
    Dregg2.Circuit.Spec.CellStateAudit.ReceiptArchiveSpec pre actor cell post →
    ∃ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace),
      Satisfied2 hash (Rfix 40) minit mfin maddrs t ∧
      tracePublishedCommit t = commitOf S pre post turn
  /-- noteSpend (tag 27). -/
  bwNoteSpend : ∀ (pre post : RecChainedState) (nf : Nat) (actor : CellId) (spendProof : Bool)
      (turn : BoundaryTurn),
    Dregg2.Circuit.Spec.NoteNullifier.NoteSpendSpec pre nf actor spendProof post →
    ∃ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace),
      Satisfied2 hash (Rfix 27) minit mfin maddrs t ∧
      tracePublishedCommit t = commitOf S pre post turn
  /-- noteCreate (tag 28). -/
  bwNoteCreate : ∀ (pre post : RecChainedState) (cm : Nat) (actor : CellId) (turn : BoundaryTurn),
    Dregg2.Circuit.Spec.NoteCommitment.NoteCreateASpec pre cm actor post →
    ∃ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace),
      Satisfied2 hash (Rfix 28) minit mfin maddrs t ∧
      tracePublishedCommit t = commitOf S pre post turn
  /-- createCell (tag 17). -/
  bwCreateCell : ∀ (pre post : RecChainedState) (actor newCell : CellId) (turn : BoundaryTurn),
    Dregg2.Circuit.Spec.AccountGrowth.CreateCellSpec pre actor newCell post →
    ∃ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace),
      Satisfied2 hash (Rfix 17) minit mfin maddrs t ∧
      tracePublishedCommit t = commitOf S pre post turn
  /-- createCellFromFactory (tag 18). -/
  bwCreateCellFromFactory : ∀ (pre post : RecChainedState) (actor newCell : CellId) (vk : ℤ)
      (turn : BoundaryTurn),
    Dregg2.Circuit.Spec.FactoryCreation.CreateFromFactorySpec pre actor newCell vk post →
    ∃ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace),
      Satisfied2 hash (Rfix 18) minit mfin maddrs t ∧
      tracePublishedCommit t = commitOf S pre post turn

/-! ## §3 — `Rfix_<e>` value-tag descriptor identities (the cohort positions the re-key preserves).

The Value rungs conclude `Satisfied2 hash <e>V3`; the apex needs `Satisfied2 hash (Rfix e)`. The re-key
(`actionTagToPos`) lands each value tag at its cohort position, so `Rfix e = <e>V3` by `rfl`. -/

theorem Rfix_burn : Rfix 4 = Dregg2.Circuit.RotatedKernelRefinementMintBurn.burnV3 := rfl
theorem Rfix_mint : Rfix 3 = Dregg2.Circuit.Emit.EffectVmEmitRotationV3.mintV3 := rfl
theorem Rfix_bridgeMint : Rfix 20 = Dregg2.Circuit.Emit.EffectVmEmitRotationV3.mintV3 := rfl

/-! ## §4 — the per-effect VALUE-LEG dischargers (DUAL of `closedLogExtract_<e>_closed`).

Each `descriptorComplete_<e> : descriptorComplete S hash (Rfix e) (kstepAll e)` now rides the UNIFORM slim
floor: it ASSEMBLES a `SatFloor S hash (Rfix e) (kstepAll e)` from the bundle's slim `bw<e>` field
(`dispatchArm_<e>` LOWERS the kernel step to its leaf `Spec`, then the slim field supplies the satisfying
trace + publication), and discharges `descriptorComplete` via `descriptorComplete_of_satFloor` (the decode
is CONSTRUCTED, not carried). The fat `<e>_descriptorComplete` rungs over `<e>TraceProver`/`<e>RootProver`
are NO LONGER on this path — the spec-determined prover data DISAPPEARED from the live apex (it survives
only as the SEPARATE `<e>_descriptorComplete_genuine` teeth). For the VALUE-family tags pinned to a
concrete `<e>V3` descriptor, `Rfix e = <e>V3` is `rfl` (the `Rfix_*` identities), so the slim field's
`Satisfied2 hash <e>V3 …` IS `Satisfied2 hash (Rfix e) …` definitionally.

These are UNCONDITIONAL in authority: `descriptorComplete` is the value/state SATISFIABILITY (a kernel-valid
step HAS a satisfying trace publishing the kernel's own commitment); the authority lives INSIDE `kstepAll e`
(the `dispatchArm` executor guard) and is discharged separately by the §6 dichotomy. The dual of each
`closedLogExtract_<e>_closed`. -/

/-- transfer (tag 0). -/
theorem descriptorComplete_transfer
    {CH : CellId → Value → ℤ} {RH : RecordKernelState → ℤ}
    {cmb compress : ℤ → ℤ → ℤ} {compressN : List ℤ → ℤ}
    {hCmb : compressInjective cmb} {hCompress : compressInjective compress}
    {hCompressN : compressNInjective compressN} {hLeaf : cellLeafInjective CH}
    {hRest : RestHashIffFrame RH}
    (hash : List ℤ → ℤ)
    (bw : CompletenessWitnesses (S_live CH RH cmb compress compressN hCmb hCompress hCompressN hLeaf hRest)
      hash compressN) :
    descriptorComplete (S_live CH RH cmb compress compressN hCmb hCompress hCompressN hLeaf hRest)
      hash (Rfix 0) (kstepAll 0) :=
  descriptorComplete_of_satFloor _ hash (Rfix 0) (kstepAll 0) <| by
    intro pre post turn hstep _hpreWF _hpostWF
    obtain ⟨tr, a, hspec⟩ := dispatchArm_transfer pre post hstep
    exact bw.bwTransfer pre post tr a turn hspec

/-- burn (tag 4). -/
theorem descriptorComplete_burn (S : CommitSurface) (hash : List ℤ → ℤ) (compressN : List ℤ → ℤ)
    (bw : CompletenessWitnesses S hash compressN) :
    descriptorComplete S hash (Rfix 4) (kstepAll 4) :=
  descriptorComplete_of_satFloor S hash (Rfix 4) (kstepAll 4) <| by
    intro pre post turn hstep _hpreWF _hpostWF
    obtain ⟨actor, cell, a, amt, hspec⟩ := dispatchArm_burn pre post hstep
    rw [Rfix_burn]
    exact bw.bwBurn pre post actor cell a amt turn hspec

/-- mint (tag 3). -/
theorem descriptorComplete_mint (S : CommitSurface) (hash : List ℤ → ℤ) (compressN : List ℤ → ℤ)
    (bw : CompletenessWitnesses S hash compressN) :
    descriptorComplete S hash (Rfix 3) (kstepAll 3) :=
  descriptorComplete_of_satFloor S hash (Rfix 3) (kstepAll 3) <| by
    intro pre post turn hstep _hpreWF _hpostWF
    obtain ⟨actor, cell, a, amt, hspec⟩ := dispatchArm_mint pre post hstep
    rw [Rfix_mint]
    exact bw.bwMint pre post actor cell a amt turn hspec

/-- bridgeMint (tag 20) — shares the mint floor over the same `mintV3`. -/
theorem descriptorComplete_bridgeMint (S : CommitSurface) (hash : List ℤ → ℤ) (compressN : List ℤ → ℤ)
    (bw : CompletenessWitnesses S hash compressN) :
    descriptorComplete S hash (Rfix 20) (kstepAll 20) :=
  descriptorComplete_of_satFloor S hash (Rfix 20) (kstepAll 20) <| by
    intro pre post turn hstep _hpreWF _hpostWF
    obtain ⟨actor, cell, a, amt, hspec⟩ := dispatchArm_bridgeMint pre post hstep
    rw [Rfix_bridgeMint]
    exact bw.bwMint pre post actor cell a amt turn hspec

/-- setField (tag 5) — at `Rfix 5`, GENERIC field name. -/
theorem descriptorComplete_setField (S : CommitSurface) (hash : List ℤ → ℤ) (compressN : List ℤ → ℤ)
    (bw : CompletenessWitnesses S hash compressN) :
    descriptorComplete S hash (Rfix 5) (kstepAll 5) :=
  descriptorComplete_of_satFloor S hash (Rfix 5) (kstepAll 5) <| by
    intro pre post turn hstep _hpreWF _hpostWF
    obtain ⟨actor, cell, f, v, hspec⟩ := dispatchArm_setField pre post hstep
    exact bw.bwSetFieldDyn pre post actor cell f v turn hspec

/-- incrementNonce (tag 7). -/
theorem descriptorComplete_incrementNonce (S : CommitSurface) (hash : List ℤ → ℤ) (compressN : List ℤ → ℤ)
    (bw : CompletenessWitnesses S hash compressN) :
    descriptorComplete S hash (Rfix 7) (kstepAll 7) :=
  descriptorComplete_of_satFloor S hash (Rfix 7) (kstepAll 7) <| by
    intro pre post turn hstep _hpreWF _hpostWF
    obtain ⟨actor, cell, n, hspec⟩ := dispatchArm_incrementNonce pre post hstep
    rw [show Rfix 7 = Dregg2.Circuit.RotatedKernelRefinementIncNonce.incNonceV3 from rfl]
    exact bw.bwIncNonce pre post actor cell n turn hspec

/-- emitEvent (tag 6) — LIVE descriptor. -/
theorem descriptorComplete_emitEvent (S : CommitSurface) (hash : List ℤ → ℤ) (compressN : List ℤ → ℤ)
    (bw : CompletenessWitnesses S hash compressN) :
    descriptorComplete S hash (Rfix 6) (kstepAll 6) :=
  descriptorComplete_of_satFloor S hash (Rfix 6) (kstepAll 6) <| by
    intro pre post turn hstep _hpreWF _hpostWF
    obtain ⟨actor, cell, topic, data, hspec⟩ := dispatchArm_emitEvent pre post hstep
    exact bw.bwEmitEvent pre post actor cell topic data turn hspec

/-- pipelinedSend (tag 47) — LIVE descriptor. -/
theorem descriptorComplete_pipelinedSend (S : CommitSurface) (hash : List ℤ → ℤ) (compressN : List ℤ → ℤ)
    (bw : CompletenessWitnesses S hash compressN) :
    descriptorComplete S hash (Rfix 47) (kstepAll 47) :=
  descriptorComplete_of_satFloor S hash (Rfix 47) (kstepAll 47) <| by
    intro pre post turn hstep _hpreWF _hpostWF
    obtain ⟨actor, hspec⟩ := dispatchArm_pipelinedSend pre post hstep
    exact bw.bwPipelinedSend pre post actor turn hspec

/-- makeSovereign (tag 38). -/
theorem descriptorComplete_makeSovereign (S : CommitSurface) (hash : List ℤ → ℤ) (compressN : List ℤ → ℤ)
    (bw : CompletenessWitnesses S hash compressN) :
    descriptorComplete S hash (Rfix 38) (kstepAll 38) :=
  descriptorComplete_of_satFloor S hash (Rfix 38) (kstepAll 38) <| by
    intro pre post turn hstep _hpreWF _hpostWF
    obtain ⟨actor, cell, hspec⟩ := dispatchArm_makeSovereign pre post hstep
    exact bw.bwMakeSovereign pre post actor cell turn hspec

/-- setPermissions (tag 8). -/
theorem descriptorComplete_setPermissions (S : CommitSurface) (hash : List ℤ → ℤ) (compressN : List ℤ → ℤ)
    (bw : CompletenessWitnesses S hash compressN) :
    descriptorComplete S hash (Rfix 8) (kstepAll 8) :=
  descriptorComplete_of_satFloor S hash (Rfix 8) (kstepAll 8) <| by
    intro pre post turn hstep _hpreWF _hpostWF
    obtain ⟨actor, cell, p, hspec⟩ := dispatchArm_setPermissions pre post hstep
    exact bw.bwSetPermissions pre post actor cell p turn hspec

/-- setVK (tag 9). -/
theorem descriptorComplete_setVK (S : CommitSurface) (hash : List ℤ → ℤ) (compressN : List ℤ → ℤ)
    (bw : CompletenessWitnesses S hash compressN) :
    descriptorComplete S hash (Rfix 9) (kstepAll 9) :=
  descriptorComplete_of_satFloor S hash (Rfix 9) (kstepAll 9) <| by
    intro pre post turn hstep _hpreWF _hpostWF
    obtain ⟨actor, cell, vk, hspec⟩ := dispatchArm_setVK pre post hstep
    exact bw.bwSetVK pre post actor cell vk turn hspec

/-- cellSeal (tag 52). -/
theorem descriptorComplete_cellSeal (S : CommitSurface) (hash : List ℤ → ℤ) (compressN : List ℤ → ℤ)
    (bw : CompletenessWitnesses S hash compressN) :
    descriptorComplete S hash (Rfix 52) (kstepAll 52) :=
  descriptorComplete_of_satFloor S hash (Rfix 52) (kstepAll 52) <| by
    intro pre post turn hstep _hpreWF _hpostWF
    obtain ⟨actor, cell, hspec⟩ := dispatchArm_cellSeal pre post hstep
    exact bw.bwCellSeal pre post actor cell turn hspec

/-- cellUnseal (tag 53). -/
theorem descriptorComplete_cellUnseal (S : CommitSurface) (hash : List ℤ → ℤ) (compressN : List ℤ → ℤ)
    (bw : CompletenessWitnesses S hash compressN) :
    descriptorComplete S hash (Rfix 53) (kstepAll 53) :=
  descriptorComplete_of_satFloor S hash (Rfix 53) (kstepAll 53) <| by
    intro pre post turn hstep _hpreWF _hpostWF
    obtain ⟨actor, cell, hspec⟩ := dispatchArm_cellUnseal pre post hstep
    exact bw.bwCellUnseal pre post actor cell turn hspec

/-- cellDestroy (tag 54). -/
theorem descriptorComplete_cellDestroy (S : CommitSurface) (hash : List ℤ → ℤ) (compressN : List ℤ → ℤ)
    (bw : CompletenessWitnesses S hash compressN) :
    descriptorComplete S hash (Rfix 54) (kstepAll 54) :=
  descriptorComplete_of_satFloor S hash (Rfix 54) (kstepAll 54) <| by
    intro pre post turn hstep _hpreWF _hpostWF
    obtain ⟨actor, cell, certHash, hspec⟩ := dispatchArm_cellDestroy pre post hstep
    exact bw.bwCellDestroy pre post actor cell certHash turn hspec

/-- refusal (tag 39). -/
theorem descriptorComplete_refusal (S : CommitSurface) (hash : List ℤ → ℤ) (compressN : List ℤ → ℤ)
    (bw : CompletenessWitnesses S hash compressN) :
    descriptorComplete S hash (Rfix 39) (kstepAll 39) :=
  descriptorComplete_of_satFloor S hash (Rfix 39) (kstepAll 39) <| by
    intro pre post turn hstep _hpreWF _hpostWF
    obtain ⟨actor, cell, hspec⟩ := dispatchArm_refusal pre post hstep
    exact bw.bwRefusal pre post actor cell turn hspec

/-- receiptArchive (tag 40). -/
theorem descriptorComplete_receiptArchive (S : CommitSurface) (hash : List ℤ → ℤ) (compressN : List ℤ → ℤ)
    (bw : CompletenessWitnesses S hash compressN) :
    descriptorComplete S hash (Rfix 40) (kstepAll 40) :=
  descriptorComplete_of_satFloor S hash (Rfix 40) (kstepAll 40) <| by
    intro pre post turn hstep _hpreWF _hpostWF
    obtain ⟨actor, cell, hspec⟩ := dispatchArm_receiptArchive pre post hstep
    exact bw.bwReceiptArchive pre post actor cell turn hspec

/-- noteSpend (tag 27). -/
theorem descriptorComplete_noteSpend (S : CommitSurface) (hash : List ℤ → ℤ) (compressN : List ℤ → ℤ)
    (bw : CompletenessWitnesses S hash compressN) :
    descriptorComplete S hash (Rfix 27) (kstepAll 27) :=
  descriptorComplete_of_satFloor S hash (Rfix 27) (kstepAll 27) <| by
    intro pre post turn hstep _hpreWF _hpostWF
    obtain ⟨nf, actor, spendProof, hspec⟩ := dispatchArm_noteSpend pre post hstep
    exact bw.bwNoteSpend pre post nf actor spendProof turn hspec

/-- noteCreate (tag 28). -/
theorem descriptorComplete_noteCreate (S : CommitSurface) (hash : List ℤ → ℤ) (compressN : List ℤ → ℤ)
    (bw : CompletenessWitnesses S hash compressN) :
    descriptorComplete S hash (Rfix 28) (kstepAll 28) :=
  descriptorComplete_of_satFloor S hash (Rfix 28) (kstepAll 28) <| by
    intro pre post turn hstep _hpreWF _hpostWF
    obtain ⟨cm, actor, hspec⟩ := dispatchArm_noteCreate pre post hstep
    exact bw.bwNoteCreate pre post cm actor turn hspec

/-- createCell (tag 17). -/
theorem descriptorComplete_createCell (S : CommitSurface) (hash : List ℤ → ℤ) (compressN : List ℤ → ℤ)
    (bw : CompletenessWitnesses S hash compressN) :
    descriptorComplete S hash (Rfix 17) (kstepAll 17) :=
  descriptorComplete_of_satFloor S hash (Rfix 17) (kstepAll 17) <| by
    intro pre post turn hstep _hpreWF _hpostWF
    obtain ⟨actor, newCell, hspec⟩ := dispatchArm_createCell pre post hstep
    exact bw.bwCreateCell pre post actor newCell turn hspec

/-- createCellFromFactory (tag 18). -/
theorem descriptorComplete_createCellFromFactory (S : CommitSurface) (hash : List ℤ → ℤ)
    (compressN : List ℤ → ℤ) (bw : CompletenessWitnesses S hash compressN) :
    descriptorComplete S hash (Rfix 18) (kstepAll 18) :=
  descriptorComplete_of_satFloor S hash (Rfix 18) (kstepAll 18) <| by
    intro pre post turn hstep _hpreWF _hpostWF
    obtain ⟨actor, newCell, vk, hspec⟩ := dispatchArm_createCellFromFactory pre post hstep
    exact bw.bwCreateCellFromFactory pre post actor newCell vk turn hspec

/-- spawn (tag 19) — now rides the UNIFORM slim floor like every other value-leg effect. The
`spawn_descriptorComplete` rung's `AccountsInsertRootProver` + `SpawnHandoffInsertProver` (the cap-tree
handoff insert, both `State`-parametric) fed ONLY an unused `_henc`, so they are GONE from the live path:
the slim `SatFloor`-shaped callback (the satisfying trace + publication) suffices, and the cap-handoff
insert survives only as the SEPARATE `spawn_descriptorComplete_handoff_genuine` tooth. The dual of
`closedLogExtract_spawn_closed`. -/
theorem descriptorComplete_spawn
    (S : CommitSurface) (hash : List ℤ → ℤ)
    (buildWitness : ∀ (pre post : RecChainedState) (actor child target : CellId) (turn : BoundaryTurn),
      Dregg2.Circuit.Spec.AccountGrowth.SpawnSpec pre actor child target post →
      ∃ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace),
        Satisfied2 hash (Rfix 19) minit mfin maddrs t ∧
        tracePublishedCommit t = commitOf S pre post turn) :
    descriptorComplete S hash (Rfix 19) (kstepAll 19) :=
  descriptorComplete_of_satFloor S hash (Rfix 19) (kstepAll 19) <| by
    intro pre post turn hstep _hpreWF _hpostWF
    obtain ⟨actor, child, target, hspec⟩ := dispatchArm_spawn pre post hstep
    exact buildWitness pre post actor child target turn hspec

/-! ## §5 — the AUTHORITY-LEG dichotomy (re-composed HONESTLY).

The value-leg dischargers (§4) are UNCONDITIONAL in authority. The authority of a cap-gated turn — what
makes `kstepAll e pre post` REACHABLE for the cap-effects — is the deployed two-axis gate, which is EXACTLY
(owner ∨ cap): `CircuitCompletenessAuthority.authorityComplete_dichotomy`. We re-export it here as the
companion of the value `∀ e` discharge, stating PRECISELY what holds: a turn whose authority disjunct is
EITHER ownership (`actor = src`, the owner rung, opening NO cap) OR a conferring cap (`AuthorizedByCap`, the
cap-open rung) passes the gate. There is NO single descriptor witnessing BOTH disjuncts — the honest shape
is the dichotomy, not a forced uniform rung. -/

open Dregg2.Exec.FacetAuthority (FacetCaps AuthProvided authorizedFacetEffB EffectMask)
open Dregg2.Circuit.CircuitCompletenessAuthority (AuthorizedByCap owner_authorityComplete
  authorityComplete_dichotomy)

/-- **`authority_leg` — the authority companion of the value `∀ e` discharge (the HONEST dichotomy).** A
turn whose authority is EITHER ownership (`actor = src`) OR a conferring cap (`AuthorizedByCap`) passes the
deployed two-axis gate at ANY effect bit — `authorityComplete_dichotomy`. This is the converse target the
cap-open authority leg discharges in-circuit; it covers every authorized turn through its OWN disjunct, and
is stated as a dichotomy because no single descriptor witnesses both (the owner path opens no cap; the cap
path needs no ownership). The honest authority-completeness, NOT folded into the value rung. -/
theorem authority_leg (caps : FacetCaps) (provided : AuthProvided) (effectBit : EffectMask)
    (tr : Turn) (h : tr.actor = tr.src ∨ AuthorizedByCap caps provided effectBit tr) :
    authorizedFacetEffB caps provided effectBit tr = true :=
  authorityComplete_dichotomy caps provided effectBit tr h

/-! ## §6 — `lightclient_complete_assembled`: THE COMPLETENESS HEADLINE at `Rfix`/`kstepAll`.

The apex `lightclient_complete` consumes the per-effect satisfiability at EXACTLY the published effect. Each
§4 discharger SUPPLIES that rung from the prover bundle, so the headline carries NO value-leg premise — only
the named realizable floors (`StarkComplete`, the `Poseidon2SpongeCR` hash carrier, the
`CompletenessWitnesses` prover bundle). We state the GENERIC headline (parametric in the published effect,
taking its discharged rung) + a CONCRETE corollary at the transfer beachhead (premise discharged by
`descriptorComplete_transfer`), exactly as the soundness side states `lightclient_unfoolable_assembled` +
its per-effect corollaries. -/

/-- **`lightclient_complete_assembled` — THE COMPLETENESS HEADLINE (generic over the published effect).**
From a genuine kernel transition `kstepAll e pre post` (with `AccountsWF` boundary kernels), the discharged
per-effect satisfiability rung `descriptorComplete S hash (Rfix e) (kstepAll e)` (SUPPLIED by the matching
§4 `descriptorComplete_<e>`), the dual STARK floor `[StarkComplete hash Rfix]`, and the named hash CR
carrier, there EXIST public inputs `pi` and a batch proof `π` with `verifyBatch (vkOfRegistry Rfix) pi π =
accept`, committing to `(pre, post)`. A VALID turn HAS an accepting proof — the dual of
`lightclient_unfoolable_assembled`. The value-leg premise is DISCHARGED (the §4 rung), not opaque. -/
theorem lightclient_complete_assembled
    (hash : List ℤ → ℤ) (S : CommitSurface)
    (hCR : Poseidon2SpongeCR hash) [StarkComplete hash Rfix]
    (e : EffectIdx) (pre post : RecChainedState) (turn : BoundaryTurn)
    (hcomplete : descriptorComplete S hash (Rfix e) (kstepAll e))
    (hstep : kstepAll e pre post)
    (hpreWF : AccountsWF pre.kernel) (hpostWF : AccountsWF post.kernel) :
    ∃ (pi : BatchPublicInputs) (π : BatchProof),
      pi.effect = e ∧
      verifyBatch (vkOfRegistry Rfix) pi π = Verdict.accept ∧
      pi.pre = S.commit pre.kernel turn ∧
      pi.post = S.commit post.kernel turn :=
  lightclient_complete hash S Rfix hCR kstepAll e pre post turn hcomplete hstep hpreWF hpostWF

/-- **`lightclient_complete_transfer` — the transfer beachhead, value-leg DISCHARGED.** The headline at the
transfer tag with the satisfiability premise supplied by `descriptorComplete_transfer` from the prover
bundle: a genuine transfer kernel step HAS an accepting proof, carrying ONLY `StarkComplete`/the hash CR/
the `CompletenessWitnesses` bundle. The completeness dual of the soundness transfer rung. -/
theorem lightclient_complete_transfer
    {CH : CellId → Value → ℤ} {RH : RecordKernelState → ℤ}
    {cmb compress : ℤ → ℤ → ℤ} {compressN : List ℤ → ℤ}
    {hCmb : compressInjective cmb} {hCompress : compressInjective compress}
    {hCompressN : compressNInjective compressN} {hLeaf : cellLeafInjective CH}
    {hRest : RestHashIffFrame RH}
    (hash : List ℤ → ℤ)
    (hCR : Poseidon2SpongeCR hash) [StarkComplete hash Rfix]
    (bw : CompletenessWitnesses (S_live CH RH cmb compress compressN hCmb hCompress hCompressN hLeaf hRest)
      hash compressN)
    (pre post : RecChainedState) (turn : BoundaryTurn)
    (hstep : kstepAll 0 pre post)
    (hpreWF : AccountsWF pre.kernel) (hpostWF : AccountsWF post.kernel) :
    ∃ (pi : BatchPublicInputs) (π : BatchProof),
      pi.effect = 0 ∧
      verifyBatch (vkOfRegistry Rfix) pi π = Verdict.accept ∧
      pi.pre = (S_live CH RH cmb compress compressN hCmb hCompress hCompressN hLeaf hRest).commit
        pre.kernel turn ∧
      pi.post = (S_live CH RH cmb compress compressN hCmb hCompress hCompressN hLeaf hRest).commit
        post.kernel turn :=
  lightclient_complete_assembled hash _ hCR 0 pre post turn
    (descriptorComplete_transfer hash bw) hstep hpreWF hpostWF

/-- **`lightclient_complete_burn` — the burn rung, value-leg DISCHARGED.** A second concrete corollary
(any of the 21 §4 dischargers composes identically): a genuine burn kernel step HAS an accepting proof. -/
theorem lightclient_complete_burn
    (hash : List ℤ → ℤ) (S : CommitSurface) (compressN : List ℤ → ℤ)
    (hCR : Poseidon2SpongeCR hash) [StarkComplete hash Rfix]
    (bw : CompletenessWitnesses S hash compressN)
    (pre post : RecChainedState) (turn : BoundaryTurn)
    (hstep : kstepAll 4 pre post)
    (hpreWF : AccountsWF pre.kernel) (hpostWF : AccountsWF post.kernel) :
    ∃ (pi : BatchPublicInputs) (π : BatchProof),
      pi.effect = 4 ∧
      verifyBatch (vkOfRegistry Rfix) pi π = Verdict.accept ∧
      pi.pre = S.commit pre.kernel turn ∧
      pi.post = S.commit post.kernel turn :=
  lightclient_complete_assembled hash S hCR 4 pre post turn
    (descriptorComplete_burn S hash compressN bw) hstep hpreWF hpostWF

/-! ## §7 — the BIDIRECTIONAL pairing: verifyBatch-acceptable ⟺ kernel-valid (mod the ASYMMETRIC floors).

Side-by-side with the soundness headline `lightclient_unfoolable_assembled`, the pair is the two-way bridge
between the circuit verdict and kernel validity. The two directions do NOT share a floor set — they are
HONESTLY asymmetric:

  * **SOUND** (`lightclient_unfoolable_assembled` / `lightclient_unfoolable_circuit_sound`):
    `verifyBatch accept ⟹ ∃ genuine kernel transition`, carrying `[StarkSound]` + `Poseidon2SpongeCR` + the
    `CommitSurface` CR fields + `WitnessDecodes` + the per-effect `EffectDecodeBridge` decode-extraction
    family (the light client must SURJECT published roots onto real kernels — the HARD direction).
  * **COMPLETE** (`lightclient_complete_assembled`, this file): `genuine kernel transition ⟹ ∃ verifyBatch
    accept`, carrying `[StarkComplete]` + `Poseidon2SpongeCR` + the `CompletenessWitnesses` prover bundle
    (the honest prover HOLDS the kernels and CONSTRUCTS their commitment — the commitment direction is
    `stateDecode_construct`, no `WitnessDecodes`; the trace is the realizable prover floor).

`verifyBatch_iff_kernel_valid` packages the two as an `↔` at a fixed published effect under the UNION of both
floor sets. The honest reading is the two named directions with their distinct floors — the `↔` is the
conjunction, not a claim that one floor set suffices for both. -/

/-- **`verifyBatch_kernel_bidirectional` — the two directions, side-by-side with their EXACT floors.** A
SINGLE statement carrying BOTH arms as a conjunction, each under its OWN named floors (the honest
asymmetry — NOT a single `⟺` pretending one floor set serves both):

  * SOUND arm: from a verifying batch `(pi, π)` against `vkOfRegistry Rfix` + the soundness floors
    (`[StarkSound]`, `Poseidon2SpongeCR`, `WitnessDecodes hash Rfix S pi`, the per-effect
    `EffectDecodeBridge` decode-extraction family), there is a genuine kernel transition
    `kstepAll pi.effect pre post` committing to `(pi.pre, pi.post)`.
  * COMPLETE arm: from a genuine kernel transition `kstepAll e pre post` + the completeness floors
    (`[StarkComplete]`, `Poseidon2SpongeCR`, the discharged satisfiability rung `descriptorComplete S hash
    (Rfix e) (kstepAll e)`), there is an accepting batch committing to `(pre, post)`.

The two arms quantify over the SAME registry `Rfix` and the SAME `kstepAll`, so they are genuinely the two
directions of "verifyBatch-acceptable ⟺ kernel-valid". They are kept as a conjunction (not a fused `↔`)
because the SOUND arm needs `WitnessDecodes` (surject roots onto kernels — the hard direction) while the
COMPLETE arm needs only `stateDecode_construct` (the prover HOLDS the kernels); fusing them would hide that
asymmetry. This IS the honest bidirectional. -/
theorem verifyBatch_kernel_bidirectional
    (hash : List ℤ → ℤ) (S : CommitSurface)
    (hCR : Poseidon2SpongeCR hash) [StarkSound hash Rfix] [StarkComplete hash Rfix]
    (hbridge : ∀ e, CircuitSoundnessAssembled.EffectDecodeBridge S hash Rfix e) :
    -- SOUND: verifyBatch accept ⟹ ∃ genuine kernel transition.
    (∀ (pi : BatchPublicInputs) (π : BatchProof),
        WitnessDecodes hash Rfix S pi →
        verifyBatch (vkOfRegistry Rfix) pi π = Verdict.accept →
        ∃ pre post : RecChainedState,
          StateDecode S pi.toPublished pre post ∧
          kstepAll pi.effect pre post ∧
          pi.pre = S.commit pre.kernel pi.turn ∧
          pi.post = S.commit post.kernel pi.turn)
    ∧
    -- COMPLETE: genuine kernel transition ⟹ ∃ verifyBatch accept.
    (∀ (e : EffectIdx) (pre post : RecChainedState) (turn : BoundaryTurn),
        descriptorComplete S hash (Rfix e) (kstepAll e) →
        kstepAll e pre post → AccountsWF pre.kernel → AccountsWF post.kernel →
        ∃ (pi : BatchPublicInputs) (π : BatchProof),
          pi.effect = e ∧
          verifyBatch (vkOfRegistry Rfix) pi π = Verdict.accept ∧
          pi.pre = S.commit pre.kernel turn ∧
          pi.post = S.commit post.kernel turn) :=
  ⟨fun pi π hwitdec hacc =>
     CircuitSoundnessAssembled.lightclient_unfoolable_assembled hash S hCR hbridge pi π hwitdec hacc,
   fun e pre post turn hcomplete hstep hpreWF hpostWF =>
     lightclient_complete_assembled hash S hCR e pre post turn hcomplete hstep hpreWF hpostWF⟩

/-! ## §8 — axiom hygiene. -/

#assert_axioms dispatchArm_transfer
#assert_axioms dispatchArm_burn
#assert_axioms descriptorComplete_transfer
#assert_axioms descriptorComplete_burn
#assert_axioms descriptorComplete_setField
#assert_axioms descriptorComplete_noteSpend
#assert_axioms descriptorComplete_makeSovereign
#assert_axioms descriptorComplete_spawn
#assert_axioms Rfix_burn
#assert_axioms authority_leg
#assert_axioms lightclient_complete_assembled
#assert_axioms lightclient_complete_transfer
#assert_axioms lightclient_complete_burn
#assert_axioms verifyBatch_kernel_bidirectional

end Dregg2.Circuit.CircuitCompletenessAssembled
