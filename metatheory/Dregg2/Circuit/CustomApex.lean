/-
# Dregg2.Circuit.CustomApex — the STAGED-AIR model the Custom refutation uses (SUPERSEDED apex).

## What this module IS now

This file holds the **staged-AIR proof-binding model** for `Effect::Custom`: the satisfaction relation
(`Satisfied2Staged`) of an effect-VM AIR whose `proofBind` row gate carries the in-AIR recursion-verifier
check (`ProofBind.boundAt E env`) instead of the deployed vacuous `| .proofBind _ => True`. That staged
model is the OBJECT the refutation (`Dregg2.Circuit.CustomCarrierAttack`) operates over: §A's forged
trace exhibits a Custom row the DEPLOYED True-gate AIR admits but the STAGED AIR rejects (`boundAt`
false), proving the deployed circuit binds nothing.

## Superseded — the deleted vacuous companions

This file ONCE carried a Custom "companion apex" (`StarkSoundCustom` + `lightclient_unfoolable_custom`
/ `lightclient_unfoolable_custom_binds` / `lightclient_custom_v3_binds` + `descriptorRefinesCustom`).
`CustomCarrierAttack` then PROVED that path vacuous-as-deployed: `StarkSoundCustom`'s extraction payload
is `Satisfied2Staged`, but no uniform bridge `Satisfied2 ⇒ Satisfied2Staged` exists over the deployed
True-gate AIR (the forged trace is the counterexample), so the binding those theorems claimed was carried
ENTIRELY by the `StarkSoundCustom` hypothesis, ungrounded against the deployed VK. The main apex carves
`Effect::Custom` OUT (`RotatedKernelRefinementExercise.no_customA_arm`), so nothing consumed the
companions.

The REAL, deployed-grounded guarantee was rebuilt in `Dregg2.Circuit.CustomBindingFromFold`
(`custom_binding_from_fold` / `custom_companion_grounded`): a verifying per-turn aggregate forces the
effect-vm leg's published custom-commitment PI to be backed by a verifying sub-proof with a uniquely
determined VK, resting only on the floor `{FRI via AggAirSound.FriExtract + Poseidon2SpongeCR + the
connect}` — `StarkSoundCustom` GONE, `EngineBinding` derived internally. The vacuous companions were
RETIRED; this file keeps ONLY the staged-AIR model the refutation depends on.

## Axiom hygiene
`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. The kept defs (`holdsAtStaged`,
`Satisfied2Staged`, `satisfied2Staged_toCustom`, `holdsAtStaged_imp_holdsAt`) introduce no axioms; all
imports read-only.
-/
import Dregg2.Circuit.CircuitSoundness

namespace Dregg2.Circuit.CustomApex

open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.EffectVmEmit (VmRowEnv siteHoldsAll)
open Dregg2.Crypto
open Dregg2.Circuit.CircuitSoundness
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Exec (RecChainedState)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## §1 — the STAGED in-AIR proof-binding verifier (beside the deployed vacuous `proofBind`). -/

/-- **The staged per-row constraint semantics.** Identical to `DescriptorIR2.VmConstraint2.holdsAt`
EXCEPT the `proofBind` op: where the DEPLOYED gate is the vacuous `True`, the STAGED gate is the
in-AIR recursion-verifier check `ProofBind.boundAt E env` — the row's `(commit, vk)` columns commit to
a VERIFYING sub-proof of engine `E`. This is the Lean twin of laying `verify_p3_batch_proof_circuit`
through the Custom row's `custom_proof_commitment` / `custom_program_vk_hash` columns. Every other arm
delegates VERBATIM to the deployed `holdsAt` (defeq per constructor — the staged semantics changes the
`proofBind` gate ALONE). -/
def VmConstraint2.holdsAtStaged (E : ProofEngine) (hash : List ℤ → ℤ) (tf : TraceFamily)
    (env : VmRowEnv) (isFirst isLast : Bool) : VmConstraint2 → Prop
  | .proofBind m  => ProofBind.boundAt E env m
  | .base c       => VmConstraint2.holdsAt hash tf env isFirst isLast (.base c)
  | .lookup l     => VmConstraint2.holdsAt hash tf env isFirst isLast (.lookup l)
  | .memOp x      => VmConstraint2.holdsAt hash tf env isFirst isLast (.memOp x)
  | .mapOp m      => VmConstraint2.holdsAt hash tf env isFirst isLast (.mapOp m)
  | .umemOp x     => VmConstraint2.holdsAt hash tf env isFirst isLast (.umemOp x)
  | .windowGate w => VmConstraint2.holdsAt hash tf env isFirst isLast (.windowGate w)

/-- The staged gate is STRONGER than the deployed gate: a constraint holding under the staged AIR holds
under the deployed AIR (the deployed `proofBind` gate is `True`; every other arm is identical). So a
staged witness satisfies the DEPLOYED denotation too — the staging only ADDS the binding leg. -/
theorem holdsAtStaged_imp_holdsAt (E : ProofEngine) (hash : List ℤ → ℤ) (tf : TraceFamily)
    (env : VmRowEnv) (isFirst isLast : Bool) (c : VmConstraint2)
    (h : VmConstraint2.holdsAtStaged E hash tf env isFirst isLast c) :
    c.holdsAt hash tf env isFirst isLast := by
  cases c with
  | proofBind m => trivial
  | base c => exact h
  | lookup l => exact h
  | memOp x => exact h
  | mapOp m => exact h
  | umemOp x => exact h
  | windowGate w => exact h

/-- `m ∈ proofBindsOf d` ⟹ the constraint `.proofBind m` is one of `d`'s declared constraints. -/
theorem proofBind_mem_constraints {d : EffectVmDescriptor2} {m : ProofBind}
    (hm : m ∈ proofBindsOf d) : VmConstraint2.proofBind m ∈ d.constraints := by
  unfold proofBindsOf at hm
  rw [List.mem_filterMap] at hm
  obtain ⟨c, hc, hcm⟩ := hm
  cases c <;> simp_all

/-- **`Satisfied2Staged` — the staged-AIR denotation.** `Satisfied2` with the `proofBind` row gate
upgraded to the in-AIR verifier check (`holdsAtStaged`). Every other leg is the deployed `Satisfied2`
verbatim. This is the satisfaction relation of the STAGED effect-VM AIR — built and reasoned about
here, NOT deployed (deployed `Satisfied2` keeps the vacuous `proofBind` gate). It is the model the
refutation `CustomCarrierAttack` runs its forged trace against. -/
structure Satisfied2Staged (hash : List ℤ → ℤ) (E : ProofEngine) (d : EffectVmDescriptor2)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace) : Prop where
  /-- every constraint holds on every row window under the STAGED gate (`holdsAtStaged`). -/
  rowConstraints : ∀ i < t.rows.length, ∀ c ∈ d.constraints,
    VmConstraint2.holdsAtStaged E hash t.tf (envAt t i) (i == 0) (i + 1 == t.rows.length) c
  rowHashes : ∀ i < t.rows.length, siteHoldsAll hash (envAt t i) d.hashSites
  rowRanges : ∀ i < t.rows.length, ∀ r ∈ d.ranges, r.holds (envAt t i)
  memAddrsNodup : maddrs.Nodup
  memClosed : ∀ op ∈ memLog d t, op.addr ∈ maddrs
  memDisciplined : MemoryChecking.Disciplined (memLog d t)
  memBalanced : MemoryChecking.MemCheck minit mfin maddrs (memLog d t)
  memTableFaithful : t.tf .memory = (memLog d t).map opRow
  mapTableFaithful : t.tf .mapOps = mapLog d t

/-- **THE STAGED-VERIFIER KEYSTONE — `satisfied2Staged_toCustom`.** A witness of the STAGED AIR IS a
`Satisfied2Custom` witness: the in-AIR `proofBind` gate PRODUCES the §6c binding leg (`proofBound`),
and the staged constraints imply the deployed `Satisfied2` (`holdsAtStaged_imp_holdsAt`, the deployed
`proofBind` gate being weaker). So the binding rests FORCED BY THE STAGED CIRCUIT, not assumed
externally. (This keystone fed the now-retired companion apex; it stands as the staged model's
content and as the precise object `CustomCarrierAttack` shows is ungrounded over the deployed AIR.) -/
theorem satisfied2Staged_toCustom (hash : List ℤ → ℤ) (E : ProofEngine) (d : EffectVmDescriptor2)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (h : Satisfied2Staged hash E d minit mfin maddrs t) :
    Satisfied2Custom hash E d minit mfin maddrs t where
  toSatisfied2 :=
    { rowConstraints := fun i hi c hc =>
        holdsAtStaged_imp_holdsAt E hash t.tf (envAt t i) (i == 0) (i + 1 == t.rows.length) c
          (h.rowConstraints i hi c hc)
      rowHashes := h.rowHashes
      rowRanges := h.rowRanges
      memAddrsNodup := h.memAddrsNodup
      memClosed := h.memClosed
      memDisciplined := h.memDisciplined
      memBalanced := h.memBalanced
      memTableFaithful := h.memTableFaithful
      mapTableFaithful := h.mapTableFaithful }
  proofBound := fun i hi m hm =>
    h.rowConstraints i hi (.proofBind m) (proofBind_mem_constraints hm)

#assert_axioms holdsAtStaged_imp_holdsAt
#assert_axioms satisfied2Staged_toCustom

end Dregg2.Circuit.CustomApex
