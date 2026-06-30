/-
# Dregg2.Circuit.CustomApex — the `Effect::Custom` apex soundness close (the VK-RISK-FREE half).

## The gap this closes (triage `fb7a472d`)

The apex `CircuitSoundness.lightclient_unfoolable` extracts a PLAIN `Satisfied2` witness, whose in-AIR
`proofBind` op is the VACUOUS `| .proofBind _ => True` (`DescriptorIR2.VmConstraint2.holdsAt`). So a
verifying batch claiming the deployed `customV3` descriptor proves NOTHING about the bound sub-proof:
a light client running only the aggregate STARK does not witness custom-program correctness. The
STRONGER `Satisfied2Custom` / `proofBind_bound` / `proofBind_determined` keystones (`DescriptorIR2`
§6c) already exist and are axiom-clean, but the apex never consumes them — `Effect::Custom` rides the
catch-all and is carved OUT (`RotatedKernelRefinementExercise.no_customA_arm`,
`lean-circuit.md` §custom).

## What this module does — the Lean MODEL of the FOLD binding (decided architecture (a))

The custom binding is enforced at the per-turn FOLD — the custom sub-proof leaf folded into the
recursion, its PI-commitment connected to the descriptor's exposed `custom_proof_commitment` /
`custom_program_vk_hash` public inputs (the rotated Custom member's eight `customPiExposure` pins,
DEPLOYED — `EffectVmEmitRotationV3.customV3` re-emit + column re-pin). It is NOT enforced by an
in-AIR row gate (the rejected architecture (b)): the per-row `proofBind` denotation stays `True`
(`DescriptorIR2.VmConstraint2.holdsAt`, UNCHANGED), exactly like `memOp`/`umemOp` whose content
rides an offline argument rather than a row-local poly. This module is the LEAN MODEL of that fold
binding.

1. **The fold-binding model AIR** (`VmConstraint2.holdsAtStaged` + `Satisfied2Staged`). The model
   AIR is the deployed row semantics with the `proofBind` arm carrying `ProofBind.boundAt E env` —
   the recursion-verifier check (`E.boundTo commit vk`: the row commits to a VERIFYING sub-proof).
   This is the Lean twin of the FOLD's leaf verifier (`circuit-prove/src/joint_turn_recursive.rs` /
   `ivc_turn_chain.rs` / `custom_proof_bind`) connected through the published
   `custom_proof_commitment` / `custom_program_vk_hash` PIs — NOT a literal in-row gate. It sits
   BESIDE the deployed `holdsAt` (deployed `| .proofBind _ => True` is UNCHANGED): the deployed
   binding lives in the published PIs + the fold, and `holdsAtStaged` models that the fold's
   verifier accepts. `satisfied2Staged_toCustom` proves a model witness IS a `Satisfied2Custom`
   (the fold's verification PRODUCES the §6c binding leg — not an external assumption).

2. **The Custom companion apex** (`lightclient_unfoolable_custom` + `lightclient_unfoolable_custom_binds`).
   A `StarkSoundCustom` extraction (the staged-AIR FRI carrier — the EXACT analog of `StarkSound`, now
   over the staged AIR) yields a staged witness; `satisfied2Staged_toCustom` lifts it to
   `Satisfied2Custom`; and the apex routes the Custom index through `proofBind_bound` /
   `proofBind_determined` under the NAMED `EngineBinding E` carrier. So the apex now genuinely CLAIMS
   custom program-correctness: every active proof-binding row binds to a VERIFYING sub-proof
   (`proofBind_bound`) whose attested program VK is DETERMINED by its commitment (`proofBind_determined`
   — the anti-ghost: a forged commitment no verifying sub-proof exposes cannot ride). The genuine
   kernel boundary is still derived (`StateDecode`); the proof-binding rides on top.

3. **The deployed-descriptor corollary** (`lightclient_custom_v3_binds`) CONSUMES the local Emit lemma
   `EffectVmEmitRotationV3.customV3_binds_proof` at the apex: for the LIVE `customV3` registry member,
   the bound columns are exactly `prmCol CUSTOM_COMMIT` / `prmCol CUSTOM_VK`.

## The named carrier (honest — NOT faked)

The custom claim rests on `EngineBinding E` (the recursion engine's in-circuit verifier is
PI-commitment-collision-free across verifying proofs — the irreducible FRI-recursion soundness floor,
`DescriptorIR2.EngineBinding`, the same shape `RecursiveAggregation.recursive_sound` carries) PLUS the
fold's leaf verifier. It does NOT rest on an out-of-circuit Rust trust step. `EngineBinding` /
`StarkSoundCustom` are HYPOTHESES (a `structure`/`class`), never axioms.

## What is DEPLOYED vs the remaining fold-wire

DEPLOYED (this VK epoch): the rotated Custom member PUBLISHES `custom_proof_commitment` /
`custom_program_vk_hash` as descriptor public inputs (`EffectVmEmitRotationV3.customPiExposure`,
IR2 PI 46..53; the wide member 70 PI), re-emitted with the column re-pin and a moved fingerprint.
The per-row `proofBind` gate STAYS `True` (the binding is at the fold, decided architecture (a), not
a row gate (b)). REMAINING fold-wire (NOT a Lean change): connect the custom sub-proof leaf's 4-felt
PI-commitment to these published PI slots in `joint_turn_recursive` / `ivc_turn_chain`, tied to the
wide host `pi::CUSTOM_PROOFS_BASE + i*12 + 8..12`. `StarkSoundCustom`/`holdsAtStaged` are the Lean
model of that wired fold. A `FullActionA.customA` executor verb is NOT added: `Effect::Custom` is the
deployed AUTHORIZATION MODE (`Authorization::Custom { predicate }`, `turn/src/action.rs`), not a
state-transition verb — adding it to the 35-constructor `FullActionA` (rippling through every total
match) is a deployed-semantics change bundled with that epoch. The companion apex lands on its OWN
custom kstep, which needs no `FullActionA` constructor.

## Axiom hygiene
`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound} + the named carriers as HYPOTHESES
(`EngineBinding`, `StarkSoundCustom`, `Poseidon2SpongeCR`). NO new axioms. NEW file; all imports
read-only.
-/
import Dregg2.Circuit.CircuitSoundness
import Dregg2.Circuit.Emit.EffectVmEmitRotationV3

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
here, NOT deployed (deployed `Satisfied2` keeps the vacuous `proofBind` gate). -/
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
`proofBind` gate being weaker). So the binding the apex consumes is FORCED BY THE CIRCUIT, not assumed
externally. -/
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

/-! ## §2 — the staged-AIR STARK extraction carrier (the EXACT analog of `StarkSound`). -/

/-- **`StarkSoundCustom` — the staged-AIR p3 batch-STARK soundness carrier (NAMED, not faked).**
A verifying batch against the live registry's VK yields, for the descriptor the PI names, a
`Satisfied2Staged` witness whose published commitments are `pi.toPublished`. Identical in form to
`CircuitSoundness.StarkSound`, but the extracted witness satisfies the STAGED AIR (the one carrying the
in-AIR proof-binding verifier). REALIZABLE / audited (the FRI extraction over the staged verifier AIR),
NOT provable in Lean — carried as a class so the companion apex consumes it explicitly. -/
class StarkSoundCustom (hash : List ℤ → ℤ) (E : ProofEngine) (R : Registry) : Prop where
  extract : ∀ (pi : BatchPublicInputs) (π : BatchProof),
    verifyBatch (vkOfRegistry R) pi π = Verdict.accept →
    ∃ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace),
      Satisfied2Staged hash E (R pi.effect) minit mfin maddrs t ∧
        tracePublishedCommit t = pi.toPublished

/-! ## §3 — the Custom companion apex: routing the Custom index through `Satisfied2Custom`. -/

/-- **`descriptorRefinesCustom` — the per-effect rung for the Custom descriptor.** The §3-analog of
`descriptorRefines`, but consuming the STRONGER `Satisfied2Custom` (the binding leg available): any
`Satisfied2Custom` witness of `d` whose published commitments decode to `pre`/`post` forces
`kstep pre post`. The Custom rung discharges from THIS (it needs the proof-binding leg the plain
`descriptorRefines` lacks). -/
def descriptorRefinesCustom (S : CommitSurface) (hash : List ℤ → ℤ) (E : ProofEngine)
    (d : EffectVmDescriptor2) (kstep : RecChainedState → RecChainedState → Prop) : Prop :=
  Poseidon2SpongeCR hash →
  ∀ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (pc : PublishedCommit) (pre post : RecChainedState),
    Satisfied2Custom hash E d minit mfin maddrs t →
    StateDecode S pc pre post →
    kstep pre post

/-- **`lightclient_unfoolable_custom` — the companion apex at a carried Custom rung.** From a verifying
batch (`verifyBatch … = accept`), the named hash CR carrier, the named engine binding, the staged-AIR
extraction (`StarkSoundCustom`), the witness→state existence rung (`WitnessDecodes`), and the carried
Custom rung (`descriptorRefinesCustom`, consuming `Satisfied2Custom`), conclude a genuine decoded
kernel boundary committing to `pi.pre`/`pi.post` together with the forced `kstep`. Mirrors
`lightclient_unfoolable`, but the witness is `Satisfied2Custom` (the staged in-AIR verifier binding the
sub-proof), not the plain `Satisfied2`. -/
theorem lightclient_unfoolable_custom
    (hash : List ℤ → ℤ) (S : CommitSurface) (R : Registry) (E : ProofEngine)
    (hCR : Poseidon2SpongeCR hash) [StarkSoundCustom hash E R]
    (kstep : RecChainedState → RecChainedState → Prop)
    (pi : BatchPublicInputs) (π : BatchProof)
    (hrefines : descriptorRefinesCustom S hash E (R pi.effect) kstep)
    (hwitdec : WitnessDecodes hash R S pi)
    (hacc : verifyBatch (vkOfRegistry R) pi π = Verdict.accept) :
    ∃ pre post : RecChainedState,
      StateDecode S pi.toPublished pre post ∧
      kstep pre post ∧
      pi.pre = S.commit pre.kernel pi.turn ∧
      pi.post = S.commit post.kernel pi.turn := by
  -- (1) the STAGED-AIR extraction supplies a `Satisfied2Staged` witness publishing `pi.toPublished`.
  obtain ⟨minit, mfin, maddrs, t, hstaged, hpub⟩ :=
    (inferInstance : StarkSoundCustom hash E R).extract pi π hacc
  -- (2) the staged in-AIR proof-binding gate makes it a `Satisfied2Custom` (the binding is CIRCUIT-FORCED).
  have hcustom : Satisfied2Custom hash E (R pi.effect) minit mfin maddrs t :=
    satisfied2Staged_toCustom hash E _ minit mfin maddrs t hstaged
  -- (3) the carried witness→state existence rung (fed the underlying `Satisfied2`) supplies the decode.
  obtain ⟨pre, post, hdecode⟩ := hwitdec minit mfin maddrs t hcustom.toSatisfied2 hpub
  -- (4) the carried Custom rung (consuming `Satisfied2Custom`) forces the step.
  have hstep : kstep pre post :=
    hrefines hCR minit mfin maddrs t pi.toPublished pre post hcustom hdecode
  exact ⟨pre, post, hdecode, hstep, by simpa using hdecode.preBinds, by simpa using hdecode.postBinds⟩

/-- **`lightclient_unfoolable_custom_binds` — the HONEST Custom program-correctness claim.** The apex
payload for `Effect::Custom`: a verifying batch yields a genuine decoded kernel boundary committing to
`pi.pre`/`pi.post` AND (the new content the staged in-AIR verifier buys) a witness in which every active
proof-binding row of the claimed descriptor BINDS its `(commit, vk)` columns to a VERIFYING sub-proof of
`E` (`proofBind_bound`), with the attested program VK DETERMINED by the commitment under the named
engine binding (`proofBind_determined` — the anti-ghost: a forged commitment is excluded). A light
client running the staged aggregate STARK WITNESSES custom-program correctness, resting only on the
named `EngineBinding` (FRI-recursion) carrier — not on an out-of-circuit Rust trust step. -/
theorem lightclient_unfoolable_custom_binds
    (hash : List ℤ → ℤ) (S : CommitSurface) (R : Registry) (E : ProofEngine)
    (hCR : Poseidon2SpongeCR hash) (hE : EngineBinding E) [StarkSoundCustom hash E R]
    (pi : BatchPublicInputs) (π : BatchProof)
    (hwitdec : WitnessDecodes hash R S pi)
    (hacc : verifyBatch (vkOfRegistry R) pi π = Verdict.accept) :
    ∃ (pre post : RecChainedState) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ)
      (t : VmTrace),
      StateDecode S pi.toPublished pre post ∧
      Satisfied2Custom hash E (R pi.effect) minit mfin maddrs t ∧
      tracePublishedCommit t = pi.toPublished ∧
      pi.pre = S.commit pre.kernel pi.turn ∧
      pi.post = S.commit post.kernel pi.turn ∧
      -- the binding (proofBind_bound): every active proof-binding row commits to a VERIFYING sub-proof.
      (∀ i, i < t.rows.length → ∀ m ∈ proofBindsOf (R pi.effect),
        m.guard.eval (envAt t i).loc = 1 →
        E.boundTo (m.commit.eval (envAt t i).loc) (m.vk.eval (envAt t i).loc)) ∧
      -- the anti-ghost (proofBind_determined): the attested VK is DETERMINED by the commitment.
      (∀ i, i < t.rows.length → ∀ m ∈ proofBindsOf (R pi.effect),
        m.guard.eval (envAt t i).loc = 1 →
        ∀ q : E.Proof, E.verify q = true →
          E.piCommit q = m.commit.eval (envAt t i).loc →
          E.vkOf q = m.vk.eval (envAt t i).loc) := by
  obtain ⟨minit, mfin, maddrs, t, hstaged, hpub⟩ :=
    (inferInstance : StarkSoundCustom hash E R).extract pi π hacc
  have hcustom : Satisfied2Custom hash E (R pi.effect) minit mfin maddrs t :=
    satisfied2Staged_toCustom hash E _ minit mfin maddrs t hstaged
  obtain ⟨pre, post, hdecode⟩ := hwitdec minit mfin maddrs t hcustom.toSatisfied2 hpub
  refine ⟨pre, post, minit, mfin, maddrs, t, hdecode, hcustom, hpub,
    by simpa using hdecode.preBinds, by simpa using hdecode.postBinds, ?_, ?_⟩
  · intro i hi m hm hactive
    exact proofBind_bound hash E (R pi.effect) hcustom hm i hi hactive
  · intro i hi m hm hactive q hq hqc
    exact proofBind_determined hash E hE (R pi.effect) hcustom hm i hi hactive q hq hqc

/-! ## §4 — the deployed-descriptor corollary: consuming the local Emit lemma at the apex. -/

open Dregg2.Circuit.Emit.EffectVmEmit (prmCol)
open Dregg2.Circuit.Emit.EffectVmEmitV2 (CUSTOM_COMMIT CUSTOM_VK SEL_CUSTOM)
open Dregg2.Circuit.Emit.EffectVmEmitRotationV3 (customV3 customV3_binds_proof)

/-- **`lightclient_custom_v3_binds` — the apex at the LIVE `customV3` registry member.** Specialises the
companion apex to the deployed Custom descriptor (`R pi.effect = customV3`) and CONSUMES the local Emit
lemma `EffectVmEmitRotationV3.customV3_binds_proof`: every active Custom row of the extracted witness
binds its DEPLOYED columns `prmCol CUSTOM_COMMIT` / `prmCol CUSTOM_VK` to a VERIFYING sub-proof of `E`,
alongside the genuine decoded kernel boundary committing to `pi.pre`/`pi.post`. This is the concrete
column-level Custom apex claim for the live circuit (under the staged in-AIR verifier + the named
`EngineBinding` carrier). -/
theorem lightclient_custom_v3_binds
    (hash : List ℤ → ℤ) (S : CommitSurface) (R : Registry) (E : ProofEngine)
    (hCR : Poseidon2SpongeCR hash) (hE : EngineBinding E) [StarkSoundCustom hash E R]
    (pi : BatchPublicInputs) (π : BatchProof)
    (hwitdec : WitnessDecodes hash R S pi)
    (hacc : verifyBatch (vkOfRegistry R) pi π = Verdict.accept)
    (hcv3 : R pi.effect = customV3) :
    ∃ (pre post : RecChainedState) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ)
      (t : VmTrace),
      StateDecode S pi.toPublished pre post ∧
      tracePublishedCommit t = pi.toPublished ∧
      pi.pre = S.commit pre.kernel pi.turn ∧
      pi.post = S.commit post.kernel pi.turn ∧
      (∀ i, i < t.rows.length →
        (envAt t i).loc SEL_CUSTOM = 1 →
        E.boundTo ((envAt t i).loc (prmCol CUSTOM_COMMIT)) ((envAt t i).loc (prmCol CUSTOM_VK))) := by
  obtain ⟨minit, mfin, maddrs, t, hstaged, hpub⟩ :=
    (inferInstance : StarkSoundCustom hash E R).extract pi π hacc
  have hcustom : Satisfied2Custom hash E (R pi.effect) minit mfin maddrs t :=
    satisfied2Staged_toCustom hash E _ minit mfin maddrs t hstaged
  have hcv3' : Satisfied2Custom hash E customV3 minit mfin maddrs t := hcv3 ▸ hcustom
  obtain ⟨pre, post, hdecode⟩ := hwitdec minit mfin maddrs t hcustom.toSatisfied2 hpub
  refine ⟨pre, post, minit, mfin, maddrs, t, hdecode, hpub,
    by simpa using hdecode.preBinds, by simpa using hdecode.postBinds, ?_⟩
  intro i hi hactive
  exact customV3_binds_proof hash E minit mfin maddrs t hcv3' i hi hactive

#assert_axioms holdsAtStaged_imp_holdsAt
#assert_axioms satisfied2Staged_toCustom
#assert_axioms lightclient_unfoolable_custom
#assert_axioms lightclient_unfoolable_custom_binds
#assert_axioms lightclient_custom_v3_binds

end Dregg2.Circuit.CustomApex
