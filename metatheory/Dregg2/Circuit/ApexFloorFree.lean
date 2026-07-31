/-
# `Dregg2.Circuit.ApexFloorFree` — the light-client apex WITHOUT the refuted floor and WITHOUT the
uninhabited surface bundle.

⚑ SITE 3 of the light-client soundness-weld de-vacuuming (2026-07-31), the one `4ef5fb288` named as
"the mechanical per-effect remainder" and left open:

> "The apex `lightclient_unfoolable_closed_final` still routes through the refuted floor via
>  `descriptorRefines`."

It does — and the measurement that made that residual look expensive was WRONG in one direction and
INCOMPLETE in the other. Both corrections are in this file.

## Correction 1 — on the apex path the `Poseidon2SpongeCR` antecedent is VESTIGIAL

`CircuitSoundness.descriptorRefines` hides the floor in its DEF BODY:

    def descriptorRefines … : Prop := Poseidon2SpongeCR hash → ∀ …, Satisfied2 … → StateDecode … → kstep …

`ClosedLogExtractPortCheck` recorded (correctly, for the tree at large) that this antecedent "is NOT
dead the way these two were … the rungs are discharged by TERM APPLICATION, not by `intro`". That is
false of the APEX's own construction path, and the evidence was already in the tree in plain sight:
`ClosureAll.effectDecodeBridge_of_closedLogExtract` — the ONLY producer the closed apex chain uses —
opens with

    intro _hCR minit mfin maddrs t pc pre post hsat hdec

and never mentions `_hCR` again, because `ClosedLogExtract` was itself ported off the floor on
2026-07-25. So `hCR` enters `lightclient_unfoolable`, is handed to `hrefines pi.effect`, and is
DISCARDED. Nothing in the closed apex chain reads it.

## Correction 2 — shedding that floor does NOT de-vacuum the apex, and this is the bigger wound

`descriptorRefines`, `StateDecode`, `WitnessDecodes` and every apex over them are stated at
`S : CommitSurface`, and `CommitSurface` carries FIVE commitment floors as FIELDS
(`cmbInj`/`compInj`/`compNInj`/`leafInj`/`restFrame`). `Verify.ApexPremiseVacuity` proves that bundle
UNSATISFIABLE at EVERY parameter — not at deployed BabyBear, at every width — because
`RestFrameCardinalityFloor.restHashIffFrame_false_by_cardinality` kills `restFrame` for every
`RH : RecordKernelState → ℤ` by Cantor (`bal : CellId → AssetId → ℤ` is a function space, `ℤ` is
countable). **`CommitSurface` HAS NO INHABITANT**, so an apex quantified over one is vacuous whether or
not it also carries `Poseidon2SpongeCR`.

⚑ That is why the repair here is not "delete a binder". A theorem stated at `(S : CommitSurface)` cannot
be given a refutability pole AT ALL: `(S : CommitSurface) → ¬ P S` is true for free. The `False`-`kstep`
acceptance test that `DescriptorRefinesShirkRefuted` set for any candidate re-grounding of
`descriptorRefines` is therefore UNSTATEABLE at `CommitSurface`, and the only way to pass it is to stop
quantifying over the bundle.

The apex never needed it. `lightclient_unfoolable`'s derivation touches `S` at exactly one place —
`S.commit`, inside `StateDecode`'s two equations. `CommitSurface.commit_binds`, the field the five
floors exist to justify, is NEVER invoked by any apex in the chain (its consumers are
`stateDecode_pre_faithful`/`stateDecode_post_faithful`, separate theorems that stay refuted). So this
file restates the apex over a BARE COMMIT MAP,

    abbrev CommitMap := RecordKernelState → Turn → ℤ

which every function inhabits, deployed `recStateCommit` included.

## Correction 3 — the publication link the old rung THREW AWAY

`descriptorRefines` quantifies over a `pc : PublishedCommit` with NO relation to the trace `t`. The apex
HAS the relation — `StarkSound.extract` hands back `tracePublishedCommit t = pi.toPublished` — and drops
it when it applies the rung. That makes the carried obligation strictly harder than anything the apex
can use (it must hold at boundaries the witnessed trace never published). `descriptorRefinesFree`
carries the link, so the rung asks exactly what the apex supplies — a weaker hypothesis, hence a
stronger apex.

## What the resulting apex CLAIMS, and what it NO LONGER CLAIMS

`lightclient_unfoolable_free`: an accepting batch + `StarkSound` + the witness-existence rung + the
published-effect refinement rung ⟹ there EXIST kernel endpoints, a genuine `kstep pi.effect pre post`
between them, and `pi.pre`/`pi.post` ARE `C` of those endpoints.

⚠ It does NOT claim those endpoints are UNIQUE. Uniqueness is `stateDecode_pre_faithful` /
`stateDecode_post_faithful`, the only consumers of `CommitSurface.commit_binds`, and they genuinely need
the commitment to BIND — the five refuted floors. So the split this file lands is:

  * **EXISTENCE of a real transition behind an accepted proof — floor-free, surface-free, TRUE.**
  * **UNIQUENESS of the state behind a published root — still refuted** (`ApexPremiseVacuity`), and
    unavailable until the rest-hash is refined to finite support
    (`Verify.RestFrameFiniteSupportSuccessor`).

Nothing that stood on the old apex falls, and the demonstration is IN SITU rather than a fresh
theorem here (see §4 for why a fresh one is impossible): `ClosureAll.lightclient_unfoolable_closed`,
`ClosureFinal.lightclient_unfoolable_one` / `…_circuit_sound`,
`ClosureFinalAvail.lightclient_unfoolable_closed_final_avail` and
`KernelConfigSoundness.kernelConfigSound{,Avail}` keep their conclusions verbatim, lose the
`Poseidon2SpongeCR` binder, and are now proved THROUGH `lightclient_unfoolable_free`.

## Anti-vacuity — both poles, and the test the tree already set

  * REFUTABLE: `descriptorRefinesFree_false_at_False_kstep` — at an EXHIBITED commit map, for EVERY hash
    and EVERY descriptor (the deployed `Rfix e` included), `descriptorRefinesFree C hash d
    (fun _ _ => False)` is FALSE. That is exactly
    `DescriptorRefinesShirkRefuted.both_hold_at_False_kstep`'s acceptance test, which `descriptorRefines`
    and `descriptorRefinesR` BOTH FAIL (each holds at the `False` step relation at every deployed-shaped
    sponge, for free, discharged by the parameters rather than by the circuit).
  * REFUTABLE (the other rung): `witnessDecodesC_false_at_offsetMap` — the existence rung is FALSE at a
    commit map that misses the published OLD root by one, on the boundary the empty trace actually
    publishes. Both carried rungs can fail; neither is the constant `True`.
  * SATISFIABLE: `descriptorRefinesFree_trivial` and `witnessDecodesC_genuine` — the apex's carried rungs
    are inhabited at a concrete commit map, so the implication is not "unsatisfiable ⟹ anything".
  * CONTINGENT CONCLUSION: `apex_conclusion_false_at_False_kstep`.

No `sorry`, no `axiom`, no `native_decide`; `#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}.
NEW file; imports read-only.
-/
import Dregg2.Circuit.CircuitSoundness

namespace Dregg2.Circuit.ApexFloorFree

open Dregg2.Circuit.CircuitSoundness
  (PublishedCommit StarkSound Registry EffectIdx BatchPublicInputs BatchProof Verdict verifyBatch
   vkOfRegistry tracePublishedCommit)
open Dregg2.Circuit.DescriptorIR2 (EffectVmDescriptor2 VmTrace Satisfied2 memLog mapLog)
open Dregg2.Circuit.StateCommit (AccountsWF)
open Dregg2.Crypto
open Dregg2.Exec (RecChainedState RecordKernelState Turn)

set_option autoImplicit false

/-! ## §1 — `CommitMap`: everything the apex ever reads out of a `CommitSurface`.

`CommitSurface` bundles five commitment primitives and five collision-resistance FIELDS. The apex chain
uses ONE projection of it, `S.commit`, and never the CR fields; the fields exist for
`CommitSurface.commit_binds`, which no apex calls. `CommitMap` is that projection's type, and unlike the
bundle it is INHABITED — which is the whole difference between a statement that can be refuted and one
that cannot. -/

/-- **The commitment map** — a full-kernel state commitment at a boundary turn. The deployed instance is
`StateCommit.recStateCommit CH RH cmb compress compressN`; ANY function inhabits it, which is exactly
what `CommitSurface` cannot say of itself. -/
abbrev CommitMap := RecordKernelState → Turn → ℤ

/-- **`StateDecodeC C pc pre post` — `CircuitSoundness.StateDecode` over a bare commit map.** Field for
field identical; the only change is that the commitment comes from a FUNCTION rather than from a bundle
whose CR fields are jointly unsatisfiable. Nothing at all is assumed about `C`. -/
structure StateDecodeC (C : CommitMap) (pc : PublishedCommit)
    (pre post : RecChainedState) : Prop where
  /-- the published OLD commitment IS `C` of `pre.kernel` at the boundary turn. -/
  preBinds  : pc.pubPre = C pre.kernel pc.turn
  /-- the published NEW commitment IS `C` of `post.kernel` at the boundary turn. -/
  postBinds : pc.pubPost = C post.kernel pc.turn
  /-- `pre`'s kernel is structurally well-formed (PROVED preserved by the executor,
      `StateCommit.recKExec_preserves_AccountsWF` — not a crypto assumption). -/
  preWF     : AccountsWF pre.kernel
  /-- `post`'s kernel is structurally well-formed. -/
  postWF    : AccountsWF post.kernel

/-! ## §2 — the per-effect rung, FLOOR-FREE, SURFACE-FREE, publication link RESTORED. -/

/-- **`descriptorRefinesFree C hash d kstep` — the per-effect refinement obligation, honestly stated.**

Three differences from `CircuitSoundness.descriptorRefines`:

  1. the `Poseidon2SpongeCR hash →` antecedent is GONE. It is refuted at deployed BabyBear
     (`HashFloorHonesty.poseidon2SpongeCR_false_babyBear`), so its presence made the obligation free
     for the parameters to discharge; and on the closed apex path it was never read
     (`effectDecodeBridge_of_closedLogExtract` introduces and drops it).
  2. `S : CommitSurface` is replaced by `C : CommitMap`. The bundle has NO inhabitant at any parameter
     (`ApexPremiseVacuity.apexCommitFloor_unsatisfiable`); the map has many.
  3. the PUBLICATION LINK `tracePublishedCommit t = pc` is CARRIED. The apex holds this fact from
     `StarkSound.extract` and used to throw it away; restoring it weakens the obligation to exactly
     what the apex supplies. -/
def descriptorRefinesFree (C : CommitMap) (hash : List ℤ → ℤ)
    (d : EffectVmDescriptor2) (kstep : RecChainedState → RecChainedState → Prop) : Prop :=
  ∀ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (pc : PublishedCommit) (pre post : RecChainedState),
    Satisfied2 hash d minit mfin maddrs t →
    tracePublishedCommit t = pc →
    StateDecodeC C pc pre post →
    kstep pre post

/-- **`WitnessDecodesC hash R C pi` — the witness→kernel-state existence rung over a bare commit map.**
`CircuitSoundness.WitnessDecodes` verbatim, with `S : CommitSurface` replaced by `C : CommitMap`. -/
def WitnessDecodesC (hash : List ℤ → ℤ) (R : Registry) (C : CommitMap)
    (pi : BatchPublicInputs) : Prop :=
  ∀ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace),
    Satisfied2 hash (R pi.effect) minit mfin maddrs t →
    tracePublishedCommit t = pi.toPublished →
    ∃ pre post : RecChainedState, StateDecodeC C pi.toPublished pre post

/-! ## §3 — ★ THE APEX, FLOOR-FREE AND SURFACE-FREE. -/

/-- **`lightclient_unfoolable_free` — single-transition light-client soundness carrying NO refuted
hypothesis.**

From an accepting batch against `vkOfRegistry R` and EXACTLY
  * `[StarkSound hash R]` — the audited p3 batch-STARK extraction (named, realizable, not provable in
    Lean and never claimed to be),
  * `WitnessDecodesC hash R C pi` — the witness→kernel-state existence rung,
  * `descriptorRefinesFree C hash (R pi.effect) (kstep pi.effect)` — the published-effect refinement
    rung,
there EXIST kernel endpoints whose `C`-commitments ARE `pi.pre`/`pi.post` and between which
`kstep pi.effect` genuinely holds. The light client RAN NOTHING.

⚑ **No `Poseidon2SpongeCR`. No `CommitSurface`.** Both are refuted — the first at deployed BabyBear, the
second at every parameter — and neither was doing work here: `hCR` was consumed only to discharge
`descriptorRefines`'s dead antecedent, and the surface bundle only for its `commit` projection.

⚠ **WHAT THIS NO LONGER CLAIMS.** Nothing here says the endpoints are UNIQUE. A light client applying
THIS theorem learns "an accepted proof stands over a real kernel transition whose endpoints commit to
the published roots", NOT "the published root determines the state". The second half is
`stateDecode_pre_faithful`/`_post_faithful` over `CommitSurface.commit_binds` and is genuinely open. -/
theorem lightclient_unfoolable_free
    (C : CommitMap) (hash : List ℤ → ℤ) (R : Registry) [StarkSound hash R]
    (kstep : EffectIdx → RecChainedState → RecChainedState → Prop)
    (pi : BatchPublicInputs) (π : BatchProof)
    (hrefine : descriptorRefinesFree C hash (R pi.effect) (kstep pi.effect))
    (hwitdec : WitnessDecodesC hash R C pi)
    (hacc : verifyBatch (vkOfRegistry R) pi π = Verdict.accept) :
    ∃ pre post : RecChainedState,
      StateDecodeC C pi.toPublished pre post ∧
      kstep pi.effect pre post ∧
      pi.pre = C pre.kernel pi.turn ∧
      pi.post = C post.kernel pi.turn := by
  -- (1) the audited extraction: an accepting batch yields a `Satisfied2` witness of the CLAIMED
  --     descriptor whose published commitments ARE `pi.toPublished`.
  obtain ⟨minit, mfin, maddrs, t, hsat, hpub⟩ :=
    (inferInstance : StarkSound hash R).extract pi π hacc
  -- (2) the existence rung supplies the decoded kernel boundary.
  obtain ⟨pre, post, hdecode⟩ := hwitdec minit mfin maddrs t hsat hpub
  -- (3) the published-effect rung — fed the SAME publication link (2) was, not a free `pc`.
  have hstep : kstep pi.effect pre post :=
    hrefine minit mfin maddrs t pi.toPublished pre post hsat hpub hdecode
  refine ⟨pre, post, hdecode, hstep, ?_, ?_⟩
  · simpa using hdecode.preBinds
  · simpa using hdecode.postBinds

/-! ## §4 — NO STRENGTH LOST, stated where it CAN be stated.

⚑ The obvious form of this tooth — "`CircuitSoundness.lightclient_unfoolable` follows from
`lightclient_unfoolable_free`" — CANNOT BE WRITTEN HERE, and the reason is the finding, not an
inconvenience: any such theorem must quantify over `S : CommitSurface`, and `#floor_ratchet` correctly
counts every declaration that does as a fresh carrier of a bundle refuted at every parameter. Writing
it would have meant adding a knowingly-vacuous theorem to prove a de-vacuuming.

So the recovery is demonstrated IN SITU instead, on every build, by the grandfathered apexes
themselves: `ClosureAll.lightclient_unfoolable_closed`,
`ClosureFinal.lightclient_unfoolable_one`/`…_circuit_sound`,
`ClosureFinalAvail.lightclient_unfoolable_closed_final_avail` and
`KernelConfigSoundness.kernelConfigSound{,Avail}` keep their conclusions VERBATIM and are now PROVED
through `lightclient_unfoolable_free`. Nothing that stood on them fell; the `Poseidon2SpongeCR` binder
left their signatures.

What CAN be stated floor-free and bundle-free is the rung comparison, and it is the load-bearing half:
the free rung asks STRICTLY LESS than the old one. -/

/-- **NO STRENGTH LOST (rung).** The body of `CircuitSoundness.descriptorRefines` — typed out at a bare
commit map rather than referenced, so no bundle and no floor appears — implies the free rung. The free
rung adds NO obligation: it drops the refuted antecedent and it RECEIVES the publication link rather
than having to hold without it. Anyone who could discharge the old rung can discharge this one. -/
theorem descriptorRefinesFree_of_unlinked (C : CommitMap) (hash : List ℤ → ℤ)
    (d : EffectVmDescriptor2) (kstep : RecChainedState → RecChainedState → Prop)
    (h : ∀ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
          (pc : PublishedCommit) (pre post : RecChainedState),
          Satisfied2 hash d minit mfin maddrs t → StateDecodeC C pc pre post → kstep pre post) :
    descriptorRefinesFree C hash d kstep :=
  fun minit mfin maddrs t pc pre post hsat _hlink hdec =>
    h minit mfin maddrs t pc pre post hsat hdec

/-! ## §5 — ⚑ TEETH: the rung is REFUTABLE — the acceptance test both existing forms FAIL.

`DescriptorRefinesShirkRefuted` set the standing test for any candidate re-grounding of
`descriptorRefines`:

> "At one and the same deployed-shaped sponge, BOTH the keystone and its replacement hold with
>  `kstep := fun _ _ => False` … A refinement obligation that is discharged at an unsatisfiable
>  conclusion constrains the circuit in no way at all. This is the falsifier any candidate re-grounding
>  of `descriptorRefines` must survive; neither of the two currently in the tree does."

`descriptorRefinesFree` survives it — at EVERY hash and EVERY descriptor, the deployed `Rfix e`
included. The witness is the EMPTY trace (every per-row obligation is `∀ i < 0`) paired with a boundary
the exhibited commit map makes decode; the conclusion `False` then cannot hold. -/

/-- The empty trace: zero main rows, all auxiliary tables empty. -/
def emptyTrace : VmTrace where
  rows := []
  pub  := fun _ => 0
  tf   := fun _ => []

@[simp] theorem emptyTrace_rows : emptyTrace.rows = [] := rfl
@[simp] theorem memLog_emptyTrace (d : EffectVmDescriptor2) : memLog d emptyTrace = [] := rfl
@[simp] theorem mapLog_emptyTrace (d : EffectVmDescriptor2) : mapLog d emptyTrace = [] := rfl

/-- **The empty trace satisfies EVERY descriptor**, at every hash and every memory boundary. (The
`transferV3` instance of this is `CircuitCompletenessNonVacuity.satisfied2_transferV3_empty`; nothing in
that proof is descriptor-specific, so it is restated here in full generality — which is what makes the
refutation below reach the deployed registry entries.) -/
theorem satisfied2_emptyTrace (hash : List ℤ → ℤ) (d : EffectVmDescriptor2)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) :
    Satisfied2 hash d minit mfin [] emptyTrace where
  rowConstraints := by intro i hi; simp at hi
  rowHashes := by intro i hi; simp at hi
  rowRanges := by intro i hi; simp at hi
  memAddrsNodup := List.nodup_nil
  memClosed := by intro op hop; simp at hop
  memDisciplined := by rw [memLog_emptyTrace]; trivial
  memBalanced := by
    rw [memLog_emptyTrace]
    simp [MemoryChecking.MemCheck, MemoryChecking.initSet, MemoryChecking.finalSet,
      MemoryChecking.readSet, MemoryChecking.writeSetFrom, MemoryChecking.boundarySet]
  memTableFaithful := by rw [memLog_emptyTrace]; rfl
  mapTableFaithful := by rw [mapLog_emptyTrace]; rfl

/-- The empty-cell kernel: no live accounts, every cell `default`. -/
def kernel0 : RecordKernelState where
  accounts := ∅
  cell     := fun _ => default
  caps     := fun _ => []

/-- A SECOND well-formed kernel, distinguishable from `kernel0` by its nullifier set alone. The
refutation needs DIFFERENT states at the two published boundaries. -/
def kernel1 : RecordKernelState where
  accounts := ∅
  cell     := fun _ => default
  caps     := fun _ => []
  nullifiers := [0]

theorem kernel0_wf : AccountsWF kernel0 := fun _ _ => rfl
theorem kernel1_wf : AccountsWF kernel1 := fun _ _ => rfl

theorem kernel1_ne_kernel0 : kernel1 ≠ kernel0 := by
  intro h
  have hn : ([0] : List Nat) = [] := congrArg RecordKernelState.nullifiers h
  simp at hn

/-- The two chained states the refutation places at the published boundary. -/
def state0 : RecChainedState := { kernel := kernel0, log := [] }
/-- The post-side chained state of the refutation (a kernel distinct from `state0`'s). -/
def state1 : RecChainedState := { kernel := kernel1, log := [] }

open Classical in
/-- **The exhibited commit map** — it sends `kernel0` to whatever the empty trace published as its OLD
commitment and every other kernel to its NEW one. A `CommitMap` is an arbitrary function, so this is a
legitimate closed instance; the tooth's job is to show `descriptorRefinesFree` is not the constant
`True`, and one instance where it fails settles that. -/
noncomputable def collapseMap (t : VmTrace) : CommitMap :=
  fun k _ => if k = kernel0 then (tracePublishedCommit t).pubPre
             else (tracePublishedCommit t).pubPost

/-- **⚑⚑ THE ACCEPTANCE TEST, PASSED.** For EVERY hash and EVERY descriptor — the deployed `Rfix e`
included — the floor-free rung is FALSE at the unsatisfiable step relation `fun _ _ => False`.

Contrast, at the same descriptor and the same deployed-shaped sponge:
`DescriptorRefinesShirkRefuted.descriptorRefines_vacuous_babyBear` PROVES
`descriptorRefines S hash d (fun _ _ => False)`, and `…descriptorRefinesR_vacuous_babyBear` proves the
same of the reduction twin. Both are discharged by the PARAMETERS. This one is not dischargeable at all
— so a proof of it is a claim about the circuit, which is what a refinement obligation is for. -/
theorem descriptorRefinesFree_false_at_False_kstep (hash : List ℤ → ℤ) (d : EffectVmDescriptor2) :
    ¬ descriptorRefinesFree (collapseMap emptyTrace) hash d (fun _ _ => False) := by
  intro h
  refine h (fun _ => 0) (fun _ => (0, 0)) [] emptyTrace (tracePublishedCommit emptyTrace)
    state0 state1 (satisfied2_emptyTrace hash d _ _) rfl ?_
  refine ⟨?_, ?_, kernel0_wf, kernel1_wf⟩
  · show (tracePublishedCommit emptyTrace).pubPre
        = collapseMap emptyTrace kernel0 (tracePublishedCommit emptyTrace).turn
    unfold collapseMap
    rw [if_pos rfl]
  · show (tracePublishedCommit emptyTrace).pubPost
        = collapseMap emptyTrace kernel1 (tracePublishedCommit emptyTrace).turn
    unfold collapseMap
    rw [if_neg kernel1_ne_kernel0]

/-! ### The OTHER carried rung is refutable too.

`WitnessDecodesC` is the apex's second hypothesis. A refutable rung and an unfalsifiable one sitting
side by side would leave the apex half-empty, so the same treatment is applied: at the public inputs the
empty trace actually publishes, and a commit map that misses the published OLD root by one, the
existence rung is FALSE. Note this is only stateable because `pi` is BUILT from
`tracePublishedCommit emptyTrace` — the publication link is not assumed, it is exhibited. -/

/-- The public inputs the empty trace publishes (built from its own `tracePublishedCommit`, so the
publication link below is `rfl` rather than an assumption). -/
def emptyPi : BatchPublicInputs where
  effect := 0
  pre    := (tracePublishedCommit emptyTrace).pubPre
  post   := (tracePublishedCommit emptyTrace).pubPost
  turn   := (tracePublishedCommit emptyTrace).turn

/-- The empty trace publishes exactly `emptyPi` — by structure eta, no hypothesis. -/
theorem emptyPi_toPublished : emptyPi.toPublished = tracePublishedCommit emptyTrace := rfl

/-- A commit map that misses the published OLD root by one, at every kernel. -/
def offsetMap : CommitMap := fun _ _ => (tracePublishedCommit emptyTrace).pubPre + 1

/-- **(CANARY — the existence rung is REFUTABLE.)** `WitnessDecodesC` is FALSE at `offsetMap` on the
boundary the empty trace actually publishes: it would have to produce a kernel whose `offsetMap`
commitment equals the published OLD root, and `x + 1 = x` has no solutions. So the apex's second
carried rung is not the constant `True` either. -/
theorem witnessDecodesC_false_at_offsetMap (hash : List ℤ → ℤ) (R : Registry) :
    ¬ WitnessDecodesC hash R offsetMap emptyPi := by
  intro h
  obtain ⟨pre, _post, hd⟩ := h (fun _ => 0) (fun _ => (0, 0)) [] emptyTrace
    (satisfied2_emptyTrace hash (R emptyPi.effect) _ _) emptyPi_toPublished
  have hx : (tracePublishedCommit emptyTrace).pubPre
      = (tracePublishedCommit emptyTrace).pubPre + 1 := hd.preBinds
  omega

/-- **The apex's CONCLUSION is contingent too.** At the unsatisfiable step relation the conclusion is
outright FALSE, so `lightclient_unfoolable_free` at that `kstep` is a genuine implication between two
refutable statements — not `True → True`. -/
theorem apex_conclusion_false_at_False_kstep (C : CommitMap) (pi : BatchPublicInputs) :
    ¬ ∃ pre post : RecChainedState,
      StateDecodeC C pi.toPublished pre post ∧
      (fun _ _ : RecChainedState => False) pre post ∧
      pi.pre = C pre.kernel pi.turn ∧
      pi.post = C post.kernel pi.turn := by
  rintro ⟨_, _, _, hfalse, _, _⟩
  exact hfalse

/-! ## §6 — SATISFIABLE: the apex's carried rungs are inhabited at a concrete boundary.

A refutable hypothesis that is never satisfiable is just as empty. (`StarkSound` is the one named
realizability the design carries explicitly; it is NOT discharged here and never claimed to be.) -/

/-- The `True` step relation — the rung's codomain when showing the obligation is inhabited. -/
def trivialKstep : RecChainedState → RecChainedState → Prop := fun _ _ => True

/-- **SATISFIABLE POLE (rung).** The floor-free rung holds at the trivially-true step relation, for
every commit map / hash / descriptor. So §5's refutation is a fact about which CONCLUSIONS the rung
admits, not about the rung being unsatisfiable. -/
theorem descriptorRefinesFree_trivial (C : CommitMap) (hash : List ℤ → ℤ)
    (d : EffectVmDescriptor2) : descriptorRefinesFree C hash d trivialKstep :=
  fun _ _ _ _ _ _ _ _ _ _ => trivial

/-- **SATISFIABLE POLE (existence rung), on a genuine boundary.** When the public inputs' roots ARE `C`
of well-formed kernels at `pi.turn`, `WitnessDecodesC` HOLDS — proved, not assumed. This is the
commit-map form of `WitnessRealizing.witnessDecodes_of_genuine_roots`, and unlike it, it is stated at a
type that has inhabitants. -/
theorem witnessDecodesC_of_genuine_roots (hash : List ℤ → ℤ) (R : Registry) (C : CommitMap)
    (pi : BatchPublicInputs) (pre₀ post₀ : RecChainedState)
    (hpreWF : AccountsWF pre₀.kernel) (hpostWF : AccountsWF post₀.kernel)
    (hpre : pi.pre = C pre₀.kernel pi.turn) (hpost : pi.post = C post₀.kernel pi.turn) :
    WitnessDecodesC hash R C pi := by
  intro minit mfin maddrs t _hsat _hpub
  exact ⟨pre₀, post₀, ⟨by simpa using hpre, by simpa using hpost, hpreWF, hpostWF⟩⟩

/-- The genuine public inputs an honest `state0 ⟶ state0` boundary publishes at turn `τ`. -/
def genuinePi (C : CommitMap) (τ : Turn) : BatchPublicInputs where
  effect := 0
  pre    := C kernel0 τ
  post   := C kernel0 τ
  turn   := τ

/-- **`witnessDecodesC_genuine` — the existence rung FIRES**, at every commit map (the deployed
`recStateCommit` included), every hash and every registry. -/
theorem witnessDecodesC_genuine (hash : List ℤ → ℤ) (R : Registry) (C : CommitMap) (τ : Turn) :
    WitnessDecodesC hash R C (genuinePi C τ) :=
  witnessDecodesC_of_genuine_roots hash R C (genuinePi C τ) state0 state0
    kernel0_wf kernel0_wf rfl rfl

/-! ## §7 — axiom hygiene. -/

#assert_axioms StateDecodeC
#assert_axioms descriptorRefinesFree
#assert_axioms lightclient_unfoolable_free
#assert_axioms descriptorRefinesFree_of_unlinked
#assert_axioms satisfied2_emptyTrace
#assert_axioms descriptorRefinesFree_false_at_False_kstep
#assert_axioms emptyPi_toPublished
#assert_axioms witnessDecodesC_false_at_offsetMap
#assert_axioms apex_conclusion_false_at_False_kstep
#assert_axioms descriptorRefinesFree_trivial
#assert_axioms witnessDecodesC_genuine

end Dregg2.Circuit.ApexFloorFree
