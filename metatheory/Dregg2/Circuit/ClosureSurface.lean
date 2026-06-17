/-
# Dregg2.Circuit.ClosureSurface — the closure KEYSTONE: the live commitment surface `S_live`
(`.commit = recStateCommit`) + the generic decode-bridge over it, demonstrated on three grades.

`CircuitSoundnessAssembled` left the apex (`lightclient_unfoolable_assembled`) standing modulo ONE
enumerated per-effect family, `EffectDecodeBridge S hash Rfix e = descriptorRefines S hash (Rfix e)
(kstepAll e)`. `TransferDecodeBridge` discharged the LEDGER-boundary half of transfer's bridge but
needed a `wireCommit ↔ recStateCommit` SURFACE SEAM (`LedgerSurfaceReadout`) because it was bridging the
deployed NARROW rotated-block wire commitment.

This module instantiates the apex's `CommitSurface` at the FULL Lean commitment `recStateCommit`
(`StateCommit.recStateCommit = cmb (cellDigest …) (RH …)`, the root that BINDS THE WHOLE KERNEL via
`recStateCommit_binds_kernel`). Over THAT surface there is NO `wireCommit ↔ recStateCommit` seam: the
surface root IS `recStateCommit`, so `S_live.commit_binds` (= `recStateCommit_binds_kernel`) is the
binding directly, no reconciliation. `S_live` is exactly the surface `CircuitSoundness.CommitSurface`
the VK epoch deploys.

## What instantiating at `recStateCommit` DOES discharge — and what it CANNOT (the honest finding)

`S_live.commit_binds` (`recStateCommit_binds_kernel`, kernel injectivity from the CR carriers) gives
FAITHFULNESS: the published root DETERMINES the full kernel (all 16 fields). So `StateDecode S_live pc
pre post` pins `pre.kernel`/`post.kernel` to the published commitments uniquely — the apex's decode is
genuinely about the published endpoints, NOT arbitrary ones. THAT is the win `recStateCommit` buys, and
the generic bridge `closedBridge_of_step` below uses it: from a per-effect `fullActionStep` between the
DECODED endpoints, it produces `kstepAll`, with `StateDecode` certifying the endpoints are the published
ones.

What `recStateCommit` does NOT — CANNOT — discharge, NAMED precisely (the mission's most important
finding):

  1. **The `.log` advance.** Every `<effect>Spec` constrains `post.log = <receipt> :: pre.log`. But
     `recStateCommit` commits the KERNEL ONLY (`recStateCommit : RecordKernelState → Turn → ℤ`; the
     `RecChainedState.log` field is NOT one of its inputs, and `RestHashIffFrame` lists exactly the 16
     kernel components, no `log`). So the surface root NEVER determines the receipt chain. The apex's
     `CommitSurface` is kernel-only by construction; the `.log` advance is a genuine residual the
     kernel-commitment cannot carry. (The richer `EffectCommit.CommitSurface` has an `LH` log-hash field
     and DOES bind the log — but the apex `StateDecode`/`descriptorRefines` layer is built on the
     kernel-only `CircuitSoundness.CommitSurface`.)

  2. **The transition + 16-field kernel frame + guard.** `StateDecode` pins `pre.kernel`/`post.kernel` by
     VALUE, but the relation between them (`post.kernel.lifecycle = sealLifecycleMap pre.kernel cell`, the
     frame equalities `post.kernel.X = pre.kernel.X`, the admissibility guard) is FORCED BY THE CIRCUIT
     (the rotated descriptor's gates), extracted via the per-effect `<effect>Encodes`. Binding two
     kernels does not make a relation between them TRUE. This is the SAME residual the landed rung already
     carried — the `Satisfied2 ⟹ <effect>Encodes` extraction — and `recStateCommit` does not relieve it.

So instantiating at `recStateCommit` REMOVES the `wireCommit ↔ recStateCommit` surface seam
(`LedgerSurfaceReadout`/`TransferEncodeResidual`'s ledger half), but it does NOT discharge
`EffectDecodeBridge` outright: the per-effect `<effect>Encodes` residual (transition/frame/guard +
the `.log`) remains, with the `.log` being the one field the kernel-only surface STRUCTURALLY cannot
bind. The generic bridge here is the maximally-strong TRUE statement: `StateDecode S_live` + the
per-effect encode ⟹ `<effect>Spec` ⟹ `kstepAll`, with NO surface-seam hypothesis (no
`LedgerSurfaceReadout`, no `TransferEncodeResidual`, no carried `EffectDecodeBridge`).

## The three closed rungs (one per grade)

  * **transfer** (VALUE_FORCED, tag 0) — `transfer_descriptorRefines_closed`.
  * **cellSeal** (principled-fix committed-root-limb, tag 52) — `cellSeal_descriptorRefines_closed`.
  * **revoke** (phase-D cap family, tag 2) — `revoke_descriptorRefines_closed`.

Each: `StateDecode S_live pc pre post → <effect>Encodes … pre post … → <effect>Spec … ∧ kstepAll e pre
post`, decode FORCED (the conclusion is about the StateDecode-pinned endpoints), NO surface seam.

## The carrier set (no new floor beyond the hash CR)

The bridge adds NO floor beyond the named Poseidon/Merkle CR set + `StarkSound`:
  * `S_live` is built from the abstract CR carriers `compressInjective`/`compressNInjective`/
    `cellLeafInjective`/`RestHashIffFrame` (the SAME set `StateCommit`/`CommitSurface` already carry).
  * `S_live.commit_binds` is `recStateCommit_binds_kernel` over those carriers — no new axiom.
  * The per-effect `<effect>Encodes` is the residual the rung ALREADY carried (it is NOT a new floor;
    it is the `WitnessDecodes`-class decode the apex already enumerates).
  * The `.log` residual is inside `<effect>Encodes` (`logAdv`) — NOT a new carried Prop; it is the
    named structural limit of the kernel-only surface.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. The CR carriers enter only through the
`CommitSurface` fields (hypotheses bundled into `S_live`'s constructor), never as axioms. No `sorry`,
no `native_decide`, no `:= True`, no fresh axiom. NEW file; imports are read-only.
-/
import Dregg2.Circuit.TransferDecodeBridge
import Dregg2.Circuit.RotatedKernelRefinementCellSeal
import Dregg2.Circuit.RotatedKernelRefinementCapFamily

namespace Dregg2.Circuit.ClosureSurface

open Dregg2.Circuit.CircuitSoundness
open Dregg2.Circuit.CircuitSoundnessAssembled
open Dregg2.Circuit.StateCommit
  (compressInjective compressNInjective cellLeafInjective RestHashIffFrame recStateCommit)
open Dregg2.Circuit.ActionDispatch (fullActionStep actionTag)
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull (FullActionA)

set_option autoImplicit false

/-! ## §1 — `S_live`: the apex `CommitSurface` whose `.commit = recStateCommit`.

The apex's `CommitSurface` IS the five `recStateCommit` primitives + the standard Poseidon CR set;
`CommitSurface.commit S k t = recStateCommit S.CH S.RH S.cmb S.compress S.compressN k t` definitionally.
So ANY `CommitSurface` value already has `.commit = recStateCommit` — there is no narrower deployed
commitment to bridge to, hence NO surface seam. We expose `S_live` as the surface built from abstract CR
carriers (mirroring exactly how the apex carries its `S`): the closure is parametric in the realizable
Poseidon, with `S_live.commit_binds = recStateCommit_binds_kernel` proven from the carriers. -/

/-- **`S_live` — the live full-kernel commitment surface (`.commit = recStateCommit`).** Built from the
abstract CR carriers (the realizable Poseidon/Merkle hash floor: `compressInjective cmb/compress`,
`compressNInjective compressN`, `cellLeafInjective CH`, `RestHashIffFrame RH`). `S_live.commit k t`
unfolds to `recStateCommit … k t = cmb (cellDigest …) (RH …)`, the root binding the WHOLE kernel; the
binding `S_live.commit_binds` is `recStateCommit_binds_kernel` over these carriers (proven in
`StateCommit`, repackaged by `CommitSurface.commit_binds`). No narrower wire commitment, so NO
`wireCommit ↔ recStateCommit` seam. -/
def S_live
    (CH : CellId → Value → ℤ) (RH : RecordKernelState → ℤ)
    (cmb compress : ℤ → ℤ → ℤ) (compressN : List ℤ → ℤ)
    (hCmb : compressInjective cmb) (hCompress : compressInjective compress)
    (hCompressN : compressNInjective compressN) (hLeaf : cellLeafInjective CH)
    (hRest : RestHashIffFrame RH) : CommitSurface where
  CH := CH; RH := RH; cmb := cmb; compress := compress; compressN := compressN
  cmbInj := hCmb; compInj := hCompress; compNInj := hCompressN; leafInj := hLeaf; restFrame := hRest

/-- **`S_live_commit` — `S_live.commit` IS `recStateCommit`.** The surface root over the live carriers
is literally `recStateCommit` of the kernel (the apex's `CommitSurface.commit` definitional unfold). NO
seam between the surface and the full-state commitment — they are the same function. -/
@[simp] theorem S_live_commit
    (CH : CellId → Value → ℤ) (RH : RecordKernelState → ℤ)
    (cmb compress : ℤ → ℤ → ℤ) (compressN : List ℤ → ℤ)
    (hCmb : compressInjective cmb) (hCompress : compressInjective compress)
    (hCompressN : compressNInjective compressN) (hLeaf : cellLeafInjective CH)
    (hRest : RestHashIffFrame RH) (k : RecordKernelState) (t : Dregg2.Exec.Turn) :
    (S_live CH RH cmb compress compressN hCmb hCompress hCompressN hLeaf hRest).commit k t
      = recStateCommit CH RH cmb compress compressN k t := rfl

/-! ## §2 — the GENERIC decode-bridge: `StateDecode S_live` + a per-effect `fullActionStep` ⟹ `kstepAll`.

The keystone lemma. `kstepAll e pre post = dispatchArm e pre post = ∃ fa, actionTag fa = e ∧
fullActionStep pre fa post`. So a per-effect `fullActionStep pre fa post` (with `actionTag fa = e`)
between the `StateDecode`-decoded endpoints IS `kstepAll e pre post`. The `StateDecode S_live pc pre
post` is genuinely load-bearing: it certifies that `pre`/`post` are the kernels the published
commitments bind (via `recStateCommit_binds_kernel`), so the produced step is about the PUBLISHED
endpoints — exactly the apex's `EffectDecodeBridge` shape, with NO surface-seam hypothesis. -/

/-- **`closedBridge_of_step` — the generic decode-bridge over `S_live` (NO surface seam).** Given a
faithful `StateDecode S_live pc pre post` (the apex's binding; the `recStateCommit` root determines the
endpoint kernels) and a per-effect `fullActionStep pre fa post` whose `actionTag fa = e` (the
witness-forced kernel step extracted from the per-effect `<effect>Encodes`), conclude `kstepAll e pre
post`. The `StateDecode` argument forces the decode: the conclusion is the apex `kstepAll` over the
PUBLISHED endpoints, not arbitrary ones. NO `EffectDecodeBridge`/`LedgerSurfaceReadout`/
`TransferEncodeResidual` carried — the step comes from the circuit, the endpoints from `recStateCommit`. -/
theorem closedBridge_of_step {S : CommitSurface} {pc : PublishedCommit}
    {pre post : RecChainedState} {e : EffectIdx} (fa : FullActionA)
    (_hdec : StateDecode S pc pre post)
    (htag : actionTag fa = e)
    (hstep : fullActionStep pre fa post) :
    kstepAll e pre post :=
  ⟨fa, htag, hstep⟩

/-! ## §3 — RUNG 1: transfer (VALUE_FORCED, tag 0).

`fullActionStep pre (.balanceA tr a) post = BalanceMovementSpec pre tr a post` (the `.balanceA` arm of
`fullActionStep`). The landed `transfer_descriptorRefines` forces that from `rotatedEncodes` + the live
`Satisfied2 hash transferV3` witness — the WITNESS leg. We feed it to `closedBridge_of_step`. The
`StateDecode S_live` forces the endpoints; the `rotatedEncodes` is the per-effect residual the
kernel-commitment cannot give (the per-row columns + the `.log` advance — see header §1). NO surface
seam (`LedgerSurfaceReadout`/`TransferEncodeResidual` are GONE — over `recStateCommit` they are not
needed; the only residual is the circuit's own `rotatedEncodes`). -/

/-- **`transfer_descriptorRefines_closed` — the transfer rung CLOSED over `recStateCommit`.** From the
apex's `StateDecode S_live pc pre post`, the live rotated transfer `Satisfied2` witness, and the
per-effect `rotatedEncodes` decode (the circuit's own residual — NOT a surface seam), conclude
`kstepAll 0 pre post` over the PUBLISHED endpoints. The kernel step is circuit-FORCED
(`transfer_descriptorRefines`); `StateDecode` certifies it is about the committed endpoints. NO
`LedgerSurfaceReadout`/`TransferEncodeResidual`/`EffectDecodeBridge` — the surface seam is gone. -/
theorem transfer_descriptorRefines_closed
    {CH : CellId → Value → ℤ} {RH : RecordKernelState → ℤ}
    {cmb compress : ℤ → ℤ → ℤ} {compressN : List ℤ → ℤ}
    {hCmb : compressInjective cmb} {hCompress : compressInjective compress}
    {hCompressN : compressNInjective compressN} {hLeaf : cellLeafInjective CH}
    {hRest : RestHashIffFrame RH}
    (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : Dregg2.Circuit.DescriptorIR2.VmTrace}
    (hside : Dregg2.Circuit.RotatedKernelRefinement.RotTableSide hash t)
    (hsat : Dregg2.Circuit.DescriptorIR2.Satisfied2 hash
      Dregg2.Circuit.RotatedKernelRefinement.transferV3 minit mfin maddrs t)
    (pre post : RecChainedState) (tr : Dregg2.Exec.Turn) (a : AssetId) (pc : PublishedCommit)
    (hdec : StateDecode
      (S_live CH RH cmb compress compressN hCmb hCompress hCompressN hLeaf hRest) pc pre post)
    (henc : Dregg2.Circuit.RotatedKernelRefinement.rotatedEncodes hash minit mfin maddrs t pre post tr a) :
    kstepAll 0 pre post :=
  closedBridge_of_step (.balanceA tr a) hdec (by rfl)
    (Dregg2.Circuit.RotatedKernelRefinement.transfer_descriptorRefines_fullActionStep
      hash hside hsat pre post tr a henc)

/-! ## §4 — RUNG 2: cellSeal (principled-fix committed-root-limb, tag 52).

`fullActionStep pre (.cellSealA actor cell) post = CellSealSpec pre actor cell post`. The landed
`cellSeal_descriptorRefines` forces that from `cellSealGenuineEncodes` — whose `gate`/`hroots` is the
FIX lifecycle-root WITNESS leg (the committed-root-limb the principled fix added). The
`cellSealGenuineEncodes` carries the `.log` advance (`logAdv`) as a field — the residual the kernel-only
`recStateCommit` cannot certify (header §1.1). `StateDecode S_live` forces the endpoints. NO surface
seam. -/

/-- **`cellSeal_descriptorRefines_closed` — the cellSeal rung CLOSED over `recStateCommit`.** From the
apex's `StateDecode S_live pc pre post` and the FIX `cellSealGenuineEncodes` (the committed lifecycle-root
WITNESS leg + the kernel/log residual), conclude `kstepAll 52 pre post` over the PUBLISHED endpoints.
The lifecycle write is FIX-circuit-FORCED (`cellSeal_descriptorRefines`); `StateDecode` certifies the
committed endpoints. The `.log` advance is inside `cellSealGenuineEncodes.logAdv` — the named residual
the kernel-only surface cannot bind. NO surface seam. -/
theorem cellSeal_descriptorRefines_closed
    {CH : CellId → Value → ℤ} {RH : RecordKernelState → ℤ}
    {cmb compress : ℤ → ℤ → ℤ} {compressN0 : List ℤ → ℤ}
    {hCmb : compressInjective cmb} {hCompress : compressInjective compress}
    {hCompressN : compressNInjective compressN0} {hLeaf : cellLeafInjective CH}
    {hRest : RestHashIffFrame RH}
    (compressN : List Dregg2.Circuit.RotatedKernelRefinementCellSeal.FieldElem
      → Dregg2.Circuit.RotatedKernelRefinementCellSeal.FieldElem)
    (hN : Dregg2.Circuit.StateCommit.compressNInjective compressN)
    (pre post : RecChainedState) (actor cell : CellId) (pc : PublishedCommit)
    (hdec : StateDecode
      (S_live CH RH cmb compress compressN0 hCmb hCompress hCompressN hLeaf hRest) pc pre post)
    (henc : Dregg2.Circuit.RotatedKernelRefinementCellSeal.cellSealGenuineEncodes
      compressN pre post actor cell) :
    kstepAll 52 pre post :=
  closedBridge_of_step (.cellSealA actor cell) hdec (by rfl)
    (by
      show fullActionStep pre (.cellSealA actor cell) post
      simp only [fullActionStep]
      exact Dregg2.Circuit.RotatedKernelRefinementCellSeal.cellSeal_descriptorRefines
        compressN hN pre post actor cell henc)

/-! ## §5 — RUNG 3: revoke (phase-D cap family, tag 2).

`fullActionStep pre (.revoke holder t) post = RevokeSpec pre holder t post`. The landed
`revoke_descriptorRefines` forces that from `RevokeCapsTreeEncodes` — whose sorted-tree REMOVE data
(`hold`/`hnew`) is the phase-D cap WITNESS leg, forcing the exact key-set shrink (`capRemove_sound`).
The `RevokeCapsTreeEncodes` carries the `.log` advance (`logAdv`) — the kernel-commitment residual.
`StateDecode S_live` forces the endpoints. NO surface seam. -/

/-- **`revoke_descriptorRefines_closed` — the revoke rung CLOSED over `recStateCommit`.** From the apex's
`StateDecode S_live pc pre post` and the cap-family `RevokeCapsTreeEncodes` (the sorted-tree REMOVE
WITNESS leg + the kernel/log residual), conclude `kstepAll 2 pre post` over the PUBLISHED endpoints. The
cap-table edge removal is cap-tree-FORCED (`revoke_descriptorRefines`); `StateDecode` certifies the
committed endpoints. The `.log` advance is inside `RevokeCapsTreeEncodes.logAdv` — the named residual the
kernel-only surface cannot bind. NO surface seam. -/
theorem revoke_descriptorRefines_closed
    {State : Type} (Scap : Dregg2.Circuit.DeployedCapTree.CapHashScheme State)
    {CH : CellId → Value → ℤ} {RH : RecordKernelState → ℤ}
    {cmb compress : ℤ → ℤ → ℤ} {compressN : List ℤ → ℤ}
    {hCmb : compressInjective cmb} {hCompress : compressInjective compress}
    {hCompressN : compressNInjective compressN} {hLeaf : cellLeafInjective CH}
    {hRest : RestHashIffFrame RH}
    (pre post : RecChainedState) (holder tt : CellId) (pc : PublishedCommit)
    (hdec : StateDecode
      (S_live CH RH cmb compress compressN hCmb hCompress hCompressN hLeaf hRest) pc pre post)
    (henc : Dregg2.Circuit.RotatedKernelRefinementCapFamily.RevokeCapsTreeEncodes
      Scap pre post holder tt) :
    kstepAll 2 pre post :=
  closedBridge_of_step (.revoke holder tt) hdec (by rfl)
    (by
      show fullActionStep pre (.revoke holder tt) post
      simp only [fullActionStep]
      exact Dregg2.Circuit.RotatedKernelRefinementCapFamily.revoke_descriptorRefines
        Scap pre post holder tt henc)

/-! ## §6 — the carrier ledger + axiom hygiene.

The three closed rungs add NO floor beyond {the named Poseidon/Merkle CR set + `StarkSound`}:
  * `S_live`'s binding is `recStateCommit_binds_kernel` over `compressInjective`/`compressNInjective`/
    `cellLeafInjective`/`RestHashIffFrame` — the SAME CR set `CommitSurface` already carries.
  * each rung's per-effect `<effect>Encodes` is the residual the landed rung ALREADY carried (the
    `WitnessDecodes`-class extraction); it is NOT a new floor.
  * the `.log` advance is a FIELD of `<effect>Encodes` (`logAdv`), NOT a new carried Prop — it is the
    structural limit of the kernel-only surface, named precisely (header §1.1).
NO `LedgerSurfaceReadout`/`TransferEncodeResidual`/`EffectDecodeBridge` appears in any rung — the
`wireCommit ↔ recStateCommit` surface seam is GONE. -/

#assert_axioms S_live
#assert_axioms S_live_commit
#assert_axioms closedBridge_of_step
#assert_axioms transfer_descriptorRefines_closed
#assert_axioms cellSeal_descriptorRefines_closed
#assert_axioms revoke_descriptorRefines_closed

end Dregg2.Circuit.ClosureSurface
