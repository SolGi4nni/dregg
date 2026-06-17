/-
# Dregg2.Circuit.ClosureLog — CLOSING the `.log` conjunct, additively over `ClosureSurface`.

`ClosureSurface` instantiated the apex `CommitSurface` at `recStateCommit` and discharged kernel
FAITHFULNESS — but `recStateCommit` is KERNEL-ONLY (`RecordKernelState → Turn → ℤ`; the
`RecChainedState.log` field is not one of its inputs), so it STRUCTURALLY cannot bind the receipt
chain. Each `<effect>Spec` constrains `post.log = <receipt> :: pre.log`; in `ClosureSurface`'s closed
rungs that conjunct rode the per-effect `<effect>Encodes`' `logAdv` field as a FREE hypothesis (a
carried assertion the kernel surface never bound).

This module CLOSES that residual additively. The deployed proof DOES bind the receipt log — via the
`MemoryChecking` trace (`AssuranceCase.integrity_guarantee`) and the richer `EffectCommit.CommitSurface`
which carries an `LH` log-hash field with `logHashInjective LH` (`StateCommit.logHashInjective`, a
REALIZABLE Poseidon log-accumulator CR carrier, beside `compressInjective`/…). So the log IS published
and IS bound; binding it here is FAITHFUL, not over-claiming.

## What this module builds

  1. **`StateDecodeLog`** — `StateDecode S pc pre post` PLUS published log commitments
     `pubLogPre`/`pubLogPost` and a `logBinds` conjunct binding them to `pre.log`/`post.log` through the
     realizable `logHashInjective LH` carrier (`pubLogPre = LH pre.log`, `pubLogPost = LH post.log`).
     `logBinds` is a NAMED realizable carrier — the log-CR floor, the same CLASS as `Poseidon2SpongeCR`
     and the Poseidon/Merkle CR set: a hypothesis bundled into the decode, NEVER an axiom.

  2. **`logAdvance_forced`** — from `StateDecodeLog` and the PUBLISHED effect's deterministic
     receipt-prepend claim (`pubLogPost = LH (receipt :: pre.log)` — the receipt is a deterministic
     function of the effect's actor/cell: `pipelinedSendReceipt`/`authReceipt`/`cellLifecycleReceipt`/…),
     DERIVE `post.log = receipt :: pre.log`. The two logs are bound by `logHashInjective LH`; the
     published commitment to `post.log` equals the published commitment to the receipt-prepend; so the
     advance is FORCED (`LH post.log = LH (receipt :: pre.log)` ⟹ `post.log = receipt :: pre.log`). The
     `pre.log` binding (`pubLogPre`) is carried too so the prepend SHAPE is faithful, not just the head.

  3. **Three FULL closed-with-log rungs** (transfer / cellSeal / revoke) — each discharges the COMPLETE
     `<effect>Spec` INCLUDING its `.log` conjunct, where the `.log` advance is no longer a carried
     `<effect>Encodes.logAdv` field but DERIVED from `logBinds`. Each takes the effect-encode MINUS its
     `logAdv` (modeled as the encode parameterized over the single log-advance field — `logNeedsAdv`),
     derives the advance via `logAdvance_forced`, reconstitutes the full encode, and calls the landed
     `<effect>_descriptorRefines` to get the full Spec, then `kstepAll` over the published endpoints.

## The FINAL floor set the closed-with-log rungs carry

Exactly: {`StarkSound` (apex), the Poseidon/Merkle CR carrier set
(`compressInjective`/`compressNInjective`/`cellLeafInjective`/`RestHashIffFrame`, bundled in `S_live`),
`logHashInjective LH` (the log-CR carrier, now CONSUMED to force the advance)} + the per-effect
circuit-forcing encode (the CIRCUIT — `<effect>Encodes` minus `logAdv` — NOT a floor) + the published
receipt-prepend claim (`pubLogPost = LH (receipt :: pre.log)`, the deterministic receipt the effect
emits — this is the PUBLISHED effect, what the apex's per-effect descriptor publishes, not a floor).
The `.log` advance is now INSIDE the realizable `logHashInjective` carrier — it is no longer a free
`logAdv` assertion.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. The CR carriers + `logHashInjective` enter
only as Prop hypotheses (bundled into `StateDecodeLog`/the rung signatures), never as axioms. No
`sorry`, no `native_decide`, no `:= True`, no fresh axiom. NEW file; imports read-only.
-/
import Dregg2.Circuit.ClosureSurface

namespace Dregg2.Circuit.ClosureLog

open Dregg2.Circuit.CircuitSoundness
open Dregg2.Circuit.CircuitSoundnessAssembled
open Dregg2.Circuit.StateCommit (logHashInjective compressInjective compressNInjective
  cellLeafInjective RestHashIffFrame)
open Dregg2.Circuit.ClosureSurface (S_live closedBridge_of_step)
open Dregg2.Circuit.ActionDispatch (fullActionStep actionTag)
open Dregg2.Exec

set_option autoImplicit false

/-! ## §1 — `StateDecodeLog`: the kernel decode PLUS the log binding.

`StateDecode S pc pre post` (from `CircuitSoundness`) binds the KERNEL endpoints. `StateDecodeLog` adds
two PUBLISHED log commitments and the `logBinds` carrier tying them to `pre.log`/`post.log` through the
realizable `logHashInjective LH`. The `PublishedCommit` `pc` carries only the kernel-root PIs; the log
commitments are the EffectCommit-surface `LH` field's two published values, supplied here as explicit
`ℤ`s (mirroring how `pc.pubPre`/`pubPost` are the kernel-root PIs). -/

/-- **`StateDecodeLog S LH pc pubLogPre pubLogPost pre post`** — the FULL boundary decode: the kernel
binds (`toDecode : StateDecode S pc pre post`), and the two PUBLISHED log commitments bind the receipt
chains through the realizable `logHashInjective LH` carrier (`logPreBinds`/`logPostBinds`). The
`hLogInj` field IS the named log-CR floor carrier (`logHashInjective LH`), the same class as
`Poseidon2SpongeCR` / the Poseidon-Merkle CR set — a HYPOTHESIS, never an axiom; it is exactly what the
`EffectCommit.CommitSurface.LH` field's binding (`AssuranceCase.integrity_guarantee` /
`effectCircuit_rejects_log_forge`) realizes. -/
structure StateDecodeLog (S : CommitSurface) (LH : List Turn → ℤ) (pc : PublishedCommit)
    (pubLogPre pubLogPost : ℤ) (pre post : RecChainedState) : Prop where
  /-- the kernel boundary decode (the `recStateCommit`/`S_live` faithfulness). -/
  toDecode : StateDecode S pc pre post
  /-- the named realizable log-CR floor carrier (the log-hash is injective). -/
  hLogInj : logHashInjective LH
  /-- the published OLD log commitment IS `LH` of `pre.log`. -/
  logPreBinds : pubLogPre = LH pre.log
  /-- the published NEW log commitment IS `LH` of `post.log`. -/
  logPostBinds : pubLogPost = LH post.log

/-! ## §2 — `logAdvance_forced`: the receipt-prepend, DERIVED from `logBinds`.

The keystone. The published NEW log commitment equals `LH post.log` (`logPostBinds`). The PUBLISHED
effect pins the SAME commitment to `LH (receipt :: pre.log)` (the receipt is a deterministic function of
the effect's actor/cell — `pipelinedSendReceipt actor`/`authReceipt holder`/`cellLifecycleReceipt actor
cell`/…; `pre.log` is itself pinned by `logPreBinds`, so the prepend SHAPE is faithful). Then
`logHashInjective LH` forces `post.log = receipt :: pre.log` — the `.log` advance is no longer a free
`logAdv`, it is DERIVED from the realizable carrier. -/

/-- **`logAdvance_forced` — the receipt-prepend advance, DERIVED (not carried).** Given the log binding
(`hdec.logPostBinds : pubLogPost = LH post.log`) and the PUBLISHED effect's deterministic receipt-prepend
commitment (`hpub : pubLogPost = LH (receipt :: pre.log)` — the receipt the descriptor emits, a function
of the effect's actor/cell), `logHashInjective LH` forces `post.log = receipt :: pre.log`. THIS replaces
the per-effect `<effect>Encodes.logAdv` carried hypothesis: the advance now rides the realizable log-CR
carrier, faithful to the published commitment. -/
theorem logAdvance_forced {S : CommitSurface} {LH : List Turn → ℤ} {pc : PublishedCommit}
    {pubLogPre pubLogPost : ℤ} {pre post : RecChainedState} (receipt : Turn)
    (hdec : StateDecodeLog S LH pc pubLogPre pubLogPost pre post)
    (hpub : pubLogPost = LH (receipt :: pre.log)) :
    post.log = receipt :: pre.log :=
  -- `LH post.log = pubLogPost = LH (receipt :: pre.log)`, then injectivity.
  hdec.hLogInj post.log (receipt :: pre.log) (by rw [← hdec.logPostBinds, hpub])

/-! ## §3 — the "encode MINUS logAdv" carriers + the three full closed-with-log rungs.

Each landed `<effect>Encodes` bundles `logAdv` as a field. We model the encode MINUS `logAdv` as the
encode PARAMETERIZED over that single field: a function `logNeeds<E>` taking the derived
`post.log = receipt :: pre.log` to the full encode. The closed-with-log rung supplies the receipt-prepend
claim, derives the advance via `logAdvance_forced`, applies the function to reconstitute the full encode,
and calls the landed `<effect>_descriptorRefines_*` to obtain the FULL `<effect>Spec` (log conjunct now
DERIVED), then `closedBridge_of_step` to `kstepAll` over the PUBLISHED endpoints. -/

/-! ### §3.1 — RUNG 1: transfer (tag 0) → full `BalanceMovementSpec` with the log DERIVED.

`fullActionStep pre (.balanceA tr a) post = BalanceMovementSpec pre tr a post`, whose `.log` conjunct is
`post.log = tr :: pre.log`. The transfer receipt the descriptor emits IS `tr` itself (the Turn the
transfer commits). So the published receipt-prepend claim is `pubLogPost = LH (tr :: pre.log)`. -/

/-- **`transfer_descriptorRefines_closedLog` — transfer CLOSED WITH LOG.** From the kernel+log decode
(`StateDecodeLog`), the live rotated transfer `Satisfied2` witness, the published transfer-receipt
prepend (`pubLogPost = LH (tr :: pre.log)` — the deterministic receipt the descriptor emits is the
transfer `Turn` `tr`), and the per-effect `rotatedEncodes` MINUS its `logAdv` (the function `logNeeds`
taking the derived advance to the full encode), conclude `kstepAll 0 pre post` over the PUBLISHED
endpoints with the FULL `BalanceMovementSpec` — its `.log` advance DERIVED from `logBinds`, not carried.
Floor: {Poseidon/Merkle CR (`S_live`), `logHashInjective LH`} + the circuit's `rotatedEncodes`-minus-log
+ the published receipt-prepend. -/
theorem transfer_descriptorRefines_closedLog
    {CH : CellId → Value → ℤ} {RH : RecordKernelState → ℤ}
    {cmb compress : ℤ → ℤ → ℤ} {compressN : List ℤ → ℤ}
    {hCmb : compressInjective cmb} {hCompress : compressInjective compress}
    {hCompressN : compressNInjective compressN} {hLeaf : cellLeafInjective CH}
    {hRest : RestHashIffFrame RH}
    {LH : List Turn → ℤ}
    (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : Dregg2.Circuit.DescriptorIR2.VmTrace}
    (hside : Dregg2.Circuit.RotatedKernelRefinement.RotTableSide hash t)
    (hsat : Dregg2.Circuit.DescriptorIR2.Satisfied2 hash
      Dregg2.Circuit.RotatedKernelRefinement.transferV3 minit mfin maddrs t)
    (pre post : RecChainedState) (tr : Dregg2.Exec.Turn) (a : AssetId)
    (pc : PublishedCommit) (pubLogPre pubLogPost : ℤ)
    (hdec : StateDecodeLog
      (S_live CH RH cmb compress compressN hCmb hCompress hCompressN hLeaf hRest) LH
      pc pubLogPre pubLogPost pre post)
    (hpub : pubLogPost = LH (tr :: pre.log))
    (logNeeds : post.log = tr :: pre.log →
      Dregg2.Circuit.RotatedKernelRefinement.rotatedEncodes hash minit mfin maddrs t pre post tr a) :
    kstepAll 0 pre post :=
  have hadv : post.log = tr :: pre.log := logAdvance_forced tr hdec hpub
  closedBridge_of_step (.balanceA tr a) hdec.toDecode (by rfl)
    (Dregg2.Circuit.RotatedKernelRefinement.transfer_descriptorRefines_fullActionStep
      hash hside hsat pre post tr a (logNeeds hadv))

/-! ### §3.2 — RUNG 2: cellSeal (tag 52) → full `CellSealSpec` with the log DERIVED.

`fullActionStep pre (.cellSealA actor cell) post = CellSealSpec pre actor cell post`, whose `.log`
conjunct is `post.log = cellLifecycleReceipt actor cell :: pre.log`. The receipt is the deterministic
`cellLifecycleReceipt actor cell`. -/

/-- **`cellSeal_descriptorRefines_closedLog` — cellSeal CLOSED WITH LOG.** From the kernel+log decode,
the published `cellLifecycleReceipt`-prepend (`pubLogPost = LH (cellLifecycleReceipt actor cell ::
pre.log)`), and the FIX `cellSealGenuineEncodes` MINUS its `logAdv`, conclude `kstepAll 52 pre post` over
the PUBLISHED endpoints with the FULL `CellSealSpec` — its `.log` advance DERIVED from `logBinds`. Floor:
{Poseidon/Merkle CR (`S_live`), `logHashInjective LH`} + the circuit's `cellSealGenuineEncodes`-minus-log
+ the published receipt-prepend. -/
theorem cellSeal_descriptorRefines_closedLog
    {CH : CellId → Value → ℤ} {RH : RecordKernelState → ℤ}
    {cmb compress : ℤ → ℤ → ℤ} {compressN0 : List ℤ → ℤ}
    {hCmb : compressInjective cmb} {hCompress : compressInjective compress}
    {hCompressN : compressNInjective compressN0} {hLeaf : cellLeafInjective CH}
    {hRest : RestHashIffFrame RH}
    {LH : List Turn → ℤ}
    (compressN : List Dregg2.Circuit.RotatedKernelRefinementCellSeal.FieldElem
      → Dregg2.Circuit.RotatedKernelRefinementCellSeal.FieldElem)
    (hN : Dregg2.Circuit.StateCommit.compressNInjective compressN)
    (pre post : RecChainedState) (actor cell : CellId)
    (pc : PublishedCommit) (pubLogPre pubLogPost : ℤ)
    (hdec : StateDecodeLog
      (S_live CH RH cmb compress compressN0 hCmb hCompress hCompressN hLeaf hRest) LH
      pc pubLogPre pubLogPost pre post)
    (hpub : pubLogPost
      = LH (Dregg2.Circuit.Spec.CellLifecycle.cellLifecycleReceipt actor cell :: pre.log))
    (logNeeds : post.log
        = Dregg2.Circuit.Spec.CellLifecycle.cellLifecycleReceipt actor cell :: pre.log →
      Dregg2.Circuit.RotatedKernelRefinementCellSeal.cellSealGenuineEncodes
        compressN pre post actor cell) :
    kstepAll 52 pre post :=
  have hadv : post.log
      = Dregg2.Circuit.Spec.CellLifecycle.cellLifecycleReceipt actor cell :: pre.log :=
    logAdvance_forced _ hdec hpub
  closedBridge_of_step (.cellSealA actor cell) hdec.toDecode (by rfl)
    (by
      show fullActionStep pre (.cellSealA actor cell) post
      simp only [fullActionStep]
      exact Dregg2.Circuit.RotatedKernelRefinementCellSeal.cellSeal_descriptorRefines
        compressN hN pre post actor cell (logNeeds hadv))

/-! ### §3.3 — RUNG 3: revoke (tag 2) → full `RevokeSpec` with the log DERIVED.

`fullActionStep pre (.revoke holder tt) post = RevokeSpec pre holder tt post`, whose `.log` conjunct is
`post.log = authReceipt holder :: pre.log`. The receipt is the deterministic `authReceipt holder`. -/

/-- **`revoke_descriptorRefines_closedLog` — revoke CLOSED WITH LOG.** From the kernel+log decode, the
published `authReceipt`-prepend (`pubLogPost = LH (authReceipt holder :: pre.log)`), and the cap-family
`RevokeCapsTreeEncodes` MINUS its `logAdv`, conclude `kstepAll 2 pre post` over the PUBLISHED endpoints
with the FULL `RevokeSpec` — its `.log` advance DERIVED from `logBinds`. Floor: {Poseidon/Merkle CR
(`S_live`), `logHashInjective LH`} + the circuit's `RevokeCapsTreeEncodes`-minus-log + the published
receipt-prepend. -/
theorem revoke_descriptorRefines_closedLog
    {State : Type} (Scap : Dregg2.Circuit.DeployedCapTree.CapHashScheme State)
    {CH : CellId → Value → ℤ} {RH : RecordKernelState → ℤ}
    {cmb compress : ℤ → ℤ → ℤ} {compressN : List ℤ → ℤ}
    {hCmb : compressInjective cmb} {hCompress : compressInjective compress}
    {hCompressN : compressNInjective compressN} {hLeaf : cellLeafInjective CH}
    {hRest : RestHashIffFrame RH}
    {LH : List Turn → ℤ}
    (pre post : RecChainedState) (holder tt : CellId)
    (pc : PublishedCommit) (pubLogPre pubLogPost : ℤ)
    (hdec : StateDecodeLog
      (S_live CH RH cmb compress compressN hCmb hCompress hCompressN hLeaf hRest) LH
      pc pubLogPre pubLogPost pre post)
    (hpub : pubLogPost = LH (Dregg2.Exec.TurnExecutorFull.authReceipt holder :: pre.log))
    (logNeeds : post.log = Dregg2.Exec.TurnExecutorFull.authReceipt holder :: pre.log →
      Dregg2.Circuit.RotatedKernelRefinementCapFamily.RevokeCapsTreeEncodes
        Scap pre post holder tt) :
    kstepAll 2 pre post :=
  have hadv : post.log = Dregg2.Exec.TurnExecutorFull.authReceipt holder :: pre.log :=
    logAdvance_forced _ hdec hpub
  closedBridge_of_step (.revoke holder tt) hdec.toDecode (by rfl)
    (by
      show fullActionStep pre (.revoke holder tt) post
      simp only [fullActionStep]
      exact Dregg2.Circuit.RotatedKernelRefinementCapFamily.revoke_descriptorRefines
        Scap pre post holder tt (logNeeds hadv))

/-! ## §4 — the carrier ledger + axiom hygiene.

The three closed-with-log rungs carry EXACTLY:
  * the Poseidon/Merkle CR set (`compressInjective cmb/compress`, `compressNInjective compressN`,
    `cellLeafInjective CH`, `RestHashIffFrame RH`) — bundled in `S_live`, the SAME set `ClosureSurface`
    carries (the kernel faithfulness floor);
  * `logHashInjective LH` — the log-CR carrier (in `StateDecodeLog.hLogInj`), now CONSUMED to FORCE the
    `.log` advance (it was un-bound in `ClosureSurface`);
  * the per-effect `<effect>Encodes` MINUS `logAdv` (the `logNeeds` function) — the CIRCUIT, NOT a floor;
  * the published receipt-prepend claim (`pubLogPost = LH (receipt :: pre.log)`) — the PUBLISHED effect
    (the deterministic receipt the descriptor emits), NOT a floor.
The `.log` advance is now INSIDE the realizable `logHashInjective` carrier — there is no longer a free
`logAdv` assertion in any of the three rungs. So the `.log` obstruction is CLOSED for all three grades. -/

#assert_axioms StateDecodeLog
#assert_axioms logAdvance_forced
#assert_axioms transfer_descriptorRefines_closedLog
#assert_axioms cellSeal_descriptorRefines_closedLog
#assert_axioms revoke_descriptorRefines_closedLog

end Dregg2.Circuit.ClosureLog
