/-
# Dregg2.Circuit.Argus.Effects.Burn — the SUPPLY-BURN effect's FULL-STATE-on-RUNNABLE welded into Argus.

`burnA`'s per-cell EffectVM soundness (`EffectVmEmitBurn.burnDescriptor_full_sound`) and its Argus weld
(`Argus/Compile.lean`, `compileE .burn = burnVmDescriptor`) already stand. `EffectVmEmitBurnRunnable`
amplified the per-cell soundness to FULL-state on the RUNNABLE descriptor via the validated recipe
(`burnVmDescriptorWide` + the generic `runnable_full_sound`): a satisfying wide burn row pins all 17
RecordKernelState fields (the per-cell debit + frame freeze AND the 8 side-table roots frozen), with the
anti-ghost on every column/root (`burn_rejects_state_tamper`/`burn_rejects_root_tamper`).

This module welds that full-state-on-RUNNABLE result into the Argus library (so the coherence anchor
`Dregg2.Circuit.Argus` carries it), re-exporting the deliverable under the Argus effect namespace. It owns
only its own declarations and imports the audited runnable module read-only.

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; the sole crypto carrier is the NAMED
`Poseidon2SpongeCR` portal (inside the reused generic theorem). No `sorry` / `:= True` / `native_decide`.
-/
import Dregg2.Circuit.Emit.EffectVmEmitBurnRunnable

namespace Dregg2.Circuit.Argus.Effects.Burn

open Dregg2.Circuit.Emit.EffectVmEmit (VmRowEnv satisfiedVm)
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound (CellState)
open Dregg2.Circuit.Emit.EffectVmEmitBurn (CellBurnSpec RowEncodes IsBurnRow)
open Dregg2.Circuit.Emit.EffectVmEmitBurnRunnable
  (burnVmDescriptorWide burn_runnable_full_sound)
open Dregg2.Exec.SystemRoots (SysRoots)

/-- **`burn_full_state_on_runnable` — the Argus-welded deliverable.** A row satisfying the RUNNABLE wide
burn descriptor `burnVmDescriptorWide` (the circuit the EffectVM prover runs), under the structured decode,
pins the FULL 17-field declarative post-state: the per-cell `CellBurnSpec` (balance debited by `amt`, the
frame frozen, runtime nonce ticked) AND the 8 side-table roots FROZEN. The genuine full-state soundness
lives in `EffectVmEmitBurnRunnable.burn_runnable_full_sound`; this names it under the Argus effect namespace
so the coherence anchor carries it. -/
theorem burn_full_state_on_runnable (amt : ℤ) (preRoots : SysRoots) (hash : List ℤ → ℤ)
    (env : VmRowEnv) (pre post : CellState) (postRoots : SysRoots)
    (hrow : IsBurnRow env)
    (henc : RowEncodes env pre amt post)
    (hroots : postRoots = preRoots)
    (hsat : satisfiedVm hash burnVmDescriptorWide env true true) :
    CellBurnSpec pre amt post ∧ postRoots = preRoots :=
  burn_runnable_full_sound amt preRoots hash env pre post postRoots hrow henc hroots hsat

#assert_axioms burn_full_state_on_runnable

end Dregg2.Circuit.Argus.Effects.Burn
