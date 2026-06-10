/-
# Dregg2.Circuit.Emit.EffectVmEmitEmitEventWide — the RUNNABLE `emitEventA` descriptor LIFTED to
FULL-STATE (the magnesium breadth, on the circuit the prover RUNS).

## What this module closes (vs the narrow `EffectVmEmitEmitEvent`)

`EffectVmEmitEmitEvent.emitEventVmDescriptor` is the deployed `EFFECT_VM_WIDTH = 186` no-state-move row
(all 14 state-block columns FROZEN — `emitEventA` moves nothing in the kernel) whose published
`state_commit` absorbs ONLY the 13 state-block columns (`absorbedCols`). The `system_roots` sub-block
(escrow / nullifier / commitment / queue / swiss / sealedBox / delegation / refcount) is bound ONLY by a
separate record-layer commitment the row does NOT carry — the dominant Class-C "pale ghost". Its per-cell
soundness `emitEventDescriptor_full_sound` pins the cell's whole block FROZEN (`CellFreezeSpec`), but the
descriptor's commitment leaves the 8 side-table roots unbound.

This module SUPERSEDES that with a verified-by-construction WIDE descriptor `emitEventVmDescriptorWide`
(`EFFECT_VM_WIDTH_SYSROOTS = 188`, `hashSites = wideHashSites`) and the FULL-STATE-on-RUNNABLE crown
`emitEvent_runnable_full_sound` — a satisfying witness of the RUNNABLE descriptor pins the FULL 17-field
declarative post-state the executor produces: the per-cell block FROZEN (via the absorbed columns) AND
ALL 8 side-table roots FROZEN. `emitEventA` is the pure observation-log effect — it freezes the ENTIRE
`RecordKernelState`, so the full clause is the WHOLE-state freeze, and the empty-side-table is bound by
the wide commitment. The analog of the abstract `emitEventA_full_sound`, but for the circuit the prover
ACTUALLY RUNS.

## The recipe applied (`EffectVmFullStateRunnable §6`, the transfer reference template)

  * **the wide descriptor** — `emitEventVmDescriptor` with `traceWidth := EFFECT_VM_WIDTH_SYSROOTS`,
    `hashSites := wideHashSites` (so `usesWideSites := rfl`). Strictly additive: the constraint list is
    byte-identical (`emitEventWide_constraints_eq`); only the width grows by 2 and site 3's spare `.zero`
    4th slot becomes the `system_roots` carrier. NO root-update gate — emit moves NO side table, so the
    carrier is FROZEN at `before`.
  * **`isRow`** := `IsEmitRow`; **`decodeAfter`** := `RowEncodes` + frozen-roots witness; **`fullClause`**
    := `CellFreezeSpec` (the whole block FROZEN) AND `postRoots = preRoots`; **`decodeFull`** := THIN,
    projecting the wide gates (= the narrow's) to the hash-site-free `emitEventGates_give_cellSpec`.

The anti-ghost on ALL 17 fields falls out of the generic `runnable_full_commit_binds` /
`wide_rejects_root_tamper` (§4).

## SURFACE — the log-receipt divergence is UNCHANGED and named.

The full clause pins the WHOLE 17-field kernel post-state (every field FROZEN). The ONE residual —
emit's SOLE motion is the receipt prepended to `RecChainedState.log`, which is NOT a `RecordKernelState`
field and has NO EffectVM row column — is the SAME boundary the narrow header and the Argus
`EmitEvent.lean` weld carry: the log receipt rides universe-A's `logHashInjective` portal, NOT this
per-row state descriptor. This module closes ONLY the side-table-root binding gap on the kernel state.

## The terminal (named, the ONLY acceptable irreducible)

`Poseidon2Binding.Poseidon2SpongeCR hash` — discharged ONCE in the generic crown; this module carries NO
new portal. `#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound} on every theorem. No `sorry`,
no `:= True`, no `native_decide`. Imports are read-only; this file owns only itself.
-/
import Dregg2.Circuit.Emit.EffectVmEmitEmitEvent
import Dregg2.Circuit.Emit.EffectVmFullStateRunnable

namespace Dregg2.Circuit.Emit.EffectVmEmitEmitEventWide

open Dregg2.Circuit
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound (CellState absorbedCols)
open Dregg2.Circuit.Emit.EffectVmEmitEmitEvent
  (IsEmitRow SEL_EMIT_EVENT emitTickRowGates emitEventVmDescriptor EmitTickRowIntent emitTickVm_faithful
   emitTickRowGates_flag_indep RowEncodes EmitTickCellSpec intent_to_tickCellSpec)
open Dregg2.Circuit.Emit.EffectVmFullStateRunnable
  (wideHashSites RunnableFullStateSpec runnable_full_sound)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Exec.SystemRoots (SysRoots systemRootsDigest emptySystemRoots N_SYSTEM_ROOTS)

set_option linter.unusedVariables false

/-! ## §1 — the GATE-ONLY per-cell soundness (no hash-site hypothesis).

The whole-block freeze factors through `emitEventVm_faithful` (`emitRowGates ⟺ EmitRowIntent`) +
`intent_to_cellSpec`, NEITHER of which reads the hash sites. So the runnable per-cell soundness depends
ONLY on the gates (the sites bind the COMMITMENT — §4 — not the per-cell spec). The analog of
`EffectVmFullStateRunnable.transferGates_give_cellSpec`. -/

/-- **`emitEventGates_give_cellSpec` — the GATE-ONLY per-cell soundness.** The narrow descriptor's per-row
gates (a constraint-list segment), on an emit row decoded by `RowEncodesEmit` with `s_noop = 0`, force
`EmitCellSpec` (the economic block FROZEN, the actor nonce TICKS by 1). No hash-site hypothesis. -/
theorem emitEventGates_give_cellSpec (env : VmRowEnv) (pre post : CellState)
    (hnoop : env.loc sel.NOOP = 0)
    (henc : RowEncodes env pre post)
    (hgates : ∀ c ∈ emitEventVmDescriptor.constraints, c.holdsVm env true true) :
    EmitTickCellSpec pre post := by
  have hrowgates : ∀ c ∈ emitTickRowGates, c.holdsVm env true true := by
    intro c hc
    apply hgates
    unfold emitEventVmDescriptor
    simp only [List.mem_append]
    exact Or.inl (Or.inl (Or.inl (Or.inl hc)))
  have hrowgates' := emitTickRowGates_flag_indep env true true hrowgates
  exact intent_to_tickCellSpec env pre post hnoop henc ((emitTickVm_faithful env).mp hrowgates')

#assert_axioms emitEventGates_give_cellSpec

/-! ## §2 — the WIDE descriptor (the `system_roots`-absorbing runnable circuit). -/

/-- **`emitEventVmDescriptorWide`** — `emitEventVmDescriptor` WIDENED: the SAME per-row gates +
transitions + boundary pins, but `traceWidth := EFFECT_VM_WIDTH_SYSROOTS` and `hashSites := wideHashSites`.
Strictly additive over `emitEventVmDescriptor`. -/
def emitEventVmDescriptorWide : EffectVmDescriptor :=
  { emitEventVmDescriptor with
    name := emitEventVmDescriptor.name ++ "-sysroots"
    traceWidth := EFFECT_VM_WIDTH_SYSROOTS
    hashSites := wideHashSites }

/-- The wide emit descriptor's constraints ARE the narrow's. -/
theorem emitEventWide_constraints_eq :
    emitEventVmDescriptorWide.constraints = emitEventVmDescriptor.constraints := rfl

/-! ## §3 — the FULL clause + the VALIDATED RUNNABLE instance.

`emitEventA` touches NO side-table (and no kernel field at all), so its `system_roots` sub-block is FROZEN:
the full clause is the per-cell `CellFreezeSpec` (the whole block frozen) AND `postRoots = preRoots`. -/

/-- **`EmitEventFullClause`** — the full declarative post-state for the emit over `(pre, post, postRoots)`:
the per-cell `EmitCellSpec` (the economic block FROZEN, the actor nonce TICKS by 1) AND the 8 side-table
roots FROZEN. Non-vacuous (`goodEmitEvent_realizes` / `emitEvent_clause_not_trivial`). -/
def EmitEventFullClause (preRoots : SysRoots)
    (pre post : CellState) (postRoots : SysRoots) : Prop :=
  EmitTickCellSpec pre post ∧ postRoots = preRoots

/-- **`emitEventRunnableSpec` — the FULL-state RUNNABLE instance.** `decodeFull` projects the wide gates to
the GATE-ONLY `emitEventGates_give_cellSpec` (extracting `s_noop = 0` from the emit-row hypothesis), then
carries the frozen-roots fact. THIN, NON-VACUOUS. -/
def emitEventRunnableSpec (preRoots : SysRoots) : RunnableFullStateSpec CellState where
  descriptor    := emitEventVmDescriptorWide
  usesWideSites := rfl
  isRow         := IsEmitRow
  decodeAfter   := fun env pre post postRoots =>
    RowEncodes env pre post ∧ postRoots = preRoots
  fullClause    := EmitEventFullClause preRoots
  decodeFull    := by
    intro env pre post postRoots hrow hdec hgates
    obtain ⟨henc, hroots⟩ := hdec
    exact ⟨emitEventGates_give_cellSpec env pre post hrow.2 henc
            (emitEventWide_constraints_eq ▸ hgates), hroots⟩

/-- **`emitEvent_runnable_full_sound` — THE CROWN (emitEvent slice).** A row satisfying the RUNNABLE wide
descriptor (`satisfiedVm emitEventVmDescriptorWide`, first/last active), under the structured decode
(`RowEncodesEmit` + frozen roots), pins the FULL 17-field declarative post-state: the per-cell
`EmitCellSpec` (the economic block FROZEN, the actor nonce TICKED) AND all 8 side-table roots FROZEN. The
analog of the abstract `emitEventA_full_sound`, but for the circuit the prover ACTUALLY RUNS (reconciled
onto the runtime nonce-TICK convention). -/
theorem emitEvent_runnable_full_sound (hash : List ℤ → ℤ)
    (env : VmRowEnv) (pre post : CellState) (sr preRoots : SysRoots)
    (hrow : IsEmitRow env)
    (henc : RowEncodes env pre post) (hroots : sr = preRoots)
    (hsat : satisfiedVm hash emitEventVmDescriptorWide env true true) :
    EmitTickCellSpec pre post ∧ sr = preRoots :=
  runnable_full_sound (emitEventRunnableSpec preRoots) hash env pre post sr
    hrow ⟨henc, hroots⟩ hsat

#assert_axioms emitEvent_runnable_full_sound

/-! ## §4 — ANTI-GHOST on ALL 17 fields (the generic teeth, instantiated). -/

/-- **`emitEvent_wide_binds_full_state` — the whole-state anti-ghost.** Two rows satisfying the wide
descriptor that publish the SAME `NEW_COMMIT`, whose carriers ARE the `systemRootsDigest` of their post
sub-blocks, agree on EVERY absorbed state-block column AND every side-table root. -/
theorem emitEvent_wide_binds_full_state (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (e₁ e₂ : VmRowEnv) (sr₁ sr₂ : SysRoots) (preRoots : SysRoots)
    (hsat₁ : satisfiedVm hash emitEventVmDescriptorWide e₁ true true)
    (hsat₂ : satisfiedVm hash emitEventVmDescriptorWide e₂ true true)
    (hpin₁ : e₁.loc (saCol state.STATE_COMMIT) = e₁.pub pi.NEW_COMMIT)
    (hpin₂ : e₂.loc (saCol state.STATE_COMMIT) = e₂.pub pi.NEW_COMMIT)
    (hpub : e₁.pub pi.NEW_COMMIT = e₂.pub pi.NEW_COMMIT)
    (hd₁ : e₁.loc sysRootsDigestCol = systemRootsDigest hash sr₁)
    (hd₂ : e₂.loc sysRootsDigestCol = systemRootsDigest hash sr₂) :
    absorbedCols e₁ = absorbedCols e₂ ∧ (∀ i : Fin N_SYSTEM_ROOTS, sr₁ i = sr₂ i) :=
  EffectVmFullStateRunnable.runnable_full_commit_binds (emitEventRunnableSpec preRoots)
    hash hCR e₁ e₂ sr₁ sr₂ hsat₁ hsat₂ hpin₁ hpin₂ hpub hd₁ hd₂

/-- **`emitEvent_wide_rejects_root_tamper` — side-table anti-ghost.** Two wide rows publishing the same
`NEW_COMMIT` (with `systemRootsDigest` carriers) whose side-table sub-blocks DIFFER cannot both satisfy. -/
theorem emitEvent_wide_rejects_root_tamper (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (e₁ e₂ : VmRowEnv) (sr₁ sr₂ : SysRoots) (preRoots : SysRoots)
    (hsat₁ : satisfiedVm hash emitEventVmDescriptorWide e₁ true true)
    (hsat₂ : satisfiedVm hash emitEventVmDescriptorWide e₂ true true)
    (hpin₁ : e₁.loc (saCol state.STATE_COMMIT) = e₁.pub pi.NEW_COMMIT)
    (hpin₂ : e₂.loc (saCol state.STATE_COMMIT) = e₂.pub pi.NEW_COMMIT)
    (hpub : e₁.pub pi.NEW_COMMIT = e₂.pub pi.NEW_COMMIT)
    (hd₁ : e₁.loc sysRootsDigestCol = systemRootsDigest hash sr₁)
    (hd₂ : e₂.loc sysRootsDigestCol = systemRootsDigest hash sr₂)
    {i : Fin N_SYSTEM_ROOTS} (htamper : sr₁ i ≠ sr₂ i) : False :=
  EffectVmFullStateRunnable.wide_rejects_root_tamper (emitEventRunnableSpec preRoots)
    hash hCR e₁ e₂ sr₁ sr₂ hsat₁ hsat₂ hpin₁ hpin₂ hpub hd₁ hd₂ htamper

#assert_axioms emitEvent_wide_binds_full_state
#assert_axioms emitEvent_wide_rejects_root_tamper

/-! ## §5 — NON-VACUITY: the full clause is INHABITED (TRUE) and REFUTABLE (FALSE), and the wide
descriptor is the genuine 188-wide `system_roots`-absorbing circuit. -/

/-- A frozen reference sub-block (the empty `system_roots`, since emit touches no side table). -/
def goodPreRoots : SysRoots := emptySystemRoots

/-- A content-rich pre-state for the witnesses: bal_lo 100, nonce 5, field[3] = 9. -/
def emitPre : CellState :=
  { balLo := 100, balHi := 0, nonce := 5, fields := fun i => if i = 3 then 9 else 0, capRoot := 0
  , reserved := 0, commit := 0 }

/-- The post-state emit produces: the economic block frozen (= `emitPre`) with the actor nonce TICKED
(5 → 6). -/
def emitPost : CellState := { emitPre with nonce := 6 }

/-- **`goodEmitEvent_realizes` — NON-VACUITY (witness TRUE).** The emit `fullClause` is INHABITED by a
real emit: `emitPost`'s economic block IS `emitPre`'s (every economic component FROZEN — emit moves nothing
in the kernel) with the actor nonce ticked (`6 = 5 + 1`), and the roots are frozen. So the full clause is
NOT `True`. -/
theorem goodEmitEvent_realizes :
    (emitEventRunnableSpec goodPreRoots).fullClause emitPre emitPost goodPreRoots :=
  ⟨⟨rfl, rfl, by simp only [emitPre, emitPost]; norm_num, fun _ => rfl, rfl, rfl⟩, rfl⟩

/-- **`emitEvent_clause_not_trivial` — the clause is REFUTABLE (witness FALSE).** A post-state whose bal_lo
is NOT frozen (`emitPre.balLo = 100`, but a forged `999`) FAILS the full clause — non-vacuity from BOTH
sides. -/
theorem emitEvent_clause_not_trivial :
    ¬ EmitEventFullClause goodPreRoots emitPre { emitPost with balLo := 999 } goodPreRoots := by
  rintro ⟨⟨hbal, _⟩, _⟩
  -- hbal : (999) = emitPost.balLo = emitPre.balLo = 100
  simp only [emitPre, emitPost] at hbal
  norm_num at hbal

/-- **NON-VACUITY (the wide descriptor is the genuine 188-wide circuit).** `emitEventVmDescriptorWide`
declares `traceWidth = 188` and its `hashSites` are EXACTLY the four `system_roots`-absorbing
`wideHashSites`. -/
theorem emitEventWide_is_genuine :
    emitEventVmDescriptorWide.traceWidth = EFFECT_VM_WIDTH_SYSROOTS
    ∧ emitEventVmDescriptorWide.hashSites = wideHashSites
    ∧ emitEventVmDescriptorWide.hashSites.length = 4 := by
  refine ⟨rfl, rfl, ?_⟩
  show wideHashSites.length = 4
  decide

#assert_axioms goodEmitEvent_realizes
#assert_axioms emitEvent_clause_not_trivial
#assert_axioms emitEventWide_is_genuine

/-! ## §6 — axiom-hygiene tripwires. -/

#guard emitEventVmDescriptorWide.traceWidth == 188
#guard emitEventVmDescriptorWide.hashSites.length == 4
#guard emitEventVmDescriptorWide.constraints.length == 13 + 14 + 4 + 3 + 1

end Dregg2.Circuit.Emit.EffectVmEmitEmitEventWide
