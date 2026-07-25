/-
# Dregg2.Circuit.Emit.EffectVmEmitEmitEventWide — the RUNNABLE `emitEventA` descriptor LIFTED to
FULL-STATE (the magnesium breadth, on the circuit the prover RUNS).

## What this module closes (vs the narrow `EffectVmEmitEmitEvent`)

`EffectVmEmitEmitEvent.emitEventVmDescriptor` is the deployed `EFFECT_VM_WIDTH = 186` no-state-move row
(all 14 state-block columns FROZEN — `emitEventA` moves nothing in the kernel) whose published
`state_commit` absorbs ONLY the 13 state-block columns (`baseAbsorbedCols`). The `system_roots` sub-block
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

The anti-ghost on ALL 17 fields falls out of the generic `runnable_full_commit_binds_or_collides` /
`wide_rejects_root_tamper_or_collides` (§4).

## SURFACE — the log-receipt divergence is UNCHANGED and named.

The full clause pins the WHOLE 17-field kernel post-state (every field FROZEN). The ONE residual —
emit's SOLE motion is the receipt prepended to `RecChainedState.log`, which is NOT a `RecordKernelState`
field and has NO EffectVM row column — is the SAME boundary the narrow header and the Argus
`EmitEvent.lean` weld carry: the log receipt rides universe-A's `logHashInjective` portal, NOT this
per-row state descriptor. This module closes ONLY the side-table-root binding gap on the kernel state.

## The sponge terminal (named, and no longer assumed)

The anti-ghost theorems carry NO collision-resistance hypothesis. Where the old forms assumed
`Poseidon2Binding.Poseidon2SpongeCR hash` — which the deployed compressing sponge REFUTES — the §4
theorems conclude a disjunction whose right side NAMES the colliding pair (`WideColl` / `RootsColl`).
`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound} on every theorem.
Imports are read-only; this file owns only itself.
-/
import Dregg2.Circuit.Emit.EffectVmEmitEmitEvent
import Dregg2.Circuit.Emit.EffectVmFullStateRunnable
import Dregg2.Circuit.Emit.EffectVmRowCommitReduction

namespace Dregg2.Circuit.Emit.EffectVmEmitEmitEventWide

open Dregg2.Circuit
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound (CellState)
open Dregg2.Circuit.Emit.EffectVmEmitEmitEvent
  (IsEmitRow SEL_EMIT_EVENT emitTickRowGates emitEventVmDescriptor EmitTickRowIntent emitTickVm_faithful
   emitTickRowGates_flag_indep RowEncodes EmitTickCellSpec intent_to_tickCellSpec)
open Dregg2.Circuit.Emit.EffectVmFullStateRunnable
  (baseAbsorbedCols wideHashSites RunnableFullStateSpec runnable_full_sound WideColl RootsColl)
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
    (hgates : ∀ c ∈ emitEventVmDescriptor.constraints, c.holdsVm env true false) :
    EmitTickCellSpec pre post := by
  have hrowgates : ∀ c ∈ emitTickRowGates, c.holdsVm env true false := by
    intro c hc
    apply hgates
    unfold emitEventVmDescriptor
    simp only [List.mem_append]
    exact Or.inl (Or.inl (Or.inl (Or.inl hc)))
  have hrowgates' := emitTickRowGates_flag_indep env true hrowgates
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
    (hgatesat : satisfiedVm hash emitEventVmDescriptorWide env true false) :
    EmitTickCellSpec pre post ∧ sr = preRoots :=
  runnable_full_sound (emitEventRunnableSpec preRoots) hash env pre post sr
    hrow ⟨henc, hroots⟩ hgatesat

#assert_axioms emitEvent_runnable_full_sound

/-! ## §4 — ANTI-GHOST on ALL 17 fields (the generic teeth, instantiated). -/

/-- ⚑ **WHAT CHANGED AND WHY (the reduction that replaces the deleted disjunctions).** This section
used to export `emitEvent_wide_binds_full_state_or_collides` / `emitEvent_wide_rejects_root_tamper_or_collides`, each concluding
`… ∨ WideColl hash e₁ e₂ ∨ RootsColl hash sr₁ sr₂`. Those forms are TRUE of the deployed sponge —
unlike the `Poseidon2SpongeCR` predecessors, which it REFUTES — but they are UNCLOSED: a collision
of the deployed sponge EXISTS at BabyBear parameters by pigeonhole
(`HashFloorHonesty.poseidon2SpongeCR_false_babyBear`), so `binds ∨ collides` is satisfiable through
its RIGHT branch WITHOUT the binding ever holding. They quantify over SOLUTIONS; cryptographic
hardness quantifies over EFFICIENT ADVERSARIES. They are DELETED and rebuilt on
`Emit.EffectVmRowCommitReduction`, exactly as `EffectVmEmitMintRunnable` §4: the forgery is a
first-class `Game` at emitEvent's OWN wide descriptor, the extractor is a MAP OF ADVERSARIES (the
reduction-internal witness), and the conclusions are (a) negligibility under the DEPLOYED sponge's
collision floor `HashCRHardQuant (spongeFamily D) Eff`, `hEff` in the open, both poles priced
(`rowCommitFloor_top_false_babyBear` / `_bot_vacuous`), and (b) the DISCHARGED keyed-ROM forms on
the PROVED birthday floor (`keyedRom_hard`) — NO floor hypothesis — in the LABELLED random-oracle
model of `EffectVmRowCommitReduction` §5's header (the sampled `Fin (2 ^ l)` digest is the
modelling step; no `l` is the deployed ~31-bit felt). The ROM commitment layer carries no
descriptor (the nested absorb schedule is one object across effects); emitEvent's per-effect circuit
content (`satisfiedVm` at `emitEventVmDescriptorWide`) lives in the `_advantage_bound` forms. -/
def emitEventWideRowSpec : Dregg2.Circuit.Emit.EffectVmRowCommitReduction.WideRowSpec where
  descriptor := emitEventVmDescriptorWide
  usesWideSites := rfl

open Dregg2.Crypto.SpongeCarrierReduction (SpongeKeyed spongeFamily carrierBreakToFinder) in
open Dregg2.Circuit.Emit.EffectVmRowCommitReduction in
open Dregg2.Crypto.FloorGames (Adversary gameAdv hashGame HashCRHardQuant) in
open Dregg2.Crypto.ConcreteSecurity (Negl) in
/-- **⚑ `emitEvent_wide_binds_full_state_advantage_bound` — THE REDUCED WHOLE-17-FIELD BINDING for
emitEvent.** Under the DEPLOYED sponge's collision floor at the class `Eff`, an adversary producing
two rows BOTH SATISFYING `emitEventVmDescriptorWide`, publishing one `NEW_COMMIT` with genuine `systemRootsDigest`
carriers, yet binding DIFFERENT state (an absorbed column or a side-table root), has NEGLIGIBLE
advantage. Replaces the deleted bare disjunction. -/
theorem emitEvent_wide_binds_full_state_advantage_bound (D : SpongeKeyed)
    (Eff : Adversary (hashGame (spongeFamily D)) → Prop)
    (A : Adversary (wideRowBreakGame D emitEventWideRowSpec))
    (hEff : Eff (carrierBreakToFinder D wideStateCarrier
      (wideRowToCarrier D emitEventWideRowSpec A)))
    (hCR : HashCRHardQuant (spongeFamily D) Eff) :
    Negl (gameAdv (wideRowBreakGame D emitEventWideRowSpec) A) :=
  wideRow_binds_advantage_bound D emitEventWideRowSpec Eff A hEff hCR

open Dregg2.Crypto.SpongeCarrierReduction (SpongeKeyed) in
open Dregg2.Circuit.Emit.EffectVmRowCommitReduction in
open Dregg2.Crypto.RomCarrierSites (RomForgeryEff) in
open Dregg2.Crypto.FloorGames (Adversary gameAdv) in
open Dregg2.Crypto.ConcreteSecurity (Negl PolyBounded) in
/-- **⚑⚑ `emitEvent_wide_binds_full_state_rom` — the DISCHARGED whole-17-field binding, on the PROVED
floor.** A query-bounded forger of the wide nested `state_commit` — the very commitment emitEvent's
wide row publishes — has NEGLIGIBLE advantage, in the keyed ROM model of
`EffectVmRowCommitReduction` §5's header. NO floor hypothesis. The COMMITMENT layer carries no
descriptor, so this is `wideRow_binds_rom` at the deployed tag space; emitEvent's per-effect circuit
content stays in the `_advantage_bound` form above, `hEff` in the open. -/
theorem emitEvent_wide_binds_full_state_rom (D : SpongeKeyed) (tagDec : DecidableEq D.Tag)
    (Q : ℕ → ℕ) (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (A : Adversary (wideRomBreakGame D tagDec))
    (hA : RomForgeryEff (wideRomFamily D tagDec) (effectVmWideRomForgery D tagDec) Q A) :
    Negl (gameAdv (wideRomBreakGame D tagDec) A) :=
  wideRow_binds_rom D tagDec Q hQ A hA

open Dregg2.Crypto.SpongeCarrierReduction (SpongeKeyed spongeFamily carrierBreakToFinder) in
open Dregg2.Circuit.Emit.EffectVmRowCommitReduction in
open Dregg2.Crypto.FloorGames (Adversary gameAdv hashGame HashCRHardQuant) in
open Dregg2.Crypto.ConcreteSecurity (Negl) in
/-- **⚑ `emitEvent_wide_rejects_root_tamper_advantage_bound` — the side-table anti-ghost, REDUCED.** An
efficient adversary cannot keep the published `NEW_COMMIT` while tampering a side-table root of a
satisfying wide emitEvent row (a dropped escrow, an omitted nullifier, a reordered queue), except
with negligible probability. Replaces the deleted `emitEvent_wide_rejects_root_tamper_or_collides`. -/
theorem emitEvent_wide_rejects_root_tamper_advantage_bound (D : SpongeKeyed)
    (Eff : Adversary (hashGame (spongeFamily D)) → Prop)
    (A : Adversary (wideRootTamperGame D emitEventWideRowSpec))
    (hEff : Eff (carrierBreakToFinder D wideStateCarrier
      (wideRowToCarrier D emitEventWideRowSpec (rootTamperToWide D emitEventWideRowSpec A))))
    (hCR : HashCRHardQuant (spongeFamily D) Eff) :
    Negl (gameAdv (wideRootTamperGame D emitEventWideRowSpec) A) :=
  wide_root_tamper_advantage_bound D emitEventWideRowSpec Eff A hEff hCR

open Dregg2.Crypto.SpongeCarrierReduction (SpongeKeyed) in
open Dregg2.Circuit.Emit.EffectVmRowCommitReduction in
open Dregg2.Crypto.RomCarrierSites (RomForgeryEff) in
open Dregg2.Crypto.FloorGames (Adversary gameAdv) in
open Dregg2.Crypto.ConcreteSecurity (Negl PolyBounded) in
/-- **⚑ `emitEvent_wide_rejects_root_tamper_rom`** — the same tooth DISCHARGED on the PROVED floor: a
query-bounded adversary cannot keep the published nested commitment while tampering a side-table
root. -/
theorem emitEvent_wide_rejects_root_tamper_rom (D : SpongeKeyed) (tagDec : DecidableEq D.Tag)
    (Q : ℕ → ℕ) (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (A : Adversary (effectVmWideRomRootTamper D tagDec).game)
    (hA : RomForgeryEff (wideRomFamily D tagDec) (effectVmWideRomRootTamper D tagDec) Q A) :
    Negl (gameAdv (effectVmWideRomRootTamper D tagDec).game A) :=
  wide_root_tamper_rom D tagDec Q hQ A hA

#assert_axioms emitEvent_wide_binds_full_state_advantage_bound
#assert_axioms emitEvent_wide_binds_full_state_rom
#assert_axioms emitEvent_wide_rejects_root_tamper_advantage_bound
#assert_axioms emitEvent_wide_rejects_root_tamper_rom

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

#guard emitEventVmDescriptorWide.traceWidth == 190
#guard emitEventVmDescriptorWide.hashSites.length == 4
#guard emitEventVmDescriptorWide.constraints.length == 13 + 14 + 4 + 3 + 1

end Dregg2.Circuit.Emit.EffectVmEmitEmitEventWide
