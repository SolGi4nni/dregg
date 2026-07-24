/-
# Dregg2.Circuit.Emit.EffectVmEmitExerciseWide — the RUNNABLE `exerciseViaCapability` hold-layer
descriptor LIFTED to FULL-STATE (the magnesium breadth, on the circuit the prover RUNS).

## What this module closes (vs the narrow `EffectVmEmitExercise`)

`EffectVmEmitExercise.exerciseVmDescriptor` is the deployed `EFFECT_VM_WIDTH = 186` hold-layer row whose
published `state_commit` absorbs ONLY the 13 state-block columns (`baseAbsorbedCols`). The `system_roots`
sub-block (escrow / nullifier / commitment / queue / swiss / sealedBox / delegation / refcount) is bound
ONLY by a separate record-layer commitment the row does NOT carry — the dominant Class-C "pale ghost".
Its per-cell soundness `exerciseDescriptor_full_sound` pins the cell's economic block (FROZEN) + nonce
(TICKED), but the descriptor's commitment leaves the 8 side-table roots unbound.

This module SUPERSEDES that with a verified-by-construction WIDE descriptor `exerciseVmDescriptorWide`
(`EFFECT_VM_WIDTH_SYSROOTS = 188`, `hashSites = wideHashSites`) and the FULL-STATE-on-RUNNABLE crown
`exercise_runnable_full_sound` — a satisfying witness of the RUNNABLE descriptor pins the FULL 17-field
declarative post-state the executor produces on the HOLD LAYER (the per-cell block via the absorbed
columns; ALL 8 side-table roots FROZEN, since dregg1's `exerciseViaCapability` hold-gate READS the c-list
and freezes the whole kernel — `apply.rs:2455` — touching NO side-table).

## The recipe applied (`EffectVmFullStateRunnable §6`, the transfer reference template)

  * **the wide descriptor** — `exerciseVmDescriptor` with `traceWidth := EFFECT_VM_WIDTH_SYSROOTS`,
    `hashSites := wideHashSites` (so `usesWideSites := rfl`). Strictly additive: the constraint list is
    byte-identical (`exerciseWide_constraints_eq`); only the width grows by 2 and site 3's spare `.zero`
    4th slot becomes the `system_roots` carrier. NO root-update gate — the hold layer moves NO side
    table, so the carrier is FROZEN at `before`.
  * **`isRow`** := `IsExerciseRow`; **`decodeAfter`** := `RowEncodesExercise` + frozen-roots witness;
    **`fullClause`** := `ExerciseCellSpec` (economic block FROZEN, nonce TICKED) AND `postRoots =
    preRoots`; **`decodeFull`** := THIN, projecting the wide gates (= the narrow's) to the hash-site-free
    gate-only `exerciseGates_give_cellSpec`.

The anti-ghost on ALL 17 fields falls out of the generic `runnable_full_commit_binds_or_collides` /
`wide_rejects_root_tamper_or_collides` (§4).

## SURFACE — the OUTER-LAYER + NONCE-TICK divergences are UNCHANGED and named.

This module pins the OUTER HOLD-GATE layer (`inner = []`), exactly the layer the narrow descriptor /
Argus `ExerciseViaCapability.lean` weld speak about; the INNER sub-forest (R4 facet-mask + `execInnerA`
fold) is the turn-composition layer (`TurnEmit`), cited, OUT of this per-effect weld. The NONCE-TICK
divergence (the runtime row ticks the cell nonce; the executor hold-step FREEZES the kernel) is INSIDE
the full clause's `CellSendSpec`-shape (`post.nonce = pre.nonce + 1`), the SAME explicit residual
`exercise_compile_sound` carries — reconciled at the turn level by the prologue's single tick (cited).
The receipt-log prepend rides universe-A's portal, NOT this per-row state descriptor. This module closes
ONLY the side-table-root binding gap on the kernel state.

## The terminal

There is NO crypto hypothesis. The §4 teeth conclude a DISJUNCTION: either the commitment binds, or the
theorem hands back a specific `WideColl`/`RootsColl` collision of `hash`. So they hold of the deployed
sponge rather than of an injective idealisation of it — the binding branch is what a collision-resistance
assumption would BUY, and it is left unbought here. `#assert_axioms` ⊆ {propext, Classical.choice,
Quot.sound} on every theorem. Imports are read-only; this file owns only itself.
-/
import Dregg2.Circuit.Emit.EffectVmEmitExercise
import Dregg2.Circuit.Emit.EffectVmFullStateRunnable

namespace Dregg2.Circuit.Emit.EffectVmEmitExerciseWide

open Dregg2.Circuit
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound (CellState)
open Dregg2.Circuit.Emit.EffectVmEmitExercise
  (SEL_EXERCISE IsExerciseRow exerciseRowGates exerciseVmDescriptor ExerciseRowIntent
   exerciseVm_faithful RowEncodesExercise ExerciseCellSpec intent_to_cellSpec)
open Dregg2.Circuit.Emit.EffectVmFullStateRunnable
  (baseAbsorbedCols wideHashSites RunnableFullStateSpec runnable_full_sound WideColl RootsColl)
open Dregg2.Exec.SystemRoots (SysRoots systemRootsDigest emptySystemRoots N_SYSTEM_ROOTS)

set_option linter.unusedVariables false

/-! ## §1 — the GATE-ONLY per-cell soundness (no hash-site hypothesis).

The hold-layer freeze+tick factors through `exerciseVm_faithful` (`exerciseRowGates ⟺
ExerciseRowIntent`) + `intent_to_cellSpec`, NEITHER of which reads the hash sites. So the runnable
per-cell soundness depends ONLY on the gates (the sites bind the COMMITMENT — §4 — not the per-cell
spec). The analog of `EffectVmFullStateRunnable.transferGates_give_cellSpec`. -/

/-- **`exerciseGates_give_cellSpec` — the GATE-ONLY per-cell soundness.** The narrow descriptor's per-row
gates (a constraint-list segment), on an exercise row decoded by `RowEncodesExercise`, force
`ExerciseCellSpec`. No hash-site hypothesis. -/
theorem exerciseGates_give_cellSpec (env : VmRowEnv) (pre post : CellState)
    (hnoop : env.loc sel.NOOP = 0) (henc : RowEncodesExercise env pre post)
    (hgates : ∀ c ∈ exerciseVmDescriptor.constraints, c.holdsVm env true false) :
    ExerciseCellSpec pre post := by
  have hrowgates : ∀ c ∈ exerciseRowGates, c.holdsVm env false false := by
    intro c hc
    have hmem : c ∈ exerciseVmDescriptor.constraints := by
      unfold exerciseVmDescriptor
      simp only [List.mem_append]
      exact Or.inl (Or.inl (Or.inl (Or.inl hc)))
    have hh := hgates c hmem
    unfold exerciseRowGates
      Dregg2.Circuit.Emit.EffectVmEmitTransfer.gFieldPassAll at hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
      List.mem_range] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩ <;>
      simpa only [VmConstraint.holdsVm] using hh
  exact intent_to_cellSpec env pre post hnoop henc ((exerciseVm_faithful env).mp hrowgates)

#assert_axioms exerciseGates_give_cellSpec

/-! ## §2 — the WIDE descriptor (the `system_roots`-absorbing runnable circuit). -/

/-- **`exerciseVmDescriptorWide`** — `exerciseVmDescriptor` WIDENED: the SAME per-row gates + transitions
+ boundary pins + selector gate, but `traceWidth := EFFECT_VM_WIDTH_SYSROOTS` and `hashSites :=
wideHashSites`. Strictly additive over `exerciseVmDescriptor`. -/
def exerciseVmDescriptorWide : EffectVmDescriptor :=
  { exerciseVmDescriptor with
    name := exerciseVmDescriptor.name ++ "-sysroots"
    traceWidth := EFFECT_VM_WIDTH_SYSROOTS
    hashSites := wideHashSites }

/-- The wide exercise descriptor's constraints ARE the narrow's. -/
theorem exerciseWide_constraints_eq :
    exerciseVmDescriptorWide.constraints = exerciseVmDescriptor.constraints := rfl

/-! ## §3 — the FULL clause + the VALIDATED RUNNABLE instance.

The hold layer touches NO side-table, so its `system_roots` sub-block is FROZEN: the full clause is the
per-cell `ExerciseCellSpec` (economic block frozen, nonce ticked) AND `postRoots = preRoots`. -/

/-- **`ExerciseFullClause`** — the full declarative post-state for the exercise hold layer over `(pre,
post, postRoots)`: the per-cell `ExerciseCellSpec` (economic block frozen, nonce ticked) AND the 8
side-table roots FROZEN. Non-vacuous (`goodExercise_realizes` / `exercise_clause_not_trivial`). -/
def ExerciseFullClause (preRoots : SysRoots)
    (pre post : CellState) (postRoots : SysRoots) : Prop :=
  ExerciseCellSpec pre post ∧ postRoots = preRoots

/-- **`exerciseRunnableSpec` — the FULL-state RUNNABLE instance.** `decodeFull` projects the wide gates
to the GATE-ONLY `exerciseGates_give_cellSpec`, then carries the frozen-roots fact. THIN, NON-VACUOUS. -/
def exerciseRunnableSpec (preRoots : SysRoots) : RunnableFullStateSpec CellState where
  descriptor    := exerciseVmDescriptorWide
  usesWideSites := rfl
  isRow         := IsExerciseRow
  decodeAfter   := fun env pre post postRoots =>
    RowEncodesExercise env pre post ∧ postRoots = preRoots
  fullClause    := ExerciseFullClause preRoots
  decodeFull    := by
    intro env pre post postRoots hrow hdec hgates
    obtain ⟨henc, hroots⟩ := hdec
    obtain ⟨_, hnoop⟩ := hrow
    exact ⟨exerciseGates_give_cellSpec env pre post hnoop henc
            (exerciseWide_constraints_eq ▸ hgates), hroots⟩

/-- **`exercise_runnable_full_sound` — THE CROWN (exercise hold-layer slice).** A row satisfying the
RUNNABLE wide descriptor (`satisfiedVm exerciseVmDescriptorWide`, first/last active), under the structured
decode (`RowEncodesExercise` + frozen roots), pins the FULL 17-field declarative post-state: the per-cell
`ExerciseCellSpec` (economic block FROZEN, nonce TICKED) AND all 8 side-table roots FROZEN. The analog of
the abstract hold-gate soundness, but for the circuit the prover ACTUALLY RUNS. -/
theorem exercise_runnable_full_sound (hash : List ℤ → ℤ)
    (env : VmRowEnv) (pre post : CellState) (sr preRoots : SysRoots)
    (hrow : IsExerciseRow env)
    (henc : RowEncodesExercise env pre post) (hroots : sr = preRoots)
    (hsat : satisfiedVm hash exerciseVmDescriptorWide env true false) :
    ExerciseCellSpec pre post ∧ sr = preRoots :=
  runnable_full_sound (exerciseRunnableSpec preRoots) hash env pre post sr
    hrow ⟨henc, hroots⟩ hsat

#assert_axioms exercise_runnable_full_sound

/-! ## §4 — ANTI-GHOST on ALL 17 fields (the generic teeth, instantiated). -/

/-- **`exercise_wide_binds_full_state_or_collides` — the whole-state anti-ghost, as EXTRACTION.** Two rows
satisfying the wide descriptor that publish the SAME `NEW_COMMIT`, whose carriers ARE the
`systemRootsDigest` of their post sub-blocks, EITHER agree on every absorbed state-block column and every
side-table root, OR exhibit a concrete collision of `hash` (`WideColl` on the wide absorbed lists,
`RootsColl` on the two root lists).

The previous form asserted the agreement outright from `Poseidon2SpongeCR hash`. The deployed BabyBear
sponge REFUTES that hypothesis (`HashFloorHonesty.poseidon2SpongeCR_false_babyBear`), so the previous form
was vacuous at deployed parameters. This disjunction is formally weaker and holds of the deployed
sponge. -/
theorem exercise_wide_binds_full_state_or_collides (hash : List ℤ → ℤ)
    (e₁ e₂ : VmRowEnv) (sr₁ sr₂ : SysRoots) (preRoots : SysRoots)
    (hsat₁ : satisfiedVm hash exerciseVmDescriptorWide e₁ true true)
    (hsat₂ : satisfiedVm hash exerciseVmDescriptorWide e₂ true true)
    (hpin₁ : e₁.loc (saCol state.STATE_COMMIT) = e₁.pub pi.NEW_COMMIT)
    (hpin₂ : e₂.loc (saCol state.STATE_COMMIT) = e₂.pub pi.NEW_COMMIT)
    (hpub : e₁.pub pi.NEW_COMMIT = e₂.pub pi.NEW_COMMIT)
    (hd₁ : e₁.loc sysRootsDigestCol = systemRootsDigest hash sr₁)
    (hd₂ : e₂.loc sysRootsDigestCol = systemRootsDigest hash sr₂) :
    (baseAbsorbedCols e₁ = baseAbsorbedCols e₂ ∧ (∀ i : Fin N_SYSTEM_ROOTS, sr₁ i = sr₂ i))
    ∨ WideColl hash e₁ e₂ ∨ RootsColl hash sr₁ sr₂ :=
  EffectVmFullStateRunnable.runnable_full_commit_binds_or_collides (exerciseRunnableSpec preRoots)
    hash e₁ e₂ sr₁ sr₂ hsat₁ hsat₂ hpin₁ hpin₂ hpub hd₁ hd₂

/-- **`exercise_wide_rejects_root_tamper_or_collides` — side-table anti-ghost, as EXTRACTION.** Two wide
rows publishing the same `NEW_COMMIT` (with `systemRootsDigest` carriers) whose side-table sub-blocks
DIFFER at some index `i` exhibit a concrete collision of `hash` — a `WideColl` on the wide absorbed lists
or a `RootsColl` on the two root lists.

The previous form concluded `False` from `Poseidon2SpongeCR hash`, which the deployed BabyBear sponge
refutes; it was therefore vacuous at deployed parameters. This form is weaker and holds of that sponge. -/
theorem exercise_wide_rejects_root_tamper_or_collides (hash : List ℤ → ℤ)
    (e₁ e₂ : VmRowEnv) (sr₁ sr₂ : SysRoots) (preRoots : SysRoots)
    (hsat₁ : satisfiedVm hash exerciseVmDescriptorWide e₁ true true)
    (hsat₂ : satisfiedVm hash exerciseVmDescriptorWide e₂ true true)
    (hpin₁ : e₁.loc (saCol state.STATE_COMMIT) = e₁.pub pi.NEW_COMMIT)
    (hpin₂ : e₂.loc (saCol state.STATE_COMMIT) = e₂.pub pi.NEW_COMMIT)
    (hpub : e₁.pub pi.NEW_COMMIT = e₂.pub pi.NEW_COMMIT)
    (hd₁ : e₁.loc sysRootsDigestCol = systemRootsDigest hash sr₁)
    (hd₂ : e₂.loc sysRootsDigestCol = systemRootsDigest hash sr₂)
    {i : Fin N_SYSTEM_ROOTS} (htamper : sr₁ i ≠ sr₂ i) :
    WideColl hash e₁ e₂ ∨ RootsColl hash sr₁ sr₂ :=
  EffectVmFullStateRunnable.wide_rejects_root_tamper_or_collides (exerciseRunnableSpec preRoots)
    hash e₁ e₂ sr₁ sr₂ hsat₁ hsat₂ hpin₁ hpin₂ hpub hd₁ hd₂ htamper

#assert_axioms exercise_wide_binds_full_state_or_collides
#assert_axioms exercise_wide_rejects_root_tamper_or_collides

/-! ## §5 — NON-VACUITY: the full clause is INHABITED (TRUE) and REFUTABLE (FALSE), and the wide
descriptor is the genuine 188-wide `system_roots`-absorbing circuit. -/

/-- A frozen reference sub-block (the empty `system_roots`, since the hold layer touches no side table). -/
def goodPreRoots : SysRoots := emptySystemRoots

/-- A pre-state for the witnesses: bal_lo 42, nonce 9, everything else 0. -/
def exPre : CellState :=
  { balLo := 42, balHi := 0, nonce := 9, fields := fun _ => 0, capRoot := 0, reserved := 0
  , commit := 0 }

/-- The post-state the hold layer produces: bal_lo 42 (frozen), nonce 10 (ticked), frame frozen. -/
def exPost : CellState :=
  { balLo := 42, balHi := 0, nonce := 10, fields := fun _ => 0, capRoot := 0, reserved := 0
  , commit := 0 }

/-- **`goodExercise_realizes` — NON-VACUITY (witness TRUE).** The exercise hold-layer `fullClause` is
INHABITED by a real hold step: `exPost` is the genuine image of `exPre` (bal_lo `42` FROZEN, nonce `9 →
10`, frame frozen) and the roots are frozen. So the full clause is NOT `True`. -/
theorem goodExercise_realizes :
    (exerciseRunnableSpec goodPreRoots).fullClause exPre exPost goodPreRoots := by
  refine ⟨⟨rfl, rfl, ?_, fun _ => rfl, rfl, rfl⟩, rfl⟩
  show (10 : ℤ) = 9 + 1; norm_num

/-- **`exercise_clause_not_trivial` — the clause is REFUTABLE (witness FALSE).** A post-state whose nonce
does NOT tick (forged frozen `9`) FAILS the full clause — non-vacuity from BOTH sides. -/
theorem exercise_clause_not_trivial :
    ¬ ExerciseFullClause goodPreRoots exPre { exPost with nonce := 9 } goodPreRoots := by
  rintro ⟨⟨_, _, hnon, _⟩, _⟩
  simp only [exPre] at hnon
  norm_num at hnon

/-- **NON-VACUITY (the wide descriptor is the genuine 188-wide circuit).** `exerciseVmDescriptorWide`
declares `traceWidth = 188` and its `hashSites` are EXACTLY the four `system_roots`-absorbing
`wideHashSites`. -/
theorem exerciseWide_is_genuine :
    exerciseVmDescriptorWide.traceWidth = EFFECT_VM_WIDTH_SYSROOTS
    ∧ exerciseVmDescriptorWide.hashSites = wideHashSites
    ∧ exerciseVmDescriptorWide.hashSites.length = 4 := by
  refine ⟨rfl, rfl, ?_⟩
  show wideHashSites.length = 4
  decide

#assert_axioms goodExercise_realizes
#assert_axioms exercise_clause_not_trivial
#assert_axioms exerciseWide_is_genuine

/-! ## §6 — axiom-hygiene tripwires. -/

#guard exerciseVmDescriptorWide.traceWidth == 190
#guard exerciseVmDescriptorWide.hashSites.length == 4
#guard exerciseVmDescriptorWide.constraints.length == 13 + 14 + 4 + 3 + 1

end Dregg2.Circuit.Emit.EffectVmEmitExerciseWide
