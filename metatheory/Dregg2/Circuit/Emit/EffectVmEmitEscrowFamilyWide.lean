/-
# Dregg2.Circuit.Emit.EffectVmEmitEscrowFamilyWide — the escrow family's WIDE (`system_roots`-binding)
RUNNABLE descriptor builder + the family lift onto the generic `runnable_full_sound` crown.

## What this closes (the magnesium breadth, the escrow family's share)

`EffectVmFullStateRunnable` discharged ONCE (off `Poseidon2SpongeCR`) the WHOLE-state binding of the
RUNNABLE `EffectVmDescriptor`: a row satisfying a descriptor whose `traceWidth =
EFFECT_VM_WIDTH_SYSROOTS` and `hashSites = wideHashSites` publishes a `state_commit` that BINDS the 13
absorbed state-block columns AND the `system_roots` digest carrier (`sysRootsDigestCol = 186`, the
DEDICATED non-aliasing column), hence — chained with `systemRootsDigest_binds_pointwise` — every one of
the 8 side-table roots. The per-effect obligation is THIN (`decodeFull`): project the per-row gates to
the effect's cell intent + the root-update gate, decode to the declarative 17-field `fullClause`.

The PRE-EXISTING escrow descriptors (`EffectVmEmitCreateEscrow.createEscrowVmDescriptorFull` /
`…Genuine`, the refund/release siblings) bound the escrow root into `state_commit` via the RAW carrier
`aux_off_sys.SYSTEM_ROOTS_DIGEST` (= the literal `96`, which lands inside the aux block at abs col 96,
aliasing a balance bit — benign but not a clean, generically-liftable home; `EffectVmEmit:147-150`).
They are NOT in the shape the generic crown consumes (186-wide, `transferHashSites`/`escrowRootHashSites`,
raw-96 carrier). This module re-targets the escrow family's root carrier onto the DEDICATED
`sysRootsDigestCol`/`sysRootsDigestColBefore` and lifts each effect through the generic
`RunnableFullStateSpec`, so the circuit the PROVER RUNS binds the FULL 17-field post-state: tamper ANY
field (incl. ANY side-table root) ⇒ the running descriptor is UNSAT (`wide_rejects_state_tamper` /
`wide_rejects_root_tamper`, instantiated at the family spec).

## The shared family pieces (one root-update gate shape, four effects)

  * **`gEscrowRootUpdateWide`** — the root-UPDATE gate over the DEDICATED carriers: `sysRootsDigestCol −
    sysRootsDigestColBefore − step = 0`, i.e. the after-state `system_roots` digest is the before-state
    digest ADVANCED by the accumulator `step` the escrow record (prepended on create / resolved on
    settle) contributes. Distinct-by-construction from the raw-96 carrier (`186 ≠ 96`); it is the carrier
    `sysRootsAbsorbSite` (the `wideHashSites` 4th site) absorbs into `state_commit`.
  * **`escrowFamilyWideDescriptor rowGates`** — the generic WIDE descriptor: the effect's per-row
    `rowGates` (debit/credit + frame freeze, REUSED verbatim) ++ the root-update gate ++ transition ++
    the 7 boundary pins, with `traceWidth := EFFECT_VM_WIDTH_SYSROOTS` and `hashSites := wideHashSites`.
  * **`escrowFamilyWideSpec`** — the generic `RunnableFullStateSpec CellState` for ANY escrow-family
    effect: parametrized by the per-row gate-soundness (gates ⇒ the effect's `CellSpec`, supplied as a
    hypothesis — for create it is `EffectVmEmitCreateEscrow.intent_to_cellCreateSpec ∘ createEscrowVm_faithful`,
    for refund/release the credit analogue), `hash`, `preRoots`, the cell `params`, and the digest `step`.
    Its `fullClause` is the per-cell move AND the side-table digest advance — non-vacuous (a real escrow
    inhabits it), refutable (a forged post-state / dropped record fails it), and lifted to the WHOLE
    17-field anti-ghost by the generic crown.

## Honesty

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; Poseidon2 CR enters ONLY through the named
`Poseidon2SpongeCR` carrier inside the generic crown's anti-ghost (NOT these constructive lemmas). No
`sorry`, no `:= True`, no `native_decide`. This module OWNS only itself; every import is read-only.
-/
import Dregg2.Circuit.Emit.EffectVmFullStateRunnable

namespace Dregg2.Circuit.Emit.EffectVmEmitEscrowFamilyWide

open Dregg2.Circuit
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitTransfer (eSB eSA ePrm eSub transitionAll boundaryFirstPins
  boundaryLastPins boundaryLast_pins site0 site1 site2)
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound (CellState absorbedCols)
open Dregg2.Circuit.Emit.EffectVmFullStateRunnable
  (wideHashSites wide_commit_eq RunnableFullStateSpec runnable_full_sound runnable_full_commit_binds
   wide_rejects_state_tamper wide_rejects_root_tamper)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Exec.SystemRoots
  (SysRoots systemRootsDigest systemRootsDigest_binds_pointwise N_SYSTEM_ROOTS emptySystemRoots
   emptySystemRootsDigest)

set_option linter.unusedVariables false

/-! ## §0 — the escrow side-table root index + the digest-advance accumulator step param.

The escrow side-table is index `ESCROW = 0` of the 8-root `system_roots` sub-block. The accumulator
step the record (prepended on create / resolved on settle) contributes to the `systemRootsDigest` rides
the SAME param column the early cohort used (`param2`); on the WIDE descriptor it advances the DEDICATED
`sysRootsDigestCol` carrier, NOT the raw 96. -/

/-- The kernel index of the `escrows` side-table root in the `system_roots` sub-block
(`Exec.SystemRoots.systemRoot.ESCROW = 0`). -/
def ESCROW_ROOT_INDEX : Fin N_SYSTEM_ROOTS := ⟨Dregg2.Exec.SystemRoots.systemRoot.ESCROW, by decide⟩

/-- The `escrows`-accumulator STEP param column (`param2`; param0 = amount, param1 = direction). The
field-element delta the escrow record contributes to the `system_roots` digest. -/
def ESCROW_STEP_PARAM : Nat := 2

/-- The accumulator-step expression (param column 2). -/
def ePrmEscrowStep : EmittedExpr := .var (prmCol ESCROW_STEP_PARAM)

/-! ## §1 — the root-UPDATE gate over the DEDICATED carriers (`sysRootsDigestCol`, not raw 96). -/

/-- **`gEscrowRootUpdateWide`** — root-update gate body over the dedicated carriers:
`sysRootsDigestCol − sysRootsDigestColBefore − step` (so `sysRootsDigestCol = sysRootsDigestColBefore +
step`). Reads the BEFORE/AFTER `system_roots` digest carriers (`187`/`186`) — the dedicated,
non-aliasing sub-block the generic `sysRootsAbsorbSite` absorbs into `state_commit` — and the `param2`
accumulator step. This is the early cohort's `gEscrowRootUpdate` shape, re-homed off the raw 96. -/
def gEscrowRootUpdateWide : EmittedExpr :=
  eSub (eSub (.var sysRootsDigestCol) (.var sysRootsDigestColBefore)) ePrmEscrowStep

/-- **`EscrowRootIntentWide env`** — the intended `escrows`-root move on the WIDE row: the dedicated
after-carrier is the dedicated before-carrier ADVANCED by the `param2` step. -/
def EscrowRootIntentWide (env : VmRowEnv) : Prop :=
  env.loc sysRootsDigestCol = env.loc sysRootsDigestColBefore + env.loc (prmCol ESCROW_STEP_PARAM)

/-- **`escrowRootUpdateWide_faithful`.** The root-update gate holds IFF the dedicated digest advances by
the accumulator step — the gate pins EXACTLY the dedicated-carrier `escrows`-root update. -/
theorem escrowRootUpdateWide_faithful (env : VmRowEnv) :
    (VmConstraint.gate gEscrowRootUpdateWide).holdsVm env false false ↔ EscrowRootIntentWide env := by
  simp only [VmConstraint.holdsVm, gEscrowRootUpdateWide, ePrmEscrowStep, eSub, EmittedExpr.eval,
    EscrowRootIntentWide]
  constructor
  · intro h; linarith
  · intro h; rw [h]; ring

/-- **Anti-ghost (root tamper, gate-level).** A WIDE row whose dedicated after-carrier is NOT the
advanced accumulator is rejected by `gEscrowRootUpdateWide` — a dropped/forged `escrows` update is
UNSAT at the gate. -/
theorem escrowRootUpdateWide_rejects_wrong (env : VmRowEnv)
    (hwrong : env.loc sysRootsDigestCol
      ≠ env.loc sysRootsDigestColBefore + env.loc (prmCol ESCROW_STEP_PARAM)) :
    ¬ (VmConstraint.gate gEscrowRootUpdateWide).holdsVm env false false := by
  intro h; exact hwrong ((escrowRootUpdateWide_faithful env).mp h)

/-! ## §2 — the generic WIDE escrow-family descriptor (any per-row gate set). -/

/-- **`escrowFamilyWideDescriptor rowGates`** — the generic WIDE escrow-family circuit: the effect's
per-row `rowGates` (debit/credit + frame freeze, REUSED) ++ the dedicated-carrier root-update gate ++
transition continuity ++ the 7 boundary PI pins, with `traceWidth := EFFECT_VM_WIDTH_SYSROOTS` and
`hashSites := wideHashSites` (so the published `state_commit` absorbs the dedicated `sysRootsDigestCol`).
The constraint list places the root-update gate immediately after the per-row gates, then the shared
transition/boundary blocks — so a per-effect `decodeFull` projects `rowGates` (a prefix) and the
root-update gate (the single element after) by membership. -/
def escrowFamilyWideDescriptor (airName : String) (rowGates : List VmConstraint) :
    EffectVmDescriptor :=
  { name := airName ++ "-wide-sysroots"
  , traceWidth := EFFECT_VM_WIDTH_SYSROOTS
  , piCount := 34
  , constraints := (rowGates ++ [.gate gEscrowRootUpdateWide])
                     ++ transitionAll ++ boundaryFirstPins ++ boundaryLastPins
  , hashSites := wideHashSites
  , ranges := [ ⟨saCol state.BALANCE_LO, 30⟩, ⟨saCol state.BALANCE_HI, 30⟩ ] }

/-- The wide family descriptor's hash-sites ARE `wideHashSites` (so the generic `usesWideSites := rfl`). -/
theorem escrowFamilyWide_usesWideSites (airName : String) (rowGates : List VmConstraint) :
    (escrowFamilyWideDescriptor airName rowGates).hashSites = wideHashSites := rfl

/-- **`escrowFamilyWide_forces_rowGates`** — the wide descriptor's per-row gates hold (flag-free): the
effect's `rowGates` are a prefix of the constraint list, and a `.gate`'s `holdsVm` ignores the boundary
flags. So whatever the per-row gates pin (the effect's cell intent), the WIDE descriptor pins too. -/
theorem escrowFamilyWide_forces_rowGates (airName : String) (rowGates : List VmConstraint)
    (hAllGates : ∀ g ∈ rowGates, ∃ b, g = .gate b)
    (env : VmRowEnv)
    (hsat : ∀ c ∈ (escrowFamilyWideDescriptor airName rowGates).constraints,
              c.holdsVm env true true) :
    ∀ c ∈ rowGates, c.holdsVm env false false := by
  intro c hc
  have hmem : c ∈ (escrowFamilyWideDescriptor airName rowGates).constraints := by
    unfold escrowFamilyWideDescriptor
    simp only [List.mem_append]
    exact Or.inl (Or.inl (Or.inl (Or.inl hc)))
  have hh := hsat c hmem
  obtain ⟨b, rfl⟩ := hAllGates c hc
  simpa only [VmConstraint.holdsVm] using hh

/-- **`escrowFamilyWide_forces_root`** — the wide descriptor forces the dedicated-carrier root update. -/
theorem escrowFamilyWide_forces_root (airName : String) (rowGates : List VmConstraint)
    (env : VmRowEnv)
    (hsat : ∀ c ∈ (escrowFamilyWideDescriptor airName rowGates).constraints,
              c.holdsVm env true true) :
    EscrowRootIntentWide env := by
  apply (escrowRootUpdateWide_faithful env).mp
  have hmem : (VmConstraint.gate gEscrowRootUpdateWide)
      ∈ (escrowFamilyWideDescriptor airName rowGates).constraints := by
    unfold escrowFamilyWideDescriptor
    simp only [List.mem_append]
    exact Or.inl (Or.inl (Or.inl (Or.inr (by simp))))
  have hh := hsat _ hmem
  simpa only [VmConstraint.holdsVm] using hh

/-- **`escrowFamilyWide_forces_commit`** — the wide descriptor's last-row boundary pins `state_commit =
PI[NEW_COMMIT]` (the shared `boundaryLastPins`, projected by membership). -/
theorem escrowFamilyWide_forces_commit (airName : String) (rowGates : List VmConstraint)
    (env : VmRowEnv)
    (hsat : ∀ c ∈ (escrowFamilyWideDescriptor airName rowGates).constraints,
              c.holdsVm env true true) :
    env.loc (saCol state.STATE_COMMIT) = env.pub pi.NEW_COMMIT := by
  have hlast : ∀ c ∈ boundaryLastPins, c.holdsVm env false true := by
    intro c hc
    have hmem : c ∈ (escrowFamilyWideDescriptor airName rowGates).constraints := by
      unfold escrowFamilyWideDescriptor
      simp only [List.mem_append]; exact Or.inr hc
    have hh := hsat c hmem
    unfold boundaryLastPins at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl <;>
      · simp only [VmConstraint.holdsVm] at hh ⊢; exact hh
  exact (boundaryLast_pins env hlast).1

/-! ## §3 — THE FAMILY `RunnableFullStateSpec` + the FULL-STATE crown for ANY escrow-family effect.

The escrow-family `fullClause` over `(pre, post, postRoots)`:
  * **the per-cell move** `cellSpec pre post` — the effect's `CellCreateSpec`/`CellRefundSpec`/… (the
    `balLo` debit/credit, the WHOLE frame frozen) — fields 1–3 (+ 13–17 via `restLimbs`) of the 17;
  * **the side-table digest advance** `systemRootsDigest hash postRoots = systemRootsDigest hash preRoots
    + step` — the `escrows` side-table digest moved by the record's accumulator step, the OTHER 7 roots
    bound through the SAME digest (fields 4–12). The generic anti-ghost (`wide_rejects_root_tamper`)
    lifts this to: tampering ANY of the 8 roots ⇒ a different digest ⇒ a different `state_commit` ⇒ UNSAT.

`decodeAfter` carries the structured decode the effect supplies: the per-cell `cellDecode` (its
`RowEncodes`-style relation) AND the dedicated digest-carrier pins (`sysRootsDigestCol =
systemRootsDigest postRoots`, `sysRootsDigestColBefore = systemRootsDigest preRoots`) AND the step-param
pin (`prmCol ESCROW_STEP_PARAM = step`). `decodeFull` is THIN: the per-cell soundness (supplied) + the
root-update gate, rewritten by the carrier/step pins. -/

/-- **`EscrowFamilyFullClause cellSpec hash preRoots step`** — the declarative full 17-field post-state for
an escrow-family effect: the per-cell move `cellSpec pre post` (the frame + balance limb) AND the
`escrows` side-table digest advanced by `step` (the other 7 roots bound through the digest). Non-`True`
by construction (it carries the genuine cell move + the genuine digest advance). -/
def EscrowFamilyFullClause (cellSpec : CellState → CellState → Prop) (hash : List ℤ → ℤ)
    (preRoots : SysRoots) (step : ℤ) (pre post : CellState) (postRoots : SysRoots) : Prop :=
  cellSpec pre post
    ∧ systemRootsDigest hash postRoots = systemRootsDigest hash preRoots + step

/-- **`escrowFamilyWideSpec` — THE FAMILY `RunnableFullStateSpec`.** Given an escrow-family effect's
  * `airName` + `rowGates` (all `.gate`s, supplied via `hAllGates`),
  * per-cell gate-soundness `cellFromGates` (the row gates, flag-free, decode to `cellSpec pre post`
    under the effect's structured `cellDecode env pre post` — for create this is
    `intent_to_cellCreateSpec ∘ createEscrowVm_faithful`, for the credit siblings the analogue),
  * the abstract carrier `hash`, the frozen-reference before-roots `preRoots`, the digest `step`,
this is the WIDE RUNNABLE `RunnableFullStateSpec` whose `fullClause` is `EscrowFamilyFullClause`. THIN:
`decodeFull` is `cellFromGates` (projected through `escrowFamilyWide_forces_rowGates`) + the root-update
gate rewritten by the decode's carrier/step pins. -/
def escrowFamilyWideSpec (airName : String) (rowGates : List VmConstraint)
    (hAllGates : ∀ g ∈ rowGates, ∃ b, g = .gate b)
    (isRow : VmRowEnv → Prop)
    (cellDecode : VmRowEnv → CellState → CellState → Prop)
    (cellSpec : CellState → CellState → Prop)
    (cellFromGates : ∀ (env : VmRowEnv) (pre post : CellState),
      isRow env → cellDecode env pre post →
      (∀ c ∈ rowGates, c.holdsVm env false false) → cellSpec pre post)
    (hash : List ℤ → ℤ) (preRoots : SysRoots) (step : ℤ) :
    RunnableFullStateSpec CellState where
  descriptor    := escrowFamilyWideDescriptor airName rowGates
  usesWideSites := rfl
  isRow         := isRow
  decodeAfter   := fun env pre post postRoots =>
    cellDecode env pre post
    ∧ env.loc sysRootsDigestCol = systemRootsDigest hash postRoots
    ∧ env.loc sysRootsDigestColBefore = systemRootsDigest hash preRoots
    ∧ env.loc (prmCol ESCROW_STEP_PARAM) = step
  fullClause    := EscrowFamilyFullClause cellSpec hash preRoots step
  decodeFull    := by
    intro env pre post postRoots hrow hdec hgates
    obtain ⟨hcellDec, hAfter, hBefore, hStep⟩ := hdec
    -- per-cell leg: project the row gates, then the supplied per-cell soundness.
    have hrowgates : ∀ c ∈ rowGates, c.holdsVm env false false :=
      escrowFamilyWide_forces_rowGates airName rowGates hAllGates env hgates
    have hcell := cellFromGates env pre post hrow hcellDec hrowgates
    -- side-table leg: the root-update gate gives the dedicated digest advance; rewrite by the pins.
    have hroot : EscrowRootIntentWide env :=
      escrowFamilyWide_forces_root airName rowGates env hgates
    refine ⟨hcell, ?_⟩
    -- hroot : sysRootsDigestCol = sysRootsDigestColBefore + step_param
    unfold EscrowRootIntentWide at hroot
    rw [hAfter, hBefore, hStep] at hroot
    exact hroot

/-- **`escrow_family_runnable_full_sound` — THE FAMILY CROWN (per-effect: just plug in).** A row
satisfying the WIDE escrow-family descriptor (`satisfiedVm`, first/last active), under the family
`decodeAfter`, pins the FULL 17-field declarative post-state (`EscrowFamilyFullClause`): the per-cell
move AND the `escrows` side-table digest advance (the other 7 roots bound through the digest). This is
`runnable_full_sound` specialized to `escrowFamilyWideSpec` — the crypto is discharged ONCE in the
generic crown; here it is the (already-proved) per-cell soundness + the root-update gate. -/
theorem escrow_family_runnable_full_sound (airName : String) (rowGates : List VmConstraint)
    (hAllGates : ∀ g ∈ rowGates, ∃ b, g = .gate b)
    (isRow : VmRowEnv → Prop)
    (cellDecode : VmRowEnv → CellState → CellState → Prop)
    (cellSpec : CellState → CellState → Prop)
    (cellFromGates : ∀ (env : VmRowEnv) (pre post : CellState),
      isRow env → cellDecode env pre post →
      (∀ c ∈ rowGates, c.holdsVm env false false) → cellSpec pre post)
    (hash : List ℤ → ℤ) (preRoots : SysRoots) (step : ℤ)
    (env : VmRowEnv) (pre post : CellState) (postRoots : SysRoots)
    (hrow : isRow env)
    (hcellDec : cellDecode env pre post)
    (hAfter : env.loc sysRootsDigestCol = systemRootsDigest hash postRoots)
    (hBefore : env.loc sysRootsDigestColBefore = systemRootsDigest hash preRoots)
    (hStep : env.loc (prmCol ESCROW_STEP_PARAM) = step)
    (hsat : satisfiedVm hash (escrowFamilyWideDescriptor airName rowGates) env true true) :
    EscrowFamilyFullClause cellSpec hash preRoots step pre post postRoots :=
  runnable_full_sound
    (escrowFamilyWideSpec airName rowGates hAllGates isRow cellDecode cellSpec cellFromGates
      hash preRoots step)
    hash env pre post postRoots hrow ⟨hcellDec, hAfter, hBefore, hStep⟩ hsat

/-! ## §4 — the WHOLE-STATE anti-ghost on the family descriptor (all 17 fields' tamper ⇒ UNSAT).

`runnable_full_commit_binds` instantiated at the family spec: two rows satisfying the wide family
descriptor that publish the SAME `NEW_COMMIT` (with `systemRootsDigest` carriers) agree on EVERY absorbed
state-block column AND every side-table root. The contrapositives (`wide_rejects_state_tamper` /
`wide_rejects_root_tamper`) give: a forged balance/field/cap-root OR a dropped/reordered side-table root
that still claims the published commitment is UNSAT — the no-malleability property on all 17 fields. -/

/-- **`escrowFamily_binds_full_state`** — two rows satisfying the WIDE family descriptor publishing the
SAME `NEW_COMMIT` (carriers = `systemRootsDigest` of their post sub-blocks) agree on EVERY absorbed
state-block column AND every side-table root. The whole post-state is bound by the runnable commitment. -/
theorem escrowFamily_binds_full_state (airName : String) (rowGates : List VmConstraint)
    (hAllGates : ∀ g ∈ rowGates, ∃ b, g = .gate b)
    (isRow : VmRowEnv → Prop)
    (cellDecode : VmRowEnv → CellState → CellState → Prop)
    (cellSpec : CellState → CellState → Prop)
    (cellFromGates : ∀ (env : VmRowEnv) (pre post : CellState),
      isRow env → cellDecode env pre post →
      (∀ c ∈ rowGates, c.holdsVm env false false) → cellSpec pre post)
    (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash) (preRoots : SysRoots) (step : ℤ)
    (e₁ e₂ : VmRowEnv) (sr₁ sr₂ : SysRoots)
    (hsat₁ : satisfiedVm hash (escrowFamilyWideDescriptor airName rowGates) e₁ true true)
    (hsat₂ : satisfiedVm hash (escrowFamilyWideDescriptor airName rowGates) e₂ true true)
    (hpin₁ : e₁.loc (saCol state.STATE_COMMIT) = e₁.pub pi.NEW_COMMIT)
    (hpin₂ : e₂.loc (saCol state.STATE_COMMIT) = e₂.pub pi.NEW_COMMIT)
    (hpub : e₁.pub pi.NEW_COMMIT = e₂.pub pi.NEW_COMMIT)
    (hd₁ : e₁.loc sysRootsDigestCol = systemRootsDigest hash sr₁)
    (hd₂ : e₂.loc sysRootsDigestCol = systemRootsDigest hash sr₂) :
    absorbedCols e₁ = absorbedCols e₂ ∧ (∀ i : Fin N_SYSTEM_ROOTS, sr₁ i = sr₂ i) :=
  runnable_full_commit_binds
    (escrowFamilyWideSpec airName rowGates hAllGates isRow cellDecode cellSpec cellFromGates
      hash preRoots step)
    hash hCR e₁ e₂ sr₁ sr₂ hsat₁ hsat₂ hpin₁ hpin₂ hpub hd₁ hd₂

/-! ## §5 — layout pins (anti-drift) + axiom hygiene. -/

-- The dedicated carriers are the NON-aliasing 186/187 sub-block (NOT the raw 96).
#guard sysRootsDigestCol == 186
#guard sysRootsDigestColBefore == 187
#guard decide (sysRootsDigestCol ≠ (Dregg2.Circuit.Emit.EffectVmEmit.aux_off_sys.SYSTEM_ROOTS_DIGEST))
-- The escrow root is index 0 of the sub-block; the step param is param2, in-range.
#guard ESCROW_ROOT_INDEX.val == Dregg2.Exec.SystemRoots.systemRoot.ESCROW
#guard ESCROW_STEP_PARAM == 2
#guard ESCROW_STEP_PARAM < NUM_PARAMS
-- The wide family descriptor declares the widened width + the 4 wide hash-sites.
#guard (escrowFamilyWideDescriptor "x" []).traceWidth == EFFECT_VM_WIDTH_SYSROOTS
#guard (escrowFamilyWideDescriptor "x" []).traceWidth == 188
#guard (escrowFamilyWideDescriptor "x" []).hashSites.length == 4

#assert_axioms escrowRootUpdateWide_faithful
#assert_axioms escrowRootUpdateWide_rejects_wrong
#assert_axioms escrowFamilyWide_usesWideSites
#assert_axioms escrowFamilyWide_forces_rowGates
#assert_axioms escrowFamilyWide_forces_root
#assert_axioms escrowFamilyWide_forces_commit
#assert_axioms escrow_family_runnable_full_sound
#assert_axioms escrowFamily_binds_full_state

end Dregg2.Circuit.Emit.EffectVmEmitEscrowFamilyWide
