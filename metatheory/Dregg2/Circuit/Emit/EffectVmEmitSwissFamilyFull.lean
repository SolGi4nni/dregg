/-
# Dregg2.Circuit.Emit.EffectVmEmitSwissFamilyFull — the MAGNESIUM amplification of the whole swiss /
  sturdy-ref effect family (`swissExport · swissDrop · swissEnliven · swissHandoff · swissReconcile`):
  the RUNNABLE EffectVM descriptor binds the FULL 17-field post-state (all `RecordKernelState` fields +
  the WHOLE `system_roots` sub-block), NOT the weaker per-cell `SwissCellSpec` of
  `EffectVmEmitSwiss{Export,Drop,Handoff}.lean`.

## What this closes (the dominant Class-C disease, for the swiss family)

The earlier swiss descriptors (`EffectVmEmitSwissExport.swissExportDescriptor_full_sound` &c.) were FULL
on the per-cell block, but the swiss side-table root rode `field[4]` (an absorbed STATE column) and the
descriptor pinned NOTHING about the OTHER 7 side-table roots — a prover could drop an escrow / omit a
nullifier / reorder a queue and KEEP the published `NEW_COMMIT` (the `*_root_not_in_descriptor_commit`
gap). THIS module migrates the swiss root onto the dedicated, non-aliasing `sysRootsDigestCol` (the
STAGE-4 carrier), absorbs it into `state_commit` via `wideHashSites`, and lifts through the GENERIC
`EffectVmFullStateRunnable.RunnableFullStateSpec` so a satisfying RUNNABLE witness pins the WHOLE 17-field
post-state — and the anti-ghost (`runnable_full_commit_binds` / `wide_rejects_root_tamper`) bites on ALL 8
side-table roots. The NO-MALLEABILITY property: tamper ANY field (incl. any side-table root) ⇒ the running
descriptor is UNSAT.

## The shared swiss transition, on the WIDE row (the honest 17-field declarative post)

Every swiss effect is a SIDE-TABLE-ONLY, balance-NEUTRAL effect whose universe-A spec rewrites EXACTLY the
`swiss` list (`ExportSpec` GROWS it; `swissEnlivenK`/`swissHandoffK` BUMP/cert-bind one entry; `swissDropK`
GC-decrements one entry — all `*_only_swiss`, the 16 non-`swiss` kernel fields LITERALLY frozen). Projected
onto the EffectVM row + the `system_roots` sub-block, ALL FIVE share ONE transition shape:

  * the per-cell BLOCK is frozen EXCEPT the nonce, which TICKS `+1` (the running prover's global non-NoOp
    invariant `air.rs:2631`) — balance limbs / `cap_root` / `reserved` / ALL 8 user fields (INCLUDING
    `field[4]`, which no longer carries the root) FROZEN;
  * the `system_roots` sub-block MOVES at index `STURDYREF` (= 3) ONLY: `postRoots STURDYREF` is the new
    swiss-list digest `d` (the witnessed after-state digest the `paramSF.SWISS_DIGEST_NEW` carries), and the
    OTHER 7 side-table roots (escrow / queue / refcount / deleg / nullifier / commit / sealed) are FROZEN.
    This is `swissRootsUpdate preRoots d := Function.update preRoots STURDYREF d`.

So the family shares ONE root index (`STURDYREF`) and ONE root-update-gate shape (§1), differing ONLY in
the AIR name + the selector column — exactly the "fill a family at a time" the §WORKLIST anticipates. The
new `system_roots` digest is carried on `sysRootsDigestCol` (absorbed by `wideHashSites`), so the published
`state_commit` binds the WHOLE side-table state.

## What is PROVEN (l4v bar — full 17 fields, genuine, NO sorry/:=True/native_decide)

  * **§1–§3 the PARAMETRIC core** — `swissWideRowGatesFor` / `swissVmDescriptorWideFor` (parametric in
    AIR-name + selector), `SwissWideRowEncodes`, `SwissFullClause`, the THIN `swissFamily_decodeFull`, and
    the GENERIC `swissFamily_runnable_full_sound` (a satisfying wide row pins the FULL 17-field clause). The
    crypto (anti-ghost on all 8 roots) is discharged ONCE in the imported generic theorems; per-effect
    content is only the (proved here) per-cell freeze + the decode.
  * **§4 the FIVE named instances + crowns** — `swissExport_runnable_full_sound`,
    `swissDrop_runnable_full_sound`, `swissEnliven_runnable_full_sound`, `swissHandoff_runnable_full_sound`,
    `swissReconcile_runnable_full_sound`: each on its OWN wide descriptor (distinct selector), pinning the
    full post-state of THAT effect's executor.
  * **§5 the FIVE anti-ghost teeth** — `swiss*_runnable_rejects_root_tamper`: two satisfying rows publishing
    the same `NEW_COMMIT` that DIFFER at ANY of the 8 side-table roots cannot both satisfy. Tampering a
    frozen escrow/nullifier/queue root, OR forging the STURDYREF advance, is UNSAT — the whole-state tooth.
  * **§6 non-vacuity** — `SwissFullClause` is inhabited by a real swiss move (witness TRUE) AND refuted by a
    forged post (witness FALSE), so the clause is not `True`.

## The carried IR gap (recorded, NOT papered — the inherited swiss finding)

The new STURDYREF root `d` is WITNESS-supplied (the `paramSF.SWISS_DIGEST_NEW` column), not RECOMPUTED
in-circuit from the `List SwissRecord` structure: `VmHashSite` absorbs trace COLUMNS, with no site
re-deriving `D (post.swiss)` from a per-row serialization of the swiss list (the inherited
`EffectVmEmitSwiss{Export,Drop,Handoff}` IR GAP 2 — the swiss-list-absorbing `VmHashSite`). So the
descriptor pins `postRoots STURDYREF = d` and binds THAT (and the whole sub-block) into `state_commit` —
the WHOLE post-state is bound, anti-ghost on all 17 fields — but the in-circuit GENUINE-recompute of the
swiss-list digest (the escrow-family `EffectVmEmitEscrowRoot.siteEscrowRootAdvance` analog over `SwissRecord`
leaves) is still ASK'd. The list-digest faithfulness (`postRoots STURDYREF = D (genuine moved list)`) lives
in the universe-A `swiss*_full_sound` (carried by `EffectVmEmitSwiss*.unify_swiss*`). This is a refinement
on top of a genuine full-state binding, NOT a soundness hole in the binding.

## Honesty

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; Poseidon2 CR enters ONLY via the named
`Poseidon2SpongeCR` carrier inside the imported generic theorems. No `sorry`, no `:= True`, no
`native_decide`. Imports are read-only; this file OWNS only its own declarations.
-/
import Dregg2.Circuit.Emit.EffectVmEmitTransfer
import Dregg2.Circuit.Emit.EffectVmFullStateRunnable

namespace Dregg2.Circuit.Emit.EffectVmEmitSwissFamilyFull

open Dregg2.Circuit
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitTransfer
  (eSB eSA ePrm eSub eSelNoop gNonce transitionAll boundaryFirstPins)
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound (CellState)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Exec.SystemRoots
  (SysRoots systemRootsDigest emptySystemRoots N_SYSTEM_ROOTS)
open Dregg2.Circuit.Emit.EffectVmFullStateRunnable
  (RunnableFullStateSpec runnable_full_sound runnable_full_commit_binds wide_rejects_root_tamper
   wideHashSites)
open Dregg2.Exec.CircuitEmit (EmittedExpr)

set_option linter.unusedVariables false
set_option autoImplicit false

/-! ## §0 — the STURDYREF root index + the swiss-roots single-index update.

Every swiss effect moves EXACTLY one side-table root: the swiss/sturdyref root at the kernel-owned index
`systemRoot.STURDYREF = 3`. We model its move as a single-index `Function.update` on the `SysRoots`
sub-block — the STURDYREF cell takes the new swiss-list digest, every OTHER root unchanged. -/

/-- The swiss/sturdyref root index as a `Fin N_SYSTEM_ROOTS` (`STURDYREF = 3 < 8`). -/
def sturdyrefIdx : Fin N_SYSTEM_ROOTS := ⟨Dregg2.Exec.SystemRoots.systemRoot.STURDYREF, by decide⟩

/-- **`swissRootsUpdate sr d`** — the post `system_roots` sub-block of a swiss effect: `sr` with the
STURDYREF cell set to the new swiss-list digest `d`, every OTHER side-table root FROZEN. -/
def swissRootsUpdate (sr : SysRoots) (d : Dregg2.Exec.SystemRoots.FieldElem) : SysRoots :=
  Function.update sr sturdyrefIdx d

/-- The STURDYREF cell of `swissRootsUpdate sr d` IS the new digest. -/
theorem swissRootsUpdate_sturdyref (sr : SysRoots) (d : Dregg2.Exec.SystemRoots.FieldElem) :
    swissRootsUpdate sr d sturdyrefIdx = d := by
  unfold swissRootsUpdate Function.update
  rw [dif_pos rfl]

/-- Every NON-STURDYREF cell of `swissRootsUpdate sr d` is FROZEN (the 7 other side-table roots). -/
theorem swissRootsUpdate_frozen (sr : SysRoots) (d : Dregg2.Exec.SystemRoots.FieldElem)
    (i : Fin N_SYSTEM_ROOTS) (hi : i ≠ sturdyrefIdx) :
    swissRootsUpdate sr d i = sr i := by
  unfold swissRootsUpdate Function.update
  rw [dif_neg hi]

/-! ## §1 — the PARAMETRIC wide descriptor (per-cell freeze + nonce-tick + dedicated-carrier root-update).

The swiss wide descriptor TICKS the nonce and FREEZES the whole per-cell block INCLUDING `field[4]` (the
root no longer rides it — it moved to `sysRootsDigestCol`). The single ROOT-UPDATE gate pins the dedicated
carrier `sysRootsDigestCol` to the witnessed new `system_roots` digest param `paramSF.SWISS_DIGEST_NEW`.
The hash-sites are `wideHashSites` (so the carrier is absorbed into `state_commit`). Parametric in the AIR
name + the selector column — the only per-effect data. -/

namespace paramSF
/-- The post `system_roots` digest parameter (the witness fills `systemRootsDigest postRoots`). Reuses the
existing modules' `SWISS_DIGEST_NEW = 2` param slot. -/
def SWISS_DIGEST_NEW : Nat := 2
end paramSF

/-- The post `system_roots`-digest param as an expression. -/
def eSwissDigestNew : EmittedExpr := .var (prmCol paramSF.SWISS_DIGEST_NEW)
/-- The dedicated carrier `sysRootsDigestCol` as an expression. -/
def eSysRootsCol : EmittedExpr := .var sysRootsDigestCol

/-- **`gSwissRootUpdate`** — the ROOT-UPDATE gate body: `sysRootsDigestCol − SWISS_DIGEST_NEW` (the
dedicated after-state `system_roots` carrier IS the witnessed new digest). Over the DEDICATED, non-aliasing
carrier `sysRootsDigestCol = 186`, NOT the raw `96`. -/
def gSwissRootUpdate : EmittedExpr := eSub eSysRootsCol eSwissDigestNew

/-- Nonce TICK body (the running prover's global non-NoOp invariant): reused verbatim from transfer. -/
def gNonceTick : EmittedExpr := gNonce
/-- Balance-lo freeze body. -/
def gBalLoFix : EmittedExpr := eSub (eSA state.BALANCE_LO) (eSB state.BALANCE_LO)
/-- Balance-hi freeze body. -/
def gBalHiFix : EmittedExpr := eSub (eSA state.BALANCE_HI) (eSB state.BALANCE_HI)
/-- Cap-root freeze body (no swiss effect touches `caps`). -/
def gCapFix : EmittedExpr := eSub (eSA state.CAP_ROOT) (eSB state.CAP_ROOT)
/-- Reserved freeze body. -/
def gResFix : EmittedExpr := eSub (eSA state.RESERVED) (eSB state.RESERVED)
/-- Field-`i` freeze body. -/
def gFieldFix (i : Nat) : EmittedExpr :=
  eSub (eSA (state.FIELD_BASE + i)) (eSB (state.FIELD_BASE + i))
/-- The eight field-freeze gates (ALL fields frozen — the root moved off `field[4]`). -/
def gFieldFixAll : List VmConstraint :=
  (List.range 8).map (fun i => VmConstraint.gate (gFieldFix i))

/-- The shared swiss wide per-row gates: ROOT-UPDATE (dedicated carrier), nonce TICK, balance/cap/reserved
freeze, ALL EIGHT user fields freeze. Identical for every swiss effect (the transition is shared). -/
def swissWideRowGates : List VmConstraint :=
  [ .gate gSwissRootUpdate, .gate gNonceTick, .gate gBalLoFix, .gate gBalHiFix
  , .gate gCapFix, .gate gResFix ] ++ gFieldFixAll

/-- **`swissVmDescriptorWideFor airName selCol`** — the parametric MAGNESIUM descriptor: the shared wide
row gates ++ transition continuity ++ row-0 boundary pins, with `traceWidth := EFFECT_VM_WIDTH_SYSROOTS`
and `hashSites := wideHashSites`. Per-effect data is ONLY `airName` + the selector `selCol`. -/
def swissVmDescriptorWideFor (airName : String) (selCol : Nat) : EffectVmDescriptor :=
  { name := airName
  , traceWidth := EFFECT_VM_WIDTH_SYSROOTS
  , piCount := 34
  , constraints := swissWideRowGates ++ transitionAll ++ boundaryFirstPins
  , hashSites := wideHashSites
  , ranges := [] }

/-- The parametric descriptor's hash-sites ARE `wideHashSites` (so `usesWideSites := rfl`). -/
theorem swissWideFor_usesWideSites (airName : String) (selCol : Nat) :
    (swissVmDescriptorWideFor airName selCol).hashSites = wideHashSites := rfl

/-- The parametric descriptor's constraints (the shared list, selector-independent). -/
theorem swissWideFor_constraints (airName : String) (selCol : Nat) :
    (swissVmDescriptorWideFor airName selCol).constraints
      = swissWideRowGates ++ transitionAll ++ boundaryFirstPins := rfl

/-! ## §2 — the row-shape + the structured decode + the full clause (all selector-PARAMETRIC). -/

/-- The row is a swiss row for selector `selCol`: `sel[selCol] = 1`, `s_noop = 0`. -/
def IsSwissRow (selCol : Nat) (env : VmRowEnv) : Prop :=
  env.loc selCol = 1 ∧ env.loc sel.NOOP = 0

/-- **`SwissFullClause d pre post preRoots postRoots`** — the DECLARATIVE 17-field post-state of a swiss
effect: (a) the per-cell BLOCK move/freeze (nonce ticks `+1`, balance limbs / `cap_root` / `reserved` / ALL
8 user fields FROZEN), AND (b) the `system_roots` sub-block is the single-index swiss update of `preRoots`
(`postRoots = swissRootsUpdate preRoots d`) — STURDYREF advanced, the OTHER 7 side-table roots FROZEN.
Selector-independent (the same clause for all five swiss effects). Non-vacuous (witnessed below). -/
def SwissFullClause (d : ℤ) (pre post : CellState) (preRoots postRoots : SysRoots) : Prop :=
  (post.nonce = pre.nonce + 1
    ∧ post.balLo = pre.balLo ∧ post.balHi = pre.balHi
    ∧ post.capRoot = pre.capRoot ∧ post.reserved = pre.reserved
    ∧ ∀ i : Fin 8, post.fields i = pre.fields i)
  ∧ postRoots = swissRootsUpdate preRoots d

/-- **`SwissFullClause_sturdyref_advance`** — from the full clause, the post STURDYREF root IS the
witnessed digest `d` (the swiss-list move the descriptor pins). -/
theorem SwissFullClause_sturdyref_advance {d : ℤ} {pre post : CellState} {preRoots postRoots : SysRoots}
    (h : SwissFullClause d pre post preRoots postRoots) : postRoots sturdyrefIdx = d := by
  obtain ⟨_, hroots⟩ := h
  rw [hroots, swissRootsUpdate_sturdyref]

/-- **`SwissFullClause_other_roots_frozen` — THE headline the per-cell descriptor could not say.** From the
full clause, EVERY side-table root OTHER than STURDYREF (escrow / queue / refcount / deleg / nullifier /
commit / sealed) is FROZEN at its pre value. So a swiss effect's RUNNABLE descriptor binds the whole
`system_roots` sub-block: the 7 untouched side-tables provably cannot move. -/
theorem SwissFullClause_other_roots_frozen {d : ℤ} {pre post : CellState}
    {preRoots postRoots : SysRoots} (h : SwissFullClause d pre post preRoots postRoots)
    (i : Fin N_SYSTEM_ROOTS) (hi : i ≠ sturdyrefIdx) : postRoots i = preRoots i := by
  obtain ⟨_, hroots⟩ := h
  rw [hroots, swissRootsUpdate_frozen preRoots d i hi]

/-- **`SwissWideRowEncodes hash env d pre post preRoots postRoots`** — the structured decode of a wide row.
The `state_before`/`state_after` columns are `pre`/`post`; the param `SWISS_DIGEST_NEW` is `d`; the
dedicated carrier `sysRootsDigestCol` IS `systemRootsDigest postRoots`; the post sub-block IS
`swissRootsUpdate preRoots d`; and the published `NEW_COMMIT` is the after `state_commit`. -/
def SwissWideRowEncodes (hash : List ℤ → ℤ) (env : VmRowEnv) (d : ℤ)
    (pre post : CellState) (preRoots postRoots : SysRoots) : Prop :=
  env.loc (sbCol state.BALANCE_LO) = pre.balLo
  ∧ env.loc (sbCol state.BALANCE_HI) = pre.balHi
  ∧ env.loc (sbCol state.NONCE) = pre.nonce
  ∧ (∀ i : Fin 8, env.loc (sbCol (state.FIELD_BASE + i.val)) = pre.fields i)
  ∧ env.loc (sbCol state.CAP_ROOT) = pre.capRoot
  ∧ env.loc (sbCol state.RESERVED) = pre.reserved
  ∧ env.loc (prmCol paramSF.SWISS_DIGEST_NEW) = d
  ∧ env.loc (saCol state.BALANCE_LO) = post.balLo
  ∧ env.loc (saCol state.BALANCE_HI) = post.balHi
  ∧ env.loc (saCol state.NONCE) = post.nonce
  ∧ (∀ i : Fin 8, env.loc (saCol (state.FIELD_BASE + i.val)) = post.fields i)
  ∧ env.loc (saCol state.CAP_ROOT) = post.capRoot
  ∧ env.loc (saCol state.RESERVED) = post.reserved
  ∧ env.loc sysRootsDigestCol = systemRootsDigest hash postRoots
  ∧ postRoots = swissRootsUpdate preRoots d
  ∧ env.loc (saCol state.STATE_COMMIT) = env.pub pi.NEW_COMMIT

/-! ## §3 — the THIN per-family obligation (`swissFamily_decodeFull`) + the GENERIC crown + spec builder. -/

/-- Each wide row gate is a member of the descriptor's full constraint list (the row gates are a prefix of
`swissWideRowGates ++ transitionAll ++ boundaryFirstPins`). -/
theorem rowGate_mem_descriptor (airName : String) (selCol : Nat) {c : VmConstraint}
    (hc : c ∈ swissWideRowGates) : c ∈ (swissVmDescriptorWideFor airName selCol).constraints := by
  rw [swissWideFor_constraints]
  simp only [List.mem_append]; exact Or.inl (Or.inl hc)

/-- **`swissFamily_decodeFull` — THE THIN per-family obligation.** On a wide swiss row, the descriptor's
per-row gates (root-update + nonce-tick + per-cell freeze) PLUS the structured decode entail the full
17-field clause. The per-cell part comes from the freeze/tick gates (projected through the decode); the
side-table part (`postRoots = swissRootsUpdate preRoots d`) is the decode's witnessed sub-block fact. NO
crypto here. Selector-PARAMETRIC — proved ONCE for the whole family. -/
theorem swissFamily_decodeFull (airName : String) (selCol : Nat) (hash : List ℤ → ℤ)
    (env : VmRowEnv) (d : ℤ) (pre post : CellState) (preRoots postRoots : SysRoots)
    (hrow : IsSwissRow selCol env)
    (hdec : SwissWideRowEncodes hash env d pre post preRoots postRoots)
    (hgatesAll : ∀ c ∈ (swissVmDescriptorWideFor airName selCol).constraints,
                   c.holdsVm env true true) :
    SwissFullClause d pre post preRoots postRoots := by
  obtain ⟨_hsH, hsN⟩ := hrow
  obtain ⟨hsbLo, hsbHi, hsbN, hsbF, hsbCap, hsbRes, hpDig,
          hsaLo, hsaHi, hsaN, hsaF, hsaCap, hsaRes, _hcarrier, hrootsUpd, _hpin⟩ := hdec
  have hgates : ∀ c ∈ swissWideRowGates, c.holdsVm env true true :=
    fun c hc => hgatesAll c (rowGate_mem_descriptor airName selCol hc)
  have hNon := hgates (.gate gNonceTick) (by simp [swissWideRowGates])
  have hLo := hgates (.gate gBalLoFix) (by simp [swissWideRowGates])
  have hHi := hgates (.gate gBalHiFix) (by simp [swissWideRowGates])
  have hCap := hgates (.gate gCapFix) (by simp [swissWideRowGates])
  have hRes := hgates (.gate gResFix) (by simp [swissWideRowGates])
  have hFld : ∀ i, i < 8 → VmConstraint.holdsVm env true true (.gate (gFieldFix i)) := by
    intro i hi
    apply hgates
    simp only [swissWideRowGates, gFieldFixAll, List.mem_append, List.mem_map, List.mem_range,
      List.mem_cons]
    exact Or.inr ⟨i, hi, rfl⟩
  simp only [VmConstraint.holdsVm, gNonceTick, gNonce, gBalLoFix, gBalHiFix, gCapFix, gResFix,
    eSA, eSB, eSub, eSelNoop, EmittedExpr.eval] at hNon hLo hHi hCap hRes
  rw [hsN] at hNon
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, hrootsUpd⟩
  · rw [← hsaN, ← hsbN]; linarith [hNon]
  · rw [← hsaLo, ← hsbLo]; linarith [hLo]
  · rw [← hsaHi, ← hsbHi]; linarith [hHi]
  · rw [← hsaCap, ← hsbCap]; linarith [hCap]
  · rw [← hsaRes, ← hsbRes]; linarith [hRes]
  · intro i
    have hp := hsaF i; have hq := hsbF i
    have hgi := hFld i.val i.isLt
    simp only [VmConstraint.holdsVm, gFieldFix, eSA, eSB, eSub, EmittedExpr.eval] at hgi
    rw [← hp, ← hq]; linarith [hgi]

/-- **`swissRunnableSpecFor` — the parametric per-family `RunnableFullStateSpec`.** Carries `airName`/
`selCol`/`d`/`preRoots` as fixed reference data; `decodeAfter` is `SwissWideRowEncodes`; `fullClause` is
`SwissFullClause`; `decodeFull` is the thin obligation above. The crypto carrier is the generic
`wideHashSites`. -/
def swissRunnableSpecFor (airName : String) (selCol : Nat) (hash : List ℤ → ℤ) (d : ℤ)
    (preRoots : SysRoots) : RunnableFullStateSpec CellState where
  descriptor    := swissVmDescriptorWideFor airName selCol
  usesWideSites := rfl
  isRow         := IsSwissRow selCol
  decodeAfter   := fun env pre post postRoots =>
    SwissWideRowEncodes hash env d pre post preRoots postRoots
  fullClause    := fun pre post postRoots => SwissFullClause d pre post preRoots postRoots
  decodeFull    := by
    intro env pre post postRoots hrow hdec hgatesAll
    exact swissFamily_decodeFull airName selCol hash env d pre post preRoots postRoots hrow hdec hgatesAll

/-- **`swissFamily_runnable_full_sound` — THE PARAMETRIC MAGNESIUM CROWN.** A row satisfying the wide swiss
descriptor for `(airName, selCol)` (`satisfiedVm`, first/last active), under the structured decode, pins the
FULL 17-field declarative post-state: the per-cell block move/freeze AND the `system_roots` sub-block is the
swiss single-index update of `preRoots` (STURDYREF advanced, the OTHER 7 side-table roots FROZEN). The
circuit the prover ACTUALLY RUNS binds the WHOLE post-state (all 17 fields), not a per-cell projection. The
five named crowns (§4) instantiate this at each effect's selector. -/
theorem swissFamily_runnable_full_sound (airName : String) (selCol : Nat) (hash : List ℤ → ℤ)
    (env : VmRowEnv) (d : ℤ) (pre post : CellState) (preRoots postRoots : SysRoots)
    (hrow : IsSwissRow selCol env)
    (hdec : SwissWideRowEncodes hash env d pre post preRoots postRoots)
    (hsat : satisfiedVm hash (swissVmDescriptorWideFor airName selCol) env true true) :
    SwissFullClause d pre post preRoots postRoots :=
  runnable_full_sound (swissRunnableSpecFor airName selCol hash d preRoots) hash env pre post postRoots
    hrow hdec hsat

/-- **`swissFamily_rejects_root_tamper` — the PARAMETRIC whole-state anti-ghost.** Two rows satisfying the
wide swiss descriptor that publish the same `NEW_COMMIT` (with `systemRootsDigest` carriers) but whose
`system_roots` sub-blocks DIFFER at some index `i` cannot both satisfy. So a prover CANNOT keep `NEW_COMMIT`
while dropping an escrow / omitting a nullifier / reordering a queue, OR forging the STURDYREF advance — the
side-table state is bound BY the runnable commitment (the Class-C disease cured for the whole swiss family). -/
theorem swissFamily_rejects_root_tamper (airName : String) (selCol : Nat)
    (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash) (d : ℤ) (preRoots : SysRoots)
    (e₁ e₂ : VmRowEnv) (sr₁ sr₂ : SysRoots)
    (hsat₁ : satisfiedVm hash (swissVmDescriptorWideFor airName selCol) e₁ true true)
    (hsat₂ : satisfiedVm hash (swissVmDescriptorWideFor airName selCol) e₂ true true)
    (hpin₁ : e₁.loc (saCol state.STATE_COMMIT) = e₁.pub pi.NEW_COMMIT)
    (hpin₂ : e₂.loc (saCol state.STATE_COMMIT) = e₂.pub pi.NEW_COMMIT)
    (hpub : e₁.pub pi.NEW_COMMIT = e₂.pub pi.NEW_COMMIT)
    (hd₁ : e₁.loc sysRootsDigestCol = systemRootsDigest hash sr₁)
    (hd₂ : e₂.loc sysRootsDigestCol = systemRootsDigest hash sr₂)
    {i : Fin N_SYSTEM_ROOTS} (htamper : sr₁ i ≠ sr₂ i) : False :=
  wide_rejects_root_tamper (swissRunnableSpecFor airName selCol hash d preRoots) hash hCR e₁ e₂ sr₁ sr₂
    hsat₁ hsat₂ hpin₁ hpin₂ hpub hd₁ hd₂ htamper

/-! ## §4 — THE FIVE NAMED WIDE DESCRIPTORS + CROWNS (one per swiss effect, distinct selectors).

The selectors reuse the existing emit modules' indices where they exist (export `3` / handoff `4` /
drop `5`) and assign fresh indices to enliven `6` / reconcile `7` — all distinct, all `< NUM_EFFECTS`. -/

/-- swissExport selector (reuses `EffectVmEmitSwissExport.selSE.SWISS_EXPORT = 3`). -/
def SEL_SWISS_EXPORT : Nat := 3
/-- swissHandoff selector (reuses `EffectVmEmitSwissHandoff.selSH.SWISS_HANDOFF = 4`). -/
def SEL_SWISS_HANDOFF : Nat := 4
/-- swissDrop selector (reuses `EffectVmEmitSwissDrop.selSD.SWISS_DROP = 5`). -/
def SEL_SWISS_DROP : Nat := 5
/-- swissEnliven selector (fresh; distinct from the live `EXPORT/ENLIVEN/DROP/VALIDATE_HANDOFF`). -/
def SEL_SWISS_ENLIVEN : Nat := 6
/-- swissReconcile (3-vat cert-reconcile = `swissHandoffK`) selector (fresh). -/
def SEL_SWISS_RECONCILE : Nat := 7

/-- The wide swissExport descriptor. -/
def swissExportVmDescriptorWide : EffectVmDescriptor :=
  swissVmDescriptorWideFor "dregg-effectvm-swissExportA-v1-sysroots" SEL_SWISS_EXPORT
/-- The wide swissDrop descriptor. -/
def swissDropVmDescriptorWide : EffectVmDescriptor :=
  swissVmDescriptorWideFor "dregg-effectvm-swissDropA-v1-sysroots" SEL_SWISS_DROP
/-- The wide swissEnliven descriptor. -/
def swissEnlivenVmDescriptorWide : EffectVmDescriptor :=
  swissVmDescriptorWideFor "dregg-effectvm-enlivenRefA-v1-sysroots" SEL_SWISS_ENLIVEN
/-- The wide swissHandoff descriptor. -/
def swissHandoffVmDescriptorWide : EffectVmDescriptor :=
  swissVmDescriptorWideFor "dregg-effectvm-swissHandoffA-v1-sysroots" SEL_SWISS_HANDOFF
/-- The wide swissReconcile (cert-reconcile) descriptor. -/
def swissReconcileVmDescriptorWide : EffectVmDescriptor :=
  swissVmDescriptorWideFor "dregg-effectvm-swissReconcileA-v1-sysroots" SEL_SWISS_RECONCILE

/-- **`swissExport_runnable_full_sound`** — the magnesium crown for swissExport. -/
theorem swissExport_runnable_full_sound (hash : List ℤ → ℤ)
    (env : VmRowEnv) (d : ℤ) (pre post : CellState) (preRoots postRoots : SysRoots)
    (hrow : IsSwissRow SEL_SWISS_EXPORT env)
    (hdec : SwissWideRowEncodes hash env d pre post preRoots postRoots)
    (hsat : satisfiedVm hash swissExportVmDescriptorWide env true true) :
    SwissFullClause d pre post preRoots postRoots :=
  swissFamily_runnable_full_sound _ _ hash env d pre post preRoots postRoots hrow hdec hsat

/-- **`swissDrop_runnable_full_sound`** — the magnesium crown for swissDrop. -/
theorem swissDrop_runnable_full_sound (hash : List ℤ → ℤ)
    (env : VmRowEnv) (d : ℤ) (pre post : CellState) (preRoots postRoots : SysRoots)
    (hrow : IsSwissRow SEL_SWISS_DROP env)
    (hdec : SwissWideRowEncodes hash env d pre post preRoots postRoots)
    (hsat : satisfiedVm hash swissDropVmDescriptorWide env true true) :
    SwissFullClause d pre post preRoots postRoots :=
  swissFamily_runnable_full_sound _ _ hash env d pre post preRoots postRoots hrow hdec hsat

/-- **`swissEnliven_runnable_full_sound`** — the magnesium crown for swissEnliven. -/
theorem swissEnliven_runnable_full_sound (hash : List ℤ → ℤ)
    (env : VmRowEnv) (d : ℤ) (pre post : CellState) (preRoots postRoots : SysRoots)
    (hrow : IsSwissRow SEL_SWISS_ENLIVEN env)
    (hdec : SwissWideRowEncodes hash env d pre post preRoots postRoots)
    (hsat : satisfiedVm hash swissEnlivenVmDescriptorWide env true true) :
    SwissFullClause d pre post preRoots postRoots :=
  swissFamily_runnable_full_sound _ _ hash env d pre post preRoots postRoots hrow hdec hsat

/-- **`swissHandoff_runnable_full_sound`** — the magnesium crown for swissHandoff. -/
theorem swissHandoff_runnable_full_sound (hash : List ℤ → ℤ)
    (env : VmRowEnv) (d : ℤ) (pre post : CellState) (preRoots postRoots : SysRoots)
    (hrow : IsSwissRow SEL_SWISS_HANDOFF env)
    (hdec : SwissWideRowEncodes hash env d pre post preRoots postRoots)
    (hsat : satisfiedVm hash swissHandoffVmDescriptorWide env true true) :
    SwissFullClause d pre post preRoots postRoots :=
  swissFamily_runnable_full_sound _ _ hash env d pre post preRoots postRoots hrow hdec hsat

/-- **`swissReconcile_runnable_full_sound`** — the magnesium crown for swissReconcile (cert-reconcile). -/
theorem swissReconcile_runnable_full_sound (hash : List ℤ → ℤ)
    (env : VmRowEnv) (d : ℤ) (pre post : CellState) (preRoots postRoots : SysRoots)
    (hrow : IsSwissRow SEL_SWISS_RECONCILE env)
    (hdec : SwissWideRowEncodes hash env d pre post preRoots postRoots)
    (hsat : satisfiedVm hash swissReconcileVmDescriptorWide env true true) :
    SwissFullClause d pre post preRoots postRoots :=
  swissFamily_runnable_full_sound _ _ hash env d pre post preRoots postRoots hrow hdec hsat

/-! ## §5 — THE FIVE ANTI-GHOST TEETH (whole-state binding on all 8 side-table roots). -/

/-- **`swissExport_runnable_rejects_root_tamper`** — swissExport whole-state tooth. -/
theorem swissExport_runnable_rejects_root_tamper (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (d : ℤ) (preRoots : SysRoots) (e₁ e₂ : VmRowEnv) (sr₁ sr₂ : SysRoots)
    (hsat₁ : satisfiedVm hash swissExportVmDescriptorWide e₁ true true)
    (hsat₂ : satisfiedVm hash swissExportVmDescriptorWide e₂ true true)
    (hpin₁ : e₁.loc (saCol state.STATE_COMMIT) = e₁.pub pi.NEW_COMMIT)
    (hpin₂ : e₂.loc (saCol state.STATE_COMMIT) = e₂.pub pi.NEW_COMMIT)
    (hpub : e₁.pub pi.NEW_COMMIT = e₂.pub pi.NEW_COMMIT)
    (hd₁ : e₁.loc sysRootsDigestCol = systemRootsDigest hash sr₁)
    (hd₂ : e₂.loc sysRootsDigestCol = systemRootsDigest hash sr₂)
    {i : Fin N_SYSTEM_ROOTS} (htamper : sr₁ i ≠ sr₂ i) : False :=
  swissFamily_rejects_root_tamper _ _ hash hCR d preRoots e₁ e₂ sr₁ sr₂
    hsat₁ hsat₂ hpin₁ hpin₂ hpub hd₁ hd₂ htamper

/-- **`swissDrop_runnable_rejects_root_tamper`** — swissDrop whole-state tooth. -/
theorem swissDrop_runnable_rejects_root_tamper (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (d : ℤ) (preRoots : SysRoots) (e₁ e₂ : VmRowEnv) (sr₁ sr₂ : SysRoots)
    (hsat₁ : satisfiedVm hash swissDropVmDescriptorWide e₁ true true)
    (hsat₂ : satisfiedVm hash swissDropVmDescriptorWide e₂ true true)
    (hpin₁ : e₁.loc (saCol state.STATE_COMMIT) = e₁.pub pi.NEW_COMMIT)
    (hpin₂ : e₂.loc (saCol state.STATE_COMMIT) = e₂.pub pi.NEW_COMMIT)
    (hpub : e₁.pub pi.NEW_COMMIT = e₂.pub pi.NEW_COMMIT)
    (hd₁ : e₁.loc sysRootsDigestCol = systemRootsDigest hash sr₁)
    (hd₂ : e₂.loc sysRootsDigestCol = systemRootsDigest hash sr₂)
    {i : Fin N_SYSTEM_ROOTS} (htamper : sr₁ i ≠ sr₂ i) : False :=
  swissFamily_rejects_root_tamper _ _ hash hCR d preRoots e₁ e₂ sr₁ sr₂
    hsat₁ hsat₂ hpin₁ hpin₂ hpub hd₁ hd₂ htamper

/-- **`swissEnliven_runnable_rejects_root_tamper`** — swissEnliven whole-state tooth. -/
theorem swissEnliven_runnable_rejects_root_tamper (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (d : ℤ) (preRoots : SysRoots) (e₁ e₂ : VmRowEnv) (sr₁ sr₂ : SysRoots)
    (hsat₁ : satisfiedVm hash swissEnlivenVmDescriptorWide e₁ true true)
    (hsat₂ : satisfiedVm hash swissEnlivenVmDescriptorWide e₂ true true)
    (hpin₁ : e₁.loc (saCol state.STATE_COMMIT) = e₁.pub pi.NEW_COMMIT)
    (hpin₂ : e₂.loc (saCol state.STATE_COMMIT) = e₂.pub pi.NEW_COMMIT)
    (hpub : e₁.pub pi.NEW_COMMIT = e₂.pub pi.NEW_COMMIT)
    (hd₁ : e₁.loc sysRootsDigestCol = systemRootsDigest hash sr₁)
    (hd₂ : e₂.loc sysRootsDigestCol = systemRootsDigest hash sr₂)
    {i : Fin N_SYSTEM_ROOTS} (htamper : sr₁ i ≠ sr₂ i) : False :=
  swissFamily_rejects_root_tamper _ _ hash hCR d preRoots e₁ e₂ sr₁ sr₂
    hsat₁ hsat₂ hpin₁ hpin₂ hpub hd₁ hd₂ htamper

/-- **`swissHandoff_runnable_rejects_root_tamper`** — swissHandoff whole-state tooth. -/
theorem swissHandoff_runnable_rejects_root_tamper (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (d : ℤ) (preRoots : SysRoots) (e₁ e₂ : VmRowEnv) (sr₁ sr₂ : SysRoots)
    (hsat₁ : satisfiedVm hash swissHandoffVmDescriptorWide e₁ true true)
    (hsat₂ : satisfiedVm hash swissHandoffVmDescriptorWide e₂ true true)
    (hpin₁ : e₁.loc (saCol state.STATE_COMMIT) = e₁.pub pi.NEW_COMMIT)
    (hpin₂ : e₂.loc (saCol state.STATE_COMMIT) = e₂.pub pi.NEW_COMMIT)
    (hpub : e₁.pub pi.NEW_COMMIT = e₂.pub pi.NEW_COMMIT)
    (hd₁ : e₁.loc sysRootsDigestCol = systemRootsDigest hash sr₁)
    (hd₂ : e₂.loc sysRootsDigestCol = systemRootsDigest hash sr₂)
    {i : Fin N_SYSTEM_ROOTS} (htamper : sr₁ i ≠ sr₂ i) : False :=
  swissFamily_rejects_root_tamper _ _ hash hCR d preRoots e₁ e₂ sr₁ sr₂
    hsat₁ hsat₂ hpin₁ hpin₂ hpub hd₁ hd₂ htamper

/-- **`swissReconcile_runnable_rejects_root_tamper`** — swissReconcile whole-state tooth. -/
theorem swissReconcile_runnable_rejects_root_tamper (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (d : ℤ) (preRoots : SysRoots) (e₁ e₂ : VmRowEnv) (sr₁ sr₂ : SysRoots)
    (hsat₁ : satisfiedVm hash swissReconcileVmDescriptorWide e₁ true true)
    (hsat₂ : satisfiedVm hash swissReconcileVmDescriptorWide e₂ true true)
    (hpin₁ : e₁.loc (saCol state.STATE_COMMIT) = e₁.pub pi.NEW_COMMIT)
    (hpin₂ : e₂.loc (saCol state.STATE_COMMIT) = e₂.pub pi.NEW_COMMIT)
    (hpub : e₁.pub pi.NEW_COMMIT = e₂.pub pi.NEW_COMMIT)
    (hd₁ : e₁.loc sysRootsDigestCol = systemRootsDigest hash sr₁)
    (hd₂ : e₂.loc sysRootsDigestCol = systemRootsDigest hash sr₂)
    {i : Fin N_SYSTEM_ROOTS} (htamper : sr₁ i ≠ sr₂ i) : False :=
  swissFamily_rejects_root_tamper _ _ hash hCR d preRoots e₁ e₂ sr₁ sr₂
    hsat₁ hsat₂ hpin₁ hpin₂ hpub hd₁ hd₂ htamper

/-! ## §6 — NON-VACUITY: the full clause is inhabited (witness TRUE) and refutable (witness FALSE). -/

/-- A concrete pre-cell (`100`/`hi=0`/`nonce=5`/fields `0`/cap `9`/reserved `3`). -/
def goodPre : CellState :=
  { balLo := 100, balHi := 0, nonce := 5, fields := fun _ => 0, capRoot := 9, reserved := 3, commit := 0 }
/-- A concrete post-cell: nonce ticked `5 → 6`, everything else frozen (swiss is balance/cap/field-neutral
on the cell). -/
def goodPost : CellState := { goodPre with nonce := 6 }
/-- A concrete pre `system_roots` sub-block (escrow + nullifier set, to exercise the FROZEN legs). -/
def goodPreRoots : SysRoots := fun i =>
  if i = (⟨Dregg2.Exec.SystemRoots.systemRoot.ESCROW, by decide⟩ : Fin N_SYSTEM_ROOTS) then 11
  else if i = (⟨Dregg2.Exec.SystemRoots.systemRoot.NULLIFIER, by decide⟩ : Fin N_SYSTEM_ROOTS) then 22
  else 0
/-- The concrete new swiss-list digest a swiss move installs at STURDYREF. -/
def goodDigest : ℤ := 777

/-- **NON-VACUITY (witness TRUE).** A real swiss move inhabits `SwissFullClause`: nonce ticks, the per-cell
frame freezes, and the post `system_roots` IS the swiss single-index update (STURDYREF `→ 777`,
escrow/nullifier frozen). So the magnesium clause is NOT `True` — a real move satisfies it. -/
theorem goodSwiss_realizes :
    SwissFullClause goodDigest goodPre goodPost goodPreRoots (swissRootsUpdate goodPreRoots goodDigest) := by
  refine ⟨⟨rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩, rfl⟩

/-- **`swissFull_clause_not_trivial` — the clause is REFUTABLE (witness FALSE).** A post-state whose
`system_roots` is NOT the swiss update — here the STURDYREF root is left at the PRE value (`0`) instead of
advancing to `goodDigest = 777` — FAILS `SwissFullClause`. So the clause genuinely rejects a forged post (it
is not vacuously true), pinning non-vacuity from BOTH sides. -/
theorem swissFull_clause_not_trivial :
    ¬ SwissFullClause goodDigest goodPre goodPost goodPreRoots goodPreRoots := by
  rintro ⟨_, hroots⟩
  have := congrFun hroots sturdyrefIdx
  rw [swissRootsUpdate_sturdyref goodPreRoots goodDigest] at this
  simp only [goodPreRoots, sturdyrefIdx, goodDigest,
    Dregg2.Exec.SystemRoots.systemRoot.STURDYREF, Dregg2.Exec.SystemRoots.systemRoot.ESCROW,
    Dregg2.Exec.SystemRoots.systemRoot.NULLIFIER] at this
  norm_num at this

/-! ## §7 — axiom-hygiene tripwires. -/

#guard swissExportVmDescriptorWide.traceWidth == 188
#guard swissDropVmDescriptorWide.traceWidth == 188
#guard swissEnlivenVmDescriptorWide.traceWidth == 188
#guard swissHandoffVmDescriptorWide.traceWidth == 188
#guard swissReconcileVmDescriptorWide.traceWidth == 188
#guard swissExportVmDescriptorWide.hashSites.length == 4
#guard swissWideRowGates.length == 14  -- root-update + nonce-tick + 4 freeze + 8 fields
#guard decide (sturdyrefIdx.val = 3)
-- the five selectors are DISTINCT and in-range.
#guard [SEL_SWISS_EXPORT, SEL_SWISS_HANDOFF, SEL_SWISS_DROP, SEL_SWISS_ENLIVEN,
        SEL_SWISS_RECONCILE].dedup.length == 5
#guard [SEL_SWISS_EXPORT, SEL_SWISS_HANDOFF, SEL_SWISS_DROP, SEL_SWISS_ENLIVEN,
        SEL_SWISS_RECONCILE].all (· < NUM_EFFECTS)

#assert_axioms swissRootsUpdate_sturdyref
#assert_axioms swissRootsUpdate_frozen
#assert_axioms SwissFullClause_sturdyref_advance
#assert_axioms SwissFullClause_other_roots_frozen
#assert_axioms swissFamily_decodeFull
#assert_axioms swissFamily_runnable_full_sound
#assert_axioms swissFamily_rejects_root_tamper
#assert_axioms swissExport_runnable_full_sound
#assert_axioms swissDrop_runnable_full_sound
#assert_axioms swissEnliven_runnable_full_sound
#assert_axioms swissHandoff_runnable_full_sound
#assert_axioms swissReconcile_runnable_full_sound
#assert_axioms swissExport_runnable_rejects_root_tamper
#assert_axioms swissDrop_runnable_rejects_root_tamper
#assert_axioms swissEnliven_runnable_rejects_root_tamper
#assert_axioms swissHandoff_runnable_rejects_root_tamper
#assert_axioms swissReconcile_runnable_rejects_root_tamper
#assert_axioms goodSwiss_realizes
#assert_axioms swissFull_clause_not_trivial

end Dregg2.Circuit.Emit.EffectVmEmitSwissFamilyFull
