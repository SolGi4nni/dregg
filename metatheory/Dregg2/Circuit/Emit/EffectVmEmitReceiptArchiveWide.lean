/-
# Dregg2.Circuit.Emit.EffectVmEmitReceiptArchiveWide — the RUNNABLE `receiptArchiveA` descriptor LIFTED
to FULL-STATE (the magnesium breadth, on the circuit the prover RUNS).

## What this module closes (vs the narrow `EffectVmEmitReceiptArchive`)

`EffectVmEmitReceiptArchive.receiptArchiveVmDescriptor` is the deployed `EFFECT_VM_WIDTH = 186` audit-write
row (sets the `lifecycle` record-slot `field[1]` to the constant `1`, frame FROZEN — nonce included)
whose published `state_commit` absorbs ONLY the 13 state-block columns (`baseAbsorbedCols`). The
`system_roots` sub-block (escrow / nullifier / commitment / queue / swiss / sealedBox / delegation /
refcount) is bound ONLY by a separate record-layer commitment the row does NOT carry — the dominant
Class-C "pale ghost". Its per-cell soundness `archiveDescriptor_full_sound` pins `field[1] = 1` + the
frame freeze, but the descriptor's commitment leaves the 8 side-table roots unbound.

This module SUPERSEDES that with a verified-by-construction WIDE descriptor `archiveVmDescriptorWide`
(`EFFECT_VM_WIDTH_SYSROOTS = 188`, `hashSites = wideHashSites`) and the FULL-STATE-on-RUNNABLE crown
`receiptArchive_runnable_full_sound` — a satisfying witness of the RUNNABLE descriptor pins the FULL
17-field declarative post-state the executor produces (the per-cell block — `field[1]` SET to `1`, the
rest FROZEN — via the absorbed columns; ALL 8 side-table roots FROZEN, since the audit write touches NO
side-table — it stamps the cell-record `lifecycle` SLOT, distinct from the kernel `lifecycle` SIDE-TABLE,
which `ReceiptArchiveSpec` freezes).

## The recipe applied (`EffectVmFullStateRunnable §6`, the transfer reference template)

  * **the wide descriptor** — `receiptArchiveVmDescriptor` with `traceWidth := EFFECT_VM_WIDTH_SYSROOTS`,
    `hashSites := wideHashSites` (so `usesWideSites := rfl`). Strictly additive: the constraint list is
    byte-identical (`archiveWide_constraints_eq`); only the width grows by 2 and site 3's spare `.zero`
    4th slot becomes the `system_roots` carrier. NO root-update gate — the audit write moves NO side
    table, so the carrier is FROZEN at `before`.
  * **`isRow`** := `IsArchiveRow`; **`decodeAfter`** := `ArchiveRowEncodes` + frozen-roots witness;
    **`fullClause`** := `ArchiveCellSpec` (`field[1]` SET to `1`, the rest of the block FROZEN) AND
    `postRoots = preRoots`; **`decodeFull`** := THIN, projecting the wide gates (= the narrow's) to the
    hash-site-free `archiveGates_give_cellSpec` (a thin re-wrapping of the already-gate-only
    `archiveDescriptor_full_sound`).

The anti-ghost on ALL 17 fields falls out of the generic `runnable_full_commit_binds_or_collides` /
`wide_rejects_root_tamper_or_collides` (§4) — tamper the set `field[1]`, any absorbed cell, OR any
side-table root ⇒ the RUNNABLE descriptor is UNSAT unless a collision of the deployed sponge is
EXHIBITED.

## SURFACE — the log-receipt divergence is UNCHANGED and named.

The full clause pins the WHOLE 17-field kernel post-state. The ONE residual — the audit write's
chained motion is the self-targeted receipt prepended to `RecChainedState.log`, which is NOT a
`RecordKernelState` field and has NO EffectVM row column — is the SAME boundary the narrow header and the
Argus `ReceiptArchive.lean` weld carry: the log receipt rides universe-A's `logHashInjective` portal, NOT
this per-row state descriptor. The `lifecycle` RECORD-SLOT vs `lifecycle` SIDE-TABLE distinction is named:
the set `field[1]` is the cell-record slot; the kernel `lifecycle` side-table is one of the FROZEN frame
fields (reached by universe-A's full-state spec; it has no EffectVM column on this effect). This module
closes ONLY the side-table-root binding gap on the kernel state.

## No terminal: the teeth are UNCONDITIONAL

The §4 theorems take NO collision-resistance hypothesis. Their alternative branch hands back a specific
colliding pair of the deployed sponge (`WideColl`/`RootsColl`). The former forms carried
`Poseidon2Binding.Poseidon2SpongeCR hash`, which the deployed compressing sponge REFUTES — at deployed
BabyBear parameters they were vacuous. `#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound} on
every theorem. Imports are read-only; this file owns only itself.
-/
import Dregg2.Circuit.Emit.EffectVmEmitReceiptArchive
import Dregg2.Circuit.Emit.EffectVmFullStateRunnable

namespace Dregg2.Circuit.Emit.EffectVmEmitReceiptArchiveWide

open Dregg2.Circuit
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound (CellState)
open Dregg2.Circuit.Emit.EffectVmEmitReceiptArchive
  (IsArchiveRow archiveRowGates receiptArchiveVmDescriptor ArchiveRowEncodes ArchiveCellSpec
   archiveDescriptor_full_sound LIFE_FIELD selRA.RECEIPT_ARCHIVE)
open Dregg2.Circuit.Emit.EffectVmFullStateRunnable
  (baseAbsorbedCols wideHashSites RunnableFullStateSpec runnable_full_sound WideColl RootsColl)
open Dregg2.Exec.SystemRoots (SysRoots systemRootsDigest emptySystemRoots N_SYSTEM_ROOTS)

set_option linter.unusedVariables false

/-! ## §1 — the GATE-ONLY per-cell soundness (no hash-site hypothesis).

`archiveDescriptor_full_sound` is ALREADY gate-only (it takes `hgates : ∀ c ∈ archiveRowGates`); here we
re-wrap it to take the whole descriptor's constraints under `(true,true)` and project to the per-row
gate segment. NEITHER reads the hash sites, so the runnable per-cell soundness depends ONLY on the gates
(the sites bind the COMMITMENT — §4 — not the per-cell spec). The analog of
`EffectVmFullStateRunnable.transferGates_give_cellSpec`. -/

/-- **`archiveGates_give_cellSpec` — the GATE-ONLY per-cell soundness.** The narrow descriptor's per-row
gates (a constraint-list segment), on an audit-write row decoded by `ArchiveRowEncodes`, force
`ArchiveCellSpec` (`field[1]` SET to `1`, the rest of the block FROZEN). No hash-site hypothesis. -/
theorem archiveGates_give_cellSpec (env : VmRowEnv) (pre post : CellState)
    (henc : ArchiveRowEncodes env pre post)
    (hgates : ∀ c ∈ receiptArchiveVmDescriptor.constraints, c.holdsVm env true false) :
    ArchiveCellSpec pre post := by
  have hrowgates : ∀ c ∈ archiveRowGates, c.holdsVm env false false := by
    intro c hc
    have hmem : c ∈ receiptArchiveVmDescriptor.constraints := by
      unfold receiptArchiveVmDescriptor
      simp only [List.mem_append]
      exact Or.inl (Or.inl hc)
    have hh := hgates c hmem
    -- archiveRowGates are all `.gate _`, whose `holdsVm` ignores the flags.
    unfold archiveRowGates
      Dregg2.Circuit.Emit.EffectVmEmitReceiptArchive.gFieldFixRest at hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩ <;>
      simpa only [VmConstraint.holdsVm] using hh
  exact archiveDescriptor_full_sound env pre post henc hrowgates

#assert_axioms archiveGates_give_cellSpec

/-! ## §2 — the WIDE descriptor (the `system_roots`-absorbing runnable circuit). -/

/-- **`archiveVmDescriptorWide`** — `receiptArchiveVmDescriptor` WIDENED: the SAME per-row gates +
transitions + boundary pins, but `traceWidth := EFFECT_VM_WIDTH_SYSROOTS` and `hashSites := wideHashSites`.
Strictly additive over `receiptArchiveVmDescriptor`. -/
def archiveVmDescriptorWide : EffectVmDescriptor :=
  { receiptArchiveVmDescriptor with
    name := receiptArchiveVmDescriptor.name ++ "-sysroots"
    traceWidth := EFFECT_VM_WIDTH_SYSROOTS
    hashSites := wideHashSites }

/-- The wide audit-write descriptor's constraints ARE the narrow's. -/
theorem archiveWide_constraints_eq :
    archiveVmDescriptorWide.constraints = receiptArchiveVmDescriptor.constraints := rfl

/-! ## §3 — the FULL clause + the VALIDATED RUNNABLE instance.

The audit write touches NO side-table, so its `system_roots` sub-block is FROZEN: the full clause is the
per-cell `ArchiveCellSpec` (`field[1]` set, the rest of the block frozen) AND `postRoots = preRoots`. -/

/-- **`ReceiptArchiveFullClause`** — the full declarative post-state for the audit write over `(pre, post,
postRoots)`: the per-cell `ArchiveCellSpec` (`field[1]` SET to `1`, the rest FROZEN) AND the 8 side-table
roots FROZEN. Non-vacuous (`goodArchive_realizes` / `archive_clause_not_trivial`). -/
def ReceiptArchiveFullClause (preRoots : SysRoots)
    (pre post : CellState) (postRoots : SysRoots) : Prop :=
  ArchiveCellSpec pre post ∧ postRoots = preRoots

/-- **`archiveRunnableSpec` — the FULL-state RUNNABLE instance.** `decodeFull` projects the wide gates to
the GATE-ONLY `archiveGates_give_cellSpec`, then carries the frozen-roots fact. THIN, NON-VACUOUS. -/
def archiveRunnableSpec (preRoots : SysRoots) : RunnableFullStateSpec CellState where
  descriptor    := archiveVmDescriptorWide
  usesWideSites := rfl
  isRow         := IsArchiveRow
  decodeAfter   := fun env pre post postRoots =>
    ArchiveRowEncodes env pre post ∧ postRoots = preRoots
  fullClause    := ReceiptArchiveFullClause preRoots
  decodeFull    := by
    intro env pre post postRoots hrow hdec hgates
    obtain ⟨henc, hroots⟩ := hdec
    exact ⟨archiveGates_give_cellSpec env pre post henc
            (archiveWide_constraints_eq ▸ hgates), hroots⟩

/-- **`receiptArchive_runnable_full_sound` — THE CROWN (receipt-archive slice).** A row satisfying the
RUNNABLE wide descriptor (`satisfiedVm archiveVmDescriptorWide`, first/last active), under the structured
decode (`ArchiveRowEncodes` + frozen roots), pins the FULL 17-field declarative post-state: the per-cell
`ArchiveCellSpec` (`field[1]` SET to `1`, the rest of the block FROZEN) AND all 8 side-table roots FROZEN.
The analog of the abstract `receiptArchiveA_full_sound`, but for the circuit the prover ACTUALLY RUNS. -/
theorem receiptArchive_runnable_full_sound (hash : List ℤ → ℤ)
    (env : VmRowEnv) (pre post : CellState) (sr preRoots : SysRoots)
    (hrow : IsArchiveRow env)
    (henc : ArchiveRowEncodes env pre post) (hroots : sr = preRoots)
    (hsat : satisfiedVm hash archiveVmDescriptorWide env true false) :
    ArchiveCellSpec pre post ∧ sr = preRoots :=
  runnable_full_sound (archiveRunnableSpec preRoots) hash env pre post sr
    hrow ⟨henc, hroots⟩ hsat

#assert_axioms receiptArchive_runnable_full_sound

/-! ## §4 — ANTI-GHOST on ALL 17 fields (the generic teeth, instantiated). -/

/-- **`receiptArchive_wide_binds_full_state_or_collides` — the whole-state anti-ghost.** Two rows
satisfying the wide descriptor that publish the SAME `NEW_COMMIT`, whose carriers ARE the
`systemRootsDigest` of their post sub-blocks, EITHER agree on EVERY absorbed state-block column (the set
`field[1]` included) AND every side-table root, OR exhibit a genuine collision of the deployed sponge
(`WideColl` on the two wide preimages, or `RootsColl` on the two root lists).

The former `receiptArchive_wide_binds_full_state` concluded the bare conjunction from
`Poseidon2SpongeCR hash`. The deployed sponge REFUTES that hypothesis, so at deployed parameters that
theorem was vacuous. This disjunction is formally weaker, but it HOLDS of the deployed sponge, which the
old one did not. -/
theorem receiptArchive_wide_binds_full_state_or_collides (hash : List ℤ → ℤ)
    (e₁ e₂ : VmRowEnv) (sr₁ sr₂ : SysRoots) (preRoots : SysRoots)
    (hsat₁ : satisfiedVm hash archiveVmDescriptorWide e₁ true true)
    (hsat₂ : satisfiedVm hash archiveVmDescriptorWide e₂ true true)
    (hpin₁ : e₁.loc (saCol state.STATE_COMMIT) = e₁.pub pi.NEW_COMMIT)
    (hpin₂ : e₂.loc (saCol state.STATE_COMMIT) = e₂.pub pi.NEW_COMMIT)
    (hpub : e₁.pub pi.NEW_COMMIT = e₂.pub pi.NEW_COMMIT)
    (hd₁ : e₁.loc sysRootsDigestCol = systemRootsDigest hash sr₁)
    (hd₂ : e₂.loc sysRootsDigestCol = systemRootsDigest hash sr₂) :
    (baseAbsorbedCols e₁ = baseAbsorbedCols e₂ ∧ (∀ i : Fin N_SYSTEM_ROOTS, sr₁ i = sr₂ i))
    ∨ WideColl hash e₁ e₂ ∨ RootsColl hash sr₁ sr₂ :=
  EffectVmFullStateRunnable.runnable_full_commit_binds_or_collides (archiveRunnableSpec preRoots)
    hash e₁ e₂ sr₁ sr₂ hsat₁ hsat₂ hpin₁ hpin₂ hpub hd₁ hd₂

/-- **`receiptArchive_wide_rejects_root_tamper_or_collides` — side-table anti-ghost.** Two wide rows
publishing the same `NEW_COMMIT` (with `systemRootsDigest` carriers) whose side-table sub-blocks DIFFER
cannot both satisfy WITHOUT exhibiting a collision of the deployed sponge.

The former `receiptArchive_wide_rejects_root_tamper` concluded `False` from `Poseidon2SpongeCR hash`,
which the deployed sponge REFUTES; at deployed parameters it was vacuous. This disjunction is formally
weaker, but it HOLDS of the deployed sponge, which the old one did not. -/
theorem receiptArchive_wide_rejects_root_tamper_or_collides (hash : List ℤ → ℤ)
    (e₁ e₂ : VmRowEnv) (sr₁ sr₂ : SysRoots) (preRoots : SysRoots)
    (hsat₁ : satisfiedVm hash archiveVmDescriptorWide e₁ true true)
    (hsat₂ : satisfiedVm hash archiveVmDescriptorWide e₂ true true)
    (hpin₁ : e₁.loc (saCol state.STATE_COMMIT) = e₁.pub pi.NEW_COMMIT)
    (hpin₂ : e₂.loc (saCol state.STATE_COMMIT) = e₂.pub pi.NEW_COMMIT)
    (hpub : e₁.pub pi.NEW_COMMIT = e₂.pub pi.NEW_COMMIT)
    (hd₁ : e₁.loc sysRootsDigestCol = systemRootsDigest hash sr₁)
    (hd₂ : e₂.loc sysRootsDigestCol = systemRootsDigest hash sr₂)
    {i : Fin N_SYSTEM_ROOTS} (htamper : sr₁ i ≠ sr₂ i) :
    WideColl hash e₁ e₂ ∨ RootsColl hash sr₁ sr₂ :=
  EffectVmFullStateRunnable.wide_rejects_root_tamper_or_collides (archiveRunnableSpec preRoots)
    hash e₁ e₂ sr₁ sr₂ hsat₁ hsat₂ hpin₁ hpin₂ hpub hd₁ hd₂ htamper

#assert_axioms receiptArchive_wide_binds_full_state_or_collides
#assert_axioms receiptArchive_wide_rejects_root_tamper_or_collides

/-! ## §5 — NON-VACUITY: the full clause is INHABITED (TRUE) and REFUTABLE (FALSE), and the wide
descriptor is the genuine 188-wide `system_roots`-absorbing circuit. -/

/-- A frozen reference sub-block (the empty `system_roots`, since the audit write touches no side table). -/
def goodPreRoots : SysRoots := emptySystemRoots

/-- A pre-state for the witnesses: `field[1]` (the lifecycle slot) is `0` before; everything else 0. -/
def arPre : CellState :=
  { balLo := 0, balHi := 0, nonce := 7, fields := fun _ => 0, capRoot := 0, reserved := 0
  , commit := 0 }

/-- The post-state the audit write produces: `field[1]` SET to `1`, everything else (incl. nonce 7)
FROZEN. -/
def arPost : CellState :=
  { balLo := 0, balHi := 0, nonce := 7, fields := fun i => if i = 1 then 1 else 0, capRoot := 0
  , reserved := 0, commit := 0 }

/-- **`goodArchive_realizes` — NON-VACUITY (witness TRUE).** The receipt-archive `fullClause` is INHABITED
by a real audit write: `arPost`'s `field[1]` is `1`, every other component FROZEN (incl. the nonce — the
audit write does NOT tick it), and the roots are frozen. So the full clause is NOT `True`. -/
theorem goodArchive_realizes :
    (archiveRunnableSpec goodPreRoots).fullClause arPre arPost goodPreRoots := by
  refine ⟨⟨?_, rfl, rfl, rfl, ?_, rfl, rfl⟩, rfl⟩
  · show (if (1 : Fin 8) = 1 then (1 : ℤ) else 0) = 1
    rw [if_pos rfl]
  · intro i hi
    show (if i = 1 then (1 : ℤ) else 0) ≡ 0 [ZMOD 2013265921]
    exact EffectVmEmitTransfer.eqToModEq (if_neg hi)

/-- **`archive_clause_not_trivial` — the clause is REFUTABLE (witness FALSE).** A post-state whose
`field[1]` is NOT the constant `1` (a forged `999`) FAILS the full clause — non-vacuity from BOTH sides. -/
theorem archive_clause_not_trivial :
    ¬ ReceiptArchiveFullClause goodPreRoots arPre { arPost with fields := fun _ => 999 } goodPreRoots := by
  rintro ⟨⟨hlife, _⟩, _⟩
  -- hlife : (999) = 1
  norm_num at hlife

/-- **NON-VACUITY (the wide descriptor is the genuine 188-wide circuit).** `archiveVmDescriptorWide`
declares `traceWidth = 188` and its `hashSites` are EXACTLY the four `system_roots`-absorbing
`wideHashSites`. -/
theorem archiveWide_is_genuine :
    archiveVmDescriptorWide.traceWidth = EFFECT_VM_WIDTH_SYSROOTS
    ∧ archiveVmDescriptorWide.hashSites = wideHashSites
    ∧ archiveVmDescriptorWide.hashSites.length = 4 := by
  refine ⟨rfl, rfl, ?_⟩
  show wideHashSites.length = 4
  decide

#assert_axioms goodArchive_realizes
#assert_axioms archive_clause_not_trivial
#assert_axioms archiveWide_is_genuine

/-! ## §6 — axiom-hygiene tripwires. -/

#guard archiveVmDescriptorWide.traceWidth == 190
#guard archiveVmDescriptorWide.hashSites.length == 4
#guard archiveVmDescriptorWide.constraints.length == 13 + 14 + 4

end Dregg2.Circuit.Emit.EffectVmEmitReceiptArchiveWide
