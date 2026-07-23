/-
# E10 PROOF-HALF — `cellSealFrozenPubkey`: the owner-freeze weld that closes the cellSeal
owner-forgery wound, authored BYTE-SAFE beside the deployed descriptor.

## THE WOUND (adversarially confirmed by `circuit/tests/zzz_e10_freeze_owner_falsifier.rs`)

The deployed `cellSealVmDescriptor2R24` = `cellSealV3` admits a self-consistent trace that silently
REWRITES the operated cell's OWNER key. Root cause (verified at HEAD):

  * `cellSealV3 := graduateV1 (rotateV3WithLifecyclePayloadGate … cellSealVmDescriptor)` — NOT
    `v3OfFrozen`, so it carries NONE of `frozenAuthorityColEqs` (`EffectVmEmitRotationV3.lean`),
    because cellSeal is a lifecycle MOVER.
  * The committed owner-key octet `B_PUBKEY_OCTET = 105 .. 112` (the operated cell's `public_key`,
    `rotation_witness.rs::produce` → `canonical_32_to_felts_8(cell.public_key())`) is in NO
    freeze/weld set on the cellSeal path — not in `frozenAuthorityColEqs`, not `weldsAt`, not any PI
    pin. So the AFTER owner limbs are UNFORCED free felts: a prover witnesses an AFTER block whose
    owner octet is FORGED (owner A → owner B), the record-pin / disc-gate / payload weld all hold,
    the `wireCommitR` chain is self-consistent, and NEW_COMMIT binds the stolen owner. A ledgerless
    light client cannot tell.

## THE COMPLETENESS FACT (verified in Rust, so the freeze is SOUND, not a DoS)

A faithful cellSeal PRESERVES the owner: `Cell::seal` (`cell/src/cell.rs:797`) mutates ONLY
`self.lifecycle` — it never touches `self.public_key`. So the honest AFTER `B_PUBKEY_OCTET` (filled
from `cell.public_key()`) EQUALS the BEFORE. Freezing AFTER == BEFORE therefore rejects NO honest
seal (the falsifier's honest witness has owner A before AND after; its forge is the SINGLE variable it
moves off that invariant).

## THE FIX — `gPubkeyFreeze` (HORIZONLOG), mirroring `frozenAuthorityColEqs`

Weld `AFTER B_PUBKEY_OCTET+i == BEFORE B_PUBKEY_OCTET+i` for `i = 0..7` — the SAME `colEq (w + off)
(w + AFTER_BLOCK_OFF + off)` gate shape the deployed authority freeze uses. Authored here as a NEW
hardened variant `cellSealFrozenPubkey := withCellSealPubkeyFreeze cellSealV3` (the E8 pattern): the
deployed `cellSeal` descriptor is BYTE-UNTOUCHED — zero descriptor bytes move, no VK regen. The
constraint the wrap appends is `VmConstraint2.base (colEq …)`, which is EXACTLY the object
`graduateV1` maps `frozenAuthorityColEqs`' `colEq`s to, so the deployed acceptance set of this variant
is identical to welding the same `colEq`s pre-graduation into the cellSeal descriptor.

RESOLUTION / HONEST RESIDUAL. The weld is a `.gate` (deployed `when_transition()`): it bites on
TRANSITION rows (`isLast = false`), vacuous on the wrap row — EXACTLY as the deployed
`frozenAuthorityColEqs` welds. The last-row NEW_COMMIT relevance rides the rotated block being
row-constant (the generator's pre/post replication), the SAME design basis the whole rotated-freeze
family already relies on; this variant does not change that basis. The teeth below are therefore
stated at the transition-row resolution the deployed authority-freeze teeth
(`rotateV3FrozenAuthority_rejects_drift`) use. The actual DEPLOY (welding `gPubkeyFreeze` into the live
cellSeal descriptor + a VK regen) is HELD for a clean-tree cutover window and is NOT done here.
-/
import Dregg2.Circuit.Emit.EffectVmEmitRotationV3

namespace Dregg2.Circuit.Emit.EffectVmEmitCellSealFrozenPubkey

open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.EffectVmEmitRotationV3
open Dregg2.Circuit.Emit.EffectVmEmitRotation (canon_eq_of_modEq)

/-! ## §1 — `withCellSealPubkeyFreeze`: append the 8 owner-octet BEFORE↔AFTER welds.

Structurally identical to `withAfterOctetPins` (additive, no site / range / mem-op / map-op touched),
except each appended constraint is the `frozenAuthorityColEqs`-shaped weld `colEq (w + B_PUBKEY_OCTET +
k) (w + AFTER_BLOCK_OFF + B_PUBKEY_OCTET + k)` (the owner octet frozen BEFORE↔AFTER) rather than a PI
pin. A PI pin would NOT close the wound — it binds the AFTER octet to a prover-supplied PI, which the
forger simply publishes at the forged value; the `colEq` weld forces AFTER == BEFORE regardless of any
PI. The base block sits at `EFFECT_VM_WIDTH` (`cellSealVmDescriptor.traceWidth`). -/
def withCellSealPubkeyFreeze (g : EffectVmDescriptor2) : EffectVmDescriptor2 :=
  { g with
    constraints := g.constraints ++ (List.range 8).map (fun k =>
      VmConstraint2.base (colEq (EFFECT_VM_WIDTH + B_PUBKEY_OCTET + k)
        (EFFECT_VM_WIDTH + AFTER_BLOCK_OFF + B_PUBKEY_OCTET + k))) }

/-- The 8 owner-octet welds are the ONLY constraints past the inner descriptor's (single `++`). -/
theorem withCellSealPubkeyFreeze_constraints (g : EffectVmDescriptor2) :
    (withCellSealPubkeyFreeze g).constraints
      = g.constraints ++ (List.range 8).map (fun k =>
          VmConstraint2.base (colEq (EFFECT_VM_WIDTH + B_PUBKEY_OCTET + k)
            (EFFECT_VM_WIDTH + AFTER_BLOCK_OFF + B_PUBKEY_OCTET + k))) := rfl

/-- The welds are `.base` gates, so they contribute NO mem-op (the mem log is unchanged). -/
theorem memOpsOf_withCellSealPubkeyFreeze (g : EffectVmDescriptor2) :
    memOpsOf (withCellSealPubkeyFreeze g) = memOpsOf g := by
  simp [memOpsOf, withCellSealPubkeyFreeze, List.filterMap_append, List.filterMap_map]

/-- The welds are `.base` gates, so they contribute NO map-op (the map log is unchanged). -/
theorem mapOpsOf_withCellSealPubkeyFreeze (g : EffectVmDescriptor2) :
    mapOpsOf (withCellSealPubkeyFreeze g) = mapOpsOf g := by
  simp [mapOpsOf, withCellSealPubkeyFreeze, List.filterMap_append, List.filterMap_map]

/-- **THE PEEL** — `Satisfied2 (withCellSealPubkeyFreeze g) ⟹ Satisfied2 g` (the refinement direction:
the hardened variant only REJECTS, never newly-accepts). The wrap only APPENDS `.base (colEq …)`
constraints: the inner constraints stay members (`List.mem_append_left`), sites / ranges / mem / map
logs are unchanged, so every existing per-effect soundness lemma lifts to the wrapped descriptor by
peeling the wrap first. Mirrors `satisfied2_of_withAfterOctetPins`. -/
theorem satisfied2_of_withCellSealPubkeyFreeze (hash : List ℤ → ℤ) (g : EffectVmDescriptor2)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (h : Satisfied2 hash (withCellSealPubkeyFreeze g) minit mfin maddrs t) :
    Satisfied2 hash g minit mfin maddrs t := by
  have hmem : memLog (withCellSealPubkeyFreeze g) t = memLog g t := by
    simp [memLog, memOpsOf_withCellSealPubkeyFreeze]
  have hmap : mapLog (withCellSealPubkeyFreeze g) t = mapLog g t := by
    simp [mapLog, mapOpsOf_withCellSealPubkeyFreeze]
  exact
    { rowConstraints := fun i hi c hc => h.rowConstraints i hi c (by
        rw [withCellSealPubkeyFreeze_constraints]; exact List.mem_append_left _ hc)
    , rowHashes := h.rowHashes
    , rowRanges := h.rowRanges
    , memAddrsNodup := h.memAddrsNodup
    , memClosed := fun op hop => h.memClosed op (by rw [hmem]; exact hop)
    , memDisciplined := by rw [← hmem]; exact h.memDisciplined
    , memBalanced := by rw [← hmem]; exact h.memBalanced
    , memTableFaithful := by rw [← hmem]; exact h.memTableFaithful
    , mapTableFaithful := by rw [← hmap]; exact h.mapTableFaithful }

/-- A `colEq` weld holds on ANY row of a satisfying witness given the two welded columns agree
mod `p`: on a transition row it IS the equality (`colEq_holds_iff`); on the wrap row the `.gate` is
vacuous (`holdsVm_gate_true`). The completeness workhorse. -/
theorem colEq_holds_of_modEq (env : VmRowEnv) (isFirst isLast : Bool) (a b : Nat)
    (hmod : env.loc a ≡ env.loc b [ZMOD 2013265921]) :
    (colEq a b).holdsVm env isFirst isLast := by
  cases isLast with
  | false => exact (colEq_holds_iff env isFirst false a b rfl).mpr hmod
  | true  => simp only [colEq, holdsVm_gate_true]

/-- **THE FREEZE — the owner octet is pinned BEFORE↔AFTER on every transition row.** On a
TRANSITION row (`i + 1 ≠ t.rows.length`) of a satisfying `withCellSealPubkeyFreeze g` witness, each of
the 8 committed AFTER owner-octet limbs EQUALS its BEFORE limb (mod `p`). The pubkey analog of
`rotateV3FrozenAuthority_freezes`. -/
theorem withCellSealPubkeyFreeze_freezes (hash : List ℤ → ℤ) (g : EffectVmDescriptor2)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hsat : Satisfied2 hash (withCellSealPubkeyFreeze g) minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnotlast : i + 1 ≠ t.rows.length) :
    ∀ k : Fin 8, (envAt t i).loc (EFFECT_VM_WIDTH + B_PUBKEY_OCTET + k.val)
      ≡ (envAt t i).loc (EFFECT_VM_WIDTH + AFTER_BLOCK_OFF + B_PUBKEY_OCTET + k.val)
        [ZMOD 2013265921] := by
  intro k
  have hlastb : (i + 1 == t.rows.length) = false := by
    simp only [beq_eq_false_iff_ne]; exact hnotlast
  have hin : VmConstraint2.base (colEq (EFFECT_VM_WIDTH + B_PUBKEY_OCTET + k.val)
      (EFFECT_VM_WIDTH + AFTER_BLOCK_OFF + B_PUBKEY_OCTET + k.val))
      ∈ (withCellSealPubkeyFreeze g).constraints := by
    rw [withCellSealPubkeyFreeze_constraints]
    exact List.mem_append_right _ (List.mem_map.mpr ⟨k.val, List.mem_range.mpr k.isLt, rfl⟩)
  have h := hsat.rowConstraints i hi _ hin
  simp only [VmConstraint2.holdsAt] at h
  exact (colEq_holds_iff (envAt t i) (i == 0) (i + 1 == t.rows.length) _ _ hlastb).mp h

/-! ## §2 — `cellSealFrozenPubkey`: the deployed cellSeal WITH the owner freeze. -/

/-- **`cellSealFrozenPubkey`** — the LIVE `cellSealV3` (deployed as `cellSealVmDescriptor2R24`) WITH the
8 owner-octet BEFORE↔AFTER welds. BYTE-SAFE: `cellSealV3` is untouched; the wrap is additive. Same
`piCount` / `traceWidth` (the welds add no column and no PI). -/
def cellSealFrozenPubkey : EffectVmDescriptor2 := withCellSealPubkeyFreeze cellSealV3

-- BYTE-SAFE guards: the deployed cellSeal shape is preserved; the wrap adds exactly 8 constraints and
-- NO PI / column (contrast the PI-pin wraps, which bump `piCount`).
#guard cellSealFrozenPubkey.piCount == cellSealV3.piCount
#guard cellSealFrozenPubkey.traceWidth == cellSealV3.traceWidth
#guard cellSealFrozenPubkey.constraints.length == cellSealV3.constraints.length + 8
#guard cellSealFrozenPubkey.piCount == 47

/-- **THE TOOTH — the owner-forge is UNSAT under the frozen variant.** A trace with a transition row
`i` whose AFTER owner-octet limb `k` DIFFERS from its BEFORE limb (both canonical) — i.e. exactly the
falsifier's forge (`owner A → owner B`, the AFTER owner moved off the pre-state owner) — does NOT
satisfy `cellSealFrozenPubkey`. This is the light-client bite the deployed `cellSealV3` LACKS:
`verify_vm_descriptor2` alone rejects the owner-rewriting seal, no trusted post-cell.

NON-VACUOUS: the hypothesis is realized by the falsifier's concrete forge — its assertion (i)
(`last_f[AFTER B_PUBKEY_OCTET] ≠ last_h[…]`, the octet moved) and (ii) (`AFTER owner B ≠ BEFORE owner
A`) are precisely `hforge` at limb `k`; the honest BEFORE octet stays owner A (`hcanonBefore`), the
forged AFTER is a distinct canonical owner B (`hcanonAfter`). The contradiction is derived from the
weld, not assumed. -/
theorem cellSealFrozenPubkey_rejects_owner_forge (hash : List ℤ → ℤ)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (i : Nat) (hi : i < t.rows.length) (hnotlast : i + 1 ≠ t.rows.length) (k : Fin 8)
    (hcanonBefore : 0 ≤ (envAt t i).loc (EFFECT_VM_WIDTH + B_PUBKEY_OCTET + k.val)
      ∧ (envAt t i).loc (EFFECT_VM_WIDTH + B_PUBKEY_OCTET + k.val) < 2013265921)
    (hcanonAfter : 0 ≤ (envAt t i).loc (EFFECT_VM_WIDTH + AFTER_BLOCK_OFF + B_PUBKEY_OCTET + k.val)
      ∧ (envAt t i).loc (EFFECT_VM_WIDTH + AFTER_BLOCK_OFF + B_PUBKEY_OCTET + k.val) < 2013265921)
    (hforge : (envAt t i).loc (EFFECT_VM_WIDTH + B_PUBKEY_OCTET + k.val)
      ≠ (envAt t i).loc (EFFECT_VM_WIDTH + AFTER_BLOCK_OFF + B_PUBKEY_OCTET + k.val)) :
    ¬ Satisfied2 hash cellSealFrozenPubkey minit mfin maddrs t :=
  fun hsat => hforge (canon_eq_of_modEq hcanonBefore hcanonAfter
    (withCellSealPubkeyFreeze_freezes hash cellSealV3 minit mfin maddrs t hsat i hi hnotlast k))

/-- **COMPLETENESS — every HONEST cellSeal trace still satisfies the frozen variant.** A trace that
satisfies the deployed `cellSealV3` AND preserves the owner octet (AFTER == BEFORE on every row — the
FAITHFUL-seal invariant, since `Cell::seal` never mutates `public_key`) also satisfies
`cellSealFrozenPubkey`. So the freeze is NOT a denial-of-service: it rejects exactly the owner-forgers
and keeps every honest seal. Together with the tooth, the weld is a PRECISE filter.

The preservation hypothesis is realized by the deployed producer: `rotation_witness.rs::produce` fills
BOTH the BEFORE and AFTER owner octets from `cell.public_key()`, which `Cell::seal` leaves unchanged,
and the rotated block is row-constant — so AFTER octet == BEFORE octet on every row of an honest seal.
NON-VACUOUS: the hypothesis is exactly the invariant the honest generator satisfies. -/
theorem cellSealFrozenPubkey_complete_honest (hash : List ℤ → ℤ)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hbase : Satisfied2 hash cellSealV3 minit mfin maddrs t)
    (hpreserve : ∀ i, i < t.rows.length → ∀ k : Fin 8,
        (envAt t i).loc (EFFECT_VM_WIDTH + B_PUBKEY_OCTET + k.val)
          ≡ (envAt t i).loc (EFFECT_VM_WIDTH + AFTER_BLOCK_OFF + B_PUBKEY_OCTET + k.val)
            [ZMOD 2013265921]) :
    Satisfied2 hash cellSealFrozenPubkey minit mfin maddrs t := by
  have hmem : memLog cellSealFrozenPubkey t = memLog cellSealV3 t := by
    simp [cellSealFrozenPubkey, memLog, memOpsOf_withCellSealPubkeyFreeze]
  have hmap : mapLog cellSealFrozenPubkey t = mapLog cellSealV3 t := by
    simp [cellSealFrozenPubkey, mapLog, mapOpsOf_withCellSealPubkeyFreeze]
  refine
    { rowConstraints := ?_
    , rowHashes := hbase.rowHashes
    , rowRanges := hbase.rowRanges
    , memAddrsNodup := hbase.memAddrsNodup
    , memClosed := fun op hop => hbase.memClosed op (by rw [← hmem]; exact hop)
    , memDisciplined := by rw [hmem]; exact hbase.memDisciplined
    , memBalanced := by rw [hmem]; exact hbase.memBalanced
    , memTableFaithful := by rw [hmem]; exact hbase.memTableFaithful
    , mapTableFaithful := by rw [hmap]; exact hbase.mapTableFaithful }
  intro i hi c hc
  simp only [cellSealFrozenPubkey, withCellSealPubkeyFreeze_constraints] at hc
  rcases List.mem_append.mp hc with hc0 | hc1
  · -- an inner (deployed cellSealV3) constraint — holds by the honest base witness
    exact hbase.rowConstraints i hi c hc0
  · -- one of the 8 owner-octet welds — holds by the preservation invariant (transition) / vacuous (wrap)
    simp only [List.mem_map, List.mem_range] at hc1
    obtain ⟨k, hk, rfl⟩ := hc1
    simp only [VmConstraint2.holdsAt]
    exact colEq_holds_of_modEq (envAt t i) (i == 0) (i + 1 == t.rows.length) _ _
      (hpreserve i hi ⟨k, hk⟩)

#assert_axioms satisfied2_of_withCellSealPubkeyFreeze
#assert_axioms withCellSealPubkeyFreeze_freezes
#assert_axioms cellSealFrozenPubkey_rejects_owner_forge
#assert_axioms cellSealFrozenPubkey_complete_honest

end Dregg2.Circuit.Emit.EffectVmEmitCellSealFrozenPubkey
