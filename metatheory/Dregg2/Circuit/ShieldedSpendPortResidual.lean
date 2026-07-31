/-
# Dregg2.Circuit.ShieldedSpendPortResidual — the residual soundness of the shielded `spend_circuit`
# port: nullifier double-spend (in-AIR + accumulator composition), the `NoteAccumulatorCR`
# fold-walk (per-row chain ↦ `foldPath`, floor reduced to a single Poseidon2-CR floor), and the
# mod-p → ℤ conservation range-lift.

**This is Lean-authored AIR discharge, downstream of the security core.** The Rust-authored shielded
spend AIR (`circuit-prove/src/shielded/spend_circuit.rs`, width-20 `shielded_spend_descriptor()`,
C1–C7b as hand-written `ConstraintExpr` data) is house-law-#1 DEBT. Its Lean re-authoring is the two
emitted `EffectVmDescriptor2` objects Rust only *decodes/witnesses*
(`Emit.ShieldedSpendDescriptor.shieldedSpendDesc`, `Emit.ShieldedValueLinkDescriptor.shieldedValueLinkDesc`),
and the security core (`ShieldedSpendPortDischarge`, seams #15/#16) discharged `AccumulatorSound`/
`linkHolds` against those objects. This module ports the REMAINING soundness pieces the discharge
module named as residual — discharging what is dischargeable and keeping ONLY genuine crypto floors as
NAMED hypotheses (never axioms).

## §A — nullifier double-spend (the in-AIR half + the accumulator composition)

The deployed C4 binds `nullifier = hash_fact(current, key[0..4])` on the leaf row; the Lean C4′
(`lkNullifier`) binds `nullifier = hash_fact(leaf_commit, key[0..4])` with `current ≡ leaf_commit`
(C6b). This section proves the published nullifier is the nullifier of the ACTUAL spent leaf — a
GENUINELY COMMITTED note, not a free value:

  * **`emitted_nullifier_is_committed_note_nullifier`** — on a satisfying trace (sound chip table) the
    published nullifier PI ≡ the row-0 nullifier cell, which is `hash_fact(leaf_commit, key[0..4])`
    with `leaf_commit` a genuine `IsCommittedNote` (the C6 value-theft tooth) and `current ≡ leaf_commit`.
    So a replayed/forged nullifier is bound to a committed note; it cannot float free.
  * **`emitted_nullifier_determined`** — replay determinism: two satisfying spends of the SAME note
    (equal `leaf_commit`) with the SAME key publish the EXACT same nullifier cell. Spending a note
    twice yields a colliding nullifier — the detection precondition.
  * **`emitted_nullifier_double_spend_refused`** — THE COMPOSITION with the just-landed nullifier
    accumulator (`Exec.NullifierAccumulator`, over the 8-felt-keyed sorted-tree gate): once a first
    spend has committed its nullifier into the accumulator root, a second satisfying spend of the SAME
    note publishes a nullifier that admits NO valid `NfAccWitness` (`present_no_witness`). The in-AIR
    determinism (same note ⇒ same nullifier) meets the set-side non-membership (a committed nullifier
    has no fresh witness) — the double-spend is unrepresentable. We COMPOSE the landed sorted-tree
    accumulator; we do not re-prove non-membership.

## §B — the `NoteAccumulatorCR` fold-walk (per-row chain ↦ `foldPath`, floor reduced)

The discharge module named `NoteAccumulatorCR` (the ∀-leaf `AccumulatorSound` at the faithful
realization) as the residual floor and deferred "the multi-row Merkle fold-walk that recomposes the
per-row AIR chain into `foldPath` + Poseidon2 CR". This section does that recomposition and factors
the floor:

  * **`emitted_fold_step_all_rows`** — every row's `parent` IS `Hair hash current level` (generalizes
    the discharge's `emitted_fold_step_row0` off row 0; exact ℤ, from the C3 `lkParent` chip lookup).
  * **`emitted_chain_continuity`** — the C5 `chainWindow` forces `current[i+1] ≡ parent[i] [ZMOD p]`
    on every transition.
  * **`emitted_membership_chain`** — THE RECOMPOSITION: the emitted per-row chain IS an abstract
    Merkle fold — leaf `current[0]` `OpensAs` row 0's own opening cells, each step `current[i+1] ≡
    Hair hash current[i] level[i] [ZMOD p]`, and the final fold `Hair hash current[last] level[last] ≡
    the committed-accumulator PI`. The per-row AIR chain (C3 chip + C5 window) genuinely composes into
    the `foldPath` reaching the committed root (field-faithful mod-p at the junctions — a BabyBear
    Merkle proof IS a chain of mod-p equalities).
  * **`accumulatorSound_of_hashFloor`** — THE FLOOR REDUCTION: accumulator soundness at ANY note
    predicate follows from the SINGLE Poseidon2 second-preimage floor `FoldReachIsMember` (only a
    member folds to the committed root — the standard Merkle-root binding, the SAME shape as the
    deployed `SpineCommits8`/`Compress8CR` floor) PLUS the honest construction fact that members
    satisfy that predicate. The ∀-leaf assumption is no longer unbounded — it is factored into a
    bounded hash-CR floor over the accumulator's own committed set + a non-crypto construction fact.
    `noteAccumulatorCR_of_hashFloor` is its instance at `IsCommittedNote`.

## ⚑ ∃-IMAGE SWEEP CORRECTIONS (2026-07-24) — read `Dregg2.Verify.ExistsImageVacuity` first.

`IsCommittedNote` is an ∃-IMAGE: with four free field inputs onto ~2^31, the C6 site is expected to be
mod-p surjective, and then the predicate holds of EVERY felt — so a conclusion stated at it excludes
nothing. Two of this module's conclusions were stated there, and both are repaired at the resolution
the AIR actually supports:

  * `emitted_membership_chain` (i) and `emitted_nullifier_is_committed_note_nullifier` (1) now conclude
    at the CELL-PINNED `ShieldedSpendPortDischarge.OpensAs` — the opening is row 0's own cells, the
    ones C4 and C7a consume — which is strictly stronger and not vacuated by surjectivity.
  * `noteAccumulatorCR_of_hashFloor` is generalized to `accumulatorSound_of_hashFloor`, parametric in
    the note predicate, so the AUTHORIZATION-carrying instance (`ShieldedOnRampPin.IsLedgerNote`) is
    reachable through the same reduction.

⚠ **NOT strengthened to `IsLedgerNote` here, and why.** No trace-level theorem in this module can
conclude that the spent note was ledger-AUTHORIZED: a satisfying `shieldedSpendDesc` trace mentions no
ledger gate, no `Shield` entry, no committed set — the AIR relates cells to cells. Authorization is a
property of what the ACCUMULATOR contains, supplied by `ShieldedOnRampPin.shieldAppend_is_ledger_note`
(a construction fact of the Shield-A append) and carried into a spend by `accumulatorSound_of_hashFloor`
at the ledger predicate. Claiming it here would be manufacturing strength the emitted object lacks.

## §C — the mod-p → ℤ conservation range-lift

The value-link `conservation_holds` gives `Σ value ≡ Σ out_val [ZMOD p]`. Under the no-wraparound
bound (each prefix sum lands in `[0, p)`, which the `VALUE_BITS` range gadget establishes), that
congruence lifts to ℤ EQUALITY (`emitted_conservation_int`, via `modp_eq_of_bounds` — the honest
"no field wraparound disguises an over-mint" argument). The bound itself is supplied as a NAMED
hypothesis here; the in-AIR range GADGET (bit-decomposition columns proving each value `< 2^VALUE_BITS`,
`nleg_air.rs:397-408` / `Dregg2.Bignum.legs_noWrap_conservation`) is the named next lane.

## §D — #17 (the PQ / wide-commitment) verdict (assessed, not forced)

#17 is BOTH a structural port piece AND a deploy cutover — they are separable:

  * **STRUCTURAL (Lean-authorable AIR, tractable next lane).** The deployed `value_binding` is a
    1-felt (~31-bit) tag. Widening it to an 8-lane wide Poseidon output and tying conservation to the
    WIDE binding over faithful multi-limb value inputs is a Lean descriptor change: the wide chip lever
    already exists (`DescriptorIR2.chipLookupTupleN` / `ChipTableSoundN` / `chip_lookup_sound_N` forces
    every one of the W squeezed lanes). The value-link block (§B of `ShieldedValueLinkDescriptor`)
    would swap `lkValueBinding`'s 1-felt `cVB` for a `chipLookupTupleN` 8-lane digest + a multi-limb
    value encoding, and re-derive `value_link_bound` over the wide digest. Sizable (new wide golden +
    multi-limb conservation), so it is NAMED as the precise next lane, not smuggled in here.
  * **DEPLOY (Rust + VK regen, NOT Lean).** Retiring the off-AIR Ristretto three-generator Pedersen
    conservation (`commit_hidden_asset`, DLog, Shor-broken — `spend_circuit.rs:46-54`) and routing
    `apply_shielded_transfer` through the ring-clearing apex (`shielded_ring_clearing_nleg_air`) as a
    1-leg ring is the approved Option-A deploy (`docs/DECISION-shielded-redesign-2026-07-20.md`). This
    is the PQ cutover — it connects to the PQ campaign's adversary-indexed floor (the replacement is
    Poseidon-based conservation; the Ristretto DLog is the Shor-broken thing retired) — and is Rust +
    descriptor-JSON golden regen + VK regen, not a Lean theorem.

So the #17 verdict: structural-port half (wide value_binding + multi-limb conservation) is
Lean-authorable and tractable as a dedicated lane; the Ristretto-retire half is the deploy. Neither is
forced into this residual lane.

## Named residual for the rest of the port (honest)

Still open after this lane: the §D structural wide-value-binding lane; the §D Ristretto-retire deploy;
the §C in-AIR `VALUE_BITS` range GADGET (the bit-decomposition columns); the §B `FoldReachIsMember`
Poseidon2 second-preimage floor (a legitimate NAMED hash floor, the deployed `Compress8CR` shape) and
its realizable committed-accumulator construction; the field-reduction identification between the
emitted mod-p membership chain and the exact-`foldPath` floor (they coincide on the deployed
canonical-BabyBear-rep trace); and the Rust producer/emit wiring (`Effect::Custom` carrier in
`apply_shielded_transfer`, descriptor-JSON golden regen into `circuit/descriptors/` + `PROVENANCE.json`,
the apex fold supplying the committed-root PI) + the VK regen — the deploy step.

## Axiom hygiene

Bridge/composition theorems over the emitted objects + the landed accumulator; no new descriptor, no
deployed-code touch. Crypto floors enter as NAMED hypotheses (`FoldReachIsMember`, the accumulator's
`SpineCommits8` carried inside `NfAccWitness`, the §C range bound), never as axioms. `#assert_axioms`
⊆ {propext, Classical.choice, Quot.sound}. NEW file; imports read-only.
-/
import Dregg2.Circuit.ShieldedSpendPortDischarge
import Dregg2.Exec.NullifierAccumulator

namespace Dregg2.Circuit.ShieldedSpendPortResidual

open Dregg2.Circuit (Assignment)
open Dregg2.Circuit.DescriptorIR2
  (VmTrace Satisfied2 ChipTableSound TableId zeroAsg envAt chip_lookup_sound CHIP_RATE
   VmConstraint2 Lookup WindowConstraint WindowExpr)
open Dregg2.Circuit.ShieldedMerkleRootPin (Level foldPath AccumulatorSound)

set_option autoImplicit false

/-- BabyBear prime — the field-faithful modulus the emitted descriptors denote over. -/
abbrev P : ℤ := 2013265921

/-- Turn `x + -1*y ≡ 0` into `x ≡ y` (the field-faithful subtraction shape the window/pin gates emit). -/
private theorem modeq_of_sub' {x y : ℤ} (h : x + -1 * y ≡ 0 [ZMOD P]) : x ≡ y [ZMOD P] := by
  have hd := Int.modEq_iff_dvd.mp h
  have he : (0 : ℤ) - (x + -1 * y) = y - x := by ring
  rw [he] at hd
  exact Int.modEq_iff_dvd.mpr hd

/-! ## §A/§B — over the emitted spend descriptor (membership + nullifier). -/

section SpendCore

open Dregg2.Circuit.Emit.ShieldedSpendDescriptor
open Dregg2.Circuit.ShieldedSpendPortDischarge (Hair IsCommittedNote OpensAs NoteAccumulatorCR
  emitted_leaf_isCommittedNote emitted_leaf_opensAs_row0 isCommittedNote_of_opensAs)
open Dregg2.Exec.NullifierAccumulator (NfAccWitness present_no_witness)
open Dregg2.Circuit.SortedTreeNonMembershipHeap8 (keysOf8)
open Dregg2.Circuit.DeployedHeapTree (Heap8Scheme)
open Dregg2.Circuit.DeployedCapTree (Digest8)

/-! ### §A — nullifier double-spend. -/

/-- **⚑ THE #A DISCHARGE (`emitted_nullifier_is_committed_note_nullifier`).** On a satisfying
`shieldedSpendDesc` trace (under the chip AIR's own soundness) the published nullifier is bound to the
ACTUAL spent leaf, which is the C6 commitment of row 0's OWN opening cells — not a free value: the
row-0 `leaf_commit` `OpensAs` `(cVAL, cASSET, cOWNER, cRAND)` (C6a); the nullifier cell is
`hash_fact(leaf_commit, key[0..4])` (C4′); the membership `current ≡ leaf_commit` (C6b); and the
published nullifier PI ≡ that cell. A replayed or forged nullifier is therefore the nullifier OF the
note whose opening the spender exhibited in-trace.

⚑ **STRENGTHENED 2026-07-24** (same class as the five sites the ∃-image sweep named, found in this
file): conjunct 1 was the ∃-image `IsCommittedNote hash cLEAF`, vacuous under
`ShieldedOnRampPin.C6Surjective`; it is now the cell-pinned `OpensAs`, whose cells are the ones the
value-link block also consumes. ⚠ Authorization is still NOT here — see
`ShieldedSpendPortDischarge.emitted_leaf_isCommittedNote` for why the AIR cannot force it. -/
theorem emitted_nullifier_is_committed_note_nullifier (hash : List ℤ → ℤ) (minit : ℤ → ℤ)
    (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace) (hne : t.rows ≠ [])
    (hsat : Satisfied2 hash shieldedSpendDesc minit mfin maddrs t)
    (hChip : ChipTableSound hash (t.tf TableId.poseidon2))
    (hwire : t.tf Dregg2.Circuit.DescriptorIR2.poseidon2narrow
      = Dregg2.Circuit.ChipNarrowLookup.narrowTable (t.tf TableId.poseidon2)) :
    OpensAs hash ((t.rows.getD 0 zeroAsg) cLEAF) ((t.rows.getD 0 zeroAsg) cVAL)
      ((t.rows.getD 0 zeroAsg) cASSET) ((t.rows.getD 0 zeroAsg) cOWNER)
      ((t.rows.getD 0 zeroAsg) cRAND)
    ∧ (t.rows.getD 0 zeroAsg) cNUL
        = hash [(t.rows.getD 0 zeroAsg) cLEAF, (t.rows.getD 0 zeroAsg) cKEY0,
                (t.rows.getD 0 zeroAsg) cKEY1, (t.rows.getD 0 zeroAsg) cKEY2,
                (t.rows.getD 0 zeroAsg) cKEY3, NS_FACT_MARK, 1]
    ∧ ((t.rows.getD 0 zeroAsg) cCUR ≡ (t.rows.getD 0 zeroAsg) cLEAF [ZMOD P])
    ∧ (t.pub piNUL ≡ (t.rows.getD 0 zeroAsg) cNUL [ZMOD P]) := by
  have hrel := spend_relation_row0 hash minit mfin maddrs t hne hsat hChip hwire
  refine ⟨?_, hrel.2.1, hrel.2.2.2.2.1, (hrel.2.2.2.2.2.1).symm⟩
  unfold OpensAs
  rw [hrel.2.2.1]

/-- **⚑ REPLAY DETERMINISM (`emitted_nullifier_determined`).** Two satisfying spends of the SAME note
(equal row-0 `leaf_commit`) with the SAME key publish the EXACT same nullifier cell. Spending a note a
second time cannot produce a fresh nullifier — the nullifier is a deterministic image of (committed
note, key). This is the in-AIR precondition the accumulator freshness gate then closes. -/
theorem emitted_nullifier_determined (hash : List ℤ → ℤ)
    (minit₁ minit₂ : ℤ → ℤ) (mfin₁ mfin₂ : ℤ → ℤ × Nat) (maddrs₁ maddrs₂ : List ℤ)
    (t₁ t₂ : VmTrace) (hne₁ : t₁.rows ≠ []) (hne₂ : t₂.rows ≠ [])
    (hsat₁ : Satisfied2 hash shieldedSpendDesc minit₁ mfin₁ maddrs₁ t₁)
    (hsat₂ : Satisfied2 hash shieldedSpendDesc minit₂ mfin₂ maddrs₂ t₂)
    (hChip₁ : ChipTableSound hash (t₁.tf TableId.poseidon2))
    (hwire₁ : t₁.tf Dregg2.Circuit.DescriptorIR2.poseidon2narrow
      = Dregg2.Circuit.ChipNarrowLookup.narrowTable (t₁.tf TableId.poseidon2))
    (hChip₂ : ChipTableSound hash (t₂.tf TableId.poseidon2))
    (hwire₂ : t₂.tf Dregg2.Circuit.DescriptorIR2.poseidon2narrow
      = Dregg2.Circuit.ChipNarrowLookup.narrowTable (t₂.tf TableId.poseidon2))
    (hLeaf : (t₂.rows.getD 0 zeroAsg) cLEAF = (t₁.rows.getD 0 zeroAsg) cLEAF)
    (hk0 : (t₂.rows.getD 0 zeroAsg) cKEY0 = (t₁.rows.getD 0 zeroAsg) cKEY0)
    (hk1 : (t₂.rows.getD 0 zeroAsg) cKEY1 = (t₁.rows.getD 0 zeroAsg) cKEY1)
    (hk2 : (t₂.rows.getD 0 zeroAsg) cKEY2 = (t₁.rows.getD 0 zeroAsg) cKEY2)
    (hk3 : (t₂.rows.getD 0 zeroAsg) cKEY3 = (t₁.rows.getD 0 zeroAsg) cKEY3) :
    (t₂.rows.getD 0 zeroAsg) cNUL = (t₁.rows.getD 0 zeroAsg) cNUL := by
  have e1 := (spend_relation_row0 hash minit₁ mfin₁ maddrs₁ t₁ hne₁ hsat₁ hChip₁ hwire₁).2.1
  have e2 := (spend_relation_row0 hash minit₂ mfin₂ maddrs₂ t₂ hne₂ hsat₂ hChip₂ hwire₂).2.1
  rw [e2, e1, hLeaf, hk0, hk1, hk2, hk3]

/-- **⚑ THE SCOPE CORRECTION, CLOSED (`emitted_same_note_forces_same_key`).**

The correction below said: `hk0..hk3` ("SAME key") are HYPOTHESES an adversary controls, because
`cKEY0..cKEY3` occurred in `lkNullifier` and in NO other constraint, and `cOWNER` occurred only inside
`lkLeafCommit`, with nothing relating them. A prover could spend the same note under a fresh key,
publish a different nullifier, satisfy the AIR, and meet no accumulator member.

The missing constraint now exists: `ShieldedSpendDescriptor.lkOwnerDerive` (C8) forces
`owner = hash_fact(key[0..4])`. So the key is DERIVED FROM THE NOTE: the leaf commits the owner, the
owner commits the key. Two satisfying spends of the SAME note either carry the SAME key — making
`hk0..hk3` derived rather than assumed — or exhibit a Poseidon2 collision. There is no third option,
and the "fresh key per spend" double-spend is gone with it. -/
theorem emitted_same_note_forces_same_key (hash : List ℤ → ℤ)
    (minit₁ minit₂ : ℤ → ℤ) (mfin₁ mfin₂ : ℤ → ℤ × Nat) (maddrs₁ maddrs₂ : List ℤ)
    (t₁ t₂ : VmTrace) (hne₁ : t₁.rows ≠ []) (hne₂ : t₂.rows ≠ [])
    (hsat₁ : Satisfied2 hash shieldedSpendDesc minit₁ mfin₁ maddrs₁ t₁)
    (hsat₂ : Satisfied2 hash shieldedSpendDesc minit₂ mfin₂ maddrs₂ t₂)
    (hChip₁ : ChipTableSound hash (t₁.tf TableId.poseidon2))
    (hwire₁ : t₁.tf Dregg2.Circuit.DescriptorIR2.poseidon2narrow
      = Dregg2.Circuit.ChipNarrowLookup.narrowTable (t₁.tf TableId.poseidon2))
    (hChip₂ : ChipTableSound hash (t₂.tf TableId.poseidon2))
    (hwire₂ : t₂.tf Dregg2.Circuit.DescriptorIR2.poseidon2narrow
      = Dregg2.Circuit.ChipNarrowLookup.narrowTable (t₂.tf TableId.poseidon2))
    (hLeaf : (t₂.rows.getD 0 zeroAsg) cLEAF = (t₁.rows.getD 0 zeroAsg) cLEAF) :
    ((t₂.rows.getD 0 zeroAsg) cKEY0 = (t₁.rows.getD 0 zeroAsg) cKEY0
      ∧ (t₂.rows.getD 0 zeroAsg) cKEY1 = (t₁.rows.getD 0 zeroAsg) cKEY1
      ∧ (t₂.rows.getD 0 zeroAsg) cKEY2 = (t₁.rows.getD 0 zeroAsg) cKEY2
      ∧ (t₂.rows.getD 0 zeroAsg) cKEY3 = (t₁.rows.getD 0 zeroAsg) cKEY3)
    ∨ (∃ xs ys : List ℤ, xs ≠ ys ∧ hash xs = hash ys) := by
  -- C6a on both traces: the leaf IS the hash of its opening cells.
  have eL1 := (spend_relation_row0 hash minit₁ mfin₁ maddrs₁ t₁ hne₁ hsat₁ hChip₁ hwire₁).2.2.1
  have eL2 := (spend_relation_row0 hash minit₂ mfin₂ maddrs₂ t₂ hne₂ hsat₂ hChip₂ hwire₂).2.2.1
  -- equal leaves ⇒ the two opening blocks have equal hashes.
  have hcollL : hash [(t₂.rows.getD 0 zeroAsg) cVAL, (t₂.rows.getD 0 zeroAsg) cASSET,
      (t₂.rows.getD 0 zeroAsg) cOWNER, (t₂.rows.getD 0 zeroAsg) cRAND, 0, NS_FACT_MARK, 1]
      = hash [(t₁.rows.getD 0 zeroAsg) cVAL, (t₁.rows.getD 0 zeroAsg) cASSET,
        (t₁.rows.getD 0 zeroAsg) cOWNER, (t₁.rows.getD 0 zeroAsg) cRAND, 0, NS_FACT_MARK, 1] := by
    rw [← eL1, ← eL2]; exact hLeaf
  by_cases hLists : ([(t₂.rows.getD 0 zeroAsg) cVAL, (t₂.rows.getD 0 zeroAsg) cASSET,
      (t₂.rows.getD 0 zeroAsg) cOWNER, (t₂.rows.getD 0 zeroAsg) cRAND, 0, NS_FACT_MARK, 1] :
      List ℤ)
      = [(t₁.rows.getD 0 zeroAsg) cVAL, (t₁.rows.getD 0 zeroAsg) cASSET,
        (t₁.rows.getD 0 zeroAsg) cOWNER, (t₁.rows.getD 0 zeroAsg) cRAND, 0, NS_FACT_MARK, 1]
  · -- the opening blocks agree ⇒ the OWNERS agree.
    have hOwner : (t₂.rows.getD 0 zeroAsg) cOWNER = (t₁.rows.getD 0 zeroAsg) cOWNER := by
      simp only [List.cons.injEq] at hLists
      exact hLists.2.2.1
    -- C8 on both traces: the owner IS the hash of the key limbs.
    have eO1 := owner_is_derived_row0 hash minit₁ mfin₁ maddrs₁ t₁ hne₁ hsat₁ hChip₁ hwire₁
    have eO2 := owner_is_derived_row0 hash minit₂ mfin₂ maddrs₂ t₂ hne₂ hsat₂ hChip₂ hwire₂
    have hcollK : hash [(t₂.rows.getD 0 zeroAsg) cKEY0, (t₂.rows.getD 0 zeroAsg) cKEY1,
        (t₂.rows.getD 0 zeroAsg) cKEY2, (t₂.rows.getD 0 zeroAsg) cKEY3, 0, NS_FACT_MARK, 1]
        = hash [(t₁.rows.getD 0 zeroAsg) cKEY0, (t₁.rows.getD 0 zeroAsg) cKEY1,
          (t₁.rows.getD 0 zeroAsg) cKEY2, (t₁.rows.getD 0 zeroAsg) cKEY3, 0, NS_FACT_MARK, 1] := by
      rw [← eO1, ← eO2]; exact hOwner
    by_cases hK : ([(t₂.rows.getD 0 zeroAsg) cKEY0, (t₂.rows.getD 0 zeroAsg) cKEY1,
        (t₂.rows.getD 0 zeroAsg) cKEY2, (t₂.rows.getD 0 zeroAsg) cKEY3, 0, NS_FACT_MARK, 1] :
        List ℤ)
        = [(t₁.rows.getD 0 zeroAsg) cKEY0, (t₁.rows.getD 0 zeroAsg) cKEY1,
          (t₁.rows.getD 0 zeroAsg) cKEY2, (t₁.rows.getD 0 zeroAsg) cKEY3, 0, NS_FACT_MARK, 1]
    · simp only [List.cons.injEq] at hK
      exact Or.inl ⟨hK.1, hK.2.1, hK.2.2.1, hK.2.2.2.1⟩
    · exact Or.inr ⟨_, _, hK, hcollK⟩
  · exact Or.inr ⟨_, _, hLists, hcollL⟩

/-- **⚑ THE #A COMPOSITION (`emitted_nullifier_double_spend_refused`).**
⚠ **SCOPE CORRECTION 2026-07-30 — read the hypotheses before citing this.** The line below reads
"The full double-spend closure". It is NOT full, and the missing half is adversary-controlled:
`hk0..hk3` ("SAME key") are HYPOTHESES, and `cKEY0..cKEY3` occur in `lkNullifier` and in NO other
constraint of `shieldedSpendDesc` — nothing relates them to `cOWNER`, which likewise occurs only
inside `lkLeafCommit`. A prover spending the same note under a different key therefore publishes a
DIFFERENT nullifier, satisfies the AIR, and meets no accumulator member. What this theorem closes is
REPLAY WITH THE SAME KEY. Closing double-spend needs an in-AIR key↔owner derivation
(`owner = hash(key…)`, the Zcash `ivk`-shape binding) that no shielded descriptor in this tree emits.
The full double-spend closure:
the in-AIR nullifier binding (replay determinism) COMPOSED with the landed sorted-tree nullifier
accumulator (`Exec.NullifierAccumulator`, 8-felt-keyed). Once a first satisfying spend of a note has
committed its nullifier into the accumulator root `root`, a SECOND satisfying spend of the SAME note
(equal `leaf_commit`, equal key) publishes a nullifier that admits NO valid `NfAccWitness` — the
non-membership proof the replay would need does not exist (`present_no_witness`). We compose the landed
accumulator's `present_no_witness`; we do not re-prove non-membership. -/
theorem emitted_nullifier_double_spend_refused (hash : List ℤ → ℤ)
    (minit₁ minit₂ : ℤ → ℤ) (mfin₁ mfin₂ : ℤ → ℤ × Nat) (maddrs₁ maddrs₂ : List ℤ)
    (t₁ t₂ : VmTrace) (hne₁ : t₁.rows ≠ []) (hne₂ : t₂.rows ≠ [])
    (hsat₁ : Satisfied2 hash shieldedSpendDesc minit₁ mfin₁ maddrs₁ t₁)
    (hsat₂ : Satisfied2 hash shieldedSpendDesc minit₂ mfin₂ maddrs₂ t₂)
    (hChip₁ : ChipTableSound hash (t₁.tf TableId.poseidon2))
    (hwire₁ : t₁.tf Dregg2.Circuit.DescriptorIR2.poseidon2narrow
      = Dregg2.Circuit.ChipNarrowLookup.narrowTable (t₁.tf TableId.poseidon2))
    (hChip₂ : ChipTableSound hash (t₂.tf TableId.poseidon2))
    (hwire₂ : t₂.tf Dregg2.Circuit.DescriptorIR2.poseidon2narrow
      = Dregg2.Circuit.ChipNarrowLookup.narrowTable (t₂.tf TableId.poseidon2))
    (hLeaf : (t₂.rows.getD 0 zeroAsg) cLEAF = (t₁.rows.getD 0 zeroAsg) cLEAF)
    (hk0 : (t₂.rows.getD 0 zeroAsg) cKEY0 = (t₁.rows.getD 0 zeroAsg) cKEY0)
    (hk1 : (t₂.rows.getD 0 zeroAsg) cKEY1 = (t₁.rows.getD 0 zeroAsg) cKEY1)
    (hk2 : (t₂.rows.getD 0 zeroAsg) cKEY2 = (t₁.rows.getD 0 zeroAsg) cKEY2)
    (hk3 : (t₂.rows.getD 0 zeroAsg) cKEY3 = (t₁.rows.getD 0 zeroAsg) cKEY3)
    (S8 : Heap8Scheme) (root : Digest8)
    (hspent : (t₁.rows.getD 0 zeroAsg) cNUL ∈ keysOf8 S8 root) :
    IsEmpty (NfAccWitness S8 root ((t₂.rows.getD 0 zeroAsg) cNUL)) := by
  have hdet := emitted_nullifier_determined hash minit₁ minit₂ mfin₁ mfin₂ maddrs₁ maddrs₂
    t₁ t₂ hne₁ hne₂ hsat₁ hsat₂ hChip₁ hwire₁ hChip₂ hwire₂ hLeaf hk0 hk1 hk2 hk3
  rw [hdet]
  exact present_no_witness hspent

/-- **`emitted_nullifier_double_spend_refused_derived_key` — the double-spend closure WITHOUT the
key hypotheses.** A second satisfying spend of the same note admits no accumulator non-membership
witness — or the deployed Poseidon2 collides. The four `hk0..hk3` assumptions are gone: C8 derives
them. -/
theorem emitted_nullifier_double_spend_refused_derived_key (hash : List ℤ → ℤ)
    (minit₁ minit₂ : ℤ → ℤ) (mfin₁ mfin₂ : ℤ → ℤ × Nat) (maddrs₁ maddrs₂ : List ℤ)
    (t₁ t₂ : VmTrace) (hne₁ : t₁.rows ≠ []) (hne₂ : t₂.rows ≠ [])
    (hsat₁ : Satisfied2 hash shieldedSpendDesc minit₁ mfin₁ maddrs₁ t₁)
    (hsat₂ : Satisfied2 hash shieldedSpendDesc minit₂ mfin₂ maddrs₂ t₂)
    (hChip₁ : ChipTableSound hash (t₁.tf TableId.poseidon2))
    (hwire₁ : t₁.tf Dregg2.Circuit.DescriptorIR2.poseidon2narrow
      = Dregg2.Circuit.ChipNarrowLookup.narrowTable (t₁.tf TableId.poseidon2))
    (hChip₂ : ChipTableSound hash (t₂.tf TableId.poseidon2))
    (hwire₂ : t₂.tf Dregg2.Circuit.DescriptorIR2.poseidon2narrow
      = Dregg2.Circuit.ChipNarrowLookup.narrowTable (t₂.tf TableId.poseidon2))
    (hLeaf : (t₂.rows.getD 0 zeroAsg) cLEAF = (t₁.rows.getD 0 zeroAsg) cLEAF)
    (S8 : Heap8Scheme) (root : Digest8)
    (hspent : (t₁.rows.getD 0 zeroAsg) cNUL ∈ keysOf8 S8 root) :
    IsEmpty (NfAccWitness S8 root ((t₂.rows.getD 0 zeroAsg) cNUL))
      ∨ (∃ xs ys : List ℤ, xs ≠ ys ∧ hash xs = hash ys) := by
  rcases emitted_same_note_forces_same_key hash minit₁ minit₂ mfin₁ mfin₂ maddrs₁ maddrs₂
    t₁ t₂ hne₁ hne₂ hsat₁ hsat₂ hChip₁ hwire₁ hChip₂ hwire₂ hLeaf with
    ⟨hk0, hk1, hk2, hk3⟩ | hcoll
  · exact Or.inl (emitted_nullifier_double_spend_refused hash minit₁ minit₂ mfin₁ mfin₂
      maddrs₁ maddrs₂ t₁ t₂ hne₁ hne₂ hsat₁ hsat₂ hChip₁ hwire₁ hChip₂ hwire₂ hLeaf
      hk0 hk1 hk2 hk3 S8 root hspent)
  · exact Or.inr hcoll

/-! ### §B — the `NoteAccumulatorCR` fold-walk. -/

/-- The running membership hash at row `i` (row 0 = the leaf = the committed note commitment). -/
def curAt (t : VmTrace) (i : Nat) : ℤ := (t.rows.getD i zeroAsg) cCUR

/-- The Merkle level absorbed at row `i` (`[sib0, sib1, sib2, position]`). -/
def levelAt (t : VmTrace) (i : Nat) : Level :=
  ⟨(t.rows.getD i zeroAsg) cSIB0, (t.rows.getD i zeroAsg) cSIB1,
   (t.rows.getD i zeroAsg) cSIB2, (t.rows.getD i zeroAsg) cPOS⟩

/-- **`emitted_fold_step_all_rows`.** Every row's `parent` cell IS `Hair hash current level` — the
abstract per-level fold realized at the emitted `lkParent` chip site, on EVERY row (generalizes the
discharge's `emitted_fold_step_row0` off row 0). Exact ℤ, from the C3 chip lookup under a sound chip
table. -/
theorem emitted_fold_step_all_rows (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat)
    (maddrs : List ℤ) (t : VmTrace)
    (hsat : Satisfied2 hash shieldedSpendDesc minit mfin maddrs t)
    (hChip : ChipTableSound hash (t.tf TableId.poseidon2))
    (hwire : t.tf Dregg2.Circuit.DescriptorIR2.poseidon2narrow
      = Dregg2.Circuit.ChipNarrowLookup.narrowTable (t.tf TableId.poseidon2)) :
    ∀ i, i < t.rows.length →
      (t.rows.getD i zeroAsg) cPAR = Hair hash (curAt t i) (levelAt t i) := by
  intro i hi
  have hkP := hsat.rowConstraints i hi lkParent
    (by simp [shieldedSpendDesc, spendConstraints])
  simp only [lkParent, Dregg2.Circuit.DescriptorIR2.VmConstraint2.holdsAt,
    Dregg2.Circuit.DescriptorIR2.Lookup.holdsAt] at hkP
  have hlen5 : (factIns [cCUR, cSIB0, cSIB1, cSIB2, cPOS]).length ≤ CHIP_RATE := by decide
  rw [hwire] at hkP
  have eP := Dregg2.Circuit.ChipNarrowLookup.chip_lookup_narrow_sound_of_wide_table hash
    (t.tf TableId.poseidon2) hChip ((envAt t i).loc) _ cPAR hlen5 hkP
  rw [factIns_eval_5] at eP
  simpa [Hair, curAt, levelAt, envAt] using eP

/-- **`emitted_chain_continuity`.** The C5 `chainWindow` transition forces `current[i+1] ≡ parent[i]
[ZMOD p]` on every transition — the per-row chain is threaded end to end. -/
theorem emitted_chain_continuity (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat)
    (maddrs : List ℤ) (t : VmTrace)
    (hsat : Satisfied2 hash shieldedSpendDesc minit mfin maddrs t) :
    ∀ i, i + 1 < t.rows.length →
      (t.rows.getD (i + 1) zeroAsg) cCUR ≡ (t.rows.getD i zeroAsg) cPAR [ZMOD P] := by
  intro i hi
  have hi' : i < t.rows.length := by omega
  have h := hsat.rowConstraints i hi' (.windowGate ⟨chainWindow, true⟩)
    (by simp [shieldedSpendDesc, spendConstraints])
  have hlf : (i + 1 == t.rows.length) = false := by
    have hx : i + 1 ≠ t.rows.length := by omega
    simpa using hx
  simp only [Dregg2.Circuit.DescriptorIR2.VmConstraint2.holdsAt,
    Dregg2.Circuit.DescriptorIR2.WindowConstraint.holdsAt, if_true] at h
  have h1 := h hlf
  simp only [chainWindow, Dregg2.Circuit.DescriptorIR2.WindowExpr.eval, envAt] at h1
  exact modeq_of_sub' h1

/-- **⚑ THE #B RECOMPOSITION (`emitted_membership_chain`).** The emitted per-row Merkle chain (C3 chip
+ C5 window) IS an abstract `foldPath` reaching the committed-accumulator root: (i) the leaf
`current[0]` is the C6 commitment of row 0's OWN opening cells; (ii) each step `current[i+1] ≡ Hair
hash current[i] level[i] [ZMOD p]` — the fold advances by one `Hair` per level; (iii) the final fold
`Hair hash current[last] level[last] ≡ pi[committed_root] [ZMOD p]`. The deferred multi-row fold-walk
the discharge module named is now recomposed — field-faithful mod-p at the junctions (a BabyBear Merkle
proof IS a chain of mod-p equalities).

⚑ **STRENGTHENED 2026-07-24 (∃-image sweep).** Conjunct (i) was the ∃-image `IsCommittedNote hash
current[0]`, which under `ShieldedOnRampPin.C6Surjective` holds of every felt and so excluded nothing;
it is now the cell-pinned `OpensAs`, from which the ∃-image follows by `isCommittedNote_of_opensAs`.
⚠ It is NOT strengthened to `ShieldedOnRampPin.IsLedgerNote`, because the chain establishes REACH — the
leaf folds to the committed root — and reach only carries authorization when the ACCUMULATOR is sound
at an authorization-carrying note predicate. That is exactly what `accumulatorSound_of_hashFloor` below
supplies and what `ShieldedOnRampPin.shieldA_pin_spends_authorized` instantiates; no rearrangement of
this trace-level statement can produce it. -/
theorem emitted_membership_chain (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat)
    (maddrs : List ℤ) (t : VmTrace) (hne : t.rows ≠ [])
    (hsat : Satisfied2 hash shieldedSpendDesc minit mfin maddrs t)
    (hChip : ChipTableSound hash (t.tf TableId.poseidon2))
    (hwire : t.tf Dregg2.Circuit.DescriptorIR2.poseidon2narrow
      = Dregg2.Circuit.ChipNarrowLookup.narrowTable (t.tf TableId.poseidon2)) :
    OpensAs hash ((t.rows.getD 0 zeroAsg) cCUR) ((t.rows.getD 0 zeroAsg) cVAL)
      ((t.rows.getD 0 zeroAsg) cASSET) ((t.rows.getD 0 zeroAsg) cOWNER)
      ((t.rows.getD 0 zeroAsg) cRAND)
    ∧ (∀ i, i + 1 < t.rows.length →
        (t.rows.getD (i + 1) zeroAsg) cCUR ≡ Hair hash (curAt t i) (levelAt t i) [ZMOD P])
    ∧ (Hair hash (curAt t (t.rows.length - 1)) (levelAt t (t.rows.length - 1))
        ≡ t.pub piCOMMITTED [ZMOD P]) := by
  have hpos : 0 < t.rows.length := by
    cases hr : t.rows with
    | nil => exact absurd hr hne
    | cons a l => simp
  refine ⟨emitted_leaf_opensAs_row0 hash minit mfin maddrs t hne hsat hChip hwire, ?_, ?_⟩
  · intro i hi
    have hstep := emitted_fold_step_all_rows hash minit mfin maddrs t hsat hChip hwire i (by omega)
    have hcont := emitted_chain_continuity hash minit mfin maddrs t hsat i hi
    rw [hstep] at hcont
    exact hcont
  · have hlast := (root_is_pinned hash minit mfin maddrs t hne hsat).2.1
    have hstep := emitted_fold_step_all_rows hash minit mfin maddrs t hsat hChip hwire
      (t.rows.length - 1) (by omega)
    rw [hstep] at hlast
    exact hlast

/-- The SINGLE Poseidon2 second-preimage floor of the emitted fold over the committed accumulator's
own member set `member`: only a genuinely-committed member folds to the committed root. This is the
standard Merkle-root binding — the SAME shape as the deployed `SpineCommits8`/`Compress8CR` floor —
NOT an unbounded per-leaf assumption. -/
def FoldReachIsMember (hash : List ℤ → ℤ) (committedRoot : ℤ) (member : ℤ → Prop) : Prop :=
  ∀ leaf path, foldPath (Hair hash) leaf path = committedRoot → member leaf

/-- **⚑ THE #B FLOOR REDUCTION (`accumulatorSound_of_hashFloor`, GENERALIZED 2026-07-24).** The
discharge module's ∀-leaf floor (`AccumulatorSound` at the faithful `Hair` realization) FOLLOWS FROM
the single Poseidon2-CR floor `FoldReachIsMember` (bounded, over the accumulator's own committed set)
PLUS the honest construction fact that every member satisfies the note predicate (the accumulator only
inserts leaves it built — no crypto). The ∀-leaf assumption is thereby factored into a legitimate
hash-CR floor + a construction fact; it is no longer an unbounded per-leaf assumption.

The note predicate is a PARAMETER, because nothing in the argument ever wanted the ∃-image: the
conclusion is exactly as strong as the construction fact supplied. Instantiate `note :=
ShieldedOnRampPin.IsLedgerNote hash auth` — whose construction fact is
`ShieldedOnRampPin.shieldAppend_is_ledger_note`, true by construction of the Shield-A append — and the
accumulator is sound at the AUTHORIZATION-carrying predicate, which is what
`ShieldedOnRampPin.shieldA_pin_spends_authorized` then spends against. Instantiate it at
`IsCommittedNote` and you get `noteAccumulatorCR_of_hashFloor`, which is vacuous under
`ShieldedOnRampPin.C6Surjective` (it holds at every root, including a prover-written one). -/
theorem accumulatorSound_of_hashFloor (hash : List ℤ → ℤ) (committedRoot : ℤ) (member note : ℤ → Prop)
    (members_are_notes : ∀ leaf, member leaf → note leaf)
    (floor : FoldReachIsMember hash committedRoot member) :
    AccumulatorSound (Hair hash) note committedRoot := by
  intro leaf path hfold
  exact members_are_notes leaf (floor leaf path hfold)

/-- **The floor reduction at the ∃-image note predicate** — `accumulatorSound_of_hashFloor`
instantiated at `IsCommittedNote`, kept because downstream consumes it in this shape
(`ShieldedOnRampPin.shieldA_noteAccumulatorCR`, `ShieldedSpendFoldReachRealized.noteAccumulatorCR_realized`).

⚠ **HONEST WEAKENING.** The conclusion `NoteAccumulatorCR` is vacuous at the deployed parameters
(`ShieldedOnRampPin.noteAccumulatorCR_vacuous_of_c6Surjective:363`); this instance therefore prices
nothing on its own. The instance that prices something is the same theorem at
`note := IsLedgerNote hash auth`. -/
theorem noteAccumulatorCR_of_hashFloor (hash : List ℤ → ℤ) (committedRoot : ℤ) (member : ℤ → Prop)
    (members_are_notes : ∀ leaf, member leaf → IsCommittedNote hash leaf)
    (floor : FoldReachIsMember hash committedRoot member) :
    NoteAccumulatorCR hash committedRoot :=
  accumulatorSound_of_hashFloor hash committedRoot member (IsCommittedNote hash)
    members_are_notes floor

/-! ### §B.1 — non-vacuity: the recomposition FIRES on the discharge module's explicit witness. -/

open Dregg2.Circuit.ShieldedSpendPortDischarge (zTf_sound)

/-- **The recomposition is not vacuous** — it FIRES on the discharge module's all-zero satisfying trace
(`zero_witness_satisfies`): the leaf really is opened by row 0's own cells, so the membership chain is
about an inhabited relation. Stated at the cell-pinned `OpensAs`; the ∃-image version would fire on
anything. -/
theorem membership_chain_fires_on_witness :
    OpensAs hzero ((zTrace.rows.getD 0 zeroAsg) cCUR) ((zTrace.rows.getD 0 zeroAsg) cVAL)
      ((zTrace.rows.getD 0 zeroAsg) cASSET) ((zTrace.rows.getD 0 zeroAsg) cOWNER)
      ((zTrace.rows.getD 0 zeroAsg) cRAND)
    ∧ (Hair hzero (curAt zTrace (zTrace.rows.length - 1)) (levelAt zTrace (zTrace.rows.length - 1))
        ≡ zTrace.pub piCOMMITTED [ZMOD P]) := by
  have h := emitted_membership_chain hzero (fun _ => 0) (fun _ => (0, 0)) [] zTrace
    (by simp [zTrace]) zero_witness_satisfies zTf_sound (by rfl)
  exact ⟨h.1, h.2.2⟩

#assert_axioms emitted_nullifier_is_committed_note_nullifier
#assert_axioms emitted_nullifier_determined
#assert_axioms emitted_nullifier_double_spend_refused
#assert_axioms emitted_fold_step_all_rows
#assert_axioms emitted_chain_continuity
#assert_axioms emitted_membership_chain
#assert_axioms accumulatorSound_of_hashFloor
#assert_axioms noteAccumulatorCR_of_hashFloor
#assert_axioms membership_chain_fires_on_witness

end SpendCore

/-! ## §C — the mod-p → ℤ conservation range-lift (over the emitted value-link descriptor). -/

section RangeLift

open Dregg2.Circuit.Emit.ShieldedValueLinkDescriptor
  (shieldedValueLinkDesc valAt outAt prefixSum conservation_holds honestTrace
   honest_balanced_satisfies)

/-- **`modp_eq_of_bounds`.** Two field elements congruent mod p AND both in the canonical range
`[0, p)` are EQUAL in ℤ — the no-wraparound uniqueness the range gadget's `[0, 2^VALUE_BITS)` bound
delivers (with a bounded row count keeping the prefix sums under p). -/
theorem modp_eq_of_bounds (A B : ℤ) (hA0 : 0 ≤ A) (hAp : A < P) (hB0 : 0 ≤ B) (hBp : B < P)
    (h : A ≡ B [ZMOD P]) : A = B := by
  have h' : A % P = B % P := h
  rwa [Int.emod_eq_of_lt hA0 hAp, Int.emod_eq_of_lt hB0 hBp] at h'

/-- **⚑ THE #C RANGE-LIFT (`emitted_conservation_int`).** The value-link `conservation_holds` gives
`Σ value ≡ Σ out_val [ZMOD p]`; under the NAMED no-wraparound bound (both prefix sums in `[0, p)` — the
`VALUE_BITS` range gadget's guarantee), it lifts to ℤ EQUALITY `Σ value = Σ out_val`. The honest
"no field wraparound disguises an over-mint" argument; the in-AIR range GADGET establishing the bound
is the named next lane. -/
theorem emitted_conservation_int (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat)
    (maddrs : List ℤ) (t : VmTrace) (hne : t.rows ≠ [])
    (hsat : Satisfied2 hash shieldedValueLinkDesc minit mfin maddrs t)
    (hVal0 : 0 ≤ prefixSum (valAt t) (t.rows.length - 1))
    (hValp : prefixSum (valAt t) (t.rows.length - 1) < P)
    (hOut0 : 0 ≤ prefixSum (outAt t) (t.rows.length - 1))
    (hOutp : prefixSum (outAt t) (t.rows.length - 1) < P) :
    prefixSum (valAt t) (t.rows.length - 1) = prefixSum (outAt t) (t.rows.length - 1) :=
  modp_eq_of_bounds _ _ hVal0 hValp hOut0 hOutp
    (conservation_holds hash minit mfin maddrs t hne hsat)

/-- **The range-lift is not vacuous** — it FIRES on the value-link module's honest balanced 2-row
witness (values 5+3 in, 4+4 out): the ℤ-lifted conservation `8 = 8` holds. -/
theorem conservation_int_fires_on_witness :
    prefixSum (valAt honestTrace) (honestTrace.rows.length - 1)
      = prefixSum (outAt honestTrace) (honestTrace.rows.length - 1) :=
  emitted_conservation_int _ (fun _ => 0) (fun _ => (0, 0)) [] honestTrace
    (by simp [honestTrace]) honest_balanced_satisfies
    (by decide) (by decide) (by decide) (by decide)

#assert_axioms modp_eq_of_bounds
#assert_axioms emitted_conservation_int
#assert_axioms conservation_int_fires_on_witness

end RangeLift

end Dregg2.Circuit.ShieldedSpendPortResidual
