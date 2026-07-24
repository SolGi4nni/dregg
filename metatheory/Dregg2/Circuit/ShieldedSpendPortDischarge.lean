/-
# Dregg2.Circuit.ShieldedSpendPortDischarge — the spend_circuit → Lean port, security core:
# the two named hypotheses of the shielded falsifier proofs DISCHARGED against the emitted AIR.

**This is the discharge lane of the shielded `spend_circuit` port.** The Rust-authored
shielded-spend AIR (`circuit-prove/src/shielded/spend_circuit.rs`, `shielded_spend_descriptor()` —
constraints C1–C7b as hand-written `ConstraintExpr` data) is house-law-#1 DEBT. Its Lean re-authoring
already exists as two emitted `EffectVmDescriptor2` objects that Rust only *decodes/witnesses*:

  * `Dregg2.Circuit.Emit.ShieldedSpendDescriptor.shieldedSpendDesc` — 4-ary Merkle membership +
    nullifier + note-commitment preimage (C6) + value-binding (C7), with the `merkle_root` claim lane
    PI-pinned to the committed accumulator (the in-AIR #15 fix). Its `root_is_pinned` /
    `spend_relation_row0` prove `Satisfied2 ⟹ (root pinned to the committed PI ∧, under the chip
    AIR's own soundness, row 0 carries the genuine spend relation)`.
  * `Dregg2.Circuit.Emit.ShieldedValueLinkDescriptor.shieldedValueLinkDesc` — the value-link +
    Σ-conservation block. Its `value_link_bound` / `conservation_holds` prove `Satisfied2 ⟹ (every
    row's value_binding & leaf_commit are the genuine hash images of ONE shared value cell ∧
    Σ value ≡ Σ out_val [ZMOD p])`.

**What was still missing — and what this module supplies.** The two falsifier proofs
(`ShieldedMerkleRootPin`, seam #15; `ShieldedValueLinkPin`, seam #16) priced the wounds over an
ABSTRACT accumulator model and had to NAME two gaps as free hypotheses, disconnected from any emitted
object:

  * `ShieldedMerkleRootPin.AccumulatorSound` — "a membership witness against the committed root
    certifies a genuinely committed note" — taken abstractly, "exactly as `FinalityCertWidth` takes
    `SigValid`", its discharge deferred to "the full `spend_circuit` AIR port".
  * `ShieldedValueLinkPin.linkHolds` — the `legValue = leafValue` conjunct the deployed conservation
    path omits (`verify_value_link` runs in tests only) — modeled as a free predicate the fix ADDS.

This module connects the abstract falsifier models to the REAL emitted objects and turns each named
hypothesis into a theorem about that object (at the resolution the single emitted trace gives; the
∀-leaf accumulator collision-resistance is reduced to a precisely-named floor, not assumed away):

  * **§A — #15 / `AccumulatorSound`.** `Hair` realizes the abstract per-level fold `H` as the emitted
    `lkParent` Poseidon2 site (`emitted_fold_step_row0`). `OpensAs` realizes the abstract
    `IsCommitted` as the emitted C6 note-commitment shape AT THE TRACE'S OWN CELLS.
    **`emitted_accept_is_committed`** proves, WITH NO `AccumulatorSound` hypothesis, that a satisfying
    `shieldedSpendDesc` trace's accepted leaf is the C6 commitment of row 0's opening cells, its
    membership chain folds to the COMMITTED-accumulator PI, and the claim-root slot cannot decouple
    from it: the emitted C6a/C6b constraints deliver DIRECTLY the "committed" conclusion the abstract
    module could only assume. `NoteAccumulatorCR` names the residual ∀-leaf floor (the deferred
    multi-row fold-walk + Poseidon2 CR), and `pin_accept_is_note` composes the abstract keystone at
    the faithful realization with that floor NAMED — no blanket abstract assumption.

    ⚠ **CORRECTED 2026-07-24 (the ∃-image sweep, `Verify.ExistsImageVacuity`).** `IsCommittedNote` is
    an ∃-IMAGE: under `ShieldedOnRampPin.C6Surjective` — expected of a real Poseidon2 with four free
    field inputs onto ~2^31 — it holds of EVERY felt, so a conclusion stated at it excludes nothing.
    The cell-pinned `OpensAs` is what this AIR actually forces and is strictly stronger
    (`isCommittedNote_does_not_pin_the_opening`); the theorems still stated at `IsCommittedNote`
    (`emitted_leaf_isCommittedNote`, `pin_accept_is_note_committed`) are labeled weakenings kept for
    downstream, each carrying the reason it is NOT strengthened to the authorization-carrying
    `ShieldedOnRampPin.IsLedgerNote:237` — **this AIR does not force authorization and could not**;
    that conjunct is supplied by the accumulator/on-ramp side and enters through `pin_accept_is_note`'s
    floor.
  * **§B — #16 / `linkHolds`.** `emitted_conserved_is_leaf_bound` proves the value that CONSERVES
    (`valAt = rowAt · cVAL`) is, on every row, the SAME cell hashed into the published `leaf_commit`
    and `value_binding` — leg and leaf are ONE in-AIR cell, so the deployed `legValue ≠ leafValue`
    mint is unrepresentable. `emitted_minted_equals_bound_spent` is `conservation_holds` at that cell.
    `emitted_linkHolds` proves the abstract `ShieldedValueLinkPin.linkHolds` holds by construction for
    the emitted realization — the deployed-omitted conjunct is a theorem here.

## Scope (honest) — the named residual for the rest of the port

This lane closes the MEMBERSHIP-root-pin + VALUE-link security core. NOT closed (the next lanes):
the nullifier soundness end-to-end (C4 is proved as a row-0 hash relation in `spend_relation_row0`
but its double-spend-set discharge lives in `ShieldedTransferStark`/`Satisfied2U`); the ℤ-integer
range lift of the mod-p conservation (`VALUE_BITS` bit-decomposition, the `2^VALUE_BITS` amount cap);
the PQ / wide-commitment #17 (the deployed 1-felt ~31-bit digests + the Ristretto conservation cut);
the ∀-leaf `NoteAccumulatorCR` floor (the deferred multi-row Merkle fold-walk that recomposes the
per-row AIR chain into `foldPath` + Poseidon2 collision-resistance); and the Rust producer/emit
wiring + VK regen (`Effect::Custom` carrier, descriptor-JSON golden regen, apex fold supplying the
committed-root PI).

## Axiom hygiene

Bridge theorems over the two emitted objects; no new descriptor, no deployed-code touch. Crypto
floors enter as NAMED hypotheses (`ChipTableSound` — the chip AIR's own faithfulness; the
`NoteAccumulatorCR` ∀-leaf floor), never as axioms. `#assert_axioms` ⊆ {propext, Classical.choice,
Quot.sound}. NEW file; imports read-only.
-/
import Dregg2.Circuit.Emit.ShieldedSpendDescriptor
import Dregg2.Circuit.Emit.ShieldedValueLinkDescriptor
import Dregg2.Circuit.ShieldedMerkleRootPin
import Dregg2.Circuit.ShieldedValueLinkPin

namespace Dregg2.Circuit.ShieldedSpendPortDischarge

open Dregg2.Circuit (Assignment)
open Dregg2.Circuit.DescriptorIR2 (VmTrace Satisfied2 ChipTableSound TableId zeroAsg)

set_option autoImplicit false

/-- BabyBear prime — the field-faithful modulus the emitted descriptors denote over. -/
abbrev P : ℤ := 2013265921

/-! ## §A — seam #15: `ShieldedMerkleRootPin.AccumulatorSound`, discharged against
`Emit.ShieldedSpendDescriptor.shieldedSpendDesc`. -/

section RootPin

open Dregg2.Circuit.Emit.ShieldedSpendDescriptor
open Dregg2.Circuit.ShieldedMerkleRootPin (Level Payload foldPath acceptsPinned AccumulatorSound
  pinned_accept_is_committed)

/-- The abstract per-level Merkle fold `H : Felt → Level → Felt` (the `ShieldedMerkleRootPin` model)
REALIZED by the emitted AIR's Poseidon2 `hash_fact` site: `H current lvl =
hash_fact(current, [sib0, sib1, sib2, pos])`. This is EXACTLY the relation the emitted `lkParent`
chip lookup enforces (`spend_relation_row0`'s first conjunct), so the abstract fold model and the
emitted object are one hash — no re-authored mirror. -/
def Hair (hash : List ℤ → ℤ) (cur : ℤ) (lvl : Level) : ℤ :=
  hash [cur, lvl.sib0, lvl.sib1, lvl.sib2, lvl.pos, NS_FACT_MARK, 1]

/-- A leaf is a **committed note** (mod p) iff it is the Poseidon2 note commitment of SOME preimage
`(value, asset, owner, randomness)` — the emitted AIR's C6 shape
`hash_fact(value, [asset, owner, randomness])`. This realizes the abstract
`ShieldedMerkleRootPin.IsCommitted` at the emitted site.

⚠ **CORRECTED 2026-07-24 — this predicate is an ∃-IMAGE and is VACUOUS at the deployed parameters.**
The docstring it replaces called it *"NON-VACUOUS: not every field element is a note commitment"*.
That is false of a real Poseidon2: the C6 site has FOUR free field inputs onto a ~2^31 codomain, so it
is expected to be surjective mod p, and then `IsCommittedNote hash leaf` holds of EVERY leaf —
`ShieldedOnRampPin.isCommittedNote_of_c6Surjective` /
`noteAccumulatorCR_vacuous_of_c6Surjective:363`, abstracted as `Verify.ExistsImageVacuity`
§1. Counting can never refute that surjectivity (`counting_is_silent_when_domain_dominates`), so the
predicate must be read as carrying NO exclusion power on its own.

The two things that DO carry content, and where each lives:

  * **the OPENING is pinned to the trace's own cells** — `OpensAs` below. That is what the emitted AIR
    actually forces (`emitted_leaf_opensAs_row0`), and it is strictly stronger than the ∃-image
    (`isCommittedNote_does_not_pin_the_opening`): the cells it names are the same cells the nullifier
    (C4) and the value-link (C7a) consume, so the opening cannot be an unrelated witness.
  * **AUTHORIZATION** — `ShieldedOnRampPin.IsLedgerNote:237`, `∃ n, auth n ∧ leaf ≡ noteLeaf hash n`.
    This AIR does NOT force it and cannot: nothing in a satisfying trace mentions any ledger gate. It
    is supplied by the ACCUMULATOR side (the Shield-A append, `shieldAppend_is_ledger_note`), and it
    reaches a spend through the floor of `pin_accept_is_note` below. -/
def IsCommittedNote (hash : List ℤ → ℤ) (leaf : ℤ) : Prop :=
  ∃ v as ow rd : ℤ, leaf ≡ hash [v, as, ow, rd, 0, NS_FACT_MARK, 1] [ZMOD P]

/-- **The WITNESSED form (`OpensAs`): the leaf is the C6 commitment of THESE cells** — not merely of
some opening. This is the content the emitted AIR forces; `IsCommittedNote` is its ∃-image weakening.
Naming the cells is what ties the leaf to the rest of the trace: the same `v` is the value the C7a
value-binding site hashes and the conservation block sums, the same leaf is what C4 derives the
nullifier from. -/
def OpensAs (hash : List ℤ → ℤ) (leaf v as ow rd : ℤ) : Prop :=
  leaf ≡ hash [v, as, ow, rd, 0, NS_FACT_MARK, 1] [ZMOD P]

/-- The ∃-image is the forgetful image of the witnessed form. -/
theorem isCommittedNote_of_opensAs (hash : List ℤ → ℤ) {leaf v as ow rd : ℤ}
    (h : OpensAs hash leaf v as ow rd) : IsCommittedNote hash leaf :=
  ⟨v, as, ow, rd, h⟩

/-- **⚑ THE ∃-IMAGE IS STRICTLY WEAKER (`isCommittedNote_does_not_pin_the_opening`).** At a site whose
C6 arm returns its first input — surjective, exactly the regime the deployed Poseidon2 is in —
EVERY leaf is an `IsCommittedNote` while `OpensAs` at a mismatched value cell is FALSE. So the gap
between "some opening exists" and "these cells open it" is real and inhabited, at this module's own
predicate and not merely in the abstract. -/
theorem isCommittedNote_does_not_pin_the_opening :
    (∀ leaf : ℤ, IsCommittedNote (fun xs => xs.headD 0) leaf)
    ∧ ¬ OpensAs (fun xs => xs.headD 0) 1 0 0 0 0 := by
  refine ⟨fun leaf => ⟨leaf, 0, 0, 0, Int.ModEq.refl _⟩, ?_⟩
  intro h
  have h' : (1 : ℤ) % P = (0 : ℤ) % P := h
  norm_num [P] at h'

/-- **The emitted AIR realizes the abstract per-level fold.** On row 0 of a satisfying trace, the
membership fold `parent` cell IS `Hair hash current level` — the abstract `H` and the emitted chip
site coincide. -/
theorem emitted_fold_step_row0 (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat)
    (maddrs : List ℤ) (t : VmTrace) (hne : t.rows ≠ [])
    (hsat : Satisfied2 hash shieldedSpendDesc minit mfin maddrs t)
    (hChip : ChipTableSound hash (t.tf TableId.poseidon2))
    (hwire : t.tf Dregg2.Circuit.DescriptorIR2.poseidon2narrow
      = Dregg2.Circuit.ChipNarrowLookup.narrowTable (t.tf TableId.poseidon2)) :
    (t.rows.getD 0 zeroAsg) cPAR
      = Hair hash ((t.rows.getD 0 zeroAsg) cCUR)
          ⟨(t.rows.getD 0 zeroAsg) cSIB0, (t.rows.getD 0 zeroAsg) cSIB1,
           (t.rows.getD 0 zeroAsg) cSIB2, (t.rows.getD 0 zeroAsg) cPOS⟩ := by
  have hrel := spend_relation_row0 hash minit mfin maddrs t hne hsat hChip hwire
  exact hrel.1

/-- **⚑ THE #15 DISCHARGE, AT THE CELLS (`emitted_leaf_opensAs_row0`).** A satisfying
`shieldedSpendDesc` trace (under the chip AIR's own soundness) forces the accepted membership leaf
`current` to be the C6 commitment of **row 0's OWN opening cells** `(cVAL, cASSET, cOWNER, cRAND)` —
with NO `AccumulatorSound` hypothesis: C6a recomputes the note commitment from those cells and C6b
(`spend_relation_row0`'s `cCUR ≡ cLEAF`) pins the leaf to it. This is the load-bearing form: the cells
it names are the ones C4 derives the nullifier from and C7a hashes into the value binding, so the
opening cannot be an unrelated witness. -/
theorem emitted_leaf_opensAs_row0 (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat)
    (maddrs : List ℤ) (t : VmTrace) (hne : t.rows ≠ [])
    (hsat : Satisfied2 hash shieldedSpendDesc minit mfin maddrs t)
    (hChip : ChipTableSound hash (t.tf TableId.poseidon2))
    (hwire : t.tf Dregg2.Circuit.DescriptorIR2.poseidon2narrow
      = Dregg2.Circuit.ChipNarrowLookup.narrowTable (t.tf TableId.poseidon2)) :
    OpensAs hash ((t.rows.getD 0 zeroAsg) cCUR) ((t.rows.getD 0 zeroAsg) cVAL)
      ((t.rows.getD 0 zeroAsg) cASSET) ((t.rows.getD 0 zeroAsg) cOWNER)
      ((t.rows.getD 0 zeroAsg) cRAND) := by
  have hrel := spend_relation_row0 hash minit mfin maddrs t hne hsat hChip hwire
  have hLeaf : (t.rows.getD 0 zeroAsg) cLEAF
      = hash [(t.rows.getD 0 zeroAsg) cVAL, (t.rows.getD 0 zeroAsg) cASSET,
              (t.rows.getD 0 zeroAsg) cOWNER, (t.rows.getD 0 zeroAsg) cRAND, 0, NS_FACT_MARK, 1] :=
    hrel.2.2.1
  have hCurLeaf : (t.rows.getD 0 zeroAsg) cCUR ≡ (t.rows.getD 0 zeroAsg) cLEAF [ZMOD P] :=
    hrel.2.2.2.2.1
  rw [hLeaf] at hCurLeaf
  exact hCurLeaf

/-- **The #15 discharge at the ∃-image (`emitted_leaf_isCommittedNote`)** — the forgetful weakening of
`emitted_leaf_opensAs_row0`, kept because downstream modules consume it in this shape
(`ShieldedSpendPortResidual`, `ShieldedSpendFoldReachRealized`).

⚠ **HONEST WEAKENING, not a strengthening we could make.** This conclusion is an ∃-image and is
VACUOUS at the deployed parameters: under `ShieldedOnRampPin.C6Surjective` it holds of EVERY felt, so
by itself it excludes nothing (`Verify.ExistsImageVacuity.inImage_vacuous_of_surjective`). It is NOT
strengthened to the authorization-carrying `ShieldedOnRampPin.IsLedgerNote:237` because **this AIR
does not force authorization and could not**: a satisfying `shieldedSpendDesc` trace mentions no
ledger gate, no `Shield` entry and no committed set — the C6/C6b constraints relate cells to cells.
The authorization conjunct is supplied on the ACCUMULATOR side (`shieldAppend_is_ledger_note`, a
construction fact of the Shield-A append) and reaches a spend through `pin_accept_is_note`'s floor;
manufacturing it here would be a claim the emitted object does not support. Use
`emitted_leaf_opensAs_row0` where content is needed. -/
theorem emitted_leaf_isCommittedNote (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat)
    (maddrs : List ℤ) (t : VmTrace) (hne : t.rows ≠ [])
    (hsat : Satisfied2 hash shieldedSpendDesc minit mfin maddrs t)
    (hChip : ChipTableSound hash (t.tf TableId.poseidon2))
    (hwire : t.tf Dregg2.Circuit.DescriptorIR2.poseidon2narrow
      = Dregg2.Circuit.ChipNarrowLookup.narrowTable (t.tf TableId.poseidon2)) :
    IsCommittedNote hash ((t.rows.getD 0 zeroAsg) cCUR) :=
  isCommittedNote_of_opensAs hash
    (emitted_leaf_opensAs_row0 hash minit mfin maddrs t hne hsat hChip hwire)

/-- **⚑ THE #15 KEYSTONE (`emitted_accept_is_committed`).** The whole shape at once, WITH NO
`AccumulatorSound` hypothesis: a satisfying trace's accepted leaf is the C6 commitment of row 0's own
opening cells, its membership chain (the last row's `parent`) folds to the COMMITTED-accumulator PI,
its row-0 claim lane is that same PI, and the claim-root slot cannot decouple from the committed root.
This is exactly what `ShieldedMerkleRootPin.deployed_admits_but_pin_rejects` said the DEPLOYED
predicate failed to force — now forced, in-AIR, by the emitted object; the abstract module's floating
hypothesis is discharged for the accepted instance.

⚑ **STRENGTHENED 2026-07-24**: the first conjunct was the ∃-image `IsCommittedNote hash cCUR`, which
is vacuous under `ShieldedOnRampPin.C6Surjective`; it is now the cell-pinned `OpensAs`, from which the
∃-image follows by `isCommittedNote_of_opensAs`. ⚠ What is still NOT here, and cannot be: the note is
not shown LEDGER-AUTHORIZED (`ShieldedOnRampPin.IsLedgerNote`) — see `emitted_leaf_isCommittedNote`'s
note for why the AIR cannot supply that conjunct and which object does. -/
theorem emitted_accept_is_committed (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat)
    (maddrs : List ℤ) (t : VmTrace) (hne : t.rows ≠ [])
    (hsat : Satisfied2 hash shieldedSpendDesc minit mfin maddrs t)
    (hChip : ChipTableSound hash (t.tf TableId.poseidon2))
    (hwire : t.tf Dregg2.Circuit.DescriptorIR2.poseidon2narrow
      = Dregg2.Circuit.ChipNarrowLookup.narrowTable (t.tf TableId.poseidon2)) :
    OpensAs hash ((t.rows.getD 0 zeroAsg) cCUR) ((t.rows.getD 0 zeroAsg) cVAL)
      ((t.rows.getD 0 zeroAsg) cASSET) ((t.rows.getD 0 zeroAsg) cOWNER)
      ((t.rows.getD 0 zeroAsg) cRAND)
    ∧ ((t.rows.getD (t.rows.length - 1) zeroAsg) cPAR ≡ t.pub piCOMMITTED [ZMOD P])
    ∧ ((t.rows.getD 0 zeroAsg) cROOT ≡ t.pub piCOMMITTED [ZMOD P])
    ∧ (t.pub piROOT ≡ t.pub piCOMMITTED [ZMOD P]) := by
  have hpin := root_is_pinned hash minit mfin maddrs t hne hsat
  exact ⟨emitted_leaf_opensAs_row0 hash minit mfin maddrs t hne hsat hChip hwire,
         hpin.2.1, hpin.1, hpin.2.2⟩

/-- The residual **accumulator collision-resistance floor**, NAMED precisely (never axiomatized):
the abstract `ShieldedMerkleRootPin.AccumulatorSound` at the FAITHFUL realization — per-level fold
`Hair hash` (the emitted `lkParent` site), "committed" = `IsCommittedNote hash` (the emitted C6
shape). This is the ∀-leaf statement the single emitted trace does NOT give — the deferred multi-row
Merkle fold-walk (recomposing the per-row AIR chain into `foldPath`) plus Poseidon2 CR — exactly as
`ShieldedTransferStark.starkResidual_of_floor` names its FRI `extract`.

⚠ At the ∃-image note predicate this floor is itself vacuous under C6 surjectivity
(`ShieldedOnRampPin.noteAccumulatorCR_vacuous_of_c6Surjective:363`): it holds for EVERY root,
including one the prover wrote. The floor that PRICES something is the same shape at an
authorization-carrying note predicate — `AccumulatorSound (Hair hash) (IsLedgerNote hash auth)`, which
`pin_accept_is_note` below takes directly. -/
def NoteAccumulatorCR (hash : List ℤ → ℤ) (committedRoot : ℤ) : Prop :=
  AccumulatorSound (Hair hash) (IsCommittedNote hash) committedRoot

/-- **⚑ THE KEYSTONE AT WHATEVER THE FLOOR CARRIES (`pin_accept_is_note`, ADDED 2026-07-24).** A
pinned-membership payload (supplied root = committed root) spends a leaf satisfying **the accumulator
floor's own note predicate** — the abstract `pinned_accept_is_committed` at the faithful `Hair`
realization, kept parametric in `note` instead of hard-wired to the ∃-image.

This is the honest strengthening of `pin_accept_is_note_committed`: the conclusion is exactly as
strong as the floor supplied, and NOTHING in the argument wanted the ∃-image specifically. Instantiate
`note := ShieldedOnRampPin.IsLedgerNote hash auth` and the conclusion is that the spend spends a note
the LEDGER AUTHORIZED (`ShieldedOnRampPin.shieldA_pin_spends_authorized`, whose floor the Shield-A
append discharges by construction); instantiate `note := IsCommittedNote hash` and you get the old,
vacuous-at-deployed-parameters statement. The authorization was never derivable from the AIR — it
comes in through the floor, and this signature is where it enters. -/
theorem pin_accept_is_note (hash : List ℤ → ℤ) (note : ℤ → Prop) (committedRoot : ℤ)
    (floor : AccumulatorSound (Hair hash) note committedRoot) (p : Payload)
    (h : acceptsPinned (Hair hash) committedRoot p) :
    note p.leaf :=
  pinned_accept_is_committed (Hair hash) note committedRoot p floor h

/-- **The abstract keystone at the ∃-image note predicate** — `pin_accept_is_note` instantiated at
`IsCommittedNote`, kept because downstream consumes it in this shape
(`ShieldedOnRampPin.shieldA_pin_closes_15`).

⚠ **HONEST WEAKENING.** Under `ShieldedOnRampPin.C6Surjective` both the floor and the conclusion are
vacuous, so this instance prices nothing on its own; the ledger-strength instance of the SAME theorem
is what closes seam #15. -/
theorem pin_accept_is_note_committed (hash : List ℤ → ℤ) (committedRoot : ℤ)
    (floor : NoteAccumulatorCR hash committedRoot) (p : Payload)
    (h : acceptsPinned (Hair hash) committedRoot p) :
    IsCommittedNote hash p.leaf :=
  pin_accept_is_note hash (IsCommittedNote hash) committedRoot floor p h

/-! ### §A.1 — non-vacuity: the discharge FIRES on the emit module's explicit satisfying witness. -/

/-- The all-zero satisfying witness's chip table is SOUND (its single row is a genuine `chipRow`
tuple of the toy hash) — so the discharge's `ChipTableSound` premise is inhabited on a real trace. -/
theorem zTf_sound : ChipTableSound hzero (zTrace.tf TableId.poseidon2) := by
  intro r hr
  simp only [zTrace, zTf, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl
  exact ⟨[0, 0, 0, 0, 0, 64207, 1], [0, 0, 0, 0, 0, 0, 0], by decide, by decide, by decide⟩

/-- **The discharge is not vacuous** — it FIRES on the emit module's explicit all-zero satisfying
trace (`zero_witness_satisfies`): the accepted leaf really is opened by row 0's own cells, so the
theorem is about an inhabited relation, not an empty one. Stated at the cell-pinned `OpensAs` (the
∃-image version would fire on anything). -/
theorem discharge_fires_on_witness :
    OpensAs hzero ((zTrace.rows.getD 0 zeroAsg) cCUR) ((zTrace.rows.getD 0 zeroAsg) cVAL)
      ((zTrace.rows.getD 0 zeroAsg) cASSET) ((zTrace.rows.getD 0 zeroAsg) cOWNER)
      ((zTrace.rows.getD 0 zeroAsg) cRAND) :=
  emitted_leaf_opensAs_row0 hzero (fun _ => 0) (fun _ => (0, 0)) [] zTrace
    (by simp [zTrace]) zero_witness_satisfies zTf_sound (by rfl)

#assert_axioms emitted_fold_step_row0
#assert_axioms isCommittedNote_of_opensAs
#assert_axioms isCommittedNote_does_not_pin_the_opening
#assert_axioms emitted_leaf_opensAs_row0
#assert_axioms emitted_leaf_isCommittedNote
#assert_axioms emitted_accept_is_committed
#assert_axioms pin_accept_is_note
#assert_axioms pin_accept_is_note_committed
#assert_axioms zTf_sound
#assert_axioms discharge_fires_on_witness

end RootPin

/-! ## §B — seam #16: `ShieldedValueLinkPin.linkHolds`, discharged against
`Emit.ShieldedValueLinkDescriptor.shieldedValueLinkDesc`. -/

section ValueLink

open Dregg2.Circuit.Emit.ShieldedValueLinkDescriptor

/-- **⚑ THE #16 DISCHARGE (`emitted_conserved_is_leaf_bound`).** In the emitted value-link block the
value that CONSERVES on every row (`valAt t i = rowAt t i cVAL`) is EXACTLY the value hashed into the
published `leaf_commit` and `value_binding` (under the chip AIR's soundness). There is no free second
"leg value" to decouple from the leaf value — leg and leaf are ONE in-AIR cell — so the deployed
`legValue ≠ leafValue` mint (`ShieldedValueLinkPin.genuine_note_inflates`) is UNREPRESENTABLE. -/
theorem emitted_conserved_is_leaf_bound (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat)
    (maddrs : List ℤ) (t : VmTrace) (hne : t.rows ≠ [])
    (hsat : Satisfied2 hash shieldedValueLinkDesc minit mfin maddrs t)
    (hChip : ChipTableSound hash (t.tf TableId.poseidon2))
    (hwire : t.tf Dregg2.Circuit.DescriptorIR2.poseidon2narrow
      = Dregg2.Circuit.ChipNarrowLookup.narrowTable (t.tf TableId.poseidon2)) :
    ∀ i, i < t.rows.length →
      rowAt t i cLEAF
        = hash [valAt t i, rowAt t i cASSET, rowAt t i cOWNER, rowAt t i cRAND, 0, NS_FACT_MARK, 1]
      ∧ rowAt t i cVB
        = hash [valAt t i, rowAt t i cASSET, rowAt t i cRAND, rowAt t i cVBP0, 0, NS_FACT_MARK, 1] := by
  intro i hi
  obtain ⟨hVB, hLEAF, _⟩ := (value_link_bound hash minit mfin maddrs t hne hsat hChip hwire).1 i hi
  exact ⟨hLEAF, hVB⟩

/-- **⚑ THE #16 KEYSTONE (`emitted_minted_equals_bound_spent`).** The minted total equals the real
spent value over the SAME cells the value-link hashes bind: `Σ value ≡ Σ out_val [ZMOD p]` — the
emitted-object form of `ShieldedValueLinkPin.linked_conservation_over_real_value`, with NO `linkHolds`
hypothesis (conservation runs over the leaf's own value cells in-AIR). Field conservation; the
ℤ-integer lift is the named `VALUE_BITS` range residual. -/
theorem emitted_minted_equals_bound_spent (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat)
    (maddrs : List ℤ) (t : VmTrace) (hne : t.rows ≠ [])
    (hsat : Satisfied2 hash shieldedValueLinkDesc minit mfin maddrs t) :
    prefixSum (valAt t) (t.rows.length - 1) ≡ prefixSum (outAt t) (t.rows.length - 1) [ZMOD P] :=
  conservation_holds hash minit mfin maddrs t hne hsat

/-- The emitted realization's input at row `i`: `legValue` and `leafValue` are BOTH the one in-AIR
value cell `rowAt t i cVAL` — the collapse of the deployed path's two free values into one cell that
`emitted_conserved_is_leaf_bound` proves is simultaneously conserved and leaf-hashed. -/
def emitInput (t : VmTrace) (i : Nat) : Dregg2.Circuit.ShieldedValueLinkPin.Input :=
  { leafValue    := rowAt t i cVAL
  , legValue     := rowAt t i cVAL
  , valueBinding := rowAt t i cVB
  , wideBinding  := rowAt t i cVB }

/-- The emitted realization's transfer over its first `n` rows (outputs immaterial to the link). -/
def emitTransfer (t : VmTrace) (n : Nat) : Dregg2.Circuit.ShieldedValueLinkPin.Transfer :=
  { inputs := (List.range n).map (emitInput t), outLegs := [] }

/-- **⚑ THE #16 LINK, DISCHARGED (`emitted_linkHolds`).** The abstract `ShieldedValueLinkPin.linkHolds`
— the `legValue = leafValue` conjunct the deployed conservation path OMITS (`verify_value_link` runs
in tests only) — holds by construction for the emitted realization: every input's leg and leaf value
are the same in-AIR cell. The deployed-omitted tie is a theorem here, not an assumption. -/
theorem emitted_linkHolds (t : VmTrace) (n : Nat) :
    Dregg2.Circuit.ShieldedValueLinkPin.linkHolds (emitTransfer t n) := by
  intro inp hinp
  simp only [emitTransfer, List.mem_map] at hinp
  obtain ⟨i, _, rfl⟩ := hinp
  rfl

/-! ### §B.1 — non-vacuity: the discharge FIRES on the emit module's honest balanced witness. -/

/-- **The value-link discharge is not vacuous** — it FIRES on the emit module's explicit honest
balanced 2-row trace (`honest_balanced_satisfies`, values 5+3 in, 4+4 out): the conserved value on
row 0 really is the leaf-hashed value. -/
theorem link_discharge_fires_on_witness :
    rowAt honestTrace 0 cLEAF
      = hzero [valAt honestTrace 0, rowAt honestTrace 0 cASSET, rowAt honestTrace 0 cOWNER,
               rowAt honestTrace 0 cRAND, 0, NS_FACT_MARK, 1] :=
  (emitted_conserved_is_leaf_bound hzero (fun _ => 0) (fun _ => (0, 0)) [] honestTrace
    (by simp [honestTrace]) honest_balanced_satisfies honTf_sound (by rfl) 0
    (by simp [honestTrace])).1

#assert_axioms emitted_conserved_is_leaf_bound
#assert_axioms emitted_minted_equals_bound_spent
#assert_axioms emitted_linkHolds
#assert_axioms link_discharge_fires_on_witness

end ValueLink

end Dregg2.Circuit.ShieldedSpendPortDischarge
