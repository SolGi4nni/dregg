/-
# Dregg2.Authority.CrossCellImport — cross-cell reads as VERIFIED PAST-SNAPSHOT imports.

`docs/CELL-PROGRAM-LANGUAGE.md §8` (gap 6, "the deepest naturalness gap"). A cell program
cannot read another cell's LIVE state, *by design*: a guard that reads cell B's current value
makes every turn on A order against every turn on B — the `ConfluenceClassifier`
`relational_decided_by_merge` arm with a non-local relation, i.e. coordination, always. The
factory/polis lanes worked around this by COPYING a parameter at birth (a constitution threshold,
a council size). That copy is sound but not *first-class*: nothing records WHERE the literal came
from, so a verifier cannot recompute it and tooling cannot say "this is stale".

This module makes the copy first-class and PROVED. The key move — and the reason it dissolves the
coordination cost the live read cannot escape — is that an import reads an **immutable past
receipt**, not the live head:

> **An import cites a receipt `r` in the source cell's append-only chain and the value the source
> field held in the state `r` commits. Because receipts are immutable (the `Exec.Receipt`
> append-only / tamper-evident chain), that reading never changes as the source advances. So the
> import is I-CONFLUENT (coordination-free): it never re-orders against the source's future turns.
> A LIVE read of the source's head is not — it changes the instant the source moves.**

We PROVE exactly that distinction (`importValid_stable_under_source_advance` vs
`liveRead_changes_under_source_advance`). The provenance is non-forgeable by inheritance from the
chain's tamper-evidence (`chain_tamper_evident`), staleness is faithful-but-visible (a stale import
still reports the cited past truthfully; the provenance pins WHICH height, so supersession is
detectable, never silent), and an imported value is a first-class citizen of the closure algebra
(`RelPred.affineEq`, per §9 — "expose `RelPred`/`ArithPred` instances, not one-off atoms"), not a
new bespoke constraint.

§8 RAIL: the commitment's binding (a valid opening of `r.newCommit` yields a unique source record)
is the NAMED §8 oracle — here carried as the structural fact that the committed-state readout is a
*function* of the receipt; the hash/commitment collision-resistance lives in `Exec.Receipt`'s
`HInj`/`HFresh` hypotheses and is never a Lean axiom. The structural law (immutable-past ⇒
confluence-free) is the Lean theorem.
-/
import Dregg2.Exec.Value
import Dregg2.Exec.Receipt
import Dregg2.Authority.RelationalClosure

namespace Dregg2.Authority.CrossCellImport

open Dregg2.Exec (Value FieldName)
open Dregg2.Exec.EffectsState (fieldOf)
open Dregg2.Exec.Receipts
open Dregg2.Authority.RelationalClosure (RelPred affineSum affineEq_eq)

/-! ## The source cell's committed history. -/

/-- A SOURCE cell's committed history: its `Exec.Receipt` chain (newest-first) paired with the
record each receipt commits — the state opened from `r.newCommit`. In the running system
`stateAt` is realized by opening the state commitment; here it is the abstract readout, and the
binding "a valid opening of `r.newCommit` yields exactly `stateAt r`" is the §8 commitment oracle
(carried structurally: `stateAt` is a *function* of the receipt, so a receipt commits to a unique
record — never a Lean axiom). -/
structure SourceHistory where
  /-- The source cell's append-only receipt chain (newest-first; head = latest). -/
  chain   : ReceiptChain
  /-- The record committed by each receipt (the opened post-state). -/
  stateAt : Receipt → Value

/-- A cross-cell import: a local field populated from a named source field, with the value and the
exact receipt (height/commitment) it was read at. Mirrors the `FactoryDescriptor.imports` design
(`{ name, source_cell, source_slot, value, provenance: ReceiptRef }`). The `source_cell` is the
`SourceHistory` this import is checked against; `provenance` is the cited `Receipt`. -/
structure Import where
  /-- The LOCAL field this import populates. -/
  localField  : FieldName
  /-- The field READ from the source cell. -/
  sourceField : FieldName
  /-- The imported literal (what the source field held at `provenance`). -/
  value       : Int
  /-- The cited source receipt — the height/commitment the read is pinned to. -/
  provenance  : Receipt
deriving Repr

/-- The honest readout: the source field's scalar in the state a receipt commits. Uses the total
`fieldOf` (absent/ill-typed ⇒ `0`), so it is defined for any record. -/
def readAt (h : SourceHistory) (r : Receipt) (f : FieldName) : Int :=
  fieldOf f (h.stateAt r)

/-! ## Validity — the import faithfully reports the source's committed past. -/

/-- **`importValid`** — the import is honest: its cited receipt lives in the source's well-linked
chain, and the source field held *exactly* `value` in the state that receipt commits. A lying
import (any `value` other than the committed one) fails this. The well-linkedness is what makes the
provenance non-forgeable (`chain_tamper_evident`). -/
def importValid (H : Receipt → Nat) (h : SourceHistory) (imp : Import) : Prop :=
  wellLinked H h.chain ∧ imp.provenance ∈ h.chain ∧
    readAt h imp.provenance imp.sourceField = imp.value

/-- **Anti-lie (uniqueness).** For a fixed source history, cited receipt, and source field, AT MOST
ONE value is valid: the readout is a function, so two valid imports agreeing on
`(provenance, sourceField)` agree on `value`. A submitter cannot present two different "imported"
values for the same citation — one of them is a lie and fails `importValid`. -/
theorem importValid_value_unique {H : Receipt → Nat} {h : SourceHistory} {imp imp' : Import}
    (hv : importValid H h imp) (hv' : importValid H h imp')
    (hsrc : imp.provenance = imp'.provenance ∧ imp.sourceField = imp'.sourceField) :
    imp.value = imp'.value := by
  obtain ⟨hp, hf⟩ := hsrc
  have e : readAt h imp.provenance imp.sourceField = readAt h imp'.provenance imp'.sourceField := by
    rw [hp, hf]
  rw [hv.2.2] at e
  rw [hv'.2.2] at e
  exact e

/-! ## THE CROWN — an import is stable as the source advances (I-confluence). -/

/-- Advance the source: prepend a fresh committed receipt at the head, committing record `v`,
leaving every OLDER receipt and the state it commits UNTOUCHED. This is the `Exec.Receipt`
append-only discipline (you may only grow the chain at the head; the past is immutable). -/
def advance (h : SourceHistory) (r : Receipt) (v : Value) : SourceHistory :=
  { chain := r :: h.chain
  , stateAt := fun x => if x = r then v else h.stateAt x }

/-- **`importValid_stable_under_source_advance` (KEYSTONE — the I-confluence of imports).** A valid
import stays valid after the source cell takes any number of further turns (here: one fresh
head receipt; iterate for many). Because the cited receipt is in the *past* and receipts are
immutable, the read is unchanged — the import never has to re-coordinate with the source's new
turns. This is precisely what makes a verified past-snapshot import COORDINATION-FREE where a live
cross-cell read is not (`liveRead_changes_under_source_advance` below).

Hypotheses: the appended receipt `r` is genuinely new (`hfresh`) and links onto the current head
(`hlink`) — exactly the append-only growth `Exec.Receipt.wellLinked_append` allows. -/
theorem importValid_stable_under_source_advance
    {H : Receipt → Nat} {h : SourceHistory} {imp : Import} {r : Receipt} {v : Value}
    (hfresh : r ∉ h.chain)
    (hlink : ∀ hd, h.chain.head? = some hd → r.prevHash = H hd)
    (hvalid : importValid H h imp) :
    importValid H (advance h r v) imp := by
  obtain ⟨hwl, hmem, hread⟩ := hvalid
  -- provenance ≠ r, since provenance ∈ chain but r ∉ chain.
  have hne : imp.provenance ≠ r := by
    intro hcontra; exact hfresh (hcontra ▸ hmem)
  refine ⟨?_, ?_, ?_⟩
  · -- well-linkedness preserved by an append onto the head.
    show wellLinked H (r :: h.chain)
    cases hc : h.chain with
    | nil =>
      -- vacuous: a valid import needs provenance ∈ chain, impossible on the empty chain.
      rw [hc] at hmem; exact absurd hmem (by simp)
    | cons hd tl =>
      -- `h.chain = hd :: tl`; the head is `hd`, so `r` links onto it (`hlink`) and the existing
      -- chain is well-linked — `wellLinked_append` grows it by one head receipt.
      have hlk : r.prevHash = H hd := hlink hd (by rw [hc]; rfl)
      have hwl' : wellLinked H (hd :: tl) := hc ▸ hwl
      exact wellLinked_append hwl' hlk
  · -- membership preserved by prepend.
    show imp.provenance ∈ r :: h.chain
    exact List.mem_cons_of_mem r hmem
  · -- the readout is unchanged: advance leaves old receipts' committed state alone.
    show readAt (advance h r v) imp.provenance imp.sourceField = imp.value
    unfold readAt advance
    simp only [if_neg hne]
    exact hread

/-! ## The live-read contrast — the distinction is REAL, not vacuous. -/

/-- A LIVE cross-cell read: read the source's CURRENT head, not a cited past receipt. This is what
the constraint language deliberately forbids — and the reason is below. -/
def liveRead (h : SourceHistory) (f : FieldName) : Option Int :=
  h.chain.head?.map (fun hd => readAt h hd f)

/-- **`liveRead_changes_under_source_advance`.** There is a source history, a fresh head, and a
field on which the live read CHANGES when the source advances. So the stability proven for imports
is a genuine property the live read lacks — the two are not the same, and the import's
coordination-freeness is not vacuous. (Witness: an empty-history source, advanced with a head whose
committed record sets the field; the live read goes `none ↦ some _`.) -/
theorem liveRead_changes_under_source_advance :
    ∃ (h : SourceHistory) (r : Receipt) (v : Value) (f : FieldName),
      liveRead (advance h r v) f ≠ liveRead h f := by
  refine ⟨⟨[], fun _ => .int 0⟩, ⟨0, 0, 0, 0⟩, .record [("x", .int 7)], "x", ?_⟩
  -- live read of the empty source is `none`; after advance the head commits x = 7, so `some 7`.
  decide

/-! ## Provenance is non-forgeable — inherited from chain tamper-evidence. -/

/-- **`importProvenance_tamper_evident`.** Under the `Exec.Receipt` §8 oracle (injective digest,
fresh sentinel), a valid import's cited receipt cannot be denied by any well-linked history that
presents the same head: same head ⇒ same history (`chain_tamper_evident`), so `provenance` is in it.
The import's trust is exactly the source chain's tamper-evidence — no extra assumption. -/
theorem importProvenance_tamper_evident
    {H : Receipt → Nat} (HInj : Function.Injective H) (HFresh : ∀ p, H p ≠ genesisSentinel)
    {h h' : SourceHistory} {imp : Import}
    (hv : importValid H h imp) (hwl' : wellLinked H h'.chain)
    (hhead : h.chain.head? = h'.chain.head?) :
    imp.provenance ∈ h'.chain := by
  have hsame : h.chain = h'.chain :=
    chain_tamper_evident HInj HFresh h.chain h'.chain hv.1 hwl' hhead
  rw [← hsame]; exact hv.2.1

/-! ## Staleness — faithful, but visible (never silent). -/

/-- The source's CURRENT value of the imported field (the live head), or `none` if the source has
no history. -/
def currentValue (h : SourceHistory) (imp : Import) : Option Int :=
  liveRead h imp.sourceField

/-- An import is STALE when the source's current value differs from the cited (imported) value. A
stale import is STILL VALID — it faithfully reports the cited past — but the divergence is visible
via the provenance, so an amendment-reissue *visibly* supersedes it. Staleness is detection, not
corruption. -/
def importStale (h : SourceHistory) (imp : Import) : Prop :=
  currentValue h imp ≠ some imp.value

/-- Cited-past receipt for `stale_import_is_still_valid`: an OLDER receipt that committed `x = 5`,
pinned to the genesis sentinel. -/
def staleOld : Receipt := mkReceipt genesisSentinel 50 50 0
/-- Head receipt for `stale_import_is_still_valid`: the CURRENT head committing `x = 9`, linking
onto `staleOld` via `demoHash` (the demo digest). -/
def staleNew : Receipt := mkReceipt (demoHash staleOld) 50 90 1
/-- The committed states: the head commits `x = 9`; every older receipt committed `x = 5`. -/
def staleState : Receipt → Value := fun x =>
  if x = staleNew then .record [("x", .int 9)] else .record [("x", .int 5)]
/-- The two-receipt source history (newest-first) for the staleness witness. -/
def staleHist : SourceHistory := ⟨[staleNew, staleOld], staleState⟩
/-- The import: cites the OLD receipt and the value `5` it held there, while the head now holds `9`. -/
def staleImp : Import := ⟨"local_x", "x", 5, staleOld⟩

/-- **`stale_import_is_still_valid` (honesty, non-vacuous).** There is an import that is BOTH valid
AND stale: the source changed the field after the cited receipt. The import keeps reporting the
cited past truthfully (valid), while the present has moved on (stale) — and the provenance pins the
height at which the value held, so tooling renders "imported at height H; current value differs".
This is the honest cross-cell story: a snapshot, dated, never a silent live read. -/
theorem stale_import_is_still_valid :
    ∃ (H : Receipt → Nat) (h : SourceHistory) (imp : Import),
      importValid H h imp ∧ importStale h imp := by
  refine ⟨demoHash, staleHist, staleImp, ⟨?_, ?_, ?_⟩, ?_⟩
  · -- well-linked `[staleNew, staleOld]`: `staleNew.prevHash = demoHash staleOld` (by construction),
    -- and the genesis `staleOld.prevHash = genesisSentinel` (by construction) — both `rfl`.
    exact ⟨rfl, rfl⟩
  · -- `staleOld ∈ [staleNew, staleOld]` (the cited receipt is the chain's tail head).
    exact List.mem_cons_of_mem _ List.mem_cons_self
  · -- `readAt staleHist staleOld "x" = 5`: `staleOld ≠ staleNew`, so `staleState staleOld` is the
    -- `x = 5` record; reading field `x` gives `5`. Decidable concrete scalar readout.
    decide
  · -- current value = head (`staleNew`) reads `x = 9`, and `9 ≠ 5`, so the import is stale.
    show currentValue staleHist staleImp ≠ some staleImp.value
    decide

/-! ## Composition with the closure algebra — an imported value is a first-class `RelPred`. -/

/-- `affineSum` of a single unit-weighted term reads exactly that field (the closure's atom over
one field). The bridge that lets an import bind to a `RelPred`. -/
theorem affineSum_single (f : FieldName) (rec : Value) :
    affineSum [(1, f)] rec = fieldOf f rec := by
  simp [affineSum]

/-- **Bind an import into the local cell's constraint language** (§9: expose closure instances, not
one-off atoms). "The local field equals the imported literal" is `RelPred.affineEq` over the single
field — the imported value is just a literal in the affine atom. -/
def importBindingPred (imp : Import) : RelPred :=
  RelPred.affineEq [(1, imp.localField)] imp.value

/-- **`importBindingPred_iff`.** The binding constraint holds exactly when the local record carries
the imported value at `localField`. So a cell whose program includes `importBindingPred imp` admits
a turn iff its post-state really set the local field to the imported value — the import is enforced
by the same proved closure algebra as every other guard, no new machinery. -/
theorem importBindingPred_iff (imp : Import) (rec : Value) :
    (importBindingPred imp).eval rec = true ↔ fieldOf imp.localField rec = imp.value := by
  unfold importBindingPred
  rw [affineEq_eq, affineSum_single, decide_eq_true_eq]

/-! ## It runs (`#guard`) — accept, lie-reject, the live-vs-import contrast, the binding. -/

/-- A concrete source: head commits balance 100, an older receipt committed balance 70. -/
def srcOld : Receipt := mkReceipt genesisSentinel 70 70 0
def srcNew : Receipt := mkReceipt (demoHash srcOld) 70 100 1
def srcState : Receipt → Value := fun x =>
  if x = srcNew then .record [("bal", .int 100)] else .record [("bal", .int 70)]
def srcHist : SourceHistory := ⟨[srcNew, srcOld], srcState⟩

/-- A truthful import: "bal was 70 at receipt srcOld" → reads 70. -/
def goodImp : Import := ⟨"imported_bal", "bal", 70, srcOld⟩
/-- A lying import: claims "bal was 999 at srcOld" — but it was 70. -/
def lieImp  : Import := ⟨"imported_bal", "bal", 999, srcOld⟩

-- The truthful import reads exactly what the cited receipt committed:
#guard decide (readAt srcHist srcOld "bal" = goodImp.value)            -- true  (70 = 70)
-- The lie fails the readout check (the heart of importValid):
#guard decide (readAt srcHist srcOld "bal" = lieImp.value) == false    -- false (70 ≠ 999) → REJECTED
-- The cited receipt really is in the chain:
#guard decide (goodImp.provenance ∈ srcHist.chain)                     -- true
-- Live read of the head sees the CURRENT value 100, not the imported-past 70 (the contrast):
#guard decide (liveRead srcHist "bal" = some 100)                      -- true  (head, not the snapshot)
#guard decide (currentValue srcHist goodImp = some 100)               -- true  (≠ imported 70 ⇒ visibly stale)
-- The binding predicate: accepts a record that carries the imported value, rejects one that doesn't:
#guard (importBindingPred goodImp).eval (.record [("imported_bal", .int 70)])           -- true
#guard (importBindingPred goodImp).eval (.record [("imported_bal", .int 71)]) == false  -- false

/-! ## Axiom hygiene — the keystones depend only on `{propext, Classical.choice, Quot.sound}`.

`importValid_stable_under_source_advance` (the I-confluence crown) and the other load-bearing
theorems carry NO bespoke axiom — the §8 commitment oracle is the `HInj`/`HFresh` *hypotheses*
threaded through `chain_tamper_evident`, never a Lean axiom. -/
#print axioms importValid_stable_under_source_advance
#print axioms liveRead_changes_under_source_advance
#print axioms importValid_value_unique
#print axioms importProvenance_tamper_evident
#print axioms stale_import_is_still_valid
#print axioms importBindingPred_iff

end Dregg2.Authority.CrossCellImport
