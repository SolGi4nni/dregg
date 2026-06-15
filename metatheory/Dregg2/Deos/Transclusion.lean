/-
# Dregg2.Deos.Transclusion — Xanadu's transclusion, made HONEST on the verified substrate.

Ted Nelson's Xanadu promised **transclusion**: include-by-reference where the quoted material keeps
its identity and provenance — the same bytes, the same source, visibly cited, never copied-and-cut.
Xanadu could never make it honest, because in an ambient-authority world a "transcluded" quote is just
a copy: nothing forces it to equal the source, nothing stops it from rotting when the source moves,
nothing bounds what authority the quote confers, and the "two-way link" back to the source was a
hand-maintained index, not a fact. dregg already has the missing piece — **the verified cross-cell
import** (`Dregg2.Authority.CrossCellImport` / its first-class binding `Dregg2.Authority.ImportBinding`):
a local field that IS the value a peer cell's field held at a cited, immutable receipt. That is
transclusion with cryptographic provenance. This module NAMES it as transclusion and proves the four
Xanadu properties Nelson wanted — each by REUSE of an existing kernel theorem, no new mathematics.

The prompt calls the underlying primitive `ObservedFieldEquals` (a verified cross-cell finalized read);
in this codebase that primitive IS `Authority.ImportBinding.ImportedEq` — the fused construct carrying
BOTH the provenance citation (`importValid`: the cited source receipt is in the source's well-linked
chain AND the source field held the value there) AND the local-field enforcement (the `affineEq` atom).
A transclusion is exactly an `ImportedEq` of a peer's finalized field, viewed through the deos membrane.

## The four Xanadu properties (each a kernel theorem restated for the docuverse)

  1. **`transclusion_is_observed_finalized_read`** (the definitional bridge) — a transclusion IS an
     `ImportedEq` of a peer cell's finalized field: the local field admits iff the post-state carries
     the cited source value (`ImportedEq.admits_iff`). Transclusion is not a new object; it is the
     verified cross-cell observation, named.

  2. **`transclusion_provenance_faithful`** (the anti-forge tooth — "you cannot fake a quote") — when
     the citation is VALID and the cell admits the transclusion, the transcluded value EQUALS the value
     the SOURCE COMMITTED at the cited receipt (rides `importedEq_binds_provenanced_value`). And a
     FORGED transclusion (claiming a value the source never committed) is NOT `importValid` — it cannot
     even be cited (rides `importedEq_lying_import_rejected`). No opened provenance ⇒ no quote: the
     transcluded value cannot diverge from its source.

  3. **`transclusion_no_amplify`** (per-viewer confinement — "a quote is a READ, not a key") — a
     transclusion confers NO authority over the source beyond observing the cited value. Through the
     deos membrane it is a per-viewer projection, and ANY chain of reshares stays a subset of the held
     authority (rides `Dregg2.Deos.Membrane.reshareN_attenuates` / `reshare_refuses_amplification`).
     Transcluding a peer's field does not hand you the peer's cell.

  4. **`transclusion_stable_under_source_advance`** (THE UNBREAKABLE LINK — "the quote never rots") —
     a snapshot transclusion stays valid when the source cell advances arbitrarily (rides
     `importValid_stable_under_source_advance` / `importedEq_stable_under_source_advance`, the
     I-confluence crown). The cited receipt is an immutable past; the read never changes. This is the
     property Nelson wanted and Xanadu's URLs could not deliver — a citation that does not break, ever,
     no matter what the source does next. Staleness is faithful-but-visible: the quote keeps reporting
     the cited past truthfully and the provenance dates it (`stale_import_is_still_valid`), so
     supersession is detectable, never silent — a dangling-pointer is impossible.

Everything here is a NAMING of `Authority.CrossCellImport` / `Authority.ImportBinding` /
`Deos.Membrane`. NO new construct, NO core edit, every keystone `#assert_all_clean` (kernel-clean:
only `propext` / `Classical.choice` / `Quot.sound`). The §8 receipt-digest collision-resistance enters
exactly where the underlying keystones name it (`HInj`/`HFresh` hypotheses through
`CrossCellImport.chain_tamper_evident`), never a Lean axiom, never a `sorry`. `lake build Dregg2`
green (LOCAL).
-/
import Dregg2.Authority.ImportBinding
import Dregg2.Deos.Membrane
import Dregg2.Tactics

namespace Dregg2.Deos.Transclusion

open Dregg2.Exec (Value FieldName)
open Dregg2.Exec.Receipts (Receipt)
open Dregg2.Authority.CrossCellImport (Import SourceHistory importValid readAt advance)
open Dregg2.Authority.ImportBinding (ImportedEq importedEq_binds_provenanced_value
  importedEq_admits_under_valid_import importedEq_lying_import_rejected
  importedEq_stable_under_source_advance)
open Dregg2.Authority (Cap Auth capAuthConferred)
open Dregg2.Deos.Membrane (reshareN reshareN_attenuates reshare_refuses_amplification)

/-! ## §1 — A TRANSCLUSION IS a verified cross-cell observation (the definitional bridge).

`Target::Surface(cell)` made transclusion a NAMING of the kernel cap; here transclusion is a NAMING of
the kernel cross-cell import. A `Transclusion` is exactly an `ImportedEq`: a citation into a peer cell's
finalized history (`imp.provenance` — the cited receipt; `imp.sourceField` — the field quoted) bound to
a local field (`imp.localField`) that the cell program enforces to hold the quoted value. The prompt's
`ObservedFieldEquals` IS this object; "transclusion" is its docuverse name. -/

/-- **`Transclusion`** — Xanadu's transcluded field, made literal: a first-class provenanced citation of
a peer cell's finalized field. It IS an `Authority.ImportBinding.ImportedEq` — the verified cross-cell
observation carrying both the provenance citation (the source receipt + the value its field held there)
and the local-field enforcement. A NAMING (a `def`, not a new type), so every transclusion theorem below
reduces to an existing import/membrane theorem. -/
def Transclusion : Type := ImportedEq

/-- The local field the transclusion populates (the place in MY document where the quote appears). -/
def Transclusion.localField (t : Transclusion) : FieldName := (t : ImportedEq).imp.localField
/-- The field quoted FROM the source cell. -/
def Transclusion.sourceField (t : Transclusion) : FieldName := (t : ImportedEq).imp.sourceField
/-- The value the source field held at the cited receipt (the quoted bytes). -/
def Transclusion.value (t : Transclusion) : Int := (t : ImportedEq).imp.value
/-- The cited source receipt — the immutable provenance the quote is pinned to (height/commitment). -/
def Transclusion.provenance (t : Transclusion) : Receipt := (t : ImportedEq).imp.provenance

/-- **`Transclusion.includes t o n`** — does the transclusion ADMIT the transition `(o, n)`? Iff the
post-state `n` carries the quoted value at the local field — the enforcement leg, the cell program's
`affineEq` atom (fail-closed: an absent local field rejects). This is the realization's "the transcluded
field shows the source value" check, as a decidable Bool. -/
def Transclusion.includes (t : Transclusion) (o n : Value) : Bool := (t : ImportedEq).admits o n

/-- **`transclusion_is_observed_finalized_read` (THE DEFINITIONAL BRIDGE).** A transclusion admits a
transition IFF the post-state carries the cited source value at the local field. So a transclusion IS an
`ObservedFieldEquals` (here: an `ImportedEq`) of a peer cell's finalized field — the verified cross-cell
observation, viewed as a docuverse quote. Not a new object: the kernel import, named. (Directly
`ImportedEq.admits_iff`.) -/
theorem transclusion_is_observed_finalized_read (t : Transclusion) (o n : Value) :
    t.includes o n = true ↔ n.scalar t.localField = some t.value :=
  ImportedEq.admits_iff (t : ImportedEq) o n

/-! ## §2 — PROVENANCE FAITHFUL: the transcluded value equals its source; a forge cannot be cited.

This is the property Xanadu most needed and could not enforce: a transclusion that DISPLAYS bytes other
than the source's is a forged quote. Here it is impossible by construction. When the citation is valid
and the cell admits the transclusion, the displayed value EQUALS the value the source committed at the
cited receipt — the import's third conjunct fused with the cell-program enforcement. And a forged
citation (claiming a value the source never committed) is not even `importValid`: it cannot be opened, so
it cannot be displayed. No opened provenance ⇒ reject. -/

/-- **`transclusion_provenance_faithful` (THE ANTI-FORGE KEYSTONE — the transcluded value CANNOT
diverge from its source).** When the transclusion's citation is VALID against the source history
(`importValid H source t.imp`: the cited receipt is in the source's well-linked chain AND the source
field held the quoted value there) AND the cell admits the transclusion (`t.includes o n`), the
post-state's local field holds EXACTLY the value the SOURCE COMMITTED at the cited receipt —
`readAt source provenance sourceField`. The quote equals its source, provably; a verifier recomputes it,
tooling dates it. This is `importedEq_binds_provenanced_value`, named for the docuverse: a transclusion
is faithful by the same proof the cross-cell import binding is. -/
theorem transclusion_provenance_faithful
    {H : Receipt → Nat} {source : SourceHistory} {t : Transclusion} {o n : Value}
    (hvalid : importValid H source (t : ImportedEq).imp)
    (hincl : t.includes o n = true) :
    n.scalar t.localField
      = some (readAt source t.provenance t.sourceField) :=
  importedEq_binds_provenanced_value hvalid hincl

/-- **`transclusion_faithful_constructible` (the positive direction).** Conversely, a transclusion whose
local field already holds the source's committed value, under a valid citation, ADMITS — the honest quote
is accepted, not merely the forged one refused. So faithful transclusion is constructible, both
polarities present. (Directly `importedEq_admits_under_valid_import`.) -/
theorem transclusion_faithful_constructible
    {H : Receipt → Nat} {source : SourceHistory} {t : Transclusion} {o n : Value}
    (hvalid : importValid H source (t : ImportedEq).imp)
    (hheld : n.scalar t.localField = some (readAt source t.provenance t.sourceField)) :
    t.includes o n = true :=
  importedEq_admits_under_valid_import hvalid hheld

/-- **`transclusion_forge_refused` (THE ANTI-FORGE TOOTH — no opened provenance ⇒ reject).** A FORGED
transclusion — one citing the same source receipt and field as a truthful one but DISPLAYING a different
value than the source committed — is NOT `importValid`, so it cannot be opened to build a faithful quote.
A truthful transclusion (displaying the committed value) IS valid; an adversary cannot present a false
provenanced value to quote. The transcluded bytes cannot be faked. (Directly
`importedEq_lying_import_rejected`.) -/
theorem transclusion_forge_refused
    {H : Receipt → Nat} {source : SourceHistory} {truthful forged : Transclusion}
    (hcite : (truthful : ImportedEq).imp.provenance = (forged : ImportedEq).imp.provenance
              ∧ (truthful : ImportedEq).imp.sourceField = (forged : ImportedEq).imp.sourceField)
    (hdiffer : (truthful : ImportedEq).imp.value ≠ (forged : ImportedEq).imp.value)
    (htruthful : importValid H source (truthful : ImportedEq).imp) :
    ¬ importValid H source (forged : ImportedEq).imp :=
  importedEq_lying_import_rejected hcite hdiffer htruthful

/-! ## §3 — NO AMPLIFICATION: a transclusion is a READ, per-viewer through the membrane.

Xanadu's transclusion was the right idea with the wrong trust model: in an ambient-authority world,
quoting a document could leak authority over it. Here a transclusion is a per-viewer projection through
the deos `Membrane`, and the membrane CANNOT amplify: any chain of reshares confers a SUBSET of the held
authority. So transcluding a peer's field grants nothing over the source beyond observing the cited
value — the quote is a read, not a key, and re-sharing the quote down a delegation chain only ever
shrinks what it grants. We RIDE the membrane's `reshareN_attenuates` directly (the projection is the same
kernel attenuation). -/

/-- **`transclusion_no_amplify` (THE PER-VIEWER CONFINEMENT KEYSTONE — a quote is a READ).** A
transclusion is surfaced per-viewer through the deos membrane (`reshareN`, an arbitrary chain of
per-hop projections). The authority any such projection confers is a SUBSET of the originally held
authority — so however a transcluded surface is re-shared, it grants no more than the holder held over
the source. Transclusion does not hand the reader the source cell; it hands a confined view of one cited
value. This IS `Dregg2.Deos.Membrane.reshareN_attenuates`, named for transclusion: the quote cannot
amplify across any reshare chain. -/
theorem transclusion_no_amplify (keeps : List (List Auth)) (held : Cap) :
    capAuthConferred (reshareN keeps held) ⊆ capAuthConferred held :=
  reshareN_attenuates keeps held

/-- **`transclusion_grants_no_unheld_authority` (the negative tooth).** If authority `a` is NOT in the
held authority over the source, then `a` is NOT conferred by ANY per-viewer transclusion projection of it
— naming `a` in a downstream membrane request does not conjure it. A transclusion cannot manufacture an
authority over the source that the transcluder never held. (Directly `reshare_refuses_amplification`.) -/
theorem transclusion_grants_no_unheld_authority (keeps : List (List Auth)) (held : Cap) (a : Auth)
    (hunheld : a ∉ capAuthConferred held) :
    a ∉ capAuthConferred (reshareN keeps held) :=
  reshare_refuses_amplification keeps held a hunheld

/-! ## §4 — THE UNBREAKABLE LINK: a snapshot transclusion never rots.

The crown. Nelson's deepest unmet promise was the link that does not break — a citation that stays valid
no matter what the source does next. Xanadu's addresses could not deliver it (an HTTP URL rots the
instant the source edits). A dregg transclusion cites an IMMUTABLE PAST receipt, so the quoted reading
never changes as the source advances: the citation is I-CONFLUENT (coordination-free). We RIDE
`importedEq_stable_under_source_advance` — the same I-confluence crown the cross-cell import binding has.
And when the source DOES move on, the quote stays faithful-but-visible: it keeps reporting the cited past
truthfully and the provenance dates it, so supersession is detectable, never a silent dangling pointer. -/

/-- **`transclusion_stable_under_source_advance` (THE UNBREAKABLE-LINK KEYSTONE).** A valid transclusion
stays valid after the source cell takes ANY further turn (here a fresh head receipt; iterate for many):
the citation pins an IMMUTABLE PAST receipt, so the quoted reading never changes as the source advances.
The transclusion is coordination-free where a live cross-cell read is not — it never has to re-coordinate
with the source's future. This is the link that does not break, the property Xanadu wanted and could not
make true. (Directly `Authority.ImportBinding.importedEq_stable_under_source_advance`, the I-confluence
crown.)

Hypotheses: the appended receipt `r` is genuinely new (`hfresh`) and links onto the current head
(`hlink`) — exactly the `Exec.Receipt` append-only growth. -/
theorem transclusion_stable_under_source_advance
    {H : Receipt → Nat} {source : SourceHistory} {t : Transclusion} {r : Receipt} {v : Value}
    (hfresh : r ∉ source.chain)
    (hlink : ∀ hd, source.chain.head? = some hd → r.prevHash = H hd)
    (hvalid : importValid H source (t : ImportedEq).imp) :
    importValid H (advance source r v) (t : ImportedEq).imp :=
  importedEq_stable_under_source_advance hfresh hlink hvalid

/-! ## §5 — NON-VACUITY: a concrete docuverse quote, every property BITES (`#guard` + theorems).

A source "document" cell whose `title` field was finalized to `7` at a cited receipt, and a transclusion
of that title into a local `quote` field. The truthful quote ADMITS and binds the source's committed
value; a quote of the WRONG value is REFUSED; the forged citation is not `importValid`; and the quote
survives the source advancing. All four Xanadu properties demonstrated inhabited and biting. -/

section Witnesses

open Dregg2.Exec.Receipts (mkReceipt genesisSentinel demoHash)
open Dregg2.Deos.Surface (Surface)

/-- The SOURCE document cell's history: an older receipt finalized `title = 7`; the head left it `7`. -/
def srcOld : Receipt := mkReceipt genesisSentinel 7 7 0
def srcNew : Receipt := mkReceipt (demoHash srcOld) 7 7 1
def srcState : Receipt → Value := fun r =>
  if r = srcNew then .record [("title", .int 7)] else .record [("title", .int 7)]
def srcDoc : SourceHistory := ⟨[srcNew, srcOld], srcState⟩

/-- The TRUTHFUL transclusion: local field `quote` IS the source's `title = 7` at `srcOld`. -/
def quoteTitle : Transclusion := (⟨⟨"quote", "title", 7, srcOld⟩⟩ : ImportedEq)
/-- A FORGED transclusion: claims the source's title was `99` (it was `7`) at the same receipt. -/
def forgedQuote : Transclusion := (⟨⟨"quote", "title", 99, srcOld⟩⟩ : ImportedEq)

-- (1) BRIDGE — the transclusion admits a post-state carrying the quoted value `7`; refuses `8`; refuses
-- an absent local field (fail-closed). A transclusion IS the verified observation:
#guard quoteTitle.includes (.record []) (.record [("quote", .int 7)])
#guard quoteTitle.includes (.record []) (.record [("quote", .int 8)]) == false
#guard quoteTitle.includes (.record []) (.record []) == false

-- (2) PROVENANCE FAITHFUL — the truthful citation reads exactly what the source finalized (`7`); the
-- forged citation's claimed value does NOT match what the source committed (the anti-forge tooth bites):
#guard decide (readAt srcDoc quoteTitle.provenance quoteTitle.sourceField = quoteTitle.value)        -- 7 = 7
#guard decide (readAt srcDoc forgedQuote.provenance forgedQuote.sourceField = forgedQuote.value) == false  -- 7 ≠ 99 ⇒ cannot be cited

-- (3) NO AMPLIFY — a doc surface held write+read+grant over the source; transcluding it per-viewer and
-- re-sharing keeps only read; the chain never grows back grant (the quote is a read, not a key):
#guard capAuthConferred (reshareN [[Auth.read]] (Surface 5 [Auth.write, Auth.read, Auth.grant]))
        == [Auth.read]
#guard !(Auth.grant ∈ capAuthConferred
          (reshareN [[Auth.read], [Auth.read]] (Surface 5 [Auth.write, Auth.read, Auth.grant])) : Bool)

/-- **`quote_is_faithful` (non-vacuity of the anti-forge keystone).** The truthful transclusion is valid
AND admits a state carrying `7`, and the keystone yields the source's committed value (`7`) at the local
field — the quote is faithful, both legs firing. -/
theorem quote_is_faithful :
    quoteTitle.includes (.record []) (.record [("quote", .int 7)]) = true ∧
      (.record [("quote", .int 7)] : Value).scalar quoteTitle.localField
        = some (readAt srcDoc quoteTitle.provenance quoteTitle.sourceField) := by
  have hvalid : importValid demoHash srcDoc (quoteTitle : ImportedEq).imp := by
    refine ⟨⟨rfl, rfl⟩, ?_, ?_⟩
    · exact List.mem_cons_of_mem _ List.mem_cons_self
    · decide
  have hincl : quoteTitle.includes (.record []) (.record [("quote", .int 7)]) = true := by decide
  exact ⟨hincl, transclusion_provenance_faithful hvalid hincl⟩

/-- **`forge_cannot_be_cited` (non-vacuity of the anti-forge tooth).** The truthful transclusion is valid
and the forged one is not — a fake quote cannot be opened. -/
theorem forge_cannot_be_cited :
    importValid demoHash srcDoc (quoteTitle : ImportedEq).imp
      ∧ ¬ importValid demoHash srcDoc (forgedQuote : ImportedEq).imp := by
  have hvalid : importValid demoHash srcDoc (quoteTitle : ImportedEq).imp := by
    refine ⟨⟨rfl, rfl⟩, ?_, ?_⟩
    · exact List.mem_cons_of_mem _ List.mem_cons_self
    · decide
  refine ⟨hvalid, ?_⟩
  exact transclusion_forge_refused (truthful := quoteTitle) (forged := forgedQuote)
    ⟨rfl, rfl⟩ (by decide) hvalid

/-- **`quote_survives_source_advance` (non-vacuity of the unbreakable link).** The truthful transclusion
stays valid after the source document takes a further turn (a fresh head receipt committing a new title)
— the citation pins the immutable past, so the quote does not rot. -/
theorem quote_survives_source_advance :
    importValid demoHash (advance srcDoc (mkReceipt (demoHash srcNew) 7 42 2) (.record [("title", .int 42)]))
      (quoteTitle : ImportedEq).imp := by
  have hvalid : importValid demoHash srcDoc (quoteTitle : ImportedEq).imp := by
    refine ⟨⟨rfl, rfl⟩, ?_, ?_⟩
    · exact List.mem_cons_of_mem _ List.mem_cons_self
    · decide
  refine transclusion_stable_under_source_advance (t := quoteTitle) ?_ ?_ hvalid
  · -- the fresh head receipt is not already in the source chain (distinct height ⇒ distinct receipt).
    decide
  · -- it links onto the current head `srcNew` via `demoHash`.
    intro hd hhd
    simp only [srcDoc, List.head?_cons, Option.some.injEq] at hhd
    subst hhd
    rfl

end Witnesses

/-! ## §6 — Axiom hygiene. Every Xanadu-property keystone checked kernel-clean. -/

#assert_all_clean [
  transclusion_is_observed_finalized_read,
  transclusion_provenance_faithful,
  transclusion_faithful_constructible,
  transclusion_forge_refused,
  transclusion_no_amplify,
  transclusion_grants_no_unheld_authority,
  transclusion_stable_under_source_advance,
  quote_is_faithful,
  forge_cannot_be_cited,
  quote_survives_source_advance
]

end Dregg2.Deos.Transclusion
