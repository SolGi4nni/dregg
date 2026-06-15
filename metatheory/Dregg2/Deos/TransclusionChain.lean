/-
# Dregg2.Deos.TransclusionChain — transclusion COMPOSES TRANSITIVELY (the deep intertwingularity).

`Dregg2.Deos.Transclusion` made ONE transclusion honest: a quote that equals its source
(`transclusion_provenance_faithful`), never rots (`transclusion_stable_under_source_advance`, the
unbreakable link), and confers no amplified authority (`transclusion_no_amplify`). Xanadu's deepest
promise was bigger than a single quote: **intertwingularity** — a document quotes a document that
quotes a document, and the whole chain stays provenance-faithful and unbreakable END-TO-END. A quote
of a quote of a quote must (a) resolve to the *original* author's committed bytes, faithfully, through
every intermediary; (b) NOT rot when ANY source in the chain edits, not just the nearest one; and
(c) confer no more authority than the first holder held, however many hops out. Xanadu could deliver
none of these because each link was an ambient copy with a hand-maintained back-index. This module
proves all three by COMPOSING the landed single-transclusion facts — no new mathematics, no new oracle.

## The chain, made literal (two `ImportedEq` legs welded at one field)

A two-hop chain "A transcludes B's transclusion of C" is two `Transclusion`s (= `ImportedEq`s):

  * **`bc`** — B's quote of C: B's local field `bc.localField` IS the value cell C committed at the
    cited receipt (`importValid H cHist bc.imp`). This is the inner quote.
  * **`ab`** — A's quote of B's quote: A's local field `ab.localField` IS the value cell B committed
    at *its* cited receipt (`importValid H bHist ab.imp`).

The two legs are WELDED at one field by the chain link `ChainLink ab bc`: A quotes *the very field B
used to hold its quote of C* (`ab.sourceField = bc.localField`), and what B committed there is exactly
C's value that B quoted (`readAt bHist ab.provenance ab.sourceField = bc.value`). That weld is what
makes the chain faithful end-to-end rather than two unrelated reads — A's quote, resolved, IS C's
committed bytes, *through* B.

## What is proven (each a COMPOSITION of landed `Transclusion`/`ImportBinding`/`Membrane` facts)

  * **`transclusion_chain_provenance_faithful` (THE COMPOSED ANTI-FORGE).** When both legs are valid,
    the weld holds, and A admits its quote, A's local field holds EXACTLY the value cell C COMMITTED at
    the original receipt (`readAt cHist bc.provenance bc.sourceField`). A quote-of-a-quote resolves to
    the *original* source, faithfully, through the chain. Composes `transclusion_provenance_faithful`
    (A's leg) with the weld and `bc`'s validity. The forged-middle-link tooth
    (`transclusion_chain_forged_middle_refused`) shows a B-leg lying about C's value cannot be cited —
    the chain refuses a forged intermediary.

  * **`transclusion_chain_stable` (THE TRANSITIVE UNBREAKABLE LINK — the keystone).** The whole chain
    stays valid as ANY source in it advances: the inner source C may take a turn (`..._inner`), the
    middle source B may take a turn (`..._middle`), or BOTH may advance together (`..._both`) — and
    every leg's citation remains valid, because each cites an IMMUTABLE PAST receipt. The quote-of-a-
    quote never rots, no matter which link's source moves on. Rides
    `importedEq_stable_under_source_advance` (= the `CrossCellImport` I-confluence crown) composed
    across the two legs. This is the property Xanadu most wanted and could not make true: a citation
    CHAIN that does not break, ever.

  * **`transclusion_chain_no_amplify` (THE LIFTED CONFINEMENT).** An N-hop transclusion chain confers a
    SUBSET of the FIRST holder's authority — however far a quote is re-quoted down the chain, it grants
    no more than the original holder held over the source. This IS `Membrane.reshareN_attenuates`
    lifted to the quote chain (each re-quote is a membrane reshare hop); the negative tooth
    (`transclusion_chain_grants_no_unheld_authority`) shows an authority the first holder never held is
    absent from every hop of the chain.

  * **§NON-VACUITY** — a concrete THREE-CELL chain (C commits `title = 7`; B quotes it into `quoteC`;
    A quotes B's `quoteC` into `quoteB`): the honest chain RESOLVES to C's `7` through B and survives
    every source advancing; a FORGED middle link (B claiming C's title was `99`) is REFUSED. Both
    polarities present — a chain that cannot refuse a forged middle is a BUG, and this one does.

Discipline: REUSE only — every theorem composes an existing kernel/`Transclusion` fact, authoring no
new oracle (LAW #1: the proof IS the spec). NEW file; touches no core. Every keystone
`#assert_all_clean` (kernel-clean: only `propext` / `Classical.choice` / `Quot.sound`); the §8
receipt-digest collision-resistance enters exactly where the underlying keystones name it
(`HInj`/`HFresh` through `chain_tamper_evident`), never a Lean axiom, never a `sorry`. `lake build
Dregg2.Deos.TransclusionChain` green (LOCAL).
-/
import Dregg2.Deos.Transclusion

namespace Dregg2.Deos.TransclusionChain

open Dregg2.Exec (Value FieldName)
open Dregg2.Exec.Receipts (Receipt)
open Dregg2.Authority.CrossCellImport (Import SourceHistory importValid readAt advance
  importValid_value_unique)
open Dregg2.Authority.ImportBinding (ImportedEq importedEq_stable_under_source_advance)
open Dregg2.Authority (Cap Auth capAuthConferred)
open Dregg2.Deos.Membrane (reshareN reshareN_attenuates reshare_refuses_amplification)
open Dregg2.Deos.Transclusion (Transclusion transclusion_provenance_faithful
  transclusion_forge_refused transclusion_stable_under_source_advance
  transclusion_no_amplify transclusion_grants_no_unheld_authority)

/-! ## §1 — THE WELD: a chain link binds A's quote to the field B used for its quote of C.

A two-hop chain is two `Transclusion`s. To be a *chain* (not two unrelated quotes) they must be welded:
A must quote the very field B populated with its quote of C, and the value B committed there must be
exactly C's value B quoted. `ChainLink ab bc` is that weld — purely a relation between the two legs'
fields and the middle source's committed readout, no new construct. -/

/-- **`ChainLink ab bc bHist`** — the weld making "A quotes B's quote of C" a genuine chain through the
middle source history `bHist`: A's `sourceField` IS the local field B used to hold its quote of C
(`ab.sourceField = bc.localField`), and at A's cited receipt in B's history the field held EXACTLY the
value C committed that B quoted (`readAt bHist ab.provenance ab.sourceField = bc.value`). The second
conjunct is the honest "B really did commit C's value into that field at that height" fact — it is what
makes the chain faithful end-to-end. -/
def ChainLink (ab bc : Transclusion) (bHist : SourceHistory) : Prop :=
  (ab : ImportedEq).imp.sourceField = (bc : ImportedEq).imp.localField ∧
    readAt bHist (ab : ImportedEq).imp.provenance (ab : ImportedEq).imp.sourceField
      = (bc : ImportedEq).imp.value

/-! ## §2 — PROVENANCE FAITHFUL, COMPOSED: a quote of a quote resolves to the ORIGINAL source.

The headline of intertwingularity. When A transcludes B's transclusion of C, and A admits its quote,
A's displayed bytes equal what cell C COMMITTED at the original receipt — through B, faithfully. The
proof composes `transclusion_provenance_faithful` (A's local field holds B's committed value), the weld
(B's committed value at that field IS the value B quoted from C), and `bc`'s validity (the value B
quoted IS C's committed value). Three landed facts, transitively. -/

/-- **`transclusion_chain_provenance_faithful` (THE COMPOSED ANTI-FORGE KEYSTONE — a quote of a quote
resolves to the ORIGINAL source).** When B's quote of C is valid (`hbc_valid : importValid H cHist
bc.imp`), A's quote of B's quote is valid (`hab_valid : importValid H bHist ab.imp`), the two are
welded into a chain (`hlink : ChainLink ab bc bHist`), and A admits its quote (`hincl : ab.includes o
n`), A's post-state local field holds EXACTLY the value cell C COMMITTED at the original cited receipt
(`readAt cHist bc.provenance bc.sourceField`). The quote-of-a-quote is faithful to the *first* author,
provably — a verifier recomputes it through the chain. Composes `transclusion_provenance_faithful` with
the weld and `bc`'s third conjunct. -/
theorem transclusion_chain_provenance_faithful
    {H : Receipt → Nat} {bHist cHist : SourceHistory} {ab bc : Transclusion} {o n : Value}
    (hbc_valid : importValid H cHist (bc : ImportedEq).imp)
    (hab_valid : importValid H bHist (ab : ImportedEq).imp)
    (hlink : ChainLink ab bc bHist)
    (hincl : ab.includes o n = true) :
    n.scalar ab.localField
      = some (readAt cHist bc.provenance bc.sourceField) := by
  -- A's leg: the local field holds the value cell B COMMITTED at A's cited receipt.
  have hA : n.scalar ab.localField
      = some (readAt bHist ab.provenance ab.sourceField) :=
    transclusion_provenance_faithful hab_valid hincl
  -- the weld: what B committed at that field IS the value B quoted from C (`bc.value`).
  obtain ⟨_, hweld⟩ := hlink
  -- `bc`'s validity: the value B quoted from C IS what C committed at the original receipt.
  have hC : readAt cHist bc.provenance bc.sourceField = (bc : ImportedEq).imp.value := hbc_valid.2.2
  -- normalize the Transclusion projections to their `.imp` fields, then chain the three equalities:
  -- localField = B's committed value (hA) = bc.value (hweld) = C's committed value (hC, reversed).
  simp only [Transclusion.localField, Transclusion.provenance, Transclusion.sourceField] at *
  rw [hA, hweld, ← hC]

/-- **`transclusion_chain_faithful_constructible` (the positive direction).** Conversely, a chain whose
A-leg local field already holds C's committed value (resolved through the weld), under both legs valid,
ADMITS — the honest quote-of-a-quote is accepted, not merely the forged one refused. Faithful chained
transclusion is constructible, both polarities present. (Rides
`Transclusion.transclusion_faithful_constructible` through the weld.) -/
theorem transclusion_chain_faithful_constructible
    {H : Receipt → Nat} {bHist cHist : SourceHistory} {ab bc : Transclusion} {o n : Value}
    (hbc_valid : importValid H cHist (bc : ImportedEq).imp)
    (hab_valid : importValid H bHist (ab : ImportedEq).imp)
    (hlink : ChainLink ab bc bHist)
    (hheld : n.scalar ab.localField = some (readAt cHist bc.provenance bc.sourceField)) :
    ab.includes o n = true := by
  -- rewrite the held value to A's source-committed value (through the weld + bc validity), then
  -- discharge A's leg by `transclusion_faithful_constructible`.
  obtain ⟨_, hweld⟩ := hlink
  have hC : readAt cHist bc.provenance bc.sourceField = (bc : ImportedEq).imp.value := hbc_valid.2.2
  have hheld' : n.scalar ab.localField
      = some (readAt bHist ab.provenance ab.sourceField) := by
    simp only [Transclusion.localField, Transclusion.provenance, Transclusion.sourceField] at *
    rw [hheld, hC, ← hweld]
  exact Dregg2.Deos.Transclusion.transclusion_faithful_constructible hab_valid hheld'

/-! ## §3 — THE FORGED-MIDDLE TOOTH: a lying intermediary cannot be cited.

The chain's anti-forge bites at the MIDDLE too, not just the ends. A forged B-leg — one citing the same
C-receipt and field as a truthful B-quote but DISPLAYING a value C never committed — is NOT `importValid`
against C's history, so it cannot be opened to feed the chain. An adversary cannot smuggle a false value
in through the intermediary. Directly `transclusion_forge_refused` on the inner (C) source. -/

/-- **`transclusion_chain_forged_middle_refused` (THE FORGED-MIDDLE TOOTH).** A forged inner quote
`forgedBC` — citing the same C-receipt and source field as a truthful `bc` but claiming a value cell C
never committed — is NOT valid against C's history, so it cannot be the middle link of any chain. The
chain refuses a forged intermediary: the only citable B-quote is the truthful one. Directly
`Transclusion.transclusion_forge_refused` on the inner source. -/
theorem transclusion_chain_forged_middle_refused
    {H : Receipt → Nat} {cHist : SourceHistory} {bc forgedBC : Transclusion}
    (hcite : (bc : ImportedEq).imp.provenance = (forgedBC : ImportedEq).imp.provenance
              ∧ (bc : ImportedEq).imp.sourceField = (forgedBC : ImportedEq).imp.sourceField)
    (hdiffer : (bc : ImportedEq).imp.value ≠ (forgedBC : ImportedEq).imp.value)
    (htruthful : importValid H cHist (bc : ImportedEq).imp) :
    ¬ importValid H cHist (forgedBC : ImportedEq).imp :=
  transclusion_forge_refused (truthful := bc) (forged := forgedBC) hcite hdiffer htruthful

/-! ## §4 — THE TRANSITIVE UNBREAKABLE LINK: the chain never rots when ANY source advances.

THE KEYSTONE. The single-transclusion crown said one quote survives its one source advancing. The chain
crown says the WHOLE chain survives ANY source in it advancing — the inner source C, the middle source
B, or both — because every leg cites an immutable past receipt. We compose
`transclusion_stable_under_source_advance` (= `importedEq_stable_under_source_advance`, the I-confluence
crown) across the two legs. The quote-of-a-quote does not rot, no matter which link's source moves on:
the unbreakable link is TRANSITIVE. -/

/-- **`transclusion_chain_stable_inner` — the inner source advances, the chain holds.** When cell C
(the original) takes a further turn, the inner quote `bc` stays valid (it pins C's immutable past); A's
leg is untouched. So the chain's validity is preserved against the *original* source moving on. Rides
`transclusion_stable_under_source_advance` on the C-leg. -/
theorem transclusion_chain_stable_inner
    {H : Receipt → Nat} {bHist cHist : SourceHistory} {ab bc : Transclusion}
    {rC : Receipt} {vC : Value}
    (hfreshC : rC ∉ cHist.chain)
    (hlinkC : ∀ hd, cHist.chain.head? = some hd → rC.prevHash = H hd)
    (hbc_valid : importValid H cHist (bc : ImportedEq).imp)
    (hab_valid : importValid H bHist (ab : ImportedEq).imp) :
    importValid H bHist (ab : ImportedEq).imp ∧
      importValid H (advance cHist rC vC) (bc : ImportedEq).imp :=
  ⟨hab_valid, transclusion_stable_under_source_advance hfreshC hlinkC hbc_valid⟩

/-- **`transclusion_chain_stable_middle` — the middle source advances, the chain holds.** When cell B
(the intermediary) takes a further turn, A's quote of B's quote stays valid (it pins B's immutable past
receipt — the field B used for its quote of C is frozen at the cited height); the inner C-leg is
untouched. So the chain survives the *intermediary* moving on. Rides
`transclusion_stable_under_source_advance` on the A-leg. -/
theorem transclusion_chain_stable_middle
    {H : Receipt → Nat} {bHist cHist : SourceHistory} {ab bc : Transclusion}
    {rB : Receipt} {vB : Value}
    (hfreshB : rB ∉ bHist.chain)
    (hlinkB : ∀ hd, bHist.chain.head? = some hd → rB.prevHash = H hd)
    (hbc_valid : importValid H cHist (bc : ImportedEq).imp)
    (hab_valid : importValid H bHist (ab : ImportedEq).imp) :
    importValid H (advance bHist rB vB) (ab : ImportedEq).imp ∧
      importValid H cHist (bc : ImportedEq).imp :=
  ⟨transclusion_stable_under_source_advance hfreshB hlinkB hab_valid, hbc_valid⟩

/-- **`transclusion_chain_stable` (THE TRANSITIVE UNBREAKABLE-LINK KEYSTONE — the chain never rots when
ANY source advances).** When BOTH the middle source B and the inner source C take further turns, the
ENTIRE chain stays valid: A's quote of B's quote pins B's immutable past, and B's quote of C pins C's
immutable past, so neither link rots. This is the property Nelson wanted and Xanadu's addresses could
never deliver — a citation CHAIN that does not break, no matter which source edits next. The unbreakable
link is TRANSITIVE: composes `transclusion_stable_under_source_advance` (the I-confluence crown) across
both legs. (Iterate either hypothesis for many advances per source; chain more legs for deeper quotes —
the same composition.) -/
theorem transclusion_chain_stable
    {H : Receipt → Nat} {bHist cHist : SourceHistory} {ab bc : Transclusion}
    {rB rC : Receipt} {vB vC : Value}
    (hfreshB : rB ∉ bHist.chain)
    (hlinkB : ∀ hd, bHist.chain.head? = some hd → rB.prevHash = H hd)
    (hfreshC : rC ∉ cHist.chain)
    (hlinkC : ∀ hd, cHist.chain.head? = some hd → rC.prevHash = H hd)
    (hab_valid : importValid H bHist (ab : ImportedEq).imp)
    (hbc_valid : importValid H cHist (bc : ImportedEq).imp) :
    importValid H (advance bHist rB vB) (ab : ImportedEq).imp ∧
      importValid H (advance cHist rC vC) (bc : ImportedEq).imp :=
  ⟨transclusion_stable_under_source_advance hfreshB hlinkB hab_valid,
   transclusion_stable_under_source_advance hfreshC hlinkC hbc_valid⟩

/-- **`transclusion_chain_stable_preserves_faithful` (the unbroken link STAYS faithful).** After BOTH
sources advance, the chain not only stays valid but, when A still admits, A's local field STILL resolves
to the value C COMMITTED at the original cited receipt — which is UNCHANGED by the advance, since it pins
C's immutable past. The quote-of-a-quote keeps reporting the original author's committed bytes
faithfully, even as every source in the chain edits. Composes `transclusion_chain_stable` with
`transclusion_chain_provenance_faithful` (the readout is the same immutable past). -/
theorem transclusion_chain_stable_preserves_faithful
    {H : Receipt → Nat} {bHist cHist : SourceHistory} {ab bc : Transclusion} {o n : Value}
    {rB rC : Receipt} {vB vC : Value}
    (hfreshB : rB ∉ bHist.chain)
    (hlinkB : ∀ hd, bHist.chain.head? = some hd → rB.prevHash = H hd)
    (hfreshC : rC ∉ cHist.chain)
    (hlinkC : ∀ hd, cHist.chain.head? = some hd → rC.prevHash = H hd)
    -- the weld holds against the ADVANCED middle history (the cited B-receipt is in the past, frozen):
    (hlink' : ChainLink ab bc (advance bHist rB vB))
    (hab_valid : importValid H bHist (ab : ImportedEq).imp)
    (hbc_valid : importValid H cHist (bc : ImportedEq).imp)
    (hincl : ab.includes o n = true) :
    n.scalar ab.localField
      = some (readAt (advance cHist rC vC) bc.provenance bc.sourceField) := by
  obtain ⟨hab', hbc'⟩ :=
    transclusion_chain_stable hfreshB hlinkB hfreshC hlinkC hab_valid hbc_valid
  exact transclusion_chain_provenance_faithful hbc' hab' hlink' hincl

/-! ## §5 — NO AMPLIFICATION, LIFTED: an N-hop quote chain confers ⊆ the first holder.

Re-quoting a quote down a delegation chain only ever shrinks authority. Each re-quote is a membrane
reshare hop (a per-viewer projection of the surface), so an N-hop transclusion chain is `reshareN`, and
`reshareN_attenuates` bounds it by the FIRST holder's authority. Transcluding a quote of a quote of …
hands no more than the original holder held over the source. We ride the membrane's chain attenuation
directly — the quote chain is the reshare chain. -/

/-- **`transclusion_chain_no_amplify` (THE LIFTED CONFINEMENT KEYSTONE — an N-hop quote chain is a
READ).** An N-hop transclusion chain (a quote of a quote of … re-shared per-viewer through the deos
membrane at every hop, `reshareN keeps`) confers a SUBSET of the FIRST holder's authority over the
source. However many times a quote is re-quoted down the chain, it grants no more than the original
holder held — the quote chain cannot amplify. This IS `Membrane.reshareN_attenuates`, lifted to the
transclusion chain (and definitionally `Transclusion.transclusion_no_amplify` on the same chain). -/
theorem transclusion_chain_no_amplify (keeps : List (List Auth)) (held : Cap) :
    capAuthConferred (reshareN keeps held) ⊆ capAuthConferred held :=
  transclusion_no_amplify keeps held

/-- **`transclusion_chain_grants_no_unheld_authority` (the negative tooth).** If authority `a` is NOT in
the FIRST holder's authority over the source, then `a` is NOT conferred by ANY hop of the N-hop quote
chain — naming `a` in a downstream re-quote does not conjure it. A quote chain cannot manufacture an
authority over the source the original holder never had. Directly
`Transclusion.transclusion_grants_no_unheld_authority` on the chain. -/
theorem transclusion_chain_grants_no_unheld_authority
    (keeps : List (List Auth)) (held : Cap) (a : Auth)
    (hunheld : a ∉ capAuthConferred held) :
    a ∉ capAuthConferred (reshareN keeps held) :=
  transclusion_grants_no_unheld_authority keeps held a hunheld

/-! ## §6 — NON-VACUITY: a concrete THREE-CELL chain, every property BITES (`#guard` + theorems).

Cell C (the original document) finalized `title = 7` at a cited receipt. Cell B quotes that title into
its `quoteC` field. Cell A quotes B's `quoteC` into its `quoteB` field. The honest chain RESOLVES to
C's `7` through B and survives every source advancing; a FORGED middle link (B claiming C's title was
`99`) is REFUSED. All three intertwingularity properties demonstrated inhabited and biting. -/

section Witnesses

open Dregg2.Exec.Receipts (mkReceipt genesisSentinel demoHash)
open Dregg2.Deos.Surface (Surface)

/-- Cell C (the ORIGINAL document): an older receipt finalized `title = 7`; head left it `7`. -/
def cOld : Receipt := mkReceipt genesisSentinel 7 7 0
def cNew : Receipt := mkReceipt (demoHash cOld) 7 7 1
def cState : Receipt → Value := fun _ => .record [("title", .int 7)]
def cDoc : SourceHistory := ⟨[cNew, cOld], cState⟩

/-- Cell B (the INTERMEDIARY): an older receipt committed `quoteC = 7` (B's quote of C's title); the
head left it `7`. B's field `quoteC` is the field A will quote. -/
def bOld : Receipt := mkReceipt genesisSentinel 7 7 0
def bNew : Receipt := mkReceipt (demoHash bOld) 7 7 1
def bState : Receipt → Value := fun _ => .record [("quoteC", .int 7)]
def bDoc : SourceHistory := ⟨[bNew, bOld], bState⟩

/-- B's quote of C: B's local field `quoteC` IS C's `title = 7` at `cOld`. -/
def bcQuote : Transclusion := (⟨⟨"quoteC", "title", 7, cOld⟩⟩ : ImportedEq)
/-- A's quote of B's quote: A's local field `quoteB` IS B's `quoteC = 7` at `bOld`. -/
def abQuote : Transclusion := (⟨⟨"quoteB", "quoteC", 7, bOld⟩⟩ : ImportedEq)
/-- A FORGED inner quote: claims C's title was `99` (it was `7`) at the same C-receipt. -/
def forgedBC : Transclusion := (⟨⟨"quoteC", "title", 99, cOld⟩⟩ : ImportedEq)

-- The legs are welded: A quotes the field B used (`quoteC`), and B committed C's value (`7`) there:
#guard decide ((abQuote : ImportedEq).imp.sourceField = (bcQuote : ImportedEq).imp.localField)  -- "quoteC" = "quoteC"
#guard decide (readAt bDoc (abQuote : ImportedEq).imp.provenance (abQuote : ImportedEq).imp.sourceField
        = (bcQuote : ImportedEq).imp.value)                                                      -- B's quoteC@bOld = 7 = bc.value

-- (1) CHAIN PROVENANCE FAITHFUL — A admits a post-state carrying `7` at `quoteB`; the inner quote reads
-- exactly what C finalized (`7`); the forged inner quote's claim does NOT match C (the tooth bites):
#guard abQuote.includes (.record []) (.record [("quoteB", .int 7)])
#guard decide (readAt cDoc bcQuote.provenance bcQuote.sourceField = bcQuote.value)               -- 7 = 7 (C's truth through the chain)
#guard decide (readAt cDoc forgedBC.provenance forgedBC.sourceField = forgedBC.value) == false   -- 7 ≠ 99 ⇒ forged middle cannot be cited

-- (3) CHAIN NO AMPLIFY — A doc surface held write+read+grant; a 3-hop quote chain keeps only read; the
-- chain never grows back grant (the quote chain is a read, not a key):
#guard capAuthConferred (reshareN [[Auth.write, Auth.read], [Auth.read], [Auth.read]]
        (Surface 5 [Auth.write, Auth.read, Auth.grant])) == [Auth.read]
#guard !(Auth.grant ∈ capAuthConferred
          (reshareN [[Auth.read], [Auth.read], [Auth.read]]
            (Surface 5 [Auth.write, Auth.read, Auth.grant])) : Bool)

/-- The chain link for the honest witness (the weld holds: A quotes B's `quoteC`, B committed `7`). -/
theorem witness_chain_link : ChainLink abQuote bcQuote bDoc := by
  refine ⟨rfl, ?_⟩
  decide

/-- The inner quote `bcQuote` is valid against C's history. -/
theorem witness_bc_valid : importValid demoHash cDoc (bcQuote : ImportedEq).imp := by
  refine ⟨⟨rfl, rfl⟩, ?_, ?_⟩
  · exact List.mem_cons_of_mem _ List.mem_cons_self
  · decide

/-- The outer quote `abQuote` is valid against B's history. -/
theorem witness_ab_valid : importValid demoHash bDoc (abQuote : ImportedEq).imp := by
  refine ⟨⟨rfl, rfl⟩, ?_, ?_⟩
  · exact List.mem_cons_of_mem _ List.mem_cons_self
  · decide

/-- **`chain_resolves_to_original` (non-vacuity of the composed anti-forge keystone).** The honest
two-hop chain, when A admits a state carrying `7` at `quoteB`, resolves A's field to the value cell C
COMMITTED at the original receipt (`7`) — through B, faithfully. The intertwingularity headline,
inhabited and firing. -/
theorem chain_resolves_to_original :
    (.record [("quoteB", .int 7)] : Value).scalar abQuote.localField
      = some (readAt cDoc bcQuote.provenance bcQuote.sourceField) := by
  have hincl : abQuote.includes (.record []) (.record [("quoteB", .int 7)]) = true := by decide
  exact transclusion_chain_provenance_faithful witness_bc_valid witness_ab_valid
    witness_chain_link hincl

/-- **`forged_middle_cannot_be_cited` (non-vacuity of the forged-middle tooth).** The truthful inner
quote is valid and the forged one (B claiming C's title was `99`) is not — a forged intermediary cannot
be smuggled into the chain. -/
theorem forged_middle_cannot_be_cited :
    importValid demoHash cDoc (bcQuote : ImportedEq).imp
      ∧ ¬ importValid demoHash cDoc (forgedBC : ImportedEq).imp := by
  refine ⟨witness_bc_valid, ?_⟩
  exact transclusion_chain_forged_middle_refused (bc := bcQuote) (forgedBC := forgedBC)
    ⟨rfl, rfl⟩ (by decide) witness_bc_valid

/-- **`chain_survives_both_sources_advancing` (non-vacuity of the TRANSITIVE unbreakable link).** The
honest chain stays valid after BOTH cell B (the intermediary) and cell C (the original) take further
turns — each leg pins its immutable past, so neither link rots. The transitive unbreakable link, biting:
the quote-of-a-quote does not break no matter which source edits. -/
theorem chain_survives_both_sources_advancing :
    importValid demoHash (advance bDoc (mkReceipt (demoHash bNew) 7 42 2) (.record [("quoteC", .int 42)]))
        (abQuote : ImportedEq).imp ∧
      importValid demoHash (advance cDoc (mkReceipt (demoHash cNew) 7 42 2) (.record [("title", .int 42)]))
        (bcQuote : ImportedEq).imp := by
  refine transclusion_chain_stable (ab := abQuote) (bc := bcQuote) ?_ ?_ ?_ ?_ witness_ab_valid witness_bc_valid
  · -- the fresh B-head is not already in B's chain (distinct height ⇒ distinct receipt).
    decide
  · -- it links onto B's current head `bNew` via `demoHash`.
    intro hd hhd
    simp only [bDoc, List.head?_cons, Option.some.injEq] at hhd
    subst hhd; rfl
  · -- the fresh C-head is not already in C's chain.
    decide
  · -- it links onto C's current head `cNew` via `demoHash`.
    intro hd hhd
    simp only [cDoc, List.head?_cons, Option.some.injEq] at hhd
    subst hhd; rfl

/-- **`chain_resolves_to_concrete_seven` (the resolution is NON-VACUOUS — a concrete value).** The
honest chain resolves A's `quoteB` field not just to "C's committed value" abstractly but to the
CONCRETE scalar `7` — the original author's actual bytes, surfaced through B. Proves the faithfulness
keystone yields a real value, not a vacuous tautology. -/
theorem chain_resolves_to_concrete_seven :
    (.record [("quoteB", .int 7)] : Value).scalar abQuote.localField = some 7 := by
  -- the chain resolves to C's committed value, and C's committed value at the cited receipt IS 7.
  rw [chain_resolves_to_original]
  decide

/-- **`forged_middle_breaks_the_weld` (the weld is LOAD-BEARING — a forged middle cannot even form a
chain link).** A chain link built from the FORGED inner quote is structurally IMPOSSIBLE at the WELD: the
field A quotes (`quoteC`) held `7` in B's history, but the forged inner quote claims value `99`, so the
weld's second conjunct (`readAt bDoc … = forgedBC.value`, i.e. `7 = 99`) is FALSE. So the forged middle
is refused at TWO independent gates — `importValid` (`forged_middle_cannot_be_cited`) AND the chain weld
(here). The `ChainLink` predicate is non-vacuous: it genuinely distinguishes the honest middle from the
forged one, not just decoration. -/
theorem forged_middle_breaks_the_weld : ¬ ChainLink abQuote forgedBC bDoc := by
  intro h
  obtain ⟨_, hweld⟩ := h
  -- hweld : readAt bDoc abQuote.imp.provenance abQuote.imp.sourceField = forgedBC.imp.value, i.e. 7 = 99.
  exact absurd hweld (by decide)

end Witnesses

/-! ## §7 — Axiom hygiene. Every intertwingularity keystone checked kernel-clean. -/

#assert_all_clean [
  transclusion_chain_provenance_faithful,
  transclusion_chain_faithful_constructible,
  transclusion_chain_forged_middle_refused,
  transclusion_chain_stable_inner,
  transclusion_chain_stable_middle,
  transclusion_chain_stable,
  transclusion_chain_stable_preserves_faithful,
  transclusion_chain_no_amplify,
  transclusion_chain_grants_no_unheld_authority,
  chain_resolves_to_original,
  chain_resolves_to_concrete_seven,
  forged_middle_cannot_be_cited,
  forged_middle_breaks_the_weld,
  chain_survives_both_sources_advancing
]

end Dregg2.Deos.TransclusionChain
