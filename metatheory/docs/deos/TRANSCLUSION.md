# Transclusion — Xanadu that shipped

Ted Nelson's Xanadu named **transclusion**: include a piece of one document inside another
*by reference*, so the quoted material keeps its identity and its provenance — the same bytes,
the same source, visibly cited, never copied-and-cut — joined by **two-way links** that do not
break. Transclusion is the honest quote: what you read is *literally* the source's content, the
citation says exactly where it came from, and following the link back from the source shows you
everyone who quoted it.

dregg ships transclusion. The four things Xanadu could never make honest are exactly the four
guarantees the verified ocap substrate already provides:

| Xanadu wanted | dregg provides | The proof |
| --- | --- | --- |
| A quote that **equals its source** | The **verified cross-cell finalized read** — a field that IS the value a peer cell committed at a cited receipt | `transclusion_provenance_faithful` |
| **Visible provenance** | The **cited receipt** + content commitment, drawn from the ledger, not the content | `transclusion_is_observed_finalized_read` |
| **Per-viewer confinement** (a quote is not a key) | The **membrane** — a quote is a per-viewer projection that cannot amplify | `transclusion_no_amplify` |
| The **unbreakable link** (the quote never rots) | The **I-confluent import** — the citation pins an immutable past, so the reading never changes | `transclusion_stable_under_source_advance` |
| The **two-way link** | The **receipt chain + witness graph** — "who transcludes me" is a verifiable fact, not a hand-kept index | `Backlinks` (the witness-graph readout) |

Transclusion is **not new machinery**. A transclusion *is* the verified cross-cell observation,
named for the docuverse. The spec is `Dregg2.Deos.Transclusion`; the realization is
`starbridge-web-surface`'s `transclusion` module. Both reuse the existing kernel primitives — no
new construct, no new trust.

## A transclusion is a verified observation

A transclusion of a peer cell's field IS an `Authority.ImportBinding.ImportedEq` — the first-class
provenanced cross-cell binding. It carries one object that holds *both* halves of a quote:

- the **provenance citation** — the source receipt and the value the source field held there
  (`importValid`: the cited receipt is in the source cell's well-linked, append-only chain, and the
  source field held exactly the quoted value in the state that receipt commits); and
- the **local-field enforcement** — the cell program's `affineEq` atom binding the local field to
  the quoted value.

The bridge `transclusion_is_observed_finalized_read` is the equation: a transclusion admits a
transition *iff* the post-state carries the cited source value at the local field. There is no
separate "transclusion type" to trust — it is the kernel import, viewed as a quote.

In the Rust surface, the finalized read is the `dregg://` attested fetch:
`TranscludedField::include(web, source)` resolves the reference, and the bytes it returns are
content-addressed (`content_hash == blake3(bytes)`) and carry a receipt + a quorum-signed
`AttestedRoot`. The quote's displayed bytes are the source's committed bytes.

## Provenance is faithful, and a forge cannot be cited

The quoted value **equals its source, provably**. When the citation is valid and the cell admits
the transclusion, the local field holds exactly the value the source committed at the cited receipt
(`transclusion_provenance_faithful`, riding `importedEq_binds_provenanced_value`). A verifier
recomputes it; tooling dates it.

The dual is the **anti-forge tooth**: a forged transclusion — one citing the same source receipt and
field but displaying a value the source never committed — is **not** `importValid`. It cannot be
opened, so it cannot be displayed (`transclusion_forge_refused`, riding
`importedEq_lying_import_rejected`). No opened provenance ⇒ no quote. In the Rust surface this is
`AttestedResource::verify` — the genuine content → commitment → receipt → receipt-stream-root →
quorum chain; tampered bytes or a receipt not in the committed stream are refused, as is an absent
source (which has no finalized read at all).

Staleness is **faithful but visible**: if the source advances after the cited receipt, the quote
keeps reporting the cited past truthfully, and the provenance dates it, so a reader sees
"quoted at receipt R; the source has since moved on" — supersession is detectable, never a silent
dangling pointer (`stale_import_is_still_valid`).

## A quote is a READ, per-viewer through the membrane

Transcluding a peer's field confers **no authority over the source** beyond observing the cited
value. A transclusion is surfaced per-viewer through the deos `Membrane`, and the membrane cannot
amplify: any chain of reshares confers a subset of the held authority
(`transclusion_no_amplify`, riding `Membrane.reshareN_attenuates`). Naming an authority a prior
holder lacked does not conjure it (`transclusion_grants_no_unheld_authority`).

So a weaker viewer sees the transclusion **attenuated** to its own ceiling, and re-sharing the quote
down a delegation chain only ever shrinks what it grants. In the Rust surface,
`TranscludedField::project_for(viewer, lineage)` is the real `Membrane::project` — the meet of held
authority and the source lineage, through `is_attenuation` on window rights and set-intersection on
the web caveats.

## The unbreakable bidirectional link

This is the property Nelson wanted most and Xanadu's addresses could not deliver: a citation that
does not break, no matter what the source does next. An HTTP URL rots the instant the source edits;
a dregg transclusion cites an **immutable past receipt**, so the quoted reading never changes as the
source advances. The citation is I-confluent — coordination-free — and a snapshot transclusion stays
valid after the source takes any number of further turns
(`transclusion_stable_under_source_advance`, riding `importedEq_stable_under_source_advance`, the
I-confluence crown). The quote never rots.

The *other* direction is the **two-way link**, finally honest. A forward link says "this quote points
at cell X"; a **backlink** says "cell X is quoted by observer O, at receipt R, of value V". In Xanadu
the back-link was a hand-maintained index that could drift out of truth; here it is the witness graph
rendered the other way — the receipt chain and the observation records *are* the bidirectional
structure. The Rust surface's `Backlinks` is the reverse index keyed by source cell:
`observers_of(cell)` enumerates who transcludes it, each record carrying the cited receipt and content
commitment, so a backlink is a **verifiable claim**, not a bare pointer that can dangle.

## Always replayable

Because a transclusion is a verified observation, it inherits the frustum-rehydration story
(`Dregg2.Deos.Rehydration`): the liveness-type carried on a reacquisition is `ReplayedDeterministic`
exactly when every interaction that produced it was a witnessed attested turn — the confined fragment.
A quote rehydrated from a snapshot replays deterministically from its witnessed trace, or is honestly
labelled a reconstruction. The quote is never a silent live read; it is a dated, replayable observation.

## Consumers (named fast-follows)

These ride the transclusion primitive and are *not* built here:

- **The leptos reactive-transclusion** — a Leptos signal that reactively reflects a transcluded field:
  the *live quote*. When the source finalizes a new height, the signal re-fetches through
  `TranscludedField::include` and the view updates, carrying the `Rehydration` liveness-type so the
  reader always knows which kind of true they are seeing.
- **The deos-app-framework transclusion affordance** — a `CellAffordance` whose render embeds a
  `TranscludedField`, so an app declares a quote the way it declares any other affordance, projected
  per-viewer through the same membrane. The `TransclusionAffordance` helper names the seam.

## Where it lives

- **Spec (Lean):** `Dregg2.Deos.Transclusion` — the four Xanadu properties as kernel theorems, each a
  reuse of `Authority.CrossCellImport` / `Authority.ImportBinding` / `Deos.Membrane`. Every keystone
  is `#assert_all_clean` (kernel-clean: only `propext` / `Classical.choice` / `Quot.sound`); the §8
  receipt-digest collision-resistance enters exactly where the underlying keystones name it, never a
  Lean axiom.
- **Realization (Rust):** `starbridge-web-surface`'s `transclusion` module — `TranscludedField`,
  `Provenance`, `Backlinks`, on the real `dregg://` attested fetch + `Membrane`. The Lean is the spec;
  the Rust mirrors the named theorems.
