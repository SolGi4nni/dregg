// =============================================================================
// dregg: A Verified Distributed Object-Capability Substrate
// =============================================================================
// Paper of record. Compile: typst compile main.typ dregg.pdf
//
// All sections are written to the current system and voice (present tense,
// first principles, Lean-pinned). Every #lean("Module.name") citation resolves
// to a declaration under metatheory/Dregg2/, #assert_axioms-pinned to the
// kernel triple {propext, Classical.choice, Quot.sound}.

#set document(
  title: "dregg: A Verified Distributed Object-Capability Substrate",
  author: ("Ember Arlynx"),
)

#set page(
  paper: "us-letter",
  margin: (x: 1.2in, y: 1.2in),
  numbering: "1",
  header: context {
    if counter(page).get().first() > 1 [
      #set text(size: 9pt, fill: luma(100))
      dregg: A Verified Distributed Object-Capability Substrate
      #h(1fr)
    ]
  },
)

#set text(font: "New Computer Modern", size: 10.5pt)
#set par(justify: true, leading: 0.58em)
#set heading(numbering: "1.1")
#set math.equation(numbering: "(1)")
#show heading.where(level: 1): it => {
  v(1.2em)
  text(size: 14pt, weight: "bold", it)
  v(0.6em)
}
#show heading.where(level: 2): it => {
  v(0.8em)
  text(size: 12pt, weight: "bold", it)
  v(0.4em)
}
#show raw.where(block: true): set text(size: 9pt)
#show raw.where(block: true): block.with(
  fill: luma(245),
  inset: 8pt,
  radius: 3pt,
  width: 100%,
)

// A Lean declaration name, rendered as inline code (the citation form for a
// mechanized claim; every such name is resolvable in metatheory/Dregg2/ and
// `#assert_axioms`-pinned to the kernel triple).
#let lean(name) = raw(name)

// --- Title -------------------------------------------------------------------

#align(center)[
  #text(size: 18pt, weight: "bold")[dregg]
  #v(0.2em)
  #text(size: 15pt, weight: "bold")[A Verified Distributed Object-Capability Substrate]
  #v(1em)
  #text(size: 11pt)[Ember Arlynx]
  #v(0.3em)
  #text(size: 10pt, fill: luma(80))[
    `github.com/emberian/dregg`
  ]
]

#v(2em)

// --- Abstract ----------------------------------------------------------------

#heading(level: 1, numbering: none)[Abstract]

dregg is a distributed object-capability substrate designed so that an absent
party can verify a history without re-executing it or trusting its executor. An
atomic turn exercises attenuable authority over owned state and leaves a
receipt. For histories produced with full-turn proving enabled, recursive
aggregation reduces those receipts to one root. Subject to an explicit
cryptographic and liveness floor, checking that root establishes that the
attested history preserves authorization, value conservation, and faithful
state commitment.

The model divides a cell into four substances with different disciplines:
linear value, guarded-mutable state, constructively produced authority, and
monotone evidence. Holding a capability means being able to exhibit the witness
required for an act; delegation may attenuate authority, while new authority
must be constructed from connectivity already held and disclosed by a receipt.
One predicate algebra expresses caveats, cell programs, turn preconditions, and
intent demands, and makes their coordination and disclosure costs explicit.

The Lean 4 kernel defines these transition semantics and is also the executor
the node invokes through FFI. The same verified modules emit byte-pinned circuit
descriptors. Rust interprets those descriptors but does not author their
constraint algebra, and the descriptor prover is the production proving path.
The assurance case then connects the running entry to five guarantees---
authority, conservation, integrity, freshness, and light-client
unfoolability---while pinning each theorem's axiom set and exposing every
cryptographic or liveness hypothesis.

Those hypotheses matter. At the deployed domain size the mechanized
commit-phase ledger (BCIKS20's $epsilon_C$, fixed-parameter) is a knob-ledger
calculation, not an adversarial soundness theorem over
supplied proofs, and extraction remains an explicit carrier; the assurance
section states the evaluated figure and its caveats. A costed
extension-degree-eight configuration exceeds 120 bits under
the same ledger but is not deployed. The paper therefore separates the
mechanized transition argument, the proof-system floor, and deployment
correspondence instead of collapsing them into one claim. The same kernel spans
distributed cells and local seL4 protection domains, and factory-minted
applications reuse its receipt and theorem boundary rather than introducing a
second execution model.

#v(1em)

// --- Sections ----------------------------------------------------------------

#include "sections/01-introduction.typ"
#include "sections/02-model.typ"
#include "sections/03-authorization.typ"
#include "sections/04-proofs.typ"
#include "sections/05-guards.typ"
#include "sections/06-ordering.typ"
#include "sections/07-realization.typ"
#include "sections/08-proof-architecture.typ"
#include "sections/09-firmament.typ"
#include "sections/10-deos.typ"
#include "sections/11-sel4.typ"
#include "sections/12-pg-dregg.typ"
#include "sections/17-games.typ"
#include "sections/18-interchain.typ"
#include "sections/19-economics.typ"
#include "sections/20-postquantum.typ"
#include "sections/13-assurance.typ"
#include "sections/14-related.typ"
#include "sections/15-limitations.typ"
#include "sections/16-conclusion.typ"

// --- Appendix ----------------------------------------------------------------

#set heading(numbering: "A.1")
#counter(heading).update(0)

#include "sections/appendix-a-garbled-poseidon2.typ"

// --- References --------------------------------------------------------------

#heading(level: 1, numbering: none)[References]

#set text(size: 9.5pt)

#bibliography(title: none, style: "ieee", "refs.yml")
