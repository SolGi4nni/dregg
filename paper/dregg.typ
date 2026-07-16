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

dregg is a distributed object-capability substrate whose proofs witness the
protocol's evolution. A verifier holding one aggregate root learns that every
state transition in the system's history was authorized, conservative, and
correctly committed. It re-executes nothing and trusts no executor.

State lives in cells. A turn is the exercise of an attenuable, proof-carrying
token over owned state, and it leaves a verifiable receipt. The kernel governs
four substances, each under its own discipline of use: value is linear,
authority is produced under non-forgeability, evidence is monotone, state is
guarded-mutable. The kernel signature is eight verbs, one structural rule per
discipline. Minimality of the signature is a theorem
(#lean("VerbRegistry.minimality")), not an aesthetic.

Authority is constructive: to hold a capability is to be able to exhibit a
witness that authorizes an act. Authority grows through introduction,
amplification, and minting, but only by authorized, receipt-disclosed
construction from connectivity already held. Every constraint on a turn is one
predicate algebra at four polarities, priced by a coordination dial and a
disclosure dial.

The semantics are a Lean 4 kernel that is also the deployed executor, reached
by FFI from the node. The STARK circuit is emitted from that kernel: no
deployed first-party circuit is authored in Rust, and a build gate fails any
constraint algebra added there. One proving path exists, the descriptor
prover; the hand-written engine is deleted. At the deployed recursion apex the
FRI carrier calculates to 57.98 bits of soundness under the proximity-gaps
bound the prover cites --- a bound on a supplied proof, not an extraction
theorem --- while a configuration at extension degree eight clears 120. The
assurance case is itself a Lean artifact: each guarantee's keystone is pinned
to the kernel's three axioms plus an explicit cryptographic and liveness
floor.

The capability is one abstraction across a distance parameter: a local
microkernel object and a distributed cell are the same attenuable reference.
On seL4 the verified executor runs inside a protection domain and commits a
turn with the same accepted receipt the host produces; the microkernel's
capability graph isolates the domains while dregg's mediates the cells within.
The circuit shape rotates under proof of equivalent enforcement, and every
finalized turn remains verifiable across shapes, so a light client's one check
covers the whole history.

Applications are factory-minted cells whose rules are predicate programs
enforced by the same executor, so their contracts are inherited from kernel
theorems rather than re-established per app; a deployed portfolio of verified
games, holding-weighted governance, and cross-chain settlement each exercise
the same receipt object.

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
