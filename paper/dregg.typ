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
protocol's correct evolution: a verifier holding one aggregate root learns that
every state transition in the system's history was authorized, conservative,
and correctly committed --- re-executing nothing and trusting no executor.

The model is small. State lives in *cells*; a *turn* is the exercise of an
attenuable, proof-carrying token over owned state, leaving a verifiable
receipt. The kernel governs four substances, each under its own discipline of
use --- value is linear ($Sigma delta = 0$, exactly), authority is produced
under non-forgeability, evidence is monotone, state is guarded-mutable --- and
its signature is eight verbs, each the structural rule of one substance's
discipline. Minimality of the signature is a theorem, not an aesthetic.

Authority is treated as _constructive knowledge_: to hold a capability is to be
able to exhibit a witness that authorizes an act, never merely to assert it.
The system is organized around the asymmetry that proof-checking is cheap and
trusted while proof-search is undecidable and untrusted, and its central
authority law is generative rather than monotone: authority genuinely grows ---
introduction, sealer/unsealer amplification, minting --- but only through
authorized, receipt-disclosed construction from connectivity already held.

Everything that constrains a turn is one predicate algebra appearing at four
polarities (caveats on delegated power, programs on owned state, preconditions
on turns, demands on the world), with two computed prices: a coordination dial
(a confluence-stable guard runs coordination-free; one that is not provably so
forces ordering) and a disclosure dial (committed, range-proved, and
jointly-garbled evaluation; what the proof does not need, it does not see).

The semantics are a Lean 4 kernel that is also the deployed executor, reached
by FFI from the node; the proof system is a STARK whose circuit is _emitted
from_ that kernel rather than hand-authored. The assurance case is organized by
guarantee --- authority, conservation, integrity, freshness, unfoolability, and
a running-entry guarantee stating the first three over the exact function the
node invokes --- with every keystone machine-pinned to the Lean kernel's three
axioms plus an explicit eight-carrier cryptographic and liveness floor.
Applications are factory-minted cells whose rules are predicate programs
enforced by the same executor, so application contracts are inherited from
kernel theorems rather than re-established per app.

The capability is one abstraction across a distance parameter. At its near end
a local microkernel object and at its far end a distributed cell are the same
attenuable reference, and the single-machine case is the collapsed limit where
revocation is immediate and a commit is synchronous, not a degraded subset. On
that axis the substrate descends to a capability-secure microkernel ($"seL4"$),
where the kernel's capability graph isolates the protection domains and dregg's
mediates the cells inside them, with a real prover checking proofs on the
device; and it descends to a database, where reads are SQL and writes are
verified turns. It surfaces, too: a window is a capability, an interaction is a
turn, and a rendered scene is a per-viewer projection whose non-interference,
attenuation, and liveness-typed rehydration are kernel theorems restated for
pixels. The proof architecture keeps these claims honest as it evolves --- the
circuit shape rotates under proof of equivalent enforcement, and every finalized
turn stays verifiable across shapes --- so a light client's one check covers the
whole history regardless of where and how it was produced.

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
