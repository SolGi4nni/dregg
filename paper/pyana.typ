// =============================================================================
// Pyana: A Distributed Object-Capability Runtime
// with Zero-Knowledge Authorization and Proof-Carrying State
// =============================================================================

#set document(
  title: "Pyana: A Distributed Object-Capability Runtime with Zero-Knowledge Authorization and Proof-Carrying State",
  author: ("Ember Arlynx"),
  date: datetime(year: 2026, month: 5, day: 21),
)

#set page(
  paper: "us-letter",
  margin: (x: 1.2in, y: 1.2in),
  numbering: "1",
  header: context {
    if counter(page).get().first() > 1 [
      #set text(size: 9pt, fill: luma(100))
      Pyana: Distributed Object-Capability Runtime
      #h(1fr)
      Draft -- May 2026
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

// --- Title -------------------------------------------------------------------

#align(center)[
  #text(size: 18pt, weight: "bold")[
    Pyana: A Distributed Object-Capability Runtime \
    with Zero-Knowledge Authorization and Proof-Carrying State
  ]
  #v(1em)
  #text(size: 11pt)[Ember Arlynx]
  #v(0.3em)
  #text(size: 10pt, fill: luma(80))[
    Draft -- May 21, 2026 \
    `github.com/pyana-dev/breadstuffs`
  ]
]

#v(2em)

// --- Abstract ----------------------------------------------------------------

#heading(level: 1, numbering: none)[Abstract]

We present Pyana, a distributed object-capability runtime in which isolated objects (cells) communicate via atomic message turns, delegate authority through attenuated capability chains, and prove authorization in zero knowledge. The core observation is that monotonic capability attenuation---restricting a bearer token's scope through successive delegation---forms an incrementally verifiable computation: each restriction step is a fold over a committed fact set, producing a strictly smaller successor state. We encode capabilities as Datalog fact sets, commit them to 4-ary Merkle trees using Poseidon2 over BabyBear, and prove correct evaluation of authorization rules inside a STARK. The verifier learns a single bit---authorized or not---without observing the delegation chain, intermediate authorities, or the agent's other capabilities.

The runtime implements E-style distributed object semantics: promise pipelining via eventual references, three-party introduction for capability routing, and sealer/unsealer pairs for partition-tolerant offline transfer. A privacy-preserving intent marketplace enables capability discovery without leaking what agents hold. State is proof-carrying: receipt chains serve as the primary state representation, with IVC compression and federation reduced to an ordering service over nullifiers. A Capability Derivation Tree---the distributed dual of seL4's CDT---tracks delegation lineage as a proof structure rather than a kernel-enforced tree.

The economic model provides sustainable federated validation without inflation: fees are split between proposer, treasury, and burn; validators stake via privacy-compatible range proofs; and an EIP-1559-adapted fee market adjusts to demand. An AI agent coordination substrate treats agents as first-class entities with identity, authority, economic relationships, and auditable histories---the networked analog of seL4's process isolation.

The system is implemented in approximately 157k lines of Rust across 26 crates, with 1,827 tests, real STARK proof generation ($tilde$24 KiB proofs, sub-second generation on BabyBear4 extension field at 124-bit security), real Ed25519/BLS12-381 cryptography, working multi-node TCP consensus, a browser extension wallet, and 20+ end-to-end demo scenarios in a unified harness.

#v(1em)

// --- Sections ----------------------------------------------------------------

#include "sections/01-introduction.typ"
#include "sections/02-model.typ"
#include "sections/03-authorization.typ"
#include "sections/04-proofs.typ"
#include "sections/05-privacy.typ"
#include "sections/06-federation.typ"
#include "sections/07-economics.typ"
#include "sections/08-agents.typ"
#include "sections/09-implementation.typ"
#include "sections/10-comparison.typ"
#include "sections/11-future.typ"
#include "sections/12-conclusion.typ"

// --- References --------------------------------------------------------------

#heading(level: 1, numbering: none)[References]

#set text(size: 9.5pt)

#bibliography(title: none, style: "ieee", "refs.yml")
