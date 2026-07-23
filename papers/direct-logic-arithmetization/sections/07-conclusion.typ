#import "../section-helpers.typ": callout, boundary

= Conclusions: from a broken shortcut to a certified compiler family

The public BitLogic shortcut fails. The underlying research direction does not.
The useful result of this audit is a stronger architecture than the claim that
prompted it.

#callout([DECISIVE RESULT], [
  We now have a coherent path from matrix FOL to sound compiler semantics and a
  statement-bound public direct-table relation, and from bounded finite logic to
  optimized public descriptors for four named DREGG decisions. The public factor
  descriptor moves from 35 to 18 constraints with exact statement soundness; live
  production proofs retain smaller serialized outputs for three optimized cases,
  while Strand supplies an unchanged negative control. Fully priced FHE accounting
  erases the earlier residual multiplication lead instead of hiding its zero
  observation. Higher-order, categorical, interaction, query, and realizability
  results then generalize the architecture beyond FOL without pretending that one
  finite polynomial table is the primitive form of logic.
])

== The corrected answer to the original claim

Gabbay's theorem is not false in its actual setting. Over nonnegative rationals,
zero residuals have the intended meaning: conjunction and bounded universal
quantification are sums; disjunction and bounded existential quantification are
products. The error is to transport those equations into a prime field without
transporting their semantic hypotheses.

The repaired compiler makes that transport explicit. It either proves numerator
and denominator bounds before field projection, or converts truth to canonical
bits with checked zero witnesses. `GabbayMatrixCompiler` reconstructs the actual
matrix language and interpolation mechanism; `GabbayMatrixBridge` proves the two
formal presentations coherent; and `GabbayDescriptorIR2` supplies a fixed-shape
private Skolem-witness relation in the live proof grammar.
`GabbayDescriptorIR2PublicBoundary` proves that this descriptor has zero public
inputs, no hash sites, and an empty v1 range carrier: acceptance does not attest
an independently named external table, and the fixed instance is not
interpolation-performance evidence. The empty carrier field is not an absent
range check --- the bound is carried by six emitted 30-bit range lookups, which
bind no external name and so leave the statement gap open. The separate
`GabbayDescriptorIR2PublicBinding` closes that gap directly: six public cells
bind the complete two-by-three table; six trace columns carry 15 constraints ---
six PI pins, three linear acceptance atoms, and six range lookups --- with no
nonlinear product anywhere in acceptance; under the canonical decoding
convention alone, a satisfying trace exists iff the named table satisfies source
`Holds`, and a one-cell public tamper is refused. This integrity variant reveals
the whole table, provides zero table privacy, and deliberately performs no
interpolation. `FiniteSignatureFOLDescriptorIR2` then
extends the live route to many relation symbols, total public function symbols,
equality, all connectives, and nested finite quantifiers.

BitLogic takes neither repaired route in its released equations. It reverses the
zero-true connective interpretation and multiplies obligations that must all
hold. The published swap product therefore accepts a displayed counterexample.
That is not a speculative concern or a disagreement about notation: it is a
wrong acceptance relation.

The same standard caught our own first attempt. That public relation originally
accepted with a field sum of three squared residuals and was made sound by a
Lean-side no-wrap premise that no emitted byte enforced --- and over BabyBear
$284861408^2 = -1$, so a fully canonical false table cancelled to zero and was
accepted. The repair moved both halves onto the wire: three linear atoms, one
per equation, and a 30-bit range lookup on each bound column, in the graduated
form the deployed assembly actually realizes. The two premises then became
theorems, so the statement results no longer take a certificate argument. Two
counterexamples are retained as armed canaries, one refuted by the atoms alone
and one refuted only by a range tooth, so neither half of the repair can be
deleted without turning a theorem red. One premise moved rather than vanished
and is named as such: `Satisfied2` has no faithfulness conjunct for the range
table, so refusals through a range tooth carry `HonestRangeTable` explicitly ---
a carrier-level condition on the trace family, uniform across every range lookup
in the codebase, discharged in deployment by the assembly that builds the limb
decomposition itself.

== The novel contribution that emerged

The strongest reusable construction is *certified change of presentation*.
One statement may be realized by different evidence objects:

#align(center)[
  $ "source judgment" arrow "residual" arrow "Boolean graph"
    arrow "shared net" arrow "AIR or FHE plan". $
]

Each arrow carries semantic equivalence, a fail-closed checker or proof, and an
explicit resource bound. Composition of such arrows is itself certified. This
turns backend choice into proof-producing compilation rather than folklore.
The deterministic optimizer realizes the idea for checked Boolean rewrites; the
reference Pareto search chooses residual or Boolean representations per grounded
subformula; and the hybrid proof/FHE certificate proves both backends decide the
same raw opening.

This is also where the verified resource results come from. Checked factor sharing
reduces graph equations from 30 to 13. Its *public* accepting descriptor includes
four PI bindings and one output check, so the complete constraint ledger moves
from 35 to 18; multiplications move from 26 to 13, auxiliaries from 17 to 8, and
width from 21 to 12. Every constraint has degree at most 2. Arbitrary-trace public
soundness, canonical completeness, and the accepted optimizer/layout/exact-byte
certificate make this an exact statement-bound result rather than a witness-only
cost model.

The same construction now compiles four production-derived DREGG decisions. For
Admission, public constraints move 121 to 71, multiplications 108 to 58, width 77
to 47, and one retained proof 14,016 to 11,894 bytes. Upgrade moves 33 to 23, 28
to 18, 21 to 15, and 10,431 to 10,081 bytes; Clearance has the same relation
ledger and moves 10,469 to 10,157 proof bytes. Strand is already normal: 17
constraints, 13 multiplications, width 11, and 9,850 proof bytes on both sides.
These skeletons are proved equivalent to the named DREGG decisions while their
arithmetic, hash, membership, lifecycle, lookup, and receipt-comparison atoms keep
their existing implementations.

The paired timing capture does not support a speedup claim. Severe host contention
produced wide, nonmonotonic distributions; most decisively, byte-identical Strand
source and optimized cases reported different medians and tails. The exact ledgers
and retained proof-size changes survive that control. A 10--100x latency claim does
not.

Fully priced FHE accounting closes a second tempting overclaim. At residual bound
$B=4$, the former 6-versus-9 inner comparison becomes 9 = 9 after the exact bounded
zero conversion, with depth 4 on both sides. At $B=8$, residual evaluation plus
conversion is 8 + 7 = 15, equal to the Boolean 15. The scaled conversion executes
at $B=2$; the captured $B=8$ scaled-bit observer refuses under the current unproved
noise envelope, while raw threshold opening succeeds only by disclosing all live
residuals. There is therefore no residual multiplication advantage to advertise,
and no general BFV noise, security, privacy, or end-to-end latency theorem.

== Higher order and the CCC question

The CCC line is now an exact frontier rather than a slogan or a no-go alone.

- The finite extensional polynomial model remains exact but dense. It gives a
  specification semantics for finite equality-HOL, not a succinct compiler for
  arbitrary higher-order programs.
- A faithful family of finite-field polynomial Yoneda actions exists exactly when
  the category is locally finite; each fixed-arrow action is linear. Even the CCC
  of finite sets admits no faithful *uniformly fixed-width* family, so local
  finiteness does not imply one bounded backend.
- The intensional route compiles typed STLC strongly-CCC to shared nets. Its local
  interaction receipts now reach live public DescriptorIR2 through direct depth
  14, with arbitrary-trace layout soundness and a proof that the erased receipt
  cannot reconstruct every exact typed endpoint.
- The indexed compiler may select dense polynomial, Boolean graph, interaction
  net, or natural residual per subterm. Its source theorem charges conversions and
  recombination in a five-axis ledger; selection is only optimal relative to the
  finite candidate list supplied.
- The global category of presentations whose meanings vary cannot be CCC: it
  is not even cartesian. After fixing the source meaning, the fibre of evidence
  families is a CCC. This is the precise fibred replacement.

Thus arbitrary small CCC semantics embed by Yoneda, locally finite CCCs additionally
admit the exact polynomial family, and represented higher-order programs have an
operational shared-net route. What is ruled out is the stronger fantasy that all of
this fits faithfully and succinctly into one uniform finite polynomial universe.

== Proof objects beyond polynomials

The realizability line now supplies more than analogy. The PCA doctrine has
arbitrary-map quantifiers and Beck--Chevalley laws; assemblies have pullbacks;
effective covers are stable under pullback, are kernel-pair coequalizers, and give
regular-image factorizations, including for compiled program certificates. These
are concrete ingredients of an exact completion, not yet the exact completion or
associated topos itself.

The query line is separate and compositional. Coverage presentations form a
category; exact presentation change preserves obstruction and miss events. A
locally accepting false statement lies in one of four explicitly priced events:
OOD, low degree or folding, commitment binding failure, or query miss. The
commit-before-query transcript theorem then prices the last event without asserting
a false deterministic total-column bridge. Under point binding and modularly
reduced queries, the sharp BabyBear-shaped bound is

#align(center)[
  $ epsilon_"OOD" + epsilon_"LDT" + ((1-delta)+delta/N)^k $
]

when $N mod m=1$. A computational commitment adds its binding budget. Additional
transcript coordinates product out of the query marginal, while OOD and folding
events may inspect the complete transcript. Category theory identifies and
transports the obstruction; coding theory makes it dense; commitments bind local
views; and the sampler prices a miss. None of the category or topos results replaces
the required hash/PCS binding, Fiat--Shamir, OOD, FRI, or verifier-correspondence
reductions.

== Executable assurance now present

- Lean emits source and optimized public descriptors and canonical traces for
  Admission, Upgrade, Clearance, and Strand. Rust pins those exact bytes, parses
  them, proves and verifies all eight cases, recomputes their ledgers, and confirms
  consumer-verifier rejection after a public-input tamper.
- The production capture retains every raw timing sample and one serialized proof
  per endpoint. Exact relation/proof-byte changes are reported; the unchanged
  Strand control prevents noisy timing differences from being sold as speedup.
- The independent reference compiler and 10,061-case conformance corpus keep
  unsound relations as visible falsification artifacts while excluding them from
  performance comparisons.
- Independent Standard ML checkers passed 15/15 v1 and 11/11 live-v2 fixtures.
  HOL4 proves accepted bytes semantically sound with zero recorded theory axioms;
  proof-producing CakeML translation certificates exist for both checkers.
- The BFV carrier executes residual evaluation, bounded scaled zero conversion,
  and n-of-n threshold opening. Its manifests record multiplication, depth,
  decryption shares, combines, comparisons, re-encryption, coverage, and leakage;
  noncanonical threshold output is refused rather than coerced to a bit.

This is already a toolchain, not a white-paper sketch. Its remaining trust
boundaries are also explicit. Production equivalence stops at the named Boolean
atom boundary. Rust implementations are not yet proved to refine the Lean models;
the CakeML certificates are not yet shipped native checker binaries. The BFV path
still lacks a general noise/security proof and a deployed cryptographic
same-opening verifier, and raw threshold observation discloses its residuals. The
query theorems still require concrete commitment, Fiat--Shamir, OOD, FRI, and
verifier-correspondence reductions. No captured timing establishes an end-to-end
prover or finality advantage.

== What may be claimed now

#callout([COMPARATIVE RESULT], [
  DREGG surpasses the reviewed public Modulus/BitLogic material in publicly
  checkable semantics, construction depth, falsification coverage, executable
  tooling, cross-language assurance, certificate discipline, and reproducibility.
  The public BitLogic relation is refuted; DREGG's corrected public relations are
  statement-bound and proved exact under stated premises. Three production-derived
  decisions show exact relation-ledger and retained proof-byte reductions, with an
  unchanged negative control. Fully priced FHE accounting reports equality rather
  than a fictitious win. DREGG does not yet establish a 10--100x end-to-end proving
  advantage, 1--3 second chain finality, or runtime superiority to an unpublished
  Modulus implementation.
])

Finality is a consensus, networking, data-availability, and validator claim; it
does not follow from replacing a circuit connective. Likewise, a symbolic
multiplication count is not a prover benchmark. A defensible performance claim
must measure the same workload through baseline AIR, repaired residual,
Boolean, and certified hybrid paths, including witness generation, proof
generation, verification, proof bytes, range checks, zero decisions, and every
conversion boundary.

== Constructive offer

#callout([TO MODULUSZK AND CULTDAO], [
  Keep the useful matrix-language insight. Replace the finite-field equations
  with one of the proved repairs. Conjoin independent obligations. Publish the
  exact source language, compiler, relation, witness generator, prover,
  verifier, parameters, corpus, raw measurements, and exclusions. Import the
  counterexamples as permanent regression tests. Then compare the repaired
  implementation against the certified residual, Boolean, shared, and hybrid
  constructions here on identical workloads.
])

#boundary([
  This report establishes a specification-level failure in the released
  BitLogic relation, not an exploit against private or deployed software. It
  also establishes positive formal and executable DREGG constructions, not a
  production security certification. Those two boundaries make the conclusion
  stronger: the criticism is reproducible, and the alternative is inspectable.
])

The research program that survives is not "logic bypasses circuits." It is:
compile judgments into the cheapest sound local presentation, attach evidence
for every translation, and let proof systems, encrypted runtimes, and future
backends compete inside one semantics-preserving envelope.
