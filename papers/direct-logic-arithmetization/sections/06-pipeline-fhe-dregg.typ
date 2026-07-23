#import "../section-helpers.typ": theorem, boundary

= From finite logic to a live proof and encrypted plan

The constructive result is now a pipeline, not merely a corrected polynomial
identity.  A finite-signature first-order sentence can be grounded into an exact
Boolean relation, compiled into the live DREGG descriptor IR, accompanied by a
canonical trace, checked against exact emitted bytes, optimized by replayable
certificates, and related to an encrypted evaluation over the same opening.
There are executable Rust, Python, Standard ML, HOL4, and CakeML artifacts at
different assurance boundaries.

#block(width: 100%, fill: rgb("dce8dd"), inset: (x: 12pt, y: 9pt), radius: 2pt)[
  #set text(font: "Avenir Next", size: 8.25pt, weight: 600)
  #align(center)[
    finite FOL
    #h(4pt)$arrow.r$#h(4pt)
    grounded Boolean relation
    #h(4pt)$arrow.r$#h(4pt)
    checked representation plan
    #h(4pt)$arrow.r$#h(4pt)
    DescriptorIR2 + proof
  ]
  #v(3pt)
  #align(center)[
    same grounded source
    #h(4pt)$arrow.r$#h(4pt)
    shared opening
    #h(4pt)$arrow.r$#h(4pt)
    BFV/hybrid plan
  ]
]

This diagram is a map of proved and executable interfaces, not one monolithic
end-to-end theorem.  In particular, a Lean compiler proof, a Rust prover test,
and a real BFV execution are three different kinds of evidence.  The named
boundaries below prevent one from being advertised as another.

== General finite FOL reaches the live descriptor IR

`FiniteSignatureFOLDescriptorIR2` is the broadest verified source compiler in
this study.  A signature contains any finite list of total public function
symbols and relation symbols of independently chosen finite arities.  Terms
contain constants, de Bruijn variables, and nested function applications.
Formulae contain equality, relation application, negation, conjunction,
disjunction, and exhaustive finite universal and existential quantification.

For a domain of size $q$, a relation of arity $a$ receives $q^a$ canonical
columns.  The complete relation layout therefore has width

#align(center)[
  $ W = sum_(r in "relations") q^(a_r). $
]

Public function tables are compiled by evaluation, while relation tables are
the model-bearing trace data.  `compileDescriptorFOL` emits exactly $W$
always-on bitness constraints and one always-on source-acceptance constraint.
Quantifiers are grounded by exhaustive enumeration, so the construction is
exact but can grow exponentially with quantifier depth.  It is not presented as
a succinct quantifier protocol.

#theorem([finite-signature live compiler], [
  `lower_correct` relates the direct finite-model semantics to the grounded
  Boolean source.  `fol_sound` proves that every row of a satisfying canonical
  live trace satisfies the original sentence.  `fol_complete` constructs a
  one-row live trace from every satisfying model, and
  `canonical_model_trace_iff` gives the exact equivalence.  The fail-closed
  `FOLLiveCertificate` binds the domain and signature, complete public function
  tables, canonical relation layout, encoded sentence, grounded source, atom
  count, and exact DescriptorIR2 JSON.  `checked_fol_sound` transports a checked
  certificate and a satisfying trace back to the source sentence.
])

The concrete nested specimen has a two-element domain, a public Boolean flip
function, one unary relation, one binary relation, and the sentence

#align(center)[
  $ forall x, exists y, R_2("flip"(x), y) and R_1("flip"("flip"(x))). $
]

Its canonical relation width is $2^1 + 2^2 = 6$ and its live descriptor has
seven constraints.  A certificate with an empty claimed layout is rejected.
This specimen exercises functions, two relation arities, nested quantifiers,
and exact live-byte binding in one kernel-checked construction.

The same target also contains a faithful fixed Gabbay matrix instance.
`GabbayDescriptorIR2` compiles a two-row, three-entry Skolem graph using
denominator-cleared Lagrange interpolation, three linear acceptance atoms, and
a 30-bit range lookup on each of the six entry columns: 12 trace columns and 15
constraints.  Its `trace_satisfied_iff_holds` theorem relates the actual live
relation to the ordinary bounded source formula; successor data is accepted,
while a tampered entry and the known unchecked modulus-five projection are
refused.  Its `WireBoundedTable` hypothesis is a completeness-side premise
naming the expressible domain; the soundness direction derives that bound from
the emitted lookups instead of assuming it.  Arbitrary matrix length remains a
separate symbolic compiler problem because it must emit and cost an
interpolation algorithm rather than hide divisions in witness data.
The fixed theorem constructs a trace from an externally named three-entry
table, but the descriptor itself proves only an existential private-witness
relation.  `GabbayDescriptorIR2PublicBoundary` proves that its public-input and
hash-site surfaces are empty, that the v1 `ranges` carrier is empty, that it
carries 15 constraints, and that all constructed tables have the same public
assignment.  Read the range conjunct exactly: an empty `ranges` field is not an
absent range check.  The no-wrap bound is carried by six graduated `lookup`
constraints against the declared 30-bit range table --- the form the deployed
assembly actually realizes, and the form it requires, since it refuses a v2
descriptor carrying the v1 carrier at all.  What the boundary theorem records is
that no surface here binds an external NAME, so acceptance cannot attest an
independently named external table.  Moreover, interpolation coefficients are
consistency columns; acceptance reads the raw input/output cells.
This specimen establishes a fixed-shape semantic relation, not an interpolation
performance result.

`GabbayDescriptorIR2PublicBinding` now closes that statement gap with a separate
direct-table descriptor.  Its six disclosed table cells are pinned to six trace
columns by six public inputs; three linear acceptance atoms and six 30-bit range
lookups bring the total to 15 constraints, and acceptance contains no nonlinear
product at all.  Under the canonical field-decoding convention alone ---
the previous no-wrap certificate is now derived rather than assumed ---
`public_statement_satisfied_iff_holds` proves that an arbitrary nonempty
satisfying trace exists exactly when the externally claimed table satisfies the
source formula.  A one-cell public tamper is refused, and the complete IR-v2 JSON
is pinned, including the `"bits":30` range table and the six lookup entries.
This construction supplies public integrity with zero table privacy.
It deliberately removes interpolation coefficients, so it closes public
binding without manufacturing an interpolation speedup.

Both Gabbay descriptors carry this shape because the previous one was proved
unsound.  Acceptance used to be the sum of the three squared successor
residuals, sound only under Lean-side premises that were never serialized, and
over BabyBear $284861408^2 = -1$ makes a fully canonical FALSE table cancel to
zero.  `DirectLogicAdversarialFalsifierV2` keeps that table and a second one ---
whose only refuting gate is a range tooth --- as armed rejection canaries in
both the preselected-trace and external-statement polarities, together with a
control proving the true statement still has a witness.  Section 3 gives the
full account, including the one premise that moved rather than vanished: a range
lookup bounds a column only against an honest range table, and `Satisfied2` has
no faithfulness conjunct for `.range`, so refusals through a range tooth carry
`HonestRangeTable` explicitly.  That premise is carrier-level and uniform across
every range lookup in the codebase, not specific to this descriptor.

== Certificates optimize the relation without changing it

The important performance mechanism is not "FOL instead of circuits."  It is
certified selection and sharing among equivalent presentations.
`DirectLogicOptimizerCertificate` is an executable translation validator for a
bounded Boolean fragment.  Each local certificate contains redundant before
and after terms plus a rule payload.  The checker reconstructs both endpoints,
checks the rule guard, checks every transitive boundary, and rejects tampered
endpoints or disconnected certificate chains.

Accepted certificates preserve three meanings at once:

- source truth under every atom interpretation;
- the exact field `BoolGraph.Accepts` relation; and
- nonincrease of equations, multiplications, witnesses, and maximum degree.

The deterministic optimizer performs constant elimination, double-negation
elimination, idempotence, Boolean factoring, and explicit fanout sharing.
`DirectLogicBoolGraphDescriptorIR2` now materializes its nodes as actual live
IR-v2 columns and degree-at-most-two `windowGate`s.  Because an accepting
descriptor also needs a linear output-equals-one gate, its constraint count is
one larger than the graph-equation count.  `factor_emitted_exact` proves:

#block(breakable: false)[
  #set text(size: 8.25pt)
  #table(
    columns: (2.0fr, 0.9fr, 0.9fr),
    inset: 4pt,
    align: left,
    table.header([*Live metric*], [*Duplicated*], [*Checked factored*]),
    [Graph equations], [30], [13],
    [Internal accepting constraints], [31], [14],
    [Public accepting constraints], [35], [18],
    [Public inputs], [4], [4],
    [Nonlinear multiplications], [26], [13],
    [Auxiliary witness columns], [17], [8],
    [Trace width at four inputs], [21], [12],
    [Maximum constraint degree], [$<= 2$], [$<= 2$],
  )
]

The 35-to-18 row is the standalone statement-bound form: four linear
public-input pins are added to the 31-to-14 internal relation without adding a
nonlinear product or auxiliary column.  `public_factor_emitted_exact` proves
the count, four-public-input layout, 21-to-12 width, and 17-to-8 auxiliary
ledger.  These are exact structural reductions in a live descriptor, not
merely a cost model.  They are also stronger than an optimizer's assertion:
`optimize_checked`, `optimize_holds_iff`, `optimize_accepts_iff`, and
`optimize_cost_nonincrease` independently expose the certificate, semantics,
field relation, and cost proof.  The live `checkLive` then reconstructs both
optimizer endpoints, the complete layout ledger, and exact emitted JSON;
tampered layout counts, bytes, or endpoints are rejected.
`canonical_trace_satisfied_iff` gives exact canonical source semantics for the
actual descriptor, and `checked_source_canonical_iff` transports an accepted
live certificate all the way back to its unoptimized source.  The production
DREGG capture below now measures proof bytes for four source/optimized pairs,
but its noisy timing distributions still do not support a wall-clock ratio.

The standalone reference tool adds per-subformula representation search.
`tools/direct-logic-reference` keeps a Pareto frontier of positive no-wrap
residual and exact Boolean candidates and records every residual-to-Boolean or
Boolean-to-residual boundary.  Its independently rechecked mixed specimen has
the lexicographic objective

#block(breakable: false)[
  #set text(size: 8.35pt)
  #table(
    columns: (1.35fr, 0.86fr, 0.86fr, 0.83fr, 0.78fr, 0.95fr),
    inset: 4pt,
    align: left,
    table.header([*Plan*], [*Mults*], [*Equations*], [*Witnesses*], [*Conversions*], [*Nodes*]),
    [Selected hybrid], [5], [9], [6], [1], [5],
    [All Boolean], [9], [11], [6], [0], [4],
    [All no-wrap], [unsupported], [-], [-], [-], [-],
  )
]

The all-no-wrap plan is refused because the single-field bound cannot certify
it.  The hybrid artifact is canonical JSON with SHA-256
`540ad40d3c282b1294db7b62ab9ad80cf287486014aba9b054369b3a79fcdef3`;
the ordinary compiler artifact remains pinned independently at
`e1d19701afcbc58adf5c624dcf33ca323375a9f858e167c0d5f258c03a11f0cd`.
`check` verifies the hash, recompiles from the embedded source, reconstructs
the chosen plan and baselines, checks every primitive equation and bound, and
then compares admitted plans with source semantics.  The Python program is an
executable specification and witness-plan checker, not a proof system.

== One opening, proof and FHE

`ProofFheSharedOpening` closes a semantic triangle that the earlier report only
proposed.  A typed Boolean source carries its atom bound; one `Opening n`
contains the raw integer word for every atom.  Admission is integer-exact:
every word must be literally zero or one, not merely congruent to a bit modulo
a field.

The proof side reads the raw opening as a one-row DescriptorIR2 trace.  The FHE
side reads the Boolean decoding of that same opening.  For every commutative
ring, `descriptorDenotation_eq_fheRing` proves equality between the descriptor
source polynomial and the structurally lowered BFV Boolean program.
`proofAccepts_iff_fheOutput_one` then proves predicate-level agreement in
BabyBear, while `noncanonical_rejected` proves that an opening containing a
non-bit is rejected by both interfaces.

`ProofFheDualCertificate` makes the bridge fail closed.  Its versioned bundle
binds the source, opening schema, exact DescriptorIR2 JSON, exact BFV program,
the BFV eight-axis operation ledger, and a length-framed canonical wire image.
An accepted bundle guarantees backend denotation agreement for every canonical
opening of the declared arity, not only the opening carried by the bundle.
Unknown versions, trailing words, noncanonical openings, descriptor
substitution, and BFV substitution are all explicit rejection theorems.

#boundary([
  The dual wire image is currently a mathematical `List Int`, not a proved Rust
  byte decoder.  Ciphertext serialization, key ownership, leakage policy,
  threshold decryption, Rust-to-Lean refinement, and cryptographic security are
  outside these semantic theorems.  The theorem says that both backends compute
  the same predicate on one admitted opening; it does not say that a deployed
  client supplied that opening correctly.
])

=== Certified mixed FHE plan

`CertifiedHybridProofFhe` goes beyond two identical Boolean lowerings.  Its
source consists of equality atoms over one raw opening.  A conversion witness
derives the exact equality-bit opening consumed by DescriptorIR2.  The encrypted
side may select, independently at each region, either a locally bounded
zero-means-true residual or a one-means-true Boolean program.  Every conversion
between those conventions is present in the plan and its cost.

`Certificate.proof_iff_fhe_plan` proves that the live proof relation and mixed
encrypted plan accept the same source predicate for every canonical raw
opening.  The concrete five-equality specimen deliberately makes the root
residual inadmissible while leaving a four-equality subregion admissible.  The
body-only ledger initially appears smaller, but the formerly omitted exact
zero observation removes that advantage:

#block(breakable: false)[
  #set text(size: 8.15pt)
  #table(
    columns: (1.55fr, 0.82fr, 0.82fr, 0.78fr, 0.74fr, 1.4fr),
    inset: 3.6pt,
    align: left,
    table.header(
      [*Plan*], [*Body mults*], [*Zero mults*], [*Total*], [*Depth*], [*Observation*]
    ),
    [Certified mixed, $B=4$], [6], [3], [9], [4], [scaled zero bit, then opening],
    [All Boolean], [9], [0], [9], [4], [Boolean output opening],
  )
]

`CertifiedHybridProofFheZeroObservation` proves why this cost is unavoidable.
Across the whole plaintext field, an exact arithmetic zero indicator has degree
at least $p-1 = 1,032,192$ and any addition/subtraction/multiplication expression
for it has multiplicative depth at least 20.  The no-wrap certificate enables a
smaller exact observer on $0..B$: the balanced product
$product_(i=1)^B (i-r)$ is $B!$ at zero and zero elsewhere, using $B-1$
ciphertext multiplications.  For $B=4$, those three multiplications change
6-versus-9 into 9-equals-9 and restore the all-Boolean depth-four envelope.
The result is a scaled two-valued ciphertext, not a free canonical Boolean.

#boundary([
  Three cost scopes remain separate.  The graph reduction is a proved live IR
  transformation; the production capture gives exact resource and proof-byte
  changes but no timing ratio.  The theorem-side presentation search still uses
  meta-level `HybridEvidence` glue.  The BFV carrier now implements bounded
  scaled zero conversion and threshold observation, but its receipts explicitly
  exclude setup, input encryption, external same-opening verification, and a
  general multiplied-ciphertext noise theorem.  Consequently none of these
  ledgers is an end-to-end latency claim.
])

== Executable backends

=== Rust finite-logic front end and live proof roundtrip

`circuit/src/direct_logic_frontend.rs` is an executable Rust compiler for
finite Boolean and enumeration inputs, equality, explicit finite predicate
tables, all Boolean connectives, and bounded quantifiers.  Enumeration values
use exact one-hot encodings; quantifiers are deterministically unrolled.
Explicit limits reject an empty or unbounded domain, oversized predicate table,
excessive quantifier expansion, unsupported source, and out-of-range input
rather than silently changing the relation.

The compiler emits the deployed `EffectVmDescriptor2` structure and canonical
JSON, reparses and structurally checks that JSON, and pins BLAKE3 digests of the
source and descriptor.  The focused suite contains nine tests covering source
evaluation, descriptor equivalence, one-hot rejection, resource refusal, hash
stability, and malformed inputs.  Most importantly,
`honest_compilation_proves_and_verifies_through_live_backend` sends a compiled
one-row trace through the actual `prove_vm_descriptor2` and
`verify_vm_descriptor2` APIs; the same prover refuses a row that falsifies the
source formula.

This is the first live Rust prove/verify path for the construction.  It is not
yet a proof that the Rust compiler refines the Lean compiler, and one tiny
roundtrip says nothing about production throughput or finality.

A separate translation-validation gate consumes the exact byte images emitted
and pinned by Lean for the public Gabbay table and public optimized BoolGraph.
The production Rust parser/prover suite passed 10/10 tests, including live proof
roundtrips and exact binary pins.  An independent Python parser/evaluator then
checked all 8,000 small Gabbay tables and all 16 assignments to the four-input
BoolGraph.  These tests are strong cross-language agreement on committed
specimens.  They are translation validation, not a theorem that either
executable implementation refines Lean.

The path now also has an absolute release benchmark.  It measures
`LogicProgram` to `compile_logic_program` to `EffectVmDescriptor2` to one-row
trace to `prove_vm_descriptor2` and `verify_vm_descriptor2`.  The capture used an
Apple M2 Max with 12 logical CPUs and 96 GiB RAM, five warmups, 30 proving
samples, and 100 verification samples.  The live BatchSTARK parameters were
BabyBear, extension degree 4, FRI log blowup 6, 19 queries, and 16 query-PoW
bits.  All proofs had `degree_bits = 0`; proof sizes are the live SDK's postcard
encoding.

#block(breakable: false)[
  #set text(size: 7.55pt)
  #table(
    columns: (1.35fr, 0.72fr, 1.05fr, 1.08fr, 0.82fr),
    inset: 3.3pt,
    align: left,
    table.header([*Workload*], [*Cols / gates*], [*Prove median / p95*], [*Verify median / p95*], [*Proof bytes*]),
    [`bool-eq`], [1 / 2], [2.219 / 4.572 ms], [0.282 / 0.789 ms], [9,262],
    [`enum-eq-4`], [4 / 6], [6.911 / 9.829 ms], [0.293 / 0.691 ms], [9,342],
    [`enum-eq-16`], [16 / 18], [4.497 / 7.140 ms], [0.309 / 0.686 ms], [9,721],
    [`enum-eq-64`], [64 / 66], [6.728 / 8.596 ms], [0.500 / 0.862 ms], [10,924],
    [`forall-4`], [4 / 6], [19.637 / 23.838 ms], [0.361 / 0.794 ms], [10,202],
    [`forall-8`], [8 / 10], [8.828 / 10.630 ms], [0.488 / 1.086 ms], [11,165],
    [`forall-16`], [16 / 18], [26.833 / 31.437 ms], [0.800 / 1.695 ms], [13,101],
  )
]

The proving medians are visibly nonmonotone.  The shared development host had
load averages 31.34 / 37.81 / 38.25, so the result supplies neither a scaling
law nor a speedup comparison.  Release proving excludes debug self-verification;
the harness separately verified every warmup and retained proof.  It does not
measure the abstract optimizer, a conventional-circuit or Modulus baseline,
zero knowledge, network inclusion, or finality.

#block(breakable: false)[
  #set text(size: 8.15pt)
  Stable capture: `docs/deos/artifacts/direct-logic-live-2026-07-22-m2-max`.
  Summary SHA-256:
  `39a623da8ea21a03e69a6f420d5b49ce52762a9e4cbb9fefbdb21e7ae661db73`.
  Raw-log SHA-256:
  `66b37bf19bfffe505b967b03fdf44a0cc8bde22ca232493417fe3350b9ef3b1e`.
]

=== Four production DREGG decision skeletons

The optimizer was also driven from four Boolean decision skeletons named and
consumed by DREGG: fail-closed turn admission, anti-brick upgrade authorization,
structured credential clearance, and stake/vouch/bond strand admission.  Lean
proved each source/optimized Boolean equivalence, emitted both public
descriptors and canonical rows, and the Rust harness pinned, parsed, proved,
and verified those exact bytes.

#block(breakable: false)[
  #set text(size: 7.25pt)
  #table(
    columns: (1.12fr, 0.82fr, 0.92fr, 0.82fr, 0.82fr, 1.12fr),
    inset: 3pt,
    align: left,
    table.header([*Decision*], [*Width*], [*Constraints*], [*Nonlinear*], [*Aux*], [*Proof bytes*]),
    [Admission], [77 to 47], [121 to 71], [108 to 58], [65 to 35], [14,016 to 11,894],
    [Upgrade], [21 to 15], [33 to 23], [28 to 18], [17 to 11], [10,431 to 10,081],
    [Clearance], [21 to 15], [33 to 23], [28 to 18], [17 to 11], [10,469 to 10,157],
    [Strand control], [11 to 11], [17 to 17], [13 to 13], [8 to 8], [9,850 to 9,850],
  )
]

The relation ledgers are deterministic.  The retained proof encodings shrink
by 2,122 bytes for Admission, 350 for Upgrade, 312 for Clearance, and zero for
the already-normal Strand control.  The run retained 25 proving and 75
verification samples per variant after five warmups, but load averages were
33.61 / 26.37 / 24.91 and the distributions were wide and nonmonotone.  Most
decisively, the byte-identical Strand pair acquired different timing medians.
The capture therefore claims no timing speedup.

Every descriptor binds atom residuals to public inputs.  The harness changed
public input zero while retaining the Lean-authored row.  In release mode the
producer omits debug self-verification and may return an invalid proof; the
consumer verifier rejected all eight such proofs.  Producer success is not an
acceptance decision.  The consumer verifier is the recorded soundness boundary.

#block(breakable: false)[
  #set text(size: 8.1pt)
  Stable capture:
  `docs/deos/artifacts/direct-logic-dregg-workloads-2026-07-22-m2-max`.
  The directory includes exact ledgers, all raw samples, metadata, and a
  SHA-256 manifest.
]

=== Independent HOL4 and CakeML checker boundary

`tools/direct-logic-cakeml` reimplements the certificate check independently of
Lean.  The version-1 Standard ML checker passed 15/15 golden and malformed
fixtures.  In HOL4, `check_bytes_sound` proves that accepted bytes decode under
the known version to the canonical source/target pair and that their Boolean
semantics agree for every environment.  The theory has zero axioms in the
recorded fresh audit, and `check_bytes_v_thm` is the proof-producing CakeML
translation certificate.

The live version-2 checker embeds the complete length-delimited v1 certificate,
a 32-bit atom bound, and exact canonical IR-v2 JSON.  It reconstructs the
Booleanity gates, acceptance polynomial, table and layout, then compares exact
bytes.  It caps the atom count at 256 and each section at one MiB.  The live SML
suite passed 11/11 fixtures, including exact agreement with Lean's pinned demo
JSON and rejection of version, bound, embedded-target, JSON, trailing, and
truncation tampering.  HOL4's `check_live_bytes_sound` establishes the embedded
v1 check, atom bound, exact descriptor bytes, and source/target semantic
equivalence; `check_live_bytes_v_thm` translates the live checker to CakeML.

#boundary([
  The checked and translated source is not yet counted here as a native verified
  checker binary.  A machine-code claim requires the completed CakeML backend
  compilation plus a fresh theorem-tag and axiom audit of the live theories.
  The live checker byte-compares reconstructed JSON; it does not independently
  parse arbitrary descriptor JSON or prove the DREGG Rust verifier equivalent to
  the HOL relation.
])

=== Real BFV execution

`FheLogicBfvModel` proves the Boolean-ring identities and a no-wrap theorem for
the nonnegative squared-equality residual

#align(center)[
  $ R = sum_i (x_i-y_i)^2. $
]

Under the declared input bounds and centered plaintext window, field zero is
equivalent to all source equalities.  For eight encrypted equalities, the
residual interpreter has 8 multiplications, 8 relinearizations, and symbolic
depth 1.  The balanced all-Boolean interpreter has 15 multiplications, 15
relinearizations, and depth 4.  Those body ledgers do not yet include observing
whether the encrypted residual is zero.

The matching `fhegg-fhe` path executes real BFV ciphertexts.  One recorded warm
release run on `persvati` (x86-64 Linux, AMD Ryzen AI 9 HX PRO 370), at ring
degree 4096 and plaintext modulus 1,032,193, produced:

#block(breakable: false)[
  #set text(size: 8.25pt)
  #table(
    columns: (1.78fr, 0.75fr, 0.88fr, 0.72fr, 0.72fr),
    inset: 4pt,
    align: left,
    table.header([*Executed workload*], [*SIMD cases*], [*BFV body*], [*Mul/relin*], [*Noise*]),
    [Boolean policy], [16], [22.950435 ms], [3 / 3], [79 bits],
    [Eight-equality residual], [4], [48.197263 ms], [8 / 8], [49 bits],
  )
]

The residual certificate checked $648 < 516096$.  These rows are different
programs with different SIMD occupancy, so their times do not define a speedup.
They are single warm observations.  The timed body excludes key generation,
encryption, decryption, and zero observation; the observed noise is not a
proved noise or security bound.  The focused release suite passed 3/3 tests,
including refusal of a cancellation-capable bound.

`fhegg-fhe` now executes the missing boundary rather than leaving it as an
unpriced counter.  The two-equality, $B=2$ oracle successfully evaluated the
scaled encrypted observer and decrypted the expected values $[2,0,2,0]$.
At $B=8$, the residual body uses eight ciphertext multiplications and the
bounded observer adds seven, so the total is 15 at depth four - exactly the
balanced Boolean ledger, not an 8-versus-15 win.  The encrypted conversion ran,
but n-of-n observation of its scaled output refused because the threshold
combine produced a value outside the canonical set $\{0,8!\}$.  The API turns
the unproved multiplied-ciphertext noise margin into a refusal rather than a
wrong truth bit.

The alternate $B=8$ boundary threshold-opens the raw residual successfully.
For four live SIMD slots it revealed $[0,1,0,2]$, from which the coordinator
computed $["true","false","true","false"]$.  Two smudged decryption-share
messages occupied 419,988 bytes and the threshold observation took roughly
165 ms in the retained run.  This path is exact but intentionally leaky: it
reveals the whole residual, not merely its zero bit.

#boundary([
  Neither observation is an end-to-end comparison.  Setup and input encryption
  were measured outside the receipt; the same-opening field is a test-only
  transparent-construction receipt rather than an executed zero-knowledge
  verifier; and the existing smudging theorem does not prove correctness for
  the multiplied-ciphertext noise envelope.  Internal residual-to-bit
  continuation is priced as an opening plus re-encryption and refused because
  no hybrid continuation machine is implemented.  The honest conclusion is a
  three-way choice: pay the bounded polynomial cost, open and leak the raw
  residual, or introduce a different private comparison carrier.
])

== Conformance before performance

`tools/direct-logic-bench` compares five relations against a common Boolean
reference.  A lane that fails semantics remains visible as a falsification
artifact but is excluded from every performance ratio.  The deterministic
corpus contains the pinned adversarial and transaction examples plus 10,000
generated formulae, for 10,061 cases in total:

#block(breakable: false)[
  #set text(size: 8.25pt)
  #table(
    columns: (1.35fr, 0.72fr, 0.86fr, 0.9fr, 0.82fr),
    inset: 4pt,
    align: left,
    table.header([*Lane*], [*Gate*], [*Supported*], [*Unsupported*], [*Mismatch*]),
    [`M-SPEC`], [fail], [10,061], [0], [3,936],
    [`G-FIELD-NAIVE`], [fail], [6,748], [3,313], [1],
    [`D-NOWRAP`], [pass], [6,737], [3,324], [0],
    [`D-BOOLGRAPH`], [pass], [10,061], [0], [0],
    [`C-AIR`], [pass], [10,061], [0], [0],
  )
]

`M-SPEC` is an exact transcription of the public BitLogic connective,
quantifier, and swap equations.  `G-FIELD-NAIVE` separately tests the
Gabbay-style positive residual after unsafe field reduction.  `D-NOWRAP` is
the corrected bounded positive route; unsupported means that its required
partial-accumulator bound was not established.  `D-BOOLGRAPH` is the exact
inverse-witness Boolean graph.  `C-AIR` is an independently written
gate-by-gate arithmetic baseline.

The harness emits environment and source hashes, every workload and gate
result, a representation-labelled symbolic ledger, raw timing samples,
bootstrap intervals, checksums, and an admitted-only summary.  Its timing
channel measures Python relation evaluation.  It does not measure witness
generation, proving, verification, proof bytes, FHE, consensus, data
availability, finality, or monetary cost.  In particular, an unsound equation
does not become an optimization because it evaluates quickly.

== What would test the claimed performance numbers

The verified constructions justify an end-to-end benchmark campaign; they do
not pre-decide its outcome.  A credible 10-100x claim requires every candidate
to prove the same source predicate, at the same security target, on the same
hardware, while including every conversion and boundary operation.  The first
matrix should contain these pipelines:

#block(breakable: false)[
  #set text(size: 8.1pt)
  #table(
    columns: (0.9fr, 1.55fr, 1.78fr),
    inset: 4pt,
    align: left,
    table.header([*Lane*], [*Construction*], [*Admission rule*]),
    [`C-AIR`], [ordinary gate-by-gate arithmetic circuit/AIR], [independent source conformance],
    [`D-NOWRAP`], [positive residual with certified partial bounds], [all no-wrap obligations discharge],
    [`D-BOOLGRAPH`], [live materialized bits and inverse-witness zero tests], [checked source, layout, and exact bytes],
    [`D-HYBRID`], [certificate-selected residual/Boolean/shared DAG], [certificate replay plus source equivalence],
    [`M-IMPL`], [public Modulus compiler/prover, if supplied], [source, parameters, build, and raw artifacts available],
  )
]

The workload matrix should cross Boolean policy logic, equality-heavy batches,
mixed negation and disjunction, nested finite quantifiers at several domain
sizes, multi-arity signatures with public functions, shared-subterm fanout,
the duplicated/factored live BoolGraph pair, the fixed Gabbay matrix instance,
and the published swap relation.  Both true and false instances are required;
a prover must refuse the latter.

For every lane and size, the preserved run artifact must report:

- exact source, grounded relation, compiler/certificate hashes, field and
  security parameters;
- equations, multiplications, degree, witnesses, rows, columns, lookup/table
  cells, and every range or zero-test gadget;
- source compilation, witness generation, proving and verification time with
  warmup, sample count, distribution, and peak memory;
- proof bytes, public-input bytes, preprocessing material, and verifier work;
- for FHE, encryption, evaluation, conversion/bootstrapping, threshold or
  private zero decision, decryption, ciphertext bytes, occupancy, depth, and
  measured remaining noise;
- machine, operating system, compiler revisions, build flags, thread count,
  accelerator residency, and raw samples.

Only the complete wall-clock and resource columns can support an end-to-end
cost ratio.  The 30-to-13 graph-equation, 31-to-14 internal and 35-to-18 public
accepting-constraint, 26-to-13 multiplication, and 21-to-12 width results are
verified live structural reductions.  The four DREGG captures add exact
source/optimized relation ledgers and retained proof-byte reductions.  They do
not add a timing ratio.  On the FHE side, including exact bounded zero
observation has already erased both advertised body-only advantages on the
measured specimens: 6 plus 3 equals Boolean 9, and 8 plus 7 equals Boolean 15.
Future experiments should search for regimes where sharing, packing, a private
comparison carrier, or a different representation improves the complete
pipeline rather than reusing the superseded body-only comparison.

The 1-3 second finality claim requires a different matrix.  At minimum it must
state the consensus and fault model, validator count and geography, block and
proof size, data-availability path, network delay and loss model, batching and
sequencing policy, hardware, confirmation rule, and latency distribution under
load and faults.  Logic arithmetization can change proving cost, but finality is
also a consensus, networking, execution, and data-availability property.

== Arithmetization is not chain portability

Mapping a finite logical relation into polynomials answers only the relation
encoding question.  A portable application additionally needs a correct
compiler, a sound proof system, a stable recursive statement ABI, verifiers on
each target, foreign-finality or inclusion evidence, action and asset binding,
data availability, and an atomicity protocol.  None follows from calling FOL
"direct."

DREGG has separate evidence in this larger stack: a whole-history fold, local
EVM, Solana, and Cosmos verifier demonstrations, and a generic data-availability
interface.  Outbound message roots currently fail closed.  Foreign light-client
folding, Celestia integration, and multi-chain atomicity remain open or
conditional.  These facts make the architecture inspectable; they do not
justify a universal-portability or live-production claim.

== Constructive public comparison

As inspected on 22 July 2026, the public
#link("https://github.com/ModulusZK/BitLogic-from-Modulus-zkFOL-Bitcoin")[BitLogic
repository] contains its whitepaper PDF but no compiler, witness generator,
prover, verifier, release, benchmark driver, parameter manifest, or raw result
bundle.  The #link("https://www.moduluszk.io/")[project site] advertises 10-100x
cost reduction and 1-3 second finality.  No public adapter exists that can run
those claims through the matrix above.  The counterexample in this report is
therefore an attack on a published relation, not on unavailable private code or
a deployed chain.

#block(breakable: false)[
  #set text(size: 7.25pt)
  #table(
    columns: (0.92fr, 1.45fr, 2.0fr),
    inset: 3pt,
    align: left,
    table.header(repeat: true, [*Axis*], [*Reviewed public Modulus evidence*], [*DREGG artifact in this study*]),
    [Source semantics],
    [Printed equations; the published swap product admits the proved bypass.],
    [Kernel-checked corrected FOL, finite-signature semantics, and exact public-table binding.],
    [Compiler],
    [No public compiler implementation found.],
    [Lean FOL-to-IR, six-PI direct-table, and four-PI BoolGraph compilers; executable Rust and Python tools.],
    [Optimization],
    [No public derivation or cost certificate found.],
    [Replayable rewrites, live graph lowering, exact layout/byte guards, checked hybrid search.],
    [Proof path],
    [Architecture prose names zkEVM, STARK, and SNARK components.],
    [Live IR-v2 descriptors, four DREGG decision captures, consumer tamper refusal, explicit FRI assumptions.],
    [Independent checker],
    [No public checker source found.],
    [SML/HOL4/CakeML boundary plus Rust/Python exact-byte translation validation.],
    [Encrypted logic],
    [No public FHE logic compiler found.],
    [Same-opening theorem, real BFV bounded zero conversion, threshold observation, and fail-closed noise refusal.],
    [Performance],
    [Headline ratios without a reviewed reproducibility bundle.],
    [Verified structural savings and proof-byte reductions; FHE body wins erased at observation; no timing winner.],
  )
]

#theorem([the public lead], [
  DREGG's present advantage is auditable semantics and compositional evidence:
  source, countermodels, repair theorems, compilers, certificates, fixtures,
  and boundary assumptions can all be inspected.  It is not yet an established
  advantage in prover latency, proof size, monetary cost, or chain finality.
])
