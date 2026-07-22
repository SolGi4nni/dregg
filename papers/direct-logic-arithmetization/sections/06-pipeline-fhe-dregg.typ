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
denominator-cleared Lagrange interpolation, squared logical residuals, an exact
aggregate numerator, and a BabyBear no-wrap certificate.  Its
`trace_satisfied_iff_holds` theorem relates the actual live relation to the
ordinary bounded source formula; successor data is accepted, while a tampered
entry and the known unchecked modulus-five projection are refused.  Arbitrary
matrix length remains a separate symbolic compiler problem because it must emit
and cost an interpolation algorithm rather than hide divisions in witness data.
The fixed theorem constructs a trace from an externally named three-entry
table, but the descriptor itself proves only an existential private-witness
relation.  `GabbayDescriptorIR2PublicBoundary` proves that its public-input,
hash-site, and range surfaces are all empty and that all constructed tables have
the same public assignment.  It therefore cannot attest an independently named
external table.  Moreover, interpolation coefficients are consistency columns;
the logical residual and final acceptance read the raw input/output cells.
This specimen establishes a fixed-shape semantic relation, not an interpolation
performance result.

`GabbayDescriptorIR2PublicBinding` now closes that statement gap with a separate
direct-table descriptor.  Its six disclosed table cells are pinned to six trace
columns by six public inputs; one acceptance gate gives seven constraints in
total and contains exactly three nonlinear products.  Under canonical field
decoding and the explicit no-wrap certificate,
`public_statement_satisfied_iff_holds` proves that an arbitrary nonempty
satisfying trace exists exactly when the externally claimed table satisfies the
source formula.  A one-cell public tamper is refused, and the complete IR-v2 JSON
is pinned.  This construction supplies public integrity with zero table privacy.
It deliberately removes interpolation coefficients, so it closes public
binding without manufacturing an interpolation speedup.

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
elimination, idempotence, Boolean factoring, and explicit fanout sharing.  The
factoring specimen has the following exact kernel-checked ledger:

#block(breakable: false)[
  #set text(size: 8.4pt)
  #table(
    columns: (1.55fr, 0.78fr, 0.78fr, 0.82fr, 0.68fr),
    inset: 4pt,
    align: left,
    table.header([*Representation*], [*Equations*], [*Mults*], [*Witnesses*], [*Degree*]),
    [Duplicated Boolean graph], [30], [26], [17], [2],
    [Checked factored graph], [13], [13], [8], [2],
    [Reduction], [56.7%], [50.0%], [52.9%], [none],
  )
]

Those percentages are exact symbolic reductions for one specimen, not prover
latency ratios.  They are nevertheless stronger than an optimizer's assertion:
`optimize_checked`, `optimize_holds_iff`, `optimize_accepts_iff`, and
`optimize_cost_nonincrease` independently expose the certificate, semantics,
field relation, and cost proof.  This is an abstract materialized `BoolGraph`
ledger, not the current live DescriptorIR2 layout, so it proves no present live
prover saving.

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
residual inadmissible while leaving a four-equality subregion admissible:

#block(breakable: false)[
  #set text(size: 8.15pt)
  #table(
    columns: (1.45fr, 0.65fr, 0.65fr, 0.67fr, 0.68fr, 0.7fr, 0.7fr),
    inset: 3.6pt,
    align: left,
    table.header(
      [*Plan*], [*Adds*], [*Subs*], [*Mults*], [*Relins*], [*Depth*], [*Zero boundary*]
    ),
    [Certified mixed], [5], [6], [6], [6], [2], [1],
    [All Boolean], [10], [10], [9], [9], [4], [0],
  )
]

Thus the mixed plan uses one third fewer ciphertext multiplications and half the
symbolic multiplicative depth on this specimen.  It also owes one private
residual-zero boundary.  Omitting that last column would make the comparison
misleading.

#boundary([
  Three cost scopes must remain separate.  The 30-to-13 optimizer result counts
  an abstract materialized `BoolGraph`, not current live DescriptorIR2.  The
  theorem-side presentation search uses meta-level `HybridEvidence` glue, so a
  zero search score omits backend recombination and conversion.  Finally,
  `boundaryZeroDecision` is a semantic counter: the 6-versus-9 hybrid ledger
  neither implements nor prices an encrypted residual-to-bit BFV zero test.
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
relinearizations, and depth 4.  The residual row excludes the required final
private zero decision.

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
encryption, decryption, and the residual plan's final private zero decision;
the observed noise is not a proved noise or security bound.  The focused
release suite passed 3/3 tests, including refusal of a cancellation-capable
bound.

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
    [`D-BOOLGRAPH`], [canonical bits and inverse-witness zero tests], [bitness and source equivalence],
    [`D-HYBRID`], [certificate-selected residual/Boolean/shared DAG], [certificate replay plus source equivalence],
    [`M-IMPL`], [public Modulus compiler/prover, if supplied], [source, parameters, build, and raw artifacts available],
  )
]

The workload matrix should cross Boolean policy logic, equality-heavy batches,
mixed negation and disjunction, nested finite quantifiers at several domain
sizes, multi-arity signatures with public functions, shared-subterm fanout,
the fixed Gabbay matrix instance, and the published swap relation.  Both true
and false instances are required; a prover must refuse the latter.

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
cost ratio.  The 30-to-13 equation result, 26-to-13 multiplication result,
eight-versus-fifteen BFV ledger, and 6-versus-9 hybrid FHE ledger are hypotheses
for that experiment, not substitutes for it.

The 1-3 second finality claim requires a different matrix.  At minimum it must
state the consensus and fault model, validator count and geography, block and
proof size, data-availability path, network delay and loss model, batching and
sequencing policy, hardware, confirmation rule, and latency distribution under
load and faults.  Logic arithmetization can change proving cost, but finality is
also a consensus, networking, execution, and data-availability property.

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
    [Lean FOL-to-IR and six-PI direct-table compilers, executable Rust front end, Python reference compiler.],
    [Optimization],
    [No public derivation or cost certificate found.],
    [Replayable Lean rewrite certificates and independently checked hybrid search artifact.],
    [Proof path],
    [Architecture prose names zkEVM, STARK, and SNARK components.],
    [Live IR-v2 descriptors, absolute Rust proof capture, explicit FRI/deployment assumptions.],
    [Independent checker],
    [No public checker source found.],
    [Independent SML checker, HOL4 soundness, proof-producing CakeML translation.],
    [Encrypted logic],
    [No public FHE logic compiler found.],
    [Same-opening proof/FHE theorem, certified mixed plan, real BFV execution.],
    [Performance],
    [Headline ratios without a reviewed reproducibility bundle.],
    [Exact symbolic savings and scoped measurements; no end-to-end winner claimed.],
  )
]

#theorem([the public lead], [
  DREGG's present advantage is auditable semantics and compositional evidence:
  source, countermodels, repair theorems, compilers, certificates, fixtures,
  and boundary assumptions can all be inspected.  It is not yet an established
  advantage in prover latency, proof size, monetary cost, or chain finality.
])
