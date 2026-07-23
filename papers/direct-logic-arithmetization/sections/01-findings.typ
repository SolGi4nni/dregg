#import "../section-helpers.typ": callout, theorem, boundary

= What was built, what failed, what got smaller

Direct logic arithmetization is salvageable, generalizable, and useful. The
reviewed public BitLogic presentation is not a sound instance of it. This
report does more than separate those statements: it supplies the missing
constructions.

#callout([RESULT], [
  We reconstructed Gabbay's matrix-language compiler, proved its characteristic-
  zero semantics, added two exact finite-field repairs, and constructed a
  fixed-shape private-witness matrix relation in DREGG's live DescriptorIR2. We
  then closed its external-statement boundary with a six-input public direct-table
  relation and built a general finite-signature FOL compiler, public statement-
  bound optimized descriptors for four production DREGG decisions, a fully priced
  proof/FHE boundary, a per-subterm certified presentation compiler, a strong-CCC
  shared-net compiler with a live interaction receipt, and categorical query and
  realizability coverage theorems. The public BitLogic equations still fail the
  permanent counterexample suite. The positive stack now reaches formal source,
  emitted descriptor bytes, live proofs, encrypted execution, and independent
  cross-language checking.
])

The audit also turned on our own construction. The first acceptance shape of the
public direct-table relation --- a field sum of squared residuals, made sound by
a Lean-side no-wrap premise that no emitted byte checked --- was proved to accept
a fully canonical false table, by exactly the class of cancellation this report
uses against BitLogic. It was replaced with three linear atoms and six emitted
30-bit range lookups; the two premises that had made it sound are now derived
theorems rather than assumptions; and both counterexamples are retained as armed
rejection canaries built by CI. Section 3 gives the account, the load-bearing
proof for each half of the repair, and the one premise that moved rather than
vanished.

== The construction stack

#block(breakable: false)[
  #set text(size: 8.05pt)
  #table(
    columns: (0.9fr, 2.15fr, 2.05fr),
    inset: 4.2pt,
    align: left,
    table.header(repeat: true, [*Layer*], [*Verified construction*], [*Exact boundary*]),
    [Gabbay front end],
    [Integer matrices, one-based Lagrange row interpolation, terms, bounded
     quantifiers, source semantics, rational residual compiler, projection
     certificate, and Boolean repair.],
    [`GabbayMatrixCompiler` and `GabbayMatrixBridge`; positive one-index matrix
     fragment, not arbitrary recursion.],
    [Live matrix relation],
    [The original three-entry instance is a private existential witness with no
     public binding. A separate direct-table descriptor binds all six claimed
     cells and accepts exactly when the public table satisfies source `Holds`.
     Its first acceptance shape was proved to accept a canonical false table and
     was replaced; the counterexamples are retained as armed rejection canaries.],
    [`GabbayDescriptorIR2PublicBinding`: 6 public inputs, 6 columns, 15
     constraints (6 PI pins, 3 linear atoms, 6 emitted 30-bit range lookups), 0
     nonlinear products, exact tamper refusal, and zero table privacy. It is not
     interpolation-performance evidence.],
    [Finite FOL],
    [Closed de Bruijn syntax with equality, many relations of independent
     arities, total public function tables, every connective, and exhaustive
     finite quantification. Four public Boolean skeletons are proved equivalent
     to DREGG Admission, Upgrade, Clearance, and Strand decisions.],
    [`FiniteSignatureFOLDescriptorIR2` and `DirectLogicDreggWorkloads`; exact
     layouts, statement soundness, live relations, certificates, and bytes.
     Interior arithmetic, hash, membership, lifecycle, lookup, and receipt atoms
     remain an explicit boundary.],
    [Certified optimization],
    [Local rules reconstruct both endpoints; a fail-closed checker proves
     semantic equivalence and cost nonincrease. The public lowering binds every
     atom residual to a PI and is sound for arbitrary nonempty satisfying traces.],
    [`DirectLogicBoolGraphDescriptorIR2`: the public factor descriptor moves from
     35 to 18 constraints, 26 to 13 multiplications, and width 21 to 12 while
     pinning optimizer endpoints, PI layout, and exact bytes.],
  )
]

#block(breakable: false)[
  #set text(size: 8.05pt)
  #table(
    columns: (0.9fr, 2.15fr, 2.05fr),
    inset: 4.2pt,
    align: left,
    table.header([*Layer (continued)*], [*Verified construction*], [*Exact boundary*]),
    [Proof and FHE],
    [One raw opening feeds the proof relation and a BFV plan through an explicit
     conversion witness. Bounded encrypted zero observation and threshold opening
     now have explicit arithmetic, message, re-encryption, and leakage ledgers.],
    [`CertifiedHybridProofFheZeroObservation`; full accounting removes the former
     6-versus-9 multiplication advantage. No general BFV noise/security theorem or
     deployed same-opening verifier is claimed.],
    [Higher order],
    [A four-mode indexed compiler charges conversions and glue per subterm. Typed
     STLC compiles strongly-CCC to shared nets; local steps emit live public
     interaction receipts through direct depth 14.],
    [`CertifiedIndexedPresentationCompiler` and
     `IntensionalCCCInteractionDescriptorIR2`; exact for the represented fragment,
     with a proved typed-syntax-erasure boundary.],
    [General CCC boundary],
    [Every small CCC embeds by Yoneda. A faithful family of finite polynomial
     actions exists exactly for locally finite hom-sets, but no fixed finite width
     works in general, already for finite sets.],
    [`FamilyPolynomialYonedaFrontier` and `CertifiedPresentationFibredCCC`;
     fixed-meaning evidence fibres are CCCs, while the global presentation category
     is not even cartesian.],
    [Sampled proof objects],
    [Coverage changes preserve obstruction and miss events exactly; false
     acceptance factors into OOD, low-degree, binding, and query-miss budgets.
     Effective assembly covers are pullback-stable and admit regular images.],
    [`CategoricalDescentQueryProtocol`, `RobustDescentTranscriptGame`, and
     `AssemblyRegularCoverage`; cryptographic/FRI reductions and the associated
     topos or exact completion remain external.],
  )
]

This changes the technical center of the report. FOL is a source language, not
the primitive substance of proof. A compiler may preserve one judgment while
changing its presentation locally: natural residual, Boolean graph, shared net,
live AIR, or encrypted plan. The reusable theorem is the certified change of
presentation, with semantics and resources preserved at every edge.

== Performance evidence we can actually claim

The strongest performance evidence is now attached to public statement-bound
descriptors for named DREGG decisions. Exact formal ledgers, retained proof
serializations, noisy timing samples, and encrypted-boundary costs are reported
separately; none is relabelled as an end-to-end speedup.

#block(breakable: false)[
  #set text(size: 7.55pt)
  #table(
    columns: (1.18fr, 1.05fr, 0.95fr, 0.8fr, 1.3fr),
    inset: 3.6pt,
    align: left,
    table.header([*Public case*], [*Constraints*], [*Nonlinear mults*], [*Width*],
      [*Retained proof bytes*]),
    [Factor specimen], [35 to 18], [26 to 13], [21 to 12],
      [Exact statement binding; paired proof not captured],
    [Admission], [121 to 71], [108 to 58], [77 to 47], [14,016 to 11,894],
    [Upgrade], [33 to 23], [28 to 18], [21 to 15], [10,431 to 10,081],
    [Clearance], [33 to 23], [28 to 18], [21 to 15], [10,469 to 10,157],
    [Strand], [17 = 17], [13 = 13], [11 = 11], [9,850 = 9,850],
  )
]

The factor theorem distinguishes 30-to-13 graph equations from the public
descriptor's complete 35-to-18 constraint ledger: four PI bindings and one
output-equals-one check are included. Multiplications fall from 26 to 13,
auxiliaries from 17 to 8, and width from 21 to 12, with degree at most 2.
`public_statement_sound` covers every nonempty satisfying trace, not only the
compiler's witness; `public_canonical_trace_complete` supplies the converse for
true canonical inputs; and `checked_public_statement_sound` transports the result
through the accepted optimizer while pinning the PI layout and exact JSON bytes.

Admission, Upgrade, Clearance, and Strand are Boolean skeletons proved equivalent
to named production DREGG decisions at the atom boundary. Lean emitted both public
descriptors and canonical traces; Rust pinned and parsed those bytes, proved and
verified every variant, and rejected a public-input tamper at the consumer
verifier. The table's relation ledgers are deterministic theorem facts. Its proof
sizes are retained postcard encodings and can vary with proof contents.

The same capture retained 25 proving and 75 verification samples per variant, but
supports no timing speedup claim: the shared host was severely contended and the
distributions were wide and nonmonotonic. Strand is the decisive negative control.
Its source and optimized descriptor, trace, and proof bytes are identical, yet its
timing medians and tails differ. The capture therefore validates the pipeline and
quantifies proof-byte changes; it does not establish a latency ratio, scaling law,
Modulus comparison, or finality result.

Fully pricing encrypted zero observation also removes the apparent residual win.
For the formal $B=4$ five-equality plan, 6 inner multiplications plus 3 bounded
zero-conversion multiplications equals the all-Boolean 9, and both reach depth 4.
For the executable $B=8$ case, 8 plus 7 equals the Boolean 15. The bounded scaled
conversion executes exactly at $B=2$. At $B=8$ the captured scaled-bit threshold
observation refused a noncanonical output under the current unproved noise
envelope, while the separate raw threshold path succeeded by revealing every live
residual. This is fail-closed engineering and explicit leakage accounting, not an
FHE speedup or a general noise/security theorem.

The executable conformance corpus evaluated 10,061 cases. The corrected
`D-NOWRAP` lane passed all 6,737 admitted cases and refused 3,324 unsupported
ones; `D-BOOLGRAPH` and `C-AIR` passed all 10,061. `M-SPEC` produced 3,936
mismatches and the naive field projection produced one cancellation mismatch.
Unsound lanes are retained as falsification artifacts and excluded from every
performance ratio.

#theorem([executable boundary], [
  The independent Standard ML checker passed 15/15 version-1 fixtures and its
  complete live version-2 checker passed 11/11. HOL4 proves semantic soundness for
  accepted v1 and live-v2 bytes with zero recorded theory axioms, and CakeML
  translation certificates exist for both checkers. Lean emits the production
  descriptors; Rust byte-pins, parses, proves, verifies, and tamper-tests them.
  This is cross-language assurance, but neither a shipped native CakeML checker
  binary, a Rust-to-Lean verifier refinement, nor a cryptographic same-opening
  reduction is claimed.
])

== The public-audit result

The audited public claim does not survive technical review.

- Gabbay's construction is sound in its stated nonnegative characteristic-zero
  semantics. Naively interpreting its zero test in a prime field is unsound
  because nonzero residues can cancel or wrap to zero.
- BitLogic reverses the published zero-true connective and quantifier rules.
  Worse, its swap relation multiplies independent obligations. Under zero-true
  semantics multiplication expresses disjunction, so satisfying one factor can
  accept while the others fail. The concrete assignment
  $A=B=10$, $k=q=1$, $A'=9$, $B'=999$ is accepted by the displayed product
  although it violates two of the three intended obligations.
- The reviewed public repository supplies a PDF, not a runnable compiler,
  prover, verifier, parameter set, raw benchmark corpus, or reproducible path to
  the advertised 10--100x cost reduction and 1--3 second finality.

#boundary([
  The relation-level counterexample is decisive for the published equations; it
  is not a claim about unseen private code or a demonstrated production exploit.
  Conversely, unseen private code cannot substantiate a public performance or
  soundness claim. The strongest comparison currently available is therefore
  public evidence against public evidence: DREGG supplies the stronger formal
  semantics, executable falsification, construction breadth, and reproducibility;
  no like-for-like Modulus runtime comparison is possible from the released
  material.
])

#callout([EVIDENCE LEGEND], [
  *Kernel-checked* means a Lean or HOL4 theorem behind the stated axiom-hygiene
  gate. *Executable* means a concrete compiler, checker, counterexample, witness,
  or evaluator. *Measured* means a recorded implementation run with its workload
  and exclusions. A *theorem socket* still needs a protocol or backend
  instantiation. A *marketing claim* lacks a public reproducibility path.
])
