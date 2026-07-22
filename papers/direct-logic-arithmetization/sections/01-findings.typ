#import "../section-helpers.typ": callout, theorem, boundary

= What was built, what failed, what got faster

Direct logic arithmetization is salvageable, generalizable, and useful. The
reviewed public BitLogic presentation is not yet a sound instance of it. This
report does more than separate those statements: it supplies the missing
constructions.

#callout([RESULT], [
  We reconstructed Gabbay's matrix-language compiler, proved its characteristic-
  zero semantics, added two exact finite-field repairs, and emitted a certified
  fixed matrix instance into DREGG's live DescriptorIR2 relation. We then built a
  general finite-signature FOL compiler, a checker-gated optimizer, a same-opening
  proof/FHE certificate, an intensional cartesian closed compiler with explicit
  sharing, a presheaf embedding for arbitrary small CCCs, and a bias-aware robust
  transcript theorem. The public BitLogic equations still fail the permanent
  counterexample suite. The positive stack does not.
])

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
    [A three-entry Skolem successor table is denominator-cleared and compiled to
     actual `EffectVmDescriptor2` constraints, with constructive trace,
     soundness, completeness, and tamper refusal.],
    [`GabbayDescriptorIR2`; fixed arity over BabyBear, not yet a symbolic
     variable-length matrix emitter.],
    [Finite FOL],
    [Closed de Bruijn syntax with equality, many relations of independent
     arities, total public function tables, every connective, and exhaustive
     finite quantification.],
    [`FiniteSignatureFOLDescriptorIR2`; exact canonical layout, live relation,
     certificate, and emitted bytes.],
    [Certified optimization],
    [Local rules reconstruct both endpoints; a fail-closed checker proves
     semantic equivalence and coordinatewise cost nonincrease; the recursive
     optimizer emits its own certificate.],
    [`DirectLogicOptimizerCertificate`; an independent reference tool also
     performs checked Pareto search across residual and Boolean presentations.],
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
     conversion witness. A mixed plan carries exact resource counts and an
     acceptance-equivalence theorem.],
    [`CertifiedHybridProofFhe`; algebraic and scheduling theorem, not a
     Rust-to-Lean refinement or a parameter-security theorem.],
    [Higher order],
    [Typed STLC compiles to shared nets with local beta, eta, and product
     evidence. The semantic quotient is a genuine CCC and the compiler is a
     strong-CCC functor.],
    [`IntensionalCCCTrace`, `IntensionalCCCInteractionBridge`, and
     `IntensionalCCCCategory`; exact for the formalized language.],
    [General CCC boundary],
    [Every small CCC embeds fully faithfully by Yoneda into presheaves, preserving
     terminal objects, products, and representable exponentials. Fixed-meaning
     evidence fibres are CCCs; the global category of meaning-changing
     presentations provably is not.],
    [`SmallCCCYonedaPresheaf` and `CertifiedPresentationFibredCCC`; no finiteness
     or finite-field succinctness is inferred.],
    [Sampled proof objects],
    [Commit-before-query descent with point binding gives an exact finite union
     bound. Modular query bias yields the sharp miss term
     $((1-delta)+delta/N)^k$ when $N mod m=1$.],
    [`RobustDescentTranscriptGame`; OOD and low-degree errors remain explicit
     protocol sockets.],
  )
]

This changes the technical center of the report. FOL is a source language, not
the primitive substance of proof. A compiler may preserve one judgment while
changing its presentation locally: natural residual, Boolean graph, shared net,
live AIR, or encrypted plan. The reusable theorem is the certified change of
presentation, with semantics and resources preserved at every edge.

== Performance evidence we can actually claim

The resulting gains are real but narrower than the advertised 10--100x claim.
They are theorem-checked structural counts on named specimens, plus separately
recorded executable measurements.

#block(breakable: false)[
  #set text(size: 8.2pt)
  #table(
    columns: (1.55fr, 1.08fr, 1.08fr, 1.45fr),
    inset: 4.5pt,
    align: left,
    table.header([*Construction*], [*Before*], [*After*], [*Verified result*]),
    [Symbolic BoolGraph optimizer],
    [30 equations#linebreak()26 multiplications#linebreak()17 witnesses],
    [13 equations#linebreak()13 multiplications#linebreak()8 witnesses],
    [57%, 50%, and 53% fewer in the materialized BoolGraph ledger.],
    [Formal hybrid BFV plan],
    [9 multiplications#linebreak()depth 4],
    [6 multiplications#linebreak()depth 2],
    [33% fewer multiplications and half the depth, before one unpriced boundary
     zero decision.],
    [Intensional sharing],
    [16 work nodes#linebreak()19 total nodes],
    [8 work nodes#linebreak()13 total nodes],
    [50% less duplicated work and 32% fewer nodes on the beta-sharing specimen.],
  )
]

The optimizer counts above do not describe the current live DescriptorIR2
encoding, which keeps a nested `WindowExpr` and materializes no intermediate
BoolGraph columns. They therefore establish a certified optimization opportunity,
not a current live-prover speedup. The hybrid `convertResidual` is likewise a
semantic boundary: its encrypted residual zero-test is not implemented or priced
as BFV arithmetic in this result.

The real BFV path separately executed a Boolean workload in 22.950435 ms and an
eight-equality residual workload in 48.197263 ms in one recorded warm release
run. Those are different computations and SIMD occupancies, so they define no
speedup ratio. The residual plan's 8 multiplications and depth 1 compare
symbolically with 15 multiplications and depth 4 for the matching all-Boolean
eight-equality formula, but exclude the residual's final private zero decision.

The executable conformance corpus evaluated 10,061 cases. The corrected
`D-NOWRAP` lane passed all 6,737 admitted cases and refused 3,324 unsupported
ones; `D-BOOLGRAPH` and `C-AIR` passed all 10,061. `M-SPEC` produced 3,936
mismatches and the naive field projection produced one cancellation mismatch.
Unsound lanes are retained as falsification artifacts and excluded from every
performance ratio.

#theorem([executable boundary], [
  The Rust finite-logic front end compiles typed finite inputs, predicates, and
  quantifiers into the live descriptor grammar; its focused suite contains an
  honest prove-and-verify round trip and refusal tests. The independent Standard
  ML checker passed 15/15 version-1 fixtures, while HOL4 proves accepted bytes
  semantically sound and records zero theory axioms; proof-producing CakeML
  translation certificates exist for that checker. The reference compiler's
  checked hybrid search is independently executable. These are substantial
  implementation artifacts, but no native CakeML checker binary,
  optimizer-to-live-descriptor lowering theorem, or
  Rust-to-Lean refinement is claimed.
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
