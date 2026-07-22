#import "../section-helpers.typ": callout, theorem, boundary

= Proof objects beyond polynomials:\ realizability, coverage, and transcript soundness

The corrected arithmetic constructions answer how to present a chosen judgment to a
chosen backend. They do not make first-order syntax, polynomial syntax, or a finite
field the primitive notion of proof. A stronger architecture starts with meaning,
chooses evidence, changes its presentation with explicit programs and costs, gives
the evidence a local coverage structure, and only then binds and samples it. Each
transition now has a named theorem or an explicitly open cryptographic socket.

#block(breakable: false)[
  #table(
    columns: (0.76fr, 1.22fr, 1.62fr, 1.4fr),
    inset: 4.5pt,
    table.header([*Layer*], [*Mathematical question*], [*Formal construction here*], [*Deployment obligation*]),
    [Meaning],
      [What does the judgment assert?],
      [finite semantics; realizability predicates; resource-sensitive denotations],
      [application-specific atoms, effects, and observation policy],
    [Evidence / presentation],
      [What witnesses the judgment, and in what representation?],
      [PCA realizers; assembly morphisms; interaction traces; per-subterm certified changes],
      [executable adapters and explicitly charged glue],
    [Coverage / agreement],
      [When do local views detect invalidity or determine one global object?],
      [effective assembly covers; exact descent; finite coverage presentations],
      [a code-specific distance and local-testability theorem],
    [Transcript],
      [How can hidden checks miss an obstruction?],
      [natural pullback of protocols; exact miss counts; BabyBear query-bias bound],
      [OOD and low-degree reductions with concrete parameters],
    [Binding],
      [Why can no response rewrite committed evidence?],
      [an explicit point-binding premise],
      [a commitment or PCS security reduction and Fiat--Shamir analysis],
  )
]

#align(center)[
  $ "judgment" arrow "evidence" arrow "presentation" arrow "local coverage"
    arrow "hidden queries" arrow "bound transcript". $
]

The categorical semantics explains what evidence, effective cover, and compatible
restriction mean. The finite probability game explains what a sampled verifier can
miss. The cryptographic backend explains why the prover cannot change an unseen view
after learning the query and why a transcript seed has the modeled distribution.
None of those explanations subsumes the others.

== Realizability is a semantics of evidence, not a field trick

The formal base is a relational partial combinatory algebra. `PCA.App f x y` says
that applying $f$ to $x$ is defined with unique result $y$; the $K$ and $S$ laws are
stated directly over that relation. The derived composition program is exact:
`PCA.app_compose_iff` characterizes precisely the two consecutive applications it
performs. An indexed predicate over $I$ is a family $I -> "Set"(A)$, and an
entailment is witnessed by one realizer that transforms every member at every index.
`entails_refl`, `entails_trans`, and `entails_reindex` prove the indexed preorder and
strict substitution action.

Chosen computable pairing, sums, and currying give the expected Heyting operations.
The formal universal properties are `entails_conj_iff`, `disj_entails_iff`, and
`entails_imp_iff`; truth, falsity, and preservation under reindexing are proved
alongside them. The construction does not assume that sum tags are injective or
that application is globally total.

There is a useful finiteness warning. Under the usual nontrivial definition, a PCA
cannot be a finite algebra. The Lean development includes `PCA.unitPCA`, a collapsed
one-point inhabitant of the law interface, but does not advertise it as a
computational realizability universe. Terwijn surveys the standard infinitude
boundary in #link("https://arxiv.org/abs/1910.09258")[_Computability in Partial
Combinatory Algebras_]. A finite-field backend should encode a finite execution
trace or certificate about a nontrivial PCA, not pretend to put the entire PCA into
a small field carrier.

=== Quantifiers and the empty-fiber test

Existential quantification is ordinary union over a map fiber and is a left adjoint
for every map (`existsAlong_adjunction`). Ordinary intersection gives the direct
right adjoint only for surjections (`forallAlong_adjunction_of_surjective`). At an
empty fiber, a pointwise premise supplies no uniform tracker and so cannot justify a
defined application.

`forallReal` repairs exactly that failure. Its evidence is a suspended pair $(e,x)$;
the application $e x$ is demanded at each point that actually lies over the target
index and is not demanded for an empty fiber. Consequently
`forallReal_adjunction` proves the right-adjoint law for every set map, while
`existsReal_adjunction` gives the matching arbitrary-map left adjoint.
`existsReal_beckChevalley` and `forallReal_beckChevalley` prove literal
Beck--Chevalley equalities for weak pullback squares. The regression theorem
`forallReal_empty_equiprovable_truth` confirms that an empty-fiber universal is
equiprovable with truth.

The uniform-family presentation packages these results without changing their
meaning. `pcaUFam_tracks_iff` and `pcaUFam_entails_iff` identify it exactly with the
PCA doctrine. `pcaUFamTriposLaws` collects the Heyting preorder, strict reindexing,
both arbitrary-map adjoints, Beck--Chevalley, exact generic classification, and
noncollapse. In particular, `pcaUFam_truth_not_entails_falsity` proves consistency
already at a singleton index.

#theorem([tripos boundary], [
  A Set-indexed realizability tripos-law package has been proved. The associated
  elementary topos has not. The development does not yet construct the exact
  completion, a subobject classifier, or an equivalence between that completion and
  the topos associated with `pcaUFamTriposLaws`. Pitts' tripos-to-topos account
  #link("https://www.cl.cam.ac.uk/~amp12/papers/tritr/tritr.pdf")[describes the
  classical route]; citation is not a substitute for the missing Lean construction.
])

=== Assemblies now carry effective regular coverage

`Assembly` pairs a semantic carrier with a nonempty realizability relation. An
assembly morphism is an actual semantic function tracked uniformly by one PCA
element. `categoryAssembly` proves genuine category laws. Terminal objects, binary
products, and equalizers were already explicit; `AssemblyRegularCoverage` adds
pullbacks with their full universal property through `pullback_condition`,
`pullbackLift_fst`, `pullbackLift_snd`, and `pullbackLift_unique`.

The new cover notion is evidence-relevant. `EffectiveCover q` does not merely say
that $q$ is surjective. It supplies one `liftCode` which, from any realizer of a
target point, computes a realizer of a source point above it. This is exactly the
program needed for constructive base change. Theorems `effectiveCover_id`,
`effectiveCover_comp`, and `effectiveCover_pullback` prove identity, composition,
and pullback stability, while `effectiveCover_surjective` recovers ordinary semantic
surjectivity.

The coverage is regular rather than decorative. `effectiveCover_isKernelPairCoequalizer`
proves that every effective cover is the coequalizer of its explicit kernel pair.
Every assembly morphism $f$ also factors as

#align(center)[
  $ X arrow^"effective cover" "im"(f) arrow^"monic" Y. $
]

Here `imageQuot_effectiveCover` supplies the cover, `imageIncl_monic` supplies exact
cancellation, and `image_factorization` proves their composite is $f$.
`imageQuot_isKernelPairCoequalizer` gives the coequalizer law for the quotient.
`ProgramCertificate.has_regular_image_factorization` transports the result directly
to compiled PCA programs. The 29 kernel-clean coverage keystones therefore construct
the regular-image ingredients of an exact completion, not merely a metaphor about
local evidence.

Modest assemblies still induce partial equivalence relations on realizers, and
`tracker_respects_realizerPER` proves their transport by uniform trackers. At the
compiler boundary, a `ProgramCertificate` contains representations, executable PCA
code, and its run theorem; `ProgramCertificate.hom` turns it into the morphism to
which the new factorization applies.

#boundary([
  Effective regular coverage is not yet the realizability topos. The development
  does not prove that all internal equivalence relations are effective, construct
  the exact completion, or establish elementary-topos axioms. Nor does a cover or
  program certificate imply transcript soundness. The concrete theorem
  `compiled_regular_image_does_not_supply_query_soundness` exhibits a certified
  constant-false program with its effective regular image alongside an always-accept
  attestation that is complete but range-unsound.
])

== Presentation change is fibred and resource-aware

The resource-aware `Presentation` interface records source meaning, evidence,
acceptance, and a five-axis backend cost. An exact `Change` maps evidence, preserves
meaning and acceptance in both directions, and carries a compositional cost bound.
These changes form a category. Section 4's `CertifiedIndexedPresentationCompiler`
now makes this operational per subterm: child changes tensor, then recombination is
charged, and `Plan.accepts_iff` closes the source-semantics induction.

The global category is deliberately not cartesian closed. Its objects may carry
different meanings, while an exact arrow requires those meanings to be equivalent.
`no_weakTerminal` proves that no object can receive arrows from both the true and
false presentations; hence `no_global_cartesian_structure`. Likewise, the obvious
presentation of logical conjunction generally has no categorical projections:
`firstProjection_forces_right` and `secondProjection_forces_left` show that such
projections would force implications between the two meanings.

The positive replacement is fibred. Over one fixed meaning, `EvidenceFamily` objects
vary only the evidence type. Pointwise evidence transformers form a genuine
cartesian closed category: unit evidence is terminal, paired evidence is product,
and evidence transformers form exponentials. `EvidenceFamily.laws` packages product
beta/eta and exponential beta/eta. This complements the indexed compiler without
changing the boundary: the exponential is a space of evidence transformers inside
one semantic fibre, not a finite-field table of every source morphism. Likewise,
`Boundary.free_glue_claim_is_false` proves that a zero-resource semantic fibre does
not justify zero-cost materialized recombination.

== Exact descent: compatible local evidence glues uniquely

`ProofObjectDescent` isolates the backend-neutral local-to-global theorem. A
`DataCover` includes a computational locator. `Matching` says local sections agree
on every pairwise overlap, and `glue` chooses the located local value pointwise. The
central theorem `matching_iff_existsUnique_amalgamation` proves

#align(center)[
  $ "all overlaps match" quad "iff" quad exists! g,
    " every local view restricts from " g. $
]

`incompatible_no_amalgamation` proves the refusal direction.
`verifiedEvidence_descends` applies the same theorem to subtype-valued evidence
${w : W_x | "Checks"(x,w)}$, so the glued global witness retains its local
verification proofs. This theorem contains no polynomial, field, hash, commitment,
random oracle, or FRI premise.

Exact descent checks every relevant overlap. `RobustProofObjectDescent` exposes what
sampled checking additionally requires:

- `WeightedQueryModel` permits an arbitrary finite weighted query distribution;
- `RejectLowerSoundness` and `DistanceUpperSoundness` carry explicit, possibly
  nonlinear robustness moduli;
- `FoldChainSoundness` separates distance preservation from weighted exceptional
  challenges; and
- `ProximityGap` bounds challenges that transform a far word into a close word.

These are theorem sockets, not assumed code theorems. Their soundness, exceptional
weight, and gap fields must be instantiated for the deployed graph, sheaf, HDX, or
FRI code. Two finite instances show that the interfaces are nonvacuous.
`FinitePatchCode.reconstruct_codeword` reconstructs the unique global codeword from
matching valid patches. The three-patch `WeightedStar` theorem
`rejection_eq_hubDistance` gives exact equality between rejected weight and distance
to the hub-selected codeword; its one-error example proves coefficient one sharp and
refutes a false factor-two bound.

== Coverage presentations make query change natural

Assembly covers describe executable lifting of semantic evidence. A second,
independent categorical structure now describes how a verifier presents local
obstructions. A `CoveragePresentation Family Invalid` contains a finite query type,
a decidable predicate `bad family query`, and a detection theorem saying that every
invalid family has at least one bad query. It contains no commitment, polynomial,
transcript, or sampler assumption.

A morphism $P arrow Q$ interprets each query of $Q$ as a query of $P$ and preserves
*and reflects* `bad`. The query map is therefore contravariant. These morphisms form
a category. `CoveragePresentation.obstruction_natural` proves the naturality square,
and `obstruction_natural_comp` proves it through successive presentation changes.
Finite bad-set membership is natural as well, but cardinality need not be preserved:
a query interpreter may duplicate a source query.

The protocol layer follows the same variance. `PresentedProtocol.pullback` reindexes
an opening scheme and local test without changing its commitment relation.
`PresentedProtocol.pullback_comp` proves that two such changes equal pullback along
their composite. `misses_natural` and `missEvent_natural` prove exact equality of the
pointwise and seed-level miss events. This event equality is the safe invariant;
silently comparing bad-set cardinalities would be false for duplicating maps.

#block(breakable: false)[
  The realizability connection is explicit but limited.
  `RealizabilityLayer.obstructionPredicate_natural` proves reindexing naturality for
  the obstruction predicate in the existing PCA doctrine, and
  `obstructionPredicate_classified` classifies it by the existing generic predicate.
  If a query interpreter additionally has one uniform PCA tracker,
  `TrackedPresentationMap.comp` composes those interpreters as assembly morphisms.
  Coverage naturality alone does not manufacture that tracker or an associated topos.
]

#theorem([CATEGORICAL QUERY NATURALITY], [
  The 37 kernel-clean keystones of `CategoricalDescentQueryProtocol` prove a category
  of finite coverage presentations, compositional protocol pullback, exact
  naturality of obstruction and miss events, a realizability reindexing law, and a
  factored soundness interface. Presentation change adds no hidden cryptographic
  error term because it proves event equality. Commitment binding, transcript
  sampling, OOD reduction, and low-degree reduction remain separate inputs.
])

=== Soundness factors into four independently priced events

For a computational commitment, `BindingFailureAtSeed` records the exact bad event:
some accepted opening differs from the view fixed by the commitment.
`locallyAccepts_misses_or_bindingFailure` proves that locally accepted openings
either miss all precommitted obstructions or exhibit that failure. The event
inclusion `acceptSeeds_subset_four_events` therefore places every accepting seed in
one of four classes:

1. an OOD exception;
2. a low-degree or folding exception;
3. a binding failure; or
4. a sampler miss.

`acceptSeed_card_le_budgets_with_binding` gives the exact finite union bound.
`factored_soundness_with_binding_budget` combines it with coverage detection and a
`SamplerBound`, yielding

#align(center)[
  $ #"accepting seeds" <= epsilon_"OOD" + epsilon_"LDT"
    + epsilon_"bind" + epsilon_"miss", $
]

where the displayed terms are finite seed counts in this theorem, not silently
normalized probabilities. `factored_soundness` is the perfect `PointBinding`
specialization and removes the binding-failure addend. A computational deployment
must supply a reduction translating its commitment advantage into the corresponding
budget.

`SamplerBound.independentUniform` supplies the exact information-theoretic reference
for $k$ uniform queries with replacement. It does *not* prove that Fiat--Shamir or a
random oracle produces that seed distribution. For the transparent reference,
`transparent_uniform_acceptance_card` proves the exact count
$|"good queries"|^k$. In the concrete finite-patch instance,
`WeightedStarInstance.oneError_uniform_one_query_strict` proves that one uniform
query has strictly fewer accepting seeds than the complete-overlap query space. This
is deliberately the *unweighted* complete-overlap sampler; it does not flatten the
weighted-star example's separate edge weights into the theorem.

#boundary([
  Categorical naturality says that exact changes of query presentation preserve the
  obstruction and miss events. It does not prove commitment binding, Fiat--Shamir or
  random-oracle soundness, an OOD polynomial identity bound, FRI proximity, or the
  adversarial seed distribution. Those are the explicitly separate premises of
  `factored_soundness_with_binding_budget` and the transcript theorems below.
])

== Hidden-query soundness: price the obstruction that was missed

Exact gluing does not imply that spot checks deterministically extract a global
object. The corrected statement is probabilistic and keeps the committed family
visible. If a finite section family has no amalgamation,
`badEdges_nonempty_of_no_amalgamation` proves that its obstruction set is nonempty.
For a query space of size $Q$, an obstruction set of size $B$, and $k$ independent
with-replacement queries, `missSamples_card_sub` proves the exact count

#align(center)[
  $ #"misses" = (Q - B)^k,
    quad #"all samples" = Q^k. $
]

Thus the exact uniform miss probability is $(1-B/Q)^k$. A bad committed object can
pass on precisely this event; acceptance alone does not yield a total column.

`QueryOpeningScheme` separates committed family, digest, view, opening relation, and
opening proof. `PointBinding` states the anti-rewriting property actually consumed by
the verifier game: after committing, any accepted opening at a query equals that
query's committed view. The responder may otherwise be adaptive.
`acceptsSample_misses` proves that a bound responder accepted on every sampled query
must have missed every obstruction, and `acceptedSamples_card_le` transfers the
exact miss count to an acceptance bound. `invalid_gluing_acceptance_bound` specializes
the statement to overlap inconsistency. In the transparent reference game, two of
four overlap edges are bad; two queries miss them in exactly four of sixteen samples,
and the accepted-sample count is at most four.

#theorem([query-game correction], [
  The proved conclusion is a finite event inclusion and count, not deterministic
  extraction. Point binding prevents post-query rewriting; it does not make hidden
  queries hit every obstruction. A computational deployment must add the adversary's
  advantage in breaking its concrete commitment's binding game.
])

== Full transcript composition, including BabyBear bias

`RobustDescentTranscriptGame` makes the protocol order explicit:

#align(center)[
  $ "commit family" arrow "sample transcript seed" arrow "derive challenges and queries"
    arrow "open queried views". $
]

A `TranscriptResponder` may inspect the entire revealed seed and the query
coordinate. Point binding still forces every accepted response to equal the
precommitted view (`locallyAccepts_misses`). The protocol-specific
`AcceptanceReduction` then has one clear job: prove that full acceptance implies at
least one of three events:

1. all bound local openings pass;
2. an OOD algebraic exception occurs; or
3. a low-degree or folding exception occurs.

`acceptSeeds_subset_exceptional_union_miss` proves the corresponding event inclusion.
`acceptProb_le_union` proves the exact finite union bound. It requires no independence
between the OOD and low-degree events.

The query sampler is also modeled rather than idealized. A squeeze value in
$"Fin"(N)$ is reduced modulo a query-domain size $m$. If the obstruction density is
at least $delta$, `mod_miss_prob_le` gives the conservative term

#align(center)[
  $ ((1-delta) + m/N)^k. $
]

When $N mod m = 1$, only one residue class is heavy. The sharp theorem
`mod_miss_prob_le_sharp` improves the term to

#align(center)[
  $ ((1-delta) + delta/N)^k. $
]

`biased_transcript_soundness_sharp_extra` allows every non-query transcript
coordinate - OOD points, folding challenges, batching challenges, and future
coordinates - to remain in an arbitrary finite `Extra` factor. The exceptional
predicates and adaptive responder may inspect all of it. The query-marginal
probability is unchanged because the uniform extra coordinates product out.

For BabyBear, $p = 2013265921$. For every realizable power-of-two domain
$m=2^ell$ with $1 <= ell <= 27$, the proved arithmetic fact is $p mod m = 1$.
Therefore `babybear_transcript_soundness_sharp_extra` proves the complete bound

#align(center)[
  $ Pr["false acceptance"] <= epsilon_"OOD" + epsilon_"LDT"
    + ((1-delta) + delta/2013265921)^k. $
]

This is the exact sharp BabyBear expression formalized by the current game. The
$delta/p$ term is the modular-reduction defect; it is not silently rounded away and
does not depend on trace height. The finite reference transcript proves that all
three addends can be load-bearing: at $N=5$, $m=2$, $k=1$, and $delta=1/2$, the
query term is $3/5$, the OOD and low-degree terms are each $1/5$, and the union
bound is attained exactly.

#boundary([
  The BabyBear theorem is conditional on a fixed precommitted invalid object,
  point binding, the stated obstruction-density premise, and a protocol-specific
  acceptance reduction. It does not itself prove the deployed commitment binding,
  an OOD Schwartz--Zippel bound, a FRI low-degree theorem, random-oracle security,
  Fiat--Shamir soundness, or a total-column extraction theorem. Those premises must
  be instantiated and their error terms composed before quoting a bit-security
  number.
])

=== What topos theory contributes - and what it cannot contribute alone

#block(breakable: false)[
  #table(
    columns: (1.05fr, 1.7fr, 1.55fr),
    inset: 4.5pt,
    table.header([*Mechanism*], [*It can establish*], [*It cannot establish by itself*]),
    [Realizability / tripos],
      [meaning, uniform evidence transformation, logical adjoints, substitution],
      [local testability, hiding, commitment binding, proof size],
    [Assemblies / regular coverage],
      [tracked maps, pullback-stable effective covers, kernel-pair descent, regular images],
      [exact completion, a topos, or query soundness],
    [Descent / sheaf condition],
      [unique gluing from complete compatible local data],
      [that a few sampled overlaps expose every inconsistency],
    [Coverage presentation],
      [natural obstruction and miss events under exact query change],
      [binding, Fiat--Shamir, OOD, or FRI budgets],
    [Robust code theorem],
      [distance versus rejected-query weight and proximity gaps],
      [that an adaptive prover is bound to one word],
    [Commitment / PCS],
      [binding or hiding under a stated security game],
      [semantic correctness of the committed proof object],
    [FRI / graph IOPP],
      [a quantitative low-degree or code-proximity test],
      [the source logic semantics or commitment theorem],
  )
]

Non-polynomial quantitative sockets remain possible: sheaf cosystolic codes
#link("https://arxiv.org/abs/2403.19388")[arXiv:2403.19388], HDX Tanner codes with
local Reed--Solomon views #link("https://arxiv.org/abs/2308.15563")[arXiv:2308.15563],
and graph IOPPs #link("https://arxiv.org/abs/2501.14337")[arXiv:2501.14337]
#link("https://arxiv.org/abs/2508.10510")[arXiv:2508.10510]. These are candidate
sockets, not theorems about DREGG's deployed parameters. FRI is one established
polynomial-code realization #link("https://doi.org/10.4230/LIPIcs.ICALP.2018.14")[ICALP
2018], not the definition of proof-object descent.

== Local interaction traces are proof objects too

The interaction route makes evidence a replayable list of local graph changes.
`InteractionNetTrace` uses a finite typed Boolean port tree. An `ActiveRule`
contracts one literal/gate interaction, and a one-hole `Context` identifies its
location. `activeRule_preserves` proves every primitive rewrite;
`contextualRule_preserves` lifts it under arbitrary contexts. `LocalCert.check` is
executable and fail-closed. `checkTrace_sound` proves denotational preservation for
accepted replays, while `checkTrace_reduces` reconstructs the finite reduction.

`LinearInteractionTrace` independently tracks resource kind, ticket, polarity, and
explicit provenance. Its trace checker preserves the extensional per-ticket
observation, total endpoint provenance, each ticket's count, and signed balance.
The executable counterexamples reject cross-kind closing, a rule at the wrong
location, and silent weakening. These traces are genuine proof objects that need
not first be formulas or residual polynomials.

The new live intensional descriptor closes one local backend boundary. For a typed
STLC step it emits the lossless root/address receipt, binds every row cell to public
inputs, and recomputes two domain-separated receipt-layout digests. `trace_complete`
and `satisfying_trace_relation_sound` connect a satisfying DescriptorIR2 witness to
both executable receipt acceptance and typed denotational preservation. Its exact
cost is $d+5$ columns and public inputs, $d+5$ linear PI constraints, two hash sites,
and $2(d+2)$ absorbed felts at address depth $d$.

That one-row descriptor is still not a succinct argument for a complete trace. The
live hash-site limit gives $d <= 14$ without a multi-block sponge, and
`no_exact_typed_source_decoder` proves that the receipt layout has already erased
the typed endpoint syntax. The remaining route is therefore precise: add typed-net
statement data where required; encode a sequence of local receipts as covered
patches; prove exact descent and the resource invariant; instantiate a robust
code/proximity theorem; then supply binding, Fiat--Shamir, and FRI or another IOPP
through the factored protocol interface.

#callout([CONSTRUCTION MAP], [
  Realizability supplies a semantics of evidence and quantification. Assembly
  regular coverage supplies executable lifting, kernel-pair descent, and image
  factorization. The indexed compiler chooses a presentation per subterm while
  charging conversion and glue. Exact descent supplies the local-to-global law;
  coverage presentations make obstruction and miss events natural under query
  change. Robust code theorems price inconsistency, and the transcript games price
  missed obstructions and modular query bias. Commitments, Fiat--Shamir, FRI, graph
  IOPPs, and live interaction receipts instantiate separate layers. No layer
  requires FOL, hashes, or polynomials to be the primitive notion of logic.
])
