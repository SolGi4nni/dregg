#import "../section-helpers.typ": callout, theorem, boundary

= Proof objects beyond polynomials:\ realizability, descent, and transcript soundness

The corrected arithmetic constructions answer how to present a chosen judgment to a
chosen algebraic backend. They do not make first-order syntax, polynomial syntax, or
a finite field the primitive notion of proof. A stronger architecture starts with
meaning, chooses evidence, gives that evidence a local agreement structure, and only
then binds and samples it. Each transition needs its own theorem.

#block(breakable: false)[
  #table(
    columns: (0.76fr, 1.22fr, 1.62fr, 1.4fr),
    inset: 4.5pt,
    table.header([*Layer*], [*Mathematical question*], [*Formal construction here*], [*Deployment obligation*]),
    [Meaning],
      [What does the judgment assert?],
      [finite semantics; realizability predicates; resource-sensitive denotations],
      [application-specific atoms, effects, and observation policy],
    [Evidence],
      [What witnesses the judgment?],
      [PCA realizers; assembly morphisms; interaction traces; presentation changes],
      [a complete source-to-evidence compiler],
    [Agreement],
      [When do local views determine one global object?],
      [exact descent; robust-soundness sockets; explicit finite testers],
      [a code-specific distance and local-testability theorem],
    [Transcript],
      [How can hidden checks miss an obstruction?],
      [commit-before-query games; exact miss counts; BabyBear query-bias bound],
      [OOD and low-degree reductions with concrete parameters],
    [Binding],
      [Why can no response rewrite committed evidence?],
      [an explicit point-binding premise],
      [a commitment or PCS security reduction and Fiat--Shamir analysis],
  )
]

#align(center)[
  $ "judgment" arrow "evidence" arrow "local views"
    arrow "hidden queries" arrow "bound transcript". $
]

The categorical semantics explains what evidence and compatible restriction mean.
The probability game explains what a sampled verifier can miss. The cryptographic
backend explains why the prover cannot change an unseen view after learning the
query. None of those three explanations subsumes the other two.

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

=== Assemblies make the program boundary concrete

`Assembly` pairs a semantic carrier with a nonempty realizability relation. An
assembly morphism is an actual semantic function tracked uniformly by one PCA
element. `categoryAssembly` proves genuine category laws: the derived identity
combinator tracks identity, the exact composition program tracks composition, and
arrow equality is equality of the semantic functions.

This category already has useful finite-limit structure. The terminal assembly has
its unique incoming arrow. A chosen PCA pairing supplies binary products, with
`pair_fst`, `pair_snd`, and `pair_unique` proving the universal property. Equalizers
inherit the source realizers, and `equalizerLift_ι` plus `equalizerLift_unique` prove
factorization and uniqueness without changing the original tracker.

Modest assemblies induce partial equivalence relations on realizers.
`tracker_respects_realizerPER` proves that every uniform tracker transports those
PERs and returns both output realizers and their exact PCA applications. At the
compiler boundary, `ProgramCertificate` contains input and output representations,
a PCA program, and a theorem that the program produces the encoded result.
`ProgramCertificate.hom` turns it into an assembly morphism, while
`ProgramCertificate.comp_hom` proves that certificate composition agrees with
categorical composition. An extensional polynomial function alone supplies none of
that executable evidence.

== Presentations form fibers, not one global CCC

The resource-aware `Presentation` interface records source meaning, evidence,
acceptance, and a five-axis backend cost. An exact `Change` maps evidence, preserves
meaning and acceptance in both directions, and carries a compositional cost bound.
These changes form a category. This is the right place to compose residual,
Boolean-graph, shared-net, proof, and FHE representations of the same judgment.

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
beta/eta and exponential beta/eta. This result complements the extensional finite
CCC boundary in Section 4 without changing it: the exponential here is a space of
evidence transformers inside one semantic fiber, not a finite-field table of every
source morphism and not a succinctness theorem.

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
    [Assemblies / PERs],
      [tracked semantic maps, executable representation boundaries, extensional quotients],
      [a compiler program without a `ProgramCertificate`],
    [Descent / sheaf condition],
      [unique gluing from complete compatible local data],
      [that a few sampled overlaps expose every inconsistency],
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

This separation leaves room for non-polynomial proof objects. First and Kaufman's
cosystolic expansion of sheaves on posets gives two-query locally testable codes
#link("https://arxiv.org/abs/2403.19388")[arXiv:2403.19388]. Dinur, Liu, and Zhang's
HDX Tanner codes combine local Reed--Solomon views with a multiplication property
#link("https://arxiv.org/abs/2308.15563")[arXiv:2308.15563]. Flowering and Cayley-graph
IOPPs provide graph-indexed alternatives
#link("https://arxiv.org/abs/2501.14337")[arXiv:2501.14337]
#link("https://arxiv.org/abs/2508.10510")[arXiv:2508.10510]. Each is a candidate for
a quantitative socket, not an imported theorem about DREGG's deployed parameters.
FRI remains one established polynomial-code realization
#link("https://doi.org/10.4230/LIPIcs.ICALP.2018.14")[ICALP 2018], not the definition
of proof-object descent.

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

They are not yet a succinct argument. The remaining path is concrete: compile a
typed interaction trace to local patch constraints; prove exact descent of its
denotation and resource invariant; instantiate a robust code/proximity theorem;
then bind the encoded patches and apply the transcript game above.

#callout([CONSTRUCTION MAP], [
  Realizability supplies a semantics of evidence and quantification. Assemblies and
  certified presentations expose program and representation boundaries. Exact
  descent supplies the local-to-global law. Robust code theorems price inconsistency;
  the hidden-query and full-transcript games price missed obstructions and modular
  query bias. Commitments, FRI, graph IOPPs, and interaction traces are composable
  realizations of particular layers. No layer requires FOL, hashes, or polynomials
  to be the primitive notion of logic.
])
