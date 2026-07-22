#import "../section-helpers.typ": theorem, boundary

= Higher-order logic and certified change of presentation

There is no single object called "the higher-order arithmetization." The exact
result is a map of several constructions, together with a compiler calculus that
may select among them *per subterm* without erasing either meaning or cost.

- Finite extensional HOL has a complete polynomial semantics, but arrow values are
  dense tables.
- A small category has a faithful family of finite-field polynomial Yoneda actions
  exactly when every hom-set is finite.
- Every small CCC embeds fully faithfully in a presheaf CCC by Yoneda, preserving
  its chosen exponentials up to explicit isomorphism. This is semantic, not a
  finite-field encoding.
- Typed STLC compiles to shared nets in a genuine CCC and now reaches a live
  DescriptorIR2 receipt statement with exact width, hash, and depth boundaries.
- A certified indexed compiler can choose dense-polynomial, Boolean-graph,
  interaction-net, or natural-residual fragments independently, then charge the
  conversions and glue that join them.

The fifth item is the synthesis. Logic is not forced through one privileged syntax.
A term may use whichever presentation has a proved semantic certificate and an
honest backend ledger. The resulting theorem is compositional, but it is not a
claim that every listed backend is already equally executable or equally fast.

#theorem([CERTIFIED PER-SUBTERM PRESENTATION], [
  `CertifiedIndexedPresentationCompiler.Plan.accepts_iff` proves source semantics
  for every recursively mixed plan. `Plan.materialization_overhead_eq_resources`
  proves that its derived materialization morphism exposes the *entire* five-axis
  ledger: equations, multiplications, witnesses, maximum degree, and table cells.
  `ResourceMorphism.tensor_comp_interchange` proves that independent child
  conversions compose. These 28 kernel-clean keystones are a calculus of certified
  presentation change, not a latency theorem.
])

== The compiler: choose locally, certify globally, charge the glue

A `Fragment truth formula mode` contains three inseparable pieces: an observable
acceptance proposition, a `semanticCertificate` identifying it with the indexed
source formula, and a `BackendCost`. The four mode tags remain distinct even when
their acceptance propositions are logically equivalent:

#align(center)[
  $ "dense polynomial" quad "Boolean graph" quad "interaction net"
    quad "natural residual". $
]

A `Plan.whole` stops at one certified fragment. `Plan.and` and `Plan.or` instead
compile their children independently and then add a caller-supplied recombination
ledger. Consequently the resource recurrence is

#align(center)[
  $ C("left" diamond "right") = C("left") + C("right") + C("glue"), $
]

where addition is componentwise except that maximum degree uses `max`.
`Plan.and_resources` and `Plan.or_resources` expose this recurrence literally.
`Plan.accepts_iff` proves exact semantics by induction over any mixture of modes.

The cost evidence is itself compositional. A `ResourceMorphism source target`
contains an explicit overhead and proves

#align(center)[
  $ "target" <= "source" + "overhead". $
]

Identity has zero overhead; sequential changes add overheads; independent changes
tensor; and `ResourceMorphism.tensor_comp_interchange` proves the interchange law.
The plan first tensors the child materializations and then applies
`ResourceMorphism.charge` for recombination. The equality
`Plan.materialization_overhead_eq_resources` rules out an untracked remainder.

Two existing direct-logic implementations instantiate the interface concretely.
`DirectLogicAdapter.naturalResidual` consumes a no-wrap certificate;
`DirectLogicAdapter.booleanGraph` consumes the materialized inverse-witness graph;
and `DirectLogicAdapter.residualToBoolean_acceptance` proves their exact semantic
conversion. Because no tighter conversion-cost theorem is yet supplied, that
adapter conservatively charges the complete Boolean target ledger. The dense and
interaction modes are valid fragment interfaces, and the four-way plan witnesses
per-subterm mixing, but a semantic `Fragment` alone does not emit either backend.

This distinction is enforced by two counterexamples. In
`Boundary.free_glue_claim_is_false`, two zero-cost semantic atoms still require a
one-equation conjunction recombiner, so the materialized plan is not bounded by a
zero ledger. In `Boundary.exact_semantics_but_no_free_conversion`, source and target
accept exactly the same proposition, but no zero-overhead resource morphism can
produce a one-equation target from a zero-cost source. Logical equivalence does not
manufacture backend work for free.

`Search.choose_minimal_relative` is deliberately finite-list-relative: it minimizes
the declared score only among the candidates a caller supplied. It proves neither
global compiler optimality nor that the score predicts wall-clock proof time.

#boundary([
  The indexed compiler certifies a change of presentation only after a backend has
  supplied a `Fragment`, any conversion morphism, and the recombination charge. It
  does not infer a live circuit, FHE program, commitment, or cost bound from semantic
  equivalence. Today the residual and Boolean-graph adapters are direct; the other
  backend connections remain separately checked constructions.
])

== Finite extensional HOL: complete, exact, and dense

Fix a finite field $F$ of cardinality $q$. For a finite coordinate type $sigma$,
write $F^sigma$ for $sigma -> F$. Every function from one finite field power to
another is represented coordinatewise by a polynomial function. For one scalar
output, the explicit interpolation formula is

$
  delta_a(x) = product_(i in sigma) (1 - (x_i-a_i)^(q-1)),
  quad
  p_f(X) = sum_(a in F^sigma) f(a) delta_a(X).
$

Fermat's finite-field law gives $delta_a(a)=1$ and $delta_a(x)=0$ for $x != a$,
so $p_f(x)=f(x)$ at every field point. `eval_interpolate` and
`eval_interpolateVector` prove the scalar and vector forms. These are polynomial
*functions*: $X^q-X$ is generally nonzero as syntax and zero as a function on $F$.

The finite HOL construction uses types generated by unit, scalar, product, and
arrow. A type $A$ has a finite coordinate type $C_A$ and value space
$bracket.l A bracket.r = F^(C_A)$. An arrow has coordinates

$
  C_(A arrow B) = (F^(C_A)) times C_B,
$

so an arrow value is its complete input-output table. Lambda fills the table;
application reads it. The intrinsically typed term language validates product beta,
function beta, and extensional eta. Its formulas add equality, Boolean connectives,
and universal and existential quantification at every generated type. Quantification
at arrow type really ranges over every table.

A typed environment is flattened losslessly by `environmentEquiv`. Every term
coordinate has a `termPolynomial`, and every formula $phi$ has a Boolean-valued
`formulaPolynomial` satisfying

$
  "eval"(p_phi, x) = 0 quad "iff" quad x models phi.
$

The headline theorems are `eval_formulaPolynomial_point_isBit` and
`eval_formulaPolynomial_point_eq_zero_iff`; forall, exists, and arrow-forall forms
are proved separately. This is a complete arithmetization of the defined finite
extensional equality-HOL. It is noncomputable truth-table interpolation, not an
extracted optimizing compiler.

=== Exact exponential cost

If $|sigma|=n$ and $|tau|=m$, then

$
  |(F^sigma -> F^tau)| = (q^m)^(q^n) = q^(m q^n).
$

The exponential object has exactly $m q^n$ field coordinates and $q^(m q^n)$
points. `card_expCoord`, `card_tableObject`, and `card_arrowQuantifierDomain`
prove those counts. The blowup is the represented function space, not slack in the
analysis. `finite_hom_bound`, `no_injective_infinite_hom`, and the concrete
`no_injective_nat_predicates` rule out a faithful injection of an infinite hom-set
into one fixed finite table carrier.

== The exact locally-finite family-polynomial frontier

The fixed-carrier obstruction is not the end of categorical arithmetization. The
right positive object is a *family* indexed by a probe $X$ and target $A$:

#align(center)[
  $ "YonedaCoord"(X,A) = "Hom"(X,A). $
]

Under local finiteness this is a finite coordinate type for each pair. A morphism
$f : A arrow B$ acts by postcomposition $a mapsto f compose a$. In one-hot
coordinates, output coordinate $b$ is the linear polynomial

$
  "Act"_(f,X,b)(x) =
    sum_(a : X arrow A) [f compose a = b] x_a.
$

`actionPolynomial_totalDegree_le_one` proves formal total degree at most one, and
`eval_actionPolynomial` proves exact evaluation on every valid code. This is linear
because $f$ is fixed. When both composands vary, the earlier one-hot composition
polynomial remains bilinear of degree at most two.

`FamilyPolynomialCategoryPresentation` couples faithful hom encodings to those
polynomial actions. Its sharp classification is

#align(center)[
  $ "family-polynomial presentation exists"
    quad "iff" quad
    "every hom-set is finite", $
]

proved by `familyPolynomialPresentation_nonempty_iff_locallyFinite`.
`polynomialAction_id_onCode` and `polynomialAction_comp_onCode` prove the categorical
laws on valid codes. `polynomial_identityProbe_iff` shows that two parallel arrows
are equal exactly when their polynomial Yoneda outputs agree at the single identity
probe. The 29 kernel-clean frontier keystones classify this family construction and
its limits.

The polynomial family and semantic Yoneda are the same postcomposition operation:
`polynomialAction_is_yoneda` states the equality. For a small CCC,
`familyYonedaExponentialIso` then preserves its chosen exponentials in the presheaf
CCC. Thus every *small, locally finite* CCC has both a faithful family of finite
polynomial actions and a fully faithful semantic embedding preserving CCC structure.
The presheaf category and the family of probes need not be finite.

=== Why one fixed width still fails, even for finite sets

Family-wise finiteness does not imply a uniform circuit. A
`UniformIndexedHomPresentation` permits pair-dependent coordinate types but bounds
all their cardinalities by one `budget`. `UniformIndexedHomPresentation.hom_card_le`
then forces

#align(center)[
  $ |"Hom"(A,B)| <= q^"budget" $
]

for every pair of objects.

The CCC of finite sets is the sharp counterexample. `FiniteSetCCC.laws` constructs
its terminal object, products, evaluation, curry, and uncurry. Every individual
hom-set is finite, yet maps from the singleton to an $n$-element set have cardinality
exactly $n$ (`card_singleton_hom_fin`). Choosing $n=q^"budget"+1$ contradicts the
uniform bound. Therefore `finite_sets_family_yes_uniform_no` proves both sides at
once: the exact family-polynomial presentation exists, but no globally fixed
coordinate budget can remain faithful.

This is stronger than the earlier infinite-hom obstruction. Even a locally finite
CCC may require unbounded widths across its family. `EffectiveLocallyFiniteHom` is
also extra data: proposition-valued local finiteness alone does not provide an
enumeration or decidable equality for executable polynomial emission. Finally,
`committed_identityProbe_sound` consumes a separately supplied binding commitment;
Yoneda and interpolation do not manufacture cryptographic binding.

#theorem([CCC FRONTIER, EXACTLY], [
  Arbitrary small CCC: fully faithful semantic Yoneda with chosen exponentials
  preserved. Small locally finite CCC: additionally, an exact family of finite-field
  polynomial representable actions. Uniform fixed-width family: impossible in
  general, already for the CCC of finite sets. Effective emission and cryptographic
  binding: additional structures, not consequences of those categorical theorems.
])

== The intensional route: shared computation instead of arrow tables

Dense tables are not the only semantics for higher-order programs. The intensional
development starts from intrinsically typed STLC with unit, natural numbers,
products, arrows, and explicit source `let1`. Its target `Net` language adds a
sharing binder. Beta compilation performs

$
  (lambda x. b) a quad arrow.r.long quad "share" a "as" x "in" b,
$

so the argument is represented once and referenced wherever the variable occurs.
`compile_denote`, `localStep_denote`, and `trace_denote` prove compilation and every
typed local trace denotationally exact. Product beta and extensional eta have their
own local certificates.

The quantitative specimen binds an eight-operation computation once and uses it
twice. Its shared target contains 8 work nodes and 13 total nodes; literal copying
contains 16 work nodes and 19 total nodes. Beta costs one local rewrite. The shared
cost is independent of $q$, while the matching one-input, two-output extensional
table has $2q$ coordinates; `shared_smaller_than_table_coordinates` proves the
shared graph smaller from $q >= 7$. This is a checked structural comparison, not a
prover latency benchmark.

`IntensionalCCCCategory` constructs genuine source and shared-net CCCs. Identity,
composition, terminal arrows, pairing, evaluation, curry, and uncurry have explicit
closed-net representatives, and `Shared.laws` proves their laws. The structural
compiler induces `compilerFunctor`; `Compiler.strongCCC` proves preservation of
identity, composition, terminal objects, products, evaluation, currying, and
uncurrying. Equality is denotational equality in a represented image/quotient, not a
decidable syntactic rewrite equivalence or the universal property of the free CCC.

=== A live DescriptorIR2 receipt, with an exact erasure boundary

The former interaction bridge stopped at an executable Boolean receipt.
`IntensionalCCCInteractionDescriptorIR2` now emits a one-row live descriptor for the
receipt's root-rule tag, complete address path, two domain tags, and two endpoint
digests. At address depth $d$, `descriptor_shape_exact` and `cost_exact` prove:

#block(breakable: false)[
  #table(
    columns: (1.45fr, 1fr),
    inset: 4.2pt,
    table.header([*Quantity*], [*Exact value*]),
    [trace columns / public inputs], [$d+5$ / $d+5$],
    [linear PI constraints], [$d+5$],
    [hash sites / absorbed felts], [$2$ / $2(d+2)$],
    [maximum arithmetic-gate degree], [$1$],
  )
]

`trace_complete` constructs a satisfying DescriptorIR2 trace for every typed local
step. Under a nonempty row and canonical BabyBear representatives for the layout
tags, `satisfying_layout_words_exact` binds an arbitrary satisfying row to the exact
root and address. `satisfying_trace_relation_sound` composes that binding with the
receipt checker and returns two deliberately separate facts: the Boolean interaction
checks, and the original typed denotation is preserved. `binder_side_tamper_refused`
rejects the concrete one-cell `shareBody` to `shareValue` mutation.

The shared live hash table absorbs at most 16 felts per site. Because each endpoint
site absorbs $d+2$, `max_live_depth_exact` gives the direct one-site boundary
$d <= 14$; deeper addresses require a multi-block sponge lowering. The depth-one
wire guard fixes 6 public inputs, 6 trace columns, 6 PI constraints, 2 hash sites,
and 6 absorbed felts. `beforeCommit_binds` additionally requires the named
`Poseidon2SpongeCR` premise. The descriptor theorem itself does not discharge that
cryptographic assumption.

Most importantly, the endpoint digest commits the *receipt layout*, not the full
typed source nets. `layout_forgets_typed_endpoints` exhibits beta redexes containing
literals 1 and 2 with the same layout; `receipt_backend_cannot_distinguish_typed_endpoints`
propagates the collision; and `no_exact_typed_source_decoder` proves that no decoder
from the erased layout can recover both exact sources. The 27 kernel-clean descriptor
keystones therefore close the live receipt boundary while proving why a later typed
syntax commitment must add new statement data.

#boundary([
  A live receipt statement is not a complete higher-order program proof. It binds one
  local rule/address receipt up to the stated hash premise, but it does not bind the
  typed syntax erased by `layout`, encode an entire interaction trace as a robust
  code, or supply commitment, Fiat--Shamir, FRI, or end-to-end proof-system soundness.
])

== What has, and has not, been generalized

#table(
  columns: (1.05fr, 1.34fr, 1.66fr),
  inset: 4.1pt,
  table.header([*Construction*], [*Exact result*], [*Boundary*]),
  [Finite extensional HOL],
    [Every defined formula has an exact Boolean polynomial.],
    [Complete arrow tables; finite carrier; dense quantification.],
  [Family-polynomial Yoneda],
    [Exists exactly for locally finite categories; linear fixed-arrow action.],
    [Family-indexed and potentially unbounded; effectiveness is extra.],
  [Semantic Yoneda],
    [Fully faithful for every small CCC; chosen exponentials preserved.],
    [Presheaf semantics, generally infinite; no arithmetic backend or succinctness.],
  [STLC to shared nets],
    [Genuine CCCs, strong-CCC compiler, live local receipt descriptor.],
    [One intensional fragment; receipt layout erases typed endpoints.],
  [Indexed presentation compiler],
    [Per-subterm semantic preservation with compositional charged resources.],
    [Backend adapters and glue costs must be supplied; search is list-relative.],
  [Fixed-meaning evidence fibre],
    [Pointwise CCC of evidence transformers.],
    [The global presentation category is not cartesian; zero-resource laws are not cost laws.],
)

An arithmetic backend for an arbitrary CCC would still require a computable
assignment of objects and arrows, a stated equality notion, faithfulness,
CCC-structure preservation, and honest resource bounds for composition, evaluation,
curry, and equality checking. The development now gives a semantic solution for all
small CCCs, an exact arithmetic classification for the locally finite ones, a sharp
uniform-width no-go, and a certified way to combine selected presentations. It does
not collapse those four results into one impossible universal circuit.
