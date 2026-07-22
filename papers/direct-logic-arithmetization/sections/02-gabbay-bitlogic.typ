= Audit of the direct FOL arithmetization claim

This section separates three statements that are easy to conflate: Gabbay's
characteristic-zero semantics, a finite-field implementation of that semantics,
and the equations printed in the public ModulusZK/BitLogic whitepaper. The
algebraic kernel of the first is sound in its stated model. A direct finite-field
port is not sound without an additional invariant or gadget. More strongly,
the published BitLogic encoding is not a finite-field implementation of
Gabbay's theorem: it changes the semantic domain and reverses every connective
and finite quantifier fold used by that theorem. These are constructive
specification findings:
they neither allege bad intent nor establish a vulnerability in a deployed
system.

The primary Gabbay source is the official
#link("https://eprint.iacr.org/2024/954")[ePrint 2024/954 record], last revised
12 February 2026 and published in the _Journal of Applied Logics_ 12(6),
1481--1548 (2025). Numbered references below follow the current ePrint text;
theorem numbers, rather than unstable viewer page counts, are the primary
locators. The BitLogic source is the 14-page PDF in the official
#link("https://github.com/ModulusZK/BitLogic-from-Modulus-zkFOL-Bitcoin")[public
repository]. Its
#link("https://github.com/ModulusZK/BitLogic-from-Modulus-zkFOL-Bitcoin/tree/26f125b37f0442d92991e3066095b1dfeb1b0ce4")[pinned
tree at commit `26f125b37f0442d92991e3066095b1dfeb1b0ce4`]
(21 November 2025) contains exactly that one PDF blob.

== What Gabbay actually proves

Gabbay interprets predicates as polynomials in $QQ[X]$ whose values on
$QQ$ are nonnegative. Zero denotes truth. Figure 2, defining the semantics in
Definition 2.2.8, assigns addition to
conjunction and bounded universal quantification, and multiplication to
disjunction and bounded existential quantification:

#align(center)[
  $ R(phi and psi) = R(phi) + R(psi), quad
    R(phi or psi) = R(phi) R(psi), $
]
#align(center)[
  $ R(forall x in H. phi(x)) = sum_(x in H) R(phi(x)), quad
    R(exists x in H. phi(x)) = product_(x in H) R(phi(x)). $
]

Definition 2.3.1 states the pointwise nonnegativity condition. Lemma 2.3.2
proves that predicate denotations preserve it. Theorem 2.3.4 is the
soundness-and-completeness theorem, and Remark 2.3.5 identifies its
load-bearing arithmetic facts:

#align(center)[
  $ a >= 0, b >= 0 ⇒ (a+b=0 ⇔ a=0 and b=0), $
]
#align(center)[
  $ a b=0 ⇔ a=0 or b=0. $
]

Thus the theorem is not a theorem that arbitrary field-valued residuals may be
combined by the same operations. It is an exact theorem about zero sets under
a protected nonnegative, characteristic-zero interpretation.

We machine-checked this algebraic kernel, rather than re-formalizing every
matrix and syntactic feature of the source paper. In
`FOLArithmetizationCorrected.lean`, the structure `ZeroTrueLaws` makes the
noncancellation and no-zero-divisor obligations explicit.
`PositiveFormula.residual_eq_zero_iff` proves exact compilation for the positive
Boolean fragment; `PositiveFormula.residual_all_eq_zero_iff` and
`PositiveFormula.residual_any_eq_zero_iff` prove the corresponding finite
quantifier folds. The instance `nonnegativeRationalLaws` discharges precisely
Gabbay's nonnegative-rational obligations. This scope distinction matters: our
Lean theorem validates the algebraic core used here, not every later
construction in ePrint 2024/954.

== Why the naive finite-field port fails

A finite field has no positivity order compatible with its ring operations, and
nonzero summands can cancel. Gabbay explicitly records this limitation in
Remark 6.3.3 ("Why Q?"): the zero-sum property used by
addition-as-conjunction is lost in a prime field. The proposed cryptographic
route is to establish the polynomial equality over $QQ[X]$ first and only then
map that equality into a suitably large prime field. It is not a direct
finite-field truth semantics, and the rational proof does not transfer
unchanged.

The failure already occurs in BabyBear, the prime field with
$p = 2,013,265,921$. Let $r = 1,728,404,513$. Lean verifies

#align(center)[
  $ r^2 = -1 mod p, quad 1 != 0, quad r^2 != 0, quad 1+r^2=0. $
]

Taking squared equality residuals gives the concrete false conjunction

#align(center)[
  $ R(0=1)=1, quad R(0=r)=r^2=-1, quad
    R((0=1) and (0=r))=0. $
]

Both atoms are false under zero-means-true, yet their sum accepts. The exact
certificate is `FOLArithmetizationCounterexamples.babyBear_false_and_false_accepted`;
`babyBear_sqrt_neg_one` certifies the field identity, and
`babyBear_false_forall_accepted` lifts the same pair to a two-point universal
quantifier. This is not a low-probability collision: it is an explicit witness.
Nor is $1-R(phi)$ a general repair for negation before Booleanization;
`babyBear_one_sub_is_not_general_negation` gives the residual $R(phi)=2$, for
which both $R(phi)$ and $1-R(phi)$ are nonzero.

Two exact finite-field repairs are already formalized. First, compile in
nonnegative integers and prove that the complete residual is strictly below the
field modulus before casting. `zmod_natCast_eq_zero_iff_of_lt` is the no-wrap
lemma, and `natural_residual_cast_sound` is the compiler theorem. Second,
reify each arbitrary residual $r$ as a Boolean false-bit $b$ with inverse
witness $z$:

#align(center)[
  $ r(1-b)=0, quad r z=b. $
]

The constraints force $b in {0,1}$ and $b=0 ⇔ r=0$, proved by
`falseBit_eq_zero_iff`, `falseBit_is_bit`, and `exists_falseBitWitness`. Once
Booleanized, exact connectives are

#align(center)[
  $ b_(phi and psi)=b_phi+b_psi-b_phi b_psi, quad
    b_(phi or psi)=b_phi b_psi, quad b_(not phi)=1-b_phi. $
]

`BooleanFormula.falseBit_correct` proves, for every formula in this Boolean
core, both that the output remains a bit and that it is zero exactly when the
source formula holds. These repairs have real costs---static bound certificates
in the first case, and witness equations plus Boolean connective gates in the
second---so they must be included in any performance comparison.

== The BitLogic connective reversal

The public BitLogic PDF states on p. 4 that conjunction maps to product and
disjunction to sum. Section 7.1 (p. 10) repeats that map and additionally maps
bounded universal quantification to product and existential quantification to
sum. Under zero-means-true, this reverses the intended logic even in an integral
domain:

#align(center)[
  $ P_phi P_psi=0 ⇔ P_phi=0 or P_psi=0. $
]

Accordingly, a product recognizes disjunction, not conjunction. The Lean theorem
`FOLArithmetizationCounterexamples.zero_of_mul_iff_or` proves this generic fact.
The finite-list regressions `product_is_not_zero_true_forall` and
`sum_is_not_zero_true_exists` show both quantifier errors: the product
$0 dot 7$ accepts a purported universal despite one false point, while the sum
$1+(-1)$ accepts a purported existential despite having no zero residual.

The issue is visible in the swap relation printed in Section 4.1 (p. 6). Writing
$q=f(k,s)$ for the quoted output, the PDF defines

#align(center)[
  $ P_"swap" = (A'-A+k)(B'-B-q)(A B-A' B') $
]

and accepts when $P_"swap"=0$. Because this is a product, any one satisfied
factor bypasses the other two. For example, over the integers choose

#align(center)[
  $ A=B=10, quad k=q=1, quad A'=9, quad B'=999. $
]

Then

#align(center)[
  $ A'-A+k=0, quad B'-B-q=988 != 0, quad
    A B-A' B'=-8,891 != 0, $
]

so the printed relation accepts while its price/output and constant-product
conditions both fail. This calculation is checked by
`published_swap_accepts_invalid_witness`. More generally,
`published_swap_first_factor_bypasses_rest` proves the bypass in every
commutative ring, and `published_swap_bypass_is_polynomial_identity` proves

#align(center)[
  $ P_"swap"(A,B,A-k,B',k,q)=0 $
]

for all remaining inputs. Random evaluation cannot detect constraints erased by
an identically zero factor; Schwartz--Zippel bounds a nonzero polynomial's
accidental zeros, not a relation that is already the zero polynomial after the
witness substitution.

#text(size: 7.5pt)[
  #table(
    columns: (0.9fr, 1.25fr, 1.05fr, 2.8fr),
    inset: 4pt,
    stroke: 0.35pt,
    table.header(
      [*Construction*], [*Connectives (zero is true)*],
      [*Finite quantifiers*], [*Established scope*],
    ),
    [Gabbay, Thm. 2.3.4],
    [$and mapsto +$; $or mapsto times$],
    [$forall mapsto sum$; $exists mapsto product$],
    [Exact for pointwise nonnegative $QQ[X]$ denotations (formal theorem above).],
    [BitLogic PDF, pp. 4, 10],
    [$and mapsto times$; $or mapsto +$],
    [$forall mapsto product$; $exists mapsto sum$],
    [Fails the connective and quantifier counterexamples above.],
    [No-wrap field repair],
    [Gabbay map, then bounded cast],
    [Gabbay folds, then bounded cast],
    [Exact under a proved residual bound; Lean:
     `natural_residual_cast_sound`.],
    [Boolean field repair],
    [$and mapsto a+b-a b$; $or mapsto a b$],
    [Boolean folds],
    [Exact over fields after atom reification; Lean:
     `BooleanFormula.falseBit_correct`.],
  )
]

The authors' May 2026 CTB workshop slides make the implementation direction
more concrete: they move through natural/integer semantics, bit decomposition,
Booleanity constraints, and a Zinc integer AIR. The slides explicitly set
range checks aside in the presented sketch and list direct finite-field
arithmetization and a non-toy implementation as future work. This is useful
convergence on the repair obligations above, not support for omitting them. Our
construction program therefore treats bounds, Booleanity, and range evidence as
first-class compiler outputs rather than prose side conditions.

== Evidence boundary and constructive next step

As of 22 July 2026, the named public BitLogic repository's pinned tree contains
exactly one 14-page PDF. It contains no executable source, build manifest,
compiler, witness generator, prover, verifier, release, parameter set,
benchmark harness, proof corpus, or raw measurement. The PDF names the real,
third-party Zinc/Zip proving stack, but the public search found no Modulus
FOL-to-Zinc compiler, proof-format adapter, or verifier integration. This is a
reproducible statement about the named public artifacts, not a claim about
private or differently named work. Consistently, the whitepaper's Phase I
roadmap (Section 9.1, p. 13) lists implementing the compiler and verifier and
benchmarking polynomial-evaluation costs as work for 2025--2026.

The public performance claim is also not one stable metric. The
#link("https://www.moduluszk.io/")[current site] applies “10--100x” to cost and
adds “1--3 second finality”; a
#link("https://www.globenewswire.com/news-release/2025/11/13/3187707/0/en/moduluszk-from-cult-dao-announces-silent-heroes-airdrop.html")[project-supplied
13 November 2025 release] gives proof-price ranges; the
#link("https://moduluszk.medium.com/modulus-story-the-courage-to-build-differently-acb65b8df656")[20
October 2025 project history] instead says 10x faster and 90% smaller; and a
#link("https://x.com/ModulusZK/status/1995501494041514372")[1 December 2025
post] says 10--100x smaller proofs. Cost, proof size, prover time, and finality
are different quantities. We found no public workload corpus, proof-system and
security parameters, comparison implementation, hardware manifest, harness,
or raw samples that bind any of them to the advertised multiplier.

“Finality” itself needs a tier. The official
#link("https://docs.moduluszk.io/glossary")[Modulus glossary] distinguishes a
trusted state committed by its single trusted sequencer, a virtual state whose
batches have reached L1, and a consolidated state proven on L1 by a ZKP. It
attributes fast or instant finality to the trusted sequencer and one-transaction
L2 blocks. Without identifying one of these states, the site's 1--3 second
figure is not a reproducible settlement or proof-latency measurement.

There is now a useful first-party disclosure boundary. In a
#link("https://x.com/ModulusZK/status/2079611667067900154")[21 July 2026 public
reply], Modulus wrote: “There are major ones. Just announcing tech breakthroughs
without the open source code is generally frowned upon ...” The same reply explains
that commercial and internal positioning precedes publication. We therefore do
not infer that private work is absent, nor that it matches the PDF. The decisive
claim in this report is narrower: the one published BitLogic relation is not
Gabbay's finite-field construction and fails its stated source logic.

Therefore we report a specification-level counterexample, not a production
exploit and not a measured performance result. A deployed implementation could
use different equations; publishing its compiler, proof interface, and verifier
would resolve the discrepancy. The shared opportunity is an open conformance
suite containing the examples above, corrected no-wrap and Booleanized
lowerings, conventional circuit baselines, and identical proof-system
parameters. Soundness is the admission gate; only implementations that agree on
the source truth table should enter a latency, size, finality, or cost chart.
