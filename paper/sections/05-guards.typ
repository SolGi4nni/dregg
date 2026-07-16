// =============================================================================
// Section 5: The guard algebra
// =============================================================================

#import "../defs.typ": lean
= The guard algebra <sec-guards>

Everything that constrains a turn is one algebra of decidable predicates over
the proposed step. The guard the executor evaluates and the obligation a proof
discharges are compiled from the same object: an installable guard and a
provable property are one mechanism. This section gives the algebra, its
closures, its compiled form, and the two prices it computes.

== One guard, four polarities

A guard is one object (#lean("Spec.Guard")):

```
Guard = firstParty(p) ⊕ all/any/not ⊕ witnessed(s)
```

A *first-party* branch is decidable now, against the old and new state. A
*witnessed* branch defers its statement to the verify seam
(#lean("Spec.Guard.admits")). That seam is the single site where external
evidence enters the grammar; a third-party discharge, a range proof, and an
arbitrary proof-carrying claim all arrive there. The novelty is not the grammar
but its reach: the one algebra appears at four *polarities* that are four
separate mechanisms in most systems.

#figure(
  table(
    columns: (auto, auto),
    align: (left, left),
    table.header([*polarity*], [*the predicate is imposed on*]),
    [*caveat*], [_delegated_ power --- a restriction travelling with a capability],
    [*program constraint*], [_owned_ state --- the cell's self-imposed law],
    [*precondition*], [a _turn_ --- what an action requires to be admissible],
    [*intent demand*], [the _world_ --- the typed hole `hole(Pred)` a counterparty's fulfillment discharges (@sec-model)],
  ),
  caption: [The four polarities of one predicate algebra. A caveat on a
    macaroon, a smart-contract invariant, a transaction guard, and an
    open-order condition are one mechanism here.],
)

Because the four are one object, a caveat is checkable by the proof system, not
only by the issuing service; an intent demand is the same kind of fact as a cell
program; and a precondition compiles to a circuit obligation exactly as an
invariant does. An intent is the demand polarity made first-class: a fulfillment
supplies the witness that closes the hole, and the counit of @sec-authority's
demand $tack.l$ supply adjunction is what discharges it.

== The grammar and its closures

The first-party atoms are small decidable shapes over a cell's slots ---
equality, bounds, write-once, immutability, monotone updates, deltas, sums,
allowed-transition automata, membership, prefix, and typed identity atoms over
symbol and digest slots. The catalog of record is the
#lean("Exec.StateConstraint") inductive; the executor's Boolean algebra over it
(#lean("PredAlgebra.Pred"), evaluated by #lean("PredAlgebra.Pred.eval")) closes
the atoms under negation, conjunction, and n-ary disjunction at every level.
Two further closures keep the grammar from ossifying into axis-aligned special
cases.

*Relational closure* (`Authority/RelationalClosure.lean`). Any affine relation
over the post-state --- $"head" lt.eq "tail" + "capacity"$, $Sigma "slots" =
"const"$ --- is the same predicate object (#lean("RelationalClosure.RelPred")),
with #lean("RelationalClosure.ofFieldLteOther_eq") recovering the single-slot
atoms as instances. There is no new atom per shape: the guard language is the
internal predicate logic of the state object, bounded only by decidability and
circuit-expressibility.

*Quantified closure* (`Authority/QuantifiedPredicate.lean`). Bounded $forall$ and
$exists$ over slot ranges compile to the relational closure with a proven
constraint budget: #lean("QuantifiedPredicate.compile_sound") welds the compiled
form to the quantified meaning, and #lean("QuantifiedPredicate.andFold_budget") /
#lean("QuantifiedPredicate.orFold_budget") bound the cost. Quantifiers cost what
they cost, and the cost is a theorem.

== The compiled form

The comparison atoms compile to circuit descriptors authored in Lean, not to
circuits authored beside the kernel. The threshold descriptor
(#lean("PredicatesArithmeticEmit.predicateGeDesc"), registered as
`dregg-predicate-arith-ge::threshold-v1`) is representative. It proves a
conjunction with a shared variable: the compared value satisfies $"value"
gt.eq "threshold"$ for a public threshold, *and* the public fact commitment
hashes over the same column being compared, binding the claim to committed
token state. Without the shared column the circuit would prove an inequality
about a number the prover chose. The comparison refuses by range: the circuit
range-proves $"diff" = "value" - "threshold"$ into $[0, 2^29)$, and a
$"value" < "threshold"$ witness wraps `diff` far outside that interval in the
field, where no limb decomposition exists.

The descriptor bytes are pinned twice. The Lean source pins its own emitted
wire string with a `#guard`, and an emit gate
(`circuit-prove/tests/predicates_arithmetic_emit_gate.rs`) embeds the identical
string, proves an honest witness through the node's one proving entry
(@sec-proofs), and runs mutation canaries that each tamper one thing and
assert the refusal bites the named constraint. Sibling descriptors cover the
$<$, $lt.eq$, $>$, $eq.not$, and in-range atoms, the relational and compound
forms, and the temporal predicate, each with its own gate. Descriptor installs
are recorded in the append-only regeneration log (`docs/VK-REGEN-LOG.md`); the
predicate-arithmetic family's current registry entry is the 2026-07-16 row.

== The coordination dial

Guards carry a coordination price, and the system computes it
(`Authority/ConfluenceClassifier.lean`) rather than assuming it. Two concurrent
turns merge without coordination exactly when their guards are
*confluence-stable* --- the invariant survives merging independently-taken steps.
The classifier is the independence logic of @sec-authority landing in the guard
language:

- #lean("ConfluenceClassifier.keeps_iff_coordinationFree") --- a guard preserves
  confluence if and only if it runs coordination-free;
- #lean("ConfluenceClassifier.monotone_keeps") --- monotone thresholds are free;
- #lean("ConfluenceClassifier.bounded_breaks") /
  #lean("ConfluenceClassifier.bounded_forces_ordering") --- an upper bound forces
  ordering (consensus).

The classifier does not forbid the expensive case; it *prices* it. A
confluence-stable guard runs coordination-free; a guard that is not provably so
forces ordering, and the difference is reported, not legislated.

== The disclosure dial

The second computed price is disclosure: how much a guard reveals while being
checked. The principle is that what the proof does not need, it does not ask to
see. The ladder, most to least disclosed:

#figure(
  table(
    columns: (auto, auto),
    align: (left, left),
    table.header([*rung*], [*what the guard sees*]),
    [*cleartext*], [the predicate reads values directly],
    [*committed*], [values behind Pedersen commitments; conservation checks
      homomorphically without opening],
    [*range-proved*], [only the bound is disclosed],
    [*jointly garbled*], [two parties evaluate a shared gate over private inputs
      and learn the verdict and nothing else],
  ),
  caption: [The disclosure dial. Each rung is an evaluation mode of the *same*
    predicate; the law is rung-invariant.],
)

The ladder is mechanized so that privacy never changes the law it checks.
Committed evaluation checks conservation homomorphically
(#lean("PrivatePredicate.private_conservation_checks_homomorphically")), and the
committed and cleartext judgments provably agree
(#lean("Spec.committed_iff_cleartext")) --- moving down the dial hides inputs, not
verdicts. A range proof discloses only the bound
(#lean("RangeProof.disclosure_only_the_bound"),
#lean("RangeProof.committed_inequality_via_range")). The garbled rung lets two
parties evaluate one gate over private inputs
(#lean("GarbledJoint.garbled_input_private"),
#lean("GarbledJoint.joint_turn_private_gate")), and its disclosure floor is
acceptance-only --- the verdict and nothing else
(#lean("GarbledJoint.garbledDialFloor_is_bot")). This rung's proof path is the
same descriptor prover as every other: the garbled-evaluation descriptor is
authored in Lean (#lean("GarbledEvalEmit.garbledEvalDesc")), byte-pinned there,
and mutation-gated in `circuit-prove/tests/garbled_eval_emit_gate.rs`. The
descriptor proves the decryption algebra over the garbled tables; the
Poseidon2 garbling-hash binding is a named carrier computed by the executor,
and @app-garbled gives the construction and its scope.

Selective disclosure of a receipt --- hide, reveal, predicate,
committed-threshold --- is the same dial applied to *Q* (@sec-proofs): a
projection of the receipt, not a second copy of it. Disclosure and proof are one
object viewed at a chosen resolution.
