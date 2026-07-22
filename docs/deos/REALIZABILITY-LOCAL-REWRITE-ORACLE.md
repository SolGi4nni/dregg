# Realizability descent for local-rewrite proof oracles

Status: formalized, kernel-clean, finite reference instance checked.

Lean authority:
`metatheory/Dregg2/Metatheory/RealizabilityLocalRewriteOracle.lean`.

## Result

The new construction makes the realizability/topos direction operational without
claiming that categorical structure is a cryptographic proof system.

Start with four assemblies over a relational PCA:

- `Query`, a represented local address;
- `RawWitness`, an intensional proof representation;
- `Family`, the semantic witness obtained after forgetting representation choices;
- `View`, the result of one local observation.

An `EffectiveLocalOracle` supplies an effective cover

```text
RawWitness --quotient--> Family
```

and a uniformly PCA-tracked local observer

```text
Query × RawWitness --rawObserve--> View.
```

The observer must be invariant when the query is unchanged and two raw witnesses
have the same semantic quotient. The formal construction lifts the effective cover
through the query product, proves the corresponding kernel-pair equation, and applies
effective-cover descent:

```text
Query × RawWitness --queryQuotient--> Query × Family
        |                                  |
        | rawObserve                       | semanticObserve
        v                                  v
       View -----------------------------> View
```

The bottom arrow is the identity. Lean proves both the commuting equation

```text
queryQuotient ≫ semanticObserve = rawObserve
```

and uniqueness of `semanticObserve` among tracked assembly morphisms satisfying it.
This is a genuine bridge: executable realizers descend a local proof oracle across a
regular cover. It is not just a Set-level quotient or an analogy with sheaves.

## Logic and query protocol

For a Boolean-valued observer, invalidity means that some finite query rejects. The
descended observer induces:

1. a finite `CoveragePresentation` whose bad set consists of rejecting queries;
2. a realizability-valued obstruction predicate, classified exactly by the existing
   `UFam` generic predicate; and
3. a transparent reference `PresentedProtocol` whose local test is faithful to that
   coverage presentation.

Nothing in this step requires a finite field, an arithmetization, or a polynomial
commitment. The proof representation can be a graph, local rewrite trace, interaction
net, proof net, evaluator receipt, or another represented object, provided its local
observer is tracked and representation-invariant.

## Non-polynomial finite witness

The checked reference instance is a two-row interaction-net oracle. Each row contains
an exposed `before` graph, a local certificate, and an `after` graph from
`InteractionNetTrace`; its query is simply a row index.

- The good oracle contains the two accepted reductions from the existing reference
  trace and has no rejecting query.
- The bad oracle replaces the second row with the same rule at the wrong location.
  It is invalid and has exactly one rejecting query.
- Under two independent uniform queries, the honest transparent reference accepts
  the bad oracle on exactly one of the four query vectors. Lean proves the exact count
  is `1`, using the generic miss-set counting theorem.

The raw witness also carries a redundant padding bit. The effective cover erases it,
and the theorem proves the descended result is exactly the direct local checker. This
makes fibre invariance nonvacuous rather than taking the quotient to be the identity.

The one-point PCA used by this finite witness establishes consistency and exercises
the categorical interfaces; it is not a performance model or a compiler backend.

## Cryptographic boundary

The formalized descent theorem supplies only the local-to-semantic factorization. A
succinct deployed protocol still needs independent theorems or assumptions for:

- commitment or vector-commitment binding;
- transcript generation and Fiat--Shamir/RO sampling;
- an acceptance reduction from the deployed verifier to the local test;
- OOD error, if an algebraic extension-domain reduction is used;
- FRI/low-degree error, if polynomial proximity testing is used;
- serialization, domain separation, and implementation refinement.

The transparent reference digest is the entire family. Its point binding is therefore
information-theoretic but non-succinct. Replacing it with Merkle openings, FRI, a
PCP/IOP, a graph commitment, or another oracle technology is an explicit backend
obligation. Categorical descent does not manufacture those guarantees.

## Why this generalizes the FOL-to-polynomial pitch

The robust primitive is not first-order logic and not polynomial syntax. It is a
represented witness with a finite, invariant local observation interface, plus a
separate argument that invalid global objects expose local obstructions. Polynomial
arithmetization is one possible realization of the observer; interaction-net rows are
another. This separation preserves the useful local-query idea while avoiding the
false inference that logical classification alone supplies a commitment, an IOP, or
FRI soundness.

