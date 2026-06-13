// =============================================================================
// Section 1: Introduction
// =============================================================================

#import "../defs.typ": lean
= Introduction <sec-intro>

A distributed object-capability substrate has one hard problem: a party who was
not present when a transition happened must be able to trust that it happened
correctly. dregg answers it by making the proof witness the protocol's *correct
evolution*. A verifier holding one aggregate root --- a new node, an auditor, a
phone --- learns that every state transition in the system's history was
authorized, conserved value exactly, and was committed faithfully, while
re-executing nothing and trusting no executor. This is the requirement
everything else is derived from, and we name its negation the thing the design
rules out: a light client cannot be fooled by a server that ran the protocol
wrong.

== The sentence

The whole system is one sentence, given algebra:

#align(center)[
  _A turn is the exercise of an attenuable, proof-carrying token over owned
  state, leaving a verifiable receipt._
]

State lives in *cells*. A *turn* exercises authority --- a *token* that may be
*attenuated* on every axis and that carries a *proof* of its own legitimacy ---
over *owned state*, and leaves *Q*, a receipt that commits to the result. The
nouns are fixed in @sec-model; the authority logic in @sec-authority; the
receipt and its aggregation in @sec-proofs.

== The organizing asymmetry

dregg treats authority as *constructive knowledge*. To hold a capability is to
be able to exhibit a witness that authorizes an act --- never merely to assert
it. This is the realizability reading of intuitionistic logic made operational,
and it rests on one asymmetry:

#align(center)[
  _proof-checking is cheap and trusted; proof-search is undecidable and untrusted._
]

Every trust decision in the system is a *check*. Whoever wants to act bears the
burden of producing a witness; whoever guards state only ever verifies. A
capability is not a key in a lock --- it is a proof obligation one can
discharge. The asymmetry places search at the untrusted edges (solvers, intent
matchers, provers) and checking at the trusted core (the executor, the circuit,
the light client). It is the same asymmetry that lets a STARK verifier accept a
statement it could not have found: the prover does the work, the checker does
the trusting.

== What the kernel governs

The kernel governs four *substances*, each with a discipline of use --- a law
about how it may move through time --- and the kernel is the enforcement of
those laws. Value is *linear*: per asset, the resource sum is exactly zero
across a turn, so nothing is minted or burned outside an issuer's supply
discipline. Authority is *produced under non-forgeability*: it grows, but only
by authorized, receipt-disclosed construction from connectivity already held,
and narrows freely along one edge. Evidence is *monotone*: once known, never
unknown --- the nullifier and commitment ledgers only grow. State is
*guarded-mutable*: it changes only under a predicate, only by its owner.

The kernel's signature is *eight verbs*, each the structural rule of one
substance's discipline. The assignment of (substance, polarity) to verbs is
injective, so minimality is a theorem (#lean("VerbRegistry.minimality"),
#lean("VerbRegistry.each_verb_irreplaceable")): drop any verb and the behavior
it provides has no other provider. The verb roster is enumerable and lives in
the generated verb catalog (`studio/verb-catalog.generated.json`), drift-checked
against the verified registry; the paper cites it rather than re-asserting it.

== Constructive authority is generative

The easily-missed fact about object-capability authority is that it is
*produced*, not merely spent. A model in which every step only narrows --- a
monotone descent down a lattice --- forbids exactly the patterns that give
capabilities their power: a holder introducing a third party (Granovetter), an
unsealer combining with a sealed box to yield contents neither names alone, a
mint creating fresh resource on an authorized gesture. dregg's central authority
law is therefore generative *and* disciplined: authority grows, but every
generative act is itself authorized by held knowledge and is receipt-disclosed,
so it lands on the chain un-strippably. Miller's *only connectivity begets
connectivity* is the one law (@sec-authority); it is an epistemic
non-forgeability invariant, not a lattice descent.

== One constraint algebra, two computed prices

Everything that constrains a turn --- a caveat on delegated power, a program on
owned state, a precondition on a turn, a demand on the world --- is one algebra
of decidable predicates over the proposed step. The same predicate the executor
evaluates is compiled to the circuit obligation a proof discharges: an
installable guard and a provable property are one mechanism. Two prices are
*computed*, not assumed. The *coordination dial* classifies whether two
concurrent turns merge without coordination: a confluence-stable guard runs
coordination-free, one that is not provably so forces ordering, and the
classifier prices the difference honestly rather than forbidding the expensive
case. The *disclosure dial* governs how much a guard reveals while checking ---
cleartext, committed, range-proved, jointly-garbled --- on the principle that
what the proof does not need, it does not ask to see (the guard algebra).

== The proofs are about the thing that runs

The semantics are a Lean 4 development that is *also the deployed executor*. The
gated whole-forest step #lean("execFullForestG") is compiled, exported through
FFI as `dregg_exec_full_forest_auth`, and invoked by the node on its production
path; the running-entry guarantee is stated over exactly this function, so "the
proofs are about the thing that runs" is a theorem
(#lean("FullForestAuth.running_entry_sound")), not a deployment note. The proof
system inherits the same discipline: the circuit is *emitted from* the kernel,
not hand-authored beside it. Each kernel statement carries a descriptor from
which both the executor reading and the circuit reading are obtained, with
agreement theorems welding them (#lean("Argus.Receipt.argus_circuit_executor_receipts_agree")).
One term has two provably-agreeing readings; no constraint is authored in Rust.

== The assurance case is an artifact

The system's guarantees are not a narrative but a Lean file
(`metatheory/Dregg2/AssuranceCase.lean`) that states five guarantees ---
authority, conservation, integrity, freshness, unfoolability --- plus a running
entry that closes them over the deployed function, assembles under each the
keystone DAG that discharges it, and `#assert_axioms`-pins every name: the build
fails unless each theorem's full axiom set is exactly the kernel triple
${"propext", "Classical.choice", "Quot.sound"}$. Everything rests on that triple
plus an explicit floor of eight cryptographic and liveness carriers, entering as
hypotheses rather than axioms (the assurance case). There is no trusted executor, no
out-of-band "this was authorized" premise, and no field of the post-state left
uncommitted.

== Applications inherit theorems

Applications do not extend the kernel; they are cells. A *factory* publishes a
descriptor --- a slot layout plus predicate constraints --- and the `create`
verb mints cells from it; from that moment the executor enforces the program on
every turn touching the cell. Recurring coordination shapes (escrow,
obligations, queues, mailboxes, bridges, sealer/unsealer boxes) ship as verified
factories whose safety keystones are kernel theorems, so an application's
contract is *inherited* from the kernel rather than re-established per app.
(the realization). The shape is uniform: value at stake lives in the minted
cell's own balance column, so funding and settling are ordinary moves and
conservation is the ordinary kernel law with no side tables.
