// =============================================================================
// Section 3: Authority as constructive knowledge
// =============================================================================

#import "../defs.typ": lean
= Authority as constructive knowledge <sec-authority>

== The thesis

A capability is a piece of constructive knowledge: to hold one is to be able to
exhibit a witness that authorizes an act --- never merely to assert it. The
capability graph is a distributed knowledge graph. Nodes are cells --- knowers
with private state and a program. Edges are capabilities --- directed facts
("this cell can constructively demonstrate authority over that one") carrying
attenuated rights. The graph is partial and local: there is no global registry
of who-may-do-what; one learns of an edge only when someone presents a witness
for it, at the point of use.

The organizing asymmetry of @sec-intro is the realizability reading of
intuitionistic logic made operational: proof-checking is cheap and trusted;
proof-search is undecidable and untrusted. Every trust decision is a check.
Whoever wants to act bears the burden of producing the witness; whoever guards
state only ever verifies. A capability is not a key in a lock --- it is a proof
obligation one can discharge.

== The demand $tack.l$ supply adjunction

Each action is judged by a matched pair: the target cell *demands*
`AuthRequired` (a predicate); the action *supplies* a witnessed `Authorization`.
Admissibility is `Verify P w` --- the counit of the $"Predicate" tack.l "Witness"$
adjunction, whose Galois connection is carried in `Dregg2/Laws.lean`. Guards
(the guard algebra) are more predicates over the same step, each either first-party
(decidable now) or witnessed (a registered verifier discharges it). The signed
binding to the canonical message pins the witness to this exact step, so an
authorization proved for one context cannot be replayed into another.

== The production law

The characteristic --- and easily-missed --- fact: *authority is produced, not
merely spent.* A model in which every step only narrows (a monotone descent down
a meet-semilattice) is _wrong_: it forbids exactly the patterns that give
capabilities their power. The real dynamics have a generative half and a
restrictive half, disciplined by one law.

*Generative (the graph grows):*

- *Introduction* (Granovetter): a holder of an edge to Carol grants Bob a _new_
  edge to Carol. Enforced non-amplifying (the conferred edge $lt.eq$ the
  introducer's own), consensual, and time-bounded.
- *Rights amplification*: a held amplifier combines with another fact to yield
  access neither names alone --- the sealer/unsealer pair
  ($"unsealer" times.o "sealed-box" tack.r "contents"$), the brand, the
  mint. It does not break the discipline precisely because the amplifier is
  connectivity already held.
- *Powerbox / mint / factory*: a designated authority creates fresh edges or
  resource on an authorized gesture --- the legitimate point where new authority
  enters.
- *Parenthood / endowment*: creating a cell endows the child.

*Restrictive (the graph narrows):*

- *Attenuation* narrows the rights on one existing edge (a caveat, a facet
  subset). The narrow-only rule governs _one edge's rights_; it is not the law
  of the whole system.
- *Revocation / expiry* removes an edge (epoch-bump; one-way).

*The one law:* Miller's _only connectivity begets connectivity_. There is no
ambient authority; every generative act is itself authorized by held knowledge;
and generative and annihilative acts are receipt-disclosed --- the conservation
typing forces them onto the chain, un-strippably. Authority grows, but only
through authorized, *non-forgeable* construction. This is an epistemic
non-forgeability invariant, not a lattice descent.

Mechanized: #lean("Metatheory.no_forge_step") (the candidate-independent law);
#lean("EffectsAuthority.introduce_non_amplifying") (a conferred capability is a
genuine subset of the held one, over the real attenuation lattice);
#lean("EffectsAuthority.amplifying_grant_rejected") (the teeth: a grant
conferring authority the holder lacks is rejected --- the predicate is
two-valued); #lean("AuthModes.captp_granted_le_held") (the dispatcher gate on
delivered handoffs); #lean("FullForestAuth.execFullForestG_no_amplify") (every
delegation edge of a committed forest, at the running entry).

== Three logics over a step

Each turn is judged by three orthogonal logics.

+ *Conservation --- substructural / linear.* Resources cannot be copied or
  discarded for free; generative and annihilative moves are disclosed exceptions
  bound into the receipt. Linear logic's structural rules, read as a security
  law: no inflation, no loss.
+ *Ordering --- temporal / modal.* When is a fact final? A finality lattice over
  one Merkle-CRDT DAG; effects commit at the join of the written cells' tiers and
  never downgrade. "Knowledge becomes common knowledge" is the modal ascent
  (the ordering logic).
+ *Independence --- the confluence lattice.* Which concurrent inferences commute?
  The join-semilattice of invariant-preserving merges --- the coordination-free
  fragment, which the guard algebra's coordination dial computes (the guard algebra).

== Crossing a trust boundary

Inside a trust root, authority is *positional*: holding the edge is the proof,
and the mediator enforces it. Across a boundary it becomes *epistemic*: one must
present a verifiable witness, because the far side shares no mediator. The
crossing is a named-lossy functor --- _permission survives, authority does not_
--- and the loss is load-bearing: confinement and revocable-forwarding are
dropped, which is why a forwarded capability is revocable _by construction_. A
hosted cell's full state lives with its host; a *sovereign* cell keeps only a
commitment and proves its own transitions, so a far federation admits it knowing
only how to check a proof, never how to re-run the cell.
