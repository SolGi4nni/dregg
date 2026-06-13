# 2 · Authority as constructive knowledge

## 2.1 The thesis

**A capability is a piece of constructive knowledge: to hold one is to be
able to exhibit a witness that authorizes an act — never merely to assert
it.** The capability graph is a distributed knowledge graph: nodes are cells
(knowers with private state and a program); edges are capabilities (directed
facts — "this cell can constructively demonstrate authority over that one" —
carrying attenuated rights); and the graph is partial and local. There is no
global registry of who-may-do-what; you learn of an edge only when someone
presents a witness for it, at the point of use.

The organizing asymmetry is the BHK/realizability reading of intuitionistic
logic made operational: **proof-checking is cheap and trusted; proof-search
is undecidable and untrusted.** Every trust decision in the system is a
check. Whoever wants to act bears the burden of producing the witness;
whoever guards state only ever verifies. A capability is not a key in a lock
— it is a proof obligation you can discharge.

## 2.2 The demand ⊣ supply adjunction

Each action is judged by a matched pair: the target cell *demands*
`AuthRequired` (a predicate); the action *supplies* a witnessed
`Authorization`. Admissibility is `Verify P w` — the counit of the
`Predicate ⊣ Witness` adjunction (`Dregg2/Laws.lean` carries the Galois
connection). Guards (§3) are more predicates over the same step, each either
first-party (decidable now) or witnessed (a registered verifier discharges
it). The signed binding to the canonical message pins the witness to this
exact step.

## 2.3 The production law

The characteristic — and easily-missed — fact: **authority is produced, not
merely spent.** A model in which every step only narrows (a monotone descent
down a meet-semilattice) is *wrong*: it forbids exactly the patterns that
give capabilities their power. The real dynamics have a generative half and a
restrictive half, disciplined by one law.

**Generative (the graph grows):**

* **Introduction** (Granovetter): a holder of an edge to Carol grants Bob a
  *new* edge to Carol. Enforced non-amplifying (the conferred edge ≤ the
  introducer's own), consensual, and time-bounded.
* **Rights amplification**: a held amplifier combines with another fact to
  yield access neither names alone — the sealer/unsealer pair
  (`unsealer ⊗ sealed-box ⊢ contents`), the brand, the mint. It does not
  break the discipline precisely because the amplifier is connectivity you
  already hold.
* **Powerbox / mint / factory**: a designated authority creates fresh edges
  or resource on an authorized gesture — the legitimate point where new
  authority enters.
* **Parenthood / endowment**: creating a cell endows the child.

**Restrictive (the graph narrows):**

* **Attenuation** narrows the rights on one existing edge (a caveat, a facet
  subset). The narrow-only rule governs *one edge's rights*; it is not the
  law of the whole system.
* **Revocation / expiry** removes an edge (epoch-bump; one-way).

**The one law:** Miller's *only connectivity begets connectivity*. No ambient
authority; every generative act is itself authorized by held knowledge; and
generative/annihilative acts are receipt-disclosed — the conservation typing
forces them onto the chain, un-strippably. Authority grows, but only through
authorized, **non-forgeable** construction. This is an epistemic
non-forgeability invariant, not a lattice descent.

Mechanized: `Metatheory.no_forge_step` (the candidate-independent law);
`EffectsAuthority.introduce_non_amplifying` (a conferred capability is a
genuine subset of the held one, over the real attenuation lattice);
`EffectsAuthority.amplifying_grant_rejected` (the teeth: a grant conferring
authority the holder lacks is rejected — the predicate is two-valued);
`AuthModes.captp_granted_le_held` (the dispatcher gate on delivered
handoffs); `FullForestAuth.execFullForestG_no_amplify` (every delegation edge
of a committed forest, at the running entry).

## 2.4 Three logics over a step

Each turn is judged by three orthogonal logics:

1. **Conservation — substructural/linear.** Resources cannot be copied or
   discarded for free; generative/annihilative moves are disclosed
   exceptions bound into the receipt. Linear logic's structural rules, read
   as a security law: no inflation, no loss.
2. **Ordering — temporal/modal.** When is a fact final? A finality lattice
   over one Merkle-CRDT DAG; effects commit at the join of the written
   cells' tiers and never downgrade. "Knowledge becomes common knowledge" is
   the modal ascent.
3. **Independence — the confluence lattice.** Which concurrent inferences
   commute? The join-semilattice of invariant-preserving merges — the
   coordination-free fragment (§3.3 connects this to the guard algebra).

## 2.5 Crossing a trust boundary

Inside a trust root, authority is positional: holding the edge is the proof
and the mediator enforces it. Across a boundary it becomes epistemic: you
must present a verifiable witness, because the far side shares no mediator.
The crossing is a named-lossy functor — *permission survives, authority does
not* — and the loss is load-bearing: confinement and revocable-forwarding are
dropped, which is why a forwarded capability is revocable *by construction*.
A hosted cell's full state lives with its host; a **sovereign** cell keeps
only a commitment and proves its own transitions, so a far federation admits
it knowing only how to check a proof, never how to re-run the cell.
