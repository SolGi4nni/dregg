# Abstract

dregg is a distributed object-capability substrate whose proofs witness the
protocol's correct evolution: a verifier holding one aggregate root learns
that every state transition in the system's history was authorized,
conservative, and correctly committed — re-executing nothing and trusting no
executor.

The model is small. State lives in **cells**; a **turn** is the exercise of
an attenuable, proof-carrying token over owned state, leaving a verifiable
receipt. The kernel governs four substances, each under its own discipline of
use — value is linear (Σδ = 0, exactly), authority is produced under
non-forgeability, evidence is monotone, state is guarded-mutable — and its
signature is eight verbs, each the structural rule of one substance's
discipline. Minimality of the signature is a theorem, not an aesthetic.

Authority is treated as *constructive knowledge*: to hold a capability is to
be able to exhibit a witness that authorizes an act, never merely to assert
it. The system is organized around the asymmetry that proof-checking is cheap
and trusted while proof-search is undecidable and untrusted, and its central
authority law is generative rather than monotone: authority genuinely grows —
introduction, sealer/unsealer amplification, minting — but only through
authorized, receipt-disclosed construction from connectivity already held.

Everything that constrains a turn is one predicate algebra appearing at four
polarities (caveats on delegated power, programs on owned state,
preconditions on turns, demands on the world), with two computed prices: a
coordination dial (a confluence-stable guard runs coordination-free; one that
is not provably forces ordering) and a disclosure dial (committed,
range-proved, and jointly-garbled evaluation; what the proof does not need,
it does not see).

The semantics are a Lean 4 kernel that is also the deployed executor, reached
by FFI from the node; the assurance case is organized by guarantee —
authority, conservation, integrity, freshness, unfoolability, and a "running
entry" guarantee stating the first three over the exact function the node
invokes — with every keystone machine-pinned to the Lean kernel's three
axioms plus an explicit eight-carrier cryptographic and liveness floor.
Applications are factory-minted cells whose rules are predicate programs
enforced by the same executor, so application contracts are inherited from
kernel theorems rather than re-established per app.
