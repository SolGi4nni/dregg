// =============================================================================
// Section 7: The realization
// =============================================================================

#import "../defs.typ": lean
= The realization <sec-realization>

The model of the previous sections is not a description *of* the running system;
it *is* the running system. This section is the realization: the Lean kernel as
the deployed executor, the trust base around it, the descriptor circuit, the
factory userspace, and the client surface.

== The Lean kernel is the executor

The gated whole-forest step #lean("FullForestAuth.execFullForestG")
(`Dregg2/Exec/FullForestAuth.lean`) is compiled, exported through FFI as
`dregg_exec_full_forest_auth`, and invoked by the node on its production path.
The running-entry guarantee (@sec-assurance) is stated over exactly this
function, so "the proofs are about the thing that runs"
(#lean("FullForestAuth.running_entry_sound")) is a theorem, not a deployment
note.

The gate is @sec-model's two-gate discipline made operational. Admission ---
credential validity, capability authority, and caveats discharged, the
#lean("FullForestAuth.gateOK") conjunction --- is evaluated fail-closed: any
failing leg rejects the entire forest
(#lean("FullForestAuth.execFullForestG_unauthorized_fails")). The substance laws
ride through the gate unchanged; conservation and non-amplification
(#lean("FullForestAuth.execFullForestG_no_amplify")) are proved over the gated
entry, not merely over the raw step. The gate adds teeth without weakening the
linear guarantees.

== The trust base

Around the kernel is a named, surveyed set of host components
(`docs/DREGGRS-SEGREGATION.md`): the FFI marshalling, the node's admission gates,
the standalone and succinct verifiers, the canonical codecs, the bearer-token
cryptography, and consensus safety. Transport, storage, and networking sit
*outside* the boundary --- commitments catch tampering below them, so they must
be *available*, not *correct*. The node reports which semantics produced what,
live, at `/api/node/producer`; @sec-limitations discusses the host-context seam
this surfaces honestly.

== The descriptor circuit

The proof system is organized so the circuit is *derived*, not hand-built (the
descriptor reading of @sec-proofs). Each kernel statement carries a descriptor
from which the executor reading (`interp`) and the circuit reading (`compile`)
are both obtained, welded by the receipt-level agreement theorem
(#lean("Argus.Receipt.argus_circuit_executor_receipts_agree")), with the
per-effect statements in `Circuit/Argus/Effects/`. The proving stack is a STARK
over Plonky3 (BabyBear, FRI) @plonky3 @fri, with the @sec-proofs commitment scheme
(Poseidon2) @poseidon2 inside the arithmetization and recursion folding receipts
into the aggregate the light client checks. The circuit layer adds exactly one
assumption to the floor --- the named engine-soundness carrier
#lean("EngineSound.recursive_sound") --- and no other; no constraint is authored
in Rust.

== The factory userspace

Applications do not extend the kernel; they are cells. A *factory* publishes a
descriptor --- a slot layout plus `Pred` constraints --- and the `create` verb
mints cells from it; from that moment the executor enforces the program on every
turn touching the cell. The recurring coordination shapes ship as verified
factories whose safety keystones are kernel theorems:

#figure(
  table(
    columns: (auto, auto),
    align: (left, left),
    table.header([*factory*], [*kernel-theorem safety keystones*]),
    [escrow (`Apps/EscrowFactory.lean`)],
      [conditional settlement: #lean("EscrowFactory.no_double_resolve"),
       #lean("EscrowFactory.release_requires_condition"),
       #lean("EscrowFactory.release_conserves") /
       #lean("EscrowFactory.refund_conserves"), and the not-stranded pair
       #lean("EscrowFactory.open_releasable") /
       #lean("EscrowFactory.open_refundable")],
    [obligation (`ObligationFactory.lean`)], [bonded proof obligations],
    [bridge (`BridgeCell.lean`)], [lock / finalize-to-pot / cancel],
    [queues, inboxes, pubsub], [value- and capability-bearing mailboxes as
      bounded state machines],
    [caps-in-slots], [sealer/unsealer boxes, sturdy references, handoff
      certificates --- a stored capability is a value, and retrieval re-checks
      the grantor's revocation epoch],
  ),
  caption: [The factory userspace. Each pattern is a cell program built from the
    surviving verbs; its contract is a kernel theorem.],
)

The shape is uniform: value at stake lives in the minted cell's own balance
column, so funding and settling are ordinary `move`s and conservation is the
ordinary kernel law with no side tables; the lifecycle is a slot governed by a
`Pred` state machine. The runtime mirrors the Lean exactly --- `cell/src/
blueprint.rs` builds per-deal descriptors whose constraints *are* the verified
state machines, and `sdk/src/factories.rs` emits the corresponding turns.
Applications *inherit theorems*: the Verify toolkit
(`Dregg2/Verify/{Contract,Frames,Tactics}`) lets an application state its
contract and discharge it by consuming receipts against descriptors, so the
kernel's guarantees flow upward without enlarging the kernel. Governance is the
same pattern at civic scale: a council is a threshold-gated cell, a constitution
is a forward-certified program, and an agent's mandate is a program on the
agent's cell --- every turn it takes carries the proof it stayed inside.

A delivered cross-session handoff is admitted only through a verified
non-amplification gate (#lean("AuthModes.captp_granted_le_held")): the CapTP
session surface --- sturdy refs, three-party handoff, promise pipelining --- is
kept out of the consensus-visible kernel, where pipelining is turn composition
and a reference is a capability in a slot.

== The client surface

The client side is the *cipherclerk*: key custody, attenuable tokens, delegation
and sub-agent derivation, and the selective-disclosure dial (hide / reveal /
predicate / committed-threshold) as literal *Q*-projections (@sec-guards). The
SDK (`sdk/`) is client-local --- turn-building, attenuation, and proof generation
run on the user's device, and witness data stays there. Search lives at this
edge, where @sec-intro places it: solvers, intent matchers, and provers produce
witnesses; the kernel only ever checks them.

== One model, projected

This userspace service is one realization of the model, not its boundary. The
remainder of the paper develops the substrate the model deploys onto and the
discipline that keeps it sound. First, the proof architecture (@sec-proof-arch):
how the light-client guarantee of @sec-proofs stays honest while the
arithmetization itself evolves --- the circuit witnesses correct evolution, its
shape rotates under proof, and every finalized turn stays provable across shapes.
Then the *firmament* (@sec-firmament): the capability of @sec-authority is one
abstraction across a distance parameter, a local microkernel object and a
distributed cell being the same attenuable reference, whose single-machine limit is
the strong case rather than a degraded subset. The firmament has three concrete
faces, each a projection of the one model rather than a new layer: a desktop, where
a window is a capability and a rendered scene a per-viewer projection
(@sec-deos); a capability-secure microkernel, where seL4's capability graph
isolates the protection domains and dregg's mediates the cells inside them
(@sec-sel4); and a database, where reads are SQL and writes are verified turns
(@sec-pg). The assurance case (@sec-assurance) then states every guarantee these
rest on, pinned to the kernel.
