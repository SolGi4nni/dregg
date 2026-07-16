// =============================================================================
// Section 7: The realization
// =============================================================================

#import "../defs.typ": lean
= The realization <sec-realization>

The model of the previous sections is not a description *of* the running
system; it *is* the running system. This section is the realization: the Lean
kernel as the deployed executor, the trust base around it, the single proving
path, the factory userspace and two of its customers, what runs today, and the
client surface.

== The Lean kernel is the executor

The gated whole-forest step #lean("FullForestAuth.execFullForestG")
(`Dregg2/Exec/FullForestAuth.lean`) is compiled, exported through FFI as
`dregg_exec_full_forest_auth` (`Dregg2/Exec/FFI.lean`), and invoked by the node
on its production path. The running-entry guarantee (@sec-assurance) is stated
over exactly this function: #lean("AssuranceCase.running_entry_sound") proves
conservation, non-amplification, and per-node attestation of the entry the node
calls, not of an abstract twin.

The gate is @sec-model's two-gate discipline made operational. Admission ---
credential validity, capability authority, and caveats discharged, the
#lean("FullForestAuth.gateOK") conjunction --- is evaluated fail-closed. Any
failing leg rejects the entire forest
(#lean("FullForestAuth.execFullForestG_unauthorized_fails")). The substance
laws ride through the gate unchanged: conservation and non-amplification
(#lean("FullForestAuth.execFullForestG_no_amplify")) are proved over the gated
entry, not merely over the raw step.

== The trust base

Around the kernel is a named, surveyed set of host components: the FFI
marshalling, the node's admission gates, the standalone and succinct verifiers,
the canonical codecs, the bearer-token cryptography, and consensus safety.
Transport, storage, and networking sit *outside* the boundary --- commitments
catch tampering below them, so they must be *available*, not *correct*. The
node reports which semantics produced each committed state, live, at
`GET /api/node/producer` (`node/src/api.rs`); @sec-limitations discusses the
host-context seam this endpoint surfaces.

== One proving path

The circuit is *derived*, not hand-built (the descriptor reading of
@sec-proofs), and the repository enforces this as an invariant rather than
stating it as a policy. There is one proving path. The earlier hand-written
STARK engine is deleted, and every production proof goes through
`prove_vm_descriptor2` / `verify_vm_descriptor2` over descriptors emitted from
Lean. Every deployed first-party circuit is emitted from a proved module. The
last hand-authored one, the revocation-freshness circuit, is now the emitted
descriptor `dregg-non-revocation-adjacency::poseidon2-fact-v1`
(`Dregg2/Circuit/Emit/NonRevocationAdjacencyEmit.lean`), byte-identical between
the emitter's output and the deployed artifact. A ratchet keeps the invariant
from decaying: a gate test (`circuit-prove/tests/law1_enforcement_gate.rs`)
counts constraint sites in every circuit source file across all three Rust
constraint dialects --- symbolic builder calls, evaluation closures, and
constraint-expression literals --- and fails the build if any file grows or a
new one appears; counts may only shrink. The sites that remain are interpreters
of Lean-authored constraints, proved-faithful lowerings, and drift detectors,
each listed in the gate with its reason.

The two readings of a descriptor --- the executor's `interp` and the circuit's
`compile` --- are welded by the receipt-level agreement theorem
(#lean("Argus.Receipt.argus_circuit_executor_receipts_agree")), with the
per-effect statements in `Circuit/Argus/Effects/`. The proving stack is a STARK
over Plonky3 (BabyBear, FRI) @plonky3 @fri, with the @sec-proofs commitment
scheme (Poseidon2) @poseidon2 inside the arithmetization and recursion folding
receipts into the aggregate the light client checks. The circuit layer adds
exactly one assumption to the floor, the named engine-soundness carrier
#lean("EngineSound.recursive_sound"); the assurance case (@sec-assurance)
states what that carrier is currently worth in quantified terms.

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

The shape is uniform. Value at stake lives in the minted cell's own balance
column, so funding and settling are ordinary `move`s and conservation is the
ordinary kernel law with no side tables; the lifecycle is a slot governed by a
`Pred` state machine. The runtime mirrors the Lean: `cell/src/blueprint.rs`
builds per-deal descriptors whose constraints *are* the verified state machines,
and `sdk/src/factories.rs` emits the corresponding turns from surviving verbs
only. Applications *inherit theorems*: the Verify toolkit
(`Dregg2/Verify/{Contract,Frames,Tactics}`) lets an application state its
contract and discharge it by consuming receipts against descriptors, so the
kernel's guarantees flow upward without enlarging the kernel.

A delivered cross-session handoff is admitted only through a verified
non-amplification gate (#lean("AuthModes.captp_granted_le_held")): the CapTP
session surface --- sturdy refs, three-party handoff, promise pipelining --- is
kept out of the consensus-visible kernel, where pipelining is turn composition
and a reference is a capability in a slot.

== Games: inherited theorems, worked

The game portfolio is the factory pattern's first customer, and a game turn is
the paper's opening sentence taken literally: the exercise of an attenuable,
proof-carrying token over owned state, leaving a verifiable receipt. Three
games run on this shape (`docs/GAME-STRATEGY.md`): a daily dungeon crawl whose
lethality, permadeath, and progression rules are cell programs on the executor
path --- an attested narrator proposes, the verified rules dispose --- and two
board games whose rulebooks are Lean definitions.

For automatafl, the staged circuit's admission relation is exactly the graph of
the rulebook's turn function
(#lean("Games.Automatafl.airAutomatafl_iff_applyTurn")), and a successor board
that relocates a piece anywhere the rules do not has no satisfying witness
(#lean("Games.Automatafl.airAutomatafl_forged_refused")). For the hidden-hand
tug game, a play is admitted exactly when it is legal, the played cards open
against the committed hand, and the successor is the rulebook's
(#lean("Games.MultiwayTug.airPlay_iff_applyAction")). The Rust game crates are
tested against these statements rather than beside them: a refinement battery
drives the built circuit against a reference oracle mirroring the Lean rules,
rejecting wrong successors, invalid moves, and forged conflict resolutions
(`dregg-automatafl/tests/refinement.rs`); and the automaton-step circuit proves
as a recursion-foldable leaf whose in-circuit commitment matches the host
binding, folds into a turn chain, and passes the light client's
`verify_history` (`dregg-automatafl/tests/prove_fold.rs`). The consequence is
the application-level restatement of unfoolability: the operator cannot
misreport a hit-point total, and a completed run is checkable by a stranger
from its receipts alone.

== Governance as a factory customer

Governance is the same pattern at civic scale, and it is realized
(`dregg-governance/`). One executor-backed vote engine drives federation
self-governance, community polls, and collective choice over shared state. A
ballot is a write-once slot; a tally is a monotone field; the committee quorum
rule (two-thirds plus one) is an in-cell affine gate, and resolving a decision
must additionally exhibit the required number of distinct approvers through a
counting gate. Enactment fires only when the executor's decision-turn commits
and the constitution manager independently agrees. The threshold rule is
therefore enforced by the same executor as any other cell program, and a
governance outcome carries the same receipt as a transfer.

== What runs

The deployment status, in one statement. The verified executor commits turns on
the node's production path, and each node reports its per-effect producer
coverage at `GET /api/node/producer`. A four-node federation spanning two
machines stream-finalizes attested turns (`docs/STAGE5-N4-RESULT.md`); with the
verified finality gate on, the two machines commit byte-identical state across
operating systems and build profiles, and the open seam is a finality-poll
recomputation cost --- a performance property, not a correctness one
(`docs/CROSS-MACHINE-FINALITY-FINDING.md`). The game portfolio is served
publicly from one host's service units (`deploy/games/`). Every descriptor
install appends an operator-stamped row to an append-only regeneration log
whose tamper-evidence is git history (`docs/VK-REGEN-LOG.md`).

== The client surface

The client side is the *cipherclerk*: key custody, attenuable tokens, delegation
and sub-agent derivation, and the selective-disclosure dial (hide / reveal /
predicate / committed-threshold) as literal *Q*-projections (@sec-guards). The
SDK (`sdk/`) is client-local --- turn-building, attenuation, and proof
generation run on the user's device, and witness data stays there. Search lives
at this edge, where @sec-intro places it: solvers, intent matchers, and provers
produce witnesses; the kernel only ever checks them.

== One model, projected

This userspace service is one realization of the model, not its boundary. The
remaining sections develop the substrate it deploys onto: the proof
architecture that lets the circuit's shape rotate under proof (@sec-proof-arch),
the capability carried across the distance parameter (@sec-firmament) and its
three faces (@sec-deos, @sec-sel4, @sec-pg), and the assurance case that pins
every guarantee (@sec-assurance).
