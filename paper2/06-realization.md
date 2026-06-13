# 6 · The realization

## 6.1 The Lean kernel is the executor

The semantics are not a model *of* the implementation; they are the
implementation. The gated whole-forest step `execFullForestG`
(`Dregg2/Exec/FullForestAuth.lean`) is compiled, exported through FFI as
`dregg_exec_full_forest_auth`, and invoked by the node on its production
path. Guarantee R (§5.1) is stated over exactly this function, so "the
proofs are about the thing that runs" is a theorem, not a deployment note.

The gate is the two-gate discipline of §1.2 made operational: admission
(credential validity ∧ capability authority ∧ caveats discharged, the
`gateOK` conjunction) is evaluated fail-closed — any failing leg rejects the
entire forest — and the substance laws ride through the gate unchanged
(conservation and non-amplification are proved over the gated entry, not
just the raw step).

Around the kernel, the trust base is a named, surveyed set of host
components (`docs/DREGGRS-SEGREGATION.md`): the FFI marshalling, the node's
admission gates, the standalone and succinct verifiers, the canonical
codecs, the bearer-token cryptography, and consensus safety. Transport,
storage, and networking sit outside the boundary — commitments catch
tampering below them, so they must be available, not correct. The node
reports which semantics produced what, live, at `/api/node/producer`
(§8 discusses the host-context seam this surfaces).

## 6.2 The descriptor circuit

The proof system is organized so the circuit is *derived*, not hand-built:
each kernel statement carries a descriptor — the structured form of its
semantics — from which the executor reading (`interp`) and the circuit
reading (`compile`) are both obtained, with agreement theorems welding them
(`argus_circuit_executor_receipts_agree` is the receipt-level weld; the
per-effect statements live in `Circuit/Argus/Effects/`). One term, two
provably-agreeing readings: the turn is a proof term, the circuit is the
logic's proof checker, a receipt is a judgment, and the chain is one growing
proof object.

The proving stack is a STARK over Plonky3 (BabyBear, FRI), with the
commitment scheme of §4.1 inside the arithmetization (Poseidon2) and
recursion folding receipts into the aggregate the light client checks. The
engine-soundness obligation is the single named carrier
`EngineSound.recursive_sound` (§5.2) — the circuit layer adds no other
assumption.

## 6.3 The factory userspace

Applications do not extend the kernel; they are cells. A **factory**
publishes a descriptor — a slot layout plus `Pred` constraints — and
`create` mints cells from it; from that moment the executor enforces the
program on every turn touching the cell. The recurring coordination shapes
ship as verified factories whose safety keystones are kernel theorems:

* **escrow** (`Dregg2/Apps/EscrowFactory.lean`) — conditional settlement:
  `no_double_resolve`, `release_requires_condition`, `release_conserves` /
  `refund_conserves`, and the not-stranded pair `open_releasable` /
  `open_refundable`;
* **obligation** (`ObligationFactory.lean`) — bonded proof obligations;
* **bridge** (`BridgeCell.lean`) — lock / finalize-to-pot / cancel;
* **queues, inboxes, pubsub** — value-bearing and capability-bearing
  mailboxes as bounded state machines;
* **caps-in-slots** — sealer/unsealer boxes, sturdy references, handoff
  certificates: a stored capability is a value in a slot, and retrieval
  re-checks the grantor's revocation epoch.

The shape is uniform: the value at stake lives in the minted cell's own
balance column (funding and settling are ordinary `move`s, so conservation
is the ordinary kernel law with no side tables), and the lifecycle is a slot
governed by a `Pred` state machine. The runtime mirrors the Lean exactly:
`cell/src/blueprint.rs` builds per-deal descriptors whose constraints *are*
the verified state machines, and `sdk/src/factories.rs` emits the
corresponding turns.

Apps **inherit theorems**: the Verify toolkit
(`Dregg2/Verify/{Contract,Frames,Tactics}`) lets an application state its
contract and discharge it by consuming receipts against descriptors, so the
kernel's guarantees flow upward without enlarging the kernel. Governance is
the same pattern at civic scale: a council is a threshold-gated cell, a
constitution is a forward-certified program readable on a page, and an
agent's mandate is a program on the agent's cell — every turn it takes
carries the proof it stayed inside.

## 6.4 The agent surface

The client side is the **cipherclerk** — the citizen's clerk: key custody,
attenuable tokens, delegation and sub-agent derivation, and the selective-
disclosure dial (hide / reveal / predicate / committed-threshold) as literal
Q-projections. The SDK (`sdk/`) is client-local: turn-building, attenuation,
and proof generation run on the user's device; witness data stays there. The
clerk is the polis interface; the kernel is what makes the clerk's promises
true.
