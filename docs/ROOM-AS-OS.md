# THE ROOM IS THE OPERATING SYSTEM

*(design + staging, 2026-06-11; the room-as-OS lane chartered in HORIZON.md §1
(docs/HORIZON.md:8-22) and ORGANS.md §4 (docs/ORGANS.md:81-99). Design only —
no implementation in this doc. Every weld claim cites the machinery it welds.)*

The shape: a group chat where membership is governed law, message bodies are
ciphertext that never touches the chain, and protocol frames — turn proposals,
threshold shares, co-signing ceremonies, intent matches — flow invisibly in the
same channel as conversation. A council IS its chatroom; certifying IS sending;
the ceremony happens where the conversation already lives. Governance stops
being a place you go and becomes a property of where you already are.

---

## 1. Groups are cells

### 1.1 The statement

A group is a CELL. Its membership state and its group-key epoch commitment are
registers on that cell; join, remove, and update are TURNS under the group's
installed program. Therefore the entire governance algebra — invite-only,
council-approved joins, cooling periods on removals, actor-bound votes —
applies to chat membership **for free**, because it is just a cell program and
the executor re-evaluates the program on every turn that touches the cell
(the polis safety posture, stated at sdk/src/polis.rs:16-23: "The safety is
NOT in these builders — it is in the installed CellProgram, which the executor
re-evaluates on EVERY turn").

Two planes, strictly separated:

* **Control plane (on-cell, auditable, capability-gated):** membership root,
  group-key epoch, epoch commitment, governance state. Every change is a turn
  with a receipt.
* **Data plane (ciphertext, any transport):** message bodies. They NEVER touch
  the chain — not as plaintext, not as ciphertext. The chain sees at most a
  payload *commitment* when an application chooses to anchor one.

### 1.2 What already exists, slot by slot

The pubsub topic cell is the group cell's direct ancestor — most of the slots
are already laid out (dregg-storage-templates/src/pubsub_topic.rs:9-19):

| Slot | pubsub today | group cell reading |
|---|---|---|
| 0 `head_seq` | publisher's monotone counter | room message-frontier counter |
| 1 `subscriber_cursors_root` | per-subscriber Merkle cursors | per-member read cursors (delivery/ack state) |
| 2 `publisher_pk_hash` | publisher identity | generalizes to the governance authority (see 1.3) |
| 3 `subscriber_set_root` | authorized-subscriber Merkle roll | **the membership root** |
| 5 `event_root` | Merkle root over published events | root over *frame commitments* (bodies off-chain) |

The membership operation already exists: `grant_subscriber` changes
`subscriber_set_root` and nothing else, publisher-authorized
(pubsub_topic.rs:194-224, with the `SenderAuthorized { set: PublicRoot {
set_root_index: PUBLISHER_PK_HASH_SLOT } }` gate at :218-223). The subscriber
capability is attenuatable by design, "so members can re-grant restricted
views to peers" (pubsub_topic.rs:249-254). The publish path already commits
only a `payload_commitment`, not a body (pubsub_topic.rs:294-327) — the
data/control separation is the existing contract, not a new invention
("commitment-inside: anyone with topic_id_hash … can verify events against
event_root", pubsub_topic.rs:42-44).

The Lean side proves the shape's safety keystones: no read-ahead
(per-reader `cursor[r] ≤ head` as the live relational caveat
`RelCaveat.fieldLteOther`, metatheory/Dregg2/Apps/PubsubFactory.lean:101-105),
publisher-authorized append, and READER ISOLATION — one subscriber's progress
never moves another's (PubsubFactory.lean:40-47, non-vacuity witnessed at
:49-54). A subscription topic of this family is seeded at node boot
(node/src/genesis.rs:371-376, label `"subscription-topic"`).

### 1.3 The governance lift

What changes from pubsub to group: slot 2's single `publisher_pk_hash`
generalizes to *the group's program deciding who may run each membership op*.
The polis machinery is exactly this algebra, already built and e2e-tested:

* **M-of-N approval**: the council proposal machine — write-once proposal
  hash, per-member `{0,1}` monotone approval slots, certification admitted
  only when `Σ approvals >= threshold` via the `AffineLe` gate, terminal
  EXECUTED/REJECTED states (sdk/src/polis.rs:144-311).
* **Actor-bound votes**: `SenderIs` / `SenderInSlot` atoms in the cell-program
  language (docs/CELL-PROGRAM-LANGUAGE.md:90-114) — approval slot *i* flips
  only in a turn whose SENDER is member *i*'s published key; a stolen
  capability cannot vote (polis.rs:192-198, landed e2e
  `approval_slots_are_actor_bound`, CELL-PROGRAM-LANGUAGE.md:46).
* **Cooling periods**: the amendment machine's `enact_not_before =
  propose_height + amendment_delay`, enforced by `TemporalGate` in the
  program, not by the operator (polis.rs:403-439).

So the governed-membership ceremonies compose from existing parts:

* **Invite-only room**: `grant_subscriber` gated on the owner key — exists
  verbatim today.
* **Council-approved join**: a proposal cell stages
  `hash(grant_subscriber effects)`; members approve (actor-bound); the
  execute turn carries the grant effects in the same turn, binding action to
  proposal in one receipt (`execute_proposal`, polis.rs:294-302).
* **Cooldown on removals**: the removal proposal is an amendment-shaped cell —
  the remove turn is rejected before `enact_not_before`. A member sees their
  removal coming on-cell, in public, before it lands.
* **Constitutional rooms**: thresholds and delays read from a constitution
  cell and baked into descriptors at build, recomputable by any verifier
  (polis.rs:180-198, :403-415).

None of this is chat-specific code. That is the claim of this section:
membership governance is not a feature of the room — the room is a cell, and
cells already have governance.

### 1.4 What the chain sees

For a room: a membership root, an epoch counter, an epoch commitment, a frame
frontier, and receipts for membership turns. It never sees message bodies,
member message content, or (with hashed member keys in the Merkle roll) even
the member roster in the clear — only its commitment. The room's *law* is
public and auditable; the room's *life* is dark.

---

## 2. THE EPOCH-UNIFICATION KEYSTONE

### 2.1 The two counters that become one

**Counter A — the MLS key epoch** (RFC 9420). An MLS group advances through
epochs; each Commit (in particular each member removal) steps `epoch n →
n+1` and derives fresh epoch secrets from which all message keys flow. A
removed member's leaf is blanked from the ratchet tree, so the member cannot
derive epoch-`n+1` secrets: removal ⇒ forward ciphertext darkness. This is
MLS's core guarantee and we adopt it wholesale (§4).

**Counter B — the capability-freshness epoch** (R7, in-tree, live). Every
cell carries a sealed `delegation_epoch` register
(cell/src/state.rs:120-123), mutated only through
`bump_delegation_epoch` (state.rs:684), bumped on `RevokeDelegation`
(turn/src/lean_apply.rs:230; turn/src/executor/apply.rs:1587), and absorbed
into the cell's state commitment (cell/src/commitment.rs:290 — the chain
commits to the epoch). Two enforcement teeth already bite on it:

* **Stored capabilities**: a cap carrying `stored_epoch: Some(e)` is
  re-checked at exercise time against the grantor's CURRENT
  `delegation_epoch`; if `e < current`, the executor rejects with
  `TurnError::CapabilityStale` (turn/src/executor/apply.rs:1195-1221).
* **Sealed boxes**: `SealedBox` carries `sealer` + `seal_epoch`, both bound
  into the box commitment so the stamp cannot be stripped or refreshed
  without the plaintext (cell/src/seal.rs:73-93, :316-339, tamper-evidence
  tested at :969-1002); `apply_unseal` rejects a box once
  `seal_epoch < sealer.delegation_epoch()` — "a cap sealed BEFORE a
  revocation can no longer be unsealed AFTER it" (seal.rs:75-79).

**The unification**: for a group cell, these are the SAME counter. The MLS
epoch number IS the group cell's `delegation_epoch`. A membership-removal
turn is the one place both step, atomically, because it is one turn producing
one post-state commitment containing one epoch register.

### 2.2 The theorem-to-be, stated precisely

> **Epoch-unification (member removal ⇒ ciphertext darkness ∧ capability
> darkness, one step).**
>
> Let `G` be a group cell with member set `M`, unified epoch `n`
> (`G.delegation_epoch = n =` the MLS group epoch), and let `m ∈ M`. Let `T`
> be the removal turn: the turn whose effects (i) replace the membership
> root with `root(M \ {m})`, (ii) record the MLS epoch-`n+1` commitment
> (GroupContext hash) in `G`'s epoch-commitment register, and (iii) bump
> `G.delegation_epoch` to `n+1`. Then in any post-`T` reachable state:
>
> 1. **(Ciphertext darkness)** `m` cannot derive the epoch-`e` application
>    secrets for any `e ≥ n+1`, hence cannot decrypt any data-plane frame
>    sealed at epoch `≥ n+1`. *(Carried by the MLS key schedule's removal
>    guarantee — the adopted crypto floor, RFC 9420 §8/§12; our obligation
>    is only that `T` is the unique writer of the epoch-`n+1` commitment.)*
>
> 2. **(Capability darkness)** every group-held capability stamped at epoch
>    `≤ n` — whether held as a stored cap (`stored_epoch ≤ n`) or sealed
>    away in a box (`seal_epoch ≤ n`) — is rejected by the executor at
>    exercise/unseal (`CapabilityStale`), *(carried by the live R7 gates,
>    apply.rs:1207-1221 + seal.rs:75-79)*; and a FRESH stamp at epoch `n+1`
>    can only be produced by a turn on `G`, which `G`'s program admits only
>    for senders in `root(M \ {m})` — which excludes `m`.
>
> 3. **(Atomicity / no interleaving)** there is no reachable state in which
>    (1) holds and (2) does not, or vice versa: both are predicates over the
>    single epoch register in `G`'s single post-state commitment
>    (commitment.rs:290), stepped by the single turn `T`. Removal is not a
>    process; it is one state transition.

Clause 3 is the part nobody else has. MLS alone gives clause 1. Capability
systems with revocation give a slower, separate clause 2. Unifying the
counters makes "kicked from the room" and "stripped of the room's authority"
*the same event* — **post-compromise security for AUTHORITY, not just for
messages**. After removal, even a member who exfiltrated both the epoch-`n`
secrets AND every group-held sealed capability is dark on both axes at
`n+1`, and re-entry on either axis requires a turn the program no longer
admits for them.

### 2.3 What the proof obligation decomposes into

* (a) The removal turn bumps `delegation_epoch` — a small executor/Lean-kernel
  extension: today the bump fires on `RevokeDelegation`
  (lean_apply.rs:228-231); membership removal on a group cell IS a
  revocation (of the member's standing delegation from the group), and gets
  the same deterministic bump. This is the weld (§5, W1).
* (b) The R7 staleness gates fire — already enforced and tested
  (apply.rs:1207-1221; seal.rs:969-1002). Already modeled kernel-side (the
  delegation_epoch kernel-widen, commit `03c638ef7`).
* (c) Fresh stamps require membership — the group program's
  `SenderAuthorized` against the post-removal root; the same gate family the
  pubsub program already uses (pubsub_topic.rs:218-223).
* (d) MLS removal ⇒ key-schedule exclusion — ADOPTED, a named crypto
  primitive at the boundary, like Poseidon2 collision resistance. We do not
  re-prove MLS; we pin the implementation and state the assumption.

### 2.4 Honest limits of the keystone

* The R7 **migration window** is loud and real: `stored_epoch: None` caps and
  unstamped legacy boxes are EXEMPT from the staleness check
  (apply.rs:1204-1206, seal.rs:84-87). The theorem quantifies over *stamped*
  authority; a room's charter must therefore require stamped grants for
  group-held caps from birth. The window's closure is its own lane.
* The `no_forge_from_storage` residual (seal.rs:83-90): whoever holds the
  unsealer secret can re-seal with a fresh stamp; pinning the stamp to chain
  state is the named W2 follow-up. Same answer: rooms mint their seal pairs
  under the room's key discipline, and the residual closes when that lane
  does.
* Epoch bump staleness is *forward*: it does not retro-invalidate effects `m`
  legitimately committed before removal. That is correct, not a gap —
  receipts are history.

---

## 3. Invisible coordination frames

### 3.1 The principle

Everything in the room is an MLS **application message**: encrypted to the
member set, sender-authenticated by the MLS membership. Human chat and
protocol traffic ride the same pipe and are indistinguishable to every
non-member, including the transport. The client renders what it understands
as conversation; the agent runtime consumes what it understands as protocol;
both are just frames. The room IS the coordination surface — there is no
separate "governance UI" channel to subscribe to, monitor, or censor
distinctly.

### 3.2 The frame type system (sketch)

```
Frame := { v: u8, kind: FrameKind, room_epoch: u64, body: cbor }
         -- room_epoch = the unified epoch at send time (binds every frame
         --              to the membership state it was uttered under)

FrameKind :=
  | Chat            { text, attachments: [payload_commitment] }
  | TurnProposal    { target_cell, effects_cbor, effects_hash }
      -- "I propose this turn on a cell our room governs."
      -- effects_hash is what a council proposal cell stages (polis propose(),
      -- sdk/src/polis.rs:238-249).
  | ApprovalShare   { proposal_cell, member_index, approval_turn_cbor }
      -- a member's signed approve() turn (polis.rs:262-269), carried in-room;
      -- anyone may submit it to the chain — actor-binding makes the relay
      -- harmless (the program checks the SENDER key, polis.rs:192-198).
  | ThresholdShare  { ciphertext_id, share }
      -- a DecryptionShare verbatim (federation/src/threshold_decrypt.rs:69-85:
      -- validator_index, share, ciphertext_id binding, share_mac).
  | CosignShare     { msg_hash, signer_index, partial_sig }
      -- BLS partial toward a committee signature (the federation's real
      -- threshold-BLS, ORGANS.md:122-127).
  | IntentAd        { intent_commitment, ttl }
      -- advertises a typed hole for in-room intent matching.
  | ReceiptGossip   { receipt_cbor }
      -- a committed turn's receipt echoed into the room: the room's shared
      -- view of "it landed" (self-certifying; verify, don't trust the echo).
  | EpochCommit     { mls_commit_ref, turn_receipt_ref }
      -- the membership/epoch control frame: pointers binding the MLS Commit
      -- to the cell turn that recorded it (§4.2). The one frame kind whose
      -- substance is control-plane.
```

Versioned, CBOR-bodied, default-ignore: a client that does not know a
`FrameKind` skips it (forward compatibility); a runtime that does dispatches
it. `room_epoch` makes every frame's membership context explicit — a
`ThresholdShare` from epoch `n` is evaluated against epoch-`n` membership,
and frames from evicted epochs are dead on arrival by local policy.

### 3.3 A council IS its groupchat (the ceremony walkthrough)

M-of-3 council spend, end to end, all in one room:

1. Member A sends `TurnProposal` (treasury spend). Clients render it as a
   message; runtimes verify `effects_hash`.
2. A (or anyone) commits the on-cell `propose()` turn staging the hash
   (polis.rs:238-249); the receipt comes back as `ReceiptGossip`.
3. B and C send `ApprovalShare` frames — *certifying IS sending*. Their
   actor-bound approve turns land on the proposal cell (relayed by anyone;
   the program admits each slot only from its member's key).
4. Threshold reached: anyone sends/commits the certify + execute turn
   carrying the spend effects (polis.rs:278-302). Receipt gossips back.

The chain never learns this was discussed, who argued, or what was said
around it. It records exactly: proposal hash staged, two actor-bound
approvals, certified execution. The room saw a conversation. **The frames
are transport and ceremony; the cell turn is the commitment.** Frames never
substitute for receipts — a `ReceiptGossip` is verified like any receipt,
never trusted as hearsay.

The epistemic reading is exact and already formalized: a `Verify`-discharged
statement is distributed knowledge among the honest agents, funnelled through
the decidable `Verify` oracle, never through agent assertion
(metatheory/Metatheory/EpistemicConsensus.lean:17-24, on the
ConstructiveKnowledge floor: holding = exhibiting a discharging witness,
ConstructiveKnowledge.lean:48-56). The room is where E_G gets *assembled* —
per-member witnesses (approval turns, shares) flowing to a common surface —
and the receipt is where it becomes common knowledge worth the name.

### 3.4 Threshold ceremonies live where the committee talks

The t-of-n machinery (federation/src/threshold_decrypt.rs:1-24; share MACs
verified before interpolation, :55-67) currently presumes a "secure channel"
for share distribution and a collection point for decryption shares. The
room is both: the committee's MLS group is the secure channel (key
distribution as application frames at epoch birth), and `ThresholdShare`
frames are the collection. The prototype's named production upgrade ("in
production this would use a DKG ceremony instead of a trusted dealer",
threshold_decrypt.rs:18-19) is *also* a room ceremony — DKG rounds are
frames. Same for co-signing: the federation's BLS threshold signatures
(ORGANS.md:122-127) collect `CosignShare` frames where the signers already
coordinate.

---

## 4. MLS integration (RFC 9420)

### 4.1 The mapping

| MLS concept | dregg reading |
|---|---|
| Group | a group cell |
| Epoch `n` | the cell's `delegation_epoch` (§2 — THE unification) |
| Commit (membership change) | a TURN on the group cell; the program decides admissibility |
| GroupContext (epoch, tree hash, confirmed transcript hash) | registers on the cell (the epoch-commitment register binds it) |
| Proposals (Add/Remove/Update) | `TurnProposal`/governance frames; validity = the cell program, not "any member may commit" |
| Application messages | data-plane frames (§3), never on-chain |
| Key schedule, secret tree, FS/PCS | **adopted** — the crypto floor |
| Authentication Service (AS) | identity cells: KERI-shaped event logs with pre-rotation (ORGANS.md:129-138) — credential = the identity cell's current key state |
| Delivery Service (DS) | pubsub/mailbox/relay transport (any of them; §5.3) |

### 4.2 The commit-as-turn protocol

An MLS Commit and its cell turn are one logical event, two artifacts:

1. Proposer assembles the MLS Commit (epoch `n → n+1`).
2. Proposer submits the membership turn: SetFields for the new membership
   root, the epoch-`n+1` GroupContext hash, and the epoch bump; the program
   gates it (council approval staged? cooling elapsed? sender authorized?).
3. The turn commits ⇒ the Commit is canonical. The proposer fans out the
   `EpochCommit` frame (and MLS Welcome to joiners). Members verify the
   GroupContext hash against the cell register before stepping their local
   key schedule.

This dissolves MLS's classic DS headache — concurrent commits racing at the
same epoch — because **the cell's turn order IS the commit order**. The chain
arbitrates; a losing committer rebases. dregg is here genuinely better
infrastructure for MLS than a bespoke DS: ordering, auditability, and
governance of commits come from the substrate. And a member who was offline
catches up by reading the cell's receipt chain — the control plane is its own
catch-up log (the derivability invariant posture of EPOCH-DESIGN.md: durable
truth = the commit log and receipt chains).

### 4.3 Adopt vs build

**ADOPT (use a maintained implementation, e.g. OpenMLS; treat as a named
crypto-primitive boundary, like Poseidon2-collision-resistance at the circuit
edge):** the key schedule; TreeKEM and the secret tree; forward secrecy and
PCS for message content; Welcome/joining; the wire formats for crypto
artifacts. We do not reimplement and we do not re-prove; we pin and state
the assumption (§2.2 clause 1, §2.3(d)).

**BUILD (ours, on existing machinery):** the on-cell membership governance
(§1 — polis programs deciding commit admissibility, which vanilla MLS simply
does not have: any member may commit in RFC 9420; we make WHO-may-commit
law); the epoch unification (§2 — bind `delegation_epoch` to the MLS epoch;
no MLS library knows what a capability is); the GroupContext-on-cell binding
(§4.2); the frame type system and runtime dispatch (§3); identity-cell
credentials as the AS.

**The honest boundary, stated once:** MLS gives message confidentiality with
FS/PCS *within whatever member set it is told*. dregg gives membership-as-law
(the member set is governed, auditable state) and capability-epoch
unification (removal is authority-PCS, not just message-PCS). Neither
subsumes the other; the seam between them is exactly one register: the epoch.

### 4.4 What we do NOT claim

MLS hides message content from non-members. It does not hide that the group
exists, its approximate size, its traffic timing, or sender-frequency
patterns from the transport; deniability is weak. The control plane is
deliberately *public* law — membership roots and epochs on-chain are
commitments, but their receipt traffic is visible. Metadata privacy at the
transport (mixing, cover traffic) is a different lane
(docs/design-network-privacy.md); rooms inherit whatever it provides, and
nothing here pretends otherwise.

---

## 5. Staging

### 5.1 The weld-vs-build ledger

**WELDS (machinery exists; connect it):**

| W | What | Existing parts (cites) |
|---|---|---|
| W1 | **Removal bumps the epoch** — membership-removal turns on group cells call the same deterministic `bump_delegation_epoch` path as `RevokeDelegation` | the bump + both R7 teeth are live (lean_apply.rs:230; apply.rs:1207-1221; seal.rs:75-79; state.rs:684); kernel model already widened to delegation_epoch (`03c638ef7`) |
| W2 | **Governed membership** — route `grant_subscriber`-shaped membership effects through council proposal cells; cooldown-on-removal via the amendment temporal gate | grant_subscriber op (pubsub_topic.rs:194-224); execute-carries-effects (polis.rs:294-302); TemporalGate cooling (polis.rs:403-439); actor-bound slots (polis.rs:192-198) |
| W3 | **Room transport** — frames ride existing rails: pubsub publish with payload commitments, relay mailboxes, captp store-and-forward (already ciphertext-only to relays) | pubsub payload_commitment (pubsub_topic.rs:294-327); relay send/drain (node/src/relay_service.rs:3-14); captp E2E ("relay operators see only ciphertext", captp/src/lib.rs:27; sender-anonymous boxes, captp/src/store_forward.rs:235); subscription seeded at boot (genesis.rs:371-376) |
| W4 | **Ceremony frames carry existing types** — `ApprovalShare` = a polis approve turn; `ThresholdShare` = `DecryptionShare` verbatim; `CosignShare` = the federation's BLS partials | polis.rs:262-269; threshold_decrypt.rs:69-85; ORGANS.md:122-127 |

**BUILDS (genuinely new):**

| B | What | Why it's real work |
|---|---|---|
| B1 | The MLS stack integration (adopt OpenMLS or peer) | RFC 9420 is a real protocol: ratchet-tree validation, proposal/commit state machine, Welcome flows. Months, not days. Pinning a maintained impl is the only honest path; bespoke MLS would be malpractice. |
| B2 | The epoch unification end-to-end (W1 is the counter weld; B2 is the MLS half: GroupContext register, commit-as-turn (§4.2), Welcome plumbing) | new executor surface + the §2.2 theorem in Lean (clauses 2-3 over existing R7 lemmas; clause 1 a named assumption) |
| B3 | The frame codec + runtime dispatch + client rendering discipline | new, but small and boring by design (CBOR, default-ignore) |
| B4 | Group-cell program family (membership root ops at scale, joiner/leaver state) | the per-slot council shape is O(n) slots — fine for councils, wrong for big rooms; needs the Merkle-roll + proof-of-membership idiom (the `subscriber_set_root` pattern generalized) |

### 5.2 Waves

* **Wave R1 (the keystone weld, no MLS yet):** W1 + the staleness test —
  *a member removed from a group cell finds their previously-stored and
  previously-sealed group caps rejected `CapabilityStale` in the next turn.*
  Capability darkness lands before any ciphertext exists.
* **Wave R2 (governed membership):** W2 — council-approved joins,
  cooldown removals, actor-bound votes, all e2e on group cells.
* **Wave R3 (the room speaks):** B3 + W3/W4 — frames over existing
  transport, sealed point-to-point first (cell/src/seal.rs machinery),
  ceremony frames driving real polis cells from a room.
* **Wave R4 (MLS):** B1 + B2 — the key schedule arrives, epochs unify with
  it, §2.2 becomes a stated theorem with its named MLS assumption.

Each wave ends shell-reachable (the ORGANS.md:148-153 discipline); R3 is a
*useful product* (governed rooms with E2E point-to-point frames) even before
MLS lands.

### 5.3 The seam to the delay-tolerant lane

A sibling lane plans store-and-forward (HORIZON.md §2, docs/HORIZON.md:24-35).
The seam is clean and load-bearing: **ciphertext frames are exactly what
bundles carry.** A frame is opaque, self-contained, and addressed to a room —
the ideal bundle payload; mailbox cells (relay_service.rs:3-14, custody
receipts per ORGANS.md:54-59) carry room traffic across arbitrary delay
without learning anything. Order tolerance splits exactly along our two
planes: data-plane frames within an epoch tolerate reordering (MLS per-sender
ratchets); control-plane commits are strictly ordered — *by the cell*, which
is the chain's job anyway. A long-offline member drains their mailbox, reads
the group cell's receipt chain to replay missed epoch commits in order, then
decrypts their backlog. The room carries over store-and-forward because
nothing in the room ever depended on being online together.

### 5.4 Honest obstructions

1. **MLS is a real protocol with real complexity.** The mitigations are
   adoption (B1) and seam-narrowing (one register, one named assumption) —
   but the integration surface (credential binding, Welcome handling, commit
   races against chain latency) will produce real bugs. Budget for it.
2. **The migration window is a hole in the keystone until closed.** Unstamped
   caps/boxes bypass the R7 teeth (apply.rs:1204-1206; seal.rs:84-87). Rooms
   must be born all-stamped, and the global window closure is a prerequisite
   for claiming §2.2 unconditionally. Plus the `no_forge_from_storage`
   residual (seal.rs:88-90).
3. **Large groups.** TreeKEM is O(log n) for keys — fine. Our governance
   programs are O(n) slots per council — fine for councils (which are small
   by nature), wrong for thousand-member rooms; B4's Merkle-membership idiom
   is required, and "the council that governs the room" (small) should be
   distinguished from "the room" (large) in program design.
4. **Untrusted transport ≠ available transport.** Ciphertext-on-anything is
   honest about confidentiality and integrity (commitments + MLS AEAD detect
   tamper; `head_seq` + MLS generations detect gaps) but NOT availability —
   a malicious relay can drop. The answer is the accountable-relay lane
   (bonds, custody receipts, slash-on-drop — ORGANS.md:54-59), not a claim
   here.
5. **Metadata.** §4.4. The room hides what is said, not that a room exists
   and breathes.

---

## The first implementation step (highest leverage)

**W1: make membership removal bump `delegation_epoch`, with the staleness
test.** One small executor + Lean-kernel change on machinery that all exists
(the bump path, both R7 teeth, the kernel's widened epoch model), zero MLS
dependency, and it IS the keystone: from that commit on, "removed from the
group" already means "the group's authority goes dark for you," and the
entire MLS integration later *inherits* a unified epoch instead of
retrofitting one. Everything else in this design decorates that counter.
