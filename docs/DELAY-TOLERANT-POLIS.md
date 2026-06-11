# THE DELAY-TOLERANT POLIS — store-and-forward over self-certifying payloads

**Status:** design + staging (2026-06-11, delay-tolerant-polis planning lane).
Sections titled **DESIGN** are proposals; everything else is present-tense
description of what exists, with file:line. Charter sketch: `docs/HORIZON.md:24-35`
(§2); the mailbox organ: `docs/ORGANS.md:44-59`; the finality substrate this
composes with: `docs/CONSENSUS-FLEX.md`.

The same design serves a phone in a tunnel and a habitat at light-minutes.
Interplanetary (LTP/DTN-style bundle networking) is not a feature target; it is
the honest limit case the architecture already respects, and the vocabulary —
bundles, custody transfer, contact windows — is the right one for naming what
the tree already builds.

---

## 1. The principle (stated once)

**Validity travels with the payload.** A signed turn with its receipt is
self-certifying: the signature binds the author, the receipt chain binds the
turn to its cell's verified history, and the proof verifies anywhere, offline,
with no appeal to the carrier. So a payload does not care who carried it, how
many hops it took, or how long it waited.

This is why store-and-forward over **untrusted** relays across **unbounded**
delay is sound here where it is unsound for systems whose validity lives in the
channel (sessions, trusted servers, online checks). The carrier's whole attack
surface collapses to *delay, drop, duplicate* — and each is already priced or
absorbed:

* **Tamper/forge/read** — impossible for the carrier. The store-and-forward box
  is X25519 → HKDF-SHA256 → ChaCha20-Poly1305 with the full handshake
  transcript bound into both the KDF info and the AEAD associated data, so a
  relay "cannot read, forge, or tamper with messages — it can only delay or
  drop" (`captp/src/store_forward.rs:149-178`, the encrypt/decrypt pair at
  `:246-285` and `:301-347`). And the payload *inside* the box is itself a
  signed turn — tamper-evidence twice over.
* **Duplicate/replay** — absorbed twice: per-creator strand sequence numbers
  are strictly monotone and fork-free at the verified lace insert (the A1 fix,
  `Dregg2/Distributed/StrandIntegrity.lean`, summarized at
  `docs/CONSENSUS-FLEX.md:131-139`), and the node's execution cursor tracks
  executed blocks **by identity**, so a block arriving twice executes once
  (`node/src/execution_cursor.rs:21-30`).
* **Delay** — the subject of this document. The blocklace is already a
  store-and-forward layer: "encrypted messages are stored as blocks with opaque
  payloads; when the destination syncs the DAG it naturally receives queued
  messages" (`captp/src/store_forward.rs:14-18`). The lace merge is a pure join
  on a content-addressed keyset — commutative, associative, idempotent
  (`metatheory/Dregg2/Distributed/LaceMerge.lean:111,138-173`) — so transport
  order and hop count are semantically invisible.
* **Drop / omission** — the one thing a carrier can still do. Silence is
  refutable (strand seq gaps are visible; the lace is content-addressed), and
  §3 makes drop *accountable*: custody is a receipt, backed by a bond.

Everything below is the working-out of this one principle against the
machinery that exists.

---

## 2. What exists — the census, grounded

### 2.1 The relay economy (ALIVE — a complete hosted-inbox service)

`dregg-node relay` is a running HTTP service (`node/src/relay_service.rs`):

* **Routes** — subscribe / unsubscribe / send / drain / inbox status / **per-message
  dequeue proof** (`relay_service.rs:7-17,613-623`).
* **Bonded operators** — bond, `required_bond` scaling with hosted capacity,
  underbonded refusal (`storage/src/operator.rs:57,153-165,324-334`); bond and
  fee policy in `RelayConfig` (`relay_service.rs:51-69,89-111`).
* **The cell-program mirror** — the relay's public state IS a cell program:
  8-slot layout (bond, bond_min, quota, byte-counter, hosted_inbox_root,
  operator_pk_hash, route_table_root, dispute_count;
  `dregg-storage-templates/src/relay_operator.rs:16-25,78-85`) with
  operation-scoped constraints: `register_inbox` operator-only, `relay` under
  `Monotonic` + `RateLimitBySum` + a DFA route classifier over witness bytes
  (`relay_operator.rs:200-243`), and `slash` encoding *no-drain-without-dispute*
  (`bond_amount` may decrease only while `dispute_count` advances by exactly
  one — `relay_operator.rs:37-43,249-...`). The node keeps the mirror in
  lockstep: every send is validated against the template's quota/capacity/deposit
  rules before the byte backend sees it (`relay_service.rs:368-394,897-916`),
  and the hosted-inbox Merkle root is recommitted on every mutation
  (`relay_service.rs:396-423`).
* **Caller authentication** — Ed25519 over domain-separated (owner, nonce)
  tuples on subscribe/unsubscribe/drain (F-P1-1,
  `relay_service.rs:630-653,706-732`), with adversarial tests
  (`relay_service.rs:1342-1420`).
* **Dequeue proofs** — every drain produces `DequeueProof { old_root, new_root }`
  per message (`storage/src/queue.rs:66-69,276-291`), cached and served at
  `GET /relay/proof/:msg_id` (`relay_service.rs:128,988-1005,1053-1082`).
* **GC and expiry** — periodic TTL sweep with operator fees and sender refunds
  (`relay_service.rs:1119-1135`; `storage/src/operator.rs:267`).

### 2.2 The E2E envelope and the client

`captp/src/store_forward.rs`:

* `QueuedMessage` — destination, ciphertext, ephemeral PK, **per-sender causal
  sequence number** ("messages MUST be processed in this order per-sender"),
  TTL, priority (`store_forward.rs:49-67`).
* `MessageRelay` — per-destination bounded queues, enqueue/drain/expire
  (`store_forward.rs:373-465`).
* `StoreForwardClient` — relay list, per-destination sequence counters, and an
  `unacknowledged` map (the retransmission seed) (`store_forward.rs:494-530`).
* Messages already carry capability material, not just chat: `InboxMessage` is
  `Capability | SturdyRef | Encrypted` (`storage/src/inbox.rs:53`;
  `relay_service.rs:888-895`) — a capability cert can be granted *to an offline
  party* through a mailbox today.

### 2.3 The identity execution cursor (the reconciliation safety pin)

`node/src/execution_cursor.rs` exists because the unconditional "finalized
prefix is append-only" assumption is **machine-checked FALSE**: an honest
lagging validator that catches up can land finalized blocks in the *middle* of
the already-executed region (`TauPrefixMonotone.lean`'s `lagBase → lagGrown`
counterexample, reproduced against the real Rust `tau` at
`execution_cursor.rs:172-265`). The corrected design tracks executed blocks by
identity and serves "exactly the finalized blocks not yet executed, in the
CURRENT tau order — execution is a set difference" (`execution_cursor.rs:21-30`),
with the prefix-shift surfaced as observability
(`observe_order`, `:128-141`). The tests pin exactly the delay-tolerant story:
*a mid-prefix late arrival executes late, exactly once, and nothing already
executed is re-served* (`:271-323`), and a cursor restored from its persisted
identity set resumes correctly across the reorg (`:358-375`).

Working-tree honesty note: as read today, the body of `pending()` still carries
the pre-fix index slice labeled "CURRENT (pre-fix) semantics … Replaced below
by identity tracking" (`execution_cursor.rs:116-121`) — the cutover is mid-flight
in a parallel lane. This document treats the identity semantics (the module
header + the tests) as the design of record; the cutover landing is a
prerequisite of Wave DT-0 (§7).

### 2.4 Consensus-on-demand and the epistemic tower

* `docs/CONSENSUS-FLEX.md` — the four-tier finality ladder (`Tier.causal`
  eligible only for I-confluent state; `ackThreshold` "under partition degrades
  to tier 1"; `bft` = tau — `CONSENSUS-FLEX.md:35-46`), the conflict relation
  and verb-pair table (§2), the fast path at causal-ack depth (§3), the
  soundness theorems T1–T6 (§4), and the n=1 collapse (every tier degenerates
  to immediate local finality, `:521-527` citing `blocklace_sync.rs:546-559`).
* `metatheory/Dregg2/Authority/Epistemic.lean` — the constructive tower:
  `Knows pocket a φ := ∃ w, pocket a w ∧ Discharged φ w` (`:99-103`) — knowledge
  is *production of a witness*, which needs no network; `CommonAt` (C_G) is
  finality at depth over a `FinalityFloor` whose growth "is exactly what a
  network partition suspends" (`:162-181`, the law at `:166-167`); and the
  killer theorem `commonAt_guard_partition_safe` (`:1052`): two partition sides
  can never BOTH reach the supermajority the C_G constructor demands
  (`superMajority_gt_half`), so a finality-guarded settlement cannot
  double-fire across a partition.
* `metatheory/Dregg2/Distributed/LaceMerge.lean` — `SameView` (`:198`) and the
  end-to-end `merge_convergence_to_state` (`:297`): two replicas that merged
  the same causally-closed blocks execute to the same state (modulo the named
  `hOrder` order-agreement residual, `:252-261`, discharged for merged replicas
  by `tauOrder_deterministic`).

---

## 3. DESIGN — the bundle/custody protocol over dregg primitives

### 3.1 The mapping (DTN vocabulary → dregg machinery)

| DTN / LTP concept | dregg realization | status |
|---|---|---|
| Bundle | `QueuedMessage` / `InboxMessage`: an E2E-encrypted, content-hashed envelope whose payload is self-certifying (a signed turn, a capability cert, a sturdy ref) | EXISTS (`store_forward.rs:49-67`; `storage/src/inbox.rs:53`) |
| Bundle node | The mailbox cell: a bonded RelayOperator cell hosting CapInbox queues | EXISTS (`relay_operator.rs`, `relay_service.rs`) |
| Custody transfer | A **custody receipt**: operator-signed acceptance at enqueue, Merkle `DequeueProof` at delivery | HALF-EXISTS (proofs exist & are served; acceptance is unsigned — see 3.2) |
| Custody accountability | Bond + the cell program's `slash` case (no-drain-without-dispute) | EXISTS as program shape; the evidence→slash pipe is unwired (shared with `CONSENSUS-FLEX.md` §7) |
| Bundle expiry / lifetime | `ttl_blocks` + GC sweep with refunds | EXISTS (`store_forward.rs:62-64`; `relay_service.rs:1119-1135`) |
| Bundle priority | `MessagePriority` eviction hint | EXISTS (`store_forward.rs:36-44`) |
| Route policy | `route_table_root` DFA caveat — the relay proves each dispatched message matches its committed route table | EXISTS (`relay_operator.rs:24,226-243`) |
| Contact-graph routing | — | BUILD (§6) |
| Fragmentation/reassembly | — | BUILD (§6) |

### 3.2 The custody receipt (the one genuinely new wire object)

Custody transfer must be a RECEIPT — accountable, bondable, slashable-on-drop.
Today the two ends are asymmetric:

* **Delivery** is already proof-carrying: each drained message yields a
  `DequeueProof { old_root, new_root }` (`storage/src/queue.rs:66-69`), cached
  and retrievable per message (`relay_service.rs:988-1005,1053-1082`).
* **Acceptance** is not: `POST /relay/send` returns
  `SendResponse { queue_root, position, bytes }` — *unsigned JSON*
  (`relay_service.rs:545-550,928-932`). The sender holds nothing it can show a
  third party.

**The design:** acceptance issues a signed **CustodyReceipt**:

```
CustodyReceipt {
  content_hash,            // inbox_message_content_hash (relay_service.rs:1197-1217)
  inbox_owner,             // destination
  old_queue_root, new_queue_root,   // the enqueue's Merkle transition
  accepted_at_height,
  deliver_or_refund_by,    // accepted_at + ttl (the custody deadline)
  operator_sig             // Ed25519 over the domain-separated tuple
}
```

and delivery upgrades the existing `DequeueProof` to a signed
**DeliveryReceipt** (same fields + the drain signature already required of the
owner, `relay_service.rs:950-973` — so delivery is *jointly* attested:
operator signs the dequeue, owner's drain auth proves the recipient asked).

The accountability calculus then closes:

* sender holds `CustodyReceipt`;
* operator discharges custody by exhibiting `DeliveryReceipt` OR the GC refund
  record before `deliver_or_refund_by`;
* failure to discharge = **EvidenceOfDrop** = (CustodyReceipt, current height >
  deadline, absence-of-delivery challenge) — a turn presenting it against the
  operator's bond cell drives the already-modeled `slash` case
  (`relay_operator.rs:37-43`: `BoundedBy{0, witness:7}` + `FieldDelta{7, +1}`).
  Slashing is an ordinary `move` under an ordinary Pred — no new verb; this is
  item-for-item the evidence machinery of `CONSENSUS-FLEX.md` §7 (evidence
  value + codec → Pred atom → bond escrow cell → identity binding), reused for
  a second evidence type.

Witness-first discipline (the adjudication organ's deep rule,
`docs/ORGANS.md:111-115`): where the operator CAN exhibit a delivery receipt,
the exhibit decides; only the absence claim ("never delivered") is a residue —
and it is decided by the deadline arithmetic plus the operator's failure to
exhibit, not by a tribunal.

### 3.3 Weld vs build, honestly

**WELDS** (machinery exists; connect it):

1. Seed the CapInbox factory at boot + the SDK **crank** (drain → owner's
   executor as deferred turns) — already chartered as the mailbox organ's weld
   (`docs/ORGANS.md:54-59`).
2. Wire the captp E2E box into the relay client path: `handle_send` today takes
   raw base64 into `InboxMessage::Encrypted` (`relay_service.rs:876-895`);
   `StoreForwardClient::prepare_message` already produces the right envelope
   (`store_forward.rs:536-...`) — connect them, and migrate addressing off
   `FederationId` per the in-file TODO (`store_forward.rs:24-26`).
3. Persist + sign the delivery proofs: `delivery_proofs` is a RAM HashMap
   (`relay_service.rs:128`) — move to the relay's durable state file alongside
   the template mirror.
4. Bond → real stake: `RelayConfig.bond_amount` is self-asserted config
   (`relay_service.rs:51-62`); the slot-0 mirror must be funded from a real
   escrow cell (the R3 obligation-factory pattern, per `docs/ORGANS.md:106-109`)
   so the slash case has a well to drain.
5. The identity-cursor cutover (`execution_cursor.rs:116-121`, in flight) — the
   reconciliation safety pin everything in §4 leans on.

**BUILDS** (new):

1. The signed CustodyReceipt + the drop-evidence object + its Pred atom (§3.2).
2. A real dequeue-proof **verifier**: the current check accepts any proof where
   `old_root != new_root` (`storage/src/queue.rs:411-424` — "the proof is valid
   if old_root and new_root differ") — that is a placeholder, not a Merkle
   transition verification. The verifier must recompute the transition (the
   prover side already produces honest roots; only verification is stubbed).
3. Fragmentation/reassembly for large payloads (§6).
4. Contact-graph routing (§6).
5. The retained/attested persistence axis applied to mailboxes (§6).

### 3.4 Which DTN guarantees are free vs work

**Free (fall out of self-certification + existing machinery):**

* *Integrity & authenticity* — AEAD transcript binding + signed turns inside.
* *Confidentiality from carriers* — the X25519 box; sender-anonymous to the
  relay (`store_forward.rs:233-237`).
* *Replay immunity* — strand seq at insert + nullifiers + the identity cursor.
* *Exactly-once execution across arbitrary delay* — the identity cursor
  (`execution_cursor.rs:271-323` is literally this test).
* *Non-omission evidence shape* — content-addressed lace + per-creator seq
  gaps make silence refutable.
* *Multi-hop indifference* — the lace merge is an idempotent commutative join
  (`LaceMerge.lean:138-173`); a bundle arriving via three relays and twice is
  the same bundle.

**Work (needs the builds above):**

* *Custody accountability end-to-end* — acceptance receipts + slash wiring +
  the real proof verifier. Most of the parts exist; none are connected.
* *Delivery liveness* — **priced, never proven.** A bonded relay can still
  silently drop; the bond makes drop cost more than carriage, it does not make
  delivery a theorem. This is the honest DTN bound (DTN itself has no stronger
  answer) and it stays named.
* *Large payloads* and *routing* — absent (§6).

---

## 4. DESIGN — contact-window reconciliation

### 4.1 The shape

An offline or partitioned participant **keeps committing locally** and
**reconciles at the next contact window**:

* **Offline commit = the n=1 collapse.** A disconnected node is, for the
  duration, an n=1 system over its own strand: every actionable local block is
  immediately final *locally* in seq order (`blocklace_sync.rs:546-559`, per
  `CONSENSUS-FLEX.md:117-119`). The consensus-on-demand frame prices this
  precisely: local commits are group-safe only on the **coordination-free
  fragment** — turns whose footprint is I-confluent with anything concurrent
  (`Dregg2/Confluence.lean`, the conflict table at `CONSENSUS-FLEX.md` §2.2).
  The non-monotone fragment (§6) does not get to pretend.
* **Contact = lace merge + cursor absorption.** Reconciliation is not a special
  protocol: it is the ordinary frontier exchange. The merged lace is the join
  (`laceIds_mergeLace`, `LaceMerge.lean:111`); both sides recompute the same
  view (`SameView`, `:198`) and hence the same finalized order and state
  (`merge_convergence_to_state`, `:297`). The returning node's late blocks may
  land **mid-prefix** in everyone else's finalized order — that is exactly the
  `TauPrefixMonotone` shape, and the identity cursor absorbs it: the late
  blocks execute late, exactly once, and the prefix-shift fires as a metric,
  not a fault (`execution_cursor.rs:32-37,128-141`).

### 4.2 The epistemic reading (the correctness frame)

The tower gives the exact semantics of being offline:

* **K_you grows offline.** `Knows` is witness-production (`Epistemic.lean:99-103`)
  — verifying received receipts, producing new signed turns, checking proofs:
  all local. Your pocket fills in the tunnel.
* **C_G politely waits for the window.** `CommonAt` requires the finality floor
  (`:162-181`), and floor growth is "exactly what a network partition suspends"
  (`:166-167`). Crucially this waiting is SAFE, not merely sad:
  `commonAt_guard_partition_safe` (`:1052`) proves two partition sides can
  never both reach the C_G supermajority — a finality-guarded effect (a
  settlement, a council certification) fires on at most one side *ever*. The
  partition cannot fork finality; it can only postpone it.
* The contact window is then literally the moment K-material drains upward into
  C_G: the offline node's exhibited witnesses enter the floor, finality
  resumes, and the guards that were waiting discharge.

### 4.3 The drill — n=3 + persvati-offline (the concrete first test)

Topology: three nodes (two local + persvati, the 24-core build box). persvati
drops for D wave-lengths; the two survivors continue; persvati returns and
reconciles.

**What the protocol DOES (stage A — today's tau-only node):** with
`superMajority n = 2n/3 + 1` (`BlocklaceFinality.lean:98` via
`CONSENSUS-FLEX.md:278`), n=3 gives supermajority = 3: ratification needs all
three. So with persvati down, **finality freezes cleanly** — by design, not by
bug (n=3 tolerates zero faults for liveness; n=4 is the smallest topology where
finality survives one silent node). The two live nodes keep accepting turns,
growing their strands, gossiping — the lace grows; the finalized prefix does
not. On persvati's return: frontier exchange, persvati's catch-up blocks
complete the stalled waves (possibly landing mid-prefix), tau resumes, all
three converge.

**Success criterion (stage A):**

1. **Clean freeze:** during the partition, finalized height flatlines on both
   sides; zero C_G-guarded effects fire anywhere (the
   `commonAt_guard_partition_safe` shape, observed live).
2. **No local damage:** the live nodes' laces grow monotonically; nothing is
   rolled back or refused-for-being-offline.
3. **Exactly-once reconciliation:** after the merge, all three nodes hold the
   identical tau order and state root; the union of executed sets equals the
   finalized set — zero re-executions, zero skipped blocks, persvati's own
   offline-issued turns finalized. `dregg_tau_prefix_shifts_total` may tick
   (expected if catch-up lands mid-prefix) and is **absorbed without operator
   intervention** — the metric ticking while state stays correct is the
   *positive* signal that the identity cursor earned its keep.
4. **Mailbox continuity:** a message sent to persvati during the partition via
   the relay is drained on return with a verifying dequeue proof, and the
   deferred turn it carries executes through the crank.

**Stage B (after the consensus-on-demand fast path lands):** the same drill,
plus: turns on the **monotone fragment** (grow-only registry writes, credits,
shield inserts, disjoint-well moves — the commute column of
`CONSENSUS-FLEX.md` §2.2) continue past local commit to tier-causal finality
on the live pair during the partition (`Tier.causal`/the partition-degraded
`ackThreshold`, `Finality.lean:32-37`), while the non-monotone fragment
demonstrably waits. Success adds: monotone-fragment turns committed during the
partition are tau-confirmed unchanged at contact (the T1/T3 agreement,
observed); a deliberately-injected contended pair (same-well debit on both
sides) is correctly held back and adjudicated by tau after contact, exactly
once.

---

## 5. The keystone theorem-to-be

**Contact transparency (delay-tolerance soundness).** Stated precisely:

> Let T be a set of issued turns whose blocks all pass the verified insert
> (signed, causally complete, equivocation-free), and let σ be any *contact
> schedule* — an assignment of block-arrival times to replicas allowing
> unbounded delay, arbitrary reordering, duplication, and partition, subject
> only to eventual delivery to every correct replica. Then for every correct
> replica r, once σ quiesces:
>
> 1. **(state)** r's executed state equals the state of the never-partitioned
>    schedule over the same T; and
> 2. **(exactly-once)** every finalized turn in T was served to r's executor
>    exactly once; and
> 3. **(no fork)** at no point under σ did two replicas hold *conflicting*
>    finalized turns,
>
> where (1) holds unconditionally for the coordination-free (I-confluent)
> fragment of T, and for the full T with finality-time as the only difference
> (contended pairs finalize when tau can run, in the order tau picks — the same
> on every schedule that delivers the same lace).

The proof decomposes onto theorems that exist plus two that are scheduled:

* **(transport-independence)** the merged lace is schedule-invariant: the join
  is commutative/associative/idempotent on the content-addressed keyset —
  `laceIds_mergeLace` + the algebra (`LaceMerge.lean:111,138-173,179`). EXISTS.
* **(view determinism)** same lace ⇒ same finalized order
  (`tauOrder_deterministic`, `BlocklaceFinality.lean:311`) and same fast
  verdicts (T4 ackDepth determinism, `CONSENSUS-FLEX.md:354-359`). EXISTS /
  afternoon.
* **(execution agreement)** same order through the verified executor ⇒ same
  state — `merge_convergence_to_state` (`LaceMerge.lean:297`), with the
  `hOrder` residual discharged by view determinism (`:252-261`). EXISTS.
* **(exactly-once)** the identity-cursor invariant: executed set = finalized
  set, regardless of which poll a block arrives in — necessary BECAUSE
  unconditional prefix-monotonicity is refuted (T5,
  `Dregg2/Consensus/TauPrefixMonotone.lean`; the corrected
  `tau_finalized_prefix_monotone` is conditional, and the cursor is the
  mechanism that does not need the condition). EXISTS as Rust tests
  (`execution_cursor.rs:271-323`); the Lean statement over the cursor model is
  a wave.
* **(no fork)** `commonAt_guard_partition_safe` (`Epistemic.lean:1052`) for
  C_G-guarded effects, plus T6 (fast-final ⊆ eventually-tau-final,
  `CONSENSUS-FLEX.md:394-416`) for the fast tier. T6 is a wave, gated on T5's
  node-side closure.
* **(linearization agnosticism, the I-confluent fragment)** T1 (proved,
  `OnDemandFeasibility.fastpath_linearization_agnostic`) generalized to T3
  Mazurkiewicz trace convergence (`CONSENSUS-FLEX.md:340-352`) — the EPOCH-sized
  centerpiece, shared with the consensus-on-demand lane rather than duplicated
  here.

What the theorem deliberately does NOT claim: **liveness.** Eventual delivery
is a hypothesis of σ, purchased economically by custody accountability (§3.2),
never proven. Delay-tolerance is a *safety* theorem: nothing breaks, nothing
forks, nothing executes twice, no matter how long the tunnel.

---

## 6. The honest obstructions (named, with their closure lanes)

* **The non-monotone fragment genuinely cannot progress offline.** Same-well
  debits that fund only one (`coupled_no_schedule_agnostic_commit` — the
  machine-checked impossibility pole), revoke-vs-exercise, council vote
  tallies, cross-cell 2PC, same-nullifier spends: these REQUIRE an order, and
  no relay, bond, or proof manufactures one across a partition. The design
  response is to *price and surface* it (the classifier demotes them; receipts
  say which tier and epoch they read), never to paper it. The sharpest cost is
  **revocation latency**: a revoke issued on one side does not bind the other
  side until contact — the bounded-staleness window must ride in Q, per the
  `CONSENSUS-FLEX.md` §8 recommendation. Closure lane: the per-cell finality
  tier + classifier weld (CONSENSUS-FLEX staging).
* **Large-payload fragmentation/reassembly does not exist.** Quotas are
  byte-denominated (`relay_operator.rs:21-22`; `relay_service.rs:213-219`) but
  a bundle is one message. Design shape: a *manifest bundle* — the mailbox
  carries the content hash + erasure-coding parameters; the body rides the
  content-addressed store (built, currently unreachable —
  `docs/ORGANS.md:62-66`), fetched at contact via the read-cap/verify-cap
  separation. This makes fragmentation a STORAGE-organ weld plus a small
  manifest codec, not a relay rewrite. Closure lane: W-organ-1 storage connect,
  then Wave DT-3.
* **Contact-graph routing does not exist.** The client picks from a flat relay
  list (`store_forward.rs:494-507`); the DFA route table
  (`relay_operator.rs:24,226-243`) is a *policy* commitment (what a relay will
  carry), not a *route* computation (which relays reach the destination, when).
  LTP/CGR-style scheduled-contact routing is real new work; for the
  phone-in-tunnel regime, one-hop hosted inboxes (what exists) cover the need,
  so this is honestly deferrable to the multi-hop/interplanetary regime. Wave
  DT-3.
* **TTL vs unbounded delay.** Expiry-with-refund (`relay_service.rs:1119-1135`)
  is right for the priced hosted-inbox economy, but "unbounded" delay needs the
  persistence axis (`docs/ORGANS.md:19-26`): a mailbox declared
  `retained(window)` or `attested` holds custody across months at the
  corresponding price; the custody deadline (§3.2) is then the declared window,
  not a global default. Parameter, not fork — exactly the parameterization
  discipline.
* **The dequeue-proof verifier is stub-grade** (`storage/src/queue.rs:411-424`
  accepts any root pair that differs). Until closed, custody receipts are
  signed claims, not checked transitions. Wave DT-0, small.
* **The evidence→slash pipe dead-ends** (shared finding,
  `CONSENSUS-FLEX.md:530-545`): the bond is config-asserted, the slash case has
  no caller, the strand-key↔bond-cell identity binding lives in node config.
  Closure: the §7 evidence machinery, with drop-evidence as the second
  evidence type alongside equivocation.
* **n=3 freezes under one fault** — by arithmetic, not accident
  (supermajority(3)=3). The drill embraces it (the freeze IS stage-A behavior);
  the polis-scale answer is n≥4 topology, not protocol change.

---

## 7. Staging

**Wave DT-0 — the accountable mailbox (rides W-organ-1's mailbox crank;
mostly welds).** Seed CapInbox at boot; the SDK crank (drain → deferred
turns); wire the captp E2E box into the relay client; the signed
CustodyReceipt on accept + signed DeliveryReceipt on drain; persist proofs
durably; close the dequeue-proof verifier. Prerequisite riding alongside: the
identity-cursor cutover lands (in flight). **Exit:** drill stage A passes —
clean freeze, exactly-once reconciliation, mailbox continuity (§4.3).

**Wave DT-1 — custody with teeth (shared with the adjudication organ /
CONSENSUS-FLEX §7).** Bond as a real escrow cell; EvidenceOfDrop codec + Pred
atom; slash as an ordinary move from the bond well; strand-key↔bond-cell
binding. **Exit:** a relay that provably dropped a custodied bundle is slashed
on-protocol in a negative e2e test.

**Wave DT-2 — offline progress (rides the consensus-on-demand staging, not
duplicated here).** Fast-path shadow mode on the n=3 devnet; tier-causal local
commit for the I-confluent fragment; receipts annotated with finality
mode + epoch-read. **Exit:** drill stage B — monotone fragment progresses
through the partition, contended pair held and adjudicated exactly once.

**Wave DT-3 — scale and reach.** Manifest bundles over the connected storage
organ (fragmentation); `retained(window)` mailboxes; contact-graph routing for
multi-hop. **Exit:** a payload larger than one inbox quota crosses a partition
in fragments and reassembles with verified hashes.

**Theorem lane (parallel):** the Lean exactly-once cursor statement (wave);
T6 (wave, after T5's node closure); T3 trace convergence (epoch, shared) —
composing into the contact-transparency theorem of §5.

---

## 8. The single highest-leverage first implementation step

**Make custody acceptance a signed receipt** (§3.2): have `POST /relay/send`
return an operator-signed `CustodyReceipt` over (content_hash, old_root,
new_root, height, deliver-or-refund deadline), persisted with the existing
delivery proofs. It is a small change to a live route
(`relay_service.rs:853-933`), it converts the already-running relay economy
into the accountable bundle-node primitive, and every later wave — slashing,
the drill's mailbox-continuity criterion, multi-hop custody chains — hangs off
exactly this object. The machinery it composes with (Merkle queues, dequeue
proofs, owner-auth, bonds, the slash program case) all exists; this is the
weld that makes the existing parts mean what the delay-tolerant polis needs
them to mean.
