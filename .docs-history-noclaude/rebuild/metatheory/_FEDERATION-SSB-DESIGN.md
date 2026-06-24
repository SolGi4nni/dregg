# Federation as Secure-Scuttlebutt-on-Crack — the comprehensive verified federation model

> READ-ONLY design pass. No code changed. This is the blueprint that directs the
> distributed-protocol verification wave. It grounds every heritage claim in
> `file:line` and every SSB claim in a fetched reference URL.

**One-line thesis.** dregg's **STRAND** = a single participant's append-only,
hash-linked, signed log — i.e. a **Secure Scuttlebutt feed**. The **blocklace** is
a DAG that weaves strands together (`captp/src/lib.rs:114`,
`blocklace/src/lib.rs:80-94`), and dregg *extends SSB on crack*: it adds (a) **BFT
finality** over the lace (the Cordial-Miners `tau` rule, already modeled +
verified in `metatheory/Dregg2/Distributed/BlocklaceFinality.lean`, commit
`c251c09b6`), (b) **object capabilities** riding on top (CapTP: swiss/handoff/GC),
and (c) **double-spend safety** (nullifier sets, attested roots). SSB gives
subjective trust, offline-first eventual consistency, and feed identity; it
*lacks* finality, capabilities, and double-spend protection — which is exactly
the surface dregg occupies. This document specifies the comprehensive model and
the Lean verification plan to make it real and *verified at n>1*.

---

## §0. What SSB actually is (fetched references)

SSB (Tarr et al., *"Secure Scuttlebutt: An Identity-Centric Protocol for
Subjective and Decentralized Applications"*, and the SSBC protocol guide) is:

- **Feed identity = an Ed25519 key pair.** "An identity is an Ed25519 key pair and
  typically represents a person, a device, a server or a bot." Each identity owns
  a **feed**: "a list of all the messages posted by that identity."
  (https://ssbc.github.io/scuttlebutt-protocol-guide/ — *Keys and identities*,
  *Feeds*.)
- **Append-only hash-linked log.** "once a message is posted it cannot be
  modified." Each message carries `previous` (hash of the prior message),
  `author`, `sequence`, `timestamp`, `hash`, `content`, and a signature; the
  message ID is a hash of the message including its signature.
  (https://ssbc.github.io/scuttlebutt-protocol-guide/ — *Message format*.) The
  `previous`-hash chain "prevents somebody with the private key from changing the
  feed history after publishing."
  (https://miguelmota.com/blog/getting-started-with-secure-scuttlebutt/)
- **Gossip replication.** `createHistoryStream` requests "all messages in the feed
  that are newer than the latest message you know about"; EBT (Epidemic Broadcast
  Tree) replication uses vector clocks for efficiency.
  (https://ssbc.github.io/scuttlebutt-protocol-guide/ — *Replication*,
  *EBT Replication*.)
- **Follow graph + partial replication.** Feeds publicly announce follows, forming
  a directed graph; clients replicate "feeds within n hops" — a transitive-interest
  model that is spam- and sybil-resistant and scales to thousands of participants.
  (https://ssbc.github.io/scuttlebutt-protocol-guide/ — *Follow graph*;
  Kermarrec et al., *"Gossiping with Append-Only Logs in Secure-Scuttlebutt"*,
  DICG 2020, https://dicg2020.github.io/papers/kermarrec.pdf.)
- **Blobs = off-chain content.** Binary data referenced by content hash, stored and
  fetched separately from feeds.
  (https://ssbc.github.io/scuttlebutt-protocol-guide/ — *Blobs*.)

**What SSB deliberately LACKS** (the room dregg occupies):
- **No global consensus / no finality.** SSB has no Byzantine agreement; peers
  gossip incrementally. (Wikipedia, *Secure Scuttlebutt*,
  https://en.wikipedia.org/wiki/Secure_Scuttlebutt.)
- **Forks are unresolved.** A key holder *can* publish two different messages at
  the same `sequence` (an **equivocation/fork**). SSB detects this only by feed
  divergence and has no built-in resolution — a forked feed is typically treated
  as poisoned/blocked, but consensus over the fork is out of scope.
- **No object capabilities.** SSB is a social-graph database; there is no
  bearer-secret authorization, no delegation, no revocation, no GC.
- **No double-spend protection.** SSB has no nullifier/ledger semantics.

The structural correspondence to dregg is exact:

| SSB | dregg heritage | file:line |
|---|---|---|
| feed identity (Ed25519) | strand / block `creator` (NodeKey = pubkey) | `blocklace/src/lib.rs:72-73`, `captp/src/lib.rs:114-122` |
| `previous` hash-link | `Block.predecessors: Vec<BlockId>` (BLAKE3) | `blocklace/src/lib.rs:86-87`, `118-131` |
| `sequence` | `Block.sequence: u64` ("monotonic per creator") | `blocklace/src/lib.rs:84-85` |
| message signature | `Block.signature: [u8;64]` (Ed25519) | `blocklace/src/lib.rs:92-93` |
| feed = author's log | strand = creator's chain; `tips[creator]` is the feed head | `blocklace/src/lib.rs:171-172`, `240-247` |
| `createHistoryStream` / EBT | cordial dissemination "send blocks you think they need" + Plumtree gossip | `blocklace/src/lib.rs:37-41`, `net/src/gossip.rs:1-23` |
| follow graph | **MISSING** (see §A) — replication is committee-driven, not follow-driven | — |
| blobs (off-chain) | Sovereign-cell off-chain state (`reason_hash`/`checkpoint_hash` commit on-chain) | `cell/src/cell.rs:13-19`, `cell/src/lifecycle.rs:42-81` |
| **(none — SSB lacks)** finality | `ordering.rs::tau` super-ratification | `blocklace/src/ordering.rs:1-25`, verified `BlocklaceFinality.lean` |
| **(none)** capabilities | CapTP swiss/handoff/GC | `captp/src/{sturdy,handoff,gc}.rs` |
| **(none)** double-spend | nullifier set + attested root | `cell/src/nullifier_set.rs`, `federation/src/types.rs` AttestedRoot |

---

## §A. The heritage under-designs (honest, cited)

The heritage federation is **fragmented and under-designed**. The most important
gaps, each grounded:

### A1. **The blocklace `insert()` is a SSB feed with the safety checks removed.**
`Blocklace::insert` (`blocklace/src/lib.rs:189-225`) checks only **causal closure**
(all predecessors present). It does **NOT**:
- verify the block's **Ed25519 signature** against `creator` (no `verify` call
  anywhere in `blocklace/src/lib.rs` — confirmed by grep; the module header at
  `:14` *claims* "signature matches creator" is verifiable, but `insert` never
  does it);
- enforce **`sequence` monotonicity** per creator (a strand can skip/repeat seq);
- **reject equivocation on write** — it blindly does
  `self.tips.insert(block.creator, block_id)` (`:218`), silently overwriting the
  feed head. Two blocks at the same `(creator, sequence)` are **both stored**.

Equivocation is only caught *much later*, during finality
(`ordering.rs::has_equivocation_in_past`, `blocklace/src/ordering.rs:118-141`), and
only for the *leader* of a wave. **This is precisely the SSB fork gap** — except
SSB at least treats a fork as feed-poisoning, whereas the heritage stores the fork
and hopes `tau` filters it. There is no "no-equivocation-without-detection" invariant
at the strand layer. **This is the single biggest under-design and the first
beachhead (§D).**

### A2. **The FederationId / StrandId / GroupId muddle.**
The identifiers are aliased without an enforced model:
- `pub type GroupId = FederationId` (`captp/src/lib.rs:112`) — group ≡ federation.
- `pub type StrandId = [u8;32]` (`captp/src/lib.rs:114-122`) — "typically derived
  from the strand owner's public key," but the derivation is **unspecified**; it is
  a bare alias with no constructor binding it to `NodeKey` (the block creator).
- CapTP sessions carry **both** `peer_strand: Option<StrandId>` *and* legacy
  `peer_id`, with a "prefer `peer_strand` when both set" rule
  (`captp/src/session.rs:27-36`) — a half-finished migration.
- `DreggUri.federation_id` is "semantically a `GroupId`"
  (`captp/src/uri.rs:68-72`) but typed as raw `[u8;32]`.
- Five `TODO(unified-lace): migrate FederationId to StrandId` markers across
  `captp/src/{handoff.rs:30-31, gc.rs (header), store_forward.rs}` — **Phase B of
  the unified-lace migration was never completed.** GC is keyed by `FederationId`
  (the group) when the design says it should be keyed by `StrandId` (the bilateral
  peer) — `captp/src/gc.rs` header TODO.

The model muddle: **is the unit of identity the feed (strand) or the committee
(federation)?** SSB answers cleanly: the feed. dregg needs *both* — strand =
feed-identity, federation = a *committee of strands* that attests finality — but the
heritage conflates them (`GroupId = FederationId`, strand-id underived).

### A3. **Membership churn is convention, not mechanism.**
`Federation::apply_epoch_transition` (`federation/src/federation.rs:246-271`)
rebuilds the committee and mints a fresh `federation_id = H(sorted(members)||epoch)`
but: (a) there are **no `join`/`leave`/`expel` operations** — the design doc itself
flags this as unresolved (`FEDERATION-UNIFICATION-DESIGN.md` §7.Q2:559-578); (b)
identity-over-time across rotations is "by convention" via blocklace continuity, with
the two-level `federation_chain_id` alternative left open (§7.Q4:600-615); (c) the
**`GovernedReferenceGroup` (`blocklace/src/constitution.rs`) and `Federation::members`
are parallel data structures with nothing enforcing they agree** (§7.Q6:638-657).
So "who is allowed to write to this lace" has two sources of truth.

### A4. **The Morpheus dead-code carcass.**
`federation/src/lib.rs:89-103` documents that the Morpheus BFT simulator
(`node.rs` + `transport.rs`) is **"legally dead"** — `dregg-blocklace` is the live
consensus path — but it survives because `teasting`, `wasm`, and `demo/sdk-consensus`
still import it. The crate re-exports a `MorpheusFederation` "pending its deletion."
The federation crate is thus *two federations*: a live attestation context and a dead
simulator.

### A5. **Cell-migration safety is unproven.**
`CellLifecycle::Migrated { to, attestation, migrated_at }`
(`cell/src/lifecycle.rs:49-59`) is a terminal state recording the destination cell
id and an attestation hash. But nothing in the heritage proves the **double-existence
/ authority-loss** safety property: that a migrating cell cannot be *live at both*
the source and destination simultaneously, and cannot *lose* its capabilities in
transit. `Migrated` is "terminal" at the source (`lifecycle.rs:340` test) but the
*atomicity* of source-retire ⟺ destination-accept across two federations' laces is
not modeled. This is a distributed commit problem (2PC-shaped over two BFT laces) and
the heritage has only the data fields, not the protocol.

### A6. **Partial / follow-graph replication is absent.**
The heritage replicates the *whole* lace via cordial dissemination
(`blocklace/src/dissemination.rs`) + Plumtree gossip (`net/src/gossip.rs`). There is
**no follow-graph-driven partial replication** — no notion of "replicate strands
within n hops of mine." For a federation this is fine (the committee replicates
everything), but for the *open mesh* of strands (the SSB-scale vision) it does not
scale, and there is no spam/sybil resistance at the strand layer (the committee
membership is the only sybil gate).

### A7. **The mixed-trust boundary is documented but not enforced inline.**
`captp/src/lib.rs:5-37` cleanly states the trust split (executor-trusted
session/swiss/GC vs trustless-when-proven handoff[Ed25519]/store-forward[X25519]),
and the Lean `Exec/CapTP.lean` mirrors handoff non-amplification. But the
**executor-trusted** half (swiss table fidelity, GC ref-count correctness) has **no
verified enforcement** — it is an *assumption* (`captp/src/lib.rs:29-30`: "Federation
executor honestly maintains swiss table and session state"). At n>1 with a Byzantine
executor, swiss-table or GC corruption is unmodeled.

---

## §B. The comprehensive dregg2 federation model — SSB extended + verified

The model is **three layers**, each a clean extension of an SSB concept, with the
dregg additions named explicitly.

### B1. Identity layer — STRAND = FEED (extended with a derivation law)
- A **strand** is an append-only, hash-linked, Ed25519-signed log owned by one key.
  `StrandId := H_strand(creator_pubkey)` — **bind the derivation** (closes A2): the
  strand id is a pure function of the owner's public key, exactly as an SSB feed id
  IS the Ed25519 pubkey. A block's `creator` field *is* its strand membership; no
  separate strand registry.
- **SSB does X; dregg extends to X+:** SSB: feed = (author, seq, previous, sig).
  dregg: same, **plus** the block may carry multiple `predecessors` (a DAG, not a
  pure chain) so strands cross-reference into a *lace* — but the **own-author
  back-edge** (`previous`) is the SSB spine and must be present and unique
  (the seq-monotone, no-fork invariant — see C1).

### B2. Lace layer — DAG of strands, with BFT finality (the crack)
- The **lace** is the DAG woven from all strands a federation replicates.
  Causal-closure on insert is the SSB "have-all-prior" property generalized to a DAG
  (`blocklace/src/lib.rs:198-208`).
- **SSB does X; dregg extends to X+BFT:** SSB has no finality — a fork is just two
  feeds. dregg runs **Cordial-Miners `tau`** (`ordering.rs`): waves, round-robin
  leaders, approval→ratification→super-ratification, producing a *total order* with a
  *finalized prefix* that cannot revert under <1/3 Byzantine. **This layer is already
  modeled + verified** (`BlocklaceFinality.lean`: `finalLeaders_one_per_wave`,
  `tauOrder_deterministic`, `finalized_prefix_monotone`, plus a Rust differential).
- **Equivocation policy (closes A1):** at the *strand* layer, a second block at an
  existing `(creator, seq)` is **rejected on insert** (fail-closed), and the
  conflicting pair is retained *only as a slashable equivocation proof* — not as two
  live feed heads. The lace layer's `tau` equivocation guard becomes a *defense in
  depth*, not the *only* line.

### B3. Membership layer — committee = a set of strands (follow-graph generalized)
- A **federation** is a *committee of strands* authorized to anchor finality — the
  `members: Vec<PublicKey>` (`federation/src/federation.rs:91-92`) reinterpreted as
  *the set of strand ids that may be wave leaders*. `federation_id =
  H(sorted(members)||epoch)` (`identity.rs`) is the committee commitment.
- **SSB does X; dregg extends to X+governance:** SSB's follow-graph is *subjective*
  (each peer picks who to replicate). dregg keeps a subjective **follow layer** for
  *partial replication* of non-committee strands (closes A6: replicate committee
  strands fully + followed strands within n hops) **and** adds an *objective*
  **committee** for *finality*. Membership churn (`join`/`leave`/`expel`, closes A3)
  is an **epoch transition block** written to the lace by the *outgoing* committee,
  signed by quorum, that names the new committee — making rotation a first-class,
  attested, replayable lace event rather than a convention. The single source of
  truth for "who may write" is the committee-defining block, with
  `GovernedReferenceGroup` a *view* over it (resolve A2/A6 muddle via Option B in
  §7.Q6).

### B4. Capability layer — CapTP on the strands (objects over feeds)
- **Cells** (`CellId`) are objects hosted by a federation (`Hosted`: full state on
  the lace) or self-hosted (`Sovereign`: only a 32-byte commitment on the lace, state
  off-chain like an SSB blob) — `cell/src/cell.rs:13-19`.
- **CapTP rides at MIXED trust** exactly as documented (`captp/src/lib.rs:5-37`):
  - **swiss / sturdy** (`sturdy.rs`): a `dregg://fed/cell/swiss` URI; the swiss number
    is a bearer secret (SSB has no analog). *Executor-trusted* mapping.
  - **handoff** (`handoff.rs`): the 3-vat Granovetter introduction, Ed25519-signed,
    *trustless-when-proven*. Already mirrored in Lean
    (`Exec/CapTP.lean::handoff_non_amplifying / handoff_same_target`).
  - **GC** (`gc.rs`): distributed ref-counting; *executor-trusted*. Re-key by
    **StrandId** (the bilateral peer), closing the Phase-B TODO.
  - **store-forward** (`store_forward.rs`): X25519-encrypted offline queue; the
    blocklace *is* the store-forward layer (`store_forward.rs:15-19`) — this is SSB's
    offline-first gossip plus end-to-end encryption.
- **Cell mobility (closes A5):** migration is a **two-lace atomic handoff**: a
  *retire-intent* block on the source lace (cell → `Migrated{to, attestation}`) and an
  *accept* block on the destination lace, bound by `attestation = H(source_retire ||
  dest_accept)`, such that finality of *both* is required before the cell is live at
  the destination and dead at the source. No interval of double-existence; authority
  (capability set) is carried in the accept block.

### The model in one paragraph
> A **strand** is a Secure-Scuttlebutt feed: an append-only, hash-linked,
> Ed25519-signed log keyed by its owner's public key, with monotone sequence and a
> no-equivocation-without-detection guarantee enforced *at write*. The **lace** is the
> DAG woven from strands; over it dregg runs Cordial-Miners `tau` to give SSB the one
> thing it lacks — **BFT finality** (a non-reverting total-ordered prefix under <1/3
> Byzantine). A **federation** is a committee of strands authorized to anchor that
> finality, with membership churn as attested epoch-transition blocks and a subjective
> follow-graph for partial replication of non-committee strands. On top ride **object
> capabilities** (CapTP): swiss bearer-secrets and distributed GC at executor-trusted
> level, handoff certificates and store-forward at trustless-when-proven level — and
> **cells** that are Hosted (state on lace) or Sovereign (commitment on lace, state
> off-chain as SSB-style blobs) and **migrate** between federations via a two-lace
> atomic handoff. dregg is SSB + capabilities + BFT-finality + double-spend-safety,
> and every layer's security property is to be discharged in Lean at the real
> distributed setting (n>1), building on the already-verified finality kernel.

---

## §C. The security properties to VERIFY in Lean (the heart, n>1)

For each: the precise property, and **whether it is non-trivial at n>1** (the real
distributed setting — never an n=1 collapse). The single-machine principle is
explicitly *rejected* here: these must hold with multiple mutually-distrusting,
possibly-Byzantine strands.

### C1. Feed integrity — append-only, hash-linked, no-equivocation-without-detection
**Property.** For any strand `s` and any two blocks `b1, b2` with
`b1.creator = b2.creator = s` and `b1.seq = b2.seq`: either `b1 = b2`, or the pair
`(b1, b2)` constitutes a **detectable, attributable equivocation proof** (both signed
by `s`, same seq, distinct id), and the lace **never holds two live tips for `s`**.
Plus: `b.id` is a collision-resistant function of `(creator, seq, preds, payload)`
(`lib.rs:118-131`) and the `previous`-edge chain is unforgeable-without-`s`'s-key.
**n>1?** *Essential.* At n=1 there is no equivocation (one honest author). The whole
point is a *Byzantine* strand owner double-publishing to *different* peers — only at
n>1 does "without detection" have content (peer A sees b1, peer B sees b2; the
property says any peer seeing both can *attribute and slash*). This is the SSB fork
problem solved.

### C2. Lace finality — non-reverting, deterministic, one-leader-per-wave ✅ DONE
**Property.** A wave anchors **at most one** final leader; the total order is a
deterministic function of `(lace, participants)`; the finalized prefix is
**append-only** under lace growth. **Status: ALREADY VERIFIED** —
`metatheory/Dregg2/Distributed/BlocklaceFinality.lean` (commit `c251c09b6`):
`finalLeaders_one_per_wave`, `tauOrder_deterministic`, `finalized_prefix_monotone`,
`#assert_axioms`-clean, *with* a Rust differential against `ordering.rs::tau`.
**n>1?** Yes — it is proved over a multi-participant lace with the super-majority
`2n/3+1` threshold; the safety theorem is precisely a quorum-intersection argument
that is vacuous at n=1. This is the **template** for every subsequent beachhead
(faithful executable Lean model of the Rust function + property + executor connection
+ Rust differential).

### C3. Capability confinement — swiss bearer secret
**Property.** A cell capability cannot be enlivened without knowledge of its 32-byte
swiss number; possession IS authorization; revocation (removing the swiss entry)
makes prior URIs un-enlivenable (`sturdy.rs` `EnlivenError::NotFound`).
**n>1?** Non-trivial: at n>1 the swiss table is *replicated* across the committee, so
confinement must hold against a *partial* view (a peer that has the URI but not the
table entry must fail-closed) and against a *Byzantine committee member* who must not
be able to mint a swiss entry it was not given. *Partially mirrored* already:
`Exec/CapTP.lean` `import_handle_confers_exactly`. Gap: the *executor-trusted* swiss
fidelity (A7) needs a model where a Byzantine executor cannot fabricate entries.

### C4. Handoff unforgeability — Ed25519 certificate, Granovetter discipline
**Property.** A `HandoffCertificate` cannot be forged without the introducer's
private key; the introduced capability is **non-amplifying** (`granted ≤ held`) and
**same-target** (`granted.target = held.target`); the result is a *revocable
forwarder*. **Status: mirrored** — `Exec/CapTP.lean` proves
`handoff_is_introduce`, `handoff_non_amplifying` (reusing `introduce_non_amplifying`),
`handoff_forwarder_revocable`; the heritage `handoff.rs:58-73` enforces
`Amplification` / `TargetMismatch` matching the Lean spec.
**n>1?** Essential and *the* trustless-when-proven property: a *third party* (vat B)
validates A's cert about C's capability *without trusting any executor* — the whole
construction is meaningless at n=1. The crypto discharge (Ed25519 `validate_handoff`)
is an honest §8 seam (a `Laws.Discharged` carrier), not Lean-proved EC math.

### C5. GC safety — never reclaim a live ref, never leak
**Property.** The distributed ref-count for an exported capability reaches zero
**iff** no peer holds a live reference; revocation at zero never strands a live ref
(safety) and a dropped ref always eventually decrements (liveness/no-leak).
**n>1?** Essential — ref-counting is *across federations* (`gc.rs` Export/Import
sides); at n=1 there is nothing to count. Byzantine subtlety: a peer must not be able
to (a) forge a `DropRef` for *another* session to prematurely revoke (heritage
mitigates via `SessionId` binding, `gc.rs` `RefCount`/`SessionId`), nor (b) withhold a
`DropRef` to leak. **Currently OPEN in Lean** — `Exec/CapTP.lean:43-45` flags
distributed-GC liveness as a documented `-- OPEN:` (relates to cross-vat-cycle
impossibility). This is a *hard* beachhead (liveness under partial synchrony).

### C6. Store-forward forward-secrecy
**Property.** A relay storing X25519-encrypted queued messages
(`store_forward.rs:9-13`) learns only ciphertext — it cannot read, forge, or
selectively-tamper messages (authenticated encryption); it can only delay or drop
(no safety violation, only liveness).
**n>1?** Essential — the relay is a *distinct distrusted party* from sender and
recipient; the property is *about* that third party. The crypto (ChaCha20-Poly1305
AEAD over X25519 DH) is an honest §8 seam; the Lean content is the *protocol* property
("relay sees only ciphertext, delivery is causal-order").

### C7. Cell-migration safety — no double-existence, no authority loss
**Property.** A migrating cell is **never simultaneously live** at source and
destination: there is no reachable global state where both the source lace shows the
cell `Live` and the destination lace shows it `Live`. Dually, the capability set is
**conserved** across the migration (authority neither amplified nor lost). The bind is
`attestation = H(source_retire || dest_accept)` with *both* finalized.
**n>1?** *The* most distributed property — it is a **cross-lace atomic commit** over
*two independent BFT federations*, each at n>1. At n=1 (single machine hosting both)
it collapses to a local state transition with no interesting failure mode; the real
hazard (partition between source and destination federations leaving the cell
double-live or lost) only exists at n>1 with two distinct committees. This is a
2PC/atomic-commit-over-BFT problem and is the deepest beachhead.

### C8. Membership-churn safety — epoch monotonicity, no two committees
**Property.** Across an epoch transition: a block finalized under epoch `e`'s
committee remains valid forever; a new-epoch receipt never verifies under the
old committee and vice-versa (`federation.rs:602-604`); and there is never a
reachable state with **two distinct live committees** for the same federation chain
at the same height (no committee fork). **n>1?** Essential — committee fork is a
Byzantine-rotation attack meaningful only at n>1.

**Priority order (by leverage × distributed-realism):**
1. **C1 feed integrity** — closes the worst under-design (A1), foundational to all else, concrete and self-contained.
2. **C4 handoff** — mostly DONE; finish the n>1 third-party framing and connect to executor.
3. **C7 migration safety** — the deepest distributed property; high product value (cell mobility is the sovereignty story).
4. **C5 GC safety** — currently OPEN; hard liveness; do after C1/C7 give the lace-state vocabulary.
5. **C3 confinement / C6 store-forward / C8 churn** — round out the suite.
(C2 finality is DONE and is the template.)

---

## §D. The Lean verification plan + ordering (the consensus template)

**The template** (set by `BlocklaceFinality.lean`): each beachhead is
(i) a *faithful, executable Lean model* of the actual Rust function (cite
`file:line`, mark FAITHFUL vs SIMPLIFIED-projection vs named-residual honestly),
(ii) a *real distributed property* proved at n>1, (iii) a *connection to the verified
executor/state* (`Exec.ConsensusExec` / `RecordKernelState`), and (iv) a *Rust
differential* (Lean model reproduces the Rust function's output on a concrete
multi-node trace). `#assert_axioms`-clean.

**Sequence of beachheads, building on `BlocklaceFinality.lean`:**

1. **`Dregg2/Distributed/StrandIntegrity.lean` — feed integrity (C1). FIRST.**
   - *Model:* a `Strand` as the per-creator projection of `Lace` (filter blocks by
     `creator`), with `strandSeq`, `strandPrev`, `strandTip`. Mirror
     `Block.id` (`lib.rs:118-131`) and the insert causal-closure (`lib.rs:198-208`).
   - *Property:* `no_equivocation_without_proof` — for any lace, any two same-`(creator,seq)`
     blocks are equal *or* form an `EquivocationProof` (both signed, distinct id);
     and `strand_single_tip` — a *fork-rejecting* insert keeps one tip.
     Prove `id` injectivity on distinct content (collision-resistance as a named
     `Laws.Discharged` hash seam, exactly as finality treats BLAKE3).
   - *Executor connection:* the strand-tip *is* the SSB feed head the executor reads;
     connect to `RecordKernelState` cell-receipt-chain (the cell's own append-only
     log is a strand).
   - *Differential:* construct a 3-strand lace in Lean + the same in Rust
     (`blocklace`), exhibit that the Lean fork-detector and a (proposed) Rust
     `insert`-with-equivocation-check agree on accept/reject. **Also surfaces the A1
     bug as a differential MISMATCH against today's `insert` (which accepts forks).**
   - *n>1:* the property is *about* two peers with divergent views of one strand.

2. **`Dregg2/Distributed/HandoffProtocol.lean` — handoff unforgeability (C4).**
   - Mostly built (`Exec/CapTP.lean`). *Add:* the n>1 third-party framing (vat B
     validates without an executor), connect the cert validation to a lace event
     (the swiss-entry registration is a block on the target federation's lace), and a
     Rust differential against `handoff.rs::validate_handoff` accept/reject on
     amplifying / target-mismatch / expired / replay certs.

3. **`Dregg2/Distributed/MigrationSafety.lean` — cell mobility (C7).**
   - *Model:* two laces `(src, dst)`, a `RetireBlock` on `src` and `AcceptBlock` on
     `dst` bound by `attestation`. Reuse `BlocklaceFinality.finalized_prefix_monotone`
     to express "both finalized."
   - *Property:* `no_double_live` (no reachable joint state with both laces showing
     the cell `Live`) + `authority_conserved` (capability set equal across the
     handoff — reuse the `introduce_non_amplifying` / conservation machinery).
   - *Connection:* `CellLifecycle::Migrated` (`lifecycle.rs:49-59`) is the source
     terminal state; the dst `Live` cell carries the migrated cap set.
   - *Differential:* against the `node`'s migration path (where it exists) /
     `lifecycle.rs` transition guards.
   - *n>1:* two distinct BFT committees, partition-tolerant atomic commit.

4. **`Dregg2/Distributed/GcSafety.lean` — distributed GC (C5).** Hardest; resolves
   the `Exec/CapTP.lean:43-45` OPEN. Model Export/Import ref-counts
   (`gc.rs`), prove `no_premature_revoke` (zero ⇒ no live importer) under
   `SessionId`-bound `DropRef` (Byzantine-drop-forge resistance), and the liveness
   `eventual_decrement` under partial synchrony (the genuinely hard half — may need a
   fairness/justness hypothesis as in `Proof/Fairness.lean`).

5. **Round-out:** `ConfinementSwiss.lean` (C3, Byzantine-executor swiss fidelity),
   `StoreForwardSecrecy.lean` (C6, relay-sees-ciphertext protocol property),
   `MembershipChurn.lean` (C8, epoch monotonicity + no-committee-fork, reusing the
   `federation_id = H(members||epoch)` commitment).

**Concrete FIRST beachhead: `StrandIntegrity.lean` (C1).** It is the most
self-contained, closes the worst under-design (A1, the SSB-fork-with-checks-removed
`insert`), is foundational to every later layer (strands are the substrate), follows
the proven finality template exactly, and its Rust differential *immediately
documents the A1 insert bug* as a Lean-vs-Rust mismatch — turning the design audit
into an executable witness.

---

## §E. dregg-vs-dreggrs segregation

This comprehensive Lean federation becomes the **dregg primary** (the
verified-by-construction specification of the real distributed protocols), with the
heritage Rust crates (`federation/`, `blocklace/`, `captp/`, `net/`) as **dreggrs**
— the heritage / differential reference. The segregation discipline (consistent with
the existing dregg1/dregg2 ledger, `_DREGG1-DREGG2-UNIFICATION-LEDGER.md`):

- **Primary = Lean.** `metatheory/Dregg2/Distributed/*` is the *authoritative* model
  of strand integrity, finality, handoff, migration, GC, churn. The properties in §C
  are the *specification* the running system must satisfy.
- **Reference = Rust (dreggrs).** The heritage crates are kept as the *executable
  differential oracle* — **but never as a correctness oracle**: where the Lean model
  and the Rust *disagree*, the disagreement is a *finding*, not a matching target
  (per the swap-framing memory: matching a buggy oracle launders the bug). The A1
  differential is the archetype — Lean *correctly* rejects the fork, Rust `insert`
  *incorrectly* accepts it; the differential records the gap and directs the fix.
- **Cutover gating.** A heritage path is migrated/deleted only after its Lean
  counterpart proves the property *and* the differential agrees on the *intended*
  (fixed) behavior — never before. The Morpheus carcass (A4) is the first deletion
  candidate (already "legally dead"); the under-designed `insert` (A1) is *fixed to
  match the Lean model*, not deleted.
- **The dead Morpheus simulator** (`federation/src/node.rs` + `transport.rs`,
  `lib.rs:89-103`) is explicitly *not* part of dregg-primary; it is dreggrs scaffolding
  pending deletion as `teasting`/`wasm`/`demo` migrate to the real blocklace.

---

## Appendix: heritage file map (for the verification wave)

- `blocklace/src/lib.rs` — `Block` (strand entry) `:80-94`; `id()` `:118-131`;
  `insert()` (the A1 under-design) `:189-225`; `tips`/frontier `:171-247`;
  `causal_past` `:266`.
- `blocklace/src/ordering.rs` — `tau` finality `:1-25`; `has_equivocation_in_past`
  `:118-141`; wave/leader arithmetic `:143-175`; approval/ratification `:177-336`.
- `federation/src/federation.rs` — unified `Federation` `:88-347`;
  `apply_epoch_transition` `:246-271`; `KnownFederations` `:378-453`.
- `federation/src/lib.rs` — crate map + dead-Morpheus note `:89-103`; BFT thresholds
  `:140-156`.
- `captp/src/lib.rs` — trust model `:5-37`; `GroupId`/`StrandId` aliases `:109-122`.
- `captp/src/{handoff,sturdy,gc,store_forward,session,uri}.rs` — the capability layer
  + the 5 `TODO(unified-lace)` Phase-B markers.
- `cell/src/cell.rs` — `CellMode` Hosted/Sovereign `:13-19`.
- `cell/src/lifecycle.rs` — `CellLifecycle::Migrated` `:49-59`.
- `net/src/gossip.rs` — Plumtree gossip transport `:1-23`; `net/src/causal.rs` causal
  DAG.
- `metatheory/Dregg2/Distributed/BlocklaceFinality.lean` — the DONE finality
  beachhead + verification template (commit `c251c09b6`).
- `metatheory/Dregg2/Exec/CapTP.lean` — the existing handoff/pipeline mirror
  (`handoff_non_amplifying`, GC OPEN at `:43-45`).
- `docs-old/FEDERATION-UNIFICATION-DESIGN.md` — the heritage's own open-questions
  ledger (§7.Q1–Q8: membership, identity-over-time, governed-group overlap).
