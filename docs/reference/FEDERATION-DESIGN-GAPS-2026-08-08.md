# Our federation against the reconfiguration literature: what we got right, what is a hole, and what to build

**Date:** 2026-08-08
**Method:** read-and-think. **No protocol code changed by this pass.**
**Companion:** `docs/reference/DYNAMIC-COMMITTEE-LITERATURE-2026-08-08.md` — what the papers settle.
Read §0 there first; it overturns the "no paper treats committee growth" claim this doc is measured against.

Every claim about our code carries `file:line`, verified at source. Every claim about a paper carries
paper + section. Where I am relaying a reading lane rather than a quotation I checked, I say so.

Citation shorthand as in the companion: **DZ** = Duan & Zhang, *Foundations of Dynamic BFT* (S&P 2022).
**LL** = Li & Lesani, *Reconfigurable Heterogeneous Quorum Systems* (DISC 2024). **LPR** = Lewis-Pye &
Roughgarden, *Permissionless Consensus*. **CM** = *Cordial Miners*. **GA** = Shapiro, *Grassroots
Architecture*.

---

## 0. THE τ-SHAPED VERDICT — yes, there is a known construction, and we are missing its second half

**The question:** is there a known construction we should be implementing instead of what we invented?

**The answer:** we invented two different things and they have opposite verdicts.

> **The join *channel* is a reasonable invention.** No paper specifies how a stranger asks to be
> admitted, because every paper assumes the request simply arrives as a client request (DZ Fig. 4:
> `broadcast ⟨SUBMIT, c, ⟨JOIN, pk⟩⟩ to M_c`). Our self-certifying gossip envelope solves a real
> transport problem the papers never face. Keep it.
>
> **The *install discipline* is a known construction and we have essentially none of it.** DZ (S&P
> 2022) formalises it, proves it, implements it in 10k LOC of Go and benchmarks it to n=30; Rondo
> (2024) transplants it onto HotStuff, by one of DZ's own authors; LPR §15.3 states the boundary rule
> for a chained protocol with the consistency violation spelled out in fn. 51. **The thing all three
> have and we do not is: a configuration number, an install point determined by a certificate rather
> than by local time, and a rule that a new member does not count until it has the state.**

**And the shape is the τ deviation, exactly, one axis over.** `CONSENSUS-FROM-SOURCE` §0 found that
our τ orders *the live lace* where CM orders *the anchor's fixed closure*. The reconfiguration
finding is: **our τ reads the *live roster* where it must read a *committed* one.** Same defect,
same cause (a function that should take a committed object as input takes the local view instead),
same consequence (two honest nodes compute different results from the same evidence). The code
already knows the principle and states it — `blocklace/src/finality.rs:271-274`, in
`MembershipAction::Join`'s own doc comment:

> at the SAME point in the order, which is what "committed" has to mean for a value the tau leader
> schedule is a function of.

That sentence is correct, it was written for `Join`, and **`auto_evict_equivocator` violates it**
(§2.1).

Three corrections to the brief that commissioned this pass, since a wrong premise propagates:

1. **We *do* have a leave path.** `MembershipAction::Leave { node_id }` exists at
   `blocklace/src/finality.rs:284`, is proposed by `propose_membership(add=false)`
   (`node/src/blocklace_sync.rs:3378`), is reachable from the CLI as `--remove` / `--rotate`
   (`docs/guide/FEDERATION-JOIN.md`), and is used by timeout auto-leave
   (`node/src/blocklace_sync.rs:19016`). The hole is not "no leave"; it is **no drain rule** (§2.6).
2. **`798e87a33` is a test-only commit** — 121 lines in `node/src/execution_cursor.rs`. It is the τ
   fork reproduction, not the membership work.
3. **`blocklace/src/finality.rs:1477` is inside a doc comment.** The actual `UnenrolledCreator`
   refusal is `blocklace/src/finality.rs:1509-1517`, and it is **per-block ingest rejection**, not a
   halt. The halt is a separate mechanism at `node/src/blocklace_sync.rs:2179-2197` (§2.9).

---

## 1. Each thing we built: known construction, reasonable reinvention, or a mistake with a name

| What we built | Verdict | Against what |
|---|---|---|
| Self-certifying `JoinRequest` gossip envelope | **Reasonable invention, and well built** | no paper specifies the ask; ours is genuinely narrow (§1.1) |
| Member sponsorship (any member authors the proposal) | **Reasonable, with a named defect** | GSN WL's single sponsor is the closest analogue; our lack of cross-member dedup is a real bug (§2.7) |
| ML-DSA proof of possession | **Reasonable invention, no analogue** | CM §2 assumes keys are known; the hazard is ours because hybrid identity is ours |
| Ratification by `⌊2n/3⌋+1` of the **OLD** roster | ✅ **Known construction, and correct** | DZ Lemma C.9; Rondo §IV; LPR §15.3 — all require the *old* configuration to certify its successor |
| ML-DSA key committed at ratification | ✅ **Correct, and it is DZ's `chist` instinct** | DZ Lemma C.1 — the membership certificate must carry what the next configuration needs |
| Threshold recomputed from the live roster | ⚠ **Right formula, wrong binding** | DZ/Rondo `Q_c` is per-*configuration*; ours is per-*moment* (§2.2) |
| `federation_id` stable across membership change | ✅ **Correct product call, but it is not a config number** | it is `H(genesis committee ‖ epoch 0)`; the roster identifier is a *separate* thing we lack (§2.3) |
| Restart replay of membership from the chain | ✅ **This is DZ's configuration history, in the right place** | DZ §VI.B; two gaps remain (§2.10) |
| `auto_evict_equivocator` applying immediately, locally, off-chain | ❌ **A mistake the literature names** | LL §5 *Reconfiguration Attacks*, in cardinality form (§2.1) |
| Finalization votes tallied against the live roster + live threshold | ❌ **Violates the property dynamic BFT exists to add** | DZ §III.E *same configuration delivery* (§2.2) |
| A ratified joiner voting before it holds the state | ❌ **A safety gap, not a performance one** | DZ §V.B + the proof of Lemma C.9 (§2.4) |
| No configuration number on any consensus message | ❌ **The enabling absence under most of the above** | DZ, Rondo, LPR, OG all carry one (§2.3) |
| `auto_approve_joins` enabled by a `.devnet` file existing | ❌ **Converts the roster into a resource any peer can force** | LPR §8.3 reactivity — and reactivity is what Thm. 11.1 kills (§2.8) |

### 1.1 The join channel, on its merits — this part is good and should be said

Verified at source. `GossipEnvelope::JoinRequest` (`net/src/gossip.rs:1051`) is admitted by
`try_admit_join_request` (`net/src/gossip.rs:3176`), reached **only** from the `None` arm of the
`peer_keys` lookup (`net/src/gossip.rs:2308`, registry read `:2293-2296`); returning `false` falls
through to the unchanged `unknown_sender` refusal + `Penalty::ProtocolViolation` (`:2318-2332`).

Validation is ordered cheapest-first, which is the right DoS shape: decode (`:3185-3191`) → 8 KiB
body cap (`:3194`, `MAX_JOIN_REQUEST_BODY` at `:185`) → `blake3(candidate_public_key) == sender`
(`:3209`) → per-IP budget 6/60 s (`:3220`) → **then** Ed25519 verify (`:3226`).

**The carve-out really is narrow.** Admission writes no registry entry, joins no topic, adds no
eager/lazy slot, no cache entry, no relay, no publish; `body` is never interpreted at the gossip
layer. A *registered* sender's `JoinRequest` is symmetrically dropped (`:2845-2858`). Both halves are
pinned by tests: `an_unregistered_key_may_send_exactly_one_join_request` (`:3391`) and
`an_unregistered_key_may_send_nothing_else` (`:3416`).

This solves a problem the literature does not pose, and solves it well. The rest of this document is
about what happens *after* the request is accepted.

---

## 2. The holes, ranked by what would bite a running federation

The ranking criterion is the one the brief asked for: **which of these is "a property assumed by
construction elsewhere and merely hoped for here"** — the τ shape. The top four all are.

---

### 2.1 ⚑⚑⚑⚑ `auto_evict_equivocator` is an unratified, off-chain, restart-reverted roster mutation

**This is the worst thing in the membership machinery, and it is live today.**

`blocklace/src/constitution.rs:174-185` (verified at source):

```rust
pub fn auto_evict_equivocator(&mut self, proof: &EquivocationProof) -> bool {
    let Some(evicted) = proof.equivocator_ed25519() else { return false; };
    if !self.participants.contains(&evicted) { return false; }
    self.participants.retain(|k| k != &evicted);
    self.threshold = compute_threshold(self.participants.len());
    self.version += 1;
    true
}
```

with the doc comment above it (`:165`): *"this does NOT require a vote -- it applies immediately."*
The only production trigger is `node/src/blocklace_sync.rs:5580`, inside `handle_push`, iterating
`outcome.equivocations` from `catchup::apply_with_buffering` — i.e. **whichever equivocations this
node's local DAG application happened to surface, from this node's inbound gossip batch, at this
node's wall-clock moment.**

**The premise is right and the mechanism is wrong.** CM §3 does say correct miners repel
equivocators, and an equivocation proof *is* self-evident, so **no vote is needed**. But
self-evidence buys you agreement on the *verdict*, not on the *position in the order* — and the
roster is an input to τ. Five consequences, each verified:

1. **No on-chain record.** `committee_replay::derive_from_lace` folds only `Payload::MembershipVote`
   blocks (`node/src/committee_replay.rs:225`). An auto-evict leaves **no trace in the lace**, so it
   is **silently reverted on restart** while a peer that did not restart keeps the smaller roster.
2. **Divergent thresholds.** `:183` recomputes `threshold` from the shrunken set on the evicting node
   only. Node A at `n=3, T=3` and node B at `n=4, T=3` now disagree about what a quorum *is*.
3. **A third divergent view on the same node.** `auto_evict` never calls
   `apply_committee_change`/`votes.reconfigure` (those are reached only from `apply_passed_proposal`,
   `node/src/blocklace_sync.rs:18930`), so after an auto-evict the constitution says `n−1` while
   `FinalizationVoteCollector.committee` still says `n` and **still counts the evictee's votes**.
4. **It changes the τ participant set.** `poll_finalized_blocks` re-reads
   `constitution.current.participants` every poll (`node/src/blocklace_sync.rs:2098`). Different
   participant sets ⇒ different leader schedules ⇒ different τ orders ⇒ the fork class `798e87a33`
   reproduced.
5. **`Constitution.version` bumps** (`:184`) but is never on the wire, so no peer can even detect
   the divergence.

**This is LL §5's reconfiguration attack in cardinality form**, and LL's closing sentence is the
operative one: *"the attack can be successful if the time to send and receive updates is longer than
the time to process a transaction."* And it is exactly the mechanism DPRB leaves unanalysed —
App. A's `convicted ← convicted ∪ {id}` with *"correct processes can subsequently exclude the
misbehaving party from the system"*, with App. E.1 filing *"a reconfiguration mechanism that detects
and evicts misbehaving users"* as an open question (companion §5.4).

The asymmetry is the tell: **the Join path was hardened** — self-certification, PoP, quorum, on-chain
payload, replay-on-boot. **Eviction has none of it.**

**Design → §3.4.**

---

### 2.2 ⚑⚑⚑⚑ Finalization votes are tallied against the live roster and the live threshold, with no pin

`node/src/finalization_votes.rs:248,255`: the collector holds **one** `committee: HashSet<[u8;32]>`
and **one** `quorum_threshold: usize` — not indexed by block, height, or epoch. Admission
(`:537`, `:543-551`) gates against the live field; `assembled_quorum` (`:490`) compares against the
live `self.quorum_threshold` (`:517`). `reconfigure` (`:420-430`) is called from
`apply_committee_change` (`node/src/blocklace_sync.rs:3285`).

**So: whose roster counts is whoever's roster is live at the instant `record` runs.**

The code has one real mitigation and its docstring states the argument (`:412-419`, verified at
source): blocks *already* attested stay attested, the `attested` set is **sticky**, and the
reconfiguration is authorised by the old committee's quorum, *"so there is no instant in which an
unattested committee holds finalization authority."*

**That argument covers blocks that already crossed. It does not cover blocks in flight.** Concretely:
on a join `n: 4 → 5`, `T: 3 → 4`, a block sitting at **3 of 4 votes — already a quorum** — loses that
status the moment `reconfigure` runs and needs a fourth. Nodes that apply the transition at different
points in their local poll cycle **disagree about whether that block is attested.** On a leave it
goes the other way. Aggravating: `assembled_quorum`'s PQ-key drop (`:503-506`) means a persisted
restart anchor assembled across a reconfigure can silently fall below threshold and yield `None`.

**This is precisely the property DZ added the whole "dynamic" apparatus to get.** DZ §III.E, the
enhanced total order: *"if a correct replica in configuration `c` delivers a request `m` with a
sequence number, and another correct replica in configuration `c′` delivers `m′` with the same
sequence number, then `m = m′` **and `c = c′`**."* Rondo restates it as its Thm. 10. **A vote must
name the configuration it is a vote in, or "did this reach quorum" is not a well-posed question.**

⚠ **The Lean theorem cited to justify this design is about a different object.** The docstring at
`node/src/finalization_votes.rs:418` credits *"the epoch-handoff no-gap property
(`EpochReconfig.lean::epoch_handoff_no_gap`)"*. `metatheory/Dregg2/Distributed/EpochReconfig.lean`
models `federation/src/epoch.rs` — its `EpochConfig`/`Transition`/`verifyTransition` cite
`epoch.rs:31-42`, `:67-80`, `:314-382` throughout — and **`federation::epoch::verify_epoch_transition`
and `apply_epoch_transition` have no production callers**: a repo-wide grep over `node/src`,
`blocklace/src`, `sdk/src` finds only `federation/src/epoch.rs` itself, `federation/src/epoch_diff.rs`
(`#[cfg(test)]`), `federation/src/federation.rs`, and doc comments. The live path is
`ConstitutionManager::apply_if_passed` → `apply_committee_change` → `VoteCollector::reconfigure`.
**The theorem is real and the citation does not reach the code it is cited in.** (Separately, and
already known to the repo: the Lean `quorumThreshold n = n − n/3` differs from the deployed
`(n*2/3)+1` at every `3 ∣ n`; `blocklace/src/ordering.rs:308-318` documents exactly this and
`federation/src/epoch_diff.rs:102,149` tests the `≥` direction. That divergence is handled — the
uncalled-module one is not.)

**Design → §3.1, §3.2.**

---

### 2.3 ⚑⚑⚑⚑ No configuration number on any consensus message — the enabling absence

Verified at source. **`Block`** (`blocklace/src/finality.rs:293-338`) carries `creator`, `ed25519`,
`seq`, `payload`, `predecessors`, `signature`, `pq_signature`. No epoch, no config id, no
constitution version. `Payload` (`:48-69`) carries none either. **`FinalizationVote`**
(`node/src/finalization_votes.rs:82-131`) carries `block_id, level, merkle_root,
receipt_stream_root, voter, signature, pq_signature, nonce`; the **signed preimage** (`:52-55`) is
`dregg-finalization-vote-v4 ‖ block_id ‖ merkle_root ‖ framed(receipt_stream_root)` — no epoch, no
committee digest. (`nonce` is explicitly unsigned and is a gossip-dedup counter, `:122-131`.)

Three things exist that look like the missing field and are not:

- **`committee_epoch`** — a genesis-descriptor constant, always 0, folded into
  `federation_id = H(sorted_committee_pubkeys ‖ committee_epoch)` (`node/src/genesis.rs:127,505-511`).
  It is **deliberately never advanced** by a membership change, and the reason is good
  (`node/src/blocklace_sync.rs:18968-18972`: it is *"the STABLE chain root the bot / bridge / light
  client pin"*). **That is a correct product decision and a consensus gap at the same time, and the
  fix is not to move `federation_id` — it is to add a second, separate identifier.**
- **`Constitution.version`** (`blocklace/src/constitution.rs:37`), bumped on every amendment
  (`:120,131,145,155,183`), with a full `history` and a `constitution_at_version` lookup (`:475`)
  that has **zero non-test callers**. It appears only in log lines and `/api/membership`.
- **`DerivedCommittee.history`** (`node/src/committee_replay.rs:59-64`) — and this one is *direct
  evidence of the gap*: the restart anchor accepts a quorum from **any** historical committee,
  because it cannot tell which one signed. That workaround exists only because the field does not.

**Every construction in the companion carries this field.** DZ: `c` in every message, and
view-change messages are *forwarded across configuration gaps* on it (Fig. 6). Rondo: `cview`, and
`b.height` determines the epoch. LPR §15.3: epoch `e`, batch `(eN, eN+N]`. OG: `IsValidChain`
derives the configuration **from the candidate chain itself** so a validator can evaluate a block
produced under a roster it has not installed. And the static-BRB papers show the same defect
arriving from a third direction: their erasure codes and Merkle trees are indexed by `n`, so *"a
fragment or root computed under `n` is not decodable or verifiable under `n′`"*, undetectably,
**because `n` is an ambient constant rather than a field on the wire** (companion §5.5).

**Design → §3.1.**

---

### 2.4 ⚑⚑⚑ A ratified joiner votes before it is required to hold the state

`docs/guide/FEDERATION-JOIN.md`: *"At quorum, `participants` grows by your key, `constitution_version`
bumps, and **your node's finalization votes count from the next wave.**"* There is no learner phase,
no state-transfer precondition, and no threshold hold.

**In DZ this is a safety requirement, not a performance one**, and it is used *inside* the safety
proof. §V.B: *"each new replica acts as a learner … **The quorum size, however, still remains the
same as the current configuration.**"* §VI.A: the joiner *"waits until it completes state transfer by
accepting `2f_c+1` `HISTORY` messages. After that, `p_i` participates."* And Lemma C.9 Case (1) leans
on it directly:

> any new replica that joins the system participates in the protocol after it completes state
> transfer from replicas in `c`. Therefore, if any of the `f_c+1` correct replicas is a new replica,
> **it will not accept `m′` if `m` is included in its execution history**.

Rondo has the same shape: `TM` receives proposals and a `catchup` message, but every quorum is
counted over `M_e` (Fig. 14 lines 13/20/24, *"from `⌈(2|M|+1)/3⌉` nodes **in M**"*).

**And OG names why the joiner cannot decide this for itself.** §1: *"it is impossible for a party to
determine whether it is already synchronized"*; Remark 2 prices a rejoining party's stake **as
adversarial** until it holds its synchronising chain. **The protocol must decide readiness, not the
joiner.**

**Design → §3.3.**

---

### 2.5 ⚑⚑⚑ No churn bound — and our threshold formula supports at most two joins per step

Nothing in the tree states a bound on how many members may be admitted in one configuration step.
DZ §III.D makes it an explicit assumption: *"from configuration `c` to `c+1`, at least `Q_c`
`c`-correct replicas are still in `c+1`."*

Instantiating DZ's cross-configuration inequality on our `T(n) = ⌊2n/3⌋+1`
(`blocklace/src/ordering.rs:317`), for `l` joins into a roster of `n`:

```
|Q_c ∩ Q_{c+1} ∩ M_c|  ≥  T(n) + T(n+l) − l − n     must exceed   f = ⌊(n+l−1)/3⌋
```

which asymptotically gives `2 > 2l/3`, i.e. **`l ≤ 2`**. Instantiated: `4 → 7` (three joins) gives
intersection 1 against `f = 2` — **broken**; `7 → 10` gives 2 against `f = 3` — **broken**. Full table
in the companion §1.5. DZ recovers larger `l`, but *only* through the state-transfer mechanism of
§2.4, which we do not have. **Today we have neither the bound nor the mechanism, so we have no
argument at all.**

Rondo has the same gap in the other direction: Lemmas 4/5 quantify over `M_e`/`M_{e+1}` as sets so
the shape admits an arbitrary batch, but §VIII only ever exercises `±1` — *"we add/remove one node at
a time."*

**Design → §3.3 (bound now, relax after the learner phase lands).**

---

### 2.6 ⚑⚑⚑ Leave exists; the drain rule does not

`MembershipAction::Leave` is real (`blocklace/src/finality.rs:284`). What is missing is what happens
between "ratified out" and "stops serving".

Both papers make it explicit. **Rondo** Fig. 14 line 16: a node in `M_{e−1}` but not `M_e` *"waits
until receiving the pre-commit message in epoch `e` **and** delivering all the blocks in epoch `e−1`
before leaving the system"*; Thm. 13's proof adds that a node may not exit until it holds a
`prepareQC` from a **later** epoch proving it is out. **DZ** Dyno-C (§VII, fn. 2): *"any correct
replica `p_i` leaves the system … only after it delivers a `⟨REMOVE, i⟩` request"*, weakenable to
*"after it receives a prepare certificate."*

And DZ §IV is the reason the rule exists, in a sentence that is about us:

> consider a `c_q`-correct replica `p_i` that leaves the system immediately after `c_r` … Another
> correct replica `p_j` … needs to collect `Q_{c_q}` matching messages to deliver `m`. Some
> `c_q`-correct replicas, however, might not be correct any more as they already move to `c_r`.
> Therefore, correct replicas might **not be able to deliver `m`**, creating agreement and liveness
> problems.

**Also unclaimed: the liveness assumption a leave path needs.** Rondo's liveness (Lemma 9, Thms. 11
and 13) rests on *"at least one correct replica in `M_0` that never leaves the system"* — the
permanent relay that forwards view-change traffic across configurations. ⚑ **If we build a general
leave path, check whether our liveness argument secretly depends on the same thing, and if it does,
say so out loud rather than discovering it at n=1.**

**Design → §3.5.**

---

### 2.7 ⚑⚑ Concurrent duplicate sponsorship, and a dead dedup field

`node/src/blocklace_sync.rs:3060` deduplicates a **re-send to the same node**. There is no
coordination *between* members, and the candidate broadcasts to all configured peers
(`run_join_requests_until_member` → `gossip.send_join_request(encoded, &self.peer_addrs)`, `:2946`).
**N auto-approving members ⇒ N concurrent Join proposal blocks for one candidate.**

`PendingJoinRequest.proposed: Option<BlockId>` (`:728`), whose own docstring advertises exactly this
dedup — *"so a re-sent request does not open a second proposal"* — is **dead**: initialised to `None`
at `:3088` and never written or read anywhere in the tree.

Duplicates are inert for safety (the first to reach threshold applies; the rest hit
`blocklace/src/constitution.rs:117`'s `if self.participants.contains(node_key) { return false; }` so
`apply_if_passed` returns `false` **without** `mark_applied`, `:518-536`) but they become
**passed-but-unapplied forever** and leak into `proposal_tallies()` / `GET /api/membership`. Also
`pending_joins` is never removed after ratification (insert `:3088`, read `:3313`), capped at
`MAX_PENDING_JOIN_REQUESTS = 64` (`:733`).

Not a safety hole today. It becomes one the moment two duplicate proposals for the *same* candidate
can pass in *different* configuration steps — which §2.5's missing batch bound permits.

---

### 2.8 ⚑⚑ `auto_approve_joins`, and the LPR framing that makes it worse than it looks

`node/src/lib.rs:2823`, verified verbatim:

```rust
let auto_approve_joins = auto_approve_joins_flag || data_path.join(".devnet").exists();
```

It does **not** skip the quorum. It does two things: auto-sponsor (`:3104`, `:3114`) and auto-approve
(`:18820-18832`). The `(n*2/3)+1` gate is untouched — but since every honest node supplies its vote
immediately, quorum is instantaneous. The flag's own doc names the risk
(`node/src/lib.rs:354-357`), and production policy pins it off
(`poa-curator/src/lib.rs:58,70`: `"auto_approve_joins":false`).

**The literature sharpens the objection.** LPR §8.3 distinguishes **reactive** from non-reactive
protocol-defined resources: a resource is reactive when the environment or other players can *force*
it to change. Our roster is non-reactive — only incumbents can move it — and **that non-reactivity is
exactly what exempts us from LPR Thm. 11.1** (no protocol with a reactive resource satisfies
consistency+liveness in partial synchrony at *any* `ρ > 0`; companion §4.2). **`auto_approve_joins`
makes the roster reactive**: an arbitrary peer's message forces it to change. It is not merely a
loose gate; it moves us across the line the impossibility result sits on.

A stray marker file in a data directory should not do that. **Delete the `.devnet` trigger** (§3.7);
this is a custody/gate question, not a design fork.

---

### 2.9 ⚑⚑ The finality halt is global-per-poll, correct in disposition, with no escape

`node/src/blocklace_sync.rs:2179-2197`. When `participants.len() != admitted.len()` — i.e. an
admitted member has no *committed* ML-DSA key — the poll returns `Vec::new()`. Its own comment:

> FAIL-CLOSED: an admitted current participant has no COMMITTED ML-DSA key (projected < admitted) —
> HALTING finality this poll rather than ordering over a subset (which would fork against a node
> holding the full set).

**The disposition is right and should be kept.** Halting rather than ordering over a subset is the
same instinct as LL's *"we never sacrifice consistency"* (LL §6, §8). But: it is **global, not
per-block** — one missing key stops the whole poll on every node with the same gap — there is **no
timeout, no operator override, no degrade path**, and the only signal is a `warn!`. Pinned by
`joined_validator_without_committed_key_halts_finality` (`:16893`).

The reason this is only ⚑⚑ and not higher: well-formed joins now commit the key at
proposal-registration time (`:18776-18783`), so the normal case does not hit it. It is a
**failure-mode** hazard, and what it needs is not a bypass but *observability* — see §3.6.

---

### 2.10 ⚑⚑ Restart replay: right idea, two documented gaps

`node/src/committee_replay.rs` is genuinely DZ's configuration history in the right place — a pure
fold over the finalized order (`fold_membership_block`, `:84`; `derive_from_lace`, `:225`), called at
boot (`node/src/lib.rs:2537-2542`), returning the `ConstitutionManager` itself so **in-flight vote
tallies survive** (`:212-219` explains why: a fresh manager would make a pending proposal unpassable
on the restarted node while its peers can still pass it — *"a committee divergence"*). It even
handles τ's roster-dependence: each applied amendment `break`s and forces an order recompute
(`:245-276`), for the stated reason at `:22-31`.

Two gaps, both documented in-tree:

1. **`fold_membership_block` discards `ml_dsa_pubkey`** (`node/src/committee_replay.rs:91`
   destructures `MembershipAction::Join { node_id, .. }`). Restoring a joiner as a participant with
   no committed PQ key would trigger §2.9's halt **on every restart**. It is closed by a *separate*
   scan over **all** blocks (not the finalized order) at `node/src/blocklace_sync.rs:4389-4415`, whose
   safety comes from `learn_committee_member_hybrid_key`'s refusal-to-rebind
   (`node/src/state.rs:2735-2742`) **rather than from ratification**. That works, and it means the
   committed-key set is derived by a different rule than the roster is.
2. **`finalized_order` in replay does not apply the enrolled-creator filter the live poll applies**,
   and runs over a lace restored by `from_checkpoint_trusted` — *"no signature, roster, closure or
   equivocation check"* (`node/src/committee_replay.rs:187-199`, which names it as a follow-up). The
   inertness argument is that `record_vote` refuses non-participants
   (`blocklace/src/constitution.rs:302-305`).

---

### 2.11 ⚑ Join requests are replayable indefinitely within a federation

`JoinRequestBody` (`node/src/blocklace_sync.rs:684-698`) carries `version, federation_id,
ml_dsa_pubkey, pq_proof`. The PoP binding (`:701-712`) is
`JOIN_REQUEST_PQ_BINDING_V1 ‖ federation_id ‖ ed25519 ‖ ml_dsa_pubkey` — **no timestamp, no nonce, no
expiry, no sequence number.** Cross-*federation* replay is blocked by `federation_id`; cross-*roster*
replay within one federation is not, because `federation_id` is epoch-stable **by design**
(`:18968-18972`).

The defences are all soft: `is_participant` short-circuit (`:3053-3058`), the per-node `pending`
dedup that dies with the process (`:3060`), and the per-IP gossip budget. So a captured request is
replayable by any third party, from any IP, at any later time — and if the candidate has since left
the roster, or a member restarts and clears `pending_joins`, it **re-opens a fresh sponsorship**.

Pastro's answer to the general form of this is instructive and is in the companion §4.2c:
forward-secure signatures **keyed by configuration height**, rotated at install, so *"processes that
still consider `C` as the current configuration cannot be deceived by a process `p` that was correct
in `C` but not in a higher installed configuration `C′`."* We do not need the full machinery; we
need the binding to name the configuration (§3.8).

---

### 2.12 ⚑ Latent: two threshold derivations that agree only by accident

The live epoch transition passes the constitution's **stored** threshold —
`apply_committee_change(&new_participants, pq_committee, new_threshold)` where
`new_threshold = constitution.threshold()` (`node/src/blocklace_sync.rs:18936`, `:18977`). The **boot**
path instead **recomputes** it from the replayed roster:
`dregg_blocklace::supermajority_threshold(participants.len())` (`node/src/blocklace_sync.rs:4248`).

These agree today because every threshold mutator (`Join`, `Leave`, `auto_evict`) sets
`threshold = compute_threshold(n)`. The one operation that would break it —
`MembershipProposal::AmendThreshold` (`blocklace/src/constitution.rs:191`) — is **unreachable from
the wire**, because `MembershipAction` (`blocklace/src/finality.rs:279-288`) has no corresponding
variant. So `AmendThreshold` and `AmendRoutes` are dead proposal shapes.

Recorded so that whoever wires `AmendThreshold` knows they are arming a divergence, and so that
nobody re-derives this. **Either delete the dead variants or make the boot path read the stored
threshold** — do not leave both.

---

## 3. Designs for what the literature does not answer

The literature answers "how does a *chain* reconfigure". It does not answer **"how does a DAG whose
ordering function reads the roster reconfigure"** — see companion §3, where I name the six DAG papers
searched. The designs below are ours. For each I state what must be proved, because a design whose
proof obligation is unstated is a design that will be shipped without one.

**Sequencing note, and it is the point.** §3.1 is a prerequisite for §§3.2–3.5. Do it first. Do not
ship §3.2 as a "containment" while §3.1 is a "later phase" — that is the substitution
`docs/../CLAUDE.md` names.

---

### 3.1 `config_seq`: a roster identifier on the wire, derived from the committed prefix

**The primitive everything else needs.**

- `Block` gains `config_seq: u32`. `FinalizationVote` gains `config_seq` **inside the signed
  preimage** (`node/src/finalization_votes.rs:52-55`, domain bumped `-v4` → `-v5`).
- **`config_seq` is not free-form: a block's declared `config_seq` must equal the configuration
  derived from that block's own causal past.** This is OG's `IsValidChain` discipline (App. B,
  Fig. 15 derives `S_C^ep` and `η_ep^C` from the candidate chain, never from the local view) and it
  is what lets a validator evaluate a block produced under a roster it has not installed.
- **A receiver that cannot yet derive a block's `config_seq` buffers it** — the same rule CM already
  applies to dangling pointers (CM Alg. 3 line 49). ⚑ *This is the pleasant part:* the blocklace
  already has the buffering discipline that DZ has to add by hand.
- `Constitution.version` becomes the value of `config_seq`, and `constitution_at_version`
  (`blocklace/src/constitution.rs:475`) acquires its first non-test caller.
- `federation_id` and `committee_epoch` **do not change**. The stable chain root stays stable
  (`node/src/blocklace_sync.rs:18968-18972` is right); `config_seq` is a second, separate identifier.

**What re-emits / refuses to load:** every block id changes (`config_seq` is in `canonical_bytes`) ⇒
**re-genesis**. The vote domain bumps ⇒ old votes refuse to verify. `DerivedCommittee.history`'s
accept-any-historical-committee workaround (`node/src/committee_replay.rs:59-64`) is **deleted**, not
kept alongside.

**What must be proved.**
1. **Derivability**: `config_seq(b)` is a function of `[b]` (the closure), hence immutable once `b`
   is signed. Follows from the fold being over the committed membership blocks in `[b]`.
2. **Buffer termination**: the buffer drains, because `[b]` is finite and closed and a block is
   admitted only when its pointers are present (CM Alg. 3:49) — so `config_seq(b)` is computable
   exactly when `b` is admissible. **This should be a theorem, not a comment.**
3. **Refusal is total**: a block whose declared `config_seq` disagrees with its derived one is
   **refused**, not reinterpreted.

---

### 3.2 Install at a wave boundary, gated by an old-configuration certificate

**The rule, stated so it can be checked:**

> A ratified `MembershipAction` in wave `k` **computes** `M_{c+1}` but does not install it. The
> install point is the first wave boundary `k′ > k` such that a **final** leader whose causal past
> contains the ratifying block is itself super-ratified. From `k′` forward, `config_seq = c+1`.

This is Rondo §IV's rule translated to a blocklace: Rondo installs only on a commit certificate over
the epoch's last block signed by **`2t+1` of the old configuration** — *"more than `t+1` correct nodes
in the previous configuration are aware of the new configuration"*. In CM's vocabulary,
super-ratification of a final leader **is** that certificate, and it is already the object our
finality is built on.

**Why a boundary and not "immediately".** LPR §15.3 + fn. 51 give the failure without one: if the
roster may change at an *indirectly* confirmed point, two candidate boundary blocks can each carry
partial certificates and produce **conflicting opinions about the next roster**, and the incoming
members *"may not have been present to implement HotStuff's locking mechanism"*, so they cannot
inherit anything the outgoing set had merely voted on. In a DAG the analogue is direct: two nodes
committing different anchors first would install at different points.

**The DAG-native alternative, and why I am not choosing it.** Hammerhead installs its derived
quantity with **zero lag** and makes laggards apply it retroactively (companion §5.3), bought by a
strong induction over the sequence of derived values *"without skips"* plus quorum intersection
(Obs. 2, Prop. 1). That is a legitimate second option and it is the one native to our substrate.
**But Hammerhead only ever moves leader *slots*, never membership, and its proofs quantify over a
fixed `Π`.** Retroactively re-applying a *roster* change means retroactively re-deciding which votes
counted — i.e. it interacts with §3.3 and with `attested` stickiness in a way nobody has analysed.
⚑ **This is a real design fork and it is ember's call**, not mine to close silently. My
recommendation is the certificate-gated boundary, because the certificate is an object we already
compute; but if the retroactive design is chosen, the obligation it carries is Hammerhead's
induction, stated over rosters, and the "without skips" condition must be enforced not hoped for.

**What must be proved.**
1. **Install agreement**: every honest node installs `c+1` at the same position in the total order.
   Reduces to CM Prop. 9 (τ prefix-monotonicity) *given* §3.1 — which is why the τ re-anchoring in
   `CONSENSUS-FROM-SOURCE` §0 is a prerequisite for this, not an unrelated task.
2. **Cross-configuration quorum intersection over a blocklace**: the DAG analogue of DZ Lemma C.9 —
   a supermajority under `c` and a supermajority under `c+1` intersect in a correct member, *or* the
   `c+1` members state-transferred (§3.3). **This is the central new theorem** and it does not exist
   in the literature for a DAG.
3. **No gap**: there is no wave at which no configuration holds finalization authority. Note that
   this is what `EpochReconfig.lean::epoch_handoff_no_gap` proves — **about a module the node does
   not call** (§2.2). Either re-target that Lean file at the live path or write its twin; do not
   leave the citation pointing at `federation/src/epoch.rs`.

---

### 3.3 A learner phase, a readiness certificate, and a churn bound

**Learner.** A ratified member is `Temporary` from ratification until install. During that window it
receives everything and may author blocks, but **it is not counted in any supermajority test**, and
the threshold stays `T(n_c)`. Directly DZ §V.B / Rondo Fig. 14.

**Readiness must be protocol-decided, not self-asserted.** OG §1: *"it is impossible for a party to
determine whether it is already synchronized."* Concretely: the joiner proves readiness by
**authoring a block whose causal past contains the install anchor** — a claim any other node can
check against the closure, with no new message type. That is the blocklace's own idiom, and it is
cheaper than DZ's `2f+1 HISTORY` messages because the evidence is already a first-class object.

**Churn bound.** Until the learner phase lands, **cap installs at two members per configuration
step** (§2.5's arithmetic). After it lands, DZ's Lemma C.9 argument covers larger batches — but only
because the joiner cannot contradict what it transferred, so **the bound may be relaxed only when the
readiness rule is enforced, not merely present.**

**What must be proved.**
1. `T(n_c) + T(n_{c+1}) − l − n_c > f` for the permitted `l` — arithmetic, checkable, and it should be
   a Lean `theorem` over the actual `supermajority_threshold`, not a `#guard` on four instances.
2. **Readiness soundness**: a member that authored a block whose past contains the install anchor
   holds every committed turn up to the install point.
3. Liveness: a correct joiner eventually becomes ready — needs the dissemination assumption CM
   already uses (Def. 27, *disseminating*).

---

### 3.4 Eviction as an ordered, on-chain action — self-evident but not self-timed

**The fix for §2.1.** Keep CM's insight that an equivocation proof needs no vote; abandon the idea
that it therefore needs no ordering.

- Add `MembershipAction::Evict { proof }`. On observing an equivocation, a member **authors an Evict
  block** carrying the proof — it does not mutate its local roster.
- The roster changes when that block is in the **committed prefix**, at the next boundary (§3.2),
  identically on every node. **No approval votes**: the proof is self-certifying, so `required_votes`
  for `Evict` is zero and it applies on inclusion. The quorum is not doing evidentiary work; the
  order is doing agreement work.
- `auto_evict_equivocator` (`blocklace/src/constitution.rs:174-185`) is **deleted**, not kept
  alongside a new path. Two mechanisms that agree today are two that will disagree later.
- Consequences that fall out for free: it survives restart (it is a `MembershipVote` block, so
  `committee_replay` already folds it); it reconfigures the vote collector through the one existing
  path; `Constitution.version` advances identically everywhere.

**What must be proved.**
1. **Eviction agreement** — every honest node applies the same eviction at the same position. Reduces
   to ordinary blocklace agreement once it is a block, which is the entire point of the change.
2. **The evidence check is deterministic**: `EquivocationProof` validity is a pure function of the
   proof. Note the existing narrowness recorded in `CONSENSUS-FROM-SOURCE` §3: `EquivocationIndex`
   groups by `(creator, round)` (`blocklace/src/ordering.rs:205`) while `detect_equivocation`
   (`blocklace/src/finality.rs:1743`) uses CM's round-independent test. **Two detectors with
   different scopes must not both be able to author an `Evict`.**
3. Liveness: an equivocation observed by a correct member is eventually committed — a correct member
   will author the block, and CM's dissemination assumption carries it.

---

### 3.5 Leave with a drain rule

- A ratified `Leave` takes effect at the same boundary discipline as `Join` (§3.2).
- **The leaver may not stop serving until** (a) it has authored/delivered everything from its last
  configuration and (b) it holds evidence it is out of a **later** configuration — Rondo Fig. 14
  line 16 and Thm. 13, DZ Dyno-C fn. 2. In blocklace terms: until a final leader whose causal past
  contains the `Leave`'s install anchor is super-ratified.
- **State the liveness assumption explicitly.** Rondo's rests on one correct member in `M_0` that
  never leaves. Either adopt that assumption and *write it down*, or prove liveness without it.
  ⚑ Do not discover it at n=1.

**What must be proved.** DZ §IV's failure is the target: after `l` departures, a request delivered
under `c` is still deliverable — i.e. the surviving members hold enough of the old configuration's
certificates. This is DZ Lemma C.9 Case (2), which needs the same cross-configuration intersection
theorem as §3.2.

---

### 3.6 A portable configuration certificate, and making the halt legible

**Certificate.** DZ §VI.B's `chist`: a genesis-rooted, sequentially ordered list of membership
batches, each with a proof of delivery, **verifiable by anyone from `M_0` alone** (Lemma C.1) and
**totally ordered** (Lemma C.2, by quorum intersection at the first divergence). We are close — the
finalized membership blocks *are* a chain — what is missing is the packaging. This is what deletes
`DerivedCommittee.history`'s accept-any-historical-committee workaround, and it is independently what
OG's bootstrap-from-genesis buys.

**The halt (§2.9) needs observability, not a bypass.** Keep fail-closed. Add: a distinct metric and a
named health field (not just a `warn!`), and a **refusal at proposal-registration time** so a Join
whose key is uncommittable never reaches ratification — today `:18785-18792` only warns when
`learn_committee_member_hybrid_key` refuses a conflicting rebind, which is exactly the case that
later halts everyone.

---

### 3.7 The `.devnet` trigger

Delete `|| data_path.join(".devnet").exists()` from `node/src/lib.rs:2823`. Auto-approval stays
available behind the explicit flag. This is a custody/gate item, not a design fork — and §2.8 is the
argument for why it is not merely untidy.

### 3.8 Join-request freshness

Add the sponsor's current `config_seq` (or the id of a recent final anchor) to the
`JOIN_REQUEST_PQ_BINDING_V1` preimage and bump it to `_V2`, with a bounded acceptance window. This
closes §2.11 without needing Pastro's forward-secure key rotation. Say plainly what it does **not**
close: a member evicted at `c+1` can still deceive a peer still operating at `c`. The containment for
that is §3.1 — a lagging peer refuses a `config_seq` it cannot derive — and if that is ever judged
insufficient, Pastro §5's install-time key rotation is the known answer.

---

## 4. The ranking, on one page

Ordered by what would bite a running federation. **"τ shape"** means the property is assumed *by
construction* in the literature and merely *hoped for* here — the same defect class as the reproduced
ledger fork.

| # | Hazard | τ shape? | Live today? | Where | Fix |
|---|---|---|---|---|---|
| 1 | **`auto_evict` mutates the roster locally, off-chain, reverted by restart, invisible to peers** | ✅ | ✅ **wired** (`blocklace_sync.rs:5580`) | `constitution.rs:174-185` | §3.4 |
| 2 | **Votes tallied against live roster + live threshold; a 3-of-4 quorum evaporates at `T:3→4`** | ✅ | ✅ every join | `finalization_votes.rs:248,255,420-430,537` | §3.1 + §3.2 |
| 3 | **No `config_seq` on blocks or votes — no node can detect 1 or 2 happening** | ✅ | ✅ always | `finality.rs:293-338`, `finalization_votes.rs:52-55` | §3.1 |
| 4 | **Joiner counts before it is required to hold the state** | ✅ | ✅ every join | `FEDERATION-JOIN.md`; no learner phase in tree | §3.3 |
| 5 | No churn bound; `l ≥ 3` breaks cross-config intersection at our `T(n)` | — | latent | `ordering.rs:317` + absence | §3.3 |
| 6 | Leave has no drain rule | — | latent (`--remove` works) | `finality.rs:284` + absence | §3.5 |
| 7 | Duplicate sponsorship; `PendingJoinRequest.proposed` is dead code | — | ✅ with auto-approve | `blocklace_sync.rs:728,3060,3088` | §2.7 |
| 8 | `.devnet` file makes the roster reactive (LPR §8.3) | — | ✅ if the file exists | `lib.rs:2823` | §3.7 |
| 9 | Finality halt is global-per-poll, `warn!`-only, no escape | — | failure mode only | `blocklace_sync.rs:2179-2197` | §3.6 |
| 10 | Replay discards `ml_dsa_pubkey`; committed keys derived by a second rule | — | mitigated | `committee_replay.rs:91`, `blocklace_sync.rs:4389-4415` | §3.6 |
| 11 | Join request replayable indefinitely within a federation | — | ✅ | `blocklace_sync.rs:684-712` | §3.8 |
| 12 | Two threshold derivations (boot recomputes, live reads stored) | — | latent | `blocklace_sync.rs:4248` vs `:18936` | §2.12 |
| 13 | `EpochReconfig.lean`'s crown theorem cites `epoch.rs`, which the node never calls | — | ✅ (a citation, not a bug) | `finalization_votes.rs:418`; `federation/src/epoch.rs` uncalled | §3.2 obligation 3 |

**Read 1–4 together.** They are one defect wearing four hats: *the roster is a derived quantity read
from the live view rather than from a committed object.* Fixing 3 (`config_seq`) is what makes 1, 2
and 4 detectable; fixing 1 and 2 without it just moves the race.

---

## 5. What I did not check

- **I did not construct a witness for hazard 2.** The 3-of-4-becomes-3-of-5 argument is derived from
  reading `record`/`assembled_quorum`/`reconfigure`; a test that drives a block to exactly threshold,
  reconfigures, and asserts the verdict flips would settle it. **Build it before believing me** — and
  build it constructively, asserting the reconfigure happened before reading the verdict
  (`minted-a-falsifier-that-stopped-falsifying`).
- **I did not measure whether hazard 1 has fired in a live federation.** `auto_evict` requires an
  actual equivocation to trigger, so it may be cold. Cold is not closed.
- **I did not audit the round-advance rule**, which `CONSENSUS-FROM-SOURCE` §5.3 flagged as the next
  liveness thing to check. It is adjacent — CM's ES instance is a package — but out of scope here.
- **The two flagged reading-lane inferences** in the companion (Hammerhead's Alg. 2 off-by-one; DPRB's
  `Π_i` divergence) are not verified by me and nothing in §3 depends on either.
- **The `l ≤ 2` bound is my derivation from DZ's inequality**, not a quotation. The arithmetic is in
  the companion §1.5 and is checkable in a minute; the constant DZ itself states for multi-join
  renders ambiguously in the PDF text and I did not rely on it.
