# Accountability, forensics and machine-checked consensus — what we can prove and prosecute

**Date** 2026-08-08 · **Tree** `/Users/ember/dev/breadstuffs` at `1dd15dd09` (shared tree, live lanes —
line numbers verified at read time, drift is expected)
**Papers** all in `pdfs/`, cited by section. **Code** verified at source; every line number below was
opened, not inferred.

Companion documents, not repeated here: `docs/reference/CONSENSUS-FROM-SOURCE-2026-08-08.md` (the
CM-paper-to-our-code conformance map) and `docs/reference/FEDERATION-DESIGN-GAPS-2026-08-08.md` (the
reconfiguration hazards). This document is the *accountability* lens only: who can be proven guilty,
of what, on what evidence, and what our proofs about consensus actually cover.

---

## 0. The answer in one paragraph

We can prove exactly one accusation: **that a named key signed two conflicting blocks for one slot.**
That proof is unconditional, constant-size, self-contained and checkable by a third party who holds no
lace and trusts no quorum — which is *stronger* than anything the BFT forensics literature extracts
from PBFT or HotStuff. We can prove **nothing whatsoever** about the fork we actually had, and that is
not an implementation gap we can close by retaining more: a validator whose *executor* computes a
different state root, while its *consensus messages* are impeccable, is outside the fault class that
Polygraph, BFT forensics, and the blocklace `byz` predicate all address. Between those two facts sits
the real finding: **our fork was undetectable, not unattributable.** No component compared the two
roots. The papers are unanimous that attribution begins with a *detected* disagreement; we never had
one, because nothing in the system is positioned to notice that two honest nodes disagree.

---

## 1. What is the accountability standard?

### 1.1 Three definitions, in increasing usefulness to us

**Polygraph** (`polygraph-accountable-byzantine-agreement-disc2020.pdf`, Def. 1, p. 45:1) defines
*Accountable Byzantine Agreement*. Beyond the usual agreement/validity/termination:

> **Accountability**: There exists a verification algorithm V such that: if two honest processes
> decide distinct values, then eventually for every honest process p_j, for every state s_j reached
> by p_j from that point onwards, the verification V(s_j) outputs a set of size at least t0 + 1,
> **containing exclusively Byzantine processes**.

Two halves, and both matter. *Completeness* — a disagreement must yield at least ⌈n/3⌉ names.
*Soundness* — the set contains **exclusively** Byzantine processes. An accountable protocol may not
name an honest node, ever.

**BFT forensics** (`bft-protocol-forensics-2010.06785.pdf`, Def. 3.2, §3) parameterises the same idea
as a triple **(m, k, d)**: if `t < f ≤ m` and two honest replicas output conflicting values, then from
the transcripts of **k** honest replicas a client can produce an irrefutable proof against at least
**d** Byzantine replicas. Their Table 2 is the punchline of the paper: PBFT-PK, HotStuff-view and VABA
get `(2t, 1, t+1)`; **PBFT-MAC and Algorand get `d = 0` — no forensic support at all**, even given every
honest replica's transcript. The authors' headline finding is that this "depends heavily on **minor
implementation details that do not affect the protocol's security or complexity**" (Abstract). Two
protocols identical in safety, liveness and message complexity can differ between full attribution and
none.

Crucially, the proof's force is unconditional: "With the irrefutable proof, any party (not necessarily
in the BFT system) can be convinced of the culprits' identities **without any assumption on the number
of honest replicas**" (§3, p. 3).

**Accountability + reconfiguration** (`accountability-bft-2105.04909.pdf`, Freitas de Souza,
Kuznetsov, Rieutord, Tucci-Piergiovanni, §3) is the most directly useful, because it is the only one of
the three that treats *eviction* as part of the specification rather than an afterthought. Its RALA
abstraction demands six properties; five are a ready-made audit checklist for us:

| Property (§3) | Statement | Us |
|---|---|---|
| **Completeness** | A correct client that learns a value incomparable with another correct client's *eventually accuses* someone it had not accused before | ❌ **the fork accused nobody** |
| **Accuracy** | If a client accuses set A, it holds a valid proof against each member | ✅ for equivocation (`evidence.rs`) |
| **Authenticity** | It is computationally infeasible to accuse a benign process | ✅ today — but see §1.4 |
| **Accusation Stability** | Accusation sets **monotonically increase** — `A_i[t] ⊆ A_i[t']` for `t < t'` | ❌ **a restart shrinks ours** |
| **Agreement** | Correct clients eventually agree on whom they accuse | ❌ eviction is per-node and in-memory |

The paper names, as a specification property, exactly the defect we have: `auto_evict_equivocator`
(`blocklace/src/constitution.rs:174`) mutates `participants` in memory, the constitution has no durable
table (the `persist` crate has zero `constitution` hits), and so the accusation set is *not* monotone
across a restart. **Accusation Stability is not a nicety — it is one of six properties that make the
abstraction implementable.**

### 1.2 What is provable under CM / blocklace — and it is a lot

The blocklace gives a form of accountability that is *stronger* than anything in the forensics paper's
Table 2, over a *narrower* fault class. This is worth stating precisely because it is a genuine
strength and we should not undersell it.

`blocklace-byzantine-repelling-crdt-almeida-shapiro-2402.08068.pdf` §4.2, Def. 4.2:

> An equivocation by a node `p` in a blocklace `B` is a pair of different `p`-blocks `a, b ∈ B` that
> are incomparable under `≺` […] **The presence of a pair of incomparable p-blocks in a blocklace
> proves that p is an equivocator.**

Compare what PBFT-PK requires (`bft-protocol-forensics` §4.2): intersect a `commitQC` with a status
certificate, reason about quorum overlap, and conclude `t+1` culprits — valid **only** while `m ≤ 2t`.
The blocklace proof needs *no* quorum argument and *no* bound on `f`. Two signatures and a
non-observation relation. `d` is not "at least `t+1`" — it is "precisely the equivocators, however many
there are, under any adversary fraction."

Our implementation is faithful to this, and I want to record that it is genuinely good work:

- **`blocklace/src/finality.rs:1743` `detect_equivocation`** implements Def. 4.2 as written — same
  creator, and neither block in the other's causal past. Not the weaker `(creator, seq)` heuristic.
- **The pointer set is inside the signature.** `Block::signing_content_from_payload_hash`
  (`finality.rs:564-579`) covers `creator ‖ seq ‖ payload_hash ‖ predecessors`, and
  `Block::id() = blake3(signing_content ‖ signature)` (`:676`). The cordial property is cryptographic,
  not conventional — which is what makes the compact exhibit below sound.
- **Both blocks are retained.** `finality.rs:1541-1553` inserts the equivocating block *before*
  returning the error, commented `// Still insert the block (we keep evidence)`. This honours the
  blocklace paper's §5.1 Principle 2 — *"A q-block b by a node q is eventually accepted if b provides
  the first evidence of q being Byzantine"* — which is easy to get wrong and which a naive "reject the
  conflicting block" implementation would destroy.
- **`blocklace/src/evidence.rs::EvidenceOfEquivocation`** is Polygraph's `verify-proof` map
  (`accountability-bft` §3: "a Boolean map verify-proof … that can be used by any process or third
  party") realised as a wire value: `(creator, hybrid_id, header_a, header_b)`, each header carrying
  `(seq, payload_hash, predecessors, signature)`. `verify()` (`:217`) checks same slot, non-identical
  content, and both Ed25519 signatures. It is constant-size and needs no lace.
- The `verify_strict` choice at `evidence.rs:113` is load-bearing and correctly identified as such in
  its own docblock: `creator` is read *out of the attacker-supplied exhibit*, so under a cofactored
  verify a small-order `creator` with `(R = identity, s = 0)` verifies over every message and an
  attacker holding no secret mints a valid accusation. The test at `:366` pins it. **That is the
  Authenticity property of RALA §3 defended at exactly the right line** — and it is the single place in
  this whole area where a subtle break would have been an accusation-forgery oracle.
- **The consequence is durable where it counts.** `node/src/equivocation_court_service.rs` slashes a
  bond and burns the evidence digest into `NS_COURT_RESOLVED` (`:432`), restored at boot by
  `CourtLedger::load` (`:136`), so no-double-slash survives restart.

**Scope limit, stated honestly in our own source** (`evidence.rs:22-33`): incomparability is
lace-relative, so only the **same-slot** fork is certifiable from a constant-size exhibit.
`EvidenceOfEquivocation::from_proof` returns `PositionMismatch` for a different-`seq` incomparable
fork. Those stay on the membership/auto-evict path — the path with no durable record. So the fault
class that is *fully* prosecutable is narrower than the fault class we *detect*.

### 1.3 Is an honest-but-diverged node distinguishable from a Byzantine one?

**Yes — and that is the problem, not the reassurance.**

Every accountability result in this cluster attributes deviations from the **agreement protocol**: a
node that sent two conflicting *messages*. None of them attributes a deviation of the **state
machine**. The blocklace's culprit predicate is exactly (`blocklace-…-2402.08068` §4.3):

```
byz(B) = { p | p ∈ eqvc(B) ∨ ∃b ∈ B · node(b) = p ∧ (¬wf(b) ∨ ¬valid(b)) }
```

Three hooks: equivocation, malformedness, invalidity. Our fork engaged none of them. Four nodes each
produced one well-formed, correctly-signed, causally-closed block per slot and one signed vote apiece.
Three said root `R`, one said `R'`. Nobody equivocated; nobody sent a malformed block; and `valid(b)`
as our ingest computes it (`finality.rs:1506-1580`: hybrid signature against the enrolled PQ roster,
predecessor closure, consensus-time frontier) **does not recompute the state root**.

So the fourth node was, in the precise sense of every paper here, **not Byzantine**. It followed the
protocol. Its executor disagreed. Under `byz(B)` it is innocent, and correctly so.

This is the load-bearing conclusion of the whole review:

> **Consensus accountability attributes disagreement about *what was said*. Our fork was a
> disagreement about *what was computed*. No retention policy, no forensic protocol, and no amount of
> Byzantine-fault machinery attributes it, because under the model there is no culprit.**

The corollary is a design instruction, not a lament. The only way a divergent executor becomes
attributable is to move the state root *inside* `valid(b)` — i.e. make the block's claimed root
something every receiver recomputes and refuses on mismatch. That converts an unattributable
divergence into an invalid block, which `byz(B)`'s second disjunct already covers and which our
existing evidence machinery could then prosecute. Until then, "we detect and slash misbehaviour" is
true only of equivocation.

Note the asymmetry this produces with the forensics literature: their `f > t` premise means *someone*
broke the rules. Our fork had `f = 0`. We were outside the entire problem statement — which is exactly
why the silence was total.

### 1.4 Would forensics have wrongly accused someone?

**On our fork: no**, because no forensic protocol would have produced any output at all. There were no
conflicting signed statements to intersect.

**In general: yes, and the mechanism should frighten us.** The forensics paper's Appendix D.1, *"A
Forensic Attack on HotStuff-view"* (p. 1231-1240) is the most important two paragraphs in this cluster.
HotStuff's published voting rule checks `(LOCK.e < highQC.e) ∨ (LOCK.v = v)`. The paper's Algorithm 6
adds `LOCK.e = highQC.e`. The authors are explicit that the extra check "will not affect the safety and
liveness for HotStuff" — it is invisible to every conventional correctness criterion. But without it,
they exhibit a run in which an honest replica `R` follows the protocol exactly and:

> In this execution, replica R follows the protocol, however, **it will be mistakenly blamed** by
> Algorithm 2 […] it is possible that some honest replicas who have the same transcripts as R will be
> **improperly held culpable** in this case.

The lesson generalises: **soundness of accusation is not a property of using signatures. It is a
property of the protocol's rules being tight enough that the culpability predicate's premises are
unreachable by honest behaviour.** A protocol can be safe, live, and yet frame its own honest
participants.

**Our live instance of this shape.** The obvious fix for the accountability hole in §2 is "retain the
conflicting vote as evidence." Do not implement it at the obvious place. `VoteCollector::record`
(`node/src/finalization_votes.rs:537`) short-circuits at `:581-590`:

```rust
if let Some(signers) = self.votes.get(&vote.block_id)
    && signers.contains_key(&vote.voter)
{
    let distinct_votes = signers.len();
    return if self.attested.contains(&vote.block_id) { ... AlreadyQuorum ... } else { ... Counted ... };
}
```

The guard is `contains_key(&vote.voter)` alone — and it returns **before `verify_hybrid` at `:592`**.
A second vote bearing a member's `voter` field is therefore never signature-checked. Today this is
harmless, because nothing is stored on that path. **Retain at that line and it becomes an
accusation-forgery oracle**: any on-path adversary could mint "member X's conflicting second vote" from
attacker-chosen bytes under X's name. That is the PBFT-MAC failure exactly — the forensics paper gives
PBFT-MAC `d = 0` because "Byzantine parties are able to construct arbitrary transcripts due to the
absence of signatures. Hence, **message transcripts cannot be used as evidence**" (§8). Evidence is
only evidence after verification. Verify first, then retain.

---

## 2. What evidence must be retained — and what we retain

### 2.1 What the papers require

| Source | Requirement |
|---|---|
| **Forensics** §4.2, Alg. 1 | "Each replica keeps **all received messages** as transcripts" and a set `Q` of all NewView messages |
| **Forensics** §7 (Diem) | A **`Forensic Storage`** component: "maintains a map from the **view number to quorum certificates** and its **persistent storage**" — a real durable table, queryable by third parties over JSON-RPC |
| **Forensics** §5.2, Table 4 | When a vote carries a **hash** rather than the value, the **preimage must be retained separately** — this is precisely why HotStuff-hash degrades from `k = 1` to `k = t+1` |
| **Polygraph** (p. 45:2-3) | Two artefact kinds: a **ledger** (justifies adopting a value) and a **certificate** (justifies a decision), each `n − t0` signed ECHOes; and the impossibility result: accountability is impossible "**without extra logs of at least Ω(n) rounds**" |
| **Blocklace** §4.3, §5.1 | "the blocklace stores not only valid blocks but **also blocks that constitute a proof that their creator is Byzantine**"; Principle 2 requires *accepting* the block that first evidences Byzantine behaviour |
| **RALA** §3 | The accusation set `(A, P)` itself, monotone and eventually agreed |
| **PeerReview** (via `accountability-bft` §5) | Tamper-evident logs + challenge-response — and its named weakness: an unresponsive process "cannot [be] determine[d] whether faulty or not", so some Byzantine processes "might be suspected forever and never proven guilty" |

The **Ω(n)-rounds** result deserves emphasis: Polygraph states that detecting equivocation alone is
*insufficient*, and that accountability provably requires retaining logs spanning a linear number of
rounds. Retention depth is not an engineering preference; it is a lower bound.

### 2.2 What we actually retain

| Artefact | Where | Survives restart |
|---|---|---|
| Every block (postcard, keyed by `BlockId`) | `persist/src/blocklace_store.rs:51,85` | ✅ |
| `BlocklaceMeta { tips, equivocators, ordered_block_ids, attested_block_ids }` | `blocklace_store.rs:28-38` | ✅ |
| `StoredAttestedRoot.finalization_quorum: Vec<QuorumSignature>` | `persist/src/federation.rs:98-172` | ✅ and **re-verifiable** (`:304-359`) |
| Court resolved-evidence **digests** | `persist/src/forever_digests.rs`, `NS_COURT_RESOLVED` | ✅ |
| **The `VoteCollector` tally — every sub-quorum vote** | in-memory only; `persist/src/tables.rs` has **no vote table** | ❌ |
| **`my_pending_votes`** | `blocklace_sync.rs:875`, in-memory | ❌ |
| **Constitution participants / threshold** | in-memory; zero `constitution` hits in `persist/` | ❌ |
| **`EquivocationProof` structs** | not held by the lace the node runs (`finality::Blocklace` has `equivocators: HashSet` and no proofs vector) | ❌ |
| **`EvidenceOfEquivocation` exhibits** | only the *digest* is stored, only *after* a slash, only if the accused was bonded on that node | ❌ |
| **Peer scoreboard / graylist** | `net/src/peer_score.rs`, in-memory | ❌ |
| Court registry, bonds, bond-cell bindings | in-memory (`equivocation_court_service.rs:53-54`) | ❌ (fails closed: `NothingAtStake`) |

**The one genuinely strong property**: the ed25519 *and* ML-DSA signatures on counted votes are
retained (`finalization_votes.rs:601-605`) and surface through `assembled_quorum` (`:491-520`) into
`StoredAttestedRoot`, where `verify_finalization_quorum` re-derives the exact preimage and re-checks
every signature against the *enrolled* roster, refusing wholesale on a misaligned PQ roster rather than
downgrading to ed25519-only. A third party can re-verify a finalized quorum from disk. That is the
Diem `Forensic Storage` shape, and we have it — **for the winning side only.**

### 2.3 Named, concrete: what a node must keep and does not

1. **Both signed halves of any vote disagreement, after signature verification.** Today the second is
   discarded unread at `finalization_votes.rs:596-605` (`or_insert`, first-write-wins). First-write-wins
   is *safety*-correct — an equivocator cannot double-count — and *accountability*-void. The file's own
   differential test names a case `"equivocating signer counts once, first-write-wins (quorum forms)"`:
   equivocation is treated as a counting nuisance rather than an offence.
2. **The losing side of any root split.** A 2/2 disagreement is dropped entirely on restart. There is
   no artefact from which the divergence could be reconstructed the next morning.
3. **The `EvidenceOfEquivocation` exhibit itself**, not merely its digest. We persist the fact that we
   punished someone and discard the proof that they deserved it. A third party auditing us later can see
   a burn record and must take our word for what it burned.
4. **The eviction as a lace event.** `auto_evict_equivocator` does `participants.retain(...)` and
   nothing else — no `MembershipProposal`, no block, no durable roster. `LeaveReason::Evicted {
   block_a_bytes, block_b_bytes }` exists in `constitution.rs` and **is never constructed by the
   evicting path**. The carrier for a durable, evidenced eviction is already defined and unused.
5. **A vote's epoch / committee version.** The signing preimage (`types/src/lib.rs:547-565`) is
   `FINALIZATION_VOTE_DOMAIN_V4 ‖ block_id ‖ merkle_root ‖ framed(receipt_stream_root)`. It binds no
   epoch, no committee version, no federation id, and not the voter. Combined with sticky `attested`
   across `VoteCollector::reconfigure` (`:420`, `:613`), a vote is not a statement about *when* it was
   cast — so no future forensic predicate can be written over "what X said in epoch N".

Against Polygraph's Ω(n)-round lower bound, our effective retention for non-finalized consensus
messages is **zero rounds**.

---

## 3. Machine-checked consensus in practice — what Moonshot had to model, and what it left out

`formally-verifying-pipelined-moonshot-2403.16637.pdf` (Praveen, Ramesh, Doidge) verifies the safety of
a real, deployed-intent BFT protocol in IVy. It is a good paper and an honest one, and its *scope
statements* are more useful to us than its result.

### 3.1 What they modelled away

All from §4.1-§4.2, quoted:

1. **"Only a high level abstract specification of the protocol is modeled and verified."**
2. **Timers → booleans.** "timers used in the protocol are replaced by Boolean propositions […] can
   switch value anytime non-deterministically". Sound for safety; it means nothing about a real timeout.
3. **Quorums → an axiom.** "Verifying this detail would require having arithmetic […] Instead, what is
   modeled is the quorum intersection property […] **modeled in IVy as an axiom, avoiding the usage of
   arithmetic**." The `2f+1` count is never checked. Every off-by-one in a real threshold computation is
   invisible to this proof.
4. **Signatures → not modelled at all.** "Checking digital signatures is not modeled in IVy — the model
   **assumes messages sent by honest validators are authentic**."
5. **Certificate integrity → a global oracle.** This is the sharpest one. Quorum-certificate validity is
   discharged by monitors that record every message every validator sent:

   > "This can be thought of as some kind of **a central authority with a global view of all
   > validators**, who records all messages sent by the validators. **Of course there is no such central
   > authority in real implementation; it is only modeled here for the sake of proving safety.**"

6. **Liveness → not proven.** "Proving liveness is future work" (§7).

The conclusion is scoped exactly to match: *"This conclusively proves the absence of **design or logic
errors** with respect to the protocol safety."* Design errors. Not implementation errors, not
cryptographic ones, not liveness. The paper never claims the running node is safe, and we should quote
its discipline rather than its result.

### 3.2 What our Lean consensus proofs cover — verified at source, and better than I expected

**First, a correction to the brief that sent me here, and to a sibling reference doc.** The claim "our
Lean consensus theorems are about a model beside the node" is **partly false, in our favour**.
`tauOrder` *is* the node's authoritative finalization rule: `@[export] dregg_tau_order`
(`metatheory/Dregg2/Distributed/FinalityGate.lean:292`) → `dregg-lean-ffi` →
`node/src/finality_gate.rs:195` → the `blocklace_sync.rs` poll path (`:2204`), where since 2026-08 the
comment states *"the AUTHORITATIVE order is `BlocklaceFinality.tauOrder` itself"* and the Rust
`ordering::tau` is demoted to a differential sibling. `tau_order_export_eq`
(`FinalityGate.lean:311`) ties the exported symbol to the proved `tauOrder`. So
`finalLeaderAt_unique`, `finalLeaderAt_needs_unique_candidate`, `tauOrder_only_enrolled` and
`tauOrder_enrolled_eq_unfiltered` are facts about **code that runs**. That is the `Lean must be the
implementation` law honoured, and it is real.

Also: **no `sorry`, no `axiom`, no `native_decide`** in `TauPrefixMonotone.lean`,
`BlocklaceFinality.lean` or `EpochReconfig.lean`, with 55 `#assert_axioms` across the three, and
`Dregg2/Tactics.lean:39-52` really does `throwError` outside `{propext, Classical.choice, Quot.sound}`,
transitively.

Now the four things those proofs do **not** cover, each verified:

**(a) The kernel does not check the code that executes.**
`BlocklaceFinality.lean:1116` carries `attribute [implemented_by tauOrderFastImpl] tauOrderFast`. The
file states the hazard itself at `:927`: *"`@[implemented_by]` is TRUSTED — the kernel does NOT check
the twin equals the pure def; a wrong twin silently corrupts finality with no theorem catching it."*
`#assert_axioms` cannot see it — `collectAxioms` does not traverse compiler attributes. And the
substitute for a proof is `#guard` differentials on **three concrete laces**. So the single most
load-bearing equality in our consensus stack — "the fast implementation the node runs equals the
function we proved about" — is defended by three unit tests wearing Lean clothes. This is precisely
the `GUARD-DISCIPLINE` sin the repo already legislates against, sitting under the marquee theorem.

**(b) The guarantee is conditional on a wall-clock budget, and fails open.**
`blocklace_sync.rs:2219-2237` says it outright: *"'The order the node finalizes over IS the verified
rule's' holds only on a poll whose verified FFI completes within `verified_order_ffi_timeout()`
(default 2500 ms)"* — with over-budget warnings **already observed on an idle 4-node committee at
`lace_size` 773–981**. `DREGG_ALLOW_UNVERIFIED_CONSENSUS=1` swaps in the unverified Rust twin, and the
gate is env-disableable at `finality_gate.rs:87-92`. A verified consensus rule that yields to an
unverified twin under load is verified in the regime where it is least needed.

**(c) A hypothesis the node evaluates nowhere — still true, but not the one we have been citing.**
`FinalizedRegionStable` and its executable mirror `stableCheck` have been **deleted**
(`TauPrefixMonotone.lean:50`: *"the old `stableCheck`, which nothing ever called, is deleted"*). The
current unmanned hypothesis is `ChainExtends.head_chain` (`TauPrefixMonotone.lean:621-625`), which
carries CM Prop. 3 as an unproved import; grep for `ChainExtends`/`head_chain` over all `.rs` returns
zero. The file's own header names two gaps, including *"our `finalLeaderAt` is not monotone, and CM's
`final_leader` is"* — so a late equivocating leader block can still shorten τ, and `ChainExtends`
silently absorbs head-monotonicity. Meanwhile **`FinalizedRegionStable` is still cited by production
Rust doc comments** at `node/src/execution_cursor.rs:22,35,198,432,435,521` and by five other files
including `docs/reference/DECISION-BRIEF-2026-08-08.md` — all dangling. `ExecutionCursor` still
performs the prefix caching CM §5 authorises **only because of Prop. 9**, now citing a deleted premise.
Substance unchanged; the name we have all been repeating is stale. (I nearly shipped the stale name
myself — the sibling doc's line was written before the refactor.)

**(d) Some theorems prove less than their names say.** `tau_execution_agreement`
(`BlocklaceFinality.lean:1544`) is `h₁ : f x = r₁, h₂ : f x = r₂ ⊢ r₁ = r₂`, proved
`by rw [← h₁, ← h₂]`. That is determinism of a Lean function, not agreement between replicas — and it
holds for *any* `Decoder`, including a constant one. `tauOrder_deterministic` and
`finalLeaders_one_per_wave` share the shape; the file admits it at `:1166` (*"Trivial as Lean"*). A
reader who sees `tau_execution_agreement` in an `#assert_axioms`-clean list will read "replicas agree."
They do not. Separately, `EnrolledLace` — the hypothesis of `tauOrder_enrolled_eq_unfiltered` — is
documented at `:1208-1214` as a precondition **the live path cannot enforce** (the PQ roster is
insert-only while the constitution's participant set shrinks, and `from_checkpoint_trusted` re-admits
every persisted block with no check).

**(e) A theorem about code with no callers.** `EpochReconfig.lean::epoch_handoff_no_gap` (`:372-388`)
models `federation/src/epoch.rs`. Per-function caller audit: `propose_epoch_transition`,
`apply_epoch_transition` and `verify_epoch_transition` have **zero production callers**;
`genesis_default` and `member_public_keys` have zero callers of any kind; the rest are test-only or
intra-module. The live path is `api.rs:10061` → `blocklace.propose_membership` →
`ConstitutionManager` → `apply_committee_change` → `VoteCollector::reconfigure`, which touches none of
it. `epoch.rs:19-32` says so itself. Its hypothesis `verifyTransition` is a `Prop`, not a `Bool` —
deliberately, per `EpochReconfig.lean:257` — so nothing *can* evaluate it at runtime.

**New finding, recorded nowhere else.** The Lean `verifyTransition` requires
`(t.validVoters SigValid).Nodup` (`EpochReconfig.lean:265`). The Rust `verify_epoch_transition`
(`federation/src/epoch.rs:340-404`) **does not dedup voters**: it checks `votes.len() < threshold` and
then loops without any distinctness test (`grep dedup|distinct|HashSet` finds only the unrelated
leaving-set index). One member's valid signature repeated `threshold` times passes the Rust gate and
violates the Lean hypothesis. Latent today only because nothing calls the Rust function — which is
exactly how a dead module becomes a live wound the day someone wires it up.

**One false citation to fix.** `TauPrefixMonotone.lean:56` and `:614` cite
`Distributed.BlocklaceFinality.isCordialBlock` as *"now defines and exports"* the receive-path
cordiality check. **`isCordialBlock` does not exist anywhere in `metatheory/`** — the only two hits
repo-wide are those two self-references. Cordiality is still unenforced at admission (`rg -i cordial`
over `blocklace/src/` returns nothing), which matters because CM's Prop. 9 — the thing `ChainExtends`
assumes — is proved *from* cordiality.

### 3.3 The honest formulation

A Lean consensus theorem here establishes a property of a Lean-defined transition system. It becomes a
property of the node exactly to the extent that (i) the node invokes the Lean artefact rather than a
Rust re-implementation — **we pass this for `tauOrder`, and it is the strongest thing in this
document**; (ii) the compiled artefact is proved equal to the one reasoned about — **we fail this, at
`@[implemented_by]`**; (iii) every hypothesis is discharged by construction or evaluated with a refusal
— **`ChainExtends` and `EnrolledLace` fail this**; (iv) the guarantee is unconditional rather than
budgeted — **we fail this at 2500 ms**; and (v) the theorem's statement means what its name suggests —
**`tau_execution_agreement` fails this**.

Moonshot's authors held themselves to exactly this discipline, in a paper whose entire point was the
proof, and still concluded only *"the absence of design or logic errors."* Note the ordering: the model
they verified is *weaker* than ours in every dimension listed above except (ii) and (iv), where they
had no compiled artefact at all and we do. We should be able to say more than they did. We currently
say it less carefully.

---

## 4. Reliable broadcast: what forgoing it costs in accountability terms

**It costs less than one would expect, and the surprise runs in our favour — but only if we retain.**

Cordial Miners (`cordial-miners-shapiro-2205.09174.pdf` §1) is explicit about the trade:

> "Both protocols use Reliable Broadcast (RB) as a building block […] **RB ensures that Byzantine
> miners cannot equivocate** […] instead of using RB to eliminate equivocation (and absorbing its
> rather high latency), miners cooperatively create a data structure that **accommodates**
> equivocations, termed blocklace."

BRB's defining property is *Consistency* — "no two correct processes deliver different messages"
(`zot-dynamic-probabilistic-reliable-broadcast.pdf` §2, alongside Validity, Totality, Integrity). Note
what Consistency does: it **suppresses** the equivocation. The second conflicting message never
becomes a delivered event. A protocol built on RBC therefore tends to have *no artefact naming the
equivocator* — prevention consumes the evidence.

The blocklace inverts this. Equivocation is permitted to happen, is materialised as two signed blocks,
and is excluded at *ordering* by τ rather than at *delivery*. So:

- **Attribution gets stronger, not weaker.** RBC's Consistency holds only while `f < n/3`; above the
  threshold RBC gives you neither safety *nor* evidence. The blocklace's proof — two incomparable
  same-creator signed blocks — is threshold-free (§1.2). In the regime the forensics literature
  actually cares about (`f > t`), forgoing RBC is an accountability *gain*.
- **The evidence disseminates by CRDT convergence** rather than by RBC's Totality, which is adequate
  under the Node Liveness Axiom (`blocklace-…-2402.08068` Def. 5.1) since correct nodes forward
  everything.
- **What you give up is the *window*.** RBC excludes before delivery; the blocklace excludes at
  ordering. Between those two points, nodes hold divergent views and act on them. CM's entire argument
  that this is safe rests on **τ's exclusion being the complete one**.

**And that is where we have a real defect.** We have *two* non-equivalent equivocation predicates:

- `finality.rs:1743 detect_equivocation` — CM Def. 4.2, round-independent incomparability. Drives
  *membership* (auto-evict).
- `ordering.rs:223-258 EquivocationIndex` — groups by `(creator, round)` and flags `len > 1`. Drives
  *ordering* exclusion, i.e. τ.

The second is strictly coarser and **will miss a cross-round incomparable fork that the first catches**
(`CONSENSUS-FROM-SOURCE-2026-08-08.md` records the same mismatch and marks it "sound, **incomplete**").
So the predicate that actually decides the total order is the weaker of the two. Since forgoing RBC is
justified *precisely by* τ's exclusion being complete, this is not a cosmetic inconsistency: it is a
gap in the argument that licenses our headline latency win. Answering Q4 directly — **the equivocation
evidence is not weaker without RBC; the exclusion is.**

One further note from the RBC cluster worth carrying: probabilistic RBC variants
(`zot-dynamic-probabilistic-reliable-broadcast.pdf` §2) fail with per-instance probability, and "if one
uses instances of probabilistic reliable broadcast for building a long-lived abstraction, **the
probability of failure converges to 1 in an infinite run**." Any future "cheap RBC" proposal here must
be priced as a long-lived abstraction, not per-instance.

---

## 5. NIST IR 8460 — what we should be able to state and cannot

`nist-smr-consensus-byzantine-8460.pdf` is a survey, not a standard, but its framing sections are a
checklist of declarations a system owes its users.

**§7.2, Accountability Against Malicious Replicas** — the bar:

> "In an accountable BA protocol, honest nodes that are not in agreement can exchange sufficient
> information to **provably identify at least n/3 malicious nodes if f ≥ n/3**. This property relies on
> the idea that malicious equivocation can be detected due to the existence of **two signatures from
> the same key on conflicting messages**."

We can state this **for block equivocation** and not for anything else. We cannot state it for the
finalization-vote channel — which, per `CONSENSUS-FROM-SOURCE-2026-08-08.md`, is an **invented surface
with no CM counterpart**, and which has no equivocation detection at all.

**§1.3, the ledger properties.** NIST asks every DLT to state *Persistence* ("once a transaction is at
least `k` blocks deep […] it will be included in the same permanent position in the ledger of every
honest node with overwhelming probability") and *Liveness*, ideally via common prefix / chain quality /
chain growth. **We cannot currently state Persistence with a `k`**, because prefix-monotonicity — the
property that would ground it — rests on the assumed-and-unevaluated `ChainExtends` (§3.2c), whose own
premise (cordiality, CM Prop. 3) is unenforced at admission.

**§1.4, The Adversary.** Static or adaptive? Coordinated? NIST's default is a single adversary
controlling all `f`. Our reconfiguration surface (`FEDERATION-DESIGN-GAPS`) makes the adaptive case the
interesting one, and I could not find a document stating which we claim.

**§1.5, Timing Assumptions.** Synchronous / asynchronous / partially synchronous, and the `∆`. We
inherit CM's model (`f < n/3`, per `CONSENSUS-FROM-SOURCE` §"model assumption"), but a consensus-time
frontier check is live in `insert_checked` — a *synchrony-flavoured* gate. Which model the deployed
node claims, and what `∆` the frontier check assumes, should be one stated sentence and is not.

**§12/§13, slashing.** NIST notes slashing's advantage is that "the protocol can specifically target
the adversary's stake". We have that mechanism. But bonds are not restored at boot
(`equivocation_court_service.rs:136`, deliberately fail-closed to `NothingAtStake`), so *"we slash
equivocators"* holds within a process lifetime and degrades silently to "we record that we would have"
across a restart.

**The summary statement we owe and cannot yet write:**

> Under `f < n/3` in [stated timing model], this system detects any block equivocation, produces a
> constant-size third-party-verifiable proof naming the offender's key, durably evicts them, and
> slashes their bond; a transaction `k` blocks deep is permanent; and any disagreement between two
> honest nodes produces, within `T`, an artefact naming a cause.

Every clause after the semicolons is currently false or unstated.

---

## 6. Claims we currently make that exceed what we can support

1. **"repel/excommunicate the equivocator … ✅ *exceeds* the paper"**
   (`CONSENSUS-FROM-SOURCE-2026-08-08.md:485`, and again at `:718` "evict **and slash** … ✅ mostly, and
   exceeds on slashing"). It does not exceed. CM Def. 29's repelling is a property of the *blocklace*,
   which is durable and shared. Our eviction is an in-memory mutation of one node's participant list,
   reverted by restart, invisible to peers, and unratified — violating RALA's **Accusation Stability**
   and **Agreement** (§1.1). Our own `FEDERATION-DESIGN-GAPS-2026-08-08.md` §2.1 says exactly this and
   ranks it hazard 1. **Two reference documents in `docs/reference/` currently contradict each other on
   this row**; the pessimistic one is right.

2. **"Equivocation evidence is retained / propagated."** Both blocks are retained in the lace (true and
   good). But the `EquivocationProof` struct is not held by the lace the node runs, the
   `EvidenceOfEquivocation` exhibit is never stored, and **evidence is never gossiped**: the
   `BlocklaceGossipMessage` enum (`blocklace_sync.rs:294-362`) has no evidence variant. Propagation is
   incidental — both blocks travel as ordinary `Push` blocks and each peer independently re-detects. A
   node that never receives both halves never learns, and there is no push channel to tell it except a
   bearer-token-gated HTTP route.

3. **"We detect equivocation" (unqualified).** True at the block layer. False at the finalization-vote
   layer, where `record` returns before the signature check and discards the conflicting exhibit
   (§1.4). Two nodes double-signing conflicting roots is exactly NIST §7.2's canonical detectable
   offence and we are blind to it.

4. **Any statement that our consensus is "verified" or "machine-checked" without scope.** Per §3, the
   qualifier is five-part and we fail four of it: the executed `tauOrderFastImpl` is `@[implemented_by]`-
   trusted rather than proved equal (§3.2a); the guarantee lapses past a 2500 ms FFI budget already
   observed to blow on an *idle* 4-node committee, falling back to the unverified Rust twin (§3.2b);
   `ChainExtends` and `EnrolledLace` are hypotheses nothing evaluates (§3.2c/d); and
   `epoch_handoff_no_gap` describes functions with no production callers (§3.2e). Moonshot's conclusion
   claims only "the absence of **design or logic errors**" for a model that axiomatised quorum
   arithmetic and omitted signatures entirely. Our claims should be *scoped as carefully* as that one.

5. **`tau_execution_agreement` as evidence of replica agreement.** It is `f x = r₁, f x = r₂ ⊢ r₁ = r₂`
   (`BlocklaceFinality.lean:1544`), proved by rewriting, valid for any `Decoder` including a constant
   one. Same for `tauOrder_deterministic` and `finalLeaders_one_per_wave`. These are true, cheap, and
   named as though they discharge the property our fork violated. **They do not touch it.** If anything
   in this repo is ever cited as "we proved the replicas agree", it must not be one of these.

6. **`TauPrefixMonotone.lean:56` / `:614` cite `BlocklaceFinality.isCordialBlock` as existing.** It does
   not exist anywhere in `metatheory/`. A false citation inside a header a reader uses to decide whether
   cordiality is enforced — and it is not. Its sibling stale name, `FinalizedRegionStable`, is still
   cited by six files including production Rust doc comments at `node/src/execution_cursor.rs:22,35,198,
   432,435,521`, all dangling since the definition was deleted.

7. **Implicit: "a restart is state-preserving for consensus."** The constitution roster, the threshold,
   every sub-quorum vote, the peer scoreboard and the court's bonds are all in-memory. After a restart
   the lace still excludes a known equivocator from τ (durable `equivocators` in `BlocklaceMeta`) while
   the constitution has **re-admitted them to `participants` and re-raised the threshold** — the two
   live in different key spaces (hybrid `H(ed25519‖ml_dsa)` vs. the ed25519 strand key). That is a
   divergence *created by* restarting.

8. **"The fork was a failure of accountability."** It was not — and this correction matters for what we
   build next. It was a failure of **detection**, upstream of accountability, in a fault class no
   accountability protocol covers (§1.3). Building more forensics would not have caught it. Comparing
   two roots would have.

---

## 7. What follows

Ordered by what the reading says is load-bearing, not by cost.

1. **Compare the roots and refuse.** Move the state root inside `valid(b)` so a divergent executor
   produces an *invalid block* — the one move that brings our actual failure inside `byz(B)`. Until
   this exists, no accountability work touches the fork we had.
2. **Make disagreement observable at all.** `RecordOutcome` has four variants and none of them means
   "I hold ≥ threshold votes that disagree" — that state is byte-identical to "still waiting"
   (`Counted{}` + a `debug!` in the caller). A fifth variant and a metric is the smallest change that
   would have made the fork visible in 27 hours instead of never.
3. **Verify, then retain, both halves of a vote conflict** — in that order, for the reason in §1.4.
4. **Make the accusation set durable and monotone** (RALA Accusation Stability): persist the
   constitution, and construct the already-defined `LeaveReason::Evicted { block_a_bytes, block_b_bytes }`
   so an eviction is a lace event carrying its own proof rather than a local forget.
5. **Store the exhibit, not just the burn digest**, and give `BlocklaceGossipMessage` an evidence
   variant so attribution does not depend on every peer independently receiving both halves.
6. **Reconcile the two equivocation predicates** (§4) — τ's exclusion is the one CM's whole
   forgo-RBC argument rests on, and it is the weaker one.
7. **Close the `@[implemented_by]` seam** (§3.2a): prove `tauOrderFastImpl = tauOrderFast`, or state
   plainly, everywhere the verified order is claimed, that the executed twin is trusted and defended by
   three `#guard`s. This is the largest single gap between our proof and our binary.
8. **Decide what the FFI budget means** (§3.2b). A verified rule that yields to an unverified twin at
   2500 ms is not a verified rule under load; either the fallback refuses, or the claim is scoped to
   "verified when the gate completes" and says so.
9. **Repair the dangling citations**: `FinalizedRegionStable` (six files, incl. production doc comments)
   and `isCordialBlock` (does not exist). A reader auditing us will follow these and conclude we check
   things we do not.
10. **Write the §5 summary statement** once the clauses are true, and until then state the model,
    the timing assumption and the `∆` explicitly somewhere a reader can find.

---

### Sources

- `pdfs/bft-protocol-forensics-2010.06785.pdf` — Sheng, Wang, Nayak, Kannan, Viswanath, CCS '21. §3
  (Def. 3.2), §4.2, §5.2/Table 4, §7 (Diem `Forensic Storage`), §8, **App. B** (impossibility at
  `n = 2t+1`), **App. D.1** (the honest-replica misblame).
- `pdfs/polygraph-accountable-byzantine-agreement-disc2020.pdf` — Civit, Gilbert, Gramoli, DISC 2020.
  Def. 1; "Ledgers and certificates"; "Proving culpability"; the Ω(n)-round log bound.
- `pdfs/accountability-bft-2105.04909.pdf` — Freitas de Souza, Kuznetsov, Rieutord, Tucci-Piergiovanni.
  §3 (RALA: Completeness / Accuracy / Authenticity / Accusation Stability / Agreement / Liveness), §5
  (PeerReview's challenge-response limitation).
- `pdfs/formally-verifying-pipelined-moonshot-2403.16637.pdf` — Praveen, Ramesh, Doidge. §4.1-§4.2
  (the five abstractions), §5 (challenges), §7 (conclusion's scope).
- `pdfs/nist-smr-consensus-byzantine-8460.pdf` — Davidson, NIST IR 8460 ipd, April 2023. §1.3, §1.4,
  §1.5, §7.2, §12-13.
- `pdfs/cordial-miners-shapiro-2205.09174.pdf` — Keidar, Naor, Poupko, Shapiro. §1, §3-§5.
- `pdfs/blocklace-byzantine-repelling-crdt-almeida-shapiro-2402.08068.pdf` — §4.1-§4.3 (`wf`, `valid`,
  Def. 4.2, `byz(B)`), §5.1 (Principles 1-3), Def. 5.1-5.3.
- `pdfs/zot-dynamic-probabilistic-reliable-broadcast.pdf` — §2 (BRB properties; long-lived failure
  convergence). Companions: `zot-minicast-*`, `zot-near-optimal-communication-*`,
  `zot-byzantine-reliable-broadcast-with-low-communication-*`.
