# The interchain-live campaign — from fixtures to mainnet, trustlessly

*Design note — 2026-07-16. Companion to `docs/deos/INTERCHAIN-MODEL.md` (the
canonical model + per-chain maturity table), which this note does not restate but
sharpens for one axis: **the Solana consensus path is cryptographically real but
fixture-fed.** Everything here is present-tense about what the code does at HEAD,
imperative about the plan, and honest about which legs are `RUNS` / `BUILT` /
`NAMED` / `VISION`. It is thought, not code.*

## 1. The through-line

The Solana consensus verifier is not a stub and never trusts a caller-supplied
stake table: it derives the stake distribution and authorized voters from Solana's
own bank state back to a governance-pinned weak-subjectivity anchor, counts a real
Ed25519 stake-weighted ≥ 2/3 supermajority, binds the accounts hash into the voted
bank hash, and — on the value-release path — additionally demands the lock slot be
*rooted (finalized)*, not merely optimistically confirmed. What is missing is not
soundness but **ingestion**: every consensus-verified holding and lock in the tree
today is assembled by an in-test fixture constructor, and the one live source that
exists (`LocalValidatorFeed`) can only speak to a `solana-test-validator` it holds
the voter key for. This campaign closes the ingestion gap in four staged rungs —
retire the last demoted ballot shim, add a rooted-vote harvester so value release
stops failing closed, build the mainnet snapshot source that reconstructs the two
commitment legs RPC structurally hides, and relocate the whole off-circuit check
into a succinct wrapper so an on-chain verifier checks a dregg *proof* instead of
re-executing consensus — turning "trustless modulo the anchor, over a fixture" into
"trustless modulo the anchor, over mainnet."

## 2. Current resolution (what is real at HEAD, with citations)

**The verifier surface is `RUNS` and sound over its inputs.**

- Holdings (inbound, read-only governance weight): `prove_holding_consensus_anchored`
  (`bridge/src/solana_holdings.rs:465`) derives the table from bank state and tallies
  the exact-slot authorized-voter supermajority via `tally_authorized`
  (`bridge/src/solana_holdings.rs:519`). It does **not** demand the rooted leg — correct,
  because granting governance weight moves no value (optimistic-confirmation grade is
  acceptable for a read-only weight; the snapshot pin is the anti-double-count guard).
- Locks (the value-import path): `verify_lock_proof_consensus_anchored`
  (`bridge/src/solana_trustless.rs:636`) calls the inner verifier with
  `require_rooted = true` (`bridge/src/solana_trustless.rs:653`). The rooted leg is
  `VerifiedStakeTable::tally_authorized_rooted` (`bridge/src/solana_provenance.rs:724`),
  which counts only later votes carrying a tower `root ≥ slot`, each signed by the proven
  on-chain authorized voter; below 2/3 it returns `Err`, surfaced as
  `LockProofError::SlotNotRooted` (`bridge/src/solana_trustless.rs:315`). The
  explicitly-named optimistic entry (`verify_lock_proof_consensus_anchored_optimistic`,
  `:664`) skips that leg and is documented as non-value-only.

**The feed seam is `BUILT`; two of its three sources are `RUNS`, the third is `NAMED`.**

- `HoldingFeedSource` (`bridge/src/solana_feed.rs:245`) is the one-method seam every
  evidence source implements; `prove_feed_holding` (`:257`) routes any feed through the
  production verifier with the trust roots taken from the **caller**, never the feed —
  the falsifier `feed_cannot_self_authorize_against_a_different_pin`
  (`bridge/src/solana_feed.rs:817`) proves a compromised feed cannot pin its own
  fabricated distribution.
- `FixtureFeedSource` (`:735`) and `LocalValidatorFeed` (`:570`) are `RUNS`.
  `LocalValidatorFeed` harvests real bank-state bytes over finalized JSON-RPC (token
  account, vote/stake accounts, StakeHistory sysvar) and signs a genuine TowerSync vote
  with the ledger's authorized-voter key. Its honest accounting (`:42`–`:57`) names the
  two **reconstructed** legs: the 16-ary accounts-hash Merkle tree
  (`single_chunk_proofs`, `:449`) and the bank-hash components — which is exactly why it
  is dev-cluster-only and its endpoint gate refuses non-loopback plaintext (`:418`).
- The mainnet `SnapshotFeed` is `NAMED` — a complete design in the module doc
  (`bridge/src/solana_feed.rs:70`–`:120`) with no implementation.

**The outbound value paths are `BUILT` but test-gated, and their live feed is absent.**

- `MirrorState::mint_against_lock_proof_anchored` (`bridge/src/solana_trustless.rs:1058`)
  is `#[cfg(any(test, feature = "test-utils"))]`. The full lock proof that drives it is
  produced only by the fixture builder `anchored_lock_with_cluster`
  (`bridge/src/solana_trustless.rs:1128`). That fixture already builds **both** the
  exact-slot votes and later rooted votes via `tower_sync_tx_rooted`
  (`bridge/src/solana_trustless.rs:1249`) — so the fixture satisfies the rooted leg. No
  *live* source produces a lock proof at all; the relayer
  (`bridge/src/solana_relayer.rs`) only produces `StructureOnly`-grade finalized-account
  observations and has an explicit "voted but not yet rooted, never minted against" state
  (`:87`).
- The Option-B succinct wrapper is a typed seam, not a proof system:
  `SolanaConsensusStatement` (`bridge/src/solana_trustless.rs:730`) is the public
  instance, and `of_verified` (`:795`) mints it **only** for a proof the in-process
  anchored verifier accepts and that binds the bridge's own vault
  (`binds_bridge_vault`, `:955`). There is no circuit behind it yet — the design is
  `docs/deos/SOLANA-SUCCINCT-WRAPPER.md`.

**The governance join is `RUNS` over fixtures — but still through the demoted shim.**

- `grant_foreign_weight` (`dregg-governance/src/holding_weight.rs:754`) is the
  chain-agnostic fail-closed core; the weight *verdict* is the Lean-proven
  `grantWeightCore` over the FFI, not Rust. `VerifiedHoldingBallotBox` — the verified
  executor front door — exists (`dregg-governance/src/holding_weight.rs:811`, impl
  `:1243`), and `HostBallotBox` is documented DEMOTED (`:825`) with a `HashSet`+`>=`
  gate.
- **But the compiled join does not yet use the front door.** `dregg-interchain-gov`'s
  end-to-end cross-chain vote imports `CollectiveChoice` from `dregg_governance`
  (`dregg-interchain-gov/tests/cross_chain_governance.rs:45`) and builds it at `:463`,
  casting through `foreign_grant_and_cast` (`:542`). At HEAD `dregg_governance::CollectiveChoice`
  is `pub type CollectiveChoice = HostBallotBox` (`dregg-governance/src/lib.rs:587`) — the
  **DEMOTED shim**, not `collective_choice::CollectiveChoice`. So the cross-chain flow
  casts through `WeightedBallotEngine for HostBallotBox`
  (`dregg-governance/src/holding_weight.rs:1121`), whose one-vote and quorum gates are a
  `HashSet` and a `>=`, not the verified executor's `WriteOnce`/`AffineLe`/`CountGe`
  turns. `HostBallotBox::new` is also built in `dregg-governance`'s own `#[cfg(test)]`
  tests (`dregg-governance/src/lib.rs:621`–`:665`). The claim "the verified engine runs the
  vote" is `NAMED`, not `RUNS`, until this alias is repointed (Rung 0).
- Every Solana holding the join proves comes from `anchored_holding_with_cluster`
  (`dregg-interchain-gov/tests/cross_chain_governance.rs:174`) — a fixture cluster. The
  join is real; its ballot box is the shim and its input is not live.

**One-line status:** the math is trustless-modulo-the-anchor; the evidence is
fixture-true. This campaign is entirely about the evidence.

## 3. The target

A `$DREGG` holder or a bridge relayer, using only public mainnet infrastructure (an
Agave snapshot archive + a vote-transaction stream), assembles a `HoldingProof` /
`SolanaLockProof` that the **unmodified** production verifiers accept against a
**governance-pinned mainnet anchor**, with every commitment leg harvested-real (no
reconstruction seam). Governance weight is granted from a live mainnet holding;
`$DREGG` value is released on-chain against a live mainnet lock; and — at the top
rung — the on-chain release verifies a single constant-size dregg proof rather than
re-executing the consensus check or trusting an M-of-N oracle set. The per-chain
maturity table in `INTERCHAIN-MODEL.md` moves Solana's cells from "runs end-to-end
(fixtures) / consensus-verified off-circuit, live feed pending" to "runs end-to-end
against mainnet snapshot state / succinct on-chain verify."

## 4. Staged rungs (smallest-first, each with a gate)

### Rung 0 — repoint the cross-chain join off the demoted shim (days)

**What it makes real:** today `dregg-interchain-gov`'s cross-chain vote casts through
`HostBallotBox` (the `HashSet`+`>=` shim) via the `dregg_governance::CollectiveChoice`
alias — so its tally is *not* a verified executor turn even though its grant path is
Lean-proven. This rung makes the whole join, tally included, run on
`VerifiedHoldingBallotBox`, so there is exactly one verified front door. Nothing here
touches Solana; it is the cheapest rung and closes a real (not cosmetic) gap before the
value-bearing work lands on top. The false step to avoid: "delete an unused impl" — the
impl is **not** unused; the alias makes the cross-chain test reach it.

**Plan.**

1. In `dregg-interchain-gov` (`tests/cross_chain_governance.rs`, `examples/cross_chain_vote.rs`),
   replace `dregg_governance::CollectiveChoice::new()` with
   `VerifiedHoldingBallotBox::new(federation_id)` and swap `engine.open_poll(spec)` for
   `open_weighted_poll(&spec)` (`dregg-governance/src/holding_weight.rs:1180`). Note the
   rule constraint: `open_weighted_poll` refuses `DecisionRule::Supermajority` (a
   closed-electorate headcount rule) — the cross-chain polls already use `Plurality`, so
   this holds, but state it. `foreign_grant_and_cast` is generic over
   `WeightedBallotEngine` and already accepts `VerifiedHoldingBallotBox` (impl `:1243`);
   no registry change is needed.
2. Then remove the `WeightedBallotEngine for HostBallotBox` impl
   (`dregg-governance/src/holding_weight.rs:1121`) so no holding-weight flow can reach the
   shim again, and either delete the `pub type CollectiveChoice = HostBallotBox` alias
   (`dregg-governance/src/lib.rs:587`) or leave `HostBallotBox`/`HostVoteEngine` (`:486`)
   only as the named causal-log derivation aid with no `WeightedBallotEngine` surface.

**Gate.** `cargo test -p dregg-governance -p dregg-interchain-gov` green; the cross-chain
test's ballot engine is `VerifiedHoldingBallotBox` (grep the test — it constructs the
verified box, not the `CollectiveChoice` alias); `grep -rn "WeightedBallotEngine for
HostBallotBox"` returns nothing; and `light_client_tally` agrees with `tally`
(`dregg-governance/src/holding_weight.rs`) on the cross-chain poll, proving the board is
the verified executor's, not the shim's `HashSet`.

### Rung 1 — the rooted-attestation feed (1–2 weeks)

**What it makes real:** today the *only* producer of a rooted lock proof is the
fixture builder; a live value-release feed built with an exact-slot vote set alone
correctly fails closed at `SlotNotRooted`. This rung gives the live feed a
rooted-vote harvester, so a genuinely-finalized mainnet lock (or holding, when a
value decision needs finality) clears `tally_authorized_rooted` from real votes —
value release stops depending on a fixture.

**Plan.** Extend the feed seam to gather, in addition to the exact-slot votes for
`(slot, bank_hash)`, a set of *later* TowerSync votes whose ingested tower `root ≥
slot`, each still bound to its proven on-chain authorized voter
(`bridge/src/solana_provenance.rs:738`–`:757` is the exact acceptance predicate the
harvester must feed). Two ingestion shapes, both matching the module-doc design
(`bridge/src/solana_feed.rs:99`–`:107`): a Geyser plugin streaming vote transactions,
or full-transaction `getBlock` harvesting (vote transactions and their signatures
appear in descendant blocks). Add a `VoteHarvester` seam (the source of the
`ValidatorVote { tx_witness }` set) so `LocalValidatorFeed` and the future
`SnapshotFeed` share it. On a local cluster this is testable end-to-end today: the
harness can advance the validator past the lock slot and collect the later rooted
votes over RPC.

**What stays fixture/reconstructed after this rung:** the accounts-hash Merkle and
bank-hash preimage (rung 2). Rung 1 makes the *rooted-finality evidence* real
without yet making the *commitment* legs real — state that boundary honestly.

**Gate.** A new `LocalValidatorFeed`-driven test that advances a
`solana-test-validator` until the lock slot roots, harvests the later votes, and
drives `mint_against_lock_proof_anchored` (or `verify_lock_proof_consensus_anchored`)
to `ConsensusVerified` from a **non-fixture** rooted vote set — plus the negative:
the same proof with the rooted votes withheld returns `SlotNotRooted`, proving the
leg is load-bearing, not decorative.

### Rung 2 — the mainnet `SnapshotFeed` (multi-week; the core rung)

**What it makes real:** replaces the two reconstructed legs
(`bridge/src/solana_feed.rs:42`–`:57`) with mainnet-committed artifacts, so a proof
verifies over **real** bank state the validators actually voted — the first time a
consensus-verified holding/lock is not assembled by dregg's own code. This is the
rung that earns "mainnet" in the maturity table.

**Plan** (the pipeline shape is specified at `bridge/src/solana_feed.rs:113`–`:120`;
build `SnapshotFeed { archive_path, vote_harvester }` implementing `HoldingFeedSource`
plus a lock analogue):

1. **Unpack an Agave full snapshot** (`snapshot-<slot>-<hash>.tar.zst`) into
   `BankHashComponents` — `parent_bank_hash`, the committed accounts hash
   (`accounts_delta_hash`, or the lattice hash post-SIMD-215), `signature_count`,
   `last_blockhash` — the four fields RPC never returns
   (`bridge/src/solana_feed.rs:76`–`:84`).
2. **Walk the accounts DB** (AppendVec / tiered-storage) to compute the **real**
   16-ary accounts-hash Merkle tree and extract a **real** `AccountsInclusionProof16`
   for the holder token account, every stake and vote account, and the StakeHistory
   sysvar — replacing `single_chunk_proofs`.
3. **Derive the mainnet `EpochStakeTable`** via `derive_stake_table` from the real
   stake/vote set, and — from snapshots at successive epoch boundaries — build the
   `RotationStep` chain (`bridge/src/solana_provenance.rs:773`) from the pinned anchor
   epoch to the snapshot epoch.
4. **Match harvested ≥ 2/3-stake exact-slot + rooted votes** (rung 1's harvester) to
   the snapshot slot's bank hash.
5. **Assemble the same `HoldingProof` / `SolanaLockProof`** the fixtures emit —
   nothing downstream changes; the verifier entry stays
   `prove_holding_consensus_anchored` / `verify_lock_proof_consensus_anchored`.

**Anchor governance (the part that is a process, not code).** The verifier is
trustless *modulo the pinned `WeakSubjectivityAnchor`*. Someone must choose the
operator's initial `(epoch, stake_table_root)` and someone must be able to advance
it. Specify this explicitly:

- **Who pins it.** The anchor lives in configuration read by the *caller*, never the
  feed (`prove_feed_holding` and `MirrorConfig::pinned_anchor_*` already enforce
  caller-pinning — `bridge/src/solana_trustless.rs:986`). Pin it via the same dregg
  governance poll machinery this whole track feeds: a `CollectiveChoice` poll whose
  subject is the anchor tuple, decided by existing $DREGG holders. The bootstrap
  anchor (before any holder exists) is pinned by the operator out-of-band and recorded
  in the deployment config, exactly as the module doc says
  (`bridge/src/solana_feed.rs:59`–`:68`).
- **By what process it advances.** The `RotationStep` chain lets the pinned anchor stay
  *old* while proofs reach the current epoch — so the anchor rarely needs to move. When
  it does (weak-subjectivity period expiry), a governance poll pins the new tuple,
  cross-checked against multiple independent snapshot providers. Document the
  weak-subjectivity period and the re-pin cadence as an operational parameter.

**Gate.** A `SnapshotFeed` ingesting a **real captured mainnet (or public devnet)
snapshot** produces a `HoldingProof` whose `mainnet` inclusion verifies through the
unmodified `prove_holding_consensus_anchored` against the pinned anchor — with the
`single_chunk` reconstruction path deleted from the live source. Adversarial gates:
a tampered account leaf fails `AccountsInclusionInvalid`; a snapshot whose derived
anchor root ≠ the pinned root fails `AnchorRootMismatch`; a below-2/3 harvested vote
set fails `StakeBelowThreshold`. The check that this rung is genuinely closed is that
**no fixture constructor and no `single_chunk_proofs` call remains on the live path** —
grep proves it.

### Rung 3 — trustless outbound release via the succinct wrapper (multi-month; `VISION`)

**What it makes real:** today outbound value release either re-executes the whole
consensus check on the verifying side or (in the mirror's shipped slice) trusts an
M-of-N oracle attestation. This rung produces a single constant-size proof that the
in-process anchored verifier would accept, so an on-chain release verifies a **dregg
proof** — reusing dregg's existing recursive-STARK verify surface — instead of an
oracle set or an O(votes + accounts + rotation) re-execution.

**Plan** (design: `docs/deos/SOLANA-SUCCINCT-WRAPPER.md`). Build the relayer circuit
for relation `R`: "there exists a `SolanaLockProof` the anchored verifier accepts,
and I reveal only `SolanaConsensusStatement`." The public instance and its binding
digest already exist as the typed seam (`bridge/src/solana_trustless.rs:730`, `:762`);
`of_verified` (`:795`) is the ground-truth contract the circuit must satisfy. Wire the
resulting proof into the on-dregg / on-chain `verify_lock_proof_succinct` that binds
`SolanaConsensusStatement::digest` as its single public input, and route the verified
statement through the same conservation accounting as the in-process path. This does
not avoid the hard consensus work — it pays for it once, off-chain, per proof.

**Gate.** A generated proof for a genuinely-finalized lock verifies in O(1) on the
target surface and binds exactly the mint-accounting public inputs; a proof for a
below-2/3 / wrong-anchor / non-bridge-vault lock fails to generate (because
`of_verified` refuses to mint the statement); the on-chain verifier rejects a proof
whose public digest does not match the credited mint. Cross-check the circuit's
accept set against `verify_lock_proof_consensus_anchored` on a battery of proofs
(both polarities) — the circuit must accept exactly what the reference verifier
accepts.

## 5. Dependencies on other tracks

- **Solana consensus circuit / recursive-STARK verify surface.** Rung 3 reuses dregg's
  existing recursion verifier as its succinct-check substrate; it cannot land before
  that surface is proof-frozen. Rungs 0–2 have **no** dependency on the circuit — they
  are pure re-executor-grade ingestion and land independently.
- **VK / protocol freeze.** Rung 3's on-chain verifier pins a verification key; it
  should not be built against an unfrozen protocol (see the launch-readiness P1
  freeze-protocol item). Rungs 0–2 are protocol-agnostic.
- **Deployment / devnet durability.** Rungs 1–2 need a persistent Solana node or
  snapshot source and a durable operator config for the pinned anchor
  (`SOLANA-DEVNET.md`, `DEVNET-DEPLOYMENT-REALITY.md`). The live games devnet's
  ledger-loss-on-reboot lesson applies: the anchor config and any harvested-vote cache
  must be on a durable data-dir, not hand-run state.
- **Governance poll machinery.** Rung 2's anchor-pinning process reuses
  `CollectiveChoice` — the same engine this track feeds — so it is self-hosting once
  rung 0 leaves a single verified ballot front door.
- **The Solana snapshot/AppendVec format.** Rung 2 tracks Agave's on-disk bank/accounts
  serialization and the SIMD-215 accounts-hash transition; a format change is a
  maintenance dependency on upstream Solana, not on another dregg track.

## 6. Risks + the falsifier for the load-bearing assumption

**The load-bearing assumption:** *a mainnet Agave snapshot's serialized bank fields
and accounts DB reproduce, byte-for-byte, the `BankHashComponents` and 16-ary
accounts-hash Merkle that the validators actually voted over* — i.e. the snapshot is
a faithful witness to the committed state, so `bank_components.compute()` equals the
`bank_hash` a real supermajority signed.

**Falsifier (run it before trusting rung 2):** take one real mainnet slot `S`.
Independently obtain (a) the snapshot-derived `bank_hash` from `SnapshotFeed`'s
`BankHashComponents::compute()` and (b) the `bank_hash` carried in a real TowerSync
vote for `S` harvested from a descendant block. **If they differ, the snapshot
reconstruction is wrong and the whole rung is a mirror** — the feed would be proving
against a hash no validator signed, and the "supermajority" would be vacuous exactly
as the caller-supplied-table forgery was (`PROOF-OF-HOLDINGS.md`'s second
load-bearing check). This is the single check that separates "verifies over real bank
state" from "verifies over dregg's reconstruction of bank state," and it must be a
CI gate on rung 2, not a one-time manual check. The SIMD-215 lattice-hash transition
is the concrete way this can silently break: if the feed computes the pre-215
`accounts_delta_hash` while the cluster votes the post-215 lattice hash, (a) and (b)
diverge and the gate catches it.

**Other risks, each with its mitigation:**

- **Anchor staleness / weak-subjectivity expiry.** If the pinned anchor ages past the
  weak-subjectivity period and no honest party re-pins, a long-range attacker with old
  keys could forge a rotation chain. Mitigation: the `RotationStep` chain keeps the
  anchor rarely-moved but not never-moved; document the re-pin cadence and require the
  governance poll to cross-check ≥ 2 independent snapshot providers. Falsifier: derive
  the anchor tuple from two independent snapshots of the same epoch — they must match.
- **Vote-harvesting liveness (rung 1).** If the Geyser/`getBlock` stream misses the
  later rooted votes (pruned history, rate limits), value release fails closed at
  `SlotNotRooted` — a liveness failure, not a soundness one. Mitigation: fail-closed is
  the correct posture; add retry/backfill from archival RPC and surface the distinction
  in the relayer's status so an operator does not misread a liveness stall as a rejected
  lock.
- **Circuit ⟂ reference divergence (rung 3).** A circuit that accepts *more* than
  `verify_lock_proof_consensus_anchored` is a value hole. Mitigation: the accept-set
  differential in the rung-3 gate; treat any divergence as a release-blocker. Do not
  ship the circuit on a "it builds green" signal — the gate is the differential against
  the reference verifier, both polarities.
- **`getProgramAccounts` unavailability on public RPC.** Rung 2 deliberately sources the
  stake set from the snapshot, not RPC, precisely because `getProgramAccounts` over the
  stake program is disabled/rate-limited on public mainnet
  (`bridge/src/solana_feed.rs:90`–`:92`) — so this is a designed-around constraint, not
  an open risk, but it means the snapshot archive is a hard dependency with no RPC
  fallback.
