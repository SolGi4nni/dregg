# Trustless Solana bridge — the honest upgrade from the trusted-oracle $DREGG mirror

## What exists today (the trusted leg)

`bridge/src/solana_mirror.rs` mirrors a Solana SPL token (`$DREGG`) into dregg's
value layer. The inbound direction works like this:

```text
Solana: user locks N $DREGG  ──►  oracle threshold-attests the lock
                                        │   SolanaLockAttestation
                                        ▼
                            MirrorState::mint_against_lock
                            → Effect::Mint { target, amount }  (Σδ=0, conserved)
```

The lock evidence is a `SolanaLockAttestation`: a `FederationAttestation`
(Ed25519/Schnorr threshold signature over `lock_id || spl_mint || amount ||
recipient || epoch`, reused verbatim from the `midnight` bridge). dregg verifies
the *signature* under the epoch oracle key. **dregg does NOT verify Solana
consensus.** The trust assumption is: ≥ threshold of the oracle/validator set is
honest and the lock they signed really happened on a finalized Solana block.

This document specifies the trustless upgrade: replace "trust the oracle's word
that the lock happened" with "verify a proof that the lock happened, anchored in
Solana's own consensus."

The existing **outbound** zk pattern (`bridge/src/ethereum.rs`, `chain/`'s SP1
guest) is the *wrong direction* for this: it wraps a dregg STARK so an EVM
contract can verify dregg's finality. Inbound proof-of-lock is the dual problem
— verify *Solana's* finality inside dregg — and shares no machinery with it.

## Why Solana is materially harder than Ethereum (be honest)

An Ethereum light client is comparatively tame: post-Merge finality is Casper
FFG with a fixed-size, randomly-sampled **sync committee** (512 validators) whose
aggregate BLS signature over a beacon block header is a single, cheap-to-verify
artifact; state/receipt inclusion is a Merkle-Patricia proof against the block's
`stateRoot`/`receiptsRoot`. That is what makes ETH light clients (Helios, the
sync-committee SNARKs) practical.

Solana has no sync committee and no compact finality artifact. To verify that a
lock happened you must reconstruct three independent things:

1. **PoH (Proof of History)** — the block's `blockhash` is the tail of a long
   SHA-256 hash chain. PoH gives *ordering and elapsed-ticks*, not finality; it
   only proves the leader did the sequential hashing. Verifying it means
   re-hashing the tick chain (or trusting the recorded tick count), which is
   cheap per-tick but unbounded in aggregate.

2. **Tower BFT vote-power on the bank hash** — finality ("optimistic
   confirmation" / rooted) is reached when validators holding ≥ 2/3 of the
   *active stake* have voted (via vote transactions) for a slot's **bank hash**,
   with lockouts. To verify this you must:
   - know the **stake distribution** for the relevant epoch (the leader schedule
     and per-vote-account stake — this is itself part of the bank state and
     changes every epoch);
   - collect the *vote transactions* (or the aggregated tower state) and sum
     their stake;
   - check ≥ 2/3 threshold and lockout consistency.
   **This stake-weighted vote-set tracking is the hard part.** There is no single
   aggregate signature; votes are individual Ed25519 sigs from hundreds of
   distinct vote accounts, and the stake weights must themselves be proven
   against the bank state. Tracking the validator/stake set across epoch
   boundaries (the analogue of ETH's sync-committee rotation, but per-epoch and
   over the *entire* stake table, ~1–2k vote accounts) is the dominant cost.

3. **Accounts inclusion against the bank hash** — Solana's `bank_hash` commits to
   (among other things) the **accounts delta hash** (the merkle/hash of accounts
   *written in that slot*) and, at epoch boundaries, the full **accounts hash**.
   To prove "the vault account holds the locked N $DREGG in the proven bank
   state" you need an inclusion proof of the vault account into the accounts
   hash that the (super-majority-voted) bank hash commits to. The accounts-hash
   structure (historically a flat sorted hash, moving toward a merkle/verkle
   form) is not designed as a light-client inclusion vehicle the way ETH's MPT
   is, which makes the inclusion proof awkward and version-dependent.

So a faithful on-dregg Solana light client must: track the full per-epoch stake
table, ingest and stake-weight the vote set for a slot, verify ≥2/3 + lockouts,
verify the PoH linkage of that slot, and verify an accounts inclusion proof into
the voted bank hash. Each piece is individually buildable; the *stake-weighted
vote-set + epoch-rotation tracking* is the genuine multi-month research/engineering
item.

## Option A — on-dregg Solana light client (verify consensus directly)

dregg ingests Solana consensus artifacts and verifies them with its own logic
(possibly proven in-circuit so a *dregg* light client, not just a re-executing
validator, witnesses it).

| Piece | What it is | Cost / feasibility |
| --- | --- | --- |
| Stake-table tracking | Per-epoch validator→stake map, rotated at epoch boundaries; root committed | **Hardest.** ~1–2k vote accounts; must be proven against bank state; epoch rotation is the sync-committee analogue but heavier. Needs a committed, updatable stake-root and a rotation proof. |
| Vote-set aggregation | Collect vote txs for a slot, sum stake, check ≥2/3 + lockouts | Hundreds of individual Ed25519 verifications + a stake-weighted sum. Expensive but mechanical. In-circuit: a batch-Ed25519 + accumulation AIR. |
| PoH linkage | Re-hash / check the tick chain to bind the slot's blockhash | Cheap per tick, but you must bound how much you check; trust-minimized requires the full chain or a recursive PoH proof. |
| Accounts inclusion | Merkle/hash inclusion of the vault account into the voted bank hash | Awkward; depends on the (changing) accounts-hash format. Version-coupled to the Solana release. |
| Maintenance | Track Solana protocol upgrades (vote format, accounts-hash format, feature gates) | Ongoing liability — every Solana hard-fork can break the verifier. |

**Verdict:** correct and maximally trustless, but a large, fragile, perpetually-
maintained subsystem. The stake-weighted vote-set tracking and the accounts-hash
format coupling are the two teeth that make this a multi-month effort, not a
slice.

## Option B — inbound zk-proof-of-lock (verify a SNARK/STARK of the lock)

A **relayer** runs the Option-A light-client logic *off-chain inside a zk circuit*
and produces a succinct proof: "Solana slot S is finalized (≥2/3 stake voted its
bank hash), and account `vault` in S's bank state holds a lock record for N
$DREGG bound to dregg recipient R." dregg verifies that one succinct proof.

```text
relayer (off-dregg):
   Solana RPC ──► light-client circuit (stake-weighted votes + PoH + accounts
                  inclusion) ──► SNARK/STARK proof π  +  public inputs
                                 (slot, bank_hash, vault, amount, recipient, lock_id)
dregg-side:
   verify_lock_proof(π, public_inputs)  ──►  same conservation accounting as today
```

- **Prover side (off-dregg, the relayer):** anyone can run it; the proof is
  self-certifying so the relayer is untrusted. The circuit *is* the Option-A
  verification logic — so Option B does not avoid the hard parts, it **relocates
  them off-chain** and pays for them once per proof instead of per-verifier. The
  stake-table commitment + vote-set + accounts-inclusion still have to be encoded
  in the circuit; this is the dominant build cost and it is shared with A.
- **dregg-side verifier:** reuses dregg's existing STARK verification machinery
  (`sdk/src/full_turn_proof.rs`, `lightclient/`, `dregg_circuit`) — dregg already
  verifies recursive BabyBear STARKs cheaply. If the proof-of-lock is produced in
  a compatible proof system, the dregg-side verify is *small* (one succinct
  check + public-input binding), which is the whole point: the verifier stays
  light even though the consensus logic is heavy.

**Verdict:** more tractable to *deploy* than A because the heavy consensus logic
lives off-chain in a single relayer circuit and the on-dregg cost is a constant-
size succinct verify dregg already has. The build cost of the circuit is
comparable to A (you still encode the consensus logic), but you build it once,
off-chain, and never carry it in every dregg verifier.

## Recommendation — hybrid, with B as the trustless target

1. **Now (shipped):** trusted-oracle threshold attestation (`SolanaLockAttestation`).
2. **Interim hardening (cheap, build next): watchtower fraud-challenge.** Mirror
   the `midnight_gateway::Watchtower` pattern (`bridge/src/midnight_gateway.rs`):
   make relaying permissionless and let *anyone* run a watcher that independently
   checks the lock against Solana and publishes a fraud-proof if the oracle signed
   a lock that did not happen. This turns "trust ≥2/3 of the oracle set" into
   "trust that ≥1 honest watcher exists" — a strictly weaker assumption — without
   building any consensus verifier. It is the highest trust-per-effort step.
3. **Trustless target: Option B (inbound zk-proof-of-lock).** Build the relayer
   light-client circuit and verify its succinct proof on dregg via the existing
   STARK verify. Prefer B over A because the on-dregg verifier stays light and the
   consensus liability is isolated in one upgradable off-chain circuit.

Option A (a full on-dregg Solana light client) is only worth it if a relayer-free,
fully-on-protocol verification is a hard requirement; otherwise B subsumes it with
a lighter deployed footprint.

## Migration — same conservation, stronger trust

The mirror's conservation invariant (`live_supply ≤ currently_locked`) and all the
replay/amount/bound checks are **independent of how the lock is evidenced**. The
trust upgrade is a swap at exactly one seam:

```text
  mint_against_lock(SolanaLockAttestation)        // trusted: verify a signature
                          ↓  swap the evidence, keep the accounting
  mint_against_lock_proof(SolanaLockProof)         // trustless: verify_lock_proof(proof)
```

Both paths converge on the *same* private accounting routine
(`MirrorState::credit_lock`) that does the amount-bound / replay / conservation
checks and emits the `Effect::Mint`. Only the front gate (signature-verify vs
proof-verify) differs. This means the trustless path can be introduced alongside
the trusted one (the trusted attestation stays as the fallback while the proof
system matures), and flipped per-mirror by config without touching the value
layer.

## What is built now (the real consensus verification)

`bridge/src/solana_consensus.rs` is the genuine cryptographic core; `bridge/src/solana_trustless.rs` wires it into the mirror. The consensus verification is **no longer a stub** — it is real Ed25519 + SHA-256 arithmetic.

### Real (reaches `LockProofTrust::ConsensusVerified`)

- **Stake-weighted vote verification (the core).** `EpochStakeTable` maps each
  validator's authorized vote pubkey → active stake. `verify_supermajority`
  verifies, for the claimed `(slot, bank_hash)`: each `ValidatorVote`'s **real
  Ed25519 signature** (`ValidatorVote::verify_signature`), collapses duplicate
  voters, sums the stake of the *cryptographically valid* voters, and enforces
  `3·voted ≥ 2·total` (the ≥ 2/3 super-majority) in `u128`. A forged signature
  contributes **zero** stake, so a set that needs a forged vote to clear 2/3 is
  refused.
- **Bank-hash binding.** `BankHashComponents::compute` recomputes
  `bank_hash = H(parent_bank_hash, accounts_hash, signature_count,
  last_blockhash)` and binds it to the voted `bank_hash`, tying the accounts hash
  (and the PoH tail) the inclusion opens into to *what the super-majority voted*.
- **Accounts-hash inclusion.** `verify_accounts_inclusion` folds a
  domain-separated **sorted-Merkle** sibling path from the vault account's
  lock-record leaf (`account_leaf` binds `vault_account, amount, recipient,
  lock_id`) to the committed `accounts_hash`. Distinct leaf/node domain tags
  prevent replaying an interior node as a leaf.
- **PoH linkage.** `verify_poh_segment` re-hashes a real SHA-256 tick chain from
  a verified `anchor_hash` to the slot's `last_blockhash`, bounded by
  `MAX_POH_REHASH` so a malicious `num_hashes` cannot make the verifier spin.

`verify_lock_proof_consensus(proof, …, stake_table, require_poh)` runs
structure+binding, then all of the above against the **tracked epoch stake
table**, and returns `ConsensusVerified` only when every check passes.
`MirrorState::mint_against_lock_proof_consensus` routes such a verified proof
through the **same** `credit_lock` conservation accounting as the trusted path.
`verify_lock_proof` / `mint_against_lock_proof` remain as a **structure-only**
path (no stake table → `StructureOnly`, never `ConsensusVerified`).

### The mainnet wire-format adapter — pass 2 (`bridge/src/solana_wire.rs`)

Pass 2 closes the two dominant wire-format gaps, using the lightweight
**type-only** Solana crate `solana-vote-interface` (verified: it pins
curve25519-dalek 4.x / ed25519-dalek 2.x and unifies with the BabyBear/proof
stack — **no version conflict**; the heavy `solana-sdk` monolith is deliberately
avoided).

1. **Vote-transaction ingestion — REAL (done).** `solana_wire::ingest_vote_transaction`
   parses a real bincode-serialized vote `Transaction` (the compact-`u16`
   `ShortVec` framing + the message), bincode-decodes its `VoteInstruction`
   (`Vote` / `TowerSync` / `CompactUpdateVoteState` / `UpdateVoteState`),
   **verifies the real Ed25519 signature** of the designated vote authority over
   the real serialized message, and extracts the voted `(slot, bank_hash)` + the
   vote account + the authorized voter. It produces a `ValidatorVote` (keyed by
   the **vote account** — the real stake-weighting key) carrying a
   `VoteTxWitness`; `ValidatorVote::verify_signature` re-verifies the real
   transaction, so the pass-1 `verify_supermajority` tally now **runs over real
   vote transactions**, not the canonical placeholder.
2. **Accounts-hash format fidelity — REAL (done).** `solana_wire::solana_account_hash`
   reproduces Solana's per-account hash `blake3(lamports_le ‖ rent_epoch_le ‖
   data ‖ executable ‖ owner ‖ pubkey)` (zero-lamport → all-zero default), and
   `verify_account_inclusion_16ary` folds the real **16-ary fan-out**
   (`MERKLE_FANOUT = 16`) Merkle whose interior nodes are `sha256(child‖…)` over
   up to 16 children. The bank-hash recipe is now the real
   `sha256(parent ‖ accounts_delta_hash ‖ signature_count_le ‖ last_blockhash)`.
   `verify_lock_proof_consensus` accepts an optional `MainnetAccountInclusion`
   (the vault account's real fields + a 16-ary proof) and verifies the real
   account hash into the voted accounts hash, decoding the lock record from the
   account `data`.

### Bank-state provenance — pass 3 (`bridge/src/solana_provenance.rs`)

Pass 3 closes the dominant remaining trust gap: the stake table and the
authorized-voter binding were **trusted input**; they are now **derived from
Solana's own bank state**, verified against the voted accounts hash and rotated
from an irreducible weak-subjectivity anchor.

1. **Stake table from bank state — REAL (done).** `solana_provenance::derive_stake_table`
   proves each stake-program and vote-program account is included in the voted
   accounts hash (reusing pass-2's `verify_account_inclusion_16ary`) and decodes
   their data: each stake account's `Delegation` (decoded from the mainnet
   `StakeStateV2` bincode layout — tag + `Meta` + `Stake.delegation`) contributes
   its active stake (`activation_epoch ≤ epoch < deactivation_epoch`) to its
   delegated vote account, and each vote account's `VoteState` (decoded with the
   type-only `solana-vote-interface`, all of V1_14_11/V3/V4) yields the
   authorized voter. The `EpochStakeTable` is now **proven from the bank hash the
   votes attest**, not supplied as trusted input. A tampered stake/vote account
   fails inclusion and is refused.
2. **Authorized-voter binding — REAL (done).** `VerifiedStakeTable::tally_authorized`
   counts a vote only when it is witness-backed (a real vote transaction, pass 2)
   **and** its signer equals the vote account's on-chain `authorized_voter` for
   the epoch (decoded from the proven vote-account state). A vote naming an
   attacker key as authority — or a placeholder vote with no on-chain authority —
   contributes **zero** stake. This closes pass-2's named gap.
3. **Epoch rotation from a trusted anchor — REAL (done).** A
   `WeakSubjectivityAnchor { epoch, stake_table_root }` pins one known-good
   checkpoint (the irreducible trust root, like every light client's). The anchor
   epoch's table is admitted only when its `EpochStakeTable::root` (a
   domain-separated commitment over the sorted `pubkey → stake` map) equals the
   pinned root; `solana_provenance::rotate` then advances the trusted table one
   epoch at a time, admitting each next-epoch table only when it is (a) derived
   from bank state and (b) attested by ≥ 2/3 of the *already-trusted* epoch's
   stake. Everything after the anchor is verified; a forged rotation (not
   attested by trusted stake) is refused.
4. **PoH anchoring policy — REAL (done).** `solana_consensus::PohAnchorPolicy`
   makes `require_poh` a real policy: a PoH segment must chain from exactly the
   trusted checkpoint blockhash (`anchor_blockhash`) and stay within `max_hashes`
   ticks before re-hashing to the slot's blockhash. A relayer can no longer pick
   its own PoH anchor. (Full-slot ~432k-hash trust-minimization is still the
   recursive-proof item; this bounds the in-process re-hash to a checkpoint
   window.)

The trustless entry point is `verify_lock_proof_consensus_anchored(proof,
spl_mint, min, max, anchor, require_poh, poh_policy)` (and
`MirrorState::mint_against_lock_proof_anchored`): it takes **no trusted stake
table** — only the anchor + the proof's `StakeProvenance`. The older
`verify_lock_proof_consensus(…, stake_table, …)` remains as the lower-level
consensus primitive (the supermajority arithmetic over an already-obtained
table).

### What still remains (honest — pass 4 and the named refinements)

1. **The weak-subjectivity anchor itself** is trusted. This is irreducible: a
   from-genesis-trustless Solana light client would replay all history. Every
   deployed light client (ETH included) trusts a recent finalized checkpoint;
   `WeakSubjectivityAnchor` is dregg's, named as such.
2. **Stake-activation timing nuance.** `active_stake` counts a delegation at full
   weight inside its `[activation, deactivation)` window; Solana's warmup/cooldown
   effective-stake curve and the two-epoch leader-schedule snapshot offset are
   refinements. The *security* property — stake weights proven against a bank hash
   rather than trusted — holds regardless; the derived total can differ from the
   cluster's only by the warmup/cooldown delta on freshly (de)activated stake.
3. **Account-data lock-record layout.** The vault account's `data` carries the
   lock record in an *adapter-defined* layout (`encode_lock_record`); the
   per-account hash + the 16-ary tree are mainnet-faithful, but the lock
   program's account schema is a deploy-time choice, not a Solana constant.
4. **Bank-hash version extras.** The classic 4-field recipe is byte-faithful; the
   epoch-accounts-hash (at EAH slots) and the accounts lt-hash (SIMD-0215) the
   modern bank folds in at specific slots are not modeled.
5. **Option-B succinct wrapper (optional).** Wrapping the above in an off-dregg
   relayer circuit + a dregg-side succinct verify keeps the on-dregg cost
   constant; the in-process verification is the Option-A logic it would encode.

**Honest status:** the bridge is now **trustless modulo the weak-subjectivity
anchor** (plus the named stake-timing / lock-layout / bank-hash-version
refinements above, none of which is a consensus-soundness hole). For a lock whose
votes are real signed vote transactions, whose accounts inclusion uses the real
16-ary format, and whose `StakeProvenance` derives the stake table + authorized
voters from bank state anchored at a `WeakSubjectivityAnchor`,
`verify_lock_proof_consensus_anchored` verifies — with **no trusted stake-table
input** — a ≥ 2/3 stake-weighted Ed25519 attestation by the on-chain authorized
voters over a stake distribution proven from the voted bank hash, binds the lock
record to that bank hash, and (when required) checks PoH against a bounded-anchor
policy. The watchtower interim remains a cheap complementary hardening for the
trusted path.
