# SOLANA-ANCHOR-AND-SNAPSHOT-FEED — pinning the operator anchor + snapshot/geyser ingestion

Track-A operational runbook. Two things live here, and they are at very different
maturities — read the status line before you touch anything:

| Procedure | Status | Where the code is |
|---|---|---|
| **Choose + publish + audit + pin the `WeakSubjectivityAnchor`** | **executable today** (the pin API and the deterministic root are real at HEAD) | `bridge/src/solana_provenance.rs:575` (type), `bridge/src/solana_consensus.rs:196` (`root()`), `bridge/src/solana_trustless.rs:986` / `dregg-pay/src/watcher.rs:319` (the pin) |
| **Derive a *mainnet* anchor from bank state in-repo** | **(pending: SnapshotFeed unbuilt — Track A rung 2)** | designed at `bridge/src/solana_feed.rs:70`–`:120`, no impl |
| **Snapshot ingestion of holdings/locks** | **(pending: SnapshotFeed unbuilt — Track A rung 2)** | designed at `bridge/src/solana_feed.rs:113`; verifier entry that will consume it is real (`prove_holding_consensus_anchored`, `bridge/src/solana_holdings.rs:465`) |
| **Live-validator ingestion (dev cluster)** | **RUNS** | `LocalValidatorFeed` (`bridge/src/solana_feed.rs:570`), harness `scripts/solana-local-harness.sh`, gated e2e `bridge/tests/solana_local_e2e.rs` (`SOLANA_LOCAL=1`) |
| **Advance/re-pin via a governance poll** | **(pending: needs rung 0 — one verified ballot front door)** | design in `docs/deos/INTERCHAIN-LIVE-CAMPAIGN.md` §4 rung 0/2 |

This runbook fills the hole `docs/ops/PAYMENTS-GO-LIVE.md:52`–`58` leaves: its step 2
says "configure the real governance-chosen `(epoch, stake_table_root)`; the anchored
path fails closed without it" but ships no procedure for *how you choose it, publish it,
let a third party check it, or wire it in*. That procedure is the executable core below.

> **⚠ DO NOT EXECUTE the snapshot-ingestion sections (§7) against mainnet funds.**
> `SnapshotFeed` does not exist at HEAD (`bridge/src/solana_feed.rs:64` states it plainly:
> "`NAMED` — a complete design in the module doc … with no implementation"). Every
> mainnet snapshot step is a **design rehearsal**, marked "(pending: SnapshotFeed unbuilt
> — Track A rung 2)". The only ingestion that runs today is the dev-cluster
> `LocalValidatorFeed` (§8), and it **cannot and must not** impersonate mainnet
> (`bridge/src/solana_feed.rs:49`–`:50`).

> **Network fact (do not design around it):** there are two tailnets and they cannot
> reach each other (`deploy/README.md:17`–`37`). Nothing in this runbook routes through
> a gateway-Caddy-over-tailnet path. Anchor config and any harvested-vote cache live on a
> **durable data-dir on the box that runs the watcher/relayer**, not shipped across
> tailnets — and the ledger-loss-on-reboot lesson (`deploy/README.md:92`–`96`) applies:
> never keep the anchor config or a vote cache in `mktemp -d`.

---

## 1. The trust model (why the anchor is the whole ballgame)

The Solana consensus verifiers are trustless **modulo one pinned checkpoint** — the
`WeakSubjectivityAnchor` (`bridge/src/solana_provenance.rs:575`):

```rust
pub struct WeakSubjectivityAnchor {
    pub epoch: u64,
    pub stake_table_root: [u8; 32],
}
```

Everything else is derived and checked: the stake distribution and authorized voters are
reconstructed from Solana's own bank state and admitted **only** when the derived table's
root equals `stake_table_root` at `epoch` (`VerifiedStakeTable::from_anchor`,
`bridge/src/solana_provenance.rs:618`; the root check is `:635`, failing with
`ProvenanceError::AnchorRootMismatch`). Later epochs are reached by attested `rotate`
steps from the anchor. The anchor is **the caller's, never the prover's/feed's**
(`bridge/src/solana_feed.rs:59`–`:68`) — a feed that fabricates a distribution *and* a
matching self-derived root is refused, because verification pins the root from operator
config, not from the feed (`feed_cannot_self_authorize_against_a_different_pin`,
`bridge/src/solana_feed.rs:817`).

**Fail-closed with no anchor.** If no anchor is pinned, the anchored path returns
`HoldingProofError::AnchorNotPinned` (`bridge/src/solana_holdings.rs:238`,
`dregg-pay/src/watcher.rs:352`) / `LockProofError::AnchorNotPinned`
(`bridge/src/solana_trustless.rs:301`). There is **no** fallback to a caller-supplied
table — that fallback was the original forgery (`docs/deos/PROOF-OF-HOLDINGS.md:115`–`127`).

So the operator's entire trust responsibility reduces to: **choose one honest
`(epoch, stake_table_root)`, and make it socially auditable.** That is a weak-subjectivity
checkpoint, exactly like any light client's — you cannot verify it from nothing; you take
it from a trusted, finalized, out-of-band-confirmed point and let the world check it.

---

## 2. The anchor's root is deterministic and publicly recomputable (the audit primitive)

`stake_table_root` is not opaque. It is a fully specified, domain-separated SHA-256 over
the epoch's `(vote_pubkey → active_stake)` map (`EpochStakeTable::root`,
`bridge/src/solana_consensus.rs:196`):

```
root = SHA256(
    "dregg-solana-stake-table-root:v1"          // STAKE_TABLE_ROOT_TAG (…:118)
  ‖ epoch            as u64 little-endian
  ‖ len(stakes)      as u64 little-endian
  ‖ for each (vote_pubkey, active_stake) in ASCENDING vote_pubkey byte order:
        vote_pubkey  (32 raw bytes)
      ‖ active_stake as u64 little-endian
)
```

Two tables commit to the same root **iff** they have the same epoch and the same
`(vote_pubkey → active_stake)` map (`bridge/src/solana_consensus.rs:190`–`:195`). The map
is sorted because it is a `BTreeMap<[u8;32], u64>` (`bridge/src/solana_consensus.rs:137`),
so iteration is canonical.

**This is what makes the anchor socially auditable:** publish the anchor tuple *together
with the full active-stake map it commits to*, and anyone can recompute the root — with no
dregg code — and confirm the tuple. A standalone recomputer (executable today; depends only
on Python's stdlib + `base58`):

```python
#!/usr/bin/env python3
# recompute-anchor-root.py — third-party check of a published WeakSubjectivityAnchor.
# Usage: recompute-anchor-root.py anchor.json
#   anchor.json = {"epoch": <u64>,
#                  "stake_table_root": "<hex-64>",
#                  "stakes": {"<base58 vote pubkey>": <active_stake_lamports>, ...}}
# Prints the recomputed root and PASS/FAIL vs the published one. Mirrors
# EpochStakeTable::root (bridge/src/solana_consensus.rs:196) byte-for-byte.
import hashlib, json, sys
import base58  # pip install base58

a = json.load(open(sys.argv[1]))
TAG = b"dregg-solana-stake-table-root:v1"
entries = []
for pk_b58, stake in a["stakes"].items():
    pk = base58.b58decode(pk_b58)
    assert len(pk) == 32, f"{pk_b58} is not a 32-byte pubkey"
    entries.append((pk, int(stake)))
entries.sort(key=lambda e: e[0])          # ASCENDING pubkey byte order (BTreeMap)

h = hashlib.sha256()
h.update(TAG)
h.update(int(a["epoch"]).to_bytes(8, "little"))
h.update(len(entries).to_bytes(8, "little"))
for pk, stake in entries:
    h.update(pk)
    h.update(stake.to_bytes(8, "little"))
got = h.hexdigest()
want = a["stake_table_root"].lower()
print(f"recomputed root: {got}")
print(f"published  root: {want}")
print("PASS" if got == want else "FAIL — the tuple does not commit to this stake map")
sys.exit(0 if got == want else 1)
```

**Honest boundary of what this proves.** The recomputer proves *the published tuple commits
to the published map*. It does **not** prove *the map is Solana's true active stake at that
epoch*. The map is `derive_stake_table`'s **active** stake (post warmup/cooldown, from the
real stake accounts + the `StakeHistory` sysvar — `bridge/src/solana_provenance.rs:474`),
**not** raw delegations. Auditors who reassemble the map independently must derive active
stake Solana's way; the closest public cross-check is `getVoteAccounts.activatedStake`, and
whether dregg's derived active stake equals that value byte-for-byte is a **faithfulness
claim to verify, not assume** (the same class of concern as the bank-hash faithfulness
falsifier in `docs/deos/INTERCHAIN-LIVE-CAMPAIGN.md:306`–`327`). Treat a mismatch as a
derivation bug, not a rounding difference.

---

## 3. Choosing the anchor `(epoch, stake_table_root)`

You are choosing a **known-good weak-subjectivity checkpoint**: an epoch recent enough that
its validator set is still socially recognizable and its keys are not long-retired, and
finalized/rooted beyond any reorg doubt.

**Step 3.1 — pick the anchor epoch.** Choose a **finalized, rooted** epoch boundary, not the
tip. Confirm rooted finality out of band (a block explorer + your own full node + at least
one independent snapshot provider all agreeing on the epoch's boundary slot and bank hash).
Prefer an epoch boundary so no mid-epoch rotation is needed to *reach* it from itself; proofs
for later epochs then rotate forward via attested `RotationStep`
(`bridge/src/solana_provenance.rs:773`), so the pinned anchor can stay **old** and rarely
move (`docs/deos/INTERCHAIN-LIVE-CAMPAIGN.md:242`–`245`).

**Step 3.2 — obtain the epoch's active-stake map.** This is the input to `root()`. Two ways,
at two maturities:

- **(pending: SnapshotFeed unbuilt — Track A rung 2) — the in-repo, bank-state-faithful
  path.** Unpack an Agave full snapshot at the epoch boundary and run
  `derive_stake_table` over the real stake/vote account set + `StakeHistory` sysvar
  (`bridge/src/solana_feed.rs:93`–`:97`, `bridge/src/solana_provenance.rs:474`). This is the
  *only* path that yields the exact map the deployed verifier will re-derive and check
  against your pin. It cannot be run today because nothing walks the accounts DB
  (`getProgramAccounts` over the stake program is disabled/rate-limited on public mainnet —
  `bridge/src/solana_feed.rs:90`–`:92` — which is exactly why the snapshot is a hard
  dependency with no RPC fallback). **Until `SnapshotFeed` exists, you cannot produce a
  mainnet anchor that a mainnet proof will verify against in-repo.**

- **Interim cross-check (not a substitute) — `getVoteAccounts`.** For a *first read* of the
  distribution and a sanity cross-check, `getVoteAccounts` (finalized commitment) returns
  `votePubkey` + `activatedStake` per validator for the current epoch. Assemble
  `{votePubkey: activatedStake}` and feed it to the §2 recomputer to get a *candidate* root.
  **Do not pin this as the deployment anchor** unless and until it is confirmed equal to the
  snapshot-derived map (§3.2 first bullet) — RPC echoes are unbound to any commitment
  (`bridge/src/solana_feed.rs:89`–`:92`) and the active-stake-faithfulness caveat in §2
  applies. This is a bootstrapping report, in the exact sense of `HoldingFeed::derived_anchor`
  (`bridge/src/solana_feed.rs:166`–`:170`): pin-once, out of band, after inspection — never a
  trust root on its own.

**Step 3.3 — compute the root.** Run the §2 recomputer over the map from 3.2 to get the
`stake_table_root` hex. The tuple `(epoch, stake_table_root)` is your candidate anchor.

**Step 3.4 — rehearse the pin against a running verifier before trusting it.** Today you can
rehearse the entire choose→derive→pin→verify loop end-to-end on a dev cluster (it is a
`RUNS` path — §8): the local feed derives an anchor from real bank state
(`LocalValidatorFeed::from_ledger_dir` → `derived_anchor`, `bridge/src/solana_feed.rs:602`,
`:671`), you pin it, and `prove_feed_holding` accepts the honest holding while a mismatched
pin is refused (`bridge/tests/solana_local_e2e.rs:700`–`:739`). This proves your pin
*mechanics* are correct even though the dev-cluster anchor is not a mainnet anchor.

---

## 4. Publishing the anchor (the weak-subjectivity trust root)

The anchor is a public constant. Publish it so that (a) every operator and verifier reads the
**same** tuple, and (b) any third party can run §2 against it.

**Step 4.1 — publish the auditable bundle**, out of band, at a durable, signable location
(the same discipline `docs/ops/PAYMENTS-GO-LIVE.md:49`–`51` uses for the notary verifying
key — publish the trust root out-of-band). The bundle is:

```json
{
  "epoch": 812,
  "stake_table_root": "<hex-64>",
  "boundary_slot": <u64>,
  "boundary_bank_hash": "<base58>",
  "stakes": { "<base58 vote pubkey>": <active_stake_lamports>, ... },
  "sources": ["<snapshot provider A url+hash>", "<provider B>", "explorer", "own full node"],
  "chosen_at": "<ISO-8601>",
  "signed_by": "<operator verifying key / PGP fingerprint>"
}
```

Sign it with the operator's published key. The `stakes` map is what makes it auditable —
**publish the full map, not just the root** (a bare root is unfalsifiable prose; the map is
the falsifier).

**Step 4.2 — record it in the durable deployment config**, not a shell scrap. The anchor is a
governance constant that must survive reboots (`deploy/README.md:83`–`96`). Put the tuple
where the operator services read it (§6), on a backed-up data-dir.

**Step 4.3 — announce the re-pin cadence.** State the weak-subjectivity period you are
assuming and when the next re-pin is due (§9). An anchor that silently ages past its
weak-subjectivity period is the one real long-range risk
(`docs/deos/INTERCHAIN-LIVE-CAMPAIGN.md:330`–`335`).

---

## 5. Third-party audit (how anyone checks the published anchor)

This section is fully **executable today** — it needs only the published bundle (§4) and
public Solana infrastructure.

1. **Recompute the root.** Run §2's `recompute-anchor-root.py` over the published bundle.
   `FAIL` means the tuple does not commit to the published map — reject the anchor outright.
2. **Independently reassemble the map.** Do **not** trust the operator's `stakes` map.
   Rebuild `{vote_pubkey → active_stake}` for `epoch` from an **independent** source — your
   own snapshot of the same epoch, or a second snapshot provider — and recompute the root
   from *your* map. It must equal the published root. This is the anti-collusion check the
   campaign names (`docs/deos/INTERCHAIN-LIVE-CAMPAIGN.md:335`: "derive the anchor tuple from
   two independent snapshots of the same epoch — they must match").
   - **(pending: SnapshotFeed unbuilt — Track A rung 2)** for the *bank-state-faithful*
     reassembly in-repo. Until then an auditor's independent path is another snapshot
     provider's tooling + the §2 formula, with the active-stake-faithfulness caveat (§2).
3. **Confirm the epoch boundary is rooted.** Cross-check `boundary_slot` / `boundary_bank_hash`
   against a block explorer and at least one full node — the epoch must be finalized and
   rooted, not optimistically confirmed.
4. **Confirm the set is recognizable.** Spot-check that the top vote accounts by
   `active_stake` are known, long-lived validators — a weak-subjectivity checkpoint is only
   as good as the social recognition of its set.

Publish your independent recomputation (root + your source) so the audit is a public,
multi-party record, not a private nod.

---

## 6. Pinning the anchor into the running system

The pin API is **real at HEAD**. Two consumers:

**6.1 — the bridge mint path (`MirrorConfig`).** Set the two governance constants
(`bridge/src/solana_mirror.rs:270`, `:274`); the anchored mint refuses any anchor whose
`(epoch, stake_table_root)` does not equal the pinned pair (`check_pinned_anchor`,
`bridge/src/solana_trustless.rs:986`–`:996`, → `LockProofError::AnchorNotPinned`):

```rust
config.pinned_anchor_epoch = Some(anchor.epoch);
config.pinned_anchor_root  = Some(anchor.stake_table_root);
```

**6.2 — the payments watcher (`dregg-pay`).** `SolanaWatcher::with_pinned_anchor`
(`dregg-pay/src/watcher.rs:319`) sets the trust root every `verify_consensus`
(`dregg-pay/src/watcher.rs:343`) checks against; unset ⟹ `HoldingProofError::AnchorNotPinned`
(`dregg-pay/src/watcher.rs:352`).

> **(pending: needs env→watcher wiring)** — `PayConfig::from_env`
> (`dregg-pay/src/config.rs:288`) has **no** anchor field, and `SolanaWatcher::new` /
> `for_asset` initialize `pinned_anchor: None` (`dregg-pay/src/watcher.rs:305`). The only
> caller of `with_pinned_anchor` at HEAD is a `#[cfg(test)]` helper
> (`dregg-pay/src/watcher.rs:585`). So `docs/ops/PAYMENTS-GO-LIVE.md:52`–`58`'s "configure
> the real governance-chosen `(epoch, stake_table_root)`" has an API but **no operator-env
> route yet**: today an operator can only pin it in code that constructs the watcher. Wiring
> two env vars (e.g. `DREGG_PAY_ANCHOR_EPOCH`, `DREGG_PAY_ANCHOR_ROOT`) through
> `PayConfig::from_env` into a `with_pinned_anchor` call at watcher construction is a small,
> real, do-now task — it is not built. Until it is, the payments go-live step 2 dry-run
> cannot be driven from env alone. **The correct fail-closed behavior already holds:** an
> unpinned watcher rejects every holding (`watcher_verify_consensus_without_pinned_anchor_fails_closed`,
> `dregg-pay/src/watcher.rs:655`), so the gap is a liveness/ergonomics gap, not a soundness
> hole.

**6.3 — verify the pin is load-bearing before trusting the deployment.** Confirm both
polarities against the *deployed* config, not a fixture:
- honest anchor + honest holding ⟹ `ConsensusVerified`
  (`watcher_verify_consensus_accepts_honest_anchored_holding`, `dregg-pay/src/watcher.rs:589`);
- attacker 1-key stake table ⟹ rejected (`AnchorRootMismatch`)
  (`watcher_verify_consensus_rejects_attacker_one_key_stake_table`, `dregg-pay/src/watcher.rs:614`);
- no anchor ⟹ `AnchorNotPinned` (`dregg-pay/src/watcher.rs:655`).

---

## 7. Snapshot ingestion — (pending: SnapshotFeed unbuilt — Track A rung 2)

> **⚠ DO NOT EXECUTE against mainnet funds — `SnapshotFeed` is DESIGNED, NOT BUILT.**
> The type does not exist at HEAD; the design is `bridge/src/solana_feed.rs:70`–`:120`. This
> section is the *intended* operator procedure, recorded so it is buildable and reviewable —
> every step is gated on the code landing (Track A rung 2, `docs/deos/INTERCHAIN-LIVE-CAMPAIGN.md:197`).

What a snapshot provides that RPC structurally cannot (`bridge/src/solana_feed.rs:70`–`:97`):
the **bank-hash preimage** (`BankHashComponents`: `parent_bank_hash`, committed accounts
hash, `signature_count`, `last_blockhash` — RPC never returns these,
`bridge/src/solana_feed.rs:76`–`:84`); the **full accounts DB** at the slot, from which the
**real** 16-ary accounts-hash Merkle and a **real** `AccountsInclusionProof16` are extracted
(replacing the reconstruction seam, `bridge/src/solana_feed.rs:85`–`:92`); and the **epoch
stake set + rotation chain** to derive the mainnet `EpochStakeTable` and rotate from the
pinned anchor epoch (`bridge/src/solana_feed.rs:93`–`:97`). Votes are **not** in the
snapshot — they are harvested from a live Geyser/`getBlock` stream
(`bridge/src/solana_feed.rs:99`–`:107`).

**Intended procedure once built** (`SnapshotFeed { archive_path, vote_harvester }` implements
`HoldingFeedSource`, `bridge/src/solana_feed.rs:113`):

1. **(pending)** Obtain an Agave full snapshot `snapshot-<slot>-<hash>.tar.zst` for a slot in
   the target epoch, on a **durable data-dir** (never `mktemp -d` —
   `deploy/README.md:92`–`96`).
2. **(pending)** Point the feed at the archive + the anchor from §4/§6; it unpacks bank fields
   → `BankHashComponents`, walks the accounts DB → real Merkle + inclusion proofs, derives the
   stake table + rotation from the pinned anchor epoch, matches harvested ≥2/3 votes to the
   snapshot bank hash, and assembles the same `HoldingProof` / `SolanaLockProof` the fixtures
   emit (`bridge/src/solana_feed.rs:113`–`:120`). **Nothing downstream changes** — the entry
   stays `prove_holding_consensus_anchored` (`bridge/src/solana_holdings.rs:465`) /
   `verify_lock_proof_consensus_anchored` (`bridge/src/solana_trustless.rs:636`).
3. **(pending)** Run the ingested proof through the **unmodified** production verifier against
   the pinned anchor (§6). A tampered leaf ⟹ `AccountsInclusionInvalid`; a snapshot whose
   derived root ≠ the pinned root ⟹ `AnchorRootMismatch`; a below-2/3 vote set ⟹
   `StakeBelowThreshold` (the rung-2 adversarial gate,
   `docs/deos/INTERCHAIN-LIVE-CAMPAIGN.md:247`–`255`).

**The CI gate that must exist before this is trusted** (the load-bearing faithfulness check,
`docs/deos/INTERCHAIN-LIVE-CAMPAIGN.md:306`–`327`): for one real slot `S`, the snapshot-derived
`BankHashComponents::compute()` **must equal** the `bank_hash` carried in a real TowerSync vote
for `S` harvested from a descendant block. If they differ, the reconstruction is a mirror and
the whole rung is void (the SIMD-215 accounts-hash transition is the concrete way this silently
breaks). Do not ingest mainnet value until this gate is green.

---

## 8. Live-validator ingestion — RUNS today (dev cluster only)

This is the one ingestion path that works at HEAD. It is **dev-cluster-only by construction**
(it must hold the authorized-voter private key, and its endpoint gate refuses non-loopback
plaintext — `bridge/src/solana_feed.rs:418`, `:565`–`:569`) and **must not** be pointed at
mainnet — a real validator set never signs the reconstructed bank hash the local feed builds
(`bridge/src/solana_feed.rs:49`–`:50`).

**8.1 — boot a validator and harvest artifacts** (needs the free Agave toolchain;
`scripts/solana-local-harness.sh:34`–`51` prints the install command if it is missing):

```bash
scripts/solana-local-harness.sh            # boots a free local test-validator, mints a
                                           # stand-in $DREGG, harvests bank-state artifacts
```

**8.2 — run the gated live-feed e2e** (proves choose→derive→pin→verify end-to-end over real
bank state; a no-op clean skip without the env var, `bridge/tests/solana_local_e2e.rs:73`):

```bash
SOLANA_LOCAL=1 cargo test -p dregg-bridge --test solana_local_e2e -- --nocapture
```

This exercises exactly the runbook loop: `LocalValidatorFeed::from_ledger_dir`
(`bridge/src/solana_feed.rs:602`) ingests the holder's account + bank-state accounts over
finalized RPC and derives the anchor (`derived_anchor`, `bridge/src/solana_feed.rs:671`); the
operator pins it once (`bridge/tests/solana_local_e2e.rs:700`–`:704`); the **production**
`prove_feed_holding` (`bridge/src/solana_feed.rs:257`) accepts the honest holding
(`:707`); and a mismatched pin is refused with `AnchorRootMismatch`
(`:721`–`:739`) — the feed cannot self-authorize.

**What stays reconstructed** on this path (so it is not mainnet): the accounts-hash 16-ary
Merkle and the bank-hash preimage (`bridge/src/solana_feed.rs:42`–`:57`,
`single_chunk_proofs` at `:449`). Only §7's snapshot pipeline closes those legs.

---

## 9. Advancing / re-pinning the anchor

The anchor rarely moves — the `RotationStep` chain lets an **old** pin verify **current**-epoch
proofs (`docs/deos/INTERCHAIN-LIVE-CAMPAIGN.md:242`–`245`). It moves only when the
weak-subjectivity period is about to expire.

**When to re-pin:** before the pinned epoch ages past your announced weak-subjectivity period
(§4.3). Track it as an operational parameter, not an ad-hoc reaction.

**How to re-pin:**
1. Repeat §3 (choose) and §5 (audit) for the new epoch, cross-checked against **≥2 independent
   snapshot providers** (`docs/deos/INTERCHAIN-LIVE-CAMPAIGN.md:334`–`335`).
2. Update the pinned tuple in the deployment config (§6) and re-publish the bundle (§4).

**(pending: needs rung 0 — one verified ballot front door)** — the *governed* re-pin, where the
anchor tuple is the subject of a `CollectiveChoice` poll decided by existing `$DREGG` holders
(`docs/deos/INTERCHAIN-LIVE-CAMPAIGN.md:232`–`241`), is self-hosting on the same governance
engine this whole track feeds — **but only after rung 0 repoints the cross-chain join off the
demoted `HostBallotBox` shim** so there is exactly one verified ballot front door
(`docs/deos/INTERCHAIN-LIVE-CAMPAIGN.md:129`–`162`). Until rung 0 lands, re-pinning is an
operator action recorded in config + the published bundle (§4/§6), **not** a poll outcome.

---

## 10. Quick reference — what runs vs what is pending

**Executable today:**
- Recompute + audit a published anchor root (§2, §5) — pure, no dregg code.
- Pin the anchor into `MirrorConfig` (§6.1) and, in code, into `SolanaWatcher` (§6.2).
- Verify both polarities of the pin (§6.3) — real tests at HEAD.
- Rehearse the whole choose→derive→pin→verify loop on a dev cluster (§3.4, §8) — `SOLANA_LOCAL=1`.
- Fail-closed with no anchor (`AnchorNotPinned`) — real at HEAD.

**Pending (labeled at each step):**
- Bank-state-faithful *mainnet* anchor derivation in-repo — needs `SnapshotFeed` (§3.2, §5.2).
- Snapshot ingestion of holdings/locks (§7) — `SnapshotFeed` unbuilt (Track A rung 2), plus its
  CI faithfulness gate (§7 last paragraph).
- `PayConfig::from_env` → `SolanaWatcher::with_pinned_anchor` env wiring (§6.2) — small do-now task.
- Governed re-pin via a `CollectiveChoice` poll (§9) — needs rung 0.

**Do NOT execute:** §7 against mainnet funds (SnapshotFeed unbuilt); pointing `LocalValidatorFeed`
at mainnet (§8 — dev-cluster-only by construction); any anchor derived only from `getVoteAccounts`
as a deployment pin (§3.2 — bootstrapping cross-check only).
