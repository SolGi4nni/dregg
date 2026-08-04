# PoA F-4 live cutover

Status: **boundary implemented; live cutover deliberately not claimed**.

`node/src/poa_strand_admission.rs` now provides the independently sound part of the Path of Angels
admission path:

- an absent-by-default and explicitly staged/enforced PoA policy;
- the fixed `N = 2` rooted transitive-vouch rule;
- no bond row, bond carrier, or bond ingestion API;
- a generic F-4 vouch signature plus a second signature binding the edge to
  `pathofangels.network/federation/v1`, the exact federation id, and a monotonic voucher-local
  sequence;
- atomic redb snapshot replacement attributed to finalized source block ids;
- authenticated restart replay, idempotent crash replay, and refusal of source conflicts,
  non-monotonic replay, wrong-domain/federation rows, and corrupt storage; and
- enforced projection through the linked Lean `dregg_strand_admit` export, with no Rust fallback.

The module has no production caller yet. This is intentional, not an omitted final line.

## Why a poll-time splice is unsafe

The current constitution has one participant set. Once a Join proposal passes, that set immediately
drives more than the late `poll_finalized_blocks` participant projection:

- block-production supermajority;
- constitutional voting threshold;
- finalization-vote collector membership and threshold;
- PQ roster and gossip committee changes; and
- the final tau participant projection.

If only the final tau projection switches to PoA admission, an approved candidate with fewer than
two rooted vouches is filtered at the end but already raises the producer and voting quorums at the
beginning. A candidate the policy correctly rejects could therefore halt the old admitted committee.
That would be a liveness regression disguised as a Sybil fix.

## Exact remaining splice

1. **Give vouches a typed consensus carrier.** Add a versioned
   `Payload::PoaAdmissionVouchV1` (preferred over making all generic `Data` actionable). Its bytes
   are the canonical `PoaVouchRowV1`. Include it in both solo and multi-party finalized ordering and
   in the verified-finality actionable set.

2. **Split candidates from the active roster.** Preserve constitution-ratified candidates, but
   derive a distinct active consensus roster from the persisted genesis seeds, finalized vouch rows,
   and the Lean projection. Block production, tau, finalization votes, membership-vote thresholds,
   PQ enrollment, and committee-gated peer discovery must all consume the same active roster.

3. **Change rosters only at a deterministic boundary.** A newly satisfied candidate becomes active
   at the next committed wave/epoch boundary, never midway through a wave. Every node must derive
   the same `(candidate set, vouch snapshot, activation boundary)` from the same finalized prefix.

4. **Make vouch durability part of finalized execution.** Add a `FinalizedBlock::PoaVouch` arm.
   Validate and call `persist_finalized_vouch` before acknowledging its cursor identity. A storage
   failure is retryable and stops the tau prefix. Invalid authenticated content is a deterministic
   rejection with durable evidence; it does not mutate the registry.

5. **Repair restart authority for the new non-turn carrier.** Today persisted non-turn executed ids
   are trusted as replay hints. A PoA vouch id may be retained only when its source id exists in the
   authenticated admission snapshot. Otherwise drop it from the recovered cursor and replay the
   finalized row. This closes crash-between-block-persist-and-row-persist.

6. **Commit the candidate's PQ key.** The present Join action carries only Ed25519. Extend the
   versioned Join carrier (or add a separate authenticated roster-key statement) so an admitted
   candidate's ML-DSA key is consensus state before activation. Continue to halt rather than project
   a node-local PQ key.

7. **Put policy in genesis and re-check it at boot.** Add a genesis object equivalent to:

   ```json
   {
     "kind": "poa-rooted-vouch-v1",
     "deployment_domain": "pathofangels.network/federation/v1",
     "threshold": 2,
     "bond_admission": false,
     "seeds": ["<genesis validator Ed25519 keys>"]
   }
   ```

   Initial boot persists the exact policy. Restart must compare genesis, runtime federation id, and
   durable policy byte-for-byte before serving. Remove the generic
   `DREGG_STRAND_ADMISSION_GATE=0` bypass from this PoA role; a missing Lean export is a startup
   refusal.

8. **Flip readiness only after an end-to-end hostile test.** The test must finalize two distinct
   rooted vouches, activate one candidate at a boundary, restart every validator, and show the same
   active roster and tau order. Its twins must cover one vouch, a three-node rootless ring, wrong
   deployment domain, wrong federation, duplicate sequence in a different block, source-id/body
   conflict, missing durable row after cursor persistence, unavailable Lean, and a candidate without
   a committed PQ key.

Until all eight land together, keep:

```text
f4_transitive_vouch_rows_live = false
objective_vouch_admission_ready = false
```

## Focused boundary verification

```sh
cargo nextest run -p dregg-node -E 'test(poa_strand_admission)'
```

These tests prove the isolated durability/authentication/Lean-projection boundary. They do not prove
that the running committee consumes it.
