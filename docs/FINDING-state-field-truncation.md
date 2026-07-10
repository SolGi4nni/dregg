# FINDING: a cell's 32-byte state fields are truncated to a u64 when a turn touches it

Observed 2026-07-10 on a 3-node F1 devnet (blocklace consensus, ML-DSA enrolled,
`dregg-node` at the commit that added the exec-lease Granted producer).

## The symptom

`starbridge-apps/execution-lease` pins the rent beneficiary into the lease
cell's `PROVIDER_SLOT` (heap slot 6) as a **full 32-byte cell id**
(`cell_tag(terms.provider)` — `f.copy_from_slice(cell.as_bytes())`). Immediately
after `open_lease` + `insert_cell`, `GET /api/cell/<lease>` reads it back intact:

```
slot 6: 934e47f222216976ecabcd76f8be42ed459e23b12e988ab7ad7a7da327d68064
```

After ONE committed turn touches that cell — here a
`GrantCapability { from: operator, to: lease, cap: { target: lease, slot: 0 } }`,
which mutates only the lease's c-list — the same slot reads back **truncated to
its low 8 bytes**, re-encoded big-endian in bytes `[24..32]`:

```
slot 6: 000000000000000000000000000000000000000000000000ad7a7da327d68064
                                                        ^^^^^^^^^^^^^^^^ the id's last 8 bytes
```

`GET /api/cell/0000…ad7a7da327d68064` → `found: false`. The lease's recorded
provider is now a cell id that does not exist, so a metered settlement Transfer
to it is refused and the whole lease→provider payment rail silently stops.

## Why it is unambiguous

Only the node that *executed* the turn is affected. On the same federation, the
same lease cell, at the same moment:

| node | executed the grant turn | `fields[6]` |
|---|---|---|
| F1-node-1 | yes | `0000…ad7a7da327d68064` (truncated) |
| F1-node-2 | not yet | `934e47f2…d68064` (intact) |
| F1-node-3 | not yet | `934e47f2…d68064` (intact) |

So the corruption is introduced by turn execution / commit writeback, not by the
seed, not by serialization, and not by consensus replication. Two replicas
disagree with the third about committed cell state.

## Scope

Any state field holding a full 32-byte value survives only until the first turn
touches its cell. That covers every cell-id tag, digest, or commitment pinned
into `fields[..]` — `cell_tag` is the obvious one, but the pattern is general.
`set_field` itself stores the value verbatim (`cell/src/state.rs:877`), and the
grant effect performs no `SetField`, so the truncation happens in the commit
writeback path, downstream of the effect application. The `field_from_u64`
big-endian-tail encoding of the surviving bytes points at a u64-lane round-trip
(the record-layer `fields_map` / effect-VM limb representation are the natural
suspects).

## Reproduction

```sh
# 3-node F1 devnet, ML-DSA-enrolled genesis, DREGG_SEED_DEMO_LEASE=1
LEASE=<the seeded lease cell id>
curl -s localhost:7811/api/cell/$LEASE | jq -r '.fields[6]'   # full 32-byte provider id
# operator grants a capability whose `to` is the lease cell
curl -s -X POST localhost:7811/api/turns/submit -H "Authorization: Bearer $BEARER" \
  -d "{\"agent\":\"$OP\",\"nonce\":$N,\"fee\":1000,\"actions\":[{\"effects\":[
       {\"kind\":\"grant_capability\",\"to\":\"$LEASE\",\"target\":\"$LEASE\",\"slot\":0}]}]}"
# once it finalizes:
curl -s localhost:7811/api/cell/$LEASE | jq -r '.fields[6]'   # low 8 bytes only
curl -s localhost:7812/api/cell/$LEASE | jq -r '.fields[6]'   # still intact — node-2 hasn't executed it
```

## Consequence for the operated layer

`DreggNet`'s provider reads the lease's `PROVIDER_SLOT` to decide who the
metered rent is paid to. It now validates that the slot names an existing cell
and falls back to the node's operator cell (which is node-local, so the
settlement is not federation-replicable). Restoring a federation-wide rent
beneficiary depends on this being fixed.

## The residual — scholar verdict 2026-07-10: DON'T widen the wire

The acute fix (skip fields the turn did not move) covers the operated need: a
32-byte id pinned at seed time SURVIVES an unrelated turn. The residual is only a
turn that genuinely `SetField`s a slot to a NEW full-width value — which nothing in
the operated trace does.

A scholar study established the load-bearing fact: a cell-state `fields[]` slot is
**definitionally a u64 lane** in this model — the kernel encodes it via
`field_from_u64` (bytes[24..32]), the Lean `setField` effect value is `Int`
(`metatheory/Dregg2/Exec/Effect.lean:98`), and every capacity gate evaluates over
that lane. The Lean *Value* model CAN hold 32 bytes (`Value.dig : Nat`, unbounded,
and the wire grammar `{"dig":"<64hex>"}` carries all 256 bits) — but the SetField
lane is scalar end-to-end, so closing the residual means widening the verified
kernel's `setField` (weeks, HIGH risk) — and it is **soundness-moot** anyway until
the v13 faithful-fields epoch retires the `Faithful8::from_lossy_31bit_DANGER`
fields[0..7] folds (`circuit/src/faithful8.rs:42`); today even Rust's committed
fields root is a ~31-bit Horner fold.

**Verdict:** the acute fix is the right stopping point. Close the residual by
relocating 32-byte identities OUT of raw scalar slots — a full cell id belongs in a
`Ty.digest`-typed field / committed digest side-table (`field_limbs8`-encoded,
`circuit/src/effect_vm/helpers.rs:122`), not `PROVIDER_SLOT`. That is the real
design correction, and any true wire+kernel widening should be sequenced WITH the
v13 epoch, not ahead of it.
