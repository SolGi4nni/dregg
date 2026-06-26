# COMMIT-BINDS-MMR — closing the trust anchor on attested queries

`dregg-query` answers carry a **non-omission certificate**: a range opening of
the receipt log against an MMR root, re-derived by the verifier so the server is
trusted for nothing but availability (`docs/EPISTEMIC-DATALOG.md` Q2,
`dregg-query/src/attested.rs`). There is exactly **one** residual trust in that
story: the root the certificate opens against is supplied to
`AttestedAnswer::verify(&hasher, &trusted_root)` as a **parameter**, and today
that root is obtained out-of-band — an operator channel, or TOFU-pinned and
watched. This document is the precise design for removing that last gap: pinning
the receipt-log root **by the IVC aggregate** so a light client *derives* the
trusted root from the one thing it already verifies, instead of being told it.

It is a **design**, written in present tense. The Lean obligation it discharges
is already proven and axiom-clean; one of the two deployment steps is
VK-affecting and is deliberately deferred to the gated rotation epoch.

---

## 1. What is already proven (the model side)

`metatheory/Dregg2/Lightclient/MMR.lean` §6 carries the obligation verbatim from
the sorted-map face (`AttestedQuery.lean`'s `CommitBindsIndex`), specialized to
the append-only receipt MMR with `iroot := mroot`:

- **`CommitBindsMMR hash limbs commit L`** — the per-turn folded state
  commitment is a sponge that absorbs the receipt-log MMR root as its **last
  limb**:

  ```
  commit = hash (limbs ++ [mroot hash L])
  ```

  `limbs` is everything else the commitment already absorbs (cells root,
  registers, map roots, turn context).

- **`commit_pins_mmr`** (`#assert_axioms`-clean) — two openings of the *same*
  commitment expose the *same* receipt log. CR peels the sponge, the root limb
  is last regardless of the other limbs' shape, and `mroot_injective` pins the
  leaves.

- **`light_client_position_non_omission`** (`#assert_axioms`-clean) — a light
  client holding **only** the aggregation root, given a sound recursion engine
  and the single check `verify agg.root = true`, plus the weld
  (`CommitBindsMMR` at every step), concludes for **any** step, **any**
  server-supplied opening, and **any** verifying range answer: the whole chain
  is attested, the answer is **exactly** the genuine range, and every committed
  in-range position is present at its dense slot. The server cannot skip a
  position anywhere in history.

So the *math* is done. What remains is making the deployed artifacts instantiate
the two hypotheses `CommitBindsMMR` quantifies over: the hash, and the limb.

---

## 2. The two deployment gaps

### Gap A — the hash floor (non-VK, caller-side)

`dregg-query`'s `Blake3Mmr` (`src/mmr.rs`) is blake3 with arity-separated domain
tags (`dregg-query-mmr-v1:{empty,leaf,node,bag}`) standing in for the model's
`Poseidon2SpongeCR` slot. The in-circuit commitment uses the field-sponge
Poseidon2 over the BabyBear/KoalaBear limbs the rest of the protocol commits
with. For the receipt-log root that a light client *derives from the aggregate*
to be byte-comparable to the root `dregg-query` opens against, the crate needs a
**`Poseidon2Mmr`** hasher: the same forest/bagging structure (`Mmr<H>` is
already generic over `MmrHasher`), but `hash_leaf` / `hash_node` / `hash_bag`
implemented as the field sponge with the arities separated exactly as the model
does (by sponge position) rather than by string tag.

This is a **caller-side change only**. `AttestedSlice::verify` and
`AttestedAnswer::verify` already take the hasher as a type parameter `H:
MmrHasher` and the root as a value; swapping `Blake3Mmr` for `Poseidon2Mmr` at
the call site changes neither the certificate shape nor the wire format. The two
hashers can coexist (blake3 for the operator-trusted interim, Poseidon2 once the
aggregate pins it). The leaf identity is preserved: leaf `i` is the 32-byte
`TurnReceipt::receipt_hash()` of chain entry `i`, re-expressed as field limbs.

**Owed:** a `Poseidon2Mmr` impl + a differential test that `Blake3Mmr` and
`Poseidon2Mmr` agree on *structure* (skip / substitute / reorder all reject
under both) even though their roots differ — the false-witness suite of
`tests/synthetic.rs`, re-run under the field hasher.

### Gap B — the limb weld (VK-affecting, deferred to the rotation)

The per-turn commitment that `TurnChainBindingAir` pins as `new_root[i]` (the
model's `recStateCommit` = `HistoryAggregation.stateRoot`) must **absorb
`mroot` as its last sponge limb**. Concretely: extend the EPOCH commitment
layout so the receipt-index root is the final absorbed element, exactly as
`CommitBindsMMR` requires (`commit = hash (limbs ++ [mroot hash L])`). This
changes the AIR's absorbed-input vector and therefore the **verification key** —
it is the one genuinely flag-day step, gated to the VK rotation epoch
(`project-umem-as-primitive-epoch`, HORIZONLOG). It is *not* on the critical
path for the rest of dregg-query: the crate already verifies against whatever
root it is handed.

The layout choice "root **last**" is load-bearing and already reflected in the
proof: `commit_pins_mmr` peels the sponge with `List.getLast?_concat`, so the
root limb's position is what makes it match "regardless of the other limbs'
shape". The deployed sponge must place it last to discharge by construction.

---

## 3. The discharge: how the root stops being operator-trusted

With both gaps closed, the light-client flow becomes:

1. The client holds the **aggregation root** and runs the **one** check it
   already runs: `verify(agg.root) = true` (`light_client_verifies_whole_history`).
2. For a queried step, the server supplies an opening of that step's attested
   commitment. By Gap B, that commitment absorbed `mroot` as its last limb; by
   `commit_pins_mmr`, the opening can only expose the **genuine** receipt log
   `L = logOf step`.
3. The client now has a root it did **not** receive out-of-band: it is the
   `mroot` *forced* by the aggregate it just verified. It hands **that** root to
   `AttestedAnswer::verify` as `trusted_root`.
4. `light_client_position_non_omission` then gives exactness and dense
   completeness for any verifying range answer over that step.

The `trusted_root` parameter survives unchanged — but its *provenance* moves
from "operator told me" to "the IVC aggregate forces it." That is the whole
close: the crate's verifier was always written to take the root as a parameter
*specifically so this swap is a caller-side change* (`src/client.rs`, the trust
anchor note).

---

## 4. Invariants the rotation must preserve

- **Dense positions.** Leaf `i` is chain entry `i`; the certificate binds
  `chain_index == lo + slot` before the MMR runs (`attested.rs`
  `AttestedError::DenseIndex`). Position is part of the commitment
  (`mmr_root_moves_on_any_log_change`); the field hasher must keep this.
- **`mroot_injective`.** Tamper / truncate / extend / reorder each move the
  root. The Poseidon2 forest must bag with the same anti-ghost shape
  (`BadFrontier` on non-mountains, count check against the root-pinned length).
- **Leaf = `receipt_hash`.** The MMR leaf is the canonical
  `dregg-receipt-v3` digest; the rotation re-expresses it as field limbs, it
  does not recompute receipts.
- **Coverage semantics.** `Coverage::WholeLog` still requires the certified
  range to reach `[0, len-1]` of the *root-pinned* length; with the root now
  pinned by the aggregate, `len` is itself aggregate-pinned, so "provably
  omitted nothing" over the whole log becomes a statement anchored to verified
  history rather than to a trusted root.

---

## 5. Staging

- **Now (non-VK):** land `Poseidon2Mmr` behind the existing `MmrHasher` trait +
  the differential false-witness suite. Caller-side; no wire/VK change. The
  served `/api/receipts/index/root` can offer both roots during the interim.
- **The rotation (VK-affecting, gated):** absorb `mroot` as the last limb of the
  EPOCH commitment; commit the welded VK; flip the deployed default. At that
  point `CommitBindsMMR` discharges by construction and
  `light_client_position_non_omission` anchors every certificate over the whole
  history from the single aggregate check.

Reference: `metatheory/Dregg2/Lightclient/MMR.lean` §6
(`CommitBindsMMR`, `commit_pins_mmr`, `light_client_position_non_omission`),
`Dregg2/Lightclient/AttestedQuery.lean` §ROOT (`server_cannot_omit`,
`CommitBindsIndex`), `dregg-query/src/{mmr,attested,client}.rs`.
