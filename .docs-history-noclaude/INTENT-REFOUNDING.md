# Intent Re-Founding

The intent layer's money edge runs through the verified executor. This document is the
census verdict for the rest of the crate: what is live, what is scaffold, which concepts
get re-founded on the Lean trunk, and what gets deleted. All references are present-tense
file:line into `intent/src/` unless noted.

## 1. The verified fulfillment edge (wired)

A fulfilled intent IS a verified, conserving, authorized executor step:

- `node/src/api.rs` `/intents/fulfill` (`post_fulfill_intent`) and the MCP fulfill tool
  (`node/src/mcp.rs`) call `dregg_intent::fulfillment::execute_fulfillment_flow_verified`.
- `sdk/src/cipherclerk.rs` `fulfill_and_collect` calls the same entry.
- `execute_fulfillment_flow_verified` (`fulfillment.rs`) verifies the fulfillment, then
  settles the payment leg through `verified_settle::settle_ring_verified`
  (`verified_settle.rs:311`) — the verified per-asset transition `recKExecAsset`. With the
  `verified-settle` feature (on in the node: `node/Cargo.toml:32`), every leg is settled by
  the REAL Lean export `@[export] dregg_record_kernel_step` (`verified_settle.rs:512`) and
  cross-checked fail-closed (`verified_settle.rs:527`). The realisation theorem is
  `RingFFI.ffi_export_realises_settleRing_leg`
  (`metatheory/Dregg2/Intent/RingFFI.lean:139`), axiom-checked.
- Fail-closed, no fallback: a payment the verified gate refuses (underfunded payer,
  payer == recipient, a cell missing from the ledger, an FFI divergence) returns
  `FulfillmentError::VerifiedRefusal` and the ledger is untouched. The legacy
  `dregg_turn::TurnExecutor` does not run on this path.
- Feature scope: `dregg-sdk` builds `dregg-intent` without `verified-settle`
  (`sdk/Cargo.toml:39`), so a standalone SDK build settles through the in-process verified
  transition — the exact transition `ffi_export_realises_settleRing_leg` proves the export
  realises — without the live FFI cross-check. In the node binary, cargo feature
  unification turns the cross-check on for every edge.
- The same verified fold already settles the batch engine's output
  (`trustless.rs:1640` `finalize_verified`) and the sealed-auction app
  (`starbridge-apps/sealed-auction/src/lib.rs:44`).

Non-money fulfillment steps (token/STARK verification, predicate proofs, receipt
construction) are unchanged; the receipt binds the same canonical payment turn
(`create_fulfillment_turn`, `fulfillment.rs:762`) plus the real pre-/post-state Merkle
roots around the verified write-back.

## 2. The four-ontology diagnosis

The crate carries FOUR disjoint notions of "intent", none of which carries the Lean
escrow + deadline faces (`metatheory/Dregg2/Intent/Core.lean` — the four-faced intent;
`Kernel.lean` — escrow-funded settle, `no_double_fulfill`):

| Ontology | Where | What it is |
|---|---|---|
| `MatchSpec` | `lib.rs:364` | capability-pattern matching (actions/resource/predicates/`min_budget`) — the one the live fulfillment edge uses |
| `ExchangeSpec` | `solver.rs:24` | offered/wanted asset pairs for ring trades |
| `GeneralizedExchange` / `GeneralizedIntentGraph` | `generalized.rs:81,232` | n-ary "anything for anything" graph |
| `Intent` (lowering) | `lowering.rs:40` | the lowering tower's enum (`RingSettlement` …) |

No escrow cell funds a `MatchSpec` intent; no deadline face gates a `GeneralizedExchange`.
Each ontology re-derives matching, settlement, and validity in its own vocabulary.

## 3. The liveness map

Of ~11.9K non-test lines, production reaches ≈3.3K. The live edges:

- `fulfillment.rs` — the verified payment flow (§1) + fulfillment creation/verification.
- `matcher.rs` — local matching. Its "Datalog evaluation" (`matcher.rs:4`) is enum-equality
  and string pattern checks; the word is prose, not an engine.
- `verified_settle.rs` — the verified edge (whole file load-bearing).
- `trustless.rs` INTAKE ONLY: the node exposes `submit_encrypted`
  (`node/src/api.rs:4203`), `contribute_decrypt_share` (`api.rs:4222`), and status
  (`api.rs:4237`). `close_batch` (`trustless.rs:1090`), `submit_solution` (`:1255`),
  `challenge` (`:1448`), `finalize` (`:1522`), `finalize_verified` (`:1640`) are called by
  nothing outside tests — the batch lifecycle never advances in production.
- `delay_pool` is a zombie field: constructed at `node/src/state.rs:761,865`, stored at
  `state.rs:311`, read by nothing.
- Dead or test-only: `generalized.rs` (1.2K), `lowering.rs` beyond the trustless tests,
  `cross_fed.rs`, `gossip_filter.rs`, `agent_mandate.rs`, `bond.rs`, `partial_fill.rs`,
  `state_machine.rs`, `exchange.rs` (20-line stub).

## 4. The trustless-layer reality table

`trustless.rs` claims a 7-layer fair-ordering protocol (header `trustless.rs:3`):

| Layer | Where | Reality |
|---|---|---|
| 1 SUBMIT | `trustless.rs:1047` | real Shamir-over-GF(256) + ChaCha20-Poly1305 math (`dregg_federation::threshold_decrypt`), but the key is dealer-generated — a trusted dealer, 1-of-1 in the running devnet shape |
| 2 BATCH | `:1081` | scaffold — `close_batch` unreached in production |
| 3 DECRYPT | `:1104` | shares are accepted via the API, but no ceremony completes (layer 2 never closes) |
| 4+5 SOLVE+PROVE | `:1242` | scaffold — `submit_solution` unreached; "validity proof" is a hash carried, not a checked circuit |
| 6 SELECT | `:1439` | scaffold — `challenge` unreached |
| 7 SETTLE | `:1503,1640` | VERIFIED (`finalize_verified` folds through the Lean-realised executor) but unreachable behind layers 2–6 — now WIRED for the live fulfillment edge by §1 |

## 5. The re-founding map

Each concept worth keeping has a home on the Lean trunk; the Rust sprawl is the lossy copy.

| Concept | Today | Re-founded as |
|---|---|---|
| sealed bids | `commit_reveal_fulfillment.rs` hash dance | `PreimageGate` — proved in `Dregg2/Intent/SealedAuction.lean` (`reveal_binds_committed`), running in `starbridge-apps/sealed-auction` |
| windows / expiry | ad-hoc height checks per module | temporal atoms (deadline face of the four-faced intent) |
| pools / orderbooks | `delay_pool.rs`, `generalized.rs` graphs | heap collections over cells |
| threshold decryption | dealer-trusted Shamir (layer 1) | `D_G` modality (group-knowledge dial) |
| solver bonds | `bond.rs:99` `BondEscrow` (in-crate map, no cell) | evidence-slashing turns over REAL escrow cells |
| mandates | `agent_mandate.rs` | already superseded by `Dregg2/Agent/Mandate.lean` |
| fulfillment-pays | `min_budget` scalar transfer | escrow-face cell-program: the intent FUNDS an escrow cell at creation; fulfillment consumes it (`Kernel.lean` `no_double_fulfill`) |

## 6. Genuine residue needing homes

Real machinery that is neither intent-shaped nor deletable:

- **PIR private discovery** (`pir.rs`, 1.8K) + **SSE search** (`sse.rs`, 1.1K): a
  discovery-privacy lane — how an agent finds an intent without revealing what it seeks.
  Not settlement; deserves its own lane.
- **Stake-proof anti-spam** (`lib.rs:240` `StakeProof`, `gossip.rs` epoch-scoped
  nullifiers): a gossip ADMISSION policy, not an intent concept — belongs in the gossip
  layer's admission rule beside the F-4 strand-admission gate.
- **Solver-market scoring** (`solver.rs` ring scores, `generalized.rs:407`
  `GeneralizedSolver`): meaningless without a checked validity circuit for "this solution
  is welfare-maximal" — either a real circuit or an explicit decision to drop the market
  and keep first-valid-settles.

## 7. The staged shrink

1. **Rewire** (done, §1): the live money edge settles verified; nothing falls back.
2. **Delete**: `matcher`'s dead generality, `generalized.rs`, `lowering.rs` (after
   re-homing `finalize_verified`'s leg extraction, which reads `SealedTurn`),
   `cross_fed.rs`, `gossip_filter.rs`, `agent_mandate.rs`, `delay_pool.rs` (+ the zombie
   field `node/src/state.rs:311`), `bond.rs`, trustless layers 2–6.
3. **Keep**: `verified_settle.rs` whole; the conservation-decision differential tests
   (`tests/ring_settlement_differential.rs`, `tests/fulfillment_verified_turn.rs`,
   `tests/fulfillment_ffi_verified.rs`); the layer-7 verified settle re-homed as the ONLY
   settlement entry; `pir`/`sse`/stake-proof per §6.
4. **Re-found**: one intent ontology with the escrow + deadline faces, lowered from
   `Dregg2/Intent/Core.lean`, settling exclusively through the verified edge.
