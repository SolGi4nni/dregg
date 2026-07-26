# fhEgg SDK readiness — current developer contract

*Rewritten 2026-07-22 at `6d0e024f19`. This answers “what can another
developer safely integrate now?” See `HANDOFF-FHEGG-FEASIBILITY-CODEX.md` for
the cryptographic ledger and `THE-DARK-BAZAAR.md` for the game/product cut.*

## 0. Verdict

| Consumer | Readiness | Meaning |
|---|---|---|
| Plaintext Rust application | **YES, EXPERIMENTAL** | `dregg_sdk::fhegg` exposes versioned uniform-price clearing and independent settlement verification. |
| Dregg-hosted private game deployment | **YES, CONTROLLED / CONFIGURED** | The catalog can mount one policy-pinned private Bazaar with shared web/Telegram/Discord surfaces, private worker custody, durable target worlds, and viewer-blind publication. This is an internal deployment contract, not a permissionless general SDK. |
| External production-private fhEgg application | **NOT YET** | No stable public API gives arbitrary applications the complete house-blind, malicious/PQ, committee-finalized shared-witness apex. |

The codebase contains much more cryptography than the stable SDK exposes.
Internal proof constructors, environment wiring, and test fixtures are not
automatically supported APIs.

## 1. Plaintext clearing surface

With the `fhegg` SDK feature:

- `clear_book(&WireBook) -> Settlement`;
- `clear_book_json(&str) -> String`;
- `verify_settlement(&Settlement, &WireBook)`; and
- versioned `WireBook`, `WireOrder`, `WireSide`, `TickGrid`, and settlement
  types

are callable today.

The surface is strict and deterministic. Unknown fields, wrong versions,
invalid grids/books, and forged settlements refuse. It does not provide FHE,
zero knowledge, no-viewer custody, or consensus finality. Do not market the
plaintext SDK as the Dark Bazaar.

## 2. Controlled hosted-private surface

The deployment entry point is
`dreggnet_catalog::private_bazaar_live::PrivateBazaarLiveDeployment`. It owns:

- validated immutable raid policy;
- exact offering and live-session registry;
- private commitment store;
- exactly-once consequence adapter;
- authority directory;
- authenticated finalized-receipt source;
- supervised worker runtime; and
- durable target registry/character store.

The ordinary catalog does not fabricate a roster, executor, reward, reserve,
signing seed, authority directory, or target world. Partial configuration
refuses.

### 2.1 Deployment identity

The current configuration contract includes:

- `DREGG_PRIVATE_BAZAAR_DEPLOYMENT_ID`
- `DREGG_PRIVATE_BAZAAR_ROSTER`
- `DREGG_PRIVATE_BAZAAR_ROSTER_COMMITMENT`
- `DREGG_PRIVATE_BAZAAR_REWARD_KIND`
- `DREGG_PRIVATE_BAZAAR_REWARD_AMOUNT`
- `DREGG_PRIVATE_BAZAAR_REWARD_COMMITMENT`
- `DREGG_PRIVATE_BAZAAR_REWARD_METHOD`
- `DREGG_PRIVATE_BAZAAR_REWARD_EVENT_TOPIC`
- `DREGG_PRIVATE_BAZAAR_EXECUTOR_PUBKEY`
- `DREGG_PRIVATE_BAZAAR_EXECUTOR_FEDERATION`
- `DREGG_PRIVATE_BAZAAR_EXECUTOR_SIGNING_SEED_FILE`
- `DREGG_PRIVATE_BAZAAR_RESERVE`
- `DREGG_PRIVATE_BAZAAR_AUTHORITY_DIR`

Worker poll/backoff knobs are separately bounded. The signing seed is a private
file; runtime custody and permissions are validated.

### 2.2 Frontend contract

All surfaces use the shared game spine:

- authority-bound `GameSessionRef`;
- stable host incarnation;
- durable close/reopen generation;
- advertised pre-head;
- signed action plus authority signature; and
- one viewer-blind publication grammar.

Web, Telegram, and Discord must not receive the raw clearing receipt, winner,
blind, private input digest, witness, proof diagnostics, executor-local
envelope, or private worker journal. Rich direct receipts belong only in the
explicitly private audience/custody path.

### 2.3 Consequence contract

A hosted private mechanic produces a typed semantic result for the private
worker. It must not call the Dungeon store directly from a frontend.

The worker polls an authenticated finalized source, rebinds the exact market
and policy, persists intent before dispatch, recovers using the target receipt,
commits the cursor only after exact application, and publishes only the
viewer-safe projection. Target worlds must be program/cell/custody pinned,
signed, checkpoint continuous, and shared with the playable offering.

## 3. Real internal substrates that are not stable SDK promises

- exact FNSP-v3 construction/acceptance and FRC1/CTM1 transport;
- private dependent turns;
- FWS1 whole-note swap proof;
- Dark-AMM/private-book HidingFRI relations;
- threshold-BFV DKG/relin/decrypt-share proofs;
- FHTRI004/FHTRI005 preprocessing and custody;
- q0 carrier/LogUp and fused-terminal work;
- TFHE/BFV WGPU engines; and
- direct-logic/collaborative-proving research backends.

These interfaces are intentionally strict, feature-gated, deployment-owned, or
fail-closed. Stabilizing a wrapper around an unfinished authority boundary
would turn research seams into compatibility debt.

## 4. Security grades a future SDK must expose

Every request/result type should state:

- visibility: public, committed, verifier-hiding, or no-single-viewer;
- witness producer: one process, threshold custodians, or collaborative prover;
- relation/version/VK identity;
- key/roster/federation epoch;
- leakage manifest;
- durability/finality level;
- PQ profile and classical dependencies;
- CPU/optional-WGPU/required-WGPU backend; and
- fallback policy.

“Private” without those coordinates is not an SDK grade.

## 5. Current refusal boundaries

Refuse rather than downgrade when:

- shielded v4 lacks live verifier/selector/persistence;
- a q0 terminal lacks full same-opening authority;
- FHTRI005 has no production cross-term provider;
- roster/key/market/deployment epoch mismatches;
- a game action lacks exact generation/head authority;
- a target lacks checkpoint/custody/program identity;
- a populated legacy fields store has not crossed v11;
- required WGPU is unavailable or returns a non-GPU backend;
- proof carrier, descriptor, public statement, or canonical codec drifts; or
- a public surface requests a private receipt.

## 6. What a production external SDK still needs

1. Full shared-witness FXC4/v4.
2. Persistent v4 state/output notes and committee finality.
3. Malicious/PQ dealerless cross-term generation and authenticated q0
   same-opening.
4. Collaborative witness/proof production.
5. Stable typed request/result/receipt codecs derived from canonical objects,
   never raw JSON source bytes.
6. Capability-scoped remote authentication and rate/replay policy.
7. Deployment migration plus key/roster rotation.
8. Rust conformance followed by Python/TypeScript bindings.

Bindings should follow the stable authority boundary, not precede it.

## 7. Recipe for a new private game mechanic

1. Author the rule/leakage in Lean or name a refinement.
2. Emit and pin one canonical typed descriptor/VK identity.
3. Define a worker-private result with no frontend accessors.
4. Bind it to the shared game epoch and exact finalized receipt.
5. Implement one deterministic restart-safe world operation.
6. Publish a viewer-blind card through the common grammar.
7. Test substitution, replay, old generation, cross-market, crash after
   dispatch, duplicate consequence, private rendering, and wrong custody.
8. Run the narrow gate under the real Lean/PQ/GPU policy.

Do not fork Telegram, Discord, and web semantics. Do not add a host-side
`if proof.verify()` bypass around ordinary finality or the private worker.

## 8. Verification

Use narrow `cargo nextest` targets:

```sh
cargo nextest run -p dregg-sdk -E 'test(/fhegg/)'
cargo nextest run -p dreggnet-catalog -E 'test(/private_bazaar|game_spine/)'
cargo nextest run -p dreggnet-web -E 'test(/game_epoch|private_bazaar|act_signed/)'
```

Proof-heavy, exact-v3, and WGPU tests run explicitly in release on
persvati/hbox. Lean goes wherever the Dregg2 oleans already are — the laptop or
hbox's `eth-lc-air` lane, **not** unconditionally local; see
`docs/BUILD-BUDGET.md` for current routing, how to read a `pbuild` `VERDICT`, and
what `ENVFAULT` means. Also `.config/nextest.toml`.

## 9. Plain-language answer

You can build against fhEgg’s plaintext clearing SDK now. You can deploy the
current private Bazaar inside the controlled Dregg host now, preserving its
exact grades. You cannot yet offer arbitrary external developers a stable API
that truthfully promises fully house-blind, dealerless, malicious/PQ,
committee-finalized private computation. The remaining work is concentrated at
named composition seams rather than missing foundations.
