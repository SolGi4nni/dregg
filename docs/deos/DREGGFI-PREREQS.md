# dreggfi / DrEX / OCIP — the PRE-REQ build-map

*A prioritized, dependency-aware build-map to the deployed, replyable state ember wants:
a live dregg devnet + testnet settlement contracts you can point at a tx + the DrEX/OCIP
roadmap. Ground-truthed against real code at HEAD (2026-07-16);
every current-state claim carries a `file:line`. This is the dispatch surface — a swarm can
be launched from any row without re-discovering the ground truth.*

Companion to `DREGGFI-VISION.md` (the graded product vision) and `DREGGFI-AMBITION.md` (the
factcheck + the bold arc). Roadmap history: `GOAL-MULTICHAIN-SETTLEMENT.md` + `HORIZONLOG.md`.

## How to read this

- **Size** is effort, not difficulty: **reachable-weld** (hours → ~2 days, mechanism exists,
  wire it) · **days** (real build, no new science) · **multi-month** (design problem / new
  crypto / cross-layer flag-day).
- **Gate**: **BUILD** (dispatch now, no permission needed) · **EMBER** (outward decision —
  deploy timing, MPC, mainnet, upstreaming) · **SIBLING** (needs coordination with the
  stark-kill / vk-epoch / turn-layer terminals).
- **State**: `WORKS` (real + tested) · `STUB` (present, fail-closed / synthetic) · `MISSING`
  (plan-only, greenfield).

---

## 0. THE CRITICAL PATH — the ordered spine to "point at a testnet tx" + a replyable claim

The shortest ordered chain of pre-reqs to a deployed, replyable state. Each step's blocker is
the step above it.

1. **[DONE] The settlement deploy path exists and is broadcast.**
   `chain/script/DeploySettlement.s.sol` deploys the 3-step sequence (verifier →
   `Groth16Verifier25Adapter` → `DreggSettlement`); siblings `DeployLaunchpad.s.sol` +
   `DeployUpgradeableSettlement.s.sol` cover the launchpad and upgradeable stacks.
   `chain/broadcast/DeploySettlement.s.sol/84532/run-latest.json` records a receipted 4-tx
   Base-Sepolia (chain id 84532) run — Verifier → adapter → `DreggSettlement`. This is the
   **"point at a testnet tx"** outbound artifact. `foundry.toml` carries `base_sepolia` +
   `robinhood_testnet` under `[rpc_endpoints]`. Standing residual (1.1): before any
   re-broadcast, confirm the shipped verifier `.sol`/`.vk` and the
   `settlement_groth16.json` fixture key to the same proof run.
2. **[BUILD · reachable-weld] Stand up a devnet the claim settles from.**
   Single-node is near-trivial and real (`cargo build -p dregg-node`; `init`; `run
   --enable-faucet`, `DEV-NODE-RUNBOOK.md:14-36`). For a federated devnet, the n=3 homelab
   lifecycle scripts exist (`HOMELAB-N3-RUNBOOK.md`; an n=4 homelab run is recorded in
   `GOAL-FEDERATION.md:25`). A *revive* is EMBER-gated (the VK-epoch flip is her eyes-open
   decision) and blocked on a not-yet-cut Lean seed (`lean-seed.pin` TAG empty,
   `HOMELAB-N3-RUNBOOK.md:241-245`).
3. **[BUILD · already done — verify + surface] The inbound replyable claim already runs.**
   `cargo run --example cross_chain_vote` (`dregg-interchain-gov/examples/cross_chain_vote.rs`)
   drives the production verifiers end-to-end (Solana anchored consensus + EVM EIP-1186 + Cosmos
   bank, the binding trilogy, the Lean weight verdict). Honest edge: the *complete* 3-chain vote
   runs over fixture/round-trip data; the live-mainnet-proven path stops at the non-custodial
   `UnboundOwner` tooth (no wallet key) — `DREGGFI-AMBITION.md` #14.

**After the critical path**, the roadmap forks into the four value tracks below (DrEX, the moat,
OCIP, the welds), none of which block the deploy — they deepen what the deployed system *does*.

**ember-gated vs pure-build on the critical path:** steps 2-build and 3 are pure BUILD and
dispatchable now. The devnet *revive/re-genesis* is EMBER (the eyes-open VK-epoch flip); the
Base-Sepolia broadcast — the one EMBER touch on this spine — is done. Production MPC is a
separate EMBER gate that only bites *mainnet*, never testnet.

---

## Track 1 — DEPLOY (toward "point at a testnet tx")

| # | Pre-req | Unblocks | State (cited) | Size | Deps | Gate |
|---|---|---|---|---|---|---|
| 1.1 | Coherent settlement fixture (verifier `.sol`/`.vk` + `settlement_groth16.json` keyed to one run) | trustworthy re-deploy artifact | standing pre-redeploy check — diff fixture vs shipped verifier before any re-broadcast (drift last audited 2026-07-13) | reachable-weld | — | BUILD |
| 1.2 | `DeploySettlement.s.sol` | any settlement deploy | WORKS: `chain/script/DeploySettlement.s.sol` (verifier → `Groth16Verifier25Adapter` → `DreggSettlement`); siblings `DeployLaunchpad.s.sol`, `DeployUpgradeableSettlement.s.sol` | done | — | — |
| 1.3 | Base-Sepolia broadcast | the outbound testnet tx | DONE: `chain/broadcast/DeploySettlement.s.sol/84532/run-latest.json` — receipted 4-tx run (Verifier → adapter → `DreggSettlement`); `base_sepolia` + `robinhood_testnet` in `foundry.toml` | done | 1.2 | — |
| 1.4 | Settlement contract itself | the on-chain twin | WORKS in-test: real pairing check, 25 canonical BabyBear lanes, genesis pinned at ctor, fail-closed; `DreggSettlement.sol` (238 ln); Foundry RealProof **7/7** | done | — | — |
| 1.5 | Generated 25-PI verifier @ 4.98M | the real VK on-chain | WORKS + CURRENT: `DreggGroth16Verifier25.sol` gen by `settlement_snark_test.go:170`, VK baked (PUB_0..24), committed `.vk` @ `151ba219e`; 4.98M (−61%), prove 17.7s | done | — | — |
| 1.6 | Single-node devnet | a chain to settle from | WORKS: `DEV-NODE-RUNBOOK.md:14-36`; `node/src/genesis.rs`; `dregg-node init/run` | reachable-weld | — | BUILD |
| 1.7 | Federated devnet revive (n=3/n=4) | multi-validator finality demo | scripts exist (`HOMELAB-N3-RUNBOOK.md`); n=4 live (`GOAL-FEDERATION.md:25`); **blocked on** Lean seed not cut (`lean-seed.pin` empty) + VK-epoch flip | days | 1.6, seed-cut | EMBER + SIBLING |
| 1.8 | outboundMessageRoot proof-binding (26th PI) | trustless cross-chain *messaging* (Hyperlane/LZ) | STUB: fail-closed, `DreggSettlement.sol:32-61,178-180`; needs apex to expose a per-turn msg commitment → new lanes → new Groth16 VK | multi-month | turn/apex layer | SIBLING |
| 1.9 | RecursionVk anchor de-decoration | a non-circular on-chain VK anchor | decorative today (hex-validated only, HORIZONLOG ~8035); governance-pinned constant + assert | days | — | BUILD |
| 1.10 | Production MPC ceremony | mainnet (not testnet) | MISSING: single-party dev ceremony (`settlement_snark_test.go:7-9`); R1CS-content-hash cache skips re-setup (`groth16_cache.go:19-25`); **zero** ptau/coordinator/phase tooling | multi-month | — | EMBER |

**Track-1 headline:** the settlement rail is *built, Foundry-verified, and broadcast to
Base-Sepolia* — the outbound testnet tx exists (1.3). The open Track-1 items are the devnet
(1.6/1.7), the messaging root (1.8), the VK-anchor de-decoration (1.9), and the mainnet-only
MPC ceremony (1.10). Note: "five-validator C3" in the memory is a **mis-remember** — no such
federation exists; "C3" is a cutover milestone / a Poseidon2 chain-hash, unrelated
(`HORIZONLOG.md:4809`, `REGEX-AUTOMATON-EVAL.md:99`).

---

## Track 2 — DrEX (the Dragon's EXchange)

| # | Pre-req | Unblocks | State (cited) | Size | Deps | Gate |
|---|---|---|---|---|---|---|
| 2.1 | Rung-1 execution soundness + fairness | the matching engine as theorems | WORKS (proved, `#assert_all_clean`): `Market/Clearing.lean` + `Market/Fairness.lean:112` (`clearing_respects_limits`, both-side IR + teeth) | done | — | — |
| 2.2 | Rung-2 order-book aggregation soundness | no-drop/insert/reorder faithful book | **WORKS — further than vision credited:** `Market/Aggregation.lean` (`aggregate_sound`, `no_drop`/`no_insert`, `aggregated_clearing_conserves_submissions`), reuses `ChainBound` shape | done | 2.1 | — |
| 2.3 | Priced/continuous substrate (lift `DemoRes`) | uniform-price + partial fills | MISSING: rungs 1-2 are over `DemoRes` — discrete 2-asset exact-book, no prices/partial-fills (`DREGGFI-AMBITION.md` #5); `Clearing.lean` structure is category-general | days→multi-month | 2.1 | BUILD |
| 2.4 | Uniform-price optimality theorem | "one clearing price for a 2-sided batch" | MISSING (named `Clearing.lean:37-54`, `Fairness.lean:39-47`) | days | 2.3 | BUILD |
| 2.5 | Envy-free / Shapley–Scarf TTC-core stability | provable no-coalition-improves | MISSING (named; today's IR is strictly weaker than core) | multi-month | 2.3 | BUILD |
| 2.6 | Ledger realization (`MarketClearing` → `settleRing`) | clearing induces a committed conserving turn | partially there: `Ring.lean` keystones proven; the induction `MarketClearing`→`RingBalanced settleRing` named `Clearing.lean:42-44`, `Fairness.lean:43-45` | days | 2.1 | BUILD |
| 2.7 | Live matcher wiring (order-book → matcher → executor) | a RUNNABLE DrEX demo | matcher WORKS (`intent/src/solver.rs` Johnson+TTC); ring routes through **real Lean FFI** (`intent/src/verified_settle.rs`, `DREGGFI-AMBITION.md` #13) — "light it up" as live conserving settlement | days | 2.2, 2.6 | BUILD |
| 2.8 | **Rung-3: ring-over-shielded-notes** (the marquee weld) | private matching; deletes the DECRYPT committee | MISSING: shielded pool is standalone, "**not woven into effect_vm**" (`shielded/mod.rs:43-48`); the `trustless.rs` DECRYPT committee still present (`DREGGFI-AMBITION.md` #10) | multi-month | 2.7, 3.x fold | BUILD |
| 2.9 | Private-matching custom ZKP | "cleared correctly over hidden orders" | MISSING (rung-3 (b), the epoch weld) | multi-month | 2.8 | BUILD |

**Critical path to a RUNNABLE DrEX demo:** 2.6 (ledger realization) + 2.7 (light up the FFI
matcher) over the **clear** book gives a runnable, proof-carrying, conserving multilateral
exchange — *days*, mostly wiring existing pieces (matcher + `verified_settle.rs` FFI + rungs
1-2 already proved). Privacy (2.8/2.9) is the multi-month marquee that comes after. **Quick-win
discovery:** rung-2 (`Aggregation.lean`) is already PROVED — the vision doc lists it as "to
build."

---

## Track 3 — THE MOAT ("everything is a leaf" — recursive structured products)

| # | Pre-req | Unblocks | State (cited) | Size | Deps | Gate |
|---|---|---|---|---|---|---|
| 3.1 | The leaf-fold fabric | fold N sub-proofs → one apex | **WORKS end-to-end (passing):** `aggregate_tree` 2-to-1 tree, N unbounded, depth ⌈log2 N⌉ (`joint_turn_recursive.rs:354`); `circuit-prove/tests/mpt_holding_fold_pilot.rs:326` + `circuit-prove/tests/apex_shrink_bn254_tooth.rs:97` | done | — | — |
| 3.2 | The leaf-adapter pattern | how to write a new leaf | WORKS: a free-function convention (no trait), 6-fn surface producing `RecursionOutput<DreggRecursionConfig>` — `_to_descriptor2` + `prove_X_leaf_with_claim` (`prove_descriptor_leaf_with_pi_slice_expose`) + `prove_X_binding_node_segmented` + `X_CLAIM_LEN`; ref `note_spend_leaf_adapter.rs:298,521,543,768` | done | — | — |
| 3.3 | **First financial leaf: shielded note-spend** | a spend proof as a foldable leaf | **LARGELY DONE:** `note_spend_leaf_adapter.rs` exists AND folds — standalone tooth (`circuit-prove/tests/note_spend_binding_node_tooth.rs`) + deployed Bridge-carrier arm (`ivc_turn_chain.rs:3170-3207`, PI-46 pinned). Re-proves the real `dregg-note-spending-dsl-v3` STARK | reachable-weld | 3.1,3.2 | BUILD |
| 3.4 | Exercise note-spend leaf on a live turn | the first financial leaf, live | needs a `BridgeWitnessBundle` carrying a note_spend witness + a PI-46-pinned descriptor to reach the deployed arm | reachable-weld | 3.3 | BUILD |
| 3.5 | **Solvency leaf** (reserve ≥ Σ liabilities) | solvency-as-a-proof, foldable | **WORKS:** `circuit-prove/src/solvency_leaf_adapter.rs` — `prove_solvency_leaf{,_with_claim}` proves `R ≥ L` via a 30-bit range gadget + two committed openings as a foldable IR-v2 leaf; composes with the ∀-schedule `stripe_reserve_solvent_forever` by CITATION (the leaf proves a state IS solvent, the Lean theorem proves it STAYS solvent — it does not re-prove the ∀-schedule in-AIR) | done | — | — |
| 3.6 | Weave shielded pool into the fabric | shielded-clearing leaf (= DrEX 2.8) | MISSING: `shielded/` has no `_leaf_adapter`/`expose_claim`/`aggregate_tree` call (`shielded/mod.rs:43-48`) | multi-month | 3.1 | BUILD |
| 3.7 | First structured product apex | {solvency ⊕ holdings ⊕ clearing} folded, verified once | **partial:** `prove_structured_product_fold` (`solvency_leaf_adapter.rs:440`) folds {note-spend ⊕ solvency} into one claim-union apex, itself reusable as a leaf (`prove_claim_union_fold`); clearing-as-leaf still MISSING (= 3.6/2.8) | days→multi-month | 3.6 | BUILD |

**The moat's current footing:** both financial leaves exist and fold — note-spend (3.3) and
solvency (3.5) — and `prove_structured_product_fold` already unions them into one apex that
verifies both. Exercising the note-spend leaf on a live turn (3.4) is a reachable-weld; the open
leg of the moat demonstrator (3.7) is the clearing leaf, which is the same weld as DrEX 2.8 (3.6).

---

## Track 4 — OCIP (attested-data + money-paths + screener + attention market)

| # | Pre-req | Unblocks | State (cited) | Size | Deps | Gate |
|---|---|---|---|---|---|---|
| 4.1 | Nitro TEE attestation | ATTESTED lane (AWS enclaves) | WORKS: real COSE_Sign1 + pinned AWS root (fingerprint verified) + ES384, real fixture `tee-verify/tests/nitro_real.rs`; `tee-verify/src/lib.rs:155-256` | done | — | — |
| 4.2 | SNP TEE (AMD SEV-SNP) | ATTESTED lane (AMD enclaves) | **WORKS, root-anchored:** real parse + ECDSA-P384 body verify + `VCEK ← ASK ← ARK` chain over the **real embedded AMD roots** per product (Milan/Genoa/Turin, from the AMD KDS — `SnpVerifier::new_with_amd_roots`, `snp.rs:293`); ARK/ASK RSA-4096-PSS verified via the `rsa` crate (`snp_chain.rs`); `new()` stays fail-closed. Residual: no live EPYC-captured report-body fixture (positive report-path tests drive a local `rcgen` PKI) | reachable-weld (the fixture) | — | BUILD |
| 4.3 | Wire TEE-fact verifier into a live path | attested data actually flows | STUB: real+tested but only tests call `install_tee_fact_verifier`; `run_hosted_agent_attested` uses zkoracle not TEE (`tee_fact.rs:107-208`, `host.rs:389-408`) | reachable-weld | — | BUILD |
| 4.4 | Money-path conservation proofs | splitter/fee-router soundness | WORKS (PROVED, Lean, 0 `sorry`): `settleRing_conserves` (`Ring.lean:118`), exactly-once escrow (`Lifecycle.lean:294,311`, axiom-audited). **No OCIP-named** splitter module — general primitives back it | done (primitive) | — | — |
| 4.5 | zkoracle price producer (price-as-witness) | attested market data / the oracle leg | WORKS fixture-backed: `zkoracle-prove/src/endpoints/price.rs` `AttestedPrice` over Coinbase; live behind `tlsn-live`; `zkoracle_leaf_adapter.rs` folds it. Real-endpoint+notary step named-not-built (`ZKORACLE-PROVER-STATUS.md`) | days | — | BUILD |
| 4.6 | Screener / data pipeline / REPLAYABLE ranking | the near-term OCIP product | MISSING: plan-only, `ocip-plan-v3.pdf` off-repo; no code (grep-empty) | multi-month | — | BUILD (greenfield) |
| 4.7 | Bonded attention market | the fair-attention product | MISSING as described (plan-only). A real bond+slash primitive exists for **relay operators** (conserving `restitution+remainder==seized`, `node/src/relay_dispute.rs`, `slash_treasury_mirror.rs`) — not an attention/promotion market | multi-month | 4.4 | BUILD (greenfield) |

**Track-4 headline:** the *attested/oracle* leg (4.1/4.2/4.5) is real — both hardware roots are
pinned (the once-open x509-parser/RSA-4096-PSS question is answered by the `rsa`-crate chain
verify in `snp_chain.rs`); the near-term OCIP *product* (screener + attention market) is genuine
greenfield.

---

## Track 5 — THE WELDS (the recurring "force it in-circuit at settlement" shape)

| # | Weld | Unblocks | State (cited) | Size | Deps | Gate |
|---|---|---|---|---|---|---|
| 5.1 | **Caveat-in-circuit** (per-trade mandate admission) | "the mandate IS the proof" venue-verified | **partial — the decidable-atom slice WORKS:** `circuit-prove/src/caveat_admission_leaf_adapter.rs` reifies `validUntil`/`heightLt`/`budget` + asset scope in-circuit (range-checked limbwise borrow-subtraction; Lean model `Dregg2/Circuit/CaveatBignumCompare.lean` `borrowSub_iff`, sorry-free). The `opaque`/`thirdParty` atoms stay executor-trusted (`Caveat.lean:59`), and the deployed trade descriptor must still dual-expose `(trade fields ++ caveat params)` to bind the leaf — the named VK-regen piece. NB the delegation/budget/revocation half is PROVED + materialized (`Agent/Mandate.lean:194,227,301`, `DREGGFI-AMBITION.md` #12) | days→multi-month | — | BUILD |
| 5.2 | **Price-as-proof-carrying-witness** (oracle weld) | solvency/lending unconditional on an exogenous mark | further-than-expected: `zkoracle-prove` produces+verifies attested prices, `zkoracle_leaf_adapter.rs` folds them (= 4.5). Weld = bind the attested price as a circuit witness into the solvency/market claim | days | 4.5, 3.5 | BUILD |
| 5.3 | **Shielded-pool-into-effect_vm** | shielded clearing + shielded solvency | MISSING: the standing `shielded/mod.rs:43-48` seam (= DrEX 2.8 = moat 3.6) | multi-month | 3.1 | BUILD |

**The four welds of the vision, mapped to rows:** capability→5.1 · shielded-markets→5.3/2.8 ·
soundness/oracle→5.2 · cross-chain→production MPC (1.10). Three of four are pure BUILD; only the
MPC weld is EMBER-gated.

---

## THE TOP 5 TO SWARM NEXT

Ranked by (unblocks-the-replyable-state × groundedness × small). Each is dispatchable now with
the cites above.

1. **Light up the live DrEX matcher over the clear book (2.6 + 2.7).** *days.* Unblocks a
   RUNNABLE DrEX demo. Rungs 1-2 are proved, the matcher (`solver.rs`) is real, and the ring
   already routes through the Lean FFI (`verified_settle.rs`) — this composes existing pieces
   into a demonstrable conserving proof-carrying exchange. No new science.
2. **Exercise the note-spend financial leaf on a live turn (3.4).** *reachable-weld.* Both
   financial leaves exist and `prove_structured_product_fold` already unions {note-spend ⊕
   solvency}; driving the note-spend leaf on a live turn is the moat's next foothold, and the
   clearing leaf (3.6/2.8) is its open leg.
3. **Wire the TEE-fact verifier into a live path + capture a live EPYC fixture (4.3 + the 4.2
   residual).** *reachable-weld.* Makes attested data actually flow. Both hardware roots are
   pinned real; the seams (`install_tee_fact_verifier`) already exist — what remains is the
   hermes wiring and a genuine SEV-SNP report captured from EPYC hardware.
4. **Bind the attested price as a circuit witness (5.2, on top of 4.5).** *days.* Unblocks the
   oracle weld — turns solvency/market theorems from "conditional on an exogenous mark" into
   proof-carrying. The producer (`zkoracle-prove` price endpoint) + the fold adapter
   (`zkoracle_leaf_adapter.rs`) already exist; the weld is binding the witness into the claim.
5. **Dual-expose the trade descriptor to bind the caveat-admission leaf (the 5.1 residual).**
   *days, VK-regen.* The decidable-atom leaf exists (`caveat_admission_leaf_adapter.rs`); binding
   it to the deployed trade descriptor's `(trade fields ++ caveat params)` limbs turns "the
   mandate IS the proof" venue-verified for the decidable vocabulary.

---

## QUICK WINS (smaller than expected)

- **DrEX rung-2 is already PROVED** (`Market/Aggregation.lean`) — the vision lists it as "to
  build." Free rung.
- **Both financial leaves exist and fold** — note-spend (`note_spend_leaf_adapter.rs` + the
  deployed Bridge arm `ivc_turn_chain.rs:3170`) and solvency (`solvency_leaf_adapter.rs`) — and
  `prove_structured_product_fold` already unions them into one apex. The moat demonstrator needs
  only the clearing leaf plus a live drive.
- **The oracle/price-as-witness leg has a runnable producer already** (`zkoracle-prove` +
  `zkoracle_leaf_adapter.rs`) — further along than the vision's "the deepest weld" framing.
- **The SNP residual is just a fixture capture** — the roots and the RSA-4096-PSS chain verify
  are real (`snp_chain.rs`); a genuine EPYC report closes the lane.
- **Single-node devnet stand-up is documented and real** — no revive needed for a local demo.

## HIDDEN BLOCKERS (bigger / riskier than they look)

- **outboundMessageRoot proof-binding (1.8)** is a full apex→shrink→gnark **VK-regen flag-day**
  across the turn layer (SIBLING territory), not an incremental contract fix — cross-chain
  *messaging* (as opposed to *settlement*) is gated on it.
- **Devnet revive (1.7)** is double-gated: EMBER (eyes-open VK-epoch flip) **and** a not-yet-cut
  Lean seed (`lean-seed.pin` empty). A local single-node devnet sidesteps both.
- **The priced substrate (2.3)** — uniform-price/envy-free (2.4/2.5) can't be built until
  `DemoRes` is lifted off discrete-exact-book to prices/partial-fills; that lift, not the
  theorems, is the real work.
- **Fixture coherence (1.1)** — a re-deploy could ship a verifier keyed to a different proof run
  than the fixture. Diff `settlement_groth16.json` against the shipped verifier `.sol`/`.vk`
  before any re-broadcast.

## EMBER-GATED vs PURE-BUILD (the honest split)

- **EMBER (outward — do not dispatch a swarm to decide):** the federated-devnet revive /
  re-genesis + the VK-epoch flip (1.7); the **production MPC ceremony** (1.10) — mainnet only,
  never testnet; upstreaming the alloy-trie finding. (The Base-Sepolia broadcast, 1.3, is done.)
- **SIBLING (coordinate, don't clobber):** outboundMessageRoot 26th-PI (1.8, turn/apex layer);
  the seed cut (1.7).
- **PURE BUILD (dispatch now):** everything else — single-node devnet (1.6), all of DrEX rungs
  2.3-2.9, the open moat/leaf items (3.4, 3.6, 3.7), the OCIP fixture + live wiring + screener +
  attention market (4.2-residual, 4.3, 4.5-4.7), and welds 5.1-5.3. The overwhelming majority of
  the roadmap is dispatchable without an ember decision.

## See also

`DREGGFI-VISION.md` · `DREGGFI-AMBITION.md` (the factcheck — #5 rung state, #12 mandate, #13
FFI ring, #14 cross-chain honest edge) · `INTERCHAIN-MODEL.md` · `GOAL-MULTICHAIN-SETTLEMENT.md`
+ `HORIZONLOG.md` (the wrap, done) · `DEV-NODE-RUNBOOK.md` / `HOMELAB-N3-RUNBOOK.md` (devnet) ·
`chain/DEPLOY.md` (stale — Vault+Gate only) · `metatheory/Market/{Clearing,Fairness,Aggregation}.lean` ·
`circuit-prove/src/{note_spend,custom,zkoracle}_leaf_adapter.rs` · `circuit-prove/src/shielded/{mod,pool,attest}.rs` ·
`tee-verify/src/{lib,snp}.rs` · `zkoracle-prove/src/endpoints/price.rs`.
