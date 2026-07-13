# dreggfi / DrEX / OCIP — the PRE-REQ build-map

*A prioritized, dependency-aware build-map to the deployed, replyable state ember wants:
a live dregg devnet + testnet settlement contracts you can point at a tx + the DrEX/OCIP
roadmap. Ground-truthed against real code at HEAD (2026-07-13, branch `mldsa-sign-route`);
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

1. **[BUILD · reachable-weld] Re-mint + commit a coherent settlement fixture.** The
   `chain/test/fixtures/settlement_groth16.json` is uncommitted-modified in the working tree
   (` M` in git status) while the verifier `.sol`/`.vk` are committed at `151ba219e`. Diff it,
   regen if stale, commit alongside — so the shipped verifier and the deploy calldata key to
   the same run. *Blocks: a trustworthy deploy artifact.*
2. **[BUILD · reachable-weld] Write `DeploySettlement.s.sol`.** No deploy script exists for the
   settlement stack — `chain/script/Deploy.s.sol:33-40` deploys only legacy `DreggVault` +
   `DreggCredentialGate` against a mock. The 3-step sequence (deploy `DreggGroth16Verifier25`
   no-args → `Groth16Verifier25Adapter(verifier)` → `DreggSettlement(adapter, vkHash,
   genesisRoot)`) already exists verbatim in test setup at
   `chain/test/DreggSettlementRealProof.t.sol:76-83`; the script is that minus the fixture
   parse. Add L1-Sepolia to `[rpc_endpoints]` (only `base_sepolia` today, `foundry.toml`).
   *Blocks: any on-chain deploy.*
3. **[EMBER · reachable-weld] Broadcast to Base-Sepolia.** `forge script … --broadcast
   --verify`. Needs a funded deployer key + the genesis-anchor `uint32[8]` chosen for the
   devnet instance. Never been broadcast (no `chain/broadcast/`). This is the **"point at a
   testnet tx"** deliverable: a real Groth16 dregg-settlement proof lands on Base-Sepolia,
   forgeries reject. *This is the replyable outbound artifact.*
4. **[BUILD, parallel to 1-3 · reachable-weld] Stand up a devnet the claim settles from.**
   Single-node is near-trivial and real (`cargo build -p dregg-node`; `init`; `run
   --enable-faucet`, `DEV-NODE-RUNBOOK.md:14-36`). For a federated devnet, the n=3 homelab
   lifecycle scripts exist (`HOMELAB-N3-RUNBOOK.md`) and ember's n=4 is live
   (`GOAL-FEDERATION.md:25`). A *revive* is EMBER-gated (the VK-epoch flip is her eyes-open
   decision) and blocked on a not-yet-cut Lean seed (`lean-seed.pin` TAG empty,
   `HOMELAB-N3-RUNBOOK.md:241-245`).
5. **[BUILD · already done — verify + surface] The inbound replyable claim already runs.**
   `cargo run --example cross_chain_vote` (`dregg-interchain-gov/examples/cross_chain_vote.rs`)
   drives the production verifiers end-to-end (Solana anchored consensus + EVM EIP-1186 + Cosmos
   bank, the binding trilogy, the Lean weight verdict). Honest edge: the *complete* 3-chain vote
   runs over fixture/round-trip data; the live-mainnet-proven path stops at the non-custodial
   `UnboundOwner` tooth (no wallet key) — `DREGGFI-AMBITION.md` #14.

**After the critical path**, the roadmap forks into the four value tracks below (DrEX, the moat,
OCIP, the welds), none of which block the deploy — they deepen what the deployed system *does*.

**ember-gated vs pure-build on the critical path:** steps 1, 2, 4-build, 5 are pure BUILD and
dispatchable now. Step 3 (broadcast) and the devnet *revive/re-genesis* are EMBER (a funded key
+ the eyes-open VK-epoch flip). Production MPC is a separate EMBER gate that only bites *mainnet*,
never testnet.

---

## Track 1 — DEPLOY (toward "point at a testnet tx")

| # | Pre-req | Unblocks | State (cited) | Size | Deps | Gate |
|---|---|---|---|---|---|---|
| 1.1 | Coherent settlement fixture (re-mint + commit) | trustworthy deploy artifact | `settlement_groth16.json` uncommitted-modified vs verifier committed @ `151ba219e` (git status) | reachable-weld | — | BUILD |
| 1.2 | `DeploySettlement.s.sol` | any settlement deploy | only `Deploy.s.sol:33-40` (Vault+Gate, mock); settlement stack has NO deploy path; sequence exists @ `DreggSettlementRealProof.t.sol:76-83` | reachable-weld | 1.1 | BUILD |
| 1.3 | Base-Sepolia broadcast + BaseScan verify | the outbound testnet tx | never broadcast (no `chain/broadcast/`); `base_sepolia` RPC + etherscan already in `foundry.toml` | reachable-weld | 1.2 | EMBER (key+anchor) |
| 1.4 | Settlement contract itself | the on-chain twin | WORKS in-test: real pairing check, 25 canonical BabyBear lanes, genesis pinned at ctor, fail-closed; `DreggSettlement.sol` (238 ln); Foundry RealProof **7/7** | done | — | — |
| 1.5 | Generated 25-PI verifier @ 4.98M | the real VK on-chain | WORKS + CURRENT: `DreggGroth16Verifier25.sol` gen by `settlement_snark_test.go:170`, VK baked (PUB_0..24), committed `.vk` @ `151ba219e`; 4.98M (−61%), prove 17.7s | done | — | — |
| 1.6 | Single-node devnet | a chain to settle from | WORKS: `DEV-NODE-RUNBOOK.md:14-36`; `node/src/genesis.rs`; `dregg-node init/run` | reachable-weld | — | BUILD |
| 1.7 | Federated devnet revive (n=3/n=4) | multi-validator finality demo | scripts exist (`HOMELAB-N3-RUNBOOK.md`); n=4 live (`GOAL-FEDERATION.md:25`); **blocked on** Lean seed not cut (`lean-seed.pin` empty) + VK-epoch flip | days | 1.6, seed-cut | EMBER + SIBLING |
| 1.8 | outboundMessageRoot proof-binding (26th PI) | trustless cross-chain *messaging* (Hyperlane/LZ) | STUB: fail-closed, `DreggSettlement.sol:32-61,178-180`; needs apex to expose a per-turn msg commitment → new lanes → new Groth16 VK | multi-month | turn/apex layer | SIBLING |
| 1.9 | RecursionVk anchor de-decoration | a non-circular on-chain VK anchor | decorative today (hex-validated only, HORIZONLOG ~8035); governance-pinned constant + assert | days | — | BUILD |
| 1.10 | Production MPC ceremony | mainnet (not testnet) | MISSING: single-party dev ceremony (`settlement_snark_test.go:7-9`); R1CS-content-hash cache skips re-setup (`groth16_cache.go:19-25`); **zero** ptau/coordinator/phase tooling | multi-month | — | EMBER |

**Track-1 headline:** the settlement rail is *built and verified on-chain in Foundry* — the gap
to a live testnet tx is almost entirely **plumbing** (a fixture commit + a ~20-line deploy
script + a funded broadcast), not circuit work. Note: "five-validator C3" in the memory is a
**mis-remember** — no such federation exists; "C3" is a cutover milestone / a Poseidon2 chain-hash,
unrelated (`HORIZONLOG.md:4809`, `REGEX-AUTOMATON-EVAL.md:99`).

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
| 3.1 | The leaf-fold fabric | fold N sub-proofs → one apex | **WORKS end-to-end (passing):** `aggregate_tree` 2-to-1 tree, N unbounded, depth ⌈log2 N⌉ (`joint_turn_recursive.rs:354`); `tests/mpt_holding_fold_pilot.rs:326` + `tests/apex_shrink_bn254_tooth.rs:97` | done | — | — |
| 3.2 | The leaf-adapter pattern | how to write a new leaf | WORKS: a free-function convention (no trait), 6-fn surface producing `RecursionOutput<DreggRecursionConfig>` — `_to_descriptor2` + `prove_X_leaf_with_claim` (`prove_descriptor_leaf_with_pi_slice_expose`) + `prove_X_binding_node_segmented` + `X_CLAIM_LEN`; ref `note_spend_leaf_adapter.rs:298,521,543,768` | done | — | — |
| 3.3 | **First financial leaf: shielded note-spend** | a spend proof as a foldable leaf | **LARGELY DONE:** `note_spend_leaf_adapter.rs` exists AND folds — standalone tooth (`tests/note_spend_binding_node_tooth.rs`) + deployed Bridge-carrier arm (`ivc_turn_chain.rs:3170-3207`, PI-46 pinned). Re-proves the real `dregg-note-spending-dsl-v3` STARK | reachable-weld | 3.1,3.2 | BUILD |
| 3.4 | Exercise note-spend leaf on a live turn | the first financial leaf, live | needs a `BridgeWitnessBundle` carrying a note_spend witness + a PI-46-pinned descriptor to reach the deployed arm | reachable-weld | 3.3 | BUILD |
| 3.5 | **Solvency leaf** (reserve ≥ Σ liabilities) | solvency-as-a-proof, foldable | partial primitive: `shielded/attest.rs:101-107` `Positive`/`Threshold{1}` = "prove-solvent", 30-bit range decomp (`attest.rs:240-259`), emits the same `CircuitDescriptor` the custom adapter lowers. **MISSING:** an *aggregate* `reserve − Σliab ≥ 0` circuit (grep-empty); StripeReserve is Lean-only (`StripeReserve.lean:48,58`, no AIR) | days | 3.1,3.2 | BUILD |
| 3.6 | Weave shielded pool into the fabric | shielded-clearing leaf (= DrEX 2.8) | MISSING: `shielded/` has no `_leaf_adapter`/`expose_claim`/`aggregate_tree` call (`shielded/mod.rs:43-48`) | multi-month | 3.1 | BUILD |
| 3.7 | First structured product apex | {solvency ⊕ holdings ⊕ clearing} folded, verified once | MISSING (the moat demonstrator) — mechanism proven (3.1), financial leaves are the build | days→multi-month | 3.3,3.5 | BUILD |

**Smallest path to a first financial leaf:** it's **already mostly built.** The note-spend leaf
(3.3) exists and folds today — exercising it live (3.4) is a reachable-weld. For solvency (3.5),
the shortest route **reuses the `attest` 30-bit range gadget + `attest_descriptor`'s
`CircuitDescriptor`** and rides the *existing* custom carrier (`custom_leaf_adapter.rs`,
already-deployed for MPT) — so a solvency leaf needs **no new `CarrierWitness` variant**: build
the `reserve − Σliab ≥ 0` `CircuitDescriptor`, wrap as a `CellProgram`, fold via the custom
binding node.

---

## Track 4 — OCIP (attested-data + money-paths + screener + attention market)

| # | Pre-req | Unblocks | State (cited) | Size | Deps | Gate |
|---|---|---|---|---|---|---|
| 4.1 | Nitro TEE attestation | ATTESTED lane (AWS enclaves) | WORKS: real COSE_Sign1 + pinned AWS root (fingerprint verified) + ES384, real fixture `tests/nitro_real.rs`; `tee-verify/src/lib.rs:155-256` | done | — | — |
| 4.2 | SNP TEE (AMD SEV-SNP) | ATTESTED lane (AMD enclaves) | STUB one-rung-short: real parse+ECDSA-P384+chain code, but **no pinned AMD roots** (`snp.rs:330-335`), no real fixture (forged rcgen PKI). KDS URL coded (`snp.rs:261`) | reachable-weld* | — | BUILD |
| 4.3 | Wire TEE-fact verifier into a live path | attested data actually flows | STUB: real+tested but only tests call `install_tee_fact_verifier`; `run_hosted_agent_attested` uses zkoracle not TEE (`tee_fact.rs:107-208`, `host.rs:389-408`) | reachable-weld | — | BUILD |
| 4.4 | Money-path conservation proofs | splitter/fee-router soundness | WORKS (PROVED, Lean, 0 `sorry`): `settleRing_conserves` (`Ring.lean:118`), exactly-once escrow (`Lifecycle.lean:294,311`, axiom-audited). **No OCIP-named** splitter module — general primitives back it | done (primitive) | — | — |
| 4.5 | zkoracle price producer (price-as-witness) | attested market data / the oracle leg | WORKS fixture-backed: `zkoracle-prove/src/endpoints/price.rs` `AttestedPrice` over Coinbase; live behind `tlsn-live`; `zkoracle_leaf_adapter.rs` folds it. Real-endpoint+notary step named-not-built (`ZKORACLE-PROVER-STATUS.md`) | days | — | BUILD |
| 4.6 | Screener / data pipeline / REPLAYABLE ranking | the near-term OCIP product | MISSING: plan-only, `ocip-plan-v3.pdf` off-repo; no code (grep-empty) | multi-month | — | BUILD (greenfield) |
| 4.7 | Bonded attention market | the fair-attention product | MISSING as described (plan-only). A real bond+slash primitive exists for **relay operators** (conserving `restitution+remainder==seized`, `node/src/relay_dispute.rs`, `slash_treasury_mirror.rs`) — not an attention/promotion market | multi-month | 4.4 | BUILD (greenfield) |

*4.2 SNP is a reachable-weld (root-fetch + fixture = hours) **only if** `x509-parser` accepts
AMD's RSA-4096-PSS ARK/ASK roots (`snp.rs:285-288`) — that is the one genuine unknown; if it
rejects them, an RSA-PSS verify shim makes it multi-day.

**Track-4 headline:** the *attested/oracle* leg (4.1/4.5) is real and further along than the
vision's "plan" framing — the near-term OCIP *product* (screener + attention market) is
genuine greenfield.

---

## Track 5 — THE WELDS (the recurring "force it in-circuit at settlement" shape)

| # | Weld | Unblocks | State (cited) | Size | Deps | Gate |
|---|---|---|---|---|---|---|
| 5.1 | **Caveat-in-circuit** (per-trade mandate admission) | "the mandate IS the proof" venue-verified | STUB: circuit binds an aggregate `caveatBit` and **trusts the executor's decision** (`Caveat.lean:59`) — expressiveness, not soundness. NB the delegation/budget/revocation half is already PROVED + materialized (`Agent/Mandate.lean:194,227,301`, `DREGGFI-AMBITION.md` #12) | days→multi-month | — | BUILD |
| 5.2 | **Price-as-proof-carrying-witness** (oracle weld) | solvency/lending unconditional on an exogenous mark | further-than-expected: `zkoracle-prove` produces+verifies attested prices, `zkoracle_leaf_adapter.rs` folds them (= 4.5). Weld = bind the attested price as a circuit witness into the solvency/market claim | days | 4.5, 3.5 | BUILD |
| 5.3 | **Shielded-pool-into-effect_vm** | shielded clearing + shielded solvency | MISSING: the standing `shielded/mod.rs:43-48` seam (= DrEX 2.8 = moat 3.6) | multi-month | 3.1 | BUILD |

**The four welds of the vision, mapped to rows:** capability→5.1 · shielded-markets→5.3/2.8 ·
soundness/oracle→5.2 · cross-chain→production MPC (1.10). Three of four are pure BUILD; only the
MPC weld is EMBER-gated.

---

## THE TOP 5 TO SWARM NEXT

Ranked by (unblocks-the-replyable-state × groundedness × small). Each is dispatchable now with
the cites above.

1. **Ship the settlement deploy to Base-Sepolia (1.1 → 1.2 → 1.3).** *reachable-weld.* Unblocks
   the entire "point at a testnet tx" deliverable. Everything below it is done and verified in
   Foundry; this is plumbing (fixture commit + ~20-line script cloned from
   `DreggSettlementRealProof.t.sol:76-83` + a funded broadcast). The broadcast itself is the one
   EMBER touch (key + genesis anchor). **Biggest bang, smallest build.**
2. **Light up the live DrEX matcher over the clear book (2.6 + 2.7).** *days.* Unblocks a
   RUNNABLE DrEX demo. Rungs 1-2 are proved, the matcher (`solver.rs`) is real, and the ring
   already routes through the Lean FFI (`verified_settle.rs`) — this composes existing pieces
   into a demonstrable conserving proof-carrying exchange. No new science.
3. **Exercise the note-spend financial leaf live + write the solvency leaf (3.4 + 3.5).**
   *reachable-weld + days.* Unblocks the moat (first structured product). The note-spend leaf is
   already folded; solvency reuses the `attest.rs` range gadget on the existing custom carrier —
   no new `CarrierWitness`. This is the "everything is a leaf" foothold, and it's closer than the
   vision states.
4. **Close the SNP TEE root-pinning + wire the TEE-fact verifier live (4.2 + 4.3).**
   *reachable-weld.* Unblocks the full ATTESTED lane (both HW roots) + makes attested data
   actually flow. The seams (`with_pinned_roots_pem`, `install_tee_fact_verifier`) already exist;
   the one risk is the x509-parser/RSA-PSS unknown (4.2*) — front-load that probe.
5. **Bind the attested price as a circuit witness (5.2, on top of 4.5).** *days.* Unblocks the
   oracle weld — turns solvency/market theorems from "conditional on an exogenous mark" into
   proof-carrying. The producer (`zkoracle-prove` price endpoint) + the fold adapter
   (`zkoracle_leaf_adapter.rs`) already exist; the weld is binding the witness into the claim.

---

## QUICK WINS (smaller than expected)

- **DrEX rung-2 is already PROVED** (`Market/Aggregation.lean`) — the vision lists it as "to
  build." Free rung.
- **The note-spend financial leaf already exists and folds** (`note_spend_leaf_adapter.rs` +
  the deployed Bridge arm `ivc_turn_chain.rs:3170`). The "first financial leaf" is ~80% there.
- **The settlement deploy script is ~20 lines** cloned from an existing passing test setup.
- **A solvency leaf needs no new carrier** — it rides the deployed custom carrier reusing the
  `attest.rs` 30-bit range gadget.
- **The oracle/price-as-witness leg has a runnable producer already** (`zkoracle-prove` +
  `zkoracle_leaf_adapter.rs`) — further along than the vision's "the deepest weld" framing.
- **Single-node devnet stand-up is documented and real** — no revive needed for a local demo.

## HIDDEN BLOCKERS (bigger / riskier than they look)

- **outboundMessageRoot proof-binding (1.8)** is a full apex→shrink→gnark **VK-regen flag-day**
  across the turn layer (SIBLING territory), not an incremental contract fix — cross-chain
  *messaging* (as opposed to *settlement*) is gated on it.
- **Devnet revive (1.7)** is double-gated: EMBER (eyes-open VK-epoch flip) **and** a not-yet-cut
  Lean seed (`lean-seed.pin` empty). A local single-node devnet sidesteps both.
- **SNP RSA-4096-PSS (4.2*)** — if `x509-parser` rejects AMD's roots, the "hours" weld becomes a
  multi-day RSA-PSS shim. Probe first.
- **The priced substrate (2.3)** — uniform-price/envy-free (2.4/2.5) can't be built until
  `DemoRes` is lifted off discrete-exact-book to prices/partial-fills; that lift, not the
  theorems, is the real work.
- **Fixture coherence (1.1)** — the uncommitted `settlement_groth16.json` means a naive deploy
  could ship a verifier keyed to a different proof run. Diff before broadcast.

## EMBER-GATED vs PURE-BUILD (the honest split)

- **EMBER (outward — do not dispatch a swarm to decide):** the Base-Sepolia broadcast (funded
  key + chosen genesis anchor, 1.3); the federated-devnet revive / re-genesis + the VK-epoch flip
  (1.7); the **production MPC ceremony** (1.10) — mainnet only, never testnet; upstreaming the
  alloy-trie finding.
- **SIBLING (coordinate, don't clobber):** outboundMessageRoot 26th-PI (1.8, turn/apex layer);
  the seed cut (1.7).
- **PURE BUILD (dispatch now):** everything else — the deploy script (1.2), single-node devnet
  (1.6), all of DrEX rungs 2.3-2.9, the whole moat/leaf track (3.x), the OCIP attested lane +
  screener + attention market (4.2-4.7), and welds 5.1-5.3. The overwhelming majority of the
  roadmap is dispatchable without an ember decision.

## See also

`DREGGFI-VISION.md` · `DREGGFI-AMBITION.md` (the factcheck — #5 rung state, #12 mandate, #13
FFI ring, #14 cross-chain honest edge) · `INTERCHAIN-MODEL.md` · `GOAL-MULTICHAIN-SETTLEMENT.md`
+ `HORIZONLOG.md` (the wrap, done) · `DEV-NODE-RUNBOOK.md` / `HOMELAB-N3-RUNBOOK.md` (devnet) ·
`chain/DEPLOY.md` (stale — Vault+Gate only) · `metatheory/Market/{Clearing,Fairness,Aggregation}.lean` ·
`circuit-prove/src/{note_spend,custom,zkoracle}_leaf_adapter.rs` · `circuit-prove/src/shielded/{mod,pool,attest}.rs` ·
`tee-verify/src/{lib,snp}.rs` · `zkoracle-prove/src/endpoints/price.rs`.
