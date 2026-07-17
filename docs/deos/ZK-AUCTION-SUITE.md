# The dregg ZK-Auction Suite — the comprehensive proven-fair, ZK-private auction family

*The definitive map of the best-possible auction suite dregg can offer: every mechanism proven-fair (the
clearing rule is a machine-checked theorem), ZK-private where privacy earns its keep (no operator peek, no
decryption committee), across the whole family — sealed / batch / Vickrey / English / Dutch / combinatorial
plus the market applications. Grounded in the REAL app foundation (`starbridge-apps/`) and the PROVEN
clearing layer (`metatheory/Market/`, `metatheory/Dregg2/`), honestly graded per claim, bold where the
proof carries it. Present-tense, what-is. The honest edges are named in §6/§8, not buried.*

The one-line thesis: **dregg is the only stack that holds all three at once — a proven-fair clearing rule
(a Lean theorem, not an audit), a working commit-reveal auction primitive re-used across five shipped apps,
and a built multi-asset shielded pool — so it can offer the *whole* auction family proof-carrying and
private-where-it-matters, from a $5 sealed-bid NFT to a private multilateral DEX. Every incumbent has one
leg; none has the fold.** The ring-clearing apex circuit is BUILT at both the 2-leg and the N-leg size
(`circuit-prove/src/shielded_ring_clearing_air.rs`, `shielded_ring_clearing_nleg_air.rs`); the named seams
between it and a running private auction live in `docs/deos/SHIELDED-DREX-ASSURANCE-ROADMAP.md` — the
reveal-nothing ZK theorem (the crux), the PQ value-commitment cutover, and the deployed-VK fold + app
integration. This doc maps the family, grades each mechanism, and names the build ladder.

---

## 1. The starbridge-apps auction foundation — what EXISTS (cited)

The app layer already carries a **single reusable commit-reveal auction primitive** and the market/settlement
organs that clear what it discovers. There is no shared Rust auction crate — `starbridge-apps/shared/` is
browser JS only (its README: "all policy … lives in the per-app Rust crates"). The primitive is the
`sealed-auction` crate; two apps mirror it structurally, two are the settlement organs, one composes them.

### 1.1 THE primitive — `sealed-auction` (`starbridge-apps/sealed-auction/src/lib.rs`)
A commit → reveal → settle sealed-bid **first-price** auction, the Rust image of the Lean `SealedAuction`.

- **The seal** (`lib.rs:129`): `Bid::seal(&self) -> [u8;32] = BLAKE3_derive_key("dregg-sealed-auction bid v1",
  bidder ‖ sign ‖ |value| ‖ nonce)` — binding + hiding, mirroring the Lean `sealOf` and the running
  `compute_commitment_hash` (`intent/src/commit_reveal_fulfillment.rs`).
- **The state machine**: `Phase::{Commit, Reveal, Settled}` (`:147`); `Auction{ seller, slot, asset,
  slot_asset, commitments: HashSet<Seal>, phase, revealed: BTreeMap<Seal,Bid> }` (`:199`); the API
  `commit(seal)` / `seal_commit_phase()` / `valid_reveal(&bid)` / `reveal(bid)` / `winner()` (`max_by_key
  value`) / `award_ring(winner)` (two balanced legs) / `settle(ledger)` folding through
  `dregg_intent::verified_settle::settle_ring_verified` (`:235–:323`).
- **The on-ledger floor** — the "two-tempo fire": (1) a deos `GatedAffordance` cap∧live-state PHASE
  precondition decides the button in-band; (2) a `fire_*` full multi-effect turn is re-enforced by the
  installed `auction_cell_program()` (`:477`): `Cases[Always(WriteOnce commit-board `COMMIT_BASE+i` +
  WriteOnce seller/high-bid/winner + `Monotonic(PHASE)`); close_commit/resolve → `StrictMonotonic(PHASE)`]`.
  The `WriteOnce` board is the **anti-front-running tooth** made a real executor refusal: a committed seal
  cannot be swapped. Rights ladder `OBSERVER=Signature ⊂ BIDDER=Either ⊂ AUCTIONEER=None`, reused verbatim
  in every app. `service.rs` re-expresses the same lifecycle as a cells-as-service object (`AuctionService`,
  5 typed methods through the `invoke_with_descriptor` front door).

### 1.2 The mirrors — `gallery` and `tussle`
- **`gallery`** (`gallery/src/lib.rs`) — sealed-submission curation, a one-for-one structural clone
  (docstring: "the same shape the sealed-auction app proves for awards"). `Submission::seal` =
  `BLAKE3(artist‖piece‖nonce)`; `Phase::{Submission, Reveal, Curated}`; `submit`↔`commit`,
  `close_submissions`↔`seal_commit_phase`, `featured()`↔`winner` (`max_by_key piece`), `curate()`↔`settle`
  (picks + marks, no ledger). Same `WriteOnce`-board floor: **you cannot swap a committed submission.**
- **`tussle`** (`tussle/src/lib.rs`) — fog-of-war commit-reveal fighting: `MoveCommit::seal =
  BLAKE3(figure‖joints‖nonce)`, `FramePhase::{Commit, Reveal, Resolved}`, `commit`/`seal_commit_phase`/
  `reveal` (three teeth: phase, seal-binding, figure-cap) / `resolve` folding contact deltas through the
  **same** `settle_ring_verified`. Extra tooth: typed `SymMemberOf` joint-slot gate.

### 1.3 The settlement organs — `compute-exchange` and `escrow-market`
- **`compute-exchange`** (`compute-exchange/src/lib.rs`) — a job+budget escrow market (`POSTED → BID →
  SETTLED`), NOT commit-reveal. `job_cell_program()` (`:372`) carries four organ caveats: BUDGET gate
  `FieldLteField{BID ≤ BUDGET}`, ACCEPTED `WriteOnce(BID)`, FLASHWELL conservation `AffineEq{PAID + REFUNDED
  − BUDGET = 0}` + no-mint `AffineLe{… ≤ 0}`, LIFECYCLE `StrictMonotonic(STATE)`. Turn builders
  `build_post`/`build_bid` (`price ≤ BUDGET`, binds provider) / `build_settle`. Plus a pooled ERC-4626-style
  `ComputeFundVault` (`:189`) over `dregg_cell::vault`. This is the **real-time job auction** organ:
  providers bid a price bounded by the requester's escrowed budget; settlement is conservation-gated.
- **`escrow-market`** (`escrow-market/src/lib.rs`) — the atomic-swap / verifiable market, re-exporting the
  proven capacity `dregg_cell::escrow_sealed`. `SealedEscrowMarket{ escrow, terms, custody_a, custody_b }`
  (`:180`) with `open(terms)` / `deposit(side, leg)` (locks a conforming leg into custody) / `settle`
  (2-of-2 atomic crossing, no partial) / `reclaim` (half-open-trade defence). Four properties proved in
  `starbridge-apps/escrow-market/tests/atomic_swap.rs`.

### 1.4 The composition — `escrow-market/examples/verifiable_market.rs`
The single real cross-crate use of the auction primitive: it wires **sealed-auction as the front-run-proof
price-discovery organ** and **escrow-market as the atomic clearing organ** — the auction's `(winner, price)`
becomes the escrow's `EscrowTerms`. This is the composition pattern the whole suite generalizes:
*discover a price under a seal, clear it atomically under conservation.*

**The takeaway:** the app layer already has (a) a battle-tested sealed commit-reveal primitive with a real
on-ledger anti-tamper floor and a service/deos surface, mirrored across three apps; (b) a budget-bounded job
market; (c) an atomic-swap market; (d) the discovery→clearing composition. What it does NOT yet have: a
*shielded* (single-phase, no-reveal) app variant and second-price winner selection. (The ring-clearing
circuit itself is built in `circuit-prove` — §2/§3.3 — but no app rides it yet.)

---

## 2. The proven-fair clearing spine — what is a THEOREM (cited)

The app primitives above bind to a machine-checked clearing layer. Grades: **PROVED** (Lean theorem about the
deployed artifact) · **PROVED-SPEC** (Lean theorem, circuit unbuilt) · **BUILT** (Rust, tested) ·
**MODEL-PROVED** (Lean, priced-model level, not yet `settleRing`-realized) · **DESIGN** (not started). This
is the OCIP trust-grade spine (`DREGGFI-VISION.md §1`) — every badge carries exactly one grade.

- **Sealed first-price, ledger-realized** — `SealedAuction.lean`. `reveal_binds_committed` (under BLAKE3 CR,
  a committed seal opens to *exactly* the sealing bid — the no-peek-then-switch tooth, non-vacuous over the
  real `Blake3Kernel`, FALSE for a collapsing hash), `uncommitted_cannot_win`, the phase gates,
  `settle_atomic`, `settle_conserves` (the award rides `Ring.settleRing` all-or-nothing, value-neutral).
  **Grade: PROVED, ledger-realized** through `recKExecAsset`. This is the *two-phase* baseline — it carries
  the reveal-round tax rung-3 deletes.
- **Uniform-price optimality + envy-freeness** — `Market/Optimality.lean`: `uniform_price_no_arbitrage`
  (every leg of a two-sided one-price batch is value-neutral), `uniform_price_envy_free` (same-direction
  legs clear at the identical rate), `uniform_price_optimal` (the capstone: sound *and* no improving
  unilateral deviation, composing rung-5 `priced_clearing_keystone`). This is the Budish-FBA
  "single price ⇔ no-arbitrage" property, machine-checked. **Grade: MODEL-PROVED** — over the priced `Fill`
  model (`Market/Priced.lean`, real ℚ prices), single-participant/pairwise core, NOT yet `settleRing`-realized,
  NOT k-coalition TTC-core stable.
- **Limit-respecting fairness (individual rationality), ledger-realized** — `Market/Fairness.lean`:
  `clearing_respects_limits` / `cycleValid_fulfilled_respects_limits` (nobody debited above its offer nor
  credited below its minimum, with refusing teeth `overdebit_refused` / `wrongAsset_refused`), stated over the
  real executor step `settleRing k … = some k'`. **Grade: PROVED, ledger-realized.**
- **The rung-3 keystone — private matching over hidden commitments** — `Market/ShieldedClearing.lean`:
  `shielded_ring_clears` welds three proven towers into one statement — a shielded ring whose matched cycle
  is `CycleValid` and settles through the verified executor is simultaneously **(a) conserving** per asset on
  the real ledger, **(b) fair** (structurally balanced + every leg within its committed offer/want), **(c)
  private + no-double-spend** (every leg spends a real committed member note, owner/value hidden inside
  `HidingFriPcs`, nullifier fresh and never re-spendable). Companion `shielded_ring_value_conserves_hidden`:
  the homomorphic excess is zero *over the commitments alone* — a verifier confirms no value was minted
  without learning a single amount. **Grade: PROVED spec + BUILT circuit (2-leg and N-leg).** The two
  layers are FUSED on both sides: `Market/LedgerRealizationExt.lean:312` `shielded_ring_fused_clears` welds
  the matcher's committed `offerAsset`/`offerAmount` to the spent note's `asset`/`value` (`LegFused`), and
  the circuit enforces the fusion IN-AIR — `circuit-prove/src/shielded_ring_clearing_air.rs` (2-leg tight
  cycle: the descriptor re-computes the Poseidon2 `value_binding` and the apex `connect`s it to the
  shielded-spend leaf's exposed lane; both-polarity tests — non-conserving / wraparound-mint / double-spend
  / mis-fused legs all UNSAT) and `shielded_ring_clearing_nleg_air.rs` (variable-length N-cycle + the
  partial-fill `offer ≥ want_min` inequality in-AIR via the bit-decomposition range bedrock). Named
  residuals ride `SHIELDED-DREX-ASSURANCE-ROADMAP.md`: the reveal-nothing ZK theorem (the crux),
  conservation over the two-coordinate `pedTwoGen` abstraction (not the real curve point), the 64-bit range
  (amounts above `2^VALUE_BITS` lean on the off-AIR Bulletproof), and the deployed-VK fold.
- **Real-crypto weld** — `Dregg2/Shielded/RealCrypto.lean`: retires the two toy stand-ins the
  audit flagged. Hidden conservation now over the REAL two-generator group Pedersen `commit v r = v·G + r·H`
  (`ring_conserves_pedersen`, binding = the named DLog carrier `CryptoPrimitives.binding`), membership over
  the REAL Poseidon2 tree (`root_binds` / `forged_set_forces_collision` under `Poseidon2SpongeCR`). **Grade:
  PROVED reduction to two named floors** (DLog binding, Poseidon2 CR) — the same floors the whole tree stands
  on, not `Nat`-additive/linear-rolling toys.
- **The shielded pool** — `circuit-prove/src/shielded/pool.rs`: a multi-asset (ZSA-style) pool.
  `commit_hidden_asset(value, asset_type, blinding) = v·V + at·H_asset + r·R` hides amount, owner, AND asset
  type; a single homomorphic Schnorr excess proof carries per-asset conservation while the asset stays hidden;
  per-output Bulletproof range proofs close the inflation hole; a Chaum-Pedersen asset-equality proof handles
  split/merge; one nullifier set gates double-spend across all assets. **Grade: BUILT + tested both
  polarities** (Rust over p3 `HidingFriPcs`); the STARK side is the DSL-emitted `shielded_spend_circuit`, no
  hand-written AIR.

**The named frontier, once:** the ring-clearing apex circuit exists — it folds N
`prove_shielded_spend_leaf_with_claim` leaves into an apex that verifies the conserving cycle over hidden
commitments, fusing each offer to its hidden note in-AIR (`prove_shielded_ring_clearing_apex`, 2-leg and
N-leg). Between it and a running private auction stand the roadmap seams: the reveal-nothing ZK theorem,
the deployed-VK fold, and a shielded-auction app surface (`SHIELDED-DREX-ASSURANCE-ROADMAP.md`).

---

## 3. The comprehensive suite — the family

For each mechanism: **what it is · the ZK-privacy tier · the dregg primitive it rests on · the app-layer
realization · the honest grade · the build cost.** Privacy tiers (from `SHIELDED-AUCTIONS-DESIGN.md §1.3`):
**Public** (open book), **Committee** (threshold-decrypt / MPC — a trusted set *does* see plaintext later),
**ZK-sealed** (commitments + proofs, *no party ever* holds plaintext — the frontier).

### 3.1 Sealed-bid first-price — the baseline
- **What.** Bidders seal `H(bidder‖value‖nonce)` in a commit window, reveal, highest bid wins and pays its
  own bid. The classic sealed auction.
- **Privacy tier.** ZK-sealed *during commit* (nothing observable before reveal), Public *at reveal* (bids
  open in the clear to clear). No committee.
- **Rests on.** `SealedAuction.lean` (`reveal_binds_committed`, `settle_conserves`) + the `sealed-auction`
  app primitive (§1.1).
- **App realization.** `starbridge-apps/sealed-auction` — SHIPPED, on-ledger enforced, service + deos surface.
- **Grade.** **PROVED, ledger-realized.** Its weakness is a mechanism-design fact, not a bug: **bid-shading**
  (winner bids below value to keep surplus, must guess rivals) — first-price is not truthful (§3.4 fixes this).
- **Cost.** **Zero — it ships today.** The reference implementation of the whole suite's commit-reveal tempo.

### 3.2 Uniform-price batch — the default clearing rule
- **What.** All orders in a window clear at ONE price (the market-clearing price); every winner pays the same.
  Discretizing time + one price kills the latency race and ordering-MEV (Budish FBA / CoW UCP).
- **Privacy tier.** Public-to-ZK-sealed depending on carrier: a plaintext batch (launchpad reveal) is Public;
  the shielded batch (§3.3) is ZK-sealed. The *mechanism* is privacy-agnostic.
- **Rests on.** `uniform_price_optimal` / `_no_arbitrage` / `_envy_free` (`Market/Optimality.lean`,
  MODEL-PROVED) + `clearing_respects_limits` (`Market/Fairness.lean`, PROVED ledger-realized) + the
  `sealed-auction` commit tempo.
- **App realization.** The **launchpad** (`chain/contracts/launchpad/DreggLaunchpad.sol` + `launchpad-web/`):
  a sealed-bid commit→reveal **uniform-price** raise, on-chain-enforced no-snipe/no-late-switch, with an
  optional `IClearingAttestor` binding a real dregg Groth16 clearing proof. SHIPPED (Solidity + web + indexer).
- **Grade.** **Mechanism PROVED (model-level); commit-reveal PROVED/on-chain; the clearing-proof attestation
  is the named weld** (Groth16 attestor wired, proof-carrying clearing = rung-2 of the launchpad).
- **Cost.** **Small** to lift the launchpad's uniform-price settlement onto the app-native `settle_ring_verified`
  path; **the anti-MEV/anti-snipe default is done.** This is the recommended default rule for every batch.

### 3.3 Shielded / ZK-sealed-bid uniform-price — THE MARQUEE
- **What.** Bidders publish a Pedersen commitment to (price, quantity) + a ZK validity proof (range + funded)
  in ONE message. The batch clears at a uniform price *over the hidden commitments*. **No reveal round, no
  committee** — winner-set and clearing price proved in-circuit.
- **Privacy tier.** **ZK-sealed (Very High) — the frontier.** Nothing to decrypt; no party ever sees a bid.
  Kills all five vectors at once: sniping (batch), front-running/MEV (commitments), non-reveal griefing
  (single-phase — the §1.5 holy grail), operator/committee collusion (nothing to peek), and — with
  uniform-price — ordering irrelevance.
- **Rests on.** `shielded_ring_clears` (rung-3) + `shielded_ring_value_conserves_hidden` + `RealCrypto.lean`
  (real Pedersen/Poseidon2) + `uniform_price_optimal` + the shielded pool (`pool.rs`, BUILT).
- **App realization.** A NEW `shielded-auction` app (the private twin of §1.1) whose winner-selection and
  clearing ride the ring-clearing apex over pool notes instead of the clear `settle_ring_verified`.
- **Grade.** **PROVED spec + BUILT circuit.** The ring-clearing apex AIR exists at 2-leg and N-leg with the
  value-commitments-in-AIR fusion enforced (§2). Still named seams: the in-circuit uniform clearing-price
  *selection*, the shielded-auction app itself, and the privacy claim's reveal-nothing ZK theorem
  (`SHIELDED-DREX-ASSURANCE-ROADMAP.md` component 3) — until that theorem lands, "no party ever sees a bid"
  is an architecture property, not a proved one.
- **Cost.** **Medium→RESEARCH remaining** — the ZK theorem + price selection + app integration; the AIR
  de-risk is done (both sizes prove honestly and refuse forges).

### 3.4 Vickrey / second-price (shielded) — the truthful single-lot
- **What.** Single-lot sealed auction paying the **highest losing bid**. Vickrey (1961): payment set by
  *others'* bids ⇒ bidding true value is dominant ⇒ **bid-shading disappears (DSIC)**. In ZK: compute the
  second-max over commitments *without revealing any bid, including the winner's*.
- **Privacy tier.** **ZK-sealed** — and doing it in ZK removes the classic Vickrey failure mode: a corrupt
  auctioneer who fakes the second price or leaks bids. The private second-price computation is the textbook
  ZK/MPC sweet spot.
- **Rests on.** The shielded pool + a NEW ZK comparison / second-max circuit + a NEW Lean `runnerUpOf` +
  truthfulness spec. dregg proves *first-price* today (`winnerOf = max`); second-price is a **new mechanism**.
- **App realization.** A single-lot mode of the shielded-auction app, targeted at **RWA / NFT** sales where
  DSIC matters and demand-reduction is moot (one unit).
- **Grade.** **DESIGN** — neither the Lean spec nor the circuit exists yet. The highest-value *new mechanism*.
- **Cost.** **Medium** (Lean `runnerUpOf` + truthfulness theorem) then **Large** (the ZK second-max circuit).
  Sequenceable *after* §3.3's AIR proves the clearing-circuit pattern.

### 3.5 English (ascending) — assess
- **What.** Open ascending outcry; price rises until one bidder remains. Strategically ≈ Vickrey (drop at
  your value), but *inherently multi-round and price-revealing*.
- **Privacy tier.** **Poorly ZK-able.** The mechanism's whole point is public price ascent; hiding it defeats
  it. A hidden-reserve English is possible (reserve committed, revealed only if unmet) but the bid dynamics
  stay public.
- **Rests on.** Would need a per-round commit-reveal loop over the `sealed-auction` tempo — many phase-gate
  cycles.
- **App realization.** Low priority; a multi-round `tussle`-style loop could host it if ever wanted.
- **Grade / cost.** **DESIGN / SKIP for the ZK suite.** English's value (price discovery via ascent) is
  exactly what §3.2 uniform-price captures without the multi-round latency race. Offer it only as a *public*
  convenience mode, not a ZK product. **Recommendation: do not build.**

### 3.6 Dutch (descending) — assess
- **What.** Price descends from a high start; first to accept wins at the current price. Fast, single-decision.
- **Privacy tier.** **Partially ZK-able and genuinely useful: the hidden-reserve Dutch.** The *floor/reserve*
  is a Pedersen commitment; the clock descends publicly; the sale clears the instant a bid crosses the hidden
  reserve, and a ZK proof shows "cleared at/above the committed reserve" *without revealing the reserve*.
  This defeats reserve-sniping (bots that park exactly at a known reserve) and operator reserve-manipulation.
- **Rests on.** The shielded pool's commitment + a ZK range/comparison proof (the same second-max primitive
  family as §3.4) + `uniform_price` for the single-clear.
- **App realization.** A "descending-clock" mode of the launchpad / a `dutch-launch` app — attractive for
  fair token launches and NFT drops that want a time-decay price with a private floor.
- **Grade.** **DESIGN** — the hidden-reserve proof is a small specialization of the §3.4 comparison circuit.
- **Cost.** **Medium**, and it *rides §3.4's circuit* — build it as the second consumer of the ZK-comparison
  primitive. **Worth offering** (unlike English) because the hidden reserve is a real, marketable ZK win.

### 3.7 Combinatorial / multi-unit uniform-price — the priced substrate
- **What.** Multiple units / multiple pairs cleared together at a (per-pair) uniform price; partial fills;
  cross-pair demand. The treasury-style multi-winner allocation.
- **Privacy tier.** ZK-sealed via the shielded ring (multi-leg) or Public via the priced book.
- **Rests on.** `priced_clearing_keystone` (`Market/Priced.lean`, rung-5 — real ℚ prices, partial fills,
  multi-pair) + `uniform_price_optimal` + the multilateral matcher (`intent/src/solver.rs`: Johnson circuits
  + Shapley-Scarf TTC).
- **App realization.** The DrEX multi-pair book (§3.13); the launchpad's multi-tranche raise.
- **Grade.** **MODEL-PROVED** (rung-5 priced substrate) — not yet `settleRing`-realized; full-combinatorial
  (arbitrary bundle bids, the NP-hard winner-determination) is NOT attempted and is a known frontier.
- **Cost.** **Medium** to ledger-realize the priced layer; **Large/RESEARCH** for true bundle combinatorics
  (out of scope — uniform-price multi-unit covers the practical demand).

### 3.8 The compute market — a real-time job auction
- **What.** A requester posts a job + escrowed budget; providers bid a price ≤ budget; the job settles under
  conservation. A live procurement market for compute / agent tasks.
- **Privacy tier.** Public today (budget + bids in slots); ZK-sealed upgrade = shielded provider bids so
  competitors can't undercut off a visible book.
- **Rests on.** `compute-exchange` (§1.3, the BUDGET-gate + FLASHWELL-conservation `job_cell_program`) +
  optionally the sealed commit tempo for a sealed-bid provider round.
- **App realization.** `starbridge-apps/compute-exchange` — SHIPPED (budget-bounded, conservation-gated,
  vault-pooled). Add a `commit_bid` phase (mirror §1.1) for a **sealed** provider auction.
- **Grade.** **BUILT** (the market); **DESIGN** for the sealed/shielded provider-bid upgrade.
- **Cost.** **Small** to add a sealed provider round (compose the existing primitive); Medium for shielded.

### 3.9 The escrow / atomic-swap market
- **What.** Two parties commit legs into custody; a 2-of-2 atomic crossing settles or each reclaims. The
  clearing organ for any discovered price.
- **Privacy tier.** Public terms today; the shielded pool makes the legs hidden (a shielded 2-leg swap =
  `demoShieldedRing`).
- **Rests on.** `escrow-market` (§1.3, `dregg_cell::escrow_sealed`, atomic settle, half-open-trade defence).
- **App realization.** `starbridge-apps/escrow-market` — SHIPPED, four properties proved
  (`starbridge-apps/escrow-market/tests/atomic_swap.rs`). The `verifiable_market.rs` composition IS the discovery→clearing pattern.
- **Grade.** **BUILT** (atomic swap); shielded legs = **circuit BUILT** (the 2-leg shielded ring apex, §3.11).
- **Cost.** **Small** (it ships); the shielded variant's 2-leg ring apex exists — app wiring remains.

### 3.10 RWA / NFT sealed auctions — the single-lot showcase
- **What.** A single high-value lot (a tokenized real-world asset, an NFT) sold sealed-bid — first-price
  today, **shielded-Vickrey** as the truthful upgrade (§3.4).
- **Privacy tier.** ZK-sealed (shielded-Vickrey) — bidders' identities and losing bids never revealed; the
  clearing price honest *and* private.
- **Rests on.** The `sealed-auction` primitive (first-price, today) → shielded pool + second-max circuit
  (Vickrey, new).
- **App realization.** A single-lot mode of the sealed/shielded-auction app.
- **Grade.** **PROVED** (first-price today, on the shipped primitive); **DESIGN** (shielded-Vickrey).
- **Cost.** **Zero** for first-price now; Medium→Large for the truthful private version.

### 3.11 Private OTC / RFQ — the smallest shielded instance
- **What.** A request-for-quote where responders submit sealed quotes; the requester clears the best without
  the quote book being public. A degenerate 2-party, single-pair shielded ring.
- **Privacy tier.** ZK-sealed — removes the OTC desk's informational edge (desks *are* the operator-peek
  problem).
- **Rests on.** `shielded_ring_clears` specialized to a bilateral cycle (`demoShieldedRing` is exactly a
  2-leg swap) + the shielded pool.
- **App realization.** A `shielded-rfq` app; the `escrow-market` atomic settle as the clearing organ.
- **Grade.** **Circuit BUILT** — the 2-leg ring apex (`shielded_ring_clearing_air.rs`) IS this instance,
  proving the honest tight swap and refusing forges; the `shielded-rfq` app surface is unbuilt.
- **Cost.** **Small** — app wiring over the existing 2-leg apex.

### 3.12 The launchpad — a fair-launch auction
- **What.** A token launch as a sealed-bid uniform-price batch: participants commit sealed bids; the sale
  clears at one price; **the operator never sees a bid before clearing** — cannot self-allocate, tip
  insiders, or front-run. Fairness = "no operator peek."
- **Privacy tier.** ZK-sealed during commit / Public at reveal (today, two-phase); ZK-sealed end-to-end once
  the shielded batch (§3.3) lands (single-phase, upgradable).
- **Rests on.** `SealedAuction` (commit tempo, PROVED) + `uniform_price_optimal` (MODEL-PROVED) + the shielded
  pool for the single-phase upgrade.
- **App realization.** `chain/contracts/launchpad/DreggLaunchpad.sol` + `launchpad-web/` — SHIPPED on-chain
  (commit/reveal/clear phases, `IClearingAttestor` for a Groth16 clearing proof).
- **Grade.** **BUILT/on-chain** (two-phase sealed uniform-price); the clearing-proof attestation is the named
  weld; single-phase inherits §3.3 (circuit built; ZK theorem + price selection + integration open).
- **Cost.** **Done** (two-phase); Large for single-phase (inherits §3.3's AIR). **Highest near-term value.**

### 3.13 The DrEX — a continuous private-matching DEX
- **What.** The multilateral ring matcher (`intent/src/solver.rs`: Johnson circuits + Shapley-Scarf TTC) runs
  over shielded notes — a private, MEV-resistant DEX where matching happens inside the proof over hidden
  commitments, cleared at a uniform price. The flagship.
- **Privacy tier.** ZK-sealed — *private and fair without trusting any operator, committee, or sequencer*
  (`DREGGFI-VISION.md §4`); residual leakage = timing + anonymity-set size + intentional clearing-price
  disclosure. No dark pool, encrypted mempool, or batch-auction DEX can claim that.
- **Rests on.** `shielded_ring_clears` + the real matcher + the shielded pool + `aggregate_sound`
  (`Market/Aggregation.lean`, the order-book faithfulness rung).
- **App realization.** DrEX (`docs/deos/DREX-DESIGN.md`) — the exchange that realizes §3.3 live.
- **Grade.** **Circuit BUILT / assurance OPEN** — the N-leg ring apex exists; the DrEX product waits on the
  roadmap components (reveal-nothing ZK, deployed-VK fold) + the ledger-realization weld of the priced
  rungs 4–6.
- **Cost.** **Large / RESEARCH** — §3.3's remaining seams realized as a live exchange.

### 3.14 The dark pool — the ONE place MPC earns a seat
- **What.** A *persistent* private order book — resting orders matched against *future* orders without ever
  being revealed or committed to a public clearing.
- **Privacy tier.** Committee (MPC) — secret-shared orders across a non-colluding node set.
- **The honest MPC-vs-ZK line** (`SHIELDED-AUCTIONS-DESIGN.md §4`): dregg's rung-3 fold **subsumes** the
  *single-clearing-batch* dark pool (a sealed batch cleared over commitments is a dark pool with *no* nodes,
  strictly stronger than MPC on trust — no committee, no liveness dependency). MPC earns its seat *only* for
  the persistent cross-time book, where no single proof spans the interaction.
- **Rests on.** A NEW MPC matching subsystem (dregg has none today — `trustless.rs` is threshold-*decryption*,
  committee crypto, not an MPC *matcher*).
- **Grade / cost.** **DESIGN / deferred, Large new-subsystem.** Only justified if a persistent shielded book
  is a product requirement; the batch primitives (§3.3, §3.11, §3.13) cover most demand without it.

---

## 4. The suite at a glance

| # | Mechanism | Privacy tier | Rests on | App | Grade | Cost |
|---|---|---|---|---|---|---|
| 3.1 | Sealed first-price | ZK-commit / Public-reveal | `SealedAuction.lean` | sealed-auction | **PROVED** | ships |
| 3.2 | Uniform-price batch | agnostic | `Optimality.lean` | launchpad | **PROVED (model)/on-chain** | small |
| 3.3 | **Shielded ZK-sealed uniform-price** | **ZK-sealed** | `shielded_ring_clears` + pool | shielded-auction (new) | **PROVED spec + BUILT circuit** | **Med→RESEARCH (ZK thm + app)** |
| 3.4 | Shielded-Vickrey (2nd-price) | ZK-sealed | pool + 2nd-max circuit (new) | shielded single-lot | **DESIGN** | Med→Large |
| 3.5 | English | poorly ZK-able | commit-reveal loop | — | **SKIP** | — |
| 3.6 | Dutch (hidden reserve) | partial ZK | pool + comparison circuit | dutch-launch (new) | **DESIGN** | Medium |
| 3.7 | Combinatorial / multi-unit | ZK / Public | `Priced.lean` rung-5 | DrEX / launchpad | **MODEL-PROVED** | Med (bundles: skip) |
| 3.8 | Compute market | Public → ZK | compute-exchange | compute-exchange | **BUILT** | small |
| 3.9 | Escrow / atomic swap | Public → ZK | escrow-market | escrow-market | **BUILT** | small |
| 3.10 | RWA / NFT sealed | ZK-sealed | primitive → Vickrey | single-lot | **PROVED**→DESIGN | 0→Large |
| 3.11 | Private OTC / RFQ | ZK-sealed | 2-leg shielded ring | shielded-rfq (new) | **circuit BUILT** | Small (app) |
| 3.12 | Launchpad fair-launch | ZK-commit/Public | `SealedAuction`+`Optimality` | launchpad | **BUILT/on-chain** | done |
| 3.13 | DrEX private DEX | ZK-sealed | `shielded_ring_clears`+matcher | DrEX | **circuit BUILT / assurance open** | Large/RESEARCH |
| 3.14 | Dark pool (persistent) | Committee (MPC) | new MPC subsystem | — | **DESIGN/deferred** | Large |

---

## 5. What makes this THE auction suite — the comprehensive-offering frame

Three properties, and **no incumbent holds more than one:**

1. **Proven-fair — the clearing rule is a THEOREM, not an audit.** `uniform_price_optimal`,
   `clearing_respects_limits`, `settle_conserves`, `reveal_binds_committed` are machine-checked in Lean over
   the real executor / real BLAKE3 CR — not "audited by a firm," not "battle-tested." An unfair clearing is
   *unconstructable*, not monitored. No auction platform on earth ships a machine-checked optimality theorem.
2. **ZK-private where it earns its keep — no operator peek, no committee.** The shielded pool is BUILT and
   the rung-3 private-matching clearing is a proved spec realized by a built ring-clearing circuit that
   **deletes the decryption committee outright** — clearing over commitments, nothing to decrypt. This is
   the frontier the literature (`SHIELDED-AUCTIONS-DESIGN.md §1.5`) is stuck short of: single-phase,
   no-committee.
3. **The whole family + the app layer.** Sealed / batch / Vickrey / Dutch / combinatorial + compute market +
   escrow swap + RWA/NFT + RFQ + launchpad + DEX — every one composing the *same* commit-reveal primitive
   (shipped, mirrored ×3), the *same* proven clearing, the *same* shielded pool. Not one auction; a suite.

**Why no incumbent matches it:**
- **CoW Protocol** — batch UCP is the right *mechanism*, but its solvers *see every order* (privacy = trust
  the solver, not crypto), and its fairness is empirical, not a theorem.
- **Shutter** — encrypted mempool, but a standing Keyper committee *does* hold the plaintext (later); no
  proof-carrying clearing.
- **pump.fun / bonding-curve launchpads** — no sealed bids, no uniform-price fairness, operator-visible flow;
  the anti-fair-launch archetype.
- **RWA chains (Ondo, Centrifuge, …)** — tokenize assets but auction them with plaintext books and no ZK; no
  private second-price, no proven clearing.
- **MPC auction networks (Arcium, zkHawk-style)** — distribute the committee but do not *delete* it (liveness
  + collusion dependency), and carry no fairness theorem.

dregg is the intersection `P1(shield) ⊗ P2(proven ring-clearing) ⊗ P3(sealed no-peek) ⊗ P4(uniform-price
fairness)` that `DREGGFI-VISION.md §3` argues **only dregg holds together** — because there is *no instant and
no party* that holds the plaintext or the ordering power, and the fairness is a proof rather than a promise.

---

## 6. The build ladder — ship-now vs AIR-gated

**Ships NOW on the app foundation + proved pieces (no new circuit):**
- Sealed first-price (§3.1) — the `sealed-auction` app, PROVED + on-ledger.
- Two-phase uniform-price launchpad (§3.12) — SHIPPED on-chain; the fair-launch product.
- Compute market (§3.8) + a sealed provider-bid round (small compose).
- Escrow / atomic-swap market (§3.9) — SHIPPED, four properties proved.
- RWA/NFT first-price single-lot (§3.10) — a mode of the shipped primitive.
- Public/Committee OTC via escrow — the plaintext path while the shielded RFQ AIR is built.

**The ring-clearing apex AIR is BUILT (2-leg + N-leg); these now gate on the assurance roadmap
(reveal-nothing ZK theorem, deployed-VK fold) + app integration:**
- Shielded ZK-sealed uniform-price (§3.3) — the marquee (adds in-circuit clearing-price selection).
- Private OTC/RFQ (§3.11) — the smallest instance; its circuit exists, the app does not.
- Shielded DrEX DEX (§3.13) — the flagship.
- Single-phase shielded launchpad (§3.12 upgrade).

**Gated on a NEW mechanism/circuit (sequence after the AIR proves the pattern):**
- Shielded-Vickrey second-price (§3.4) — the ZK second-max circuit.
- Hidden-reserve Dutch (§3.6) — rides §3.4's comparison primitive.

**Deferred / skip:** English (§3.5 — do not build), true bundle combinatorics (§3.7 — uniform-price multi-unit
suffices), MPC dark pool (§3.14 — only if a persistent shielded book becomes a requirement).

### The top-3 to build (in order)
1. **The reveal-nothing ZK theorem + the deployed-VK fold for the built ring apex**
   (`SHIELDED-DREX-ASSURANCE-ROADMAP.md` components 3/6). The 2-leg and N-leg circuits exist and fix the
   transcript shape `[nf, root, vb]ⁿ`; what converts "built research circuit" into a deployable private
   clearing is the proof that this transcript is simulable from public data alone, plus folding the apex
   under the deployed VK.
2. **The single-phase shielded launchpad** (§3.12 upgrade / §3.3 realized). Carry the built AIR into the
   shipped fair-launch product — the concrete near-term user, whose promise *is* "no operator peek." The
   deployable two-phase version ships today *while* the assurance work runs, so value lands before the
   research finishes.
3. **The shielded-Vickrey second-max circuit** (§3.4) — the truthful single-lot for RWA/NFT, the highest-value
   *new mechanism*. Needs a Lean `runnerUpOf` + truthfulness theorem then the ZK second-max circuit;
   sequence it after (1) proves the clearing-circuit pattern, and let the hidden-reserve Dutch (§3.6) ride the
   same comparison primitive.

---

## 7. The mechanism-design recommendation (from `SHIELDED-AUCTIONS-DESIGN.md §5`)

**Ship uniform-price as the default clearing rule; add shielded-Vickrey as a single-lot specialization later;
do not build MPC for the auction program.** Uniform-price is envy-free, it is the Budish-FBA discipline that
makes sniping and ordering-MEV worthless, and — decisively — **it is the rule dregg has already proved optimal
and no-arbitrage.** Its known weakness (multi-unit demand reduction) is a second-order strategic cost,
acceptable for a batch DEX / launchpad and far outweighed by standing on a machine-checked optimality theorem.
Shielded-Vickrey is the truthfulness upgrade for single-lot RWA/NFT (where DSIC matters, demand-reduction is
moot) — worth doing, but *after* the uniform-price rung-3 AIR proves the clearing-circuit pattern. MPC
re-introduces the committee the ZK fold exists to delete; reserve it strictly for a future persistent dark
pool if that ever becomes a product requirement.

---

## 8. The honest edges (named once, load-bearing)

- **Rung-3's circuit is BUILT; a running private auction is NOT.** The ring-clearing apex proves and
  refuses at both 2-leg and N-leg with the value-commitments-in-AIR fusion enforced — but nothing folds it
  under the deployed VK, no app rides it, the in-circuit clearing-price *selection* is unbuilt, and the
  reveal-nothing ZK theorem (that the transcript leaks nothing beyond roots, fresh nullifiers, and batch
  size) is unproven (`SHIELDED-DREX-ASSURANCE-ROADMAP.md` components 2/3/6). Say "built research circuit,"
  never "running private auction," until those land.
- **Uniform-price optimality is MODEL-PROVED, not ledger-realized.** `Market/Optimality.lean` lives over the
  priced `Fill` model (real ℚ prices) at the single-participant/pairwise core, connected to the kernel only via
  `ofMatchNode`, NOT through `settleRing`. Individual-rationality fairness (`clearing_respects_limits`) IS
  ledger-realized; uniform-price/envy-free is not. Say which. Also NOT k-coalition Shapley-Scarf TTC-core stable.
- **First-price ships; second-price does not exist yet.** dregg proves `winnerOf = max` (first-price). Vickrey
  (§3.4) and hidden-reserve Dutch (§3.6) are DESIGN — neither Lean spec nor circuit exists. Do not imply a
  truthful auction is shippable.
- **The crypto floors are named, not laundered.** Hidden conservation reduces to the DLog `binding` carrier;
  membership to `Poseidon2SpongeCR`; sealed-bid binding to BLAKE3 CR (`Blake3Kernel`). These are `Prop` floors
  the whole tree stands on, not Lean laws — and each is non-vacuous (FALSE for a collapsing hash / linear
  rolling hash, which `RealCrypto.lean` retired). The shielded batch's conservation arithmetic is in-AIR
  with the value coordinate range-gated (a wraparound mint is UNSAT in-circuit), but over the
  two-coordinate `pedTwoGen` abstraction: the real curve-point excess and the blinding coordinate's
  group-scalar reduction ride the off-AIR Schnorr excess — the named faithfulness upgrade.
- **Shielding ≠ perfect anonymity.** Residual leakage: timing, anonymity-set size, and intentional aggregate
  (clearing-price) disclosure. The range-proof anti-inflation rib is discharged in the pool *circuit* (tested
  both polarities); welding that back into the Lean conservation law is the open seam.
- **The launchpad clearing proof is a weld, not yet a binding.** `IClearingAttestor` wires an optional dregg
  Groth16 clearing proof; the on-chain enforcement of *no-snipe/no-late-switch* is real today, but the
  proof-carrying uniform-price clearing is the named rung-2 weld (and any Groth16 rides a dev-ceremony setup,
  not mainnet MPC — a prerequisite, not a detail).

**The precise dreggic claim, everywhere:** not "the perfectly private, perfectly fair auction for everything"
— but **"proven-fair (the clearing is a theorem) and ZK-private where it matters (no operator, no committee),
across the whole auction family, with the remaining trust named, graded, and minimized"** — a claim no
incumbent can make, backed by machinery that is, unusually, mostly already proven or built in the tree.

---

## See also
`docs/deos/SHIELDED-DREX-ASSURANCE-ROADMAP.md` (the successor roadmap: the six assurance components) ·
`docs/deos/SHIELDED-AUCTIONS-DESIGN.md` (the mechanism survey + the ranked shielded primitives) ·
`docs/deos/DREGGFI-VISION.md` (the trust-grade spine + DrEX) · `docs/deos/DREX-DESIGN.md` ·
`docs/deos/DREGG-LAUNCHPAD-DESIGN.md` · `metatheory/Dregg2/Intent/SealedAuction.lean` ·
`metatheory/Market/{Optimality,Fairness,Priced,ShieldedClearing,LedgerRealizationExt,Aggregation}.lean` ·
`metatheory/Dregg2/Shielded/{ClaimRefinement,RealCrypto}.lean` · `circuit-prove/src/shielded/pool.rs` ·
`circuit-prove/src/shielded_ring_clearing_air.rs` · `circuit-prove/src/shielded_ring_clearing_nleg_air.rs` ·
`starbridge-apps/{sealed-auction,gallery,tussle,compute-exchange,escrow-market}/` ·
`chain/contracts/launchpad/DreggLaunchpad.sol` · `intent/src/solver.rs`.

*Grade summary: sealed first-price = PROVED, ledger-realized · uniform-price batch = PROVED (model) / launchpad
on-chain · shielded ZK-sealed uniform-price = PROVED spec + BUILT circuit (2-leg + N-leg), assurance roadmap
open · shielded-Vickrey = DESIGN · hidden-reserve Dutch = DESIGN · combinatorial multi-unit = MODEL-PROVED ·
compute/escrow markets = BUILT · RFQ = circuit BUILT, app unbuilt · DrEX = circuit BUILT / assurance open ·
dark pool = DESIGN/deferred. The frontier is a built, both-polarity-tested ring-clearing circuit whose
reveal-nothing ZK theorem and deployed-VK fold are the named remaining seams — and the whole rest of the
family ships now on the app foundation.*
