# dreggfi — the most dreggic DeFi possible

*Synthesis of four scholar-ideator studies (capability-native · provable-soundness · shielded-fair-markets · cross-chain), grounded in dregg's real, cited primitives and the OCIP attested-data plan. Present-tense, what-is. Every claim carries a trust grade (below). Nothing here is a roadmap promise; the honest edges are named in §7.*

## 0. The thesis, and why it's a *lift* not a greenfield

Normal DeFi is "trust the contract + the oracle + the liquidator + the solver + the bridge." **dreggfi replaces each of those trust points with a proof.** The four ideation lenses converged on one fact: the hard primitives **already exist and are proven** in the tree. dreggfi is not new science — it is a *lift* of proven machinery, with a small number of clearly-named welds.

What already exists, cited:
- **Attenuation-only is a theorem** — `attenuate_narrows`/`attenuate_subset` (`Dregg2/Authority/Caveat.lean:162,170`): a delegated key can *only* shrink authority. Authority **is** a verification witness (`token_discharges`), off-island-verifiable via the biscuit split.
- **Revocation binds at the settlement tip** — `settlement_soundness` (`Dregg2/Circuit/SettlementSoundness.lean:210`) + `revokedPersists` (`Verify/Catalog.lean`): closes the revocation-race hole every capability system leaves open.
- **Solvency-forever** — `stripe_reserve_solvent_forever`: the reserve is never negative over **every** schedule (`Verify/StripeReserve.lean:45`) — a ∀-adversary solvency theorem, the anti-Iron-Finance/anti-Terra object.
- **Multilateral clearing conserves + is atomic** — `settleRing_conserves` + `settleRing_atomic` (`Dregg2/Intent/Ring.lean`), backed by the real matcher (`intent/src/solver.rs`: Johnson's circuits + Shapley-Scarf top-trading-cycles). `crossBid_needs_market` proves you *need* the multilateral market.
- **Sealed no-peek auctions** — `reveal_binds_committed`, phase-gate, `uncommitted_cannot_win` (`Dregg2/Intent/SealedAuction.lean`), non-vacuous over the real Blake3 CR kernel.
- **Structural multi-asset shielding** — `circuit-prove/src/shielded/pool.rs`: hides value, owner, *and* asset; homomorphic excess proof enforces per-asset conservation *while the asset stays hidden*; range proofs close inflation; tested both polarities.
- **Tamper-evident receipts** — `chain_tamper_evident`, `cexec_appends_receipt` (`Exec/Receipt.lean`); per-asset conservation `maExec_conserves_per_asset`.
- **The refinement-tower METHOD, instantiated twice** — `DealLifecycle→ProviderMarket→MarketRefinement` and `Trustline→StripeReserve→StripeMoneyIn`. dreggfi lifts this pattern onto exchange/lending/synthetics.
- **A 7-layer trustless batch** (`intent/src/trustless.rs`) that compares itself to CoW/SUAVE/Anoma.
- **Attested data + TEE** — `tee-verify` (AMD SEV-SNP + AWS Nitro report verifiers), `deos-hermes/tee_fact.rs`, `zkoracle-prove`, `dregg_cell::tee_attest`; the OCIP plan's attested lane.

## 1. The trust-grade spine (from OCIP — the honesty framework that IS the brand)

Every dreggfi claim carries exactly one grade. This is not marketing hygiene — it is the differentiation. "Verified/audited/secure" blurred into paste is the incumbent move; grading is ours.

| grade | means | you still trust |
|---|---|---|
| **PROVED** | a machine-checked theorem about the deployed artifact (e.g. splitter conservation; `settleRing_conserves`) | the proof checker + named cryptographic assumptions |
| **ATTESTED** | a hardware-rooted attestation (TEE — SEV-SNP/TDX/Nitro) or a zkTLS provenance proof that data came from a named origin | the HW vendor's root + side-channel residual (why it isn't "PROVED") |
| **REPLAYABLE** | a pure function over public data; anyone re-derives with one command (e.g. a ranking list) | nothing but your own machine + the public chain |

Every badge, API header, and doc claim in dreggfi carries its grade. §7 below grades the whole vision.

## 2. The recurring pattern: the weld is always "force it in-circuit at settlement"

All four studies independently hit the *same* north-star shape. The primitive **expresses** the guarantee today; the north-star **forces it in-circuit at settlement** so a counterparty verifies it as a proof rather than trusting the executor:
- capability: `Caveat.lean` binds an aggregate `caveatBit` and *trusts the executor's decision* — the weld is forcing the caveat policy in-circuit (its own named honesty edge).
- shielded markets: the ring settles over the **clear** ledger; the shielded pool is "not woven into `effect_vm`" (`shielded/mod.rs:47`) — the weld is clearing over shielded notes.
- soundness: solvency is proven *given the mark*; the weld is making the price a **proof-carrying witness** (the oracle edge).
- cross-chain: settlement verifies on a **dev-ceremony** Groth16 — the weld is the production MPC.

**One pattern, four instances. Naming it is the map: expressiveness exists; the in-circuit-at-settlement soundness + the input-integrity are the frontier.** And the input-integrity half is exactly what the ATTESTED lane (TEE/zkTLS, OCIP) and the interchain proof-carrying holdings provide.

## 3. The convergent product suite (best-of the four lenses)

### Capability-native — **"The mandate IS the proof"** (the single most dreggic idea overall)
A prime-brokerage sub-account where the manager's *entire authority* is an attenuated biscuit — "trade up to $X, assets/venues {…}, until block Y, **no withdrawals**" — and every trade carries the proof it lies inside the mandate, checked by the settling venue itself. Collapses all five gaps no existing system closes together: cryptographically-scoped (caveats, not a legal clause), attenuable-**with-a-proof** (`attenuate_narrows`), revocable-**without-racing** (`settlement_soundness` at the tip), self-enforcing-at-settlement (`token_discharges`), receipt-as-track-record (`chain_tamper_evident`). **A mandate breach is *unconstructable*, not monitored** — it annihilates the counterparty-trust premise of prime brokerage. *Grade: expressiveness PROVED today; venue-verified admission needs the caveat-in-circuit weld.*

### Provable-soundness — **Proof-of-Solvency-Forever unit**
A synthetic/stablecoin whose *backing* invariant and *supply* invariant are BOTH theorems over the ∀-schedule adversary: `reserve ≥ liabilities` for every schedule (`stripe_reserve_solvent_forever`, proven for one channel) ∧ every unit minted is a disclosed spec-authorized turn (`execMintA_iff_spec_satisfiable`). Makes **both** billion-dollar archetypes unconstructable: Terra's unbacked reflexive mint (issuance bounded by *real* reserve, not a reflexive option on the protocol's own token) and Iron Finance's fractional bank run (`R−settled ≥ 0` every schedule → no par-shortfall state). Sibling: **undercollateralization-impossible lending** (the "liquidatable-but-can't-repay" bad state has no constructor). *Grade: single-channel solvency PROVED; portfolio + mark-as-proof is the lift.*

### Shielded-fair-markets — **The Shielded Multilateral Clearing House** (this is DrEX; see §4)
A market where matching happens **inside the proof over hidden commitments** — no operator peeks, no committee decrypts, no sequencer reorders. The intersection P1(shield) ⊗ P2(ring clearing) ⊗ P3(sealed no-peek) ⊗ P4(causal anti-frontrun) that *only dregg holds together*. Beats CoW (orders visible to solvers), Penumbra (validator flow-decryption), Shutter (Keyper committee), and dark pools (operator can peek) — because there is **no instant and no party** that holds the plaintext or the ordering power. *Grade: pieces PROVED separately; the weld is ring-over-shielded-notes + the uniform-price fairness theorem.*

### Cross-chain — **The settle-anywhere unified position**
One position whose collateral is proven simultaneously across Solana + EVM + Cosmos, that opens/margins/settles against *any* chain's verifier, with no asset leaving the wallet it lives in and no trusted party anywhere. **A bridge structurally cannot build this**: a bridge's only verb is move-the-token, so it must converge assets onto one chain — and the convergence is the honeypot (Ronin *was* the vault). dregg's atomic unit is *proving a state transition* that *references* holdings proofs; nothing converges. The field-parameterized shrink means "settle anywhere" is one design, not N integrations. *Grade: EVM-outbound + Solana-inbound REAL (dev-ceremony); Mina GO; Cosmos landing; unified-position logic is new build.*

## 4. DrEX — Dragon's EXchange (the marquee, where they converge)

DrEX is the Shielded Multilateral Clearing House realized as a proof-carrying exchange, with the other three lenses composed in. Its proof stack, honest per rung:

1. **Execution soundness** — the multilateral clearing conserves per-asset + is atomic. *`Ring.lean` PROVED.* Plus the **fairness theorem** (uniform-price / envy-free clearing) — the one genuinely-unbuilt piece (conservation ≠ fairness); the first `metatheory/Market/` rung.
2. **Order-book aggregation soundness** — the aggregated book faithfully represents submitted orders (no drop/insert/reorder, priority respected); composes with the `ChainBound` unfoolable-history discipline. *To build.*
3. **Private DrEX via a custom ZKP** — the marquee weld: the ring matcher clears over **shielded notes** (not the clear ledger), so matching happens over hidden commitments — the custom private-matching circuit atop the shielded pool + AIR layer. Deletes the `trustless.rs` DECRYPT committee entirely (nothing to decrypt). *The epoch weld.*
4. **Capability-native order flow** — orders/mandates as attenuable biscuits (§3 capability).
5. **Provable solvency** — the venue/LP reserve is solvent-forever (§3 soundness).
6. **Cross-chain settlement** — a DrEX fill settles on any chain by proof (§3 cross-chain).
7. **Attested market data** — prices/marks/security-flags carried with a trust grade via the ATTESTED lane (§5) — the oracle-integrity leg.

DrEX's claim, precise: **private and fair without trusting any operator, committee, or sequencer** — with the remaining leakage being timing, anonymity-set size, and intentional aggregate (clearing-price) disclosure. No dark pool, encrypted mempool, or batch-auction DEX can make that claim.

## 5. OCIP — the near-term product + the oracle-integrity leg

The **Open Contract Intelligence Platform** (attested DEX screener/terminal + fair attention market, `~/Desktop/ocip-plan-v3.pdf`) is both a near-term revenue product *and* the piece every dreggfi product needs. Its **ATTESTED lane** (TEE-rooted attestations + zkTLS provenance for off-chain sources — "verify their response," not "trust our servers") is the **oracle/data-integrity solution**: dregg's ZK proves the *logic*; the attested lane provides trustworthy *inputs* (prices, marks, security flags) carried with a grade. Its PROVED money-paths (revenue splitter conservation, fee router "exactly once") and its **bonded-not-boosted attention market** (promotion posts a conduct bond, slashed on mechanical on-chain misconduct predicates, slashes compensate *holders* never the platform) are themselves dreggfi products. OCIP funds the vision and de-risks the substrate in public. *Grade: money-paths PROVED, ranking REPLAYABLE, data lane ATTESTED — graded per claim, which is the whole pitch.*

## 6. The honest build ladder

1. **Now (unblocked, composing on proven pieces):** the DrEX rung-1 **fairness theorem** (`metatheory/Market/`, composing with `Ring.lean`); the cross-chain governance demo; OCIP's attested lane + money-paths.
2. **Then:** the DrEX **private-matching weld** (ring over shielded notes) — the marquee; the **caveat-in-circuit** weld (mandate-as-proof); the portfolio **solvency lift**.
3. **Alongside:** the interchain rung-3 (Mina Pasta build; Cosmos outbound; the price-as-proof-carrying-witness that pulls the oracle into the model).
4. **Gated on ember (outward):** production MPC ceremony; mainnet; the provably-fair native-token mirror.

## 7. The honest edges (named once, plainly — this section is load-bearing)

- **Oracle inputs are exogenous.** Solvency/lending theorems are *conditional on the mark*. The ATTESTED lane (TEE/zkTLS) and proof-carrying holdings pull inputs into the model, graded ATTESTED (HW-vendor trust) not PROVED — until the price is itself a ZK witness.
- **Trusted setup.** On-chain enforcement rides a Groth16 verifier on a **single-party dev ceremony (toxic-waste-known), not mainnet MPC.** A prerequisite, not a detail.
- **The refinement seam is load-bearing.** A theorem about the abstract protocol binds the executor only through a `_refines_` theorem. `MarketRefinement` proves the claim leg; the **slash-leg alignment is still open** (in-file). Every dreggfi product needs its own refinement.
- **Caveat policy is expressiveness, not yet soundness.** The circuit binds an aggregate `caveatBit` and trusts the executor's decision (`Caveat.lean` says so itself). "dregg can express this mandate" is true today; "the venue verifies it as a proof" is the weld.
- **Shielding ≠ perfect anonymity.** Timing, anonymity-set size, and edge graph-analysis leak; the range-proof anti-inflation rib is named-open (`Conservation.lean:51`) — ship the private version only once closed.
- **Fairness is unproven today.** dregg proves conservation + atomicity, not uniform-price optimal clearing. Until that theorem lands, "fair" is an architecture claim, not a verified one — say which.
- **Solana asset-lock is M-of-N oracle-attested**, not proof-carrying (the trustless successor is built to `ConsensusVerified`, not live).

The precise dreggic claim, everywhere: **not "perfectly private, perfectly fair, perfectly solvent" — but "private, fair, and solvent *without trusting any operator, committee, sequencer, bridge, or counterparty*, with the remaining trust named, graded, and minimized."** That is a claim no existing DeFi system can make — and the machinery to back it is, unusually, mostly already proven in the tree.

## See also
`INTERCHAIN-MODEL.md` · `metatheory/Dregg2/Intent/{Kernel,Ring,SealedAuction}.lean` · `Dregg2/Authority/Caveat.lean` · `Dregg2/Verify/StripeReserve.lean` · `circuit-prove/src/shielded/pool.rs` · `~/Desktop/ocip-plan-v3.pdf` · `GOAL-MULTICHAIN-SETTLEMENT.md`. The four full ideator studies are the source; this is the synthesis.
