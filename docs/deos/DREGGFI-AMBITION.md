# dreggfi — the ambition upgrade (factcheck + the boldest coherent version)

*A proposal to fold into the revised dreggfi plan. Part A factchecks `DREGGFI-VISION.md`
against the real code + the multichain roadmap (skeptic's pass on the PRODUCT/architecture
claims — the 8 core theorems were already verified by the critic-doer). Part B pushes the
vision to the most ambitious coherent version that still survives that factcheck. Every
ambitious claim carries a real primitive cite + a named honest gap. Present-tense, graded.*

---

## PART A — FACTCHECK + GROUND

### A.1 The claim → grounding table

Grades: **GROUNDED** (claim maps to cited real code) · **UNDERSTATED** (real code is *further*
along than the claim credits) · **DRIFT** (claim unbacked / stale / weaker than stated).

| # | VISION claim | verdict | grounding (file:line) / note |
|---|---|---|---|
| 1 | Attenuation-only is a theorem (`attenuate_narrows`/`attenuate_subset`) | **GROUNDED** | `Dregg2/Authority/Caveat.lean:162,170`; `token_discharges:212`. Present, non-vacuous. |
| 2 | Revocation binds at the settlement tip (`settlement_soundness`) | **GROUNDED** | `Dregg2/Circuit/SettlementSoundness.lean:210` (+ `_single_machine:251`). |
| 3 | Solvency-forever ∀-schedule (`stripe_reserve_solvent_forever`) | **GROUNDED** | `Dregg2/Verify/StripeReserve.lean:48`, `#assert_axioms`-clean `:76`. Sibling apexes `stripe_exposure_within_reserve_forever:39`, `stripe_money_in_loss_bounded:58`. **Scope is honest: ONE channel.** |
| 4 | Multilateral clearing conserves + atomic + respects limits | **GROUNDED** | `Dregg2/Intent/Ring.lean:118,147,156`; `Market/Fairness.lean:112` (`clearing_respects_limits`), teeth `overdebit_refused:196`, `wrongAsset_refused:203`; `crossBid_needs_market` in `Intent/Kernel.lean`. Backed by real matcher `intent/src/solver.rs` (Johnson `:244`, Shapley–Scarf TTC). |
| 5 | DrEX rung-1 fairness = individual-rationality only; uniform-price + envy-free/TTC-core UNBUILT | **GROUNDED (minor undersell + a scope caveat to add)** | Accurate that uniform-price optimality + envy-free/TTC-core stability are absent (`Market/Clearing.lean:37-54` names them rung-2/rung-3, "named not claimed"). **Undersell:** rung-1 already proves MORE than the vision lists — `clearing_fair:168` (each participant's own predicate accepts its outcome), `clearing_conserves_per_asset:248`, `exact_clears_iff:285` (a clearing exists IFF offered pool = wanted pool — a *clearability/price-existence-for-exact-books* characterization), and `mint_refused:433`/`unfair_refused:448` teeth. **Scope caveat to ADD (§7):** the per-asset Σ-conservation + `exact_clears_iff` are stated over `DemoRes` — a *discrete two-asset* demo resource theory (gold/art), **exact-book only** (all-or-nothing, no prices, no partial fills). The `MarketClearing` structure/`fair`/`route` are category-general, but conservation + clearability are demo-specific. So uniform-price/envy-free are not just unproven theorems — the *priced/continuous substrate* they need isn't in the module either. What IS proven is genuinely individual rationality, strictly weaker than TTC-core stability (the "Shapley–Scarf" label on `solver.rs`/`cycle_individuallyRational` names the algorithm, not a proven core theorem). Hygiene is real: `#assert_all_clean` over all 14+8 keystones (`Clearing.lean:486`, `Fairness.lean:227`). |
| 6 | Sealed no-peek auctions (`reveal_binds_committed`, `uncommitted_cannot_win`) | **GROUNDED** | `Dregg2/Intent/SealedAuction.lean:248,415`; `#assert_axioms:572,578`; non-vacuous over a real Blake3 CR kernel (`demoCR:476`). |
| 7 | Structural multi-asset shielding (hides value, owner, AND asset) | **GROUNDED** | `circuit-prove/src/shielded/pool.rs`: `HiddenAssetLeg:81` (asset on blinded `H_asset`), homomorphic excess `:32-41`, per-output Bulletproof range proofs `:136-148`, transcript binding `pool_message:217`. Tested both polarities (`circuit/tests/shielded_pool_m2b.rs`). |
| 8 | Tamper-evident receipts + per-asset conservation | **GROUNDED** | `Exec/Receipt.lean:130` (`chain_tamper_evident`), `:255` (`cexec_appends_receipt`); `Exec/MultiAsset.lean:126` (`maExec_conserves_per_asset`). |
| 9 | Refinement-tower method instantiated twice (Deal→ProviderMarket→MarketRefinement; Trustline→StripeReserve→MoneyIn) | **GROUNDED** | `Dregg2/Storage/{DealLifecycle,ProviderMarket,MarketRefinement}.lean`; `Verify/{StripeReserve,StripeMoneyIn}.lean`. |
| 10 | 7-layer trustless batch vs CoW/SUAVE/Anoma | **GROUNDED** | `intent/src/trustless.rs` (3055 lines): COMMIT→…→DECRYPT ceremony `:15-33`, threshold decrypt from `dregg_federation::threshold_decrypt:44`. **Confirms the DrEX honest edge:** the private-matching weld would *delete this DECRYPT committee* (still present today). |
| 11 | Attested data + TEE (SEV-SNP + Nitro verifiers) | **GROUNDED, asymmetric — sharpen §7** | **Nitro is production-grade:** real COSE_Sign1 parse (`lib.rs:155`), full X.509 chain leaf←cabundle←*pinned* AWS root with per-link `verify_signature` (`lib.rs:220`), ES384 COSE verify (`lib.rs:253`), proven against a REAL captured enclave fixture (`tests/data/nitro_att.bin`, 4490 B; `tests/nitro_real.rs`). **SNP is one rung short (honestly):** real 1184-byte parse (`snp.rs:126`) + real ECDSA-P384/SHA-384 body verify over VCEK (`snp.rs:215`) + real chain-structure code (`snp.rs:289`), BUT ships with NO pinned AMD roots (`new()` → `trust:None`, rejects all, `snp.rs:328`), has NO real AMD fixture (all positive tests forge a local `rcgen` PKI), and carries an unresolved question of whether `x509-parser` accepts AMD's RSA-4096-PSS roots (`snp.rs:286`). Fails closed. **§7 addition:** the "ATTESTED lane" is actually TWO mechanisms — the TEE-fact verifier (`deos-hermes/src/tee_fact.rs`, real, tested, exported) is **not yet woven into a live hermes run path** (only its own tests call `install_tee_fact_verifier`); hermes's live attestation crown (`host.rs:389`, `run_hosted_agent_attested`) is the *zkOracle turn-attestation*, a different mechanism. So "attested data leg" = Nitro-real + SNP-fail-closed + a TEE-fact verifier not-yet-live. |
| 12 | "Mandate IS the proof" — expressiveness PROVED, venue-admission needs the caveat-in-circuit weld | **UNDERSTATED** | The mandate is FAR more built than "expressiveness." `metatheory/Dregg2/Agent/Mandate.lean`: `subtree_rights_le_root:194` (transitive no-amplify), `subtree_budget_le_root:301` + `children_no_oversubscribe:282` (budget conservation), `revoke_kills_subtree`, and **`materialize_non_amplifying:227` / `materialize_grants:235`** — the mandate MATERIALIZES into real committed executor kernel steps (`materialize = recKDelegateAtten = execFullA`'s delegate arm), checked INLINE. Rust mirror `intent/src/agent_mandate.rs` (511 lines) emits the exact `Effect::GrantCapability`/`Effect::RevokeDelegation` the verified executor runs. So the *delegation/budget/revocation* half of prime brokerage is PROVED + materialized today. The genuinely-open weld is narrower than §3 states: only the **per-trade caveat-admission** (the aggregate `caveatBit` that "trusts the executor's decision", `Caveat.lean:59`) is not yet reified in-circuit. |
| 13 | Refinement seam is load-bearing; executor↔abstract only via `_refines_` | **UNDERSTATED (for the ring)** | `intent/src/verified_settle.rs` (985 lines) routes the LIVE ring through the **real Lean FFI executor** (`@[export] dregg_record_kernel_step` over proved `Exec.recKExec`), leg-by-leg all-or-nothing — "an intent fulfilled LITERALLY MEANS a verified, conserving, authorized executor turn executed" (`:1-25`), NOT a Rust mirror. `RingFFI.ffi_export_realises_settleRing_leg` proves the export realises the leg. So the ring's executor-refinement is CLOSED via FFI; the *slash-leg* alignment (`MarketRefinement`) remains the open instance. §7's blanket "verified by prose" undersells the ring. |
| 14 | Cross-chain settle-anywhere: EVM-outbound + Solana-inbound REAL (dev-ceremony) | **GROUNDED, with a sharper altitude** | EVM outbound is real end-to-end: real Groth16 settles on-chain (Foundry 7/7), 25-lane state root bound to the verified apex, both shrink+apex VK pinned, circuit 4.98M, setup cached, GPU prover 6.6× (HORIZONLOG 07-13). The **wrap works end-to-end on real data** (real apex → BN254-native shrink → gnark `VerifyFriNative`). **Altitude correction for the "runnable cross-chain vote":** `dregg-interchain-gov` runs real verifier *code*, but the single test that completes a bound-and-tallied 3-chain vote runs over fixture/round-trip data (Solana self-cluster, EVM synth-trie with `FinalizedExecution::new_unchecked` finality stub, Cosmos `consensus_proven:true` fixture verdict); the *genuine* mainnet proofs (WETH `eth_getProof`, cosmoshub-4 180-validator ICS-23) run in a **separate** test that stops at the non-custodial `UnboundOwner` tooth (no wallet key). **No single test proves-AND-binds-AND-votes a live-mainnet holding.** Nothing is silently mocked; the crate is candid. |
| 15 | §7 honest edges complete (oracle exogenous; trusted setup; refinement seam; caveat expressiveness; shielding≠anonymity; fairness partly proven; Solana M-of-N) | **GROUNDED + one addition** | All six edges verified real. **Add a 7th, from #14:** the interchain governance demo's complete-vote path is fixture/round-trip, not live-mainnet-consensus-bound — the honest edge is "real verifier code; end-to-end vote not yet over live-mainnet-proven holdings on all 3 chains simultaneously." Belongs in §7. Also worth surfacing: the shielded pool is "**not woven into `effect_vm`**" (`shielded/mod.rs:47`) — §7 mentions the range-rib weld but not this structural seam explicitly. |

### A.2 The true current altitude

**No product/architecture claim in `DREGGFI-VISION.md` is DRIFT (overclaimed).** The vision is
unusually well-grounded — the skeptic's finding is the *opposite* of drift: **the vision
UNDERSELLS its own altitude in two load-bearing places (#12, #13) and slightly in a third (#5),
and needs one honest edge added (#14/#15).**

Net altitude, stated plainly:

- **The capability spine is deeper than "expressiveness."** Non-amplification, budget
  conservation, and revocation are proven for the *whole delegation tree* AND materialize into
  committed executor effects. Prime brokerage's authority model is PROVED + wired, not aspirational.
  Only per-trade in-circuit caveat admission is open.
- **The ring already touches the verified executor** through real Lean FFI (`verified_settle.rs`),
  not prose. DrEX rung-1 is not just "theorems on paper" — it settles through the proved kernel.
- **The wrap is DONE end-to-end on real data** (the roadmap's marquee). A real dregg apex shrinks
  BN254-native and a gnark gadget verifies it; EVM settlement lands on-chain (Foundry). This is the
  single biggest thing "further along than the vision credits" — the vision §3 cross-chain grade
  says "unified-position logic is new build" but does not convey that the *settlement rail itself*
  is empirically validated end-to-end.
- **The shielded pool is real and structurally complete** (value+owner+asset hidden, homomorphic
  conservation, range proofs) but stands beside `effect_vm`, not inside it — the marquee DrEX weld.
- **Honest gaps confirmed real (and a few to ADD to §7):** threshold-DECRYPT committee still in the
  batch; Groth16 single-party dev ceremony; caveat `caveatBit` trusts the executor; **Nitro TEE is
  real+fixture-proven but SNP ships no AMD roots / no real fixture, and the TEE-fact verifier isn't
  woven into a live hermes lane** (add to §7); Solana settle is M-of-N attested; **solvency is
  single-channel over cleartext integers**; **the market conservation/clearability theorems are over a
  discrete two-asset exact-book `DemoRes`, no prices/partial-fills** (add to §7); the complete
  cross-chain vote is fixture/round-trip, not live-mainnet-bound (add to §7).

**Where dreggfi sits in the broader dregg arc:** dreggfi is not a new limb. Every dreggfi
primitive is a *financial reading* of a dregg core object that already exists for other reasons:
the turn+receipt (settlement/federation), the attenuable biscuit (the capability core), the
multilateral ring (intent settlement), StripeReserve (the storage/deal market), the shielded pool
(privacy), the recursion leaf-adapters (the universal fold), and the cross-chain wrap (multichain
settlement). dreggfi is the point where these converge on money. That is the upgrade thesis of
Part B: **stop treating dreggfi as a suite of four products bolted onto dregg; treat it as what
dregg's core already IS, viewed financially.**

---

## PART B — THE MOST AMBITIOUS DREGGFI (grounded, bold)

### B.1 The endgame frame: dreggfi is a proof-carrying financial *substrate*, not a product suite

The strongest unifying frame — and the one the code actually supports — is this:

> **dreggfi is the financial instantiation of the dregg turn. Every economic fact is a graded
> proof, every position is an attenuable capability over owned state, every settlement is an
> atomic multilateral clearing that conserves, and every product's proof is a recursion leaf in
> the next product's proof. There is no trusted operator, oracle, committee, sequencer, bridge, or
> counterparty anywhere in the stack — only proofs, attestations, and replayable public functions,
> each carrying its grade.**

This is not a metaphor — it is a *typing*. The memory through-line ("a turn = the exercise of an
attenuable proof-carrying token over owned state, leaving a receipt") IS the definition of a
financial position under this frame:

| dregg core object (real, cited) | financial reading |
|---|---|
| attenuable biscuit + `Mandate` (`Agent/Mandate.lean`, `agent_mandate.rs`) | a margin mandate / position ownership / prime-broker sub-account |
| the turn + `chain_tamper_evident` receipt (`Exec/Receipt.lean:130`) | a trade + its immutable settlement record (the track record) |
| multilateral ring clearing (`Ring.lean`, `Market/Clearing.lean`) | the DEX / central clearing house |
| `stripe_reserve_solvent_forever` (`StripeReserve.lean:48`) | the money-market / stablecoin backing invariant |
| the shielded pool (`shielded/pool.rs`) | the private book / dark pool (value+owner+asset hidden) |
| sealed auction (`SealedAuction.lean`) | primary issuance / batch clearing |
| cross-chain proof-of-holdings + wrap (`chain/gnark`, light clients) | prime-brokerage collateral spanning venues; settle-anywhere |
| nullifier accumulator (`Exec/NullifierAccumulator.lean`) | the no-double-spend / no-rehypothecation gate |
| guarded holes / partial turns / promises (partial-turn project) | derivatives, forwards, conditional orders, structured products |
| recursion leaf-adapters (`circuit-prove/src/*_leaf_adapter.rs`) | composability: one instrument's proof folds as another's input |

The frame's payoff: it converts "build four products" into "expose the financial face of one
already-proven substrate, and wire the welds between faces." It also tells you the *unit of
ambition*: not a bigger product, but a deeper **composition** — because the leaf-adapter fabric
means dreggfi products are recursively composable in a way no other DeFi stack can be.

### B.2 The ranked ambitious upgrades (novel primitives dregg's COMBINATION unlocks)

Ranked by ambition × groundedness. Each names its real primitive and its honest gap.

**#1 — Recursive / composable dreggfi: the proof-carrying structured product ("everything is a leaf").**
*The single most dreggic upgrade, because it is the one NO other stack can copy.* dregg already has
a working recursion-fold fabric of leaf adapters — `deco_leaf_adapter.rs` (a zkTLS/Stripe payment
commitment folded in-AIR), `note_spend_leaf_adapter.rs`, `mpt_holding_leaf.rs` (an EVM-MPT holding
commitment), `blinded_membership_leaf_adapter.rs`, `bridge_leaf_adapter.rs`, `custom_leaf_adapter.rs`,
all composed by `joint_turn_recursive.rs` / `recursive_witness_bundle.rs` — and the wrap that shrinks
an apex of these is *confirmed end-to-end on real data*. The upgrade: a **structured product is a
single apex proof that folds N sub-proofs as leaves** — e.g. a private collateralized note = fold of
{a shielded note-spend proof} ⊕ {a `stripe_reserve` solvency proof} ⊕ {an `mpt_holding` proof of
cross-chain collateral} ⊕ {a `clearing_respects_limits` proof} → one apex a venue verifies once, on
any chain. Every economic fact in the instrument is a proof, and the instrument's *own* proof is
reusable as a leaf in a fund-of-funds above it. *Grounding: the leaf-adapter fabric + the confirmed
apex→shrink→gnark wrap (HORIZONLOG 07-13). **Solvency-as-a-leaf now landed** (`solvency_leaf_adapter.rs`:
INSTANCE `R ≥ L` via a 30-bit range gadget + two committed openings, re-proven as a foldable IR-v2
leaf; it composes with the ∀-schedule `stripe_reserve_solvent_forever` by CITATION — the leaf proves a
given state IS solvent, the Lean theorem proves the state STAYS solvent — it does NOT re-prove the
∀-schedule in-AIR), and `prove_structured_product_fold` folds {note-spend ⊕ solvency} into one apex
that verifies both (both poles re-run green: insolvent/forged-commitment ⇒ UNSAT, honest ⇒ mints). Gap:
clearing-as-leaf is not yet written as an adapter, and a Lean spec of the composed instrument's
soundness. This is a build, not new science — the fold machinery works today.*

**#2 — Private, capability-scoped, cross-chain prime brokerage with an unconstructable mandate breach.**
The convergence product the vision names in §3 as "the single most dreggic idea" — raised. A
manager's *entire* authority is a `Mandate` (proven non-amplifying + budget-conserved + revocable-
at-tip, `Agent/Mandate.lean:194,301`, materialized into committed executor effects `:227`), whose
collateral is proof-of-holdings across Solana/EVM/Cosmos (`bridge/`, light clients), trading over
the **shielded pool** (no operator sees the orders), settling by proof on any chain (the wrap). No
party ever holds the plaintext orders, the custody, or the mandate-widening key — a mandate breach
is *unconstructable*, not monitored. *Grounding: #12/#13 above (mandate proved + materialized; ring
through Lean FFI) + shielded pool + wrap. Gap: (a) per-trade caveat-admission in-circuit (`Caveat.lean:59`)
— the DECIDABLE-atom slice now landed (`caveat_admission_leaf_adapter.rs`: `validUntil`/`heightLt`/`budget`
`≤`/`<` over u128-scale bignum operands by a range-checked limbwise borrow-subtraction + a limbwise
asset-equality, teeth re-run green: past-expiry/over-budget/over-height/wrong-asset ⇒ UNSAT; Lean model
`Dregg2/Circuit/CaveatBignumCompare.borrowSub_iff`, a `sorry`-free soundness+completeness biconditional);
the un-reified `Caveat.opaque`/`Caveat.thirdParty` atoms stay executor-trusted, and the deployed trade
descriptor must still DUAL-EXPOSE the `(trade fields ++ caveat params)` limbs to bind this leaf (the named
VK-regen piece); (b) ring-over-shielded-notes weld (DrEX rung-3); (c) the "one position, collateral proven
across 3 chains simultaneously" logic is new — and per #14, no test yet binds a live-mainnet holding end-to-end.*

**#3 — The shielded solvency-proven money-market (private AND provably-never-insolvent).**
`stripe_reserve_solvent_forever` proves `reserve ≥ liabilities` over *every* schedule (∀-adversary),
but on a *clear* single channel. The shielded pool proves per-asset conservation over *hidden*
Pedersen commitments via a homomorphic excess proof (`pool.rs:32-41`). Fuse them: a money-market
where deposits and loans are shielded notes and the solvency invariant `Σ reserve ≥ Σ liabilities`
is proven **over the hidden aggregate** (the homomorphic sum), so the market is simultaneously
private and provably-never-insolvent — the anti-Terra/anti-Iron-Finance object AND a dark pool that
*cannot lie about its book*. *Grounding: `StripeReserve.lean:48` + `shielded/pool.rs` homomorphic
conservation. Gap: solvency is proven per-channel over cleartext; lifting to a portfolio AND to the
hidden aggregate (prove `reserve ≥ liabilities` over Pedersen sums, not integers) is the weld — a
range/comparison argument over commitments. Named, not trivial.*

**#4 — Solvency-as-a-feed: proof-of-solvency as a first-class, subscribable, composable market datum.**
Invert the oracle problem. Instead of *trusting* a price feed, a venue continuously *emits a PROVED*
`reserve ≥ liabilities` proof (grade PROVED, not ATTESTED — it's a theorem-instance, not a hardware
root), which other dreggfi products fold in as a **leaf** (#1) before extending credit to it.
Counterparty risk becomes a proof you verify, not a rating you trust. *Grounding: `StripeReserve.lean`
+ OCIP's graded-emission discipline + the leaf-adapter fabric. Gap: continuous per-epoch proof
emission + a subscription/registry surface; the solvency proof must be cheap enough to emit
per-epoch (the wrap's 17.7s prove / GPU 6.6× makes this plausible but unmeasured for this shape).*

**#5 — Cross-chain atomic multilateral clearing (the settle-anywhere clearing house).**
Today's ring clears within one ledger. The upgrade: a *single* multilateral cycle whose legs settle
on *different* chains, atomically, each leg's settlement checked by that chain's own verifier via the
wrap — a clearing house with no chain-of-convergence and no bridge honeypot. *Grounding:
`settleRing_atomic` (`Ring.lean:147`) + the field-parameterized wrap (`dregg_outer_config.rs`) verified
on EVM. Gap: cross-chain atomicity (a leg failing on chain B must roll back the leg on chain A) needs a
commit/abort protocol across verifiers — the hardest coordination piece; Ring.lean's atomicity is
single-machine. Multi-month; a real distributed-commit design problem, honestly.*

### B.3 The moonshots (impossible-sounding; honestly rated)

- **Mathematically-unconstructable systemic collapse.** A market where every leveraged position's
  solvency is a live ∀-adversary proof, so a Terra/FTX/Iron-Finance-shaped collapse has *no
  constructor* at the substrate. *Feasibility: RESEARCH.* The ∀-schedule solvency object exists
  (`StripeReserve.lean:48`) but only per-channel/cleartext; portfolio + mark-as-proof + the hidden
  aggregate (#3) are each welds, and "the mark is itself a proof" is the deepest one (§7 oracle edge).
  The object is real; the reach is multi-weld.

- **A cross-chain shielded CLOB with no operator/committee/sequencer holding plaintext or ordering
  power, at usable latency.** *Feasibility: MULTI-MONTH → RESEARCH.* The private-matching custom
  circuit (ring over shielded notes) is DrEX rung-3, "the epoch weld"; uniform-price fairness is
  unbuilt (rung-2); and matching over hidden orders *fast enough for a CLOB* is a perf frontier even
  with the wrap+GPU 6.6×. Grounded in real pieces (shielded pool, ring, sealed auction, the DECRYPT
  committee it would delete), but the composition + latency is genuinely open.

- **The everything-is-a-leaf portfolio: one apex proof for an entire book's correctness, verified
  once on any chain.** *Feasibility: REACHABLE-WELD → MULTI-MONTH.* This is #1 scaled: the fold
  machinery works end-to-end today (real apex shrunk BN254-native, gnark verifies — HORIZONLOG
  07-13), so the *mechanism* is proven; wiring the financial leaves and bounding the recursion depth/
  prove-time for a realistic portfolio is the build. The most "impossible-sounding thing that is
  actually closest," because the recursion rail already carries real proofs.

- **Self-custodial prime brokerage that a regulator can verify without trusting the broker.** A
  supervisor verifies the mandate-non-amplification proof + the solvency proof + the receipt chain —
  never trusting the broker's books, never seeing the client's positions (shielded). *Feasibility:
  MULTI-MONTH.* Every piece is grounded (#2, #3, #4); it is a productization + the per-trade
  caveat-in-circuit weld, not new science. The boldest *deployable* moonshot.

### B.4 The boldest coherent 12-month arc (all-in on dreggfi)

Spine: **make DrEX the substrate, and make composition the product.** Sequenced so each quarter
ships something real and de-risks the next.

- **Q1 — Close the capability weld + finish rung-1→2.** Reify per-trade caveat-admission in-circuit
  (`caveatBit` → a real constraint), turning "mandate IS the proof" from UNDERSTATED-#12 into a
  venue-verified admission. Ship DrEX rung-2 (order-book aggregation soundness, reusing the
  `ChainBound` no-drop/no-insert/no-reorder discipline, `Clearing.lean:37`). `verified_settle.rs`
  already routes the ring through the Lean FFI — light it up as live conserving settlement. *Ships:
  the mandate-as-proof prime-brokerage MVP over a clear book.*

- **Q2 — The private-matching weld (the marquee).** Ring over shielded notes: the custom
  private-matching circuit atop `shielded/pool.rs`, deleting the `trustless.rs` DECRYPT committee.
  *Ships: DrEX — private + fair without trusting any operator/committee/sequencer.*

- **Q3 — Solvency lift + cross-chain unified position.** Lift `stripe_reserve` to a portfolio and to
  the hidden aggregate (#3) → the shielded solvency-proven money-market; and land the unified
  cross-chain position (collateral proven across ≥2 chains, settle by proof — the wrap is done). Fix
  the #14 gap: one test that proves-binds-votes/settles a *live-mainnet* holding end-to-end. *Ships:
  the private money-market + settle-anywhere collateral.*

- **Q4 — Recursive composition (the thing only dregg can do).** Wire the first proof-carrying
  structured product (#1) as a fold of {solvency ⊕ holdings ⊕ shielded-clearing} leaves via the
  existing adapter fabric — one apex, verified once, settling cross-chain; then a fund-of-funds that
  folds *it*. *Ships: the composable-dreggfi demonstrator — the moat.*

**North star beyond the arc:** a proof-carrying financial substrate on which a Terra/FTX is
*unconstructable*, every position is a private attenuable capability, every economic fact is a
graded proof, and any chain can verify any dreggfi fact by checking one recursively-composed proof —
with the residual trust (trusted setup → production MPC; the mark → a ZK witness; the TEE root)
named, graded, and driven toward zero. The precise claim, everywhere and unchanged from the vision's
discipline: **not "perfectly private, fair, solvent" — but "private, fair, and solvent *without
trusting any operator, committee, sequencer, bridge, or counterparty*, with the remaining trust
named, graded, minimized — and now COMPOSABLE, because each product's proof is the next one's input."**

---

## See also
`DREGGFI-VISION.md` (the base) · `INTERCHAIN-MODEL.md` · `GOAL-MULTICHAIN-SETTLEMENT.md` +
`HORIZONLOG.md` (the wrap, done end-to-end) · `metatheory/Dregg2/Agent/Mandate.lean` ·
`metatheory/Market/Clearing.lean` · `intent/src/{agent_mandate,verified_settle,trustless,solver}.rs` ·
`circuit-prove/src/shielded/pool.rs` + `circuit-prove/src/*_leaf_adapter.rs` · `tee-verify/src/snp.rs`.
