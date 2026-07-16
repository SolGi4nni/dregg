# FORWARD-CAMPAIGN-2026-07 — the four tracks, why, and in what order

*The synthesis a newcomer reads to understand where dregg is going. It ties together four
concurrently-designed tracks into one campaign map: the through-line, each track's current
resolution with citations, the target, the staged rungs, the dependency spine, a recommended
sequencing, and what would make the whole thing credible to an outsider. Current-state claims
carry maturity labels — **RUNS** (a test or demo exercises it green), **BUILT** (real code, not
driven end-to-end live), **NAMED** (stub/doc/residual), **VISION** (design only) — and cite
`file:line`/doc at HEAD (2026-07-16). Sibling designs: Track D =
`docs/reference/REPRODUCIBLE-BUILD-AND-FREEZE.md` (being authored), Track B =
`docs/reference/FRI-CUTOVER-PLAN.md` + `docs/reference/FRI-EXTRACTION-FLOOR-DESIGN.md` (written),
Track A = `docs/deos/INTERCHAIN-LIVE-CAMPAIGN.md` (being authored), Track C =
`docs/deos/PROTOCOL-NATIVE-ECONOMY.md` (being authored).*

## 1. The through-line, in one paragraph

The 2026-07-15 launch-readiness audit named one disease under four axes: **the real system is
green on ember's laptop, not in a frozen, reproducible, deployed artifact** (`HORIZONLOG.md:141`).
The math is strong; the gap is engineering discipline and scope focus. The four forward tracks are
the four cures, and they are not independent: **D** puts the system somewhere other than one
laptop and freezes what it is (the meta-enabler — every other track's "deployed" claim is a lie
until D lands); **B** sharpens the proof from a 57.98-bit calculator artifact to a proven-122.60
configuration and grounds the one still-assumed soundness leg, so that when D freezes a VK it
freezes the *strong* one; **A** turns the interchain story from fixture-clusters and a local test
validator into a real mainnet consensus feed, so a holding or a lock references value that
actually exists; and **C** turns the token economy from "RUNS on mock chains" into protocol-native
payments that move real value, gated behind everything above. The campaign is the order in which
those cures compose without wasting a re-key or shipping a frozen artifact we would immediately
want to unfreeze.

## 2. Current resolution — the four tracks, each with its maturity and next rung

### Track D — off-laptop + freeze (the meta-enabler)

**Maturity: NAMED, with the first reproducibility fixes landed.** The audit's P0 is a reproducible
build: the root `Cargo.toml` still `[patch]`-points crypto deps at sibling checkouts while its own
comment claims "pure git deps"; the four `p3-*` git revs, the `emberian/*` forks, and a rolling
`nightly` toolchain are not all pinned to one pushed immutable commit; there is no bare-clone-into-
empty-`~/dev` CI gate, so "works on my machine" can regress silently (`HORIZONLOG.md:146`). Done
this session: the p3 fork was pushed, workflow clone revs bumped `993efec→0a4a554`, and the staged
TSV LFS-tracked so Pages goes green (`HORIZONLOG.md:151`). P1-freeze is the protocol-side twin:
production MPC VK ceremony pinned as a hex KAT constant (killing the self-recompute tautology at
`recursive_witness_bundle.rs:180`), one `v-final` descriptor registry retiring the 7-registry
churn and the lying `-staged` names, the commitment context/width flip finished, Control-4 (the
non-regression differential, design-only at `VK-REGEN-CONTROLS.md:92`) built, and a deterministic
published genesis (`federation_id` is non-deterministic today) — done *now, while no community
state exists* (`HORIZONLOG.md:152`). **Next rung:** drop the sibling `[patch]` and add the
bare-clone CI gate — the smallest change that converts the disease's root cause into a red build.

### Track B — proof-sharp (cutover + floor)

**Maturity: BUILT design, RUNS numerics, cutover not executed.** The deployed apex proves at
`d=4`, `|D⁰|=2^22` → **57.98 → 57 proven bits** (`docs/reference/PROVEN-120-CONFIG.md:131`; the apex
height 2^22 is resolved and the older 2^19 census refuted, ibid. `:145-183`). That number is a
Finset density ratio from a parametric Lean ledger, not an adversary bound, and the one leg below
the grounded apex — the per-node FRI extraction bundle `FriLdtExtractV3`
(`AlgoStarkSoundTransferV3.lean:131`) and its recursion twin `AggAirSound.FriExtract`
(`AggAirSound.lean:140`) — is an assumed deterministic universal claim, undischarged. Two designs
exist and are internally consistent: the **cutover plan** takes the shipped config to
`d=8, lb=6, q=36, pow=16` → **λ = 122.60 on every config with 2.6 bits of margin**, counted
site-by-site (~119 gnark lines across 14 files, 25 Rust `const D` sites, one Lean `rfl` pin), phased
with a go/no-go gate G1 and scoped at 4–8 weeks dominated by the gnark wrap
(`docs/reference/FRI-CUTOVER-PLAN.md:1-19`); the **extraction-floor design** re-bases the assumed
bundle over a query-counting oracle model so each conjunct becomes either a theorem or a
citation-shaped probabilistic carrier with a real adversary type (`FRI-EXTRACTION-FLOOR-DESIGN.md:1-11`)
— no cost model, which the record twice warns is the trap. **Next rung:** cutover Phase 0 (free,
correct today, degree-independent) — `WRAP_LOG_CEIL 16→15` for +2 bits and ~2× less apex work,
plus the three wrong-artifact corrections (`FRI-CUTOVER-PLAN.md:135-168`).

### Track A — interchain-real (live consensus feed)

**Maturity: RUNS in test / against a local validator; no mainnet consensus ever verified.** dregg
networks proofs, not tokens — other chains verify proofs *about* dregg state
(`docs/deos/INTERCHAIN-MODEL.md`). The holdings path proves a wallet held N units at a finalized
snapshot against a stake-weighted ≥2/3 Solana supermajority, with custody preservation a Lean
theorem (`weight_backed_and_noncustodial`, `metatheory/Dregg2/Bridge/ProofOfHoldings.lean`) — 13/13
bridge-holdings polarities RUN, but **no live Solana feed has been ingested**
(`docs/TOKENOMICS.md:46-57`). The live-feed trait `HoldingFeedSource` and a real
`solana-test-validator` holding proven end-to-end over live RPC exist
(`bridge/src/solana_feed.rs:245`, `HORIZONLOG.md:85`); the mainnet `SnapshotFeed` that unpacks bank
fields into a real `EpochStakeTable` is **designed in the module doc, not built**
(`bridge/src/solana_feed.rs:70-114`). The consensus-verified inbound bridge is green against fixture
clusters (`bridge/tests/solana_lock_trustless.rs`) but has never seen real mainnet consensus, and
**release is oracle-custodial on every path** (`docs/TOKENOMICS.md:60-73`). The three Solana
value-path holes the audit flagged are now CLOSED with red-first canaries
(`HORIZONLOG.md:80-83`), leaving a live-wiring gap: the production relayer/geyser must supply
*rooted* attestations. **Next rung:** build the mainnet `SnapshotFeed` behind the existing trait and
prove one real mainnet holding end-to-end, with the operator anchor (weak-subjectivity checkpoint)
pinned.

### Track C — economy-runs (protocol-native payments)

**Maturity: RUNS on mock chains; the mainnet flip is unfired.** `$DREGG` is a fixed-supply SPL
token that buys services, never features; the payment rail `dregg-pay/` (per-user Solana deposit
addresses, idempotent credit ledger, dual-asset USDC-fuel/`$DREGG`-pile treasury, Jupiter-priced
discount) is real code that **RUNS end-to-end on mock chains** (`cargo test -p dregg-pay` green),
but **the mainnet flip has not been made** — the deployed game surface is free, sets no payment
env, and the go-live runbook `docs/ops/PAYMENTS-GO-LIVE.md` is written but unfired; **no real
`$DREGG` has been accepted for a service** (`docs/TOKENOMICS.md:29-41`). Critically, **there is no
peg, oracle, or purchase path between computrons (the internal gas) and `$DREGG` anywhere in the
code** — "$DREGG powers dregg compute" is unsupported at HEAD; what exists are the docking points
(`relay_service.rs` `external_rate_micros`, the Payable rail, the fee-distribution engine)
(`docs/TOKENOMICS.md:115-126`). The `$DREGG` bond is a quote-floored two-tranche design
(`docs/deos/DREGG-BOND-DESIGN.md`), **DESIGNED not built**, that deliberately prices the
correlated-devaluation problem a token-denominated bond would suffer. **Next rung:** the bond
rung-1 as an ordinary Payable-rail sink — the first place `$DREGG` moves real value inside the
protocol without touching the ember-gated mainnet payment flip.

## 3. The target

A stranger clones the public repo into an empty environment, the build goes green, and the VK it
produces byte-matches a frozen, ceremony-pinned `v-final` VK whose proven soundness is **λ ≥ 122**
(not 57.98), whose one soundness leg is grounded in an adversary model rather than assumed; that
same stranger proves a *real* mainnet `$DREGG` holding against real Solana consensus and receives
governance weight non-custodially; and a service — a launchpad deploy, an AI-narration run, a bond
— accepts real value denominated in `$DREGG` through a rail that conserves supply by construction.
Every one of those sentences is presently blocked on exactly one track, and the tracks compose in a
fixed order.

## 4. The dependency spine

```
        D (off-laptop + FREEZE)  ← the meta-enabler; nothing is "deployed" until this
        ▲
        │ B-cutover MUST precede D-freeze
        │ (freeze the PROVEN 122.60 VK, not the 57.98 calculator one)
        │
   B (proof-sharp) ──────────────┐
                                 │  (B and A are independent of each other)
   A (interchain-real) ──────────┤
        │                        │
        │ A live-feed FEEDS      ▼
        ▼                   D freezes what A/C reference
   C (economy-runs) ── C mainnet-flip is EMBER-GATED (never lane-autonomous)
```

- **D is the meta-enabler.** Reproducible-build unblocks all CI (`HORIZONLOG.md:146`); until it
  lands, every other track's "green" is green-on-one-laptop and every "deployed" is unverifiable.
  D's work (pins, bare-clone gate) is orthogonal to what the other tracks *do*, so it can start
  first — but its *freeze* half must wait (below).
- **B-cutover must precede D-freeze.** The freeze pins a production VK as a hex KAT constant
  (`HORIZONLOG.md:152`). If D freezes before the FRI cutover, it freezes the `d=4` / 57.98-bit
  calculator configuration; the cutover then forces a full VK re-key (the anchor pair
  `DREGG_APEX_RECURSION_VK` / `DreggApexRecursionVk`, Solidity verifier, all fixtures —
  `FRI-CUTOVER-PLAN.md:104-126`), wasting the ceremony. Freezing the proven-122.60 config once is
  cheaper than freezing 57.98 and re-freezing. **The cutover's own re-key ceremony (Phase 4) IS the
  freeze event** — the two tracks share it; do them as one Phase-4/VK-REGEN-LOG commit.
- **A's live-feed feeds C's real payments.** C's payment and bond rails move `$DREGG` that entered
  dregg state as a mirror against a real lock, and its governance weight derives from a real
  holding — both are A's `SnapshotFeed` output. A mock-chain economy (C today) references a fixture
  bridge (A today); a real economy references a real feed. C's *real-value* rungs cannot outrun A's
  mainnet feed.
- **C's mainnet-flip is ember-gated.** Accepting real `$DREGG` for a service is a deployment flip,
  not a lane-autonomous act (`docs/TOKENOMICS.md:39`, `HORIZONLOG.md:75`); everything up to the flip
  is buildable and testable, the flip itself waits on ember.

## 5. Recommended sequencing

The ordering below front-loads the one thing that needs no frozen protocol and no mainnet, then
does the expensive proof/freeze work once, then lights up real value.

1. **Early win — the rung-1 launchpad, off-laptop, dregg-NOT-in-the-loop.** The audit names this the
   fastest stranger-usable product: deploy `DreggLaunchpad` to Base-Sepolia and host `launchpad-web`
   public (`HORIZONLOG.md:162`). The deploy artifacts already exist — `deploy/launchpad/`
   (deploy script, systemd unit, RUNBOOK, caddy) and the `tools/deployer-gate/` anti-scam capability
   layer ("deploying is a turn", README `:23`). Because rung-1 puts dregg *not in the loop*, it
   **sidesteps every unfrozen-protocol dependency** — it needs neither B's cutover nor D's freeze nor
   A's feed. It is the one thing shippable this week that a stranger can use end-to-end off ember's
   laptop, and it buys the campaign a real deployed surface while the harder tracks proceed.
   *Gate: a stranger deploys a token through the hosted gate on Base-Sepolia without ember present.*
   Land the persistent systemd node alongside it so the Descent funnel re-anchors (its devnet ledger
   was lost when hbox was hard-killed, `HORIZONLOG.md:164`).
2. **D reproducibility half + B Phase 0, in parallel.** Drop the sibling `[patch]`, pin the revs, add
   the bare-clone CI gate (D); land `WRAP_LOG_CEIL 16→15` and the three artifact corrections (B
   Phase 0). Both are free/correct today and neither touches the VK.
   *Gate: bare clone into empty `~/dev` builds green in CI; `fri_trace_height_measure` + FriLedger
   Lean green at the corrected numbers.*
3. **B Phase 1 measurements → G1 go/no-go.** Measure the d=8 wrap R1CS and outer-shrink cost before
   any rewrite (`FRI-CUTOVER-PLAN.md:170-182`). If G1 fails, the fallback is Phase-0's 59 bits plus
   the BCSS25 route — *and D-freeze then pins that 59-bit config deliberately*, not by accident.
   *Gate: measured Groth16 setup peak fits hbox under `swarm-build`; outer-shrink prove time
   acceptable.*
4. **B Phases 2–5 (Rust flip → gnark wrap → VK re-key → apex re-verify).** The re-key in Phase 4 is
   the freeze event D was waiting for — execute D-freeze's ceremony steps here so the `v-final`
   registry and the hex-KAT VK pin land on the proven-122.60 config in one VK-REGEN-LOG row.
   *Gate: G5 — a devnet turn settles under the new VK; the old-VK proof is rejected by the new
   verifier and vice versa.*
5. **A mainnet feed.** Build `SnapshotFeed` behind the existing trait; prove one real mainnet holding
   with the operator anchor pinned; wire the production relayer/geyser to supply rooted attestations.
   *Gate: one real mainnet `$DREGG` holding proven end-to-end, no fixtures.*
6. **C real-value rungs, mainnet-flip last (ember-gated).** Ship the bond rung-1 on the Payable rail
   (real `$DREGG`, no mainnet payment flip); then, ember-gated, fire `PAYMENTS-GO-LIVE.md`.
   *Gate: a bond posts real bridged `$DREGG`; separately, ember authorizes the payment flip.*

Steps 2–3 can overlap step 1. Step 4 is the long pole (4–8 weeks). Steps 5–6 depend on 4 only
through the shared freeze; A's feed work can be *built* in parallel and *proven-against-mainnet*
once the frozen VK exists.

## 6. What would make this credible to an outsider

A researcher or grant reviewer does not care that the code is green; they care which labeled-honest
claim each track upgrades to proven-excellent. The mapping:

| Track | Claim today (labeled-honest) | Claim after the next rungs (proven-excellent) | What an outsider can independently check |
|---|---|---|---|
| **D** | "It builds green" (on one laptop; `[patch]` to sibling checkouts, unpinned revs) | "*You* build it green from a bare clone, and the VK you get byte-matches the ceremony-frozen one" | Clone the public repo into an empty env; CI's bare-clone gate is the reproducibility proof; the VK KAT constant is checkable against your own build |
| **B** | "57.98 proven bits, one soundness leg assumed" (`PROVEN-120-CONFIG.md:131`, `FriLdtExtractV3` undischarged) | "λ ≥ 122 with 2.6 bits margin on every config, the extraction leg grounded in a query-counting adversary model" | Read `FRI-CUTOVER-PLAN.md` §3's re-pinned test table and the Lean ledger; the number is computed by an exact transcription validated against all 14 numbers the Lean proves |
| **A** | "Proven against fixture clusters and a local test validator; no mainnet consensus ever verified" | "One real mainnet holding proven against real ≥2/3 Solana consensus, non-custodially, anchor-pinned" | Reproduce the mainnet holding proof against a public snapshot; custody preservation is a Lean theorem you can read (`ProofOfHoldings.lean`) |
| **C** | "Payment rail RUNS on mock chains; no real `$DREGG` accepted; no computron↔token peg" (`TOKENOMICS.md:29-41,115`) | "Real `$DREGG` posts a bond / buys a service through a supply-conserving rail; the honest non-existence of a peg is stated by the project" | Post a bond on the deployed rail; the supply invariant `live_supply ≤ currently_locked` is enforced in `bridge_ledger.rs` and testable |

The differentiating posture is the one the tokenomics doc already takes: **the maturity labels are
published by the project itself.** The campaign's job is to move each label rightward without ever
letting the doc claim a resolution the code does not have — the recurring sin the record names
(`feedback-describe-at-current-not-intended-resolution.md`). An outsider's trust is earned by the
gap between "here is what runs" and "here is what does not" being *ours to state first*, and by each
named gap arriving with its closure rung already scheduled above.

## 7. Risks and the load-bearing falsifier

- **B's G1 measurement is the campaign's single biggest unknown.** The d=8 gnark wrap is estimated
  at ~7.5–12M R1CS and ~15–25 GB Groth16 setup (`FRI-CUTOVER-PLAN.md:290-291`); both are ESTIMATED,
  both gate everything downstream. **Load-bearing assumption: the 122.60 config is affordable to
  prove and wrap on available hardware.** *Falsifier:* run Phase-1.1 (`TestSettlementGadgetMarginal
  Costs` at d=8 + a phase-stripped compile) — if measured setup peak exceeds hbox's `MemoryMax=96G`
  under `swarm-build`, or the outer-shrink prove time is unacceptable, G1 fails and the whole
  proof-sharp track falls back to the 59-bit Phase-0 posture (`FRI-CUTOVER-PLAN.md:179-182`). This is
  a real fork, and D-freeze must not run until G1 has answered it, or D freezes a config the
  campaign may abandon.
- **Sequencing risk: freezing before B decides.** If schedule pressure lands D-freeze before B's
  G1, the ceremony pins 57.98 and the cutover forces a second ceremony. Mitigation is structural:
  the cutover's Phase-4 re-key *is* the freeze; do not run a standalone freeze ceremony ahead of it.
- **A's mainnet feed is a live-network dependency, not a proof gap.** The consensus circuit is built
  and green on fixtures; the risk is operational (public RPC cannot serve the snapshot; the operator
  anchor must be socially published and audited). *Falsifier:* the local `solana-test-validator`
  path already RUNS (`solana_feed.rs:245`), so the circuit is proven — a failure here is a data-
  plumbing failure, surfaced the moment `SnapshotFeed` ingests a real bank snapshot, not a soundness
  surprise.
- **C's economy is deliberately thin, and that is a claim not a bug.** No staking, no burn, no P2E,
  no computron↔token peg — the template is empty on purpose (`TOKENOMICS.md:89-99,115`). The risk is
  an outsider reading the emptiness as incompleteness; the mitigation is the published maturity
  labels and the bond design that prices the one real economic hazard (correlated devaluation)
  before shipping. *Falsifier for the honesty claim:* any place the docs say a peg/purchase-path
  exists — grep the code; at HEAD there is none, and the doc says so.

The campaign succeeds when a stranger, from a bare clone, reproduces a λ≥122 VK, proves a real
mainnet holding against it, and moves real `$DREGG` through a conserving rail — each step checkable
without ember in the room. That is the whole point of putting D first and the mainnet flip last.
