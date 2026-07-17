# FORWARD-CAMPAIGN-2026-07 — the four tracks, why, and in what order

*The synthesis a newcomer reads to understand where dregg is going. It ties four
concurrently-designed tracks into one campaign map: the through-line, each track's current
resolution with citations, the target, the staged rungs, the dependency spine, a recommended
sequencing, and what would make the whole thing credible to an outsider. Current-state claims
carry maturity labels — **RUNS** (a test or demo exercises it green), **BUILT** (real code, not
driven end-to-end live), **NAMED** (stub/doc/residual), **VISION** (design only) — and cite
`file:line`/doc at HEAD (2026-07-16). This map states the **code**, not the stale audit bullet:
where the 2026-07-15 launch-readiness workstream text (`HORIZONLOG.md:146`) has been overtaken by
work that landed, the map says so and cites the tree. The four sibling designs are all written:
Track D = `docs/reference/REPRODUCIBLE-BUILD-AND-FREEZE.md`, Track B =
`docs/reference/FRI-CUTOVER-PLAN.md` + `docs/reference/FRI-EXTRACTION-FLOOR-DESIGN.md`, Track A =
`docs/deos/INTERCHAIN-LIVE-CAMPAIGN.md`, Track C = `docs/deos/PROTOCOL-NATIVE-ECONOMY.md`. This
doc does not restate their rungs; it sequences them.*

## 1. The through-line, in one paragraph

The 2026-07-15 launch-readiness audit named one disease under four axes: **the real system is
green on ember's laptop, not in a frozen, reproducible, deployed artifact** (`HORIZONLOG.md:141`).
The math is strong; the gap is engineering discipline and scope focus. The four forward tracks are
the four cures, and they are not independent. **D** puts the system somewhere other than one
laptop and freezes what it is (the meta-enabler — every other track's "deployed" claim is
green-on-one-laptop until D lands). **B** sharpens the proof from a 57.98-bit calculator artifact
to a proven-122.60 configuration and re-bases the one still-assumed soundness leg over a real
adversary model, so that when D freezes a VK it freezes the *strong* one. **A** turns the
interchain story from fixture-clusters and a local test validator into a real mainnet consensus
feed, so a holding or a lock references value that actually exists. **C** turns the token economy
from "RUNS on mock chains" into protocol-native, supply-conserving payments, staged so the
*mechanisms* ship on internal assets before any *real external value* rides them. The campaign is
the order in which those cures compose without wasting a re-key or shipping a frozen artifact we
would immediately want to unfreeze.

## 2. Current resolution — the four tracks, each with its maturity and next rung

### Track D — off-laptop + freeze (the meta-enabler)

**Maturity: reproducibility floor mostly BUILT/RUNS; the freeze targets are BUILT-but-tautological
or NAMED.** State from code, because the audit bullet is now partly stale: the plonky3-recursion
sibling-`[patch]` is **gone** (`Cargo.toml:157-162`, whose comment now truthfully reads "PURE git
deps, no `[patch]`"; the four `p3-*` crates resolve from rev `0a4a554`, `Cargo.toml:236-239`), the
forks are pushed and rev-pinned, and `federation_id` is **already deterministic**
(`node/src/genesis.rs:243-252`, `H(sorted committee pubkeys ‖ ml-dsa ‖ epoch=0)`, closing audit
F1) — three items the `HORIZONLOG.md:146` P0 lists as open are done. What is genuinely open (per
`REPRODUCIBLE-BUILD-AND-FREEZE.md` §2.2): the toolchain is a rolling `nightly`, not date-pinned
(`rust-toolchain.toml:8`); `ark-serialize`/`-derive` are pinned by a **mutable branch**, the last
non-immutable ref (`Cargo.toml:180-181`, `branch = "serde-integration"`); the Lean seed is cut and
verified but **unpublished** (`dregg-lean-ffi/lean-seed.pin` `TAG=` empty), so the
`lean-marshal-gate` job asserts nothing (`ci.yml:250`); and **there is no bare-clone-into-empty-
`~/dev` CI gate** — the keystone that would turn "works on my machine" into a red build. The freeze
half: the recursion VK is a **self-recompute tautology** (`recursive_witness_bundle.rs:180-186`
returns `Some(())` iff the hash equals `compute_recursive_vk_hash()`), eleven `-staged` descriptor
names still ship, the 8-felt commitment is tooth-guarded but the 1-felt escape is not yet
impossible, and Control 4 (the non-regression differential) is design-only
(`VK-REGEN-CONTROLS.md:88`). **Next rung: D0 + D2** — immutable every dependency ref (date-pin the
nightly, rev-pin `ark-serialize`) and add the bare-clone gate; the smallest change that converts
the disease's root cause into a falsifier (`REPRODUCIBLE-BUILD-AND-FREEZE.md` §4).

### Track B — proof-sharp (cutover + extraction floor)

**Maturity: BUILT design, RUNS numerics, cutover not executed.** The deployed apex proves at
`d=4`, apex height `2^22` → **57.98 → 57 proven bits** (`PROVEN-120-CONFIG.md` §3.1). That number
is a Finset density ratio from a parametric Lean ledger, not an adversary bound, and the one leg
below the grounded apex — the per-node FRI extraction bundle `FriLdtExtractV3`
(`AlgoStarkSoundTransferV3.lean:131`) and its recursion twin `AggAirSound.FriExtract`
(`AggAirSound.lean:140`) — is an assumed deterministic universal claim, which the floor design
argues can *never* be discharged in that shape (`FRI-EXTRACTION-FLOOR-DESIGN.md` §2). Two designs
exist and are internally consistent. The **cutover plan** takes the shipped config to
`d=8, lb=6, q=36, pow=16, WRAP_LOG_CEIL=15` → **λ = 122.60 on every config with 2.6 bits of
margin**, counted site-by-site (~119 gnark lines across 14 files, 25 Rust `const D` sites, one Lean
`rfl` pin), phased with a go/no-go gate G1, scoped at 4–8 weeks dominated by the gnark wrap
(`FRI-CUTOVER-PLAN.md` §1–2). The **extraction-floor design** re-bases the assumed bundle over a
query-counting oracle model (`RomOracle`, in-tree and `#assert_axioms`-clean) so each conjunct
becomes either a theorem or a citation-shaped probabilistic carrier with a real adversary type and
a concrete `εFri(Q, params)` — explicitly **not** a cost model, which the record twice warns is the
trap (`FRI-EXTRACTION-FLOOR-DESIGN.md` §3, §4.3). **Next rung: Cutover Phase 0** — free, correct
today, degree-independent: `WRAP_LOG_CEIL 16→15` (+2 bits at d=4: 57→59, ~2× less apex work) plus
the three wrong-artifact corrections (`FRI-CUTOVER-PLAN.md` Phase 0). The floor design's Stage 1
(the faithfulness bridge `verifyAlgoO_run_eq`) can proceed in parallel — it is pure structure, no
crypto, and everything downstream needs it.

### Track A — interchain-real (live consensus feed)

**Maturity: RUNS in test / against a local validator; no mainnet consensus ever verified.** dregg
networks proofs, not tokens — other chains verify proofs *about* dregg state
(`docs/deos/INTERCHAIN-MODEL.md`). The verifier surface is real and sound over its inputs: holdings
derive the stake table from Solana bank state and tally the exact-slot authorized-voter
supermajority (`bridge/src/solana_holdings.rs:465`), and the **value-import path now enforces
rootedness** — `verify_lock_proof_consensus_anchored` calls the inner verifier with
`require_rooted = true` (`bridge/src/solana_trustless.rs:653`), so an unrooted slot fails closed at
`SlotNotRooted`. The three audit-flagged value-path holes (finality over-claim, stake-set
completeness, rotation signer binding) are **CLOSED with red-first canaries** (`HORIZONLOG.md:80-83`).
What is missing is not soundness but **ingestion**: every consensus-verified holding and lock in
the tree is assembled by an in-test fixture constructor. The live-feed seam `HoldingFeedSource`
exists and a real `solana-test-validator` holding is proven end-to-end over live RPC
(`bridge/src/solana_feed.rs:245`, `:570`); the mainnet `SnapshotFeed` that unpacks bank fields into
a real `EpochStakeTable` is **designed in the module doc, not built** (`:70-120`); release is
oracle-custodial on every path (there is no trustless outbound yet). **Next rung: Rung 0 — retire
the demoted `HostBallotBox` shim** (`INTERCHAIN-LIVE-CAMPAIGN.md` §4): the cheapest rung, no Solana,
constructed only in `#[cfg(test)]` at HEAD (`dregg-governance/src/lib.rs:621-665`) — deleting its
`WeightedBallotEngine` impl leaves exactly one verified ballot front door before the value-bearing
feed work lands on top. The core rung behind it is Rung 2, the mainnet `SnapshotFeed`.

### Track C — economy-runs (protocol-native payments)

**Maturity: RUNS on mock chains; the mainnet flip is unfired; the conserved rail is PROVED.**
`$DREGG` is a fixed-supply SPL token that buys services, never features
(`docs/TOKENOMICS.md` §role-1); the payment rail `dregg-pay/` is real code that **RUNS end-to-end
on mock chains** (`cargo test -p dregg-pay` green) but is **custodial by construction** — it holds
the HD seed and tracks run budgets as an off-chain sqlite number
(`dregg-pay/src/lib.rs:18-20,56-58`) — and **the mainnet flip has not been made**; no real `$DREGG`
has been accepted for a service. The endgame the crate itself names is protocol-native settlement:
every value flow a conserving `Effect::Transfer` under the kernel's per-asset value law, no
operator holding user funds. That rail **already exists and is proven** — `resolve_pay` desugars to
one `Signature`-gated conserving `Transfer` (`dregg-payable/src/payable.rs:24`,
`turn/src/action.rs:1069`); the distance to it is custody. Critically, **there is no peg, oracle, or
purchase path between computrons (the internal gas) and `$DREGG` anywhere in the code** — "$DREGG
powers dregg compute" is unsupported at HEAD (`docs/TOKENOMICS.md:115-126`). The `$DREGG` bond is a
quote-floored two-tranche design (`docs/deos/DREGG-BOND-DESIGN.md`), **DESIGNED not built**, that
deliberately prices the correlated-devaluation problem a token-denominated bond would suffer.
**Next rung: Rung 2a — the protocol-native run budget on an internal asset**
(`PROTOCOL-NATIVE-ECONOMY.md` §4): a run credit becomes a cell balance the *user* authorizes via
`resolve_pay`, deleting the seed and sweeper from the value path — the endgame mechanism, shippable
now on computrons/an internal `Payable` asset with **no bridge value and no ember-gated flip**.
Rung 1 (one real dollar through the custodial rail) is an ember-gated external trigger; Rung 4's
`$DREGG` bond junior tranche is the one genuinely new token sink and is also internal-first.

## 3. The target

A stranger clones the public repo into an empty environment, the build goes green from a bare clone
enforced by CI, and the VK it produces byte-matches a frozen, ceremony-pinned `v-final` VK whose
proven soundness is **λ ≥ 122** (not 57.98) and whose one soundness leg is grounded in a
query-counting adversary model rather than assumed. That same stranger proves a *real* mainnet
`$DREGG` holding against real ≥ 2/3 Solana consensus and receives governance weight
non-custodially; and a service — a launchpad deploy, an AI-narration run, a bond — accepts real
value denominated in `$DREGG` through a rail that conserves supply by construction, with no operator
holding user funds. Every one of those sentences is presently blocked on exactly one track, and the
tracks compose in a fixed order.

## 4. The dependency spine

```
        D (off-laptop + FREEZE)  ← the meta-enabler; nothing is "deployed" until this
        ▲
        │ B-cutover MUST precede D-freeze
        │ (freeze the PROVEN 122.60 VK, not the 57.98 calculator one)
        │ — and the two SHARE one event: cutover Phase 4 IS D's freeze ceremony
        │
   B (proof-sharp) ──────────────┐
                                 │  (B and A are independent of each other)
   A (interchain-real) ──────────┤
        │                        │
        │ A live-feed FEEDS      ▼
        ▼                   D freezes what A/C reference
   C (economy-runs) ── C real-value rungs gated on A's feed; mainnet-flip is EMBER-GATED
```

- **D is the meta-enabler.** Until the bare-clone gate is green, every other track's "green" is
  green-on-one-laptop and every "deployed" is unverifiable. D's *reproducibility* half (D0–D2) is
  orthogonal to what the other tracks *do* and can start first; its *freeze* half must wait on B
  (below).
- **B-cutover must precede D-freeze, and they share one event.** The freeze pins a production VK as
  a hex KAT constant, killing the self-recompute tautology at `recursive_witness_bundle.rs:180`. If
  D freezes before the FRI cutover, it freezes the `d=4`/57.98-bit config; the cutover then forces a
  full VK re-key (the anchor pair `DREGG_APEX_RECURSION_VK`/`DreggApexRecursionVk`, Solidity
  verifier, all fixtures), wasting the multi-GB Groth16 ceremony. **The cutover's Phase-4 re-key IS
  the freeze event** — `REPRODUCIBLE-BUILD-AND-FREEZE.md` Rung D4 is literally
  `FRI-CUTOVER-PLAN.md` Phase 4, not a parallel event. Run them as one Phase-4/VK-REGEN-LOG commit,
  paying the ceremony exactly once. D0–D3 have no Track B dependency and proceed immediately.
- **A's live-feed feeds C's real payments.** C's payment and bond rails move `$DREGG` that entered
  dregg state as a mirror against a real lock, and its governance weight derives from a real
  holding — both are A's `SnapshotFeed` output. A mock-chain economy (C today) references a fixture
  bridge (A today); a real economy references a real feed. Concretely: C's Rung 2b (bridged `$DREGG`
  as the run-budget asset) and its external-senior bond rungs are **hard-gated on A's value-path
  work landing on mainnet**, while C's Rung 2a (internal asset) and the internal bond rung proceed
  independently. C's real-value rungs cannot outrun A's mainnet feed.
- **C's mainnet-flip is ember-gated.** Accepting real `$DREGG` for a service is a deployment flip,
  not a lane-autonomous act (`docs/TOKENOMICS.md:39`, `HORIZONLOG.md:75`); everything up to the flip
  is buildable and testable, the flip itself waits on ember.

## 5. Recommended sequencing

The ordering front-loads the one thing that needs no frozen protocol and no mainnet, then does the
reproducibility and free-proof work, then the expensive proof/freeze once, then lights up real
value.

1. **Early win — the rung-1 launchpad, off-laptop, dregg-NOT-in-the-loop.** The audit names this the
   fastest stranger-usable product: deploy `DreggLaunchpad` to Base-Sepolia and host `launchpad-web`
   public (`HORIZONLOG.md:162`). The deploy artifacts exist — `deploy/launchpad/` and the
   `tools/deployer-gate/` anti-scam capability layer ("deploying is a turn"). Because rung-1 puts
   dregg *not in the loop*, it **sidesteps every unfrozen-protocol dependency** — it needs neither
   B's cutover nor D's freeze nor A's feed. It is the one thing shippable this week that a stranger
   can use end-to-end off ember's laptop, and it buys the campaign a real deployed surface while the
   harder tracks proceed. Land the persistent systemd node alongside it so the Descent funnel
   re-anchors (its devnet ledger was lost when hbox was hard-killed, `HORIZONLOG.md:164`).
   *Gate: a stranger deploys a token through the hosted gate on Base-Sepolia without ember present.*
2. **D reproducibility (D0–D2) + B Phase 0 + B floor Stage 1, in parallel.** Immutable every
   dependency ref (date-pin the nightly, rev-pin `ark-serialize`), then add the bare-clone CI gate
   (D0, D2); land `WRAP_LOG_CEIL 16→15` and the three artifact corrections (B Phase 0); begin the
   floor's faithfulness bridge (B Stage 1). All free/correct today and none touches the VK.
   *Gate: bare clone into empty `~/dev` builds green in CI (D2, the keystone falsifier);
   `fri_trace_height_measure` + FriLedger Lean green at the corrected numbers.*
   In the same window, A Rung 0 (retire `HostBallotBox`) and C Rung 2a (protocol-native run budget on
   an internal asset) are both cheap, lane-autonomous, and unblocked — schedule them here.
3. **B Phase 1 measurements → G1 go/no-go.** Measure the d=8 wrap R1CS and outer-shrink cost before
   any rewrite. If G1 fails, the fallback is Phase-0's 59 bits plus the BCSS25 route — *and
   D-freeze then pins that 59-bit config deliberately*, not by accident.
   *Gate: measured Groth16 setup peak fits hbox under `swarm-build` (`MemoryMax=96G`); outer-shrink
   prove time acceptable.*
4. **B Phases 2–5 (Rust flip → gnark wrap → VK re-key → apex re-verify), and D-freeze rides Phase 4.**
   The re-key in Phase 4 is the freeze event D was waiting for — execute D's ceremony steps here
   (retire `-staged` names, finish the 8-felt sole-width, build Control 4, pin the hex-KAT VK) so
   the `v-final` registry and the frozen VK land on the proven-122.60 config in one VK-REGEN-LOG row.
   *Gate: G5 — a devnet turn settles under the new VK; the old-VK proof is rejected by the new
   verifier and vice versa.*
5. **A mainnet feed (Rungs 1–2).** Build the rooted-attestation harvester, then the mainnet
   `SnapshotFeed` behind the existing trait; prove one real mainnet holding with the operator anchor
   pinned. *Gate: one real mainnet `$DREGG` holding proven end-to-end, no fixtures, `single_chunk`
   reconstruction deleted from the live path.*
6. **C real-value rungs, mainnet-flip last (ember-gated).** With A's feed live and the bridge sound,
   swap C's run-budget asset to bridged `$DREGG` (Rung 2b) and ship the bond rungs; then, ember-gated,
   fire `PAYMENTS-GO-LIVE.md`. *Gate: a bond posts real bridged `$DREGG`; separately, ember
   authorizes the payment flip.*

Steps 2–3 overlap step 1. Step 4 is the long pole (4–8 weeks, dominated by the gnark wrap). The
smaller internal-only rungs of A (Rung 0) and C (Rung 2a, internal bond) can be *built* throughout;
their *real-value* completions depend on step 4 (the frozen VK) and step 5 (A's feed).

## 6. What would make this credible to an outsider

A researcher or grant reviewer does not care that the code is green; they care which labeled-honest
claim each track upgrades to proven-excellent, and whether they can check it themselves.

| Track | Claim today (labeled-honest) | Claim after the next rungs (proven-excellent) | What an outsider can independently check |
|---|---|---|---|
| **D** | "It builds green" — but on one laptop, with a mutable-branch dep, a rolling nightly, and no bare-clone gate (`REPRODUCIBLE-BUILD-AND-FREEZE.md` §2.2) | "*You* build it green from a bare clone into an empty home, every dep an immutable ref, and the VK you get byte-matches the ceremony-frozen KAT constant" | Clone the public repo into an empty env; CI's bare-clone gate (Rung D2) is the reproducibility proof; the VK KAT constant is checkable against your own build |
| **B** | "57.98 proven bits, computed by a ledger that never touches the apex; one soundness leg an undischarged deterministic universal claim" (`PROVEN-120-CONFIG.md` §3.1, `FriLdtExtractV3`) | "λ ≥ 122 with 2.6 bits margin on every config; the extraction leg re-based over a query-counting adversary with a concrete `εFri(Q,params)` — b bits means `εFri(2^b) ≤ 1/2`" | Read `FRI-CUTOVER-PLAN.md` §3's re-pinned test table and the parametric Lean ledger validated against all 14 numbers it proves; read the floor design's per-stage falsifiers |
| **A** | "Sound over its inputs, but every holding/lock is a fixture; no mainnet consensus ever verified" (`INTERCHAIN-LIVE-CAMPAIGN.md` §2) | "One real mainnet holding proven against real ≥ 2/3 Solana consensus, non-custodially, anchor-pinned, with the reconstruction seam deleted" | Reproduce the mainnet holding proof against a public snapshot; custody preservation is a Lean theorem you can read (`ProofOfHoldings.lean`); the load-bearing falsifier (snapshot `bank_hash` = the hash a real supermajority signed) is a CI gate |
| **C** | "Payment rail RUNS on mock chains, custodial by construction; no real `$DREGG` accepted; no computron↔token peg" (`TOKENOMICS.md:29-41,115`) | "Real `$DREGG` posts a bond / buys a service through a supply-conserving rail with no operator custody; the honest non-existence of a peg is stated by the project" | Post/spend through the deployed rail; the supply invariant `live_supply ≤ currently_locked` (`bridge_ledger.rs`) and per-asset Σδ = 0 (`action.rs:1069`) are enforced and testable; grep the run path for `Seed`/`Sweeper` and find nothing |

The differentiating posture is the one the tokenomics doc already takes: **the maturity labels are
published by the project itself.** The campaign's job is to move each label rightward without ever
letting a doc claim a resolution the code does not have — the recurring sin the record names
(`feedback-describe-at-current-not-intended-resolution.md`), and the exact sin this rewrite
corrected in Track D (the `[patch]` was gone; the old draft still called it open). An outsider's
trust is earned by the gap between "here is what runs" and "here is what does not" being *ours to
state first*, and by each named gap arriving with its closure rung already scheduled above.

## 7. Risks and the load-bearing falsifier

- **B's G1 measurement is the campaign's single biggest unknown.** The d=8 gnark wrap is estimated
  at ~7.5–12M R1CS and ~15–25 GB Groth16 setup (`FRI-CUTOVER-PLAN.md` §4); both are ESTIMATED, both
  gate everything downstream. **Load-bearing assumption: the 122.60 config is affordable to prove
  and wrap on available hardware.** *Falsifier:* run Phase-1.1 — if measured setup peak exceeds
  hbox's `MemoryMax=96G` under `swarm-build`, or the outer-shrink prove time is unacceptable, G1
  fails and proof-sharp falls back to the 59-bit Phase-0 posture plus the BCSS25 route. D-freeze
  must not run until G1 has answered it, or D freezes a config the campaign may abandon.
- **The whole campaign's load-bearing falsifier is D2, the bare-clone gate.** Everything the math
  earns is worth zero to an outsider until a stranger's `git clone` into an empty home reproduces
  the author's green. The assumption "the sibling paths are all gone and §2.1's done items are done"
  is stated so it can be attacked: D2 either goes green or reds on the first uncaught sibling path or
  mutable ref. Do not assert reproducibility from reading `Cargo.toml` — assert it from a green D2.
  A design that trusts the manifest over the gate is the "green on ember's laptop" disease one level
  up (`REPRODUCIBLE-BUILD-AND-FREEZE.md` §6).
- **Sequencing risk: freezing before B decides.** If schedule pressure lands D-freeze before B's G1,
  the ceremony pins 57.98 and the cutover forces a second ceremony. Mitigation is structural: the
  cutover's Phase-4 re-key *is* the freeze; do not run a standalone freeze ceremony ahead of it.
- **A's mainnet feed is a live-network dependency, not a proof gap — with one real soundness
  falsifier.** The consensus circuit is built and green on fixtures; most of the risk is operational
  (public RPC cannot serve the snapshot; the anchor must be socially published and audited). The one
  soundness falsifier that must be a CI gate: a snapshot-derived `bank_hash` must equal the
  `bank_hash` carried in a real TowerSync vote for the same slot — if they differ (the SIMD-215
  lattice-hash transition is the concrete way this silently breaks), the feed proves against a hash
  no validator signed and the supermajority is vacuous (`INTERCHAIN-LIVE-CAMPAIGN.md` §6).
- **C's economy is deliberately thin, and that is a claim not a bug.** No staking, no burn, no P2E,
  no computron↔token peg — the template is empty on purpose (`TOKENOMICS.md:89-99,115`). The risk is
  an outsider reading emptiness as incompleteness; the mitigation is the published maturity labels
  and the bond design that prices the one real economic hazard (correlated devaluation) before
  shipping. *Falsifier for the honesty claim:* any place a doc says a peg/purchase-path exists — grep
  the code; at HEAD there is none, and the doc says so. And after C's Rung 2, the custody falsifier:
  grep the run-execution path for `Seed`/`Sweeper`/`DREGG_PAY_SEED` and find nothing.

The campaign succeeds when a stranger, from a bare clone, reproduces a λ ≥ 122 VK, proves a real
mainnet holding against it, and moves real `$DREGG` through a conserving rail — each step checkable
without ember in the room. That is the whole point of putting D first, sharing B's cutover with D's
freeze, feeding C from A, and leaving the mainnet flip for last.
