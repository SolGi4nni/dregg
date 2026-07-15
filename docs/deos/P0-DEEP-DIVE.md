# p0 (p0.systems) — the exhaustive offering map

*Ember asked for the deepest possible picture of what **p0** actually is and does — with a
specific, load-bearing question: does p0 do the **registrar / DNS / domains / hosting / infra**
layer, or only the token-factory / terminal / locker surfaces? This doc is the answer: an
inventory of every product and feature, each claim cited to a source, with honest confidence
flags. It builds on `P0-DREGGIC.md` (the prior MEDIUM-HIGH identification) and goes deeper +
wider. It found a whole second pillar the prior doc missed (an AI-inference gateway), the real
agent-native API surface (`x402`), and a **precise** registrar/DNS/hosting answer.*

**Confidence legend:** **[SITE]** = p0's own live pages/API (primary, high) · **[3P]** =
third-party aggregator (CoinGecko/exchange, medium) · **[SEARCH]** = search-snippet only, not
directly fetched (lower) · **[UNVERIFIED]** = single-source / promotional / could not confirm.

---

## 0. Identification — settled

**p0 = p0 Systems, `p0.systems`.** An AI-powered, agent-native token-creation-and-trading stack
on **Solana**, plus a co-branded **AI-inference gateway** ("Peezy Gateway"). This confirms and
sharpens `P0-DREGGIC.md`'s primary identification (was MEDIUM-HIGH; now **HIGH** — the live site,
the agent API, the `skill.md` reference, and the P0 token all corroborate). The `P0-DREGGIC.md`
secondary candidate (Project 0 / prime broker, `@macbrennan_cc`) remains a *different* product and
is not p0 Systems; keep it only as the alternate reading if "p0" ever means the prime broker.

Two token contract addresses appear in sources (see §4) and `p0.systems/migrate` exists — p0
appears to have **migrated its own token** (pump.fun → bags.fm era). Flagged, not resolved.

---

## 1. The full surface inventory — p0 has TWO pillars

The prior doc saw only Pillar A. p0 is really **two businesses under one brand**:

- **Pillar A — the memecoin loop** (create → launch → trade → lock), agent-native.
- **Pillar B — an AI-inference gateway** (Peezy Gateway, an OpenRouter competitor) — the actual
  revenue engine per p0's own promotion.

### Pillar A — the memecoin create/launch/trade/lock loop

**A1. AI Token Factory** — `p0.systems`. *"Build meme coins with AI. Deploy to Pump.fun or Bags.fm
in 60 seconds. Claim creator fees. All onchain, all automated."* and *"Claim creator fees
forever."* (meta description + og tags, **[SITE]**). Page keywords: *"solana, meme coins, pump.fun,
bags.fm, token launch, AI, crypto, defi, token factory"* **[SITE]**. It is a **convenience layer**:
p0 does **not** run its own launch venue — it emits an SPL token and **deploys it to an external
launchpad** (pump.fun bonding curve or bags.fm). Confirmed by the deploy API (§A4):
`"platform": "pump_fun"` or `"bags"` **[SITE, skill.md]**.

**A2. p0 Terminal** — `terminal.p0.systems`. *"Trade Solana meme coins with cashback rewards. The
ultimate onchain trading terminal. Buy, sell, and earn."* (meta description, **[SITE]**). Feature
detail beyond "buy/sell/cashback" is client-rendered and not server-visible; the **cashback-rewards**
trading angle is the only confirmed differentiator **[SITE]**. (Chart/portfolio/swap features are
implied by "trading terminal" but not individually confirmed — treat specific sub-features as
**[SEARCH]**: a Bitrue-explainer-level "charts, swaps, portfolio" description.)

**A3. p0 Locker** — token **locking / vesting / airdrop** surface (from `P0-DREGGIC.md` §1 +
Bitrue explainer, **[SEARCH]**). Could **not** independently re-confirm a dedicated Locker product
page this pass (`p0.systems/locker` is the same SPA shell). Treat the Locker as **[SEARCH]-level**
— named in explainers, not re-verified against a live product surface this survey. Merkle-airdrop
detail is **[SEARCH]**, single-source.

**A4. P0 for Agents — the agent-native deploy API (`x402`)** — `agents.p0.systems` +
`agents.p0.systems/skill.md` (**[SITE]**, the authoritative reference). This is the real heart of
Pillar A and the clearest evidence p0 is *"built for agents."* Tagline: *"AI agents deploy tokens
on Solana, earn creator fees from pump.fun and bags.fm, and pay their own rent."* **[SITE]**

- **Base URL** `https://api.p0.systems/api/x402`; auth via `x-api-key: p0_live_...`; 60 req/min.
  (The `x402` path name references the HTTP-402 / Coinbase-style **agent-payments** convention —
  p0 frames the whole surface as machine-payable.) **[SITE, skill.md]**
- **Capabilities** (verbatim from the agents page) **[SITE]**:
  - **RAPID MODE** — *"Deploy a token with landing page to pump.fun or bags.fm in a single API call."*
  - **FEE CLAIMING** — *"Claim creator fees from every trade. Earn SOL passively from deployed tokens."*
  - **BATCH DEPLOY** — *"Launch up to 10 tokens at once. Unique sites, logos, and themes for each."*
  - **CUSTOM SUBDOMAINS** — *"Every token gets a free .p0.surf subdomain. Pro agents get custom domains."*
- **Flow:** `POST /register` (wallet → API key + 1,000 credits) → `POST /projects` (token name /
  ticker / `templateId`, returns a project with `domain: "agentcoin.p0.surf"`) → `POST
  /projects/:id/deploy` (`platform` + `initialBuySol`) → `POST /projects/:id/claim-fees`. Plus
  `/earnings`, `/claim-all-fees`, `/batch` (Pro), `/api-keys`, `/credits/*`. **[SITE, skill.md]**
- **Self-sustaining-agent loop** is the explicit pitch: deploy → tokens trade on pump.fun/bags.fm →
  creator fees accrue on-chain → agent claims SOL → reinvests into `initialBuySol` on more deploys.
  *"This is how agents sustain themselves."* **[SITE, skill.md]**

**A5. AI features (credit-metered, inside the agent API)** **[SITE, skill.md]**:
- **AI chat / coding agent** — 400–1,000 credits / 1M tokens.
- **Image generation** (token logos/art) — 40–70 credits / megapixel.
- **Birdeye token data** — 1–3 credits / call (market-data passthrough).
- **Custom domain** — 7,000 credits (one-time, Pro).

### Pillar B — Peezy Gateway (AI inference — the OpenRouter competitor)

**B1. Peezy Gateway** — `gateway.p0.systems`. *"Peezy Gateway is an OpenAI-compatible inference
gateway. One endpoint, every open model, transparent per-token pricing. Bring your own key or pay
by credit."* / *"Your own OpenRouter."* (meta + og, **[SITE]**). A separate OpenAI-compatible
agent gateway also lives at `https://api.p0.systems/api/agents/v1` (Bearer-token auth; returns
`p0_agent_gateway_error` / `missing_api_key` when unauthenticated — **[SITE]**, confirmed by direct
probe), advertising *"19+ open models, pay-per-token, BYOK or credits"* **[SEARCH]**.
- **Traction claims (p0's own promotion, treat as [UNVERIFIED]):** processing *"2–3 billion tokens
  per hour and growing"*; an investor page showing *"live, real-time revenue … verifiable straight
  from @OpenRouter"*; Peezy ranked *"#1 in General Chat on OpenRouter, #11 globally"* (also #2
  Programming App, #3 Productivity/Personal Agents, #8 Coding Agents) **[SEARCH/UNVERIFIED — from
  p0's X account via search snippet, not independently confirmed]**.
- **Crypto-native payments:** *"one of the only AI providers who accept crypto natively"*
  **[SEARCH/UNVERIFIED]**.

**Reading:** Pillar B is a real, plausibly-larger business than the memecoin loop — an LLM API
reseller/router that takes crypto. It is **AI infrastructure** in the *model-access* sense, not the
DNS/hosting/compute sense (see §2).

---

## 2. ⚑ The registrar / DNS / domains / hosting / infra verdict

**Ember's specific question — precise, evidence-based answer:**

**p0 does NOT operate a general registrar / DNS / web-hosting / compute-cloud layer.** No source
shows p0 registering `.com`/`.net` domains, running authoritative DNS for third-party sites,
offering general web hosting, object storage, edge/CDN, or arbitrary compute. It is emphatically
**not** a "Cloudflare-for-agents." **[SITE + SEARCH, by absence across all sources surveyed]**

**But it is not zero, either — p0 runs a scoped, memecoin-bound micro-hosting + subdomain layer:**

1. **Landing-page hosting.** Every token deployed through the Factory/agent-API gets a generated
   **landing page** (a "site" with logo + theme). RAPID MODE = *"Deploy a token with landing page
   … in a single API call"*; BATCH = *"Unique sites, logos, and themes for each."* p0 hosts these.
   **[SITE, skill.md + agents page]**
2. **Subdomain issuance.** p0 **owns `p0.surf`** and issues each token a free
   `*.p0.surf` subdomain (`POST /projects` returns e.g. `domain: "agentcoin.p0.surf"`). This is a
   real, if narrow, **DNS/subdomain + hosting** function — for token pages only. **[SITE, skill.md]**
3. **Custom-domain mapping (paid, Pro).** Pro agents can attach a **custom domain**; it costs 7,000
   credits (~0.1 SOL). This is domain *mapping/binding*, **not** domain *registration* — the user
   brings/registers the domain elsewhere; p0 points a token page at it. **[SITE, skill.md]**
4. **AI-inference "infrastructure" (Pillar B).** p0 runs model-routing infra (Peezy Gateway). That
   is compute/model-access infra, **not** network/DNS/hosting infra. **[SITE]**

**One-line verdict:** *p0's "infra" is (a) a memecoin **landing-page host** that issues `*.p0.surf`
subdomains and can bind a Pro user's own custom domain, and (b) an **LLM-inference gateway**.
It does **no** general domain registration, **no** third-party DNS, **no** general web hosting/CDN,
**no** general compute. The verified-edge/registrar/DNS/hosting-for-agents space is **wide open**
— p0 is not in it.* **[HIGH confidence on the negative; the positive `.p0.surf`/custom-domain
scope is [SITE]-confirmed.]**

---

## 3. Tech, model, and how it makes money

- **Chain:** **Solana only** (SPL tokens; pump.fun bonding curve + bags.fm; Meteora DAMM V2 for the
  P0 token's own liquidity). No EVM/multichain surface found. **[SITE + 3P]**
- **"Built for agents":** literal — the whole Pillar-A surface is an **HTTP API keyed to a Solana
  wallet**, documented as a machine-readable `skill.md`, on an `x402` (agent-payments) base path;
  the pitch is autonomous agents that self-fund via creator fees. **[SITE, skill.md]**
- **Revenue model:**
  - **Pillar A:** subscription (**Pro Agent = 1 SOL / month**), **credit packs** for AI features
    (0.1 SOL = 7,000 credits; 0.5 = 42,000; 1.0 = 70,000), and **custom-domain** fees. Note: *"Credits
    are for optional AI features, not for deploying or claiming fees"* — **deploying and fee-claiming
    are free**; p0 monetizes the AI extras + Pro + gas-sponsorship. **[SITE, skill.md]**
  - **Pillar B:** per-token inference margin (BYOK or credits), OpenRouter-style. **[SITE]**
  - **Gas sponsorship as acquisition:** Free Agents get **3 gas-free deploys** (promo); Pro gets
    **all gas covered** up to 0.05 SOL/tx. **[SITE, skill.md]**
- **$P0 token utility:** an SPL on Solana; the one **concrete, cited utility** is **"50% off with
  $P0 token"** on credit purchases **[SITE, skill.md]**. Broader utility (governance/staking/
  buyback-burn) is **[SEARCH/UNVERIFIED]** — community-speculated, not in p0's own reference.

---

## 4. The P0 token — market data

**[3P: CoinGecko, at survey 2026-07-14]:**
- Price ~**$0.00149**; **market cap ~$1.37M** (rank ~#2367) — **down from ~$3.3M** at the prior
  `P0-DREGGIC.md` survey days earlier (a fresh, falling micro-cap).
- FDV ~$1.49M; circulating **921.1M**; total **999.96M**; max **1B**.
- 24h volume ~**$414K**; primary venue **Meteora (DAMM V2)**, pair P0/SOL.
- **ATH $0.004261 (2026-07-07)**, **ATL $0.0003549 (2026-07-04)** → **launched ~2026-07-04**
  (about ten days old at survey). CoinGecko category: **"Infrastructure (Solana Ecosystem)."**
- CoinGecko risk note (verbatim): *"There is a risk of market manipulation due to large
  concentration of tokens held in one or more unidentified wallets."*

**⚑ Contract-address discrepancy (flagged, unresolved):**
- CoinGecko lists **`HmTi3CQfKfXWbn1tNoiAxH7GzMV7L3tDAmPWabZEBAGS`** (ends `EBAGS`). **[3P]**
- `skill.md` lists **`CCj42knHtiG1sr8ZEDTeCrXwMNumrSh5xztpscDcpump`** (ends `pump`) for the "50% off"
  $P0. **[SITE]**
- Combined with `p0.systems/migrate` existing, the likeliest reading: p0 **migrated its token**
  (original pump.fun `…pump` mint → a bags.fm `…EBAGS` mint), and `skill.md` still cites the old
  address. **[INFERRED — flagged, not confirmed. Do not treat either address as canonical without
  checking `p0.systems/migrate` live.]**

---

## 5. Traction, team, roadmap

- **Traction (Pillar B):** the only quantified numbers are p0's own — *"2–3B tokens/hour,"* an
  OpenRouter-verifiable revenue page, top-of-leaderboard OpenRouter ranks. **All [UNVERIFIED /
  single-source promotional.]** Pillar-A usage (# tokens deployed, # agents) — **no data found.**
- **Team / founder:** **could not verify.** The `P0-DREGGIC.md` "founder Cory" name traces to a
  single promotional tweet and **did not surface in any independent source** this pass. No
  whitepaper, no named team, no corporate registry. Treat **"Cory" and any team claim as
  [UNVERIFIED].** (Note the noise: "P0 Security" is an *unrelated* enterprise-security company on
  PitchBook/Crunchbase — do **not** conflate it with p0.systems.) **[SEARCH]**
- **Roadmap:** *"local payments coming back (card payments, QR, etc)"* is the only forward item
  found **[SEARCH/UNVERIFIED]**. Pillar B's "19+ models and growing" implies model expansion. No
  formal roadmap doc found.
- **Maturity:** **very new** — token ~10 days old at survey; product surfaces live and functional
  (the agent API responds), but the whole thing is a fast-moving, thin-liquidity, early-stage
  crypto-AI project. **[SITE + 3P]**

---

## 6. What p0 does NOT do — the gaps (where dregg wins)

Every gap below is an **opening**, cited to p0's actual scope (not invented). See `P0-DREGGIC.md`
for the full feature-by-feature dregg-native rebuild; the sharpest ones:

| p0 gap | Evidence | dregg's answer |
|---|---|---|
| **No verification of what it deploys** — the Factory ships an AI-drafted token to pump.fun/bags.fm with **no audit/proof stage**; inherits the launchpad's rug economy (~98.6% scam/rug traits, Solidus) | deploy API just hands off `platform: pump_fun\|bags` **[SITE]** | disclosed-supply mint *biconditional* (PROVED) + the DREGG-kernel audit-service; **hidden supply unconstructable** |
| **No fair clearing** — Terminal routes swaps on public Solana DEXs (MEV/sandwich-exposed); launches are time-priority bonding curves (snipable) | *"trading terminal … buy, sell"* on public venues **[SITE]** | uniform-price sealed-bid clearing (PROVED); DrEX fair-by-proof + privacy tiers |
| **The locker is a trusted contract** — a lock is a promise, not a proof | Locker **[SEARCH]** | committed monotone `Pred` vesting; violation = REPLAYABLE, bonded, holder-compensating |
| **Agents hold raw keys** — the `x-api-key` + wallet model gives an agent full deploy/claim authority; a compromised key drains it | `x-api-key: p0_live_…`, wallet-bound **[SITE, skill.md]** | attenuable **capability mandate** — non-amplifying, budget-conserved, revocable; **breach unconstructable, not monitored** |
| **⚑ No verified infra/edge layer** — p0's only "hosting" is memecoin landing pages on `*.p0.surf`; **no DNS/registrar/CDN/compute** | §2 **[SITE, by scope]** | the verified-agent-infra space is **open** — dregg's proof-carrying substrate can *be* the trustworthy edge/registry p0 isn't |
| **Solana-only, single-venue** | no multichain surface found **[SITE]** | OCIP socket — networks **proofs, not tokens**, cross-chain |
| **Token = concentration risk + speculative utility** — only cited utility is a 50%-off credit discount; wallet concentration flagged | **[SITE + 3P]** | $DREGG buys **services**, ranking is REPLAYABLE, slashes compensate holders |

**The sharpest single gap:** p0 is a **fast, unverified deploy button + an LLM reseller** — it
**packages** the memecoin loop and **routes** model calls, but it **verifies nothing**: not the
token contract, not the clearing, not the lock, not the agent's authority. dregg does p0's exact
create→launch→trade→lock job on a substrate where each of those becomes a **Lean theorem you cannot
route around**. And on ember's specific question — **p0 is not the registrar/DNS/hosting/infra
layer for agents; that lane is empty, and dregg's verified substrate is the natural occupant.**

---

## Sources

**p0's own surfaces [SITE]:** `p0.systems` (+ `/migrate`, meta/og/keywords) · `terminal.p0.systems`
· `gateway.p0.systems` · `agents.p0.systems` (full page) · `agents.p0.systems/skill.md` (the x402
API reference — capabilities, endpoints, pricing, credits, gas, $P0 discount) ·
`api.p0.systems/api/x402/*` and `api.p0.systems/api/agents/v1` (probed: auth-gated, error shapes).
**Third-party [3P]:** CoinGecko `p0-systems` (market data, contract, ATH/ATL, risk note).
**Search-snippet [SEARCH]:** Bitrue "What is p0 Systems"; p0's `@P0Systems` X promotion (traction/
revenue claims); bags.fm p0-Systems app listing. **[UNVERIFIED]:** founder "Cory", team, buyback-
burn, governance utility, the OpenRouter-rank/token-throughput figures — single-source/promotional,
not independently confirmed.

## See also
`P0-DREGGIC.md` (the dregg-native rebuild — feature-by-feature p0 → p0-but-dreggic; trust grades) ·
`DREGG-LAUNCHPAD-DESIGN.md` · `DREX-DESIGN.md` · `DREGGFI-PRIVACY-TIERS.md` ·
`DREGG-AUDIT-SERVICE.md` (`tools/dregg-audit/`) · `OCIP-SECURITY-SOCKET.md`.
