# DreggNet + DreggCloud — pull-forward evaluation toward the full p0-matching offering

*Read-only recon (2026-07-14). Inventories `~/dev/DreggNet` and `~/dev/DreggCloud`, classifies
each notable asset against the repo boundary, and recommends what to pull-forward toward a full
"everything a p0-class launchpad/trading product does" offering — DNS, gateway, deploy infra, the
offerings/launchpad/trading surfaces. **This is EVALUATE + RECOMMEND. No code was pulled, no
DreggNet/DreggCloud file was modified, the live dreggcloud `:8787` service was not touched.** The
DNS/deploy story here is **evaluated now, deployed later** (deploy is parked per ember).*

---

## 0. The boundary (read first)

Three repos, three postures — this eval respects them and never recommends pulling proprietary
product into the public repo:

- **breadstuffs** — the PUBLIC substrate. AGPL, `github.com/emberian/dregg`. The rail: cells,
  `Payable`/Transfer, the intent ring, `StandingObligation` metering, `execution-lease`, the
  verified executor. Only **SUBSTRATE-GENERAL** (generic mechanism) and **OPERATIONAL** (deploy/ops
  config) things belong here.
- **DreggNet** (`~/dev/DreggNet`) — a PROPRIETARY product: a verifiable permissionless **cloud**
  ("Liftoff/Render/fly.io made trustless"), built *on top of* breadstuffs as the rail
  (`ARCHITECTURE.md:15-20` states this explicitly). Its **product identity** stays private.
- **DreggCloud** (`~/dev/DreggCloud`) — a service repo: a self-hosted **"House"** (sovereign
  operated-graph substrate, the `:8787` service on hbox). Its **House product** stays private.

Every asset below is tagged **SUBSTRATE-GENERAL** (pullable to public breadstuffs), **OPERATIONAL**
(DNS/deploy/ops config — reusable/shareable), or **PRODUCT-PRIVATE** (stays in its repo; may inform
breadstuffs design but is not copied).

**Verdict on the memory's "DreggNet ABANDONED; parts ported to breadstuffs":** confirmed *and*
documented in-tree, with nuance. DreggNet's `Cargo.toml` header records that the agent-platform /
grain-verify / sandstorm-bridge / dregg-ipfs family was "ported to the dregg monorepo
(~/dev/breadstuffs) … local copies deleted 2026-07-09," and the Elide `net/*` stack was ejected.
The **cloud-product crates are frozen** (dregg-domains, dregg-deploy, console, landing all last
touched ~07-02; gateway 07-10; control 07-12); active dev has shifted entirely to a Lean-proven
compiler / verified data-plane track (`Pancake/`, `Dsl/`, `net/conformance-kit`). So the *hosting
product* is dormant — its DNS/gateway/deploy machinery is stable, self-contained, and exactly the
kind of thing worth mining. **DreggCloud is very much live** (last commit 07-12, schema v16).

---

## 1. What the full p0-offering needs (the parity target)

"Everything p0 does" (a pump.fun-family launchpad + a trading terminal), grounded against our own
plan docs, decomposes into:

| Need | Where breadstuffs stands today |
|---|---|
| **Token launchpad** (create → bonding curve → graduate) | ✅ BUILT — `DREGG-LAUNCHPAD-DESIGN.md` + launchpad-web `:8785`, contracts 29/29 gate green (`DREGGFI-DEVNET-OFFERINGS.md` row f) |
| **Trading terminal / DEX** (order entry, clearing, portfolio) | ✅ BUILT engine — ring DrEX `:8781`, derivatives/package/shielded offerings `:8790`, portfolio/CFMM lib (`DREGGFI-DEVNET-OFFERINGS.md` rows a–e) |
| **A public menu of offerings** | ✅ BUILT — `offerings.mjs` menu surface |
| **DNS** (subdomains per surface; ideally BYO custom domain per launch/site) | ⚠ PARTIAL — the verified custom-domain registry is now in-tree (`starbridge-apps/domains`: `DomainBinding`, `is_verified`, `site_for_host` — the ask hook). The per-surface Caddyfiles (`deploy/games`, `deploy/launchpad`) still carry hand-set domain defaults, and DNS records stay manual. |
| **Gateway / TLS / ingress** | ✅ BUILT in-tree — `deploy/gateway-ask/` serves the on-demand-TLS `ask` (`GET /internal/site-exists` off the domain registry) + a capability forward-auth gate, with `Caddyfile.on-demand-tls` (one wildcard block, no baked-in domain); `deploy/webauth-edge/Caddyfile.capauth` is the cap-auth edge idiom. |
| **Deploy infra** (ship a surface/site → live) | ⚠ PARTIAL — `deploy/PRACTICES.md` codifies the rules and `gateway-ask/deploy.sh` does staged-alt-port → atomic-swap → rollback; there is still no generic git→build→publish pipeline. |
| **Hosting a user's launched site** (a token's page as its own site) | ❌ ABSENT — no "a site is a cell / `<name>.<apex>`" hosting surface in breadstuffs. |

**The remaining gap is the deploy-pipeline + hosting rows — and a live edge.** The financial
*engine* is done, and the gateway/TLS/registry layer this eval recommended now exists in-tree
(`deploy/gateway-ask`, `starbridge-apps/domains`); what's still missing for a "full offering" is
the git→build→publish pipeline, the hosted-site surface, and an edge actually running the wildcard
block (nothing is deployed as a public product right now). The pipeline + hosting halves are
precisely what DreggNet already built.

---

## 2. Inventory — DreggNet (`~/dev/DreggNet`)

~102,500 LOC Rust; a verifiable permissionless cloud consuming the breadstuffs payment rail. Cited
by absolute path.

### 2.1 DNS / custom domains — `dregg-domains/` ⭐ the marquee
- `/Users/ember/dev/DreggNet/dregg-domains/src/lib.rs` (1,311 LOC) — **BYO custom domain as a
  verifiable cell.** A `DomainBinding` (`:109`) with `VerificationState{Pending,Verified}` (`:93`)
  and `ChallengeMethod{Txt,Cname}` (`:84`); `DomainRegistry` (`:433`) with `bind()` (cap-gated,
  `:582`), `verify()` (`:660`), `site_for_host()` (verified-only Host→site, `:719`), and
  `is_verified()` (`:728`) — **the exact hook a Caddy on-demand-TLS `ask` (`/internal/site-exists`)
  consults so a cert is minted per-domain only after DNS proof-of-control.** ACME-style: TXT
  `_dregg-verify.<domain>` or CNAME to `<site>.dregg.works` (apex `HOSTING_APEX = "dregg.works"`,
  `:80`). Cap model: `DomainCap` (`:190`), `BIND_CAP_PREFIX="domain-bind/"` (`:73`).
- `/Users/ember/dev/DreggNet/dregg-domains/src/live.rs` (269 LOC) — `LiveDns` (`:72`) over
  `hickory_resolver`, system config with **Cloudflare 1.1.1.1 fallback** (`:147`). It only *reads*
  DNS to verify tenant records — **no registrar/Cloudflare-API integration**; certs come from Caddy
  on-demand-TLS, not this crate. `DnsResolver` is a trait (`:374`), so tests drive `MockDns`.
- **Classification: SUBSTRATE-GENERAL.** This is a generic DNS-proof-of-control mechanism, not a
  product secret. It path-depends on breadstuffs cell/receipt types (the dependency already lives in
  the target repo, easing any pull).

### 2.2 Gateway — `gateway/` (7,676 LOC)
- `/Users/ember/dev/DreggNet/gateway/src/route.rs` (187) + `types.rs` (264) — a **fly.io
  Machines-API-compatible** classifier (`/v1/apps/{app}/machines/...`) so `flyctl`/fly clients speak
  to it unchanged. `MachineState`, `GuestConfig` (`cpu_kind`→dregg cap-grade).
- `/Users/ember/dev/DreggNet/gateway/src/sitepublish.rs` (474) — `SitePublishHandler` (`:78`):
  `POST /v1/sites/<name>/publish`, **cap-auth** (a `dga1_` credential must chain to a root authority,
  fails closed 401) + **funding gate** (publish refused 402 without a funded lease). Publishes into
  `SiteRegistry`.
- `main.rs` (1,684), `gateway.rs` (884), `vats.rs` (783), `storage.rs` (608, S3-ish), `api.rs` (636),
  `hosting.rs`, `funding.rs`, `lease.rs`, `webapp.rs`, `metrics.rs`, `status.rs`.
- **Classification: SUBSTRATE-GENERAL** for the routing/site-publish/on-demand-TLS-ask spine; the
  fly-compat API is a generic compatibility layer. (The *"DreggNet Cloud" branding* around it is
  PRODUCT-PRIVATE, but the mechanism is not.)

### 2.3 Deploy pipeline — `dregg-deploy/` (2,546 LOC)
- `/Users/ember/dev/DreggNet/dregg-deploy/src/lib.rs` + `workflow.rs` (the durable orchestration),
  `clone.rs`, `plan.rs` (`BuildPlan::{Static,Command,Compute}`, framework detect), `build.rs`,
  `publish.rs` (injects a `/.well-known/dregg-deploy.json` commit manifest into the cell root),
  `sandbox.rs` (deny-default cage for untrusted `npm run build`: `env_clear()`, fresh process group,
  rlimits, Linux netns — closes documented RCE findings). **`dregg deploy <git-url>` →
  Clone(pinned commit) → Detect → Build(metered sandbox) → Publish(SiteCell + receipt) → Live at
  `<name>.dregg.works`**, modeled as a crash-resumable exactly-once metered durable workflow.
- **Classification: SUBSTRATE-GENERAL.** A generic git→build→publish pipeline with a real untrusted-
  build sandbox — high-value, self-contained, reproducibility built in (commit-in-receipt).

### 2.4 Deploy/ops artifacts — `deploy/` (not Rust)
- `/Users/ember/dev/DreggNet/deploy/staging/docker-compose.yml` — the real stack: `postgres`,
  `gateway`, `provider`, `ops`, `webauth`, `caddy`, `dregg-node`, `dreggnet-discord-bot`, and a
  self-hosted **`headscale`** (Tailscale control server) joining the AWS edge box ↔ persvati compute
  box ↔ devices.
- `/Users/ember/dev/DreggNet/deploy/staging/Caddyfile` + `Caddyfile.capauth` — **reverse proxy with
  dregg-native capability forward-auth**: `forward_auth` → `webauth:8099` verifies a `dga1_` session
  offline (2xx admit / 401 bounce), plus a header-strip "no-forge" discipline
  (`dregg_strip_forged_identity`) and a break-glass override. Two faces: `portal.dregg.studio`
  (public read-only) + `dreggnet.fg-goose.online` (gated operator surface).
- `/Users/ember/dev/DreggNet/deploy/staging/deploy.sh` — cross-builds with `cargo zigbuild
  --target x86_64-unknown-linux-gnu`, rsyncs binaries (the box does NOT compile Rust — OOMs), `docker
  compose up`; supports `releases`/`rollback`/`--auto-revert`.
- `deploy/staging/headscale/{config.yaml,acls.hujson}` — the private-mesh control plane.
- `deploy/observability/` — full Prometheus/alertmanager/blackbox/node-exporter + a custom
  `persvati-thermal-exporter`.
- **Classification: OPERATIONAL** across the board — deploy/ops config, directly reusable, maps onto
  our own `deploy/aws` + `deploy/games` + `deploy/launchpad` pattern (§4).

### 2.5 Product crates (context — mostly PRODUCT-PRIVATE, a few substrate-general seams)
- **exec** (`exec/`, 3,111) — owned pure-Rust `wasmi` sandbox (`Sandboxed` real; JIT/native/microVM/
  GPU fail-closed). **SUBSTRATE-GENERAL** (generic sandbox).
- **durable** (3,587) — DBOS/Temporal-style crash-resumable exactly-once metered workflows.
  **SUBSTRATE-GENERAL.**
- **bridge** (2,204) — funded `execution-lease` → cap-tier → metered workload → reap. Rail-adjacent;
  the rail itself is already in breadstuffs. **SUBSTRATE-GENERAL seam.**
- **control** (11,467, largest) — scheduling, providers (`local.rs`/`ec2.rs`), fleet lifecycle,
  settlement ledger (`settle_ledger.rs`, `xop_settle.rs` cross-operator settlement, touched 07-12),
  WireGuard mesh (boringtun). Mostly **PRODUCT-PRIVATE** (fleet/provider control plane); the
  settlement-ledger math is rail-adjacent.
- **webapp** (3,942) — agent-served web apps + the `hosting` module (`SiteRegistry`/`SiteCell`, the
  `<name>.dregg.works` wildcard). **SUBSTRATE-GENERAL** hosting primitive.
- **storage** (1,786, "a bucket is a cell"), **billing** (1,867, invoices over the meter), **org**
  (1,032, IAM via cap-attenuation), **guard** (2,177, KYC-free abuse quotas), **webauth** (2,689,
  the `dga1_` cap-auth service), **umem** (1,680, registry-is-a-cell), **webcell** (1,366, leased JS
  runtime — "adopted from breadstuffs `hosted-lease`"), **http** (555, clean-room HTTP/1.1). Mixed:
  the mechanisms are substrate-general; the "DreggNet Cloud" packaging is product.
- **cli** (`dregg-cloud`: `login/deploy/domains add|verify/run/...`), **console**/**landing**/**ops**/
  **status**/**attach** — all **server-rendered Rust HTML, no React/bundler, zero `package.json`**.
  The rendered marketing/console *copy + product identity* is **PRODUCT-PRIVATE**.

### 2.6 p0 / DeFi / launchpad / trading in DreggNet
**None.** No launchpad, DEX, AMM, orderbook, bonding-curve, or token-sale code. "launchpad" appears
only as competitive framing in the permissionless-cloud plan notes (a described *future*
"couple a token launch to a real hosted site" differentiator). The monetary primitives are
**usage-billing/settlement** (leases, metering, `xop_settle.rs`, invoices, Stripe→mint in `demo/`),
not trading. → **The launchpad/trading half of p0 does NOT exist in DreggNet; it exists in
breadstuffs already** (`DREGGFI-*`). DreggNet contributes only the **hosting/DNS/deploy half.**

---

## 3. Inventory — DreggCloud (`~/dev/DreggCloud`)

A live self-hosted "House" (`dreggcloud-house`, the single `:8787` Axum binary, schema v16),
sovereign operated-graph substrate. ~94,500 LOC, last commit 07-12.

### 3.1 DNS / gateway / TLS — essentially ABSENT
DreggCloud ships **no reverse proxy, TLS terminator, or DNS/subdomain config**. It binds a raw HTTP
port and expects an external TLS proxy in front (`docs/deos/SELF-HOSTING-LOOP.md` says so explicitly). The only
"domain" config is `DREGGCLOUD_PUBLIC_ENDPOINT` (canonical URL pinned at first boot; mismatch refuses
startup). "Gateway" here means the *service-economy `ToolGateway`*, not HTTP ingress. → **DreggCloud
is NOT a source for the DNS/gateway pull-forward.** The one transferable idea is the
public-endpoint-pinning discipline.

### 3.2 Deploy / ops — a real rollback engine
- `/Users/ember/dev/DreggCloud/scripts/dreggcloud_ops.py` (58 KB, + 21 KB tests) — the actual
  deploy/rollback engine: staging boot on an alt port (`127.0.0.1:18787`), whole-directory rollback
  copy, atomic binary swap, health/probe, hash recording. Wrapped by `scripts/dreggcloud`.
- `/Users/ember/dev/DreggCloud/Dockerfile` (multi-stage: builds Lean FFI + plonky3 recursion +
  `dreggcloud-house`, `EXPOSE 8787`), `compose.yaml` (`read_only:true`, tmpfs, requires
  `DREGGCLOUD_PUBLIC_ENDPOINT` + `DREGGCLOUD_OPERATOR_TOKEN`), `deploy/dreggcloud-hardened.user.service`
  (loopback 8787, `ProtectSystem=strict`), and an `ops.toml.example` under `deploy/`.
- **Classification: OPERATIONAL.** The Python ops/rollback engine is a reusable staging-swap-rollback
  pattern (complements our RUNBOOKs, which are prose-only today).

### 3.3 Service surfaces / offerings
- `/Users/ember/dev/DreggCloud/service-cells/src/lib.rs` — **the DeFi-adjacent core**: escrow,
  conserving-value funding, market matching (`RingSolver`), prepaid leases, signed receipt release,
  timeout refund, ledger, nullifiers — a capability-scoped receipt-backed **service economy** over
  breadstuffs. **SUBSTRATE-GENERAL** (a settlement/escrow mechanism; overlaps our own intent-ring/
  `verified_settle` — likely a WELD candidate, not a fresh pull).
- `service-house-adapter` (3,646) — custody-grade operated daemon: WAL-before-side-effect, durable
  nullifiers, fsynced compensating obligations, public offline re-audit, deterministic reopen.
  Genuinely settlement-grade discipline. **SUBSTRATE-GENERAL** discipline / **PRODUCT-PRIVATE**
  packaging.
- `dreggcloud-web-verify` (812) + `web/verifier*` — **WASM in-browser receipt-chain verifier.**
  **SUBSTRATE-GENERAL** (a light-client-in-the-tab; matches our verified-light-client north star).
- `dreggcloud-gate` (bounded admission gates), `dreggcloud-custody` (archive-first custody contract),
  `notary-selfhost` + `notary-live-client` (real MPC-TLS / TLSNotary daemon + live Bedrock/GitHub
  clients — a real DECO/attested-data carrier), `proof-bridge` (zk recursion leaf). Mix of
  **SUBSTRATE-GENERAL** mechanisms the repo *itself* intends to push upstream.
- **PRODUCT-PRIVATE:** `dreggcloud-house` (the operated-House product), the `dreggcloud-expedition`
  game engine, `native-workbench` (GPUI desktop client).

### 3.4 Frontend / marketing
- `/Users/ember/dev/DreggCloud/microsite/` — a static **branded build-report/landing** (canonical
  `https://www.dregg.net/gpt56sol/`; "an operated firmament where sovereign Worlds become inhabited
  Rooms"). Hosted externally, not by the House. **PRODUCT-PRIVATE** (branded copy).
- `/Users/ember/dev/DreggCloud/web/` — the **World Workbench** served at `:8787`: a custom-element
  desktop app (`app.js` 4,575 LOC — graph, transcript, market, Forge, Expedition, oracle, federation,
  surfaces) + WASM verifier + Cipherclerk key-handoff. **PRODUCT-PRIVATE** (the House UI); the
  Cipherclerk-handoff and WASM-verify *patterns* are substrate-general.

---

## 4. The DNS / gateway / deploy eval — and how it maps to our deploy-prep

**Our current pattern (at HEAD).** The old `deploy/aws` layout this eval originally mapped against
is superseded — its systemd/Caddy/setup content is quarantined in `deploy/aws/SUPERSEDED/`, and
`deploy/aws/README.md` describes the AWS box as it is (the tailnet's public exit + edge; nothing
app-shaped runs from that directory). The live deploy docs are `deploy/PRACTICES.md` +
`deploy/README.md`. The per-surface pattern survives in `deploy/games/caddy/Caddyfile.games` +
`deploy/launchpad/caddy/Caddyfile.launchpad` — **one hand-written site block per surface**
(`{$DREGG_GAMES_DOMAIN}` → hbox `:8790`, `{$DREGG_LAUNCHPAD_DOMAIN}` → hbox `:8785`), each
reverse-proxying **over Tailscale** to a **fixed hbox port**, each with its own systemd unit and
RUNBOOK. Their domain *defaults* still name `dregg.fg-goose.online` — a dead devnet-era domain (the
product domain is `dregg.net`, and there is no live public devnet).

The per-surface pattern **scales by hand**: every new offering = a new hardcoded block + unit + DNS
record. The replacement now exists in-tree: `deploy/gateway-ask/` (the on-demand-TLS `ask` sidecar +
capability forward-auth, over `starbridge-apps/domains`) + its `Caddyfile.on-demand-tls` one-wildcard
block, and `deploy/webauth-edge/Caddyfile.capauth`. What is still missing is the **deploy pipeline**
(git→build→publish) and a hosted-site surface.

**How DreggNet's infra maps onto it (1:1, same topology):**

| Our deploy-prep piece | DreggNet analog | What it upgrades |
|---|---|---|
| Manual per-surface Caddy site block | `gateway` on-demand-TLS `ask` → `dregg-domains::is_verified` | One block serves *any* verified host; new surfaces/domains need **no Caddyfile edit** |
| Manual DNS subdomain records | `dregg-domains` TXT/CNAME proof-of-control + `LiveDns` | **BYO custom domain per launch/site**, verified, cap-gated |
| Per-domain Let's Encrypt, hand-listed | Caddy on-demand-TLS gated by the `/internal/site-exists` ask | Certs minted on-demand only for proven domains (no `DREGG_SITE_DOMAINS` list to maintain) |
| systemd unit + RUNBOOK per surface | `dregg-deploy` git→build→publish durable pipeline | `dregg deploy <repo>` → live `<name>.dregg.works`, crash-resumable, commit-reproducible |
| Prose rollback in RUNBOOKs | DreggCloud `dreggcloud_ops.py` staging-swap-rollback engine | Real staged deploy + atomic swap + auto-revert |
| Tailscale hand-config, gateway "must join tailnet" (ember-gated step 0) | DreggNet self-hosted `headscale` + `deploy.sh` zigbuild/rsync | A repeatable mesh + cross-build-and-ship flow |
| CORS/security-header discipline (our Caddyfiles already do this well) | Same in DreggNet Caddyfiles + `dregg_strip_forged_identity` cap-auth | Adds password-less **capability forward-auth** for gated operator surfaces |

**The single biggest upgrade** is replacing "one hardcoded Caddy block + DNS record per surface" with
"**on-demand-TLS + a verified-domain registry**," so the full p0 offering (launchpad + trading +
offerings menu + per-launch sites) is served under **one** gateway discipline, and users can point
**their own domains** at a launch. That was the DreggNet marquee, and its breadstuffs realization
now exists in-tree (`deploy/gateway-ask` + `starbridge-apps/domains` — Tier-1 items 1–2 of §6); it
slots directly onto the Tailscale-fronted-hbox topology, pending an edge that runs it.

---

## 5. Classification summary table

| Asset (path) | What it is | Class | Relevance to full p0-offering |
|---|---|---|---|
| `DreggNet/dregg-domains/` | BYO custom-domain + DNS proof-of-control, on-demand-TLS ask | **SUBSTRATE-GENERAL** | ⭐ realized in-tree as `starbridge-apps/domains` (§6 #1) |
| `DreggNet/gateway/{route,types,sitepublish}.rs` | fly-compat API + cap+funding-gated site publish + Host routing | **SUBSTRATE-GENERAL** | the `ask`/forward-auth spine is realized in-tree (`deploy/gateway-ask`, §6 #2); the fly-compat/site-publish API is not |
| `DreggNet/dregg-deploy/` | git→build(sandbox)→publish→live durable pipeline | **SUBSTRATE-GENERAL** | HIGH — ship-a-surface/site from git |
| `DreggNet/deploy/staging/*` (compose, Caddyfile.capauth, deploy.sh, headscale) | staging stack + cap-auth proxy + zigbuild ship + mesh | **OPERATIONAL** | HIGH — reusable deploy/ops config |
| `DreggNet/deploy/observability/` | Prometheus/alertmanager/exporters | **OPERATIONAL** | MED — ops for a live offering |
| `DreggNet/exec/`, `durable/` | wasmi sandbox, crash-resumable metered workflows | **SUBSTRATE-GENERAL** | MED — under deploy/build; may already be re-homed |
| `DreggNet/webapp/hosting` (`SiteRegistry`/`SiteCell`) | "a site is a cell", `<name>.dregg.works` wildcard | **SUBSTRATE-GENERAL** | MED — host a launched token's own page |
| `DreggNet/webauth/` (`dga1_` cap auth) | password-less capability forward-auth service | **SUBSTRATE-GENERAL** | MED — gate operator/admin surfaces |
| `DreggNet/{billing,storage,org,guard}/` | invoices, bucket-is-cell, IAM, abuse quotas | **SUBSTRATE-GENERAL** mechanism / **PRODUCT-PRIVATE** packaging | LOW-MED |
| `DreggNet/control/` fleet/provider control plane | scheduling, EC2/local providers, mesh | **PRODUCT-PRIVATE** | LOW (settlement-ledger math rail-adjacent) |
| `DreggNet/{landing,console,ops,status,attach}/` | server-rendered Rust HTML product surfaces | **PRODUCT-PRIVATE** (branded copy) | LOW — informs design only |
| `DreggCloud/service-cells/` | escrow/lease/market-match/settlement/nullifiers | **SUBSTRATE-GENERAL** (WELD candidate) | MED — overlaps our intent-ring; weld not pull |
| `DreggCloud/dreggcloud-web-verify` + `web/verifier*` | WASM in-browser receipt-chain verifier | **SUBSTRATE-GENERAL** | MED — light-client-in-tab |
| `DreggCloud/{notary-selfhost,notary-live-client}` | real MPC-TLS/TLSNotary daemon + live clients | **SUBSTRATE-GENERAL** | MED — DECO/attested-data carrier |
| `DreggCloud/scripts/dreggcloud_ops.py` | staging-swap-rollback deploy engine | **OPERATIONAL** | MED — real rollback for our RUNBOOKs |
| `DreggCloud/{dreggcloud-house, expedition, native-workbench}` | the operated-House product + game + desktop UI | **PRODUCT-PRIVATE** | LOW |
| `DreggCloud/microsite/`, `DreggNet` marketing copy | branded landing/report pages | **PRODUCT-PRIVATE** | none (never public-pull) |

---

## 6. Recommendation — pull-forward toward the full p0-offering

**Ordered, boundary-respecting. No pulls were performed in this eval; items marked ✅ LANDED have
since been realized in-tree in breadstuffs (as fresh substrate, not copies). The rest remain
evaluated-not-pulled, ember-directed.**

**Tier 1 — the DNS/gateway/deploy layer that closes the p0 gap (SUBSTRATE-GENERAL + OPERATIONAL):**
1. ✅ **LANDED in-tree: the verified-domain registry.** `starbridge-apps/domains` is the breadstuffs
   realization of the `dregg-domains` recommendation — `DomainBinding`/`is_verified`/`site_for_host`,
   the exact hook an on-demand-TLS `ask` consults, with no hardcoded apex (the eval's apex-mismatch
   note is answered by configuration).
2. ✅ **LANDED in-tree: the on-demand-TLS gateway pattern.** `deploy/gateway-ask/` serves the
   `on_demand_tls { ask …/internal/site-exists }` endpoint off the registry plus a capability
   forward-auth gate, and `Caddyfile.on-demand-tls` is the one-wildcard-block replacement for the
   per-surface blocks; `deploy/webauth-edge/Caddyfile.capauth` carries the cap-auth idiom.
3. **Pull-forward `dregg-deploy/`** (git→build→publish pipeline + `sandbox.rs`) as the "ship an
   offering/site from a repo" path — SUBSTRATE-GENERAL, reproducibility built in.
4. **Reuse the OPERATIONAL deploy kit** as *config templates* next to `deploy/aws`: the cap-auth
   Caddyfile discipline (password-less operator gating), the `zigbuild`+rsync `deploy.sh` (the box
   OOMs compiling — we hit the same on hbox), the `headscale` mesh config, and DreggCloud's
   `dreggcloud_ops.py` staging-swap-rollback engine to harden our prose RUNBOOKs.

**Tier 2 — hosting a launched surface as its own site (SUBSTRATE-GENERAL):**
5. **`webapp/hosting` (`SiteRegistry`/`SiteCell`, the `<name>.<apex>` wildcard)** so a token launch
   can get its own hosted page — the "couple a launch to a real hosted site" idea DreggNet only
   *named*. Pairs with `dregg-domains` for BYO-domain-per-launch.
6. **`exec`/`durable`** under (3) if not already re-homed (some agent-platform pieces were ported
   07-09 — census first per the WELD method; the capability may already exist in breadstuffs).

**Tier 3 — weld, don't pull (SUBSTRATE-GENERAL but overlapping):**
7. **`DreggCloud/service-cells`** (escrow/market-match/settlement) overlaps our intent-ring +
   `verified_settle` — a WELD/reconcile, not a fresh copy. **`dreggcloud-web-verify`** (WASM tab
   verifier) and **`notary-*`** (MPC-TLS carrier) align with existing north stars (light-client-in-
   tab, DECO) — evaluate as welds.

**Build-new (do NOT pull — the launchpad/trading half isn't in either repo, and stays public-native):**
- The **launchpad + trading terminal + offerings menu** already exist in breadstuffs (`DREGGFI-*`,
  launchpad-web, drex-web) and are the *public-native* half. p0-parity there is a **wiring/deploy**
  task on top of the pulled DNS/gateway/deploy layer — not a DreggNet pull.

**Never pull (PRODUCT-PRIVATE — boundary):**
- The "DreggNet Cloud" and "operated firmament / House" **product identities**, branded
  landing/console/microsite copy, the fleet/provider control plane, the House operated daemon, the
  Expedition game, the GPUI desktop client. These stay private; at most they *inform* the public
  design.

---

## 7. Honest edges

- **Read-only.** No DreggNet/DreggCloud file modified; no code pulled into breadstuffs; the live
  `:8787` dreggcloud service was not touched. This is EVALUATE + RECOMMEND only.
- **Deploy is parked (ember).** The DNS/gateway/deploy story here is mapped-now, deployed-later; the
  gateway-joins-the-tailnet step is already the ember-gated step 0 in our own RUNBOOKs.
- **Coupling caveat.** Every high-value DreggNet pull path-depends on breadstuffs crates. That mostly
  *helps* (dependencies live in the target), but the agent-platform family was already re-homed
  07-09 — so **census breadstuffs first** before pulling `exec`/`durable`/webcell to avoid a
  duplicate.
- **Apex mismatch — answered in-tree.** DreggNet's `dregg-domains` hardcodes `dregg.works`; the
  breadstuffs realization (`starbridge-apps/domains` + `deploy/gateway-ask`) parameterizes the apex
  (`{$HOSTING_APEX}`, no baked-in domain). The product domain is `dregg.net`; `fg-goose.online` is a
  dead devnet-era domain.
- **Boundary held.** Only SUBSTRATE-GENERAL mechanisms and OPERATIONAL config are recommended for the
  public repo; every product-identity asset is tagged PRODUCT-PRIVATE and left in place.
