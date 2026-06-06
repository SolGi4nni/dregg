# Devnet Composition Audit

**Date:** 2026-06-06  
**Scope:** Local Docker devnet (`docker/docker-compose.yml`), AWS Caddy devnet (`deploy/aws/caddy/Caddyfile`), genesis wiring (`deploy/genesis/`), starbridge-apps manifests, legacy `apps/` HTTP services.

**Goal:** A devnet where every *useful* app is deployable end-to-end — browser surfaces, node APIs, and (where applicable) standalone HTTP backends.

---

## Executive Summary

Devnet today is **node-centric**: 3 federation nodes + gallery + discharge-gateway + a thin local proxy. The **4 ready starbridge-apps** (nameservice, identity, subscription, governed-namespace) run through the node/WASM/Studio stack, not as separate containers. **Legacy HTTP apps** (gallery, bounty-board, compute-exchange, privacy-voting) build outside the workspace and are only partially wired. **`deploy/genesis/apps.json` is aspirational** — `dregg-node genesis` never reads it; checked-in `genesis.json` only seeds a faucet + 3 demo agents.

**Critical blocker:** `docker-compose.yml` mounts `./devnet-config/{genesis.json,.devnet,node-*.key}` but **`docker/devnet-config/` does not exist**. `docker compose up` fails until genesis material is generated or symlinked from `deploy/genesis/`.

---

## Current State (What Works vs What Doesn't)

| Layer | Works today | Broken / missing |
|-------|-------------|------------------|
| **3-node federation** | `scripts/test-devnet-cluster.sh` (native binaries) | Docker compose (missing `devnet-config/`) |
| **Node API** | `/api/*`, `/status`, `/ws`, faucet, `/api/starbridge/*` | Rich genesis cells from `apps.json` |
| **Starbridge UI (4 apps)** | Built into `site/dist/starbridge-apps/` via `site/build.js` | AWS Caddy has no explicit `/starbridge-apps/*` handler (relies on `site/dist` catch-all) |
| **Starbridge UI (2 mandate apps)** | Rust crates + manifests (`ready`) | No `pages/`, not in `node/Cargo.toml`, not in Studio catalog |
| **Legacy HTTP apps** | Runnable via `cargo` from `apps/*` dirs | Not workspace members; not in Dockerfile; not in compose |
| **DeFi (stablecoin/AMM/orderbook)** | Documented in `deploy/genesis/apps.json` | **No Rust crates** — design docs only (`apps/*/CLAUDIT.md`) |
| **Governed namespace HTTP** | AWS: `/namespace/*` → `:3003`, `/app/namespace/*` static | `apps/governed-namespace/` retired; starbridge version has no standalone HTTP server |
| **Discord bot** | AWS systemd + Caddy `/discord-bot/*` | Not in Docker compose |

---

## Proof vs Runtime

Maps Lean proof modules (`metatheory/Dregg2/Apps/`) to Rust runtime status and how each app is composed on devnet.

| Lean module | Rust runtime | Composition model | Devnet path |
|-------------|--------------|-------------------|-------------|
| **NameService** / NameserviceGated | `starbridge-apps/nameservice` ✅ | Starbridge cell program + WASM factory + node MCP tools | `/starbridge-apps/nameservice/`, node `/api/starbridge/*` |
| **Identity** / IdentityGated | `starbridge-apps/identity` ✅ | Starbridge + `dregg-credentials` | `/starbridge-apps/identity/` |
| **Subscription** / SubscriptionGated | `starbridge-apps/subscription` ✅ | Starbridge pub/sub cell | `/starbridge-apps/subscription/` |
| **GovernedNamespace** / GovernedNamespaceGated | `starbridge-apps/governed-namespace` ✅ | Starbridge DFA route table + governance cell | `/starbridge-apps/governed-namespace/`; AWS legacy `/namespace/*` (stale `:3003`) |
| **CompartmentWorkflowMandate** (+ Gated, CrossVatBridge) | `starbridge-apps/compartment-workflow-mandate` 🟡 scaffold | Starbridge mandate cell (MonotonicSequence cursor) | Manifest only — no page, not embedded in node |
| **StorageGatewayMandate** (+ Gated, Core) | `starbridge-apps/storage-gateway-mandate` 🟡 scaffold | Starbridge mandate cell (volume budget) | Manifest only — no page, not embedded in node |
| **Gallery** / GalleryGated | `apps/gallery` (`dregg-gallery`) 🟡 legacy HTTP | Standalone axum server + frontend; **not** starbridge-ported | Docker `gallery:3040`, `/gallery/*` (local Caddy only) |
| **BountyBoard** / BountyBoardGated | `apps/bounty-board` 🟡 legacy HTTP | Standalone axum; manifest `status: unported` | Not in compose/Caddy |
| **ComputeExchange** / ComputeExchangeGated | `apps/compute-exchange` 🟡 legacy HTTP | Standalone axum; manifest `status: unported` | Not in compose; **port conflicts with gallery (3040)** |
| **PrivacyVoting** / PrivacyVotingGated | `apps/privacy-voting` 🟡 legacy HTTP | Standalone axum (`:3100`); manifest `status: unported` | Not in compose/Caddy |
| **SealedBidAuction** | (subset of gallery Lean + `apps/gallery` private Vickrey) | Legacy gallery submodule | Via gallery only |
| **MultisigVote** | — ❌ | Proof only | — |
| **AtomicSwap** | — ❌ | Proof only | — |
| **AgentOrchestration** | — ❌ | Proof only | — |
| **ConservationBridge** | — ❌ | Proof / bridge pattern | — |
| **CrossCellCovenantGated** | — ❌ | Proof only | — |
| **EpistemicSheaf** | — ❌ | Proof only | — |
| **OrbitalScreen** | — ❌ | Proof only | — |
| **RightOfWay** | — ❌ | Proof only | — |
| **WhoYields** | — ❌ | Proof only | — |
| **Stablecoin / AMM / Orderbook** (genesis `apps.json`) | — ❌ no crates | Aspirational CellProgram names (`stablecoin_cdp_v1`, etc.) | Documented in genesis README only |

**Legend:** ✅ shipped starbridge-app · 🟡 runnable legacy or scaffold · ❌ Lean-only (no Rust app surface)

**Two composition models:**

1. **Starbridge (target):** FactoryDescriptor → sovereign/hosted cell → browser page loads WASM + extension cclerk → turns via node. No per-app HTTP container.
2. **Legacy HTTP (transitional):** Standalone axum binary in `apps/*` → Caddy reverse proxy → vanilla JS frontend. Starbridge manifests mark these `unported` with `legacy_path`.

---

## Starbridge-Apps Manifest Status

| App | `manifest_health.status` / `status` | `page` | In workspace | In `node/Cargo.toml` | Has `pages/index.html` |
|-----|--------------------------------------|--------|--------------|----------------------|------------------------|
| nameservice | ready | ✅ | ✅ | ✅ | ✅ |
| identity | ready | ✅ | ✅ | ✅ | ✅ |
| subscription | ready | ✅ | ✅ | ✅ | ✅ |
| governed-namespace | ready | ✅ | ✅ | ✅ | ✅ |
| compartment-workflow-mandate | ready | ✅ (path declared) | ✅ | ❌ | ❌ |
| storage-gateway-mandate | ready | ✅ (path declared) | ✅ | ❌ | ❌ |
| gallery | **unported** | null | ❌ | ❌ | ❌ (use `apps/gallery/frontend`) |
| bounty-board | **unported** | null | ❌ | ❌ | ❌ |
| compute-exchange | **unported** | null | ❌ | ❌ | ❌ |
| privacy-voting | **unported** | null | ❌ | ❌ | ❌ |

**Unported manifest fix (PR-sized):** Until port completes, add `runtime_mode: "legacy-http"`, `listen_port`, and `caddy_prefix` fields so Studio/Caddy can route legacy apps without pretending they are starbridge-ready. Example for gallery:

```json
"runtime_mode": "legacy-http",
"legacy_listen": "gallery:3040",
"caddy_prefix": "/gallery"
```

---

## Genesis / `apps.json` Wiring Gap

| File | Claimed purpose | Actual wiring |
|------|-----------------|---------------|
| `deploy/genesis/apps.json` | 7 app families, fixed cell IDs, program names | **Not read** by `node/src/genesis.rs` or `generate.sh` |
| `deploy/genesis/routes.json` | DFA route table | **Not read** by genesis generator |
| `deploy/genesis/accounts.json` | 10 pre-funded accounts | **Not read** — genesis creates faucet + alice/bob/carol only |
| `deploy/genesis/genesis.json` | Canonical devnet state | Matches minimal `run_genesis()` output (4 cells) |
| `docker/devnet-config/` | Compose volume source | **Missing directory** |

`deploy/genesis/README.md` describes a rich devnet that **does not match** the generator implementation. Either implement ingestion or downgrade README to match reality.

**Target genesis cells for useful apps (minimum):**

| App | Suggested genesis action |
|-----|--------------------------|
| nameservice | `CreateCellFromFactory` with VK `737461726272696467652d6e616d65736572766963652d666163746f72792121` |
| identity issuer | VK `737461726272696467652d6964656e746974792d6973737565722d6661637421` |
| subscription topic | VK `737461726272696467652d737562736372697074696f6e2d666163746f727921` |
| governed-namespace root | VK `737461726272696467652d676f7665726e65642d6e616d6573706163652d6661` |
| CWM mandate | VK `737461726272696467652d63776d2d6d616e646174652d666163746f72792121` |
| SGM gateway | VK `737461726272696467652d73676d2d6d616e646174652d666163746f72792121` |
| Legacy gallery/bounty/compute/voting | Keep as HTTP services OR port to factories (separate track) |

---

## Port Allocation (Canonical — fix conflicts)

| Service | Current default | Proposed devnet port |
|---------|-----------------|----------------------|
| dregg-node (node-0) | 8420 | 8420 |
| dregg-node (node-1/2) | 8421/8422 | 8421/8422 |
| local proxy | 8400 | 8400 |
| **dregg-gallery** | 3040 | **3040** |
| **dregg-bounty-board** | 3030 | **3031** |
| **compute-exchange** | 3040 ⚠️ conflicts | **3042** |
| **dregg-privacy-voting** | 3100 ⚠️ collides w/ relay docs | **3043** |
| discharge-gateway | 8480 (host) / 8080 (container) | 8480 |
| discord-bot | 8080 (AWS) | 8080 |
| static explorer | 3000 | 3000 |
| governed-namespace (legacy AWS) | 3003 | **remove** — use starbridge |

---

## Prioritized Checklist (PR-Sized Tasks)

Ordered by leverage. Each item is one reviewable PR.

### P0 — Devnet boots at all

1. **[BLOCKER] Materialize `docker/devnet-config/`**  
   - Add `scripts/prepare-docker-devnet.sh` that runs `deploy/genesis/generate.sh --force` and copies/symlinks into `docker/devnet-config/`.  
   - Document in `docker/README.md`.  
   - *Acceptance:* `docker compose up -d` reaches healthy `node-0` + `gallery`.

2. **[BLOCKER] Add `apps/*` to workspace `members`**  
   - Add `apps/gallery`, `apps/bounty-board`, `apps/compute-exchange`, `apps/privacy-voting` to root `Cargo.toml`.  
   - *Acceptance:* `cargo build --release -p dregg-gallery -p dregg-bounty-board -p compute-exchange -p dregg-privacy-voting` from repo root.

3. **Fix port collisions**  
   - Change `compute-exchange` default listen to `:3042`; document canonical table above in `apps/README.md`.  
   - Update `scripts/test-devnet-cluster.sh` to use distinct ports when starting gallery + compute-exchange together.  
   - *Acceptance:* cluster test starts both without bind error.

### P1 — Starbridge apps fully reachable

4. **Caddy: explicit `/starbridge-apps/*` on AWS and Docker**  
   - AWS `deploy/aws/caddy/Caddyfile`: add `handle /starbridge-apps/*` → `root * /opt/dregg/site/dist` + `file_server` **before** catch-all.  
   - Docker `docker/Caddyfile`: mount `site/dist` (or build step) and serve `/starbridge-apps/*`, `/starbridge.html`, `/explorer*`.  
   - *Acceptance:* `curl localhost:8400/starbridge-apps/nameservice/manifest.json` returns 200 in compose.

5. **Embed mandate starbridge-apps in node**  
   - Add `starbridge-compartment-workflow-mandate` and `starbridge-storage-gateway-mandate` to `node/Cargo.toml`; call `register()` at node startup (mirror nameservice pattern in `app-framework`).  
   - Preload factory VKs in `wasm/src/runtime.rs` factory registry.  
   - *Acceptance:* `teasting` cross-app test can create CWM/SGM cells from factory.

6. **Add mandate app pages + Studio catalog**  
   - Create `starbridge-apps/{compartment-workflow-mandate,storage-gateway-mandate}/pages/index.html` (+ inspectors/turn-builders JS).  
   - Add IDs to `site/src/_includes/studio/starbridge.js` `STARBRIDGE_APP_IDS`.  
   - *Acceptance:* Starbridge picker shows 6 apps; each loads without 404.

7. **Rebuild and ship `site/dist` in Docker compose**  
   - Add `site-builder` service or multi-stage copy of `site/dist` + `starbridge-apps` into proxy container.  
   - *Acceptance:* full browser demo works at `:8400/starbridge.html` without host-side `npm run build`.

### P2 — Legacy HTTP apps in compose

8. **Extend `docker/Dockerfile` with legacy app stages**  
   - Build targets: `bounty-board`, `compute-exchange`, `privacy-voting` (gallery already exists).  
   - Copy respective `frontend/` trees where present.

9. **Add compose services + Caddy routes for legacy apps**  
   ```yaml
   bounty-board:    # :3031, DREGG_NODE_URL=http://node-0:8420
   compute-exchange:  # :3042
   privacy-voting:    # :3043
   ```  
   - Docker Caddy: `/bounty/*`, `/compute/*`, `/voting/*` reverse_proxy.  
   - AWS Caddy: same prefixes (remove stale `/namespace/*` → `:3003` or repoint to starbridge).

10. **Extend `scripts/test-devnet-cluster.sh`**  
    - Start all 4 legacy HTTP apps after nodes healthy.  
    - Health-check each `/health`.  
    - Optionally hit one starbridge manifest via built `site/dist`.  
    - *Acceptance:* script exits 0 with 3 nodes + 4 apps healthy.

### P3 — Genesis truth + manifest hygiene

11. **Wire `apps.json` into genesis generation (or delete drift)**  
    - **Option A (preferred):** Extend `node/src/genesis.rs` to ingest `deploy/genesis/apps.json` + `routes.json`, emit factory-born cells with VKs from starbridge manifests.  
    - **Option B:** Mark `apps.json` `status: "planned"` and rewrite `deploy/genesis/README.md` to match minimal genesis.  
    - *Acceptance:* post-genesis `/api/cells` includes nameservice + identity cells.

12. **Fix unported manifest records**  
    - For gallery/bounty/compute/privacy-voting: add `runtime_mode`, ports, Caddy prefixes (see above).  
    - Set `manifest_health: { "status": "legacy-http", "porting_target": "starbridge-apps/<id>" }`.  
    - *Acceptance:* Studio starbridge catalog shows correct badge; no `page: null` without explanation.

13. **Add subscription + mandates to `deploy/genesis/apps.json`**  
    - Replace fictional `gallery_auction_v1` / `stablecoin_cdp_v1` program strings with starbridge `factory_vks` where crates exist.  
    - Defer stablecoin/AMM/orderbook entries until crates land.  
    - *Acceptance:* `apps.json` is an accurate deploy manifest for everything that has Rust code.

### P4 — AWS parity + smoke

14. **AWS `update.sh`: build legacy apps + web artifacts**  
    - Build `dregg-gallery`, bounty-board, compute-exchange, privacy-voting alongside node.  
    - Run `scripts/build-web-artifacts.sh` before `deploy-site.sh`.  
    - *Acceptance:* `scripts/devnet-smoke.sh` passes against public URL with starbridge assets.

15. **Discord bot optional compose profile**  
    - `docker compose --profile discord up` adds `discord-bot` + Caddy `/discord-bot/*`.  
    - *Acceptance:* matches AWS Caddy routing for local parity.

---

## Docker / Workspace: What to Add

### Workspace members (root `Cargo.toml`)

```
apps/gallery
apps/bounty-board
apps/compute-exchange
apps/privacy-voting
```

Already members: all `starbridge-apps/{nameservice,identity,subscription,governed-namespace,compartment-workflow-mandate,storage-gateway-mandate}`.

### Docker Compose services to add

| Service | Image stage | Depends on | Host port |
|---------|-------------|------------|-----------|
| `bounty-board` | `bounty-board` | `node-0` healthy | 3031 |
| `compute-exchange` | `compute-exchange` | `node-0` healthy | 3042 |
| `privacy-voting` | `privacy-voting` | `node-0` healthy | 3043 |
| `site` or `proxy` volume | static `site/dist` | build step | via `proxy:8400` |

### Caddy routes to add (both environments)

| Path | Backend |
|------|---------|
| `/starbridge-apps/*` | `site/dist` static |
| `/starbridge.html` | `site/dist` |
| `/gallery/*` | `gallery:3040` (already in docker Caddy) |
| `/bounty/*` | `bounty-board:3031` |
| `/compute/*` | `compute-exchange:3042` |
| `/voting/*` | `privacy-voting:3043` |
| `/discharge/*` | `discharge-gateway:8080` (docker only today) |

Remove or repoint AWS `/namespace/*` → `:3003` (no listener in current tree).

---

## Testing Matrix

| Script | Covers | Gap |
|--------|--------|-----|
| `scripts/test-devnet-cluster.sh` | 3 nodes, faucet, bounty + compute (optional) | No Docker, no privacy-voting, port clash, no starbridge |
| `scripts/devnet-smoke.sh` | Node API, starbridge.html, `/api/starbridge/receipts` | No legacy HTTP apps, no compose |
| `docker compose up` | Intended full stack | **Blocked** on `devnet-config/` |

**Target:** one `scripts/test-devnet-docker.sh` wrapping compose up + smoke curls for nodes, 4 legacy apps, 6 starbridge manifests.

---

## Recommended PR Sequence

```
PR1  docker/devnet-config bootstrap + compose fixes
PR2  workspace members + port table
PR3  Caddy starbridge-apps routes (docker + AWS)
PR4  mandate apps: node embed + pages + catalog
PR5  Dockerfile + compose legacy services
PR6  genesis apps.json ingestion (or README downgrade)
PR7  manifest unported → legacy-http metadata
PR8  test-devnet-cluster + docker smoke expansion
PR9  AWS update.sh builds all app binaries
PR10 discord compose profile (optional)
```

---

## References

- `docker/docker-compose.yml` — 3 nodes, gallery, discharge-gateway, proxy (no legacy apps)
- `docker/Caddyfile` — `/api`, `/gallery`, `/discharge` only
- `deploy/aws/caddy/Caddyfile` — node API, explorer, playground, starbridge shell; **no** per-app HTTP routes for bounty/compute/voting
- `deploy/genesis/apps.json` — aspirational 7-app manifest (not wired)
- `node/src/genesis.rs` — minimal genesis (faucet + 3 agents)
- `site/build.js` — copies `starbridge-apps/` → `site/dist/starbridge-apps/`
- `site/src/_includes/studio/starbridge.js` — catalog lists 8 IDs; 4 unported
- `apps/README.md` — documents apps; ports disagree with code defaults
- `starbridge-apps/README.md` — canonical userspace model