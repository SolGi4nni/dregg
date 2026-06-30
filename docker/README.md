# `dregg` Devnet

Launch a local 3-node federation with one command.

## Which semantics does the devnet run?

The devnet nodes execute turns on the **verified Lean executor**
(`metatheory/Dregg2/`, the source of truth, via `dregg-lean-ffi`): on native
builds it is the **authoritative** state producer on the commit path by default.
The legacy dregg1 Rust executor (`dregg-turn`) runs as a **differential
cross-check** that re-executes each turn and compares its commit decision against
the Lean path. Set `DREGG_LEAN_PRODUCER=0` in the node service env to fall back
to Rust-only production (e.g. for differential debugging); on targets where Lean
cannot link (wasm32/zkvm) the Rust producer runs in its place.

## Quick Start

```bash
./docker/start-devnet.sh
```

This will:
1. Build the site (`site/dist`) if missing (or pass `--rebuild-site` to force)
2. Generate genesis configuration (keys + genesis.json) in `docker/devnet-config/`
3. Build the Docker image
4. Start 3 validator nodes, gallery, discharge gateway, site, and reverse proxy

## Endpoints

| Service        | URL                                      | Description                          |
|----------------|------------------------------------------|--------------------------------------|
| Proxy          | http://localhost:8400                    | Unified entry (API, gallery, site)   |
| Node 0         | http://localhost:8420                    | API + faucet enabled                 |
| Node 1         | http://localhost:8421                    | API                                  |
| Node 2         | http://localhost:8422                    | API                                  |
| Gallery        | http://localhost:3040                    | Gallery backend + frontend           |
| Discharge      | http://localhost:8480                    | Macaroon discharge gateway           |
| Explorer       | http://localhost:3000                    | Block explorer UI                    |

### Via proxy (`:8400`)

| Path                  | Backend              | Description                    |
|-----------------------|----------------------|--------------------------------|
| `/api/*`              | Federation nodes     | Round-robin across 3 nodes     |
| `/gallery/*`          | Gallery              | Gallery API + frontend         |
| `/discharge/*`        | Discharge gateway    | Third-party caveat discharge   |
| `/starbridge-apps/*`  | Site                 | Starbridge app bundles         |
| `/_includes/*`        | Site                 | Studio/runtime includes        |
| `/assets/*`, `/pkg/*` | Site                 | Static assets + WASM packages  |
| `/studio`             | Site                 | Studio UI                      |
| `/starbridge`         | Site                 | Starbridge shell               |
| `/learn/*`            | Site                 | Documentation                  |
| `/apps`               | Site                 | Apps catalog                   |
| `/health`             | Proxy                | Proxy health check             |

## Faucet

Node 0 has the faucet enabled. Request computrons for any cell:

```bash
curl -X POST http://localhost:8420/api/faucet \
  -H 'Content-Type: application/json' \
  -d '{"recipient": "<64-hex-char-cell-id>", "amount": 1000}'
```

Rate limit: 1 request per recipient cell per minute. Max 10000 per request.

## Manual Genesis

Generate configuration without Docker:

```bash
cargo run -p dregg-node -- genesis \
  --validators 3 \
  --epoch-length 1000 \
  --checkpoint-interval 100 \
  --output ./docker/devnet-config/
```

## Stop

```bash
docker compose -f docker/docker-compose.yml down
```

## Logs

```bash
docker compose -f docker/docker-compose.yml logs -f
docker compose -f docker/docker-compose.yml logs -f node-0
```

## Reset

Remove all data volumes and regenerate:

```bash
docker compose -f docker/docker-compose.yml down -v
rm -rf docker/devnet-config/*
./docker/start-devnet.sh
```