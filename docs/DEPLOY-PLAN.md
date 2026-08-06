# Deploy plan — public demo + testnet (deploy scout)

HEADLINE: the fastest public demo needs NEITHER the node, NOR a testnet, NOR the heavy prover. dreggnet-web hosts all 5 games
+ the no-cheat leaderboard + stranger-run re-verification ENTIRELY IN-PROCESS, and its "verify" is deterministic REPLAY
re-execution (a stranger re-runs your run and confirms it), NOT a STARK check. The runnable server exists: the
`dreggnet-web-server` bin (dreggnet-web/src/bin/dreggnet-web-server.rs, a `[[bin]]` target in dreggnet-web/Cargo.toml), with
systemd units + runbooks under deploy/games/ (dregg-web-games.service and the funnel variant that serves on hbox). The honest
framing: the demo verifies by REPLAY (= "anyone re-runs your run and confirms it"); the STARK fold (private-strategy, portable
proof) is the labeled Phase-3 UPGRADE. Deploy caveat (once, for the whole doc): nothing is deployed as a durable public product
— the reproducible build is the P0.

⚑ **DOMAIN FACTS RE-CHECKED 2026-08-05 — the sentence that used to end this paragraph was wrong on
every clause.** It said "fg-goose.online is a dead domain, and the product domain is www.dregg.net."
Today: `headscale.dreggnet.fg-goose.online` is **live** and is the tailnet control plane (it has its
own block in `~/dev/dregg-infra/edge/anchor/Caddyfile`); `www.dregg.net` does **not** point at the
edge box (it is CloudFront/Squarespace, the marketing site); `demo.dregg.net`, named below as "the
planned app subdomain", is **NXDOMAIN**; and the two domains actually registered for the product,
**`dregg.gg` and `dregg.tech`** (2026-08-02), appear nowhere in this doc. The edge serves fourteen
names from one Caddyfile — check it, not this paragraph.

## RANKED PATH
- PHASE 0 — THE STANDALONE WEB DEMO (no node/testnet/prover). BUILT: the `dreggnet-web-server` bin mounts
  router()/catalog_router()/descent_router() and serves the merged app; deploy/games/ carries the units
  (dregg-web-games.service + dregg-web-games-funnel.service — the funnel variant is what runs on hbox), deploy-hbox.sh, and
  two dedicated runbooks (RUNBOOK.md, RUNBOOK-FUNNEL.md). All 5 games, the clickable automatafl board, tug, the re-verified
  leaderboard, and stranger-run replay-verify are green (dreggnet-web/src/{lib.rs, descent.rs}). REMAINING: the durable public
  product surface — a persistent named data-dir under systemd (deploy/PRACTICES.md rule 2: no hand-run production processes)
  + fronting on the product domain (demo.dregg.net is the planned app subdomain; ~/dev/dregg-site is the marketing site).
- PHASE 1 (hours, parallel) — THE DISCORD DAILY. The bot is COMPLETE (reveal cron + live drand + /descent + sqlite + two
  deploy targets + deploy/hbox/RUNBOOK.md). Ops only: place prod tokens (DISCORD_TOKEN/APP_ID/BOT_SECRET), set
  DESCENT_ANNOUNCE_CHANNEL_ID, STOP GRAVITON'S BOT FIRST (two bots on one token double-fire).
- PHASE 2 (hours single-box / days multi-host) — THE TESTNET FEDERATION. One-command genesis (deploy/genesis/generate.sh —
  every validator enrolls a HYBRID ed25519 + ML-DSA-65 key pair, and deploy/genesis/genesis.json carries the ML-DSA roster
  the beacon's PQ finalized-root half consumes) + real BFT + Lean finality + a runnable local n=4
  (scripts/federation-local.sh). Deploy practice lives in deploy/PRACTICES.md; deploy/aws is superseded wholesale (its
  content sits under deploy/aws/SUPERSEDED/ — do not build on it). GAPS (named): n>=4 for fault slack (n=3 is
  unanimity-fragile); multi-host distribution is manual (keys/DNS/cross-host QUIC :9420).
- PHASE 3 — PORTABLE STARK PROOFS (the hard upgrade, NOT demo-blocking). BUILT: the async match-fold PROVING SERVICE
  (dreggnet-prove-service — enqueue -> a worker folds OFF the play path -> status/wait, bounded + metered, the proof
  correctness-identical to the foreground fold, a forged match rejected). So proving is OFF-PATH (the UX fix). The fold's
  per-layer proving auto-dispatches to the GPU backend: prove_turn_chain_recursive routes layer + aggregation proving through
  gpu_backend::{prove_recursion_layer_auto_with_expose, prove_recursion_aggregation_auto_with_expose}
  (circuit-prove/src/ivc_turn_chain.rs:214) — GPU where a working device exists (hbox), CPU otherwise. In-browser: the
  on-device commitment + full VERIFY landed, and tug PROVES in the tab — `proveTugPlayOnDevice` mints the per-play membership
  STARK on-device and `foldTugMatchOnDevice` runs the whole recursion fold to a verify_history-accepted WholeChainProof
  (wasm/src/bindings_multiway_tug.rs; the fold run is the honest heavy-recursion boundary). NAMED SEAM: the service->board
  submit wire — dreggnet-prove-service stops at the MatchProof; handing it to dreggnet_game_board::GameBoard is the caller's.
  Verify is succinct + K-independent (sub-second) so per-entry server verify is cheap regardless.
- PHASE 4 — THE EXTENSION (off critical path — it's the wallet). Store docs all READY; rebuild (./build.sh) + submit; the
  ~50MB wasm is an MV3 size/perf review risk.

## HONEST BLOCKERS
1. no durable public product surface — the games demo has its bin, units, and runbooks, but the public deployment (product
   domain + persistent systemd data-dir + the reproducible-build P0 named in the headline) is the remaining Phase-0 work.
2. the fold is heavy relative to play — but it is off-path (the prove service) and GPU-auto-dispatched, and the demo's
   no-cheat = REPLAY re-execution, so this is a Phase-3 upgrade not a Phase-0 blocker.
3. testnet single-box (no multi-host turnkey; n=3 unanimity-fragile).
4. bot prod tokens + stop-graviton (pure ops).
5. extension rebuild + gitignored 50MB artifact (off critical path).
Hosting: an AWS Graviton EC2 gateway (headscale control-plane + caddy edge) + hbox (x86 build/host, serves the games funnel)
+ persvati (build); Prometheus/Grafana monitoring built (deploy/observability). Domain: the app/demo = demo.dregg.net
(planned subdomain of the product domain www.dregg.net). Key files: dreggnet-web/src/bin/dreggnet-web-server.rs,
dreggnet-web/src/{lib.rs,descent.rs}, node/src/{lib.rs,api.rs,prove_pool.rs,finalization_votes.rs}, procgen-dregg/src/beacon.rs,
scripts/federation-local.sh, deploy/{genesis,games,hbox}/, deploy/PRACTICES.md, docs/ops/OPS-RUNBOOK.md,
discord-bot/src/{main.rs,reveal_cron.rs}, extension/build.sh.
