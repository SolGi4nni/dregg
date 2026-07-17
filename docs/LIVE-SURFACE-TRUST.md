# Live-Surface Trust — what the deployed surfaces actually trust today

*Maintained by hand. This is the honest composition of the LIVE surfaces at current resolution —
not the intended resolution, not the strongest leg that exists behind a seam, but what a stranger
touching the running system is actually relying on right now.*

The point of this page: dregg labels each inadequacy honestly *in place*, but the **composition**
— "what does the live demo trust when you add up all its legs" — lived nowhere until someone
assembled it by hand. This is that assembly, kept current. It complements `docs/TRUST-LEVELS.md`
(the verification *ladder*, a per-object concept) by reporting, per *deployed surface*, which rung
each leg actually stands on.

Legend: **REAL** = the strong leg is on the live path · **MODELED** = a deliberate stand-in with
the real leg built behind a seam · **DEAD** = the leg's target is down and the surface fails
closed. Every MODELED/DEAD row links the seam that upgrades it.

Last hand-verified against code: 2026-07-17.

---

## Web games — `https://hbox-dregg.skunk-emperor.ts.net` (kubo/funnel on hbox)

| Leg | Status | Reality |
|---|---|---|
| Rule enforcement | **REAL** | Every move is a real `WorldCell` turn; an illegal move is a `WorldError::Refused` committing nothing. This is the strong leg and it is live. |
| Turn verification | **MODELED** (replay, not proof) | `/verify` and the boards re-verify by **in-process re-execution**, not by checking a STARK. The fold path is real but `#[ignore]` SLOW; the async prove-service is scaffold. Seam: `dreggnet-prove-service`; roadmap G9 option C. |
| Player identity | **MODELED** (self-asserted) | Web actor = `blake3(dregg_user cookie)` — a self-asserted string; any legal move can be made as anyone. The **signed** path exists both ends now (extension `signOfferingTurn` ↔ `advance_signed`); the web `act-signed` route is the join (Track E1, landing). Until a surface routes through it, web identity is asserted, not signed. |
| Session durability | **REAL** | `FileResumeStore` weld — sessions survive restart, resume by replay, a tampered log refuses to reopen. |
| Session bounds | **REAL** (host-layer) | `SessionPolicy` quota/rate/TTL/LRU in `OfferingHost`; refusals are 429/409. The legacy single-offering `WebState` surface (`/session/{id}`) is NOT yet on the policied host — named follow-up. |
| Node anchoring | **DEAD → fail-closed** | Offering play is in-process (dregg-the-library). Only Descent *settles*, and its `DREGG_NODE_URL` → `:8420` is down; runs rank in-process but do not anchor. The hbox `dregg-node` unit (TODO-1) is the fix; catalog games get the settle seam in G9 option B. |

## The Descent — daily roguelite

| Leg | Status | Reality |
|---|---|---|
| Where you play | Discord bot (`/descent play`) | Web has the **board** (`/descent`, run cards, `POST /descent/submit`) but no play UI yet — Track E2 registers `DailyDescentOffering` in the web catalog. |
| Daily beacon | **MODELED when the cron hasn't fired** | Live drand `quicknet` (BLS-verified) via a 5-min reveal cron; absent that, a **hardcoded pinned round** — same dungeon until the cron reaches drand. Now labeled in the footer ("beacon: PINNED fallback"). Seam: a live round-fetch client (the `dice` verification is done; only the fetch is out). |
| No-cheat leaderboard | **REAL** | A `Completion` ranks only if it re-executes to the declared win; every board row is replay-verified on boot; a tampered row cannot resurrect a cheat. Durable (sqlite). |
| Permadeath character | **REAL on the bot** | `WriteOnce`-final death, persisted per derived identity. On web (once E2 lands) permadeath keyed to a cookie is **forgeable** until identity is signed (E1) — the surface must say so. |

## Discord bot — AWS edge container

| Leg | Status | Reality |
|---|---|---|
| Identity | **MODELED** (custodial) | Real ed25519 keys, but derived from `BOT_SECRET` — the bot can sign as any user; compromise of the secret = every user's identity. By design (custodial handles); the non-custodial upgrade is the same signed seam. |
| Payments | **REAL-selection** (`e91222144`) | `select_watcher` now returns a real `SolanaWatcher`+`RpcAccountFetcher` on a real-network config and REFUSES the mock on mainnet (`WatcherSelectError::MockOnMainnet`); an empty RPC is a loud `RpcMissing`. Watch-only, no seed. Mainnet arming + seed-custody split stay ember-gated. |
| **No live-path mocks** | **REAL / verified 2026-07-17** | Adversarial audit across discord-bot/telegram/wechat traced every mock/stub/fixture: all are `#[cfg(test)]`-confined, honestly-gated (`HERMES_LIVE_LLM=1`, the free-tier scripted narrator self-reports "scripted (free)"), or not-deployed-gaps (telegram/wechat are lib-only). The live LLM path produces only real HTTP/Bedrock/ollama/on-box `LocalBrain` completions. Verdict: **the live bot paths reach no mock.** |
| Rule enforcement / boards | **REAL** | Real executor turns, replay-verified boards, BLS-verified beacon (same pinned fallback as above). |
| Hosting | **fragile** | Runs on the tailnet-exit box (DO-NOT-STOP) from a ~2-week-old unreproducible image; re-home to persvati is a deferred ops lane. |

## IPFS node — kubo on hbox (LIVE 2026-07-17)

| Leg | Status | Reality |
|---|---|---|
| Content addressing | **REAL** | A dregg blake3 commitment IS a CIDv1; publish/fetch re-witnesses every block; a universe fetched through the **public** ipfs.io gateway re-derives its exact commitment. Observed end-to-end. |
| Authorship binding | **REAL** | UniverseId (authorship, over semantics) and CID (transport, over bytes) joined by re-derivation — the transport is never trusted; the wire carries only constructor inputs. |
| Durability | **single-node** | One hbox node = content as durable as hbox. Third-party pinning (`PinningServiceClient`) is format-tested; picking a provider is an ember decision. Reboot-survival unobserved (hbox is co-tenant). |
| Unit hardening | **reduced, honestly** | hbox's user manager can't apply the `Protect*` sandbox set; the units keep `NoNewPrivileges` and document the rest as `#hbox`-disabled (the games-funnel unit had been silently running this way; both are now de-fossiled). |

---

## The through-line

Every REAL row is an *object-level* guarantee — the executor, the content address, the no-cheat
replay. Most MODELED/DEAD rows are *meta-level* or *deployment* gaps: identity binding, node
anchoring, live feeds, hosting. That asymmetry is the standing work — the object level has teeth,
the meta level is catching up. See the game-affordances closure ledger
(`docs/GAME-AFFORDANCES-MAP.md` §8) for each seam's status and the plan
(`give-the-meta-level-teeth`) for the campaign closing them.
