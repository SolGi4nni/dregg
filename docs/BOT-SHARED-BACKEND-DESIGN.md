# Discord + Telegram Shared-Backend Convergence — Design

*2026-07-17. Companion to `docs/BOT-EXCELLENCE-BACKLOG-2026-07-17.md` (items #15, #25, #29,
#32 all get easier after this). Design + seam skeleton only; the cutover is scheduled work.*

## What is true today (verified by reading, at HEAD)

The frontend-agnostic backend already exists and already carries every offering:
`dreggnet_offerings::OfferingHost` (`dreggnet-offerings/src/host.rs:305`) — `register` /
`ensure_open` / `advance` / `advance_collective` / `render_for` / `actions_for` / `verify`,
with `!Send` sessions confined to whatever thread builds the host.

What does NOT exist is one place that says **what the DreggNet catalog is**. The 18-offering
portfolio (5 games + 8 RPG feature surfaces + 5 service offerings) is registered in **four
hand-maintained copies**:

| copy | where | shape |
|---|---|---|
| web | `dreggnet-web/src/lib.rs:1232` `catalog_default_host` + `:1296` `register_non_game_offerings` + `demo_host` (`:2138`) | the original; electorate = `blake3("alice"/"bob")` |
| telegram | `dreggnet-telegram/src/host.rs:416` `telegram_default_host` | byte-level re-statement of all 18 registrations, electorate parameterized |
| wechat | `dreggnet-wechat/src/host.rs:490` `wechat_default_host` | third re-statement |
| discord | no `OfferingHost` at all | bespoke: per-offering-TYPE `Store<O>` threads + `DiscordOffering` impls + an 18-arm static type match in `offering.rs:1337/:1400` |

Plus **four byte-peer copies of `SeatedTug`** (the seat-claiming multiway-tug adapter):
`dreggnet-web/src/seated.rs:25`, `dreggnet-telegram/src/seated.rs`,
`dreggnet-wechat/src/seated.rs:27`, `discord-bot/src/commands/portfolio.rs` (~line 60).
And **two byte-peer copies of `HostThread`** (the `!Send`-host job-channel handle):
`dreggnet-web/src/lib.rs:1118`, `dreggnet-telegram/src/host.rs:83` (wechat has a third).

(One correction to the brief: `dreggnet-telegram` does *not* register few offerings — at HEAD
`telegram_default_host` reaches full 18-offering parity. It reached it by **duplicating** the
registration list, which is exactly the disease. The stale doc-comment on `TelegramHost::new`
(`host.rs:161`, "dungeon + council + market") is drift evidence of the same disease.)

## What makes Discord and Telegram DRIFT today

1. **Offering-set drift (the registration lists).** Adding an offering means editing four
   registration sites, plus for Discord: a `DiscordOffering` impl, `PLAY_KEYS`
   (`portfolio.rs:335`), two arms in `route_component`/`route_modal` (`offering.rs:1341/:1404`),
   and the `main.rs` command registry. Nothing checks the four lists agree. The duplicated
   *content* drifts too: council proposals ("Fund the archive"=42, "Ratify the charter"=7,
   quorum 2), grain budget (1000), and every catalog title string exist as 4 unchecked copies.

2. **Store drift (the real architectural fork).** Web/Telegram/WeChat: ONE `OfferingHost` on a
   `HostThread`, sessions keyed by chat-scoped `SessionId`, offerings registered ONCE so
   `dreggnet_surfaces::register_surfaces` mounts **one `SharedWorld` across trade/inventory/craft**
   (the craft→inventory→trade composition works). Discord: one `Store<O>` thread PER OFFERING
   TYPE keyed by raw channel `u64`, offering value **rebuilt per open** — so every `/play trade`
   gets a fresh `SharedWorld::demo("Adventurer")` and the composition is severed
   (`portfolio.rs:403,413,436`; backlog #15). Also `open_in` silently replaces live sessions
   (backlog #32) — a policy web already solves with `SessionPolicy`/lifecycle, which Discord's
   bespoke store can never inherit.

3. **Identity drift (who the actor is).**
   - Discord: `UserCipherclerk::derive(bot_secret, user_id, federation_id)` → pubkey hex
     (`offering.rs:296`) — **federation-bound**.
   - Telegram: `TelegramCipherclerk::derive(bot_secret, uid)` → pubkey hex — **no federation
     binding** (a real drift bug: the same uid+secret collides across federations).
   - Web: `blake3(username)` hex (`dreggnet-web/src/lib.rs:531`) — demo-grade, not a key.
   Council electorates are then built three different ways from these. Convergence does NOT mean
   one derivation (uid spaces are platform-native); it means one **shape** — `DreggIdentity =
   hex(ed25519 pubkey derived from (bot_secret, platform_uid, federation_id))` — and the
   electorate always expressed as `Vec<[u8;32]>` pubkeys handed to the shared registrar.

4. **Session-durability drift.** Web has `demo_host_over` (move-log persistence + replay-verified
   resume + `SessionPolicy`). Telegram and Discord are in-memory. Once all frontends build their
   host through one function, web's persistence wrapper becomes reachable by all of them instead
   of being a web-only feature.

## The seam: a new small crate `dreggnet-catalog`

**Why not `dreggnet-offerings`:** the registrar must depend on every offering crate
(council/market/doc/names/compute/grain/hermes/surfaces/automatafl/tug) and those crates all
depend on `dreggnet-offerings` for the `Offering` trait — putting the registrar there is a
dependency **cycle**. Dead on arrival.

**Why not `dreggnet-surfaces`:** no cycle (the other offering crates don't dep it), but it drags
9 new offering deps into a crate whose charter is "the do-once RPG feature batch", and every
consumer of surfaces-the-library would pay for catalog-the-registry. Charter muddle.

**Why a new crate works for BOTH workspaces:** `discord-bot` is a standalone workspace that
already path-deps root-workspace members (`discord-bot/Cargo.toml:163-203` — offerings,
surfaces, council, market, …; its header comments document this exact pattern). A root-workspace
member `dreggnet-catalog` is consumable by `dreggnet-web`, `dreggnet-telegram`,
`dreggnet-wechat` (root workspace) AND `discord-bot` (path dep) with **no cycle**: nothing in
the catalog crate depends on any frontend.

### The exact seam

```
dreggnet-catalog/src/lib.rs:

pub struct CatalogConfig { council_members: Vec<[u8;32]>, council_quorum, grain_budget, … }
pub fn build_full_catalog(host: &mut OfferingHost, cfg: &CatalogConfig)   // THE seam
pub fn full_catalog_host(cfg: &CatalogConfig) -> OfferingHost             // convenience
pub mod seated { pub struct SeatedTug; }   // the ONE copy of the seat-claiming adapter
```

Everything platform-specific stays OUT: the config carries derived pubkeys (already `Send`
plain data), never a cipherclerk or a uid. The host is built on whatever thread the frontend's
`HostThread::spawn` closure runs on, preserving the `!Send` confinement discipline unchanged.

Skeleton landed at: `dreggnet-catalog/Cargo.toml` + `dreggnet-catalog/src/lib.rs` (registrars
complete, ported from the web/telegram byte-identical copies; parity test included) +
`dreggnet-catalog/src/seated.rs` (signature-complete, three cited-port `todo!` bodies).

### Companion move (same convergence, different seam)

`HostThread` deps only `std` + `OfferingHost` → move ONE copy into `dreggnet-offerings` as
`dreggnet_offerings::host_thread::HostThread` (additive module; web/telegram/wechat re-export
theirs as deprecated aliases during cutover). It is a property of the `!Send` host, so the
trait crate is its natural home; it must NOT go in `dreggnet-catalog` (Discord's adapter layer
will want `HostThread` even in intermediate states where it builds a partial host).

## How the convergence removes each drift

1. **One list.** All four `*_default_host` bodies become `full_catalog_host(&cfg)` one-liners.
   Adding an offering = one registration in `build_full_catalog` + (for Discord, until Phase C)
   its custom-id key. A parity test in `dreggnet-catalog` asserts `list_offerings().len()` and
   the exact key set — the number 18 stops being folklore.
2. **One store architecture.** Phase C moves Discord onto `OfferingHost` behind the (now shared)
   `HostThread`, sessions keyed by a channel-scoped `SessionId` — which is what restores the
   shared `SharedWorld` composition (backlog #15's substrate) and makes web's
   `SessionPolicy`/persistence applicable to chat surfaces.
3. **One identity shape.** `CatalogConfig.council_members: Vec<[u8;32]>` forces every frontend
   to express its electorate as derived pubkeys; the telegram missing-federation-binding drift
   gets fixed in `TelegramCipherclerk::derive` as its own small item (flagged here, not smuggled
   into the refactor).
4. **One `SeatedTug`.** Four byte-peers collapse into `dreggnet_catalog::seated`.

## Cutover phases (each independently landable, each behavior-preserving)

- **Phase A — the crate exists. LANDED (Repair, 07-17).** `dreggnet-catalog` is a root-workspace
  member; the `seated.rs` bodies are the verbatim web port; the in-crate parity test pins
  `full_catalog_host` to `CATALOG_KEYS`.
- **Phase B — web/telegram/wechat delegate. TELEGRAM LANDED (Repair, 07-17); web/wechat remain.**
  `telegram_default_host` is now a one-line call into `full_catalog_host` (its ten offering deps
  collapsed to `dreggnet-catalog`), `dreggnet-telegram/src/seated.rs` is
  `pub use dreggnet_catalog::seated::{SeatedTug, SeatedTugSession}`, and
  `dreggnet-telegram/tests/full_parity_through_telegram.rs` asserts BOTH-POLARITY key-set
  equality against the LIVE `dreggnet_web::demo_host()` (dev-dep), not a hand-copied list.
  Remaining: `wechat_default_host` and web's (`catalog_default_host` +
  `register_non_game_offerings` + `demo_host` body) become the same one-liners; their `seated.rs`
  modules become re-exports. `HostThread` moves to `dreggnet-offerings` in the same phase.
- **Phase C — Discord adopts the host (the big one, NOT this change).** A new
  a new `host_bridge.rs` under `discord-bot/src/commands/`: one `HostThread` built from `full_catalog_host`,
  sessions at `SessionId(format!("discord:{channel_id}"))`, presses routed **by key string
  through the host** instead of the 18-arm static type match. `DiscordOffering`'s per-type
  `Store` shrinks to the offerings that genuinely need Discord-only behavior (collective ballot
  rounds — `CollectiveRound` — until `advance_collective` semantics are hosted per-session).
  The modal/value-prompt tables (`value_prompt`/`text_prompt`) become key-driven lookups.
- **Phase D — durability.** Point one `demo_host_over`-style persistence wrapper (move-log +
  replay-verify) at the shared host so a bot restart re-verifies instead of forgetting
  (fixes backlog #29's "sessions don't survive restart" honestly, and devnet's lost-ledger class).

## Wiring status (Repair phase, 07-17)

1. ✅ root `Cargo.toml` — `"dreggnet-catalog"` in `members` (adjacent to `"dreggnet-surfaces"`).
2. ✅ `dreggnet-telegram/Cargo.toml` — `dreggnet-catalog` dep (replacing its ten offering deps)
   + `dreggnet-web` dev-dep for the both-polarity parity test.
3. ☐ `dreggnet-web/Cargo.toml`, `dreggnet-wechat/Cargo.toml` — same dep line (Phase B remainder).
4. ☐ `discord-bot/Cargo.toml` — `dreggnet-catalog = { path = "../dreggnet-catalog" }` (Phase C).
5. ✅ `dreggnet-catalog/src/seated.rs` — the three `todo!` bodies are the verbatim web port.

No edits were made to `discord-bot/src/main.rs`, `commands/offering.rs`, or `cards.rs`; Phase C
is the only phase that touches them, and it is explicitly deferred.
