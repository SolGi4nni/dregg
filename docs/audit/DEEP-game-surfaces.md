# DEEP archaeology — the GAME SURFACES

*Read-only review, 2026-07-23, at HEAD `b4452caedf`. Every surface a player could touch, mapped and
classified at CURRENT resolution. No code, no commits. Claims cite `file:line`; live claims cite a
read-only probe run on 2026-07-23.*

Companion to `docs/audit/DEEP-live-reality.md` (2026-07-19, the deployment ground truth). Where this
doc **supersedes** that one it says so explicitly — three of its findings have moved, one has not.

---

## The one-paragraph answer

**At HEAD the seam is genuinely unified and the flagship is genuinely built. On the one live surface,
neither is true yet.** Every frontend — web, Telegram, WeChat, Discord — drives the *same*
`dreggnet_catalog::full_catalog_host` over the *same* `dreggnet_offerings::Offering` trait
(`dreggnet-catalog/src/lib.rs:191`, `:306`); the four-way `SeatedTug` copy is deduped
(`discord-bot/src/commands/portfolio.rs:74`); `/descent/play` is now a real in-tab Lean-native game
over `NativeDescentWorld` → `NativeDescentOffering` (`dreggnet-web/src/descent_play.rs:292`,
`wasm/src/bindings_native_descent.rs:63`), superseding the 07-19 "STUBBED" verdict **in the tree**.
But the running funnel serves a build from *before* 2026-07-20: `/descent/play` returns the wasm-glue
**placeholder** and its blob **503s**, `/descent/play/static/{day.json,actions.js}` **404**, and
`/offerings/descent` answers **"unknown offering"**. So the flagship game — the thing everything else
is oriented around — is **reachable by nobody today**. Below that, three quieter structural gaps:
the web's Descent is **never beacon-bound** (`dreggnet-web/src/descent.rs:85-87` hardcodes the offline
day while Discord resolves a BLS-verified drand round), the new **`banked_notes`** relics never cross
the browser→server wire (dropped by both halves of a hand-mirrored portable-record type), and the
**v3 canonical board** that carries them has zero non-test consumers.

---

## Classification legend

- **REAL** — drives the actual offering/executor: a real cell, a real turn, a real `TurnReceipt`.
- **REAL-AT-HEAD / STALE-AS-DEPLOYED** — the code is real; the running instance predates it.
- **STUBBED** — the served path returns placeholder/mock/hardcoded data.
- **DEAD** — points at a route, file, node, or constant that no longer exists.
- **NAMED** — exists as a library/scaffold; no process, no player can reach it.

---

## Live probe (read-only GETs, 2026-07-23)

| URL | Result | Meaning |
|---|---|---|
| `https://hbox-dregg.skunk-emperor.ts.net/` | **200** | The one open game surface is UP (unchanged from 07-19). |
| `…/descent` | **200** | Board renders; one demo row (`ember`, 8 turns, depth 4), "no node, no testnet". |
| `…/offerings` | **200**, **19** cards | HEAD's catalog is **23** (`dreggnet-catalog/src/lib.rs:306`). Live is missing `descent`, `descent-campaign`, `quest`, `private-raid`. |
| `…/offerings/descent/session/…` | **200 `<title>… unknown offering</title>`** | **The Lean-native Descent is not on the live server at all.** |
| `…/descent/play` | **200** | Shell renders… |
| `…/descent/play/static/dregg_wasm.js` | **200, 510 B** — `PLACEHOLDER … throw new Error` | …but the glue is the placeholder; `grep -c NativeDescentWorld` = **0**. |
| `…/descent/play/static/dregg_wasm_bg.wasm` | **503** | The honest fail-closed notice. |
| `…/descent/play/static/client.js` | **200, 597 B** — `__DESCENT_CLIENT_PLACEHOLDER` | A route that **no longer exists at HEAD** — proof the binary is old. |
| `…/descent/play/static/day.json` | **404** | Route added 2026-07-20 (`d8314527c6`); absent live. |
| `…/descent/play/static/actions.js` | **404** | Same. |
| `…/tg` | **200** | The Telegram Mini App IS mounted (so `TELEGRAM_BOT_TOKEN` is set on the box). |
| `…/da` | **404** | Discord Activity not mounted (`DISCORD_CLIENT_ID`/`_SECRET`/`BOT_SECRET` unset). |
| `…/gallery`, `…/health` | **200** | Sprite gallery + health live. |
| `…/metrics` | **404** | Correct — metrics bind to a separate loopback listener (`dreggnet-web/src/lib.rs:4571`). |
| `https://node.dregg.net/status` | **000** | The extension's out-of-box node host still resolves to nothing (`extension/src/endpoints.ts:23`). |
| `https://www.dregg.net/` | **200** | The product site — **zero links to any playable surface** (grep for `hbox-dregg` = 0 hits). |

**The live player-visible consequence:** a stranger who somehow finds the funnel URL sees a hero
button "Play The Descent →" (`dreggnet-web/src/lib.rs:4676`) which lands on a page whose bootstrap
prints *"The Descent web client is not built into this deployment yet — the game cannot start."*
(the live `app.js`, served at `/descent/play/static/app.js`).

---

## 1. `dreggnet-offerings` — THE SEAM

**REAL, and it is genuinely the one seam.** `trait Offering`
(`dreggnet-offerings/src/lib.rs:550`) is `open`/`actions`/`advance`/`verify`/`render`/`price`, with
`advance` returning `Outcome::Landed{receipt: TurnReceipt, ended}` or `Outcome::Refused(String)` —
the anti-ghost shape (`:286`). The frontend-facing tamper seam is the separate `RecordVerify`
extension trait: `export_record` (`:793`) / `verify_record` (`:799`).

Completeness of the loop, per method: open ✓, play ✓, verify-by-replay ✓ (`VerifyReport`, `:344`),
settle ✓ (offering-specific terminal), **banked relic/asset ✓ at the offering layer** — the daily
descent really mints owned notes (`native_descent.rs:284` `banked_notes: Vec<NativeDescentBankedNote>`,
minted at `:1002` via `mint_banked_notes`, `:2308`). Also carried: session lifecycle/eviction
(`lifecycle.rs`), durable resume by replay (`resume.rs`), signed attribution (`signed.rs`),
session-key paymaster (`session.rs`), audience projection (`audience.rs`).

`export_record`/`verify_record` consumers, counted: `dreggnet-offerings` (dungeon, campaign,
overworld, native_descent), `dreggnet-party`, `dreggnet-doc`, `dreggnet-adventure`,
`dreggnet-game-board`, `wasm/src/bindings_native_descent.rs`, `dreggnet-web/src/descent.rs`,
`dreggnet-surfaces/src/party.rs`, `dungeon-on-dregg`. That is a real, broadly-used seam — not a
decorative trait.

## 2. `dreggnet-catalog` — THE ONE REGISTRY

**REAL.** `CATALOG_KEYS` is 23 keys (`dreggnet-catalog/src/lib.rs:306-333`) and
`full_catalog_host` (`:191`) is what **all four** frontends build through:

| Frontend | Builds via |
|---|---|
| web | `dreggnet-web/src/lib.rs:1977-1978` → `dreggnet_catalog::full_catalog_host` |
| telegram | `dreggnet-telegram/src/host.rs:2255` → same |
| wechat | `dreggnet-wechat/src/host.rs:521` → same |
| discord | `discord-bot/src/commands/portfolio.rs:474-486` — `play_keys()` is **derived** from `CATALOG_KEYS` minus 6 bespoke-command keys plus 3 Discord extras |

The parity contract is a test, not folklore (`dreggnet-catalog/src/lib.rs:366-375`), and Discord's
dispatch-parity tests fail if a catalog key has no press route (`:472-478` doc). This is the single
best-integrated thing in the whole review. `lab_intro()` (`:344`) is one shared framing string across
all four front doors — the same discipline applied to product copy.

**Gap:** the shared registry is 23 keys but there is no shared *availability* statement. The live web
serves 19 of them; nothing in-tree detects that a deployment is behind its own catalog.

## 3. `dreggnet-web` — the games site

**REAL-AT-HEAD / STALE-AS-DEPLOYED.**

Router (`dreggnet-web/src/lib.rs:4525-4553`): `/` `/health` + session routes (`:426-428`) + catalog
routes (`:2000-2013`) + `descent_router` (`descent.rs:942-951`) + `descent_play_router`
(`descent_play.rs:68`) + sprite/gallery (`sprite.rs:161-162`) + overlay + env-gated `/tg` and `/da`.

**The loop, per leg:**

| Leg | State |
|---|---|
| open | ✓ `GET /offerings/{key}/session/{id}` — lazy open, seeded from the id, lifecycle-aware (`lib.rs:2026-2060`) |
| play | ✓ `POST …/act` (cookie identity, `Attribution::Asserted`) and ✓ `POST …/act-signed` (`act_signed.rs`, verified Ed25519 → `Attribution::Signed`) |
| verify | ✓ `GET …/verify` — the offering's own replay verifier |
| receipt | ✓ shared card `PlayerTurnReceipt::from_landed` (`lib.rs:490`, `:2373`) |
| settle/board | ✓ procgen lane `POST /descent/submit` (`descent.rs:1060`) — re-executes + no-cheat-verifies before ranking; ✓ native lane `POST /descent/native/submit` (`:988`) |
| anchor | ✓ **procgen only** — `settle_run` is called from `post_submit` (`:1104-1140`) and **never from the native lane**. The flagship's runs are re-verified but never anchored. |
| banked relic | ✗ **the notes never cross the wire** — see §9 |

**`/descent/play` — the flagship, in the tab.** At HEAD this is real and good: strict CSP with
`script-src 'self' 'wasm-unsafe-eval'`, no CDN (`descent_play.rs:41-51`); same-origin wasm glue +
blob; a **fail-closed 503** when the blob is absent (`:178-189`); `day.json` resolves TODAY's day
through the same `procgen_dregg::descent_day` helper the board uses (`:125-152`); the controller
drives `world.advance(turn, arg, actor)` and shows a live `world.verify()` badge (`:292`+). A run's
`recordJson()` is retained in `localStorage` and re-imported only by **fresh native replay with exact
receipt/state/root comparison** (`bindings_native_descent.rs:80-90`). Publication is opt-in.
This wholly supersedes `DEEP-live-reality.md`'s `/descent/play` = STUBBED — *in the tree*.

**Stale doc-comment (DEAD anchor):** `dreggnet-web/src/lib.rs:4531-4533` still says `/descent/play`
"serves the in-tab `<dregg-descent>` client over the wasm `DescentWorld`". It does not — it serves a
bespoke DOM controller over `NativeDescentWorld`, and `descent_play.rs:612` explicitly asserts the
shell does **not** contain `<dregg-descent`.

**Session durability:** in-memory by default; durable only with `DREGGNET_WEB_SESSION_DIR`
(`lib.rs:4144-4180`, warn-and-degrade at `:4273`). Leaderboard durable only with `DATABASE_URL`
(`:4582-4600` → `descent_store::SqliteDescentRunStore`, boot-time replay re-verification).

**Landing-page inconsistency:** the deck claims "in your browser, with **no client JavaScript**"
(`lib.rs:4684-4686`) while the primary CTA on the same line leads to a page that requires JS + wasm.

## 4. `dreggnet-telegram` — the bot

**REAL, NOT DEPLOYED.** The bin is a genuine process shell: live `getMe` token check, real reqwest
transport (`reqwest_transport.rs:47`), durable per-`(offering, chat)` `FileResumeStore` move-logs so
a restart **resumes every session by replay**
(`dreggnet-telegram/src/bin/dreggnet-telegram-bot.rs:1-31`). The host is the richest non-Discord one:
game epochs, player worlds (per-identity RPG), binary operations, text-taking affordances, verify
control, close/resume (`host.rs:622-2088`). The audience boundary is enforced structurally — a
`hidden_information()` offering is *refused at open* in a group chat
(`host::OpenError::HiddenInSharedChat`, `lib.rs:41-46`), and there is a standing canary that an RPG
key never changes a message's audience (`host.rs:2263-2276`).

**Deployment: still "⚠ NOT YET INSTALLED ANYWHERE"** (`deploy/telegram/dregg-telegram-bot.service:3`),
ops-gated on a BotFather token. Unchanged since 07-19.

**Odd asymmetry worth flagging:** the web *Mini App* (`/tg`) **is live** (probe: 200), so the box has
a `TELEGRAM_BOT_TOKEN` — but the bot that would deep-link players into it is not running. The Mini
App's launch buttons come from the bot (`bin/…:24-26`); today there is a mini-app with no front door.

## 5. `dreggnet-wechat` — the OA surface

**NAMED.** Library only: no `[[bin]]` in `dreggnet-wechat/Cargo.toml`, and the only `Transport` impl
in-tree is `MockTransport` (`transport.rs:38-83`). `RawWeChatApi` composes the real
`api.weixin.qq.com/cgi-bin/message/custom/send` URL purely and delegates the POST to an injected
`HttpPost` (`:96-115`) — **and there is no `HttpPost` impl for WeChat anywhere in the repo** (the
three that exist are dregg-pay, dreggnet-telegram, dregg-ipfs). Access-token fetch is explicitly out
of scope (`:110-113`).

It does drive the full shared catalog (`host.rs:521`), so the *logic* is at parity. What it lacks vs
Telegram: game epochs, durable resume, lifecycle policy, player worlds, binary operations, signed
attribution, and the shared `PlayerTurnReceipt` card (`host.rs` has 17 public fns to Telegram's 40).
No group/collective shape (OA is 1:1 by design, honestly stated at `lib.rs:39-44`).

## 6. `discord-bot` — the deployed surface

**REAL and DEPLOYED** — hbox user unit, durable sqlite, "the only live instance"
(`deploy/hbox/dregg-discord-bot.service:1-14`). It is by a wide margin the most complete surface:

- **~28 `DiscordOffering` impls**, `/play <offering>` derived from `CATALOG_KEYS`
  (`portfolio.rs:474-486`), so a new catalog offering can never be silently absent.
- `/play <offering> action:verify` — the flagship games answer verify-don't-trust with a command
  (`portfolio.rs:687-710`).
- **`/crown` — the only proof-carrying lane on any surface** (`commands/crown.rs:1-53`): a finished
  `tug`/`automatafl` match folds in the background (`dreggnet_prove_service::MatchProveService`) into
  ONE `WholeChainProof`, submitted to `dreggnet_game_board::GameBoard` and verified in **O(1)**, with
  a **Re-verify button any user can press**. Board + fold records are in-process (a restart forgets
  pending folds — stated at `crown.rs:39-41`); the proof file survives on Discord.
- **The only beacon-bound day.** `resolve_todays_day` (`commands/descent.rs:224-241`) uses the reveal
  cron's cached, **BLS-pairing-verified** drand round when fresh, keyed `d{utc}-r{round}`, else the
  offline day keyed `d{utc}-off`, with the footer honestly labeling which (`:203-206`).
- Durable board (`descent_board_store.rs`) with **boot replay through the real no-cheat gate**, so a
  tampered row cannot resurrect a cheat.

**Two games both called "The Descent" in one bot:** `/descent` opens the older procgen/spween
`DailyDescentOffering` (`commands/descent.rs:1-4`); `/play offering:descent` opens the Lean-native
`NativeDescentOffering` (`commands/native_descent.rs:15-18`). Both real, both `Offering`s, different
rulesets, different boards, same name in the UI.

**$DREGG pay** — unchanged from 07-19: falls back to `MockWatcher` with no `DREGG_PAY_*` env
(`discord-bot/src/pay.rs:21,301,558`), so the deployed bot is effectively free-tier.

## 7. The extension + `<dregg-*>` web components

**RUNS-ON-EMBERS-LAPTOP; components remain EXTENSION-ONLY.** `customElements.define` happens only in
the content script's isolated world (`extension/src/content.ts:8-57`, registering `dregg-embed`,
`dregg-doc`, `dregg-story`, `dregg-descent`, `dregg-sprite`, `dregg-poll`). **No served page mounts
any of them** — verified by grep across `dreggnet-web/src` and `site/`; the only hits are a stale
comment and a negative assertion.

The offering-signing rung 2 is genuinely built and **byte-pinned against the Rust**
(`extension/src/offering-sign.ts:14-32` carries the same canonical
`"dregg-offering-turn-v1:" ‖ …` vector as `signed.rs`'s pin test), and the web verifier exists
(`dreggnet-web/src/act_signed.rs`). **But no page connects them** — it is a bridge with both
abutments and no deck.

**Two DEAD anchors here:**

1. **`extension/src/descent-play-entry.ts:1-19`** documents itself as the bundle entry for
   `/descent/play/static/client.js`, referencing a `PLAY_APP_JS` constant in `descent_play.rs`.
   Neither the route nor the constant exists at HEAD (`descent_play.rs` has only
   `NATIVE_PLAY_APP_JS:292`). The file is not in `extension/build.mjs`'s entryPoints (4 entries,
   `:6-11`) and nothing references it. **Dead file.** (And it is exactly the placeholder the live
   server is still 200-ing.)
2. **`extension/README.md:269`** tells an integrator to
   `fetch("/api/offerings/${key}/sessions/${id}/act-signed")`. The real route is
   `/offerings/{key}/session/{id}/act-signed` (`dreggnet-web/src/lib.rs:2004-2007`) — no `/api`
   prefix, `session` singular. Copy-paste → 404.

Also unchanged: default node host `node.dregg.net` probes **000** (`extension/src/endpoints.ts:23`);
extension is unpublished/sideload-only (`extension/REVIEWER-NOTES.md`).

## 8. The wasm bindings

**REAL.** `wasm/src/bindings_native_descent.rs` owns an actual `NativeDescentOffering` and crosses
`Offering::advance` per click (`:63-120`); import is untrusted-by-construction (fresh session, full
replay, byte-for-byte envelope compare, `:80-90`); the assurance boundary is stated honestly —
wasm32 cannot link the native Lean library, so the checked-in Lean-emitted program is installed in the
real embedded executor but the native Lean differential does not run in-browser (`:17-23`). It also
declines to authenticate the identity it is handed and says so (`:24-29`).

`bindings_multiway_tug.rs` proves a real per-play Poseidon2 membership STARK **on device** (`:11-28`).
`bindings_descent.rs` is the OLD procgen `DescentWorld` — the one `<dregg-descent>` drives
(`extension/src/port.ts:2027-2065`), which is why the extension's Descent and the web's Descent are
**different games**.

CI builds and smoke-tests the bundle (`.github/workflows/ci.yml:192-210`), and the games deploy
script builds it in the same release transaction and health-gates on
`NativeDescentWorld` appearing in the served glue (`deploy/games/deploy-hbox.sh:296,313,458-481`) —
which is precisely the gate that would have caught the current stale deploy, had it been run.

## 9. `dreggnet-game-board` — the "canonical" board

**REAL, but with a DEAD-END half.**

- The **FULL-STARK half** (`src/lib.rs:1-72`) is real and consumed: `TugMatch`/`AutomataflMatch` →
  `LeafBundle` → `prove_match` → `ugc_dregg::Registry::submit_proof`, verified O(1), ranked with
  `has_moves() == false`. Consumers: `dreggnet-prove-service` and `discord-bot/src/commands/crown.rs`
  only.
  - Good news for house-law #1: the automatafl leaf now proves through the **PROVEN Lean-emitted
    descriptor** `automataflStepDescN {n}` for n ∈ {2,11}, with the Rust `build_d1_honest` demoted to
    a fail-closed lowering gate scheduled for deletion (`src/lib.rs:296-355`). `n=5` still falls back
    to the Rust AIR, named as a residual.
- The **native-Descent half** (`src/native_descent_board.rs`) is where the **v3 canonical snapshot**
  lives: `SNAPSHOT_VERSION = 3` / `SNAPSHOT_DIGEST_DOMAIN = "dregg.native-descent-board.snapshot.v3"`
  (`:36-39`), whose entire reason for existing is that **v3 carries `banked_notes`** (`:33-36`). Its
  admission is fail-closed (fresh executor, full replay, exact player/seed/root/revision/settlement/
  relic-set/crowned equality, `:10-23`), and it is explicitly *not* called the same thing as the
  FULL-STARK path (`:1-8`) — good discipline.
  **Its only consumer in the entire repo is its own test file** (`dreggnet-game-board/tests/native_descent_board.rs:4`).
  `dreggnet-web`, `discord-bot`, `dreggnet-telegram` all do not import it.

**The banked-relic hole, precisely.** `NativeDescentCompletion.banked_notes`
(`dreggnet-offerings/src/native_descent.rs:284`) is the real minted asset. The browser→server wire
does **not** carry it:

- `wasm/src/bindings_native_descent.rs:463-470` — `CompletionWire { actor, revision, root_hex,
  settlement_receipt_hash_hex, banked_relics: Vec<u64>, crowned }`. No `banked_notes`.
- `dreggnet-web/src/descent.rs:206-215` — `NativeCompletionWire { … }`, **the same six fields**,
  independently declared.

So the whole "the daily descent now mints real relics" advance is invisible on every player-reachable
surface: the browser mints notes locally, drops them on export, the server re-mints them on replay
and drops them again, the run card can only show `banked_relics: usize`
(`dreggnet-web/src/descent.rs:230-232`), and the one board type that models them is unreachable.

## 10. The wire MIRROR (the one real re-implementation found)

The portable native-Descent record is declared **twice, independently**:

| | file | struct | format / version |
|---|---|---|---|
| producer | `wasm/src/bindings_native_descent.rs:368` | `PortableRecord` | `"dregg.native-descent.record"` / `1` (`:39-41`) |
| consumer | `dreggnet-web/src/descent.rs:159` | `NativePortableRecord` | `"dregg.native-descent.record"` / `1` (`:148-149`) |

Neither imports the other. **Both carry `#[serde(deny_unknown_fields)]`** (`descent.rs:171`,
mirrored in the wasm side). The failure mode is sharp: add a field on the producer and every submit
400s with "native record JSON: unknown field"; add it on the consumer and nothing ever populates it.
This is exactly the coupling that is currently *keeping* `banked_notes` out (§9) — the mirror is not
only a duplication, it is the mechanism of the gap.

**This is not a game-logic mirror.** Both sides genuinely drive the real offering:
`dreggnet-web/src/descent.rs:776-805` opens a fresh `NativeDescentOffering`, replays every event
through `Offering::advance`, runs `Offering::verify`, and then compares `export_record()` to the
submitted record field-for-field. That is a correct, non-vacuous re-verifier — just spelled twice.

**Structural duplication (not logic duplication) also found:**

- Two native-Descent boards: `dreggnet-web/src/descent.rs` (`DescentState.native_runs`,
  rusqlite-backed, `descent_store.rs`) and `dreggnet-game-board/src/native_descent_board.rs`
  (v3 snapshot, banked_notes, unused). Both re-verify by replay; different persistence, different
  fields, zero shared code.
- Two Descent-board stores across processes: `discord-bot/src/descent_board_store.rs` (sqlx, async
  bridge) and `dreggnet-web/src/descent_store.rs` (rusqlite, sync). The `rusqlite`-vs-`sqlx` split is
  a *justified* `links = "sqlite3"` constraint (`descent_store.rs:20-28`) — but the **schemas and the
  boards themselves** are separate, so a Discord run and a web run never appear on one leaderboard.

## 11. The day divergence (a correctness gap, not just cosmetics)

- **Web:** `dreggnet-web/src/descent.rs:85-87` — `pub fn todays_day() -> DescentDay {
  descent_day::todays_offline_day() }`. Unconditional. The web can therefore **never** produce a
  beacon day; `day.json`'s `"source"` field (`descent_play.rs:142`) is dead code on the
  `is_live_beacon()` branch, and `descent.rs:1862` asserts `source == DaySource::OfflineDate` as the
  expected outcome.
- **Discord:** `commands/descent.rs:224-241` returns a **BLS-pairing-verified** beacon day when the
  reveal cron has one fresh, keyed `d{utc}-r{round}`.

Both keys name the same UTC day, but **different seeds → different worlds**. Two doc-comments assert
a parity that does not hold: `discord-bot/src/commands/descent.rs:216-217` says "the web re-derives it
by fetching and re-verifying that exact round", and `dreggnet-web/src/lib.rs:4311` says "Both
processes now resolve their day from the SAME helper." The web *can* resolve a beacon key when one is
**explicitly named** on a submit (`descent.rs:1179-1194` → `resolve_day_key` with
`HttpRoundFetch`) — so the bridge exists for cross-posting, but the **default "today" on each surface
is a different world**.

## 12. Everything else, briefly

| Surface | Class | Note (cited) |
|---|---|---|
| `dreggnet-surfaces` (9 RPG feature offerings) | **REAL** | Real substrate writes: gift/trade are owner-signed transfers, a re-gift of a note you no longer hold is a real executor refusal (`src/lib.rs:11-45`). Per-identity isolation on web (`dreggnet-web/src/lib.rs:1343-1349`) and Telegram. |
| `dreggnet-prove-service` | **REAL, Discord-only** | Bounded worker pool, drop-on-full, off the play path (`src/lib.rs:1-45`). Named residuals: GPU apex aggregation, on-device fold, service→board wire. |
| `demo/real-dungeon-service` | **REAL engine, off the seam, undeployed** | Real `spween_dregg::WorldCell::apply_choice` + `verify_by_replay` + the live `.dungeon` compiler (`src/main.rs:1-66`). But it drives the WorldCell **directly**, not through `Offering`; **one in-memory session behind a mutex**, no auth, no persistence (`:57-63`, self-declared). Zero references in `deploy/` or `.github/workflows/`. |
| `demo/dungeon-service` | **REAL typed-effect gate, MODELED attestation** | The cap gate + anti-ghost tooth are real; the attestation's *authentic* leg is an in-tree fixture and says so (`src/main.rs:24-36`). |
| `node` `/realm/*` ingress | **REAL, durable, ZERO game consumers** | 17 routes (`node/src/realm_service.rs:898-917`), durable `REALM_LOG` with boot replay. Grep for consumers outside `node/`: **none**. Honest residuals named in-file: not in the kernel executor path, custodial identity mint, invisible to `/api/receipts` (`:47-69`). |
| node receipt-chain durability | **CLOSED — supersedes 07-19** | `install_receipt_chain_durability` (`node/src/state.rs:809`, wired `:1161`, `:1341`); the 07-19 "receipt log is EPHEMERAL" finding no longer holds at HEAD. |
| games funnel node anchor | **STILL DEAD — unchanged from 07-19** | `deploy/games/dregg-web-games-funnel.service:7-11`: "⚠ ITS `DREGG_NODE_URL` TARGET IS DEAD … Submitted runs cannot anchor until a node is back on :8420." |
| `dreggnet-audit` | **REAL, shared** | One JSONL envelope facility across discord/telegram/web, per-process filenames so one shared dir correlates; hard secret-hygiene rule with a `find_leak` canary (`src/lib.rs:1-36`). The deploy units point all three at one dir (`deploy/hbox/dregg-discord-bot.service:24-31`). |
| `www.dregg.net` | **REAL site, DEAD END for players** | 200, but zero links to any playable surface. |
| `dregg-chutes-e2ee` | **NEW, uncommitted** | Attested E2EE Chutes inference for the paid narrator — real DCAP gate, fail-closed before encrypt (`src/lib.rs:11-21`). Untracked in git at review time. |

---

## RANKED GAPS — what would most improve player-reachable completeness

**1. Redeploy the games funnel from HEAD.** *(Highest ratio by an enormous margin.)* Everything below
is real in the tree and reachable by nobody. `deploy/games/deploy-hbox.sh` already builds the wasm in
the same release transaction and **already health-gates on `NativeDescentWorld` appearing in the
served glue** (`:296,313,458-481`) — the gate exists, it just has not been run since before
2026-07-20. One deploy takes the flagship from "cannot start" to playable, and takes the catalog from
19 to 23.

**2. Put the games where a player can find them.** `www.dregg.net` (200, the product surface) has zero
links to any playable surface, and the one live surface is an unlisted `*.ts.net` funnel. Today the
*only* discoverable front door to a dregg game is a Discord invite — and the funnel's own Discord CTA
is env-gated behind `DESCENT_DISCORD_INVITE` (`dreggnet-web/src/lib.rs:3169`).

**3. Carry `banked_notes` across the browser→server wire, by deleting the mirror.** The relic-minting
work is complete at the offering layer and invisible at every surface. The correct fix is not to add
the field twice — it is to make **one** portable-record type (a `dreggnet-offerings` wire module both
the wasm binding and `dreggnet-web` import), which closes the mirror (§10) and the relic gap (§9) in
one move. `deny_unknown_fields` on both sides makes any additive change a two-repo lockstep until
this is done.

**4. Unify "today".** Give `dreggnet-web::descent::todays_day()` the same beacon-then-offline
resolution Discord has (`commands/descent.rs:224-241`), or make Discord's day the published one both
read. Until then two surfaces play two different worlds under one name, and two doc-comments claim
otherwise (`discord-bot/src/commands/descent.rs:216-217`, `dreggnet-web/src/lib.rs:4311`).

**5. Anchor the native lane.** `settle_run` runs only for procgen submits
(`dreggnet-web/src/descent.rs:1104-1140`); the flagship's runs are re-verified but never anchored —
and the anchor target is dead anyway (`deploy/games/dregg-web-games-funnel.service:7-11`, the
07-19 TODO-1 that has not moved). These are one problem: a durable node unit on `:8420` unblocks both.

**6. Give the v3 board a consumer, or delete it.** `native_descent_board.rs` (646 lines, the only
place `banked_notes` reaches a leaderboard) has zero non-test consumers. Either `dreggnet-web`'s
native lane becomes it (deleting `DescentState.native_runs`'s parallel implementation), or it goes.
Landing it *beside* the web's board is the un-additive move to avoid.

**7. Connect the signed-play bridge.** `offering-sign.ts` (signer) and `act_signed.rs` (verifier) are
both built and byte-pinned to each other, and **no page uses either**. One "sign this move with your
extension" affordance on the web session page turns rung 2 of the identity ladder from two artifacts
into one working path. Fix `extension/README.md:269`'s wrong route while there.

**8. Delete the dead extension anchors.** `extension/src/descent-play-entry.ts` targets a route and a
constant that no longer exist and is in no build. It is also, verbatim, the placeholder the live
server is serving — deleting it removes the last thing that makes the stale deploy look intentional.

**9. Decide what `<dregg-descent>` is for.** It drives the OLD procgen `DescentWorld`
(`extension/src/port.ts:2027-2065`) while `/descent/play` drives the Lean-native one. Either the
element moves to `NativeDescentWorld` or the extension's Descent is honestly a different game.

**10. Telegram: install it.** The runtime is complete (durable resume, epochs, player worlds, verify),
the unit is written, the Mini App is *already live*. It is one token away, and it is currently the
cheapest way to add a second reachable surface (`deploy/telegram/dregg-telegram-bot.service:9-11`:
outbound-only, no listening socket, no funnel).

**11. WeChat: one `HttpPost` impl + a bin,** or reclassify it out of the "four frontends" language it
currently uses in three module docs. The logic is at parity; the network edge is empty
(`transport.rs:96-115`).

**12. Detect deployment drift in-tree.** Nothing catches "the live catalog has 19 of 23 keys" or "the
served glue is the placeholder". The health gate in `deploy-hbox.sh:458-481` is the right shape; it
needs to run *against the live funnel* on a schedule, not only at deploy time.

---

## MIRRORS / RE-IMPLEMENTATIONS — the honest tally

**Found (1 true wire mirror, 3 structural duplications):**

1. **`PortableRecord` / `NativePortableRecord`** — the native-Descent transport type, declared twice,
   both `deny_unknown_fields`, no shared code (`wasm/src/bindings_native_descent.rs:368` vs
   `dreggnet-web/src/descent.rs:159`). The only genuine wire mirror in the game surfaces, and it is
   load-bearing for the `banked_notes` gap.
2. **Two native-Descent boards** (`dreggnet-web` `DescentState` vs `dreggnet-game-board`
   `native_descent_board`) — same re-verify-by-replay discipline, different fields, one unused.
3. **Two Descent board stores/schemas** across processes (`discord-bot/src/descent_board_store.rs` vs
   `dreggnet-web/src/descent_store.rs`) — the driver split is justified, the *board* split is not.
4. **Two "The Descent"s in one Discord bot** (`/descent` procgen vs `/play offering:descent`
   Lean-native) — not a mirror technically (both are real distinct offerings), but a product-level
   name collision a player cannot resolve.

**Notably NOT found — mirrors that were fixed:**

- The four-copy `SeatedTug` adapter is deduped into `dreggnet_catalog::seated`; Discord is now a
  `pub use` (`discord-bot/src/commands/portfolio.rs:74`), and the port note names all four former
  copies (`dreggnet-catalog/src/seated.rs:6-14`).
- No frontend re-implements a game rule. Discord's native-Descent module says so and is 283 lines of
  metadata (`commands/native_descent.rs:1-6`); the wasm binding says so (`:6-8`); the web's native
  verifier really opens a `NativeDescentOffering` and replays (`descent.rs:776-805`).
- The catalog list is derived, not duplicated, in all four frontends (§2).

---

## What a player can actually DO end-to-end TODAY — the player-reachable truth

**Reachable by a stranger with no invite: one surface.**

`https://hbox-dregg.skunk-emperor.ts.net` (unlisted; not linked from `dregg.net`), serving a build
from before 2026-07-20:

- ✅ **Browse the Lab** — 19 offerings, cards + live session counts.
- ✅ **Play 19 offerings server-rendered, no JS**: `dungeon`, `tug`, `automatafl`, `council`,
  `market`, `bazaar`, the 8 RPG surfaces, the 5 services. Each is a real cap-gated affordance → one
  real executor turn → a real `TurnReceipt`; an illegal move is a real refusal that commits nothing.
- ✅ **Re-verify any session by replay** — `GET /offerings/{key}/session/{id}/verify`.
- ✅ **Read the no-cheat Descent board** and open the demo run-card; the forged demo run shows FAIL
  by re-execution, node-free.
- ✅ **The sprite gallery** — deterministic content-addressed SVGs.
- ❌ **Play The Descent.** The hero CTA leads to a page that prints *"The Descent web client is not
  built into this deployment yet — the game cannot start."* The wasm blob 503s. `/offerings/descent`
  answers "unknown offering". **The flagship is reachable by nobody.**
- ❌ **Rank a run.** No real player has submitted; the board's one row is the built-in demo winner.
- ❌ **Anchor anything.** `DREGG_NODE_URL` points at a node whose ledger was permanently lost.
- ❌ **Bank a relic.** Not on the wire.
- ❌ **Sign a move with your own key.** No page offers it.

**Reachable in Discord (invite-gated, but the most complete surface by far):** the live bot is the
only place where the loop actually closes. A player can `/descent` a **beacon-seeded** permadeath run
with a persistent carrying character on a **durable, boot-re-verified** board; `/play` any of ~28
offerings; `/play <key> action:verify` to replay-verify a chain; and — uniquely — `/crown` a finished
`tug`/`automatafl` match into ONE succinct STARK that **any user re-verifies in O(1)** with a button,
moves never posted. Free-tier only (pay falls back to `MockWatcher`).

**Reachable nowhere:** the Lean-native Descent's in-tab game, the Telegram bot, WeChat, the extension
and every `<dregg-*>` component, both demo dungeon services, the `/realm` MUD ingress, and the v3
banked-relic board.

**The shape of it:** the seam is unified, the flagship is built, the proofs are real, and the
distance between the tree and the one running process is now the single largest thing standing
between this and a player. Gap #1 is a deploy.
