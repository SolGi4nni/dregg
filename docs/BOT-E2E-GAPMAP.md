# Bot E2E Flow Gap-Map — Discord · Telegram · WeChat (2026-07-17)

Static analysis of every user-facing flow across the three chat frontends, from code
reading at HEAD (no build, no live run). Companion to
`docs/BOT-EXCELLENCE-BACKLOG-2026-07-17.md` (the Discord-only adversarial review — item
numbers `#N` below refer to it). A REAL run against a deployed bot + node is the follow-up
ops step (the Discord bot runs on the AWS edge); this map scopes it.

## The one-sentence shape

**Discord is the only bot that exists as a bot.** `discord-bot/` is a deployable binary
(`src/main.rs` + `src/bin/`) with 49 commands, sqlite persistence, a pay layer, and a node
connection; `dreggnet-telegram/` and `dreggnet-wechat/` are **library crates with no
`[[bin]]`, no update loop, no HTTP dependency, and zero consumers in the tree** — every
flow they have is real (same `OfferingHost`, same executor, driven end-to-end in tests over
`MockTransport`) but **unreachable by any actual user** until someone writes the ~200-line
runtime shell each crate's own docs honestly scope out
(`dreggnet-telegram/src/host.rs:36-44`: token + reqwest `HttpPost` + update loop/webhook +
durable session store).

Legend: ✅ works E2E · ⚠ exists but dead-ends or degrades · 🧪 works in-library only
(driven tests; no live surface) · ❌ absent.

## The gap-map

| flow | discord | telegram | wechat | works? | code path | gap |
|---|---|---|---|---|---|---|
| **Onboarding** (guided tour) | ✅ | ❌ | ❌ | Discord E2E — the best flow in any bot: identity → faucet → first paid turn, node-outage retry | `discord-bot/src/commands/start.rs:100` (register), `:113` (handle), tour faucet step `:348`, tour send `:376` | TG/WX have no `/start` at all; nearest analog is the offerings menu (`dreggnet-telegram/src/host.rs:232 present_offerings_menu`, `dreggnet-wechat/src/host.rs:277`) which assumes you already know what dregg is |
| **Identity** (derived cipherclerk) | ✅ | 🧪 | 🧪 | All three derive a REAL Ed25519 identity from platform uid; TG/WX only inside tests | Discord `discord-bot/src/cipherclerk.rs:63` (`derive`, federation-scoped); TG `dreggnet-telegram/src/cipherclerk.rs:50` + `lib.rs:264 identity()`; WX `dreggnet-wechat/src/cipherclerk.rs:54` + `lib.rs:208` | TG/WX derivations take NO `federation_id` (Discord's does) and use separate bot secrets — the same human is three unrelated identities with no cross-platform link flow anywhere |
| **Identity: LLM key mgmt** | ⚠ | ❌ | ❌ | Discord works but `/key set` leaks the secret as a visible slash option (#3) | `discord-bot/src/commands/key.rs:32` (register), `:109` (handle), `:55` (visible option); the safe modal already exists at `start.rs:447 key_modal` | TG/WX have no key store, no LLM layer at all — keyless-Hermes class issues (#7) can't even arise |
| **Identity: external cclerk link** | ⚠ dead-end | ❌ | ❌ | Discord `/link-cipherclerk` hands a challenge no command can ever answer (#4) | `discord-bot/src/commands/federation.rs:250` (pending, "not active until ownership is proven"); walls out `/cap-*` at `captp.rs:580` | Permanent dead-end on Discord; flow does not exist elsewhere |
| **Faucet** | ✅ | ❌ | ❌ | Discord E2E against devnet | `discord-bot/src/commands/social.rs:32 handle_faucet` → `:43 execute_faucet` → `:84 state.devnet.faucet_request` | TG/WX have no economic layer whatsoever (no faucet, no credits, no balance — grep-clean) |
| **A game turn** (descent / play) | ⚠ | 🧪 | 🧪 | Discord commits the turn but can SHOW failure (#1 — the most dangerous bug); TG/WX advance the same offerings cleanly in tests | Discord `descent.rs:1101` (on-chain commit) → `:1156` (20s narration await) → `:1177` (first ACK — blows Discord's 3s window; no defer); reopen abandons the run `:1013`. `/play` `portfolio.rs:351` (register), `:369` (handle). TG `host.rs:325 press()` → `:373 h.advance` → re-present `:379`; WX `host.rs:414 reply()` → `:449 h.advance` → `:455` re-present | Discord: defer + re-render (#1). TG/WX: unreachable without a runtime; sessions are in-memory only (restart loses in-flight state — same class as #29) |
| **Offering advance** (generic adapter) | ✅ | 🧪 | 🧪 | The strongest parity story: ONE `OfferingHost`, full 18-offering catalog on all three | Discord adapter `offering.rs:964`/`:989` (`Offering::advance`), collective `:559 advance_collective`; TG catalog `host.rs:416 telegram_default_host` (5 games + 8 RPG surfaces + 5 non-game); WX `host.rs:490 wechat_default_host` (identical); WX even has multi-participant rooms via `host.rs:344 join()` | Discord: silent drops (`offering.rs:1093 NotOurs => {}`, #31), un-typeable stale hint (`:1274`, #29), demo worlds not shared state (`portfolio.rs:22,399`, #15). TG/WX: library-only |
| **Verify** | ⚠ | 🧪⚠ | 🧪⚠ | The ethos failure everywhere: verification exists as API, not as a thing a user presses | Discord `offering.rs:1032 handle_verify` — registered for `/council /market /grain /doc /dungeon` but NOT `/play` (`portfolio.rs:351`, #10); `/proof turn` fetches a STARK and never verifies it (`explorer.rs:949`, #11); descent re-verify only runs in a test (`descent.rs:1736`, #9); the crown (match-fold, `dreggnet-game-board`) has zero refs (#8). TG `host.rs:388 verify()`, WX `host.rs:464 verify()` — pub methods returning a real `VerifyReport` | TG/WX: `verify` is host-API-only — `press()`/`reply()` route ONLY menu-opens and offering turns, so even with a runtime no user input reaches it. Discord: #8–#12 |
| **Pay** (buy credits / balance / send) | ⚠ | ❌ | ❌ | Discord works E2E; failure mode reads as "money vanished" (#2). Transfer is the register-setter | `pay.rs:77 handle_buy`, `:121 handle_balance`, poll `Err(_) => 0` at `:83` and `:125`; transfer `transfer.rs:51 handle`, records real `tx_hash` `:180`, the "Verify it yourself" embed `:322` | TG/WX: absent — and the pay layer lives inside `discord-bot` (bot sqlite + devnet HTTP), nothing platform-agnostic to reuse. Note TG/WX offering turns are therefore UNMETERED (no `RunCost` charging in either host) |
| **Governance vote** | ⚠ | 🧪 | 🧪 | Discord: two systems, both impaired. TG/WX: council voting genuinely works in-library with a real electorate + quorum | Discord dashboard modal demands the 64-hex prior root (`dashboard.rs:685 gov_vote_modal`, `:691`), shown only in the proposer's ephemeral embed (`:1006`) → single-player governance (#5); submit `:1027`. `/council` offering (`council.rs:107`/`:164`) works in-channel but never reaches `cast_weighted` (#22). TG electorate: `host.rs:170-174` (derived member pubkeys, quorum 2 at `:434`); WX same `:502-509` | Discord: proposals list + public vote buttons (#5), weighted engine (#22). TG/WX: electorate is constructor-time config — no runtime enrollment of a new voter |
| **Gallery publish** | ✅ | ❌ | ❌ | Discord E2E and exemplary: signed ed25519 authorship, durable store, replay-verified on load | `gallery.rs:892` (register), `:967` → `handle_publish`; store install `:140`, replay-verify on load `:430`; publish signs with the publisher's cclerk (module doc `:31-38`) | TG/WX: absent — gallery is Discord-crate code (registry + store + handlers all in `discord-bot`), not an `Offering`, so the parity route doesn't carry it. IPFS pinning unwired (#19) |

## Straightforward alignments (small edits, big honesty)

1. **`/play <offering> verify` on Discord** — `offering::handle_verify::<SeatedTug>` is one
   line away from `portfolio.rs:351` (#10). Closes the "flagship games are the least
   verifiable surfaces" hole.
2. **A `verify` affordance in the TG/WX routers** — both hosts already compute a real
   `VerifyReport` (`dreggnet-telegram/src/host.rs:388`, `dreggnet-wechat/src/host.rs:464`);
   reserve a host-level turn verb next to `TURN_OPEN` (`host.rs:70` in both) and route it in
   `press()`/`reply()` to `self.verify(...)` + render the report. ~30 lines per crate, all
   in-crate, no shared-file collisions.
3. **`/key set` opens the existing modal** (`key.rs:55` → reuse `start.rs:447 key_modal`, #3).
4. **Pay poll errors stop reading as zero** (`pay.rs:83,125`, #2) — distinguish "couldn't
   check, funds safe" from a genuine 0.
5. **Stale-session hint + `/help` games-first** (`offering.rs:1274` #29 — NOTE: offering.rs
   is a Repair-phase file, report-only; `start.rs:222` #28).
6. **Kill or complete `/link-cipherclerk`** (#4) — either the prove step or unregister; as
   shipped it actively walls users out of `/cap-*`.
7. **Council electorate hygiene on TG/WX** — expose `council_member_pubkey` enrollment via a
   host-level turn instead of constructor-only config; small because the derivation is
   already pure and public (`host.rs:210` TG, `:242` WX).

## Deep gaps (real work)

1. **THE platform gap: no Telegram/WeChat runtime exists.** No `[[bin]]`, no reqwest
   `HttpPost` impl, no update loop/webhook, no durable session store, no deploy unit, and
   zero consumers of either crate anywhere in the tree (only `deos-view`'s shared renderers
   reference the names). Every 🧪 above is bounded by this. The crates' own docs scope it
   honestly (`dreggnet-telegram/src/host.rs:36-44`); it is a lane, not an edit — and until
   it lands, "the FIRST non-Discord frontend" is a proof of frontend-agnosticism, not a bot.
2. **Cross-platform identity.** Three disjoint derivations (Discord's is federation-scoped,
   TG/WX's are not — `cipherclerk.rs:63` vs `:50`/`:54`), no link/attestation flow, so one
   human = three strangers; portfolio, credits, and council membership can never follow the
   person. Needs a designed link ceremony (the `/link-cipherclerk` challenge shape, finished).
3. **A platform-agnostic economic layer.** Faucet/credits/pay/transfer are welded into
   `discord-bot` (sqlite + devnet HTTP + serenity embeds). TG/WX turns run unmetered because
   there is nothing to reuse. Extract the pay/credit core behind the same host-thread pattern
   before any second platform charges a turn.
4. **Gallery (and descent, dashboards, explorer) as offerings.** Everything that is a
   Discord *command* rather than an `Offering` — gallery publish, descent daily, the
   explorer, governance dashboards — gets parity for free ONLY if refactored onto the
   offering/host seam the other two frontends consume. Gallery is the cheapest first mover
   (its registry is already frontend-neutral code inside the discord crate).
5. **Discord's own Tier-1s remain deep**: defer-everywhere in game paths (#1), the unwired
   crown (fold-a-match → stranger-verify, #8), real persistent worlds under `/play` (#15),
   public governance (#5). These are backlogged with owners in
   `docs/BOT-EXCELLENCE-BACKLOG-2026-07-17.md`.

## Follow-up ops step (out of scope here)

A REAL run against the deployed Discord bot + node on the AWS edge, exercising each ✅/⚠ row
above (tour → faucet → paid turn → verify → pay-fail path → gov vote → gallery publish) and
recording where the live behavior diverges from this static map. TG/WX have nothing to run
until deep gap 1 closes.
