# Bot E2E Flow Gap-Map — Discord · Telegram · WeChat (FINAL, 2026-07-17)

Cross-adapter map of every user-facing flow across the three chat frontends, from code
reading at HEAD. This is the FINAL revision after the four phases of this run landed:
**Ground** (the original static map + `docs/BOT-EXCELLENCE-BACKLOG-2026-07-17.md`, whose `#N`
numbers are used below), **Fanout** (the shared `dreggnet-catalog` registrar —
`docs/BOT-SHARED-BACKEND-DESIGN.md`), **Repair** (the Discord Tier-1/Tier-2 closure sweep),
and **Telegram** (viewer-aware rendering + electorate + catalog cutover). A REAL run against
the deployed Discord bot + node remains the ops follow-up; the checklist at the bottom scopes
it.

## The one-sentence shape

**Discord is still the only bot that exists as a bot** — but the gap inside Discord closed
hard (every Tier-1 UX/honesty hole from the backlog is now fixed at HEAD), and the gap
between the three frontends changed kind: `dreggnet-telegram` and `dreggnet-wechat` now build
the SAME 18-offering catalog from ONE registrar (`dreggnet_catalog::build_full_catalog`)
instead of hand-copied lists, route verify through their routers, and project per-viewer
surfaces — full mechanism-level parity, still **library-only** (no `[[bin]]`, no update
loop, no durable session store) until the runtime-shell lane lands.

Legend: ✅ works E2E · ⚠ exists but dead-ends or degrades · 🧪 works in-library only
(driven tests; no live surface) · ❌ absent · **[CLOSED]** = fixed during this run.

## The gap-map

| flow | discord | telegram | wechat | state at HEAD | gap |
|---|---|---|---|---|---|
| **Onboarding** (guided tour) | ✅ | ❌ | ❌ | Discord E2E: identity → faucet → first paid turn, node-outage retry (`start.rs:100/:113`, tour faucet `:348`, send `:376`); `/help` leads with the games-first "just type" flow | TG/WX have no `/start`; nearest analog is the offerings menu (`dreggnet-telegram/src/host.rs:239`, `dreggnet-wechat/src/host.rs` `present_offerings_menu`) which assumes you already know what dregg is |
| **Identity** (derived cipherclerk) | ✅ | 🧪 | 🧪 | All three derive a REAL Ed25519 identity from platform uid (TG `cipherclerk.rs:50`, WX `:54`, Discord `cipherclerk.rs:63`) | UNCHANGED deep gap: TG/WX derivations take NO `federation_id` (Discord's does) and use separate bot secrets — the same human is three unrelated identities with no cross-platform link flow. The `/link-prove` ceremony (below) is now the shape to generalize |
| **Identity: LLM key mgmt** | ✅ **[CLOSED #3]** | ❌ | ❌ | `/key set` and `/key rotate` now open the private modal (`key.rs:93/:111` → `start::key_modal`); the secret never travels as a visible slash option | TG/WX still have no key store / LLM layer at all |
| **Identity: external cclerk link** | ✅ **[CLOSED #4]** | ❌ | ❌ | `/link-prove` (`link_proof.rs`) verifies the Ed25519 challenge signature + cell-id derivation and promotes to `ExternalVerified`, unlocking handoff-redeem / `/cap-delegate` / dashboard actions. Honest scope: an external key is never custodially signed for | Flow still Discord-only; the generalized cross-platform ceremony is deep gap 2 |
| **Faucet** | ✅ | ❌ | ❌ | Discord E2E against devnet (`social.rs:32→:84`) | TG/WX still have no economic layer (deep gap 3) |
| **A game turn** (descent / play) | ✅ **[CLOSED #1]** | 🧪 | 🧪 | Descent defers BEFORE the ~20s narration (`descent.rs:1101 ack::defer_slash`, re-render lands as an EDIT `:1255`) — the "commits but shows failure" hole is gone; `/descent room` re-shows a lost room message. TG `press()` / WX `reply()` advance real turns AND project per-viewer surfaces (`render_for`/`actions_for` — hidden-hand fog reaches the right chat) | TG/WX: unreachable by a user without the runtime shell; in-memory sessions lose in-flight state on restart (same class as #29) |
| **Offering advance** (generic adapter) | ✅ **[CLOSED #29 #31 #32]** | 🧪 | 🧪 | STRONGEST parity story, now by construction: ONE `OfferingHost`, and TG + WX build the FULL 18-offering catalog from the ONE registrar (`dreggnet_catalog::full_catalog_host`; TG `host.rs:408`, WX `host.rs` `wechat_default_host` — aligned this pass). ONE `SeatedTug` home (`dreggnet-catalog/src/seated.rs`; TG/WX re-export). TG's parity test compares against the LIVE web catalog both ways. Discord: silent `NotOurs` drops now answer honestly (`offering.rs:1161-1165`), live-session wipe is refuse-with-confirm (`open_guard.rs`) | Discord still registers its 18 bespoke (per-type stores + static match, `offering.rs:1337/:1400`) — the catalog cutover for Discord is scheduled work (deep gap 4). Demo worlds still not shared state (#15) |
| **Verify** | ✅ **[CLOSED #10 #11 #12]** | 🧪 **[router CLOSED]** | 🧪 **[router CLOSED]** | The ethos failure is repaired on all three at the logic level: Discord has a standing "⛓ re-verify chain" button on EVERY offering surface (`verify_chain.rs`), `/play <offering> verify` (`portfolio.rs:460-493`), and `/proof turn` runs the REAL `dregg_sdk::verify_full_turn` on the fetched STARK (`proof_verify.rs` — internal-soundness + VK-binding, canonical-root binding honestly named as the seam). TG/WX now route the reserved `verifychain` verb through `press()`/`reply()` to the real re-verifier (this pass — `TURN_VERIFY`, `HostPress::Verified`/`WeChatReply::Verified`, driven tests) | The crown stays unwired: fold-a-match → stranger-verify (`dreggnet-game-board`, #8) has zero refs — own lane. Descent re-verify still test-only (#9) |
| **Pay** (buy credits / balance / send) | ✅ **[CLOSED #2 #13]** | ❌ | ❌ | Poll errors now read "couldn't check — funds safe, retry", never a fake 0 (`pay.rs:13,:147,:211`); `/history`/`/leaderboard` rows carry a `txcheck:` button that re-checks the hash against the LIVE node (`tx_recheck.rs`) | TG/WX absent AND unmetered (no `RunCost` charging in either host) — the platform-agnostic economic layer is deep gap 3 |
| **Governance vote** | ✅ **[CLOSED #5]** / ⚠ #22 | 🧪 | 🧪 | A successful proposal now posts a PUBLIC card with vote buttons (`dashboard.rs:367,:1008`) — anyone with a hosted cipherclerk votes without typing anything; the modal's prior-root field is copyable from the card / Proposals list (`:742`). TG/WX council works in-library with a real derived electorate + quorum | Discord's `/council` offering still never reaches the verified weighted engine (`collective_choice::cast_weighted` has zero discord-bot refs — #22, own lane). TG/WX electorate is constructor-time only (no runtime enrollment) |
| **Subscription DMs** | ✅ **[CLOSED #6]** | ❌ | ❌ | Publish now fans the body out as real DMs to every subscriber and reports delivered/failed (`subscription_dispatch.rs`) — "You will receive DMs" is no longer fiction | Discord-only surface |
| **Gallery publish** | ✅ **[CLOSED #19]** | ❌ | ❌ | Signed ed25519 authorship, durable store, replay-verified on load (`gallery.rs:140,:430`); publish now pins `pin:true` and shows the CID over the committed ugc-dregg IPFS bridge (`gallery_ipfs.rs` — CID derived network-free, live pin needs the deploy's IPFS endpoint) | TG/WX absent — gallery is Discord-crate code, not an `Offering`; parity requires the offering-ization lane (deep gap 4) |

## Gaps CLOSED this run

**Repair phase (Discord):** #1 defer-before-narration + `/descent room` recovery · #2 honest
pay-poll failures · #3 `/key set`→modal · #4 `/link-prove` completes the link ceremony ·
#5 public proposal cards + vote buttons · #6 subscription DM dispatch · #10/#12 pressable
verify everywhere (standing button + `/play … verify`) · #11 `/proof turn` actually verifies
the STARK · #13 ledger-row re-check button · #19 gallery IPFS pin + CID · #29/#31 stale/foreign
presses answered honestly · #32 live-session wipe guard.

**Fanout phase:** `dreggnet-catalog` (ONE registrar, `CatalogConfig`, ONE `SeatedTug` home)
+ Telegram cutover + a both-polarity parity test against the live web catalog.

**Telegram phase:** viewer-aware `render_for`/`actions_for` through the TG host (per-viewer
hidden-hand on TG, matching WX's 07-15 fix), electorate derivation in the constructor,
`seated.rs` collapsed to the shared re-export.

**Final alignment pass (this document's edit):**
1. **WeChat → the shared catalog registrar** — `wechat_default_host` is now
   `dreggnet_catalog::full_catalog_host(...)` (behavior-preserving by construction; the
   catalog's registrations are byte-identical to the hand copy it replaces); ten
   per-offering deps dropped from `dreggnet-wechat/Cargo.toml`; `src/seated.rs` is now the
   compatibility re-export. Closes the last hand-maintained catalog copy among the
   `OfferingHost` frontends (web's own copy is guarded by the TG parity referee).
2. **A routable verify verb on TG + WX** — reserved `TURN_VERIFY = "verifychain"` (the same
   verb string as Discord's standing button) routed in `TelegramHost::press` /
   `WeChatHost::reply` to the offering's REAL re-verifier, returned as
   `HostPress::Verified` / `WeChatReply::Verified` with the `VerifyReport`; surfaces stay
   byte-stable (never presented; WX rides the codec's off-list marked-id path
   `#verifychain:0`). Driven tests added in both crates (verify after a real turn; read-only
   — next press still resolves; menu-state honestly refused). Closes "verify is
   host-API-only — no user input reaches it".

## Deep gaps — each needs its OWN lane (not an edit)

1. **THE platform gap: no Telegram/WeChat runtime exists.** No `[[bin]]`, no reqwest
   `HttpPost` impl, no update loop/webhook, no durable session store, no deploy unit, zero
   consumers of either crate. Every 🧪 above is bounded by this. The crates' docs scope it
   honestly (`dreggnet-telegram/src/host.rs:36-44`). Until it lands, TG/WX are proofs of
   frontend-agnosticism, not bots.
2. **Cross-platform identity.** Three disjoint derivations (Discord's federation-scoped,
   TG/WX's not), separate bot secrets, no link flow — one human = three strangers.
   `/link-prove` now demonstrates the ceremony shape (challenge → external Ed25519 signature
   → verified promotion); the lane is generalizing it across platforms + federation-scoping
   the TG/WX derivations.
3. **A platform-agnostic economic layer.** Faucet/credits/pay/transfer are welded into
   `discord-bot` (sqlite + devnet HTTP + serenity embeds); TG/WX turns run UNMETERED (no
   `RunCost` charging in either host). Extract the pay/credit core behind the host-thread
   pattern before any second platform charges a turn.
4. **Discord onto the catalog seam; gallery (and descent, explorer, dashboards) as
   offerings.** Discord still registers bespoke (per-type stores, 18-arm match) — the
   cutover design is written (`docs/BOT-SHARED-BACKEND-DESIGN.md`); gallery is the cheapest
   first offering-ization (its registry is already frontend-neutral code inside the discord
   crate). This is what makes TG/WX parity for onboarding/gallery/pay free later.
5. **The remaining Discord Tier-1s:** the unwired crown (fold-a-match → stranger-verify,
   #8; descent re-verify user-facing, #9), real persistent worlds under `/play` (#15), and
   `/council` → the verified weighted engine (`cast_weighted`, #22). Backlogged with owners
   in `docs/BOT-EXCELLENCE-BACKLOG-2026-07-17.md`.
6. **(small lane) TG/WX council electorate enrollment at runtime** — both hosts take the
   electorate at construction only; a new voter needs a host rebuild. The derivation is
   already pure + public (`council_member_pubkey`), but enrollment must reach the live
   `CouncilOffering`, which today takes members only in `new()`.

## THE one thing only a REAL deployed run can confirm — and its checklist

Everything above is confirmed at the logic level (driven tests / read code). The ONE
behavior no test here can establish is **Discord's 3-second ACK discipline under real
gateway latency on the game-turn path** — that the `#1` fix (defer, then the ~20s narration
landing as an EDIT) actually beats the window on the deployed bot against a real node, for
every long-running handler. That is the ops follow-up (the Discord bot runs on the AWS
edge; NEVER `docker compose down` the edge gateway).

**Checklist for the deployed-bot-against-real-node run** (record every divergence from this
map as a new backlog item):

1. `/start` tour end-to-end: identity → **Get test DEC** (faucet) → first paid turn; then
   repeat with the node stopped mid-tour → the retry affordance, not a dead embed.
2. **THE headline:** `/descent daily` — commit + full narration; confirm ONE deferred ACK
   (no "The application did not respond"), the room arriving as an edit, and buttons live
   after ~20s. Then delete the room message and recover it with `/descent room`.
3. `/play tug` → play a move → press the standing **⛓ re-verify chain** button → the public
   report; also `/play tug action:verify`.
4. `/proof turn <hash>` on a real committed turn → "verifies under VK …, checked just now".
5. `/pay buy` and `/balance` with the node STOPPED → "couldn't check — funds safe", never a
   `0`; with the node up → real credit flow.
6. `/send` a transfer → row in `/history` → press its `txcheck:` button → live-node
   confirmation of the recorded `tx_hash`.
7. Governance: propose from account A → the PUBLIC card appears in-channel → vote from
   account B via the button (no hex typed) → enact at quorum.
8. `/key set` → the modal opens (secret never visible in the slash option); a keyless
   real-AI path still fails honestly.
9. `/link-cipherclerk` with an external cell → sign the challenge → `/link-prove` →
   confirm `ExternalVerified` actually unlocks `/cap-delegate` + handoff redemption.
10. Gallery: publish → CID shown; confirm whether the deploy has a live IPFS endpoint wired
    (in-process derivation is network-free; pinning is only real with an endpoint).
11. Subscription: subscribe from B, publish from A → B receives the DM; publisher receipt
    counts delivered/failed truthfully (including a subscriber with DMs closed).
12. TG/WX: nothing to run until deep gap 1 closes — do NOT stand up ad-hoc shells for this
    checklist; the runtime shell is its own lane with a durable session store.
