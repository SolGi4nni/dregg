# Crowd-Stream Engine — Design (2026-07-19)

**Status: DESIGN.** The "branch out" expansion ember + spwashi (RPG Wednesday) sketched: crowd-played,
streamed, VERIFIABLE games where the audience's collective decisions drive ONE real on-chain turn —
"even the audience's moves are receipts." Synthesized from a read-only survey of the real code (the
crowd-vote engine, the render pipeline, the persistence primitives, companions). Facts are grounded
in files; the round-driver-with-live-events wiring is NEW.

## The reusable ANCESTOR is already built + tested

`dungeon_on_dregg::collective::CollectiveRound` / `CollectiveChoice` is the "signed-ballot tally → ONE
verified turn" primitive, and its `resolve_into_world` (collective.rs:513) is literally documented as
**"THE SEAM — the crowd decides, the real world resolves the decision"**: it quorum-certifies the
argmax winner, binds a decision_commitment into the world cell, and applies the winning command as ONE
real `TurnReceipt`. Below quorum → refused, world unchanged. The quorum gate is the polis `AffineLe`
predicate `M·RESOLVED − Σ TALLY ≤ 0` (WriteOnce ballots + Monotonic tally + light-client replay).

Its small-group instances are LIVE: `dreggnet-party` `PartyFork::resolve_into` (3-of-4 seated custody
keys → one gate turn), the HTTP `/party` lane (`demo/dungeon-service` `handle_party_close`, M=3-of-5),
and `dregg-pay` governance + coauthor all reuse the SAME engine. The round-driver ancestor is
`run_collective` — a passage-loop that opens a poll, collects a ballot closure, resolves, and advances
one verified turn. **The crowd-stream adapter replaces that ballot closure with live stream events.**

## The pipeline

```
stream events (YouTube Super Chat / Twitch cheer / TikTok gift + chat)
  → ingestion adapter  → a ballot per viewer (weighted by the paid amount)
  → CollectiveRound.cast (custody-signed; the adapter mints/holds the per-viewer key)
  → CollectiveRound.resolve_into_world  → ONE certified TurnReceipt on the game executor
  → the game state (ViewNode) re-renders → pushed to a transparent OBS overlay
  → the whole run folds to a proof (the crown)
```

## Reuse vs build

### REUSE (real, tested)
- **`CollectiveRound` / `resolve_into_world`** — the crowd-round → one-turn core, with the quorum
  certificate. This IS the round primitive; the stream adapter feeds it.
- **`ViewNode` IR + `render_html`** (deos-view web.rs:67) — the richer renderer that already emits
  `data-slot`/`data-max`/`data-cases` live-binding hooks (the form path drops them); the overlay's
  starting point. **`render_tally_live_document`** (web.rs:890) is an existing self-contained live
  tally-board page — the vote-widget's closest ancestor.
- **`OfferingHost`/`HostThread`** — the authoritative live state a spectator identity renders (fog via
  `render_for`).
- **`DreggIdentity`** (offerings lib.rs:374) — the cross-platform derived-pubkey "per-viewer thread";
  the resume store (`SqliteRpgResumeStore`) already scopes a player's whole world to it. A viewer's
  **Companion** (`dreggnet-companion`: owned content-addressed asset + a receipt-chain-persistent
  leveling cell) is the personal thread that follows them across streams — fuse Companion + DreggIdentity.
- **The federation** (attested cross-node turn stream) — the substrate for async multi-group.
- **The crown / `WholeChainProof`** — folds a run to one proof a stranger re-verifies.
- **`branch-stitch`** (`BranchStitchSession`: real fork → drive → stitch with a proven settlement gate;
  disjoint edits merge, conflicts refused first-class, revoked authority dropped) + **`World::open`**
  (durable redb commit-log, crash-safe) — the correct conceptual core + persistence spine for
  "groups diverge privately then merge soundly."

### NEW (must build)
1. **Ingestion adapters** — YouTube Live Chat API (Super Chat → weighted ballot; official, 70/30
   split), Twitch EventSub/IRC, TikTok webcast (UNOFFICIAL, fragile, needs a LIVE-enabled account).
   Each maps a platform event → a `SignedBallot` for the round.
2. **The round driver over live events** — `run_collective` with the ballot closure replaced by the
   adapter stream; a round opens/tallies/closes on a timer into one turn.
3. **A live PUSH channel** — there is NO SSE/WebSocket/polling anywhere in dreggnet-web today (the only
   liveness is a client-initiated `X-Fragment` swap on the acting client's own POST). An overlay showing
   *other people's* votes needs server→browser push (axum `Sse` is the fit) + a broadcast-on-vote fan-out.
4. **A transparent OBS surface** — a `document()`/CSS variant with `background:transparent`, chrome
   stripped (every current body/card background is opaque), sized as an overlay browser-source.
5. **Electorate scaling** — the vote roster is FIXED at `muster` (no join/leave); a large crowd needs a
   dynamic electorate + real per-viewer custody signatures (the demo derives keys from name strings).
6. **Async multi-group fold** — `branch-stitch` `stitch` is strictly pairwise and NEVER writes back to
   base; NEW = `apply(verdict)` to advance base, an N-way/sequential fold, and wiring it onto the durable
   `World::open` image (the three exist but are disjoint).

## LANDED (2026-07-20) — the close-loop runs on a DEPLOY PATH, not only in tests

NEW items #2 (round driver over live events + a close-on-a-timer) and #3 (a live SSE push) are
built and wired into the served app (`dreggnet-web`), env-gated so the default is unchanged:

- `dreggnet_web::crowd_round::CrowdRound` feeds live stream events into the real
  `CollectiveRound` and folds a window into ONE certified `TurnReceipt` (`close_into_world`).
- `dreggnet_web::overlay::OverlayState` is the SSE surface (`GET /overlay`, `/overlay/sse`,
  `POST /overlay/ingest[/youtube]`, operator-bearer-gated). Its `drive_close` is the deployment
  close-tick: close → resolve the quorum-certified winner into the world → push the reset tally.
- `dreggnet_web::overlay::LiveCloseLoop` binds an `OverlayState` to a live game `WorldCell` +
  `Scene` and drives `drive_close` on a `tokio::time::interval` (round window). `make_app` mounts
  it via `overlay_mount_from_env`:
  - **`OVERLAY_LIVE_WORLD` unset (default)** → the tally board (ingest→push only, no world resolve),
    byte-identical to before;
  - **`OVERLAY_LIVE_WORLD` set** → a LIVE demo Warden's Keep the crowd steers, closing every
    `OVERLAY_ROUND_SECONDS` seconds into one certified world turn.
- **Stuck-window handling:** a quorum-certified but ILLEGAL command (the executor's teeth) is
  *dropped* (the round is never bricked re-certifying it), distinct from a below-quorum window,
  which is *retained* for retry.

**Honest labeling (unchanged posture):** "certified" here means **quorum-certified +
executor-admitted, NOT FRI-sound-on-chain** — it inherits the deployed ledger's undischarged
FRI/STARK floor. The mounted world is a **demo** (the Keep); a real deployment supplies its own
game world (`WorldCell`/`Scene`/proposals) — the demo is a poll-driven scene, not the product's
persistent RPG-Wednesday world. The viewer overlay page carries this caveat as page chrome
(`LIVE_OVERLAY_LABEL`). Electorate scaling (#5: dynamic roster + real per-viewer custody, not
platform-held keys) and the async multi-group fold (#6) remain the named net-new pieces.

## Multi-group / RPG-Wednesday async model
Each streaming group runs its own `branch-stitch` branch off a shared persistent `World` (`World::open`);
a group's crowd rounds land turns on its branch; periodically the branches fold back into base via the
settlement-sound stitch (once apply-to-base + N-way fold are built). The federation witnesses the folds.
The pilot: one shared RPG-Wednesday world that persists between Wednesdays and accumulates each group's
verified contributions.

## Highest-leverage first step
**One YouTube adapter → `CollectiveRound` → one turn → a transparent SSE tally overlay**, on The Descent
or a tug match. It exercises the whole spine (ingest → weighted ballot → certified turn → live overlay)
with the one official, best-paying platform, and proves the novel claim — a crowd-played game that's
*provably fair* — before any multi-group/persistence work. Gating bits are ember's: a YouTube channel +
API key + OBS.

## Honest gaps
Platform API keys + a LIVE-enabled account + OBS are ember's. TikTok ingest is unofficial (ToS
gray-area, fragile). The verified-turn spine inherits the deployed ledger's undischarged FRI/STARK floor
(no "verified on-chain" over-claim). The async multi-group fold (apply-to-base + N-way + persistent
branch-stitch) is the largest net-new piece.
