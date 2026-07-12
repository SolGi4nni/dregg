# DreggNet Cloud — the Offering/Session abstraction (design)

Status: **design** (2026-07-11). The dungeon we built is **offering #0** — the first instance of a general pattern.
The discord-bot (and a parallel web surface) are **frontends to DreggNet Cloud**; the cloud hosts *offerings*
(confined, verifiable, paid, per-session things) on the real dregg substrate. The dungeon proved the whole shape
end-to-end; this generalizes it so hosted-Hermes, Sandstorm grains, and the next thing plug into the same rails.

## The shape every offering shares (already built, for the dungeon)
1. **A per-session confined thing** — a channel/thread hosts one live session.
2. **A confined intelligence/app** — the dungeon's narrator (jailed LLM); for others, a hosted Hermes agent or a grain.
3. **Real verifiable turns** — each input is a real executor turn -> a `TurnReceipt`; `verify_by_replay` re-checks the
   whole chain. The executor is the source of truth (a jailbroken narration cannot change the world).
4. **Payment-gated** — `dregg-pay` credits (dual-asset $DREGG/USDC); a paid action debits a credit; empty -> free tier.
5. **Optionally collective** — write-once ballots + quorum (collective-choice) when a crowd drives one session.

## The abstraction
```
trait Offering {
    type Session;                                   // the live confined state (a WorldCell, a Hermes jail, a grain)
    fn open(&self, cfg: SessionConfig) -> Result<Self::Session, OfferingError>;
    fn actions(&self, s: &Self::Session) -> Vec<Action>;         // candidate moves (ballot options / buttons)
    fn advance(&self, s: &mut Self::Session, input: Action, actor: DreggIdentity) -> Outcome; // one real turn
    fn verify(&self, s: &Self::Session) -> VerifyReport;         // verify_by_replay / the offering's proof
    fn render(&self, s: &Self::Session) -> Surface;             // room/prose/state for the channel embed
    fn price(&self, input: &Action) -> RunCost;                 // what a paid action costs (credits)
}
```
- **Outcome** = `Landed(TurnReceipt) | Refused(reason)` — the same anti-ghost shape the dungeon uses.
- **Session** is offering-specific but always carries a real verifiable state chain.
- The bot never trusts the confined intelligence — it resolves the *typed Action* on the substrate, not the prose.

## The shared orchestration layer (the bot's job — the "Midjourney" layer)
`/start <offering>` -> the bot (admin) **spins a channel/thread** (via the dormant `discord_caps` engine + `GUILDS`/
`GUILD_MEMBERS` intents + a `guild_create` handler) -> `Offering::open` -> posts `render` with `actions` as buttons ->
each press is a ballot / a paid action (gate on `dregg-pay` credits) -> `Offering::advance` (a real turn) -> update
the embed -> on completion, `Offering::verify` + archive the thread. One lifecycle, every offering.

## Frontends — Discord is #0; Telegram, WeChat, web are the SAME offerings, different surfaces
The offering/session/payment/verify/ballot CORE is **frontend-agnostic**. A `Frontend` renders an offering's `Surface`
and collects `Action`s; the core resolves them on the substrate. So every surface reuses ONE core — only presentation
differs (and the executor stays the sole source of truth on all of them).
```
trait Frontend {
    fn identity(&self, user: PlatformUser) -> DreggIdentity;         // derive the user's dregg identity per platform
    fn spin_session(&self, off: &dyn Offering, cfg: SessionConfig) -> SessionSurface; // a thread/group/chat per session
    fn present(&self, s: &SessionSurface, surface: Surface);         // room/prose/state + the action controls
    fn collect(&self, ev: PlatformEvent) -> Option<(SessionId, Action, DreggIdentity)>; // a press/command -> an action
    fn teardown(&self, s: SessionSurface);                           // archive on completion
}
```
- **Discord (#0, built):** threads/channels + buttons + `GUILDS`/`GUILD_MEMBERS` intents; identity from the user's
  derived Ed25519 (`UserCipherclerk`).
- **Telegram:** Bot API — groups/forum-topics, inline keyboards, per-chat sessions; identity from the Telegram user id
  → derived dregg identity; payment via Telegram Payments OR the same on-chain deposit-address flow.
- **WeChat:** Official Account (template/menu messages — no arbitrary buttons) for lightweight play, a **Mini-Program**
  for rich surfaces; China-platform constraints (mp.weixin.qq.com, OA message API, WeChat Pay). The heaviest lift.
- **Web:** the richest surface; the same offerings + `dregg-pay` credits.

**The factoring this demands:** pull the offering/session/payment/verify/ballot logic OUT of `discord-bot/fiction.rs`
into a **frontend-agnostic `dreggnet-offerings` crate**; the discord-bot becomes a thin `Frontend` impl; Telegram/
WeChat/web are more `Frontend` impls. `dregg-pay` (payments), the verifiable substrate (WorldCell/receipts), and the
collective are shared across all of them. Doing this NOW (while there is one frontend) is cheap; later it is a rewrite.

**REUSE the deos surface — do NOT reinvent `Surface`/`Action`.** The frontend-agnostic surface layer ALREADY EXISTS
and the bot already renders it: `deos-view` = a `ViewNode` (a moldable view of a cell); `starbridge-web-surface::
affordance` = a cell's **cap-gated affordances** (`AffordanceIntent`/`EffectSummary`), each firing a real dregg turn.
The bot's `/deos` (a cell's affordance surface → cap-gated buttons) and `/card` (a `deos_view` ViewNode → interactive
buttons that fire real turns + re-render, `deos_surface.rs`) are exactly this. So map the abstractions onto it, don't
duplicate: an offering's **`Surface` is a deos `ViewNode`/affordance surface**; its **`Action`s are cap-gated
affordances**; a **`Frontend` is an affordance-renderer** (Discord is built — `deos_surface.rs`; Telegram/WeChat are
more affordance-renderers mapping the same affordances onto inline keyboards / OA-menus / a Mini-Program). The **web
frontend is `deos-js` + `web-cells`** (the existing web cell rendering). The dungeon's ballot buttons are just one
affordance shape. EVERYTHING — offerings AND plain deos cells (dregg-doc, the cockpit, a tally card, a grain view) —
flows through this ONE cap-gated, verifiable, moldable surface, on every frontend. That is the unification: the
offering/session layer sits *above* the deos affordance surface; the frontends are *renderers of affordances*; the
executor is the sole referee on all of them.

## Offerings
- **#0 dungeon** — `RealSession` over `dungeon_on_dregg` WorldCell + the narrator + ballots. **Built + being migrated
  into `/dungeon` now.**
- **hosted-hermes** — a confined Hermes *agent* session (the jailed LLM produces typed Actions; turns are receipts).
  Reuse `deos-hermes`/`grain-jail`. Next.
- **grain** — a Sandstorm grain session (a confined app) surfaced in a channel. Next.
- **web** — the same offerings, a parallel surface.

## What's built vs to-build
- BUILT (dungeon-proven): the substrate (WorldCell/receipts/verify), payments (dregg-pay dual-asset), the collective
  (ballots/quorum), the narrator (real Bedrock, attested), the beginnings of channel orchestration (`channel.rs` +
  the dormant `discord_caps`).
- TO BUILD: the `Offering` trait + factoring the dungeon behind it; the full channel/thread **lifecycle**
  (create/permission/archive/resume per session, roles); hosted-Hermes + grain offerings; the web surface; the
  DreggNet Cloud integration (bot + web as cloud frontends). Entwingle with `~/dev/DreggCloud` (operated firmament)
  and `~/dev/DreggNet` — sibling infra; contribute breadstuffs-native pieces, never scope against them.
