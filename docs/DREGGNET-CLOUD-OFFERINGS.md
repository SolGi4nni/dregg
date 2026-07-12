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
