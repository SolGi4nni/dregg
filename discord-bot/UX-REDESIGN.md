# DreggNet Bot UX redesign — from a command palette to a conversation

## The problem

The bot ("Dragon's Egg", live on the devnet) exposed ~50 slash commands. To do
anything a user had to *discover* and *memorise* the right command and its
options: `/cipherclerk create`, `/faucet`, `/send @user 10`, `/key set …`,
`/name-register …`, `/gov-propose …`, `/queue-create …`, and so on. That is a
high-friction, palette-style interface — the user is expected to learn the API.

Telegram bots feel lighter because they invert that. You send `/start`, the bot
welcomes you and shows a few **buttons** (an "inline keyboard"). After that you
mostly just **type**, and the bot responds and drives the next step. You click,
you don't memorise.

## The new model

Three affordances, in priority order:

1. **A handful of entry points.** `/start` (onboard + a button menu) and `/help`
   (the map). These are the only commands a newcomer needs to know.
2. **Conversational.** Your semi-private channel is the primary surface: you just
   *type* and your confined Hermes responds, metered + cap-gated + receipted
   (already implemented in `hermes_channel.rs` — now the headline path, not a
   footnote). `read …`, `search …`, `fetch …`, `run …`, `write …`, or plain
   chat (routed through your own ported-in LLM key when set).
3. **Buttons / select-menus.** The common actions are buttons on bot messages
   (the inline-keyboard equivalent), not slash commands. A press fires the SAME
   real, cap-gated, receipted dregg turn the slash command did — the affordance
   changed, the verification did not.

Onboarding flow:

```
/start
  └─ no wallet yet?  →  [Create my wallet]  (one button → a real derived cell)
  └─ have a wallet?  →  [Get test DEC] [Balance] [Send] [Claim my channel]
                        [Set my LLM key] [Node status] [Apps…] [Help]
        │
        ├─ [Claim my channel] → a private channel; from then on you just TYPE
        ├─ [Send]             → a small form (modal) → real transfer turn
        ├─ [Set my LLM key]   → a form → sealed key, metered brain
        └─ [Apps…]            → the rich /dregg dashboard (Identity / Names /
                                Governance / Subscription panels — buttons+forms)
```

## Where every old slash command now lives

Legend: **conv** = just type it in your channel · **button** = a button/menu in
`/start` or the `/dregg` dashboard · **slash** = kept as an (advanced/optional)
slash command · **dropped** = retired from the slash surface (capability kept,
reachable via a button).

| Old command | New home |
|---|---|
| `/cipherclerk create` | **button** `/start` → Create my wallet |
| `/cipherclerk balance` | **button** `/start` → Balance |
| `/cipherclerk address` / `export` / `mint` / `attenuate` / `tokens` / `authorize` | **slash** (advanced keychain; kept) |
| `/faucet` | **button** `/start` → Get test DEC (still **slash** too) |
| `/send` | **button** `/start` → Send (modal) (still **slash** too) |
| `/tip` | **dropped** (duplicate of `/send`) |
| `/key set/rotate/revoke/status` | **button** `/start` → Set my LLM key (modal); rotate/revoke/status still **slash** |
| `/channel` | **button** `/start` → Claim my channel (still **slash** too) |
| `/status` | **button** `/start` → Node status (still **slash** too) |
| `/metrics` | **dropped** (folded into Node status / dashboard) |
| `/dashboard` | **slash** (live node health; also reachable) |
| `/dregg` | **button** `/start` → Apps… (the rich dashboard; still **slash**) |
| `/credential` | **dropped** → `/dregg` → Identity panel |
| `/name-register` / `name-resolve` / `name-whois` | **dropped** → `/dregg` → Names panel |
| `/gov-propose` / `gov-vote` / `gov-status` / `gov-routes` | **dropped** → `/dregg` → Governance panel |
| `/queue-create` / `publish` / `subscribe` / `status` / `mount` | **dropped** → `/dregg` → Subscription panel |
| `/explorer`, `/activity`, `/leaderboard`, `/history` | **slash** (reads; kept; surfaced from Help) |
| `/proof` | **slash** (verification read; kept) |
| `/presence`, `/gallery` | **slash** (kept) |
| `/cap-share/accept/delegate/list/revoke/peer` | **slash** (advanced CapTP; kept) |
| `/handoff`, `/handoff-redeem`, `/handoff-status`, `/intent` | **slash** (advanced; kept) |
| `/setup-federation`, `/link-cipherclerk`, `/unlink-cipherclerk`, `/federation-status`, `/federation-peers` | **slash** (admin/advanced; kept) |
| `/council-status`, `/council-approve` | **slash** (polis governance; kept) |
| `/bounty`, `/deos`, `/card`, `/coordinate` | **slash** (interactive surfaces; kept) |

### Net effect

A newcomer needs to learn **two** commands (`/start`, `/help`) instead of fifty.
Everything common (wallet, faucet, balance, send, channel, key, status, the app
suite) is a **button** or just **typing**. Fifteen redundant slash commands
(`tip`, `metrics`, `credential`, the four `gov-*`, the three `name-*`, the five
`queue-*`) are retired from the slash surface — their capability is unchanged and
reachable from the `/dregg` dashboard's panels. The remaining slash commands are
re-cast as an *advanced/optional* surface, not the thing you must memorise.

## What is real underneath (unchanged)

The buttons are pure affordance. Every action button calls the same code the
slash command did:

- **Create my wallet** → `UserCipherclerk::derive` + `devnet.register_cell` +
  `db.register_user_with_mode` (a real custodial cell).
- **Get test DEC** → the real faucet turn (`devnet.faucet_request`, rate-limited).
- **Balance** → `devnet.get_balance` on your cell.
- **Send** → `devnet.submit_transfer_turn` — a canonical signed conserving turn.
- **Claim my channel** → the real gated channel + DB binding; messages then drive
  your confined Hermes (cap-gated, metered, receipted).
- **Set my LLM key** → `key_vault::seal` (AEAD, per-user key) + `db.set_llm_key`.
- **Node status** → the live `/status` read.
- **Apps…** → the `/dregg` dashboard, whose panel buttons submit the real
  nameservice / governance / queue / identity actions.

So the redesign is an *interaction-model* change. The verification, metering,
conservation, and receipts are untouched.

## What is implemented now vs. deeper rework remaining

Implemented in this pass (`src/commands/start.rs` + the `execute_*` refactors):

- `/start` onboarding + the status-aware action-button menu.
- `/help` — the map of the new model.
- Action buttons firing the real turns: create wallet, faucet, balance, send
  (modal), set key (modal), claim channel, node status, open Apps dashboard.
- The conversational channel promoted to the primary path (already wired in
  `hermes_channel.rs`); `/start` and `/help` funnel users into it.
- Fifteen redundant slash commands retired from the registered surface.

Deeper rework (named, not done here):

- Conversation outside a claimed channel (DMs / @mention anywhere) — today the
  conversational loop only runs inside a registered per-user channel.
- A real LLM intent-parser replacing the deterministic verb classifier in
  `hermes_channel::classify` (the live-Hermes/ACP seam, already documented there).
- Folding the remaining advanced slash commands (CapTP, handoff, federation,
  polis) into dashboard-style button panels.
- Select-menu-driven recipient picking for Send (modals can't host a user
  picker, so Send takes an @mention / id in the form for now).
