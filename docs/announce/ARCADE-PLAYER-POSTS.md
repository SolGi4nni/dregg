# Dragon's Arcade — copy you can post

Written 2026-07-26 for **players**, not developers. Everything below is meant to be
copy-pasted as-is. No private vocabulary: if a word here is one you learned from this
repo, it is a bug and should be cut.

The hook, in one sentence, because it is the whole reason to care and it needs no jargon:
**the game re-runs your move against the rules before it counts, so an illegal move is
refused instead of accepted — and a finished game can be replayed by anyone, so the
leaderboard cannot be faked.**

---

## ⚑ PRE-POST CHECK — do this before you post the Automatafl or Multiway-Tug lines

`arcade.dregg.net` is a real public surface, but as of 2026-07-26 it is serving the
**2026-07-19 build**, on which:

| path | live | note |
|---|---|---|
| `/` | 200 | landing |
| `/descent/play` | 200 | **safe to post today** |
| `/offerings` | 200 | catalog — but the 07-19 build still advertises 23 games, not 3 |
| `/automatafl` | **404** | built and green locally; blocked on the redeploy hold |
| `/tug` | **404** | same |

So: **The Descent line is postable now. The Automatafl and Multiway-Tug lines are not,
until the box is redeployed** (`deploy/hbox/RUNBOOK.md`, held pending a HEAD-matching Lean
seed). Curl the two paths before posting.

⚑ And note this reaches the *tweet* too: it says "three games", and on the current live
build two of the three are 404. Either redeploy first, or use the **one-game variant**
below. Do not post a count the box cannot serve.

---

## 1. Tweet-length (251 characters)

> Three games, one browser tab, nothing to install. Every move is re-run against the
> rules before it counts — an illegal move is refused, not accepted — and anyone can
> replay a finished game to check it. So a leaderboard can't be faked.
> arcade.dregg.net

Shorter variant if you want room for a reply or an image credit (203 characters):

> A dungeon crawl, a board game, and a game of hidden influence — in a browser tab, no
> install. Each one refuses an illegal move instead of accepting it, and replays for
> anyone afterwards. arcade.dregg.net

⚑ **One-game variant — safe to post on the current live build** (255 characters). Claims no
count, links only the path that is actually up:

> One life, one torch, and it never refills. Everyone gets the same dungeon each day, drawn
> from a public random number nobody can pick in advance. An illegal move is refused, not
> accepted, and the whole run replays for anyone. arcade.dregg.net/descent/play

---

## 2. Discord post

> **Dragon's Arcade is up.** Three games you can play in a browser tab — no install, no
> account, no wallet. A solo dungeon crawl, a two-player board game, and a two-player
> game of hidden influence.
>
> What makes it different is dull to say and hard to build: when you take a turn, the game
> re-runs your move against the rules before it writes anything down. A move that isn't
> allowed is refused and leaves no trace — you can't talk the page into it. And when a
> game is over, anyone can replay it from the first move to the last. That's why the daily
> leaderboard can't be faked: a run that doesn't replay is shown as FAIL and never ranks.
>
> Two honest warnings. **By default you're identified by a browser cookie** — clear your
> browser data and you're a new person, with no way to get the old one back. And it's
> early: no chat, no friends list, no matchmaking, and nothing you own here is attached to
> money.
>
> Start with The Descent — everyone in the world gets the same dungeon each day:
> <https://arcade.dregg.net/descent/play>

---

## 3. One line per game

### The Descent

> One life, one torch, and it never refills. Everyone gets the same dungeon each day,
> drawn from a public random number nobody can pick in advance. Every single thing you do
> burns a breath of light — including the climb back out — and you only keep what you
> carry to the surface. And your hands hold less the deeper you are: at the bottom, three
> keys and the prize is exactly full. **You can never bring out a treasure AND the prize.**
> Every run is that one choice.

Short: *A daily dungeon crawl with one life and a torch that never refills. You only keep
what you carry back out.*

### Automatafl

> A two-player board game where the piece that decides it is the one neither of you
> controls. You both pick a move in secret, both moves open at the same time, and then a
> neutral automaton in the middle steps according to what you left standing around it.
> You're guessing at your opponent, not waiting on them.

Short: *You both move at once, in the dark, and a piece neither of you controls answers
whatever you left around it.*

### Multiway-Tug

> Two houses pull at seven guilds with cards neither can see the other holding. You get
> four moves for the whole round, one of each: play a card face down, burn two, lay out
> three and let them take one, or lay out two pairs and let them take a pair. Then
> everything turns face up at once and you find out who was really leading what.

Short: *Seven guilds, hidden hands, four moves each. You cut; your opponent chooses which
half they take.*

---

## What NOT to say

These would all be false or misleading today. They are listed so nobody re-adds them.

- ❌ "your history is saved" / "your account" — **by default** identity is an unsigned
  browser cookie (`dregg_user`), minted per browser, with **no password and no recovery**.
  ⚑ An **opt-in 24-word recovery phrase** at `/identity` (`dreggnet-web/src/seed_identity.rs`)
  was in flight as this was written and did not yet compile. **Check it before you promise
  durability.** If it is live, the honest line is *"claim a recovery phrase and your history
  survives a cleared browser"* — and the default is still the cookie, so a player who does
  not claim one has no recovery.
- ❌ "your moves are hidden from us" — in both two-player games, the hidden move is hidden
  by the server *declining to show it to your opponent*. The server can read both sides.
  Say "hidden from your opponent", never "hidden from everyone".
- ❌ "on-chain" / "on a blockchain" — the re-run and the replay happen in the game server
  and in your own tab. There is no live public node today.
- ❌ "earn" / "rewards" / "assets" — banking a relic in The Descent creates an entry that
  belongs to your run and re-derives on replay. It is a score, not money, and nothing on
  the arcade is for sale.
- ❌ "23 games" — we advertise three (`dreggnet_catalog::SHIPPED_KEYS`). The rest still
  open by URL and are not to be written about.
- ❌ any claim that a tug move visibly moves the seven lanes right away — **it usually
  doesn't**, and that is the rules working, not a bug. If you mention tug at all, say
  the face-down card lands at the reveal.
- ❌ "the tug round ends the moment someone hits 11" — **false.** The round always runs all
  12 turns; the 11-weight and 4-guild bars only select *which rule names the winner* at the
  end. (The live tug page currently states the early-end version; another lane owns that.)
