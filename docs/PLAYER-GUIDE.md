# How to play — Dragon's Arcade

*For someone who has never heard of any of this. If you want the developer material
instead, that is `docs/guide/` and `docs/ONBOARDING.md`; this file is for players.*

---

## What this is

Three games you can play in a browser tab. Nothing to install, no account, no wallet.

One thing is different about them, and it is the reason they exist. **When you take a
turn, the game re-runs your move against the rules before it writes anything down.** If
the move isn't allowed, it is refused and nothing happens — you cannot talk the page into
letting you through. And **when a game is over, anyone can replay it** from the first move
to the last and watch it come out the same way. That is why the daily leaderboard can't be
faked: a submitted run that doesn't replay correctly is shown as **FAIL** and never ranks.

That's the whole pitch. It happens in the game server and in your own browser tab — not on
a blockchain, and there is no live public network involved.

### Two honest warnings before you start

- **By default you are identified by a browser cookie.** No password, no email, and **no
  recovery**. Clear your browser data (or open the site in a private window) and you are a
  brand-new person with a blank history. Nothing you did before comes back. If the site
  offers you a recovery phrase, claiming one is what makes an identity survive that — until
  you claim one, nothing here is durable. (An opt-in 24-word phrase at `/identity` was
  in flight as this was written; check whether it is live before telling anyone their
  history is safe.)
- **It is early.** No chat, no friends list, no matchmaking. To play a two-player game you
  open a table and send someone the link yourself. And nothing you collect here is money or
  is for sale.

---

## The Descent

**What it is:** a solo dungeon crawl with one life, played against a torch that never
refills.

**What you're trying to do:** get down to the bottom floor, pick up the prize that lies
there, and climb all the way back out to the surface — before your light runs out. The
score sheet calls a run that carries the prize out **crowned**. That's the whole word;
there is nothing else to it.

**How a turn works.** You press one button, and every button spends light. You have 30
breaths of light for the entire run and there is no way to get more. The buttons are:

- **Descend** — one floor down, one breath.
- **Climb** — one floor up, one breath. This is the only way out, and it is why the light
  you have left is never the real number: you also have to be able to afford the climb
  home. Four floors down means four breaths just to reach the surface.
- **Take the relic** — pick up what's on this floor, one breath.
- **Use a key** — three of the eight relics are keys, and a locked way needs the matching
  key carried in hand. Keys are never hidden behind the door they open, so every way is
  openable if you go get the key first.
- **Press the guardian** — two breaths, no cost to you otherwise.
- **Lunge at the guardian** — the same result for one breath, but it permanently costs you
  one carrying slot for the rest of the run. Cheaper now, worse at the bottom.
- **Bank and end the run** — only possible standing on the surface. Everything you carried
  out is yours; everything still down there is gone, and the run is over. There is no
  second attempt today.

**The squeeze — this is the whole game.** You can hold 8 things, minus how deep you are,
minus any lunge damage. So at floor 1 you have 7 slots and at floor 4 you have 4 — and at
floor 4 you need three keys plus the prize, which is exactly 4. **So you can never carry a
treasure out AND the prize.** Every run is the same choice: go for the prize, or come back
shallow and full. It is also why a lunge is a real decision and not a free discount: the
slot it costs you is one you needed.

**One thing that makes it interesting:** everyone in the world gets the *same* dungeon each
day, and the dungeon is drawn from a public random number that nobody — including us — can
pick in advance. So today's dungeon was not chosen; it was revealed. There are 16 possible
maps, every one of them checked to be beatable, and the best possible line on any given day
spends between 24 and 30 of your 30 breaths. There is almost no slack. Most runs should not
make it.

**Where:** `/descent/play` to play, `/descent` to see today's finished runs.

---

## Automatafl

**What it is:** a two-player board game where the piece that decides it is the one neither
of you controls.

**What you're trying to do:** drive the automaton — the single glowing piece in the middle —
onto one of your own two corners.

**How a turn works.** You do not take turns. **Both players choose a move at the same
time**, in secret. When you have both chosen, both moves open at once, and then one turn
applies both of them.

The board is 11×11 and holds two kinds of ordinary piece plus the automaton:

- **repulsors** (marked `R`) — the pale, spiky ones. They push the automaton away.
- **attractors** (marked `A`) — the round brass discs. They pull it toward them.
- **the automaton** (marked `@`) — the violet ring, the only thing on the board that glows.

Pieces move in straight lines only: along a row or along a column, any distance, never
diagonally, never onto the automaton. (If you play chess: exactly like a rook.) And
**either player may push any piece.** The pieces are not yours or theirs — they're shared.
That is the entire source of the tension.

Once the round resolves, the automaton takes one step, pulled toward attractors and pushed
from repulsors along each axis. Get it to your corner and you've won.

**When you both grab the same square:** that round doesn't happen at all. The contested
square is marked with a dead `×`, the board freezes exactly where it was, and both of you
owe a fresh move that may not use a marked square at either end. The turn counter does not
advance until a round comes back clean. Every re-try burns a new square, so this cannot go
on forever.

**One thing that makes it interesting:** because you are both moving shared pieces
simultaneously, a good move is not "the move that helps me" — it is the move that still
helps me given what they are probably doing to the same board. You are guessing at your
opponent rather than waiting on them.

**Be clear about the secrecy.** While your move is sealed, your opponent isn't shown it —
but the hiding is the *server declining to tell them*. Your move is sitting on the server
in plain form until you open it. It is hidden from your opponent, not from the server. If
you don't want to trust the server with that, don't play here.

**Where:** `/automatafl` — read the rules, then open a table. You get two links: one is
yours, the other is the one you send your opponent. Which side of the board each of you
gets is decided by the game on the first move.

---

## Multiway-Tug

**What it is:** a two-player game of hidden influence over seven guilds. ("Guild" and
"lane" mean the same thing — guild 3 *is* lane 3, and the page uses both words.)

**What you're trying to do:** end the round leading more of the seven guilds than your
opponent, weighted. The seven are worth **2, 2, 2, 3, 3, 4, 5**. Whoever is leading a
guild takes its whole weight — there is no splitting. **The round always plays out in
full**, and *then* it is decided: you win if you hold 11 weight or 4 guilds, and failing
that it still comes out one way — on total weight first, guilds held second — with only an
exact tie on both being a draw. (Nothing ends the round early. Reaching 11 does not stop
play; it only selects which rule names the winner at the end.)

**How a turn works.** You hold six cards, hidden — your opponent sees only *how many* you
hold, never which. Each card belongs to one guild; that is the guild it pulls for whoever
ends up holding it. There are 21 cards in the deck and none is ever created or destroyed
during a round.

You get **four moves for the whole round, one of each kind**, and you choose the order:

- **Play one face down.** It sits face down until the very end.
- **Burn two.** Those two cards leave the round and score for nobody, ever.
- **Lay out three.** Your opponent takes one of the three; you get the other two.
- **Lay out two pairs.** Your opponent takes one pair; you get the other.

On the last two, you decide *what to put in front of them* and they decide *which part they
take*. You can never answer your own offer. That is the game.

Then everything turns face up at once: each face-down card lands on its owner's side of its
guild, and only then is the leading counted.

**⚑ The thing that looks broken and isn't.** Spending a move usually does not move the
seven guild rows at all. A face-down card reaches nobody until the reveal. Burnt cards
reach nobody ever. A three-card or two-pair offer sits in the middle and only lands when
your opponent answers it. So it is completely normal to press a button and see all seven
rows come back identical. What *does* move is the running account of where all 21 cards are
— held, face down, burnt, placed — and the table prints that. If you want feedback that
your move landed, watch that line, not the guild rows.

**One thing that makes it interesting:** on both of the "lay out" moves you are choosing
how *balanced* to make the split. An even cut gives away less but gains you less; a lopsided
cut hands your opponent a real prize if they see it. You're not bluffing about your hand so
much as pricing what you're willing to lose.

**Honest about the size of it:** a round is one round. There is no match, no best-of, and no
alternating first move — and the seat that answers the last offer has a measurable
advantage. Mechanics derived from Hanamikoji (Kota Nakayama); this is an original
re-theming.

**Where:** `/tug` — read the rules, open a table, send the second link to your opponent.

---

## Words this guide deliberately did not use

Kept as a checklist for anyone editing player-facing copy. If you need one of these, define
it on the spot in ordinary words or cut it.

| word | what to say instead |
|---|---|
| executor | "the game", "the rules" — as in *the game re-runs your move* |
| receipt | say what actually happened ("the move landed", "the run was recorded") |
| substrate / fold | nothing. There is no player-facing use for these |
| refereed / no-cheat | "re-checked", "replayed", "checked against the rules" |
| crowned | defined once above: *carried the prize out* |
| fog | "hidden from your opponent" — and say *who* it's hidden from |
| rook line | "straight lines only, along a row or a column" (chess note in parentheses) |
| lane vs guild | equated on first use: *guild 3 is lane 3* |
| ◈ | not needed — nothing shipped uses a currency glyph |
| commitment / root / hash | nothing. If the honest claim needs them, the claim is too technical for this page |
