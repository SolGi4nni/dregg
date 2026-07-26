# UX QA sweep — four first-time readers on eight rendered pages (2026-07-26)

**Method.** One harness run dumps rendered HTML per surface (`demo_playthrough`'s `sample()` →
`/tmp/demo-samples/`). Four cheap agents then read those artifacts **as first-time users**, with no
build and therefore no lock contention — *build once, judge many*. Each was told to get confused
honestly, to quote the page for every claim, and that "this looks clear" is worthless unless it
names what was made clear. Cost: ~410k tokens, ~10 minutes wall, four surfaces.

⚑ **This is not a substitute for the mechanical harness** — it is its complement. A test can assert
"the bytes differ after an act"; only a reader can say "they differ and I still cannot tell what I
did." Conversely a reader cannot re-run on every commit. Build both.

## Platform-wide findings (the generic renderer, so EVERY offering)

1. ⚑ **The editable `arg` box makes every button label non-binding.** Each affordance renders
   `<input class="arg" type="number" name="arg" value="N" aria-label="…value">` beside a button whose
   text already fully names the target (`List Ember Cloak (legendary★ · 3◈)`). Change the box, press
   the button, act on something else. Confirmed in markup. It bites hardest where two rows differ
   only by index — trade ships **two Ember Cloaks** (2◈ and 3◈) with identical name, rarity and
   lineage. Tug's defaults are worse: `0, 7, 28, 63` against seven lanes numbered 0–6 and a 6–7 card
   hand — "arbitrary or leaked internal data" to a reader. FIX SHAPE: render `arg` HIDDEN when the
   affordance label already encodes it; expose the box only where the affordance genuinely wants a
   user-supplied value.
2. ⚑ **"Every control is inert" is FALSE, and provably so.** Both game surfaces tell a seatless
   viewer "every control is inert"; the automatafl board then serves 121 cell buttons carrying NO
   `disabled` attribute. The reader proved it from the before/after pair: pressing an "inert" control
   changed their seat, their hand and the turn counter. Either disable them or stop saying it.
3. **Confirmations name nothing.** The success banner is `Turn committed — Recorded (asserted) ·
   executor receipt 02f5138e…` — a 64-char hex and no item, no price, no action. "The confirmation
   confirms that SOMETHING happened, not WHAT."
4. **Verification vocabulary leaks into player copy** on all four surfaces: `no node, no testnet`,
   `in-process re-execution`, `Poseidon2 commitment`, `committed root`, `asserted actor provenance`,
   `journal-root envelope`. Infrastructure disclaimers on a dungeon page.
5. **`Recorded (asserted)` and `verified` describe the same action on the same page** — one hedges,
   one claims certainty.

## Per-surface

**Catalog / landing.** Could not produce a one-sentence answer to "what is this site" — ⚑ *"the
sentence describing what the site IS is itself written in the site's private vocabulary"*
(`executor`, `substrate`, `refereed`, none defined). Sixteen-term jargon list; the reader's verdict:
"not a nitpick list; it's the majority of the page's distinctive vocabulary." **Every one of the 23
cards ends `<slug> · 0 open`** → *"my honest read as a stranger is 'nobody is using this right now'"*.
Audience never stated (framing says casual gamer, vocabulary says crypto-fluent). Financial verbs
(auction/bid/settle/swap/spend budget) with no word on whether anything is real, reversible, or
visible to others. Verdict: *"closer to 'vaporware ghost town' than 'come play'."*

**Trade.** The subtitle promises `list · settle an atomic asset swap` and **"settle" never exists as
an action** (only list/buy/cancel) — "I don't know if 'buy' IS settling, silently." `◈` never
defined. Nothing says whether you are buying from yourself, another player, or a simulation, while
offering you the button to buy back what you just listed. Title/deck/heading are three near-duplicate
restatements before any content. Before/after **PASSES** — five distinct signals of change.

**Tug.** Before/after **FAILS**: all seven lane rows identical across the move ("nobody has pulled",
"A 0 · B 0"), influence and guilds unchanged. *"I would have concluded the button did nothing."* This
may be CORRECT (a face-down Secret should not move lanes yet) — in which case the page must SAY so; a
scoreboard that does not move is indistinguishable from one that is broken. ⚑ **A promise broken
between two pages of one session**: "the first move you land CLAIMS seat A" → "You hold seat B."
Turn jumps 0/12 → 2/12 for one action. The four actions state a COST but never an EFFECT, and none is
legibly tied to a **lane** — which is what the entire win condition is about. `guild`/`lane` and
`favor`/`card` used interchangeably, never equated. Disabled inputs carry `value="-1"`.

**Automatafl.** The best of the four: it states an objective and a real "do this" instruction. But
**it never says which seat is yours** — both panels read "Seat A — them" / "Seat B — them", so a
reader cannot tell if they are a player or a spectator. Undefined: `rook line` (assumes chess),
`fog`, `CLASH`.

**Descent leaderboard.** ⚠ My brief mislabelled this as the reference *game* surface; the reader
caught it from the nav (`/descent/play` beside `/descent aria-current`) — **"Board" here means
scoreboard.** The play page was never sampled, so the reference surface remains unjudged. On the
leaderboard itself: `Depth: 2` in the header contradicts `depth: 5` in the row below it; `Day: today`
is a literal string where every sibling is a real value; `Warden HP: 45` has no maximum; the main
table has NO heading while the second one does.

## The one pattern worth propagating

From the descent reader, unprompted: ⚑ **"State your empty/exclusion cases explicitly, in prose,
instead of leaving a silent gap."** Its own examples — *"No crowned native browser run has
re-verified for this day"* and *"A forged or unfinished run appears in neither lane — exclusion comes
from re-verification, not a stored flag."* Formulated as: **never let an absence speak for itself.**
That is the product-surface face of [[minted-gating-defaults-to-silence]] — an absent thing emits no
line.

## Next

Cheap and mechanical: the `arg` box; `0 open` hidden at zero; the inert claim; confirmations that
name the action; the depth contradiction; `Day: today`. Needs a decision, not a lane: **who the
product is for**, which is what the jargon layer and the trust questions both bottom out in.
Not yet sampled: `/descent/play`, and every offering the harness will cover that these eight did not.
