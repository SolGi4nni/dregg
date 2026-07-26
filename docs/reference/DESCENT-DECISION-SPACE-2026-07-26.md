# The Descent has zero strategic branch points — exhaustively verified, and the one-token fix

ember: *"the entire descent game is …. mediocre to the point of needs rewritten??? or what do you think"*

**The instinct is right, and this is the proof rather than an opinion.** A lane re-implemented the mover verb-for-verb
in Python from `dungeon-on-dregg/src/descent.rs` (`delve/ascend/unlock/smite/lunge/loot/flee`), read the 16 day maps
straight out of the Lean-emitted `dungeon-on-dregg/program/dungeon_program.json`, and — because the reachable state
space is only **3,832–15,426 states per day** — **enumerated every reachable state on all 16 days.** Not sampled, not
Dijkstra-shortcut: complete.

The ranked objective is not a guess; `dreggnet-web/src/descent.rs:1628` states it — *"Only a crowned settlement ranks"*
and *"The ranking is still `turns`, not the score."*

| measure, on the ranked objective | result |
|---|---|
| distinct minimum-turn crowned lines | 1 / 9 / 24 / 39 / 216 by day |
| **distinct move MULTISETS** | **1 — on all 16 days** |
| **strict forks** (two optimal continuations differing in *what remains*, not its order) | **0 — on all 16 days** |
| breath slack | 0 · 2 (×7) · 4 (×6) · 6 (×2); mean 3.12 of 30 |
| `lunge` in any optimal crowned line | **never, on any day** |

Day 12's "216 winning lines" are **216 orderings of one fixed bag of moves** — `loot 1` before `loot 2`, `unlock 3`
before `delve`. Not one is a decision.

**Three independent confirmations.**
1. **`minTurns` is a closed form in the map**: `turns = 16 + Σ ghp[f]` over `{homes[1..3]} ∪ {4}`. Predicted exactly on
   all 16 days (range 20–23). ⚑ **No player input enters the ranked number** — everyone who plays correctly ties, and
   the rank is tie-break order.
2. **One hand-written, day-blind, four-line policy is turn-optimal on all 16 days**: on each floor, if a key or the
   crown is minted here, smite `ghp` times and take it; unlock whatever you now hold; delve. Then ascend ×4, flee.
3. **Random legal play crowns 0 / 20,000 times on every day.** So it is not *easy* — it is a **tightrope**, which is a
   different product from a decision.

## ⚑ Two things previously believed that are false

- **"You can never take a treasure AND the crown" is FALSE on 10 of 16 days.** Capacity attenuates with depth, so it
  *opens up on the climb*: crown at depth 4 at exactly `3 keys + depth 4 + crown = 8`, then loot on the way up. Day 12
  banks **6 relics with the crown**; days 2 and 10 also 6. That is arguably the most elegant mechanic in the game and
  it had been missed — I relayed the wrong version to ember and this corrects it.
- ⚑ **`lunge` — the headline "two blows" verb — is provably DEAD.** `harm` at the instant `loot 0` lands is **0 on all
  16 days**, because `3 keys + depth 4 + crown` is *exactly* `CAP 8`. Any lunge anywhere on the descent forfeits the
  crown. **Yet Lunge is offered as an ENABLED button at 8–10 of the ~21 crown-line turns, and 5–10 of those presses
  silently end the run's ranking prospects.** Two comments are load-bearing and wrong *in the direction that hides it*:
  `metatheory/Dregg2/Games/Dungeon.lean:333-334` (*"at depth 1 it costs a slot you were never going to fill"* — it
  costs the prize at depth 1 too, because `harm` ratchets into the same budget the crown needs at the bottom) and
  `dungeon-on-dregg/src/descent.rs:62-63` (*"cheap at depth 1 (7 slots)"* — same error).

## The one rule change — measured, not asserted

Same solver, one rule changed at a time, strict-fork metric, ranked objective, summed over 16 days:

| variant | strict forks | days with >0 | mean score |
|---|---|---|---|
| **BASELINE (shipped)** | **0** | **0** | 10.25 |
| BREATH 30 → 34 (the negative control) | **0** | **0** | 12.12 |
| **`CAP` 8 → 9** | **370** | **16** | 12.94 |
| `CAP` 8 → 10 | 708 | 16 | 15.44 |
| `unlock` consumes the key | 708 | 16 | 11.31 |

⚑ **The negative control is the load-bearing row: more light buys ZERO decisions.** The budget is not the problem — the
*sum* is. Every cost in this game is additive in one scalar, so the optimum is a shortest path, and shortest paths are
unique. **A decision needs two incomparable currencies.**

`CAP: 8 → 9` (`metatheory/Dregg2/Games/Dungeon.lean:99`) creates exactly that for one token: at 9,
`3 keys + depth 4 + crown + 1 harm = 9`, so **one lunge becomes crown-compatible** and the whole descent gains a
breath↔capacity exchange the player must price at every guardian. Mean turn count is unchanged (21.44) — it adds
decisions without loosening the clock. Runner-up if we want the sharper change: **`unlock` consumes the key** — same
708 forks and it *lowers* mean score, i.e. a real give-up-score-for-capacity trade rather than a loosening — but it
needs a new custody code through the schema range teeth, the conservation `SumEquals`, the emitted artifact and
`RunScore`, and it retires `Dungeon.custody_ratchet` in its current shape.

**It is a RULES change, not a rendering one.** `CAP` is a term in the deployed `AffineLe` tooth the executor re-checks
on every committed post-state, so a surface drawing a 9-slot meter would simply be lying — the referee would still
refuse. Propagation: Lean `Dungeon.lean:99` is the authority → re-emit via `dungeon-on-dregg/program/regen.sh` →
`program/dungeon_program.json` carries the new teeth → `descent.rs:150`'s `pub const CAP: u64 = 8` is the mover's
pinned mirror. Theorems that restate: `banked_bank_pays_for_harm`, `costAt_tense`, and `crowned_full_bank_harmless` —
that last one is the *point*, since the crowned line's harm-0 property stops being a law and becomes a **choice**.

## The failure state is a sum, not a decision — and the rules already know

- **96–99.5% of all reachable alive states have already lost the crown.**
- On **7 of 16 days a single wasted 2-breath round trip at turn 2 kills the run** — and **25 more legal turns follow.**
  Max legal turns remaining after death: **28, on every day.**
- ⚑ `Dungeon.doomed_never_banks` **proves** a living state with `BREATH ≤ toll` can never bank, witnessed on all 16
  maps by `doomed_every_day`. **The game has a machine-checked oracle for "this run is over" and does not use it as a
  rule.** (A surface lane did surface it as a `STRANDED` status today — but it remains advisory, not terminal.)

## One incoherence to fix regardless of the above

**On 8 of 16 days the highest displayed `score` belongs to a run the board excludes.** Best uncrowned vs best crowned
mint-depth: day 3 is 13 vs 10, day 7 is 11 vs 8, day 11 is 11 vs 9. `RunScore::banked_depth` is honest about what it
sums and `descent_card.rs:190-193` is explicit that making the score the rank is an open rules decision — but as
shipped, the number the page shows biggest and the gate that admits you to the page point in opposite directions on
half the days.

## Bottom line

**The Descent is a solved puzzle with a daily reseed, and the reseed varies one 4-valued number.** Zero strategic
branch points on all 16 days, exhaustively verified; the optimal line is a unique move multiset; one four-line day-blind
policy plays it perfectly everywhere; and the verb sold as the interesting decision is provably a forfeit the UI offers
as a live button. The tightness is real — 0–6 breath of slack in 30, and random play crowns 0 in 20,000 — but tightness
is not choice, and copy that sells strategy is selling the wrong product.

Solver scripts: `<session scratchpad>/descent_solve.py` (the mover replica) and siblings.
