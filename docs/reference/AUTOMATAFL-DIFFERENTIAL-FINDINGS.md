# Automatafl executable differential — findings & rulings (2026-07-20)

The first **executable** correspondence check for the automatafl spec: the running
prototype engine (`~/dev/automatafl/old_python_prototype/model.py`, author-designated
"the actual game") vs. the Lean spec (`Dregg2.Games.AutomataflRules`), cell-for-cell over
a generated corpus. This replaces the old `differential_reference.rs`, which compared the
hand-written Rust reference against the `logic` crate — **mirror-vs-mirror**, unable to
detect a shared divergence by construction.

> **2026-07-25.** `differential_reference.rs` is now DELETED, with the
> `dregg-automatafl/src/reference.rs` oracle it differenced and the `automatafl-logic` git
> dev-dependency that drove it: `dregg-automatafl` computes every transition by calling the Lean
> (`@[export] dregg_automatafl_rules`), so a Rust-vs-Rust differential has nothing left to compare.
> The corpus below is the surviving differential, and it is the one that can find something: two
> INDEPENDENT engines, the Lean spec and the author's python prototype.

Harness: `metatheory/Dregg2/Games/AutomataflDifferential.lean` (Lean side, `#eval`; inert —
not in the build glob) + a scratch Python driver of `model.py`.

## Result

**580 scenarios · 538 agreements · 42 disagreements.** Every disagreement is **semantic**
(0 encoding artifacts survive — the harness was validated on trivial/single-move cases
first, and both engines were injected the *same* explicit board to sidestep the
`Coord::ix = (y,x)` vs `DEFAULT_SETUP = [x][y]` transpose). In all 42, the **Lean spec
follows the Creator-Approved README and the prototype deviates.**

Scope differenced: single-round resolution (marks/waiting/verdict + resolved board) and the
automaton step, at 2–11 board sizes, curated (audit witnesses D1–D6, chains, forks,
collides, cycles, identical-move, all four automaton priorities incl. equidistant-removals
and the tie) + fuzzed (26 seeds). **Not** differenced head-to-head: the multi-round
re-entry *recursion* (single rounds only; the Lean recursion is covered by its own
`#guard`s), and the win-check (`winOnEntry`).

## The five divergences and the author's rulings

Lean driven with `tieBreak := .row` (the correct match to `model.py::AgentStep`; the
deployed `.column` default is the transpose of it — same game).

| # | cases | divergence | ruling |
|---|-------|-----------|--------|
| **S1** | 30 | same-**destination** conflict: README needs *"a non-vacuum source"*; `model.py` flags any two moves to one square. Witness: attractor slides while a second move targets the square from a *vacuum* source — Lean resolves, prototype conflicts. | **README (Lean).** Non-vacuum required. Prototype bug. |
| **S2** | 8 | a marked coordinate is illegal *for everyone* (README) vs only the direct participants re-enter (`model.py`). | **Moot at 2 players** (a 2p conflict involves both players; no third-party survivor exists). Defer to 4p; README reading is natural there and fixes the prototype deadlock. |
| **S3** | 1 | a fully-occupied `>2`-cycle **rotates** (README simultaneous lift-then-place) vs **deadlocks** (`model.py` greedy scan needs an empty dest). | **README (Lean).** Rotates. Prototype bug. (2-cycles still stay — separate ruling.) |
| **S4** | 1 | *"flee the nearest threat"* — `model.py` flees the **farther** repulsor, literally inverted. | **README (Lean).** Prototype bug. |
| **S5** | 2 | *"flee if an empty space exists"* — `model.py` has no room-to-flee guard and **freezes against a wall**. | **README (Lean).** Prototype bug. |

## Conclusion

On the differenced scope (resolution + automaton, two-player), **the Lean spec matches
canonical automatafl.** All five prototype divergences are confirmed bugs (S1/S3/S4/S5) or
moot at 2p (S2). No spec change was required — the Lean was already correct. This is the
first execution-grounded confirmation that the spec is the game, superseding every prior
"differentially validated" claim in the campaign (all of which rode the mirror-vs-mirror
suite and were void).

## Prototype bugs (to report upstream to `~/dev/automatafl`)

`model.py` (and by inheritance the `logic` crate the old differential trusted) carries four
real bugs relative to its own Creator-Approved README:
- **inverted flee** (`_DoAgent` ranks larger repulsor distance higher — flees the farther, not nearest);
- **missing room-to-flee guard** (flees into a wall / freezes, no empty-space check; no axis fallback when the chosen axis is out of bounds);
- **over-eager same-destination conflict** (`pending_move[1] in seen_dests` ignores the non-vacuum-source requirement);
- **`>2`-cycle deadlock** (greedy `CompleteMoves` needs an empty destination, so a full ring never fires — README says it rotates).

Plus two prior findings: `DEFAULT_GOALS[2]` is malformed (repeats `(10,0)`, gives seat 1 a
column not a row), and a locked seat whose move becomes newly conflicted has its move
deleted but is never removed from `self.locked` → deadlock (the README overrides:
"all players involved must prepare another move").
