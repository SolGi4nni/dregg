# Automatafl — rules-conformance audit of the Lean spec

**Date** 2026-07-20 · **Scope** `metatheory/Dregg2/Games/Automatafl.lean` (the spec) vs the
Creator-Approved ruleset · **Mode** audit only, nothing rewritten.

**Ground truth**, in precedence order:

1. `~/dev/automatafl/logic/README.md` §"Game Rules" — the Creator-Approved ruleset.
2. `~/dev/automatafl/logic/MOVE_EXPLAIN.md`, `logic/PHILOSOPHY.md`,
   `MERGE_RESOLUTION_DESIGN.md` — intent/detail, normative where the README is silent.
3. Implementations as corroboration only: `logic/src/{game,board,automaton,types}.rs`
   (a later generalization, carries its own defects) and
   `old_python_prototype/model.py` (oldest; contradicts the README in several places).

## STATUS — 2026-07-25: the Rust side of this audit is CLOSED by DELETION

The findings below were about two objects: the Lean spec (repaired in
`metatheory/Dregg2/Games/AutomataflRules.lean`, the rules-faithful rewrite) and the Rust oracle
`dregg-automatafl/src/reference.rs`, which was a hand transcription of `logic/src/game.rs` and
therefore carried the same defects. **`reference.rs` is deleted.** `dregg-automatafl` now asks the
Lean for every board transition, legality verdict, conflict set and win, through
`@[export] dregg_automatafl_rules` (`Dregg2.Games.AutomataflFFI` over `AutomataflRules`) — see
`dregg-automatafl/src/rules.rs`. There is no Rust fallback, so none of the divergences below is
reachable from Rust any more; the three that DESTROY MATERIAL are gone from the deployed path.

`tests/differential_reference.rs` — the harness this document calls out for *"comparing a second
copy of the same code against the first"* — is deleted too, along with the `automatafl-logic` git
dev-dependency it drove. Its purpose is served by `tests/lean_oracle.rs`, which pins the ruleset's
answer on the audit's own witnesses (the 2-cycle 3.5a, the inclusive path check 3.2, ruling D on
1.4) — inputs the deleted transcription answered differently, so the tests are evidence about
*which object* answered.

Two of the divergences below therefore now show up as CHANGED BEHAVIOUR in the deployed surface,
deliberately: naming the automaton's square as a move DESTINATION is legal to propose (1.4, ruling
D) and so appears in the rook-line highlight set; and a conflicted round MARKS the contested square
and RE-ENTERS rather than resolving anything (§2.4 below, now CLOSED on the played surface).

### ⚑ 2026-07-25 — §2.4 is CLOSED on the played surface, and this document's own claim about the
### old behaviour was WRONG

The conflict RE-SUBMISSION loop is wired to `AutomataflOffering`: `Phase::Resubmit`, the
`RoundState` (`marks` / `locked` / `waiting`) on the session, and ONE `rules::round` call per round
(`AutomataflRules.roundStep` through `@[export] dregg_automatafl_rules`) that returns the clash set,
the marks, the freeze, the lock set and the waiting set together. So 2.4a (re-entry), 2.4b (the
marker, illegal at either endpoint for everyone, re-checked at the commit gate), 2.4c (illegal FOR
EVERYONE) and 2.4d (recursion) are all live in play. The 2.4 rows below are kept as the HISTORY of
`Automatafl.lean`'s `conflictResolve`, which is what they were written about.

**And the correction.** An earlier revision of this header said the deployed surface "does not
resolve its moves at all" on a clash — i.e. that the drop was at least harmless to the board. That
is FALSE, and it is now pinned by a test
(`dregg-automatafl/src/surface/tests.rs::a_forced_clash_re_enters_the_round_instead_of_dropping_the_moves`).
`rules::turn` / `apply_turn` are the RESOLUTION LEGS — `resolveMoves` is guarded by `resolvableB`,
which is the MERGE clause (`unresolved`) ALONE; the fork/collide clauses live in `roundStep` and
those verbs never consult them. On the stock 11×11 opening, two seats forking the attractor at
`(3,1)` to `(3,3)` and `(5,1)` made seat B's move blocked mid-path (a repulsor stands on `(4,1)`),
which left seat A's as the single unblocked edge out of `(3,1)` — and it **EXECUTED**. So the old
surface did not drop both moves: it silently picked one seat's move, discarded the other, and
advanced the turn. `rules::apply_turn`'s doc comment now carries that warning at the call site.

## 0. The headline

The **automaton half is right**. `evaluateAxis`'s nine-case table, its empty-space guards, its
equidistant-removals and its tie-break order were checked clause-by-clause against README
Priorities 1–4 and conform on every one. The only open question there is which *axis* the column
rule names.

The **resolution half is wrong**, and wrong in a specific, diagnosable way: it was mirrored off
`logic/src/game.rs::apply_moves`, and the differential harness that guards it
(`dregg-automatafl/tests/differential_reference.rs`) compares a *second copy of the same code*
against the first. Every clause of rules step 3 that the two implementations get wrong together,
we get wrong too. **Nine divergences, six of them outcome-changing, three of them destroy pieces.**
The smallest fires with **one move on a 3×3 board**.

Every divergence below marked ⚑ is **machine-checked** against the built spec — probe file
`scratchpad/AuditProbe.lean`, 24 `#guard`s, all passing, with a mutation canary confirming the
harness bites.

---

## A. Divergence table

Severity: **CRIT** = destroys/duplicates material · **HIGH** = changes outcomes ·
**MED** = changes outcomes in a reachable but narrow configuration · **LOW** = stated-clause
mismatch, hard to reach · **AMB** = source material is self-inconsistent, needs the author.

### (1) Move validity — `MoveValid` / `moveValidB`

| # | Rules clause | Our def | Verdict | What ours does |
|---|---|---|---|---|
| 1.1 | source ≠ destination | `MoveValid` conj 1 | **CONFORMS** | — |
| 1.2 | shares an axis (rook move on an empty board) | conj 2, `frm.x = to.x ∨ frm.y = to.y` | **CONFORMS** | — |
| 1.3 | in-bounds | conj 3–4 | **CONFORMS** | — |
| 1.4 | the automaton square | conj 5–6, `¬isAutomaton frm ∧ ¬isAutomaton to` | **DIVERGES (LOW)** | The README never restricts the automaton square at all. `game.rs::propose_move` bans it as *both* endpoints; `model.py::ev_Move` bans it only as a **source** (a move *targeting* the automaton is legal to propose and simply fails at resolution, because `CanMove` finds a non-empty non-passable square). We ban both at proposal. Under the rules-as-written a targeting move is proposable-and-failing, not rejected; the difference is observable because `applyTurn` silently `filter`s invalid moves instead of surfacing them. |
| 1.5 | conflicted-coordinate illegality | conj 7–8, `¬isConflict frm ∧ ¬isConflict to` | **PRESENT BUT DEAD (HIGH)** | `Board.conflictAt` is **never set true anywhere in the metatheory tree** (only `:= fun _ => false` at the default and at `applyMoves:528`). The clause is structurally present and semantically vacuous. See 2.4. |

### (2) Conflicts — `frmConflict` / `toConflict` / `conflictResolve`

| # | Rules clause | Our def | Verdict | What ours does |
|---|---|---|---|---|
| 2.1 | "Multiple players specify the same source" | `frmConflict` (≥2 distinct destinations from one source) | **CONFORMS** | — |
| 2.2 | "Multiple players specify the same destination **with a non-vacuum source**" | `toConflict` | **CONFORMS** | — |
| 2.3 | ⚑ EXCEPTION: "two players specifying an identical (same sources, same targets) move is not a conflict" | both, via `hasTwoDistinct` | **CONFORMS** | Identical moves collapse to one destination (resp. one source), so `hasTwoDistinct` is false. Correct by construction. |
| 2.4a | "all players involved must invalidate their previous move and **prepare another move**" | `conflictResolve` | **ABSENT (HIGH)** | We **drop** the moves and resolve the turn immediately. Under the rules the involved players *resubmit*; they do not forfeit. The number of pieces that move in a turn differs. |
| 2.4b | "It is illegal to specify as a source or destination the *exact* coordinate which was conflicted upon … immovable by all / can no longer be moved to by anyone … temporary marker" | nothing | **ABSENT (HIGH)** | No coordinate is ever marked. `applyMoves` explicitly resets `conflictAt := fun _ => false`. The `Board.conflictAt` field and `MoveValid` clauses 7–8 exist solely as dead scaffolding. |
| 2.4c | ⚑ the conflicted coordinate is illegal **for everyone** | `conflictResolve` | **DIVERGES (HIGH)** | The drop is not even a faithful drop. We drop a move only if *its own* source is fork-conflicted or *its own* destination is collide-conflicted. A move that merely **mentions** a conflicted coordinate at its other endpoint **survives and executes**. Machine-checked twice: (D4a) destination-conflict at `(2,0)` from `(0,0)`/`(4,0)`; a third move `(2,0)→(2,4)` survives — `conflictResolve = [d4C]` — and carries the repulsor off `(2,0)`. (D4b) fork-conflict at `(0,0)`; a third move `(0,4)→(0,0)` targeting the conflicted square survives. `game.rs::resolve_conflicts` puts *every* move touching a conflicted coord into `conflict_moves`. |
| 2.4d | "the conflict resolution will **recurse**" | nothing | **ABSENT (HIGH)** | No recursion; one round only. |

**Is the drop a sound approximation?** No. It is not a conservative under-approximation of the
rules in any direction: it forfeits turns the rules would let players re-take (2.4a), it lets
moves execute that the rules make illegal (2.4c), and because it never marks a coordinate it
cannot express the recursion's fixed point (2.4d). It changes which pieces are on the board at
the end of a turn, so it is not sound even for the automaton step that follows.

> **STATUS (2026-07-25): these four rows are CLOSED on the played surface** — see the dated note in
> the header. `AutomataflRules.roundStep` is the surface's resolution verb, and the marks / locks /
> waiting set it returns are carried on the session rather than recomputed. The rows stay as the
> record of what `Automatafl.lean`'s `conflictResolve` did, and as the falsifier set: a surface that
> resolves a clash instead of re-entering it fails
> `dregg-automatafl/src/surface/tests.rs` §5b.

### (3) Resolution — `occluded` / `nextOf` / `followChain` / `applyMoves`

Rules step 3, quoted in full:

> 2. All pieces specified as the source of a move are temporarily removed from the board,
>    remembering the original position.
> 3. Each piece removed is placed in the specified destination, but *only* if no other piece
>    (which is not in the process of being moved) is on the straight-line path between the source
>    and the destination (otherwise, the piece is replaced at its original position). … Anytime a
>    piece is placed into a source position of some specified move, as long as there is no
>    destination piece already present the piece will obey the move and be placed to the
>    destination (this applies recursively).
>    * As a particular erratum, if a piece is moved into a square which is the source of another
>      move, the piece participates in the move twice. That is, sort the moves topologically, with
>      each move being an edge. Cycles are permissible, including a move from an empty square
>      directly back to some source square--the piece simply doesn't move in this case.
> 4. After all these resolve, any remaining move is simply marked "invalid", and causes no change
>    in state.

| # | Rules clause | Our def | Verdict | What ours does |
|---|---|---|---|---|
| 3.1 | sources temporarily removed, origin remembered | `pieceSrcs` + `clearedSrc` + `Journey.src` | **CONFORMS** | — |
| 3.2 | ⚑ placed **only if** no non-moving piece is on the straight-line path, **else replaced at origin** | `occluded` via `interior` (strictly between) | **DIVERGES — CRIT** | `interior` is **exclusive of the destination**, so a non-moving piece standing *on the destination* does not block. `followChain` then returns that square and `applyMoves` writes the mover's particle over it: **the occupant is deleted from the board**. Machine-checked (D1): 3×3, attractor `(0,0)`, repulsor `(0,2)`, move `(0,0)→(0,2)`; result has **zero repulsors anywhere on the board**. The oldest prototype gets this right — `model.py::Board.CanMove` scans the **inclusive** rectangle `range(min, max+1)` on both coords, exempting sources via `PC_F_PASSABLE`. So does the rules text ("no destination piece already present") and the author's own gloss quoted in our own `followChain` docstring: *"designating a move to an occupied square is fine, it just fails to execute."* **This fires at arity 1.** |
| 3.3 | recursive continuation through vacated squares | `followChain` dead-end/continue branches | **CONFORMS** | — |
| 3.4 | the ERRATUM: participates twice ⇒ topological sort, each move one edge (the caterpillar) | `followChain`'s `pieceSrcs.contains nxt` stop | **CONFORMS** | Matches MOVE_EXPLAIN §4 "Chains". |
| 3.5a | ⚑ 2-cycle, **both** squares carrying | `followChain` | **DIVERGES (MED / AMB)** | Ours **swaps the two pieces**. Machine-checked (D2): attractor↔repulsor exchange positions. PHILOSOPHY.md ("2-cycles … **Always** stay in place"), MERGE_RESOLUTION_DESIGN.md ("Fixed behavior (not configurable)") and `game.rs` (`is_two_cycle ⇒ dest_coord = start_coord`) all say **stay**. The README erratum ("each move being an edge", each firing once) arguably implies swap, and MOVE_EXPLAIN's "all pieces rotate one position along the cycle" does too — **the source material is genuinely inconsistent here**. Two normative docs plus the implementation agree on *stay*. Note also that our own `followChain` docstring **claims** "cycle stasis (2-cycles 'always stay')" — the doc contradicts the code it documents. |
| 3.5b | ⚑ "a move from an empty square directly back to some source square — **the piece simply doesn't move in this case**" | `followChain` | **DIVERGES (MED)** | Ours moves it. Machine-checked (D3): piece at `(0,0)`, moves `(0,0)→(0,2)` and `(0,2)→(0,0)` with `(0,2)` **vacuum**; the attractor ends on `(0,2)`. The README names this exact configuration; `game.rs` (SCC size 2 ⇒ stay) agrees with the README. |
| 3.5c | ⚑ empty cycles cannot pull a piece in (MOVE_EXPLAIN §4 "Special Case (Empty Cycles) … The move is nullified") | `followChain` | **DIVERGES (MED)** | Machine-checked (D6): piece at `(0,0)`, `(0,0)→(0,1)`, plus the all-empty 2-cycle `(0,1)→(0,2)`, `(0,2)→(0,1)`; the attractor is pulled in and lands on `(0,2)`. |
| 3.5d | >2-cycle, all squares carrying | `followChain` | **CONFORMS (incidentally)** | The `pieceSrcs` stop yields exactly "advance one position" = `CycleBehaviorMode::RotatePieces`, the documented default. |
| 3.5e | — | `followChain`'s `visited.contains nxt ⇒ start` | **NOT A RULE** | The only branch that actually produces stasis fires when a chain re-enters a previously visited square, and returns the piece to its *origin*. That is neither rotate nor nullify — a third behavior with no clause behind it. |
| 3.6 | "any remaining move is simply marked invalid, and causes no change in state" | `applyMoves` | **PARTIAL (LOW)** | Blocked moves cause no state change ✓. No `MoveResult` is modelled, so "marked invalid" is unobservable. And the merge loser *does* suffer a state change — see 3.7. |
| 3.7 | ⚑ piece conservation at a vacuum confluence; PHILOSOPHY "Principle of Fairness" | `journeys.find?` in `applyMoves` | **DIVERGES — CRIT** | Two chains converging on one square through vacuum waypoints trigger no conflict (both waypoint sources are vacuum, so `toConflict` filters them out). `journeys.find?` awards the square to whichever journey is **first in move-list order**; the other piece is **deleted**. Machine-checked (D5), 5×5, four moves: `[m1,m2,m3,m4]` leaves an attractor on `(2,0)` and **no repulsor anywhere**; the permutation `[m3,m4,m1,m2]` leaves the repulsor instead. **This refutes `FairnessObligation` (§4) outright — it is FALSE, not merely unproven.** No `MergeResolutionMode` is modelled. Cannot fire at arity 2 (needs ≥2 pieces and ≥2 waypoint moves), so it is a 4-player bug — but the obligation it falsifies is stated unconditionally. |
| 3.8 | overshoot / axis selection in the path | `interior` | **CONFORMS** | Vertical when `frm.x = to.x`, else horizontal; correct on validity-filtered moves. `followChain` returns coordinates and never extrapolates past a destination. |
| 3.9 | "which is not in the process of being moved" — sources are passable even when their own move fails | `srcs = moves.map (·.frm)` | **CONFORMS** | Matches `mark_passable` and `PC_F_PASSABLE`. |

### (4) Automaton step — `raycast` / `evaluateAxis` / `decisionCmp` / `chooseOffset`

| # | Rules clause | Our def | Verdict | Notes |
|---|---|---|---|---|
| 4.0 | "the Automaton can never move into an occupied square" | `automatonStep`'s `cellAt target = .vacuum` guard | **CONFORMS** | Redundant given the per-priority empty-space guards, but harmless. |
| 4.0b | "only ever moves by at most one step in a cardinal direction" | `automatonOffset_bounded` (proven) | **CONFORMS** | — |
| 4.0c | raycast reports the nearest piece per direction, or its absence | `raycastFuel` → `.vacuum` + the OOB step index | **CONFORMS** | Matches `board.rs::raycast`'s documented contract; fuel `size+1` always reaches the wall. |
| 4.1 | **P1** toward attractor + away from repulsor on the same axis, *as long as there is an empty space toward the attractor*, else **the axis is invalidated** | `evaluateAxis` arms `(A,R)`/`(R,A)` with `dist > 1`, else `.none` | **CONFORMS** | `dist > 1` ⟺ ≥1 empty square before the attractor. |
| 4.1b | both axes: prefer closer attractor → then **flee the closer repulsor** → then column rule | `tiebreak` = `revCmp att` then `revCmp rep`; `chooseOffset .eq` | **CONFORMS** | Note the old prototype **contradicts the README** here: `model.py::_DoAgent` encodes `PRI_UNBAL \| ((maxdist-whdist)<<8) \| bldist`, i.e. it prefers the *farther* repulsor. README + `automaton.rs` + ours agree; the prototype is the outlier. |
| 4.2a | **P2** (1) both closest are repulsors ⇒ flee the closer | `(R,R) if pos.dist ≠ neg.dist` | **CONFORMS** | The empty-space guard looks *missing* here but is **implied**: distances are ≥1, so `pos.dist ≠ neg.dist` forces `max ≥ 2`, and flight is toward the farther repulsor. Worth a comment in the rewrite so it is not "fixed" into a bug. |
| 4.2b | "If (1) applies and both repulsor are equidistant, this rule is **removed** from consideration on that axis" | `else .none` | **CONFORMS** | The easy-to-miss case; present. |
| 4.2c | (2) only one repulsor visible ⇒ flee it *if an empty space exists opposite* | `(R,V)`/`(V,R)` with `neg.dist > 1`/`pos.dist > 1` | **CONFORMS** | — |
| 4.2d | "only one repulsor is visible" also holds for `(A,R)`/`(R,A)` when P1 is invalidated | `_ , _ ⇒ .none` | **CONFORMS under either reading (AMB, outcome-neutral)** | The README's "the axis is invalidated" reads as *the axis contributes nothing*; a defensible alternative is *only P1 is invalidated, now consider P2*. Under the alternative, P1 fails only when the attractor is at distance 1, and P2's flight direction is *toward* that adjacent attractor — no empty space — so P2 fails too. **Both readings give `.none`.** No action needed. |
| 4.3a | **P3** (1) both closest are attractors ⇒ toward the closer, *with an empty space* | `(A,A) if pos.dist ≠ neg.dist ∧ min > 1` | **CONFORMS** | — |
| 4.3b | equidistant ⇒ rule **removed** from that axis | `else .none` | **CONFORMS** | — |
| 4.3c | (2) only one attractor visible | `(A,V)`/`(V,A)` with `dist > 1` | **CONFORMS** | Same outcome-neutral ambiguity as 4.2d. |
| 4.4 | **P4** no movement on an axis with nothing; no movement at all if neither axis | `.none` priority 0 → `chooseOffset` `(0,0)` | **CONFORMS** | — |
| 4.5 | ⚑ **the column rule** — "prefers to move along the column instead of the row" | `chooseOffset .eq true ⇒ yDec.delta (0,1)` | **AMBIGUOUS — needs the author (HIGH if wrong)** | We break ties along **Y**, matching `automaton.rs`. But the README explicitly sources the rule to the prototype ("arguably a bug with the initial prototype, but we're going to stick with it"), and **the prototype breaks ties along X**: `model.py::AgentStep` computes `colpri` from `nearest[(1,0)]`/`nearest[(-1,0)]` — the X axis, which that file calls "columns" because `self.columns` is indexed by x — and on `colpri >= rowpri` steps to `colpair = (agent.x + coldir, agent.y)`. If the rule means "keep the prototype's bug", we have it on the wrong axis. Changes the outcome of **every equal-priority tie**. |
| 4.6 | the freeze alternative ("a selectable preference in every game") | `useColumnRule = false ⇒ (0,0)` | **CONFORMS** | — |

### (5) Setup and win condition

| # | Rules clause | Our def | Verdict | What ours does |
|---|---|---|---|---|
| 5.1 | "In a two-player game, each player picks two corners **that are in the same row**" | — | **ABSENT (HIGH)** | `Automatafl.lean` has no `stockTwoPlayer`, no board layout, no corner set and no goal assignment. The 11×11 opening and `GOAL_CORNERS_2P` exist **only in hand-written Rust** (`dregg-automatafl/src/reference.rs`) — the substrate CLAUDE.md names as debt. (That Rust constant *is* rules-correct: P0 = `{(0,0),(10,0)}`, P1 = `{(0,10),(10,10)}`, each pair sharing a row. The old prototype's `DEFAULT_GOALS[2] = [[(0,0),(10,0)], [(10,0),(10,10)]]` is buggy — it repeats `(10,0)` and gives P1 a *column*. Do not transcribe the prototype.) |
| 5.2 | "In a four-player game, each player picks exactly one corner" | — | **ABSENT (MED)** | — |
| 5.3 | "the game is won by whomever owns the corner" | `winner` / `winnerAux` over an arbitrary `goals : List (Coord × Pid)` | **PARTIAL (MED)** | The scan is right; nothing constrains `goals` to be corners, to be two-per-seat-sharing-a-row, or to be distinct. `winner_sound` proves only "the automaton is on a *declared* goal" — it cannot prove "…in a corner", because cornerhood is not in the model. `winnerAux` returns the first match, so overlapping goal entries resolve silently by list order. |
| 5.4 | "When the Automaton **moves into** a corner" | `winner` reads occupancy of the final board | **DIVERGES (LOW)** | We test *sits on*, not *moved into*. The spec's own witness makes this visible: `#guard winner demoBoard [(⟨2,2⟩, 7)] = some 7` (Automatafl.lean:716) reports a win on a board where the automaton has not moved at all. Unreachable from the stock opening (the automaton starts centred), and `game.rs` inherits the same reading — but the clause says *moves into*. |

---

## B. Which divergences are load-bearing for the existing proofs

Dependency map, by leg (line counts are the Lean files as they stand).

### Leg A — the automaton step (~13,785 lines): essentially untouched

`AutomataflStepRefine` (6389), `StepBackend` (1762), `StepCapstone` (1516), `StepChoose` (1233),
`StepStep` (1208), `StepEmit` (1074), `StepCoord` (603). Everything downstream of
`raycast` / `evaluateAxis` / `automatonOffset` / `automatonStep`.

Only divergence 4.5 touches this leg, and it touches exactly one `if` — `chooseOffset`'s `.eq`
branch. If the author says X, the affected proofs are the tie-break case analyses in `StepChoose`
(18 `chooseOffset` + 18 `automatonOffset` sites), `StepEmit` (9), `StepBackend` (12),
`StepCoord` (2), `StepRefine` (29). The nine-case `evaluateAxis` table itself — `StepBackend`'s 48
sites and `StepRefine`'s 70 — **survives untouched either way**, as do `raycastFuel_congr`,
`raycast_congr`, `automatonOffset_congr`, `automatonStep_congr`, `automatonOffset_bounded`,
`automatonStep_preserves_inBounds` and `astep_sat_imp_automatonStep`.

### Leg R — the resolution (~10,262 lines): the statements go with the definitions

`AutomataflResolveRefine` (4382), `ResolveEmit` (1375), `OcclusionBridgeN` (1218),
`ResolveCapstone` (1004), `OcclusionBridge` (957), `OcclusionGeneric` (714),
`ResolveMembership` (612). Every one is downstream of `occluded` / `interior` / `nextOf` /
`followChain` / `applyMoves` / `conflictResolve` — **all six change**.

Invalidated in `Automatafl.lean` itself (statement becomes false, or true-but-about-the-wrong-function):

- `followChain_landing_has_edge` — an invariant of the branch being replaced.
- `chainDest_aN` / `chainDest_bN` — the five-case landing tables. The case split changes (a
  destination-occupancy test is added; the cycle branches change).
- `chainStay_a` / `chainStay_b` / `chainGo_a` / `chainGo_b` — corollaries of the above.
- `applyMoves_cell_TT/TF/FT/FF` — survive in *shape* (they unfold the `filter`/`map`/`find?`
  pipeline), but their `followChain` arguments change and the `find?` tie-break they encode
  ("A's landing wins a shared destination — exactly the gate's `B`-before-`D` priority") is
  divergence 3.7 and must not survive.
- `applyMoves_conserves_pieces` — **gets stronger**. Its hypotheses `hlandA`/`hlandB` ("neither
  target square holds a piece that is not one of the two movers") are *exactly* rules clause 3.2,
  assumed away. Once 3.2 is implemented they become provable side conditions and the hypotheses
  can be dropped. `ConservesPieces`, `conserves_of_single`, `conserves_of_pair` are reusable at
  the statement level.
- `landsOnStayer_witness`, `buggy_refutes_conservation`, `followChainBuggy`, `applyMovesBuggy` —
  retire or re-point. See the note on `reference.rs` below.
- `FairnessObligation` — currently **false** (D5). It becomes provable only after 3.7 is fixed.
- `resolveMid`, `applyTurn`, `applyTurn_factors`, `applyMoves_automaton`,
  `applyTurn_preserves_inBounds` — survive structurally; meaning changes with the definitions.

In `AutomataflResolveCapstone`: `stayer_keeps_cell`, `writeCell_forces_other`,
`occludedStayer_witness_n3` and the §6 "wound" material patch a *sub-case* of clause 3.2. They
survive as special cases but stop being the frontier once 3.2 is done properly.

In `Games/AutomataflAir.lean`: `conflictResolve_pair` is precisely the D3 fork/collide/survive
truth table at arity 2; it survives *iff* conflict semantics stay drop-based, and changes with
2.4c. `airAutomatafl_iff_applyTurn`, `concreteAutomataflAIR_refines`,
`automatafl_air_refines_applyTurn_concrete` are parametric over abstract gadgets with
`MoveSound`/`StepSound` bridges — near-zero proof work to re-point, but their *meaning* moves with
`applyTurn`. (That file already carries its own ⚠ note that these are not connected to the
deployed Rust circuit.)

In `Games/AutomataflBraid.lean`: `TurnBraid`, `runTurn`, `turnBraid_functional` are plumbing over
`resolveMid`/`automatonStep`/`winner`; survive structurally, and gain content once 5.1–5.3 give
`goals` a well-formedness predicate.

Emitted artifacts: `circuit/descriptors/by-name/automatafl-resolve.json` must be regenerated;
`automatafl-step.json` only if 4.5 flips.

### The mechanism of the drift — worth recording

`dregg-automatafl/src/reference.rs::follow_chain` (line 353) is **verbatim the pre-fix chain** —
it is `followChainBuggy`, landing on `nxt` unconditionally. So the Lean spec and the Rust
reference it was ported from are **already two different functions**; defect #8 was fixed in Lean
only. Meanwhile `dregg-automatafl/tests/differential_reference.rs` compares that Rust reference
against the o1 `logic` crate. Reading `logic/src/game.rs::apply_moves` Phase 4 + Phase 6: a chain
ending on a square held by a non-source piece pushes that square onto the path and
`final_placements` overwrites the occupant, which is never cleared — i.e. **o1 has divergence 3.2
too** (read-derived; I did not build and run the o1 crate). The differential suite is therefore a
mirror-vs-mirror agreement between two implementations that share the defect, and **cannot detect
divergences 3.2, 3.5 or 3.7 by construction**. That is how a 10k-line proof tower came to sit on
a 15-line `followChain` that had never been read against the ruleset.

---

## C. Ordered re-implementation plan

### Phase 0 — adjudicate with the author (blocking, cheap, do this first)

1. **Column rule (4.5)**: X (prototype, the stated source of the rule) or Y (`automaton.rs`)?
2. **2-cycles (3.5a)**: stay (PHILOSOPHY + MERGE_RESOLUTION_DESIGN + `game.rs`) or swap (README
   erratum "each move being an edge", MOVE_EXPLAIN "rotate one position")? The source material
   contradicts itself; only the author can settle it.
3. **Merges (3.7)**: which `MergeResolutionMode` is the game we ship? If `DetectAndConflict`, the
   detection is `detect_merging_pathways` — designed in MERGE_RESOLUTION_DESIGN §Phase 1 and
   **never implemented in the reference either**.
4. **Automaton square (1.4)**: illegal to *target* at proposal time, or proposable-and-failing?
5. **Conflict protocol (2.4)**: do we model re-entry, or is "conflicted players forfeit the turn"
   the deployed game? This one is structural — see Phase 1.

### Phase 1 — the type of a turn

If Q5 is "re-entry", then `applyTurn : Board → List Move → Board` is **the wrong type**: a turn is
a multi-round interaction with per-round locked players and a growing conflicted-coordinate set.
The honest shape is a round function
`conflictRound : Board → List Move → Sum (List Move) (List Coord × List Pid)` plus a turn as a
proof-carrying trace of rounds, with `applyTurn` the composite. **This must precede any AIR work**,
because the conflicted-coordinate set becomes part of the mid-state commitment and the circuit's
public inputs change. Getting this wrong is the expensive mistake; getting it late is worse.

### Phase 2 — occlusion (Lean, `Automatafl.lean` §4)

Replace `occluded` with the rules' path predicate, **inclusive of the destination**, sources exempt:

```lean
def pathBlocked (b : Board) (srcs : List Coord) (m : Move) : Bool :=
  ((interior m.frm m.to) ++ [m.to]).any
    (fun c => ¬ (b.cellAt c).isVacuum ∧ ¬ srcs.contains c)
```

A blocked move contributes **no edge**, so the piece is replaced at its origin. `interior` is
unchanged, so `AutomataflOcclusionGeneric`'s enumeration lemmas are reusable; `OcclusionBridge{,N}`
need one extra endpoint term in the arithmetic scan. Falsifier to keep green: probe **D1**.

### Phase 3 — the move graph and cycles (Lean)

Replace `followChain` with an SCC-shaped resolution: compute the non-blocked edge relation;
classify each carrying source's forward orbit as dead-end / caterpillar-stop / cycle; apply the
cycle rule per Q2 — 2-cycle → identity, >2-cycle all-carrying → advance one, **any cycle
containing no carrying source → nullify every move that would enter it** (piece replaced at
origin). Falsifiers: **D2, D3, D6**.

### Phase 4 — merges and fairness (Lean)

Replace `journeys.find?` with an explicit merge resolution per Q3, and **prove**
`FairnessObligation` (permutation-invariance) rather than stating it. Under `DetectAndConflict`
the merge is caught in `conflictResolve` and fairness becomes provable because no two journeys can
then share a destination. Falsifier: **D5**. A `def FairnessObligation : Prop` that is currently
*false* is decoration; it must become a theorem or be deleted.

### Phase 5 — conflicts (Lean)

`conflictResolve` returns the **conflicted coordinate set**, not a filtered list. The closure rule
is "drop every move mentioning a conflicted coordinate as *either* endpoint". Write the set into
`Board.conflictAt` so `MoveValid` clauses 7–8 stop being dead. `applyMoves` must **not** reset
`conflictAt` — step 1 of resolution clears the marks, which happens once resolution is genuinely
reached. Falsifiers: **D4a, D4b**.

### Phase 6 — setup and win (Lean)

Add `stockTwoPlayer : Board` (the 11×11 layout, transcribed from `board.rs::stock_two_player`
with the row/column convention pinned by a `#guard` on a known raycast), `cornersOf : Nat → List
Coord`, and a `GoalAssignment` carrying its well-formedness predicate: 2P ⇒ each seat holds
exactly two corners sharing a row; 4P ⇒ exactly one each; corners partitioned. Retype `winner` to
take a well-formed assignment, and state the win as **entry** if Q confirms 5.4. Falsifier: the
current `#guard winner demoBoard [(⟨2,2⟩, 7)] = some 7` (a win with no move) must **flip**.

### Phase 7 — automaton (Lean)

Only if Q1 says X: change `chooseOffset`'s `.eq` branch. Nothing else in Leg A moves. Add a
comment at the `(R,R)` arm recording that its empty-space guard is *implied* (4.2a), so it is not
later "fixed" into a bug.

### Phase 8 — descriptors and Rust

Regenerate `automatafl-resolve.json` (and `automatafl-step.json` iff Q1 flips) through
`EmitByName`. **Delete** `dregg-automatafl/src/reference.rs::follow_chain` and re-point
`tests/differential_reference.rs` at the Lean-emitted reference. Add a rules-conformance suite
that is *not* a differential against o1 — o1 shares the defects, so agreement with it proves
nothing. Per CLAUDE.md the AIR stays Lean-authored; the hand-written Rust AIR in `dregg-automatafl`
is debt and must not be extended to cover the new cases.

### Phase 9 — re-prove Leg R

The ~10k-line rebuild. Everything above is prerequisite to it; doing it in the other order rebuilds
the tower twice.

---

## D. How much of the proof tower survives — honest judgement

**Leg A (~13,785 lines): ~95% survives.** This half was, in effect, audited against the ruleset
already — `evaluateAxis` is a transcription of README Priorities 1–4 and conforms on every clause
including the two equidistant-removals and all four empty-space guards, which are the easiest
things to get wrong. The refinement work over it (`StepRefine`, `StepBackend`, the raycast
congruences, the arithmetization) is real proof about the right function. Total exposure: one `if`.

**Leg R (~10,262 lines): ~15–25% survives, and what survives is scaffolding, not content.**
Reusable: the descriptor plumbing, the one-hot and range extraction lemmas (`srcIndN_of_sat`,
`dstIndN_of_sat`, `moveCoordBounds`, `eqCoordsN_of_sat`, `validMoveN_of_sat`,
`sourceReadN_of_sat`), the board-window machinery, `interior`'s enumeration, and the
`ConservesPieces` statement family. Not reusable: every theorem whose *statement* mentions
`followChain`, `nextOf`, `applyMoves`, `conflictResolve`, or the D3 selection table — which is
`ResolveRefine`'s entire chain layer and all of `ResolveCapstone`.

**`Automatafl.lean` itself:** §1–§3 (state, validity, automaton) and §7/§8b survive. §4
(resolution) is a rewrite. §5 (win) needs the setup it never had. §8c–§8e (per-cell unfolding,
landing tables, conservation) are rewrites — though the conservation theorem should come out
*stronger*, since its two honest hypotheses are exactly the rules clause we were missing.

**The blunt version.** The game author is right. We implemented the automaton faithfully and the
resolution by mirroring `logic/src/game.rs`, then guarded it with a differential test pointed at a
second copy of the same code. Three divergences destroy pieces; one of them fires with a single
move on a 3×3 board. `FairnessObligation` — the one place PHILOSOPHY's design principle is named
in our spec — is not merely unproven, it is false, and a four-line permutation refutes it. The
scale of the tower is not evidence of conformance: ~10k lines of machine-checked refinement sit on
top of a 15-line `followChain` that had never been read against the ruleset. The proof is real;
it is proof about the wrong function.

---

## Appendix — the probe

`scratchpad/AuditProbe.lean`, run with `lake env lean` against the built
`Dregg2.Games.Automatafl`. 24 `#guard`s, all passing; a deliberately-false guard was added and
confirmed to fail, so the harness bites. Probes D1 (destination overwrite), D2 (2-cycle swap),
D3 (empty-square 2-cycle), D4a/D4b (conflicted-coordinate leakage), D5 (merge destruction +
fairness refutation), D6 (empty-cycle capture).
