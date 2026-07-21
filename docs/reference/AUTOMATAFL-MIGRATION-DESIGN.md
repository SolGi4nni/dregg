# Automatafl circuit-tower migration to the validated spec

**Status:** design (read-and-design only; no tower code changed by this doc).
**Date:** 2026-07-20.
**Substrate:** the AIR / constraint / gadget layer stays **Lean-authored**
(`Dregg2.Circuit.Emit.Automatafl*`). The existing hand-written Rust in
`dregg-automatafl/` is DEBT; it is not extended. Every "descriptor" below is an
`emitVmJson2`-pinned Lean object; every refinement is a machine-checked theorem over
that emitted object.

---

## 0. What validated, and what the tower currently refines

`metatheory/Dregg2/Games/AutomataflRules.lean` is the **correct** game. It is
execution-grounded: `docs/reference/AUTOMATAFL-DIFFERENTIAL-FINDINGS.md` differenced it
cell-for-cell against the author-designated prototype (`~/dev/automatafl/
old_python_prototype/model.py`) over 580 scenarios — 538 agreements, 42 disagreements,
**and in all 42 the Lean spec follows the Creator-Approved README and the prototype has
the bug** (inverted flee, missing room-to-flee guard, over-eager same-destination
conflict, >2-cycle deadlock). No spec change was owed.

The entire circuit tower refines the **OLD** spec
`metatheory/Dregg2/Games/Automatafl.lean`, whose turn is

```
applyTurn b ms = automatonStep (applyMoves b (conflictResolve b (ms.filter (moveValidB b))))
             = automatonStep (resolveMid b ms)
```

The OLD spec is wrong in exactly the ways the audit and the differential caught, and —
this is the load-bearing fact for the migration — **the tower already knows one of the
wrongs is a wound in itself**: `AutomataflResolveCapstone` §6 (`stayer_keeps_cell` /
`writeCell_forces_other` / `occludedStayer_witness_n3`) proves the emitted resolve
descriptor and the OLD reference DISAGREE at board size `n ≥ 3` (a non-vacuum occluded
source stays put and the other carrying piece lands on it). That wound is precisely what
the new spec's inclusive-path check fixes. So the migration is not only a re-point; it is
the fix that unblocks the resolve leg past `n = 2`.

### The two axes the descriptors are parametric in

Read this before anything else — the whole plan turns on it:

* `NN` in `AutomataflResolveEmit` / `AutomataflStepEmit` is the **board size** (`NN = 2`
  today ⇒ a 2×2, 4-cell board). `automataflResolveDescN n` / `automataflStepDescN n`
  generalize the board size; the Leg-A refinement `astep_sat_imp_automatonStepN` is closed
  at arbitrary `n ≤ 99`, and the Leg-R capstone is n-generic **except** for the occluded
  wound.
* The **move count is hardcoded at 2** (`mvBase 0`, `mvBase 1`, every `List.range 2` in
  `writeMid`/`selection`/`flowThrough`). Two moves = the **2-player** per-round move count.
  Four-player (m = 4) is *not* an instance of the current family — it needs the move count
  generalized, which is where the genuinely-new resolution arithmetization lives.

The real playable game is 11×11. So "the 2-player real turn" = `automataflResolveDescN 11`
(board 11, moves 2) + the new conflict/round composition; "the 4-player real turn" = move
count 4 + the general landing walk.

---

## 1. Function-level correspondence: what the migration re-points

| OLD `Automatafl.lean` (DEAD after migration) | NEW `AutomataflRules.lean` | nature of change |
|---|---|---|
| `applyTurn = automatonStep ∘ resolveMid` | `runTurn cfg g rs trace` (a **fold over rounds**) | **type change** — turn is N rounds, not one shot |
| `resolveMid = applyMoves ∘ conflictResolve ∘ filter moveValidB` | `roundStep` clean branch: `resolveMoves board (locked ++ fresh)` | re-point + new mid-state |
| `applyMoves` (Journey/`journeys.find?`) | `resolveMoves` → `writeBoard (movers) (landMap)` via `arrivalAt`/`uniqueOf` | re-point; **arrival uniqueness is now the guard** |
| `followChain` / `nextOf` (occlusion-aware caterpillar) | `stopWalk` / `leaves` / `landOf` / `landMap` / `edgeMap`/`edgeOf` | re-point; **`leaves` adds the non-leaver recursion** |
| `occluded` (uses `interior`, EXCLUSIVE) | `blockedB` (uses `pathCells = interior ++ [dst]`, **INCLUSIVE**) | **one extra endpoint term** |
| `interior frm to` | `pathCells frm to = interior frm to ++ [dst]` | reused + endpoint |
| `frmConflict`/`toConflict`/`hasTwoDistinct` | `forkAt`/`collideAt`/`clashCoords` | re-point (semantics identical; already proven equal in `AutomataflAir.conflictResolve_pair`) |
| `conflictResolve` (drop-both filter) | `roundStep` detect-and-conflict: emits `marks`/`locked`/`waiting` | **new output surface + recursion** |
| — (nothing) | `unresolved` / `landBad` (merge/confluence conflict) | **genuinely new arithmetization** |
| `moveValidB` / `MoveValid` (uses `conflictAt`, bans `to = automaton`) | `moveLegalB` / `MoveLegal` (uses `marks`, allows `to = automaton`) | small gate delta |
| `automatonStep` / `automatonOffset` / `chooseOffset` | `automatonStepCfg` / `automatonOffsetCfg` / `chooseOffsetCfg` | **survives at `.column`** — a rewrite, not a re-emit |
| `winner` (SITS ON a goal) | `winOnEntry` (automaton MOVED into a goal) | small: add "moved" guard + `winnerAux` reused |
| `FairnessObligation` (a `Prop`; **FALSE** — audit D5) | `resolve_perm` (a **THEOREM**) | the spec side is already done |
| `applyMoves_conserves_pieces` (`hlandA`/`hlandB` hyps, arity 2) | `resolve_conserves` (**unconditional**) | the spec side is already done |

Everything on the NEW side already exists and is proven in `AutomataflRules.lean`
(`resolve_conserves`, `resolve_perm`, `winOnEntry_sound/corner`, the full §10 `#guard`
conformance block keyed to the audit's D1–D6). The migration is entirely **circuit-side**:
re-emit / extend descriptors and re-state / re-prove the `_of_sat` refinements against the
new reference functions.

---

## 2. The new RESOLUTION AIR — gate-level deltas

The current resolve descriptor `automataflResolveDesc` (`= automataflResolveDescN 2`) is
291 columns / 366 constraints / 20 PIs, assembled by `NGen.resolveConstraints n`:

```
onePin
:: boardRange           -- assert_member(cell,{0,1,2,3}) on old & mid  (DEFECT #4 fix)
++ autoRead
++ validateMove ×2       -- rook / in-bounds / not-automaton-source
++ validateOcclusion ×2  -- the masked STRICTLY-INTERIOR line scan
++ srcNonVac             -- anz/bnz  = [src ≠ vacuum]
++ pattern               -- eq_ff / eq_tt / eq_ab / eq_ba
++ selection             -- fork / collide / survive
++ carry                 -- carry_i = survive ∧ nz_i ∧ ¬occ_i
++ flowThrough           -- ft_a/ft_b (the m=2 caterpillar) → dest interpolation
++ writeMid              -- per-cell one-hot rewrite mid == resolve_mid(old,·)
++ commitBoards          -- base-4 packed commitment of old & mid + auto coord
```

The migration to refine `resolveMoves` (instead of `applyMoves ∘ conflictResolve`) touches
these families:

### Δ1 — `validateOcclusion`: the INCLUSIVE destination (RE-POINT + ONE TERM) — **confirmed**

The occlusion apparatus is `AutomataflOcclusionGeneric`: `segHead` builds a between-mask
`seg[k] = 1 ⟺ Between af at_ k` (`Between af at_ k := (af<k∧k<at_) ∨ (at_<k∧k<af)`, i.e.
STRICTLY interior), `msumHead` sums `Σ_k seg[k]·(1−osrc[k])·line[k]`, and `occ = [msum ≥ 1]`.
The bridge `occ_eq_occluded_vert/horiz` equates that bit with the reference
`Automatafl.occluded` (which scans `interior frm to`, exclusive).

The new reference is `blockedB`, which scans `pathCells frm to = interior frm to ++ [dst]`.
The delta is **one extra term** in exactly the shape the fold already produces:

* circuit: extend the `msum` fold with `(1 − osrc[at_])·line[at_]` for the destination index
  `at_` — the same `osrc` passable-mask and `line` read the interior terms use, so a *moving
  source* standing on the destination remains passable (matches `blockedB`'s
  `¬(ms.any (m'.frm == c))` exemption). Equivalently, widen `Between` to
  `(af<k∧k≤at_) ∨ (at_≤k∧k<af)` and leave `msumHead` structurally identical.
* reference: `mem_interior_vert/horiz` → `mem_pathCells_vert/horiz` (the same characterization
  with `≤ at_` on the endpoint), and `occluded_vert_iff`/`occluded_horiz_iff` → `blocked_*_iff`.

`segVal_eq`, `msumVal_eq_sum_between`, `msum_ge_one_iff`, and the whole
`OcclusionBridge{,N}` discharge chain are **parametric over the index set** and survive the
widening unchanged. This is the "OcclusionGeneric is reusable with ONE extra endpoint term"
claim — **confirmed**. It is a small, local, re-pointing change, not new arithmetization.

Consequence: the `ResolveCapstone` §6 occluded-stayer wound **closes**. In the wound
witness (A occluded at `(0,0)→(0,2)` through `(0,1)`; B `(1,0)→(0,0)`), under `blockedB` the
piece that would land on the stayer instead **fails to execute** (its forward walk hits a
non-leaving piece, `leaves = false`; see Δ3), so `resolveMoves` leaves both pieces in place —
matching the new spec's `stuckBoard` `#guard` (§10, clause 3.6). `resolve_sat_imp_resolveMoves`
therefore becomes **restatable at arbitrary `n`**, which the OLD `resolve_sat_imp_resolveMid`
could never be.

### Δ2 — `validateMove` / legality (SMALL GATE DELTA)

`moveValidB` → `moveLegalB`. Two clauses change:

* **drop** `¬ b.isAutomaton m.to` — new ruling (D): naming the automaton square as a
  DESTINATION is legal to propose and simply fails to execute (the occupied square blocks
  the inclusive path). Remove the `to`-side automaton gate from `validateMove`.
* **replace** `¬ b.isConflict frm ∧ ¬ b.isConflict to` (which read `conflictAt`, a field never
  set true anywhere in the OLD tree) with `frm ∉ marks ∧ to ∉ marks`. This is a membership
  test against a **committed marks set** (§3). On the opening round `marks = []`, so at the
  single-round level this gate is vacuously satisfied — the change bites only in round ≥ 2.

`Board.conflictAt` / `Board.isConflict` and `useColumnRule` can be dropped from the decoded
`Board` (the new spec never reads them; the tie-break moves to `GameConfig`).

### Δ3 — the LANDING WALK: `carry`/`flowThrough` → `landMap`/`leaves` (RE-POINT + NEW BIT)

Today `carry_i = survive ∧ nz_i ∧ ¬occ_i` and the m=2 caterpillar is `ft_a`/`ft_b` (A flows
through to B's destination iff A's dest is B's *vacuum* source, `¬eq_ba` breaking the
2-cycle). This is a specialization of the new `edgeMap`/`stopWalk`/`leaves`/`landMap` at m=2.

Two changes:

1. **`¬occ` now inclusive** — automatic once Δ1 lands; `carry` reads the widened `occ`.
2. **NEW: the "lands on a non-leaver" bit** (`landBad` clause 2 / the recursion inside
   `leaves`). A carrying piece whose forward walk comes to rest on a square held by a piece
   that does **not itself leave** must fail to execute (`carry_i := 0` there). At m=2 this is
   a single extra AND into `carry`: "my landing square holds a non-mover, OR the other
   piece's landing is itself blocked". `ResolveCapstone` §6 already names this bit precisely
   ("`carry_b` must be forced to 0 whenever B's landing square holds a NON-CARRYING piece …
   ANDed into `carry`"). This is small at m=2.

At **m > 2** (4-player) `landMap = landOf edgeMap carAt (m+1) (m+1)` is a bounded-fuel walk
(`stopWalk` + `leaves`, fuel `ms.length + 1`). The m=2 `ft` gadget cannot express it; a
general in-circuit fixed-fuel walk over the move graph is **genuinely new arithmetization**
(the >2-cycle-rotates / empty-cycle-nullified / 2-cycle-stays cases of `leaves`). Flag: this
is the single largest new-arithmetization item, and it is *only* needed for 4-player.

### Δ4 — `writeMid` → `writeBoard`/`arrivalAt` (RE-POINT; uniqueness becomes the guard)

`write_mid_witnessed` forces `mid[c]` to the one-hot rewrite of `old` at the witnessed
source/landing indices (`writeCellHead`, with the DEFECT #5 shared-endpoint
inclusion-exclusion). The new `writeBoard` reads `arrivalAt M L q = uniqueOf (M.filter (L·==q))`
— *exactly one* mover may arrive on `q`. In the OLD tower a contested landing was silently
awarded by list order; in the NEW spec a contested landing is a **conflict** and resolution
never runs. So the write gate is the same one-hot deposit, but its well-definedness is now
supplied by the resolvable guard (Δ5) rather than assumed. `writeCellHead` survives
structurally; `writeCellN_of_sat` re-points from `applyMoves`-cell to `writeBoard`-cell.

### Δ5 — the DETECT-AND-CONFLICT surface (**GENUINELY NEW**)

This is the new column family and the heart of the migration. The reference is:

```
clash      = clashCoords board all              -- fork/collide (present as pattern/selection)
unresolved = ((movers.filter landBad).map landMap).dedup   -- merge/confluence (NEW)
landBad c  = ¬(|movers.filter (L·==L c)| == 1)  -- per-landing-square UNIQUENESS   (NEW)
             ∨ (carAt (L c) ∧ L(L c) == L c)    -- lands on a non-leaver           (Δ3 bit)
             ∨ ¬inBounds (L c)                  -- off board (unreachable via roundStep)
resolvable = unresolved.isEmpty
```

New emitted columns/gates:

* **per-landing-square uniqueness.** For each mover `c`, a gate asserting
  `Σ_{c'∈movers} [L c' == L c] == 1`. At m=2 this is a 2×2 comparison (cheap). At general m
  it is a landing-collision histogram (one column per mover, one-hot-collision detection) —
  new but shallow.
* **the conflict OUTPUT.** A public `resolvable` bit; when 0, the emitted `marks`/`locked`/
  `waiting` sets (§3), when 1, the `resolveMoves` board write (Δ4) is enabled and the marks
  output is empty. This is a branch selector on a public bit — the same discipline as Leg A's
  `moved` guard.
* **`clashCoords` marks.** fork/collide already have `eq_ff`/`eq_tt`/`selection`. The marks
  set is the union `(clash ∪ unresolved)` mapped to the marked coordinates, packed for the
  next round.

`clashCoords` fork/collide is a **re-point** (the `d3Fork`/`d3Collide` truth table is already
proven equal to the reference in `AutomataflAir.conflictResolve_pair`; the new `forkAt`/
`collideAt` are the same predicates). The `unresolved` / `landBad` uniqueness + non-leaver
surface, and the marks/locked/waiting output, are **new arithmetization**.

### Δ6 — piece conservation by construction

The new spec proves `resolve_conserves` (a bijection on occupied squares) with **no
hypotheses**, discharged by the inclusive path (Δ1) + the resolvable guard (Δ5). This is a
spec theorem, already done. Circuit-side, no new gates are owed for conservation *per se*:
once Δ1/Δ3/Δ4/Δ5 land, `writeCellN_of_sat` reproduces `writeBoard` cell-wise and
`resolve_conserves` transports through the decode. It is worth a `#guard`/theorem that the
emitted write preserves the packed multiset, but that is a consequence, not a new family.

### Survival of the resolve descriptor families

| family | fate |
|---|---|
| `onePin`, `boardRange`, `commitBoards`, `autoRead` | **survive verbatim** (commit machinery is n-generic; marks/locked packs are new *instances*, §3) |
| `srcNonVac`, `pattern`, `selection` | **survive** (fork/collide unchanged; `d3` truth table already proven) |
| `validateMove` | survive minus one clause + marks-membership (Δ2) |
| `validateOcclusion` | survive + one endpoint term (Δ1) |
| `carry`, `flowThrough`, `writeMid` | survive structurally; re-point + non-leaver bit (Δ3/Δ4) |
| — | **NEW:** `landUnique` / `unresolved` / `conflictOutput` / `marksPack` / `lockedPack` (Δ5, §3) |

---

## 3. The RoundState type + public-input layout

### The reference (already in `AutomataflRules.lean` §7)

```
structure RoundState where
  board   : Board          -- TURN-START board, frozen for the whole turn
  marks   : List Coord     -- accumulated conflict markers
  locked  : List Move      -- moves that stand
  waiting : List Pid       -- seats that owe a (re-)submission

roundStep cfg g rs subs : RoundOutcome     -- .again rs' | .resolved board win
runTurn  cfg g rs trace : Option (Board × Option Pid)   -- fold the round trace
```

A turn is a **trace of rounds**. Each round is one STARK instance; rounds chain by a
PUBLIC-INPUT seam exactly as the current R→A mid-board seam does today
(`resolve_step_sat_imp_applyTurn`'s `hseamPack`/`hseamAutoX/Y`), which is already discharged
via `AutomataflCommit.pack_injective_modp` + `seam_of_equal_pis` — **no fold object, no hash
assumption, no chip soundness** on that path.

### The PI layout (per round instance)

Reusing `AutomataflCommit` throughout — every commitment is base-4 positional pack, injective
by `pack_injective_modp` (`4^15 < p`), bound one-felt-per-15-cells directly to a PI:

```
PI[0 .. 16)          door / recursion prefix                       (unchanged)
PI[16 .. 16+fc)      pack(turn-start board)   -- CONSTANT across all rounds of a turn
PI[16+fc .. 16+2fc)  pack(marks_in)           -- marks as an n²-cell 0/1 indicator board
PI[.. )              locked_in                -- committed locked-move vector (see below)
PI[.. )              waiting_in               -- committed waiting-seat bitmask (≤4 bits)
PI[.. )              auto coord (ax, ay)                            (unchanged, autoCoordCommit)
--- outputs ---
PI[.. )              resolvable bit  b∈{0,1}
PI[.. )   if b=0:    pack(marks_out), locked_out, waiting_out       (feeds next round)
          if b=1:    pack(mid board)  -- feeds Leg A                (the current mid seam)
```

**Marks commitment — machinery reuses directly.** `marks : List Coord` is committed as an
`n²`-cell indicator (`markCell c ∈ {0,1} ⊂ {0,1,2,3}`), so `packBoardConstraintsAt n markCol
markFelt piBase` and `pack_injective`/`pack_injective_modp` apply **verbatim** (values are in
alphabet). Membership `c ∈ marks` used by `moveLegalB` (Δ2) is a one-hot read of the marks
board at `c` — the same `oneHotHeadN`/`oneHot_of_sat` primitive Leg R uses for source reads.
Round-to-round `marks_out(k) == marks_in(k+1)` is `seam_of_equal_pis`. **Confirmed
applicable.**

**Locked-move commitment.** `locked : List Move` at the real game is ≤ (#seats) entries, each
a `(who, frm, to)` with `who < 4` and coords `< n`. Commit as a fixed-width felt vector, one
felt per coordinate/seat, bound like `autoCoordCommitConstraints` (direct `.piBinding`, no
sub-15 pack needed since a coordinate `< 11` already fits a felt). The seam is again
`seam_of_equal_pis`. (An alternative — pack `locked` as *two* marks-shaped indicator boards
"has a locked source here / locked dest here" — loses the seat and the pairing, so prefer the
felt vector.) The pairing (which source goes to which dest, which seat) matters because
`roundStep` re-adds `locked` to `all` and re-checks it for conflict; the felt-vector carrier
preserves it. **This is the one commitment shape that is a new instantiation rather than a
literal reuse**, but it rides the same `pack`/`seam` lemmas.

**waiting** is a ≤4-bit seat mask; a handful of boolean columns + a `.piBinding`.

### The leg structure (per round, then the turn fold)

```
Leg S  (round reveal)   : open this round's submissions  -> moves + their commitments
Leg C  (conflict-detect): filter legal (Δ2) -> compute landMap (Δ3) ->
                           clashCoords ∪ unresolved (Δ5)
                           -> if nonempty: emit marks_out/locked_out/waiting_out, resolvable=0
                              else: resolvable=1
[recurse on resolvable=0 via the PI seam marks_out(k)=marks_in(k+1), etc.]
Leg R  (resolve)        : on resolvable=1, writeBoard movers landMap  (Δ4) -> mid
Leg A  (automaton)      : automatonStepCfg cfg mid                    (Leg A, survives)
Leg W  (win-on-entry)   : winOnEntry mid after g                     (small)
```

Leg C and Leg R **share the `landMap` computation** (`resolveMoves` internally gates on
`resolvableB = unresolved.isEmpty`). In the descriptor they are best emitted as one extended
resolve descriptor that computes `landMap` once, derives `resolvable`, and branches the write
vs the conflict-output on the public `resolvable` bit — rather than two descriptors
recomputing the walk. So "Leg C" is a **new output family bolted onto the extended resolve
descriptor**, not a separate circuit.

### The re-typed top-level obligation

`AutomataflAir.airAutomatafl_iff_applyTurn` currently reads

```
airAutomatafl MG SG old moves new ↔ new = applyTurn old moves
```

with `MoveSound MG := MG.resolve b ms = applyMoves b (conflictResolve b (ms.filter moveValidB))`
and `StepSound SG := SG.step b = automatonStep b`. Re-typed:

```
-- one round:
airRound CG RG SG cfg g rs subs outcome ↔ outcome = roundStep cfg g rs subs
-- the turn:
airTurn ... cfg g rs trace res ↔ res = runTurn cfg g rs trace
```

with the gadget-soundness bridges re-pointed:
`ConflictSound CG := CG.detect = (clashCoords, unresolved)`,
`ResolveSound RG := RG.resolve b ms = resolveMoves b ms`,
`StepSound SG := SG.step = automatonStepCfg cfg`. The `MoveSound`/`StepSound` carried-hypothesis
discipline (never axioms; `#assert_axioms` stays clean) is unchanged — the STARK-soundness
remainder is still *carried*, and the new spec's `resolve_perm`/`resolve_conserves` make the
correspondence NON-vacuous in exactly the way the old `airAutomatafl_forged_refused` witnessed.

`AutomataflBraid.TurnBraid` (currently `out.mid = resolveMid ∧ out.final = automatonStep ∧
out.win = winner`) re-types to a **round-trace braid** over `runTurn cfg g rs trace` with
`winOnEntry`. `turnBraid_functional` re-derives from `roundStep`/`runTurn` determinism.
`AutomataflAir.conflictResolve_pair` (the D3 fork/collide truth table = reference) survives as
the m=2 `clashCoords` correspondence with the collide clause's non-vacuum-source condition —
already exactly `forkAt`/`collideAt`.

---

## 4. Survival map (per file)

`~13.8k` lines of Leg A + `~11.4k` lines of resolve/commit/occlusion + `~1.6k` Leg S +
`~0.6k` Air/Braid.

### Leg A — the automaton (SURVIVES ~100%; re-point, no re-emit at `.column`)

The new spec **reuses the automaton verbatim**: `AutomataflRules.§5` rebuilds
`chooseOffsetCfg`/`automatonOffsetCfg`/`automatonStepCfg` on top of `evaluateAxis`/
`decisionCmp`/`Decision.delta`/`stepTo`/`raycast` from `Automatafl.lean` UNCHANGED, and proves
`chooseOffsetCfg x y .column = chooseOffset x y true` and (given `useColumnRule = true`)
`automatonOffsetCfg b .column = automatonOffset b`. The decoded board fixes
`useColumnRule := true` (`AutomataflStepRefine:499`, `AutomataflCommitRefine:170`).

| file | lines | % surviving | change |
|---|---|---|---|
| `AutomataflStepEmit` | 1074 | 100% (`.column`) | none — descriptor unchanged for the default game |
| `AutomataflStepRefine` | 6389 | 100% (`.column`) | `astep_sat_imp_automatonStep` target rewrites `automatonStep` → `automatonStepCfg .column` via `automatonOffsetCfg_column` (a defeq rewrite) |
| `AutomataflStepCoord` | 603 | 100% | none |
| `AutomataflStepBackend` | 1762 | 100% | none |
| `AutomataflStepChoose` | 1233 | 100% (`.column`) | for `.row`/`.freeze` only: re-emit the `.eq` tie branch (`col=true` cascade at line ~197) |
| `AutomataflStepStep` | 1208 | 100% (`.column`) | `astep_sat_imp_automatonStepN` re-point (defeq) |
| `AutomataflStepCapstone` | 1516 | 100% (`.column`) | re-point |

**Leg A quantified need:** for a game shipping the **default `.column`** tie-break — the
deployed default, and `stockTwoPlayer`'s play — Leg A needs **nothing re-emitted**; only the
top-level statements rewrite their target through `automatonOffsetCfg_column`
(`b.useColumnRule = rfl true`), which is a defeq/`rw`, not a proof re-do. A game shipping
`.row` or `.freeze` needs the `.eq`-tie branch of `chooseOffset` re-emitted in `StepChoose`
and `automatafl-step.json` regenerated. **This confirms the prompt's Leg-A hypothesis.**

### Commit / occlusion — SURVIVE (n-generic; one endpoint term)

| file | lines | % surviving | change |
|---|---|---|---|
| `AutomataflCommit` | 470 | 100% | reused for board + **new marks/locked pack instances** |
| `AutomataflCommitRefine` | 677 | 100% | new `_pi_of_sat` instances for marks/locked seams |
| `AutomataflOcclusionGeneric` | 714 | ~90% | widen `Between`/`segVal` to include the endpoint; `occluded_*_iff` → `blocked_*_iff` |
| `AutomataflOcclusionBridge` | 957 | ~90% | discharge the widened hypotheses (same gate shapes) |
| `AutomataflOcclusionBridgeN` | 1218 | ~90% | `occ_iff_occluded_of_sat` → `occ_iff_blocked_of_sat` |

### Resolve leg — PARTIAL; the real work

| file | lines | % surviving | change |
|---|---|---|---|
| `AutomataflResolveEmit` | 1375 | ~70% | Δ1 endpoint term; Δ2 legality; Δ3 non-leaver bit; **Δ5 new conflict/marks/locked families** |
| `AutomataflResolveRefine` | 4382 | ~60% | `resolve_sat_imp_resolveMid` → `resolve_sat_imp_resolveMoves`; extraction lemmas re-point; new `unresolved`/`landBad` extractions |
| `AutomataflResolveCapstone` | 1004 | ~75% (net gain) | §6 wound **closes**; `resolve_sat_imp_resolveMoves` now **stateable at n≥3**; assembly (`resolveFactsN`/`writeCellN`/`nextOf_pairN`/`chainDest`) re-points |
| `AutomataflResolveMembership` | 612 | ~85% | structured membership re-lays for the new families (append spine grows) |

### Leg S / Air / Braid

| file | lines | % surviving | change |
|---|---|---|---|
| `AutomataflRevealEmit` | 206 | ~80% | becomes the round-reveal leg; PI grows marks/locked/waiting |
| `AutomataflRevealJoin` | 221 | ~80% | seam grows the marks/locked carriers |
| `AutomataflRevealRefine` | 469 | ~80% | `LegSSemantics` re-point to per-round submissions |
| `AutomataflCoord` | 730 | 100% | n-generic coordinate/one-hot foundation, reused as-is |
| `AutomataflAir` | 308 | ~60% | re-type `airAutomatafl_iff_applyTurn` → round/turn; bridges re-point; `conflictResolve_pair` → `clash` correspondence |
| `AutomataflBraid` | 282 | ~55% | `TurnBraid` → round-trace braid over `runTurn`; `winner` → `winOnEntry` |

---

## 5. What is genuinely NEW arithmetization vs re-pointing

**Flag, honestly:**

* **NEW (largest):** the general **landing walk** `landMap`/`stopWalk`/`leaves` at move-count
  m > 2 (4-player) — a bounded-fuel in-circuit walk over the move graph with the
  2-cycle-stays / >2-cycle-rotates / empty-cycle-nullified cases. The m=2 caterpillar
  (`ft_a`/`ft_b`) does not generalize. **Only needed for 4-player.**
* **NEW:** the **detect-and-conflict surface** (Δ5): per-landing-square uniqueness
  (`|movers.filter (L·==L c)| == 1`), the `unresolved` merge/confluence detector, the
  `resolvable` public branch bit, and the `marks_out`/`locked_out`/`waiting_out` output
  columns. Needed for BOTH 2- and 4-player (conflicts happen at 2p too).
* **NEW:** the **round composition** — the marks/locked/waiting PI carriers and the
  round-to-round recursion seam. Reuses `pack`/`seam` lemmas but is a new braid structure.
* **NEW (small):** the "lands on a non-leaver" bit (Δ3) ANDed into `carry`.
* **RE-POINT (mechanical):** the inclusive-endpoint occlusion term (Δ1, confirmed one term);
  the legality clause deltas (Δ2); `writeMid` → `writeBoard` (Δ4); Leg A's target
  (`automatonStep` → `automatonStepCfg .column`, a rewrite); `winner` → `winOnEntry`;
  `frmConflict`/`toConflict` → `forkAt`/`collideAt` (predicates identical).
* **ALREADY DONE (spec side):** `resolve_conserves` (unconditional conservation),
  `resolve_perm` (determinism — the theorem the FALSE `FairnessObligation` should have been),
  `winOnEntry_sound`/`winOnEntry_corner`, the entire §10 conformance `#guard` block.

The honest headline: the automaton half of the tower (~14k lines) **survives as a rewrite**;
the resolution half is a **re-point plus two genuinely new families** (conflict-detect,
round composition) plus, *for 4-player only*, a genuinely new **general landing walk**.

---

## 6. Ordered, honestly-costed build plan

Costs are relative effort, not calendar. Each step is Lean-authored; each descriptor change
is `emitVmJson2`-pinned and its `#guard` golden re-pinned; every refinement re-proven against
the byte-pinned object, `#assert_axioms` ⊆ `{propext, Classical.choice, Quot.sound}`.

**Phase 0 — spec is done.** `AutomataflRules.lean` builds green with the full §10 conformance
block. Nothing owed. (Verify `#assert_all_clean` and the D1–D6 `#guard`s in CI.)

**Phase 1 — re-point the SURVIVING legs (cheap, unblocks the type).**
1. **Leg A re-point (`.column`).** Rewrite `astep_sat_imp_automatonStep{,N}` targets from
   `automatonStep` to `automatonStepCfg .column` via `automatonOffsetCfg_column`. No re-emit.
   Cost: **S**. Descriptors regenerated: **none**.
2. **Occlusion → inclusive.** Widen `Between`/`segVal` + one `msum` endpoint term; re-point
   `occluded_*_iff` → `blocked_*_iff` and `OcclusionBridge{,N}`. Cost: **M**. Regenerate
   `automatafl-resolve.json` (occlusion family grows by 1 term × 2 moves).
3. **Legality delta (Δ2).** Drop `to`-automaton gate; wire marks-membership (vacuous at
   round 1). Cost: **S**. Same regen as (2).

**Phase 2 — the resolve leg to `resolveMoves` at m=2, arbitrary n (closes the wound).**
4. **Non-leaver bit (Δ3) + `writeMid` → `writeBoard` (Δ4).** Add the "landing is a non-leaver"
   AND into `carry`; re-point `writeCellN_of_sat` from `applyMoves`-cell to `writeBoard`-cell.
   Cost: **M**.
5. **`resolve_sat_imp_resolveMoves` at arbitrary n.** With Δ1+Δ3+Δ4, restate the capstone
   against `resolveMoves`; the `ResolveCapstone` §6 wound is now closed — **state it at n = 11**
   (board size), move count 2. Cost: **M–L** (this is where the n-generic assembly finally
   pays off). Regenerate `automatafl-resolve.json` at the new families; **instantiate
   `automataflResolveDescN 11`** and byte-pin an 11×11 golden.

**Phase 3 — the conflict/round surface (genuinely new, needed for 2-player).**
6. **Detect-and-conflict family (Δ5).** Emit per-landing-square uniqueness, the `unresolved`
   detector, the `resolvable` public bit, and `clashCoords` marks. Prove
   `unresolved_of_sat`/`resolvable_of_sat` against the reference. Cost: **L**. Extends
   `automatafl-resolve.json` (or a sibling `automatafl-conflict` descriptor sharing `landMap`).
7. **RoundState PI carriers + seam.** Emit `marks`/`locked`/`waiting` commitments (reusing
   `pack`/`autoCoordCommit`); prove the round-to-round seam via `seam_of_equal_pis`. Cost:
   **M**. New PI layout pinned.
8. **Re-type Air + Braid.** `airAutomatafl_iff_applyTurn` → `airRound`/`airTurn` over
   `roundStep`/`runTurn`; `TurnBraid` → round-trace braid with `winOnEntry`; re-derive
   functional/no-spurious-winner. Cost: **M**.
9. **`winner` → `winOnEntry`** in the win leaf (`winBound` → moved-guard). Cost: **S**.

**→ At the end of Phase 3: a proven 2-player 11×11 real turn** (board 11, moves 2, full
conflict recursion, correct automaton, win-on-entry) — refined, cell-wise, to `runTurn cfg g`
with `cfg.tieBreak = .column`, carrying only the same STARK-soundness remainder the current
tower carries (no hash, no chip-soundness on the seam path).

**Phase 4 — 4-player + selectable tie-break (the long tail).**
10. **General landing walk (m > 2).** The bounded-fuel `landMap`/`leaves` in-circuit for move
    count 4 (2-cycle-stays / >2-cycle-rotates / empty-cycle-nullified). **Largest new
    arithmetization.** Cost: **XL**. New descriptor family; regen at m = 4.
11. **`.row`/`.freeze` tie-break.** Re-emit the `chooseOffset` `.eq` branch in `StepChoose`;
    regenerate `automatafl-step.json`. Cost: **M**.

### Descriptors to regenerate

* `circuit/descriptors/by-name/automatafl-resolve.json` — Phases 1(2,3), 2(5), 3(6,7).
  Re-pin `AutomataflResolveEmit`'s `#guard` goldens (traceWidth / piCount / constraints.length /
  wire string) at each change; instantiate an **11×11** golden in Phase 2.
* `circuit/descriptors/by-name/automatafl-step.json` — **only** Phase 4(11) (`.row`/`.freeze`).
  The default `.column` game leaves it untouched.
* `circuit/descriptors/PROVENANCE.json` — update the two SHA-256 hashes
  (`automatafl-resolve.json`: `4274610d…`, `automatafl-step.json`: `5c9c6223…`) on each regen.
* If a sibling `automatafl-conflict.json` is split out (Phase 3 alt), register it in
  `circuit/descriptors/rotation-wide-registry-staged.tsv` (LFS-tracked; `lfs:true` for the
  circuit CI gate) and add its `PROVENANCE.json` entry.

### Honest sizing

* **Automaton (Leg A, ~14k lines): a rewrite.** Survives ~100% at `.column`. This is the
  single biggest reason the migration is tractable — the validated spec was *designed* to
  reuse it verbatim (`AutomataflRules.§5`, the "Leg-A migration bridge").
* **2-player real turn (Phases 1–3): re-point + two new families.** The occlusion inclusive
  endpoint is confirmed one term; the conflict/round surface is genuinely new but shallow at
  m = 2; the round composition rides the existing `pack`/`seam` machinery.
* **4-player (Phase 4): a genuinely new general landing walk.** This is the real cost and
  should not be smuggled into the 2-player estimate.

Nothing here is closed by this doc; every "survives" is a claim to be discharged by building
against the real tree and reading the theorem *statements* (not greens), per the project's
verification discipline.
