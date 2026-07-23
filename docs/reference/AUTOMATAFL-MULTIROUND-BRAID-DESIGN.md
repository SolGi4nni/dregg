# AUTOMATAFL — THE MULTI-ROUND CONFLICT BRAID: folding the fork/collide re-entry protocol

**Status:** DESIGN ONLY (2026-07-23). Nothing here is landed. This is the last game-completeness
piece for automatafl: the two-leg fold (`AUTOMATAFL-TWO-LEG-FOLD-DESIGN.md`) attests a **clean**
turn end-to-end (Leg R resolve ∘ Leg A step, seamed and chained). A turn that hits a **fork/collide**
recurses through `roundStep`'s `.again` branch, and that recursion is **not folded**. This document
designs the fold of the re-entry protocol.

**The substrate, said out loud (TRIPWIRE checked at constraint #1):** every constraint object named
here — the Leg C conflict-detect descriptor, the RoundState commitment, the marks/locked/waiting PI
families, the gated braid — is **Lean-authored AIR** (`metatheory/Dregg2/Circuit/Emit/Automatafl*.lean`,
emitted through `metatheory/EmitByName.lean` into `circuit/descriptors/by-name/`). Rust **fills traces
and drives the fold**; it authors zero constraints. `dregg-automatafl/src/{air,moves,builder}.rs` are
**DEBT**, read only as a witness-generation oracle, never extended as an AIR. The moment this design
touches "does the prover accept a re-entry round X", the answer is a Lean descriptor + a real
refinement theorem over the emitted object — never a hand-written Rust `air_accepts`.

---

## 0. THE GAP, STATED EXACTLY

`AutomataflRules.roundStep` (`metatheory/Dregg2/Games/AutomataflRules.lean:617`) is the honest type of
a round:

```lean
def roundStep (cfg : GameConfig) (g : GoalAssignment) (rs : RoundState) (subs : List Move) :
    RoundOutcome :=
  let fresh := subs.filter (fun m => rs.waiting.contains m.who && moveLegalB rs.board rs.marks m)
  let all   := rs.locked ++ fresh
  let clash := clashCoords rs.board all
  let cs    := if clash.isEmpty then unresolved rs.board all else clash
  if cs.isEmpty then                                   -- CLEAN → resolve + step  (the two-leg fold)
    let mid   := resolveMoves rs.board all
    let after := automatonStepCfg cfg mid
    .resolved after (winOnEntry mid after g)
  else                                                 -- CLASH → re-enter  (THIS DOCUMENT)
    .again
      { board   := rs.board                                                          -- UNCHANGED
        marks   := (rs.marks ++ cs).dedup                                            -- GROWS
        locked  := all.filter (fun m => !(cs.contains m.frm || cs.contains m.to))    -- non-conflicted stand
        waiting := ((all.filter (fun m => cs.contains m.frm || cs.contains m.to)).map (·.who)).dedup }
```

The proven whole-turn capstone `AutomataflTurnCapstone.turn_sat_imp_roundStep_pi` covers **only the
CLEAN branch** (`hclean : clashCoords … = []`), and only the FIRST round (`hfresh` is stated at
`marks = []`, `AutomataflTurnCapstone.lean:296`). So today's fold is silent about:

| # | Un-attested | Why |
|---|---|---|
| **B1** | a round that hits a clash actually re-enters correctly | the `.again` transition (marks add / locked drop / waiting re-enter) is in no descriptor |
| **B2** | the accumulated `marks`/`locked` carry from round `k` to round `k+1` | there is no RoundState window; only the board window exists, and it does not carry marks/locked/waiting |
| **B3** | the clean round of a *multi-round* turn resolved under the right `marks`/`locked` | Leg R consumes a bare pair with `marks = []`, `who = 0`; it cannot consume an accumulated RoundState |
| **B4** | a turn's round count is what the game forces (not what the prover chose) | nothing binds the number of rounds to the actual clash sequence |

**All four close with ONE new descriptor (Leg C) + ONE generalized seam (the RoundState window)** —
the exact analogue of how the two-leg doc closed its three gaps with the board window. The braid is:

```
   turn i  =  Leg C(round 1)  →  Leg C(round 2)  →  …  →  Leg C(round N−1)  →  Leg R(round N)  →  Leg A(round N)
              └────────────── each carries the RoundState window; clash rounds only ──────────────┘ └── clean round ──┘
```

with `S_k` (sealed-move reveal, `AUTOMATAFL-TWO-LEG-FOLD-DESIGN.md` §4) supplying the *waiting seats'*
new submissions ahead of each round.

---

## 1. THE LEG C DESCRIPTOR — the conflict-detect round transition

Leg C is `roundStep`'s `.again` branch as a Lean-authored AIR: given a RoundState that is **not clean**
plus the round's move list `all` (= locked-carried ‖ fresh-revealed), it emits the NEW RoundState with
the **board unchanged**, the conflicted coordinate(s) added to `marks`, the non-conflicted moves added
to `locked`, and the conflicted seats added to `waiting`.

### 1.1 What Leg C reuses verbatim from Leg R

The resolve descriptor **already** computes the clash. Leg C's conflict engine is *the same columns*:

* `cFork` / `cCollide` / `cSurv` (`AutomataflResolveEmit.lean:351,1521`): `cSurv` is constrained to be
  exactly `clashCoords rs.board all = []` — proven by `surv_iff_clash_empty_of_sat`
  (`AutomataflResolveMovesCapstone.lean:2487`). So **the clash/clean verdict is already forced
  in-circuit**; Leg C consumes it instead of dropping it.
* the board decode (`old` cell columns + the injective base-4 pack `packBoardConstraintsAt`,
  `AutomataflCommit.lean:377`) and the move-legality gates (`validMoveN`: rook-aligned, in-bounds,
  distinct, non-automaton source).

Leg C is therefore **Leg R with the resolution tail replaced by a state-transition tail** — and on the
fork/collide path it is *cheaper* than Leg R, because it never runs the `landMap`/`movers`/`landBad`
resolution machinery (§9.1 is the caveat: the `unresolved`-merge path is not cheap).

### 1.2 The new columns Leg C adds (n-generic, P = seat count)

```
  marksIn cells        n²         the mark-indicator board at round entry, codes ∈ {0,1}
  marksIn felts        RFC        = feltCount n, its injective base-4 pack (§2)
  per submission w<P:
    who[w]             1          the seat (needs Leg S; see §3, §4.2)
    inMarksFrm[w]      1          marksIn[frm[w]]     (indicator lookup into marksIn cells)
    inMarksTo[w]       1          marksIn[to[w]]
    legal[w]           1          validMove ∧ ¬inMarksFrm ∧ ¬inMarksTo         (the moveLegalB gate)
    inClash[w]         1          frm[w]∈cs ∨ to[w]∈cs       (this move is dropped this round)
  csCell               n²         the clash-delta indicator: 1 exactly on the conflicted coords cs
  marksOut cells       n²         marksOut[c] = marksIn[c] ∨ csCell[c]        (the "marks ++ cs" board)
  marksOut felts       RFC        its injective base-4 pack
  lockedOut[s] s<P     P·5        seat-indexed: [lockedBit ‖ fromX ‖ fromY ‖ toX ‖ toY]  (§2.3)
  waitingOut[s] s<P    P          seat-indexed indicator: 1 iff seat s is a conflicted re-entrant
```

### 1.3 The Leg C gate families (all Lean, degree ≤ existing budget)

1. **marks decode + pack.** `packBoardConstraintsAt n marksInCell marksInFelt`, range-gated to `{0,1}`
   (a `gBin` per cell in place of Leg R's `assert_member {0,1,2,3}`). Injectivity is the SAME theorem
   `packCell_inj` (codes `< 4` ⊇ `{0,1}`). Identical for `marksOut`.
2. **the marks lookup.** `inMarksFrm[w] = marksInCell[ linear(frm[w]) ]` via the standard row×column
   one-hot select the resolve descriptor already uses for board reads; likewise `inMarksTo`.
3. **the legality gate.** `legal[w] = validMove[w] ∧ ¬inMarksFrm[w] ∧ ¬inMarksTo[w]`. This is
   `moveLegalB rs.board rs.marks` — the marks half is the NEW conjunct over the resolve descriptor,
   which gated legality against `marks = []` implicitly.
4. **clash verdict → cs.** `cSurv = 0` (clash) is forced. `csCell[c]` is pinned to the conflicted
   coordinates: for the pair case, `csCell = onehot(sharedSrc)` on a fork (`cFork = 1`), `onehot(sharedDst)`
   on a collide (`cCollide = 1`) — both recoverable from the move columns (`clashCoords_pair_iff`,
   `AutomataflRules.lean:1960`, is the reference this pins to). For P>2, a pairwise OR of fork/collide
   over `{0..P}²` (§9.1).
5. **marksOut = marksIn ∨ cs.** `marksOutCell[c] − marksInCell[c] − csCell[c] + marksInCell[c]·csCell[c] == 0`
   (boolean OR, degree 2), on every cell; then pack.
6. **lockedOut / waitingOut.** `inClash[w] = inMarksAfterCs(frm[w]) ∨ inMarksAfterCs(to[w])` where
   `inMarksAfterCs = marksOut` (a move touching a newly-marked coord is dropped). For each seat `s`:
   `waitingOut[s] = OR over moves owned by s with inClash = 1`; `lockedOut[s]` copies that seat's move
   iff it is present and `inClash = 0`, else the zero entry (`lockedBit = 0`). This is `all.filter
   (¬touching cs)` re-keyed by seat, and its reference is `roundStep`'s two `filter`s verbatim.

### 1.4 The Leg C PI geometry (append-only past the deployed layout)

Leg C shares Leg R's PI 0..35 layout (`AUTO_PI_BASE n = 16 + 2·RFC`, door prefix ‖ pack_in ‖ pack_out
‖ auto) so the existing seam machinery applies unchanged, then **appends** the RoundState-out lanes:

```
  PI[0 .. 16)              door prefix          (free)
  PI[16 .. 16+RFC)         pack(board)          IN  board window      (unchanged, = Leg R's pack_in)
  PI[16+RFC .. 16+2·RFC)   pack(board)          OUT board window      = IN (board frozen: pinned equal, §5.2)
  PI[AUTO_PI_BASE], +1     ax, ay               (unchanged)
  ── appended, 0..35 untouched ──
  PI[38 .. 38+RFC)         pack(marksIn)        IN  marks window
  PI[38+RFC .. 38+2·RFC)   pack(marksOut)       OUT marks window
  PI[38+2·RFC .. +P·5)     lockedIn / lockedOut seat-indexed locked windows       (IN carried, OUT emitted)
  PI[… .. +P)              waitingIn / waitingOut  seat indicators
```

**The Leg C refinement theorem** (the real machine-checked statement over the emitted object):

```lean
theorem legC_sat_imp_roundAgainN (n P : Nat) (g : GoalAssignment)
    (hsat  : Satisfied2 hash (automataflLegCDescN n P) minit mfin maddrs t)
    (hc    : StepCanon t) (hlen : 1 < t.rows.length)
    (hclash : clashCoords (boardDecodeOldN n (envAt t 0)) (allDecodeN n P (envAt t 0)) ≠ []) :
      roundStep ⟨.column⟩ g
        (roundStateDecodeIn  n P (envAt t 0))
        (freshSubsDecodeN    n P (envAt t 0))
      = .again (roundStateDecodeOut n P (envAt t 0))
```

i.e. the descriptor's decoded OUT window IS `roundStep`'s `.again` RoundState — board, marks, locked
and waiting, cell-for-cell and seat-for-seat, on a genuine clash. `#assert_axioms` ⊆ {propext,
Classical.choice, Quot.sound}, no hash, no chip-table soundness (the marks pack is base-4 injective,
`pack_injective_modp`, exactly like the board pack).

---

## 2. THE ROUNDSTATE COMMITMENT + THE SEAM

The board already commits injectively (`pack_injective_modp`) and carries round-to-round through
`left.OUT == right.IN` (the board window, `AUTOMATAFL-TWO-LEG-FOLD-DESIGN.md` §2.3). The braid
generalizes that ONE mechanism from a **board window** to a **RoundState window**.

```
  RoundState window  W  =  [ boardPack(RFC) ‖ marksPack(RFC) ‖ lockedVec(P·5) ‖ waitingInd(P) ‖ auto(2) ]
```

and the **only** cross-leaf rule in the whole braid stays:

```
  ROUNDSTATE CONTINUITY:   left.OUT  ==  right.IN     (per-lane cb.connect over the whole window)
```

### 2.1 marks — a free reuse of the board machinery

marks is an `n²` `{0,1}` indicator board (`docs` note: "an n² 0/1 indicator board"). Because
`packBoardConstraintsAt n cellCol feltCol` is **parametric in the cell column**, a marks board packs
with the identical call — `packBoardConstraintsAt n marksCell marksFelt` — into `feltCount n` felts
(9 at n=11), and its injectivity is the SAME `packCell_inj` (the alphabet `{0,1}` is a subset of
`{0,1,2,3}`). `commitBoardConstraintsAt n marksFelt marksPiBase` publishes them. **This half is clean
and small.** marksIn ‖ marksOut = 2·RFC = 18 lanes at n=11.

### 2.2 The seam across a clash round

```
  Leg C_k:   IN  = board ‖ marksIn_k  ‖ lockedIn_k  ‖ waitingIn_k  ‖ auto
             OUT = board ‖ marksOut_k ‖ lockedOut_k ‖ waitingOut_k ‖ auto     (board, auto UNCHANGED)
  connect:   C_k.OUT == C_{k+1}.IN                     (the clash braid carry — closes B2)
             C_last.OUT.{board,marks,locked} feeds R.IN     (the clean round consumes it — closes B3)
```

Board and auto are pinned equal IN↔OUT inside Leg C (`resolveMoves`/`.again` never move them:
`AutomataflRules` freezes `rs.board` for the whole turn), so the board pack is **invariant across the
entire clash braid** and only changes at the final Leg R (`old → cMidV4`). marks strictly grows; locked
and waiting evolve.

### 2.3 locked / waiting — the part that is bigger than it looks

marks reuses a board; `locked` and `waiting` are **sets**, and a set has no canonical felt vector unless
you impose an order. The design imposes the **seat index** as the canonical order:

* `locked` holds **at most one move per seat** (a seat submits one move; `roundStep`'s `locked` is a
  subset of `all`, one move per participating seat). So commit it as a **seat-indexed table** of `P`
  fixed slots `[lockedBit ‖ fromX ‖ fromY ‖ toX ‖ toY]` — canonical by construction, `P·5` felts.
* `waiting` is a **seat indicator**, `P` bits.

This canonicalization is why locked/waiting cannot ride the board pack: they are not board-shaped. The
`P·5 + P` lanes are the price. For n=11: 2p → 12 lanes, 4p → 24 lanes.

**The 2-player collapse (the first-landing simplification).** On the deployed 2-player board, a clash
is *always* between the only two moves, so **both** seats are conflicted every clash round: `locked`
is **always empty** and `waiting` is **always both seats**. Proof sketch: `all` has ≤ 2 moves; a
nonempty `clashCoords` needs a fork (shared src) or collide (shared dst) between the two, so both touch
`cs`, so `all.filter(¬cs) = []`. Therefore **the first landing needs only the marks carry** — `locked`
and `waiting` are constant and can be dropped from the window entirely. The full seat-indexed
locked/waiting machinery is 3–4-player work.

### 2.4 The Rust side (all additive, mechanism already exists)

The two-leg fold already built the slice-list window primitive: `BoardWindowBinding { in_slices,
out_slices }` (`circuit/src/effect_vm/custom_state_binding.rs`), the board-window leaf adapter, the
board-window binding node, and the `SegmentCombine::WithBoardWindow { lanes }` merge
(`ivc_turn_chain.rs`). The RoundState window is the **same primitive with a wider `lanes`** — the IN/OUT
slice lists just enumerate `[board ‖ marks ‖ locked ‖ waiting ‖ auto]` instead of `[board ‖ auto]`. No
new merge primitive; `Plain` stays byte-identical (the hard requirement from
`ordered_digest_combine_is_not_associative`). The host mirror `board_window_of_chain` gains a
`roundstate_window_of_chain` twin that folds the wider window and **fails closed before proving** on any
mismatch (milliseconds, not hours).

---

## 3. THE MOVES AS INPUT PER ROUND — public / committed / revealed

### 3.1 Only the *waiting* seats submit each round

Round 1: every seat submits. Round k>1: only the conflicted re-entrants (`waiting`) submit; every
non-conflicted seat's move is **carried in `lockedIn`**, not re-revealed. So per round the new-move
surface is exactly the `waiting` set — which the previous round's Leg C emitted as `waitingOut`.

### 3.2 The submissions are committed-and-revealed (Leg S per round)

The moves enter through **Leg S** (`AutomataflRevealEmit.lean`, the sealed-move reveal leg,
`AUTOMATAFL-TWO-LEG-FOLD-DESIGN.md` §4): each round is preceded by a reveal leg proving the openings
match the committed seals, with the **seat pinned** (`who`). This is what supplies Leg C's `who[w]`
columns (§1.2) — without Leg S, `who` is free witness and the `waiting`/`fresh` routing is unattested
(the same completeness hole the two-leg doc flags for moves generally). So:

```
  round i:   Leg S_i  (waiting seats reveal new sealed moves)
             Leg C_i  (if clash)     OR     Leg R_i , Leg A_i  (if clean)
```

The clear-side surface (`dregg-automatafl/src/surface.rs`: select → commit → reveal → resolve, per-seat
fog, monotone commit/reveal counters, `SealedMove::commit`) already models a turn-per-phase executor.
The **per-round re-commit loop** (round k>1 re-opens commit/reveal for the `waiting` seats only) is a
surface extension — the structure is there; the multi-round re-entry wiring is not.

### 3.3 The locked and marked constraints on a submission

* **marked coordinate is illegal as src AND dst, for ALL** — §1.3(3): `legal[w] = validMove ∧
  ¬marksIn[frm] ∧ ¬marksIn[to]`, exactly `moveLegalB rs.board rs.marks m` (`AutomataflRules.lean:114`,
  the `m.frm ∉ marks ∧ m.to ∉ marks` conjuncts). A fresh submission naming any marked square fails the
  gate and cannot enter `all`.
* **a locked seat's move is fixed** — a locked seat does not re-submit; its move rides `lockedIn` and
  Leg C copies it into `all` unchanged. Leg C's `lockedOut = (lockedIn ∪ fresh).filter(¬cs)` can only
  **drop** a locked move (when it is newly conflicted), never mutate it. So a locked move is frozen
  until it either survives to the clean resolve or is knocked into re-entry.

### 3.4 Privacy (unchanged posture)

Moves are trace columns + intra-recursion PIs; marks/locked/waiting are intra-recursion window lanes.
The root exposes only `first.IN` and `last.OUT` — the opening and final **boards**, not the marks
history or the moves. Data-availability privacy, not a cryptographic hiding claim — the same honest
caveat as the rest of the stack.

---

## 4. THE BRAID + THE `runTurn` CONNECTION

### 4.1 The fold shape

A turn folds a **variable** number of rounds, each round being `S` then (`C`) or (`R`,`A`):

```
  fold(turn i) =  S_1 · C_1 · S_2 · C_2 · … · S_{N−1} · C_{N−1} · S_N · R_N · A_N
```

seamed by RoundState continuity: `C_k.OUT == C_{k+1}.IN`, `C_{N−1}.OUT == R_N.IN` (board+marks+locked),
`R_N.OUT == A_N.IN` (the existing mid seam), and across turns `A_N.OUT(board) == (next turn's first
leg).IN(board)` (the existing inter-turn board carry).

### 4.2 Is the round count a prover choice? NO — it is game-forced

The two-leg doc §6.1 rightly rejects a *data-dependent leg count* when the verdict is unconstrained.
Here the verdict **is** constrained: `cSurv` forces clash-vs-clean **per round** (`surv_iff_clash_empty_of_sat`).

* A round with a real clash **cannot** be folded as the clean `R,A` — the clean Leg R requires
  `clashCoords = []`, which its own `cSurv` gate makes UNSAT when the submitted moves clash.
* A round with no clash **cannot** be folded as a spurious extra Leg C — Leg C's refinement is guarded
  by `cSurv = 0` (clash), UNSAT on a no-clash round.
* A clash round changes **nothing** the prover can harvest — the board is frozen, no step happens
  (`roundStep_pair_outcomeBoard` gives `outcomeBoard = bR` on a clash). The turn only completes at the
  clean Leg R.

So the prover cannot inject, skip, or reorder rounds: the marks/locked/waiting carry (§2.2) forces each
round's inputs to be the previous round's outputs, and `cSurv` forces the verdict. The braid length is
**pinned like the turn count** — the match already folds a variable number of turns; a variable number
of rounds-within-a-turn is the same pinned-variable-length structure (the ordered digest and streaming
schedule already handle variable length, and the host mirror computes the exact schedule up front).

> **Alternative, if a fixed shape is wanted:** pad to a fixed `R_max` per match and gate each surplus
> Leg C to identity with a `resolved` bit (the exact analogue of §6.2's gated step). This trades a
> uniform tree for `R_max` legs always. With the variable-length argument above it is **not required**;
> it is the fallback if the host schedule cannot express nested variable length cleanly.

### 4.3 The `runTurn` connection theorem

`runTurn` (`AutomataflRules.lean:636`) folds a trace of per-round submissions:

```lean
def runTurn cfg g rs : List (List Move) → Option (Board × Option Pid)
  | []           => none
  | subs :: rest => match roundStep cfg g rs subs with
                    | .resolved b w => some (b, w)
                    | .again rs'    => runTurn cfg g rs' rest
```

The braid theorem is an induction on the round trace that threads the RoundState window through each
Leg C and closes with the clean-round capstone:

```lean
theorem braid_sat_imp_runTurn (n P : Nat) (g : GoalAssignment) (seats : List Pid)
    -- a chain of satisfying Leg C traces  tC : Fin (N-1) → VmTrace  (each a genuine clash, §1)
    -- seamed:  roundStateDecodeOut (tC k) = roundStateDecodeIn (tC (k+1))     (the fold connects)
    --          roundStateDecodeIn  (tC 0) = openRound (boardDecodeOldN n eR₀) seats
    -- and a final clean (tR, tA) with the two-leg capstone hypotheses
    --   at marks = marksOut(tC last), locked = lockedOut(tC last):
    ( … ) :
    runTurn ⟨.column⟩ g (openRound (boardDecodeOldN n eR₀) seats) subsTrace
      = some ( boardDecodeNewOf tA ,
               winOnEntry (resolveMoves …) (boardDecodeNewOf tA) g )
```

The engine of each inductive step is `legC_sat_imp_roundAgainN` (§1.4, `roundStep = .again rs'` with
`rs'` the decoded OUT window); the base case is `turn_sat_imp_roundStep_pi` **generalized off
`marks = []`** — which is the B3 work: Leg R's `hfresh` must be re-stated at the accumulated `marks`,
and Leg R must consume `lockedIn` (i.e. resolve `all = locked ++ fresh`, not a bare pair).

---

## 5. TERMINATION — the fold's round bound is `n²`

### 5.1 marks strictly grows, and is bounded by the board

Each clash round adds `cs` (nonempty: it is the `.again` branch) to `marks`, and **`cs` is disjoint
from `marks`**:

* `cs ⊆ candidates all = (all.map .frm) ++ (all.map .to)` (the fork/collide coords are move endpoints,
  `clashCoords` filters `candidates`).
* every move in `all` has both endpoints **∉ marks**: `fresh` moves are `moveLegalB … marks`-legal
  (`frm,to ∉ marks`), and `locked` moves were legal when submitted and are dropped the instant a new
  mark touches them (§3.3). So `candidates all ∩ marks = ∅`, hence `cs ∩ marks = ∅`.

Therefore `|marksOut| = |marks| + |cs| ≥ |marks| + 1`, and `marks ⊆` the `n²` board coordinates, so
**a turn has at most `n²` rounds** (121 at n=11). This is the fold's structural bound: the braid
descends on `n² − |marks|`, which strictly decreases each Leg C.

### 5.2 The Lean statement

```lean
theorem legC_marks_strictly_grow (n P : Nat) (hsat : Satisfied2 … (automataflLegCDescN n P) … t)
    (hc) (hlen) (hclash : clashCoords … ≠ []) :
    (roundStateDecodeIn n P (envAt t 0)).marks.length
      < (roundStateDecodeOut n P (envAt t 0)).marks.length
```

plus `marks ⊆ boardCoords n` (`length ≤ n²`), giving the fold a concrete fuel `n² + 1`. For the
fork/collide first landing this is clean (cs is a single endpoint coord, obviously ∉ marks). The
`unresolved`-merge case needs the extra step that a contested **landing** square is also ∉ marks
(landings are reached through `.to`-edges of legal moves) — true, but §9.1's heavier path.

---

## 6. WHAT A LIGHT CLIENT VERIFIES FOR A FULL (MULTI-ROUND) TURN

With the braid landed, an O(1) light-client accept of a K-turn match means, per turn:

1. **each round's verdict was game-forced** — every Leg C satisfied `automataflLegCDescN` under
   `cSurv = 0` (a real clash); the clean round's Leg R satisfied `cSurv = 1` (no clash). The prover
   could not fake the round count (§4.2).
2. **the re-entry was correct** — each Leg C's OUT RoundState IS `roundStep`'s `.again` state
   (`legC_sat_imp_roundAgainN`): marks grew by exactly the conflicted coords, the non-conflicted moves
   locked, the conflicted seats re-entered.
3. **the RoundState braided** — `C_k.OUT == C_{k+1}.IN` held for every `k` (the marks/locked/waiting
   carry), so the rounds are ONE trajectory over a frozen board, no state substitution between rounds.
4. **the clean round resolved under the accumulated state** — Leg R consumed `marksOut(C_last)` and
   `lockedOut(C_last)`, resolved `all = locked ++ fresh`, and Leg A stepped
   (`turn_sat_imp_roundStep_pi` generalized off `marks = []`).
5. **endpoints pinned** — the trajectory started at the pinned genesis board window and ended at the
   pinned final board window; the pack is injective, so the verifier **decodes the final 9-felt window
   into the actual 11×11 board in the clear** and checks the goal-corner win with no circuit.

The light client never sees marks/locked/waiting (intra-recursion) — only the opening and final boards.

**Still un-attested after the braid (state these; do not let them drift):**

* `hfresh`/`hres` reduced but not eliminated — the `MoveValid → moveLegalB` bridge and the sound
  `cResolvable ↔ resolvableB` biconditional (`AUTOMATAFL-TWO-LEG-FOLD-DESIGN.md` §7.3) are still owed;
  the marks conjunct of `moveLegalB` is NEW in Leg C, so that bridge grows.
* the `unresolved`-merge conflict path at P>2 (§9.1).
* seat ↔ player-account identity (Leg S pins seat ∈ {0..P}; nothing binds it to an account).
* the FRI floor (57 calculator bits) and the witness-gen perimeter (the Rust trace generator is
  trusted) — the marks pack is deliberately hash-free, so it adds no new crypto floor, but it inherits
  those two.

---

## 7. THE ORDERED BUILD PLAN

Continues the two-leg doc's phases (which end at 15 = "multi-round turns: marks/locked carrier"). This
document **is** the detailed design of that item; the phases below decompose it. Each is independently
landable and independently meaningful.

| # | phase | substrate | gate that proves it landed |
|---|---|---|---|
| **M0** | **marks commitment** — `packBoardConstraintsAt` on a `{0,1}` marks cell column; `marksPack` felts; `#guard` the felt count = RFC | Lean (`AutomataflCommit`/new `AutomataflMarks`) | `packCell_inj` reused; `marksPack` length = `feltCount n`; a two-marks board packs injectively |
| **M1** | **Leg C descriptor (2-player, fork/collide, marks-only)** — the `.again` transition tail on Leg R's front half; `csCell`, `marksOut = marksIn ∨ cs`, board pinned IN==OUT | Lean (`AutomataflLegCEmit`) | descriptor emits; `#guard` PI count = `38 + 2·RFC`; golden on disk |
| **M2** | **Leg C refinement** — `legC_sat_imp_roundAgainN` at `n=11, P=2` (marks-only; locked=[], waiting=both) | Lean (`AutomataflLegCCapstone`) | the decoded OUT window IS `roundStep`'s `.again` RoundState; `#assert_axioms` clean; a forged marksOut is UNSAT |
| **M3** | **termination lemma** — `legC_marks_strictly_grow` + `marks ⊆ boardCoords` | Lean | fold fuel `n²+1` discharged; strict-growth `#guard` on a 2-round example |
| **M4** | **register + witness-gen Leg C** — `dregg-automatafl-legc-n11` by name; `legc_witness.rs` mirroring `witness.rs` | Rust (NEW) | an honest clash round satisfies the descriptor under `ir2_eval_accepts_i64`; tamper canary red; a no-clash round is REFUSED (`cSurv=0` UNSAT) |
| **M5** | **RoundState window** — widen the slice-list window to `[board ‖ marks ‖ (locked) ‖ (waiting) ‖ auto]`; leaf adapter + binding node + `SegmentCombine{lanes}`; host `roundstate_window_of_chain` mirror | Rust | `Plain` root byte-identical for tug; a marks-mismatched carry fails closed in ms; leaf under-exposing lanes REFUSED |
| **M6** | **Leg R consumes the RoundState** — generalize `turn_sat_imp_roundStep_pi` off `marks = []` and off the bare pair to `all = locked ++ fresh`; the marks conjunct of `moveLegalB` | Lean (B3) | clean-round capstone holds at `marks ≠ []`; the marks legality gate proven |
| **M7** | **the braid fold + `runTurn`** — `braid_sat_imp_runTurn`; the fold folds `S·C…·S·R·A`; host schedule for the pinned-variable inner length | Lean + Rust (`dreggnet-game-board`) | **THE GATE:** an honest 2-round turn (one clash then clean) folds and `verify_history` ACCEPTS; a fold that drops the clash round, or substitutes marks between rounds, is UNSAT |
| **M8** | **per-round reveal loop** — `surface.rs` re-commit/re-reveal for `waiting` seats only; Leg S per round wired ahead of each Leg C | Rust + Lean (S seam) | round-2 reveals only the re-entrants; `who` attested; `waitingOut(C_1)` == `revealed seats(S_2)` in-fold |
| **M9** | **4-player: locked/waiting seat-indexed windows + P²-pairwise clash** — the general Leg C (§9.1) | Lean + Rust | a 4-player turn where one clash locks two seats and re-enters two folds end-to-end |

**One-line summary:** M0–M3 build and prove Leg C (2-player, marks-only); M4–M5 fold it; M6–M7 splice it
into the whole-turn proof and the match; M8 attests the re-submissions; M9 generalizes to 4 players.

---

## 8. HONEST EFFORT ESTIMATE

| block | ~scale | note |
|---|---|---|
| M0 marks commitment | ~150 Lean | genuinely small — verbatim reuse of the board pack |
| M1 Leg C descriptor (2p) | ~600–900 Lean | Leg R's front half is reused; the `.again` tail is new |
| M2 Leg C refinement (2p) | ~1500–2500 Lean | the load-bearing proof; decode + every gate → `roundStep.again` |
| M3 termination | ~250–400 Lean | clean for fork/collide |
| M4 witness-gen | ~500–700 Rust | mirrors `witness.rs`; reuses the per-gate failure reporter |
| M5 RoundState window | ~600–1000 Rust | mechanism exists; wider lanes + host mirror |
| M6 Leg R off `marks=[]` | ~800–1500 Lean | re-opens the two-leg capstone; the marks conjunct + locked list |
| M7 braid fold + runTurn | ~800–1200 Lean + ~400 Rust | the induction + the pinned-variable schedule |
| M8 per-round reveal | ~400 Rust + Leg-S seam | depends on the two-leg doc's Leg S landing first |
| M9 4-player general | ~1500+ Lean + Rust | the P²-pairwise clash + seat-indexed locked/waiting |

**First landing (M0–M7, 2-player, fork/collide, marks-only): realistically 2–3 focused weeks**, with a
**serial spine** (M1 descriptor → M2 refinement → M6 Leg-R generalization → M7 braid) that does not
fan well — each step consumes the previous one's proven statement. M0/M3/M4/M5 are fannable around the
spine. **Full generality (through M9): a multi-week campaign on top of that.**

---

## 9. WHAT IS GENUINELY BIGGER THAN IT LOOKS

### 9.1 General clash detection is the whole resolution machinery

`roundStep` computes `cs = if clash.isEmpty then unresolved rs.board all else clash`. The `unresolved`
branch (`AutomataflRules.lean:303`) is the **merge/confluence** conflict, and computing it requires the
FULL resolution engine — `edgeMap`, `landMap`, `movers`, `landBad`. So a **fully general** Leg C is
nearly as expensive as Leg R; it is not "just a cheaper detector."

**The reprieve for the first landing:** for a **legal 2-move round**, `clashCoords = [] ⟹ resolvableB`
(`resolvableB_pair`, `AutomataflRules.lean:1855`), so the `unresolved` branch adds **nothing** beyond
fork/collide, which `cSurv` already computes. So the 2-player Leg C is genuinely cheap (reuse `cSurv`,
single clash coord). The `unresolved`-merge path only bites at **P > 2** (three-plus moves can converge
without a pairwise fork/collide) — and that is the M9 cost, carried honestly, not smuggled into M1.

### 9.2 `who` couples Leg C to Leg S

Leg C's `waiting`/`fresh` routing needs the seat `who`, which the resolve descriptor **hard-codes to 0**
(`moveDecodeN`, `AutomataflResolveRefine.lean:3785`). So a **standalone** Leg C attests the *marks*
braid but not the *seat routing*; the routing is load-bearing only once **Leg S** (pinned seat) is
welded — and Leg S has its own two REAL blockers (the 1-felt commitment width, the truncated host seal;
`AUTOMATAFL-TWO-LEG-FOLD-DESIGN.md` §4.4). **The 2-player reprieve applies again:** `waiting` is always
"both seats", so who-routing is trivial and M0–M7 can land without Leg S. The dependency is real for
M8/M9.

### 9.3 Leg R off `marks = []` re-opens a proven capstone (M6)

`turn_sat_imp_roundStep_pi` is proven at `marks = []` and at a bare **pair**. A multi-round turn's
clean round has `marks ≠ []` and `all = locked ++ fresh` (a list, not a pair). Generalizing the capstone
off both is not plumbing — it re-enters the resolve-pair proof chain (`resolveMoves_cell_pair`,
`arrivalAt_pair`, the `_sep` lemmas) at list arity. This is the single most under-estimated item; budget
it as its own phase (M6), not a rider on M7.

### 9.4 The variable inner braid length stresses the fold schedule

The match already folds variable-length turn sequences, but a **nested** variable length (turns × rounds)
is new for the ordered-digest host schedule and the streaming scheduler. §4.2's soundness argument
(the verdict is `cSurv`-forced) is solid, but the *engineering* of computing the exact per-turn round
schedule up front and threading it through `aggregate_tree_streaming` is real work — and the §4.2
"padded fixed `R_max`" fallback exists precisely if that nesting proves awkward.

---

## 10. THE SEAM ENFORCEMENT — end to end (the sound core)

```
1.  C_k's trace satisfies automataflLegCDescN         ← in-circuit FRI verify of the leaf, folded
2.  C_k.OUT decodes to roundStep(…).again's RoundState ← legC_sat_imp_roundAgainN (EMITTED, base-4 injective)
3.  C_k.OUT == C_{k+1}.IN                              ← cb.connect over the RoundState window        ★
4.  ⇒ round k+1's inputs ARE round k's re-entry state (marks, locked, waiting all carried)
5.  cSurv forces clash on every C, no-clash on the final R  ← surv_iff_clash_empty_of_sat (EMITTED)
6.  C_last.OUT.{board,marks,locked} == R.IN            ← cb.connect                                    ★
7.  R,A compose to roundStep's resolved outcome        ← turn_sat_imp_roundStep_pi, off marks=[] (M6)
8.  ⇒ braid_sat_imp_runTurn: the whole multi-round turn IS runTurn's outcome board
```

★ = the two things the fold adds (both the existing `cb.connect` primitive, wider window). Everything
else is an emitted-and-proven Lean theorem. NO hash, NO chip-table soundness on the seam — the marks
pack, like the board pack, is base-4 injective (`pack_injective_modp`), so the window equality **is**
RoundState equality, not a collision-resistance assumption.
