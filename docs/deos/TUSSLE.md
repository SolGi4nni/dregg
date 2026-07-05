# TUSSLE — a Toribash-style verified joint-combat match

*Teach-what-is. The forcing-function game where the SERVER is pg-dregg and a figure's
JOINTS are set in a 2-party JOINT TURN. Companion: `DEOS-APPS.md` (the deos app model
+ the fog-of-war webgame), `DEOS.md`, `REHYDRATABLE-SURFACES.md`. The heart lives in
`starbridge-apps/tussle/`.*

## What TUSSLE is

Two **figures** fight by posing their **joints**. Each frame both players secretly choose
a pose, lock it in, then a deterministic resolution runs and the figures clash. It is a
small, deterministic, *verifiable* fighting game — a Toribash clone whose every guarantee
is one the deos substrate already enforces. There is no toy combat engine: the game is a
COMPOSITION of the real primitives.

The architecture pun is the design: in Toribash you set a fighter's joints and the engine
steps the bodies; in deos a **figure is a cell**, a **joint state is a `sym` slot**, and a
frame is a **2-party joint turn** that advances both figure cells at once. A figure's joints
are set in a joint turn.

## The mapping (Toribash → deos)

| Toribash                            | deos / dregg                                                   |
|-------------------------------------|----------------------------------------------------------------|
| a fighter                           | a **figure** = a dregg **cell** (`dregg_cell::CellState`)      |
| a joint (knee, elbow, …)            | a **`sym` slot** of the figure cell                            |
| a joint state (Relax/Contract/…)    | a `JointState` enum case — a `Value.sym` interned identity     |
| "you can't see my move yet"         | a **sealed commitment** (`MoveCommit::seal`, fog-of-war)       |
| both players lock in, then it runs  | **commit → reveal → resolve** (`Frame`)                        |
| the frame steps the physics         | a **deterministic resolution** (a pure cell-program function)  |
| the engine moves bodies + scores    | a **2-party joint turn**: the score deltas fold through the    |
|                                     | **verified per-asset executor** (`dregg_intent::verified_settle`) |
| the match server                    | **pg-dregg** (durable verified state) — *staged follow-on*     |
| watching a replay                   | **STARK replay-rehydration** — *staged follow-on*              |
| the controls UI                     | **gated-affordance controls** on the render surface — *staged* |

## The four real primitives TUSSLE composes

A frame is not a simulation tick. It is four substrate mechanisms welded into a turn.

### 1. The sealed commit — fog-of-war you cannot peek through

A move is a joint-state vector (which way each joint pulls). Before the reveal, a player
publishes only `seal(figure, joints, nonce) = BLAKE3("dregg-tussle move-commit v1", …)` —
the **same commit-reveal construction the sealed-auction app uses** (`MoveCommit::seal`
mirrors `Bid::seal`). The commitment HIDES the joints (the nonce blinds even the small
256-element joint space) and BINDS the player to exactly one move and one figure.

This is real fog-of-war: an opponent who sees your seal cannot recover your joints, and a
peeker who waits for your reveal and then changes their own move hashes to a different seal
that is **not among the frame's commitments**, so their reveal is refused. The no-late-switch
guarantee is the auction's `reveal_binds_committed`, here over joint vectors.

> **Tooth — fog-of-war.** `Frame::opponent_move_is_sealed(me)` returns the *only* public datum
> about the opponent's move: its 32-byte seal. The test `opponent_move_is_unreadable_before_reveal`
> brute-forces all 256 joint vectors × a nonce window and confirms NONE reproduces the seal
> without the secret nonce — the move is computationally unreadable. `peek_then_switch_is_refused`
> confirms a changed move is rejected (`TussleError::NotCommitted`).

### 2. The joint-state-is-an-enum gate — the typed `sym` atom

A joint slot's value must be one of the four `JointState` cases — never an arbitrary scalar.
That tooth is the freshly-landed typed atom **`dregg_cell::StateConstraint::SymMemberOf`**, the
Rust image of the Lean `Pred.symMemberOf` (`metatheory/Dregg2/Exec/PredAlgebra.lean`): a field
reads as a `Value.sym` whose identity is one of the enum set. Each figure cell carries a real
`CellProgram::Predicate([SymMemberOf{joint_slot_j, {0,1,2,3}} ; j])` (`Figure::joint_program`),
evaluated by the **same `CellProgram::evaluate` the executor runs every turn**. A pose that
drives a joint out of the enum is refused in-band.

The `sym` lane is the point: a joint state is an interned IDENTITY (a case), not an orderable
integer. `Relax`/`Contract`/`Hold`/`Extend` are symbols, and `SymMemberOf` pins the slot to
exactly that symbol set — the toy-gap fix the typed atoms were added for.

> **Tooth — the enum gate.** `out_of_enum_joint_is_refused_by_the_cell_program` drives a joint
> slot to `sym 7` (not a `JointState`) and confirms the REAL evaluator refuses it, while a legal
> pose is admitted (non-vacuous: the gate is true AND false). `joint_program_is_symmemberof_per_joint`
> pins the program shape to `SymMemberOf` per joint.

### 3. The 2-party joint turn — the verified per-asset executor

The deterministic resolution emits the contact **score deltas** as a balanced **ring of legs**,
and folds them through the verified per-asset executor
**`dregg_intent::verified_settle::settle_ring_verified`** — the Rust mirror of the Lean
`Ring.settleRing`. The two figures' score cells are the ledger accounts; a contact moves `points`
of the score asset from a neutral bank into the scorer. The fold is:

- **atomic** — a rejected leg aborts the whole frame, leaving the ledger untouched (`settleRing_atomic`);
- **conserving** — the bank column falls exactly as the scorer's rises; the total point supply never
  changes (`settleRing_conserves`);
- **really verified** — on every native build the score leg is ALSO cross-checked against the REAL
  Lean executor export `dregg_record_kernel_step` (`@[export]`, the proved `Exec.recKExec`),
  leg-by-leg, failing closed on any divergence. The match binary links `libdregg_lean.a`. An
  advanced frame's score move IS a verified, conserving executor turn — not a Rust shadow.

This is the **joint** in joint turn: one frame advances *both* figure cells (their poses, positions,
and a conserving score transfer between them) as a single atomic unit.

> **Tooth — the verified turn.** `frame_resolves_through_the_verified_executor` plays a frame and
> asserts the verified ledger moved exactly the points bank→scorer AND conserved the total supply;
> `empty_ring_frame_is_a_conserving_noop` confirms a no-contact frame is a conserving no-op fold;
> `full_match_plays_to_a_knockout` confirms point supply is conserved across a whole match.

### 4. Cap ∧ state gating — your joints, your phase

A player may set joints only on THEIR figure (the **cap** tooth) during THEIR commit phase (the
**state** tooth) — the same cap∧state conjunction the deos `GatedAffordance` models. The cap tooth
binds every `MoveCommit` to a `figure` cell id (the seal's preimage includes the figure, so a move
re-targeted at the opponent's figure hashes to a non-committed seal); the state tooth is the
`Commit → Reveal → Resolved` phase gate (a reveal before the commit phase closes is refused).

> **Tooth — cap-gating.** `player_cannot_pose_the_opponents_figure` confirms a player posing the
> opponent's figure is refused; `reveal_before_commit_phase_closes_is_refused` confirms the phase gate.

## The deterministic resolution (the cell-program of a frame)

The resolution (`resolution::resolve_contact`) is a **pure function** of the two figures'
`(id, position, joints)` — no clock, no randomness, no hidden state — so the same revealed moves
always produce the same outcome. From each joint vector it computes a **forward drive**
(`Contract` +1 toward the opponent, `Extend` −1 away, `Relax`/`Hold` 0) and a **brace**
(each `Hold` cancels one unit of the opponent's drive). The figures step toward each other along
a 1-D strip (clamped so they cannot cross); on **contact** within a small gap, each figure's
effective hit is `max(0, drive − opponent.brace)`, and the stronger lands the blow for the margin
in points. A perfectly cancelled clash scores nothing (an empty, still-conserving ring).

Simple and deterministic by design — that is what puts it on the path to a circuit: the same
function the resolver runs is the one a STARK can later witness.

> **Tooth — reproducibility.** `resolution_is_reproducible` and `match_is_reproducible_end_to_end`
> confirm the same moves give byte-identical outcomes across runs; the headless example re-runs its
> scripted bout and asserts the final state matches.

## What this lane built

The crate `starbridge-apps/tussle/` (`starbridge-tussle`), wired into the workspace as a single
members entry, plus this doc:

- **`src/lib.rs`** — the match data model on dregg cells: `JointState` (the `sym` enum),
  `Figure` (a cell whose first `N_JOINTS` slots are joint `sym` slots), `MoveCommit` (the sealed
  joint-vector), the `Frame` state machine (`commit → reveal → resolve` = one joint turn), and the
  `Match` (a sequence of frames played to a target score, advancing only through verified joint turns).
- **`src/resolution.rs`** — the deterministic frame resolution: the pure `resolve_contact` function
  and the balanced score-leg it emits for the verified fold.
- **`src/card.rs`** — the frame surface as a renderer-independent `deos.ui.*` CARD (the
  `deos_view::ViewNode` view-tree, pure `serde_json`): the down-payment on staged follow-on #2
  (the render surface), shipped as DATA the deos world's three renderers consume, not a renderer call.
- **`src/tests.rs`** — 20 tests covering the four teeth (fog-of-war, the enum gate, the verified
  turn, cap-gating) plus reproducibility and a full match to a knockout. `cargo test -p starbridge-tussle`
  is green.
- **`tests/deos_seam.rs`** — the deos-native `commit → reveal → resolve` verbs fired through the
  REAL executor against the full figure `CellProgram`, proving the verified caveats bite in the fire
  path itself (an illegal joint reveal is a real executor refusal, not a `program.evaluate`-only check).
- **`tests/reexpress_deos_app.rs`** + **`manifest.json`** — the deos-app re-expression (the app as a
  first-class deos citizen with its manifest).
- **`examples/tussle_match.rs`** — a runnable headless match
  (`cargo run -p starbridge-tussle --example tussle_match`): a scripted bout printing each frame's
  commit → reveal → resolution + the running score (read from the verified ledger) + the conserved
  supply, ending in a knockout, then a reproducibility check and a teeth spot-check.

Every score move in a played match settles through the verified per-asset executor, cross-checked
against the real Lean export. The heart is done; the body parts that dress it are staged below.

## Staged follow-ons (named, not built here)

This lane is the HEART. Each follow-on welds an existing deos organ onto it.

1. **The pg-dregg match server.** Host the match state on pg-dregg (durable verified state, the
   pg-dregg substrate — `docs/design-frontiers/PG-DREGG-DX.md`): each `Frame::resolve` is a pg-dregg transaction; the score
   ledger is durable; two remote players submit sealed moves through the SDK. The figure cells become
   web-of-cells citizens. *Welds: `pg-dregg/` + `sdk-py`/`sdk-ts`.*

2. **The render surface.** Project the match onto a `starbridge-web-surface` (the same surface the
   fog-of-war board game uses, `game.rs`): per-viewer projection so each player sees their own joints
   but only the opponent's *committed seal* until reveal — fog-of-war as the membrane's projection,
   not a client-side secret. The strip + figures render from the cells' position/joint slots.
   *Welds: `starbridge-web-surface` + `app-framework::rehydration`.*

3. **STARK replay-rehydration.** A match is a chain of verified joint turns; a spectator
   rehydrates the whole bout from the turn receipts and a STARK, replaying frame-by-frame without
   re-trusting the server (the `stark_rehydrate` / `rehydration` path). The deterministic resolution
   is what makes the replay exact. *Welds: `app-framework::stark_rehydrate`.*

4. **Gated-affordance controls.** The joint-setting UI is a set of `GatedAffordance`s
   (`app-framework`): a "set knee = Contract" button fires iff the viewer holds the figure's cap
   (the cap tooth) AND the frame is in the commit phase (the state tooth) — the cap∧state gate this
   lane already enforces in the protocol, surfaced as buttons. *Welds: `app-framework::affordance`
   `GatedAffordance`.*

5. **The in-circuit resolution.** Lift `resolve_contact` into a cell-program circuit so the frame
   resolution itself is proved (not just the score settlement): the deterministic joint-combat
   function becomes an AIR, and a frame is fully in-circuit. The simplicity of the resolution is the
   down-payment on this. *Welds: `circuit/` descriptor IR.*
