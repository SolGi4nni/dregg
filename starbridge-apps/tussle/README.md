# starbridge-tussle

**A Toribash-style verified joint-combat match — two figures fight by posing their joints, and
a figure's joints are set in a 2-party joint turn.** Each figure is a dregg cell; each joint is
a typed `sym` slot; a move runs `commit → reveal → resolve`, and the contact score folds
through the verified per-asset executor as a conserving ring.

There is **no toy combat engine**: every guarantee is one the substrate already enforces. The
app COMPOSES four real primitives into a small, deterministic, verifiable fighting game.

## The four teeth (each a real refusal, not app bookkeeping)

| Tooth | What it guarantees | How this app enforces it | Where |
|---|---|---|---|
| **enum joint** | a joint slot's value is one of the `JointState` cases (`Relax/Contract/Hold/Extend`), never an arbitrary scalar | `StateConstraint::SymMemberOf` per joint slot, run by the REAL `CellProgram::evaluate` — the exact gate the executor runs every turn | `Figure::joint_program`, `src/lib.rs:241` |
| **phase (state)** | the frame advances `COMMIT → REVEAL → RESOLVED`, never rewinds | `StateConstraint::Monotonic(PHASE_SLOT)` conjoined onto the figure program | `figure_deos_program`, `src/lib.rs:925` |
| **fog-of-war (commit)** | the opponent's move is unreadable before reveal, and a player is bound to exactly one move | a sealed `BLAKE3(figure ‖ joints ‖ nonce)` commitment; a peek-then-switch hashes to a seal that is not among the commitments → reveal refused | `MoveCommit::seal` / `Frame::reveal`, `src/lib.rs:364` / `:547` |
| **cap (wrong-figure)** | a player may set joints only on THEIR figure | a reveal whose commit was authored under another figure is `TussleError::WrongFigure` | `Frame::reveal`, `src/lib.rs:547` |

The enum tooth is the load-bearing one and the reason this app exists: it is the executable
witness of the freshly-landed typed `sym` atom `StateConstraint::SymMemberOf` — the Rust image
of the Lean `Pred.symMemberOf` (`metatheory/Dregg2/Exec/PredAlgebra.lean`). `Figure::pose_checked`
builds the candidate `(old, new)` transition and runs `joint_program().evaluate(...)` over it;
an out-of-enum drive is refused in-band with `TussleError::IllegalJoint` (`src/lib.rs:284`).

## The 2-party joint turn (conserving score)

The deterministic frame resolution (`src/resolution.rs`, `resolve_contact`) is a pure function
of the two revealed joint vectors and positions — no clock, no randomness (the reproducibility
tooth). On a decisive clash it emits a single **balanced score leg**: `points` of `SCORE_ASSET`
move from the neutral `SCORE_BANK` into the scoring figure's column — a conserving transfer, not
a mint. `Frame::resolve` folds the ring through `dregg_intent::verified_settle::settle_ring_verified`
(the Rust mirror of the Lean `Ring.settleRing`). When a host has installed the Lean intent gate
(a native node does at startup), each leg is ALSO cross-checked leg-by-leg against the real Lean
executor export; in this crate's own process (tests included) the fold is the in-process Rust
mirror — no FFI cross-check runs.

## The deos surface (four verbs, cap∧state gated)

The match is composed as a **two-figure `DeosApp`** (`tussle_app`, `src/lib.rs:982`). Each figure
cell carries the four verbs, each bound to that specific cell (the cap tooth) and, where gated,
carrying its live-state phase precondition (the htmx tooth — the button lights only in its phase):

| verb | method const | tier | gate |
|---|---|---|---|
| `view_figure` | `METHOD_VIEW` | `SPECTATOR_RIGHTS` = `Signature` | cap-only read |
| `commit_move` | `METHOD_COMMIT` | `FIGHTER_RIGHTS` = `Either` | `PHASE == COMMIT` |
| `reveal_move` | `METHOD_REVEAL` | `FIGHTER_RIGHTS` = `Either` | `PHASE == REVEAL` |
| `resolve_frame` | `METHOD_RESOLVE` | `REFEREE_RIGHTS` = `None`/root | `PHASE == REVEAL` |

`seed_figure` installs `figure_deos_program` and the genesis state (`Relax` pose, `PHASE = COMMIT`);
`fire_commit_move` / `fire_reveal_move` / `fire_resolve_frame` submit the full gated turns, and
the executor re-enforces `SymMemberOf` + `Monotonic(PHASE)` on the produced transition — so an
illegal joint reveal or a phase rewind is a real executor refusal in the fire path. `register` /
`register_deos` mount the seeded two-figure surface. `src/card.rs` ships the frame as a
renderer-independent `deos.ui.*` view-tree (native gpui / web HTML / discord — one piece of data).

## What this crate exports

```rust
// the game core
JointState (Relax/Contract/Hold/Extend), JointVector, Figure, MoveCommit, Frame, Match
Figure::joint_program() -> CellProgram          // the SymMemberOf-per-joint tooth
resolution::resolve_contact(...)                // the deterministic frame resolution

// the deos surface
figure_deos_program() -> CellProgram            // enum tooth ∧ Monotonic(PHASE)
tussle_app / register / register_deos
seed_figure / seed_figure_b
fire_commit_move / fire_reveal_move / fire_resolve_frame

// the card
card::* -> serde_json::Value                    // the deos.ui.* view-tree
```

## Tests

```
cargo test    -p starbridge-tussle
cargo run     -p starbridge-tussle --example tussle_match
```

| Test | What it pins |
|---|---|
| `src/tests.rs::out_of_enum_joint_is_refused_by_the_cell_program`, `pose_checked_is_the_in_band_enum_gate` | the `SymMemberOf` enum tooth bites |
| `src/tests.rs::opponent_move_is_unreadable_before_reveal`, `peek_then_switch_is_refused` | the fog-of-war commit |
| `src/tests.rs::player_cannot_pose_the_opponents_figure`, `wrong_figure_binding_fires_on_a_mismatched_filing` | the cap tooth |
| `src/tests.rs::frame_resolves_through_the_verified_executor`, `empty_ring_frame_is_a_conserving_noop`, `resolution_is_reproducible` | the conserving joint turn + determinism |
| `tests/deos_seam.rs` | the teeth biting through real signed fires (enum caveat, wrong-figure cap, phase gate, `Monotonic(PHASE)` rewind refusal) |
| `tests/reexpress_deos_app.rs` | the two-figure axum surface: per-viewer projection, web-of-cells publish, rehydration, manifest, web component |
