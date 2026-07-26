# Games as Receipts — the thesis made playable

dregg's core claim is one sentence: *a turn is the exercise of an attenuable,
proof-carrying capability over owned state, leaving a receipt.* The game portfolio is
that sentence made playable. In each of these games, a move is a real executor turn: a
legal move commits and lands a `TurnReceipt`; an illegal move is not forbidden by app
code — it is **unprovable at the kernel**. The executor refuses it in-band, nothing
commits, and the anti-ghost property means no forged effect can ride along
(see [`OVERVIEW.md`](OVERVIEW.md) for the kernel model this rests on).

Three games, three genres, one engine:

| game | genre | crate(s) | the mechanic that exercises the engine |
|---|---|---|---|
| **The Descent** | daily permadeath roguelite | `dreggnet-offerings/src/daily_descent.rs` + `dungeon-on-dregg` | drand-seeded daily world; HP-floor / WriteOnce-death teeth; no-cheat leaderboard |
| **multiway-tug** | hidden-hand card game | `dregg-multiway-tug` | Poseidon2-committed hidden hand; membership-proven plays; the STARK fold |
| **automatafl** | simultaneous-move board game | `dregg-automatafl` | a hand-authored Custom-VK AIR for the whole board transition |

The strategy of record for shipping these is [`GAME-STRATEGY.md`](GAME-STRATEGY.md);
the per-game inventory is [`VERIFIED-GAME-PORTFOLIO.md`](VERIFIED-GAME-PORTFOLIO.md);
the engine roadmap is [`GAME-ENGINE-ROADMAP.md`](GAME-ENGINE-ROADMAP.md). This document
is the cross-cutting story: what "every move is a receipt" concretely means, and at
which assurance tier each surface currently delivers it.

## Illegal means unprovable

The rule enforcement is a kernel predicate, not a client courtesy. The pattern, on the
real substrate (`spween-dregg`'s `WorldCell` over the `EmbeddedExecutor` — the same
cell / `CellProgram` / `TurnReceipt` machinery the rest of dregg runs):

- A move's effects lower to `Effect::SetField` writes on the game cell; the whole move
  is ONE cap-bounded turn.
- The rules are `StateConstraint` teeth installed as `CellProgram` cases, re-checked by
  the executor on the post-state: an HP floor is `FieldGte`, a claimed-once crown is
  `WriteOnce`, a spend budget is a cross-slot `FieldLteField`, a collapsed stair is a
  `Monotonic` ratchet (`demo/real-dungeon-service/src/main.rs:17-22` names these
  exactly; all four are installed live in that service, and its `--self-check`
  demonstrates the `WriteOnce` crown refusal end-to-end).
- A failing tooth is a real `WorldError::Refused` from the executor: nothing commits,
  no receipt exists, the session state is unchanged. There is no "server said no" —
  there is no provable turn.

`dungeon-on-dregg/src/lib.rs` documents the lowering (a scene condition
`{ has_lantern >= 1 }` compiles to a `StateConstraint::FieldGte` case), and its
`multicell` module carries the cross-cell version: room B's gate reads item A's
finalized owner slot on item A's *own* cell via `ObservedFieldEquals` +
`FinalizedRootAuthority` — a cross-cell rule as a kernel predicate, not a host `if`.

## The assurance ladder — three tiers, distinguished

"A stranger can check the game" is true at three different strengths in this tree.
They are different objects and the docs and services name which one they deliver.

### Tier 1 — replay-verify (O(N) re-execution, trust-minimized)

The verifier re-drives a fresh, identically-seeded world through the recorded choice
sequence and confirms every committed state reproduces, with the receipt chain linking
throughout. Two teeth (`spween-dregg/src/verify.rs`):

- **chain linkage** (`verify_chain_linkage`, `spween-dregg/src/verify.rs:99`) — each
  receipt's `pre_state_hash` equals its predecessor's `post_state_hash`; every
  `turn_hash` genuine and distinct. Splice / drop / reorder / tamper breaks the link.
- **replay** (`verify_by_replay`, `spween-dregg/src/verify.rs:123`) — a forged or
  ineligible choice is refused *by the real executor* on replay; an altered record
  diverges from the reproduced state.

This tier is what the playable surfaces run today:

- `demo/real-dungeon-service` exposes it as `GET /session/verify`, and its module
  header carries the scope note verbatim (`demo/real-dungeon-service/src/main.rs:38-45`):
  verification there is O(N) replay + chain linkage, **not** the succinct light client,
  and the service does not claim otherwise.
- The Descent's no-cheat leaderboard accepts a run only if
  `ugc_dregg::verify_completion` re-executes it to the win against a fresh
  identically-seeded world (`dreggnet-offerings/src/daily_descent.rs`); the persisted
  Discord board replays and re-verifies every stored completion on boot
  (`discord-bot/src/descent_board_store.rs:5`).
- `attested-dm` has its own engine-internal analogue, `verify_ledger_replay`
  (`attested-dm/src/game.rs:3482`), over its own blake3 hash-chain ledger. That ledger
  is a **labeled toy** relative to the deployed VK; the portfolio ships on the real
  executor path only, never on it (the scope note at the top of
  [`GAME-ENGINE-ROADMAP.md`](GAME-ENGINE-ROADMAP.md)).

What tier 1 buys: no trust in the server's arithmetic — only in the code you run
yourself. What it costs: the verifier re-executes the whole history.

### Tier 2 — STARK-backed (succinct; a match is one proof)

A whole match folds into one `WholeChainProof` that a pure light client
(`dregg_lightclient::verify_history`) accepts, re-executing nothing.

multiway-tug is the resident of this tier (`dregg-multiway-tug/src/fold.rs`): each
hidden-hand play — proven in the clear as a `StateConstraint::Witnessed {
MerkleMembership }` against the hand's committed Poseidon2 4-ary Merkle root — lowers
to a `LoweredMembership` custom leaf on the deployed `merkle_poseidon2_descriptor`,
proves through `prove_custom_leaf_with_commitment`, binds into a `Custom`-effect turn,
and the turns fold via `prove_turn_chain_recursive`. A turn whose leg claims a
commitment no verifying sub-proof backs is UNSAT: a forged match mints no root.

The honest scope lives in the module header: the played card is face-up; the public
inputs carry only `[leaf, root]`, so the card ids and the rest of the hand are not in
the proof — but the deployed STARK is **succinct, not zero-knowledge**.
Transcript-hiding crypto-ZK is a separate, later concern, named, not claimed.

### Tier 3 — Custom-VK (a bespoke AIR is the game's rules)

The deepest tier: the game's whole transition function is itself a hand-authored
circuit, and "the move was legal" is the statement the proof proves — not a membership
side-condition. automatafl lives here (`dregg-automatafl/src/lib.rs:1-15`): a
Custom-VK AIR checking `new == apply_turn(old, moves)`, built from low-degree DSL
gates, one-hot random-access board reads, and a bit-decomposition range gadget —
hash-free, so it folds through the generic custom-leaf path unchanged.

⚑ 2026-07-25. The staging this section described (**D1** automaton-only → **D2** +
single move → **D3** + the n=2 simultaneous resolution) belonged to a HAND-WRITTEN
RUST AIR that is deleted (`f44e26e7b`), together with the two Rust batteries that
gated it. Calling that arrangement "translation validation" was wrong: there is no
formal semantics of Rust, so a Rust AIR differenced against a spec on cases proves
nothing about all inputs. The AIR is now authored in Lean and emitted at n=11 — Leg R
`automataflResolveDescN`
(`metatheory/Dregg2/Circuit/Emit/AutomataflResolveEmit.lean`), Leg A
`automataflStepDescN` (`.../AutomataflStepEmit.lean`), Leg C for conflict rounds
(`.../AutomataflLegCEmit.lean`) — plus a sealed-move reveal leaf
(`.../AutomataflRevealEmit.lean`) for the commit → reveal → resolve shape the Offering
plays (`dregg-automatafl/src/surface.rs`). What gates it now:

- the acceptance battery (`dregg-automatafl/tests/lean_oracle.rs`): every transition,
  legality verdict, conflict set and win is answered by `@[export]
  dregg_automatafl_rules` over `Dregg2.Games.AutomataflRules`, with the first test
  ASSERTING the export is linked so a thin archive fails RED instead of skipping;
- the refinement, in Lean over the emitted descriptors
  (`metatheory/Dregg2/Circuit/Emit/AutomataflResolveRefine.lean`,
  `AutomataflStepRefine.lean`, and the capstones);
- the seam canaries (`dreggnet-game-board/tests/two_leg_board_window.rs`,
  `multi_round_fold.rs`) — PI-level and constraint-level arms run green; every
  deployed-prover fold arm is `#[ignore]`d at tens of minutes and **has not been
  run**, so end-to-end light-client acceptance of a played match is not a measured
  result.

Why Custom-VK and not the simple teeth: the 16-register `StateConstraint` vocabulary
handles state shape, counts, and thresholds; it does not hold an 11×11 board or a
raycast-decided automaton step. Complex mechanics get a bespoke AIR (a `Custom` leaf in
the same fold), and the simple teeth keep doing what they are good at alongside it.
The design study for the n=2 staging is
[`AUTOMATAFL-N2-DESIGN.md`](AUTOMATAFL-N2-DESIGN.md); the platform framing is
[`GAME-INFRA-ROADMAP.md`](GAME-INFRA-ROADMAP.md) and
[`DESIGN-verifiable-game.md`](DESIGN-verifiable-game.md).

## The Lean connection

Both circuit-tier games carry their rules as Lean models with connected refinements
(`metatheory/Dregg2/Games/`):

- `Automatafl.lean` + `AutomataflAir.lean` — the pure `applyTurn` model;
  `airAutomatafl_iff_applyTurn` (the staged circuit's admission relation is the graph
  of `applyTurn`) and `conflictResolve_pair` (the D3 truth table matches the reference
  resolution). The gadget arithmetizations' soundness is carried as the named
  `MoveSound` / `StepSound` hypotheses — like `MerkleSound` upstream, discharged by the
  deployed circuit, not re-proven in Lean.
- `MultiwayTug.lean` + `MultiwayTugAir.lean` — conservation (genuine multiset
  arithmetic), one-action-per-round, control-correct scoring;
  `airPlay_iff_applyAction` connects the Phase-3 fold-leaf shape to the model, with
  the commitment's collision-resistance carried as the named STARK-soundness-remainder
  hypothesis (opaque `M.commit`).

The named hypotheses are stated in the theorems, not hidden: `#assert_axioms` does not
inspect hypotheses, so the statement is the honesty surface.

## Named residuals (labeled, not closed)

- **automatafl width** — the D2/D3 numbers (1178 / 1411 at n=5, 509 / 661 at n=3) were
  measured by a test that was deleted with the Rust AIR; they are RETRACTED, not
  carried forward. The emitted legs at n=11 are 1273 columns (Leg R), 680 (Leg A) and
  1208 (Leg C) — see the `#[ignore]` reasons in
  `dreggnet-game-board/tests/two_leg_board_window.rs` and `multi_round_fold.rs`, and
  [`VERIFIED-GAME-PORTFOLIO.md`](VERIFIED-GAME-PORTFOLIO.md).
- **automatafl fold not run** — every n=11 deployed-prover arm is `#[ignore]`d at tens
  of minutes and has not been run on the build box.
- **automatafl move count** — the general N=11 occlusion scan and full-SCC resolution
  are labeled residuals.
- **multiway-tug privacy** — succinct, not zero-knowledge (see tier 2 above).
- **The Descent's attested narrator** — the DM is always world-resolved (the AI
  proposes, the executor disposes), but the attestation's live pinned-notary session is
  the named operational frontier ([`GAME-STRATEGY.md`](GAME-STRATEGY.md), decision 3).
- **Tier mobility** — the Descent's dungeon surfaces verify at tier 1 today; lifting a
  playthrough onto the succinct fold the other two games exercise is planned work, not
  a current property.

Deployment truth, stated once: no public devnet is anchored right now — these games,
their proofs, and their verifiers run in-tree and on project machines (the SLOW
prove/fold gates are `#[ignore]` tests run on the build box), and no doc in this set
claims a durable public deployment.

## Why this is the thesis and not a demo

The portfolio is three genres exercising every layer of one engine: the executor teeth
(Descent), the witnessed-predicate + fold path (multiway-tug), the Custom-VK path
(automatafl) — each game a customer of the engine rather than its author, each with a
falsifier battery (forged move refused, forged record diverges on replay, forged board
fails to prove, spliced root rejected by the light client). The claim "every move is a
receipt" is not a metaphor here; it is the type of the return value.
