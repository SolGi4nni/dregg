# The Verified-Game Portfolio — automatafl + multiway-tug

Two games as the dregg engine's 2nd/3rd customers — the platform proof. Both ship as full crates
(`dregg-automatafl`, `dregg-multiway-tug`) and both are verified games: rules modeled in Lean, a
custom AIR for the mechanics, plays as real executor turns, playable as Offerings on every dreggnet
frontend, and a whole match folding to one succinct proof a pure light client accepts. NB the
mechanics are a CUSTOM VK (a bespoke AIR / a `Custom` leaf in the fold), NOT plain StateConstraint
teeth — teeth handle the simple state-shape + validity; the Custom AIR proves the complex transition.

## The shared architecture (per game)

1. The rules engine is the deterministic `apply_turn`/`applyAction` oracle. For **automatafl this is
   the LEAN** — `@[export] dregg_automatafl_rules` over `Dregg2.Games.AutomataflRules`, called from
   `dregg-automatafl/src/rules.rs`; the vendored Rust oracle `src/reference.rs` is DELETED (2026-07-25)
   because the conformance audit found the transcribed lineage divergent from the ruleset, including
   three divergences that destroy material. For **multiway-tug the TERMINAL rule is now the LEAN
   too** — `@[export] dregg_multiway_tug_rules` over `Dregg2.Games.MultiwayTug`, called from
   `dregg-multiway-tug/src/rules.rs`; the Rust `winner_of` is DELETED (2026-07-25) because it was
   `roundWinner` truncated to its two absolute-threshold branches and therefore drew **78.5%** of
   played rounds against the model's 5.1%. ⚠ The wound is only PARTLY closed: `reference.rs` still
   decides action legality and the transition itself (`legal_decisions`, `apply`, `apply_action`,
   `apply_response`) in Rust. The FFI verbs for those exist (`legal`, `legalresp`, `kinds`, `act`,
   `respond`). ⚑ An earlier note here claimed routing them was blocked on per-call FFI cost — that
   claim was made without measuring and is WRONG: a wire call costs **31 us isolated / 112 us under
   concurrent load** (measured both, persvati 2026-07-25, `rules::tests::one_oracle_call_costs` —
   quote the RANGE), so the ~3.8e5 calls a routed maximin search would make cost **12-43 s** per
   200-round run — ordinary, not prohibitive. The LEGALITY half is
   routable now. What actually blocks the TRANSITION half is that `MultiwayTug.lean` models cards
   at guild-row resolution and has no notion of a distinct card id, so the id bookkeeping has no
   spec to route to.
2. The STATE: simple scalars as dregg-schema register components; the board/deck/hand as a heap
   COLLECTION (the 16-register model doesn't hold a 121-cell board or a 21-card deck).
3. The SIMPLE teeth lower via game-turn-slice's compiler (validity, counts, win-thresholds,
   conservation).
4. The COMPLEX transition is a CUSTOM AIR (a `Custom` leaf): the mover computes the next state
   off-circuit; the circuit re-checks each rule against the witnessed next state. ⚑ For automatafl
   that AIR is now **Lean-authored and emitted** — the hand-authored Rust one is deleted — and the
   "translation-validation" label this list used to carry was wrong either way: there is no formal
   semantics of Rust, so a Rust AIR differenced against a spec on cases is unit testing, not
   validation.
5. The LEAN: model the rules and connect the AIR to `applyTurn` — "the circuit accepts iff
   `next == applyTurn(old, moves)`", the game-level analogue of the `evalSimpleCtx_*_iff`
   constraint twins.
6. The STARK: the Custom leaf → `prove_turn_chain_recursive` (fold) → `verify_history` — generic
   over any CellProgram, reused unchanged.
7. The Offering + frontends: the `open`/`actions`/`advance`/`verify`/`render`/`price` shape every
   dreggnet frontend (web / Discord / Telegram / WeChat) drives.

## THE FOLD — WIRED IN-TREE, ITS ACCEPTANCE GATE NOT YET RUN

⚑ 2026-07-25 correction. This section used to cite a `prove_fold.rs` under `dregg-automatafl/tests/`
for a green D1 leaf → fold → `verify_history` ACCEPTS. That test was deleted with the hand-written Rust
AIR it drove, and the two-leg descriptor path that replaced it does not carry the same green.

What is true now: `dreggnet-game-board/tests/two_leg_board_window.rs` chains Leg R
(`automataflResolveDescN 11`) and Leg A (`automataflStepDescN 11`) and states its own three tiers —
the PI level (windows carry the right values, a forged mid breaks the seam) and the constraint level
(`dregg-circuit-prove::board_window_seam_tests`, a broken equality is a `connect` conflict) RUN
GREEN; the deployed-prover arm, `the_honest_two_leg_match_folds_and_the_light_client_reads_the_final_position`,
is `#[ignore]`d at tens of minutes and **has not been run**. Same shape in
`dreggnet-game-board/tests/multi_round_fold.rs` (the Leg C conflict braid) and
`dreggnet-prove-service/tests/match_fold.rs` (fast arm green, fold arm `--ignored`). So the seam is
wired and its mechanism bites; a light client accepting a real automatafl match is not a measured
result. The same fold carries multiway-tug's membership-proven plays
(`dregg-multiway-tug/src/fold.rs`): a whole private match becomes ONE `WholeChainProof`.

## multiway-tug — the hidden-hand card game (all phases present)

A 2-player card game re-themed from Hanamikoji (Kota Nakayama): 7 guild rows (influence
`[2,2,2,3,3,4,5]` = 21), a 21-card deck, a hidden 6-card hand, 4 once-per-round actions
(Secret/Discard/Gift/Competition), win at ≥ 11 influence OR ≥ 4 rows. Conservation is the game's own
design — cards only move, never destroyed. The phase ladder is BUILT, each phase a module:

- **Phase 0 — rules on the executor** (`src/game.rs`): a play commits the reference engine's
  projection as a real turn; a legal move lands a `Landed` receipt, an illegal one is `Refused` and
  commits nothing.
- **Phase 1 — cards-as-assets + provably-fair packs** (`src/packs.rs`): a printed card is a real
  `dreggnet_asset` note; a booster's contents are a pure verified function of a committed pack seed
  over the verified procgen stream (committed-weight rarity draws).
- **Phase 2 — the cryptographic hidden hand** (`src/hidden_hand.rs`): each hand is COMMITTED at deal
  as a Poseidon2 4-ary Merkle root over blinded leaves (`Poseidon2(DOMAIN, card, nonce, 0)`); each
  play carries a `StateConstraint::Witnessed { MerkleMembership }` proof verified through the REAL
  `WitnessedPredicateRegistry` by the REAL `CellProgram::evaluate_full`; the remaining-hand root
  updates per play, so a re-play fails membership (the crypto is the no-double-play tooth); the
  Gift/Competition blind pick and the concealed Secret ride commit→reveal (`BlindPick`).
- **Phase 3 — the STARK fold** (`src/fold.rs`): each membership-proven play lowers to a
  `LoweredMembership` custom leaf (the deployed `merkle_poseidon2_descriptor` — the same 4-ary
  Poseidon2 recurrence the clear-side verifier walks) with public inputs `[leaf, root]`; the turns
  fold into one `WholeChainProof`. HONEST SCOPE: the played card is face-up; "private-in-fold" means
  the card ids and the rest of the hand are NOT in the proof/public inputs. The deployed STARK is
  SUCCINCT, not zero-knowledge — transcript-hiding crypto-ZK is a separate, later concern.
- **Phase 4 — the Lean** (`metatheory/Dregg2/Games/MultiwayTug.lean` + `MultiwayTugAir.lean`): the
  pure model proves conservation (genuine multiset arithmetic, lifted along the `Boundary` keystone),
  one-action-per-round, and control-correct scoring; `MultiwayTugAir` connects the concrete Phase-3
  fold-leaf shape to the model — `airPlay_iff_applyAction` (the leaf's admission relation IS the
  graph of `applyAction`, non-vacuous, `#assert_axioms`-clean), with the commitment's
  collision-resistance carried as the named STARK-soundness-remainder hypothesis (opaque
  `M.commit`), not re-proven.
- **Phase 5 — the Offering** (`src/surface.rs`): `TugOffering` with per-viewer fog — `render` paints
  both hands as fog (count + committed root); `render_for` reveals only the viewer's own hand,
  sourced from their committed `HandTree`. The UI fog and the proof-layer hiding are separate seams
  that agree.

## automatafl — the simultaneous-move cellular-automaton game (the deeper one)

An original game (o1Labs / Corey Richardson), NOT a Tafl variant: an 11×11 grid of
{Repulsor, Attractor, Automaton, Vacuum}; players SIMULTANEOUSLY submit secret moves, reveal
together, moves conflict-resolve and apply, then the Automaton ("Daemon") takes one autonomous
raycast-decided step; win = steer the Daemon into your goal (no capture). What exists:

- **The engine** — the LEAN, called. `dregg-automatafl/src/rules.rs` asks
  `@[export] dregg_automatafl_rules` (`Dregg2.Games.AutomataflFFI` over the rules-faithful
  `AutomataflRules`) for every board transition, legality verdict, conflict set and win; `src/board.rs`
  is the state shape plus the wire, and there is no Rust fallback. ⚑ 2026-07-25: this replaced
  `src/reference.rs`, a hand transcription of `~/dev/automatafl/logic` (a non-canonical experiment)
  that swapped the pieces of a 2-cycle and let a mover destroy a stationary piece on its destination.
- **The board-transition AIR — Lean-authored, the Rust one DELETED.** The hand-written Custom AIR
  (`air.rs`, `builder.rs`, `moves.rs`) and its Rust batteries (`refinement.rs`, `prove_fold.rs`,
  `size.rs`, `prove_11x11.rs`) were deleted in `f44e26e7b` / `e3c5bb8b9`; per house law #1 an AIR is
  authored in Lean, and a Rust AIR carried no proof of anything. The deployed object is now two
  emitted descriptors at n=11 — Leg R `automataflResolveDescN`
  (`metatheory/Dregg2/Circuit/Emit/AutomataflResolveEmit.lean`, `old → mid`, move adjudication) and
  Leg A `automataflStepDescN` (`metatheory/Dregg2/Circuit/Emit/AutomataflStepEmit.lean`, `mid →
  new`, the automaton) — plus Leg C for conflict rounds
  (`metatheory/Dregg2/Circuit/Emit/AutomataflLegCEmit.lean`).
- **The acceptance battery** (`dregg-automatafl/tests/lean_oracle.rs`) — every board transition,
  legality verdict, conflict set and win comes back through `@[export] dregg_automatafl_rules`, and
  the first test ASSERTS the export is present so a thin archive fails RED rather than skipping.
- **The refinement** — in Lean, over the ACTUAL emitted descriptors:
  `metatheory/Dregg2/Circuit/Emit/AutomataflResolveRefine.lean` and `AutomataflStepRefine.lean`,
  with the capstones `AutomataflResolveCapstone.lean` / `AutomataflStepCapstone.lean` /
  `AutomataflTurnCapstone.lean`. The old Rust "refinement battery" was a differential test on cases
  and proved nothing about all inputs.
- **The Lean model** (`metatheory/Dregg2/Games/Automatafl.lean` + `AutomataflRules.lean`) — the pure
  `applyTurn` with its load-bearing properties, `AutomataflFFI.lean` exporting it to the crate.
  ⚠ `metatheory/Dregg2/Games/AutomataflAir.lean` (`airAutomatafl_iff_applyTurn`,
  `concreteAutomataflAIR_refines`) is the ABSTRACT staged-AIR relation whose own header already
  disclaimed any machine-checked tie to the deployed circuit; with the Rust AIR it described now
  deleted, it models an object nothing runs. Read it as lineage, not as a deployed guarantee.
- **The Offering** (`src/surface.rs`) — `AutomataflOffering` renders the board as a
  `ViewNode::CoordGrid` and runs the simultaneous-move shape as COMMIT → REVEAL → RESOLVE (sealed
  moves, opened against their commitments, one real turn applying `apply_turn`).

**Named residuals (labeled, not closed):**
- **Width** — the D2/D3 width numbers this section used to record (1178 / 1411 at n=5, 509 / 661 at
  n=3, measured in the deleted `size.rs`) were measurements of the deleted Rust AIR and are
  RETRACTED. The emitted legs at n=11 are 1273 columns (Leg R), 680 (Leg A) and 1208 (Leg C), per
  the `#[ignore]` reasons in `dreggnet-game-board/tests/two_leg_board_window.rs` and
  `multi_round_fold.rs`.
- **The fold has not been run** — every deployed-prover arm at n=11 is `#[ignore]`d at tens of
  minutes. Until one is run on the build box, "a played match folds and the light client accepts"
  is a wiring claim, not a result.
- **Move count** — the general N=11 occlusion scan and full-SCC resolution are the labeled
  residuals (`metatheory/Dregg2/Games/Automatafl.lean` §4).

## The portfolio claim

Descent (roguelite) + multiway-tug (hidden-hand card game) + automatafl (simultaneous-move
boardgame): three genres on one verifiable engine — the Custom-VK/custom-leaf path, the
verified-emit-from-Lean discipline, the generic fold + `verify_history` backend, and the
Offering/frontend reuse, each exercised by a game that is not the engine's author.
