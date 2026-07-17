# The Verified-Game Portfolio — automatafl + multiway-tug

Two games as the dregg engine's 2nd/3rd customers — the platform proof. Both ship as full crates
(`dregg-automatafl`, `dregg-multiway-tug`) and both are verified games: rules modeled in Lean, a
custom AIR for the mechanics, plays as real executor turns, playable as Offerings on every dreggnet
frontend, and a whole match folding to one succinct proof a pure light client accepts. NB the
mechanics are a CUSTOM VK (a bespoke AIR / a `Custom` leaf in the fold), NOT plain StateConstraint
teeth — teeth handle the simple state-shape + validity; the Custom AIR proves the complex transition.

## The shared architecture (per game)

1. The reference rules engine is vendored as the deterministic `apply_turn`/`applyAction` oracle
   (`dregg-automatafl/src/reference.rs`, `dregg-multiway-tug/src/reference.rs`).
2. The STATE: simple scalars as dregg-schema register components; the board/deck/hand as a heap
   COLLECTION (the 16-register model doesn't hold a 121-cell board or a 21-card deck).
3. The SIMPLE teeth lower via game-turn-slice's compiler (validity, counts, win-thresholds,
   conservation).
4. The COMPLEX transition is a hand-authored CUSTOM AIR (a `Custom` leaf), TRANSLATION-VALIDATION
   shape: the mover computes the next state off-circuit; the circuit re-checks each rule against the
   witnessed next state.
5. The LEAN: model the rules and connect the AIR to `applyTurn` — "the circuit accepts iff
   `next == applyTurn(old, moves)`", the game-level analogue of the `evalSimpleCtx_*_iff`
   constraint twins.
6. The STARK: the Custom leaf → `prove_turn_chain_recursive` (fold) → `verify_history` — generic
   over any CellProgram, reused unchanged.
7. The Offering + frontends: the `open`/`actions`/`advance`/`verify`/`render`/`price` shape every
   dreggnet frontend (web / Discord / Telegram / WeChat) drives.

## THE FOLD IS EXERCISED IN-TREE (the former "Lane-D" gate is behind us)

`dregg-automatafl/tests/prove_fold.rs` builds a D1 automaton-step custom leaf, folds a multi-turn
chain via `prove_turn_chain_recursive`, and `dregg_lightclient::verify_history` ACCEPTS — with a
forged-chain arm (a spliced `final_root`) REJECTED, so the acceptance is non-vacuous. The same fold
carries multiway-tug's membership-proven plays (`dregg-multiway-tug/src/fold.rs`): a whole private
match becomes ONE `WholeChainProof`. Match-as-one-succinct-proof is a shipped path, not a gated plan.

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

- **The engine** (`src/reference.rs`) — the vendored deterministic `apply_turn` oracle, mirroring
  `Dregg2.Games.Automatafl` and its `#guard`s.
- **The staged board-transition AIR** (`src/air.rs`, `src/builder.rs`, `src/moves.rs`) — the
  translation-validation Custom AIR, staged D1 (Daemon-only) → D2 (single move + occlusion) → D3
  (n=2 simultaneous resolution with the fork/collide/survive truth table).
- **The refinement battery** (`dregg-automatafl/tests/refinement.rs`) — the AIR accepts `(old, moves, next)` IFF
  `next == apply_turn(old, moves)`, driven against the oracle; non-vacuous (a wrong `next`, an
  invalid move, and a forged resolution are each REJECTED).
- **The fold** (`dregg-automatafl/tests/prove_fold.rs`) — D1/D2/D3 leaves prove, fold, and `verify_history` accepts;
  forged steps mint no leaf.
- **The Lean** (`metatheory/Dregg2/Games/Automatafl.lean` + `AutomataflAir.lean`) — the pure
  `applyTurn` model with its load-bearing properties, and the CONNECTED refinement:
  `airAutomatafl_iff_applyTurn` (the staged circuit's admission relation IS the graph of
  `applyTurn`), `conflictResolve_pair` (the D3 fork/collide/survive table matches the reference
  resolution), fed into the §7 obligation `concreteAutomataflAIR_refines`. The gadget
  arithmetizations' soundness is carried as the named `MoveSound`/`StepSound` hypotheses (like
  `MerkleSound` upstream), not re-proven — that is the deployed circuit's job.
- **The Offering** (`src/surface.rs`) — `AutomataflOffering` renders the board as a
  `ViewNode::CoordGrid` and runs the simultaneous-move shape as COMMIT → REVEAL → RESOLVE (sealed
  moves, opened against their commitments, one real turn applying `apply_turn`).

**Named residuals (labeled, not closed):**
- **Width** — D2/D3 run the automaton gadget twice, so at n=5 they EXCEED `MAX_TRACE_WIDTH = 1024`
  (D2 = 1178, D3 = 1411; measured in `dregg-automatafl/tests/size.rs`). They fit and prove-fold-verify at n=3
  (D2 = 509, D3 = 661). The named close is the segmented board-read scan (the N=11 follow).
- **Move count** — the concrete gadget is staged to n≤2 simultaneous moves; the general N=11
  occlusion scan and full-SCC resolution are the labeled residuals (`Automatafl.lean` §4,
  `moves.rs`).

## The portfolio claim

Descent (roguelite) + multiway-tug (hidden-hand card game) + automatafl (simultaneous-move
boardgame): three genres on one verifiable engine — the Custom-VK/custom-leaf path, the
verified-emit-from-Lean discipline, the generic fold + `verify_history` backend, and the
Offering/frontend reuse, each exercised by a game that is not the engine's author.
