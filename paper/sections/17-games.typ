// =============================================================================
// Section 17: The game portfolio
// =============================================================================

#import "../defs.typ": lean
= The game portfolio <sec-games>

The factory userspace of @sec-realization has a first product family: games. A
game turn is the model's opening sentence with nothing adapted --- the exercise
of an attenuable, proof-carrying token over owned state, leaving a verifiable
receipt. The receipt is the run. The same primitive serves the player, who gets
a fair game no operator can falsify, and the author, who gets an engine whose
contract is a kernel theorem rather than server code; the flagship game is the
first client of the platform schema it motivates. This section states what each
maturity level in the portfolio is: what is proved in Lean, what is exercised by
tests, what is deployed, and what is coded behind an operator switch that has
not been flipped.

== Three games, one shape

*The Descent* (`dreggnet-offerings/src/daily_descent.rs`, played through
`discord-bot/src/commands/descent.rs`) is a daily dungeon crawl. Each day one
world is generated from the drand `quicknet` randomness beacon, so every player
plays the same seed and no one --- operator included --- can grind a favourable
dungeon; the beacon check is a real BLS pairing verification against the pinned
group key, and fetching the day's round from a drand node is the named client
seam. The stakes are enforced by the executor, not the narrator. A lethal
position routes to a committed defeat passage: the hit-point floor refuses every
other move, a write-once `downed` flag ends the run, and a lost run re-verifies
by replay exactly as a won one does (`dungeon-on-dregg/src/bloodgate.rs`). A
d20-versus-difficulty gamble gates a shortcut, with the roll bound into the
receipt so a forged pass is caught on re-verification, and a shared write-once
slot prices an either/or choice. Opt-in hardcore permadeath is write-once-final
over a persistent character (`dreggnet-offerings/src/character.rs`, durable in
the bot's sqlite store), and a weekly bracket advances only on a verified win
(`dreggnet-offerings/src/descent_tournament.rs`).

The narrator is a language model, and the division of authority is strict: the
model proposes, the verified rules dispose. Hit points, inventory, and dice
outcomes are cell fields governed by the cell's program on the executor path,
and the narrator holds no capability to write them outside an admitted turn. A
narration that contradicts the committed state changes nothing, so the game
master cannot misreport the world it narrates. Attesting the narrator itself
--- that a disclosed model produced the prose --- is designed against the
attestation carrier and has a named operational remainder, a live pinned-notary
session (`docs/GAME-STRATEGY.md`).

The other two games are board games whose rulebooks are Lean definitions.
*automatafl* is a board game of indirect control: players place attractors and
repulsors, moves are resolved for conflicts, and a neutral automaton takes one
rule-determined step. *Multiway tug* is a hidden-hand card game whose plays
open against a committed hand. For both, the deployed circuit's admission
relation is proved equal to the rulebook's step function, stated over the
staged form the circuit actually computes rather than over a restatement of the
rules.

== The rulebook theorems

For automatafl, the staged circuit admits a triple exactly when the successor
board is the rulebook's turn function applied to the old board and moves
(#lean("Games.Automatafl.airAutomatafl_iff_applyTurn")); a successor that
relocates a piece anywhere the rules do not has no satisfying witness
(#lean("Games.Automatafl.airAutomatafl_forged_refused")); the circuit admits at
most one successor per position
(#lean("Games.Automatafl.airAutomatafl_functional")); and the in-circuit
conflict-selection table is proved to match the reference resolution
(#lean("Games.Automatafl.conflictResolve_pair")). The packaged circuit
discharges the abstract refinement obligation rather than leaving it a bare
hypothesis (#lean("Games.Automatafl.concreteAutomataflAIR_refines")). For the
tug game, a play is admitted exactly when it is legal, its cards open by
membership proof against the committed hand root, and the successor is the
rulebook's (#lean("Games.MultiwayTug.airPlay_iff_applyAction")); after a play,
the committed root of the remaining hand is the commitment of the hand minus
the played cards, so replaying a spent card fails membership under the new root
(#lean("Games.MultiwayTug.remaining_root_updates")); consecutive leaves compose
as consecutive rule steps
(#lean("Games.MultiwayTug.airPlay_chain_are_applySteps")).

The statements carry their remainder explicitly. The arithmetization soundness
of the low-level gadgets --- that a satisfying witness forces the move-resolve
and automaton gadgets to compute their reference stages, and that Merkle
membership implies hand membership --- is carried as named hypotheses
(#lean("Games.Automatafl.MoveSound"), #lean("Games.Automatafl.StepSound"),
#lean("Games.MultiwayTug.MerkleSound")), in the same discipline as the engine
carrier of @sec-proofs: hypotheses, never axioms, so the axiom audit stays on
the kernel triple while the obligation remains visible in the statement.
Discharging them is the deployed circuit's job, not the model's.

== The tests against the statements

The Rust game crates are tested against these theorems rather than beside them.
A fast refinement battery (`dregg-automatafl/tests/refinement.rs`) drives the
built circuit against a reference oracle that mirrors the Lean rules and their
`#guard` cases: the circuit accepts the honest successor and rejects a wrong
successor, an invalid move, and a forged conflict resolution. The proving
battery (`dregg-automatafl/tests/prove_fold.rs`, minutes-long and run on
demand) takes each staged circuit --- the automaton step, the single-move
apply, the two-move resolution, and a sealed-move stage whose Poseidon2
commit-and-reveal is opened inside the circuit --- through the deployed path of
@sec-proofs: the circuit proves as a recursion-foldable leaf, the in-circuit
commitment byte-matches the host binding, the leaf binds into a `Custom`-effect
turn, a turn chain folds through the deployed recursive prover, and the light
client's `verify_history` accepts. The negative directions are driven at the
same depth: a forged automaton step, a forged apply, a reveal that opens a move
other than the committed one, and a spliced final root each fail to produce an
accepting artifact.

The staging has a measured boundary (`dregg-automatafl/tests/size.rs`). The
two-move and single-move stages run the automaton gadget a second time on the
resolved board, and at board size five their trace widths (1178 and 1411
columns) exceed the prover's 1024-column ceiling; they fit and prove at board
size three. The full 11-by-11 board and general $N$-move resolution are the named
residuals, to be closed by a segmented board-read scan. Complex mechanics of this kind ride the custom-leaf path, not the
standard per-effect descriptors.

== Cheating, today and next

On the deployed surface, no-cheat is by replay: a submitted run carries its
public inputs, the server re-executes it on the same executor path, and the
leaderboard admits only runs that re-verify. Replay already suffices for the
central claim --- the operator cannot misreport a hit-point total, and a forged
roll or resolution is caught --- but the checker must re-run the game. The
labeled upgrade is the portable STARK proof: a completed run checkable by a
stranger from its receipts alone, with no re-execution and no trust in the
serving host. The fold tests above exercise exactly that path end-to-end for
the board-game leaves, so the upgrade is a change in what the submission
carries, not new proving machinery.

== What is deployed, and what awaits a flip

The public surface is the games web server behind a Tailscale funnel hostname
(`deploy/games/RUNBOOK-FUNNEL.md`): five games and the replay leaderboard,
served from one host as a user service unit that has survived a host reboot.
Its receipt-anchoring leg is currently down --- the devnet node the surface
anchored runs to was hand-run with an ephemeral data directory and its ledger
did not survive a host power-cycle --- so a submitted run ranks in-process and
anchoring fails closed until an operator brings up a durable node.

The payment loop is coded and tested but not live. The `dregg-pay` crate
implements a custodial backend: per-user deposit addresses by hardened
SLIP-0010 derivation from one seed, a payment watcher, a per-user run-credit
ledger idempotent per payment reference, and a treasury sweeper. Its economics
are dual-asset: USDC is the fuel that real-AI runs draw down, \$DREGG
accumulates in an illiquid treasury pile, a run costs \$0.10 by default, paying
in \$DREGG earns a 20% discount through a price oracle, and an
over-the-counter leg sells pile \$DREGG for USDC at a 10% discount. The
end-to-end suites pass on mock chains, including the liquidity-governance vote
that authorizes a signed pile-to-fuel swap. The Discord bot consumes the
backend: a buy-credits command issues the caller's deterministic deposit
address, polling credits payments idempotently into a sqlite-persisted ledger,
and a paid run debits one credit only after a successful narration under a
per-run dollar budget, falling back to the free tier on an empty balance
(`discord-bot/src/pay.rs`). Nothing mainnet is hardcoded; the bot defaults to a
mock watcher on devnet parameters, and the deployed surface's environment sets
no payment variables at all. Going live is an operator configuration change ---
mint, treasury, seed, network --- plus a custody watcher/sweeper service that
does not yet run, and no \$DREGG has been accepted for a service on the
deployed surface. The design endgame is protocol-native settlement, a run
budget as a conserved transfer balance with no operator custody; the custodial
backend names itself the bridge to that.

The token's role here is fixed by a locked policy: \$DREGG buys services ---
narration credits, hosting, cosmetics, entry --- and never buys power,
features, or yield; the leaderboard confers standing, not income. The asset
itself, its supply discipline, and the fee mechanics are the subject of the
paper's treatment of the system's own economics.

== From one game to an engine

The platform half of the portfolio is a schema between authors and cell
programs (`dregg-schema`). An author declares typed component archetypes ---
stats as bounded fields, resources as monotone counters, identity as
write-once, collections as heap fields --- and an allocator lowers them to a
slot and heap layout by translation validation: the search is untrusted, the
output is checked against a legality discipline under which an ill-aligned
layout cannot be constructed, and the result is a generated cell program and a
typed API. The Lean-proved legality obligation over this allocator, and the
leaf refinement from schema output to the fold, are its named next resolution.
Play UX rides the capability model directly: a session key is a caveat-bounded
delegation of the player's play capability --- attenuation, no new trust model
--- whose paymaster binds to the same run-credit ledger, so an out-of-credit
move commits nothing (`dreggnet-offerings/src/session.rs`); a session resumes
by replay of its reproducible public input, never from a trusted blob.

The portfolio's maturity gradient is uniform and deliberate. The rulebooks and
their circuit refinements are proved; the proving path is exercised by tests at
deployed depth; the play surface is deployed with replay as its verifier; the
payment loop is code behind an unflipped switch. What a player exercises today
is already the object the kernel theorems govern. The labeled upgrades change
how a run is checked and how it is paid for, not what a move is.
