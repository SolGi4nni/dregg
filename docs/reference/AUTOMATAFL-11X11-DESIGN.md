# Automatafl 11×11 (two-player) — circuit arithmetization design

**Goal:** prove a real 11×11 automatafl move-resolution turn, faithful to the reference rules
(`~/dev/automatafl`), as efficiently as possible under the deployed proof budget
(`MAX_TRACE_WIDTH=1024`, `MAX_CONSTRAINT_DEGREE=8`, `MAX_PUBLIC_INPUTS=64`).

**Scope — TWO PLAYERS ONLY (m = 2).** The multiplayer (m ≤ 4) extensions never matured; they are
future work. So: NO Tarjan-SCC engine, NO merge modes (Annihilate / BunchBeforeMerge / BunchedStacking),
NO >2-cycles. At m=2 the move graph is ≤2 edges — the only cycle is a 2-cycle (stays put), two moves to
one square is a collision-conflict, and the existing `dregg-automatafl/src/moves.rs::build_d3`
(fork / collide / survive / flow-through) is **already the faithful m=2 resolution**. The remaining work
is pure board scaling, not graph-algorithm-in-circuit.

## The real game (not hnefatafl)
It is **automatafl**: particles `{Vacuum, Repulsor, Attractor, Automaton}` on an 11×11 tafl-shaped board;
both players secretly submit one rook move (commit → reveal → resolve); after resolution the **Automaton**
takes ≤1 cardinal step decided by 4-axis raycasts (`evaluate_axis`, priorities UnbalancedPair>FromRepulsor
>TowardAttractor); you win when the Automaton enters your goal corner. The dregg `air.rs::automaton_gadget`
is the **faithful, correctly-ported Automaton** — not a stand-in. The only reduced part is the board size
(N=5) and the compile-time occlusion residual.

## No MPC
Simultaneity is a game-layer commit–reveal concern: the executor's seal/reveal/resolve teeth withhold
each move until both are sealed, and Leg S opens each seat's Poseidon2 `hash_4_to_1([frm,to,seat,nonce])`
in-circuit (a post-reveal swap needs a hash collision). Resolution is then a single-prover ZK statement
over already-revealed moves. Commit-reveal + in-AIR hash binding = fairness; the fold = correctness. **MPC
is not needed and not used.**

## The two walls, and the fixes
- **Degree wall:** `assert_member(coord, 0..n)` is a degree-n vanishing product (deg 11 > cap 8).
  **C.1 — bit-decompose** each coordinate: `c = Σ 2^k b_k` (4 bits, 0..15) + one `forced_ge0(10−c)`.
  Degree → ≤2. Semantics-preserving; the prerequisite for n=11.
- **Width wall:** D3 ≈ 14n² monolithic. Two fixes:
  - **C.2 — row×column √n reads:** a read `board[y·11+x]` builds two 11-wide one-hots `sel_row[y]`,
    `sel_col[x]` (22 selectors, not 121) → `val = Σ sel_row·sel_col·board`. Degree 3, hash/lookup-free.
    (Fallback if still tight: Merkle-path reads against the already-committed `board_root8`.)
  - **C.5 — fold-leg split:** the Automaton gadget alone is ≈750 cols at n=11; a monolith ≈1700. Split
    into foldable custom leaves connected by the intermediate board root `mid`:
    - **Leg S** (reveal) — opens the Poseidon2 move commitments; publishes `old_root`. ≈300 cols.
    - **Leg R** (`old → mid`) — validity + m=2 conflict + chain/flow-through + real occlusion + board
      rewrite; publishes `mid_root`. ≈900 cols (with Merkle-path old-reads).
    - **Leg A** (`mid → new`) — the existing automaton gadget on `mid`; publishes `new_root`; optional
      win check. ≈880 cols.
    All three fit 1024; degree ≤4. PI budget ≤32/64 per leg.
- **C.4 — real occlusion:** replace the compile-time interior residual with a coordinate-indexed 1-D
  masked scan: one authenticated line-extract (11-wide one-hot over the move's row/column) + an OR over
  the ≤9 interior positions gated by `[min<k<max]` (from decomposed endpoints) ∧ `[line[k]≠vacuum]` ∧
  `[k not a moving source]`. ~30 cols/move, no further board reads.

## The `mid_root` seam — CONFIRMED already-deployed (no protocol work)
Turn-chain continuity is exactly `new_root[i] == old_root[i+1]` (`circuit-prove/src/ivc_turn_chain.rs:32,
840-845`), and the state-binding fold `connect`s these lane-by-lane
(`joint_turn_recursive.rs:746-751`; a mismatch is a per-lane conflict ⇒ UNSAT ⇒ no root). So model Leg R
and Leg A as **two chained sub-turns on the same cell**: R exposes `mid_root` as its `last_new8`, A
exposes the same `mid_root` as its `first_old8`. Both compute a byte-identical `mid` on the honest path;
any disagreement fails the connect. Zero new machinery — wiring, not research. (Model as two receipts,
not two leaves under one receipt, to ride the deployed chain path.)

## Ordered build plan (two-player)
0. **Reference oracle → n=11, m=2** (`reference.rs`) — the refinement target; scale the faithful
   two-player `apply_turn` + the 11×11 stock opening + goal corners + win check. Differential-verify vs
   the automatafl reference (`~/dev/automatafl/logic`). *No SCC/merge/multiplayer.*
1. **C.1 coord bit-decomposition** — lowest risk, unblocks the degree wall; n=5 tests stay green,
   `max_degree` drops. Prerequisite for everything.
2. **C.2 row×column authenticated reads/writes** — retrofit `validate_move` / `write_mid_witnessed` /
   automaton reads; gate with the `air_accepts` shadow + tamper forgery tests.
3. **C.5 leg split + `mid_root` seam** — carve `build_d3` into Leg R (`old→mid`) + Leg A (`mid→new`);
   wire as chained sub-turns through the deployed state-binding fold. End-to-end: real leaf + fold +
   light-client accept.
4. **C.4 occlusion line-extract** — differential-fuzz the masked-window indicators vs `reference::occluded`
   across all rook moves on 11×11.
5. **Win check in Leg A** (optional) — closes the currently-executor-only `winner` gap.

**Foundation handed to every lane (absolute paths):** oracle `dregg-automatafl/src/reference.rs`;
builder primitives `dregg-automatafl/src/builder.rs`; the seam `circuit-prove/src/joint_turn_recursive.rs`
+ `circuit-prove/src/ivc_turn_chain.rs`; the Lean contract `metatheory/Dregg2/Games/Automatafl.lean`; the
automatafl ground truth `~/dev/automatafl/logic/src/{game,automaton,board}.rs`.
