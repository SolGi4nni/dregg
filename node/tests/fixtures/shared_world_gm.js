// shared_world_gm.js — A LIVE SHARED WORLD two identities co-inhabit, written as a PURE
// deos-js program hosted headless INSIDE a dregg node. This is the first REAL rung of
// MULTI-PERSON deos: not two isolated forks, but ONE space whose cells BOTH parties hold
// caps over and co-act in, every act a real verified turn on the single ledger.
//
// THE WORLD (a shared "board" — think a room with a shared whiteboard + two seats):
//
//   BOARD       — the GM spawnCells a shared board cell. Its fields are the shared state
//                 both identities write: slot 0 = a turn counter (how many posts landed),
//                 slot 1 = the last value posted by A, slot 2 = the last value posted by B.
//                 BOTH identities are granted a cap over THIS cell — it is genuinely shared.
//   SEAT A / B  — a presence cell per identity (slot 0 = "present" flag, slot 1 = a posted
//                 value). The GM grants each identity a cap over its OWN seat. This is the
//                 attribution+presence substrate: a connected identity flips its seat's
//                 present flag, and its posts stamp its seat.
//   PRIVATE-A   — a cell ONLY identity A is granted a cap over. Identity B can SEE it
//                 (discover the affordance) but a B-signed turn writing it is REFUSED by
//                 the executor's authority gate — the over-reach proof.
//
// AFFORDANCES (cap-gated verbs both identities discover + fire as signed turns):
//   present     → SetField(seat, PRESENT := 1)   — announce yourself in the room.
//   post        → SetField(board, ...)            — write the shared board (the co-act).
//   touch-private → SetField(privateA, ...)       — only A's cap authorizes; B is refused.
//
// The host substitutes each identity's agent-cell hex for "__PLAYER_A__" / "__PLAYER_B__"
// so the GM grants the right holders. The Rust harness re-derives the same deterministic
// cell ids and asserts the shared state evolves for BOTH, live, every turn attributed.

// ── THE SHARED BOARD — the one cell both identities co-write ─────────────────────────
var board = deos.server.spawnCell("shared-world-board", "open");
deos.server.setField(board, 0, 0);   // slot 0 = POST COUNT := 0
deos.server.setField(board, 1, 0);   // slot 1 = LAST FROM A := 0
deos.server.setField(board, 2, 0);   // slot 2 = LAST FROM B := 0

// ── SEATS — a presence cell per identity (the attribution+presence substrate) ────────
var seatA = deos.server.spawnCell("shared-world-seat-a", "open");
deos.server.setField(seatA, 0, 0);   // slot 0 = PRESENT := 0
deos.server.setField(seatA, 1, 0);   // slot 1 = LAST POSTED := 0
var seatB = deos.server.spawnCell("shared-world-seat-b", "open");
deos.server.setField(seatB, 0, 0);
deos.server.setField(seatB, 1, 0);

// ── PRIVATE-A — a cell ONLY identity A may write (the over-reach foil) ────────────────
var privateA = deos.server.spawnCell("shared-world-private-a", "open");
deos.server.setField(privateA, 0, 0); // slot 0 = TOUCHED := 0

// ── GRANTS — wire each identity to the cells it may co-act on ──────────────────────────
// BOTH identities hold a cap over the SHARED board (the heart of "one shared world").
deos.server.grant("__PLAYER_A__", board, "none");
deos.server.grant("__PLAYER_B__", board, "none");
// Each identity holds a cap over its OWN seat only.
deos.server.grant("__PLAYER_A__", seatA, "none");
deos.server.grant("__PLAYER_B__", seatB, "none");
// PRIVATE-A: ONLY identity A is granted a cap. Identity B is deliberately NOT granted one,
// so a B-signed write of privateA is refused by the executor's authority gate.
deos.server.grant("__PLAYER_A__", privateA, "none");

// ── AFFORDANCES — the cap-gated co-act verbs both identities discover + fire ──────────
// PRESENT: announce yourself (the harness supplies the seat cell as the effect target;
// the surface advertises the verb, the holder supplies the concrete effect it is capped for).
deos.server.defineAffordance({
    name: "present",
    required: "signature",
    effects: [
        { type: "setField", cell: seatA, index: 0, value: 1 }
    ]
});

// POST: write the shared board. The advertised effect is illustrative; each identity fires
// `post` with its OWN concrete effects (bump the count, stamp its lane + its seat) — all on
// cells it holds caps over, so the executor authorizes each.
deos.server.defineAffordance({
    name: "post",
    required: "signature",
    effects: [
        { type: "setField", cell: board, index: 0, value: 1 }
    ]
});

// TOUCH-PRIVATE: write privateA. Both identities can DISCOVER this verb, but only A's cap
// authorizes the fire; a B-signed touch is refused — the receipted over-reach.
deos.server.defineAffordance({
    name: "touch-private",
    required: "signature",
    effects: [
        { type: "setField", cell: privateA, index: 0, value: 1 }
    ]
});

// Witness object the host returns (1 iff the whole shared world stood up): every spawn
// produced a 64-char hex id and the affordances registered.
(board && board.length === 64 &&
 seatA && seatA.length === 64 &&
 seatB && seatB.length === 64 &&
 privateA && privateA.length === 64) ? 1 : 0;
