// gm.js — a GAMEMASTER private server program, hosted headless INSIDE a dregg node.
//
// The deos-host runs this on a dedicated SpiderMonkey thread, attached to the node's
// live ledger as the server (GM) agent. The host has already minted an OPEN door cell
// and substituted its hex id for "__DOOR__" below (the host owns the open-perms mint +
// the player grant, so a player's cross-cell write is authorized). The program's setup:
//
//   1. exercises a GM SUPERPOWER — spawnCell mints a fresh "lever" cell (a real
//      CreateCell verified turn committed through the host); and
//   2. registers a cap-gated "knock" affordance carrying a real SetField effect on the
//      door cell. A player who holds `signature` (and the granted door cap) discovers +
//      fires "knock" through the node's /turns/submit ingress — flipping the door's
//      field on the real ledger.
//
// Everything here is DATA + verified turns; there is no gpui anywhere.

// (1) GM superpower: mint a lever cell (a real CreateCell turn). Returns its id hex.
var lever = deos.server.spawnCell("gm-lever", "open");

// (2) Register the cap-gated "knock" affordance: fire ⇒ SetField(door, slot 0 := 1).
deos.server.defineAffordance({
    name: "knock",
    required: "signature",
    effects: [
        { type: "setField", cell: "__DOOR__", index: 0, value: 1 }
    ]
});

// Witness: 1 iff the lever spawned (a 64-char hex id) — proves the GM superpower
// committed a real CreateCell turn during setup.
(lever && lever.length === 64) ? 1 : 0;
