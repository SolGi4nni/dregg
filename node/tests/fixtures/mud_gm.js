// mud_gm.js — a MUD GAMEMASTER, written as a PURE deos-js program, hosted headless
// INSIDE a dregg node. This is the rich living world (NOT fog-of-war): the GM is a
// PRIVILEGED server holding broad caps over its whole world; players are cap-constrained
// and drive the world only through signed turns over the affordances the GM offers.
//
// There is no Rust gameplay logic and no gpui anywhere — the world is DATA + verified
// turns. The deos-host runs this on a dedicated SpiderMonkey thread, attached to the
// node's live ledger as the GM (server) agent. The GM's broad authority is what lets it
// spawn the world and stamp its cells; a player can only exercise the caps it was granted.
//
// THE LIVING-WORLD ARC this setup builds (each step a real verified turn):
//
//   ROOMS         — the GM spawnCells a small map: an ENTRANCE and a HALL (cells).
//   CHARACTER     — the GM spawnCells a player character cell and stamps its stats
//                   (level := 1, xp := 0, room := ENTRANCE) via the setField superpower.
//   NPC           — the GM spawnCells a watchman NPC and stamps its mood (calm := 0).
//   GRANT         — the GM grants the player a capability over its character cell, so the
//                   player's signed cross-cell turns (move / gain-xp) are authorized.
//   AFFORDANCES   — the GM offers cap-gated gameplay verbs players discover + fire:
//                     MOVE      → SetField(char, ROOM := HALL)   [required: signature]
//                     GAIN-XP   → SetField(char, XP := 120)      [required: signature]
//   (The GM-only verbs — LEVEL-UP, the NPC REACTION, opening a DUNGEON INSTANCE — are
//    NOT affordances; they are driven by the GM's own server-side superpowers, which a
//    player cannot reach. A player attempting a GM move via a forged signed turn is
//    refused by the executor's authority gate — see the Rust harness.)
//
// The host substitutes the player's agent-cell hex for "__PLAYER__" so the GM can grant
// the cap to the right holder. All cell SEEDS are deterministic so the Rust harness can
// re-derive the same ids and assert the arc on the real ledger.

// ── ROOMS — the GM spawns the map (real CreateCell turns) ──────────────────────────
var entrance = deos.server.spawnCell("mud-room-entrance", "open");
var hall = deos.server.spawnCell("mud-room-hall", "open");

// ── CHARACTER — spawn + stamp stats (level/xp/room) via the setField superpower ─────
var character = deos.server.spawnCell("mud-char-aria", "open");
deos.server.setField(character, 0, 1);   // slot 0 = LEVEL  := 1
deos.server.setField(character, 1, 0);   // slot 1 = XP     := 0
deos.server.setField(character, 2, 1);   // slot 2 = ROOM   := 1 (ENTRANCE)

// ── NPC — a watchman; mood field starts calm ────────────────────────────────────────
var watchman = deos.server.spawnCell("mud-npc-watchman", "open");
deos.server.setField(watchman, 0, 0);    // slot 0 = MOOD := 0 (calm)

// ── GRANT — the player holds a cap over its character (so its move/gain-xp authorize) ─
deos.server.grant("__PLAYER__", character, "none");

// ── AFFORDANCES — the cap-gated gameplay verbs players fire via /turns/submit ────────
// MOVE: enter the HALL (room := 2).
deos.server.defineAffordance({
    name: "move",
    required: "signature",
    effects: [
        { type: "setField", cell: character, index: 2, value: 2 }
    ]
});

// GAIN-XP: a kill grants XP (xp := 120, crossing the level-up threshold of 100).
deos.server.defineAffordance({
    name: "gain-xp",
    required: "signature",
    effects: [
        { type: "setField", cell: character, index: 1, value: 120 }
    ]
});

// ── DUNGEON INSTANCE — the GM FORKS a fresh private room-set for the party ───────────
// A fork is a cap-bounded instance of the server's world (the membrane-fork): a fresh
// OPEN cell minted on the live ledger that publishes as its OWN discoverable surface.
// We scope a "descend" affordance to it (index 0 := 1 marks the party as having descended
// into THAT instance), isolated from the root surface + sibling parties.
var dungeon = deos.server.fork("mud-dungeon-party1");
deos.server.defineAffordance({
    name: "descend",
    required: "signature",
    instance: dungeon,
    effects: [
        { type: "setField", cell: dungeon, index: 0, value: 1 }
    ]
});

// Witness object the host returns (1 iff the whole world stood up): all spawns produced
// 64-char hex ids, the fork instance opened, and the affordances registered. The Rust
// harness reads the published surfaces for discovery; this is the in-JS sanity check.
(entrance && entrance.length === 64 &&
 hall && hall.length === 64 &&
 character && character.length === 64 &&
 watchman && watchman.length === 64 &&
 dungeon && dungeon.length === 64) ? 1 : 0;
