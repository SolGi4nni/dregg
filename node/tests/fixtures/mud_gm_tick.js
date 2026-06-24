// mud_gm_tick.js — the MUD GAMEMASTER's reactive TICK, a pure deos-js program hosted
// headless inside the dregg node. The host runs this AFTER a player has acted (moved +
// gained XP via signed turns). The GM — holding broad caps over its world — OBSERVES the
// live ledger and reacts. This is the living-world's "the world responds" half:
//
//   LEVEL-UP        — read the character's XP off the real ledger; if it crossed the
//                     threshold (100), apply a LEVEL-UP: a real SetField turn raising the
//                     character's level (and resetting XP). A player cannot do this — it
//                     is the GM's setField superpower over a cell it governs.
//   NPC REACTION    — the watchman REACTS to the player's arrival in the HALL: the GM
//                     fires a SetField raising the watchman's mood (alert).
//   DUNGEON INSTANCE — the GM opens a fresh, private room-set for the party: spawnCell
//                     mints brand-new dungeon-room cells (a dungeon instance is modeled as
//                     a spawned room-set under the GM's authority).
//
// The host substitutes the real character + watchman hexes for "__CHAR__" / "__NPC__".

var XP_THRESHOLD = 100;

// ── observe ── read the character's live XP + room off the ledger.
var xp = deos.server.getField("__CHAR__", 1);
var room = deos.server.getField("__CHAR__", 2);

var leveled = 0;
var reacted = 0;

// ── LEVEL-UP ── XP crossed the threshold ⇒ raise level, reset XP (real turns).
if (xp >= XP_THRESHOLD) {
    var setLevel = deos.server.setField("__CHAR__", 0, 2);   // LEVEL := 2
    var resetXp = deos.server.setField("__CHAR__", 1, 0);    // XP    := 0
    leveled = (setLevel === 1 && resetXp === 1) ? 1 : 0;
}

// ── NPC REACTION ── the player reached the HALL (room 2) ⇒ the watchman goes alert.
if (room === 2) {
    var mood = deos.server.setField("__NPC__", 0, 1);        // MOOD := 1 (alert)
    reacted = (mood === 1) ? 1 : 0;
}

// ── DUNGEON INSTANCE ── the GM FORKS a fresh private instance for a second party
//    (the membrane-fork: a cap-bounded instance cell, its own discoverable surface).
var d1 = deos.server.fork("mud-dungeon-party2");
var d2 = deos.server.spawnCell("mud-dungeon-crypt-party2", "open");
var instanced = (d1 && d1.length === 64 && d2 && d2.length === 64) ? 1 : 0;

// Witness: 1 iff all three GM reactions fired.
(leveled === 1 && reacted === 1 && instanced === 1) ? 1 : 0;
