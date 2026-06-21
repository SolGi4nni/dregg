// world.js — project live Minecraft state onto the governor's public model,
// and simulate what a proposed action WOULD do (without touching the game).
//
// The governor reasons over `AgentId -> dist` where dist is "how far from a
// bounded-exit / safe state" (see governor.js, mirroring PolisSandbox.World).
// We keep that projection deliberately thin and motive-free: it is the only
// thing the verified decision ever sees.
//
// The mapping below is illustrative — a real deployment tunes which game
// quantities constitute "the floor". The point of the harness is the SEAM and
// the loop, not this particular health/distance heuristic.

/**
 * Read the current public projection from the bot's view of the world.
 *
 * "self" is the bot. We model its dist as a blend of danger signals:
 *   - low health raises dist (closer to losing its bounded exit = death)
 *   - being far below safe light / underground could be added here too.
 *
 * Other tracked players could be added (so the governor can refuse the bot
 * dominating THEM — the politician case), but the skeleton models self only.
 *
 * @param {import('mineflayer').Bot} bot
 * @returns {Record<string, number>}
 */
export function observeWorld(bot) {
  const health = bot.health ?? 20; // 0..20
  const food = bot.food ?? 20; // 0..20

  // dist 0 == fully safe; grows as health/food drop. Tuned so that a healthy
  // bot sits comfortably under BUDGET (5) and a near-death bot exceeds it.
  const selfDist = Math.max(
    0,
    Math.round((20 - health) / 2) + Math.round((20 - food) / 6),
  );

  return { self: selfDist };
}

/**
 * Simulate the public-projection effect of a proposed action — the "nextWorld"
 * the governor checks. We do NOT execute anything here; we predict the move's
 * effect on the floor-relevant quantities so the governor can decide first.
 *
 * The simulation is intentionally conservative: if we can't predict an action's
 * effect, we assume it does not improve the floor (so risky/unknown actions are
 * judged on the current state, and clearly-dangerous ones are caught).
 *
 * @param {Record<string, number>} world current projection
 * @param {object} proposal              the LLM's proposed action
 * @returns {Record<string, number>}
 */
export function simulateAction(world, proposal) {
  const next = { ...world };

  switch (proposal.action) {
    case "eat":
      // eating restores food -> lowers dist a little
      next.self = Math.max(0, next.self - 1);
      break;
    case "flee":
    case "retreat":
      // moving to safety lowers dist
      next.self = Math.max(0, next.self - 2);
      break;
    case "attack_entity":
    case "dig_down":
      // aggressive / risky actions raise dist (you expose yourself)
      next.self = next.self + 3;
      break;
    case "jump_into_lava": // the obvious self-domination move
      next.self = 99;
      break;
    case "wait":
    case "look_around":
    case "chat":
    default:
      // benign / unknown: no predicted change to the floor projection
      break;
  }

  return next;
}
