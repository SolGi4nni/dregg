// actuator.js — applies an ADMITTED action to the live bot. This is the only
// code that mutates the world, and it is only ever reached for moves the
// governor admitted. A refused move never gets here.
//
// Each branch is a thin wrapper over Mineflayer. Unknown/benign actions are
// no-ops on the bot side (the agent still "did" them in the projection).

/**
 * @param {import('mineflayer').Bot} bot
 * @param {{action: string, arg?: string}} proposal
 */
export async function applyAction(bot, proposal) {
  switch (proposal.action) {
    case "chat":
      bot.chat(proposal.arg ?? "hello");
      return;

    case "eat":
      // Requires a food item equipped; guarded so the skeleton doesn't throw.
      if (bot.food < 20) {
        try {
          await bot.consume?.();
        } catch {
          /* no food equipped — skeleton stays alive */
        }
      }
      return;

    case "flee":
    case "retreat": {
      // Walk a few blocks away from the nearest hostile, if any.
      const hostile = bot.nearestEntity?.((e) => e.kind === "Hostile mobs");
      if (hostile) {
        const dx = bot.entity.position.x - hostile.position.x;
        const dz = bot.entity.position.z - hostile.position.z;
        bot.lookAt?.(bot.entity.position.offset(dx, 0, dz));
      }
      bot.setControlState?.("forward", true);
      setTimeout(() => bot.setControlState?.("forward", false), 800);
      return;
    }

    case "attack_entity": {
      const target = bot.nearestEntity?.((e) => e.type === "mob");
      if (target) bot.attack?.(target);
      return;
    }

    case "look_around":
      bot.look?.(Math.random() * Math.PI * 2, 0, true);
      return;

    case "wait":
    default:
      // no-op
      return;

    // NOTE: dig_down / jump_into_lava are deliberately NOT actuated here.
    // They exist so the agent CAN propose them and the governor CAN refuse
    // them — demonstrating the seam. If you choose to actuate dig_down, do it
    // behind the governor (which it already is) and add a real implementation.
  }
}
