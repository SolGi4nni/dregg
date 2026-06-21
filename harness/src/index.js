// index.js — the governed agent loop.
//
//   connect bot
//     └─ loop:
//          observe world ──▶ LLM proposes action ──▶ GOVERNOR decides ──┬─ admit ─▶ apply ─▶ log
//                                                                       └─ refuse ──────────▶ log (world unchanged)
//
// The governor is the seam where the verified polis decision (PolisSandbox.govStep,
// proven safe by sandbox_governed_safe) replaces a hand-rolled check. The loop
// itself never inspects the agent's motive — it only ever applies admitted moves.
//
// WHAT RUNS WITHOUT EXTERNAL DEPENDENCIES:
//   - the governor (stub backend) — `node src/governor/selftest.js`
//   - the loop's structure / dry-run — `DRY_RUN=1 node src/index.js`
// WHAT NEEDS A SERVER + KEY:
//   - the live loop needs a reachable Minecraft server (MC_HOST/MC_PORT) AND
//     ANTHROPIC_API_KEY. Without them, run the dry run or the selftest.

import { governorDecide } from "./governor/governor.js";
import { observeWorld, simulateAction } from "./world.js";
import { logStep } from "./log.js";

const TICK_MS = Number(process.env.TICK_MS ?? 4000);
const DRY_RUN = process.env.DRY_RUN === "1";

// agent.js (Anthropic SDK) and actuator.js are imported lazily in live mode only,
// so the no-deps dry-run / selftest paths never require them to be installed.
async function governedTick(bot) {
  const { proposeAction } = await import("./agent.js");
  const { applyAction } = await import("./actuator.js");

  // 1. observe
  const world = observeWorld(bot);
  const observation = {
    world,
    health: bot.health,
    food: bot.food,
    position: bot.entity?.position
      ? { x: bot.entity.position.x, y: bot.entity.position.y, z: bot.entity.position.z }
      : null,
    time: bot.time?.timeOfDay ?? null,
  };

  // 2. LLM proposes
  const proposal = await proposeAction(observation);

  // 3. simulate + govern (THE SEAM)
  const nextWorld = simulateAction(world, proposal);
  const verdict = await governorDecide({ world, nextWorld, proposal });

  // 4. apply iff admitted; else shield (world unchanged)
  if (verdict.admit) {
    await applyAction(bot, proposal);
  }

  // 5. log
  logStep({ world, nextWorld, proposal, verdict });
}

async function main() {
  if (DRY_RUN) {
    // Exercise the loop wiring with a fake bot and a fake agent — no server,
    // no API key. Proves the structure end-to-end.
    const { runDryRun } = await import("./dryrun.js");
    await runDryRun();
    return;
  }

  // Live mode: requires a Minecraft server and ANTHROPIC_API_KEY.
  const mineflayer = (await import("mineflayer")).default;
  const bot = mineflayer.createBot({
    host: process.env.MC_HOST ?? "localhost",
    port: Number(process.env.MC_PORT ?? 25565),
    username: process.env.MC_USERNAME ?? "polis-agent",
    auth: process.env.MC_AUTH ?? "offline",
  });

  bot.once("spawn", () => {
    console.log("[harness] bot spawned; starting governed loop");
    const interval = setInterval(async () => {
      try {
        await governedTick(bot);
      } catch (err) {
        console.error("[harness] tick error:", err.message);
      }
    }, TICK_MS);
    bot.once("end", () => clearInterval(interval));
  });

  bot.on("error", (err) => console.error("[harness] bot error:", err.message));
  bot.on("kicked", (reason) => console.error("[harness] kicked:", reason));
}

main().catch((err) => {
  console.error("[harness] fatal:", err);
  process.exit(1);
});
