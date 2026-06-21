// selftest.js — assert the governor stub honors the govStep contract.
//
// These are the harness-side analogs of the Lean theorems:
//   govStep_admits_benign        — floor-preserving move admitted
//   govStep_refuses_only_harmful — floor-breaking move refused
//   sandbox_governed_safe        — under governance, the floor always holds
//
// Run with no dependencies: `node src/governor/selftest.js`.

import assert from "node:assert/strict";
import { governorDecide, worldFloor, BUDGET } from "./governor.js";

async function main() {
  // 1. benign move (post-state within budget) is admitted, unchanged.
  {
    const world = { self: 1 };
    const nextWorld = { self: 0 }; // got safer
    const v = await governorDecide({ world, nextWorld, proposal: {} });
    assert.equal(v.admit, true, "benign move must be admitted");
  }

  // 2. harmful move (post-state breaks the floor) is refused.
  {
    const world = { self: 1 };
    const nextWorld = { self: 99 }; // jumped into lava
    const v = await governorDecide({ world, nextWorld, proposal: {} });
    assert.equal(v.admit, false, "floor-breaking move must be refused");
  }

  // 3. boundary: exactly at budget is still on the floor.
  {
    const v = await governorDecide({
      world: { self: BUDGET },
      nextWorld: { self: BUDGET },
      proposal: {},
    });
    assert.equal(v.admit, true, "dist == BUDGET is within the floor");
  }

  // 4. under governance, applying only admitted moves keeps the floor — the
  //    runnable analog of sandbox_governed_safe over a scripted controller.
  {
    let world = { self: 0 };
    const proposals = [
      { self: 2 },
      { self: 99 }, // would break — must be shielded
      { self: 4 },
      { self: 100 }, // would break — must be shielded
    ];
    for (const nextWorld of proposals) {
      const v = await governorDecide({ world, nextWorld, proposal: {} });
      if (v.admit) world = nextWorld; // apply
      // else: shield — world unchanged
      assert.ok(worldFloor(world), "floor must hold at every governed tick");
    }
  }

  console.log("governor selftest: all assertions passed (govStep contract upheld).");
}

main().catch((err) => {
  console.error("governor selftest FAILED:", err.message);
  process.exit(1);
});
