// governor.js — THE SEAM.
//
// This is the one place where a proposed agent action meets the verified polis
// decision. Everything upstream (observe, LLM-propose) produces a candidate
// move; everything downstream (apply, log) only ever sees an ADMITTED move.
// The governor is the cage; the LLM is the animal. We verify the cage.
//
// The decision we enforce is `govStep` from
//   metatheory/Metatheory/PolisSandbox.lean
// in plain words:
//
//   admit the proposed move IFF executing it preserves the shared floor;
//   otherwise SHIELD (refuse — the world is left unchanged).
//
// and its two gentleness theorems (PolisSandboxRun.lean):
//   - govStep_admits_benign     : a floor-preserving move is admitted UNCHANGED.
//   - govStep_refuses_only_harmful : every refusal is a genuine floor break.
//
// So: honest play is never blocked, only genuine domination is refused, and the
// floor holds for EVERY controller (sandbox_governed_safe) — not just the one we
// happened to test.
//
// There are TWO interchangeable backends, selected by env:
//   GOVERNOR_BACKEND=stub   (default) — a faithful JS re-implementation of the
//                                       floor check. Self-contained; runs with no
//                                       Lean toolchain. NOT the proof; a mirror.
//   GOVERNOR_BACKEND=lean   — shells out to a Lean executable that decides admit/
//                             refuse using the SAME kernel-checked govStep. This is
//                             the seam where the *verified* artifact replaces the
//                             mirror. See governor-lean/README.md.
//
// The contract both backends honor is identical, so the agent loop never changes
// when you swap the mirror for the proof.

import { execFile } from "node:child_process";
import { promisify } from "node:util";

const execFileP = promisify(execFile);

// ---------------------------------------------------------------------------
// The world model the governor reasons over.
//
// In PolisSandbox the World is `AgentId -> Nat` (each agent's distance-to-home)
// and the floor is "every agent stays within recovery budget". For a Minecraft
// harness we keep the SAME shape — a public, motive-free projection of state —
// but the quantities are read off the live game:
//
//   For each tracked agent (the bot, and any others we model):
//     dist  : a non-negative integer "distance from its bounded-exit / safe
//             state". Larger = closer to being dominated / stuck.
//
// The floor: every tracked agent has dist <= BUDGET.
// A move is a proposed change to this projection (what the action WOULD do).
//
// This is deliberately small and decidable — exactly so `decide` tells the truth
// and the Lean side can mirror it byte-for-byte.
// ---------------------------------------------------------------------------

export const BUDGET = 5; // == PolisSandbox.budget

/** worldFloor: every tracked agent is within recovery budget. */
export function worldFloor(world) {
  return Object.values(world).every((dist) => dist <= BUDGET);
}

const backend = process.env.GOVERNOR_BACKEND ?? "stub";

/**
 * Decide whether a proposed action is admitted.
 *
 * @param {object} ctx
 * @param {Record<string, number>} ctx.world      current public projection
 * @param {Record<string, number>} ctx.nextWorld  projection AFTER the action
 * @param {object} ctx.proposal                    the LLM's proposed action (opaque to the governor)
 * @returns {Promise<{admit: boolean, reason: string, backend: string}>}
 */
export async function governorDecide(ctx) {
  if (backend === "lean") return decideViaLean(ctx);
  return decideViaStub(ctx);
}

// --- stub backend: faithful mirror of govStep -------------------------------

function decideViaStub({ world, nextWorld }) {
  // govStep: admit iff the post-state preserves the floor, else shield.
  if (worldFloor(nextWorld)) {
    return Promise.resolve({
      admit: true,
      reason: "post-state preserves the shared floor (govStep_admits_benign)",
      backend: "stub",
    });
  }
  // Identify which agent(s) the move would push below the floor — honest reason.
  const broken = Object.entries(nextWorld)
    .filter(([, d]) => d > BUDGET)
    .map(([a, d]) => `${a}: ${d} > ${BUDGET}`)
    .join(", ");
  return Promise.resolve({
    admit: false,
    reason: `move breaks the floor (${broken}) — shielded (govStep_refuses_only_harmful)`,
    backend: "stub",
  });
}

// --- lean backend: shell out to the verified decision -----------------------
//
// The Lean executable is expected to read a one-line JSON proposal on stdin and
// print a one-line JSON verdict on stdout: {"admit": bool, "reason": "..."}.
// Its admit logic is `govStep` — the SAME definition the theorems are about — so
// the verdict here is backed by `sandbox_governed_safe`, not by this file.

async function decideViaLean(ctx) {
  const exe = process.env.GOVERNOR_LEAN_EXE; // e.g. .lake/build/bin/polis_governor
  if (!exe) {
    throw new Error(
      "GOVERNOR_BACKEND=lean but GOVERNOR_LEAN_EXE is unset. See governor-lean/README.md.",
    );
  }
  const input = JSON.stringify({
    world: ctx.world,
    nextWorld: ctx.nextWorld,
    budget: BUDGET,
  });
  const { stdout } = await execFileP(exe, [], { input, timeout: 5000 });
  const verdict = JSON.parse(stdout.trim());
  return {
    admit: Boolean(verdict.admit),
    reason: verdict.reason ?? "(lean)",
    backend: "lean",
  };
}
