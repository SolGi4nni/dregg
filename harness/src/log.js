// log.js — a verifiable receipt of every governed step.
//
// One line per tick: the proposal, the floor projection before/after, and the
// governor's admit/refuse verdict + reason. This is the audit trail — it makes
// the seam observable: you can read off exactly which moves were shielded and
// why, and confirm that no refused move ever changed the world.

export function logStep({ world, nextWorld, proposal, verdict }) {
  const tag = verdict.admit ? "ADMIT" : "REFUSE";
  const arrow = verdict.admit ? "applied" : "shielded (world unchanged)";
  console.log(
    `[${tag}] action=${proposal.action}` +
      (proposal.arg ? `(${proposal.arg})` : "") +
      ` world=${JSON.stringify(world)} -> ${JSON.stringify(nextWorld)}` +
      ` | ${arrow} | ${verdict.backend}: ${verdict.reason}` +
      ` | rationale: ${proposal.rationale ?? "-"}`,
  );
}
