import { ArtifactRefusal } from "./poag1.js";

/**
 * Which SHAPE a POAG1 descriptor is, decided by reading it — never by its
 * `game_id`, so a descriptor cannot pick its own consumer by renaming itself.
 *
 * This mirrors `pick_backend` in scripts/poa-design-gate.py, deliberately and
 * name-for-name — INCLUDING THE ORDER IT TESTS IN, because a descriptor carrying
 * two of these keys must land in the same place on both sides. That gate already
 * classifies every emitted descriptor into the same shapes before it will score
 * one, so the taxonomy is not something this client invented: it is the one the
 * emitter is already held to. Keeping the two in step is the point — if a NEW
 * shape appears, BOTH refuse until somebody teaches them, rather than one of them
 * quietly guessing.
 *
 *   deduction       an instances-by-guesses feedback matrix          (Signal)
 *   probe-oracle    an instances-by-probes answer matrix             (Black Box)
 *   machine-family  one complete machine per instance                (Relay)
 *   parametric      one machine whose rows may defer to the instance (Salvage,
 *                                                                     Artificer)
 *   push-your-luck  a published hazard ladder over a hidden reward   (Vent Crawl)
 *   machine         one deterministic machine, no hidden information — REFUSED,
 *                   because there is nothing for a commitment to bind
 *
 * ⚑ `push-your-luck` was the FIFTH shape, and it is the case the invariant above
 * was written for. The gate learned `vent` (`PushYourLuckGame`, `pick_backend`)
 * while this file still held four, so `descriptorShape` refused the emitted vent
 * descriptor with `shape-no-hidden-information` — correctly, because its rows
 * carry `accept`/`refuse`/`wager` and no `resolve`, and NOTHING here had been
 * taught that a wager is hidden information. The invariant held; the debt was
 * one-sided, and this is it paid. A `wager` row publishes the exact hazard
 * numerator and enumerates one successor per still-possible table, so what is
 * hidden is WHICH table — the reward — rather than which state.
 *
 * ⚠ WHAT THIS BUYS, precisely. Shape determines the MECHANICS: how to validate a
 * descriptor, how to hold a run, what a practice oracle is, what goes in the
 * transcript. It does not determine PRESENTATION — labels, board layout, the
 * copy that tells a player what they are looking at. A new game that lands in an
 * existing shape needs no new runtime and no new controller, only a presentation
 * record. A new game that lands in a NEW shape needs both, and should.
 *
 * That presentation record is a real thing now, not a gesture: `game-rack.js`
 * holds one per game and checks its claimed shape against what this file decides
 * about the emitted descriptor, so a card cannot advertise mechanics the
 * descriptor does not have.
 */

const SHAPES = Object.freeze({
  deduction: "deduction",
  probeOracle: "probe-oracle",
  machineFamily: "machine-family",
  parametric: "parametric",
  pushYourLuck: "push-your-luck",
});

function refuse(condition, code, message) {
  if (!condition) throw new ArtifactRefusal(code, message);
}

export function descriptorShape(doc) {
  refuse(doc !== null && typeof doc === "object" && !Array.isArray(doc), "shape-input", "a descriptor object is required");
  refuse(doc.format === "POAG1-GAME", "shape-format", `${doc.game_id ?? "descriptor"} is not a POAG1-GAME descriptor`);
  // ⚠ The three key tests come BEFORE the state-machine ones and in exactly the
  // order `pick_backend` uses. A vent descriptor also has a `state_machine`, so a
  // reordering here would route it somewhere the gate does not.
  if ("oracle" in doc) return SHAPES.probeOracle;
  if ("rules" in doc) return SHAPES.deduction;
  if ("vent" in doc) return SHAPES.pushYourLuck;
  const machine = doc.state_machine;
  refuse(machine !== null && typeof machine === "object" && !Array.isArray(machine), "shape-unknown", `${doc.game_id} carries no analysable shape`);
  if ("machines" in machine) return SHAPES.machineFamily;
  if (Array.isArray(machine.transitions) && machine.transitions.some((row) => row?.verdict === "resolve")) return SHAPES.parametric;
  refuse(
    false,
    "shape-no-hidden-information",
    `${doc.game_id} carries a deterministic single machine with no oracle row and no board family: ` +
      "it has no hidden information, so there is nothing for a commitment to bind",
  );
}

export { SHAPES };
