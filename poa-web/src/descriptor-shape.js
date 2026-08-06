import { ArtifactRefusal } from "./poag1.js";

/**
 * Which SHAPE a POAG1 descriptor is, decided by reading it — never by its
 * `game_id`, so a descriptor cannot pick its own consumer by renaming itself.
 *
 * This mirrors `pick_backend` in scripts/poa-design-gate.py, deliberately and
 * name-for-name. That gate already classifies every emitted descriptor into the
 * same five shapes before it will score one, so the taxonomy is not something
 * this client invented: it is the one the emitter is already held to. Keeping
 * the two in step is the point — if a fifth shape appears, BOTH refuse until
 * somebody teaches them, rather than one of them quietly guessing.
 *
 *   deduction       an instances-by-guesses feedback matrix          (Signal)
 *   probe-oracle    an instances-by-probes answer matrix             (Black Box)
 *   machine-family  one complete machine per instance                (Relay)
 *   parametric      one machine whose rows may defer to the instance (Salvage)
 *   machine         one deterministic machine, no hidden information — REFUSED,
 *                   because there is nothing for a commitment to bind
 *
 * ⚠ WHAT THIS BUYS, precisely. Shape determines the MECHANICS: how to validate a
 * descriptor, how to hold a run, what a practice oracle is, what goes in the
 * transcript. It does not determine PRESENTATION — labels, board layout, the
 * copy that tells a player what they are looking at. A new game that lands in an
 * existing shape needs no new runtime and no new controller, only a presentation
 * record. A new game that lands in a NEW shape needs both, and should.
 */

const SHAPES = Object.freeze({
  deduction: "deduction",
  probeOracle: "probe-oracle",
  machineFamily: "machine-family",
  parametric: "parametric",
});

function refuse(condition, code, message) {
  if (!condition) throw new ArtifactRefusal(code, message);
}

export function descriptorShape(doc) {
  refuse(doc !== null && typeof doc === "object" && !Array.isArray(doc), "shape-input", "a descriptor object is required");
  refuse(doc.format === "POAG1-GAME", "shape-format", `${doc.game_id ?? "descriptor"} is not a POAG1-GAME descriptor`);
  if ("oracle" in doc) return SHAPES.probeOracle;
  if ("rules" in doc) return SHAPES.deduction;
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
