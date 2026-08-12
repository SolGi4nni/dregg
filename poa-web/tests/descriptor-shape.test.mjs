import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";
import { test } from "node:test";
import { SHAPES, descriptorShape } from "../src/descriptor-shape.js";

const games = new URL("../../poa/artifacts/poag1/games/", import.meta.url);
const emitted = async (file) => JSON.parse(await readFile(new URL(file, games), "utf8"));

test("every emitted descriptor classifies by shape, not by its game id", async () => {
  const [signal, relay, salvage, blackBox] = await Promise.all([
    emitted("signal-triangulation.json"),
    emitted("relay-repair.json"),
    emitted("salvage-lock.json"),
    emitted("black-box-reconstruction.json"),
  ]);
  assert.equal(descriptorShape(signal), SHAPES.deduction);
  assert.equal(descriptorShape(relay), SHAPES.machineFamily);
  assert.equal(descriptorShape(salvage), SHAPES.parametric);
  assert.equal(descriptorShape(blackBox), SHAPES.probeOracle);

  // Renaming a descriptor does not move it: the shape is read, not declared.
  assert.equal(descriptorShape({ ...relay, game_id: "salvage-lock" }), SHAPES.machineFamily);
  assert.equal(descriptorShape({ ...salvage, game_id: "relay-repair" }), SHAPES.parametric);
});

test("a descriptor with no hidden information is refused, not defaulted", async () => {
  const salvage = await emitted("salvage-lock.json");
  // Collapse every oracle row: what is left is a deterministic machine, which
  // has nothing for a commitment to bind. It must refuse rather than fall back
  // to the nearest consumer.
  const flattened = structuredClone(salvage);
  let collapsed = 0;
  for (const row of flattened.state_machine.transitions) {
    if (row.verdict !== "resolve") continue;
    row.verdict = "accept";
    row.next = row.on_match;
    collapsed += 1;
  }
  assert.equal(collapsed, 1920, "the mutation must actually remove every oracle row");
  assert.throws(() => descriptorShape(flattened), { code: "shape-no-hidden-information" });

  assert.throws(() => descriptorShape({ format: "POAG1-GAME", game_id: "x" }), { code: "shape-unknown" });
  assert.throws(() => descriptorShape({ format: "SOMETHING-ELSE" }), { code: "shape-format" });
  assert.throws(() => descriptorShape(null), { code: "shape-input" });
});

test("the JS router and the Python design gate classify by the same rules", async () => {
  // ⚠ Two implementations of one taxonomy is a mirror unless they are pinned to
  // each other. This reads the gate's own dispatch and checks the discriminators
  // still say what this module says, so a change on either side goes red here
  // rather than drifting into a client that consumes a descriptor the gate never
  // scored — or refuses one it did.
  const gate = await readFile(new URL("../../scripts/poa-design-gate.py", import.meta.url), "utf8");
  const dispatch = gate.slice(gate.indexOf("def pick_backend"), gate.indexOf("def analyse_doc"));
  assert.ok(dispatch.length > 100, "pick_backend must still exist in the design gate");
  assert.match(dispatch, /if "oracle" in doc:\s*\n\s*return ProbeOracleGame/);
  assert.match(dispatch, /if "rules" in doc:\s*\n\s*return DeductionGame/);
  assert.match(dispatch, /if "machines" in sm:\s*\n\s*return MachineFamilyGame/);
  assert.match(dispatch, /verdict"\) == "resolve".*\n?.*return ParametricMachineGame/);
  // …and that it refuses the no-hidden-information case rather than defaulting.
  assert.match(dispatch, /raise Refusal/);

  const router = await readFile(new URL("../src/descriptor-shape.js", import.meta.url), "utf8");
  for (const discriminator of ['"oracle" in doc', '"rules" in doc', '"machines" in machine', '"resolve"']) {
    assert.ok(router.includes(discriminator), `the router lost its ${discriminator} discriminator`);
  }
});
