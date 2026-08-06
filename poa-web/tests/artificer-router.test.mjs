/**
 * The two routers, on the same bytes.
 *
 * ⚑ WHY THIS EXISTS.  Artificer Logic was written by one lane, and that lane
 * decided BOTH where the descriptor routes in `descriptor-shape.js` and where it
 * routes in `scripts/poa-design-gate.py`.  One author against one set of bytes is
 * one source wearing two hats: if the author had a wrong idea about the shape,
 * both sides would carry it and agree with each other about a mistake.
 *
 * So this asks them separately and compares.  `descriptor-shape.js:8-12` states
 * the invariant the two files are supposed to hold — "if a fifth shape appears,
 * BOTH refuse until somebody teaches them" — and the artificer descriptor is the
 * case that tests it, because it LOOKS like a new shape (it carries a published
 * rule manual no other game has) and is not one: its rows resolve, so it is a
 * parametric machine, and the induction analysis is a rule MODEL on top rather
 * than a new backend.
 *
 * ⚠ The check runs on a minimal descriptor with the artificer's structural
 * signature rather than on the emitted artifact, because the emitted artifact has
 * no tracked home yet — it is written to `poa/artifacts/poag1-pending/` and is not
 * in the signed bundle.  When it is enrolled, the right upgrade is to feed the
 * real bytes here.  A version that SKIPPED when the artifact was absent would be a
 * gate that cannot go red, which is worse than this.
 */
import { strict as assert } from "node:assert";
import { execFileSync } from "node:child_process";
import { readFileSync } from "node:fs";
import test from "node:test";
import { fileURLToPath } from "node:url";
import { descriptorShape } from "../src/descriptor-shape.js";

const REPO = fileURLToPath(new URL("../..", import.meta.url));
const GATE = `${REPO}scripts/poa-design-gate.py`;

/** The artificer's structural signature: a rule manual AND resolving rows. */
function artificerShaped() {
  return {
    format: "POAG1-GAME",
    schema_version: 1,
    game_id: "artificer-logic",
    ruleset: "artificer-v1",
    engine_module: "Dregg2.Games.PathOfAngels.ArtificerLogic",
    action_limit: 5,
    security: {},
    instance: {},
    manual: { rules: [], charges: [] },
    practice: {},
    state_machine: {
      initial_state: "s0",
      states: [],
      actions: [],
      transitions: [{ state: "s0", action: "a", verdict: "resolve" }],
    },
    output: {},
  };
}

/** Ask the design gate, in its own process, which backend it picks. */
function pythonBackend(doc) {
  const script =
    "import importlib.util,json,sys\n" +
    `spec=importlib.util.spec_from_file_location('g',${JSON.stringify(GATE)})\n` +
    "m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)\n" +
    "doc=json.load(sys.stdin)\n" +
    "print(m.pick_backend(doc).__name__)\n" +
    "print(m.PARAMETRIC_RULE_MODELS.get(doc['ruleset'],lambda:0).__name__)\n";
  // stderr piped, not inherited: two of the checks below EXPECT a refusal, and a
  // traceback on the console reads like a broken suite rather than a working one.
  return execFileSync("python3", ["-c", script], {
    input: JSON.stringify(doc),
    encoding: "utf8",
    stdio: ["pipe", "pipe", "pipe"],
  }).trim().split("\n");
}

test("the artificer descriptor routes the same way in both routers", () => {
  const doc = artificerShaped();
  const js = descriptorShape(doc);
  const [backend, model] = pythonBackend(doc);

  // The JS says parametric; the gate must reach the parametric backend too.
  assert.equal(js, "parametric");
  assert.equal(backend, "ParametricMachineGame");
  // ...and the induction analysis must be reached, or the table is measured by
  // nothing: an unregistered ruleset is refused, but a ruleset registered to the
  // WRONG model would be analysed by another game's semantics.
  assert.equal(model, "_artificer_differential");
});

test("a rule manual alone does not make a new shape in either router", () => {
  // Strip the resolving row: the manual block is still there, and BOTH sides must
  // now refuse rather than one of them inventing a fifth shape from the manual.
  const doc = artificerShaped();
  doc.state_machine.transitions = [{ state: "s0", action: "a", verdict: "accept" }];
  assert.throws(() => descriptorShape(doc), /no hidden information/);
  assert.throws(() => pythonBackend(doc), /Refusal|no hidden information/);
});

test("the emitted manual block is not what either router keys on", () => {
  // Remove the manual entirely and the shape is unchanged, which is the whole
  // claim: the manual is a rule MODEL selector (via `ruleset`), not a shape.
  const doc = artificerShaped();
  delete doc.manual;
  assert.equal(descriptorShape(doc), "parametric");
  assert.equal(pythonBackend(doc)[0], "ParametricMachineGame");
});

test("the design gate refuses a parametric table whose ruleset it cannot rebuild", () => {
  const doc = artificerShaped();
  doc.ruleset = "not-a-registered-ruleset";
  assert.equal(descriptorShape(doc), "parametric");
  const [backend, model] = pythonBackend(doc);
  assert.equal(backend, "ParametricMachineGame");
  assert.equal(model, "<lambda>");
});

test("the gate source declares exactly the rulesets it can rebuild", () => {
  const source = readFileSync(GATE, "utf8");
  const block = source.match(/PARAMETRIC_RULE_MODELS = \{([^}]*)\}/);
  assert.ok(block, "PARAMETRIC_RULE_MODELS is not where this test expects it");
  assert.match(block[1], /"artificer-v1": ParametricMachineGame\._artificer_differential/);
});
