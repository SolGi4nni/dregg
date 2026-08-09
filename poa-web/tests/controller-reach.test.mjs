import assert from "node:assert/strict";
import { readFile, readdir } from "node:fs/promises";
import { test } from "node:test";
import { INSTALLED_GAME_IDS } from "../src/mission-launcher.js";

/**
 * ⚑ THE HOLE THIS CLOSES, AND IT HID TWO COMPLETE GAMES FOR A DAY.
 *
 * `artificer-controller.js` (103 lines) + `artificer-runtime.js` (372) and
 * `ventcrawl-controller.js` (268) + `ventcrawl-runtime.js` (482) were written,
 * finished, and imported BY NOTHING BUT EACH OTHER. Every gate in this suite was
 * green the entire time, and each one was green for a good reason:
 *
 *   - `module-graph.test.mjs` checks that every relative import RESOLVES to a real
 *     export. An orphan module imports nothing that is missing, so it passes.
 *   - the per-module tests exercise the modules that HAVE tests. An orphan has
 *     none, so there is nothing to fail.
 *   - `mission-launch.test.mjs` checks the dispatch table dispatches. A controller
 *     absent from that table is absent from the test too.
 *
 * Every one of those asks "is what is here correct?" and none asks "is what is
 * here REACHED?" — so a module could be perfect and dead at the same time, and the
 * suite could not tell the difference. That is the defect class, and it is not
 * specific to controllers: an entry point is the only thing that makes a module
 * part of the product.
 *
 * Two statements, then:
 *
 *   1. every `*-controller.js` is REACHED from the page that is supposed to mount
 *      it, by a transitive walk of the real import graph;
 *   2. every game the launcher INSTALLS has a descriptor loader in `app.js`, so a
 *      card the rack renders playable cannot reach the launcher with nothing to
 *      feed it.
 *
 * ⚠ (2) is not hypothetical either. Black Box's controller was installed, its
 * mission was in the signed catalog, and `boot` loaded three descriptors by hand
 * — signal, relay, salvage. Its card therefore rendered `open`, and one click
 * refused into `sealAuthority`, sealing the whole terminal. Two hand-maintained
 * lists had stopped agreeing and nothing compared them.
 */

const web = new URL("../", import.meta.url);
const IMPORT = /(?:^|[\s;=({[,])(?:import|export)\s*(?:[\w${}*,\s]*?\s*from\s*)?["']([^"']+)["']/g;
const DYNAMIC_IMPORT = /\bimport\s*\(\s*["']([^"']+)["']\s*\)/g;

/** Every relative specifier a source file names, static or dynamic. */
function specifiersOf(source) {
  const found = new Set();
  for (const pattern of [IMPORT, DYNAMIC_IMPORT]) {
    for (const match of source.matchAll(pattern)) {
      if (match[1].startsWith(".")) found.add(match[1]);
    }
  }
  return [...found];
}

/**
 * The transitive closure of one entry point, as repo-relative paths.
 *
 * `overrides` lets a test substitute a MUTATED source for one file without
 * touching the tree, which is how the falsifier below runs the real walk over the
 * real defect rather than asserting the walk's parts.
 */
async function reachableFrom(entry, overrides = new Map()) {
  const seen = new Set();
  const queue = [entry];
  while (queue.length > 0) {
    const path = queue.shift();
    if (seen.has(path)) continue;
    seen.add(path);
    const source = overrides.get(path) ?? await readFile(new URL(path, web), "utf8");
    for (const specifier of specifiersOf(source)) {
      const resolved = new URL(specifier, new URL(path, web));
      queue.push(resolved.href.slice(web.href.length));
    }
  }
  return seen;
}

/** Every `*-controller.js` in the tree, with the entry that must reach it. */
async function controllersByEntry() {
  const pairs = [];
  for (const [dir, entry] of [["src", "src/app.js"], ["labs", null]]) {
    for (const file of await readdir(new URL(`${dir}/`, web))) {
      if (!file.endsWith("-controller.js")) continue;
      // A lab is its own page, so its controller's entry is its own lab script.
      const owner = entry ?? `labs/${file.replace("-controller.js", ".js")}`;
      pairs.push({ module: `${dir}/${file}`, entry: owner });
    }
  }
  return pairs;
}

test("every controller module is reached from the page that mounts it", async () => {
  const pairs = await controllersByEntry();
  assert.ok(pairs.length >= 10, "the controller census should not have shrunk silently");
  const closures = new Map();
  const orphans = [];
  for (const { module, entry } of pairs) {
    if (!closures.has(entry)) closures.set(entry, await reachableFrom(entry));
    if (!closures.get(entry).has(module)) orphans.push(`${module} is imported by nothing reachable from ${entry}`);
  }
  assert.deepEqual(orphans, []);
});

/**
 * ⚑ THE GENERALIZATION THE TEST ABOVE ASKED FOR AND DID NOT MAKE.
 *
 * Its own header says the defect class "is not specific to controllers: an entry
 * point is the only thing that makes a module part of the product" — and then it
 * filters to `*-controller.js`. So a census run against this tree found an orphan
 * the controller gate is structurally unable to see:
 * `src/dregg-wallet-verification.js`, 98 lines, in the directory that IS the
 * browser bundle, reached from no page, its only importer its own test.
 *
 * The pairing with `module-graph.test.mjs` is what makes that invisible rather
 * than merely unnoticed: that test enumerates `src/` by `readdir`, so an orphan
 * is IMPORTED, CHECKED and COUNTED toward its `files.length > 10` guard. It emits
 * a green tick for a module nothing runs.
 *
 * This is exact-set, not an allowlist. Every module in `src/` and `labs/` is
 * either reached from a page or named below, and a name below that becomes
 * reachable ALSO fails — so an entry cannot outlive the condition it describes,
 * and the list cannot quietly grow.
 */
const DECLARED_ORPHANS = Object.freeze({
  "src/dregg-wallet-verification.js":
    "SUPERSEDED TWIN, delete-or-implement owed. `buildDreggServerVerificationPlan` " +
    "describes the server-side checks for `poa-dregg-proof-v1` — a protocol NO server " +
    "implements in any language. The live admission path is v2: the reached " +
    "`dregg-admission-panel.js` posts `poa-dregg-holding-challenge-v2` to " +
    "`/api/poa/holding/{challenge,verify}`, served by `node/src/poa_holding_api.rs` over " +
    "`poa-solana-gate`. Its 200 lines of test read as coverage of a feature that does not " +
    "exist. Cutting it also strands the v1 surface it is the sole non-test consumer of " +
    "(`DREGG_PROOF_PROTOCOL`, `DREGG_CHALLENGE_DOMAIN`, `normalizeDreggChallenge`, " +
    "`formatDreggChallenge`) in `dregg-wallet.js`, which is why it is one deliberate cut " +
    "rather than a drive-by deletion. `DREGG_OWNER_BIND_DOMAIN` is NOT part of that cut: " +
    "`dregg-holding-weight-bind-v1` is live in `dregg-governance/src/holding_weight.rs` " +
    "and cross-wired by `dregg-cross-wire.test.mjs`.",
});

test("every module in src/ and labs/ is reached from a page, or is a declared orphan", async () => {
  const entries = ["src/app.js"];
  for (const file of await readdir(new URL("labs/", web))) {
    if (file.endsWith(".html")) entries.push(`labs/${file.replace(".html", ".js")}`);
  }
  assert.ok(entries.length >= 4, "the page census should not have shrunk silently");

  const reached = new Set();
  for (const entry of entries) for (const module of await reachableFrom(entry)) reached.add(module);

  const authored = [];
  for (const dir of ["src", "labs"]) {
    for (const file of await readdir(new URL(`${dir}/`, web))) {
      if (file.endsWith(".js")) authored.push(`${dir}/${file}`);
    }
  }
  assert.ok(authored.length > 40, "the module census should not have shrunk silently");

  const unreached = authored.filter((module) => !reached.has(module)).sort();
  assert.deepEqual(
    unreached,
    Object.keys(DECLARED_ORPHANS).sort(),
    "a module in the browser bundle is reached from no page and is not declared, or a " +
      "declared orphan is now reached and its entry must go. Add a DECLARED_ORPHANS entry " +
      "saying why it is unreachable and what closes it — or wire it, or delete it.",
  );
  for (const reason of Object.values(DECLARED_ORPHANS)) {
    assert.ok(reason.length > 80, "a declared orphan must carry a reason, not a shrug");
  }
});

test("the module census actually fails when a reached module is unwired", async () => {
  // ⚠ The REAL walk over a REAL unwiring, so the falsifier cannot become a no-op.
  // `records-view.js` is imported by `app.js` and by nothing else in the tree, so
  // removing that one line is the whole path to it — the exact state
  // `dregg-wallet-verification.js` is in permanently. A module with a second
  // importer would make this mutation a no-op and the falsifier decoration, so if
  // the import moves, re-point this at another single-importer module rather than
  // deleting the test.
  const entry = "src/app.js";
  const source = await readFile(new URL(entry, web), "utf8");
  const broken = source.replace(/^import \{[^}]*\} from "\.\/records-view\.js";\n/m, "");
  assert.notEqual(broken, source, "the mutation must actually change app.js source; if the import moved, update this, do not delete it");
  assert.ok(!broken.includes("./records-view.js"), "the mutation must remove the only path to records-view.js");

  const reached = await reachableFrom(entry, new Map([[entry, broken]]));
  assert.equal(reached.has("src/records-view.js"), false, "the unwired module must fall out of the closure");
  // …and the unmutated graph reaches it, so the census is not simply always red.
  assert.equal((await reachableFrom(entry)).has("src/records-view.js"), true);
});

test("the reach checker actually fails when a controller is unwired", async () => {
  // ⚠ The REAL checker over the REAL defect: `mission-launcher.js` with the
  // artificer import and its dispatch row taken back out, which is exactly the
  // state the tree was in this morning. A falsifier that stops falsifying is
  // worse than none, so the mutation is asserted to have happened before the
  // verdict is read.
  const launcher = "src/mission-launcher.js";
  const source = await readFile(new URL(launcher, web), "utf8");
  const broken = source
    .replace('import { mountArtificerLogic } from "./artificer-controller.js";\n', "")
    .replace('  "artificer-logic": mountArtificerLogic,\n', "");
  assert.notEqual(broken, source, "the mutation must actually change the launcher source; if the import moved, update this, do not delete it");
  assert.ok(!broken.includes("artificer-controller.js"), "the mutation must remove the only path to artificer-controller.js");

  const reached = await reachableFrom("src/app.js", new Map([[launcher, broken]]));
  assert.equal(reached.has("src/artificer-controller.js"), false, "the unwired controller must fall out of the closure");
  // …and the unmutated graph reaches it, so the checker is not simply always red.
  assert.equal((await reachableFrom("src/app.js")).has("src/artificer-controller.js"), true);
});

test("every installed game has a descriptor loader in the app entry", async () => {
  // Read statically rather than by importing `app.js`: that module calls `boot()`
  // on import and needs a DOM, so the only way to ask it this question without
  // running the whole terminal is to read what it declares.
  const source = await readFile(new URL("src/app.js", web), "utf8");
  const block = source.match(/const DESCRIPTOR_LOADERS = Object\.freeze\(\{([\s\S]*?)\n\}\);/);
  assert.ok(block, "DESCRIPTOR_LOADERS is not where this test expects it in app.js");
  const declared = [...block[1].matchAll(/^\s*"([a-z0-9-]+)":/gm)].map((match) => match[1]);
  assert.ok(declared.length > 0, "no loaders were parsed, which would make this test vacuous");

  const missing = INSTALLED_GAME_IDS.filter((gameId) => !declared.includes(gameId));
  assert.deepEqual(missing, [], "a controller is installed for a game the app entry cannot decode");
  // The other direction is a defect too, and a quieter one: a loader for a game
  // nothing can mount is dead weight that reads as coverage.
  const unmountable = declared.filter((gameId) => !INSTALLED_GAME_IDS.includes(gameId));
  assert.deepEqual(unmountable, [], "a descriptor loader exists for a game no controller mounts");
});
