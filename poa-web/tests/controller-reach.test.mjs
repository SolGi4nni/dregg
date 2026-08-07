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
