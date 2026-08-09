import { test } from "node:test";
import assert from "node:assert/strict";
import { readFileSync, readdirSync, statSync } from "node:fs";
import { join } from "node:path";
import { fileURLToPath } from "node:url";

/**
 * ⚑ AN INTEGRATION HARNESS WITH NO WAY TO INVOKE IT IS NOT A TEST.
 *
 * `extension/tests/dregg-poa-actions/` — `run.mjs` (179 lines) plus a `harness.ts`
 * and a fixture page, a complete Playwright + esbuild integration test for signed
 * routes and the receipt seam — was authored on 2026-08-04 and had **no
 * `test:dregg-poa-actions` script**. Every one of the other twelve
 * `tests/<dir>/run.mjs` had one. Someone copied the pattern from its sibling
 * `tests/dregg-poa/`, added two days earlier, and did not copy the last line of
 * `package.json`. Nothing anywhere referenced the directory: not a workflow, not a
 * shell script, not a doc. It was findable only by listing the directory.
 *
 * ⚠ THE REASON IT COULD HAPPEN IS THE REASON THIS TEST LIVES IN `test/` AND NOT
 * `tests/`. The two directories are different runners and only ONE is in CI:
 * `test/` (singular) is `npm test`, run by `.github/workflows/extension.yml`.
 * `tests/` (plural) is a separate install with its own `node_modules`, twelve
 * standalone harnesses and ten Playwright specs, and is invoked by NO workflow at
 * all. Its CI signal is already zero, so a directory added with no script changes
 * nothing observable — the omission was undetectable by construction.
 *
 * That larger gap is not closed here and this test does not pretend to close it:
 * a harness this asserts is *routable* still only runs when a human types the
 * script. What it does close is the silent part. A new `tests/<dir>/run.mjs` with
 * no script now fails the suite CI does run, and a script pointing at a harness
 * that no longer exists fails it too — the correspondence is checked in BOTH
 * directions, so neither list can drift under the other.
 */

const extension = new URL("../", import.meta.url);
const testsDir = fileURLToPath(new URL("tests/", extension));

/** Every `tests/<dir>/run.mjs` harness on disk. */
function harnessDirectories() {
  return readdirSync(testsDir, { withFileTypes: true })
    .filter((entry) => entry.isDirectory() && entry.name !== "node_modules")
    .map((entry) => entry.name)
    .filter((name) => {
      try {
        return statSync(join(testsDir, name, "run.mjs")).isFile();
      } catch {
        return false;
      }
    })
    .sort();
}

/** Every `test:<name>` script that invokes a `tests/<dir>/run.mjs`. */
function routedHarnesses(scripts) {
  const routed = [];
  for (const command of Object.values(scripts)) {
    const match = /(?:^|\s)tests\/([^/\s]+)\/run\.mjs(?:\s|$)/.exec(command);
    if (match) routed.push(match[1]);
  }
  return routed.sort();
}

test("every tests/<dir>/run.mjs harness is reachable from an npm script, and every script from a harness", () => {
  const scripts = JSON.parse(readFileSync(new URL("package.json", extension), "utf8")).scripts;
  const onDisk = harnessDirectories();
  const routed = routedHarnesses(scripts);

  assert.ok(onDisk.length >= 10, "the harness census should not have shrunk silently");
  assert.deepEqual(
    new Set(routed).size,
    routed.length,
    `two npm scripts invoke the same harness (${routed.join(", ")}), so one of them is a copy ` +
      `whose directory name was never changed`,
  );
  assert.deepEqual(
    routed,
    onDisk,
    "an integration harness exists that no npm script can invoke, or a script names a harness " +
      "that is not on disk. Add the missing `test:<dir>` line to extension/package.json, or " +
      "delete the harness — an unroutable harness is 100+ lines that read as coverage and run " +
      "never.",
  );
});

test("the routing check actually fails when a harness loses its script", () => {
  // ⚠ The REAL checker over the REAL defect: the scripts block with the
  // `test:dregg-poa-actions` line taken back out, which is exactly the state the
  // tree was in from 2026-08-04 until this test landed. A falsifier that stops
  // falsifying is worse than none, so the mutation is asserted to have happened
  // before the verdict is read.
  const scripts = JSON.parse(readFileSync(new URL("package.json", extension), "utf8")).scripts;
  assert.ok(scripts["test:dregg-poa-actions"], "the subject of this falsifier has moved; re-point it, do not delete it");

  const broken = { ...scripts };
  delete broken["test:dregg-poa-actions"];
  assert.notEqual(Object.keys(broken).length, Object.keys(scripts).length, "the mutation must actually remove a script");

  assert.ok(
    !routedHarnesses(broken).includes("dregg-poa-actions"),
    "the unrouted harness must fall out of the routed set",
  );
  // …and the unmutated scripts do route it, so the checker is not simply always red.
  assert.ok(routedHarnesses(scripts).includes("dregg-poa-actions"));
  assert.ok(harnessDirectories().includes("dregg-poa-actions"), "the harness must actually be on disk");
});
