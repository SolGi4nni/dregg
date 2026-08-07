import assert from "node:assert/strict";
import { access, readFile } from "node:fs/promises";
import { test } from "node:test";
import { POAG1_EXPECTED_ARTIFACTS, POAG1_PENDING_ARTIFACTS } from "../src/poag1.js";
import { GAME_RACK, loadRackEntry } from "../src/game-rack.js";
import { INSTALLED_GAME_IDS } from "../src/mission-launcher.js";

/**
 * ⚑ THE CLIENT'S PIN AND THE EMITTER'S OUTPUT, COMPARED.
 *
 * `POAG1_EXPECTED_ARTIFACTS` is the exact artifact set this browser will accept —
 * count, order, path and media type, all refused rather than warned about. It has
 * to equal what `Dregg2.Games.PathOfAngels.Emit.canonicalArtifacts` renders, and
 * until now the only thing joining those two lists was somebody remembering.
 *
 * The failure that buys is silent on both sides and loud in the worst place: a
 * game joins the emitter, the ceremony emits a bundle with one more artifact, and
 * the first thing that notices is a PLAYER'S BROWSER refusing the whole bundle
 * with `artifact-set` — every card sealed, the terminal dark. Nothing in Lean is
 * wrong, nothing in the client is wrong, and no test anywhere had both halves.
 *
 * This has both halves. Lean's `POAG1_GAME_PATHS` is read out of the SOURCE rather
 * than out of an emitted artifact on purpose: the emitted bundle is exactly the
 * thing that will not exist until the ceremony runs, so a check against it could
 * only ever confirm the past.
 */

const repo = new URL("../../", import.meta.url);
const EMIT = new URL("metatheory/Dregg2/Games/PathOfAngels/Emit.lean", repo);

/** `POAG1_GAME_PATHS` as Lean declares it, in declaration order. */
async function leanGamePaths() {
  const source = await readFile(EMIT, "utf8");
  const block = source.match(/def POAG1_GAME_PATHS : List String :=\n([\s\S]*?)\n\n/);
  assert.ok(block, "POAG1_GAME_PATHS is not where this test expects it in Emit.lean");
  const paths = [...block[1].matchAll(/"([^"]+)"/g)].map((match) => match[1]);
  assert.ok(paths.length > 0, "no paths were parsed, which would make this test vacuous");
  return paths;
}

const gamePathsOf = (artifacts) => artifacts.map((entry) => entry.path).filter((path) => path.startsWith("games/"));

async function exists(url) {
  try { await access(url); return true; } catch { return false; }
}

test("pinned plus pending is exactly what the emitter renders", async () => {
  const lean = await leanGamePaths();
  const pinned = gamePathsOf(POAG1_EXPECTED_ARTIFACTS);
  const pending = gamePathsOf(POAG1_PENDING_ARTIFACTS);

  assert.deepEqual(pinned.filter((path) => pending.includes(path)), [], "a path cannot be both signed and pending");
  assert.deepEqual([...pinned, ...pending].sort(), [...lean].sort(), "the client's artifact census disagrees with Emit.lean's POAG1_GAME_PATHS");

  // Order is not decoration on either side: the content root is framed
  // `path_ascending` and `validateManifest` refuses any other artifact order, so a
  // wrongly ordered list does not raise an error — it binds a DIFFERENT root.
  assert.deepEqual([...lean], [...lean].sort(), "Emit.lean's game paths are not path-ascending");
  assert.deepEqual([...pinned], [...pinned].sort(), "the pinned artifact list is not path-ascending");
  assert.deepEqual([...pending], [...pending].sort(), "the pending artifact list is not path-ascending");
});

test("the checker fails when the emitter enrols a game the client has not been told about", async () => {
  // The REAL comparison against a REAL new path, so the falsifier cannot quietly
  // become a no-op. `games/zzz-containment-inspection.json` is the shape of the
  // next enrolment and sorts last, which is the easy case; the check would fail
  // the same way for one that sorts first.
  const lean = [...await leanGamePaths(), "games/zzz-containment-inspection.json"];
  const known = [...gamePathsOf(POAG1_EXPECTED_ARTIFACTS), ...gamePathsOf(POAG1_PENDING_ARTIFACTS)];
  assert.notDeepEqual([...known].sort(), [...lean].sort(), "an unknown emitted game must not compare equal");
});

test("every game the client pins has a descriptor in the signed bundle, and every pending one does not", async () => {
  const signed = new URL("poa/artifacts/poag1/", repo);
  const pendingDir = new URL("poa/artifacts/poag1-pending/", repo);
  for (const path of gamePathsOf(POAG1_EXPECTED_ARTIFACTS)) {
    assert.equal(await exists(new URL(path, signed)), true, `${path} is pinned and the signed bundle does not carry it`);
  }
  for (const path of gamePathsOf(POAG1_PENDING_ARTIFACTS)) {
    // ⚠ Both directions. A pending descriptor that has ALREADY landed in the
    // signed bundle means the ceremony ran and this list was not moved, which is
    // the exact drift a browser would find out about at load.
    assert.equal(await exists(new URL(path, signed)), false, `${path} is in the signed bundle and still listed as pending`);
    assert.equal(await exists(new URL(path, pendingDir)), true, `${path} is declared pending and nothing has emitted it`);
  }
});

test("a pending game already has its client, so enrolling it cannot downgrade its card", () => {
  // ⚑ THE CEREMONY'S OWN-GOAL, MADE UNREACHABLE. `game-rack.js` renders a game the
  // signed catalog enrols and this terminal cannot mount as `unsupported`:
  // "a browser must never approximate a game it was not given". That is the only
  // card state on the rack that is a defect, and the ceremony is the one act that
  // can create it — by enrolling a descriptor whose controller did not ship in the
  // same cut. So the requirement is stated HERE, where it is checkable before the
  // ceremony rather than after it.
  const byGame = new Map(GAME_RACK.map((entry) => [entry.gameId, entry]));
  for (const { path } of POAG1_PENDING_ARTIFACTS) {
    const gameId = path.replace("games/", "").replace(".json", "");
    assert.ok(INSTALLED_GAME_IDS.includes(gameId), `${gameId} is one ceremony from being enrolled and no controller mounts it`);
    const entry = byGame.get(gameId);
    assert.ok(entry, `${gameId} is one ceremony from being enrolled and has no presentation record`);
    loadRackEntry(entry, gameId);
    assert.notEqual(entry.session, null, `${gameId} would open with no declared length`);
    assert.notEqual(entry.shape, null, `${gameId} would open with no declared shape`);
  }
});
