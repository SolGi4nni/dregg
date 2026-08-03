// EMIT PROVENANCE — the freshness floor under every gate in this directory that grades an artifact
// SOME OTHER COMMAND produced.
//
// ## THE FAIL-OPEN THIS CLOSES, MEASURED
//
// `stepmain-region-conformance.mjs` read `/tmp/pickles-stepmain/stepmain_step_r8_finalize.json` with
// `existsSync` + `readFileSync` and NOTHING ELSE. Measured 2026-08-02: an artifact copied aside and
// back-dated to `Jul 29 03:15` — four days older than the Lean sources it was supposedly emitted from
// — scored **GREEN, exit 0**, reported `fixture: in sync`, and printed the whole conformance verdict.
// The instrument had no freshness leg of any kind, so a `DREGG_SM=smoke` re-emit (which rewrites the
// `smoke` rungs and leaves the `step` rungs untouched), an interrupted emit, or simply a `/tmp` that
// survived a previous session all produce a green that graded an object nobody had just emitted.
//
// That is this repo's single most repeated gate defect. Two siblings of it were found the same night:
// a committed `.gz` fixture that predated a fix and so made two ledger entries read 8/8 and 228/228
// falsely, and `pickles-harnesses.sh` reading `git ls-files` — THE INDEX, not HEAD — and printing
// `ok` for a harness HEAD did not carry.
//
// ## THE SHAPE OF THE FIX: REFUSE, ON TWO INDEPENDENT CONTENT LEGS
//
// A warning inside a green run is invisible, so nothing here warns. Every check below either returns
// a provenance record or THROWS, and the message names STALENESS rather than letting the divergence
// surface later as a spurious content mismatch.
//
// The floor is the SOURCE CONE DIGEST: the transitive `import Dregg2.*` closure of the emit driver,
// each file hashed by CONTENT, folded into one digest. An emission stamps the cone digest it was
// produced from; a gate recomputes the cone digest FROM THE CURRENT TREE and refuses on any
// difference. That is stronger than an mtime rule in both directions — it survives a `touch`, and it
// does not fire on a file that was rewritten with identical bytes.
//
// The two legs are both about CONTENT, and they are independent of each other:
//
//   leg 1 (SOURCE)    the stamped cone digest == the cone digest of the tree as it is right now
//                     — "the assembly moved and nobody re-emitted";
//   leg 2 (ARTIFACT)  the file's own sha256 == the sha256 the stamp recorded for it
//                     — "this file is not the one that emission produced", which catches a rung
//                     swapped in from a different `DREGG_SM` shape, a truncated write, and a stamp
//                     carried over from a different run.
//
// ⚠ AND WHAT IS DELIBERATELY *NOT* A LEG, having been written, tested and RETIRED the same night:
// "the artifact's mtime is not older than the newest file in its own cone". It sounded like a second
// independent source and it is neither independent nor sound. MEASURED: running the gate from a
// clean `git worktree add HEAD` extract REFUSED the honest artifact — `git` stamps checkout-time
// mtimes on every file, so `lean-toolchain` was 24 minutes "newer" than an emission that was in fact
// exactly correct. Every fresh clone and every CI checkout would have reported STALE. And it adds no
// soundness: the emitter is a function of the cone, so an artifact whose cone digest and own sha256
// both match IS the emission of that source, whatever its mtime says. A leg that reds on a correct
// input is not a stricter gate — it is the thing that teaches people to route around floors.
//
// ⚠ SCOPE OF THE CONE. Only `Dregg2.*` modules are hashed. Mathlib/Std/the toolchain are pinned by
// `lean-toolchain` + `lake-manifest.json`, which are hashed as cone members in their own right. The
// cone is the closure of the DRIVER, so the thirteen `KimchiStepMainPins*` guard modules are NOT in
// it — the driver imports `KimchiStepMainCore`, not the umbrella, and a `#guard` cannot change the
// emitted bytes. Editing a pin module does not (and must not) invalidate an emission.
import { createHash } from 'node:crypto';
import { execFileSync } from 'node:child_process';
import { existsSync, readFileSync, statSync, writeFileSync } from 'node:fs';
import { basename, dirname, join, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';

export const REPO_ROOT = resolve(dirname(fileURLToPath(import.meta.url)), '..', '..', '..');
export const META_ROOT = join(REPO_ROOT, 'metatheory');
export const PROVENANCE_SCHEMA = 'pickles-emit-provenance/1';
/** The name of the stamp an emission drops beside its artifacts. */
export const PROVENANCE_FILE = 'EMIT-PROVENANCE.json';

const sha256 = (buf) => createHash('sha256').update(buf).digest('hex');

/** Toolchain files that are cone members even though nothing `import`s them. */
const TOOLCHAIN = ['lean-toolchain', 'lake-manifest.json', 'lakefile.lean', 'lakefile.toml'];

/**
 * The transitive `import Dregg2.*` closure of one Lean driver, hashed by CONTENT.
 *
 * Returns `{ root, files: [{rel, sha}], digest }`. `digest` is
 * sha256 over `rel + '\0' + sha` for every member in SORTED order, so it is independent of the
 * traversal order and of where the tree lives on disk.
 *
 * A member that does not exist is a HARD ERROR, never a skipped file: a cone that silently shrinks
 * is a freshness floor that silently stops covering the module somebody just deleted.
 */
export function leanConeDigest(rootRel, { metaRoot = META_ROOT } = {}) {
  const seen = new Set();
  const files = [];
  const visit = (rel) => {
    if (seen.has(rel)) return;
    seen.add(rel);
    const abs = join(metaRoot, rel);
    if (!existsSync(abs)) throw new Error(`emit cone: ${rel} is imported but does not exist under ${metaRoot}`);
    const buf = readFileSync(abs);
    files.push({ rel, sha: sha256(buf) });
    for (const m of buf.toString('utf8').matchAll(/^import\s+([A-Za-z0-9_.]+)/gm)) {
      if (m[1].startsWith('Dregg2')) visit(`${m[1].split('.').join('/')}.lean`);
    }
  };
  visit(rootRel);
  for (const t of TOOLCHAIN) {
    if (seen.has(t)) continue;
    const abs = join(metaRoot, t);
    if (!existsSync(abs)) continue; // lakefile.lean XOR lakefile.toml; absence of one is not a defect
    seen.add(t);
    files.push({ rel: t, sha: sha256(readFileSync(abs)) });
  }
  files.sort((a, b) => (a.rel < b.rel ? -1 : a.rel > b.rel ? 1 : 0));
  const digest = sha256(files.map((f) => `${f.rel}\0${f.sha}`).join('\n'));
  // ⚠ NO mtime is carried out of here, on purpose. A `newestMs` field is all the invitation the
  // next reader needs to re-add the clock leg that this floor RETIRED for refusing honest artifacts
  // in every fresh checkout (see the header, and `--stale-self-test` leg F3b which would go red).
  return { root: rootRel, files, digest };
}

/** `git rev-parse HEAD` + whether the cone is clean at HEAD. Never throws — a non-git tree is a
 *  legitimate build lane, and the cone digest is the load-bearing leg, not this. */
export function gitContext(coneRels) {
  const git = (...a) => execFileSync('git', ['-C', REPO_ROOT, ...a], { encoding: 'utf8', stdio: ['ignore', 'pipe', 'ignore'] }).trim();
  try {
    const head = git('rev-parse', 'HEAD');
    let dirty = [];
    try {
      const paths = (coneRels ?? []).map((r) => join('metatheory', r));
      if (paths.length) {
        dirty = git('status', '--porcelain', '--', ...paths).split('\n').filter(Boolean).map((l) => l.slice(3));
      }
    } catch { dirty = ['<status unavailable>']; }
    return { head, cone_dirty_at_head: dirty };
  } catch { return { head: null, cone_dirty_at_head: [] }; }
}

export const provenancePathFor = (dir) => join(dir, PROVENANCE_FILE);

/** Stamp an emission. `artifacts` is a list of absolute paths the emit run produced. */
export function writeProvenance(dir, { cone, command, cwd, artifacts, label }) {
  const rec = {
    schema: PROVENANCE_SCHEMA,
    label,
    emitted_at: new Date().toISOString(),
    emitted_at_ms: Date.now(),
    command,
    cwd,
    // `files_detail` is carried so a refusal can NAME the modules that moved. A refusal that says
    // only "the digest differs" sends the reader looking for a content bug in the wrong place.
    cone: { root: cone.root, files: cone.files.length, digest: cone.digest,
            files_detail: cone.files.map((f) => ({ rel: f.rel, sha: f.sha })) },
    git: gitContext(cone.files.map((f) => f.rel)),
    artifacts: Object.fromEntries(artifacts.map((p) => [basename(p), sha256(readFileSync(p))])),
  };
  writeFileSync(provenancePathFor(dir), `${JSON.stringify(rec, null, 2)}\n`);
  return rec;
}

export function readProvenance(dir) {
  const p = provenancePathFor(dir);
  if (!existsSync(p)) return null;
  const rec = JSON.parse(readFileSync(p, 'utf8'));
  if (rec.schema !== PROVENANCE_SCHEMA)
    throw new Error(`STALE PROVENANCE SCHEMA: ${p} is ${rec.schema}, this gate speaks ${PROVENANCE_SCHEMA}. Re-emit.`);
  return rec;
}

/** The refusal, spelled so a reader knows it is STALENESS and not a content divergence. */
class StaleArtifact extends Error {
  constructor(msg) { super(msg); this.name = 'StaleArtifact'; this.stale = true; }
}
export const isStale = (e) => e instanceof StaleArtifact || e?.stale === true;
const refuse = (what, why, how) => {
  throw new StaleArtifact(`⚑ STALE INPUT REFUSED — ${what}\n   ${why}\n   emit it fresh:  ${how}`);
};

/** Which cone members changed between a stamp and the tree as it is now. Named in the refusal so the
 *  reader is pointed at the module that moved instead of at a phantom content bug. */
function movedModules(stamped, cone) {
  const was = new Map((stamped.files_detail ?? []).map((f) => [f.rel, f.sha]));
  if (!was.size) return [];
  const out = cone.files.filter((f) => was.get(f.rel) !== f.sha).map((f) => f.rel);
  const now = new Set(cone.files.map((f) => f.rel));
  for (const rel of was.keys()) if (!now.has(rel)) out.push(`${rel} (no longer in the cone)`);
  return out;
}

/**
 * ⚑ THE GATE. Returns the provenance record, or THROWS naming staleness.
 *
 * `artifact`  absolute path to the emitted file about to be graded
 * `cone`      the result of `leanConeDigest` computed FROM THE CURRENT TREE
 * `emitCmd`   the literal command that produces a fresh one, printed in every refusal
 */
export function requireFreshArtifact({ artifact, cone, emitCmd }) {
  const dir = dirname(artifact);
  const name = basename(artifact);
  const rec = readProvenance(dir);
  if (!rec)
    refuse(`${artifact}`,
      `no ${PROVENANCE_FILE} beside it, so NOTHING is known about which source tree produced it. An `
      + `artifact left over from an earlier session is indistinguishable from a fresh one, and that is `
      + `exactly how a green graded a file nobody had emitted.`, emitCmd);

  if (rec.cone.digest !== cone.digest) {
    const moved = movedModules(rec.cone, cone);
    refuse(`${artifact}`,
      `it was emitted from a DIFFERENT source cone: stamped ${rec.cone.digest.slice(0, 16)}… (${rec.cone.files} files, `
      + `${rec.emitted_at}) but ${cone.root}'s closure hashes ${cone.digest.slice(0, 16)}… (${cone.files.length} files) right now`
      + (moved.length ? `; moved: ${moved.slice(0, 6).join(', ')}${moved.length > 6 ? ` +${moved.length - 6}` : ''}` : ''),
      emitCmd);
  }

  const want = rec.artifacts?.[name];
  if (!want)
    refuse(`${artifact}`,
      `the ${PROVENANCE_FILE} beside it stamps ${Object.keys(rec.artifacts ?? {}).length} artifact(s) and `
      + `${name} is not one of them — this file is left over from a DIFFERENT emit run than the stamp.`, emitCmd);
  // leg 2, INDEPENDENT of leg 1: this file's own bytes against the bytes the stamp recorded. Leg 1
  // says the SOURCE is right; this says the ARTIFACT is the one that source produced.
  const got = sha256(readFileSync(artifact));
  if (got !== want)
    refuse(`${artifact}`,
      `its bytes (${got.slice(0, 16)}…) are not the bytes the stamp recorded (${want.slice(0, 16)}…) — it was `
      + `rewritten, truncated, or swapped for a rung from a different emit run, after the emission that `
      + `vouches for it.`, emitCmd);

  return rec;
}

/**
 * The same floor for a COMMITTED fixture, whose stamp is a tracked sidecar rather than a scratch-dir
 * file. A fixture is a snapshot of an emission and goes stale exactly the same way — the `.gz` that
 * made two ledger entries read 8/8 and 228/228 falsely predated the fix and nothing looked.
 */
export function requireFreshFixture({ fixture, sidecar, cone, emitCmd, refreshCmd }) {
  const fpath = fixture instanceof URL ? fileURLToPath(fixture) : fixture;
  const spath = sidecar instanceof URL ? fileURLToPath(sidecar) : sidecar;
  if (!existsSync(spath))
    refuse(`${basename(fpath)} (committed fixture)`,
      `no provenance sidecar ${basename(spath)}, so the fixture vouches for nothing: a fixture that `
      + `predates the assembly it grades is the same fail-open as a stale /tmp artifact.`, refreshCmd);
  const rec = JSON.parse(readFileSync(spath, 'utf8'));
  if (rec.schema !== PROVENANCE_SCHEMA)
    refuse(`${basename(fpath)} (committed fixture)`, `sidecar schema ${rec.schema} != ${PROVENANCE_SCHEMA}`, refreshCmd);
  const got = sha256(readFileSync(fpath));
  if (got !== rec.artifact_sha256)
    refuse(`${basename(fpath)} (committed fixture)`,
      `its bytes (${got.slice(0, 16)}…) are not the bytes its own sidecar records (${String(rec.artifact_sha256).slice(0, 16)}…) — `
      + `the fixture was refreshed without refreshing the sidecar, or the other way round.`, refreshCmd);
  if (rec.cone.digest !== cone.digest) {
    const moved = movedModules(rec.cone, cone);
    refuse(`${basename(fpath)} (committed fixture)`,
      `it was emitted from a DIFFERENT source cone: sidecar ${rec.cone.digest.slice(0, 16)}… (${rec.refreshed_at}) `
      + `vs ${cone.digest.slice(0, 16)}… for the tree right now. The assembly moved and the fixture did not`
      + (moved.length ? `; moved: ${moved.slice(0, 6).join(', ')}${moved.length > 6 ? ` +${moved.length - 6}` : ''}` : ''),
      refreshCmd);
  }
  return rec;
}

/** Write the committed fixture's sidecar. Called only by a `--refresh-fixture`. */
export function writeFixtureSidecar(sidecar, { fixture, cone, from, extra }) {
  const spath = sidecar instanceof URL ? fileURLToPath(sidecar) : sidecar;
  const fpath = fixture instanceof URL ? fileURLToPath(fixture) : fixture;
  const rec = {
    schema: PROVENANCE_SCHEMA,
    fixture: basename(fpath),
    artifact_sha256: sha256(readFileSync(fpath)),
    refreshed_at: new Date().toISOString(),
    refreshed_from: from,
    cone: { root: cone.root, files: cone.files.length, digest: cone.digest,
            files_detail: cone.files.map((f) => ({ rel: f.rel, sha: f.sha })) },
    git: gitContext(cone.files.map((f) => f.rel)),
    ...extra,
  };
  writeFileSync(spath, `${JSON.stringify(rec, null, 2)}\n`);
  return rec;
}

/**
 * OPTION (a): the gate EMITS ITS OWN INPUT, so there is no stale path to read at all. Runs the Lean
 * driver and stamps what it produced. Costs a Lean run (minutes for the full step shape) and needs a
 * toolchain, which is why it is a flag rather than the unconditional default — but when it is used
 * there is no window between emission and grading for anything to go stale in.
 */
export function runLeanEmit({ driver, dir, env = {}, label, glob }) {
  const cone = leanConeDigest(driver);
  const cmd = `${Object.entries(env).map(([k, v]) => `${k}=${v}`).join(' ')} lake env lean --run ${driver}`.trim();
  process.stderr.write(`   emitting: (cd metatheory && ${cmd})\n`);
  const t0 = Date.now();
  execFileSync('lake', ['env', 'lean', '--run', driver],
    { cwd: META_ROOT, env: { ...process.env, ...env }, stdio: ['ignore', 'inherit', 'inherit'] });
  const produced = glob().filter((p) => existsSync(p) && statSync(p).mtimeMs >= t0 - 1000);
  if (!produced.length) throw new Error(`emit produced no artifact newer than the run — ${dir} was not written`);
  const rec = writeProvenance(dir, { cone, command: `(cd metatheory && ${cmd})`, cwd: META_ROOT, artifacts: produced, label });
  process.stderr.write(`   emitted ${produced.length} artifact(s) in ${((Date.now() - t0) / 1000).toFixed(1)}s, stamped ${PROVENANCE_FILE}\n`);
  return { cone, rec };
}
