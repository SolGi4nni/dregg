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
//   leg 3 (GIT)       the emit cone was CLEAN at a real commit when the stamp was written
//                     — "this tree is a commit". ⚑ ADDED 2026-08-03, and it is the leg the other two
//                     are structurally blind to: legs 1 and 2 both hash the CURRENT WORKING TREE, so
//                     an emission from a tree no commit contains satisfies both. `cone_dirty_at_head`
//                     had been recorded since day one and GATED ON NOWHERE — its only consumers
//                     interpolated it into a status line. MEASURED: the committed stepmain fixture's
//                     sidecar carried `cone_dirty_at_head: [KimchiStepMainCore.lean]` beside
//                     `refreshed_from: "… (⚠ FIXTURE STALE)"`, and the session's whole "conformance
//                     GREEN, 31/31 byte-exact" rested on it. See `unreproducibleFromGit`.
//                     It REFUSES on every path: a live artifact at grade time, a COMMITTED FIXTURE
//                     at grade time AND at write time (so an unreproducible snapshot cannot even be
//                     created). ⚠ The cost is deliberate — while a cone file is uncommitted, the
//                     gates that depend on it do not run. That is what "reproducible from git"
//                     costs, and a field nobody read is what the alternative cost.
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
import { existsSync, readFileSync, readdirSync, rmSync, statSync, writeFileSync } from 'node:fs';
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
 *  legitimate build lane, and the cone digest is the load-bearing leg, not this.
 *
 *  ⚠ DO NOT `.trim()` THE STATUS OUTPUT. `git status --porcelain` writes `XY<space>PATH` where `X`
 *  is the INDEX status and `Y` the worktree one, so an unstaged modification begins with a SPACE
 *  (` M metatheory/…`). Trimming the whole output ate that leading space on the FIRST line only, and
 *  the `slice(3)` below then ate the first character of the path — which is how the stepmain fixture
 *  sidecar came to record `etatheory/Dregg2/Circuit/Emit/KimchiStepMainCore.lean`. One character, on
 *  one line, in the one field that says the emission is not reproducible from git. */
export function gitContext(coneRels) {
  const raw = (...a) => execFileSync('git', ['-C', REPO_ROOT, ...a], { encoding: 'utf8', stdio: ['ignore', 'pipe', 'ignore'] });
  try {
    const head = raw('rev-parse', 'HEAD').trim();
    let dirty = [];
    try {
      const paths = (coneRels ?? []).map((r) => join('metatheory', r));
      if (paths.length) {
        dirty = raw('status', '--porcelain', '--', ...paths)
          .split('\n').filter(Boolean).map((l) => l.slice(3));
      }
    } catch { dirty = ['<status unavailable>']; }
    return { head, cone_dirty_at_head: dirty };
  } catch { return { head: null, cone_dirty_at_head: [] }; }
}

/**
 * ⚑ IS THIS STAMP REPRODUCIBLE FROM GIT AT ALL?
 *
 * `cone_dirty_at_head` was recorded by `gitContext` from the day this file existed and GATED ON
 * NOWHERE: its only consumers interpolated it into a status line. MEASURED 2026-08-03 — the
 * committed stepmain fixture's sidecar carried
 *     "cone_dirty_at_head": ["etatheory/Dregg2/Circuit/Emit/KimchiStepMainCore.lean"]
 * beside `refreshed_from: "… (⚠ FIXTURE STALE)"`, i.e. the fixture behind every "conformance GREEN,
 * 31/31 byte-exact" statement of that session was stamped from a WORKING TREE THAT EXISTS IN NO
 * COMMIT, and could not be reproduced from `d245921c7` plus the tree. The freshness floor could not
 * see it: the cone digest matched, because the cone digest is computed from the same dirty tree.
 *
 * So: a cone digest says the artifact matches THIS tree. This says THIS TREE IS A COMMIT.
 *
 * Returns `null` when the stamp is git-reproducible, else a one-line reason.
 */
export function unreproducibleFromGit(rec) {
  const g = rec?.git;
  if (!g || !g.head) return 'the stamp records no git HEAD — it was produced outside a git tree, so nothing can check it out';
  const d = g.cone_dirty_at_head ?? [];
  if (d.length)
    return `${d.length} emit-cone file(s) were UNCOMMITTED at the stamped HEAD ${String(g.head).slice(0, 12)}: `
      + `${d.slice(0, 4).join(', ')}${d.length > 4 ? ` +${d.length - 4}` : ''}`;
  return null;
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
  // ⚠ SAY IT AT STAMP TIME TOO. The gates below refuse on it, but the emitter is where the operator
  // can still fix it with one `git commit`, and a reader who only ever sees the gate's refusal has
  // to go looking for which of their own edits caused it.
  const why = unreproducibleFromGit(rec);
  if (why) process.stderr.write(`   ⚠ THIS EMISSION IS NOT REPRODUCIBLE FROM GIT — ${why}\n`);
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

  // ⚑ LEG 3 — THE ONE LEGS 1 AND 2 ARE STRUCTURALLY BLIND TO, AND IT REFUSES.
  // Both legs above hash the CURRENT WORKING TREE, so an emission from a tree that no commit
  // contains satisfies both perfectly: the cone digest matches because the cone was hashed from the
  // same dirty files. MEASURED 2026-08-03 — the sidecar of the committed stepmain fixture behind
  // that session's "conformance GREEN, 31/31 byte-exact" recorded
  //     "cone_dirty_at_head": ["…/KimchiStepMainCore.lean"]   (the module that decides the gates)
  // and NOTHING read the field: its only consumers interpolated it into a ║-banner. The grade could
  // not be reproduced from `d245921c7` plus the tree by anyone, including the agent that made it.
  //
  // ⚠ THIS IS A REFUSAL AND NOT A WARNING, and the cost is deliberate: while a cone file is
  // uncommitted, this gate does not run. That is the point — a green whose input exists in no commit
  // is a green nobody can check. `git commit` the cone (this is a greenfield tree; committing is
  // free) and re-emit. There is no env var here that makes a run green.
  const gitWhy = unreproducibleFromGit(rec);
  if (gitWhy)
    refuse(`${artifact}`,
      `⚑ IT IS NOT REPRODUCIBLE FROM GIT: ${gitWhy}. The cone digest and the artifact sha256 both `
      + `MATCH — they are computed from the very tree that is uncommitted, which is why neither can `
      + `see this. Commit the emit cone and re-emit; the grade then names a commit.`,
      emitCmd);

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
  // ⚑ THE THIRD LEG, AND THE ONE THE OTHER TWO CANNOT SEE. Legs 1 and 2 say the fixture is the
  // emission of THIS TREE. This says THIS TREE IS A COMMIT — a committed fixture whose sidecar
  // records a dirty emit cone is reproducible by nobody, which is the whole reason a fixture is
  // committed. It is a HARD REFUSAL here and not a conform entry: an unreproducible fixture must not
  // be gradeable at all, and unlike a live /tmp artifact there is no "iterating locally" case for it.
  const why = unreproducibleFromGit(rec);
  if (why)
    refuse(`${basename(fpath)} (committed fixture)`,
      `⚑ IT IS NOT REPRODUCIBLE FROM GIT: ${why}. It was stamped from a working tree that no commit `
      + `contains, so the grade it produces cannot be re-derived from this repository by anyone — `
      + `which is the only thing a COMMITTED fixture is for. Re-emit from a clean checkout of a `
      + `commit (\`scripts/dregg-clean-build … --sha HEAD --host hbox --keep\`) and refresh it there.`,
      refreshCmd);
  return rec;
}

/**
 * Write the committed fixture's sidecar. Called only by a `--refresh-fixture`.
 *
 * ⚑ IT REFUSES TO STAMP AN UNREPRODUCIBLE FIXTURE. `requireFreshFixture` refuses to GRADE one, which
 * is the floor; this refuses to CREATE one, which is where the defect is cheap to fix. The measured
 * incident is the reason both exist: a `--refresh-fixture` run in a churned working tree wrote a
 * sidecar naming a dirty `KimchiStepMainCore.lean`, the run printed GREEN, and the fixture was
 * committed — a snapshot of a circuit that is in no commit, grading as though it were HEAD's.
 */
export function writeFixtureSidecar(sidecar, { fixture, cone, from, extra }) {
  const spath = sidecar instanceof URL ? fileURLToPath(sidecar) : sidecar;
  const fpath = fixture instanceof URL ? fileURLToPath(fixture) : fixture;
  const g = gitContext(cone.files.map((f) => f.rel));
  const gitWhy = unreproducibleFromGit({ git: g });
  if (gitWhy)
    refuse(`${basename(fpath)} (refusing to WRITE the sidecar)`,
      `⚑ THE EMISSION IS NOT REPRODUCIBLE FROM GIT: ${gitWhy}. A committed fixture stamped from a `
      + `working tree that no commit contains grades every future run against a circuit nobody can `
      + `check out. Commit the emit cone first, then re-emit and refresh from that commit.`,
      'commit the cone, then re-emit from a clean checkout: scripts/dregg-clean-build <target> --sha HEAD --host hbox --keep');
  const rec = {
    schema: PROVENANCE_SCHEMA,
    fixture: basename(fpath),
    artifact_sha256: sha256(readFileSync(fpath)),
    refreshed_at: new Date().toISOString(),
    refreshed_from: from,
    cone: { root: cone.root, files: cone.files.length, digest: cone.digest,
            files_detail: cone.files.map((f) => ({ rel: f.rel, sha: f.sha })) },
    git: g,
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
  // ⚑ BUILD BEFORE EMITTING, BECAUSE THE STAMP MEASURES THE SOURCE AND THE EMISSION READS THE
  // BINARIES. `lake env lean --run` elaborates the DRIVER fresh and loads every import from
  // whatever `.olean` happens to be on disk. So a cone that is clean at HEAD — which is exactly
  // what `leanConeDigest` and `gitContext` certify — can still be emitted by oleans built from an
  // older cone, and the stamp would record that run as fresh and reproducible. The floor's three
  // legs are all about the SOURCE; none of them can see a stale binary.
  //
  // MEASURED 2026-08-04. `wrapmain-region-conformance.mjs --emit` refused with
  // `xhatXY IS NOT THE MSM'S OUTPUT`, quoting a `shapeWrap` value from one commit against an
  // `xhatOut` derived from another: `KimchiWrapMain.olean` was 11:47:06 and its own source
  // 11:48:47, while `KimchiWrapMainField.olean` had already been rebuilt past it. The emission was
  // running HALF of one commit and half of another. It only failed loudly because that one shape
  // field carries a fail-closed memo check; every other divergence between two oleans would have
  // emitted silently and been stamped fresh.
  //
  // ⚠ NOT an mtime leg — `emit-provenance.mjs` retired one of those for good reason (`7d9a20bef`,
  // `31b12026f`) and this does not reintroduce it. It does not COMPARE timestamps or refuse
  // anything; it makes the binaries be the cone's, which is what the stamp was already claiming.
  // It is ~4 s when the tree is already built, and it THROWS rather than warning if it cannot.
  const mod = driver.replace(/\.lean$/, '').replace(/\//g, '.');
  process.stderr.write(`   building:  (cd metatheory && lake build ${mod})\n`);
  execFileSync('lake', ['build', mod],
    { cwd: META_ROOT, env: { ...process.env }, stdio: ['ignore', 'inherit', 'inherit'] });
  process.stderr.write(`   emitting: (cd metatheory && ${cmd})\n`);
  // ⚑ INVALIDATE THE STAMP BEFORE THE RUN, NOT AFTER IT. The stamp is written at the END, so until
  // now a run that died partway left the PREVIOUS run's stamp standing over a directory that was
  // now a mixture of two runs. Measured 2026-08-03: `/tmp/pickles-stepmain` held a nine-rung `smoke`
  // set from 11:46–11:48 beside a four-rung `step` set from 12:48–16:13, with no stamp at all and
  // nothing recording that either run had finished.
  //
  // Unlinking first makes the invariant "a stamp exists ⟹ the run that wrote it ran to completion",
  // so a half-finished directory is UNSTAMPED and `requireFreshArtifact` refuses it on leg 0. This
  // only ever produces MORE refusals — it does not touch the freshness floor's tests.
  //
  // The Lean driver stages each artifact as `*.partial` and `rename(2)`s it into place, so the other
  // half of the hole — a file with the right name and torn bytes — cannot occur either. Any
  // `*.partial` still lying about is the debris of a death mid-write; clear it so the glob below
  // cannot mistake one for output.
  const stamp = provenancePathFor(dir);
  if (existsSync(stamp)) rmSync(stamp);
  if (existsSync(dir))
    for (const f of readdirSync(dir)) if (f.endsWith('.partial')) rmSync(join(dir, f));
  const t0 = Date.now();
  execFileSync('lake', ['env', 'lean', '--run', driver],
    { cwd: META_ROOT, env: { ...process.env, ...env }, stdio: ['ignore', 'inherit', 'inherit'] });
  const produced = glob().filter((p) => existsSync(p) && statSync(p).mtimeMs >= t0 - 1000);
  if (!produced.length) throw new Error(`emit produced no artifact newer than the run — ${dir} was not written`);
  const rec = writeProvenance(dir, { cone, command: `(cd metatheory && ${cmd})`, cwd: META_ROOT, artifacts: produced, label });
  process.stderr.write(`   emitted ${produced.length} artifact(s) in ${((Date.now() - t0) / 1000).toFixed(1)}s, stamped ${PROVENANCE_FILE}\n`);
  return { cone, rec };
}

// ── ⚑ THE FLOOR'S OWN RED PATH ────────────────────────────────────────────────────────────────────
/**
 * `node scripts/emit-provenance.mjs --self-test`
 *
 * The three legs above are the only thing standing between a gate's GREEN and a file nobody emitted,
 * so each must be shown to REFUSE, and the honest shape must still be ACCEPTED — a floor that reds on
 * everything proves nothing, and one that reds on nothing is what leg 3 was for its whole life.
 *
 * ⚠ It needs NO Lean, no emission and no toolchain: every input is synthesised in a temp dir, and the
 * "cone" is a two-file fake. What it measures is THIS MODULE, which is the object the region-conformance
 * gates delegate their whole notion of freshness to.
 */
async function selfTest() {
  const { mkdtempSync, writeFileSync: wf, rmSync } = await import('node:fs');
  const { tmpdir } = await import('node:os');
  const d = mkdtempSync(join(tmpdir(), 'emit-prov-selftest-'));
  const art = join(d, 'artifact.json');
  wf(art, '{"gates":[]}\n');
  const cone = { root: 'X.lean', files: [{ rel: 'X.lean', sha: 'a'.repeat(64) }], digest: 'd'.repeat(64) };
  const cleanGit = { head: '0'.repeat(40), cone_dirty_at_head: [] };
  const stamp = (over) => wf(join(d, PROVENANCE_FILE), JSON.stringify({
    schema: PROVENANCE_SCHEMA, emitted_at: new Date().toISOString(), command: 'fake',
    cone: { root: cone.root, files: 1, digest: cone.digest, files_detail: cone.files },
    git: cleanGit, artifacts: { 'artifact.json': sha256(readFileSync(art)) }, ...over,
  }));

  let bad = 0;
  const leg = (label, run, wantRefusal) => {
    let refused = null;
    try { run(); } catch (e) { refused = e; }
    const ok = wantRefusal ? (refused !== null && isStale(refused)) : refused === null;
    if (!ok) bad++;
    console.log(`   ${ok ? 'ok  ' : 'RED '} ${label.padEnd(62)} ${refused ? (isStale(refused) ? 'REFUSED as STALE' : `threw, NOT as staleness: ${refused.message.slice(0, 50)}`) : 'accepted'}`);
    if (ok && refused) console.log(`          ${String(refused.message).split('\n')[1]?.trim().slice(0, 140)}`);
  };
  const check = () => requireFreshArtifact({ artifact: art, cone, emitCmd: 'fake-emit' });

  console.log('── emit-provenance --self-test (three legs, each must REFUSE; the honest shape must PASS) ──');
  // (A0) THE ANCHOR.
  stamp({});
  leg('A0 anchor: a correct stamp over a clean, committed cone', check, false);
  // (L0) no stamp at all — the measured `/tmp` survivor.
  rmSync(join(d, PROVENANCE_FILE));
  leg('L0 no stamp beside the artifact (a /tmp survivor)', check, true);
  // (L1) SOURCE: the cone moved.
  stamp({ cone: { root: cone.root, files: 1, digest: 'e'.repeat(64), files_detail: [{ rel: 'X.lean', sha: 'b'.repeat(64) }] } });
  leg('L1 stamped from a cone that has since moved', check, true);
  // (L2) ARTIFACT: right stamp, wrong bytes.
  stamp({ artifacts: { 'artifact.json': 'f'.repeat(64) } });
  leg('L2 correct cone, but the artifact is not the one it vouches for', check, true);
  // ⚑ (L3) GIT: the leg that was recorded and gated on NOWHERE until 2026-08-03. This is the exact
  //      shape the committed stepmain fixture had — cone digest matching, artifact matching, and the
  //      emit cone uncommitted at the stamped HEAD.
  stamp({ git: { head: '0'.repeat(40), cone_dirty_at_head: ['Dregg2/Circuit/Emit/KimchiStepMainCore.lean'] } });
  leg('L3 cone + artifact BOTH match, but the cone was uncommitted at HEAD', check, true);
  // (L3b) and a stamp from outside git at all.
  stamp({ git: { head: null, cone_dirty_at_head: [] } });
  leg('L3b stamped outside a git tree (no HEAD to check out)', check, true);
  // (L4) the ANCHOR AGAIN, so the four refusals above are not a floor that reds on everything.
  stamp({});
  leg('L4 anchor again: the honest stamp is still ACCEPTED', check, false);
  // ⚑ (L5) THE DISPLAY BUG THAT HID L3 IN PLAIN SIGHT. `gitContext` used to `.trim()` the whole
  //      `git status --porcelain` output before splitting, which ate the leading space of the FIRST
  //      line only — so `slice(3)` then ate the first character of the path and the sidecar recorded
  //      `etatheory/…`. A path this module reports must be one that exists.
  const realCone = leanConeDigest('Dregg2/Circuit/Emit/EmitStepMainJson.lean');
  const g = gitContext(realCone.files.map((f) => f.rel));
  const mangled = (g.cone_dirty_at_head ?? []).filter((p) => !existsSync(join(REPO_ROOT, p)));
  if (mangled.length) { console.log(`   RED  L5 gitContext reports paths that do not exist: ${mangled.join(', ')}`); bad++; }
  else console.log(`   ok   L5 every path gitContext reports EXISTS on disk`.padEnd(70)
    + ` (${g.cone_dirty_at_head?.length ?? 0} dirty cone file(s) right now)`);

  rmSync(d, { recursive: true, force: true });
  console.log();
  if (bad) { console.log(`emit-provenance --self-test: ${bad} LEG(S) FAILED`); process.exit(1); }
  console.log('emit-provenance --self-test: 8 legs green (3 anchors + 5 refusals, each naming staleness)');
}

if (process.argv[1] && resolve(process.argv[1]) === fileURLToPath(import.meta.url)) {
  // ── SCOPE ─ this pair is the ONLY copy; it prints on every run, pass or fail. It lives INSIDE the
  // CLI entry guard on purpose: five gates in this directory `import` this module, and a banner at
  // module scope would prepend itself to every one of their outputs. ────────────────────────────
  const SCOPE_ANSWERS =
    'over a SYNTHESISED temp artifact and a two-file FAKE cone, does requireFreshArtifact ACCEPT the honest '
    + 'stamp and REFUSE-as-StaleArtifact each of five bends (no stamp beside the artifact, a cone that has '
    + 'since moved, artifact bytes that are not the stamped ones, an emit cone uncommitted at the stamped '
    + 'HEAD, and a stamp from outside git) — plus, on the REAL tree, does every path gitContext reports for '
    + 'EmitStepMainJson.lean cone actually exist on disk?';
  const SCOPE_DOES_NOT_ANSWER =
    'whether any artifact or fixture in this tree is fresh. Seven of the eight legs run on inputs this file '
    + 'writes into a temp dir; what is measured is the FLOOR own accept/refuse behaviour. Each gate that '
    + 'delegates freshness to this module grades its own artifact, and none of that happens here.';
  console.log(`ANSWERS:         ${SCOPE_ANSWERS}`);
  console.log(`DOES NOT ANSWER: ${SCOPE_DOES_NOT_ANSWER}`);
  if (process.argv.includes('--self-test')) await selfTest();
  else { console.error('usage: node scripts/emit-provenance.mjs --self-test'); process.exit(2); }
}
