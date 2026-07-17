// validate:extension-package — drift guard for the MV3 Cipherclerk package.
//
// Closes #7 (manifest reference drift) and the residual half of #8 (permission
// drift: the `alarms` gap is already fixed in both manifests; this keeps it and
// its siblings from silently regressing).
//
// Two checks, both fail-closed (exit 1) so CI catches drift before a broken
// package ships:
//   1. PERMISSION DRIFT — scan src/** for chrome.<api>. / browser.<api>. calls,
//      map each api to the MV3 permission it needs, and assert that permission
//      is declared in BOTH manifest.json and manifest-firefox.json. Used-but-
//      undeclared fails; declared-but-unused warns (over-permission).
//   2. REFERENCE DRIFT — every file a manifest references (service worker,
//      content scripts, web-accessible resources, popup, icons, options page)
//      plus the build.mjs entrypoints must exist on disk.
//
// Dependency-free: Node built-ins only. Run with `npm run validate:extension-package`
// or `node scripts/validate-package.mjs` from the extension/ dir.

import { readFileSync, existsSync, readdirSync, statSync } from 'node:fs';
import { join, dirname, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';

const EXT_ROOT = resolve(dirname(fileURLToPath(import.meta.url)), '..');
const SRC_DIR = join(EXT_ROOT, 'src');
const MANIFESTS = ['manifest.json', 'manifest-firefox.json'];

const errors = [];
const warnings = [];
const fail = (m) => errors.push(m);
const warn = (m) => warnings.push(m);

// ── api → MV3 permission map ────────────────────────────────────────────────
// Hardcoded to the APIs the source ACTUALLY uses (grep chrome.<api>./browser.<api>.).
// Keep this list explicit and small; add an entry when a new api appears.
//   baseline: true  → available without any declared permission (MV3 always-on).
//   requires: [...] → satisfied if ANY listed permission is declared.
// Conservative-by-design: where a permission is genuinely optional for the calls
// we make (chrome.tabs is only gated for cross-tab url/title reads — we only
// create/sendMessage/onRemoved), we accept the weaker grant rather than fail a
// correct build.
const API_PERMISSIONS = {
  storage: { requires: ['storage'] },
  alarms: { requires: ['alarms'] },
  contextMenus: { requires: ['contextMenus'] },
  runtime: { baseline: true }, // messaging/getURL — always available in MV3
  action: { baseline: true }, // the toolbar action; gated by the `action` key, not a permission
  windows: { baseline: true }, // window create/onRemoved need no permission
  // tabs.create / sendMessage / onRemoved need no `tabs` permission; activeTab
  // is sufficient for the active-tab reads we do. Accept either — don't force
  // the broad `tabs` grant on a build that gets by with activeTab.
  tabs: { requires: ['tabs', 'activeTab'] },
};

// ── collect source files ────────────────────────────────────────────────────
function walk(dir) {
  const out = [];
  for (const name of readdirSync(dir)) {
    const p = join(dir, name);
    if (statSync(p).isDirectory()) out.push(...walk(p));
    else if (/\.(ts|tsx|js|mjs)$/.test(name)) out.push(p);
  }
  return out;
}

// ── check 1: permission drift ───────────────────────────────────────────────
function collectUsedApis() {
  const used = new Map(); // api -> Set(relative file paths)
  const re = /\b(?:chrome|browser)\.([a-zA-Z_$][a-zA-Z0-9_$]*)\b/g;
  for (const file of walk(SRC_DIR)) {
    const text = readFileSync(file, 'utf8');
    let m;
    while ((m = re.exec(text)) !== null) {
      const api = m[1];
      if (!used.has(api)) used.set(api, new Set());
      used.get(api).add(file.slice(EXT_ROOT.length + 1));
    }
  }
  return used;
}

function checkPermissions(manifests) {
  const used = collectUsedApis();
  // permissions required by used apis (union across apis), tracking which apis need them
  const requiredPerms = new Map(); // perm-satisfier-signature -> {apis, options}

  for (const [api, files] of used) {
    const spec = API_PERMISSIONS[api];
    if (!spec) {
      // Unknown api — conservative: warn so a human extends the map, don't block.
      warn(`unknown extension api chrome.${api} (used in ${[...files][0]}); ` +
        `add it to API_PERMISSIONS in validate-package.mjs to check its permission`);
      continue;
    }
    if (spec.baseline) continue;
    const options = spec.requires;
    // For each manifest, require at least one of `options` to be declared.
    for (const { name, perms } of manifests) {
      const satisfied = options.some((p) => perms.has(p));
      if (!satisfied) {
        fail(`permission drift: chrome.${api} is used (e.g. ${[...files][0]}) but ` +
          `none of [${options.join(', ')}] is declared in ${name}`);
      }
    }
    requiredPerms.set(api, options);
  }

  // declared-but-unused (over-permission) — warn only.
  // A declared permission is "used" if some used api lists it as a satisfier.
  const satisfierPerms = new Set();
  for (const [, options] of requiredPerms) options.forEach((p) => satisfierPerms.add(p));
  for (const { name, perms } of manifests) {
    for (const p of perms) {
      if (!satisfierPerms.has(p)) {
        warn(`over-permission: ${name} declares "${p}" but no scanned api requires it`);
      }
    }
  }
}

// ── check 2: reference drift ────────────────────────────────────────────────
function refExists(rel, origin) {
  const p = join(EXT_ROOT, rel);
  if (!existsSync(p)) fail(`dangling reference in ${origin}: ${rel} does not exist on disk`);
}

function checkReferences(manifest, name) {
  // background
  const bg = manifest.background || {};
  if (bg.service_worker) refExists(bg.service_worker, `${name} background.service_worker`);
  for (const s of bg.scripts || []) refExists(s, `${name} background.scripts`);
  // content scripts
  for (const cs of manifest.content_scripts || []) {
    for (const j of cs.js || []) refExists(j, `${name} content_scripts.js`);
    for (const c of cs.css || []) refExists(c, `${name} content_scripts.css`);
  }
  // web accessible resources
  for (const war of manifest.web_accessible_resources || []) {
    for (const r of war.resources || []) refExists(r, `${name} web_accessible_resources`);
  }
  // action
  const action = manifest.action || {};
  if (action.default_popup) refExists(action.default_popup, `${name} action.default_popup`);
  for (const size of Object.keys(action.default_icon || {})) {
    refExists(action.default_icon[size], `${name} action.default_icon.${size}`);
  }
  // icons
  for (const size of Object.keys(manifest.icons || {})) {
    refExists(manifest.icons[size], `${name} icons.${size}`);
  }
  // options page
  const opts = manifest.options_ui || {};
  if (opts.page) refExists(opts.page, `${name} options_ui.page`);
}

// build.mjs entrypoints — the source files esbuild bundles into dist/.
function checkBuildEntrypoints() {
  const buildSrc = readFileSync(join(EXT_ROOT, 'build.mjs'), 'utf8');
  const block = buildSrc.match(/entryPoints\s*:\s*\[([^\]]*)\]/);
  if (!block) {
    warn('could not parse entryPoints from build.mjs (skipping entrypoint check)');
    return;
  }
  const entries = [...block[1].matchAll(/['"]([^'"]+)['"]/g)].map((m) => m[1]);
  if (entries.length === 0) warn('build.mjs entryPoints array is empty');
  for (const e of entries) refExists(e, 'build.mjs entryPoints');
}

// ── run ─────────────────────────────────────────────────────────────────────
function main() {
  const parsed = [];
  for (const name of MANIFESTS) {
    const path = join(EXT_ROOT, name);
    if (!existsSync(path)) {
      fail(`manifest missing: ${name}`);
      continue;
    }
    let manifest;
    try {
      manifest = JSON.parse(readFileSync(path, 'utf8'));
    } catch (e) {
      fail(`${name} does not parse as JSON: ${e.message}`);
      continue;
    }
    parsed.push({ name, manifest, perms: new Set(manifest.permissions || []) });
    checkReferences(manifest, name);
  }

  if (parsed.length === MANIFESTS.length) checkPermissions(parsed);
  checkBuildEntrypoints();

  for (const w of warnings) console.warn(`warn: ${w}`);
  if (errors.length > 0) {
    for (const e of errors) console.error(`FAIL: ${e}`);
    console.error(`\nvalidate:extension-package FAILED with ${errors.length} error(s).`);
    process.exit(1);
  }
  console.log(
    `validate:extension-package OK — permissions + references consistent across ` +
    `${MANIFESTS.join(', ')}` + (warnings.length ? ` (${warnings.length} warning(s))` : ''),
  );
}

main();
