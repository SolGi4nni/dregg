/**
 * resolver.js — the ONE dregg:// link resolver for the whole image.
 *
 * Every surface (explorer / playground / studio / learn) names objects with
 * the same dregg:// scheme; this module maps a ref to the surface + URL that
 * inspects it, so any cell id, receipt hash, verb chip, constraint kind,
 * guarantee badge, or factory vk ANYWHERE in the UI can be opened with one
 * resolver. Pure (node-importable); browser callers use `surfaceHref` which
 * applies the deployed BASE_PATH automatically.
 *
 * The map:
 *   dregg://cell/<id>             → explorer  /explorer/?at=…   (live object)
 *   dregg://cell-history/<id>     → explorer  (receipt time-travel)
 *   dregg://receipt/<hash>        → explorer  (witnessed receipt)
 *   dregg://turn/<hash>           → explorer
 *   dregg://block/<fed>/<h>       → explorer
 *   dregg://block-dag/<fed>       → explorer
 *   dregg://capability/<id>, token, intent, federation[-list], activity,
 *   capability-list, receipt-list, cell-list                → explorer
 *   dregg://council/<cell-id>     → explorer  (polis inspectors)
 *   dregg://constitution/<cell-id>→ explorer
 *   dregg://mandate/<cell-id>     → explorer
 *   dregg://amendment-ceremony/<cell-id>[/old/<id>/new/<id>] → explorer
 *   dregg://verb/<name>           → docs      substances rung anchor #verb-<name>
 *   dregg://constraint/<kind>     → studio    predicate browser entry (?constraint=…#predicates)
 *   dregg://guarantee/<letter>    → docs      trust-boundary rung anchor #guarantee-<letter>
 *   dregg://factory/<vk-or-key>   → studio    factory composer worked example (?factory=…#factory)
 *   dregg://effect/<name>         → studio    effect catalog (?effect=…#catalog)
 *   dregg://concept/<rung>        → docs      /learn/concepts/<rung>.html
 */

const EXPLORER_KINDS = new Set([
  'cell', 'cell-list', 'cell-history', 'receipt', 'receipt-list', 'turn',
  'block', 'block-dag', 'capability', 'capability-list', 'token', 'intent',
  'intent-list', 'federation', 'federation-list', 'activity',
  'council', 'constitution', 'mandate', 'amendment-ceremony',
]);

const CONCEPT_RUNGS = new Set([
  'turn', 'substances', 'guards', 'receipts', 'light-client', 'userspace', 'trust-boundary',
]);

/**
 * Resolve a dregg:// ref to { surface, href } (href WITHOUT base path).
 * Throws on non-refs; returns null for unknown kinds.
 */
export function resolveRef(uri) {
  const m = /^dregg:\/\/([a-z-]+)\/(.+)$/i.exec(String(uri).trim());
  if (!m) throw new Error(`not a dregg ref: ${uri}`);
  const kind = m[1].toLowerCase();
  const rest = m[2];
  const id = rest.split('/')[0].split('@')[0];

  if (EXPLORER_KINDS.has(kind)) {
    return { surface: 'explorer', href: `/explorer/?at=${encodeURIComponent(uri)}` };
  }
  switch (kind) {
    case 'verb':
      return { surface: 'learn', href: `/learn/concepts/substances.html#verb-${encodeURIComponent(id)}` };
    case 'constraint':
      return { surface: 'studio', href: `/studio.html?constraint=${encodeURIComponent(id)}#predicates` };
    case 'guarantee':
      return { surface: 'learn', href: `/learn/concepts/trust-boundary.html#guarantee-${encodeURIComponent(id)}` };
    case 'factory':
      return { surface: 'studio', href: `/studio.html?factory=${encodeURIComponent(id)}#factory` };
    case 'effect':
      return { surface: 'studio', href: `/studio.html?effect=${encodeURIComponent(id)}#catalog` };
    case 'concept':
      if (!CONCEPT_RUNGS.has(id)) return null;
      return { surface: 'learn', href: `/learn/concepts/${id}.html` };
    default:
      return null;
  }
}

/** The docs rung that explains each inspector kind ("what is this?"). */
export const RUNG_FOR_KIND = {
  cell: 'substances',
  'cell-list': 'substances',
  capability: 'substances',
  'capability-list': 'substances',
  token: 'substances',
  turn: 'turn',
  receipt: 'receipts',
  'receipt-list': 'receipts',
  'witnessed-receipt': 'receipts',
  'cell-history': 'receipts',
  proof: 'receipts',
  block: 'light-client',
  'block-dag': 'light-client',
  federation: 'light-client',
  'federation-list': 'light-client',
  'cell-program': 'guards',
  predicate: 'guards',
  constraint: 'guards',
  'factory-descriptor': 'userspace',
  factory: 'userspace',
  council: 'userspace',
  constitution: 'userspace',
  mandate: 'userspace',
  'amendment-ceremony': 'userspace',
};

/** dregg://concept/<rung> ref for an inspector kind, or null. */
export function rungRef(kind) {
  const rung = RUNG_FOR_KIND[kind];
  return rung ? `dregg://concept/${rung}` : null;
}

/**
 * The deployed site base path, derived from where THIS module is served
 * (e.g. https://host/dregg/_includes/studio/resolver.js → "/dregg"). Works
 * for both the root deploy ("" base) and GitHub-Pages-style subpaths.
 */
export function siteBase() {
  try {
    const p = new URL(import.meta.url).pathname;
    const i = p.indexOf('/_includes/studio/resolver.js');
    if (i > 0) return p.slice(0, i);
  } catch { /* non-browser or odd embedding */ }
  return '';
}

/** Browser-facing: absolute href (base-path applied) for a dregg:// ref. */
export function surfaceHref(uri) {
  const r = resolveRef(uri);
  return r ? siteBase() + r.href : null;
}

export function isResolvable(uri) {
  try { return resolveRef(uri) != null; } catch { return false; }
}
