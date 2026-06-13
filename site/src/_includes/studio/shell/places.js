/**
 * places.js — the shell's curated place registry.
 *
 * A place is a destination the shell mounts inside its frame: same identity
 * context, same receipt stream, no full-page reset. The registry is
 * deliberately small — the shell carries the few app surfaces that are real
 * end-to-end places; everything mandate-shaped or demo-shaped lives in the
 * collapsed Experiments drawer, and the heavyweight inspector IDE is a tool.
 *
 * App places mount /starbridge-apps/<id>/pages/index.html with ?embedded=1
 * (the existing app-boot host bridge: in-frame runtime + postMessage link).
 */

export const PLACES = [
  {
    id: 'nameservice',
    label: 'Names',
    glyph: '@',
    what: 'the federation name directory — register, renew, transfer, resolve',
    page: '/starbridge-apps/nameservice/pages/index.html',
  },
  {
    id: 'identity',
    label: 'Identity',
    glyph: 'id',
    what: 'credential issuance and selective disclosure',
    page: '/starbridge-apps/identity/pages/index.html',
  },
  {
    id: 'governed-namespace',
    label: 'Governance',
    glyph: 'gov',
    what: 'route tables and proposals under a governing program',
    page: '/starbridge-apps/governed-namespace/pages/index.html',
  },
  {
    id: 'subscription',
    label: 'Subscriptions',
    glyph: 'sub',
    what: 'pub/sub topics with capability-gated publish and consume (the live encrypted-group organ is under Organs → Channels)',
    page: '/starbridge-apps/subscription/pages/index.html',
  },
];

/** Demoted: working surfaces that are mandate demos, not daily places. */
export const EXPERIMENTS = [
  {
    id: 'compartment-workflow-mandate',
    label: 'Workflow Mandate',
    glyph: 'wf',
    what: 'a DAG workflow mandate with a monotonic step cursor',
    page: '/starbridge-apps/compartment-workflow-mandate/pages/index.html',
  },
  {
    id: 'storage-gateway-mandate',
    label: 'Storage Gateway',
    glyph: 'vfs',
    what: 'a VFS gateway mandate with GET/PUT/LIST under a volume budget',
    page: '/starbridge-apps/storage-gateway-mandate/pages/index.html',
  },
];

/** Tools: full pages of their own; the shell links to them as places. */
export const TOOLS = [
  {
    id: 'workbench',
    label: 'Workbench',
    href: '/starbridge/workbench.html',
    what: 'the inspector IDE — every object as a dregg:// URI, raw JSON, time scrubber',
  },
  {
    id: 'explorer',
    label: 'Explorer',
    href: '/explorer/',
    what: 'browse a live node — cells, witnessed receipts, time travel',
  },
  {
    id: 'playground',
    label: 'Playground',
    href: '/playground/',
    what: 'drive the eight verbs against the in-browser wasm executor',
  },
  {
    id: 'studio',
    label: 'Studio',
    href: '/studio.html',
    what: 'author turns, predicates, and factories from generated catalogs',
  },
];

export function placeById(id) {
  return PLACES.find((p) => p.id === id) || EXPERIMENTS.find((p) => p.id === id) || null;
}
