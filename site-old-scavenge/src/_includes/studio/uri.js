/**
 * dregg:// URI parsing and formatting.
 *
 * Format: dregg://<kind>/<id>[@<height>][/<sub>...]
 *
 * Examples:
 *   dregg://cell/abc123
 *   dregg://cell/abc123@42
 *   dregg://cell/abc123/cap/dns
 *   dregg://turn/deadbeef
 *
 * Resolution is the runtime's job; this module only parses.
 */

const KIND_RX = /^dregg:\/\/([a-z-]+)\/([^?#@/]+)(?:@([0-9a-f]+|[0-9]+))?(?:\/(.*))?$/i;

export function parseRef(s) {
  if (typeof s !== 'string') throw new TypeError('ref must be a string');
  const m = KIND_RX.exec(s.trim());
  if (!m) throw new Error(`not a dregg ref: ${s}`);
  const [, kind, id, height, sub] = m;
  return {
    kind,
    id,
    height: height != null ? height : null,
    sub: sub ? sub.split('/') : [],
    toString() { return s; },
  };
}

export function isRef(s) {
  return typeof s === 'string' && KIND_RX.test(s);
}

export function makeRef(kind, id, opts = {}) {
  let s = `dregg://${kind}/${id}`;
  if (opts.height != null) s += `@${opts.height}`;
  if (opts.sub?.length) s += `/${opts.sub.join('/')}`;
  return s;
}
