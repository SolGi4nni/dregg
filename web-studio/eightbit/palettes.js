// palettes.js — retro color palettes for the 8-bit shader. Pure data + a hex
// helper; no DOM, no deps. Importable in the browser (ES module) and in node
// (the headless verifier imports this directly).
//
// A palette is an array of [r,g,b] triples (0..255). The shader quantizes every
// downsampled pixel to its nearest palette color. Two of these — `dregg-navy`
// and `dregg-dark` — are lifted from the real product theme so shader output
// composes with the deos-view board (assets/games README navy: #0b1020 /
// #5cc9ff / #dfe8fb) and the DrEX v2 dark theme (styles.css: #0d1117 / #58a6ff
// / #3fb950 / #d29922 / #f85149 / #f0c14b / #bc8cff).

/** Parse "#rrggbb" (or "rrggbb") to [r,g,b]. */
export function hex(h) {
  const s = h.replace('#', '');
  return [
    parseInt(s.slice(0, 2), 16),
    parseInt(s.slice(2, 4), 16),
    parseInt(s.slice(4, 6), 16),
  ];
}

const P = (...hexes) => hexes.map(hex);

// The palette registry. id → { name, colors }.
export const PALETTES = {
  // Classic Game Boy DMG 4-shade green.
  gameboy: {
    name: 'Game Boy (DMG)',
    colors: P('#0f380f', '#306230', '#8bac0f', '#9bbc0f'),
  },
  // 1-bit high-contrast (Obra Dinn feel), navy/cream tuned to the board theme.
  '1bit-navy': {
    name: '1-bit (navy)',
    colors: P('#0b1020', '#dfe8fb'),
  },
  // CGA mode 4 palette 1 (high-intensity): black / cyan / magenta / white.
  cga: {
    name: 'CGA (mode 4)',
    colors: P('#000000', '#55ffff', '#ff55ff', '#ffffff'),
  },
  // A PICO-8-ish 16-color workhorse — broad, friendly for arbitrary art.
  pico8: {
    name: 'PICO-8 (16)',
    colors: P(
      '#000000', '#1d2b53', '#7e2553', '#008751',
      '#ab5236', '#5f574f', '#c2c3c7', '#fff1e8',
      '#ff004d', '#ffa300', '#ffec27', '#00e436',
      '#29adff', '#83769c', '#ff77a8', '#ffccaa',
    ),
  },
  // DREGG NAVY — the game board's designed look (assets/games README).
  // Deep navy ground, cyan accent, cream ink, plus rarity-accent ramp.
  'dregg-navy': {
    name: 'dregg navy (board theme)',
    colors: P(
      '#0b1020', '#141b33', '#26314f', '#3a4a73',
      '#5cc9ff', '#8fe0ff', '#dfe8fb', '#ffffff',
      '#f0c14b', '#bc8cff', '#3fb950', '#f85149',
    ),
  },
  // DREGG DARK — the DrEX v2 product theme (styles.css tokens).
  'dregg-dark': {
    name: 'dregg dark (DrEX theme)',
    colors: P(
      '#0d1117', '#161b22', '#1c2230', '#2a3240',
      '#6e7681', '#9da7b3', '#e6edf3', '#58a6ff',
      '#3fb950', '#d29922', '#f85149', '#f0c14b',
      '#bc8cff',
    ),
  },
};

export const DEFAULT_PALETTE = 'dregg-navy';

/** List of {id, name, size} for building UI selectors. */
export function paletteList() {
  return Object.entries(PALETTES).map(([id, p]) => ({
    id, name: p.name, size: p.colors.length,
  }));
}
