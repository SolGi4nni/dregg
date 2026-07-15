# Needed assets — the pickable list

Pick any row, make it, open a PR (see [`docs/CONTRIBUTING-ASSETS.md`](../../docs/CONTRIBUTING-ASSETS.md)).
Sizes/formats are in [`README.md`](./README.md). **P1 = highest leverage / lowest friction.**

When you claim a row, it helps to say so in the PR title (`assets(descent): salt-warden monster`).
When an asset lands, tick its box and add the real filename.

## The Descent (roguelite) — `descent/`

The daily descent + no-cheat board (`dreggnet-web` descent surface, `spween-dregg`,
`procgen-dregg` biomes/monsters). Art here is currently entirely procedural/text.

| Pri | Slot | What | Format |
|---|---|---|---|
| P2 | monsters/ | **Salt warden** — the daily's gate boss | 128 sprite (SVG or WebP) |
| P2 | monsters/ | Biome monster set — 3–5 per biome (`procgen-dregg` has 6 biomes) | 128 sprites |
| P2 | items/ | **Hoard key** + **the hoard** (win item) | 128 sprites |
| P3 | items/ | Loot/weapon/consumable icons — blade, potion, torch, gold | 128 sprites |
| P3 | characters/ | Player class marks (the run-card shows class+level) | 128 sprites |
| P3 | tiles/ | Corridor / room / vault tile art | 128 sprites, tileable |

## multiway-tug (card game) — `multiway-tug/`

21-card favor deck; four action types (Secret / Discard / Gift / Competition). Cards are owned
`dreggnet-asset` notes; the printed face is procedural today.

| Pri | Slot | What | Format |
|---|---|---|---|
| P2 | cards/ | **Card back** (one, shared) | 128 square + 500×700 |
| P2 | cards/ | **Favor-card faces** — one per action type (4) | 128 square (drop-in) |
| P3 | cards/ | Full-art card faces — the collectible tier | 500×700 portrait |

## automatafl (board game) — `automatafl/`

n=2 verified board; renders as a `CoordGrid` of unicode glyph cells today
(`deos-view` `CoordGrid`, `dregg-automatafl` surface).

| Pri | Slot | What | Format |
|---|---|---|---|
| P3 | pieces/ | Piece art to replace the unicode glyphs | 128 sprites, transparent |
| P3 | board/ | Board / cell texture (light+dark cell) | 128 tiles |

## UI — `ui/icons/`

Shared across the portfolio (deos-view affordances, catalog, run-cards).

| Pri | Slot | What | Format |
|---|---|---|---|
| P2 | icons/ | Status glyphs — verified ✓ / refused ✕ / pending | 128 or 64 SVG |
| P3 | icons/ | Affordance/button icons — play, verify, share, inventory | 64 SVG |

## Brand / token / microsite — `brand/`  ← START HERE (works today)

Static art the launchpad + microsite serve directly — no engine wiring needed.

| Pri | Slot | What | Format |
|---|---|---|---|
| **P1** | logo/ | **$DREGG / project logo mark** — square, transparent | 512 PNG (+256,+128) + SVG |
| **P1** | token/ | **OG / social share image** | 1200×630 PNG |
| P2 | token/ | Token card art (launch/create/token pages) | 512 PNG |
| P2 | logo/ | Favicon set | 32/48/128 PNG + SVG |

---

**First three to grab:** `brand/logo` logo mark (P1, drop-in), `brand/token` OG image (P1, drop-in),
`descent/monsters` salt warden (P2, the daily's face). See the examples in `_examples/`.
