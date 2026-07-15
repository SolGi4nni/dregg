# `assets/games/` — game art drop point + format spec

This is where hand-made / AI-generated game art lives. If you are here to **contribute art**,
read [`docs/CONTRIBUTING-ASSETS.md`](../../docs/CONTRIBUTING-ASSETS.md) first — it is the welcome
mat, the scout of how the engine actually renders, and the submission process. This file is the
terse spec + the directory map.

## Where things go

```
assets/games/
  descent/            The Descent (roguelite)
    characters/         player classes / hero portraits
    monsters/           enemies, wardens, bosses
    items/              loot, weapons, consumables, keys
    tiles/              environment / corridor / room tiles
  multiway-tug/        the card game
    cards/              favor-card faces + card backs
  automatafl/          the verified board game
    pieces/             piece art (currently unicode glyphs)
    board/              board / cell textures
  ui/
    icons/              buttons, status glyphs, affordance icons
  brand/
    logo/               token / project logo marks
    token/              token cards, OG images, microsite art
  _examples/           copy-me template SVGs (do not treat as real assets)
```

Each leaf directory takes the asset files **plus** a one-line entry in
[`NEEDED-ASSETS.md`](./NEEDED-ASSETS.md) so a reviewer can find and wire it.

## Format spec (what the engine consumes)

The engine's in-house art is **procedural SVG** — `dreggnet-sprite` renders a `128×128`
`viewBox` SVG from a content address (`dreggnet-sprite/src/svg.rs:88`, `CANVAS = 128`). Hand-made
art rides the same canvas so it drops into the same slots.

| Property | Value |
|---|---|
| **In-game sprite canvas** | `128×128` (`viewBox="0 0 128 128"`) — the engine's native size |
| **Preferred vector** | SVG, integer coordinates, no external refs, self-contained |
| **Raster (Midjourney/Grok)** | WebP (preferred) or PNG, **transparent background**, ship `512` source + `256` + `128` exports |
| **Card face (multiway-tug)** | `128×128` square (drop-in today) **or** `500×700` portrait (designed full-card slot) |
| **Brand logo** | square SVG **or** `512` PNG (+256, +128), transparent |
| **OG / social image** | `1200×630` PNG |
| **Transparency** | required for sprites/icons/logos — no full-canvas background rect |
| **Naming** | `kebab-case`, descriptive, no spaces: `salt-warden.webp`, `favor-gift.svg` |

**Match the designed look** (the deos-view palette, `deos-view/src/web.rs:1654`) — art sits on a
deep-navy board (`--bg #0b1020`, panels `--card #0f1830`, tiles `#181a20`):

```
bg #0b1020   panel #111a2e   card #0f1830   elev #152444   border #243352
fg #dfe8fb   muted #8fa2c4   accent #5cc9ff  head #7fdfe0
good #48d597 warn #f2c94c    bad #f8737f
```

Rarity accent colors (from `dreggnet-sprite/src/svg.rs:82`), if you tier an asset:
`common #9ca3af · uncommon #3fb950 · rare #3b82f6 · epic #a855f7 · legendary #f5b301`.

## How art reaches the screen (honest, per slot)

- **Brand / token / microsite art** — **works today.** Static files are already served
  (`launchpad-web/public/`, root `assets/`). Drop the file, reference it. Lowest friction; start here.
- **In-game sprites (Descent / cards / pieces)** — **needs one small wiring step.** The engine
  paints a `ViewNode::Tile { handle }` node (`deos-view/src/tree.rs:223`); today the web resolver
  (`dreggnet-web/src/sprite.rs:115` `tile_html`, `:133` `parse_handle`) only recognises
  `sprite:`/`asset:` handles and paints procedural SVG. A hand-art handle scheme (`art:<pack>/<name>`)
  + a `ServeDir` route over `assets/games/` is **designed, not yet built** — see
  `docs/CONTRIBUTING-ASSETS.md` § "The hand-art slot (designed)". A reviewer wires it when the first
  real pack lands. Your art does not block on it: submit the file + manifest entry.

Nothing on disk is loaded as game art today except fonts (`deos-view/assets/fonts/`); the sprite
layer is 100% generated. This directory is the deliberate slot for the hand-made layer.
