# Contributing game assets

Welcome — this is the guide for making and submitting **game art** (sprites, card faces, icons,
logos). It is written so you can pick one thing, make it, and open a PR the same afternoon.

If you write **procedural sprite renderers, `.scene` content, or procgen tables** instead of
hand-made art, that has its own guide: [`CONTENT-AND-ASSET-SPEC.md`](./CONTENT-AND-ASSET-SPEC.md).
This document is specifically for **hand-drawn / AI-generated (Midjourney, Grok, etc.) art**.

- **The pickable to-do list:** [`assets/games/NEEDED-ASSETS.md`](../assets/games/NEEDED-ASSETS.md)
- **The format spec + directory map:** [`assets/games/README.md`](../assets/games/README.md)
- **Copy-me templates:** [`assets/games/_examples/`](../assets/games/_examples/)

## How the games render art today (the honest scout)

Before you make art, here is what the engine actually consumes — so your art fits the real slots,
not an imagined pipeline.

**The portfolio is three verified games** (`docs/VERIFIED-GAME-PORTFOLIO.md`): *The Descent*
(roguelite), *multiway-tug* (card game), *automatafl* (board game), rendered through a shared
themed web renderer (`deos-view`) and the web surface (`dreggnet-web`).

**Almost all art today is procedural — generated, not drawn.** Concretely:

- **Sprites are generated from a content address.** `dreggnet-sprite` is a pure function
  `AssetId → 128×128 SVG`: it seeds a `dregg-dice` draw stream off the asset's blake3 address and
  draws each trait (blade shape, material, rune, rarity, …), composing layered SVG
  (`dreggnet-sprite/src/lib.rs`, `svg.rs`, `card.rs`, `gear.rs`). Two kinds ship: **gear** (a
  weapon emblem) and **card** (a sigil emblem). Same asset ⇒ byte-identical art, so anyone
  re-derives and verifies it. The web serves these at `GET /sprite/{kind}/{ref}` and shows a
  gallery at `/gallery` (`dreggnet-web/src/sprite.rs`).
- **Board cells and icons are unicode glyphs.** automatafl and multiway-tug render as a
  `CoordGrid` whose cells are glyph strings (`deos-view/src/web.rs:276`); status/affordance
  indicators are `Icon { glyph }` (`deos-view/src/tree.rs:183`). Text, not images.
- **The only art loaded from disk is fonts** (`deos-view/assets/fonts/`). There is **no raster
  image loader in the game path** — nothing reads a PNG/WebP off disk as sprite art today.
- **Ownership vs. looks are separate layers.** `dreggnet-asset` is the *verifiable ownership*
  primitive (a content-addressed, transfer-gated note lineage with a committed `trait_root`); it
  carries no pixels. The sprite layer *reads* that identity and *draws* it.

**What that means for you:** the games are procedural-first, and hand-made art is a **new layer**
we are opening on purpose. The design principle the procedural art rides — *provable rarity +
deterministic, reproducible render* (`CONTENT-AND-ASSET-SPEC.md`) — does **not** constrain
hand-made art: your art is referenced by name, not re-derived from a seed. You are adding the
human-crafted look on top of the generated substrate.

## The format (short version)

Full table in [`assets/games/README.md`](../assets/games/README.md). The essentials:

- **In-game sprites:** `128×128` — the engine's native canvas (`CANVAS = 128`,
  `dreggnet-sprite/src/svg.rs:88`). SVG preferred; raster as **WebP/PNG with a transparent
  background**, shipped at `512` (source) + `256` + `128`.
- **Card faces:** `128×128` square drops into the existing card slot; `500×700` portrait is the
  designed full-card-face slot.
- **Brand/token art:** square logo (SVG or `512` PNG), `1200×630` OG image.
- **Match the board's designed look** — a deep-navy palette (`--bg #0b1020`, `--accent #5cc9ff`,
  `--fg #dfe8fb`; full palette in the README). Transparent backgrounds for anything that sits on
  the board.
- **Prepping AI art (Midjourney/Grok):** generate large, **remove the background** (so it composes
  on the navy board), crop square to the subject, export WebP/PNG at 512, then downscale to 256 and
  128. Keep the palette close to the board theme, or lean on the rarity accent colors.

## Where art plugs in (per slot, honest)

- **Brand / token / microsite — works right now.** Static files are already served
  (`launchpad-web/public/`, the root `assets/` holds the current brand PNGs). Add your file and
  reference it; nothing to wire. **This is the best place to start.**
- **In-game sprites — one small wiring step (designed, not yet built).** See below.

### The hand-art slot (designed)

The engine's paint slot is `ViewNode::Tile { handle, w, h }` (`deos-view/src/tree.rs:223`) — "a
card-referenced native paint region; an unresolvable handle paints a labelled placeholder." The web
resolver `tile_html`/`parse_handle` (`dreggnet-web/src/sprite.rs:115,133`) currently recognises only
`sprite:{kind}:{ref}` and `asset:{kind}:{ref}` handles and paints procedural SVG.

The hand-art path is a small, additive change a maintainer wires when the first real pack lands:

1. A **static route** — a `ServeDir` over `assets/games/` (e.g. `GET /art/*path`), added beside
   `sprite_router` (`dreggnet-web/src/sprite.rs:159`).
2. A **handle scheme** — teach `parse_handle` an `art:<pack>/<name>` handle that resolves to
   `<img src="/art/<pack>/<name>.webp" width=w height=h>` instead of inline SVG.

That's it — no kernel or crate-interface change, and it does not touch the verified game logic.
Until it lands, your sprite still belongs in the repo: submit the file + the manifest entry, and it
gets wired at review. **Do not block on the wiring.**

## Submitting (the process)

1. **Pick a row** from [`NEEDED-ASSETS.md`](../assets/games/NEEDED-ASSETS.md). Grabbing a P1 brand
   asset is the fastest first win. Copy a template from `_examples/` if you want a starting frame.
2. **Make it** to the format above. For raster, include the 512/256/128 exports.
3. **Drop the file** into the right `assets/games/<game>/<slot>/` directory, `kebab-case` named.
4. **Add one line** to `NEEDED-ASSETS.md`: tick the box and note the filename.
5. **Open a PR** titled `assets(<game>): <what>` — e.g. `assets(descent): salt-warden monster`.
   Include a quick preview (drag the image into the PR description) and say which row it fills.
6. **Review** checks: right size/format, transparent where required, palette-consistent, named per
   convention. In-game sprites also get their `Tile` handle wired (or the `art:` slot enabled if
   yours is the first). Brand assets merge as-is.

Small PRs are ideal — one asset (or one coherent set) per PR reviews and lands fast. Thank you for
making the games look like something. ٩( ᐛ )و
