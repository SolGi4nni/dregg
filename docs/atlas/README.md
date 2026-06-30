# dregg architecture atlas

A navigable, grounded, honest map of everything across **dregg**.
Vanilla HTML/CSS/JS, no build step required to develop.

## Files

- `index.html` — the page template + the app logic (DOM build, filters, map, views). **Source — edit this.**
- `data.js` — the grounded model (`ATLAS`, `STATUS`). **Source — edit this.**
- `styles.css` — styling. **Source — edit this.**
- `build.sh` — inlines `styles.css` + `data.js` into `index.html` → emits `atlas.html`.
- `atlas.html` — **generated, single self-contained file. Do not hand-edit — it is regenerated.**

## Develop

Open `index.html` directly, or serve from the repo root so the `file:line` source
refs are clickable:

```
cd ~/dev/breadstuffs && python3 -m http.server   # then visit localhost:8000/docs/atlas/
```

## Build & share

Edit the sources, then regenerate the single shareable file:

```
bash docs/atlas/build.sh
```

This produces `docs/atlas/atlas.html` — everything inline, no external local
file refs. Send it / host it anywhere; it opens standalone via `file://`.

Note: in the single-file `atlas.html` the `file:line` source refs render as
links/text but cannot resolve to the repo when opened via `file://` (there is no
repo to serve). That is expected — the single file is for shareability of the
*map*; use the served split version when you want clickable source.
