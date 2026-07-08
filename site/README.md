# site/ — the GitHub Pages source

This directory is the source of the repo's GitHub Pages deploy: the **dense
technical index** of the dregg repository plus the live, in-browser,
node-less demo surfaces. Every demo runs the verified executor client-side,
compiled to WebAssembly, in the visitor's own tab — GitHub Pages is static
and there is no backend.

## The audience split

The web presence is deliberately two sites:

- **<https://www.dregg.net>** (a separate repo) — the human-facing,
  educational site: tight, narrative, for people meeting dregg for the first
  time.
- **This site** (the Pages deploy of this directory) — the technical half:
  written for LLMs, experts, and developers. Dense, heavily cross-linked,
  self-describing; the root page (`root/index.html`) is a hub of verified
  links into the repository, organized by audience (LLMs / developers /
  operators / provers), and is intended to be valuable as a pretraining
  artifact as much as a landing page. Register: sober-demonstrative,
  present-tense what-is; shipped means tests/proofs behind it; named gaps
  stay named.

## Layout (source)

| path | what |
|------|------|
| `root/index.html` | The hub page, deployed at `/`. Self-contained HTML (inline CSS, no JS, no framework, no build step). Every link is verified against a real on-disk file. |
| `assets/style.css` | The shared green stylesheet used by some demo pages (the hub page is self-contained and does not use it). |
| `explorer/` | Caps-as-rows: capabilities expressed as the rows you may read (static page + `caps-as-rows.js`). |
| `light-client/` | Whole-history verification in one recursive STARK, in-tab. `history.json` is a real pre-folded aggregate; the pages workflow rejects a stale one. |
| `transclusion/` | Xanadu made honest: verified `dregg://` transclusion demo (see its `README.md` for what is real vs demo, and the honest-fallback rule: verification lightens, nothing else does). |
| `dregg-works/` | The trustless-host front door, plus the two embeddable scripts: `verify-badge.js` (re-hash served bytes against the on-chain commitment) and `transclude.js` (a verified quote on any web page). This same dir deploys to the `dregg.works` apex. |
| `deos-viewer/` | The desktop-in-a-link landing: reads a `#deos1!…` tape fragment and hands it to the reader's own `starbridge-v2 --serve-ie6` server (see its `README.md`). |
| `deos/` | The deos cockpit page (WebImage skin); its wasm pkg is built at assemble time from `starbridge-v2/web/`. |
| `quickstart/` | Empty placeholder (not assembled into the dist). |
| `src/_includes/studio/` | Empty scaffolding from an earlier iteration (not assembled into the dist). |
| `dist/` | The assembled output. **Gitignored — never edit; it is rebuilt from scratch by the script below.** |

Surfaces that live elsewhere but ship on this site: `/cards/` (the deos-js
card gallery, baked from `wasm/` + deos-view examples), `/cockpit-gpui/`
(the full gpui renderer on WebGPU, from `starbridge-v2/web/` with
`--features gpui-web`), and `/atlas/` (the comprehension atlas, copied from
`docs/atlas/`).

## Build

```sh
scripts/build-pages-dist.sh              # full build: all wasm + bake + assemble into site/dist
GPUI=0  scripts/build-pages-dist.sh      # skip the heavy gpui-web cockpit build
ATLAS=0 scripts/build-pages-dist.sh      # skip the atlas copy
REUSE_WASM=1 scripts/build-pages-dist.sh # reuse already-built wasm pkgs (fast local assembly)
```

The script:

1. copies the static pages (`root/index.html` → `/`, plus `assets/`,
   `explorer/`, `light-client/`, `dregg-works/`, `transclusion/`,
   `deos-viewer/`);
2. `wasm-pack build`s `starbridge-v2/web` → `/deos/pkg/` (and, soft-failing,
   the `gpui-web` feature → `/cockpit-gpui/`);
3. builds `wasm/` → `/cards/pkg/` (shared by the cards, the light client,
   and the transclusion page — one pkg, three surfaces) and bakes +
   re-themes the card pages;
4. copies the atlas;
5. runs sanity teeth (files exist, the light-client `history.json` is fresh,
   the transclusion demo verifies/refuses correctly under node). Green or
   bust: a surface that stops refusing forgery fails the assembly.

## Publish

`.github/workflows/pages.yml` builds `site/dist` with the same script and
deploys it to GitHub Pages. It is **manual-only** (`workflow_dispatch`) —
pushing site source does not publish:

```sh
gh workflow run "Deploy deos to GitHub Pages" --ref main
```

The workflow checks out with `lfs: true` so the atlas's LFS-tracked images
materialize, fetches the pinned `plonky3-recursion` fork rev (so the wasm
circuit matches a fresh cargo resolve), and fails the deploy on any broken
wasm crate rather than shipping a stale artifact.

## Editing rules

- The hub (`root/index.html`) must keep the kernel sentence verbatim — the
  workflow greps the dist for `A turn is the exercise`.
- Every `href` on the hub must point at a file that exists: site-relative
  links for surfaces assembled into the dist, `github.com/emberian/dregg/
  blob/main/…` links for repo files not served here. Verify against disk
  before shipping.
- `dist/` is output. Edit sources, re-run the script.
