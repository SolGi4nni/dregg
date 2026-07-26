#!/usr/bin/env bash
# Assemble the GitHub Pages dist: a LAYERED site — a sober landing that opens into
# the live, in-browser, node-LESS deos.
#
# The landing (/) is plain static HTML on a shared green stylesheet (site/assets/).
# It explains what dregg/deos IS and links into the wonder layer. Every demo surface
# below runs CLIENT-SIDE in WebAssembly: the verified executor runs in the visitor's
# own tab, firing real cap-gated verified turns, leaving real receipts. No backend.
#
# Layout of the produced dist/:
#   /                  — the sober landing (what-is / play / quickstart / does / enables).
#                        Static HTML + site/assets/style.css (the salvaged green look).
#   /deos/             — the deos cockpit (the WebImage launcher): cells · inspector ·
#                        affordances · ocap web. Click an authorized affordance → a REAL
#                        verified turn in-tab. wasm: starbridge-v2/web (gpui-FREE skin).
#   /cockpit-gpui/     — the FULL gpui renderer on a WebGPU canvas (same in-tab executor).
#                        Heavier; needs WebGPU. wasm: starbridge-v2/web --features gpui-web.
#   /cards/            — the deos-js card gallery: counter · reflective inspector · tally
#                        board · kv-store · doc-collab. Each a real verified turn in-tab.
#                        wasm: wasm/ (the card/runtime bindings). Re-themed green.
#   /explorer/         — caps-as-rows: your capabilities expressed as the rows you may read
#                        (the browser twin of the pg-dregg cap-gated RLS cookbook).
#   /light-client/     — verify a whole finalized history in ONE recursive proof, in-tab,
#                        re-witnessing nothing. wasm: reuses /cards/pkg/dregg_wasm.js.
#   /paper/            — the paper landing + a PDF compiled from paper/main.typ in this build.
#   /papers/direct-logic-arithmetization/direct-logic-arithmetization.pdf
#                      — the direct-logic research report, compiled when its source exists.
#   /transclusion/     — Xanadu made honest: transclude a span (a verified dregg://
#                        finalized read), amend the source (live follows, snapshot pins),
#                        forge (REFUSED), receipt-pinned backlinks. wasm: reuses
#                        /cards/pkg/dregg_wasm.js (bindings_transclusion).
#   /atlas/            — the interactive atlas (the whole protocol + UI surfaces).
#
# Usage:
#   scripts/build-pages-dist.sh           # full build (all wasm + bake + assemble)
#   GPUI=0 scripts/build-pages-dist.sh    # skip the heavy gpui-web cockpit build
#   ATLAS=0 scripts/build-pages-dist.sh   # skip the atlas copy
#   REUSE_WASM=1 scripts/build-pages-dist.sh  # reuse already-built wasm pkgs + baked
#                                             # cards; no recompile, no cargo.
#
# TWO MODES, TWO FAILURE POLARITIES — this is the load-bearing distinction.
#
#   FULL BUILD (REUSE_WASM=0). This script BUILDS the wasm. A surface that is missing
#   afterwards, or a browser-surface tooth that bites, is a REAL BREAK in the thing this
#   invocation just produced, and it ABORTS. That is where a failure belongs, and it is
#   what `.github/workflows/pages-wasm.yml` (the heavy, scheduled wasm workflow) runs
#   its equivalent of.
#
#   REUSE_WASM=1. This script only ASSEMBLES, from wasm somebody else built — in CI, the
#   fast content path (`.github/workflows/pages.yml`) downloading artifacts from the most
#   recent heavy run. Here a missing or stale surface is NOT this build's fault and MUST
#   NOT fail it: a red deploy job would block a typo fix on the landing page, which is
#   the exact coupling the split exists to remove. So the assembly CONTINUES and the
#   degradation is made VISIBLE IN THE RENDERED SITE instead — see
#   `scripts/stamp-wasm-provenance.sh`, which this script always runs last, and which
#   writes /wasm-provenance.{json,html} plus in-page markers on every affected surface.
#
# The invariant is NO SILENT DEGRADATION, not "no degradation". Every surface this build
# could not ship says so on the page where it would have been.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
DIST="$ROOT/site/dist"
GPUI="${GPUI:-1}"
ATLAS="${ATLAS:-1}"
REUSE_WASM="${REUSE_WASM:-0}"

# Re-theme a baked deos-view card page from its fixed blue palette to the site's
# salvaged green palette (the cards are baked by a Rust example with an inline
# palette; we swap the tokens at assemble time so the gallery is of-a-piece).
greenify() {
  local f="$1"
  sed -i.bak \
    -e 's/#121317/#0a0f0d/g' \
    -e 's/#e6e7eb/#e4ddd0/g' \
    -e 's/#9aa0aa/#7a7265/g' \
    -e 's/#5b8cff/#5b8a5a/g' \
    -e 's/#2a2c33/#1a2d25/g' \
    -e 's/#181a20/#121b16/g' \
    "$f"
  rm -f "$f.bak"
}

echo "=== clean dist ==="
rm -rf "$DIST"
mkdir -p "$DIST"

# Facts about THIS assembly that scripts/stamp-wasm-provenance.sh turns into the
# deployed provenance record and the in-page markers. Consumed and deleted there, so it
# never ships.
NOTES="$DIST/.assembly-notes"
note() { echo "$1" >>"$NOTES"; }

# The mtime of the SOURCE blob, i.e. when that wasm was actually built. Recorded because
# `cp -R` does NOT preserve mtimes, so the copy inside the dist is stamped with the COPY
# time — reading it would report every bundle as built seconds ago, which is precisely the
# "assume fresh" answer a staleness signal must never give. Only consulted when no CI run
# provenance was supplied (a local run); in CI, WASM_PROV_BUILT_AT is authoritative.
note_src_built_at() {
  local key="$1" path="$2" ts
  ts="$(python3 -c 'import os,sys,datetime as d;print(d.datetime.fromtimestamp(os.path.getmtime(sys.argv[1]),d.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"))' "$path" 2>/dev/null || true)"
  [ -n "$ts" ] && note "surface.$key.src_built_at=$ts"
  return 0
}

# A surface this mode is not allowed to ship silently. In REUSE_WASM the absence is
# recorded and the assembly continues (the site will carry a marker); in a full build the
# same absence means the build we just ran is broken, so it aborts.
absent_surface() {
  local key="$1" what="$2" fix="$3"
  note "surface.$key=absent"
  if [ "$REUSE_WASM" = "1" ]; then
    echo "=== $what is ABSENT — the site will ship a MISSING-wasm marker for it ===" >&2
    return 0
  fi
  echo "=== $what is ABSENT after a FULL build — that is a break, not a reuse gap ===" >&2
  echo "    $fix" >&2
  exit 1
}

# ── 0. THE LANDING (sober, static, green) ────────────────────────────────────────
echo "=== 0/6 the sober landing + shared green assets ==="
cp "$ROOT/site/root/index.html" "$DIST/index.html"
# the dense technical index — the developer/operator/prover/machine hub, linked
# from the landing's nav; deploys at /technical.html (it does NOT replace the landing).
cp "$ROOT/site/root/technical.html" "$DIST/technical.html"
# The paper is a first-class build artifact, not a checked-in binary. Its landing
# is source-controlled; the PDF is compiled from paper/main.typ on every assembly.
mkdir -p "$DIST/paper"
cp "$ROOT/site/root/paper.html" "$DIST/paper/index.html"
typst compile "$ROOT/paper/main.typ" "$DIST/paper/dregg.pdf"
test -s "$DIST/paper/dregg.pdf"
test "$(head -c 5 "$DIST/paper/dregg.pdf")" = '%PDF-'

# The direct-logic report is being developed alongside its formalization. Keep
# today's Pages deploy green before the source lands; once main.typ exists, a
# missing or invalid PDF is a hard assembly failure. --root lets the report cite
# checked-in formalization artifacts outside its own directory without weakening
# Typst's filesystem boundary beyond this repository.
DIRECT_LOGIC_SRC="$ROOT/papers/direct-logic-arithmetization/main.typ"
DIRECT_LOGIC_DIST="$DIST/papers/direct-logic-arithmetization"
DIRECT_LOGIC_PDF="$DIRECT_LOGIC_DIST/direct-logic-arithmetization.pdf"
if [ -f "$DIRECT_LOGIC_SRC" ]; then
  echo "=== compile the direct-logic arithmetization report ==="
  mkdir -p "$DIRECT_LOGIC_DIST"
  typst compile --root "$ROOT" "$DIRECT_LOGIC_SRC" "$DIRECT_LOGIC_PDF"
  test -s "$DIRECT_LOGIC_PDF"
  test "$(head -c 5 "$DIRECT_LOGIC_PDF")" = '%PDF-'
else
  echo "=== direct-logic arithmetization report not present yet; skipped ==="
fi
# the cloud & userspace subsite — the grain economy (the cloud) + the ~30 starbridge
# apps (the userspace of the kernel) + trustless serving; deploys at /cloud/.
cp -R "$ROOT/site/cloud" "$DIST/cloud"
cp -R "$ROOT/site/assets" "$DIST/assets"
cp -R "$ROOT/site/explorer" "$DIST/explorer"
cp -R "$ROOT/site/light-client" "$DIST/light-client"
# dregg.works — the trustless-host front door + the injectable verify badge. Shipped
# under /dregg-works/ on the main site; the same dir is what deploys to the dregg.works
# apex (where verify-badge.js sits at the root as /verify-badge.js).
cp -R "$ROOT/site/dregg-works" "$DIST/dregg-works"
# transclusion — Xanadu made honest: the parallel-source demo page (drives the wasm
# transclusion bindings from /cards/pkg/, built in step 3) + the embeddable
# transclude.js that carries a verified dregg:// quote to ANY web page (it ships
# beside verify-badge.js inside the dregg-works copy above).
cp -R "$ROOT/site/transclusion" "$DIST/transclusion"
# deos-viewer — THE DESKTOP IN A LINK landing: reads a #deos1!... share fragment
# (pinned instant + message tape + root claim), previews it client-side, and hands
# it to the reader's own --serve-ie6 viewer server as /shared?d=... for the real
# fail-closed decode + deterministic replay + root verdict. Static HTML+JS only.
cp -R "$ROOT/site/deos-viewer" "$DIST/deos-viewer"

# deep — the full dense product site (the pretraining-grade twin of dregg.net):
# every page with its theorem names, test counts, and seam ledgers intact. Static
# prebuilt HTML (zola output from ~/dev/dregg-site, base-url .../deep); dregg.net
# carries the accessible layer and links here per-page.
cp -R "$ROOT/site/deep" "$DIST/deep"
test -f "$DIST/explorer/index.html"
test -f "$DIST/light-client/index.html"
test -f "$DIST/paper/index.html"
test -s "$DIST/paper/dregg.pdf"
test -f "$DIST/dregg-works/index.html"
test -f "$DIST/dregg-works/verify-badge.js"
test -f "$DIST/dregg-works/transclude.js"
test -f "$DIST/transclusion/index.html"
test -f "$DIST/deos-viewer/index.html"
test -f "$DIST/deep/index.html"
test -f "$DIST/deep/egg/index.html"

# ── 1. THE deos COCKPIT: the WebImage launcher (gpui-free skin), node-less ───────
echo "=== 1/6 build the WebImage cockpit wasm (starbridge-v2/web, default) ==="
if [ "$REUSE_WASM" = "0" ]; then
  wasm-pack build "$ROOT/starbridge-v2/web" --target web --out-dir pkg --release
fi
mkdir -p "$DIST/deos"
cp "$ROOT/site/deos/index.html" "$DIST/deos/index.html"
# The page ships EITHER WAY. Without the pkg the cockpit cannot boot, and the stamp puts a
# visible MISSING-wasm marker on it rather than serving a dead app with no explanation.
if [ -s "$ROOT/starbridge-v2/web/pkg/starbridge_web_bg.wasm" ]; then
  cp -R "$ROOT/starbridge-v2/web/pkg" "$DIST/deos/pkg"
  test -s "$DIST/deos/pkg/starbridge_web_bg.wasm"
  note "surface.webimage=present"
  note_src_built_at webimage "$ROOT/starbridge-v2/web/pkg/starbridge_web_bg.wasm"
else
  absent_surface webimage "the WebImage cockpit pkg (starbridge-v2/web/pkg)" \
    "wasm-pack build starbridge-v2/web --target web --out-dir pkg --release"
fi

# ── 2. THE FULL gpui-web COCKPIT (WebGPU canvas), node-less ──────────────────────
# The gpui-web build pulls deos-matrix AND zed's sqlez — the one `links="sqlite3"`
# pair the workspace cannot link together (a documented narrow resolution wall,
# starbridge-v2/Cargo.toml "BLOCKER 1"). When it resolves it is the real full
# renderer; when the pair collides we still ship the rest of in-browser deos rather
# than failing the whole deploy. GPUI=1 REQUIRES it (fail-hard); default soft.
if [ "$GPUI" = "0" ]; then
  echo "=== 2/6 SKIPPED the gpui-web cockpit (GPUI=0) ==="
  note "surface.cockpit_gpui=skipped-by-request"
elif [ "$REUSE_WASM" = "1" ] && [ -s "$ROOT/starbridge-v2/web/pkg-gpui/starbridge_web_bg.wasm" ]; then
  echo "=== 2/6 reuse the prebuilt gpui-web cockpit ==="
  mkdir -p "$DIST/cockpit-gpui"
  cp "$ROOT/starbridge-v2/web/cockpit_gpui.html" "$DIST/cockpit-gpui/index.html"
  cp -R "$ROOT/starbridge-v2/web/pkg-gpui" "$DIST/cockpit-gpui/pkg-gpui"
  note "surface.cockpit_gpui=present"
  note_src_built_at cockpit_gpui "$ROOT/starbridge-v2/web/pkg-gpui/starbridge_web_bg.wasm"
elif [ "$REUSE_WASM" = "1" ]; then
  # WAS THE SILENT ONE. Until 2026-07-26 this branch omitted /cockpit-gpui/ entirely and
  # said so only on stderr: the deployed site simply had no such directory, and a visitor
  # following the landing page's own link got a bare 404 with no account of why. The
  # omission stays non-fatal — that is correct — but the stamp now stands a marker page up
  # at that route naming the artifact that was missing.
  echo "=== 2/6 NO prebuilt pkg-gpui — /cockpit-gpui/ ships as a MISSING-wasm marker ===" >&2
  note "surface.cockpit_gpui=absent"
elif wasm-pack build "$ROOT/starbridge-v2/web" --target web --out-dir pkg-gpui --release -- --features gpui-web; then
  echo "=== 2/6 gpui-web cockpit built ==="
  mkdir -p "$DIST/cockpit-gpui"
  cp "$ROOT/starbridge-v2/web/cockpit_gpui.html" "$DIST/cockpit-gpui/index.html"
  cp -R "$ROOT/starbridge-v2/web/pkg-gpui" "$DIST/cockpit-gpui/pkg-gpui"
  test -s "$DIST/cockpit-gpui/pkg-gpui/starbridge_web_bg.wasm"
  note "surface.cockpit_gpui=present"
elif [ "${GPUI}" = "1" ]; then
  echo "=== 2/6 gpui-web cockpit FAILED and GPUI=1 (required) — failing ===" >&2
  exit 1
else
  echo "=== 2/6 gpui-web cockpit did not resolve (the matrix+zed sqlite pair) — shipping without it ===" >&2
  note "surface.cockpit_gpui=absent"
fi

# ── 3. THE CARD GALLERY: the deos-js cards (wasm/ runtime bindings), node-less ────
echo "=== 3/6 build the card-world wasm (wasm/) + bake the gallery ==="
if [ "$REUSE_WASM" = "0" ]; then
  # A larger wasm stack gives the in-tab recursion verify (the light client's
  # verify-a-whole-history path) headroom — scoped to this build, not the native bake.
  RUSTFLAGS="-C link-arg=-zstack-size=33554432" wasm-pack build "$ROOT/wasm" --target web --out-dir pkg --release
  ( cd "$ROOT/deos-view" && cargo run -q --no-default-features --features web --example web_render_card )
fi
# The light-client page verifies a REAL pre-folded whole-history aggregate in-tab. The
# aggregate (site/light-client/history.json) is produced ONCE, off the verifier, by the
# heavy native prover and committed as a data artifact (CI does NOT re-fold it):
#   cargo run --release -p dregg-lightclient --bin produce_history_envelope --features prover -- 3 7 \
#     > site/light-client/history.json
# Regenerate it whenever the circuit/VK or the WholeChainProofBytes wire format moves
# (e.g. the v12 geometry epoch turned the scalar roots into 8-felt sequences) — the
# FRESHNESS TOOTH below (scripts/check-web-surface-teeth.sh) catches a baked demo the
# visitor's tab would refuse: it ABORTS a full build, and marks the shipped page as
# known-broken in REUSE_WASM mode.
test -s "$ROOT/site/light-client/history.json"
mkdir -p "$DIST/cards"
# TWO independent inputs from the heavy path: the BAKED gallery pages (artifact
# `cards-baked`) and the card-world wasm (artifact `wasm-cards`). Either can be absent in
# REUSE_WASM mode, and each gets its own marker rather than aborting the content deploy.
if [ -s "$ROOT/deos-view/target/web-out/dist/index.html" ]; then
  for card in index counter inspector tally kvstore doccollab; do
    cp "$ROOT/deos-view/target/web-out/dist/$card.html" "$DIST/cards/$card.html"
    greenify "$DIST/cards/$card.html"
  done
  note "cards_baked=present"
else
  absent_surface cards_baked "the baked card gallery pages (deos-view/target/web-out/dist)" \
    "cd deos-view && cargo run -q --no-default-features --features web --example web_render_card"
fi
if [ -s "$ROOT/wasm/pkg/dregg_wasm_bg.wasm" ]; then
  cp -R "$ROOT/wasm/pkg" "$DIST/cards/pkg"
  test -s "$DIST/cards/pkg/dregg_wasm_bg.wasm"
  note "surface.cards=present"
  note_src_built_at cards "$ROOT/wasm/pkg/dregg_wasm_bg.wasm"
else
  absent_surface cards "the card-world wasm (wasm/pkg)" \
    "RUSTFLAGS=... wasm-pack build wasm --target web --out-dir pkg --release"
fi

# THE BROWSER-SURFACE TEETH — the light-client freshness check and the transclusion
# both-polarities check. They now live in scripts/check-web-surface-teeth.sh (one source)
# so the HEAVY wasm workflow can run the SAME two checks against the wasm it just built
# and go RED there, which is where a genuine circuit/VK or refusal-path break belongs.
#
# The polarity here follows the mode (see this script's header):
#   full build  — a tooth that bites ABORTS. This invocation built that wasm; it is broken.
#   REUSE_WASM  — a tooth that bites is RECORDED, and the site ships a visible "this demo
#                 is not yet built — this is a STAGING site" marker on the affected pages. A content
#                 deploy is not hostage to a baked artifact somebody else needs to re-fold.
if [ -s "$DIST/cards/pkg/dregg_wasm_bg.wasm" ]; then
  teeth_log="$(mktemp)"
  # NOT `... | tee`: a pipeline reports the LAST command's status, so piping would read
  # tee's success as the teeth's success and the gate would never be able to bite.
  set +e
  bash "$ROOT/scripts/check-web-surface-teeth.sh" "$DIST/cards/pkg" >"$teeth_log" 2>&1
  teeth_rc=$?
  set -e
  cat "$teeth_log"
  teeth_detail="$(tr '\n' ' ' <"$teeth_log" | tr -s ' ' | cut -c1-400)"
  rm -f "$teeth_log"
  if [ "$teeth_rc" -eq 0 ]; then
    note "teeth.web_surface=green"
  elif [ "$teeth_rc" -eq 2 ]; then
    # The script could not test (no node, or no baked aggregate). Recorded, never assumed
    # green — an untested surface that reports "fine" is the hole this repo keeps finding.
    note "teeth.web_surface=not-run"
    note "teeth.web_surface.detail=$teeth_detail"
  elif [ "$REUSE_WASM" = "1" ]; then
    echo "=== note: a browser-surface tooth bit on REUSED wasm. EXPECTED during staging; the site ships" >&2
    echo "    marker on the affected pages and the content deploy continues ===" >&2
    note "teeth.web_surface=bit"
    note "teeth.web_surface.detail=$teeth_detail"
  else
    echo "=== a browser-surface tooth BIT on wasm THIS BUILD produced — failing ===" >&2
    exit 1
  fi
else
  note "teeth.web_surface=not-run"
  note "teeth.web_surface.detail=no card-world wasm in this build, so the teeth had nothing to test"
fi

# ── 4. THE ATLAS (relative paths, works at any subpath) ──────────────────────────
if [ "$ATLAS" = "1" ] && [ -d "$ROOT/dregg-atlas/site" ]; then
  echo "=== 4/6 bundle the atlas ==="
  mkdir -p "$DIST/atlas"
  cp -a "$ROOT/dregg-atlas/site/." "$DIST/atlas/"
  test -f "$DIST/atlas/index.html"
else
  echo "=== 4/6 SKIPPED the atlas ==="
fi

# ── 5. .nojekyll so /pkg/ + dotfiles ship verbatim ───────────────────────────────
echo "=== 5/6 finalize ==="
touch "$DIST/.nojekyll"

# ── 6. STAMP THE PROVENANCE + MARK EVERY SURFACE THIS BUILD COULD NOT SHIP ───────
# Always runs, in both modes. It consumes $DIST/.assembly-notes (written above), writes
# /wasm-provenance.{json,html}, puts a <meta name="dregg-wasm-provenance"> on every
# wasm-serving page, and stands a visible marker where a surface is absent, stale, or
# known-broken. It exits non-zero ONLY if the static content itself failed to assemble.
echo "=== 6/6 stamp the wasm provenance into the dist ==="
DIST="$DIST" bash "$ROOT/scripts/stamp-wasm-provenance.sh"

echo
echo "dist ready: $DIST"
echo "  /              -> the sober landing ($(du -sh "$DIST/index.html" | cut -f1))"
echo "  /deos/         -> $(du -sh "$DIST/deos" | cut -f1) (the WebImage cockpit)"
[ -d "$DIST/cockpit-gpui" ] && echo "  /cockpit-gpui/ -> $(du -sh "$DIST/cockpit-gpui" | cut -f1) (the full gpui-web cockpit)"
echo "  /cards/        -> $(du -sh "$DIST/cards" | cut -f1) (the deos-js card gallery)"
echo "  /explorer/     -> $(du -sh "$DIST/explorer" | cut -f1) (caps as rows)"
echo "  /light-client/ -> $(du -sh "$DIST/light-client" | cut -f1) (verify a whole history)"
echo "  /transclusion/ -> $(du -sh "$DIST/transclusion" | cut -f1) (xanadu made honest)"
[ -f "$DIRECT_LOGIC_PDF" ] && echo "  /papers/direct-logic-arithmetization/ -> $(du -sh "$DIRECT_LOGIC_PDF" | cut -f1) (the direct-logic report)"
[ -d "$DIST/atlas" ] && echo "  /atlas/        -> $(du -sh "$DIST/atlas" | cut -f1) (the atlas)"
echo "  total: $(find "$DIST" -type f | wc -l | tr -d ' ') files"
