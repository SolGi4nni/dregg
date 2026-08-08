#!/usr/bin/env bash
# Serve the LIVE browser-native deos: deos-js cards rendered via the gpui-free web renderer
# (deos-view/src/web.rs), firing REAL cap-gated verified turns over in-tab wasm executors
# (wasm/src/bindings_card.rs — the wasm analogs of the native Applet / inspector). Two pages
# are baked + served:
#
#   /                — the GALLERY / card-picker (plain HTML, no wasm): clickable tiles, one
#                      per live card — the discoverable front door that opens each card page.
#   /counter.html    — the COUNTER card (CardWorld): a `+1` click commits a SetField +
#                      IncrementNonce turn; the bound count re-paints from the committed ledger.
#   /inspector.html  — the REFLECTIVE-INSPECTOR card (InspectorWorld): a cockpit surface, in a
#                      TAB. The inspector card's view-tree (generated from a focused cell's REAL
#                      moldable faces — RawFields + Affordances, via deos-reflect) renders to
#                      HTML: a "Cell State" section (several live Bind rows + structural rows)
#                      and an "Affordances" section. Clicking an affordance (tick/add/score)
#                      fires a real cap-gated verified turn and the bound field re-paints, with
#                      a live balance/nonce/receipt readout.
#   /tally.html      — the TALLY-BOARD card (TallyWorld): the FULL ViewNode layout vocabulary
#                      (Row + Table + a multi-affordance row). A table of named tallies, each a
#                      row with a live count and +1/−1 buttons; every click fires a real
#                      cap-gated verified turn moving that one tally, and the row re-paints.
#   /kvstore.html    — the KV-STORE SERVICE-CELL card (KvStoreWorld): a cell publishing a typed
#                      interface (put · delete · get). Clicking put/del ROUTES the call through
#                      the store's InterfaceDescriptor (the verified DFA) before it desugars to
#                      the version-bump + register SetField effects — a real cap-gated verified
#                      turn against the store cell, the monotone version advancing (a rollback is
#                      refused by the program's Monotonic constraint; get is a named OFE seam).
#   /doccollab.html  — the DOCUMENT-COLLABORATION surface (DocCollabWorld): Pijul, in a tab. A
#                      doc-cell carries a base document published to its umem-heap (the fork).
#                      Click `stitch` to diverge two authors and merge (the categorical pushout):
#                      a first-class CONFLICT surfaces (both alternatives attributed side-by-side,
#                      held off-heap). Click a resolution and the merged document publishes to the
#                      doc-cell's umem-heap as a real cap-gated verified turn — the boundary
#                      heap_root moves, a receipt is left. Conflicts-as-objects, node-less.
#
# Builds the wasm bundle, bakes the live pages, assembles a self-contained dist/, and serves it
# (each page is a module-import + a .wasm fetch — file:// is CORS-blocked, so it MUST be served
# over HTTP).
#
#   scripts/serve-deos-card.sh           # build + bake + serve on :8000
#   scripts/serve-deos-card.sh --no-serve  # build + bake only (print the dist path)
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
PORT="${PORT:-8000}"
DIST="$ROOT/deos-view/target/web-out/dist"

echo "=== 1/3 Building the playground wasm bundle (wasm-pack, --target web) ==="
# THE FLAG PAIR, from the one definition. This line carried NO RUSTFLAGS at all, which is
# one of the two ways to separate the pair: it took `getrandom_backend` from
# `.cargo/config.toml` and never got the 32 MiB stack the in-tab recursion verifier needs.
# It also writes `wasm/pkg` — the directory `scripts/check-wasm-freshness.sh` grades —
# WITHOUT stamping provenance, so after this script runs that gate reads RED ("no
# provenance record"), which is the correct fail-closed answer and the reason to build the
# shipping bundle with `scripts/build-descent-wasm.sh` instead of this dev-loop helper.
# shellcheck source=scripts/wasm-build-flags.sh
. "$ROOT/scripts/wasm-build-flags.sh"
RUSTFLAGS="$DREGG_WASM_RUSTFLAGS" wasm-pack build "$ROOT/wasm" --target web --out-dir pkg --release

echo "=== 2/3 Baking the live card page (gpui-free web renderer) ==="
( cd "$ROOT/deos-view" && cargo run --no-default-features --features web --example web_render_card )

echo "=== 3/3 Assembling the self-contained dist ==="
rm -rf "$DIST/pkg"
cp -R "$ROOT/wasm/pkg" "$DIST/pkg"
echo "dist ready: $DIST"
ls -la "$DIST"

if [[ "${1:-}" == "--no-serve" ]]; then
  echo "Skipping serve. Open it with:  (cd '$DIST' && python3 -m http.server $PORT)"
  exit 0
fi

echo
echo "=== Serving the LIVE deos cards at http://localhost:$PORT ==="
echo "  GALLERY   : http://localhost:$PORT/            — the card-picker (open a card below)"
echo "  COUNTER   : http://localhost:$PORT/counter.html   — click +1 (a real cap-gated verified turn)"
echo "  INSPECTOR : http://localhost:$PORT/inspector.html — a reflective cockpit surface; click an"
echo "              affordance (tick/add/score) → a real verified turn → the bound field re-paints."
echo "  TALLY     : http://localhost:$PORT/tally.html     — a table of named tallies (Row + Table);"
echo "              click +1/−1 on any row → a real verified turn moves that one tally."
echo "  KVSTORE   : http://localhost:$PORT/kvstore.html   — a SERVICE CELL (published put/delete/get);"
echo "              click put/del → a method routed through the verified DFA → a real verified turn."
echo "  DOCCOLLAB : http://localhost:$PORT/doccollab.html — Pijul, in a tab. Click stitch (the pushout)"
echo "              → a first-class conflict; click resolve → the merged doc publishes to the umem-heap."
echo "(Ctrl-C to stop.)"
cd "$DIST"
exec python3 -m http.server "$PORT"
