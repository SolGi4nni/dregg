"""Screenshot every cockpit surface for the UI-atlas pillar, via the dregg-mcp
`screenshot` tool (the real gpui Cockpit bake at 1280x832). Writes the PNGs to
screenshots/ and a surfaces.json manifest the site-builder ingests.

The surface roster is the canonical census in `surfaces.py` (grounded in the
cockpit's `Tab` enum + the dock dev panes). Each surface is baked by its declared
path:
  bake='tab'      → screenshot tab=<render_tab>     (the per-surface bake)
  bake='showcase' → the --render-showcase composite (the full cockpit dock)

If the MCP `screenshot` tool isn't available (the headless-render binary isn't
built), shoot.py still emits the manifest (sans PNGs) so build.py can render the
surface atlas pages + data; a later shoot.py fills the screenshots. Regenerable:
  python3 crawl.py && python3 shoot.py && python3 build.py
"""
import json
import os
import sys

import shutil

from mcp_client import Mcp
from surfaces import SURFACES

ROOT = os.path.dirname(os.path.abspath(__file__))
PARENT = os.path.dirname(ROOT)
SHOTS = os.path.join(ROOT, "screenshots")
DATA = os.path.join(ROOT, "data")
os.makedirs(SHOTS, exist_ok=True)
os.makedirs(DATA, exist_ok=True)

# EXTERNAL bakes (bake='external'): committed PNGs from each demonstration's own
# e2e/headless bake, copied in by id. Repo-relative to the atlas's parent tree.
# A surface with no entry here (e.g. the test-proved-only ones) simply carries no
# screenshot — build.py renders its explainer without an image.
EXTERNAL_SOURCES = {
    "self-hosting-loop": "starbridge-v2/self-hosting-loop-full.png",
    "web-deos":          "starbridge-v2/web/cockpit-gpui-web-painted.png",
    "servo-page":        "servo-render/servo_real_page_render.png",
    "unified-boot":      "deos-unified-boot.png",
}


def manifest_entry(sid, label, bake, deep, blurb, png=None, size=None):
    """One surface record — stable id + the hypermedia fields the site links over."""
    return {
        "id": "surface:" + sid,
        "tab": sid,                     # the atlas page slug (back-compat key)
        "label": label,
        "bake": bake,
        "deep": deep,                   # the explainer-section slug
        "explainer": blurb,
        "file": os.path.basename(png) if png else None,
        "size": size,
    }


def main():
    no_mcp = "--no-mcp" in sys.argv or os.environ.get("ATLAS_NO_MCP")
    m = None if no_mcp else Mcp()
    manifest = []
    captured = 0
    try:
        for (sid, render_tab, label, bake, deep, blurb) in SURFACES:
            png = None
            size = None
            # reuse a prior bake if present (so the gallery stays populated when a
            # full re-shoot isn't possible — the new MCP only needs to fill the new
            # surfaces). A fresh MCP bake below overwrites it.
            prior = os.path.join(SHOTS, sid + ".png")
            if os.path.exists(prior):
                png = prior
            if bake == "external":
                # copy the committed demonstration PNG into the atlas (no MCP).
                src_rel = EXTERNAL_SOURCES.get(sid)
                if src_rel:
                    src = os.path.join(PARENT, src_rel)
                    if os.path.exists(src):
                        dst = os.path.join(SHOTS, sid + ".png")
                        shutil.copyfile(src, dst)
                        png = dst
                        captured += 1
                        print(f"  ext  {sid} <- {src_rel}", file=sys.stderr)
                    else:
                        print(f"  MISS-EXT {sid}: source not found {src_rel}", file=sys.stderr)
                manifest.append(manifest_entry(sid, label, bake, deep, blurb, png, size))
                continue
            if m is not None:
                out = os.path.join(SHOTS, sid)
                try:
                    if bake == "showcase":
                        # the composite full-cockpit bake (the dock workspace).
                        res = m.call("screenshot", out=out, size="1600x1000")
                    else:
                        res = m.call("screenshot", out=out, size="1280x832", tab=render_tab)
                    p = res.get("png", "")
                    if p and os.path.exists(p):
                        png, size = p, res.get("size")
                        captured += 1
                        print(f"  shot {sid} -> {os.path.basename(p)}", file=sys.stderr)
                    else:
                        print(f"  MISS {sid}: {res}", file=sys.stderr)
                except Exception as e:
                    print(f"  ERR {sid}: {e}", file=sys.stderr)
            manifest.append(manifest_entry(sid, label, bake, deep, blurb, png, size))
        json.dump(manifest, open(os.path.join(DATA, "surfaces.json"), "w"), indent=2)
        if m is None:
            print(f"surfaces: {len(manifest)} cataloged (NO MCP — manifest only, no PNGs). "
                  f"Build the headless-render binary then re-run shoot.py to fill screenshots.",
                  file=sys.stderr)
        else:
            print(f"surfaces: {captured}/{len(manifest)} captured", file=sys.stderr)
    finally:
        if m is not None:
            m.close()


if __name__ == "__main__":
    main()
