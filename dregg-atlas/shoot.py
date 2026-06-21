"""Screenshot every cockpit surface for the UI-atlas pillar, via the dregg-mcp
`screenshot` tool (the real gpui Cockpit bake at 1280x832). Writes the PNGs to
screenshots/ and a surfaces.json manifest (tab, file, size, explainer) the
site-builder ingests.
"""
import json
import os
import sys

from mcp_client import Mcp

ROOT = os.path.dirname(os.path.abspath(__file__))
SHOTS = os.path.join(ROOT, "screenshots")
DATA = os.path.join(ROOT, "data")
os.makedirs(SHOTS, exist_ok=True)
os.makedirs(DATA, exist_ok=True)

# The 28 cockpit surfaces (Tab::label, normalized) with a first-principles blurb.
SURFACES = [
    ("home", "The at-rest landing — what the live verified image IS, in prose, with its headline stats."),
    ("inspector", "The moldable inspector (Registry · Spotter · Halo): every object's seven presentation faces; the inspector is itself inspectable."),
    ("inspect-act", "The inspect→act loop: a cell's reflected state on the left, the messages it understands on the right, each with its cap badge; firing one commits a real turn."),
    ("graph", "The ocap delegation graph — cells as nodes, capability grants as directed edges, laid out by multi-hop delegation depth."),
    ("web-of-cells", "The cells as a navigable web — the distributed-attestation view of the image."),
    ("objects", "The object browser — every protocol object by kind."),
    ("proofs", "The STARK/verification axis — the proof status of turns."),
    ("debugger", "Step + explain a turn against the live world — the time-aware debugger."),
    ("replay", "Deterministic replay / time-travel over the canonical history."),
    ("workspace", "The DOIT/PRINTIT evaluator — a Smalltalk-style workspace over the live image."),
    ("wonder", "The AOL-wonder direct-manipulation surface — click around and absorb, no comprehension required."),
    ("lanes", "The moldable-inspector gadgets (L2–L10): predicate/turn/cap/token construction."),
    ("powerbox", "The capability powerbox — granting/brokering authority."),
    ("links-here", "What-links-here — the inbound reference graph for the focused object."),
    ("organs", "The organ survey — the image's specialized verified-program cells."),
    ("cipherclerk", "The sovereign cipherclerk vault — HD-derived identities, macaroon signing."),
    ("editor", "The conserving forest editor — build a turn, validate it, commit."),
    ("composer", "The predicate/caveat composer."),
    ("simulate", "Simulate a turn against a fork before committing."),
    ("agent", "The agent surface — autonomous loops over the image."),
    ("swarm", "The swarm orchestration surface."),
    ("shell", "The command shell over the image."),
    ("terminal", "The terminal surface."),
    ("buffer", "The text buffer surface."),
    ("trust", "The trust panel — identity, guardians, the K-of-N recovery threshold, the KEL timeline."),
    ("docs", "The document lens — the Pijul-shaped patch-theory document object."),
    ("time", "The time/history scrubber."),
    ("share", "The sharing/membrane surface."),
]


def main():
    m = Mcp()
    manifest = []
    try:
        for tab, blurb in SURFACES:
            out = os.path.join(SHOTS, tab)
            try:
                res = m.call("screenshot", out=out, size="1280x832", tab=tab)
                png = res.get("png", "")
                if png and os.path.exists(png):
                    manifest.append({"tab": tab, "file": os.path.basename(png), "size": res.get("size"), "explainer": blurb})
                    print(f"  shot {tab} -> {os.path.basename(png)}", file=sys.stderr)
                else:
                    print(f"  MISS {tab}: {res}", file=sys.stderr)
            except Exception as e:
                print(f"  ERR {tab}: {e}", file=sys.stderr)
        json.dump(manifest, open(os.path.join(DATA, "surfaces.json"), "w"), indent=2)
        print(f"surfaces: {len(manifest)}/{len(SURFACES)} captured", file=sys.stderr)
    finally:
        m.close()


if __name__ == "__main__":
    main()
