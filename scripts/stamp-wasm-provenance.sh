#!/usr/bin/env bash
# STAMP THE PROVENANCE OF THE WASM SURFACES INTO THE DEPLOYED SITE — and MARK, in the
# rendered page, any surface this build could not ship.
#
# THE WOUND THIS CLOSES
# ---------------------
# The Pages deploy is split in two (2026-07-26): a FAST content path (typst + a
# cargo-free `REUSE_WASM=1` assembly + deploy, on every push) and a HEAVY path
# (`.github/workflows/pages-wasm.yml`: the three `wasm-pack --release` builds, on a
# schedule). The fast path REUSES wasm artifacts it did not build. That buys reliability
# — a docs fix is never behind three release wasm builds — and it buys a new hazard:
# the deployed site can carry WebAssembly that is weeks old, or can be missing a surface
# entirely, and NOTHING WOULD SAY SO.
#
# The deploy must not fail for that (a red deploy job blocks the typo fix, which is the
# exact coupling the split removes). So the deploy proceeds and this script makes the
# degradation VISIBLE IN THE RENDERED SITE instead:
#
#   * every wasm-serving page carries a <meta name="dregg-wasm-provenance"> line;
#   * /wasm-provenance.json + /wasm-provenance.html record what was included, from which
#     run and commit, built when, and WHAT WAS MISSING;
#   * a surface whose wasm is ABSENT gets a visible in-page marker (and a wholly absent
#     surface gets a marker page where a 404 would otherwise be — "link broken", said
#     out loud, instead of a directory that quietly is not there);
#   * a surface whose wasm is present but STALE (older than WASM_STALE_DAYS) gets a
#     visible in-page marker naming its age and source run;
#   * a surface whose TEETH BIT (scripts/check-web-surface-teeth.sh: the baked
#     light-client aggregate no longer attests, or transclusion stopped refusing) gets a
#     visible in-page marker. The demo is shipped and honest about being broken.
#
# NO SILENT DEGRADATION is the invariant — not "no degradation". The difference between
# this and the wound class is that a human loading the page can see it, and so can a
# machine reading one JSON file.
#
# EXIT STATUS: 0 even when surfaces are absent/stale/broken — that is the whole point.
# Non-zero ONLY when the dist itself is unusable (no $DIST, no $DIST/index.html), i.e.
# when the STATIC content — the thing the fast path exists to ship — did not assemble.
#
# INPUTS (all optional; absent => provenance is derived from the local working tree and
# labelled as such, so a local run is honest rather than fabricating CI metadata)
#   DIST                      default ./site/dist
#   WASM_STALE_DAYS           default 10 (the heavy workflow's schedule is weekly, so a
#                             single missed run shows up as stale)
#   WASM_PROV_SOURCE          this-run | reused-run | local-tree
#   WASM_PROV_RUN_ID          the run id that BUILT the wasm
#   WASM_PROV_RUN_URL         its html_url
#   WASM_PROV_COMMIT          the commit that wasm was built from
#   WASM_PROV_HEAD            that run's branch or tag
#   WASM_PROV_BUILT_AT        ISO8601 Z instant the wasm run started
#   WASM_PROV_COMMITS_BEHIND  how many commits the site content is ahead of the wasm
#   WASM_PROV_SITE_COMMIT     the commit the STATIC content came from
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
DIST="${DIST:-$ROOT/site/dist}"

if [ ! -d "$DIST" ]; then
  echo "stamp-wasm-provenance: no dist at $DIST — the assembly did not run" >&2
  exit 1
fi
if [ ! -f "$DIST/index.html" ]; then
  echo "stamp-wasm-provenance: $DIST/index.html is missing — the STATIC content failed to" >&2
  echo "  assemble. That is a real deploy failure, not a missing wasm artifact." >&2
  exit 1
fi

export ROOT DIST
export WASM_STALE_DAYS="${WASM_STALE_DAYS:-10}"
export WASM_PROV_SOURCE="${WASM_PROV_SOURCE:-local-tree}"
export WASM_PROV_RUN_ID="${WASM_PROV_RUN_ID:-}"
export WASM_PROV_RUN_URL="${WASM_PROV_RUN_URL:-}"
export WASM_PROV_COMMIT="${WASM_PROV_COMMIT:-}"
export WASM_PROV_HEAD="${WASM_PROV_HEAD:-}"
export WASM_PROV_BUILT_AT="${WASM_PROV_BUILT_AT:-}"
export WASM_PROV_COMMITS_BEHIND="${WASM_PROV_COMMITS_BEHIND:-}"
export WASM_PROV_SITE_COMMIT="${WASM_PROV_SITE_COMMIT:-$(git -C "$ROOT" rev-parse HEAD 2>/dev/null || echo '')}"

python3 - <<'PY'
import hashlib, json, os, re, sys
from datetime import datetime, timezone

DIST = os.environ["DIST"].rstrip("/")
ROOT = os.environ["ROOT"].rstrip("/")
STALE_DAYS = int(os.environ.get("WASM_STALE_DAYS") or 10)

def env(k):
    v = os.environ.get(k, "").strip()
    return v or None

def sha256(p):
    h = hashlib.sha256()
    with open(p, "rb") as fh:
        for chunk in iter(lambda: fh.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()

# ── the assembly notes build-pages-dist.sh left for us ───────────────────────────
notes = {}
notes_path = os.path.join(DIST, ".assembly-notes")
if os.path.exists(notes_path):
    with open(notes_path, encoding="utf-8") as fh:
        for line in fh:
            line = line.strip()
            if "=" in line and not line.startswith("#"):
                k, _, v = line.partition("=")
                notes[k.strip()] = v.strip()
    os.remove(notes_path)

# ── THE SURFACE TABLE ────────────────────────────────────────────────────────────
# blob      : the file whose presence means "this surface really shipped"
# dir       : the surface's directory (a marker page goes here when it is wholly absent)
# pages     : every page that DEPENDS on this wasm and therefore must carry the marker
# built_by  : the heavy-workflow artifact that supplies it
SURFACES = [
    {
        "key": "webimage",
        "label": "the deos cockpit (WebImage skin)",
        "blob": "deos/pkg/starbridge_web_bg.wasm",
        "dir": "deos",
        "pages": ["deos/index.html"],
        "built_by": "wasm-webimage",
        "route": "/deos/",
    },
    {
        "key": "cockpit_gpui",
        "label": "the full gpui-web cockpit (WebGPU canvas)",
        "blob": "cockpit-gpui/pkg-gpui/starbridge_web_bg.wasm",
        "dir": "cockpit-gpui",
        "pages": ["cockpit-gpui/index.html"],
        "built_by": "wasm-gpui",
        "route": "/cockpit-gpui/",
    },
    {
        "key": "cards",
        "label": "the card-world engine (cards · light-client · transclusion)",
        "blob": "cards/pkg/dregg_wasm_bg.wasm",
        "dir": "cards",
        "pages": [
            "cards/index.html", "cards/counter.html", "cards/inspector.html",
            "cards/tally.html", "cards/kvstore.html", "cards/doccollab.html",
            "light-client/index.html", "transclusion/index.html",
        ],
        "built_by": "wasm-cards",
        "route": "/cards/ · /light-client/ · /transclusion/",
    },
]

# ── age / staleness ──────────────────────────────────────────────────────────────
built_at = env("WASM_PROV_BUILT_AT")
built_at_basis = "the source run's start time"
if not built_at:
    # No CI metadata (a local run). Fall back to the SOURCE blob build times the assembly
    # recorded, and take the OLDEST — the site is exactly as stale as its stalest surface,
    # and rounding that toward "fresh" is the answer a staleness signal must never give.
    # NOT the mtime of the copy inside the dist: `cp -R` does not preserve mtimes, so that
    # would report every bundle as seconds old. SAY WHICH, either way.
    recorded = sorted(
        (notes[f"surface.{s['key']}.src_built_at"], s["key"])
        for s in SURFACES
        if f"surface.{s['key']}.src_built_at" in notes
    )
    if recorded:
        built_at, oldest_key = recorded[0]
        built_at_basis = (f"the build time of the OLDEST shipped surface ({oldest_key}); "
                          f"no CI run provenance was supplied")
    else:
        built_at_basis = ("UNKNOWN — no CI run provenance and no recorded source build "
                          "time; age below cannot be trusted")

age_days = None
if built_at:
    try:
        t = datetime.strptime(built_at, "%Y-%m-%dT%H:%M:%SZ").replace(tzinfo=timezone.utc)
        age_days = round((datetime.now(timezone.utc) - t).total_seconds() / 86400.0, 1)
    except ValueError:
        pass

stale = age_days is not None and age_days > STALE_DAYS

# ── the teeth verdict ────────────────────────────────────────────────────────────
teeth = notes.get("teeth.web_surface", "not-run")
teeth_detail = notes.get("teeth.web_surface.detail", "")

# ── classify every surface ───────────────────────────────────────────────────────
included, missing, degraded = [], [], []
for s in SURFACES:
    blob = os.path.join(DIST, s["blob"])
    s["present"] = os.path.exists(blob) and os.path.getsize(blob) > 0
    if s["present"]:
        s["bytes"] = os.path.getsize(blob)
        s["sha256"] = sha256(blob)
        included.append(s["key"])
        if stale:
            degraded.append(s["key"])
    else:
        s["bytes"] = None
        s["sha256"] = None
        missing.append(s["key"])

# The teeth only ever describe the card-world surface.
cards = next(s for s in SURFACES if s["key"] == "cards")
if cards["present"] and teeth == "bit" and "cards" not in degraded:
    degraded.append("cards")

# ── the durable record ───────────────────────────────────────────────────────────
record = {
    "schema": "dregg-pages-wasm-provenance-v1",
    "stamped_at": datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
    "wasm": {
        "source": os.environ.get("WASM_PROV_SOURCE") or "local-tree",
        "run_id": env("WASM_PROV_RUN_ID"),
        "run_url": env("WASM_PROV_RUN_URL"),
        "head": env("WASM_PROV_HEAD"),
        "commit": env("WASM_PROV_COMMIT"),
        "built_at": built_at,
        "built_at_basis": built_at_basis,
        "age_days": age_days,
        "stale_after_days": STALE_DAYS,
        "stale": stale,
    },
    "site": {
        "commit": env("WASM_PROV_SITE_COMMIT"),
        "commits_ahead_of_wasm": (
            int(os.environ["WASM_PROV_COMMITS_BEHIND"])
            if (os.environ.get("WASM_PROV_COMMITS_BEHIND") or "").isdigit() else None
        ),
    },
    "teeth": {
        "web_surface": teeth,
        "detail": teeth_detail or None,
        "what_it_checks": "the baked light-client aggregate attests under the shipped "
                          "engine; transclusion verifies AND refuses a forge",
    },
    "surfaces": {
        s["key"]: {
            "label": s["label"],
            "route": s["route"],
            "included": s["present"],
            "built_by_artifact": s["built_by"],
            "blob": s["blob"],
            "bytes": s["bytes"],
            "sha256": s["sha256"],
        } for s in SURFACES
    },
    "included": included,
    "missing": missing,
    "degraded": degraded,
    "notes": notes,
}

with open(os.path.join(DIST, "wasm-provenance.json"), "w", encoding="utf-8") as fh:
    json.dump(record, fh, indent=2, sort_keys=False)
    fh.write("\n")

# ── marker markup ────────────────────────────────────────────────────────────────
def esc(x):
    return (str(x).replace("&", "&amp;").replace("<", "&lt;")
            .replace(">", "&gt;").replace('"', "&quot;"))

def short(c):
    return c[:8] if c else "unknown"

def prov_href(rel_page):
    # every surface page lives N directories deep; keep the link relative so the site
    # works at any subpath (github.io/<repo>/ as well as an apex domain).
    depth = rel_page.count("/")
    return "../" * depth + "wasm-provenance.json"

def source_phrase():
    if record["wasm"]["run_id"]:
        return f"source run #{record['wasm']['run_id']}"
    return f"source: {record['wasm']['source']}"

BAR = ("position:fixed;left:0;right:0;bottom:0;z-index:2147483647;"
       "font:12px/1.5 ui-monospace,SFMono-Regular,Menlo,monospace;"
       "padding:9px 14px;text-align:center;box-sizing:border-box")

def banner(kind, headline, detail, rel_page):
    tone = {
        "absent":  ("#3a1b12", "#ffd9c9", "#d9663f"),
        "stale":   ("#3a2f12", "#ffeec9", "#c49245"),
        "broken":  ("#3a1b12", "#ffd9c9", "#d9663f"),
    }[kind]
    bg, fg, line = tone
    href = esc(prov_href(rel_page))
    run = record["wasm"]["run_url"]
    runlink = f' <a href="{esc(run)}" style="color:{fg}">build log</a> ·' if run else ""
    return (
        f'\n<div data-dregg-provenance-marker="{kind}" style="{BAR};'
        f'background:{bg};color:{fg};border-top:2px solid {line}">'
        f'<b>{esc(headline)}</b> {esc(detail)}'
        f'{runlink} <a href="{href}" style="color:{fg}">provenance</a>'
        f'</div>\n'
    )

def meta_tag():
    w = record["wasm"]
    bits = [
        f"source={w['source']}",
        f"run={w['run_id'] or 'none'}",
        f"commit={short(w['commit'])}",
        f"built={w['built_at'] or 'unknown'}",
        f"age_days={w['age_days'] if w['age_days'] is not None else 'unknown'}",
        f"stale={str(w['stale']).lower()}",
        f"included={'+'.join(included) or 'none'}",
        f"missing={'+'.join(missing) or 'none'}",
        f"teeth={teeth}",
        f"site_commit={short(record['site']['commit'])}",
    ]
    return f'<meta name="dregg-wasm-provenance" content="{esc(" ".join(bits))}">\n'

def inject(path, before, markup):
    """Insert markup before the LAST occurrence of `before`. Returns True if injected."""
    with open(path, encoding="utf-8", errors="surrogateescape") as fh:
        html = fh.read()
    idx = html.rfind(before)
    if idx < 0:
        return False
    html = html[:idx] + markup + html[idx:]
    with open(path, "w", encoding="utf-8", errors="surrogateescape") as fh:
        fh.write(html)
    return True

MARKER_PAGE = """<!doctype html>
<html lang=en>
<head>
<meta charset=utf-8>
<meta name=viewport content="width=device-width,initial-scale=1">
<title>{title} — not in this build</title>
{meta}<style>
html,body{{margin:0;height:100%;background:#0a0f0d;color:#e4ddd0;
font:14px/1.6 ui-monospace,SFMono-Regular,Menlo,monospace}}
.w{{max-width:44rem;margin:0 auto;padding:12vh 1.5rem}}
h1{{font:600 20px/1.35 'Iowan Old Style',Palatino,Georgia,serif;color:#d9663f;margin:0 0 1rem}}
p{{color:#a89e8e;margin:0 0 1rem}}
code{{color:#9cc08a}}
a{{color:#7aab6f}}
.k{{border-left:2px solid #d9663f;padding-left:1rem;margin:1.5rem 0}}
</style>
</head>
<body>
<div class=w>
<h1>{title} is not in this build</h1>
<p class=k>This surface runs WebAssembly that is built by a separate, heavier workflow
(<code>pages-wasm.yml</code>, artifact <code>{artifact}</code>). The build this site was
assembled from did not carry it, so the page it would have served does not exist here.
Nothing stale is being shown to you — the surface is simply absent.</p>
<p>{detail}</p>
<p>What this build DID include, and exactly where its WebAssembly came from, is recorded
in <a href="{prov}">wasm-provenance.json</a> and rendered at
<a href="{up}wasm-provenance.html">wasm-provenance.html</a>.</p>
<p><a href="{up}">&larr; back to the landing</a></p>
</div>
</body>
</html>
"""

actions = []
metatag = meta_tag()

# Every route in the table is ADVERTISED by the landing/nav, so every route gets an
# answer. Three cases, and none of them is silence:
#   the page is not in this build at all -> stand up a marker PAGE where a bare 404
#                                           would otherwise be ("link broken", said out loud)
#   the page is here but its wasm is not -> the page ships, with an ABSENT marker
#   the page and wasm are here, degraded -> the page ships, with a STALE / BROKEN marker
for s in SURFACES:
    for rel in s["pages"]:
        p = os.path.join(DIST, rel)

        if not os.path.exists(p):
            os.makedirs(os.path.dirname(p) or DIST, exist_ok=True)
            detail = (f"Expected artifact <code>{esc(s['built_by'])}</code>; "
                      f"{esc(source_phrase())}.")
            with open(p, "w", encoding="utf-8") as fh:
                fh.write(MARKER_PAGE.format(
                    title=esc(s["label"]), artifact=esc(s["built_by"]),
                    detail=detail, meta=metatag, prov=esc(prov_href(rel)),
                    up="../" * rel.count("/")))
            actions.append(f"marker PAGE -> {rel}")
            continue

        inject(p, "</head>", metatag)

        if not s["present"]:
            # A missing thing cannot also be stale — say the stronger thing only.
            inject(p, "</body>", banner(
                "absent",
                "WebAssembly MISSING from this build.",
                f"{s['label']} needs the '{s['built_by']}' artifact, which this deploy "
                f"could not obtain ({source_phrase()}). Anything on this page that needs "
                f"the engine will not start.",
                rel))
            actions.append(f"absent marker -> {rel}")
            continue

        if stale:
            inject(p, "</body>", banner(
                "stale",
                "STALE WebAssembly.",
                f"This page's wasm was built {age_days} days ago "
                f"({source_phrase()}, commit {short(record['wasm']['commit'])}) while the "
                f"page around it is from commit {short(record['site']['commit'])}. It may "
                f"not match what the code now does.",
                rel))
            actions.append(f"stale marker -> {rel}")

        if s["key"] == "cards" and teeth == "bit":
            inject(p, "</body>", banner(
                "broken",
                "THIS DEMO IS KNOWN BROKEN in this build.",
                f"The shipped engine refuses the baked demo data "
                f"({teeth_detail[:240] if teeth_detail else 'see the provenance record'}).",
                rel))
            actions.append(f"broken marker -> {rel}")

# ── the human-readable provenance page ───────────────────────────────────────────
def row(k, v):
    return f"<tr><th>{esc(k)}</th><td>{v}</td></tr>"

w = record["wasm"]
badge = ("#7aab6f", "COMPLETE")
if missing:
    badge = ("#d9663f", f"INCOMPLETE — missing: {', '.join(missing)}")
elif stale or teeth == "bit":
    badge = ("#c49245", "DEGRADED")

surface_rows = "".join(
    "<tr><th>{}</th><td>{}</td></tr>".format(
        esc(s["label"]),
        (f'<span style="color:#7aab6f">included</span> · {s["bytes"]:,} bytes · '
         f'<code>{s["sha256"][:16]}…</code>') if s["present"] else
        f'<span style="color:#d9663f">MISSING</span> · needs artifact <code>{esc(s["built_by"])}</code>'
    ) for s in SURFACES
)

run_cell = (f'<a href="{esc(w["run_url"])}">#{esc(w["run_id"])}</a>'
            if w["run_url"] else esc(w["run_id"] or "—"))

with open(os.path.join(DIST, "wasm-provenance.html"), "w", encoding="utf-8") as fh:
    fh.write(f"""<!doctype html>
<html lang=en>
<head>
<meta charset=utf-8>
<meta name=viewport content="width=device-width,initial-scale=1">
<title>wasm provenance — what this deploy actually shipped</title>
{metatag}<style>
html,body{{margin:0;background:#0a0f0d;color:#e4ddd0;
font:13px/1.6 ui-monospace,SFMono-Regular,Menlo,monospace}}
.w{{max-width:56rem;margin:0 auto;padding:6vh 1.5rem 12vh}}
h1{{font:600 21px/1.35 'Iowan Old Style',Palatino,Georgia,serif;color:#9cc08a;margin:0 0 .4rem}}
h2{{font:600 15px/1.4 'Iowan Old Style',Palatino,Georgia,serif;color:#7aab6f;margin:2.2rem 0 .6rem}}
p{{color:#a89e8e}}
table{{border-collapse:collapse;width:100%;margin:.5rem 0}}
th,td{{text-align:left;vertical-align:top;padding:.45rem .7rem;
border-bottom:1px solid rgba(228,221,208,.10)}}
th{{color:#7a7265;font-weight:normal;white-space:nowrap;width:16rem}}
code{{color:#9cc08a}} a{{color:#7aab6f}}
.badge{{display:inline-block;padding:.2rem .6rem;border:1px solid {badge[0]};
color:{badge[0]};border-radius:4px;font-size:11px;letter-spacing:.4px}}
</style>
</head>
<body>
<div class=w>
<h1>wasm provenance</h1>
<p><span class=badge>{esc(badge[1])}</span></p>
<p>This site's static content and its WebAssembly are built by <b>two different
workflows</b>. The content ships on every push; the wasm surfaces are built on a
schedule by <code>pages-wasm.yml</code> and <b>reused</b> here. So the wasm can be
older than the page around it. This is that record, and it is the machine-readable
one too: <a href="wasm-provenance.json">wasm-provenance.json</a>.</p>

<h2>where the WebAssembly came from</h2>
<table>
{row("source", esc(w["source"]))}
{row("built by run", run_cell)}
{row("built from commit", f'<code>{esc(w["commit"] or "—")}</code>')}
{row("on ref", esc(w["head"] or "—"))}
{row("built at", esc(w["built_at"] or "unknown"))}
{row("that timestamp is", esc(w["built_at_basis"]))}
{row("age", (f'{w["age_days"]} days' + (' — <b style="color:#c49245">past the '
      f'{STALE_DAYS}-day staleness line</b>' if stale else '')) if w["age_days"] is not None else "unknown")}
</table>

<h2>the static content around it</h2>
<table>
{row("site commit", f'<code>{esc(record["site"]["commit"] or "—")}</code>')}
{row("commits ahead of the wasm", esc(record["site"]["commits_ahead_of_wasm"]
      if record["site"]["commits_ahead_of_wasm"] is not None else "not computed"))}
</table>

<h2>the surfaces</h2>
<table>
{surface_rows}
</table>

<h2>the browser-surface teeth</h2>
<table>
{row("verdict", esc(teeth))}
{row("detail", f'<code>{esc(teeth_detail or "—")}</code>')}
{row("what they check", esc(record["teeth"]["what_it_checks"]))}
</table>
</div>
</body>
</html>
""")

# ── report ───────────────────────────────────────────────────────────────────────
gha = os.environ.get("GITHUB_ACTIONS") == "true"
summary = os.environ.get("GITHUB_STEP_SUMMARY")

print("=== wasm provenance stamp ===")
print(f"  source        : {w['source']} run={w['run_id'] or '—'} commit={short(w['commit'])}")
print(f"  built at      : {w['built_at'] or 'unknown'}  ({w['built_at_basis']})")
print(f"  age           : {w['age_days'] if w['age_days'] is not None else 'unknown'} days "
      f"(stale after {STALE_DAYS})")
print(f"  included      : {', '.join(included) or 'NOTHING'}")
print(f"  missing       : {', '.join(missing) or 'none'}")
print(f"  teeth         : {teeth}")
for a in actions:
    print(f"  {a}")
print(f"  wrote         : wasm-provenance.json + wasm-provenance.html")

if gha:
    if missing:
        print(f"::warning title=Pages shipped without a wasm surface::"
              f"missing: {', '.join(missing)} — the site deployed WITH IN-PAGE MARKERS "
              f"instead of failing. Run the 'Build the Pages wasm surfaces' workflow.")
    if stale:
        print(f"::warning title=Pages shipped stale wasm::the reused wasm is "
              f"{w['age_days']} days old (limit {STALE_DAYS}); every wasm page carries a "
              f"visible stale marker.")
    if teeth == "bit":
        print(f"::warning title=A browser-surface tooth bit::{teeth_detail[:400]}")

if summary:
    with open(summary, "a", encoding="utf-8") as fh:
        fh.write(f"\n### wasm provenance — `{badge[1]}`\n\n")
        fh.write(f"| | |\n|---|---|\n")
        fh.write(f"| wasm source | {w['source']} |\n")
        fh.write(f"| built by run | {run_cell if w['run_url'] else (w['run_id'] or '—')} |\n")
        fh.write(f"| wasm commit | `{w['commit'] or '—'}` |\n")
        fh.write(f"| built at | {w['built_at'] or 'unknown'} ({w['age_days']} days ago) |\n")
        fh.write(f"| site commit | `{record['site']['commit'] or '—'}` |\n")
        fh.write(f"| included | {', '.join(included) or '**NOTHING**'} |\n")
        fh.write(f"| missing | {', '.join(missing) or 'none'} |\n")
        fh.write(f"| teeth | {teeth} |\n")
        if actions:
            fh.write("\nIn-page markers written:\n\n")
            for a in actions:
                fh.write(f"- {a}\n")
PY
