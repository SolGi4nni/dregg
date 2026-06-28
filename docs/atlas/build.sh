#!/usr/bin/env bash
# Build the single, self-contained dregg atlas.
#
# Inlines styles.css (into a <style>) and data.js (into a <script>) into the
# index.html template, emitting docs/atlas/atlas.html — one file, no external
# local refs, opens standalone via file:// and serves fine.
#
# Edit the SOURCES (index.html / data.js / styles.css); re-run this script to
# regenerate atlas.html. Share atlas.html.
set -euo pipefail

DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

python3 - "$DIR" <<'PY'
import sys, pathlib

d = pathlib.Path(sys.argv[1])
html = (d / "index.html").read_text()
css  = (d / "styles.css").read_text()
js   = (d / "data.js").read_text()

# Inline the stylesheet (replace the <link> with an inline <style>).
link = '<link rel="stylesheet" href="styles.css">'
assert link in html, "stylesheet <link> not found in index.html"
html = html.replace(link, "<style>\n" + css + "\n</style>")

# Inline the data model (replace the external <script src> with an inline one).
src = '<script src="data.js"></script>'
assert src in html, "data.js <script src> not found in index.html"
html = html.replace(src, "<script>\n" + js + "\n</script>")

out = d / "atlas.html"
out.write_text(html)
print(f"wrote {out} ({out.stat().st_size} bytes)")
PY
