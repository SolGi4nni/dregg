#!/usr/bin/env bash
# Build the shared static document root both servers serve from, plus a
# sibling file OUTSIDE the root (the traversal-escape target).
# Deterministic content + pinned mtimes so Last-Modified is comparable.
set -euo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
SITE="$HERE/site"
rm -rf "$SITE" "$HERE/outside"
mkdir -p "$SITE/sub" "$HERE/outside"

printf '<!doctype html><html><head><title>root index</title></head><body><h1>root index page</h1></body></html>\n' > "$SITE/index.html"
printf 'hello world\n' > "$SITE/hello.txt"
printf '{"kind":"fixture","n":42}\n' > "$SITE/data.json"
printf 'body { color: #222; margin: 0; }\n' > "$SITE/style.css"
printf 'console.log("fixture");\n' > "$SITE/script.js"
printf '' > "$SITE/empty.txt"
printf 'no extension content\n' > "$SITE/no-ext"
printf 'hidden file content\n' > "$SITE/.hidden.txt"
printf 'space name content\n' > "$SITE/sp ace.txt"
printf 'utf8 name content\n' > "$SITE/café.txt"
printf '<!doctype html><html><body><p>sub page</p></body></html>\n' > "$SITE/sub/page.html"
printf '<!doctype html><html><body><p>sub index</p></body></html>\n' > "$SITE/sub/index.html"
# 200 KiB deterministic binary for range tests: repeating 0..255 pattern.
python3 - "$SITE/big.bin" <<'EOF'
import sys
with open(sys.argv[1], "wb") as f:
    f.write(bytes(range(256)) * 800)
EOF
# A biggish compressible text file (gzip behaviour probe).
python3 - "$SITE/lorem.txt" <<'EOF'
import sys
line = "the quick brown fox jumps over the lazy dog 0123456789\n"
with open(sys.argv[1], "w") as f:
    f.write(line * 400)
EOF
# The escape target: must NEVER be reachable via /static/../
printf 'TRAVERSAL ESCAPE MARKER\n' > "$HERE/outside/secret.txt"

# Pin every mtime so both servers report the identical Last-Modified.
find "$SITE" "$HERE/outside" -exec touch -d '2026-01-02 03:04:05 UTC' {} +
echo "site built at $SITE"
