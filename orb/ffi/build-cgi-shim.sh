#!/usr/bin/env bash
# Compile the CGI process-spawn shim (ffi/cgi_exec.c) to an object file that the
# exes whose deployed serve reaches a CGI route link via moreLinkArgs. TOML
# lakefiles cannot compile a C source as a build target, so this runs as a
# prerequisite step. Idempotent; re-run after editing cgi_exec.c, then rebuild
# the linking exe (e.g. `lake build orb`).
#
# The shim is plain POSIX (fork/execve/pipe/waitpid) — no external backend. It
# compiles against the active Lean toolchain's runtime header (<lean/lean.h>)
# so the object matches the runtime ABI, while still finding the system SDK
# headers (which the bundled leanc clang does not locate).
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"

# Resolve the active toolchain's include dir (lean/lean.h) robustly:
inc="$(lean --print-prefix 2>/dev/null || true)/include"
if [ ! -f "$inc/lean/lean.h" ]; then
  inc="$HOME/.elan/toolchains/leanprover--lean4---v4.17.0/include"
fi

cc -c -O2 -fPIC -I "$inc" -o "$here/cgi_exec.o" "$here/cgi_exec.c"
echo "built $here/cgi_exec.o (POSIX fork/execve CGI shim)"
