#!/usr/bin/env bash
# Compile the untrusted TCP-client seam the `derp-live` exe links against:
#   ffi/derp_net.c -> ffi/derp_net.o  (connect, send-all, recv-exact over TCP)
# TOML lakefiles cannot compile a C source directly, so we precompile here and
# reference the object from moreLinkArgs in lakefile.toml. Re-run whenever the C
# source changes. Uses the Lean toolchain include path so the object matches the
# runtime ABI (<lean/lean.h>).
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
inc="$(lean --print-prefix)/include"
cc -c -O2 -fPIC -I "$inc" -o "$here/derp_net.o" "$here/derp_net.c"
echo "built $here/derp_net.o"
