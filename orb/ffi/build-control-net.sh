#!/usr/bin/env bash
# Compile the untrusted TCP-server seam the `control-live` coord mode links against:
#   ffi/control_net.c -> ffi/control_net.o  (bind+listen, accept over TCP)
# The client side (connect, send-all, recv-exact, close) is reused from
# ffi/derp_net.o. TOML/Lake lakefiles cannot compile a C source directly, so we
# precompile here and reference the object from moreLinkArgs in lakefile.lean.
# Re-run whenever the C source changes. Uses the Lean toolchain include path so
# the object matches the runtime ABI (<lean/lean.h>).
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
inc="$(lean --print-prefix)/include"
cc -c -O2 -fPIC -I "$inc" -o "$here/control_net.o" "$here/control_net.c"
echo "built $here/control_net.o"
