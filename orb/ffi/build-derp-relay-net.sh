#!/usr/bin/env bash
# Compile the untrusted TCP-server seam the `derp-relay` exe links against:
#   ffi/derp_relay_net.c -> ffi/derp_relay_net.o
#     (listen, accept, send-all, recv-exact, recv-some, poll, close over TCP)
# TOML lakefiles cannot compile a C source directly, so we precompile here and
# reference the object from moreLinkArgs in lakefile.toml. Re-run whenever the C
# source changes. Uses the Lean toolchain include path so the object matches the
# runtime ABI (<lean/lean.h>).
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
inc="$(lean --print-prefix)/include"
cc -c -O2 -fPIC -I "$inc" -o "$here/derp_relay_net.o" "$here/derp_relay_net.c"
echo "built $here/derp_relay_net.o"
